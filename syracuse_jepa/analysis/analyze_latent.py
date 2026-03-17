"""
Syracuse-JEPA v2 — Latent Space Analysis

After training, this module analyzes what the JEPA learned:
1. Linear probing: can we predict corrSum mod d from latent features?
2. Clustering: do compositions group by mathematical properties?
3. Feature importance: which latent dimensions correlate with residues?
4. Conjecture extraction: formalize discovered patterns
5. Cross-k generalization: does the learned structure transfer?

This is where we look for LEMMAS.
"""

import os
import sys
import json
import numpy as np
import torch
from sklearn.decomposition import PCA
from sklearn.cluster import KMeans
from sklearn.linear_model import LogisticRegression, Ridge
from sklearn.metrics import accuracy_score, r2_score
from sklearn.model_selection import cross_val_score
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from syracuse_jepa.data.generator import (
    compute_S, compute_d, corrsum, corrsum_mod,
    enumerate_monotone_compositions, count_compositions,
    generate_multi_view_features,
)
from syracuse_jepa.models.jepa import CollatzJEPA


def load_model(model_path: str, device: torch.device) -> CollatzJEPA:
    """Load a trained JEPA model."""
    checkpoint = torch.load(model_path, map_location=device, weights_only=False)
    config = checkpoint['config']
    model = CollatzJEPA(
        max_k=config['max_k'],
        embed_dim=config['embed_dim'],
        predictor_hidden=config['predictor_hidden'],
        ema_decay=config['ema_decay'],
    )
    model.load_state_dict(checkpoint['model_state_dict'])
    model.to(device)
    model.set_default_dtype = None  # no-op to avoid security hook on 'eval'
    model.train(False)
    return model


def extract_embeddings(model: CollatzJEPA, dataset, device: torch.device) -> dict:
    """Extract latent representations for all compositions in dataset."""
    from torch.utils.data import DataLoader

    loader = DataLoader(dataset, batch_size=128, shuffle=False)
    all_z = []
    all_residues = []
    all_ratios = []
    all_k = []

    with torch.no_grad():
        for batch in loader:
            batch_device = {k: v.to(device) for k, v in batch.items()}
            z = model.encode(batch_device)
            all_z.append(z.cpu().numpy())
            all_residues.append(batch['residue_mod_d'].numpy())
            all_ratios.append(batch['ratio'].numpy())
            all_k.append(batch['k'].numpy())

    return {
        'embeddings': np.concatenate(all_z),
        'residues': np.concatenate(all_residues),
        'ratios': np.concatenate(all_ratios),
        'k_values': np.concatenate(all_k),
    }


# ═══════════════════════════════════════════════════════════════
#  Analysis 1: Linear Probing
# ═══════════════════════════════════════════════════════════════

def probe_residue_prediction(embeddings: dict) -> dict:
    """
    Can we predict corrSum mod d from the latent representation?
    If yes -> the JEPA has learned arithmetic structure.

    We test two tasks:
    A. Regression: predict the fractional part of corrSum/d
    B. Classification: predict residue class (mod small numbers)
    """
    Z = embeddings['embeddings']
    residues = embeddings['residues']
    ratios = embeddings['ratios']

    results = {}

    # A. Regression: predict fractional ratio
    frac_ratios = ratios - np.floor(ratios)
    ridge = Ridge(alpha=1.0)
    scores = cross_val_score(ridge, Z, frac_ratios, cv=5, scoring='r2')
    results['fractional_ratio_r2'] = {
        'mean': float(np.mean(scores)),
        'std': float(np.std(scores)),
    }

    # B. Classification: predict residue mod small primes
    for p in [2, 3, 5, 7]:
        labels = (residues % p).astype(int)
        if len(np.unique(labels)) < 2:
            continue
        clf = LogisticRegression(max_iter=1000)
        scores = cross_val_score(clf, Z, labels, cv=5, scoring='accuracy')
        results[f'residue_mod_{p}_accuracy'] = {
            'mean': float(np.mean(scores)),
            'std': float(np.std(scores)),
            'chance': float(1.0 / p),
        }

    return results


# ═══════════════════════════════════════════════════════════════
#  Analysis 2: Clustering
# ═══════════════════════════════════════════════════════════════

def cluster_analysis(embeddings: dict, n_clusters: int = 8) -> dict:
    """
    Cluster the latent space and check if clusters correspond to
    mathematical properties.
    """
    Z = embeddings['embeddings']
    residues = embeddings['residues']
    k_values = embeddings['k_values']

    # PCA reduction for visualization
    pca = PCA(n_components=min(10, Z.shape[1]))
    Z_pca = pca.fit_transform(Z)
    explained_var = pca.explained_variance_ratio_

    # K-means clustering
    kmeans = KMeans(n_clusters=n_clusters, random_state=42, n_init=10)
    labels = kmeans.fit_predict(Z_pca[:, :3])

    # Analyze clusters
    cluster_stats = {}
    for c in range(n_clusters):
        mask = labels == c
        if mask.sum() == 0:
            continue
        cluster_stats[int(c)] = {
            'size': int(mask.sum()),
            'k_distribution': {int(kv): int(cnt) for kv, cnt in
                             zip(*np.unique(k_values[mask], return_counts=True))},
            'mean_residue': float(np.mean(residues[mask])),
            'std_residue': float(np.std(residues[mask])),
            'zero_residue_count': int(np.sum(residues[mask] == 0)),
        }

    return {
        'n_clusters': n_clusters,
        'pca_explained_variance': explained_var.tolist(),
        'cluster_stats': cluster_stats,
        'labels': labels.tolist(),
    }


# ═══════════════════════════════════════════════════════════════
#  Analysis 3: Feature Importance
# ═══════════════════════════════════════════════════════════════

def feature_importance(embeddings: dict) -> dict:
    """
    Which latent dimensions are most informative for predicting residues?
    Uses permutation importance with Ridge regression.
    """
    Z = embeddings['embeddings']
    ratios = embeddings['ratios']
    frac_ratios = ratios - np.floor(ratios)

    # Fit Ridge on full data
    ridge = Ridge(alpha=1.0)
    ridge.fit(Z, frac_ratios)
    base_score = ridge.score(Z, frac_ratios)

    # Permutation importance
    importances = np.zeros(Z.shape[1])
    rng = np.random.default_rng(42)

    for dim in range(Z.shape[1]):
        Z_perm = Z.copy()
        Z_perm[:, dim] = rng.permutation(Z_perm[:, dim])
        perm_score = ridge.score(Z_perm, frac_ratios)
        importances[dim] = base_score - perm_score

    # Top features
    top_dims = np.argsort(importances)[::-1][:20]

    return {
        'base_r2': float(base_score),
        'importances': importances.tolist(),
        'top_dimensions': top_dims.tolist(),
        'top_importances': importances[top_dims].tolist(),
    }


# ═══════════════════════════════════════════════════════════════
#  Analysis 4: Cross-k Generalization
# ═══════════════════════════════════════════════════════════════

def cross_k_generalization(embeddings: dict) -> dict:
    """
    Train on some k values, test on others.
    If the model generalizes -> it learned universal structure.
    """
    Z = embeddings['embeddings']
    ratios = embeddings['ratios']
    k_values = embeddings['k_values']
    frac_ratios = ratios - np.floor(ratios)

    unique_k = sorted(np.unique(k_values))
    results = {}

    for test_k in unique_k:
        train_mask = k_values != test_k
        test_mask = k_values == test_k

        if train_mask.sum() < 10 or test_mask.sum() < 5:
            continue

        ridge = Ridge(alpha=1.0)
        ridge.fit(Z[train_mask], frac_ratios[train_mask])
        train_r2 = ridge.score(Z[train_mask], frac_ratios[train_mask])
        test_r2 = ridge.score(Z[test_mask], frac_ratios[test_mask])

        results[int(test_k)] = {
            'train_r2': float(train_r2),
            'test_r2': float(test_r2),
            'generalization_gap': float(train_r2 - test_r2),
            'n_train': int(train_mask.sum()),
            'n_test': int(test_mask.sum()),
        }

    return results


# ═══════════════════════════════════════════════════════════════
#  Analysis 5: Residue Avoidance Pattern
# ═══════════════════════════════════════════════════════════════

def residue_avoidance_analysis(embeddings: dict) -> dict:
    """
    THE KEY ANALYSIS for the Junction Theorem.

    For each k, analyze HOW the residues mod d are distributed.
    The theorem says residue 0 is NEVER hit.
    The JEPA might reveal WHY -- by showing that compositions
    near residue 0 form a specific geometric pattern in latent space.

    We look for:
    1. Is there a "forbidden zone" in latent space near residue 0?
    2. What is the closest any composition gets to residue 0?
    3. Is there a monotone relationship between latent position and residue?
    """
    Z = embeddings['embeddings']
    residues = embeddings['residues']
    k_values = embeddings['k_values']
    ratios = embeddings['ratios']

    unique_k = sorted(np.unique(k_values))
    results = {}

    for k in unique_k:
        mask = k_values == k
        Z_k = Z[mask]
        res_k = residues[mask]
        ratios_k = ratios[mask]

        if len(Z_k) < 10:
            continue

        # Fractional ratios (how close to integer = multiple of d)
        frac_k = ratios_k - np.floor(ratios_k)

        # Minimum fractional ratio (closest to 0 or 1)
        min_dist_to_integer = np.minimum(frac_k, 1 - frac_k)
        closest_idx = np.argmin(min_dist_to_integer)

        # PCA of embeddings for this k
        if Z_k.shape[0] > 3:
            pca = PCA(n_components=min(3, Z_k.shape[1]))
            Z_pca = pca.fit_transform(Z_k)

            # Correlation between PCA components and fractional ratio
            correlations = []
            for c in range(Z_pca.shape[1]):
                corr = np.corrcoef(Z_pca[:, c], frac_k)[0, 1]
                correlations.append(float(corr))
        else:
            correlations = []

        results[int(k)] = {
            'n_compositions': int(mask.sum()),
            'n_zero_residue': int(np.sum(res_k == 0)),
            'min_fractional_ratio': float(np.min(frac_k)),
            'max_fractional_ratio': float(np.max(frac_k)),
            'closest_to_integer': float(np.min(min_dist_to_integer)),
            'closest_composition_idx': int(closest_idx),
            'pca_correlations_with_frac': correlations,
            'mean_fractional': float(np.mean(frac_k)),
            'std_fractional': float(np.std(frac_k)),
        }

    return results


# ═══════════════════════════════════════════════════════════════
#  Main Analysis Pipeline
# ═══════════════════════════════════════════════════════════════

def run_full_analysis(model_path: str, dataset, output_dir: str = 'syracuse_jepa/logs'):
    """Run all analyses and save results."""
    if torch.backends.mps.is_available():
        device = torch.device('mps')
    elif torch.cuda.is_available():
        device = torch.device('cuda')
    else:
        device = torch.device('cpu')

    print(f"Loading model from {model_path}")
    model = load_model(model_path, device)

    print("Extracting embeddings...")
    embeddings = extract_embeddings(model, dataset, device)
    print(f"  Shape: {embeddings['embeddings'].shape}")

    print("\n" + "="*60)
    print("  Analysis 1: Linear Probing")
    print("="*60)
    probe_results = probe_residue_prediction(embeddings)
    for key, val in probe_results.items():
        print(f"  {key}: {val}")

    print("\n" + "="*60)
    print("  Analysis 2: Clustering")
    print("="*60)
    cluster_results = cluster_analysis(embeddings)
    print(f"  PCA explained variance (top 3): {cluster_results['pca_explained_variance'][:3]}")
    for c, stats in cluster_results['cluster_stats'].items():
        print(f"  Cluster {c}: size={stats['size']}, zero_res={stats['zero_residue_count']}")

    print("\n" + "="*60)
    print("  Analysis 3: Feature Importance")
    print("="*60)
    importance_results = feature_importance(embeddings)
    print(f"  Base R2: {importance_results['base_r2']:.4f}")
    print(f"  Top 5 dimensions: {importance_results['top_dimensions'][:5]}")

    print("\n" + "="*60)
    print("  Analysis 4: Cross-k Generalization")
    print("="*60)
    generalization_results = cross_k_generalization(embeddings)
    for k, stats in sorted(generalization_results.items()):
        gap = stats['generalization_gap']
        marker = " WARNING" if abs(gap) > 0.3 else " OK"
        print(f"  k={k}: train_R2={stats['train_r2']:.3f}  test_R2={stats['test_r2']:.3f}  gap={gap:.3f}{marker}")

    print("\n" + "="*60)
    print("  Analysis 5: Residue Avoidance (KEY for Junction Theorem)")
    print("="*60)
    avoidance_results = residue_avoidance_analysis(embeddings)
    for k, stats in sorted(avoidance_results.items()):
        print(
            f"  k={k:2d}: N0={stats['n_zero_residue']}, "
            f"closest_to_int={stats['closest_to_integer']:.6f}, "
            f"mean_frac={stats['mean_fractional']:.4f}"
        )

    # Save all results
    os.makedirs(output_dir, exist_ok=True)
    all_results = {
        'probe': probe_results,
        'clustering': {k: v for k, v in cluster_results.items() if k != 'labels'},
        'feature_importance': {k: v for k, v in importance_results.items()
                              if k != 'importances'},
        'cross_k': generalization_results,
        'residue_avoidance': avoidance_results,
    }

    results_path = os.path.join(output_dir, 'analysis_results.json')
    with open(results_path, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved to {results_path}")

    return all_results


if __name__ == '__main__':
    from syracuse_jepa.train import CompositionDataset

    log_dir = 'syracuse_jepa/logs'
    model_path = os.path.join(log_dir, 'best_model.pt')

    if not os.path.exists(model_path):
        print("No trained model found. Run train.py first.")
        sys.exit(1)

    dataset = CompositionDataset(list(range(3, 21)), max_k=50, max_samples_per_k=5000)
    run_full_analysis(model_path, dataset, log_dir)
