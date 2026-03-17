"""
Syracuse-JEPA v2 — Training Loop

Trains the JEPA on compositions from multiple k values.
The model learns representations that capture the mathematical structure
linking composition patterns to their corrSum arithmetic properties.

After training, the latent space is analyzed for:
1. Clusters that correlate with mathematical properties
2. Separating structures that explain N₀(d) = 0
3. Features that could be formalized as lemmas
"""

import os
import sys
import json
import time
import math
import numpy as np
import torch
import torch.nn as nn
from torch.utils.data import Dataset, DataLoader

# Add parent to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from syracuse_jepa.data.generator import (
    compute_S, compute_d, corrsum, corrsum_terms, corrsum_mod,
    enumerate_monotone_compositions, count_compositions,
    sample_monotone_composition, generate_multi_view_features,
)
from syracuse_jepa.models.jepa import CollatzJEPA
from syracuse_jepa.models.vicreg import VICRegLoss


# ═══════════════════════════════════════════════════════════════
#  Dataset
# ═══════════════════════════════════════════════════════════════

class CompositionDataset(Dataset):
    """Dataset of monotone compositions with multi-view features."""

    def __init__(self, k_values: list, max_k: int = 50,
                 max_samples_per_k: int = 10000, seed: int = 42):
        self.max_k = max_k
        self.data = []
        rng = np.random.default_rng(seed)

        for k in k_values:
            S = compute_S(k)
            d = compute_d(k)
            n_comp = count_compositions(k, S)

            if n_comp <= max_samples_per_k:
                # Enumerate all
                compositions = list(enumerate_monotone_compositions(k, S))
            else:
                # Sample
                compositions = []
                seen = set()
                for _ in range(max_samples_per_k * 2):  # oversample to handle duplicates
                    A = sample_monotone_composition(k, S, rng)
                    if A not in seen:
                        seen.add(A)
                        compositions.append(A)
                    if len(compositions) >= max_samples_per_k:
                        break

            for A in compositions:
                features = generate_multi_view_features(A, k, S, d)
                self.data.append({
                    'k': k,
                    'S': S,
                    'd': d,
                    'composition_raw': A,
                    'features': features,
                })

        print(f"Dataset: {len(self.data)} compositions from k={k_values}")

    def __len__(self):
        return len(self.data)

    def __getitem__(self, idx):
        item = self.data[idx]
        f = item['features']
        k = item['k']

        def pad(arr, target_len, fill=0.0):
            arr = np.array(arr, dtype=np.float32)
            if len(arr) >= target_len:
                return arr[:target_len]
            return np.pad(arr, (0, target_len - len(arr)), constant_values=fill)

        return {
            'composition': torch.tensor(pad(f['view1_composition'], self.max_k)),
            'fft_magnitude': torch.tensor(pad(f['view3_fft_magnitude'], self.max_k)),
            'fft_phase': torch.tensor(pad(f['view3_fft_phase'], self.max_k)),
            'prime_residues': torch.tensor(f['view2_prime_residues']),
            'fractional_ratio': torch.tensor(f['view2_fractional_ratio']),
            # Labels for probing (not used in JEPA training)
            'residue_mod_d': torch.tensor(float(f['residue_mod_d'])),
            'ratio': torch.tensor(float(f['ratio'])),
            'k': torch.tensor(k),
        }


# ═══════════════════════════════════════════════════════════════
#  Training
# ═══════════════════════════════════════════════════════════════

def train_jepa(
    k_values: list = list(range(3, 21)),
    max_k: int = 50,
    embed_dim: int = 128,
    predictor_hidden: int = 256,
    ema_decay: float = 0.996,
    lr: float = 1e-3,
    epochs: int = 100,
    batch_size: int = 64,
    max_samples_per_k: int = 5000,
    seed: int = 42,
    log_dir: str = 'syracuse_jepa/logs',
    device_str: str = 'auto',
):
    """Train the Collatz-JEPA model."""

    # Device
    if device_str == 'auto':
        if torch.backends.mps.is_available():
            device = torch.device('mps')
        elif torch.cuda.is_available():
            device = torch.device('cuda')
        else:
            device = torch.device('cpu')
    else:
        device = torch.device(device_str)
    print(f"Device: {device}")

    # Dataset
    dataset = CompositionDataset(k_values, max_k, max_samples_per_k, seed)
    loader = DataLoader(dataset, batch_size=batch_size, shuffle=True, drop_last=True)

    # Model
    model = CollatzJEPA(
        max_k=max_k,
        embed_dim=embed_dim,
        predictor_hidden=predictor_hidden,
        ema_decay=ema_decay,
    ).to(device)

    params = model.count_parameters()
    print(f"Model parameters: {params}")

    # Loss
    criterion = VICRegLoss(lambda_inv=25.0, lambda_var=25.0, lambda_cov=1.0)

    # Optimizer
    # Only optimize context encoder + predictor (target encoder is EMA)
    trainable_params = list(model.context_encoder.parameters()) + list(model.predictor.parameters())
    optimizer = torch.optim.AdamW(trainable_params, lr=lr, weight_decay=1e-4)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs)

    # Logging
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, 'training_log.jsonl')
    best_loss = float('inf')

    print(f"\n{'='*60}")
    print(f"  Syracuse-JEPA v2 Training")
    print(f"  k values: {k_values}")
    print(f"  Dataset size: {len(dataset)}")
    print(f"  Epochs: {epochs}")
    print(f"  Batch size: {batch_size}")
    print(f"{'='*60}\n")

    t_start = time.time()

    for epoch in range(epochs):
        model.train()
        epoch_losses = {'loss': 0, 'invariance': 0, 'variance': 0, 'covariance': 0}
        n_batches = 0

        for batch in loader:
            # Move to device
            batch_device = {k: v.to(device) for k, v in batch.items()}

            # Forward
            out = model(batch_device)

            # VICReg loss
            loss_dict = criterion(out['z_pred'], out['z_target'])
            loss = loss_dict['loss']

            # Backward
            optimizer.zero_grad()
            loss.backward()
            torch.nn.utils.clip_grad_norm_(trainable_params, max_norm=1.0)
            optimizer.step()

            # Update target encoder (EMA)
            model.update_target_encoder()

            # Accumulate
            for key in epoch_losses:
                epoch_losses[key] += loss_dict[key] if key == 'loss' else loss_dict[key]
            n_batches += 1

        scheduler.step()

        # Average
        for key in epoch_losses:
            epoch_losses[key] /= max(n_batches, 1)

        # Log
        log_entry = {
            'epoch': epoch,
            'loss': float(epoch_losses['loss']),
            'invariance': epoch_losses['invariance'],
            'variance': epoch_losses['variance'],
            'covariance': epoch_losses['covariance'],
            'lr': scheduler.get_last_lr()[0],
            'time_elapsed': time.time() - t_start,
        }

        with open(log_path, 'a') as f:
            f.write(json.dumps(log_entry) + '\n')

        if epoch % 10 == 0 or epoch == epochs - 1:
            print(
                f"Epoch {epoch:3d}/{epochs}  "
                f"Loss={epoch_losses['loss']:.4f}  "
                f"Inv={epoch_losses['invariance']:.4f}  "
                f"Var={epoch_losses['variance']:.4f}  "
                f"Cov={epoch_losses['covariance']:.4f}  "
                f"LR={scheduler.get_last_lr()[0]:.6f}"
            )

        # Save best
        if epoch_losses['loss'] < best_loss:
            best_loss = epoch_losses['loss']
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'loss': best_loss,
                'config': {
                    'k_values': k_values,
                    'max_k': max_k,
                    'embed_dim': embed_dim,
                    'predictor_hidden': predictor_hidden,
                    'ema_decay': ema_decay,
                },
            }, os.path.join(log_dir, 'best_model.pt'))

    total_time = time.time() - t_start
    print(f"\nTraining complete in {total_time:.1f}s. Best loss: {best_loss:.4f}")

    # Save final model
    torch.save({
        'epoch': epochs - 1,
        'model_state_dict': model.state_dict(),
        'config': {
            'k_values': k_values,
            'max_k': max_k,
            'embed_dim': embed_dim,
            'predictor_hidden': predictor_hidden,
            'ema_decay': ema_decay,
        },
    }, os.path.join(log_dir, 'final_model.pt'))

    return model, dataset


# ═══════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    model, dataset = train_jepa(
        k_values=list(range(3, 21)),
        epochs=100,
        batch_size=64,
        embed_dim=128,
        max_samples_per_k=5000,
    )
