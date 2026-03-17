#!/usr/bin/env python3
"""
Davies-Style Attribution Model for Collatz Range Exclusion Tightness
====================================================================

Inspired by Davies et al. (Nature 2021): train a supervised model to predict
a mathematical quantity, then use feature importance / saliency to guide
mathematical intuition.

APPROACH:
  For each k in [3, 200] (excluding k=4, the phantom):
    - Target: how "tight" is the Range Exclusion mechanism?
      theta(k)     = (cs_max(k) mod d(k)) / d(k)     (closeness to failure)
      log_margin(k)= log10(theta / (range/d))          (safety margin in log)
      is_tight(k)  = 1 if log_margin < median          (binary classification)

    - Features: 15 mathematical quantities derived from k
      (number-theoretic, Diophantine, continued-fraction, spectral)

    - Insight: which features determine whether k is "easy" or "hard"?

FALLBACK: if scikit-learn is unavailable, uses Pearson + Spearman correlation
of each feature with the target as a surrogate for feature importance.

Reference: Davies, Velickovic, Buesing et al., "Advancing mathematics by
guiding human intuition with AI", Nature 600, 70-74 (2021).

Author: Eric Merle (generated with Claude attribution pipeline)
"""

import math
import statistics
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from fractions import Fraction

# =====================================================================
#  Constants
# =====================================================================

LOG2_3 = math.log2(3)  # 1.58496...

# Continued fraction partial quotients of log_2(3) (first 50 terms)
CF_LOG2_3 = [
    1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1,
    15, 1, 9, 2, 5, 7, 1, 1, 4, 8, 1, 11, 1, 20, 2, 1, 10, 1, 4, 1,
    1, 1, 1, 1, 37, 4, 55, 1, 1, 49,
]

FEATURE_NAMES = [
    "k", "r_excess", "r_mod", "delta_frac", "log_d",
    "n_prime_factors", "log2_smallest_pf", "log2_largest_pf",
    "cf_distance", "cf_partial_quotient", "frac_k_alpha",
    "plateau_length", "log10_range_over_d", "rho_best", "k_min_best",
]


# =====================================================================
#  Number-theoretic helpers (self-contained)
# =====================================================================

def _compute_S(k: int) -> int:
    """S(k) = ceil(k * log2(3))."""
    return math.ceil(k * LOG2_3)


def _compute_d(k: int) -> int:
    """d(k) = 2^S(k) - 3^k."""
    S = _compute_S(k)
    return (1 << S) - 3 ** k


def _factorize(n: int, limit: int = 10 ** 7) -> List[Tuple[int, int]]:
    """Trial division up to limit. Returns [(p, e), ...]."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n and d <= limit:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors


def _multiplicative_order(a: int, n: int) -> int:
    """ord_n(a) via divisor descent on phi(n). Assumes n prime."""
    if math.gcd(a, n) != 1:
        return 0
    if n <= 2:
        return 1
    phi = n - 1
    order = phi
    for p, _ in _factorize(phi):
        while order % p == 0 and pow(a, order // p, n) == 1:
            order //= p
    return order


def _cf_convergents(partial_quotients: List[int]) -> List[Tuple[int, int]]:
    """Compute convergents p_n/q_n from partial quotients. Returns [(p, q), ...]."""
    convergents = []
    h_prev, h_curr = 0, 1
    k_prev, k_curr = 1, 0
    for a in partial_quotients:
        h_prev, h_curr = h_curr, a * h_curr + h_prev
        k_prev, k_curr = k_curr, a * k_curr + k_prev
        convergents.append((h_curr, k_curr))
    return convergents


# Precompute convergents of log2(3) once
_CONVERGENTS = _cf_convergents(CF_LOG2_3)


def _cf_distance_and_pq(k: int) -> Tuple[float, int]:
    """
    For a given k, find the nearest convergent denominator q_n of log2(3)
    and return (|k - q_n|, partial quotient a_{n+1} active at k).
    """
    best_dist = float("inf")
    best_pq = 1
    for idx, (p, q) in enumerate(_CONVERGENTS):
        dist = abs(k - q)
        if dist < best_dist:
            best_dist = dist
            # The "active" partial quotient is the next one (a_{n+1})
            best_pq = CF_LOG2_3[idx + 1] if idx + 1 < len(CF_LOG2_3) else 1
    return float(best_dist), best_pq


def _corrsum_min(k: int, S: int) -> int:
    """corrSum for the minimum composition (1, 1, ..., 1, S-k+1)."""
    total = 0
    for i in range(k - 1):
        total += 3 ** (k - 1 - i) * 2  # a_i = 1
    total += 2 ** (S - k + 1)           # a_{k-1} = S - k + 1, weight 3^0 = 1
    return total


def _corrsum_max(k: int, S: int) -> int:
    """corrSum for the flat composition (q, q, ..., q+1, ..., q+1)."""
    q, r = divmod(S, k)
    total = 0
    for i in range(k - r):
        total += 3 ** (k - 1 - i) * (1 << q)
    for i in range(k - r, k):
        total += 3 ** (k - 1 - i) * (1 << (q + 1))
    return total


def _rho_bound_for_prime(p: int) -> Tuple[float, int]:
    """
    Character sum bound: rho <= sqrt(p) / q where q = ord_p(2).
    Returns (rho_bound, k_min).
    """
    if p < 5:
        return 0.99, 3
    q = _multiplicative_order(2, p)
    if q == 0:
        return 0.99, 999
    sqrt_p = math.sqrt(float(p))
    rho = sqrt_p / float(q)
    if rho >= 1.0:
        return rho, 999999
    k_min = max(3, math.ceil(1 + math.log(float(q)) / math.log(1.0 / rho)))
    return rho, k_min


# =====================================================================
#  Data structure
# =====================================================================

@dataclass
class KFeatures:
    """All 15 features and 3 target variables for a single k value."""
    # --- Features ---
    k: int
    r_excess: int             # S(k) - k
    r_mod: int                # r % k
    delta_frac: float         # S/k - log2(3)
    log_d: float              # log2(d(k))
    n_prime_factors: int      # distinct prime factors of d(k)
    smallest_pf: int          # smallest prime factor of d(k)
    largest_pf: int           # largest prime factor of d(k) (within trial limit)
    cf_distance: float        # distance to nearest CF convergent denominator
    cf_partial_quotient: int  # active partial quotient at k
    frac_k_alpha: float       # {k * log2(3)} (fractional part)
    plateau_length: int       # 2k - S (forced flatness)
    range_over_d: float       # range(k) / d(k)
    rho_best: float           # best rho_p over prime factors of d(k)
    k_min_best: int           # smallest k_min(p) over prime factors of d(k)

    # --- Targets ---
    theta: float              # (cs_max mod d) / d
    log_margin: float         # log10(theta / (range/d)), or -inf if theta==0
    is_tight: bool            # True if log_margin < median

    def feature_vector(self) -> List[float]:
        """Return the 15 features as a flat list of floats.

        Large integers (smallest_pf, largest_pf, k_min_best) are log-transformed
        to avoid float32 overflow in sklearn. range_over_d is log-transformed
        to avoid underflow for large k.
        """
        # Safe log for potentially huge or zero values
        def _safe_log2(x: float) -> float:
            if x <= 0:
                return 0.0
            try:
                return math.log2(x)
            except (ValueError, OverflowError):
                return 0.0

        rod = self.range_over_d
        log_rod = math.log10(rod) if rod > 0 else -30.0

        return [
            float(self.k),
            float(self.r_excess),
            float(self.r_mod),
            self.delta_frac,
            self.log_d,
            float(self.n_prime_factors),
            _safe_log2(float(self.smallest_pf)),   # log2(smallest_pf)
            _safe_log2(float(self.largest_pf)),     # log2(largest_pf)
            self.cf_distance,
            float(self.cf_partial_quotient),
            self.frac_k_alpha,
            float(self.plateau_length),
            log_rod,                                # log10(range/d)
            self.rho_best,
            min(float(self.k_min_best), 999.0),     # cap k_min_best
        ]


# =====================================================================
#  Main class
# =====================================================================

class DaviesAttribution:
    """
    Davies-style ML attribution for Collatz Range Exclusion tightness.

    Pipeline:
      1. Extract 15 features for each k in [k_min, k_max]
      2. Train a model to predict tightness (regression on log_margin
         or classification on is_tight)
      3. Extract and rank feature importances
      4. Saliency analysis on the tightest k values
      5. Pattern discovery from the attribution

    If scikit-learn is available, uses GradientBoostingRegressor.
    Otherwise, falls back to Pearson + Spearman rank correlation analysis.
    """

    def __init__(self, k_min: int = 3, k_max: int = 200):
        self.k_min = k_min
        self.k_max = k_max
        self.data: List[KFeatures] = []
        self.importances: Dict[str, float] = {}
        self._model = None
        self._has_sklearn = False

    # -----------------------------------------------------------------
    #  Step 1: Feature extraction
    # -----------------------------------------------------------------

    def extract_features(self) -> List[KFeatures]:
        """
        Compute all 15 features and 3 targets for each k in [k_min, k_max].
        Skips k=4 (phantom cycle).
        """
        raw_data = []
        log_margins = []

        for k in range(self.k_min, self.k_max + 1):
            if k == 4:
                continue

            S = _compute_S(k)
            d = _compute_d(k)
            if d <= 0:
                continue

            # --- Basic features ---
            r_excess = S - k
            r_mod = r_excess % k
            delta_frac = S / k - LOG2_3
            log_d = math.log2(float(d)) if d > 0 else 0.0
            plateau_length = 2 * k - S

            # --- Prime factor features ---
            factors = _factorize(d)
            primes = [p for p, _ in factors]
            n_prime_factors = len(primes)
            smallest_pf = min(primes) if primes else 1
            largest_pf = max(primes) if primes else 1

            # --- Continued fraction features ---
            cf_dist, cf_pq = _cf_distance_and_pq(k)
            frac_k_alpha = (k * LOG2_3) - math.floor(k * LOG2_3)

            # --- Range exclusion features ---
            cs_max = _corrsum_max(k, S)
            cs_min = _corrsum_min(k, S)
            range_width = cs_max - cs_min
            range_over_d_val = float(range_width) / float(d) if d > 0 else 0.0

            # --- Spectral features (rho, k_min) ---
            best_rho = 0.99
            best_kmin = 999
            for p in primes:
                if p < 5:
                    continue
                try:
                    rho_p, kmin_p = _rho_bound_for_prime(p)
                    if rho_p < best_rho:
                        best_rho = rho_p
                    if kmin_p < best_kmin:
                        best_kmin = kmin_p
                except Exception:
                    pass

            # --- Targets ---
            theta = float(cs_max % d) / float(d)
            if theta > 0 and range_over_d_val > 0:
                log_margin = math.log10(theta / range_over_d_val)
            else:
                log_margin = -20.0  # sentinel for theta=0 or range=0

            log_margins.append(log_margin)

            kf = KFeatures(
                k=k, r_excess=r_excess, r_mod=r_mod,
                delta_frac=delta_frac, log_d=log_d,
                n_prime_factors=n_prime_factors,
                smallest_pf=smallest_pf, largest_pf=largest_pf,
                cf_distance=cf_dist, cf_partial_quotient=cf_pq,
                frac_k_alpha=frac_k_alpha,
                plateau_length=plateau_length,
                range_over_d=range_over_d_val,
                rho_best=best_rho, k_min_best=best_kmin,
                theta=theta, log_margin=log_margin, is_tight=False,
            )
            raw_data.append(kf)

        # Compute median log_margin and set is_tight
        if log_margins:
            med = statistics.median(log_margins)
            for kf in raw_data:
                kf.is_tight = kf.log_margin < med

        self.data = raw_data
        return self.data

    # -----------------------------------------------------------------
    #  Step 2: Model training
    # -----------------------------------------------------------------

    def train_model(self) -> str:
        """
        Train a model to predict log_margin from the 15 features.

        Tries sklearn GradientBoostingRegressor first, falls back to
        correlation-based importance if sklearn is unavailable.

        Returns a string describing the method used.
        """
        if not self.data:
            self.extract_features()

        X = [kf.feature_vector() for kf in self.data]
        y = [kf.log_margin for kf in self.data]

        try:
            from sklearn.ensemble import GradientBoostingRegressor
            from sklearn.model_selection import cross_val_score
            import numpy as np

            X_arr = np.array(X)
            y_arr = np.array(y)

            model = GradientBoostingRegressor(
                n_estimators=200, max_depth=4, learning_rate=0.05,
                subsample=0.8, random_state=42,
            )
            scores = cross_val_score(model, X_arr, y_arr, cv=5,
                                     scoring="neg_mean_squared_error")
            model.fit(X_arr, y_arr)

            self._model = model
            self._has_sklearn = True
            self.importances = {
                name: float(imp)
                for name, imp in zip(FEATURE_NAMES, model.feature_importances_)
            }
            rmse = float(np.sqrt(-scores.mean()))
            return (f"GradientBoosting (200 trees, depth 4), "
                    f"5-fold CV RMSE = {rmse:.4f}")

        except ImportError:
            return self._correlation_fallback(X, y)

    def _correlation_fallback(self, X: List[List[float]],
                              y: List[float]) -> str:
        """
        Fallback: rank features by |Pearson| + |Spearman| correlation
        with the target (log_margin).
        """
        n = len(y)
        if n < 5:
            return "Too few data points for correlation analysis."

        def _pearson(a: List[float], b: List[float]) -> float:
            ma = sum(a) / len(a)
            mb = sum(b) / len(b)
            cov = sum((ai - ma) * (bi - mb) for ai, bi in zip(a, b))
            sa = math.sqrt(sum((ai - ma) ** 2 for ai in a))
            sb = math.sqrt(sum((bi - mb) ** 2 for bi in b))
            if sa == 0 or sb == 0:
                return 0.0
            return cov / (sa * sb)

        def _rank(vals: List[float]) -> List[float]:
            indexed = sorted(enumerate(vals), key=lambda x: x[1])
            ranks = [0.0] * len(vals)
            for rank, (idx, _) in enumerate(indexed):
                ranks[idx] = float(rank)
            return ranks

        def _spearman(a: List[float], b: List[float]) -> float:
            return _pearson(_rank(a), _rank(b))

        combined = {}
        for j, name in enumerate(FEATURE_NAMES):
            col = [X[i][j] for i in range(n)]
            pc = abs(_pearson(col, y))
            sc = abs(_spearman(col, y))
            combined[name] = (pc + sc) / 2.0

        # Normalize to sum=1
        total = sum(combined.values())
        if total > 0:
            self.importances = {k: v / total for k, v in combined.items()}
        else:
            self.importances = {k: 1.0 / len(combined) for k in combined}

        self._has_sklearn = False
        return "Correlation-based (Pearson + Spearman average, normalized)"

    # -----------------------------------------------------------------
    #  Step 3: Feature importance
    # -----------------------------------------------------------------

    def feature_importance(self) -> Dict[str, float]:
        """
        Return feature importances sorted by descending importance.
        Must call train_model() first.
        """
        if not self.importances:
            self.train_model()
        return dict(sorted(self.importances.items(),
                           key=lambda x: -x[1]))

    # -----------------------------------------------------------------
    #  Step 4: Saliency analysis
    # -----------------------------------------------------------------

    def saliency_analysis(self, top_n: int = 10) -> str:
        """
        For the top_n tightest k values, analyze which features contribute
        most to their tightness.

        If sklearn is available, uses model prediction decomposition.
        Otherwise, identifies which features are anomalous (>1.5 sigma
        from the mean) for each tight k.
        """
        if not self.data:
            self.extract_features()
        if not self.importances:
            self.train_model()

        # Sort by log_margin ascending (tightest first)
        tight = sorted(self.data, key=lambda kf: kf.log_margin)[:top_n]

        # Compute feature statistics (mean, std)
        n = len(self.data)
        feat_stats: Dict[str, Tuple[float, float]] = {}
        for j, name in enumerate(FEATURE_NAMES):
            vals = [self.data[i].feature_vector()[j] for i in range(n)]
            mu = sum(vals) / n
            var = sum((v - mu) ** 2 for v in vals) / max(n - 1, 1)
            feat_stats[name] = (mu, math.sqrt(var))

        lines = []
        lines.append(f"SALIENCY ANALYSIS — Top {top_n} tightest k values")
        lines.append("=" * 72)

        ranked_feats = sorted(self.importances.items(), key=lambda x: -x[1])

        for kf in tight:
            vec = kf.feature_vector()
            anomalies = []
            for j, name in enumerate(FEATURE_NAMES):
                mu, sigma = feat_stats[name]
                if sigma > 1e-12:
                    z = (vec[j] - mu) / sigma
                    if abs(z) > 1.5:
                        anomalies.append((name, z, vec[j]))

            anomalies.sort(key=lambda x: -abs(x[1]))
            top_anomalies = anomalies[:5]

            lines.append(
                f"\n  k={kf.k:3d}  theta={kf.theta:.6f}  "
                f"log_margin={kf.log_margin:+.3f}  "
                f"tight={'YES' if kf.is_tight else 'no '}"
            )
            if top_anomalies:
                for name, z, val in top_anomalies:
                    imp = self.importances.get(name, 0)
                    direction = "HIGH" if z > 0 else "LOW"
                    lines.append(
                        f"    -> {name:22s}  z={z:+.2f} ({direction})  "
                        f"val={val:.4g}  importance={imp:.4f}"
                    )
            else:
                lines.append("    -> No anomalous features (all within 1.5 sigma)")

        return "\n".join(lines)

    # -----------------------------------------------------------------
    #  Step 5: Pattern discovery
    # -----------------------------------------------------------------

    def pattern_discovery(self) -> str:
        """
        Identify mathematical patterns from the attribution analysis.

        Looks for:
        - CF convergent proximity effect (do convergent denominators produce tight k?)
        - Delta-frac clustering (is tightness governed by {k*alpha}?)
        - Prime factor structure (do specific prime factors cause tightness?)
        - Plateau effect (does 2k-S correlate with tightness?)
        """
        if not self.data:
            self.extract_features()
        if not self.importances:
            self.train_model()

        lines = []
        lines.append("PATTERN DISCOVERY")
        lines.append("=" * 72)

        tight_set = [kf for kf in self.data if kf.is_tight]
        easy_set = [kf for kf in self.data if not kf.is_tight]

        # --- Pattern 1: CF convergent proximity ---
        lines.append("\n[1] CONTINUED FRACTION PROXIMITY")
        tight_cf = [kf.cf_distance for kf in tight_set]
        easy_cf = [kf.cf_distance for kf in easy_set]
        if tight_cf and easy_cf:
            mean_tight = sum(tight_cf) / len(tight_cf)
            mean_easy = sum(easy_cf) / len(easy_cf)
            lines.append(f"    Mean CF distance:  tight={mean_tight:.2f}  "
                         f"easy={mean_easy:.2f}")
            if mean_tight < mean_easy * 0.8:
                lines.append("    --> SIGNAL: tight k values cluster near CF "
                             "convergent denominators")
            else:
                lines.append("    --> No strong CF proximity effect detected")

        # --- Pattern 2: Fractional part {k*alpha} ---
        lines.append("\n[2] FRACTIONAL PART {k * log2(3)}")
        tight_frac = [kf.frac_k_alpha for kf in tight_set]
        easy_frac = [kf.frac_k_alpha for kf in easy_set]
        if tight_frac and easy_frac:
            mean_t = sum(tight_frac) / len(tight_frac)
            mean_e = sum(easy_frac) / len(easy_frac)
            # Check if tight k cluster near 0 or 1 (small fractional excess)
            tight_near_0 = sum(1 for f in tight_frac if f < 0.15 or f > 0.85)
            easy_near_0 = sum(1 for f in easy_frac if f < 0.15 or f > 0.85)
            frac_tight = tight_near_0 / max(len(tight_frac), 1)
            frac_easy = easy_near_0 / max(len(easy_frac), 1)
            lines.append(f"    Mean {{k*alpha}}:  tight={mean_t:.4f}  "
                         f"easy={mean_e:.4f}")
            lines.append(f"    Near 0 or 1 (within 0.15):  "
                         f"tight={frac_tight:.1%}  easy={frac_easy:.1%}")
            if frac_tight > frac_easy * 1.5:
                lines.append("    --> SIGNAL: tight k have small fractional "
                             "excess (near integer multiple of log2(3))")

        # --- Pattern 3: Prime factor structure ---
        lines.append("\n[3] PRIME FACTOR STRUCTURE")
        tight_npf = [kf.n_prime_factors for kf in tight_set]
        easy_npf = [kf.n_prime_factors for kf in easy_set]
        if tight_npf and easy_npf:
            mean_t_npf = sum(tight_npf) / len(tight_npf)
            mean_e_npf = sum(easy_npf) / len(easy_npf)
            lines.append(f"    Mean # prime factors:  tight={mean_t_npf:.2f}  "
                         f"easy={mean_e_npf:.2f}")
            tight_small_pf = [kf.smallest_pf for kf in tight_set]
            easy_small_pf = [kf.smallest_pf for kf in easy_set]
            med_t = statistics.median(tight_small_pf) if tight_small_pf else 0
            med_e = statistics.median(easy_small_pf) if easy_small_pf else 0
            lines.append(f"    Median smallest pf:   tight={med_t:.0f}  "
                         f"easy={med_e:.0f}")

        # --- Pattern 4: Plateau length ---
        lines.append("\n[4] PLATEAU LENGTH (2k - S)")
        tight_pl = [kf.plateau_length for kf in tight_set]
        easy_pl = [kf.plateau_length for kf in easy_set]
        if tight_pl and easy_pl:
            from collections import Counter
            ct = Counter(tight_pl)
            ce = Counter(easy_pl)
            lines.append(f"    Tight distribution:  {dict(ct.most_common(5))}")
            lines.append(f"    Easy distribution:   {dict(ce.most_common(5))}")
            # plateau_length = 2k - S = 2k - ceil(k*log2(3))
            # This is k*(2 - log2(3)) - {k*log2(3)} ~ 0.415*k
            # So the interesting quantity is plateau_length mod something

        # --- Pattern 5: Range/d ratio ---
        lines.append("\n[5] RANGE/d RATIO (exponential decay)")
        tight_rod = sorted([kf.range_over_d for kf in tight_set], reverse=True)
        easy_rod = sorted([kf.range_over_d for kf in easy_set], reverse=True)
        if tight_rod and easy_rod:
            lines.append(f"    Max range/d:  tight={tight_rod[0]:.6e}  "
                         f"easy={easy_rod[0]:.6e}")
            lines.append(f"    Mean range/d: tight="
                         f"{sum(tight_rod)/len(tight_rod):.6e}  "
                         f"easy={sum(easy_rod)/len(easy_rod):.6e}")

        # --- Pattern 6: rho_best ---
        lines.append("\n[6] SPECTRAL CONTRACTION (rho_best)")
        tight_rho = [kf.rho_best for kf in tight_set]
        easy_rho = [kf.rho_best for kf in easy_set]
        if tight_rho and easy_rho:
            mean_tr = sum(tight_rho) / len(tight_rho)
            mean_er = sum(easy_rho) / len(easy_rho)
            lines.append(f"    Mean rho_best:  tight={mean_tr:.4f}  "
                         f"easy={mean_er:.4f}")
            if mean_tr > mean_er * 1.1:
                lines.append("    --> SIGNAL: tight k have weaker spectral "
                             "contraction (higher rho)")

        return "\n".join(lines)

    # -----------------------------------------------------------------
    #  Step 6: Recommendations
    # -----------------------------------------------------------------

    def recommendations(self) -> str:
        """
        Based on feature importance and pattern analysis, recommend where
        to focus proof efforts.
        """
        if not self.importances:
            self.train_model()

        ranked = sorted(self.importances.items(), key=lambda x: -x[1])
        top3 = [name for name, _ in ranked[:3]]

        lines = []
        lines.append("RECOMMENDATIONS FOR PROOF EFFORTS")
        lines.append("=" * 72)

        # Map feature names to mathematical directions
        directions = {
            "cf_distance": (
                "Continued fraction theory: the tightest k values cluster "
                "near convergent denominators of log2(3). Strengthening "
                "Diophantine approximation bounds (a la Baker/Rhin-Viola) "
                "would directly improve Range Exclusion margins."
            ),
            "frac_k_alpha": (
                "Three-distance theorem / equidistribution: the fractional "
                "part {k*alpha} controls tightness. Bounds on ||k*alpha|| "
                "(Dirichlet/Thue-Siegel-Roth) translate to Range Exclusion "
                "safety margins."
            ),
            "delta_frac": (
                "Delta = S/k - log2(3) measures the fractional excess. "
                "Small delta means d(k) is small relative to 3^k, making "
                "range exclusion harder. Focus on k where delta is minimal."
            ),
            "rho_best": (
                "Spectral contraction: improving universal rho bounds for "
                "character sums over multiplicative subgroups would "
                "strengthen the FCQ regime."
            ),
            "log10_range_over_d": (
                "Range/d ratio: this is the core Range Exclusion quantity. "
                "Tighter asymptotic bounds on the range shrinkage rate "
                "would close the argument."
            ),
            "log_d": (
                "Size of d(k): larger d(k) means more multiples to avoid. "
                "Understanding the arithmetic of d(k) = 2^S - 3^k (a "
                "Pillai-type equation) is key."
            ),
            "n_prime_factors": (
                "Number of prime factors: CRT coverage depends on having "
                "enough small prime factors with good spectral properties. "
                "Smooth d(k) values are easier."
            ),
            "plateau_length": (
                "Plateau = 2k - S: controls how 'balanced' compositions can "
                "be. Smaller plateau means the flat composition is closer to "
                "the extremal one, compressing the range."
            ),
            "k_min_best": (
                "k_min threshold: improving the k_min bound (from LDS or "
                "character sum refinements) directly extends the FCQ regime."
            ),
        }

        lines.append(f"\n  Top 3 features driving tightness:")
        for i, name in enumerate(top3):
            imp = self.importances[name]
            lines.append(f"\n  [{i+1}] {name} (importance = {imp:.4f})")
            if name in directions:
                lines.append(f"      {directions[name]}")

        # Identify hardest k values
        hardest = sorted(self.data, key=lambda kf: kf.log_margin)[:5]
        lines.append(f"\n  Hardest k values (smallest safety margin):")
        for kf in hardest:
            lines.append(
                f"    k={kf.k:3d}  log_margin={kf.log_margin:+.3f}  "
                f"theta={kf.theta:.6f}  rho_best={kf.rho_best:.4f}"
            )

        lines.append(
            f"\n  STRATEGIC SUMMARY: The proof should prioritize understanding "
            f"the role of '{top3[0]}' in Range Exclusion. If this feature also "
            f"appears as a dominant pattern in the saliency analysis, it "
            f"suggests a unified Diophantine/spectral approach."
        )

        return "\n".join(lines)

    # -----------------------------------------------------------------
    #  Full report
    # -----------------------------------------------------------------

    def report(self) -> str:
        """
        Generate the full Davies attribution report.

        Runs the entire pipeline: extract -> train -> importance ->
        saliency -> patterns -> recommendations.
        """
        sections = []

        # Header
        sections.append(
            "+" + "=" * 72 + "+\n"
            "|  DAVIES-STYLE ATTRIBUTION — Collatz Range Exclusion Tightness"
            "        |\n"
            "|  Inspired by Davies et al., Nature 600 (2021)"
            "                        |\n"
            "+" + "=" * 72 + "+"
        )

        # Step 1
        data = self.extract_features()
        sections.append(f"\n[STEP 1] Feature extraction: {len(data)} k values "
                        f"(k={self.k_min}..{self.k_max}, excluding k=4)\n")

        # Step 2
        method = self.train_model()
        sections.append(f"[STEP 2] Model: {method}\n")

        # Step 3
        ranked = self.feature_importance()
        sections.append("[STEP 3] FEATURE IMPORTANCE RANKING")
        sections.append("-" * 50)
        for i, (name, imp) in enumerate(ranked.items()):
            bar = "#" * int(imp * 100)
            sections.append(f"  {i+1:2d}. {name:22s}  {imp:.4f}  {bar}")
        sections.append("")

        # Step 4
        sections.append(self.saliency_analysis(top_n=10))
        sections.append("")

        # Step 5
        sections.append(self.pattern_discovery())
        sections.append("")

        # Step 6
        sections.append(self.recommendations())

        # Footer
        n_tight = sum(1 for kf in self.data if kf.is_tight)
        sections.append(
            f"\n+" + "=" * 72 + "+\n"
            f"|  {n_tight} tight / {len(self.data)} total  |  "
            f"Method: {'sklearn GB' if self._has_sklearn else 'correlation'}  "
            f"|  k range: [{self.k_min}, {self.k_max}]"
            f"\n+" + "=" * 72 + "+"
        )

        return "\n".join(sections)


# =====================================================================
#  Main
# =====================================================================

if __name__ == "__main__":
    import sys

    k_min = 3
    k_max = 200
    if len(sys.argv) > 1:
        k_max = int(sys.argv[1])
    if len(sys.argv) > 2:
        k_min = int(sys.argv[2])

    attribution = DaviesAttribution(k_min=k_min, k_max=k_max)
    print(attribution.report())
