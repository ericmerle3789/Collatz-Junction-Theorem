#!/usr/bin/env python3
"""
r92_test_t4.py — Test conjecture T4 for k=21, p=5, r=ord_5(2)=4.

Setup:
  p=5, k=21, S=ceil(21*log2(3))=34, N=S-k=13
  H = {1,2,4,3} mod 5  (powers of 2 mod 5)
  r = 4 = ord_5(2)
  alpha_i = 3^{20-i} mod 5 for i=0,...,20

We use character orthogonality to compute:
  N_H(0) = (1/p) sum_{t=0}^{p-1} prod_{i=0}^{k-1} sigma_i(t)
  where sigma_i(t) = sum_{h in H} e_5(t * alpha_i * h)

Then for each ell in {1,2,3}, compute weighted sums W_ell and check |W_ell/(p*N_H(0))| < 1.
"""

import numpy as np
from math import ceil, log2

# ── Parameters ──
p = 5
k = 21
S = ceil(k * log2(3))
N = S - k
r = 4  # ord_5(2)

print(f"Parameters: p={p}, k={k}, S={S}, N={N}, r={r}")
print(f"|H^k| = {r}^{k} = {r**k} ≈ {r**k:.3e}")
print()

# ── H = {2^b mod 5 : b=0,...,r-1} ──
H = [pow(2, b, p) for b in range(r)]
print(f"H = {H} mod {p}")

# ── alpha_i = 3^{20-i} mod 5 ──
alpha = [pow(3, 20 - i, p) for i in range(k)]
print(f"alpha = {alpha}")

# Check period of 3 mod 5: 3^1=3, 3^2=4, 3^3=2, 3^4=1
print(f"Period of 3 mod 5: {[pow(3, j, p) for j in range(1, 6)]}")
print()

# ── Helper: e_p(x) = exp(2*pi*i*x/p) ──
def e_p(x):
    return np.exp(2j * np.pi * x / p)

# ── Step 2: Compute N_H(0) via character orthogonality ──
# sigma_i(t) = sum_{h in H} e_p(t * alpha_i * h)
def sigma(i, t):
    return sum(e_p(t * alpha[i] * h) for h in H)

# N_H(0) = (1/p) sum_t prod_i sigma_i(t)
total = 0.0 + 0j
for t in range(p):
    prod_val = 1.0 + 0j
    for i in range(k):
        prod_val *= sigma(i, t)
    total += prod_val

N_H_0 = total / p
print("=" * 60)
print("STEP 2: N_H(0) — number of zero-sum tuples")
print("=" * 60)
print(f"N_H(0) = {N_H_0.real:.6f} + {N_H_0.imag:.6f}i")
print(f"N_H(0) (rounded) = {round(N_H_0.real)}")
print(f"r^k / p = {r**k} / {p} = {r**k / p:.1f}")
print(f"Ratio N_H(0) / (r^k/p) = {N_H_0.real / (r**k / p):.10f}")
print()

# Sanity: imaginary part should be ~0
assert abs(N_H_0.imag) < 1e-3, f"Imaginary part too large: {N_H_0.imag}"
N_H_0_val = round(N_H_0.real)

# ── Step 3: Compute W_ell for ell=1,2,3 ──
# omega_4 = exp(2*pi*i/4) = i
omega_4 = np.exp(2j * np.pi / 4)  # = i

def S_i_ell(i, ell, t):
    """S_i^{(ell)}(t) = sum_{b=0}^{r-1} omega_4^{ell*b} * e_p(t * alpha_i * 2^b)"""
    val = 0.0 + 0j
    for b in range(r):
        h_b = H[b]  # 2^b mod p
        val += (omega_4 ** (ell * b)) * e_p(t * alpha[i] * h_b)
    return val

print("=" * 60)
print("STEP 3: Weighted sums W_ell for ell = 1, 2, 3")
print("=" * 60)

results = {}
for ell in range(1, 4):
    W_ell = 0.0 + 0j
    for t in range(p):
        prod_val = 1.0 + 0j
        for i in range(k):
            prod_val *= S_i_ell(i, ell, t)
        W_ell += prod_val

    abs_W = abs(W_ell)
    ratio = abs_W / (p * abs(N_H_0.real))
    results[ell] = (W_ell, abs_W, ratio)

    print(f"\nell = {ell}:")
    print(f"  W_{ell} = {W_ell.real:.6f} + {W_ell.imag:.6f}i")
    print(f"  |W_{ell}| = {abs_W:.6f}")
    print(f"  p * N_H(0) = {p * N_H_0.real:.6f}")
    print(f"  |W_{ell}| / (p * N_H(0)) = {ratio:.10f}")

# ── Step 4: Summary and conjecture verification ──
print()
print("=" * 60)
print("STEP 4: Summary and T4 conjecture verification")
print("=" * 60)
print(f"\nN_H(0)       = {N_H_0_val}")
print(f"r^k/p        = {r**k/p:.1f}")
print(f"Expected main term r^k/p = 4^21/5 = {4**21//5} (integer part)")
print()

print(f"{'ell':>4} | {'|W_ell|':>20} | {'|W_ell/(p*N_H(0))|':>22} | {'T4 holds?':>10}")
print("-" * 65)

all_pass = True
for ell in range(1, 4):
    W_ell, abs_W, ratio = results[ell]
    holds = ratio < 1.0
    all_pass = all_pass and holds
    print(f"{ell:>4} | {abs_W:>20.6f} | {ratio:>22.10f} | {'PASS' if holds else 'FAIL':>10}")

print()
if all_pass:
    print("✓ CONJECTURE T4 HOLDS for k=21, p=5, r=4: all |W_ell/(p*N_H(0))| < 1")
else:
    print("✗ CONJECTURE T4 FAILS for k=21, p=5, r=4")

# ── Bonus: show the t=0 terms and individual factor magnitudes ──
print()
print("=" * 60)
print("DETAIL: Factor magnitudes |sigma_i(t)| for each t")
print("=" * 60)
for t in range(p):
    mags = [abs(sigma(i, t)) for i in range(k)]
    prod_mag = np.prod(mags)
    print(f"  t={t}: prod |sigma_i(t)| = {prod_mag:.6e},  min|sigma|={min(mags):.6f}, max|sigma|={max(mags):.6f}")

print()
print("=" * 60)
print("DETAIL: Factor magnitudes |S_i^(ell)(t)| for each t, ell")
print("=" * 60)
for ell in range(1, 4):
    for t in range(p):
        mags = [abs(S_i_ell(i, ell, t)) for i in range(k)]
        prod_mag = np.prod(mags)
        print(f"  ell={ell}, t={t}: prod |S_i^(ell)(t)| = {prod_mag:.6e},  min={min(mags):.6f}, max={max(mags):.6f}")
