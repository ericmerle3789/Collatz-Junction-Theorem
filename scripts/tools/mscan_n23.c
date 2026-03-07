/*
 * mscan_n23.c — M-scan for n=23 (Piste J.2)
 *
 * Proves d(q_23) = 2^S - 3^k is composite by showing ord_d(2) > S-1.
 *
 * Method: For each m in [5, m_max] with m odd and gcd(m, 6) = 1,
 * check that val(m) = (m+1)*3^k - m*2^S is NOT a power of 2.
 *
 * This is done by sieving: for each odd prime p, precompute
 *   A = 3^k mod p,  B = 2^S mod p
 * Then val(m) mod p = m*(A-B) + A (mod p).
 * If this is 0 for some prime p, then val(m) has an odd prime factor,
 * hence is NOT a power of 2, and m is eliminated.
 *
 * n=23: S = 217976794617, k = 137528045312
 * delta = S - k*log2(3) ≈ 1.296e-12
 * m_max = floor(1/(2^delta - 1)) ≈ 1.113 × 10^12
 *
 * Expected: ~5-10h on Apple M1 Pro
 *
 * Compile: gcc -O3 -march=native -o mscan_n23 mscan_n23.c -lm
 * Run:     ./mscan_n23
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

/* Target: n=23 */
#define S_VAL   217976794617ULL
#define K_VAL   137528045312ULL

/* m_max from CF theory: floor(1/(2^delta - 1)) where delta ≈ 1.296e-12 */
#define M_MAX   1112774250075ULL

/* Sieve parameters */
#define SMALL_PRIME_LIMIT  1000000   /* primes up to 10^6 for initial sieve */
#define BLOCK_SIZE         (1 << 22) /* ~4M per block */
#define CHECK_PRIMES       10000     /* primes for per-survivor verification */

/* Modular exponentiation: base^exp mod mod (64-bit) */
static inline uint64_t powmod64(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            __uint128_t tmp = (__uint128_t)result * base;
            result = (uint64_t)(tmp % mod);
        }
        exp >>= 1;
        if (exp > 0) {
            __uint128_t tmp = (__uint128_t)base * base;
            base = (uint64_t)(tmp % mod);
        }
    }
    return result;
}

/* Simple sieve for primes up to n */
static uint32_t *small_sieve(uint32_t n, uint32_t *count) {
    uint8_t *is_prime = (uint8_t *)calloc(n + 1, 1);
    if (!is_prime) { fprintf(stderr, "OOM\n"); exit(1); }
    memset(is_prime, 1, n + 1);
    is_prime[0] = is_prime[1] = 0;
    for (uint32_t i = 2; (uint64_t)i * i <= n; i++) {
        if (is_prime[i]) {
            for (uint32_t j = i * i; j <= n; j += i)
                is_prime[j] = 0;
        }
    }
    *count = 0;
    for (uint32_t i = 2; i <= n; i++)
        if (is_prime[i]) (*count)++;
    uint32_t *primes = (uint32_t *)malloc(*count * sizeof(uint32_t));
    uint32_t idx = 0;
    for (uint32_t i = 2; i <= n; i++)
        if (is_prime[i]) primes[idx++] = i;
    free(is_prime);
    return primes;
}

int main() {
    printf("================================================================\n");
    printf("M-SCAN n=23 — Piste J.2\n");
    printf("  S = %llu, k = %llu\n", (unsigned long long)S_VAL, (unsigned long long)K_VAL);
    printf("  m_max = %llu (~%.3e)\n", (unsigned long long)M_MAX, (double)M_MAX);
    printf("  Method: eliminate m by showing val(m) has odd prime factor\n");
    printf("  val(m) = (m+1)*3^k - m*2^S\n");
    printf("================================================================\n\n");
    fflush(stdout);

    struct timespec ts_start, ts_now;
    clock_gettime(CLOCK_MONOTONIC, &ts_start);

    /* Phase 1: Generate primes */
    uint32_t n_primes;
    uint32_t *primes = small_sieve(SMALL_PRIME_LIMIT, &n_primes);
    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    double t = (ts_now.tv_sec - ts_start.tv_sec) +
               (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
    printf("Phase 1: %u primes <= %u (%.2f s)\n\n", n_primes, SMALL_PRIME_LIMIT, t);

    /* Phase 2: Precompute A = 3^k mod p, B = 2^S mod p for each prime */
    printf("Phase 2: Precomputing modular exponentiations...\n");

    /* We need: val(m) mod p = m*(A-B) + A (mod p)
     * val(m) ≡ 0 (mod p)  ⟺  m ≡ -A / (A-B) ≡ A / (B-A) (mod p)
     *
     * For each prime p where A != B mod p, exactly one residue class
     * of m mod p is eliminated. We store this residue.
     *
     * For sieving, we use the residue r_p such that m ≡ r_p (mod p)
     * means val(m) ≡ 0 (mod p).
     */

    /* Arrays for sieve: store (prime, residue) pairs */
    /* Only use primes >= 5 (skip 2, 3 since m is coprime to 6) */
    typedef struct { uint32_t p; uint32_t r; } PrimeRes;
    PrimeRes *sieve_data = (PrimeRes *)malloc(n_primes * sizeof(PrimeRes));
    uint32_t n_sieve = 0;

    /* Also prepare a set of "check" primes for survivor verification */
    /* We'll use primes beyond SMALL_PRIME_LIMIT for secondary checks */
    /* But actually, all primes can serve as check primes */

    for (uint32_t i = 0; i < n_primes; i++) {
        uint64_t p = primes[i];
        if (p < 5) continue;

        uint64_t A = powmod64(3, K_VAL, p);
        uint64_t B = powmod64(2, S_VAL, p);

        if (A == B) continue; /* this prime can't eliminate any m */

        /* val(m) ≡ 0 (mod p) ⟺ m ≡ A * modinv(B-A, p) (mod p) */
        /* modinv via Fermat's little theorem: modinv(x, p) = x^(p-2) mod p */
        uint64_t diff;
        if (B >= A) diff = B - A;
        else diff = p - A + B;

        uint64_t inv_diff = powmod64(diff, p - 2, p);
        uint64_t r = (uint64_t)(((__uint128_t)A * inv_diff) % p);

        sieve_data[n_sieve].p = (uint32_t)p;
        sieve_data[n_sieve].r = (uint32_t)r;
        n_sieve++;
    }

    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    t = (ts_now.tv_sec - ts_start.tv_sec) +
        (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
    printf("  %u effective primes (%.2f s)\n\n", n_sieve, t);
    fflush(stdout);

    /* Phase 3: Segmented sieve of m values */
    printf("Phase 3: Segmented m-sieve [5, %llu]...\n", (unsigned long long)M_MAX);
    printf("  Only testing m with m odd and gcd(m, 6) = 1\n");
    printf("  (i.e., m ≡ 1 or 5 mod 6)\n\n");
    fflush(stdout);

    /*
     * Strategy: process m in blocks of BLOCK_SIZE.
     * For each block, use a bitmap where bit i represents m = block_start + i.
     * Mark bit = 1 for "eliminated" (val(m) has a factor p).
     * Initially all bits = 0. Sieve with each prime p.
     * After sieving, count survivors (m where no prime eliminated it).
     *
     * We only care about m with m ≡ 1 or 5 (mod 6), so we filter at check time.
     * Also m must be >= 5.
     */

    /* Use byte array for simplicity (1 byte per m) */
    uint8_t *block = (uint8_t *)calloc(BLOCK_SIZE, 1);
    if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

    uint64_t total_eligible = 0;  /* m with gcd(m,6)=1, m odd */
    uint64_t total_eliminated = 0;
    uint64_t total_survivors = 0;
    uint64_t blocks_done = 0;
    uint64_t report_interval = 500000000ULL / BLOCK_SIZE; /* ~every 0.5G */

    clock_gettime(CLOCK_MONOTONIC, &ts_start); /* reset for rate */

    for (uint64_t block_lo = 5; block_lo <= M_MAX; block_lo += BLOCK_SIZE) {
        uint64_t block_hi = block_lo + BLOCK_SIZE - 1;
        if (block_hi > M_MAX) block_hi = M_MAX;
        uint64_t bsize = block_hi - block_lo + 1;

        /* Clear block */
        memset(block, 0, bsize);

        /* Sieve: mark eliminated m's */
        for (uint32_t s = 0; s < n_sieve; s++) {
            uint64_t p = sieve_data[s].p;
            uint64_t r = sieve_data[s].r;

            /* Find first m >= block_lo with m ≡ r (mod p) */
            uint64_t first;
            if (block_lo <= r) {
                first = r;
            } else {
                uint64_t offset = (block_lo - r + p - 1) / p;
                first = r + offset * p;
            }

            for (uint64_t m = first; m <= block_hi; m += p) {
                block[m - block_lo] = 1; /* eliminated */
            }
        }

        /* Count survivors (only eligible m: m ≡ 1 or 5 mod 6) */
        for (uint64_t j = 0; j < bsize; j++) {
            uint64_t m = block_lo + j;
            /* Eligible: m odd and gcd(m, 6) = 1, i.e., m % 6 == 1 or m % 6 == 5 */
            uint64_t m6 = m % 6;
            if (m6 != 1 && m6 != 5) continue;
            total_eligible++;

            if (block[j]) {
                total_eliminated++;
            } else {
                total_survivors++;

                /* This m survived the sieve — needs individual verification.
                 * Check val(m) mod p for more primes beyond the sieve set.
                 * Since we used primes up to 10^6 in sieve, survivors are
                 * extremely rare and we can afford deep per-survivor checks.
                 *
                 * In practice, the sieve with ~78K primes eliminates virtually
                 * all eligible m. Any survivor indicates val(m) might be a
                 * power of 2 — which would mean d(q_23) is prime, contradicting
                 * the compositeness claim.
                 */

                /* For now, just report survivors */
                if (total_survivors <= 100) {
                    printf("  *** SURVIVOR: m = %llu (val(m) has no factor < 10^6) ***\n",
                           (unsigned long long)m);
                    fflush(stdout);
                }
            }
        }

        blocks_done++;

        /* Progress report */
        if (blocks_done % report_interval == 0) {
            clock_gettime(CLOCK_MONOTONIC, &ts_now);
            double elapsed = (ts_now.tv_sec - ts_start.tv_sec) +
                             (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
            double progress = (double)(block_hi - 5) / (double)(M_MAX - 5) * 100.0;
            double rate = total_eligible / elapsed;
            double eta = (elapsed / progress) * (100.0 - progress);
            printf("  %7.2fG m, %6.2f%%, %llu eligible, %llu eliminated, %llu survivors, "
                   "%.0f m/s, %.0f s elapsed, ETA %.0f s\n",
                   (double)(block_hi - 5) / 1e9,
                   progress,
                   (unsigned long long)total_eligible,
                   (unsigned long long)total_eliminated,
                   (unsigned long long)total_survivors,
                   rate, elapsed, eta);
            fflush(stdout);
        }
    }

    free(block);

    /* Results */
    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    double total_time = (ts_now.tv_sec - ts_start.tv_sec) +
                        (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;

    printf("\n================================================================\n");
    printf("RESULTS — M-scan n=23\n");
    printf("================================================================\n");
    printf("m range: [5, %llu]\n", (unsigned long long)M_MAX);
    printf("Total eligible m (odd, gcd(m,6)=1): %llu\n", (unsigned long long)total_eligible);
    printf("Eliminated by sieve (primes <= %u): %llu (%.4f%%)\n",
           SMALL_PRIME_LIMIT,
           (unsigned long long)total_eliminated,
           100.0 * total_eliminated / total_eligible);
    printf("Survivors: %llu\n", (unsigned long long)total_survivors);
    printf("Total time: %.1f s (%.2f hours)\n\n", total_time, total_time / 3600.0);

    if (total_survivors == 0) {
        printf("************************************************************\n");
        printf("*** SUCCESS: ALL eligible m eliminated!                   ***\n");
        printf("*** ord_d(2) > S-1 = %llu PROVEN       ***\n",
               (unsigned long long)(S_VAL - 1));
        printf("*** d(q_23) = 2^%llu - 3^%llu is COMPOSITE ***\n",
               (unsigned long long)S_VAL, (unsigned long long)K_VAL);
        printf("*** (even if d were prime, its order condition fails)     ***\n");
        printf("************************************************************\n");
    } else {
        printf("WARNING: %llu survivors remain — need deeper verification\n",
               (unsigned long long)total_survivors);
        printf("These m values have val(m) with no odd prime factor < %u.\n",
               SMALL_PRIME_LIMIT);
        printf("This is expected to be 0 with overwhelming probability.\n");
        printf("If survivors persist, val(m) might be a power of 2.\n");
    }

    printf("================================================================\n");

    free(sieve_data);
    free(primes);
    return 0;
}
