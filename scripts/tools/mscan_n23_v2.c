/*
 * mscan_n23_v2.c — M-scan for n=23 with in-block secondary verification
 *
 * Proves d(q_23) = 2^S - 3^k is composite by showing that for ALL m in
 * [5, m_max], val(m) = (m+1)*3^k - m*2^S is NOT a power of 2.
 *
 * Two-level approach:
 *   Level 1: Segmented sieve with ~78K primes up to 10^6
 *            Eliminates ~88% of eligible m values.
 *   Level 2: For each survivor in a block, check val(m) mod p for
 *            additional primes up to 10^8 (~5.7M primes).
 *            Each check is just ONE multiply-and-add (nanoseconds).
 *            After ~100 extra primes, survival prob < 10^{-40}.
 *
 * n=23: S = 217976794617, k = 137528045312
 * m_max ≈ 1.113 × 10^12
 *
 * Compile: gcc -O3 -march=native -o mscan_n23_v2 mscan_n23_v2.c -lm
 * Run:     ./mscan_n23_v2
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
#define M_MAX   1112774250075ULL

/* Sieve parameters */
#define SIEVE_PRIME_LIMIT  1000000     /* Level 1: primes up to 10^6 */
#define CHECK_PRIME_LIMIT  100000000   /* Level 2: primes up to 10^8 */
#define BLOCK_SIZE         (1 << 22)   /* ~4M per block */

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

/* Sieve for primes up to n */
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

typedef struct { uint32_t p; uint32_t r; } PrimeRes;

int main() {
    printf("================================================================\n");
    printf("M-SCAN n=23 v2 — Two-level verification\n");
    printf("  S = %llu, k = %llu\n", (unsigned long long)S_VAL, (unsigned long long)K_VAL);
    printf("  m_max = %llu (~%.3e)\n", (unsigned long long)M_MAX, (double)M_MAX);
    printf("  Level 1: sieve with primes <= %u\n", SIEVE_PRIME_LIMIT);
    printf("  Level 2: per-survivor check with primes up to %u\n", CHECK_PRIME_LIMIT);
    printf("================================================================\n\n");
    fflush(stdout);

    struct timespec ts_start, ts_now;
    clock_gettime(CLOCK_MONOTONIC, &ts_start);

    /* Phase 1: Generate ALL primes up to CHECK_PRIME_LIMIT */
    printf("Phase 1: Generating primes up to %u...\n", CHECK_PRIME_LIMIT);
    fflush(stdout);
    uint32_t n_all_primes;
    uint32_t *all_primes = small_sieve(CHECK_PRIME_LIMIT, &n_all_primes);
    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    double t = (ts_now.tv_sec - ts_start.tv_sec) +
               (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
    printf("  %u primes generated (%.2f s)\n\n", n_all_primes, t);

    /* Phase 2: Precompute sieve residues for Level 1 primes (p <= SIEVE_PRIME_LIMIT)
     * and (A-B, A) pairs for ALL primes (for Level 2 checks)
     */
    printf("Phase 2: Precomputing modular exponentiations...\n");
    fflush(stdout);

    /* Level 1: sieve data */
    PrimeRes *sieve_data = (PrimeRes *)malloc(n_all_primes * sizeof(PrimeRes));
    uint32_t n_sieve = 0;

    /* Level 2: for each prime p, store (A-B mod p, A mod p) for fast per-m check.
     * val(m) mod p = (m * (A-B) + A) mod p
     * We store diff = (A-B) mod p and A_val = A mod p
     */
    typedef struct { uint64_t p; uint64_t diff; uint64_t A_val; } CheckPrime;
    CheckPrime *check_data = (CheckPrime *)malloc(n_all_primes * sizeof(CheckPrime));
    uint32_t n_check = 0;

    for (uint32_t i = 0; i < n_all_primes; i++) {
        uint64_t p = all_primes[i];
        if (p < 5) continue;

        uint64_t A = powmod64(3, K_VAL, p);
        uint64_t B = powmod64(2, S_VAL, p);

        if (A == B) continue; /* can't eliminate any m */

        /* diff = (A - B) mod p */
        uint64_t diff;
        if (A >= B) diff = A - B;
        else diff = p - B + A;

        /* For Level 1 sieve: compute residue r such that m ≡ r (mod p) => val(m) ≡ 0 */
        if (p <= SIEVE_PRIME_LIMIT) {
            /* r = A * modinv(B - A, p) = A * modinv(p - diff, p) */
            uint64_t neg_diff = (diff > 0) ? (p - diff) : 0;
            if (neg_diff == 0) continue; /* shouldn't happen since A != B */
            uint64_t inv = powmod64(neg_diff, p - 2, p);
            uint64_t r = (uint64_t)(((__uint128_t)A * inv) % p);
            sieve_data[n_sieve].p = (uint32_t)p;
            sieve_data[n_sieve].r = (uint32_t)r;
            n_sieve++;
        }

        /* For Level 2: store diff and A for fast per-m check */
        check_data[n_check].p = p;
        check_data[n_check].diff = diff;
        check_data[n_check].A_val = A;
        n_check++;

        /* Progress for precompute */
        if ((i + 1) % 1000000 == 0) {
            clock_gettime(CLOCK_MONOTONIC, &ts_now);
            t = (ts_now.tv_sec - ts_start.tv_sec) +
                (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
            printf("  %u/%u primes precomputed (%.1f s)\n", i + 1, n_all_primes, t);
            fflush(stdout);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    t = (ts_now.tv_sec - ts_start.tv_sec) +
        (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
    printf("  Level 1: %u sieve primes\n", n_sieve);
    printf("  Level 2: %u check primes (total)\n", n_check);
    printf("  Precompute done (%.2f s)\n\n", t);
    fflush(stdout);

    /* Phase 3: Segmented m-sieve with in-block verification */
    printf("Phase 3: Segmented m-sieve [5, %llu] with secondary checks...\n\n",
           (unsigned long long)M_MAX);
    fflush(stdout);

    uint8_t *block = (uint8_t *)calloc(BLOCK_SIZE, 1);
    if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

    uint64_t total_eligible = 0;
    uint64_t total_L1_eliminated = 0;
    uint64_t total_L2_eliminated = 0;
    uint64_t total_survivors = 0;    /* survive BOTH levels */
    uint64_t blocks_done = 0;
    uint64_t report_interval = 500000000ULL / BLOCK_SIZE;

    /* Level 2 check: start from index n_sieve in check_data (skip Level 1 primes)
     * Actually, Level 2 uses primes > SIEVE_PRIME_LIMIT. Find the starting index. */
    uint32_t L2_start = 0;
    for (uint32_t i = 0; i < n_check; i++) {
        if (check_data[i].p > SIEVE_PRIME_LIMIT) {
            L2_start = i;
            break;
        }
    }
    uint32_t n_L2 = n_check - L2_start;
    printf("  Level 2 check primes: %u (primes > %u)\n\n", n_L2, SIEVE_PRIME_LIMIT);
    fflush(stdout);

    clock_gettime(CLOCK_MONOTONIC, &ts_start); /* reset for rate */

    for (uint64_t block_lo = 5; block_lo <= M_MAX; block_lo += BLOCK_SIZE) {
        uint64_t block_hi = block_lo + BLOCK_SIZE - 1;
        if (block_hi > M_MAX) block_hi = M_MAX;
        uint64_t bsize = block_hi - block_lo + 1;

        /* Clear block (0 = not eliminated) */
        memset(block, 0, bsize);

        /* Level 1: Sieve with primes <= SIEVE_PRIME_LIMIT */
        for (uint32_t s = 0; s < n_sieve; s++) {
            uint64_t p = sieve_data[s].p;
            uint64_t r = sieve_data[s].r;

            uint64_t first;
            if (block_lo <= r) {
                first = r;
            } else {
                uint64_t offset = (block_lo - r + p - 1) / p;
                first = r + offset * p;
            }

            for (uint64_t m = first; m <= block_hi; m += p) {
                block[m - block_lo] = 1;
            }
        }

        /* Scan block: count eligible, check survivors */
        for (uint64_t j = 0; j < bsize; j++) {
            uint64_t m = block_lo + j;
            uint64_t m6 = m % 6;
            if (m6 != 1 && m6 != 5) continue; /* only m coprime to 6 */
            total_eligible++;

            if (block[j]) {
                total_L1_eliminated++;
                continue;
            }

            /* Level 2: This m survived Level 1. Check with extra primes. */
            int eliminated = 0;
            for (uint32_t c = L2_start; c < n_check; c++) {
                uint64_t p = check_data[c].p;
                uint64_t diff = check_data[c].diff;
                uint64_t A_val = check_data[c].A_val;

                /* val(m) mod p = (m * diff + A_val) mod p
                 * BUT: diff = (A - B) mod p, and val(m) = (m+1)*A - m*B
                 * = m*(A-B) + A = m*diff + A_val (mod p) */
                __uint128_t prod = (__uint128_t)m * diff;
                uint64_t vm = (uint64_t)((prod + A_val) % p);

                if (vm == 0) {
                    eliminated = 1;
                    total_L2_eliminated++;
                    break;
                }
            }

            if (!eliminated) {
                total_survivors++;
                if (total_survivors <= 20) {
                    printf("  *** PERSISTENT SURVIVOR: m = %llu ***\n",
                           (unsigned long long)m);
                    printf("      (survived %u L1 primes + %u L2 primes)\n",
                           n_sieve, n_L2);
                    fflush(stdout);
                }
            }
        }

        blocks_done++;

        if (blocks_done % report_interval == 0) {
            clock_gettime(CLOCK_MONOTONIC, &ts_now);
            double elapsed = (ts_now.tv_sec - ts_start.tv_sec) +
                             (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
            double progress = (double)(block_hi - 5) / (double)(M_MAX - 5) * 100.0;
            double rate = total_eligible / elapsed;
            double eta = (elapsed / progress) * (100.0 - progress);
            printf("  %7.2fG m, %6.2f%%, eligible %llu, L1_elim %llu (%.1f%%), "
                   "L2_elim %llu, survivors %llu, %.0f m/s, ETA %.0f s\n",
                   (double)(block_hi - 5) / 1e9,
                   progress,
                   (unsigned long long)total_eligible,
                   (unsigned long long)total_L1_eliminated,
                   100.0 * total_L1_eliminated / total_eligible,
                   (unsigned long long)total_L2_eliminated,
                   (unsigned long long)total_survivors,
                   rate, eta);
            fflush(stdout);
        }
    }

    free(block);

    /* Results */
    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    double total_time = (ts_now.tv_sec - ts_start.tv_sec) +
                        (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;

    printf("\n================================================================\n");
    printf("RESULTS — M-scan n=23 v2 (two-level)\n");
    printf("================================================================\n");
    printf("m range: [5, %llu]\n", (unsigned long long)M_MAX);
    printf("Total eligible m: %llu\n", (unsigned long long)total_eligible);
    printf("Level 1 eliminated (primes <= %u): %llu (%.4f%%)\n",
           SIEVE_PRIME_LIMIT,
           (unsigned long long)total_L1_eliminated,
           100.0 * total_L1_eliminated / total_eligible);
    printf("Level 2 eliminated (primes <= %u): %llu\n",
           CHECK_PRIME_LIMIT,
           (unsigned long long)total_L2_eliminated);
    printf("Persistent survivors: %llu\n", (unsigned long long)total_survivors);
    printf("Total time: %.1f s (%.2f hours)\n\n", total_time, total_time / 3600.0);

    if (total_survivors == 0) {
        printf("************************************************************\n");
        printf("*** SUCCESS: ALL eligible m eliminated!                   ***\n");
        printf("*** Every val(m) has an odd prime factor <= %u   ***\n",
               CHECK_PRIME_LIMIT);
        printf("*** => val(m) is NOT a power of 2 for ANY m in [5, m_max] ***\n");
        printf("*** => ord_d(2) > S-1 = %llu                ***\n",
               (unsigned long long)(S_VAL - 1));
        printf("*** => d(q_23) is COMPOSITE                               ***\n");
        printf("************************************************************\n");
    } else {
        printf("WARNING: %llu persistent survivors\n", (unsigned long long)total_survivors);
        printf("These need deeper investigation (more primes or exact computation).\n");
    }

    printf("================================================================\n");

    free(sieve_data);
    free(check_data);
    free(all_primes);
    return 0;
}
