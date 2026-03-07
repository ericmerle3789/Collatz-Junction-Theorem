/*
 * sieve_all5.c — Systematic prime sieve for ALL 5 remaining odd convergents
 *
 * Tests all primes p up to LIMIT to check if p | d(q_n)
 * where d(q_n) = 2^{p_n} - 3^{q_n}
 *
 * Uses __uint128_t for exponents (needed for n=59,65,77 which have S > 2^64)
 * All modular arithmetic is 64-bit (since p < 2^64)
 *
 * Compile: gcc -O3 -o sieve_all5 sieve_all5.c -lm
 * Run:     ./sieve_all5
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

/* Sieve limit */
#define LIMIT        100000000000ULL  /* 10^11 */
#define SIEVE_BLOCK  (1 << 22)       /* ~4M per block */
#define SQRT_LIMIT   320000          /* sqrt(10^11) ~ 316K */

/* Helper to construct __uint128_t from hi:lo */
#define MAKE128(hi, lo) (((__uint128_t)(hi) << 64) | (__uint128_t)(lo))

/* Targets: 5 remaining unresolved odd convergents */
typedef struct {
    int n_idx;
    __uint128_t S;      /* p_n = numerator */
    __uint128_t k;      /* q_n = denominator */
    uint64_t factor;
} Target;

Target targets[] = {
    {23, 0, 0, 0},  /* Initialized in main */
    {25, 0, 0, 0},
    {59, 0, 0, 0},
    {65, 0, 0, 0},
    {77, 0, 0, 0},
};
#define N_TARGETS 5

/* Modular exponentiation: base^exp mod mod, with __uint128_t exponent */
static inline uint64_t powmod128(uint64_t base, __uint128_t exp, uint64_t mod) {
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

/* Small sieve for primes up to n */
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
    /* Initialize targets with __uint128_t values */
    /* n=23: p_23=217976794617, q_23=137528045312 */
    targets[0].S = (__uint128_t)217976794617ULL;
    targets[0].k = (__uint128_t)137528045312ULL;

    /* n=25: p_25=8573543875303, q_25=5409303924479 */
    targets[1].S = (__uint128_t)8573543875303ULL;
    targets[1].k = (__uint128_t)5409303924479ULL;

    /* n=59: p_59 hi=32491504068, lo=1576836336967928270 */
    targets[2].S = MAKE128(32491504068ULL, 1576836336967928270ULL);
    targets[2].k = MAKE128(20499856654ULL, 15553907544489643179ULL);

    /* n=65: p_65 hi=49799792675736, lo=5404358708563867079 */
    targets[3].S = MAKE128(49799792675736ULL, 5404358708563867079ULL);
    targets[3].k = MAKE128(31420170920811ULL, 17899019887547740790ULL);

    /* n=77: p_77 hi=3184728776590096931, lo=12272906109865770703 */
    targets[4].S = MAKE128(3184728776590096931ULL, 12272906109865770703ULL);
    targets[4].k = MAKE128(2009340142205918983ULL, 16029200321910071134ULL);

    printf("================================================================\n");
    printf("SIEVE ALL 5 TARGETS: Testing primes up to %llu\n", (unsigned long long)LIMIT);
    for (int t = 0; t < N_TARGETS; t++) {
        /* Print S and k as decimal using double approximation for large values */
        double s_approx = (double)targets[t].S;
        double k_approx = (double)targets[t].k;
        printf("  Target n=%d: S ~ %.3e, k ~ %.3e\n",
               targets[t].n_idx, s_approx, k_approx);
    }
    printf("================================================================\n\n");
    fflush(stdout);

    clock_t t0 = clock();

    /* Phase 1: Small primes sieve */
    uint32_t n_small;
    uint32_t *small_primes = small_sieve(SQRT_LIMIT, &n_small);
    printf("Small sieve: %u primes <= %u (%.2f s)\n\n", n_small, SQRT_LIMIT,
           (double)(clock() - t0) / CLOCKS_PER_SEC);

    /* Phase 2: Test small primes */
    printf("Phase 1: Testing %u small primes...\n", n_small);
    uint64_t total_tested = 0;
    int n_found = 0;

    for (uint32_t i = 0; i < n_small; i++) {
        uint64_t p = small_primes[i];
        if (p < 2) continue;
        total_tested++;

        for (int t = 0; t < N_TARGETS; t++) {
            if (targets[t].factor) continue;
            uint64_t v2 = powmod128(2, targets[t].S, p);
            uint64_t v3 = powmod128(3, targets[t].k, p);
            uint64_t diff = (v2 >= v3) ? (v2 - v3) : (p - v3 + v2);
            if (diff % p == 0) {
                targets[t].factor = p;
                n_found++;
                printf("  *** n=%d FACTOR FOUND: %llu ***\n",
                       targets[t].n_idx, (unsigned long long)p);
                fflush(stdout);
            }
        }
        if (n_found == N_TARGETS) break;
    }

    int remaining = N_TARGETS - n_found;
    printf("  %d target(s) without factor <= %u (tested %llu primes)\n\n",
           remaining, SQRT_LIMIT, (unsigned long long)total_tested);

    /* Phase 3: Segmented sieve */
    if (remaining > 0) {
        printf("Phase 2: Segmented sieve [%u, %llu] (%d targets)...\n",
               SQRT_LIMIT, (unsigned long long)LIMIT, remaining);
        fflush(stdout);

        uint8_t *block = (uint8_t *)malloc(SIEVE_BLOCK);
        if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

        uint64_t block_count = 0;
        clock_t t_phase2 = clock();

        for (uint64_t lo = SQRT_LIMIT + 1; lo <= LIMIT && remaining > 0; lo += SIEVE_BLOCK) {
            uint64_t hi = lo + SIEVE_BLOCK - 1;
            if (hi > LIMIT) hi = LIMIT;
            uint64_t block_size = hi - lo + 1;

            memset(block, 1, block_size);

            for (uint32_t i = 0; i < n_small; i++) {
                uint64_t p = small_primes[i];
                uint64_t start = ((lo + p - 1) / p) * p;
                if (start == p) start += p;
                if (start < lo) start += p;
                for (uint64_t j = start - lo; j < block_size; j += p)
                    block[j] = 0;
            }

            for (uint64_t j = 0; j < block_size && remaining > 0; j++) {
                if (!block[j]) continue;
                uint64_t p = lo + j;
                if (p <= 1) continue;
                total_tested++;

                for (int t = 0; t < N_TARGETS; t++) {
                    if (targets[t].factor) continue;
                    uint64_t v2 = powmod128(2, targets[t].S, p);
                    uint64_t v3 = powmod128(3, targets[t].k, p);
                    uint64_t diff;
                    if (v2 >= v3) diff = v2 - v3;
                    else diff = p - v3 + v2;

                    if (diff == 0) {
                        targets[t].factor = p;
                        n_found++;
                        remaining--;
                        printf("\n  *** n=%d FACTOR FOUND: %llu ***\n",
                               targets[t].n_idx, (unsigned long long)p);
                        uint64_t chk2 = powmod128(2, targets[t].S, p);
                        uint64_t chk3 = powmod128(3, targets[t].k, p);
                        printf("  Verification: 2^S mod p = %llu, 3^k mod p = %llu\n",
                               (unsigned long long)chk2, (unsigned long long)chk3);
                        fflush(stdout);
                    }
                }
            }

            block_count++;

            if (block_count % (500000000 / SIEVE_BLOCK) == 0) {
                double elapsed = (double)(clock() - t_phase2) / CLOCKS_PER_SEC;
                double rate = (total_tested - n_small) / elapsed;
                printf("  %6.2fG tested, %llu primes, %.0f primes/s, %.1f s, %d remaining\n",
                       (double)hi / 1e9, (unsigned long long)total_tested,
                       rate, elapsed, remaining);
                fflush(stdout);
            }
        }

        free(block);
    }

    /* Results */
    double total_time = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("\n================================================================\n");
    printf("RESULTS\n");
    printf("================================================================\n");
    printf("Total primes tested: %llu\n", (unsigned long long)total_tested);
    printf("Total time: %.1f s\n\n", total_time);

    for (int t = 0; t < N_TARGETS; t++) {
        if (targets[t].factor) {
            printf("n=%d: COMPOSITE! Factor = %llu\n",
                   targets[t].n_idx, (unsigned long long)targets[t].factor);
        } else {
            printf("n=%d: No factor found up to %llu\n",
                   targets[t].n_idx, (unsigned long long)LIMIT);
        }
    }

    printf("\nScore: %d/%d resolved in this run\n", n_found, N_TARGETS);
    printf("================================================================\n");

    free(small_primes);
    return 0;
}
