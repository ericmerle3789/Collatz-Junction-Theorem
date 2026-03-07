/*
 * sieve_1e12_all3.c — Segmented sieve [10^11, 10^12] for n=23, n=25, n=59
 *
 * Tests ONLY the range (10^11, 10^12] since all primes <= 10^11 have
 * already been tested in sessions 10f26k.
 *
 * Three targets tested per prime to maximize throughput.
 *
 * n=23: d = 2^217976794617 - 3^137528045312
 * n=25: d = 2^8573543875303 - 3^5409303924479
 * n=59: d = 2^S59 - 3^K59  (S59 ~ 5.99e29, 128-bit exponents)
 *
 * Compile: gcc -O3 -march=native -o sieve_1e12 sieve_1e12_all3.c -lm
 * Run:     ./sieve_1e12
 *
 * Expected runtime: ~30-35h on Apple M1 Pro
 * Expected primes to test: ~33.5 billion (pi(10^12) - pi(10^11))
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

/* Range: test primes in (START, LIMIT] */
#define START        100000000000ULL   /* 10^11 — already done */
#define LIMIT        1000000000000ULL  /* 10^12 */
#define SIEVE_BLOCK  (1 << 22)        /* ~4M per block */
#define SQRT_LIMIT   1000000           /* sqrt(10^12) = 10^6 */

#define MAKE128(hi, lo) (((__uint128_t)(hi) << 64) | (__uint128_t)(lo))

/* ---- Modular exponentiation (64-bit exponent) ---- */
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

/* ---- Modular exponentiation (128-bit exponent) ---- */
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

/* ---- Small sieve for primes up to n ---- */
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

/* ---- Targets ---- */
typedef struct {
    int n_idx;
    int is_128;       /* 1 if exponent needs __uint128_t */
    uint64_t S64;     /* 64-bit exponent (n=23, n=25) */
    uint64_t k64;
    __uint128_t S128; /* 128-bit exponent (n=59) */
    __uint128_t k128;
    uint64_t factor;
} Target;

int main() {
    /* n=59 128-bit exponents */
    __uint128_t S59 = MAKE128(32491504068ULL, 1576836336967928270ULL);
    __uint128_t K59 = MAKE128(20499856654ULL, 15553907544489643179ULL);

    Target targets[3] = {
        {23, 0, 217976794617ULL, 137528045312ULL, 0, 0, 0},
        {25, 0, 8573543875303ULL, 5409303924479ULL, 0, 0, 0},
        {59, 1, 0, 0, S59, K59, 0},
    };
    int n_targets = 3;
    int n_remaining = 3;

    printf("================================================================\n");
    printf("SIEVE [10^11, 10^12]: 3 targets (n=23, n=25, n=59)\n");
    printf("  Range: (%llu, %llu]\n",
           (unsigned long long)START, (unsigned long long)LIMIT);
    printf("  n=23: d = 2^%llu - 3^%llu\n",
           (unsigned long long)targets[0].S64,
           (unsigned long long)targets[0].k64);
    printf("  n=25: d = 2^%llu - 3^%llu\n",
           (unsigned long long)targets[1].S64,
           (unsigned long long)targets[1].k64);
    printf("  n=59: d = 2^S59 - 3^K59  (S59 ~ %.3e)\n", (double)S59);
    printf("  Expected: ~33.5 billion primes to test\n");
    printf("================================================================\n\n");
    fflush(stdout);

    struct timespec ts_start, ts_now;
    clock_gettime(CLOCK_MONOTONIC, &ts_start);

    /* Phase 1: Small primes sieve (for segmented sieve, NOT for testing) */
    uint32_t n_small;
    uint32_t *small_primes = small_sieve(SQRT_LIMIT, &n_small);
    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    double setup_time = (ts_now.tv_sec - ts_start.tv_sec) +
                        (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
    printf("Small sieve: %u primes <= %u (%.2f s)\n\n", n_small, SQRT_LIMIT,
           setup_time);
    fflush(stdout);

    /* Phase 2: Segmented sieve over (START, LIMIT] */
    printf("Phase 2: Segmented sieve (%llu, %llu]...\n",
           (unsigned long long)START, (unsigned long long)LIMIT);
    fflush(stdout);

    uint8_t *block = (uint8_t *)malloc(SIEVE_BLOCK);
    if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

    uint64_t total_tested = 0;
    uint64_t report_interval = 500000000ULL / SIEVE_BLOCK; /* ~every 0.5G */
    uint64_t block_count = 0;

    clock_gettime(CLOCK_MONOTONIC, &ts_start); /* reset for rate calc */

    for (uint64_t lo = START + 1; lo <= LIMIT && n_remaining > 0; lo += SIEVE_BLOCK) {
        uint64_t hi = lo + SIEVE_BLOCK - 1;
        if (hi > LIMIT) hi = LIMIT;
        uint64_t block_size = hi - lo + 1;

        memset(block, 1, block_size);

        /* Mark composites */
        for (uint32_t i = 0; i < n_small; i++) {
            uint64_t p = small_primes[i];
            uint64_t start = ((lo + p - 1) / p) * p;
            if (start == p) start += p; /* skip p itself */
            for (uint64_t j = start - lo; j < block_size; j += p)
                block[j] = 0;
        }

        /* Test primes in block */
        for (uint64_t j = 0; j < block_size && n_remaining > 0; j++) {
            if (!block[j]) continue;
            uint64_t p = lo + j;
            if (p <= 1 || (p & 1) == 0) continue; /* skip even */
            total_tested++;

            for (int t = 0; t < n_targets; t++) {
                if (targets[t].factor) continue;

                uint64_t v2, v3;
                if (targets[t].is_128) {
                    v2 = powmod128(2, targets[t].S128, p);
                    v3 = powmod128(3, targets[t].k128, p);
                } else {
                    v2 = powmod64(2, targets[t].S64, p);
                    v3 = powmod64(3, targets[t].k64, p);
                }

                uint64_t diff;
                if (v2 >= v3) diff = v2 - v3;
                else diff = p - v3 + v2;

                if (diff == 0) {
                    targets[t].factor = p;
                    n_remaining--;

                    /* Double-check */
                    uint64_t c2, c3;
                    if (targets[t].is_128) {
                        c2 = powmod128(2, targets[t].S128, p);
                        c3 = powmod128(3, targets[t].k128, p);
                    } else {
                        c2 = powmod64(2, targets[t].S64, p);
                        c3 = powmod64(3, targets[t].k64, p);
                    }

                    clock_gettime(CLOCK_MONOTONIC, &ts_now);
                    double elapsed = (ts_now.tv_sec - ts_start.tv_sec) +
                                     (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;

                    printf("\n");
                    printf("  ****************************************************\n");
                    printf("  *** n=%d FACTOR FOUND: %llu ***\n",
                           targets[t].n_idx, (unsigned long long)p);
                    printf("  *** Verification: 2^S=%llu, 3^k=%llu (mod p) ***\n",
                           (unsigned long long)c2, (unsigned long long)c3);
                    printf("  *** Time: %.1f s, after %llu primes ***\n",
                           elapsed, (unsigned long long)total_tested);
                    printf("  *** Remaining targets: %d ***\n", n_remaining);
                    printf("  ****************************************************\n\n");
                    fflush(stdout);
                }
            }
        }

        block_count++;

        /* Progress report every ~0.5G */
        if (block_count % report_interval == 0) {
            clock_gettime(CLOCK_MONOTONIC, &ts_now);
            double elapsed = (ts_now.tv_sec - ts_start.tv_sec) +
                             (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;
            double rate = total_tested / elapsed;
            double progress = (double)(hi - START) / (double)(LIMIT - START) * 100.0;
            double eta = (elapsed / progress) * (100.0 - progress);
            printf("  %7.2fG range, %6.2f%%, %llu primes, %.0f p/s, %.0f s elapsed, ETA %.0f s (%d remain)\n",
                   (double)(hi - START) / 1e9,
                   progress,
                   (unsigned long long)total_tested,
                   rate, elapsed, eta, n_remaining);
            fflush(stdout);
        }
    }

    free(block);

    /* Results */
    clock_gettime(CLOCK_MONOTONIC, &ts_now);
    double total_time = (ts_now.tv_sec - ts_start.tv_sec) +
                        (ts_now.tv_nsec - ts_start.tv_nsec) / 1e9;

    printf("\n================================================================\n");
    printf("RESULTS — Sieve [10^11, 10^12]\n");
    printf("================================================================\n");
    printf("Total primes tested: %llu\n", (unsigned long long)total_tested);
    printf("Total time: %.1f s (%.2f hours)\n\n", total_time, total_time / 3600.0);

    int n_found = 0;
    for (int t = 0; t < n_targets; t++) {
        if (targets[t].factor) {
            n_found++;
            printf("n=%d: COMPOSITE! Factor = %llu\n",
                   targets[t].n_idx, (unsigned long long)targets[t].factor);
            if (targets[t].is_128) {
                printf("  d(q_%d) = 2^(~%.3e) - 3^(~%.3e) is divisible by %llu\n",
                       targets[t].n_idx,
                       (double)targets[t].S128,
                       (double)targets[t].k128,
                       (unsigned long long)targets[t].factor);
            } else {
                printf("  d(q_%d) = 2^%llu - 3^%llu is divisible by %llu\n",
                       targets[t].n_idx,
                       (unsigned long long)targets[t].S64,
                       (unsigned long long)targets[t].k64,
                       (unsigned long long)targets[t].factor);
            }
        } else {
            printf("n=%d: No factor found in (10^11, 10^12]\n",
                   targets[t].n_idx);
        }
    }

    printf("\nScore: %d/3 resolved in this run\n", n_found);
    printf("Overall: %d/37 convergents now resolved\n", 34 + n_found);
    printf("================================================================\n");

    free(small_primes);
    return 0;
}
