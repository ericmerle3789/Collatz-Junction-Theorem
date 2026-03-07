/*
 * sieve_n59.c — Extended sieve for n=59 (single target, up to 10^11)
 *
 * n=59 had no factor found up to 10^10 in sieve_big3.
 * Extends the search to 10^11 with a single target for better throughput.
 *
 * Uses __uint128_t for the exponent S ~ 5.99 × 10^29
 *
 * Compile: gcc -O3 -o sieve_n59 sieve_n59.c -lm
 * Run:     ./sieve_n59
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define LIMIT        100000000000ULL  /* 10^11 */
#define SIEVE_BLOCK  (1 << 22)       /* ~4M per block */
#define SQRT_LIMIT   320000          /* sqrt(10^11) ~ 316K */

#define MAKE128(hi, lo) (((__uint128_t)(hi) << 64) | (__uint128_t)(lo))

/* n=59: S ~ 5.99e29, k ~ 3.78e29 */
static __uint128_t S59, K59;

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
    /* n=59: p_59 hi=32491504068, lo=1576836336967928270 */
    S59 = MAKE128(32491504068ULL, 1576836336967928270ULL);
    K59 = MAKE128(20499856654ULL, 15553907544489643179ULL);

    printf("================================================================\n");
    printf("SIEVE n=59 EXTENDED: Testing primes up to %llu\n", (unsigned long long)LIMIT);
    printf("  S ~ %.3e, k ~ %.3e\n", (double)S59, (double)K59);
    printf("  Starting from scratch (includes re-check of primes < 10^10)\n");
    printf("================================================================\n\n");
    fflush(stdout);

    clock_t t0 = clock();

    uint32_t n_small;
    uint32_t *small_primes = small_sieve(SQRT_LIMIT, &n_small);
    printf("Small sieve: %u primes <= %u (%.2f s)\n\n", n_small, SQRT_LIMIT,
           (double)(clock() - t0) / CLOCKS_PER_SEC);

    printf("Phase 1: Testing %u small primes...\n", n_small);
    uint64_t total_tested = 0;
    int found = 0;

    for (uint32_t i = 0; i < n_small && !found; i++) {
        uint64_t p = small_primes[i];
        if (p < 5) continue;
        total_tested++;
        uint64_t v2 = powmod128(2, S59, p);
        uint64_t v3 = powmod128(3, K59, p);
        uint64_t diff = (v2 >= v3) ? (v2 - v3) : (p - v3 + v2);
        if (diff % p == 0) {
            printf("  *** n=59 FACTOR FOUND: %llu ***\n", (unsigned long long)p);
            found = 1;
        }
    }

    if (!found)
        printf("  No factor <= %u (%llu primes tested)\n\n", SQRT_LIMIT,
               (unsigned long long)total_tested);

    if (!found) {
        printf("Phase 2: Segmented sieve [%u, %llu]...\n", SQRT_LIMIT,
               (unsigned long long)LIMIT);
        fflush(stdout);

        uint8_t *block = (uint8_t *)malloc(SIEVE_BLOCK);
        if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

        uint64_t block_count = 0;
        clock_t t_phase2 = clock();

        for (uint64_t lo = SQRT_LIMIT + 1; lo <= LIMIT && !found; lo += SIEVE_BLOCK) {
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

            for (uint64_t j = 0; j < block_size && !found; j++) {
                if (!block[j]) continue;
                uint64_t p = lo + j;
                if (p <= 1) continue;
                total_tested++;

                uint64_t v2 = powmod128(2, S59, p);
                uint64_t v3 = powmod128(3, K59, p);
                uint64_t diff;
                if (v2 >= v3) diff = v2 - v3;
                else diff = p - v3 + v2;

                if (diff == 0) {
                    found = 1;
                    printf("\n  *** n=59 FACTOR FOUND: %llu ***\n", (unsigned long long)p);
                    uint64_t chk2 = powmod128(2, S59, p);
                    uint64_t chk3 = powmod128(3, K59, p);
                    printf("  Verification: 2^S mod p = %llu, 3^k mod p = %llu\n",
                           (unsigned long long)chk2, (unsigned long long)chk3);
                    fflush(stdout);
                }
            }

            block_count++;

            if (block_count % (500000000 / SIEVE_BLOCK) == 0) {
                double elapsed = (double)(clock() - t_phase2) / CLOCKS_PER_SEC;
                double rate = (total_tested - n_small) / elapsed;
                printf("  %6.2fG tested, %llu primes, %.0f primes/s, %.1f s\n",
                       (double)hi / 1e9, (unsigned long long)total_tested,
                       rate, elapsed);
                fflush(stdout);
            }
        }

        free(block);
    }

    double total_time = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("\n================================================================\n");
    printf("RESULT\n");
    printf("================================================================\n");
    printf("Total primes tested: %llu\n", (unsigned long long)total_tested);
    printf("Total time: %.1f s\n\n", total_time);

    if (found) {
        printf("n=59: COMPOSITE!\n");
    } else {
        printf("n=59: No factor found up to %llu\n", (unsigned long long)LIMIT);
    }

    printf("================================================================\n");

    free(small_primes);
    return 0;
}
