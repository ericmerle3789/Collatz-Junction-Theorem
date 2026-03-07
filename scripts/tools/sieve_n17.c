/*
 * sieve_n17.c — Systematic prime sieve for n=17 compositeness test
 *
 * Tests all primes p up to LIMIT to check if p | d(q_17)
 * where d(q_17) = 2^272500658 - 3^171928773
 *
 * Method: for each prime p, compute (pow(2, S, p) - pow(3, k, p)) % p
 * Uses segmented sieve + 64-bit modular exponentiation (no GMP needed for p < 2^32)
 *
 * Compile: gcc -O3 -o sieve_n17 sieve_n17.c -lm
 * Run:     ./sieve_n17
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

/* Target: n=17 convergent of log_2(3) */
#define S_VAL  272500658ULL   /* p_17 = numerator */
#define K_VAL  171928773ULL   /* q_17 = denominator */

/* Sieve limit — adjust as needed */
#define LIMIT        100000000000ULL  /* 10^11 */
#define SIEVE_BLOCK  (1 << 22)        /* ~4M per block (cache-friendly) */
#define SQRT_LIMIT   320000           /* sqrt(10^11) ~ 316K */

/* Also test all 6 targets */
typedef struct {
    int n_idx;
    uint64_t S;
    uint64_t k;
    uint64_t factor;
} Target;

/* 6 unresolved odd convergents */
Target targets[] = {
    {17, 272500658ULL, 171928773ULL, 0},
    /* n=23,25 have S and k too large for uint64, skip in basic version */
};
int n_targets = 1;  /* Only n=17 for now */

/* Modular exponentiation: compute base^exp mod mod */
static inline uint64_t powmod(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            /* result = (result * base) % mod, using 128-bit */
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
    printf("================================================================\n");
    printf("SIEVE n=17: Testing primes up to %llu\n", (unsigned long long)LIMIT);
    printf("Target: d = 2^%llu - 3^%llu\n", (unsigned long long)S_VAL, (unsigned long long)K_VAL);
    printf("================================================================\n\n");

    clock_t t0 = clock();

    /* Phase 1: Small primes sieve */
    uint32_t n_small;
    uint32_t *small_primes = small_sieve(SQRT_LIMIT, &n_small);
    printf("Small sieve: %u primes <= %u (%.2f s)\n", n_small, SQRT_LIMIT,
           (double)(clock() - t0) / CLOCKS_PER_SEC);

    /* Phase 2: Test small primes directly */
    printf("\nPhase 1: Testing %u small primes...\n", n_small);
    uint64_t total_tested = 0;
    uint64_t factor_found = 0;

    for (uint32_t i = 0; i < n_small; i++) {
        uint64_t p = small_primes[i];
        if (p < 2) continue;
        total_tested++;
        uint64_t v2 = powmod(2, S_VAL, p);
        uint64_t v3 = powmod(3, K_VAL, p);
        uint64_t diff = (v2 >= v3) ? (v2 - v3) : (p - v3 + v2);
        if (diff % p == 0) {
            factor_found = p;
            printf("  *** FACTOR FOUND: %llu ***\n", (unsigned long long)p);
            break;
        }
    }

    if (!factor_found) {
        printf("  No factor <= %u (tested %llu primes)\n", SQRT_LIMIT,
               (unsigned long long)total_tested);
    }

    /* Phase 3: Segmented sieve for larger primes */
    if (!factor_found) {
        printf("\nPhase 2: Segmented sieve [%u, %llu]...\n", SQRT_LIMIT,
               (unsigned long long)LIMIT);

        uint8_t *block = (uint8_t *)malloc(SIEVE_BLOCK);
        if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

        uint64_t block_count = 0;
        clock_t t_phase2 = clock();

        for (uint64_t lo = SQRT_LIMIT + 1; lo <= LIMIT && !factor_found; lo += SIEVE_BLOCK) {
            uint64_t hi = lo + SIEVE_BLOCK - 1;
            if (hi > LIMIT) hi = LIMIT;
            uint64_t block_size = hi - lo + 1;

            /* Initialize block */
            memset(block, 1, block_size);

            /* Sieve this block with small primes */
            for (uint32_t i = 0; i < n_small; i++) {
                uint64_t p = small_primes[i];
                uint64_t start = ((lo + p - 1) / p) * p;
                if (start == p) start += p;
                if (start < lo) start += p;
                for (uint64_t j = start - lo; j < block_size; j += p)
                    block[j] = 0;
            }

            /* Test primes in this block */
            for (uint64_t j = 0; j < block_size; j++) {
                if (!block[j]) continue;
                uint64_t p = lo + j;
                if (p <= 1) continue;
                total_tested++;

                uint64_t v2 = powmod(2, S_VAL, p);
                uint64_t v3 = powmod(3, K_VAL, p);
                uint64_t diff;
                if (v2 >= v3) diff = v2 - v3;
                else diff = p - v3 + v2;

                if (diff == 0) {
                    factor_found = p;
                    printf("\n  *** FACTOR FOUND: %llu ***\n", (unsigned long long)p);
                    /* Verify */
                    uint64_t check = powmod(2, S_VAL, p);
                    uint64_t check3 = powmod(3, K_VAL, p);
                    printf("  Verification: 2^S mod p = %llu, 3^k mod p = %llu\n",
                           (unsigned long long)check, (unsigned long long)check3);
                    break;
                }
            }

            block_count++;

            /* Progress every ~500M */
            if (block_count % (500000000 / SIEVE_BLOCK) == 0) {
                double elapsed = (double)(clock() - t_phase2) / CLOCKS_PER_SEC;
                double rate = total_tested / elapsed;
                printf("  %6.2fG tested, %llu primes, %.0f primes/s, %.1f s\n",
                       (double)hi / 1e9, (unsigned long long)total_tested,
                       rate, elapsed);
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
    printf("Total time: %.1f s\n", total_time);

    if (factor_found) {
        printf("\nn=17: COMPOSITE! Factor = %llu\n", (unsigned long long)factor_found);
        printf("  d(q_17) = 2^%llu - 3^%llu is divisible by %llu\n",
               (unsigned long long)S_VAL, (unsigned long long)K_VAL,
               (unsigned long long)factor_found);
    } else {
        printf("\nn=17: No factor found up to %llu\n", (unsigned long long)LIMIT);
        printf("  The smallest prime factor of d(q_17) is > %llu\n",
               (unsigned long long)LIMIT);
    }

    printf("================================================================\n");

    free(small_primes);
    return 0;
}
