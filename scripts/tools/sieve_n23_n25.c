/*
 * sieve_n23_n25.c — Systematic prime sieve for n=23 and n=25 compositeness test
 *
 * Tests all primes p up to LIMIT to check if p | d(q_n)
 * where d(q_n) = 2^{p_n} - 3^{q_n}
 *
 * Method: segmented sieve + 64-bit modular exponentiation via __uint128_t
 *
 * Compile: gcc -O3 -o sieve_n23_n25 sieve_n23_n25.c -lm
 * Run:     ./sieve_n23_n25
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

/* Targets */
typedef struct {
    int n_idx;
    uint64_t S;      /* p_n = numerator */
    uint64_t k;      /* q_n = denominator */
    uint64_t factor;
} Target;

Target targets[] = {
    {23, 217976794617ULL, 137528045312ULL, 0},
    {25, 8573543875303ULL, 5409303924479ULL, 0},
};
#define N_TARGETS 2

/* Modular exponentiation: base^exp mod mod */
static inline uint64_t powmod(uint64_t base, uint64_t exp, uint64_t mod) {
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
    printf("================================================================\n");
    printf("SIEVE n=23,25: Testing primes up to %llu\n", (unsigned long long)LIMIT);
    for (int t = 0; t < N_TARGETS; t++) {
        printf("  Target n=%d: d = 2^%llu - 3^%llu\n",
               targets[t].n_idx,
               (unsigned long long)targets[t].S,
               (unsigned long long)targets[t].k);
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
    int all_found = 0;

    for (uint32_t i = 0; i < n_small && !all_found; i++) {
        uint64_t p = small_primes[i];
        if (p < 2) continue;
        total_tested++;

        for (int t = 0; t < N_TARGETS; t++) {
            if (targets[t].factor) continue;
            uint64_t v2 = powmod(2, targets[t].S, p);
            uint64_t v3 = powmod(3, targets[t].k, p);
            uint64_t diff = (v2 >= v3) ? (v2 - v3) : (p - v3 + v2);
            if (diff % p == 0) {
                targets[t].factor = p;
                printf("  *** n=%d FACTOR FOUND: %llu ***\n",
                       targets[t].n_idx, (unsigned long long)p);
                fflush(stdout);
            }
        }

        /* Check if all found */
        all_found = 1;
        for (int t = 0; t < N_TARGETS; t++)
            if (!targets[t].factor) { all_found = 0; break; }
    }

    if (!all_found) {
        int remaining = 0;
        for (int t = 0; t < N_TARGETS; t++)
            if (!targets[t].factor) remaining++;
        printf("  No factor <= %u for %d target(s) (tested %llu primes)\n",
               SQRT_LIMIT, remaining, (unsigned long long)total_tested);
    }

    /* Phase 3: Segmented sieve */
    if (!all_found) {
        printf("\nPhase 2: Segmented sieve [%u, %llu]...\n", SQRT_LIMIT,
               (unsigned long long)LIMIT);
        fflush(stdout);

        uint8_t *block = (uint8_t *)malloc(SIEVE_BLOCK);
        if (!block) { fprintf(stderr, "OOM\n"); exit(1); }

        uint64_t block_count = 0;
        clock_t t_phase2 = clock();

        for (uint64_t lo = SQRT_LIMIT + 1; lo <= LIMIT && !all_found; lo += SIEVE_BLOCK) {
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

            for (uint64_t j = 0; j < block_size && !all_found; j++) {
                if (!block[j]) continue;
                uint64_t p = lo + j;
                if (p <= 1) continue;
                total_tested++;

                for (int t = 0; t < N_TARGETS; t++) {
                    if (targets[t].factor) continue;
                    uint64_t v2 = powmod(2, targets[t].S, p);
                    uint64_t v3 = powmod(3, targets[t].k, p);
                    uint64_t diff;
                    if (v2 >= v3) diff = v2 - v3;
                    else diff = p - v3 + v2;

                    if (diff == 0) {
                        targets[t].factor = p;
                        printf("\n  *** n=%d FACTOR FOUND: %llu ***\n",
                               targets[t].n_idx, (unsigned long long)p);
                        uint64_t check2 = powmod(2, targets[t].S, p);
                        uint64_t check3 = powmod(3, targets[t].k, p);
                        printf("  Verification: 2^S mod p = %llu, 3^k mod p = %llu\n",
                               (unsigned long long)check2, (unsigned long long)check3);
                        fflush(stdout);
                    }
                }

                all_found = 1;
                for (int t = 0; t < N_TARGETS; t++)
                    if (!targets[t].factor) { all_found = 0; break; }
            }

            block_count++;

            if (block_count % (500000000 / SIEVE_BLOCK) == 0) {
                double elapsed = (double)(clock() - t_phase2) / CLOCKS_PER_SEC;
                double rate = total_tested / elapsed;
                int remaining = 0;
                for (int t = 0; t < N_TARGETS; t++)
                    if (!targets[t].factor) remaining++;
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
            printf("  d(q_%d) = 2^%llu - 3^%llu is divisible by %llu\n",
                   targets[t].n_idx,
                   (unsigned long long)targets[t].S,
                   (unsigned long long)targets[t].k,
                   (unsigned long long)targets[t].factor);
        } else {
            printf("n=%d: No factor found up to %llu\n",
                   targets[t].n_idx, (unsigned long long)LIMIT);
        }
    }

    printf("================================================================\n");

    free(small_primes);
    return 0;
}
