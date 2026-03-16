/*
 * R171 — Vérification Collatz auto-contenue pour le Bloc 3
 * =========================================================
 *
 * Vérifie que tous les entiers de 1 à N_MAX atteignent 1
 * par itérations de la suite de Collatz.
 *
 * Pour le Bloc 3 (k=22-41) : N_MAX = 727,618,686
 *
 * Compilation : gcc -O3 -o collatz_verify R171_collatz_verify.c
 * Exécution : ./collatz_verify
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <stdint.h>

#define N_MAX 727618686ULL  /* Pire cas Bloc 3 : k=41, n_min ≤ 727,618,686 */

int main(void) {
    printf("R171 — Vérification Collatz auto-contenue\n");
    printf("==========================================\n");
    printf("Vérification de tous les entiers de 1 à %llu\n\n", (unsigned long long)N_MAX);

    clock_t start = clock();
    uint64_t max_steps = 0;
    uint64_t hardest_n = 0;

    for (uint64_t n = 2; n <= N_MAX; n++) {
        uint64_t x = n;
        uint64_t steps = 0;

        /* Itérer jusqu'à descendre sous n (déjà vérifié) */
        while (x >= n) {
            if (x & 1) {
                x = 3 * x + 1;
                /* Vérifier l'overflow */
                if (x < n) {
                    printf("ERREUR: overflow pour n=%llu\n", (unsigned long long)n);
                    return 1;
                }
            } else {
                x >>= 1;
            }
            steps++;

            if (steps > 1000000) {
                printf("ALERTE: n=%llu ne converge pas après 1M étapes!\n",
                       (unsigned long long)n);
                return 1;
            }
        }

        if (steps > max_steps) {
            max_steps = steps;
            hardest_n = n;
        }

        /* Progress */
        if (n % 50000000ULL == 0) {
            double pct = 100.0 * n / N_MAX;
            double elapsed = (double)(clock() - start) / CLOCKS_PER_SEC;
            printf("  %12llu / %llu (%.1f%%) — t=%.1fs, max_steps=%llu (n=%llu)\n",
                   (unsigned long long)n, (unsigned long long)N_MAX,
                   pct, elapsed, (unsigned long long)max_steps,
                   (unsigned long long)hardest_n);
            fflush(stdout);
        }
    }

    double elapsed = (double)(clock() - start) / CLOCKS_PER_SEC;

    printf("\n==========================================\n");
    printf("✓ VÉRIFIÉ : tous les entiers de 1 à %llu atteignent 1\n",
           (unsigned long long)N_MAX);
    printf("  Temps total : %.1f secondes\n", elapsed);
    printf("  Étape max : %llu (pour n=%llu)\n",
           (unsigned long long)max_steps, (unsigned long long)hardest_n);
    printf("\n  ★★★ BLOC 3 (k=22-41) PROUVÉ — AUTO-CONTENU ★★★\n");
    printf("==========================================\n");

    return 0;
}
