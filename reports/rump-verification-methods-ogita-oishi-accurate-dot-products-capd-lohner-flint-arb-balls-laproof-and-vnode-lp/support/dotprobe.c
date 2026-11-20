/* Probe: compiler flags vs. error-free transformations, and the run-time cost of Dot2.
 *
 * Implements, in C99:
 *   dot_naive      recursive dot product, s = s + x[i]*y[i]
 *   dot2_fma       Dot2 (Ogita-Rump-Oishi 2005, Alg. 5.3) with TwoProduct via fma()
 *   dot2_dekker    Dot2 with Dekker's Split-based TwoProduct (no FMA needed)
 * These are independent re-implementations, not library code.
 *
 * Modes:
 *   ./dotprobe acc  <file>   read n, then n pairs (x_i, y_i) as binary64 from <file>;
 *                            print the three results as C99 hex floats (for exact checking
 *                            in Python with fractions.Fraction; see check_dot.py)
 *   ./dotprobe time <n> <reps>  time the three kernels on random data of length n
 *
 * Build variants used in REPORT.md:
 *   gcc -O2 -std=c99 -march=x86-64-v3 -ffp-contract=off dotprobe.c -lm -o dot_strict
 *   gcc -O2 -std=gnu99 -march=x86-64-v3                 dotprobe.c -lm -o dot_gnu      (contraction default: fast)
 *   gcc -O2 -std=c99 -march=x86-64-v3 -ffast-math       dotprobe.c -lm -o dot_fastmath
 */
#define _POSIX_C_SOURCE 199309L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static inline void two_sum(double a, double b, double *x, double *y) {
    double s = a + b;
    double z = s - a;
    *y = (a - (s - z)) + (b - z);
    *x = s;
}

static inline void two_prod_fma(double a, double b, double *x, double *y) {
    double p = a * b;
    *y = fma(a, b, -p);
    *x = p;
}

static inline void split(double a, double *hi, double *lo) {
    double c = 134217729.0 * a;   /* 2^27 + 1 */
    double h = c - (c - a);
    *hi = h;
    *lo = a - h;
}

static inline void two_prod_dekker(double a, double b, double *x, double *y) {
    double a1, a2, b1, b2, p = a * b;
    split(a, &a1, &a2);
    split(b, &b1, &b2);
    *y = a2 * b2 - (((p - a1 * b1) - a2 * b1) - a1 * b2);
    *x = p;
}

__attribute__((noinline)) double dot_naive(const double *x, const double *y, long n) {
    double s = 0.0;
    for (long i = 0; i < n; i++) s = s + x[i] * y[i];
    return s;
}

__attribute__((noinline)) double dot2_fma(const double *x, const double *y, long n) {
    double p, s, h, r, q;
    two_prod_fma(x[0], y[0], &p, &s);
    for (long i = 1; i < n; i++) {
        two_prod_fma(x[i], y[i], &h, &r);
        two_sum(p, h, &p, &q);
        s = s + (q + r);
    }
    return p + s;
}

__attribute__((noinline)) double dot2_dekker(const double *x, const double *y, long n) {
    double p, s, h, r, q;
    two_prod_dekker(x[0], y[0], &p, &s);
    for (long i = 1; i < n; i++) {
        two_prod_dekker(x[i], y[i], &h, &r);
        two_sum(p, h, &p, &q);
        s = s + (q + r);
    }
    return p + s;
}

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

int main(int argc, char **argv) {
    if (argc >= 3 && strcmp(argv[1], "acc") == 0) {
        FILE *f = fopen(argv[2], "rb");
        if (!f) return 2;
        int64_t n;
        if (fread(&n, sizeof n, 1, f) != 1) return 2;
        double *x = malloc(sizeof(double) * n), *y = malloc(sizeof(double) * n);
        for (int64_t i = 0; i < n; i++) {
            if (fread(&x[i], 8, 1, f) != 1 || fread(&y[i], 8, 1, f) != 1) return 2;
        }
        fclose(f);
        printf("%a %a %a\n", dot_naive(x, y, n), dot2_fma(x, y, n), dot2_dekker(x, y, n));
        return 0;
    }
    if (argc >= 4 && strcmp(argv[1], "time") == 0) {
        long n = atol(argv[2]), reps = atol(argv[3]);
        double *x = malloc(sizeof(double) * n), *y = malloc(sizeof(double) * n);
        srand(12345);
        for (long i = 0; i < n; i++) {
            x[i] = (double)rand() / RAND_MAX - 0.5;
            y[i] = (double)rand() / RAND_MAX - 0.5;
        }
        double (*fns[3])(const double *, const double *, long) = {dot_naive, dot2_fma, dot2_dekker};
        const char *names[3] = {"naive", "dot2_fma", "dot2_dekker"};
        double best[3] = {1e30, 1e30, 1e30}, sink = 0;
        for (int trial = 0; trial < 5; trial++) {
            for (int k = 0; k < 3; k++) {
                double t0 = now();
                for (long r = 0; r < reps; r++) sink += fns[k](x, y, n);
                double dt = (now() - t0) / (double)reps / (double)n * 1e9;
                if (dt < best[k]) best[k] = dt;
            }
        }
        for (int k = 0; k < 3; k++)
            printf("%-12s n=%ld ns/element=%.3f ratio_to_naive=%.2f\n", names[k], n, best[k], best[k] / best[0]);
        fprintf(stderr, "sink=%g\n", sink);
        return 0;
    }
    fprintf(stderr, "usage: %s acc <file> | time <n> <reps>\n", argv[0]);
    return 2;
}
