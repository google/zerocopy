/* Probe: does compiler floating-point contraction break Dekker's error-free TwoProduct?
 *
 * Dekker's TwoProduct (Dekker 1971; Ogita-Rump-Oishi 2005, Algorithms 3.2/3.3) computes
 * x = fl(a*b) and y with a*b = x + y exactly, using only round-to-nearest +, -, *.
 * Its correctness argument assumes every operation is individually rounded. If the
 * compiler fuses a multiply and a dependent add/subtract into one FMA ("contraction"),
 * that assumption no longer holds.
 *
 * Exactness is checked with __float128 (113-bit significand), in which the product of
 * two binary64 numbers (<= 106 significant bits) and the sum x + y are exact.
 *
 * Build/run (see REPORT.md for the recorded results):
 *   gcc -O2 -march=x86-64-v3                    eft_contract.c -o c_default && ./c_default
 *   gcc -O2 -march=x86-64-v3 -ffp-contract=off  eft_contract.c -o c_off     && ./c_off
 *   gcc -O2 -march=x86-64-v3 -std=c17           eft_contract.c -o c_iso     && ./c_iso
 */
#include <stdio.h>
#include <stdint.h>

static uint64_t s = 0x9E3779B97F4A7C15ull;
static double rnd(void) {                /* xorshift64*, uniform-ish in (-1, 1) * 2^k */
    s ^= s >> 12; s ^= s << 25; s ^= s >> 27;
    uint64_t r = s * 0x2545F4914F6CDD1Dull;
    double m = (double)(r >> 11) / 9007199254740992.0;  /* [0,1) with 53 bits */
    int k = (int)((r >> 3) & 31) - 16;
    double v = (2.0 * m - 1.0);
    while (k > 0) { v *= 2.0; k--; }
    while (k < 0) { v *= 0.5; k++; }
    return v;
}

static void split(double a, double *hi, double *lo) {
    const double factor = 134217729.0;   /* 2^27 + 1 */
    double c = factor * a;
    double x = c - (c - a);
    *hi = x;
    *lo = a - x;
}

static void two_product_dekker(double a, double b, double *x, double *y) {
    double a1, a2, b1, b2;
    *x = a * b;
    split(a, &a1, &a2);
    split(b, &b1, &b2);
    *y = a2 * b2 - (((*x - a1 * b1) - a2 * b1) - a1 * b2);
}

int main(void) {
    const long N = 2000000;
    long bad = 0;
    for (long i = 0; i < N; i++) {
        double a = rnd(), b = rnd(), x, y;
        two_product_dekker(a, b, &x, &y);
        __float128 exact = (__float128)a * (__float128)b;
        __float128 got = (__float128)x + (__float128)y;
        if (exact != got) bad++;
    }
    printf("pairs=%ld not_error_free=%ld (%.4f%%)\n", N, bad, 100.0 * (double)bad / (double)N);
    return 0;
}
