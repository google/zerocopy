/* C usual-arithmetic-conversion probe (integer promotions and the usual
 * arithmetic conversions, as summarized by Dietz et al. 2015, Section 3.2).
 *
 * Build/run (UBSan reports the signed-overflow case at run time):
 *   cc -std=c11 -O0 -Wall -Wextra -Wsign-compare -Wconversion \
 *      -fsanitize=undefined c_conversions_probe.c -o c_probe
 *   ./c_probe
 * Assumes an LP64 target with 16-bit short and 32-bit int.
 */
#include <stdint.h>
#include <stdio.h>

static double average_int(int sum, int n) { return sum / n; }   /* int division, then convert */
static double average_fix(int sum, int n) { return (double)sum / n; }

int main(void) {
    printf("sizeof(short)=%zu sizeof(int)=%zu sizeof(long)=%zu\n",
           sizeof(short), sizeof(int), sizeof(long));

    /* 1. signed/unsigned comparison: -1 is converted to UINT_MAX. */
    int minus_one = -1;
    unsigned one_u = 1u;
    printf("(-1 < 1u) = %d\n", minus_one < one_u);

    /* 2. long vs unsigned int on LP64: unsigned int converts to long; no surprise. */
    long minus_one_l = -1L;
    printf("(-1L < 1u) = %d\n", minus_one_l < one_u);

    /* 3. unsigned short * unsigned short promotes to (signed) int. */
    unsigned short a = 65535, b = 65535;
    unsigned int prod = a * b; /* 65535*65535 = 4294836225 > INT_MAX: signed overflow (UB) */
    printf("(unsigned short)65535 * 65535 stored in unsigned = %u\n", prod);

    /* 4. integer division where real division was meant. */
    printf("average_int(7, 2) = %f\n", average_int(7, 2));
    printf("average_fix(7, 2) = %f\n", average_fix(7, 2));

    /* 5. truncation toward zero for negative operands (C99 and later). */
    printf("-7 / 2 = %d, -7 %% 2 = %d\n", -7 / 2, -7 % 2);

    /* 6. int -> float precision loss. */
    int big = 16777217; /* 2^24 + 1 */
    float f = (float)big;
    printf("(float)16777217 = %.1f\n", f);

    /* 7. unsigned wraparound is defined. */
    unsigned u0 = 0u;
    printf("0u - 1 = %u\n", u0 - 1u);

    /* 8. uint8_t arithmetic promotes to int, then narrows on assignment. */
    uint8_t x = 200, y = 100;
    uint8_t s = (uint8_t)(x + y);
    printf("(uint8_t)(200 + 100) = %u, (x + y) as int = %d\n", s, x + y);
    return 0;
}
