/* Contraction probe: a*b + c within one expression (f) and across statements (g).
   Inputs chosen so that the exact product 1 - 2^-54 rounds to 1.0 in binary64:
   unfused result is 0, fused result is -2^-54. */
#include <math.h>
#include <stdio.h>
#ifdef USE_PRAGMA_OFF
#pragma STDC FP_CONTRACT OFF
#endif
__attribute__((noinline)) double f(double a, double b, double c) { return a * b + c; }
__attribute__((noinline)) double g(double a, double b, double c) {
  double t = a * b;
  return t + c;
}
int main(void) {
  volatile double a = 1.0 + 0x1p-27, b = 1.0 - 0x1p-27, c = -1.0;
  printf("expr=%a stmt=%a libm_fma=%a\n", f(a, b, c), g(a, b, c), fma(a, b, c));
  return 0;
}
