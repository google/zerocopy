/* Excess-precision probe: a*b overflows binary64 but not the x87 80-bit format.
   h(): one expression.  k(): the product is assigned to a double first. */
#include <float.h>
#include <stdio.h>
__attribute__((noinline)) double h(double a, double b, double c) { return a * b / c; }
__attribute__((noinline)) double k(double a, double b, double c) {
  double t = a * b;
  return t / c;
}
int main(void) {
  volatile double a = 1e308, b = 10.0, c = 100.0;
  printf("FLT_EVAL_METHOD=%d expr=%g assigned=%g\n", (int)FLT_EVAL_METHOD, h(a, b, c), k(a, b, c));
  return 0;
}
