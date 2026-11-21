/* Probe: cost of saving and restoring floating-point control state with
   different interfaces (direct MXCSR access, x87 CW, fegetenv/fesetenv,
   fegetround/fesetround). Build: cc -O2 save_restore_cost.c -o save_restore_cost -lm */
#include <fenv.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <xmmintrin.h>
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static int cmp(const void *p, const void *q) { double a=*(double*)p,b=*(double*)q; return (a>b)-(a<b); }
#define BENCH(name, body) do { double t[7]; long n = 5000000; \
  for (int r = 0; r < 7; r++) { double s = now(); for (long i = 0; i < n; i++) { body; } t[r] = (now()-s)/n*1e9; } \
  qsort(t, 7, sizeof t[0], cmp); printf("%-44s median %.2f ns per save+restore pair\n", name, t[3]); } while (0)
int main(void) {
  BENCH("stmxcsr + ldmxcsr", { unsigned v = _mm_getcsr(); __asm__ volatile("" ::: "memory"); _mm_setcsr(v); });
  BENCH("stmxcsr+fnstcw + ldmxcsr+fldcw", { unsigned v = _mm_getcsr(); unsigned short cw; __asm__ volatile("fnstcw %0" : "=m"(cw)); _mm_setcsr(v); __asm__ volatile("fldcw %0" :: "m"(cw)); });
  BENCH("fegetenv + fesetenv (glibc)", { fenv_t e; fegetenv(&e); __asm__ volatile("" ::: "memory"); fesetenv(&e); });
  BENCH("fegetround + fesetround (glibc)", { int r = fegetround(); __asm__ volatile("" ::: "memory"); fesetround(r); });
  return 0;
}
