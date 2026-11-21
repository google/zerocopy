/* Probe: cost of subnormal operands/results for scalar SSE2 double multiply on
   the host CPU, with MXCSR FTZ/DAZ off (IEEE gradual underflow) and on.
   Build: cc -O2 denormal_cost.c -o denormal_cost ; run: ./denormal_cost */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <xmmintrin.h>

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
/* dependent chain: latency-bound */
__attribute__((noinline)) static double chain(double x, double m, long n) {
  for (long i = 0; i < n; i++) x = x * m;
  return x;
}
/* 8 independent chains: throughput-bound */
__attribute__((noinline)) static double indep(double x, double m, long n) {
  double a=x,b=x,c=x,d=x,e=x,f=x,g=x,h=x;
  for (long i = 0; i < n; i++) { a*=m; b*=m; c*=m; d*=m; e*=m; f*=m; g*=m; h*=m; }
  return a+b+c+d+e+f+g+h;
}
static int cmp(const void *p, const void *q) { double a=*(double*)p,b=*(double*)q; return (a>b)-(a<b); }
static double bench(double (*fn)(double,double,long), double x, double m, long n, int ops) {
  double t[7], sink = 0;
  for (int r = 0; r < 7; r++) { double s = now(); sink += fn(x, m, n); t[r] = (now() - s) / ((double)n * ops) * 1e9; }
  qsort(t, 7, sizeof t[0], cmp);
  if (sink == 12345.0) puts("");
  return t[3]; /* median ns per multiply */
}
int main(void) {
  volatile double vm = 1.0, vnorm = 1e-300, vsub = 1e-310;
  double m = vm, xn = vnorm, xs = vsub;
  long n = 20000000;
  for (int mode = 0; mode < 2; mode++) {
    _mm_setcsr(mode ? (0x1f80 | 0x8040) : 0x1f80);
    printf("MXCSR=0x%04x  chain normal %.3f ns/op  chain subnormal %.3f ns/op  indep normal %.3f ns/op  indep subnormal %.3f ns/op\n",
           _mm_getcsr(), bench(chain, xn, m, n, 1), bench(chain, xs, m, n, 1), bench(indep, xn, m, n/4, 8), bench(indep, xs, m, n/4, 8));
  }
  return 0;
}
