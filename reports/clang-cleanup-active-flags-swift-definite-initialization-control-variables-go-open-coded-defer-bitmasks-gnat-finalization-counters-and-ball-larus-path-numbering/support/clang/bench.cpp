// Timing driver: calls the flag-based (t_cond) and hand-duplicated
// (t_cond_dup) functions N times each with an alternating condition.
#include <cstdio>
#include <cstdlib>
#include <ctime>
int t_cond(bool c, int x);
int t_cond_dup(bool c, int x);
static double now() {
  timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + ts.tv_nsec * 1e-9;
}
int main(int argc, char **argv) {
  long n = argc > 1 ? atol(argv[1]) : 100000000L;
  int pattern = argc > 2 ? atoi(argv[2]) : 0; // 0: alternate, 1: always true, 2: always false
  long acc = 0;
  for (int rep = 0; rep < 3; ++rep) {
    double t0 = now();
    for (long i = 0; i < n; ++i) {
      bool c = pattern == 0 ? (i & 1) : pattern == 1;
      acc += t_cond(c, (int)i);
    }
    double t1 = now();
    for (long i = 0; i < n; ++i) {
      bool c = pattern == 0 ? (i & 1) : pattern == 1;
      acc += t_cond_dup(c, (int)i);
    }
    double t2 = now();
    printf("rep=%d flag_ns_per_call=%.3f dup_ns_per_call=%.3f\n", rep,
           (t1 - t0) * 1e9 / n, (t2 - t1) * 1e9 / n);
  }
  printf("acc=%ld\n", acc);
  return 0;
}
