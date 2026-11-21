/* Is the mode-0 heuristic per request or cumulative? usage: multi <MiB> <count>
   Performs <count> mallocs of <MiB> each without touching them. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
int main(int argc, char **argv) {
  unsigned long long mib = strtoull(argv[1], NULL, 10);
  int count = atoi(argv[2]);
  for (int i = 0; i < count; i++) {
    struct timespec a, b;
    clock_gettime(CLOCK_MONOTONIC, &a);
    void *p = malloc((size_t)mib << 20);
    clock_gettime(CLOCK_MONOTONIC, &b);
    long ns = (b.tv_sec - a.tv_sec) * 1000000000L + (b.tv_nsec - a.tv_nsec);
    printf("malloc #%d (%llu MiB): %s in %ld ns\n", i + 1, mib, p ? "non-NULL" : "NULL", ns);
  }
  return 0;
}
