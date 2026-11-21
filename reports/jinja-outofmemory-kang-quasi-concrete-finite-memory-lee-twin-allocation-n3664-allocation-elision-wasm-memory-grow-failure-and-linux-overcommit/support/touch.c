/* Where does exhaustion surface? usage: touch <MiB> [notouch]
   Prints whether malloc returned NULL, then (unless "notouch") writes one
   byte per 4 KiB page, reporting progress every 16 MiB. */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: touch MiB [notouch]\n"); return 64; }
  unsigned long long mib = strtoull(argv[1], NULL, 10);
  size_t n = (size_t)mib << 20;
  errno = 0;
  volatile char *p = malloc(n);
  if (p == NULL) {
    printf("malloc(%llu MiB): NULL (errno=%d %s)\n", mib, errno, strerror(errno));
    return 2;
  }
  printf("malloc(%llu MiB): non-NULL\n", mib);
  fflush(stdout);
  if (argc > 2 && strcmp(argv[2], "notouch") == 0) { free((void *)p); return 0; }
  for (size_t i = 0; i < n; i += 4096) {
    p[i] = 1;
    if (i % ((size_t)16 << 20) == 0) { printf("touched %zu MiB\n", i >> 20); fflush(stdout); }
  }
  printf("touched all %llu MiB\n", mib);
  return 0;
}
