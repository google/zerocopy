/* Allocation-elision probe (C). 1 PiB exceeds the 128 TiB user address
   space of x86-64 4-level paging, so a real malloc call must fail. */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  void *p = malloc((size_t)1 << 50);
  if (p == NULL) { puts("malloc(2^50): NULL"); return 1; }
  free(p);
  puts("malloc(2^50): non-NULL");
  return 0;
}
