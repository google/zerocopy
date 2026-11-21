#include <stdlib.h>
/* Double free reachable only when exactly one formal parameter is non-zero. */
void param2_one(int c0, int c1) {
  int n = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) n++;
  if (c1) n++;
  free(p);
  if (n == 1) free(p);
}
