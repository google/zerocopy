#include <stdlib.h>
/* Double free reachable only when c0 is zero and c1 is non-zero (s == 2). */
void param2_ft(int c0, int c1) {
  int s = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) s += 1;
  if (c1) s += 2;
  free(p);
  if (s == 2) free(p);
}
