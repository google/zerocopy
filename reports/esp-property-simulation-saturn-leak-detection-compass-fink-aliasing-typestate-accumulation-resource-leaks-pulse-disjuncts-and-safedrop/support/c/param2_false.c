#include <stdlib.h>
/* Double free reachable only when both formal parameters are zero. */
void param2_false(int c0, int c1) {
  int n = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) n++;
  if (c1) n++;
  free(p);
  if (n == 0) free(p);
}
