#include <stdlib.h>
/* Safe: a flag variable records whether the resource was released. */
void corr_flag(int b) {
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  int released = 0;
  if (b) { free(p); released = 1; }
  if (!released) free(p);
}
