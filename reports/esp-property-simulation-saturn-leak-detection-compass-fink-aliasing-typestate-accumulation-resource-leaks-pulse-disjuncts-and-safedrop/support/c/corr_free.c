#include <stdlib.h>
/* Safe: the two branches test the same condition, so exactly one free runs. */
void corr_free(int b) {
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (b) free(p);
  if (!b) free(p);
}
