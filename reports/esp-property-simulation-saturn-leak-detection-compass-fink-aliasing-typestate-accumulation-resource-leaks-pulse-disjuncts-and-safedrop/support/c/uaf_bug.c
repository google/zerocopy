#include <stdlib.h>
/* Bug: use after free on the path where b is non-zero. */
void uaf_bug(int b) {
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (b) free(p);
  if (b) *p = 1;
  if (!b) free(p);
}
