#include <stdlib.h>
/* Bug: leak on the path where b is zero. */
void leak_bug(int b) {
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (b) free(p);
}
