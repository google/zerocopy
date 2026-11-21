#include <stddef.h>
/* Safe: p is dereferenced only when it was set. */
int corr_null(int b) {
  int x = 0;
  int *p = NULL;
  if (b) p = &x;
  if (b) *p = 1;
  return x;
}
