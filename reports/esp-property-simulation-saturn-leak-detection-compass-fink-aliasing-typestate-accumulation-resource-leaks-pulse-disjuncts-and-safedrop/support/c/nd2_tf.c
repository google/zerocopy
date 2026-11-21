#include <stdlib.h>
extern int nondet(void); /* unknown function: each call returns an arbitrary int */
/* Double free reachable on exactly one of the 4 branch combinations
   (c0 non-zero and c1 zero, so s == 1). */
void nd2_tf(void) {
  int c0 = nondet(), c1 = nondet();
  int s = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) s += 1;
  if (c1) s += 2;
  free(p);
  if (s == 1) free(p);
}
