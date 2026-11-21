#include <stdlib.h>
extern int nondet(void); /* unknown function: each call returns an arbitrary int */
/* Double free reachable on exactly one of 2^2 branch combinations
   (all c_i non-zero). Branch conditions come from calls to an
   unknown function rather than from formal parameters. */
void ndtrue_2(void) {
  int c0 = nondet();
  int c1 = nondet();
  int n = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) n++;
  if (c1) n++;
  free(p);
  if (n == 2) free(p);
}
