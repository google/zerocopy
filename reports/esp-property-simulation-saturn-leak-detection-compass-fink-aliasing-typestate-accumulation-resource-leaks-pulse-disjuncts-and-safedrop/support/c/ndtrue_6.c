#include <stdlib.h>
extern int nondet(void); /* unknown function: each call returns an arbitrary int */
/* Double free reachable on exactly one of 2^6 branch combinations
   (all c_i non-zero). Branch conditions come from calls to an
   unknown function rather than from formal parameters. */
void ndtrue_6(void) {
  int c0 = nondet();
  int c1 = nondet();
  int c2 = nondet();
  int c3 = nondet();
  int c4 = nondet();
  int c5 = nondet();
  int n = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) n++;
  if (c1) n++;
  if (c2) n++;
  if (c3) n++;
  if (c4) n++;
  if (c5) n++;
  free(p);
  if (n == 6) free(p);
}
