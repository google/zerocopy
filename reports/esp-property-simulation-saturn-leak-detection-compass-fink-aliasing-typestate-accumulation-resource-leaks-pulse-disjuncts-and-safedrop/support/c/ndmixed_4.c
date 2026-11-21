#include <stdlib.h>
extern int nondet(void); /* unknown function: each call returns an arbitrary int */
/* Double free reachable on exactly one of 2^4 branch combinations:
   odd-indexed c_i non-zero and even-indexed c_i zero (s == 10). */
void ndmixed_4(void) {
  int c0 = nondet();
  int c1 = nondet();
  int c2 = nondet();
  int c3 = nondet();
  int s = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) s += 1;
  if (c1) s += 2;
  if (c2) s += 4;
  if (c3) s += 8;
  free(p);
  if (s == 10) free(p);
}
