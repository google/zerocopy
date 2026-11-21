#include <stdlib.h>
extern int nondet(void); /* unknown function: each call returns an arbitrary int */
/* Double free reachable on exactly one of 2^10 branch combinations:
   odd-indexed c_i non-zero and even-indexed c_i zero (s == 682). */
void ndmixed_10(void) {
  int c0 = nondet();
  int c1 = nondet();
  int c2 = nondet();
  int c3 = nondet();
  int c4 = nondet();
  int c5 = nondet();
  int c6 = nondet();
  int c7 = nondet();
  int c8 = nondet();
  int c9 = nondet();
  int s = 0;
  int *p = malloc(sizeof(int));
  if (p == NULL) return;
  if (c0) s += 1;
  if (c1) s += 2;
  if (c2) s += 4;
  if (c3) s += 8;
  if (c4) s += 16;
  if (c5) s += 32;
  if (c6) s += 64;
  if (c7) s += 128;
  if (c8) s += 256;
  if (c9) s += 512;
  free(p);
  if (s == 682) free(p);
}
