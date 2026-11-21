/* N processes, each performing K purely local increments.
   Every transition touches only process-local state, so all
   transitions are "safe" for Spin's partial-order reduction. */
#ifndef N
#define N 3
#endif
#ifndef K
#define K 3
#endif
active [N] proctype P() {
  byte i = 0;
  do
  :: i < K -> i++
  :: else -> break
  od
}
