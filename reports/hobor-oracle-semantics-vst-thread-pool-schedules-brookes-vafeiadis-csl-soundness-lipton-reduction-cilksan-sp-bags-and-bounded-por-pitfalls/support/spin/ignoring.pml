/* Classic "ignoring" shape: process A has an infinite loop of
   purely local (safe) transitions; process B performs a global
   write followed by a failing assertion. A reduction that always
   preselects A without a cycle proviso would never schedule B. */
byte g = 0;
active proctype A() {
  bit l = 0;
  do
  :: l = 1 - l
  od
}
active proctype B() {
  g = 1;
  assert(g == 0)
}
