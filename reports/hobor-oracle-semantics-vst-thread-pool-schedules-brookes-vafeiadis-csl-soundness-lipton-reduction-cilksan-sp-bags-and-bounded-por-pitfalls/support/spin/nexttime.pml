/* A next-time property is not stutter-invariant. Process A takes
   two local (safe) steps; process B performs one global write.
   The property X (g == 0) is violated exactly by runs in which
   B's write is the first system step. */
byte g = 0;
active proctype A() {
  byte l = 0;
  l++;
  l++
}
active proctype B() {
  g = 1
}
ltl p { X (g == 0) }
