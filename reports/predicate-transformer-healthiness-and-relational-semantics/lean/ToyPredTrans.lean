import ToyPredTrans.Defs
import ToyPredTrans.Basic
import ToyPredTrans.Programs
import ToyPredTrans.Witnesses
import ToyPredTrans.Algebra
import ToyPredTrans.MonotoneNormalForm
import ToyPredTrans.SmallStateSpaces
import ToyPredTrans.Main
import ToyPredTrans.Corollaries

/-!
# Predicate-transformer healthiness laws and relational semantics

* `Defs` — predicates, transformers, relations, `wlp`/`wp`, and every law as a separate
  proposition.
* `Basic` — implications between the laws; the laws satisfied by `wlp` and `wp`.
* `Programs` — example programs and transformers; a positive and a negative example for every
  definition.
* `Witnesses` — tightness counterexamples, non-vacuity theorems, positive controls, and the
  logical-strength witnesses (statements that imply excluded middle or the limited principle
  of omniscience, proved without axioms).
* `Algebra` — `wp`/`wlp` of sequential composition and demonic choice.
* `MonotoneNormalForm` — monotone transformers as angelic choices of demonic updates.
* `SmallStateSpaces` — when finitary conjunctivity suffices: finite state types; with
  ω-continuity, state types that inject into `Nat → Bool`; with continuity over directed
  families, every state type.
* `Main` — the main correspondence results.
* `Corollaries` — consequences of the results in `Main`.
-/
