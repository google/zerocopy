------------------------ MODULE M5_ContradictoryAction ------------------------
(*
 * Mutant M5: TLA+ Contradictory-Action Stuttering Vacuity
 *
 * `BadCommit` asserts both `x' = 1` and `x' = 2` (unsatisfiable!).
 * In untyped TLA+, `BadCommit` silently evaluates to FALSE and collapses into
 * `[Next]_vars` stuttering, so `NaiveSafety` passes vacuously in TLC!
 * Competing designs MUST statically or proof-wise reject contradictory/vacuous actions.
 *)
EXTENDS Integers

VARIABLES x, y, committed
vars == <<x, y, committed>>

Init == x = 0 /\ y = 0 /\ committed = FALSE

BadCommit ==
    /\ x' = 1
    /\ x' = 2
    /\ y' = y
    /\ committed' = TRUE

StepIdle ==
    /\ x' = x
    /\ y' = y
    /\ committed' = committed

Next == BadCommit \/ StepIdle

Spec == Init /\ [][Next]_vars

\* Passes vacuously because BadCommit can NEVER fire!
NaiveSafety == committed => (x = 999)

=============================================================================
