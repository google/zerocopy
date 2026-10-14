# Generic invariant gate

Run `lean InvariantGate.lean` using the Lean 4.34.1 revision/binary identity in observations.json. Expect exit 0. invariant_gate has no axioms; proposed_checked and all_reachable_even depend only on propext.

The fixture proves the generic initiation/preservation/consequence interface and checks a concrete even-state proposal. It does not run an analyzer or establish an IC3/PDR/liveness certificate mechanism. CheckerAdequacy is a proposed evidence interface, not an implemented Anneal registration system.
