# LRAT controls

Run `lean LratControls.lean` using Lean 4.34.1 at the revision/binary identity in observations.json. Expect exit 0, Boolean outputs true/true/false, parsed one-step certificate output, and the retained axiom lists. The changedSatWitness uses kernel reduction; checker equalities and sourceUnsat deliberately use native_decide.

The .first-failed files preserve the original ordinary-decide run with its wrong shortened-hint negative expectation. That run exits 1 and contains recovery sorryAx dependencies. It is a failed diagnostic, not an accepted proof. To repeat it without touching the successful fixture, copy LratControls.lean.first-failed to a temporary diagnostic name and invoke Lean on that file.

direct-import-artifacts.json hashes the three directly imported olean artifacts. It is not a complete transitive runtime/library identity or an executable-correctness proof.
