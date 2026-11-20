# Toy.AbsInt — Galois connections, best abstract transformers, fixpoint transfer

Self-contained Lake project (Lean `v4.34.1`, no dependencies, no Mathlib).

* `Toy/AbsInt/Basic.lean` — concrete domain `Pred σ`, order laws, monotonicity, chain conditions.
* `Toy/AbsInt/Domains.lean` — small fixture domains used by examples and counterexamples.
* `Toy/AbsInt/Galois.lean` — Galois connections and their characterization by four laws.
* `Toy/AbsInt/Sign.lean` — the sign domain with a proved Galois connection.
* `Toy/AbsInt/Transformer.lean` — best abstract transformers and their composition.
* `Toy/AbsInt/Fixpoint.lean` — least fixpoints, fixpoint transfer, Kleene iteration.
* `Toy/AbsInt/Widening.lean` — widening operators and iteration with widening.

Build with `lake build`.
