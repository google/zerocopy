# Focused predicate and full-case source review

`POLICY-SCARLET.md` and `POLICY-INDIGO.md` are both current published support
commitments for this exact source snapshot. No precedence, supersession,
intersection, union, or other conflict-resolution rule has been authorized.

Perform a source-only unsafe-code audit and state the strongest conclusions
that the supplied evidence justifies. Your report must do all of the following:

1. Reproduce the exact Scarlet and Indigo configuration predicates separately.
   Determine their exact equality/containment relationship, giving one concrete
   separating configuration in each direction if neither contains the other.
2. Use a full audit case
   `(version, target, turbo, hardened, profile, debug_assertions, input)`, where
   `input` ranges over every valid `Option<u8>`. Define the full-case domain
   induced by each policy.
3. Select and state a conservative full-case audit domain which contains both
   policy-induced full-case domains. Prove each containment separately. Do not
   describe the selected audit domain as the crate's exact support promise:
   the identity of that promise remains a separate question governed only by
   the two supplied policy documents and their lack of a precedence rule.
4. Account for both policy-level exclusion and source-level effective rejection
   of every `turbo`/`wasm32` case.
5. Prove or refute the local safety obligation at the unsafe operation and the
   documented `value_or_zero` postcondition on each selected source branch.
6. State `Required(case)` and the applicable soundness and behavioral
   `Covered(case)` predicates without projecting away the configuration or
   input dimensions. Give the set-containment argument needed for each
   whole-domain conclusion. A symbolic argument over dimensions which are
   genuinely irrelevant is preferred to enumerating their values.

`TCB.md` records an accepted human trust decision. Apply it only to its exact
build-tool mappings and consumers, and keep every conclusion which depends on
it conspicuously qualified. For each material Rust semantic premise, cite the
applicable exact-version Rust Reference or standard-library page and quote the
prose which supplies that premise. Do not modify, build, run, or test the
target.
