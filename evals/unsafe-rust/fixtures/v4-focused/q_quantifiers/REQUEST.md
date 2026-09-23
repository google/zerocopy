# Focused source-only review

Audit the soundness of both exported APIs in `lib.rs` as separate claims. For
each claim, state the exact valid-use and compilation domain, the strongest
verdict justified by the supplied source and evidence, and the complete proof
or the smallest missing proposition.

The supported domain is exactly Rust 1.80.0, every target on which this source
and its exact dependency resolve, and every ordinary debug or release profile.
The dependency resolution, submitted dependency API, evidence policy, and trust
decision are part of the review.

This is a source-only evidence-packet review. Do not build, test, execute,
download dependency source, inspect any evaluator material, or edit the source.
You may open only the exact versioned official Rust URL named in `EVIDENCE.md`
to verify its supplied proposition. Do not assume facts about the unavailable
dependency implementation beyond an accepted TCB entry.
