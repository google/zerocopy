# Focused source-only review

Audit the safe API in `lib.rs` on exactly Rust 1.80.0, every target on which
this exact source and the used Rust 1.80.0 standard-library item exist, and
every ordinary debug or release profile. Report separate conclusions for:

1. freedom from undefined behavior for every valid safe call;
2. the documented input-zero panic guarantee; and
3. the documented normal-return result guarantee.

For any negative conclusion, give the exact witness and justify which claimed
theorem that witness can establish. Analyze distinct inputs independently.

This is a source-only review. Do not build, test, execute, inspect evaluator
material, or edit the source. You may open only the exact versioned official
Rust URLs named in `EVIDENCE.md` to verify the supplied propositions.
