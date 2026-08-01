# Multi-release source-only review

Audit the four exported unsafe APIs in `lib.rs` as four independent claims over
their exact release sets in `SUPPORT.md`. For each API, report soundness and
every documented postcondition separately, recover `Required`, state the exact
`Covered` release region justified by the submitted evidence, and give the
strongest combined verdict. Report every regional result material to that
verdict.

The authority entries and their claim-specific applicability are exactly those
in `EVIDENCE.md`. The only non-authoritative admitted premises are the two
accepted, narrowly scoped entries in `TCB.md`. Do not transfer an entry between
different operations merely because their contracts or implementations look
similar.

This is a source-only evidence-packet review. Do not build, test, execute,
inspect evaluator material, edit source, search for other Rust releases, or add
new evidence. You may open only the exact versioned official Rust URLs already
named in `EVIDENCE.md` to verify the supplied propositions.
