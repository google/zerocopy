# Scoped lead: Lean-native Iris remains a separate feasibility investigation

## Inspected source establishes a lead, not parity

Directly inspected source at `leanprover-community/iris-lean@04b7689c294bb1dd6401e2dd53b337871934ea47` includes `Iris/Iris/ProgramLogic/Adequacy.lean`, with `adequate`, `wp_adequacy_gen`, and `adequate_tp_safe`. The tree also contains `TotalAdequacy.lean`, `TotalWeakestPre.lean`, cameras and proof-mode modules. File existence is a lead for a fuller audit; it does not establish complete Rocq-Iris feature parity or a closed proof dependency chain.

## Anneal and library pins differ

The inspected Lean pin is `leanprover/lean4:v4.34.1`; `Iris/lakefile.toml` requests Qq and Batteries at `v4.34.0`. The assigned zerocopy main snapshot `8d8ed8dcc98c991d32cee3c3a84e129f29cba136` embeds Lean `v4.31.0` in `anneal/v1/Cargo.toml`. PR-stack `cce761ad53785973ec2f4a6b13715b770b340c87` likewise pins `anneal/lean/lean-toolchain` to `v4.31.0`. Compatibility was not built or tested.

## The Rust instantiation and trust audit remain open

R029 and R087 remain partial leads, with P114 integration implications. A useful next bounded investigation is: identify the exact imported assumption closure of one adequacy theorem, inventory lifetime/parametric-prophecy and invariant constructions actually needed by a Rust instance, then try a small adequacy/resource build with already available dependencies and an explicit Lean-pin decision. No Rust operational instance or semantic-typing layer was established here.

Observed on 2026-10-14. Basis: source only. [Adequacy source](https://github.com/leanprover-community/iris-lean/blob/04b7689c294bb1dd6401e2dd53b337871934ea47/Iris/Iris/ProgramLogic/Adequacy.lean), [Lean pin](https://github.com/leanprover-community/iris-lean/blob/04b7689c294bb1dd6401e2dd53b337871934ea47/Iris/lean-toolchain), [dependencies](https://github.com/leanprover-community/iris-lean/blob/04b7689c294bb1dd6401e2dd53b337871934ea47/Iris/lakefile.toml).

*Authored by an AI agent acting on joshlf's behalf.*
