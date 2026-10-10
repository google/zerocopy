# Admission fixture

`boolean.before.ullbc` contains the two function declarations and value carriers
needed by `checked_bool` from the pinned Charon 0.1.276 promoted-MIR extraction.
Unrelated declarations and crate bookkeeping are omitted; executable bodies,
signatures, attributes, options, and target information remain from the actual
extraction. JSON whitespace is compressed to avoid a large generated diff.

Regenerate with `run.sh --extract-only`, then select `checked_bool`,
`transmute_unchecked`, the unit carrier, and `Option` from
`target/aeneas/verification/zerocopy.before.ullbc`. Keep the options profile intact.
The mutation tests never execute invalid Rust; they challenge admission of the
compiler's intermediate representation. Lean and native Rust tests check the
accepted helper models and safe callers separately.
