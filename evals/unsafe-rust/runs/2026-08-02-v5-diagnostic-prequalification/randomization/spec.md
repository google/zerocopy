# Randomization Specification — DRAFT / UNSEALED

Integration supplies six distinct evaluator-custodied nonzero 32-byte seeds,
encoded as lowercase 64-hex strings: `condition`, `schedule`, `blind`,
`presentation`, `scorer`, and `consistency`. This directory contains no seed,
stand-in seed, generated map, or unblinding material.

The keyed ordering function is:

```text
SHA256(tag_utf8 || 0x00 || seed_bytes || 0x00 || value_utf8)
```

Items sort lexicographically by that digest and then by their public stable ID.
The seed commitment is a distinct formula:

```text
SHA256((seed_name + "-v5-diagnostic-v1")_utf8 || 0x00 || seed_bytes)
```

There are eight modes, three conditions, and five replicates. The schedule has
five balanced waves of all 24 mode/condition cells, for 120 fresh slots. Each
mode therefore has exactly 15 reports. Blinding assigns the 15 opaque labels
`A` through `O` independently within each mode. Presentation order is keyed by
mode, scorer, and opaque label; scorer-claim and consistency-claim orders use
their dedicated seeds.

Condition labels, target labels, slot order, blind maps, presentation orders,
and commitments are generated only during integration into an explicit empty
output directory. A lock and input manifest, if later approved, are created
after those products and are deliberately absent from this DRAFT.
