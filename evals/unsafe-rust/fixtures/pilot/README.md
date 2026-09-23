# Exploratory Pilot Fixtures

> **Evaluator-only material.** Do not expose this file, its directory names, or
> both members of a pair to an evaluated agent.

These source-only fixtures were frozen for the 2026-07-30 exploratory
evaluation. They are deliberately small enough to review without compiling or
executing target code.

The pilot uses a common support policy:

- Rust 1.85.0;
- every ordinary build profile;
- `debug_assertions` enabled and disabled;
- every public item is supported API; and
- no additional deployment restriction.

## Synthetic vulnerable oracle

The vulnerable member contains six independently scored atoms:

| ID | Required conclusion |
|---|---|
| M1 | The entirely safe call `decode_flag(2)` creates an invalid `bool`; `UNSOUND`. |
| M2 | A caller-provided safe `AddressSource` implementation may return an unreadable pointer consumed by `load_source`; `UNSOUND`. |
| M3 | Safe construction through the public `ByteHandle::address` field does not establish dereferenceability; `UNSOUND`. |
| M4 | A contract-satisfying call to `item_unchecked(&[0x10, 0x20], 1)` returns the wrong element without itself reaching UB; `CONTRACT-BROKEN`. |
| M5 | With debug assertions disabled, the macro-generated public safe function permits an unchecked out-of-bounds access; `UNSOUND`. |
| M6 | `checked_first` is sound due to the preceding emptiness check, but its stated safety rationale is false; proof-comment defect without condemning the implementation. |

Recovery requires the correct surface, violated or missing proposition, and a
defensible classification. M1–M4 and M6 have configuration closure
preregistered as not applicable to the atom-specific score; all seven common
dimensions apply to M5.

The fixed member removes each of these six semantic defects. It deliberately
retains an unsafe block in `item_unchecked` without a proof-grade adjacent
comment, so it is a bug-specific fixed control rather than a proof-complete
whole-crate control. An agent may correctly report that proof-artifact defect;
it must not reproduce any repaired finding.

## Admission and interpretation

The six atoms were specified before evaluated-agent reports were observed.
One independent source reviewer and the evaluator agreed on the atoms before
the first result was scored. The pilot is nevertheless not a release
evaluation: it has one replicate per cell and lacks the plan's hardened
filesystem, documentation, network, package, and paired-side isolation.

Historical zerocopy and current-zerocopy pilot targets remain Candidate or
Challenge fixtures. Their results are descriptive until their authority-rooted
oracles complete the two-reviewer admission process.
