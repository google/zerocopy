# 2026-07-31 Legacy Regression Replay Result

Protocol and identities: [`manifest.md`](manifest.md).

## Disposition

**Exploratory pass with one unconfirmed improvement hypothesis.** The revised
skill preserved every objective known-issue and fixed-control behavior from the
old pilot and introduced no hard error. It improved the current challenge on
version applicability and literal contract closure. It did not reliably cause
the agent to complete a valid indirect `Copy`/`UnsafeCell` derivation.

This is one replicate under procedural isolation, not evidence of statistical
lift or release readiness.

## Objective regression results

| Target | Revised skill | Contemporary baseline | Regression result |
|---|---|---|---|
| Synthetic vulnerable | `6/6`, `78/78`, no hard error | `6/6`, `78/78`, no hard error | Pass; ceiling tie |
| Synthetic fixed | No repaired atom; scoped `PROVED`; missing proof comment reconstructed and reported | No repaired atom; scoped pass; missing proof comment omitted | Pass; treatment wins proof-artifact control |
| Historical vulnerable | Admitted defect recovered; `14/14` | Defect recovered; minor authority/coverage scoring disagreement | Pass |
| Historical fixed | Exact defect closed; detailed in-place-zeroing proof; no repaired false positive | Exact defect closed; no repaired false positive | Pass |
| Current challenge | `UNPROVED`; no production `UNSOUND`; test-only scope correct | No whole-target proof; no production `UNSOUND` | Pass on preregistered calibration |

The blind synthetic scorer assigned both vulnerable reports `78/78`. Unlike the
prior pilot's `78` versus `73`, this replicate's no-skill agent supplied enough
detail to reach the ceiling. The result establishes non-regression, not lift.

The independent historical scorer assigned the skill report `14/14`. It
assigned the baseline `12/14`, partly because it incorrectly treated links to
the baseline's own opaque target copy as out-of-scope. That deduction is
invalid: the paired copies had identical verified bundle hashes. The baseline
report is semantically correct; its representation-layout citation and explicit
configuration closure are less complete than the skill report, but this does
not affect the treatment regression gate.

Both fixed historical reports prove the essential repair: `uninit(); zero()`
writes the complete final object storage in place before a byte-slice reference
is constructed. The skill report additionally exposes material proof-comment
debt rather than silently accepting the implementation.

## Current-source comparison

| Behavior | Revised skill | Baseline | Adjudication |
|---|---|---|---|
| Overall production result | `UNPROVED`; no UB witness | No unconditional defect claimed | Calibrated |
| Rust 1.56 versus later citations | Found exact Option and broader range gaps | Applied Rust 1.89 Option guarantee across the target | Treatment improvement confirmed |
| Literal `ManuallyDrop::HasField` clauses | Found visibility/name/model mismatch | Declared projection compliant | Treatment improvement confirmed as obligation discovery; final contract interpretation remains disputed |
| Optional function-pointer/`NonNull` `Immutable` | Left unproved | Accepted without visible derivation | Valid indirect `Copy`/`UnsafeCell` proof omitted by both; treatment false positive |
| `Box<T>: Immutable` | Found incomplete normative proof | Blanket approval outside SIMD | Treatment improvement |
| SIMD | Found universal gap | Found universal gap | Tie |
| Generated `KnownLayout` provenance | Found `NonNull::cast` documentation gap | Missed | Treatment improvement |
| Test-only `assume_initialized` | Correctly `cfg(test)` and `UNPROVED`, not production UB | Not emphasized in final findings | Treatment scope correct |
| Safe transmute-delegation macro | Not reported | Found latent size-equality contract hole; no current bad invocation | Valid baseline-only maintenance finding |
| Missing fixture inputs | Explicitly excluded derive/dependency closure | Mentioned omitted derive/path dependency | Both avoid whole-crate proof |

The skill report overgeneralized the Rust-version gap for stable primitive
numerics: later citations were inapplicable, but exact Rust 1.56 conversion and
representation APIs can reconstruct several required facts. That is an
overbroad `UNPROVED`, not a hard error or unsoundness claim.

The `HasField` result must remain calibrated. Literal review correctly exposes
that the checked-in comment substitutes “effectively public” for the contract's
visibility clause. The contract also permits a field belonging to any
layout-equivalent struct, so a public transparent proxy-field model may be a
valid proof route. The replay therefore admits obligation discovery and the
missing literal derivation, not a final `CONTRACT-BROKEN` verdict.

## Planned-improvement checks

| Hypothesis | Result | Evidence |
|---|---|---|
| Applicability follows every premise | **Pass** | Treatment rejects backward use of Rust 1.89 Option prose for Rust 1.56–1.88 and states the missing version interval. |
| Every literal contract clause receives a disposition | **Pass** | Treatment separately identifies the `HasField` visibility/name/model clauses instead of accepting operational projection alone. |
| Search closes valid indirect multi-premise proofs | **Fail** | Treatment still calls optional function-pointer and `NonNull` `Immutable` impls unproved instead of deriving the sufficient fact through exact `Copy` and `UnsafeCell` rules. |
| Material reconstructed proofs are visible | **Partial pass** | Synthetic fixed and historical fixed reports expose full reconstructed derivations and proof-artifact defects; the current indirect proof was not reconstructed. |

## Quality and hard-error review

- No known vulnerable atom was missed by a skill-enabled report.
- No repaired atom was reproduced on a fixed control.
- No skill report issued unsupported production `UNSOUND` or a whole-current
  `PROVED`.
- Caller-provided safe `Read` and safe trait implementations were treated as
  adversarial for soundness.
- Mandatory postconditions remained separate from UB freedom.
- Current test-only code remained separate from downstream-shippable code.
- No target code was executed.

The result is therefore a regression pass, while the indirect-proof miss is a
real remaining skill-quality limitation. The frozen revision was not modified
after observing it.

