# Unsafe Rust source audit: four exported APIs

## Claim, snapshot, and aggregate result

This is a source-level review of the supplied `lib.rs` snapshot, at the
2026-07-31 support cutoff, relative only to `EVIDENCE.md` and accepted TCB
entries `SEM-EMPTY-BLOCK-180-182` and `COMPAT-COPY-180-182`. It covers all four
exported unsafe functions, their caller contracts, UB freedom for every valid
call, and every stated result. It makes no compiler-backend, binary, deployment,
or broader robustness claim. There are no dependencies, generated artifacts,
features, conditional source paths, stateful invariants, safe wrappers, fields,
traits, macros, or other exported surfaces in the supplied source.

Let `T_f(v)` mean every target on which item `f` exists, and let
`P={ordinary-debug, ordinary-release}`. For each API,
`Required_f={(v,t,p) | v in V_f, t in T_f(v), p in P}`. `SUPPORT.md` directly
defines each `V_f` as an exact finite set, so no interval interpolation or
enumeration inference is used. Target and profile are semantic parameters: the
source has no branch on either, and every cited authority or consumed TCB entry
applies to all such cases in its stated release region.

| API | `V_f` | Exact aggregate `Covered` release region | Soundness | Documented results | Strongest API verdict |
|---|---|---|---|---|---|
| `acknowledge` | `{1.80.0,1.80.1,1.81.0,1.82.0}` | all `V_f` | **PROVED** | return `()`: **PROVED** | **PROVED** |
| `store_word` | `{1.80.0,1.81.0}` | all `V_f` | **PROVED** | stores `value`: **PROVED**; old `u16` is neither read nor dropped: **PROVED** | **PROVED** |
| `copy_byte` | `{1.80.0,1.80.1,1.81.0,1.82.0}` | all `V_f` | **PROVED** | destination receives the source byte: **PROVED**; source is preserved: **PROVED** | **PROVED**, relative to `COMPAT-COPY-180-182` |
| `load_word` | `{1.80.0,1.80.1,1.81.0,1.82.0}` | `{1.80.0,1.82.0}` | **UNPROVED** over `Required`; **PROVED** on `Covered` | returned value and unchanged source: each **UNPROVED** over `Required`, **PROVED** on `Covered` | **UNPROVED** |

Thus the combined four-API mandatory claim is **UNPROVED**, solely because
`Required_load` is not contained in `Covered_load`. No submitted fact proves a
valid UB witness or a UB-free postcondition counterexample, so neither
`UNSOUND` nor `CONTRACT-BROKEN` is certified.

## Obligation ledger and proofs

**ACK-S/Q.** The caller contract imposes no additional safety requirement, and
the exact body is `{}`. `SEM-EMPTY-BLOCK-180-182` applies to precisely all four
releases, all item-bearing targets, and both profiles; the checked empty body
connects the source to its admitted proposition that evaluation is defined and
returns `()`. Hence `Required_ack = Covered_ack` for soundness and return.

**STORE-S.** The only operation is `ptr::write::<u16>(dst,value)`. The public
contract supplies its two documented safety clauses: `dst` is properly aligned
and valid for one `u16` write. The 1.80.0 and 1.81.0 `ptr::write` authorities
apply separately to the two members of `V_store`; their exhaustive union is
`Covered_store=V_store`. A typed `u16` supplies the value passed to the exact
call. Soundness is therefore proved.

**STORE-Q1/Q2.** Those same two release-specific pages state that `write`
overwrites the destination with the given value without reading or dropping
the old value. The direct call has no later transition, proving both documented
results over the same exhaustive union.

**COPY-S.** Locally, `T=u8` and `count=1`; the caller contract establishes
initialized readable source, writable destination, alignment, and non-overlap
for the one-byte regions. The 1.80.0 `copy_nonoverlapping` contract, primitive
layout, `u8: Copy`, and `Copy` semantics establish the base case.
`COMPAT-COPY-180-182` explicitly preserves those exact propositions for every
member of `V_copy`, target, and profile, and is authorized only for this call.
Thus `Covered_copy=V_copy` and soundness is proved.

**COPY-Q1/Q2.** The same accepted entry expressly guarantees that this exact
call copies exactly one byte to `dst`, leaves the source byte unchanged, and
does not move ownership from it. These propositions directly establish both
documented results throughout `Required_copy`.

**LOAD-S/Q.** The only operation is `ptr::read::<u32>(src)`. The caller contract
provides readable validity, alignment, and initialization. At 1.80.0, that
release's `read`, `u32: Copy`, and `Copy` pages prove a defined read returning
the source value while leaving source memory unchanged. The parallel 1.82.0
pages prove the same case at 1.82.0. Therefore each soundness and result
obligation has `Covered={1.80.0,1.82.0}` (with all corresponding targets and
profiles). No authority applies at 1.80.1 or 1.81.0, and `TCB.md` explicitly has
no `read` compatibility entry. Endpoint facts do not cover the interior.

## Evidence and TCB audit log

All authority entries are accepted versioned Rust standard-library/Reference
premises with exactly the claim-specific applicability stated in `EVIDENCE.md`:
[write 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) and
[write 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html);
[copy_nonoverlapping 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html),
[primitive layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout),
[u8: Copy](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8),
and [Copy semantics 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html);
and `read`, `u32: Copy`, and `Copy` semantics at
[1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html) and
[1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html), with the
corresponding versioned primitive/trait pages identified in `EVIDENCE.md`. No
entry is transferred between operations.

| TCB ID | Disposition and exact use | Limit / trigger |
|---|---|---|
| `SEM-EMPTY-BLOCK-180-182` | accepted; defined evaluation and `()` return of an exact empty-body unsafe function over `V_ack` | only `ACK-S/Q`; any signature, body, contract, release-set, or disposition change |
| `COMPAT-COPY-180-182` | accepted; preserves the enumerated 1.80 copy/layout/Copy propositions over all `V_copy` | only `COPY-S/Q`; any call/type/count/base proposition/release-set/disposition change |

No tool-derived evidence, test result, sampled configuration, or unlisted
assumption contributes to a verdict.

## Findings, proof artifacts, and residual scope

**F-LOAD-COVERAGE — UNPROVED.** The smallest missing proposition is: for each
`v in {1.80.1,1.81.0}`, `ptr::read::<u32>` under the documented caller clauses
is defined, returns the read value, leaves the source unchanged, and the needed
`u32: Copy` semantics apply, for every supported target/profile. Resolution
requires applicable versioned authorities or an accepted, exact compatibility
premise; testing or endpoint interpolation is insufficient. Re-audit all
`load_word` claims after resolution.

The three local `SAFETY` comments identify their callees but omit the material
release-applicability and, for copy/read, layout/`Copy` bridges and TCB route.
Implementation status remains as above, but the proof artifacts are deficient.
Minimum documentation repair is to cite stable canonical proofs containing the
corresponding ledger derivation; this cannot repair `F-LOAD-COVERAGE` without
new evidence.

Residual scope is exactly nonlisted Rust releases, nonordinary profiles,
targets where an item does not exist, backend/binary correctness, and behavior
beyond the stated results. Re-audit on source or contract changes, support-set
changes, material authority changes, or either TCB entry's trigger.

**Attestation:** every in-scope surface, safety obligation, documented result,
release case, and consumed premise has a disposition; affirmative claims have
`Required subseteq Covered`, and the unresolved remainder remains explicit.
