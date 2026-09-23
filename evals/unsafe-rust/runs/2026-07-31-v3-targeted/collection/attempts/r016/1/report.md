# Focused unsafe-Rust audit

## Claim, scope, and verdicts

Snapshot: the exact supplied `target/lib.rs`; no expansion, execution, build, or repository history was used. `Required = {Rust 1.82.0} × {targets on which this exact source and its used 1.82.0 standard-library items exist} × {ordinary profiles}`, exactly preserving the request's symbolic target and profile predicates. The claim is freedom from Rust undefined behavior for every well-typed safe use, plus compliance with the published `Lane` implementer contract for in-scope implementations.

| Claim | Verdict | Certificate |
|---|---|---|
| Whole supplied source | **UNSOUND** | CB-R and CB-W are independent valid safe-use UB witnesses. |
| `callback_index::read` | **UNSOUND** | CB-R. |
| `callback_index::write` | **UNSOUND** | CB-W. |
| `local_proof::last` unsafe operation | **PROVED** | LP proves the unchecked index in bounds for every input. |
| `published_lane::High` contract and `read` | **PROVED** | PL-I and PL-R cover every contract-valid implementation, not merely visible ones. |

The combined mandatory result is therefore **UNSOUND**, without stopping review of the other modules. There are no extra TCB assumptions, dependencies, generated artifacts, tools, FFI, concurrency, or conditional code. TCB-R82 contains only the cited, exact Rust 1.82.0 Reference/standard-library contracts as governing semantics.

## Boundary and obligation inventory

All language-reachable surfaces are: `Position` and its safe caller-provided `position`; safe `callback_index::{read, write}`; safe `local_proof::last`; public `Word` tuple constructor/field; public `High` unit constructor; unsafe `Lane`, its associated constants, downstream `unsafe impl`s, the `High` impl, and safe `published_lane::read`. There are no macros, reexports, hidden APIs, methods, `Drop` implementations, or configuration-specific surfaces in the supplied source.

Rust 1.82.0 documents for both [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked) and [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut): “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.”

### CB-R — safe read permits an out-of-bounds index

**Implementation: UNSOUND; proof artifact: missing.** Define in safe code `struct End; impl Position for End { fn position(&self) -> usize { 0 } }`, then call `read(&[], &End)`. Implementing this safe trait, constructing the empty slice, and calling `read` are valid safe uses; `Position` has no behavioral restriction. The call reaches `get_unchecked(0)` on a length-zero slice. Index 0 is out of bounds, so the quoted Rust 1.82.0 contract entails UB. This establishes valid use, reachability, the false bounds proposition, and the UB consequence. It applies parametrically to every required target/profile.

### CB-W — safe write permits an out-of-bounds index

**Implementation: UNSOUND; proof artifact: missing.** With the same safe `End`, `let mut bytes = []; write(&mut bytes, &End, 7)` is a valid all-safe call. It reaches `get_unchecked_mut(0)` on a length-zero slice. The required in-bounds proposition is false and the cited mutable contract entails UB, independently of CB-R and before the assignment can justify anything. This witness is likewise target/profile-parametric.

### LP — implementation correct, existing comment inadequate

**Implementation: PROVED; proof artifact: deficient.** Let `n = bytes.len()`. [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) is true exactly when the slice length is zero, and [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) returns its element count. The unsafe branch therefore has `n > 0`. Consequently `n - 1` is representable in unsigned `usize` (no underflow under the [integer arithmetic rules](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators)) and yields `i = n - 1 < n`. Thus `i` is in bounds, satisfying `get_unchecked`; dereferencing the shared element reference copies a valid `u8`. The empty branch executes no unsafe operation. This also proves `None` for an empty slice and `Some` of the final element otherwise.

“This is the fast path” supplies none of the required obligation, dominating fact, arithmetic step, or bound. Replace it with:

```rust
// SAFETY: `is_empty()` was false, so `bytes.len() > 0`. Thus
// `index = bytes.len() - 1` is representable and `index < bytes.len()`,
// which is the bounds precondition of `get_unchecked`.
```

### PL-I/PL-R — published unsafe-trait boundary closes

The Rust 1.82.0 Reference requires unsafe traits to be implemented through an unsafe implementation ([traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits), [`unsafe` keyword](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait)); the source's published `# Safety` text is the controlling implementer contract.

**PL-I: PROVED; local proof missing.** `High` supplies `INDEX = 1`, hence `INDEX < 2`, and supplies `NAME = "high"`, exactly the clause required when `INDEX == 1`. Suggested adjacent proof: `// SAFETY: INDEX is 1 (< 2), and for INDEX == 1 the required NAME is "high".`

**PL-R: PROVED; local proof missing.** For every valid `L: Lane`, including unknown downstream implementations, the unsafe-trait contract entails `L::INDEX < 2`. `word.0` is always `[u32; 2]`; its public field introduces no stronger invariant and has length 2. Therefore `L::INDEX` is in bounds and `get_unchecked` is permitted. Suggested comment: `// SAFETY: Every valid Lane impl guarantees L::INDEX < 2, and word.0 is [u32; 2].`

An incorrect downstream `unsafe impl` is a violated out-of-scope implementer obligation, not a hidden precondition on safe callers. Conversely, repository-visible consumers are not exhaustive: `NAME` is a literal published guarantee even though this `read` does not consume it. Removing or weakening it in a 1.x release could invalidate downstream unsafe reasoning; strengthening either clause could invalidate existing implementations. No such contract change is justified by this audit.

## Minimal repair for `callback_index` (proposal only)

Keep the signatures and caller-selected positions, but replace the two bodies with checked indexing:

```rust
pub fn read<P: Position>(bytes: &[u8], position: &P) -> u8 {
    bytes[position.position()]
}

pub fn write<P: Position>(bytes: &mut [u8], position: &P, value: u8) {
    bytes[position.position()] = value;
}
```

This is the smallest repair: in-range behavior and both callable APIs remain; an adversarial/out-of-range safe position now causes defined bounds-check failure rather than UB. The trait could instead be replaced by `usize`, since its preservation is not required, but that is a larger public API change. Making `Position` unsafe, sealing it without usable implementations, or deleting the functions would transfer/bypass the required safe-caller functionality and is not recommended. This proposal is **not certified**: it must be implemented as a new snapshot and freshly audited, including its panic behavior across the intended ordinary profiles.

## Domain closure, residual scope, and triggers

No finite target enumeration was inferred. LP and PL are parametric in the request's target/profile predicates: target-dependent `usize` width is irrelevant because LP proves subtraction non-overflowing and PL uses only 1 and a fixed length 2; overflow-check and optimization choices do not alter those facts. Thus `Covered_LP = Covered_PL = Required`, establishing `Required ⊆ Covered` for each proved claim. CB-R/CB-W refute universal soundness with witnesses available throughout `Required`.

This is a Rust source-level result only, not a compiler-binary, platform, security, or downstream-implementation audit. Re-audit on any source or safety-contract change, implementation of the repair, Rust/support-domain change, added configuration/generation/dependency, or new downstream-facing contract evidence.
