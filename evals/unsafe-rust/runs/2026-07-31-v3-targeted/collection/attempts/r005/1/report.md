# Focused unsafe-Rust audit

## Claim and verdict

**Snapshot:** the complete supplied `lib.rs`; no generated code, dependencies, macros, FFI, assembly, or prior audit. **Supported set:** Rust and standard library 1.82.0, every target on which this source and the used items exist, and every ordinary profile. **Claim:** every well-typed safe use of the safe surfaces is free of Rust undefined behavior, provided any out-of-scope unsafe-trait implementation satisfies its published contract; the in-scope `unsafe impl` must satisfy that contract. This is a source-level claim under documented Rust abstract semantics, not a compiler-binary claim.

**Combined soundness verdict: UNSOUND (F-CB).** `callback_index::read` and `write` each admit a wholly safe call that violates `get_unchecked[_mut]`'s precondition. The review did not stop at that aggregate result:

- `callback_index`: `Position` alone is sound, but `read` and `write` are each **UNSOUND**.
- `local_proof::last`: implementation **PROVED**; existing `SAFETY` comment **deficient** (F-LP).
- `published_lane`: `Lane`'s contract, `High`'s `unsafe impl`, and `read` are **PROVED** for valid implementations (P-PL). Unknown downstream implementations and consumers do not change that literal result.
- Mandatory documented guarantee: `High` supplies both published `Lane` constant requirements, **PROVED**. No `CONTRACT-BROKEN` witness is established.

**TCB:** TCB-1 below contains only Rust 1.82 authoritative axioms; there are no additional assumptions, dependency entries, tool-derived facts, or conditional application claims. No build, test, execution, or expansion was performed.

## Boundary and obligation coverage

| ID | Language-reachable surface | Status / obligation |
|---|---|---|
| C1 | safe public `Position` and caller implementation of `position` | A safe implementation may return every `usize`; no in-bounds invariant follows. |
| C2 | safe public `read<P: Position>` | Must prove returned position `< bytes.len()`; false (F-CB-R). |
| C3 | safe public `write<P: Position>` | Same obligation; false (F-CB-W). |
| L1 | safe public `last` | Empty and nonempty paths covered; implementation P-LP, comment F-LP. |
| P1 | public `Word` tuple constructor/field; public `High` constructor | `[u32; 2]` fixes field length at two; safe construction/access introduces no stronger invariant. |
| P2 | public unsafe `Lane`, `INDEX`, `NAME`; `unsafe impl Lane for High` | Literal implementer contract and both `High` clauses covered by P-PL-I. |
| P3 | safe public `published_lane::read<L: Lane>` | Requires `L::INDEX < word.0.len()`; P-PL-R derives it. |

There are no hidden/configuration-specific items, callbacks other than `Position::position`, custom trait methods, custom destruction, or generated surfaces in this file. Built-in auto-trait/destruction behavior creates no additional unsafe consumer here.

## TCB-1: authoritative premise log

All entries are accepted as the request's governing Rust 1.82 authority, apply to the full supported set, and are rechecked if that version/scope changes.

- **AX-SHARED:** [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked) returns a reference without bounds checking and states: “Calling this method with an out-of-bounds index is undefined behavior”. Consumers: C2, L1, P3.
- **AX-MUT:** [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) gives the same quoted rule for a mutable reference. Consumer: C3.
- **AX-LENGTH:** [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) “Returns the number of elements in the slice”; [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) is true exactly when that length is zero. Consumers: L1, P1/P3.
- **AX-INTEGER:** the [`usize` table](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types) gives minimum zero; the [binary-operator table and overflow rules](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators) define integer subtraction. Thus for a `usize n != 0`, `n - 1` is representable and strictly below `n`. Consumer: L1.
- **AX-TRAIT:** the [unsafe-trait description](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait) says an unsafe trait has extra safety conditions “that must be upheld by implementations of the trait”; the [trait rules](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits) state that a correctly implemented unsafe trait is safe to use. Consumers: P2/P3.

No rejected or pending premise is consumed.

## Findings and proofs

### F-CB — safe callback results reach unchecked indexing

**Implementation: UNSOUND; proof artifact: missing.** `Position::position` has no contract or enforcement restricting its result. A safe caller may define `P::position` to return `0`. In one valid execution, `read(&[], &P)` calls `get_unchecked(0)`; in a separate valid execution, `write(&mut [], &P, value)` calls `get_unchecked_mut(0)`. Index zero is out of bounds for the empty slice, so AX-SHARED/AX-MUT proves UB even if the resulting reference were not used. These witnesses use only safe caller syntax and work throughout the supported set. They establish F-CB-R and F-CB-W independently. No UB-free postcondition refutation is claimed.

**Smallest repair:** retain all public signatures and make the two accesses safe-indexing expressions: `bytes[position.position()]` and `bytes[position.position()] = value`. Then arbitrary safe callback results cause a bounds-check panic rather than forming an unchecked out-of-bounds reference, while safe callers still choose positions and both read/write remain callable. Removing `Position` in favor of `usize` is possible but is a larger, source-breaking change and is not needed for soundness. This proposal is **not implemented and not certified**; the resulting snapshot needs a fresh audit.

### F-LP — correct implementation, inadequate local proof

**P-LP reconstructed proof:** On the `None` branch there is no unsafe operation. On the other branch, AX-LENGTH turns `!bytes.is_empty()` into `n = bytes.len() != 0`. Since `n: usize`, AX-INTEGER gives `n >= 1`, makes `index = n - 1` non-overflowing in every profile, and gives `index < n`. AX-SHARED's bounds obligation is therefore satisfied; it returns the last element reference, and copying its valid `u8` yields `Some(last byte)`. This proves implementation soundness over every supported target/profile.

The existing comment, “This is the fast path,” states none of the required facts or implication. Replace it with:

```rust
// SAFETY: The else branch means `bytes.len() != 0`. Therefore
// `index = bytes.len() - 1` is representable and `index < bytes.len()`,
// which satisfies `get_unchecked`'s bounds requirement.
```

### P-PL — published unsafe-trait composition

**P-PL-I:** `High::INDEX` is `1`, hence less than `2`; because it is `1`, the contract requires and the impl supplies `NAME == "high"`. The `INDEX == 0` implication is vacuously true. Thus the in-scope `unsafe impl` discharges every literal clause, including the clause unused locally.

**P-PL-R:** for every valid `L: Lane`, its published contract supplies `L::INDEX < 2`. `word.0` has exactly two elements, so the index is in bounds and AX-SHARED discharges `get_unchecked`. `read` consumes no `NAME` proposition.

An incorrect unknown downstream `unsafe impl` violates its out-of-scope obligation and is not a valid implementation; it does not add a hidden precondition to safe callers. Conversely, unknown downstream consumers may rely on both `INDEX` and `NAME`. Because this is a published 1.x contract, deleting/weakening either guarantee or strengthening implementer obligations requires compatibility handling; the absence of a repository-visible `NAME` consumer is not evidence that weakening is safe.

## Configuration closure, residual scope, and triggers

There are no source selection axes. The proofs are parametric in target and ordinary profile: slice/array lengths and the non-overflowing arithmetic relation are unchanged; both callback witnesses remain available. No generated artifact or enforced exclusion exists or is needed.

Excluded from the source theorem are correctness of a particular compiler/backend binary and downstream unsafe implementations that breach `Lane`. Unknown downstream consumers were intentionally not treated as enumerable. The proposed repair remains outside the audited snapshot.

Re-audit on any source or safety-contract change; Rust/standard-library version or supported-set change; addition of cfg, generation, dependencies, or new consumers; or any evolution of the published `Lane` guarantees. No authoritative-documentation or skill-guidance gap blocked this audit. Independent review was not performed.
