# Focused unsafe-Rust audit

## Claim, snapshot, and verdict

Audited snapshot: the supplied `target/lib.rs` in full, reviewed 2026-08-01 using the supplied unsafe-Rust skill snapshot. No generated code, dependencies, features, `cfg`, FFI, assembly, allocator, concurrency, or macro surfaces exist in the supplied target. No code was built, tested, executed, expanded, or modified.

`Required(c) := c uses Rust/stdlib 1.82.0, is a target on which this exact source and the used standard-library items exist, and uses any ordinary profile.` The claim is source-level freedom from Rust undefined behavior for every well-typed safe use, while unsafe-trait implementations satisfy their published safety obligations, plus the requested behavior checks.

| Claim | Verdict | Certificate |
|---|---|---|
| All three modules, aggregate soundness | **UNSOUND** | CB-READ and CB-WRITE are distinct valid safe executions reaching UB. |
| `callback_index::read` | **UNSOUND** | CB-READ. |
| `callback_index::write` | **UNSOUND** | CB-WRITE. |
| `local_proof::last` implementation and requested return behavior | **PROVED** | LP below, for all `Required`. Existing proof comment is deficient. |
| `published_lane::High` contract and `read` soundness | **PROVED** | PL below, for all `Required` and every contract-valid `Lane` implementation. Local proof artifacts are missing. |

There is no `CONTRACT-BROKEN` result. The callback witnesses contain UB and therefore cannot prove a defined-behavior postcondition violation; no independent UB-free refutation was found. The combined mandatory result remains `UNSOUND`, not diluted by the independently proved modules.

## Authority and TCB (`R061-TCB-1`)

There are no additional assumptions. These verified Rust 1.82 axioms are the complete consumed authority:

- AX-SLICE-INDEX: [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked) and [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) require an in-bounds index. Their common safety text states: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.”
- AX-SLICE-SIZE: [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) returns the element count; [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) is true exactly when that count is zero.
- AX-INTEGER: the Reference identifies `-` as integer subtraction and describes overflow/profile behavior; [`usize` is unsigned](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types). Thus for a nonzero `usize` value `n`, `n - 1` is representable and less than `n`, independently of overflow-check settings. See [binary arithmetic](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators).
- AX-TRAIT: Rust says correctly implemented unsafe traits are safe to use and implementations must be `unsafe`; the unsafe keyword marks extra conditions implementations must uphold. See [unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits) and [unsafe-trait obligations](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait).

Disposition: accepted as the governing versioned Rust semantics; no dependency, tool, implementation, external, deployment, probabilistic, or out-of-band entry is consumed.

## Boundary and configuration closure

The safe/caller-reachable inventory is complete: public safe trait `Position` and its caller-supplied method; safe `callback_index::{read, write}`; safe `local_proof::last`; public tuple constructor and field of `Word`; public unsafe trait `Lane` and associated constants; public unit constructor `High`; its `unsafe impl`; and safe `published_lane::read`. There are no hidden or configuration-generated surfaces. Ordinary compiler-supplied move/drop/auto-trait behavior creates no invariant used by an unsafe operation.

The exact source is configuration-invariant. CB-READ/CB-WRITE work on every `Required` target. LP is parametric over every target's `usize` width and does not rely on profile-dependent overflow behavior. PL uses the target-independent array length 2. Therefore each proved obligation has `Covered = Required`, and `Required ⊆ Covered`; no sampled configuration or version-compatibility premise is used.

## Findings and obligation proofs

### CB-READ — safe callback can select an out-of-bounds index

`Position` is a safe, public, downstream-implementable trait with no bound contract. Safe code may define:

```rust
struct Bad;
impl callback_index::Position for Bad {
    fn position(&self) -> usize { 0 }
}
let _ = callback_index::read(&[], &Bad);
```

This is a well-typed safe use. `read` calls `position()` once, then executes `get_unchecked(0)` on a length-zero slice. `0` is out of bounds, so AX-SLICE-INDEX entails UB at the call, before dereference relevance. This closes the full `UNSOUND` certificate: valid use, reachability, false in-bounds proposition, and authoritative UB consequence. The unsafe block has no proof comment, but the implementation defect is independently established.

### CB-WRITE — independent mutable out-of-bounds witness

Using the same safe `Bad` implementation:

```rust
let mut bytes: [u8; 0] = [];
callback_index::write(&mut bytes, &Bad, 7);
```

This safe execution reaches `get_unchecked_mut(0)` on length zero. Its in-bounds condition is false, and AX-SLICE-INDEX entails UB. This is a separate certificate for `write`; exclusive borrowing does not establish bounds.

Documentation cannot add a safety precondition to either safe API. Making or sealing `Position` unsafe would also fail the stated requirement that safe callers choose positions.

**Smallest repair (proposal only):** retain signatures and `Position`, but replace the bodies with `bytes[position.position()]` and `bytes[position.position()] = value`. In-range behavior is retained; arbitrary safe caller-selected positions remain accepted; out-of-range positions panic rather than cause UB; and both unsafe blocks disappear. Changing the parameter to `usize` is an optional, larger API simplification, not needed for soundness. This proposal is **uncertified** until implemented and freshly audited.

### LP — implementation correct; existing comment inadequate

Let `n = bytes.len()`. The empty branch executes no unsafe operation and returns `None`. In the other branch, the dominating `!bytes.is_empty()` and AX-SLICE-SIZE give `n != 0`. AX-INTEGER gives representable `index = n - 1` and `index < n`; AX-SLICE-INDEX therefore permits `get_unchecked(index)`. The returned shared reference designates the final initialized `u8` in the input slice, and copying it yields `Some(bytes[n-1])`. This covers both exhaustive branches and every `Required` profile/target.

The existing `SAFETY: This is the fast path` states neither the operation's precondition nor any fact or derivation. Replace it with:

```rust
// SAFETY: `bytes.is_empty()` was false, so `bytes.len() != 0`.
// Therefore `index = bytes.len() - 1` is representable and
// `index < bytes.len()`, satisfying `get_unchecked`'s bounds condition.
```

### PL — published contract closes the proof

The published unsafe contract is literal: every valid `Lane` implementation has `INDEX < 2`, and `NAME` is `"low"` for index 0 and `"high"` for index 1. `High` establishes both clauses with `(1, "high")`. For any contract-valid downstream `L`, `Word::0` has exactly two elements and `L::INDEX < 2`; hence AX-SLICE-INDEX permits `get_unchecked`, and `read` returns `word.0[L::INDEX]`. Unknown invalid unsafe impls violate an out-of-scope implementer obligation; they are not hidden premises or valid uses.

Proof artifacts are nevertheless missing. Add adjacent comments equivalent to:

```rust
// SAFETY: `INDEX` is 1 (< 2), and the required name for index 1 is "high".
unsafe impl Lane for High { /* unchanged */ }

// SAFETY: `Lane`'s published contract gives `L::INDEX < 2`, while
// `Word::0` has length 2, satisfying `get_unchecked`'s bounds condition.
```

Because this is a published 1.x unsafe-trait contract, repository-visible users are not exhaustive. Do not strengthen implementer obligations (unknown impls may cease to comply), weaken/remove the `NAME` guarantee (unknown consumers may rely on it), or seal/remove the trait without explicit breaking-change handling. No contract change is needed for the current proof.

## Residual scope and re-audit triggers

No source outside the supplied target, non-ordinary configuration, other Rust release, downstream implementation body, or downstream consumer body was audited. Re-audit after any source or safety-documentation change, repair implementation, support-domain expansion, Rust/stdlib authority change, or change to the published `Lane` contract. All current-artifact verdicts above are independent of the unimplemented proposal.
