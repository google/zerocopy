# Focused unsafe-Rust review

## Claim, domain, and verdicts

Snapshot: the supplied `lib.rs`, reviewed 2026-08-01 without expansion, execution, tests, or repository context. Scope is all three modules and every language-reachable surface in that file.

`Required(c) := rustc/stdlib 1.82.0 AND c.target admits this exact source and every used 1.82.0 std item AND c.profile is an ordinary profile.` There are no source `cfg`s, features, dependencies, generators, FFI, concurrency, allocator choices, or profile-dependent assertions. The arguments below are parametric in target and profile, so their covered domain equals `Required`; no finite target/profile enumeration or exclusion is inferred.

The TCB consists only of the linked, version-exact Rust 1.82.0 Reference and standard-library axioms; there are no additional assumptions, selected dependencies, tools, or prior results.

| Claim | Verdict | Certificate |
|---|---|---|
| Combined safe-API freedom from UB | **UNSOUND** | CB-R and CB-W below are valid safe executions reaching documented UB. |
| `callback_index::read` | **UNSOUND** | CB-R, throughout `Required`. |
| `callback_index::write` | **UNSOUND** | CB-W, throughout `Required`. |
| `local_proof::last` | **PROVED** | LP below, throughout `Required`; proof comment deficient. |
| `High: Lane` contract | **PROVED** | PL-I proves both published clauses. |
| `published_lane::read` | **PROVED** | PL-R, for every valid `Lane` implementation throughout `Required`; proof comment missing. |

No unsafe function documents a provider postcondition. `Lane`'s two implementer obligations are both disposed below. No `CONTRACT-BROKEN` witness is claimed.

## Boundary, invariants, and obligation ledger

The complete explicit surface is: safe public `Position` and `Position::position`; safe public callback `read` and `write`; safe public `last`; public tuple struct `Word` and its field/constructor; public unsafe `Lane` and its associated constants; public unit struct `High`, its unsafe impl, and safe public lane `read`. No macros, hidden items, explicit reexports, or user-defined trait impls beyond those listed occur.

**CB-NONE.** `Position` owns no slice-relative invariant. A safe implementation may return every `usize`; neither callback validates the result before consuming it.

**LP-BOUND.** On the nonempty branch only, `index = bytes.len() - 1` and `index < bytes.len()`.

**PL-LANE.** Each valid unsafe `Lane` impl continually supplies `INDEX < 2` and the exact `NAME` mapping in the published contract. `Word([u32; 2])` supplies length 2 by its type; its public field permits arbitrary lane values but cannot change that length.

The applicable slice contracts state that out-of-bounds `get_unchecked` and [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) calls are UB even if their resulting references are unused; the immutable contract says the same and expressly includes index `len` ([`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked)).

### CB-R — safe read has an in-scope UB witness

Safe code may define `struct P; impl Position for P { fn position(&self) -> usize { 0 } }` and call `read(&[], &P)`. This is well typed, requires no unsafe act or hidden precondition, and reaches `get_unchecked(0)` on a length-zero slice. Thus 0 is out of bounds, the required safety proposition is false, and the cited contract entails UB. This completes the **UNSOUND** certificate independently of any later behavior.

### CB-W — safe write has an in-scope UB witness

The same safe `P` can be passed to `write(&mut [], &P, 7)`. It reaches `get_unchecked_mut(0)` on a length-zero slice, falsifying its in-bounds requirement; the cited mutable-slice contract entails UB. This separately completes **UNSOUND**.

### LP — implementation proof and comment review

[`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) is true exactly when slice length is zero, and [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) returns the element count. Therefore the `else` branch establishes `len != 0`. `usize` is an unsigned pointer-width integer ([integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types)), hence `len >= 1`. Consequently `len - 1` is representable and strictly below `len`; binary subtraction overflows only when its result is outside the type's range ([operator semantics](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators)). LP-BOUND therefore entails the exact `get_unchecked` precondition. Dereferencing the returned shared reference copies its valid `u8`. The empty branch performs no unsafe operation. This proves implementation soundness in every ordinary profile, including when overflow checks differ.

The existing comment, “This is the fast path,” identifies neither the operation's precondition nor any fact implying it. Its proof-artifact status is **deficient** despite the proved implementation. Material replacement:

```rust
// SAFETY: The `else` branch establishes `bytes.len() != 0`. Because the
// length is a `usize`, `index = bytes.len() - 1` is representable and
// `index < bytes.len()`, so `index` is in bounds as `get_unchecked` requires.
```

### PL-I/PL-R — published unsafe-trait boundary

Rust 1.82 says unsafe traits impose extra conditions on implementations and that an `unsafe impl` asserts those obligations are discharged ([unsafe traits and impls](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait)); using a correctly implemented unsafe trait is safe ([trait items](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits)). This is an enforced unsafe boundary, not trust in arbitrary safe caller code.

PL-I: `High` sets `INDEX = 1`, so it is less than 2, and sets `NAME = "high"`, exactly the clause applicable at index 1. The index-0 implication is vacuous. Both published obligations are proved.

PL-R: for any valid (including unknown downstream) `L: Lane`, PL-LANE yields `L::INDEX < 2`; the array type yields `word.0.len() = 2`. The index is therefore in bounds and the immutable unchecked access satisfies its contract. Contents and `NAME` are irrelevant to this operation. The implementation is **PROVED**, but the unsafe block lacks the material local bridge. Proposed adjacent comment:

```rust
// SAFETY: Every valid `Lane` implementation guarantees `INDEX < 2`, and
// `word.0` is a `[u32; 2]`; therefore `L::INDEX` is in bounds.
```

The unsafe impl likewise deserves adjacent proof text: `INDEX` is 1 (<2) and its required name is `"high"`. These documentation defects do not negate the reconstructed implementation proofs.

Because this is a published 1.x unsafe contract with unknown implementations and consumers, `NAME` is not removable merely because local `read` ignores it: unsafe downstream consumers may rely on that guarantee. Strengthening implementer obligations may invalidate unknown impls; weakening guarantees may invalidate consumers. No contract change is certified here.

## Repair and residual scope

The smallest callback repair retains all signatures and safe caller-selected positions, evaluates the callback once, and uses checked indexing:

```rust
pub fn read<P: Position>(bytes: &[u8], position: &P) -> u8 {
    bytes[position.position()]
}
pub fn write<P: Position>(bytes: &mut [u8], position: &P, value: u8) {
    bytes[position.position()] = value;
}
```

Out-of-range positions then panic rather than violate an unsafe precondition. Making `Position` unsafe/sealed or making either operation unsafe is unnecessary and would shift or restrict the required safe functionality. Replacing `Position` with `usize` could be a larger breaking simplification, not the smallest repair. Every proposal remains **uncertified** until implemented as a new snapshot and freshly audited.

Unknown downstream `Lane` implementations and unsafe consumers were not inspected. Their compliance is their documented unsafe obligation; they do not narrow the current contract or justify changing it. Re-audit is required after any source, Rust-version, support-domain, trait-contract, or proposed-repair change.
