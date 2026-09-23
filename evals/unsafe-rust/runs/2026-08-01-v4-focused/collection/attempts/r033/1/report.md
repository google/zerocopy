# Focused unsafe-Rust audit and redesign

## Claims and verdicts

**Snapshot.** Exact supplied `lib.rs` (18 lines), reviewed without execution or expansion. Scope is Rust 1.82.0 and

`Required = { (target, profile, use) | target admits this source and the used Rust 1.82.0 standard-library items; profile is ordinary; use is well-typed safe use of a language-reachable safe surface }`.

There are no `cfg`s, macros, dependencies, generated artifacts, FFI, concurrency, allocator choices, or target-dependent operations in the supplied snapshot. The source contains no support-policy transformation: the request supplies the symbolic target set directly. Audit cutoff 2026-08-01 does not extend the fixed Rust release.

| Claim | Verdict | Certificate |
|---|---|---|
| Every safe use of the current public API is free of Rust UB over `Required`. | **UNSOUND** | F-1 gives a valid entirely-safe use, reaches `get_unchecked_mut(2)` on a length-2 slice, proves its bounds precondition false, and links that event to Rust 1.82.0's explicit UB consequence. The witness is target/profile-parametric. |
| For every initial `[a, b]`, `increment::<Tail>` terminates with `[a, b.wrapping_add(1)]` without UB. | **PROVED** | P-TAIL below covers every `u32` pair and every required target/profile. |

There is no documented unsafe public API postcondition. The request's `Tail` behavior is the only additional behavior claim. No `CONTRACT-BROKEN` verdict applies: F-1's execution contains UB, while the independently reviewed `Tail` behavior holds.

## Boundary, invariants, and obligation ledger

The complete relevant language-reachable surface is: public safe trait `Slot` and safe associated function `Slot::index` (`lib.rs:3-5`); public unit struct and constructor `Tail` (`:7`); its safe trait implementation (`:9-13`); and safe generic function `increment<S: Slot>` (`:15-18`). There are no fields, derives, reexports, hidden items, exported macros, or other manual implementations. Compiler-supplied auto-trait/drop behavior carries no state and is not consumed by the unsafe block.

The unsafe operation needs `BOUND(S): S::index() < 2`. No type, check, privacy boundary, trait contract, or invariant establishes `BOUND` for arbitrary `S`. `Slot` is public and safe. Rust 1.82.0's [visibility rules](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy) make the root `pub` surfaces externally reachable, and its [trait-implementation/orphan rules](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations) permit another crate to implement this trait for its own local type.

| ID | Obligation | Status |
|---|---|---|
| O-BOUND | At `:16`, the `usize` index must be in `0..2`. | **False** for a valid implementation returning 2; proved for `Tail` because `Tail::index()` is exactly 1. |
| O-SAFE | Safe `increment` must discharge O-BOUND for every safe `S: Slot`. | **Refuted** by F-1. |
| O-TAIL | The in-bounds mutable reference denotes element 1; the write preserves element 0 and stores modular `b + 1`. | **Proved** by P-TAIL. |
| O-CONFIG | Cover all requested targets/profiles. | Control flow, array length, constants, and the exact Rust 1.82.0 contracts are invariant across the symbolic availability set; thus P-TAIL covers it, and F-1 works in every member. |

### P-TAIL

For `S = Tail`, source fixes `S::index()` to 1. An array `[u32; 2]` has length 2, so 1 is in bounds. Rust 1.82.0 documents that [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) returns a mutable reference to the selected element without checking bounds and states: “Calling this method with an out-of-bounds index is undefined behavior.” Here that forbidden condition is false. The exclusive array borrow supplies the access for the returned reference, and no intervening call occurs. Rust 1.82.0 documents [`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add) as computing addition “wrapping around at the boundary of the type.” Therefore the sole write changes element 1 from `b` to modular `b + 1`; element 0 remains `a`.

## F-1 — safe implementer selects an out-of-bounds slot

**Implementation: UNSOUND. Proof artifact: missing and not repairable under the current safe contract.** A downstream crate can write, with `audited_crate` denoting this crate:

```rust
struct Bad;
impl audited_crate::Slot for Bad {
    fn index() -> usize { 2 }
}
let mut pair = [0, 0];
audited_crate::increment::<Bad>(&mut pair);
```

This contains no unsafe operation or unmet caller obligation. The ordinary impl is legal for the downstream-local `Bad`; `Slot` imposes no safety condition. `increment` is also safe. Its call to `Bad::index()` returns 2, so line 16 executes `pair.get_unchecked_mut(2)` after array-to-slice method resolution with length 2. Thus the exact required proposition `2 < 2` is false. The linked Rust 1.82.0 standard-library contract says the call itself is UB even if its resulting reference is never used. This completes the existential certificate; it is not merely a missing universal proof.

The absent adjacent `SAFETY` comment is independently deficient. No truthful comment can derive O-BOUND for arbitrary safe implementations. Minimum repair is to enforce the bound or remove this generic unsafe path; changing prose alone cannot add a hidden precondition to safe callers or implementers.

## TCB and evidence

`TCB-R033` contains only the exact Rust 1.82.0 Reference/std axioms linked above: public reachability and legal local-type trait implementation, `get_unchecked_mut`'s return/bounds contract, and `wrapping_add`'s modular result. They are the controlling authorities selected by the request, not additional assumptions. No dependency, tool result, implementation behavior, compatibility premise, test, or deployment restriction is consumed.

## Preferred redesign

Delete `Slot`, its impl, the marker `Tail`, the type parameter, and the unsafe operation. The stated behavior needs only a concrete safe function:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its contract is: no caller safety preconditions; on normal return, initial `[a, b]` becomes `[a, b.wrapping_add(1)]`. The fixed array type and constant index make the access locally checkable, while safe indexing removes the unsafe contract entirely. Keeping `Tail` as an associated-function namespace is possible but adds surface without supplying required capability.

This intentionally breaks source compatibility: `increment::<Tail>(&mut pair)` migrates to `increment(&mut pair)`; `Slot` implementations and other generic instantiations disappear. The request authorizes that delta because the abstraction is unreleased and those uses need not survive.

The proposal is not a new verdict. After implementation, freshly audit the exact new snapshot: public surface and migrated in-scope callers, the fixed index/array-length argument, the wrapping postcondition for every `u32`, absence of unsafe or callback-selected indexing, and Rust-1.82 target/profile closure. Re-audit on source/API changes, reintroduced generic dispatch or unsafe code, new configurations/generated code, or a change to the consumed Rust contracts.
