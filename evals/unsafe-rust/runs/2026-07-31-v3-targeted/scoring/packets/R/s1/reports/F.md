# Focused unsafe-Rust audit and redesign

## Claim, domain, and verdicts

**Snapshot and scope.** This is a source-level review of `lib.rs` exactly as supplied. The in-scope boundary is its public `Slot`, `Tail`, and `increment` items and the single unsafe operation inside `increment`. No generated artifacts, dependencies other than Rust 1.82.0 `std`, or tool-derived evidence were supplied or used; the source was not built, tested, executed, or expanded.

Let

`Required(r,t,p) := (r = Rust/stdlib 1.82.0) && source-and-used-items-exist(t) && ordinary-profile(p)`.

This preserves the request's target and profile predicates symbolically. There are no `cfg`s, features, generators, FFI, assembly, allocator choices, concurrency, profile-dependent assertions, or ordinary overflowing `+` operations in the source. Both proofs below are parametric in `t` and `p`; thus no finite target/profile inventory is assumed.

| Claim | Verdict | Certificate |
|---|---|---|
| Every well-typed safe use of the current public surface is free of Rust UB over `Required` | **UNSOUND** | `F-1` gives a valid safe call that executes `get_unchecked_mut(2)` on a length-2 array; this is UB. The witness works throughout `Required`. |
| For every initial `[a,b]`, current `increment::<Tail>` returns with `[a, b+1 mod 2^32]` without UB over `Required` | **PROVED** | `P-TAIL` below; aggregate `Covered = Required`, so `Required ⊆ Covered`. |

The combined current-artifact soundness result is **UNSOUND**. The proved `Tail` subcase neither narrows the current safe generic API nor changes that verdict. There is no source-documented postcondition for generic `increment`; the second claim is the behavior expressly required by the request.

**TCB-1.** No additional TCB assumptions are admitted. The only ground premises are these verified, version-exact authoritative standard-library axioms:

- `AXIOM-BOUNDS`: Rust 1.82.0 says, “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” It also says the method returns a mutable reference to the indexed element/subslice. [slice::get_unchecked_mut](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)
- `AXIOM-WRAP`: Rust 1.82.0 specifies modular addition, “wrapping around at the boundary of the type.” [u32::wrapping_add](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)

These axioms apply to every member of `Required` by construction (exact Rust/stdlib version, and only targets where the items exist).

## Boundary, invariants, and obligation ledger

The complete crate-owned surface is: public safe trait `Slot`; its safe implementer-controlled `index() -> usize`; publicly constructible unit struct `Tail`; the safe `Slot for Tail` impl returning `1`; and public safe generic function `increment<S: Slot>`. There are no unsafe declarations, fields, impls, macros, hidden items, callbacks, or explicit constructors beyond the unit-struct constructor. Downstream safe code may implement `Slot` for a downstream-local type. No invariant enforces `S::index() < 2`; documentation cannot supply a hidden safety precondition to either safe boundary.

| ID | Proposition and disposition |
|---|---|
| `O-OPEN` | Every safe `Slot` implementation used by `increment` must return an index below 2. **False:** neither the type nor validation, privacy, or sealing enforces it. |
| `O-BOUNDS` | At the unsafe call, `S::index()` must be in `0..2`. **False in general** by `F-1`; true for `Tail`. |
| `O-TAIL` | `Tail::index() = 1` and `1 < 2`. **Proved directly from the impl and array type.** |
| `O-POST` | The selected element receives old value plus one modulo `2^32`. **Proved for `Tail`** from `O-TAIL`, the returned-reference postcondition, assignment, and `AXIOM-WRAP`. |

`P-TAIL`: for input `[a,b]`, the inspected impl makes the index exactly `1`; a `[u32; 2]` has indices `0` and `1`. `AXIOM-BOUNDS` therefore is not violated, and `get_unchecked_mut` returns a mutable reference to element 1. `wrapping_add(1)` produces `b+1 mod 2^32`; assignment writes that value only to element 1, leaving element 0 as `a`. These facts do not vary by target or ordinary profile.

The unsafe block has no adjacent `SAFETY` proof. That proof artifact is missing, but prose cannot repair the false generic obligation; the implementation must change or the implementer set must be enforced.

## F-1 — open safe trait makes the safe function unsound

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0, 0];
increment::<Bad>(&mut pair);
```

This is a well-typed, entirely safe downstream use: `Slot` and its method are safe and public, and the implementation uses a downstream-local type. The call reaches the unsafe operation because `Bad::index()` returns normally. The exact required proposition is `2 < pair.len()`; it is false because `pair.len() = 2`. `AXIOM-BOUNDS` then entails UB at the call itself, even before any use of the returned reference. This completes the existential `UNSOUND` certificate for every `Required` configuration. No separate UB-free postcondition refutation is claimed.

## Recommended provable abstraction

The minimum capability is not implementer-selected indexing; it is one fixed transformation. Delete `Slot`, `Tail`, their impl, and the generic parameter, and implement only:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

**Proposed contract.** This safe function has no caller-side safety precondition beyond a well-typed `&mut [u32; 2]`. On return, element 0 equals its old value and element 1 equals its old value plus one modulo `2^32`. It has no representation invariant or unsafe surface. Constant safe indexing is within the type-enforced length; even an indexing defect would panic rather than create an unchecked reference.

**Migration/contract delta.** Replace `increment::<Tail>(&mut pair)` with `increment(&mut pair)`. Remove construction/naming of `Tail`, downstream `Slot` implementations, and generic calls; the request explicitly permits all of these breaking source/API changes and states the abstraction is unreleased. The required `Tail` behavior is unchanged, while unsupported extensibility and its hidden range obligation disappear.

This is an unimplemented proposal, not a `PROVED` new artifact. After implementation, freshly audit the exact snapshot: enumerate remaining exports/reexports/generated surfaces; verify all old generic paths are gone; prove both output clauses and any promised panic behavior from applicable Rust 1.82.0 contracts; re-establish `Required ⊆ Covered`; and recheck that no unsafe operation or invariant remains. Re-audit on source/API changes, Rust or support-domain changes, newly generated surfaces, or material changes to either consumed standard-library contract.
