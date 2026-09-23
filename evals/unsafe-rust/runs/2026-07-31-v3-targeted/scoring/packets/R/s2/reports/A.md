# Focused unsafe-Rust audit: `lib.rs`

## Claim, snapshot, and verdict

**Snapshot.** Exactly the supplied `lib.rs` (19 lines), with no expansion or generated artifact. The audit covers Rust and standard library 1.82.0, every target on which this source and the two used standard-library items exist, and every ordinary profile. The supplied source has no `cfg`, feature, dependency, FFI, allocator, concurrency, macro, or build-time branch. No prior audit or tool-derived evidence was used.

**Soundness theorem.** Every well-typed safe use of the public items `Slot`, `Tail`, and `increment`, including caller-provided safe `Slot` implementations, must be free of Rust undefined behavior under the documented Rust 1.82 abstract semantics.

**Verdict: UNSOUND.** `increment` is safe but its unchecked access requires a property that the open safe trait does not enforce. This holds throughout the supported set; profiles and targets do not alter the source, array length, index, or applicable Rust 1.82 contract.

**Requested `Tail` behavior: PROVED.** Independently of the whole-surface verdict, for every input `pair`, `increment::<Tail>` returns with element 0 unchanged and element 1 equal to its prior value plus one modulo `2^32`.

There are no source-documented postconditions. Consequently no `CONTRACT-BROKEN` verdict applies. The user-stated `Tail` requirement is reported separately as an explicit robustness requirement. The UB witness below is not used as a defined behavioral witness.

## Boundary and obligation coverage

| ID | Safe surface / proof site | Disposition |
|---|---|---|
| API-1 | Public safe trait `Slot` and safe required method `index() -> usize` | Downstream code may implement it; no bound or behavioral contract constrains the result. |
| API-2 | Public unit struct/constructor `Tail`; crate impl of `Slot` | `index()` always returns `1`; adequate for the requested path only. |
| API-3 | Public safe generic `increment<S: Slot>` | Accepts every valid `S: Slot`, then consumes `S::index()` in unsafe code; UNSOUND. |
| OBL-1 | `pair.get_unchecked_mut(S::index())` | Requires the returned index to be in bounds. No check, type fact, sealed boundary, or trait contract establishes this for arbitrary `S`; refuted by WITNESS-1. |
| OBL-2 | Same call for `S = Tail` | `Tail::index() = 1`, and `[u32; 2]` has indices 0 and 1; PROVED. |
| OBL-3 | Tail update | The call returns a mutable reference to element 1; `wrapping_add(1)` computes modular addition; assignment writes that result to element 1. Element 0 is not selected; PROVED. |

There is no owned invariant. The proposition `S::index() < 2` would be needed at API-3, but neither `Slot` nor module privacy establishes it. Proving it for the crate-owned producer `Tail` cannot be reversed into a fact about every implementation of the public trait.

No public fields, unsafe declarations, hidden APIs, reexports, callbacks, custom `Drop`, or generated surfaces occur in the supplied source. The unsafe block has no adjacent `SAFETY` proof. Its proof artifact is therefore missing; more importantly, its general implementation obligation is false, so a comment alone cannot repair it.

## Finding F-1 — safe downstream implementation reaches UB

A valid safe caller can write:

```rust
struct Oob;
impl Slot for Oob {
    fn index() -> usize { 2 }
}

let mut pair = [0, 0];
increment::<Oob>(&mut pair);
```

The caller contains no unsafe operation and violates no contract: `Slot` is a public safe trait and specifies no restriction. `pair` has length 2, hence index 2 is out of bounds. AX-1 states that calling `get_unchecked_mut` with such an index is UB even if its returned reference is unused. The UB occurs at the unchecked call, before wrapping arithmetic. This is a concrete valid-use witness on every in-scope configuration.

**Minimum current-API repair:** enforce the bound before unsafe use, or change the implementer boundary to a sufficient compiler-enforced unsafe/sealed contract and audit every implementation and consumer. Given the authorized requirements, both retain unnecessary machinery; the specialization below is preferable.

## TCB log TCB-R1

Trust policy: only exact authoritative Rust 1.82 standard-library propositions may be consumed. There are no additional assumptions, dependencies, external specifications, compiler-implementation premises, or tools.

- **AX-1 (accepted, Rust axiom):** Rust 1.82 [`slice::get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut), all in-scope targets/profiles: it “Returns a mutable reference to an element or subslice, without doing bounds checking,” and “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” Consumers: OBL-1, OBL-2, F-1.
- **AX-2 (accepted, Rust axiom):** Rust 1.82 [`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add), all in-scope targets/profiles: “Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.” Consumer: OBL-3 and the redesign contract.

Both pages were opened at their exact versioned URLs and checked in context. Re-audit their consumers if those contracts or the Rust version changes.

## Preferred redesign

Remove the unused generic capability and all unsafe code:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    let value = &mut pair[1];
    *value = value.wrapping_add(1);
}
```

**Contract.** This is a safe function with no caller safety precondition. It returns normally with `pair[0]` unchanged and `pair[1] = old(pair[1]).wrapping_add(1)`, equivalently addition modulo `2^32`. The fixed array type makes index 1 locally in bounds; ordinary checked indexing removes the unchecked-operation obligation. AX-2 supplies the arithmetic postcondition. There is no representation invariant, implementer promise, unsafe surface, or additional TCB premise.

**Migration delta.** Delete public `Slot`, `Tail`, the type parameter, and the unsafe block. Change `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Downstream `Slot` implementations and generic calls cease to compile, exactly as authorized; the abstraction is unreleased, so no compatibility commitment is retained. The required observable `Tail` behavior is unchanged.

This is a design proposal, not a verdict for a new artifact. After implementation, freshly audit the exact new source: confirm the old trait/type/generic and all reexports or generated copies are absent; verify Rust 1.82 checked access and AX-2 over the full target/profile set; prove both-element postconditions and all exits; and inventory any surrounding code introduced with the change. Source, API, support-set, or cited-contract changes trigger re-audit.
