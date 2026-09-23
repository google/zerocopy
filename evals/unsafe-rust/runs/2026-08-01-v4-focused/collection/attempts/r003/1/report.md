# Focused literal audit and redesign

## Claim, snapshot, and verdict

The snapshot is exactly `target/lib.rs` as supplied. `Required` is Rust 1.82.0, every target on which this source and the used 1.82.0 standard-library items exist, every ordinary profile, and every well-typed safe use of the public API. There are no `cfg`s, features, dependencies, generated artifacts, macros, FFI, concurrency, allocator choices, or profile-sensitive arithmetic in the source. Thus the source, API, and proof obligations are identical throughout that symbolic target/profile domain; no finite target inventory is assumed.

**Current-artifact soundness: UNSOUND.** A valid downstream safe implementation can supply an out-of-bounds index to the executed `get_unchecked_mut` call. The complete witness is below. This result is independent of the redesign.

**Crate-owned Tail behavior: PROVED.** For every initial `pair == [a, b]` in `Required`, `increment::<Tail>(&mut pair)` changes it to `[a, b.wrapping_add(1)]`. This is the separately requested behavioral subclaim, not a repair of the universal safe-API verdict. The source documents no API postcondition, so there is no additional documented-postcondition verdict.

TCB `TCB-R003` contains only the exact Rust 1.82.0 Reference/std axioms cited below; there are no additional assumptions, dependencies, prior results, or tool-derived evidence. No source was built, executed, tested, or expanded.

## Boundary, invariant, and obligation coverage

The complete relevant surface is: public safe trait `Slot`; its public safe associated function `index`; public unit struct `Tail`; crate-owned safe `impl Slot for Tail`; public safe generic function `increment`; and its internal unsafe call at line 16. Public-trait associated items are public by default, and public items are externally accessible through accessible ancestors ([visibility authority](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy): “Associated items in a `pub` Trait are public by default”). A downstream crate may implement this trait for its own nominal type: the orphan rule permits an implementation when a participating type is local and the earlier uncovered-parameter restriction is met, vacuously here ([implementation authority](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations)).

The needed generic invariant is `S::index() < 2` at line 16. Nothing owns or enforces it: `Slot` is neither private/sealed nor `unsafe`, `index` has no checked range type, and `increment` performs no check. Unsafe traits are the mechanism whose implementations accept extra safety conditions; they and their implementations require `unsafe` ([unsafe-trait authority](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits)). Here both implementation and call are ordinary safe Rust; `increment` exposes no caller safety contract. Rust 1.82 describes unsafe functions as the functions carrying compiler-unchecked caller conditions and requires the `unsafe` prefix ([unsafe-function authority](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-functions-unsafe-fn)).

| ID | Exact obligation | Status |
|---|---|---|
| O1 | Every safe `increment::<S>` call must give `get_unchecked_mut` an in-bounds index. | **Refuted; UNSOUND witness F1.** |
| O2 | For `Tail`, the index is in bounds. | **Proved:** the inspected impl returns literal `1`, and `[u32; 2]` has indices 0 and 1. |
| O3 | The Tail call increments exactly element 1 with wrapping arithmetic. | **Proved:** the unsafe API returns a mutable reference to the selected element when its precondition holds; assignment targets that element, while element 0 is untouched. `wrapping_add(1)` computes modular addition ([wrapping authority](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add): “Wrapping (modular) addition ... wrapping around at the boundary of the type”). |
| O4 | Configuration closure. | **Proved for O2–O3:** the derivation is parametric over every requested target/profile. O1 is refuted throughout that same domain, so a positive aggregate closure certificate is neither claimed nor needed. |

## F1 — safe implementer causes undefined behavior

```rust
struct Bad;
impl Slot for Bad {
    fn index() -> usize { 2 }
}
let mut pair = [0u32, 0u32];
increment::<Bad>(&mut pair);
```

This is a valid in-scope safe use: `Bad` is local downstream, its ordinary trait implementation satisfies coherence, and `increment` is safe. The call reaches line 16 with `S::index() == 2`; a two-element array has no element 2. Rust 1.82 states: “Calling this method with an out-of-bounds index is undefined behavior,” even if the reference is unused ([`get_unchecked_mut` contract](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)). Therefore the executed operation's exact safety proposition is false and authoritative semantics supplies the UB consequence. This completes the existential `UNSOUND` certificate for every requested target/profile. Because the witness contains UB, it is not used as a postcondition refutation.

The unsafe block has no `SAFETY` proof, but documentation alone cannot repair O1: there is no true derivation to document. The minimum generic repair would enforce bounds with safe checked indexing. Given the narrower authorized requirement, the design below is smaller.

## Preferred provable design

Replace the trait, marker type, generic parameter, and unsafe operation with one safe specialized function:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its contract is: for every initial `[a, b]`, normal return leaves `[a, b.wrapping_add(1)]`; it has no caller-side safety precondition. It has no invariant-bearing representation, implementer boundary, or unsafe/TCB premise. The array type fixes the length, literal index 1 supplies the needed projection locally, and `wrapping_add` supplies the required overflow behavior.

Migration deletes `Slot` and `Tail`; `increment::<Tail>(&mut pair)` becomes `increment(&mut pair)`. Downstream `Slot` implementations and generic calls cease to compile. Those are deliberate contract/API removals authorized because the abstraction is unreleased and only Tail behavior must remain.

This proposal is not implemented and has no artifact verdict. After implementation, freshly audit the exact new snapshot: enumerate its public surfaces and any newly introduced configuration/generated code; verify safe indexing is in bounds for `[u32; 2]`; prove the exact element-0 preservation and modular element-1 postcondition; confirm removal/migration of every old trait/generic consumer; and re-establish target/profile closure. Re-audit on any source, signature, behavioral contract, Rust version, supported-target/profile, or standard-library-contract change.
