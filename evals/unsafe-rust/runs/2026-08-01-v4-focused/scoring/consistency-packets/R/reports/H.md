# Focused unsafe-Rust audit and redesign

## Claim, domain, and verdicts

**Snapshot.** Exact supplied `lib.rs`, lines 1–18; no generated artifacts, dependencies, conditional compilation, or build inputs are present in the supplied scope. Review was static only. Skill basis: supplied unsafe-Rust package.

Let `D` be exactly: Rust compiler and standard library 1.82.0; every target on which this source and the used 1.82.0 standard-library items exist; every ordinary profile. This preserves the requester’s symbolic target predicate rather than inventing a finite target list.

**SOUND-CURRENT — UNSOUND over `D`.** Claim: every well-typed safe use of the public surfaces `Slot`, `Tail`, and `increment` is free of Rust undefined behavior. Finding F1 gives a valid safe-use UB witness. It is target-, edition-, optimization-, overflow-check-, and panic-strategy-independent, so it refutes the claim in every case in `D`. No proposal below affects this verdict.

**REQ-TAIL — PROVED over `D`.** For every initial `[a, b]: [u32; 2]`, `increment::<Tail>` returns normally with `[a, b.wrapping_add(1)]` and no UB. This is the requester’s required crate-owned behavior, not an inferred documented guarantee of the otherwise undocumented current API.

There are no documented unsafe-API postconditions: the crate declares no unsafe API. The requested Tail behavior is assessed separately above.

## Boundary and obligation inventory

All items are at crate root. `Slot` is a public **safe** trait; its required associated function `index` is public by default. `Tail` is a public unit struct, with a safe `Slot` implementation returning `1`. `increment<S: Slot>` is a public safe generic function accepting every safe implementation satisfying the type bound. Its sole unsafe operation is `pair.get_unchecked_mut(S::index())`; the returned exclusive reference is then read via `wrapping_add(1)` and written.

There is no representation invariant. The only needed local proposition is `S::index() < 2` at line 16. No type, validation, privacy boundary, or trait contract establishes it. The `unsafe` block has no adjacent safety proof.

| ID | Obligation | Status |
|---|---|---|
| O1 | Every safe `Slot` implementation used with `increment` returns an index below 2. | False; F1 |
| O2 | At line 16, the unchecked index is in bounds. | False for F1; true for `Tail` |
| O3 | For `Tail`, only element 1 changes, to modular old-value-plus-one. | Proved below |
| O4 | `Required = D` is covered. | F1 and the Tail proof are parametric over all of `D` |

## F1 — safe implementer controls an unchecked index

**Implementation classification:** UNSOUND. **Proof artifact:** missing, and no correct proof exists for the current generic contract.

A downstream crate can write entirely safe code equivalent to:

```rust
struct OutOfBounds;
impl Slot for OutOfBounds {
    fn index() -> usize { 2 }
}

let mut pair = [0, 0];
increment::<OutOfBounds>(&mut pair);
```

This is a valid in-scope use. Rust 1.82 says a `pub` item is externally accessible when its ancestor modules are accessible, and associated items in a public trait are public by default ([visibility](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy)). The downstream implementing type is local there, satisfying the orphan rule’s local-type alternative ([trait implementations](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations)). `Slot` is not an unsafe trait; Rust reserves `unsafe trait`/`unsafe impl` for extra implementer safety conditions ([unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits)). Thus neither defining the implementation nor calling `increment` requires an unsafe act or an undocumented obligation from this caller.

The call reaches line 16 with a slice of length 2 and index 2. Rust 1.82 specifies that calling `get_unchecked_mut` with an out-of-bounds index is undefined behavior even if the resulting reference is unused ([`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)). The false required proposition is `2 < 2`. The UB occurs at the call itself. Rust also states that an unsafe block asserts its operations’ extra safety conditions have been discharged; it does not impose them on callers of a containing safe function ([unsafe functions/blocks](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-functions-unsafe-fn)). This closes valid use → reachability → false safety condition → documented UB.

No UB-free postcondition counterexample is needed or claimed. Minimum repair is to stop relying on an unenforced safe-implementer property: check the index, make and document an unsafe trait, effectively seal it, or remove the genericity. The last is preferred because only `Tail` is required.

## Proof of REQ-TAIL

`Tail::index()` is exactly `1`; `[u32; 2]` has length 2, hence `1 < 2`, satisfying the unchecked call’s complete stated bounds condition. The input `&mut` borrow supplies exclusive mutable access for the returned reference. Line 17 touches only that reference. Rust 1.82 defines `u32::wrapping_add` as modular addition wrapping at the type boundary ([`wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)). Therefore element 0 remains `a`, element 1 becomes `b + 1 mod 2^32`, and no arithmetic profile branch arises. These facts and cited contracts apply uniformly to `D`, so `D ⊆ Covered`.

## TCB log

**TCB-R182-1:** only the five Rust 1.82 Reference/std propositions cited above are consumed as authoritative AXIOM entries; each was checked at its exact versioned allowlisted URL. There are no SAFE-DEP, UNSAFE-DEP, external, implementation, tool, deployment, compatibility, or probabilistic assumptions. Consumers: F1 and REQ-TAIL. Re-audit on source/API change, support-domain change, or material change to any cited Rust 1.82 contract. No tool-derived evidence or prior audit was used.

## Recommended abstraction

Replace `Slot`, `Tail`, and generic `increment` with the single safe operation the requirement needs:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    let tail = &mut pair[1];
    *tail = tail.wrapping_add(1);
}
```

Its proposed contract is: for every `[a, b]`, return `[a, b + 1 mod 2^32]`; it has no caller safety precondition. The fixed array type and constant index make the selected element locally checkable, safe indexing performs the bounds enforcement, and all unsafe code, implementer obligations, invariants, and generic proof fan-out disappear. A sealed marker would preserve unnecessary machinery; an unsafe trait would export an unnecessary unsafe obligation.

**Migration delta.** Delete the public `Slot` trait and `Tail` type; change calls from `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Downstream `Slot` implementations and generic calls cease to compile, expressly permitted because the abstraction is unreleased and they need not be preserved. The required observable Tail behavior is unchanged.

This design is not implemented and has no audit verdict. After implementation, freshly audit the exact new snapshot: enumerate its resulting public surface and all call sites/reexports; prove constant index 1 is in bounds for `[u32; 2]`; prove the modular postcondition and that element 0 is unchanged; confirm no generated/configuration-specific alternate implementation; and re-establish `D ⊆ Covered`. Re-audit any change to the signature, array length, chosen index, arithmetic, visibility, support predicate, or cited contracts.
