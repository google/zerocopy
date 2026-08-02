# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

**Snapshot.** Exactly the supplied `lib.rs`; no expansion or generated artifact. Scope is Rust and standard library 1.82.0, every target on which this source and the used items exist, and every ordinary profile. Audit cutoff: 2026-08-01. There are no dependencies, features, `cfg`s, build scripts, FFI, assembly, concurrency, allocators, or additional TCB assumptions.

**Current safe-API soundness: UNSOUND.** A well-typed safe downstream implementation of `Slot` can return `2`; `increment` then executes `get_unchecked_mut(2)` on a two-element array. Rust 1.82 documents that an out-of-bounds call is undefined behavior even if the reference is unused.

**Required `Tail` behavior: PROVED.** For every initial `[a, b]`, `increment::<Tail>` returns with `[a, b.wrapping_add(1)]`, and this execution is free of undefined behavior. This regional result does not alter the whole safe-API verdict.

**Combined current-artifact result: UNSOUND.** The source documents no other postcondition. The `Tail` behavior is included because `REQUEST.md` expressly requires it.

## Exact domain and configuration closure

Let a case be `(t, p, S, pair, execution)`. `Required` means: this exact source; Rust/std 1.82.0; `t` is any target on which the source and used items exist; `p` is any ordinary profile; `S` is any type satisfying the public safe bound `Slot`; `pair` is any valid `&mut [u32; 2]`; and the call is well-typed safe Rust. `Required_cfg(t,p)` is its Rust/target/profile projection. This is an equality-preserving transcription of the request, not a sampled inventory or inferred support promise.

The source has one unconditional path and no generation or selection stage. Target/profile facts do not control the index, length, call, or library contracts used below. The counterexample is therefore parametric over every member of `Required_cfg`; one required case is already sufficient for `UNSOUND`. The `Tail` proof is likewise parametric over the full configuration projection and all `pair` values. No version-bridging premise is used.

## Boundary, surfaces, and invariants

- `Slot` and its safe associated function `index` are public; associated items in a public trait are public by default, and root-public items are externally accessible. [Rust 1.82 visibility](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy)
- A downstream crate can define local `Oob` and write `impl Slot for Oob`: the implementation supplies the sole required item, and the local implementing type satisfies the orphan rule. Only unsafe traits require `unsafe impl`; `Slot` is not declared unsafe. [Rust 1.82 trait implementations](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations)
- `Tail` is a public unit struct (including its constructor) with the crate-owned `Slot` implementation. `increment` is a public safe generic free function. Its unsafe block is the only unsafe operation.
- There are no fields, methods, other trait items/impls, callbacks, macros, hidden APIs, reexports, or invariant-bearing state. No abstraction invariant constrains caller implementations of `Slot`.

## Authority/TCB log `TCB-1`

There are no admitted non-authoritative premises. These checked Rust 1.82 axioms are the entire authority inventory:

- **AX-ACCESS:** the visibility and implementation propositions stated above; consumers: witness validity and safe-surface inventory.
- **AX-GET:** `get_unchecked_mut` “returns a mutable reference to an element or subslice” without bounds checking, and calling it with an out-of-bounds index is UB even if unused. The page specifically identifies `len` as UB. Consumer: the unsafe-call obligation and `Tail` result. [Rust 1.82 slice contract](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)
- **AX-WRAP:** `wrapping_add` computes modular addition, wrapping at the type boundary. Consumer: the required value postcondition. [Rust 1.82 `u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)

All apply exactly to Rust/std 1.82.0; changing that identity or any cited contract triggers review.

## Obligation ledger and proofs

**O1 — safe generic boundary.** Every safe call must establish `S::index() < 2` before the unsafe operation. Neither `S: Slot` nor any check establishes it. **Refuted; FIND-1.**

**O2 — unsafe call for `Tail`.** `Tail::index()` returns literal `1`; `[u32; 2]` has length `2`; hence `1 < 2`. AX-GET then supplies a mutable reference to element 1. **PROVED** for all `Tail` cases.

**O3 — update/postcondition for `Tail`.** The sole store is through that element-1 reference. AX-WRAP makes the stored value old element 1 plus one modulo the `u32` range; element 0 is not written. There is no alternative source path. **PROVED** for all initial arrays and configurations.

**O4 — local proof artifact.** The unsafe block has no adjacent `SAFETY` proof. The reconstruction in O2 proves only `Tail`, not arbitrary `S`, so no truthful generic safety comment can repair the current implementation. **Deficient and implementation-unsound.**

Aggregate positive coverage for the required `Tail` claim is `O2-covered ∩ O3-covered = Required_Tail`, establishing `Required_Tail ⊆ Covered_Tail`. Aggregate coverage for universal safe-API soundness fails at O1 and is existentially refuted below.

## FIND-1 — safe implementer selects an out-of-bounds index

**Status: UNSOUND; proof artifact missing.** Consider downstream safe code:

```rust
struct Oob;
impl Slot for Oob { fn index() -> usize { 2 } }
let mut pair = [0u32, 0u32];
increment::<Oob>(&mut pair);
```

**Valid use.** AX-ACCESS plus the source’s public, non-unsafe declarations make the implementation and call available without any caller-side unsafe obligation. The implementation defines the only required associated item and is coherent because `Oob` is local.

**Reachability.** Monomorphization does not change the written control flow: `S::index()` returns `2`, which is passed directly to the executed `get_unchecked_mut` call before the store.

**False safety proposition.** The array length is `2`, so the supplied index equals `len` and is out of bounds.

**UB consequence.** AX-GET expressly makes that call UB even if its result is never used. Thus the whole execution witnesses soundness failure; it cannot witness a defined postcondition failure. No separate required postcondition is refuted.

Minimum repair is to stop relying on an unenforced safe-implementer promise: validate the index, make and fully document an unsafe trait, effectively seal it, or remove the genericity. The stated requirements make removal preferable.

## Preferred redesign (not a verdict on new code)

Replace `Slot`, `Tail`, and generic `increment<S>` with the specialized safe operation:

```rust
pub fn increment_tail(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its contract has no safety precondition: for every valid input `[a,b]`, normal return produces `[a, b + 1 mod 2^32]`. The fixed array type and safe indexing enforce the only memory-selection fact; AX-WRAP supplies the arithmetic postcondition. It exposes no unsafe caller/implementer surface, owns no invariant, and needs no additional TCB premise. This is more parsimonious than sealing a trait whose only required implementation is fixed.

**Migration/contract delta.** Remove the public `Slot` implementer contract, `Slot::index`, the nominal `Tail` constructor/implementation, and generic calls. Change the required internal call from `increment::<Tail>(&mut pair)` to `increment_tail(&mut pair)`. Downstream implementations and generic calls intentionally cease to compile; the request authorizes that break and states the API is unreleased. The required observable behavior is unchanged.

**Fresh audit after implementation.** Treat it as a new snapshot: re-inventory its actual visibility and all call sites; verify the safe element-selection semantics and AX-WRAP applicability on every requested target/profile; prove both elements’ post-state and all exits; confirm no conditional/generated alternative; and redo `Required ⊆ Covered`. This proposal itself is **not implemented and has no audit verdict**.

## Evidence, residual scope, and triggers

No target was built, run, tested, expanded, or tool-verified; none of those facts supports a conclusion. This is a source-level Rust-semantics audit, not a compiler-backend, binary, platform-implementation, performance, panic-freedom-beyond-the-required-case, or maximal-safe-subset claim. Re-audit on source/API/contract changes, Rust/std or support-domain changes, addition of configuration/generation/dependencies, or implementation of the redesign.
