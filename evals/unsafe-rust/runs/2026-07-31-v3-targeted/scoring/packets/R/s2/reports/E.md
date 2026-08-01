# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

Audited artifact: `lib.rs`, SHA-256 `b2d9d02f117745925aa24c5b09461c200c3f36f1d1e026c1f289f971711dc122`; request SHA-256 `2d044b4aa4dca16c51aeedd3bd9db58d182a0929e6b73a98478fdc2710094b8f`. Scope is exactly this source, under documented Rust abstract semantics. No source was executed or expanded; no generated artifacts, dependencies, `cfg`s, features, FFI, concurrency, or allocator behavior occur in the supplied artifact.

`DOMAIN-R1` is preserved directly from the request:

> Rust and standard library exactly 1.82.0; every target on which this exact source and its used 1.82.0 standard-library items exist; every ordinary profile.

Other Rust releases, targets where those conditions fail, nonordinary profiles, compiler/backend correctness, and any wider crate are excluded. Audit cutoff: 2026-08-01; it does not broaden the fixed version.

- **CLAIM-SOUND — UNSOUND.** The public safe generic `increment<S: Slot>` is not sound for all well-typed safe uses. `F-1` below supplies a valid safe witness, reachability, a false unsafe precondition, and the authoritative UB consequence. The witness is parametric over every configuration in `DOMAIN-R1`.
- **CLAIM-TAIL — PROVED.** For every initial `[a, b]: [u32; 2]` and every configuration in `DOMAIN-R1`, `increment::<Tail>` is UB-free and returns with `[a, b.wrapping_add(1)]`. `P-TAIL` below proves this requested behavior independently of the redesign.
- **Combined current-artifact result: UNSOUND.** There is no source-authored documented generic postcondition. The UB-containing witness is not used to claim `CONTRACT-BROKEN`.

TCB log `TCB-R1` contains only the two accepted Rust 1.82 authoritative axioms below; there are no additional admitted assumptions, dependency facts, implementation claims, or tool results.

## Boundary, invariants, and obligation ledger

The complete relevant language-reachable surface is: public safe trait `Slot` and its safe implementer-provided static method `index`; public constructible unit struct `Tail` and its safe `Slot` impl; and public safe generic function `increment`. There are no fields, unsafe declarations/impls, macros, hidden items, callbacks other than `S::index`, or generated APIs in the supplied source. Downstream code may implement `Slot` for a downstream type because the trait is public and unsealed.

No enforced invariant connects `Slot` to the two-element array. The tempting proposition `S::index() < 2` is neither type-enforced, checked, nor module-owned. Its producer is adversarial safe code (`S::index`); its consumer is `get_unchecked_mut`.

| ID | Obligation | Status |
|---|---|---|
| O-1 | Every safe `increment::<S>` call avoids UB without a hidden caller/implementer safety condition. | **Refuted: F-1** |
| O-2 | At the unsafe call, `S::index()` is in bounds for the length-2 slice. | **False generically; proved for `Tail`** |
| O-3 | The returned reference denotes the selected element and is used within the exclusive `&mut` borrow. | **Proved when O-2 holds, by the method contract and types** |
| O-4 | The stored value is old value plus one modulo the `u32` range. | **Proved by AX-WRAP** |
| O-5 | Element 0 is unchanged for `Tail`. | **Proved: only the reference to element 1 is written** |

The unsafe block has no adjacent `SAFETY` proof. This is a missing proof artifact, but documentation alone cannot repair O-1: prose on a safe trait cannot impose a soundness precondition on safe implementers.

## Authoritative premises (`TCB-R1`)

- **AX-SLICE (accepted AXIOM).** Rust 1.82 [`slice::get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) returns a mutable reference to the indexed element/subslice without checking bounds and states: “Calling this method with an out-of-bounds index is undefined behavior.” Scope: every `DOMAIN-R1` use of this item. Consumers: O-2, O-3, F-1, P-TAIL.
- **AX-WRAP (accepted AXIOM).** Rust 1.82 [`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add) specifies wrapping modular addition at the type boundary. Scope: every `DOMAIN-R1` use of this item. Consumers: O-4, P-TAIL.

Both citations were opened at the exact version and fragment. Re-audit either entry if that exact documentation, source, or supported domain changes.

## F-1 — complete UB certificate

Downstream safe code can write:

```rust
struct Oob;
impl Slot for Oob {
    fn index() -> usize { 2 }
}
let mut pair = [0, 0];
increment::<Oob>(&mut pair);
```

**Valid use.** The trait and method are safe and public; the implementation and call are well-typed and contain no caller-written unsafe operation or violated documented obligation.

**Reachability.** `Oob::index()` returns `2`; `increment` then executes `pair.get_unchecked_mut(2)` on the two-element array viewed as a slice of length 2.

**False safety proposition.** Its valid element indices are 0 and 1, so index 2 is out of bounds.

**Consequence.** AX-SLICE says that this call itself has undefined behavior, even independently of later reference use. Thus one valid safe use reaches an executed operation whose required proposition is false and whose applicable contract entails UB. The same construction uses no target- or profile-dependent fact, so it witnesses every member of `DOMAIN-R1`.

Minimum repair requires enforcing the bound before the unsafe call, making an implementer obligation compiler-enforced, or removing the unnecessary extensibility. The last is preferred below.

## P-TAIL — requested-behavior proof and configuration closure

`Tail::index()` is locally and unconditionally `1`. The input type fixes length at 2, hence 1 is in bounds. AX-SLICE therefore supplies a mutable reference to element 1. The subsequent assignment reads that element, applies AX-WRAP with operand 1, and writes only through that reference; element 0 is untouched. This proves UB freedom and the exact `[a, b] -> [a, b.wrapping_add(1)]` postcondition for all `u32` values.

The source has no conditional compilation or profile-sensitive arithmetic: unchecked indexing's contract and modular addition apply parametrically across the request's target/profile predicate. Thus `Covered(CLAIM-TAIL) = DOMAIN-R1`, proving `Required ⊆ Covered`. For CLAIM-SOUND, F-1 applies parametrically across the same domain; no configuration remainder can weaken its `UNSOUND` verdict.

## Preferred redesign

Replace the trait, marker, generic dispatch, and unsafe operation with one specialized safe function:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    let tail = &mut pair[1];
    *tail = tail.wrapping_add(1);
}
```

Its proposed public contract has no safety precondition: on normal return, element 0 equals its entry value and element 1 equals its entry value plus one modulo `u32`. It has no invariant-bearing representation, downstream implementer contract, generic capability, or unsafe proof site. Fixed index 1 is valid by the array's type; `wrapping_add` supplies the requested arithmetic. This is the minimum capability actually required.

Migration changes `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. `Slot`, downstream `Slot` implementations, generic calls, and the nominal `Tail` marker disappear. Those are breaking source/contract changes, explicitly authorized because the abstraction is unreleased and none must be preserved. No caller safety obligation is transferred.

This is a design, not a verdict for a new artifact. After implementation, freeze and audit that exact snapshot anew: re-inventory every exposed/reexported/generated surface; verify the fixed-index operation for `[u32; 2]`, borrow/dataflow, AX-WRAP postcondition, both elements' outcomes and every exit; confirm no unsafe or hidden extensibility remains; and re-establish parametric `DOMAIN-R1` closure. Any changed signature, documentation, configuration, generated code, standard-library contract, or Rust version triggers re-audit.

## Residual attestation

Every in-scope surface and unsafe obligation has a disposition above. No test or absence of counterexamples supports either verdict. No independent second review was performed.
