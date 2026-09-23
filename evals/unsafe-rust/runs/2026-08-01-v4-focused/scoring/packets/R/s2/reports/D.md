# Focused literal audit and redesign

## Claim, domain, and results

**Current-artifact soundness: `UNSOUND`.** For the complete supplied `lib.rs`, a well-typed entirely safe downstream use reaches undefined behavior. This verdict is independent of the redesign below.

**Requested `Tail` behavior: `PROVED`.** For every initial `pair = [a, b]`, `increment::<Tail>(&mut pair)` returns normally with `[a, b.wrapping_add(1)]`. This is a user-requested robustness result, not a documented current-API postcondition.

There are no documented postconditions or unsafe public APIs, so no `CONTRACT-BROKEN` claim applies.

Let `T` be exactly the targets on which this source and its used Rust 1.82.0 standard-library items exist, and `P` every ordinary profile. A required case is

`Required(source, rust, target, profile, S, pair, execution) := source = supplied lib.rs ∧ rust = 1.82.0 ∧ target ∈ T ∧ profile ∈ P ∧ the call is a well-typed safe use`.

Thus `Required_cfg = {1.82.0} × T × P`. This is the request's predicate verbatim, not a finite target inventory. The source has no `cfg`, features, dependencies, generators, FFI, assembly, concurrency, allocation, or profile-sensitive operation. The proofs and counterexample below are parametric in `target ∈ T` and `profile ∈ P`; optimization, overflow-check, panic-strategy, and debug-assertion differences do not alter them. Audit cutoff: 2026-08-01.

## Boundary and obligation inventory

The complete language-reachable crate-owned surfaces are: public safe trait `Slot` and its public safe associated function `index`; public constructible unit struct `Tail`; the crate-owned `Slot for Tail` implementation; and public safe generic function `increment<S: Slot>`. The sole unsafe operation is `pair.get_unchecked_mut(S::index())`. `wrapping_add` and assignment are safe. There are no fields, constructors beyond the unit-struct expression, macros, hidden items, callbacks, or explicit unsafe declarations. No enforced invariant constrains implementations of `Slot` or their returned index.

| ID | Obligation | Disposition |
|---|---|---|
| O1 | Every safe call to `increment<S>` must pass an in-bounds index to `get_unchecked_mut`. | **Refuted; F1.** |
| O2 | For `Tail`, the selected index is in bounds for `[u32; 2]`. | `Tail::index()` is source-constant `1`; valid indices are `0,1`. **Proved** for all required configurations. |
| O3 | The requested normal result for `Tail` is `[a, b+1 mod 2^32]`. | O2 makes the returned reference designate element 1; assignment changes that element only; `wrapping_add(1)` supplies the modular value. **Proved**. |
| O4 | Every required configuration reaches the reviewed source and the same material semantics. | Exact source only, with no selectors or generated stages; O1–O3 are target/profile-parametric. **Proved**. |

## F1 — safe trait implementation causes out-of-bounds unchecked access

Severity/classification: **UNSOUND implementation defect; missing local proof artifact.** The unsafe block has no adjacent `SAFETY` proof, but documentation alone cannot repair the false premise.

A downstream crate can write entirely safe code:

```rust
struct Bad;
impl audited_crate::Slot for Bad {
    fn index() -> usize { 2 }
}
let mut pair = [0, 0];
audited_crate::increment::<Bad>(&mut pair);
```

Certificate:

1. **Valid in-scope use.** `Slot` and `increment` are public at crate root. `Slot` is a safe trait and states no behavioral contract. The Rust 1.82 orphan rule permits this implementation because `Bad` is local to the downstream crate; its relevant clause is “At least one of the types `T0..=Tn` must be a local type.” There are no uncovered type parameters. The call is to a safe function and uses no unsafe operation at the call site. ([visibility](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy), [trait implementations](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations), [unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits))
2. **Reachability.** `Bad::index()` returns `2`; `increment` unconditionally calls `get_unchecked_mut(2)` on the borrowed `[u32; 2]`.
3. **False safety proposition.** Index `2` is outside the two-element array's index set `{0,1}`.
4. **UB consequence.** Rust 1.82 documents: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” ([`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut))

This witness works for every `target ∈ T` and ordinary profile. One valid required execution suffices to refute universal safe-API soundness. No UB-free postcondition refutation is needed or claimed.

## Authority and trust

TCB revision `TCB-0` contains only the exact Rust 1.82 Reference/std propositions cited above and the `u32` contract: “Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.” ([`wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)) These are version-matched Rust axioms, not additional assumptions. There are no dependencies, tool results, prior audits, external specifications, implementation claims, or deployment assumptions. Review was source-only; nothing was built, executed, tested, or expanded.

## Preferred design

Remove `Slot` and the generic free function. Retain the crate-owned name as one safe inherent operation:

```rust
pub struct Tail;

impl Tail {
    pub fn increment(pair: &mut [u32; 2]) {
        pair[1] = pair[1].wrapping_add(1);
    }
}
```

Proposed contract: for every `[a,b]`, `Tail::increment` has no caller safety precondition, returns normally, leaves element 0 equal to `a`, and sets element 1 to `b + 1 mod 2^32`. The fixed array type makes index `1` locally in bounds; ordinary checked indexing removes all unsafe code, implementer promises, invariants, and additional TCB premises.

Migration is intentionally source-breaking but authorized for this unreleased abstraction: replace `increment::<Tail>(&mut x)` with `Tail::increment(&mut x)`; remove downstream `Slot` implementations and generic calls, which the requirement expressly does not preserve. The required `Tail` behavior is unchanged. Do not regard this sketch as audited or `PROVED`.

After implementation, audit the new snapshot afresh: verify the actual visibility/reexports and absence of generated or conditional alternatives; inventory every remaining safe/unsafe surface; prove index `1` is in bounds from `[u32;2]`; prove normal return, element-0 preservation, and wrapping element-1 update for every input, target in `T`, and ordinary profile; reconcile the final documentation with that contract; and repeat the configuration/TCB closure if source, support policy, dependencies, or Rust version changes.

Residual scope: binary/backend correctness, nonordinary profiles, other Rust releases, unavailable targets/items, performance, and APIs other than the supplied source are excluded by the request.
