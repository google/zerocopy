# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

**Snapshot.** Exact supplied `lib.rs`; no expansion, execution, tests, dependencies, generated artifacts, or prior audit were used. Audit date: 2026-08-01. Scope is Rust and standard library 1.82.0, every target on which this exact source and its used standard-library items exist, and every ordinary profile. The source has no `cfg`, feature, target, generator, FFI, allocator, concurrency, or dependency branch. Profile-dependent overflow checks are immaterial because the code explicitly uses wrapping arithmetic.

**Soundness theorem.** Every well-typed safe use of the public surfaces must be free of Rust undefined behavior, with no caller safety precondition, over that supported set.

**Current-artifact soundness verdict: UNSOUND (F-1).** The result is universal across the supported set; a safe downstream trait implementation can select an out-of-bounds index.

**Required `Tail` behavior: PROVED.** For every initial `pair == [a, b]`, `increment::<Tail>(&mut pair)` returns without UB with `pair == [a, b.wrapping_add(1)]`. This requested behavior is not a source-documented postcondition, so there is no separate `CONTRACT-BROKEN` result. The overall safe API remains `UNSOUND` despite this regional proof.

**TCB:** `TCB-1` below. It contains only verified Rust 1.82.0 standard-library axioms and no additional admitted assumptions. Conditional application claims: none.

## Boundary, invariants, and obligation ledger

Public safe surfaces are: implementable trait `Slot`; safe associated function `Slot::index`; constructible unit struct `Tail`; its safe `Slot` implementation; and safe generic free function `increment<S: Slot>`. The sole unsafe operation is the internal `get_unchecked_mut` call. There are no unsafe public APIs, fields, macros, hidden items, or generated surfaces in the supplied source. Ordinary unit-struct construction and auto traits do not supply an index-range guarantee.

No enforced invariant exists. The needed proposition, `S::index() < 2`, cannot be an invariant of all `S: Slot`: the safe public trait permits caller-controlled implementations and its method has neither a type-enforced restriction nor validation.

| ID | Location | Exact obligation | Status |
|---|---|---|---|
| O-1 | `increment`, unchecked projection | The particular returned index is in bounds for the two-element slice before `get_unchecked_mut` is called. | **False** for general `S`; F-1. |
| O-2 | `increment::<Tail>` | `Tail::index() == 1` and `1 < 2`. | **PROVED** directly from the implementation and array length. |
| O-3 | mutation | On the Tail path, write the old second value plus one modulo the `u32` range, leaving element 0 unchanged. | **PROVED** from O-2, exclusive `&mut` access, A-1, and A-2. |
| O-4 | configuration closure | O-1--O-3 cover every requested target/profile. | **PROVED** parametrically: the fixed length, constants, and cited 1.82 contracts do not vary across this source's supported set. |

For the Tail derivation, method evaluation yields `1`; the receiver has length two, so A-1's only stated safety condition is met. The resulting mutable reference designates element 1 and is used within the exclusive borrow without intervening caller code. A-2 makes the computed value `(b + 1) mod 2^32`; assignment changes only that element. No material derivation is present in the source: the unsafe block has no adjacent `SAFETY` proof. More importantly, no comment could prove O-1 for arbitrary safe implementations.

## F-1 — safe implementer reaches out-of-bounds unchecked access

**Implementation classification:** `UNSOUND`. **Proof artifact:** missing and irreparable under the current safe generic contract.

A downstream crate can use only safe Rust:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0, 0];
increment::<Bad>(&mut pair);
```

`Bad` is caller-controlled and satisfies the complete declared bound. The array/slice length is 2, and `Bad::index()` returns that length. A-1 says this call itself has undefined behavior even if the reference is unused. Thus this valid safe use reaches UB on every supported configuration. This whole-execution witness establishes `UNSOUND`; it is not used as a defined postcondition refutation.

Minimum resolution is to remove the unchecked operation or enforce bounds before it. Merely documenting that a safe `Slot` implementation should return 0 or 1 would leave a hidden safety precondition and would not repair soundness.

## TCB-1 audit log

| ID | Category and exact proposition | Identity, evidence, consumers, disposition |
|---|---|---|
| A-1 | AXIOM: `get_unchecked_mut` returns a mutable element/subslice reference without a bounds check; an out-of-bounds index makes the call UB. | Rust 1.82.0 [`slice::get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut), verified in context. Exact safety text: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” Consumers O-1--O-3; accepted authoritative axiom. |
| A-2 | AXIOM: `u32::wrapping_add(rhs)` computes modular addition at the type boundary. | Rust 1.82.0 [`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add), verified in context: “Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.” Consumer O-3; accepted authoritative axiom. |

There are no safe/unsafe dependency, implementation, tool, external, deployment, probabilistic, or out-of-band entries. No tool-derived evidence was used. Re-audit triggers are any source/API change, supported-set change, or material change to either cited Rust contract.

## Preferred redesign (not a verdict on current source)

The minimum capability is one fixed, safe mutation; neither type-level slot identity nor implementer extensibility is required. Delete `Slot`, `Tail`, the generic parameter, and all unsafe code:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its proposed safe contract is: for every `[a, b]`, return normally as `[a, (b + 1) mod 2^32]`, with no caller safety obligations. Constant `1` is in bounds by the input type; safe indexing localizes enforcement, and A-2 supplies the arithmetic result. There is no representation invariant, unsafe surface, implementer promise, or extra TCB premise.

This intentionally breaking migration replaces `increment::<Tail>(&mut pair)` with `increment(&mut pair)` and removes all `Slot` implementations, generic calls, and references to the marker type. Those losses are expressly authorized for this unreleased API; the required observable mutation is unchanged.

The proposal is unimplemented and has no audit verdict. After implementation, freeze a new snapshot and audit its complete public/reexported and generated surface, confirm the exact fixed index and array type, prove safe indexing and A-2's postcondition over the full supported set, check every normal exit and call-site migration, and re-establish configuration closure. Any retained compatibility wrapper or newly introduced macro/configuration becomes additional audit scope.

## Residual scope and attestation

Only the supplied source and requested Tail behavior were audited; no broader crate or binary claim is made. Every discovered obligation has a status, both allowlisted citations were opened and checked at version 1.82.0, no test result substitutes for proof, and the redesign does not alter the current-artifact verdict.
