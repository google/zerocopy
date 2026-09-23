# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

Audited artifact: the supplied `lib.rs`, exactly as inspected; no expansion,
execution, tests, dependencies, generated artifacts, features, or prior audit
were used. Scope is Rust and standard library 1.82.0, every target on which this
source and its used standard-library items exist, and every ordinary profile.

Let `D` be exactly that configuration predicate. Valid use of each safe public
API means every well-typed safe use, including caller-chosen implementations of
the safe `Slot` trait. The source-level claims are:

| Claim | Verdict | Certificate |
|---|---|---|
| Every safe use of the exposed API is free of Rust UB over `D`. | **UNSOUND** | `F-1` gives a valid safe use, reaches the unsafe operation, falsifies its bounds precondition, and reaches the documented UB consequence. |
| For every `pair`, `increment::<Tail>` changes element 1 to its prior value plus 1 modulo `2^32` and leaves element 0 unchanged, over `D`. | **PROVED** | `P-TAIL` below; `D ⊆ CoveredTail = D`. |

The overall current-artifact soundness verdict is **UNSOUND**. The redesign
proposal below does not qualify or alter it. There is no separate
`CONTRACT-BROKEN` finding: the requested `Tail` behavior holds, and the source
contains no other documented postcondition.

## Boundary and inventory

The complete relevant public surface is: safe trait `Slot`; its safe required
associated function `index`; the public unit struct/constructor `Tail`; its safe
`Slot` implementation; and safe generic free function `increment`. A downstream
crate may implement `Slot` without `unsafe`. There are no unsafe public APIs,
fields, hidden items, macros, callbacks, FFI, dependencies, or persistent
representation invariants. `increment` contains the sole unsafe operation,
`get_unchecked_mut(S::index())`, with no adjacent `SAFETY` proof.

The only local invariant-like fact is `ARRAY-2`: the borrowed array has exactly
two elements, hence valid scalar indices are `0` and `1`. `Tail::index()`
locally establishes `INDEX-TAIL = 1`. No type or boundary establishes
`S::index() < 2` for arbitrary `S: Slot`.

## Obligations and proofs

The Rust 1.82 slice contract says that `get_unchecked_mut` returns a mutable
reference without bounds checking and that calling it with an out-of-bounds
index is UB, even if the reference is unused
([slice documentation](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)).
Thus obligation `O-BOUNDS` is `S::index() < 2` at the call for every safe
instantiation. The Rust 1.82 integer contract says `wrapping_add` performs
modular addition, wrapping at the type boundary
([u32 documentation](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)).

**F-1 — open safe trait makes `increment` unsound.** A downstream safe program
may write:

```rust
struct Outside;
impl Slot for Outside { fn index() -> usize { 2 } }
let mut pair = [0u32, 0u32];
increment::<Outside>(&mut pair);
```

This uses no unsafe caller operation and violates no documented or
compiler-enforced caller obligation. Dynamic dispatch is not involved:
`Outside::index()` returns `2`, so the safe call reaches
`pair.get_unchecked_mut(2)`. By `ARRAY-2`, `2` is out of bounds. The cited
contract makes the call itself UB. The witness is parametric over `D`: the
literal `2`, array length, trait implementation, and callee selection are
profile- and target-independent wherever the source/items exist. This closes
every link of the `UNSOUND` certificate. The missing safety comment is also a
proof-artifact defect, but documentation cannot repair this safe boundary.

**P-TAIL — requested behavior.** For `S = Tail`, inspected code gives
`S::index() = 1`; `ARRAY-2` gives `1 < 2`, discharging `O-BOUNDS`. The cited
slice contract therefore identifies the returned mutable reference with
element 1. If its old value is `x`, the cited integer contract gives
`x.wrapping_add(1) = (x + 1) mod 2^32`; assignment stores that result through
the element-1 reference. No operation targets element 0. This one parametric
case applies to every input and every configuration in `D`, including overflow
and all ordinary profile settings.

## Domain closure and TCB log

`Required = D` comes verbatim from the request; no range normalization,
enumeration, exclusion, or moving policy is used. Actual axes are target and
ordinary profile. There is one handwritten implementation with no `cfg`; both
proofs above are parametric over those axes. Therefore the unsound witness and
`P-TAIL` each cover all of `D`. Audit cutoff is 2026-08-01 and only freezes the
inspected source and fixed-version documentation.

TCB `TCB-1` contains only two verified authoritative Rust 1.82 axioms: (A1) the
quoted `get_unchecked_mut` contract, consumed by `F-1` and `P-TAIL`; and (A2) the
quoted `wrapping_add` contract, consumed by `P-TAIL`. Both apply over `D` by its
definition. No additional assumptions, safe/unsafe dependencies, compiler
implementation claims, tools, external specifications, or deployment premises
are admitted.

## Preferred redesign

Replace the generic abstraction with one concrete safe operation:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its contract is: for every input array, normal return leaves element 0 equal to
its entry value and sets element 1 to its entry value plus 1 modulo `2^32`; it
has no caller safety precondition. The fixed array type and safe indexing
enforce selection of the required element, and `wrapping_add` supplies the
arithmetic. There is no unsafe block, implementer contract, or representation
invariant. `Slot` and `Tail` should be removed because nominal slot identity and
extensibility supply no required capability.

Migration changes `increment::<Tail>(&mut pair)` to `increment(&mut pair)` and
removes all `Slot` implementations and generic uses. This is an authorized
source/API break: the request says the abstraction is unreleased and those
surfaces need not be preserved. The required observable `Tail` behavior is
unchanged.

This is a design, not an implemented-artifact verdict. After implementation,
fresh review must inspect the exact new snapshot; enumerate its complete public
surface; prove safe index `1` is in bounds for `[u32; 2]`; prove the modular
write and preservation of element 0 for every input; re-establish `D ⊆
Covered`; and check that no conditional/generated alternative or remaining
unsafe/generic surface exists. Re-audit is also required for any source,
contract, Rust version, support-domain, or relevant standard-library contract
change.
