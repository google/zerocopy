# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

Snapshot: the supplied `lib.rs` exactly as inspected; scope is its complete surface (`Slot`, `Tail`, their associated items/impl, and `increment`). `REQUEST.md` supplies the only behavioral requirement. No generated artifacts, dependencies, prior audit, build tooling, or tests are used. This is a source-level Rust-abstract-semantics review.

`DOMAIN-R` is

`rustc = std = 1.82.0 ∧ target supports this exact source and the used 1.82.0 items ∧ profile is ordinary`.

The proof is parametric over every such target, profile, and Rust-1.82-supported edition in which the source compiles.

| Claim | Verdict | Certificate |
|---|---|---|
| Every well-typed safe use of the current public surface is UB-free | **UNSOUND** throughout `DOMAIN-R` | `F-UB` below gives a valid safe witness in every case. |
| `increment::<Tail>` changes `[a,b]` to `[a,b.wrapping_add(1)]` | **PROVED** throughout `DOMAIN-R` | `P-TAIL`; `Covered = DOMAIN-R`, hence `Required ⊆ Covered`. |
| Source-documented postconditions | none | No `CONTRACT-BROKEN` verdict applies. The requested Tail behavior is proved separately above. |

The redesign authorization does not narrow the current artifact's safe public contract, so the proposal below does not affect **UNSOUND**.

## Boundary, invariants, and obligations

Safe surfaces are the public safe trait `Slot`, its safe associated function `index`, downstream implementations, public unit type/constructor `Tail`, its implementation, and public safe generic function `increment`. The only unsafe site is `pair.get_unchecked_mut(S::index())`. There are no fields, unsafe traits/impls, macros, hidden items, callbacks, FFI, concurrency, custom allocation, or destruction behavior relevant to that site.

There is no enforced invariant. The needed proposition `S::index() < 2` cannot be an invariant of every `S: Slot`: `Slot` is public, safe, and unsealed, and neither its type system nor a check constrains the return value.

| ID | Exact obligation | Status |
|---|---|---|
| O-BOUNDS | At the unsafe call, `S::index()` indexes the two-element slice in bounds. | **Refuted** for the generic safe surface by `F-UB`; proved for `S=Tail`. |
| O-TAIL | On normal return for `Tail`, mutate only element 1 to its old value plus one modulo `2^32`. | **PROVED** by `P-TAIL`. |
| O-DOC | Adjacent proof must derive O-BOUNDS from enforceable facts. | **Missing**, and no truthful generic derivation exists. |

### F-UB — complete existential certificate

A downstream crate can write entirely safe code:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }

let mut pair = [0, 0];
increment::<Bad>(&mut pair);
```

`Slot` and `increment` are externally reachable public items under the Rust 1.82 [visibility rules](https://doc.rust-lang.org/1.82.0/reference/visibility-and-privacy.html#visibility-and-privacy). Because `Bad` is downstream-local, this implementation satisfies the [trait-implementation coherence/orphan rules](https://doc.rust-lang.org/1.82.0/reference/items/implementations.html#trait-implementations). `Slot` is not an [unsafe trait](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits), so neither implementation nor call accepts a safety obligation.

The call reaches `get_unchecked_mut(2)` on a slice of length 2. Its exact 1.82.0 contract says: “Calling this method with an out-of-bounds index is undefined behavior” ([`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)); it expressly applies even when the result is unused. Thus the executed unsafe operation's required proposition is false and Rust's contract entails UB. No earlier operation in the witness is unsafe. `2` and `[u32; 2]` exist in every `DOMAIN-R` case, and cfg/profile/optimization does not alter this path.

### P-TAIL — reconstructed local proof

`Tail::index()` is definitionally `1`; `[u32; 2]` has length 2, so `1 < 2`. The unsafe method therefore returns a mutable reference to element 1. There is no intervening call or escaped alias. Rust 1.82 documents `wrapping_add` as “Wrapping (modular) addition” ([`u32::wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add)). Assigning that result through the reference changes element 1 to `(old + 1) mod 2^32`; element 0 is untouched. This material derivation is absent from the source, but it proves only the Tail case and cannot repair the generic contract.

## Configuration closure and TCB

The controlling expression is exactly `DOMAIN-R`; no normalization or exclusion was added. Actual axes are target, ordinary profile, and compiling Rust-1.82 edition. There is one handwritten, unconditional path. Fixed array length, index values, the UB witness, and modular arithmetic are independent of those axes, giving parametric coverage. There are no sampled configurations or tool-derived claims.

TCB log `TCB-R016-r1` has no additional assumptions. Its accepted authoritative axioms are: `AX-GET`, the quoted Rust-1.82 `get_unchecked_mut` contract (consumer O-BOUNDS); `AX-WRAP`, the quoted Rust-1.82 modular-addition contract (O-TAIL); and `AX-TRAIT`, the linked Rust-1.82 visibility, implementation, and unsafe-trait rules (F-UB). Exact identities are the linked versioned pages; scope is `DOMAIN-R`. Re-audit on source/API changes, Rust or support-domain changes, or material changes to those pages.

## Finding and required resolution

`F-UB` is an implementation defect in the current safe generic API; severity critical. The proof artifact is also missing: there is no `SAFETY` comment. Adding prose such as “implementers return an in-bounds index” would leave a hidden safety precondition on a safe trait and would not fix the defect. A generic design would need enforcement (for example, checked indexing) or an unsafe/sealed implementer boundary. The stated requirement needs no genericity, making those larger contracts unnecessary.

## Preferred redesign

Remove `Slot`, `Tail`, the type parameter, and all unsafe code:

```rust
/// Replaces `[a, b]` with `[a, b.wrapping_add(1)]`.
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Contract: every well-typed safe call has no safety precondition beyond the parameter type; on return element 0 equals its old value and element 1 equals its old value plus one modulo `2^32`. The array type makes index 1 in bounds, safe indexing enforces bounds regardless, and `wrapping_add` supplies the exact arithmetic. There is no invariant, unsafe boundary, implementer obligation, or additional TCB premise.

Migration: `increment::<Tail>(&mut pair)` becomes `increment(&mut pair)`. The `Slot` implementation surface, generic calls, and nominal `Tail` type disappear; the request expressly authorizes those breaking changes and says the abstraction is unreleased. Tail's observable required effect is unchanged.

This sketch is **not implemented and has no audit verdict**. After implementation, freeze a new snapshot and freshly audit every remaining/reexported safe surface; verify removal of the trait, impls, and unsafe site; prove index 1 in bounds, element 0 unchanged, and the wrapping postcondition; redo `DOMAIN-R` configuration closure; and review the final documentation and migrated consumers.

## Residual scope

Binary/backend correctness, non-ordinary configurations, other Rust releases, and any source not supplied are excluded. No target was built, tested, executed, or macro-expanded.
