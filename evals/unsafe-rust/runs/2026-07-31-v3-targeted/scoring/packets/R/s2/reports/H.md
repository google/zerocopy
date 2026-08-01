# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

Audited artifact: the exact supplied `lib.rs`, lines 1–18. `REQUEST.md` is the controlling scope. No generated code, dependencies, features, `cfg`, FFI, allocator, concurrency, or build-time inputs appear in the artifact.

Let `Required` be: Rust and standard library 1.82.0, every target on which this exact source and the two used standard-library items exist, and every ordinary profile. The source is identical over that domain; target and profile do not affect the array length, either index value below, or the selected methods. The audit cutoff is this supplied snapshot. TCB-R1 contains only the two verified Rust 1.82.0 standard-library axioms below; it admits no additional assumptions, dependency implementations, tools, compiler backend, or environment.

| Claim | Verdict | Certificate |
|---|---|---|
| Every well-typed safe use of the public API is free of Rust UB over `Required` | **UNSOUND** | U1 below |
| For every input `[a, b]`, `increment::<Tail>` returns with `[a, b.wrapping_add(1)]` | **PROVED** | OBL-2–3; `Covered_tail = Required`, hence `Required ⊆ Covered_tail` |

There are no source-documented unsafe-API postconditions. The second claim is the user-required behavior, not a repair or narrowing of the first claim. The combined current-artifact result is **UNSOUND**.

## Authority and TCB-R1

- **AXIOM-SLICE-1 (accepted):** Rust 1.82.0 documents that `get_unchecked_mut` returns a mutable reference to the indexed element or subslice without bounds checking, and: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” [Rust 1.82.0 slice documentation](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut). Applies to every `Required` case where that item exists; consumed by U1 and P2.
- **AXIOM-U32-1 (accepted):** `wrapping_add` performs “Wrapping (modular) addition” and wraps at the type boundary. [Rust 1.82.0 `u32` documentation](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add). Applies throughout `Required`; consumed by P3.

Re-audit these entries if Rust/stdlib version or either cited contract changes. This is a source-level result relative to documented Rust semantics, not a binary/backend claim.

## Boundary and obligation coverage

| ID | Safe surface / proof site | Disposition |
|---|---|---|
| API-1 | Public safe trait `Slot` and safe required method `index() -> usize` (lines 3–5) | Downstream safe code may implement it and return any `usize`; no contract or type restriction enforces bounds. |
| API-2 | Public constructible unit struct `Tail` and its safe `Slot` impl (lines 7–13) | `index()` is locally fixed to `1`. |
| API-3 | Public safe generic `increment<S: Slot>` (lines 15–18) | Must be sound for every well-typed safe `S`; it invokes caller-controlled safe code, then consumes its result in unsafe code. |
| OBL-1 | `get_unchecked_mut(S::index())` (line 16) | For the `usize` index, the required proposition is `S::index() < pair.len() = 2`. **False in a valid safe use; U1.** |
| OBL-2 | `increment::<Tail>` at line 16 | **Proved:** `Tail::index() = 1`, and `1 < 2`; AXIOM-SLICE-1 therefore supplies a mutable reference to element 1. |
| OBL-3 | Assignment at line 17 | **Proved for `Tail`:** the only write is through that element-1 reference; AXIOM-U32-1 gives the new value `b + 1 mod 2^32`, while element 0 is untouched. |

There are no fields, other constructors, methods, macros, hidden items, reexports, callbacks other than the trait implementation dispatch, or invariant-bearing state in the supplied source. No tool-derived evidence was used.

## U1 — complete UB certificate

A downstream crate can write entirely safe Rust:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0u32, 0u32];
increment::<Bad>(&mut pair);
```

This is a valid in-scope use: `Slot` is safe and public, `Bad` is downstream-owned, and `increment` is safe. Dispatch reaches line 16 with index `2`. The borrowed array has exactly two elements, so valid indices are `0` and `1`; `2` is out of bounds. AXIOM-SLICE-1 makes the call itself UB, independently of later dereference. The witness is parametric over every `Required` target/profile because the same source path and constants apply. Thus the universal safe-API claim is **UNSOUND**, not merely unproved.

The unsafe block also has no adjacent `SAFETY` proof. More importantly, no truthful proof comment can close OBL-1: the needed implication `S: Slot => S::index() < 2` is unenforced and refuted above. Behavioral prose on a safe trait would not fix that.

## Preferred redesign (not a verdict on implemented code)

Remove `Slot`, `Tail`, the type parameter, and the unsafe operation. Specialize the sole required capability:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Proposed safe contract: for every input whose old value is `[a, b]`, normal return produces `[a, b + 1 mod 2^32]`; callers have no safety precondition beyond supplying the typed mutable reference. Fixed safe indexing enforces the only projection needed. There is no representation invariant, implementer obligation, generic capability, or unsafe surface to trust. This is more parsimonious than sealing or making `Slot` unsafe because no required consumer needs generic selection.

Migration is intentionally breaking but authorized for this unreleased abstraction: delete downstream `Slot` implementations and change `increment::<Tail>(&mut pair)` to `increment(&mut pair)`. Generic calls cease to exist; the required element-1 behavior and wrapping arithmetic remain.

The proposal is unimplemented and has no audit verdict. After implementation, audit the new exact snapshot independently: verify its public contract, safe indexing of `1` into `[u32; 2]`, the wrapping result and preservation of element 0, panic/profile independence, configuration closure, and absence of generated or alternate paths. Re-audit on source/API changes, support-domain expansion, or relevant Rust documentation changes.
