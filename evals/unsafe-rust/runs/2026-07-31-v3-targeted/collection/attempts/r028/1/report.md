# Focused unsafe-Rust audit and redesign

## Claim, snapshot, and verdicts

**Snapshot and scope.** This is a source-only review of the complete supplied `lib.rs`, lines 1–18. The supported predicate is exactly Rust/standard library 1.82.0, every target on which this source and the used standard-library items exist, and every ordinary profile. There are no dependencies, `cfg` branches, features, generated artifacts, macros, FFI, allocation, concurrency, or build inputs in the supplied artifact. The proof is parametric over target and profile: array length `2`, values `1` and `2`, safe-trait openness, and the cited library contracts do not vary across that set. Audit date: 2026-08-01.

**Soundness theorem.** Every well-typed safe use of the public surfaces is free from Rust undefined behavior under Rust 1.82.0 abstract semantics. **Verdict: UNSOUND** (`F-1`) over the entire supported predicate. The safe generic API admits an out-of-bounds unchecked access.

**Requested Tail behavior.** For every initial `pair == [a, b]`, `increment::<Tail>(&mut pair)` returns with `pair == [a, b.wrapping_add(1)]`. **Verdict: PROVED** (`O-2`) over the entire supported predicate. This regional behavioral result does not qualify the soundness verdict. The source documents no caller-facing postcondition, so there is no separate source-documented postcondition to classify as `CONTRACT-BROKEN`.

**Combined current-artifact result: UNSOUND.** No proposal below participates in this verdict.

## Boundary and obligation coverage

The complete public surface is: safe, downstream-implementable trait `Slot` and safe associated function `Slot::index` (lines 3–5); publicly constructible unit struct `Tail` (line 7); its safe `Slot` implementation (lines 9–13); and safe generic function `increment<S: Slot>` (lines 15–18). The sole unsafe operation is the internal `get_unchecked_mut` call at line 16. There are no fields, unsafe declarations/impls, hidden APIs, callbacks, custom `Drop`, or generated surfaces. Ordinary compiler-provided moves, destruction, and auto traits carry no state and do not affect the finding.

| ID | Exact obligation and derivation | Status |
|---|---|---|
| O-1 | A safe call to `increment::<S>` must establish `S::index() < 2` before line 16 for every safe `S: Slot`. The trait type/signature and source perform no check and enforce no such behavior. | **False; UNSOUND (F-1)** |
| O-2 | For `S = Tail`, line 11 yields `1`; a `[u32; 2]` has indices `0,1`, so the unchecked call is in bounds and selects element 1. `wrapping_add(1)` computes its modular successor, which line 17 stores through that exclusive reference. Only element 1 is targeted. | **PROVED** |
| O-3 | The unsafe block needs an adjacent proof of O-1. It has no `SAFETY` comment, and no truthful proof exists for its generic domain. The O-2 reconstruction validates only the Tail specialization and cannot retroactively narrow the safe API. | **Proof artifact deficient; implementation globally UNSOUND** |
| O-4 | Configuration closure: F-1 uses index `2`, representable on every supported target, against an array of invariant length `2`; O-2 uses index `1`. No profile-dependent assertion, overflow operation, or code selection occurs. | **Complete** |

There is no enforceable representation invariant. The needed proposition “all `Slot` implementations return an index below 2” has no owner or sealing boundary and is disproved by F-1.

## TCB audit log `TCB-R028-r1`

Policy: only exact Rust 1.82.0 Reference/standard-library axioms may be consumed; no additional assumptions, dependencies, tools, tests, implementation behavior, or compatibility premise is admitted.

* **AXIOM-SLICE-1 (accepted):** for Rust 1.82.0 on the supported set, `slice::get_unchecked_mut` returns the indexed mutable reference without bounds checking, and: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” [Rust 1.82.0 `get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut). Consumers: O-1, O-2, F-1. Recheck if the Rust version or contract changes.
* **AXIOM-U32-1 (accepted):** for Rust 1.82.0 on the supported set, `u32::wrapping_add` is “Wrapping (modular) addition” and wraps at the type boundary. [Rust 1.82.0 `wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add). Consumer: O-2 and the proposed contract. Recheck if the Rust version or contract changes.

No tool-derived evidence or sampled execution was used. Both citations were opened at the exact version. No premise is pending or rejected.

## F-1 — safe implementer controls an unchecked index

**Classification:** implementation `UNSOUND`; proof artifact missing. `Slot` is a public safe trait, so well-typed safe downstream code may implement it with any `usize` result:

```rust
struct Bad;
impl Slot for Bad { fn index() -> usize { 2 } }
let mut pair = [0, 0];
increment::<Bad>(&mut pair);
```

This is a valid safe use. `Bad::index()` returns `2`; for length 2 that is out of bounds. AXIOM-SLICE-1 therefore makes the call at line 16 UB immediately, independently of later dereference. This witness applies to every supported target and profile. No UB-free postcondition refutation is claimed from this execution. Minimum resolution is to remove the unchecked generic access, validate the index before unsafe use, or enforce implementer behavior at an actual unsafe/sealed boundary. Given the stated requirement, specialization is smaller and removes the premise entirely.

## Preferred redesign (not implemented; no fresh verdict)

Use one monomorphic safe function and delete `Slot` and `Tail`:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Its proposed contract is: no caller safety precondition; for every `[a,b]`, normal return produces `[a, b.wrapping_add(1)]`. The fixed array type and safe constant indexing enforce access to element 1; AXIOM-U32-1 supplies the arithmetic postcondition. There is no unsafe surface, implementer obligation, representation, or abstraction invariant. Making `Slot` unsafe, sealing it, or retaining a checked generic index would preserve genericity that no required consumer needs.

**Migration/contract delta.** Remove the public trait, its downstream implementation capability, `Tail`, and the type parameter. Replace `increment::<Tail>(&mut pair)` with `increment(&mut pair)`. Generic calls and downstream `Slot` implementations intentionally cease to compile, as authorized for this unreleased abstraction. The required Tail-observable mutation is unchanged; the new explicit function contract strengthens the previously undocumented behavioral surface.

After implementation, audit the new snapshot independently: enumerate its actual public surface; verify constant array indexing and wrapping semantics for Rust 1.82.0; prove the complete mutation/postcondition and panic behavior for every input; re-establish target/profile closure; and confirm that no conditional/generated code or unsafe operation was introduced. Source, public-contract, supported-set, or cited Rust-contract changes trigger re-audit. Nothing outside the supplied file was audited.
