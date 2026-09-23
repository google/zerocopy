# Focused literal audit and redesign

## Claim, scope, and verdict

**Snapshot:** the supplied `lib.rs`, reviewed as source without execution or expansion. **Supported set:** Rust 1.82.0; every Rust 1.82 edition, target on which this source and the used standard-library items exist, and ordinary profile. The proof is parametric over target, edition, and profile: the file has no `cfg`, features, generated code, dependencies, FFI, concurrency, target features, allocation, panic-mode-sensitive checks, or profile-sensitive arithmetic.

The current-artifact claim is that every well-typed safe use of its public safe surfaces is free of Rust undefined behavior. The separately requested behavior is: for input `[a, b]`, `increment::<Tail>` returns normally with `[a, b.wrapping_add(1)]`.

- **Current safe-API soundness: UNSOUND** (`F-1`).
- **Required `Tail` behavior: PROVED** throughout the supported set, relative only to the cited Rust 1.82 standard-library semantics.
- **Documented-postcondition result:** the source contains no API documentation. The user-specified `Tail` postcondition is proved; there is no current documented postcondition to classify as `CONTRACT-BROKEN`.
- **Combined current-artifact result: UNSOUND.** The successful `Tail` proof does not qualify the public generic function's universal safe-use claim.
- **Additional TCB assumptions:** none. No dependency, implementation, environmental, compatibility, or tool-result premise is admitted.

## Authority and exact contracts

`AXIOM-INDEX`, Rust 1.82 slice documentation: `get_unchecked_mut` returns a mutable reference without bounds checking, and “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” [Rust 1.82 `get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut).

`AXIOM-WRAP`, Rust 1.82 `u32` documentation: `wrapping_add` is “Wrapping (modular) addition” and wraps at the type boundary. [Rust 1.82 `wrapping_add`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#method.wrapping_add).

These are version-matched Rust axioms, not additional TCB assumptions. No tool-derived evidence was used.

## Boundary and obligation coverage

The complete language-reachable source surface is:

| Surface | Kind | Disposition |
|---|---|---|
| `Slot` and safe `Slot::index` (`lib.rs:3-5`) | public safe, downstream-implementable trait | Supplies an arbitrary `usize`; no contract or enforcement makes it less than 2. |
| `Tail`, its public unit constructor, and `impl Slot` (`lib.rs:7-13`) | public safe type/implementation | `Tail::index()` is locally fixed at 1. No fields or state invariants exist. |
| `increment<S: Slot>` (`lib.rs:15-18`) | public safe generic function containing the sole unsafe operation | Unsound for arbitrary valid `S`; proved for `S = Tail`. |

There are no manual trait implementations other than `Slot for Tail`, macros, hidden APIs, restricted-visible fields, reexports, callbacks, custom destruction, or configuration-specific surfaces in the supplied source. Compiler-provided behavior of the fieldless `Tail` is irrelevant to the unsafe call.

The sole safety invariant consumed at `lib.rs:16` is `INV-BOUND: S::index() < pair.len() = 2` at the instant `get_unchecked_mut` is called. The array-reference type fixes the length at 2. `Tail::index()` establishes `1`, so `INV-BOUND` holds for `Tail`. The public safe trait boundary neither checks nor promises it for arbitrary `S`.

Obligation ledger:

| ID | Proposition | Status |
|---|---|---|
| `OBL-1` | At `lib.rs:16`, `S::index() < 2` for every safe-callable `S`. | **Refuted** by `F-1`; hence **UNSOUND**. |
| `OBL-2` | For `S = Tail`, the unchecked access produces a mutable reference to element 1. | **PROVED:** local constant 1 is in the type-fixed length 2; `AXIOM-INDEX` supplies the operation contract. |
| `OBL-3` | The `Tail` call leaves element 0 unchanged and replaces element 1 by its old value plus 1 modulo `2^32`. | **PROVED:** `OBL-2` identifies the only assignment target; `AXIOM-WRAP` gives the assigned value. |

No existing `SAFETY` comment states any of these obligations. The reconstructed `Tail` derivation is material, but it cannot repair the generic case.

## F-1 — safe downstream implementation reaches UB

**Status:** `UNSOUND`; implementation defective and local proof missing.

This is a valid, entirely safe downstream use:

```rust
struct Bad;
impl Slot for Bad {
    fn index() -> usize { 2 }
}

let mut pair = [0u32, 0u32];
increment::<Bad>(&mut pair);
```

The public trait is safe and unsealed, its method has no precondition, and the downstream type is local to its implementing crate. The call therefore satisfies every current caller obligation. It passes index 2 to a length-2 array. By `AXIOM-INDEX`, the call at `lib.rs:16` itself has undefined behavior, whether or not the returned reference is later used. This witness and reasoning are independent of target and profile.

The smallest false implication is `S: Slot => S::index() < 2`. Neither the type system, validation, privacy, nor a trait contract supplies it. A comment cannot impose a safety precondition on this safe trait or safe function. Because the witness execution contains UB, it does not establish a defined postcondition refutation.

## Preferred design

Delete `Slot`, `Tail`, the type parameter, and the unsafe operation. Expose exactly the required capability:

```rust
/// Increments the second element modulo 2^32.
pub fn increment(pair: &mut [u32; 2]) {
    let [_, tail] = pair;
    *tail = tail.wrapping_add(1);
}
```

This is the most parsimonious boundary because no runtime-selected slot or nominal marker is required. The two-element pattern structurally obtains the second element; no index validity proposition is delegated to a caller or implementer. All operations are safe, and `AXIOM-WRAP` directly supplies the behavioral postcondition. There is no representation invariant, unsafe surface, sealing argument, or additional TCB entry.

**Contract and migration delta:** `increment::<Tail>(&mut pair)` becomes `increment(&mut pair)`. `Slot`, downstream implementations, generic dispatch, and the `Tail` marker disappear. Those are source-breaking changes, expressly authorized because the abstraction is unreleased and none of those capabilities must be preserved. The new public contract should state normal return with element 0 unchanged and element 1 incremented modulo `2^32`.

This is a proposal, not a verdict for an unimplemented artifact. After implementation, audit the fresh source snapshot: confirm the exact public surface and documentation; re-prove element selection and modular arithmetic on Rust 1.82.0 across the requested target/edition/profile set; and recheck any newly introduced configuration, generated code, dependency, or caller surface. Re-audit on source, contract, supported-set, or relevant Rust-documentation change.
