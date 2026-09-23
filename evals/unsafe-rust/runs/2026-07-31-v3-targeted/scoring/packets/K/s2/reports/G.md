# Focused unsafe-Rust audit

## Claim, snapshot, and verdict

Snapshot: exactly the supplied `lib.rs`. Scope is all three modules, Rust and standard library 1.82.0, every target on which this source and its used standard-library items exist, and every ordinary profile. There are no features, `cfg`s, dependencies, generated artifacts, FFI, concurrency, or build-time inputs in the supplied source.

Claim: every well-typed safe use of each safe surface is free of Rust undefined behavior; uses of the unsafe `Lane` implementer boundary must satisfy its complete published contract. The result is relative only to the Rust 1.82.0 axioms recorded below; there are no additional TCB assumptions.

**Combined soundness verdict: UNSOUND.** `callback_index::read` and `write` each admit an independent, wholly safe call that reaches UB. Review continued through the remaining modules: `local_proof::last` is **PROVED** sound, and `published_lane` (including `High` and generic `read`) is **PROVED** sound under the literal current `Lane` contract. Their local proof documentation is deficient. There are no documented unsafe-function postconditions. Conformance of `High` to both published trait clauses is **PROVED**.

## Boundary and obligation inventory

| ID | Surface or proof site | Result |
|---|---|---|
| CB-P | safe, downstream-implementable `Position` and safe `position` | unconstrained `usize` producer |
| CB-R | safe `callback_index::read`; `get_unchecked` consumer | **UNSOUND** |
| CB-W | safe `callback_index::write`; `get_unchecked_mut` consumer | **UNSOUND** |
| LP | safe `local_proof::last`; unchecked shared access | implementation **PROVED**; comment deficient |
| PL-W | public `Word(pub [u32; 2])`, including tuple construction/field access | **PROVED**; array length is type-enforced |
| PL-L | public unsafe `Lane`, associated constants, downstream unsafe impl boundary | literal two-clause contract reviewed |
| PL-H | safe `High` construction and `unsafe impl Lane for High` | implementation **PROVED**; proof comment missing |
| PL-R | safe generic `published_lane::read`; unchecked shared access | implementation **PROVED**; proof comment missing |

There is no representation invariant beyond the types. The relevant local contracts are `CB-IN-BOUNDS` (an unchecked index must be in bounds) and `LANE-1X` (`INDEX < 2`, plus the stated `NAME`/`INDEX` correspondence).

## Rust 1.82.0 axioms / TCB log

All entries were opened at the exact versioned URLs and are accepted only for the requested domain.

- **A-SHARED:** [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked): “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” Consumer: CB-R, LP, PL-R.
- **A-MUT:** [`slice::get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) states the same requirement for mutable access. Consumer: CB-W.
- **A-SLICE:** [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) “Returns the number of elements in the slice”; [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) returns true when that length is zero. Consumer: LP.
- **A-ARITH:** The Reference classifies `usize` as an [unsigned integer type](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types), and `-` on integers as [subtraction](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators). Consumer: LP.
- **A-TRAIT:** An unsafe trait has extra conditions that implementations must uphold, and an `unsafe impl` asserts their discharge ([unsafe-trait explanation](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait)); it is safe to use a correctly implemented unsafe trait ([trait rule](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits)). Consumer: PL-H, PL-R.

No tools, tests, executions, or sampled evidence were used.

## Findings and proofs

### F-CB-R — safe read reaches UB

`Position` has no safety contract or enforced range. Safe downstream code can implement `position` to return `0`, then call `read(&[], &p)`. The index is out of bounds for the empty slice, yet `read` passes it to `get_unchecked`. A-SHARED therefore proves UB. No unsafe caller action or additional premise occurs. This refutes soundness on every requested target/profile.

### F-CB-W — safe write independently reaches UB

The analogous safe call `write(&mut [], &p, 1)` passes `0` to `get_unchecked_mut`. A-MUT proves UB. This is a separate defect and witness from F-CB-R. Neither UB-containing execution is used as a postcondition refutation.

**Smallest repair:** retain the signatures and caller-implementable trait, but replace the bodies with checked indexing:

```rust
bytes[position.position()]
bytes[position.position()] = value;
```

This preserves safe callers' ability to select positions for both reads and writes; an invalid position panics rather than becoming a hidden safety precondition. It requires neither sealing nor making `Position` unsafe. Replacing `Position` with a `usize` parameter is an optional larger API simplification, not needed for the minimal repair. **The proposal is not implemented and is not certified; audit the exact changed snapshot anew.**

### F-LP-DOC — correct implementation, inadequate `SAFETY` comment

Implementation proof: the unsafe path is reached only when `is_empty()` is false. By A-SLICE, `len != 0`; because `len: usize` is unsigned, `len >= 1`. A-ARITH then makes `index = len - 1` representable, with `0 <= index < len`. Thus `index` is in bounds and A-SHARED's sole safety requirement is met. Dereferencing the resulting shared reference copies its valid `u8`. The empty path performs neither subtraction nor unsafe access. This argument is parametric over target and profile; overflow checking is irrelevant because subtraction cannot underflow.

“This is the fast path” states none of the obligation, dominating fact, or derivation. Replace it with:

```rust
// SAFETY: This branch establishes bytes.len() != 0. Therefore
// index = bytes.len() - 1 is in 0..bytes.len(), as get_unchecked requires.
```

The current implementation verdict remains **PROVED**; the current proof artifact is deficient.

### F-PL-PROOF — sound implementation, missing adjacent proofs

`High` discharges every literal `LANE-1X` clause: `1 < 2`; the `INDEX == 1` implication requires `NAME == "high"`, which holds; the `INDEX == 0` antecedent is false. Suggested adjacent impl proof:

```rust
// SAFETY: INDEX is 1 (< 2), NAME is "high" as required for INDEX == 1,
// and the INDEX == 0 clause is inapplicable.
```

For every valid `L: Lane`, the published first clause gives `L::INDEX < 2`. `word.0` is exactly `[u32; 2]`, so that index is in bounds and A-SHARED is satisfied. Suggested `read` proof:

```rust
// SAFETY: Lane requires L::INDEX < 2, and word.0 has exactly two elements.
```

A bad downstream `unsafe impl` is outside valid use because A-TRAIT assigns it the published obligations; no hidden condition is imposed on safe callers. The current implementations are **PROVED**, while both adjacent proof artifacts are missing.

`NAME` is not consumed by this file's `read`, but remains a published 1.x implementer guarantee. Unknown downstream consumers may rely on it, including in soundness proofs. Removing or weakening it can invalidate consumers; strengthening either clause can invalidate existing implementations. Repository-visible uses cannot justify either change. Any evolution needs the applicable compatibility process and a fresh audit; this review certifies no proposed contract change.

## Configuration closure, residual scope, and triggers

Coverage is parametric: the callback witnesses use only an empty slice and index zero; LP derives a mathematical in-bounds index before profile-sensitive overflow behavior can differ; PL uses a fixed two-element array and the contract's strict bound. Hence target widths and ordinary profiles do not change any result. There are no generated/configuration branches to enumerate and no excluded requested cases.

Residual scope is limited to implementations and consumers not supplied here: they are not individually audited, but PL-R quantifies over every implementation satisfying the published unsafe contract. Re-audit on any source or safety-contract change, Rust/standard-library version change, support-domain expansion, or implementation of either proposed documentation/code repair.
