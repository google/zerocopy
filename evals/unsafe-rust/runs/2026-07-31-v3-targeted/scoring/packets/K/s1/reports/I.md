# Focused unsafe-Rust audit

## Claim, snapshot, and verdicts

Audited artifact: the supplied `lib.rs`, all three modules, with no generated code, dependencies, prior result, execution, or tool-derived evidence. The source-level claim is: for every well-typed safe use (and every unsafe-trait implementation satisfying its published contract), execution is free of Rust undefined behavior under Rust 1.82.0 abstract semantics. Mandatory unsafe-contract clauses are also in scope.

`Required = {exact supplied source} × {Rust and std 1.82.0} × {every target on which this source and the used 1.82.0 std items exist} × {every ordinary profile}`. The audit cutoff is 2026-08-01. There are no `cfg`s, features, macros, generators, FFI, dependencies, or enforced exclusions.

| Claim | Verdict | Certificate |
|---|---|---|
| All three modules, combined soundness | **UNSOUND** | CB-R and CB-W independently establish UB from valid safe uses. |
| `callback_index::read` | **UNSOUND** | CB-R. |
| `callback_index::write` | **UNSOUND** | CB-W. |
| `local_proof::last` implementation | **PROVED** | LP below; `Required ⊆ Covered`. |
| `local_proof::last` existing `SAFETY` comment | **Deficient** | It states no obligation or derivation. |
| `published_lane::{Lane, High, read}` | **PROVED** | PL below, for all valid `Lane` implementations; `Required ⊆ Covered`. |
| `published_lane` proof artifacts | **Deficient** | The unsafe impl and unchecked access lack adjacent proofs. |

No broader undocumented safe-API behavior (including panic freedom) is claimed. CB-R/CB-W apply on every required target/profile, so the aggregate result is not diluted by configuration uncertainty.

## Authority and TCB log R080-TCB-1

There are no additional TCB assumptions. These accepted Rust-1.82-only axioms are the complete trust boundary:

- AX-SLICE: [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked) and [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) each state that an out-of-bounds call is undefined behavior, even if the reference is unused. They return shared/mutable references without bounds checking.
- AX-LENGTH: [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) “Returns the number of elements in the slice”; [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) is true exactly when length is zero.
- AX-INTEGER: the Reference defines binary `-` as subtraction and overflow as producing a value outside the integer type's range ([operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators)); `usize` is unsigned and has pointer width ([integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types)).
- AX-TRAIT: implementing an unsafe trait may be unsafe, while using a correctly implemented one is safe ([traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits)); an unsafe impl asserts discharge of the trait's extra safety conditions ([unsafe keyword](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait)).

Each entry applies to all `Required` cases and is consumed below. Re-audit on source, contract, Rust version, support-domain, or cited-document change.

## Boundary and obligation inventory

| ID | Surface/obligation | Disposition |
|---|---|---|
| CB-P | Public safe `Position` trait and safe `position`; downstream safe implementations are adversarial. | No invariant enforces an in-bounds result. |
| CB-R | Public safe `read`; unchecked shared indexing at line 9. | **UNSOUND**. |
| CB-W | Public safe `write`; unchecked mutable indexing at line 13. | **UNSOUND**. |
| LP | Public safe `last`; nonempty branch, subtraction, unchecked indexing at lines 19–24. | Implementation **PROVED**; comment deficient. |
| PL-W | Public `Word(pub [u32; 2])`, including tuple construction/field access/move/drop. | The field's type enforces exactly two initialized `u32` lanes; no hidden invariant. |
| PL-T | Public unsafe `Lane`, constants `INDEX` and `NAME`, and unknown downstream impls. | Valid impls owe both literal clauses at lines 36–37. |
| PL-H | Safe unit construction of `High`; its unsafe `Lane` impl. | Contract **PROVED**; proof comment missing. |
| PL-R | Public safe generic `read`; unchecked indexing at line 51. | **PROVED** for every valid impl; proof comment missing. |

No other constructors, methods, callbacks, hidden items, macros, reexports, operators, or semantically relevant custom trait behavior occur in the supplied source.

## Findings and proofs

### CB-R — safe `read` reaches UB

Let safe downstream code define `struct P; impl Position for P { fn position(&self) -> usize { 0 } }` and call `read(&[], &P)`. This is well-typed and uses no unsafe operation or undocumented precondition. Line 9 executes `get_unchecked(0)` on a slice of length zero. Index 0 is out of bounds; AX-SLICE makes the call itself UB. This proves every existential link: valid in-scope use, reachability, false bounds proposition, and authoritative UB consequence.

### CB-W — safe `write` independently reaches UB

With the same safe `P`, call `write(&mut [], &P, 1)`. Line 13 executes `get_unchecked_mut(0)` on length zero. The use is valid safe Rust, index 0 is out of bounds, and AX-SLICE makes that call UB before assignment. This is a second complete certificate, not merely fallout from CB-R. No UB-free documented-postcondition refutation is needed or established.

**Smallest repair:** retain the public signatures and `Position`, but implement `read` as `bytes[position.position()]` and `write` as `bytes[position.position()] = value`. Safe callers still choose positions for reads and writes; out-of-range positions panic rather than violate a hidden safety condition. No caller-implementable abstraction was required to be preserved, but retaining it minimizes API and source change. This proposal is **not certified**: implement it, then freshly audit the new snapshot and its documented panic behavior if promised.

### LP — correct implementation, inadequate comment

On the else branch, AX-LENGTH gives `len != 0`; because `len: usize` is unsigned, `len > 0`. Therefore mathematical `len - 1` is representable, so AX-INTEGER's overflow condition is false in every overflow-check profile, and `0 ≤ index = len - 1 < len`. AX-LENGTH identifies `len` as the element count, hence `index` is in bounds. AX-SLICE discharges `get_unchecked(index)`; dereferencing the returned shared reference copies the selected valid `u8`. The empty branch performs no unsafe operation. These exhaustive branches prove soundness on `Required` and the evident result (`None` exactly for empty input; otherwise the final element).

“This is the fast path” supplies none of that material derivation. Replacement:

```rust
// SAFETY: The else branch establishes `bytes.len() > 0`, so `len - 1`
// cannot underflow and is strictly less than `bytes.len()`; `index` is in bounds.
```

### PL — current contract and unknown downstream code

The published contract is a conjunction: (1) `INDEX < 2`; (2) at index 0, `NAME == "low"`; (3) at index 1, `NAME == "high"`. `High` sets index 1 and name `"high"`, discharging all applicable clauses. For any valid downstream `L`, clause (1) and `word.0: [u32; 2]` imply `L::INDEX` is in bounds, so AX-SLICE proves line 51. `read` consumes no stronger fact. Clauses (2)–(3) remain binding even though this file does not consume `NAME`: unknown published 1.x consumers may rely on them in their own unsafe proofs. Removing/weakening the mapping can invalidate consumers; strengthening it can invalidate existing impls. Either is a compatibility change requiring downstream analysis, not a documentation cleanup.

Proposed adjacent proofs:

```rust
// SAFETY: `1 < 2`, and the contract requires `NAME == "high"` at index 1.
unsafe impl Lane for High { /* unchanged */ }

// SAFETY: Every valid `Lane` impl guarantees `L::INDEX < 2`, and `word.0`
// is `[u32; 2]`; therefore the index is in bounds.
```

These documentation proposals do not alter the current implementation verdict and remain unaudited until applied.

## Configuration closure and residual scope

The relevant axes are target pointer width, optimization, overflow checks/debug assertions, and panic strategy. The proofs are parametric: CB uses index zero on length zero; LP proves subtraction representable before profile-dependent overflow behavior matters; PL uses a type-level array length. Thus each stated positive proof covers all `Required`, and the witnesses refute soundness throughout it. No configuration was sampled or tested. Binary/compiler-correctness, security, and any source outside the two supplied target files are excluded.

Final attestation: every supplied surface and unsafe obligation has a disposition; all citations were checked at Rust 1.82.0; no result relies on testing, a missing counterexample, hidden caller obligations, repository-visible consumer completeness, or a proposed repair.
