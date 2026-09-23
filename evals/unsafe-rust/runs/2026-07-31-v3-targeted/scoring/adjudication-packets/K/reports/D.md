# Focused unsafe-Rust source audit

## Claim, domain, and result

Snapshot: the complete supplied `lib.rs`; no generated code, dependencies, `cfg`, macros, FFI, or build inputs are present. `Required` is exactly Rust/stdlib 1.82.0 × every target on which this source and the used 1.82.0 std items exist × every ordinary profile. The claim quantifies over every well-typed safe call, in a context satisfying any independently introduced unsafe-code obligations (notably, downstream `unsafe impl Lane`). It is a source-level claim under documented Rust abstract semantics, not a compiler-binary claim.

| Scope | Soundness verdict | Proof-artifact verdict |
|---|---|---|
| `callback_index::read` | **UNSOUND** (CB-R) | missing and incapable of proving the current code |
| `callback_index::write` | **UNSOUND** (CB-W) | missing and incapable of proving the current code |
| `local_proof::last` | **PROVED** | **deficient**; material proof reconstructed below |
| `published_lane` (`Word`, `Lane`, `High`, `read`) | **PROVED** | trait contract adequate; `High` and `read` local proofs missing |
| All three modules, aggregate | **UNSOUND** | CB-R and CB-W |

There are no explicit function postconditions to certify. The two normative clauses of `Lane`'s published safety contract are separately discharged for the in-scope `High` implementation. No UB-free documented-postcondition counterexample was established, so `CONTRACT-BROKEN` is not claimed.

## Authoritative premises (TCB-1)

No additional TCB assumptions are admitted. The only ground premises are these verified Rust 1.82 authorities:

- AX-SLICE: [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked) and [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut) require the index to be in bounds; “Calling this method with an out-of-bounds index is undefined behavior.” They return a reference to the selected element when their contract holds.
- AX-LEN: [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len) “Returns the number of elements in the slice”; [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty) is true exactly when length is zero.
- AX-INT: [`usize` is an unsigned integer type](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types); the [binary-operator rules](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators) govern subtraction and overflow. The proofs below perform subtraction only from a positive value.
- AX-TRAIT: Rust requires an unsafe implementation for an unsafe trait and assigns such implementations extra safety invariants: [trait rules](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits), [`unsafe` trait rules](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait).

These axioms apply exactly to 1.82.0 across `Required`; there is no cross-version compatibility premise.

## Boundary and obligation inventory

| Surface/obligation | Disposition |
|---|---|
| safe, downstream-implementable `Position` and safe `position()` | An implementation may return any `usize`; no bounds invariant exists. |
| safe `callback_index::{read, write}` | Each passes that adversarial result to an unchecked operation; false obligation, CB-R/CB-W. |
| safe `local_proof::last` | All inputs covered by the empty/nonempty branch proof LP. |
| public `Word(pub [u32; 2])` and its tuple constructor | Safe construction cannot alter the type-enforced length of two; no stronger invariant is needed. |
| public unsafe `Lane`, `INDEX`, and `NAME` | Valid implementations promise `INDEX < 2` and the exact index/name mapping. Both clauses remain live published obligations. |
| public unit `High` constructor and `unsafe impl Lane for High` | `INDEX = 1 < 2`; because it is 1, `NAME = "high"` meets the second clause. |
| safe `published_lane::read<L: Lane>` | PL proves its unchecked access for every valid implementation, including unknown downstream ones. |

There are no other constructors, methods, fields, callbacks, hidden items, reexports, generated APIs, or configuration-specific surfaces in the supplied source.

## CB-R and CB-W — complete UB certificates

Define, entirely in safe caller code, `struct Bad; impl Position for Bad { fn position(&self) -> usize { 1 } }`.

- **CB-R valid use:** `read(&[0u8], &Bad)` is well typed and invokes only safe APIs. No caller safety precondition exists.
- **CB-R reachability/falsity/consequence:** `position()` returns 1; the slice length is 1, so index 1 is out of bounds. `get_unchecked(1)` executes. AX-SLICE classifies that call as UB.
- **CB-W valid use:** with `let mut a = [0u8];`, `write(&mut a, &Bad, 7)` is likewise a well-typed safe call.
- **CB-W reachability/falsity/consequence:** `get_unchecked_mut(1)` executes on length 1; the required in-bounds proposition is false, and AX-SLICE classifies the call as UB.

The witnesses use values available on every `Required` target and do not depend on optimization, overflow checks, or panic strategy. Thus both scoped universal safe-API claims are refuted throughout `Required`; one witness would also suffice for the aggregate `UNSOUND` result.

### Smallest required repair (proposal only)

Delete `Position` and replace the functions with:

```rust
pub fn read(bytes: &[u8], position: usize) -> u8 {
    bytes[position]
}

pub fn write(bytes: &mut [u8], position: usize, value: u8) {
    bytes[position] = value;
}
```

This retains caller-chosen positions and callable read/write operations, removes the caller-implementable behavioral boundary and all unsafe operations, and gives out-of-range inputs the safe indexing behavior. Removing the public trait and changing parameter types is a source/API compatibility break; migrate callers from `&P` to a `usize`. This candidate is **not certified**: implement it as a new snapshot and freshly audit its exact behavior and full domain.

## LP — implementation proof and proof-documentation defect

On the `None` branch no unsafe operation executes. On the other branch, AX-LEN gives `n = bytes.len() != 0`. Since `n: usize` is unsigned, `n >= 1`; therefore `n - 1` neither underflows nor varies by overflow-check profile, and `0 <= n - 1 < n`. Hence `index` is in bounds, satisfying AX-SLICE. The returned shared reference designates the last initialized `u8`; copying it into `Some` adds no aliasing or lifetime obligation. This proof is parametric over `usize` width and every target/profile in `Required`.

The existing comment, “This is the fast path,” identifies neither the operation nor any precondition or fact. Replace it with:

```rust
// SAFETY: `is_empty()` was false on this branch, so `bytes.len() != 0`.
// Thus `bytes.len() >= 1`, subtraction cannot underflow, and
// `index = bytes.len() - 1 < bytes.len()`. `index` is therefore in bounds,
// as required by `slice::get_unchecked`.
```

## PL — unsafe-trait proof and published-contract constraints

For any valid `L: Lane`, the published unsafe contract supplies `L::INDEX < 2`. `Word.0` has type `[u32; 2]`, hence that index is in bounds and AX-SLICE discharges `read`'s unchecked access. `NAME` is not consumed locally, but it is not ignored: `High` satisfies it syntactically, and every valid downstream implementation owes it. An incorrect downstream `unsafe impl` is a violation of an out-of-scope unsafe obligation, not a valid-use counterexample to this safe generic API.

Add these local proofs:

```rust
// SAFETY: `INDEX` is 1, hence less than 2, and for index 1 `NAME` is "high".
unsafe impl Lane for High { /* unchanged items */ }

// SAFETY: every valid `Lane` implementation guarantees `L::INDEX < 2`;
// `word.0` is a two-element array, so that index is in bounds.
unsafe { *word.0.get_unchecked(L::INDEX) }
```

Because this is a published 1.x unsafe-trait contract with unknown implementations and consumers, a repository-only search cannot authorize evolution. Weakening/removing `INDEX < 2` breaks `read`; weakening/removing the `NAME` mapping can invalidate downstream unsafe consumers; strengthening either clause can invalidate existing downstream implementations. Making the trait safe would admit arbitrary indices unless every consumer validates them, and would also withdraw guarantees from unknown consumers. Preserve the contract in 1.x; any redesign needs an explicit compatibility/migration plan and a fresh whole-ecosystem-facing audit.

## Configuration closure, residual scope, and triggers

Source inspection finds no configuration-selecting construct. LP and PL are parametric over target `usize` width and profile behavior; their aggregate `Covered` equals `Required`, so `Required ⊆ Covered`. CB-R/CB-W witnesses apply to every member of `Required`. Nothing was built, tested, executed, or expanded; no tool evidence is claimed.

Excluded: compiler/backend correctness, binary/platform behavior beyond Rust's abstract semantics, nonexistent downstream implementation auditing, and undocumented robustness properties. Re-audit on any source or safety-contract change, implementation of the repair, support-domain/Rust-version change, or material change to a consumed Rust 1.82 authority.
