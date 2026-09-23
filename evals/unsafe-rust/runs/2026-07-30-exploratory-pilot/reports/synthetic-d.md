# Unsafe Rust Audit: `opaque-byte-tools` 0.1.0

## Claims and verdicts

- **Soundness:** **PROVED** for the exact snapshot, under Rust/stdlib 1.85.0,
  edition 2021, every target on which the crate is compilable, all ordinary
  profiles, either debug-assertion state, and either panic strategy.
- **Documented postconditions:** **PROVED**. A valid call to
  `item_unchecked(bytes, index)` returns the copied value of `bytes[index]`.
- **Combined mandatory result:** **PROVED**, relative to the stated TCB.
- **Binary/backend/security claims:** None.
- **Findings affecting the verdict:** No `UNSOUND`, `UNPROVED`, or
  `CONTRACT-BROKEN` findings.

The crate has no dependencies, lockfile, features, build script, FFI,
assembly, atomics, custom allocator, included/generated files, target `cfg`s,
or external state. The declarative macro has exactly one in-scope invocation
and was audited textually. No target code was modified, built, tested,
expanded by a tool, or executed.

## Boundary and API coverage

| Surface | Classification | Result |
|---|---|---|
| `decode_flag` | Safe free function | **PROVED**: exhaustive `u8` match; invalid encodings panic without unsafe state. |
| `AddressSource` and `load_source` | Caller-implementable safe trait and safe generic consumer | **PROVED**: the consumer relies only on the type-valid `&u8` returned by the trait. |
| `ByteHandle`, `new`, and `load` | Public type with private field; safe methods | **PROVED**: the sole field is an ordinary shared reference supplied by the constructor and only read. |
| `item_unchecked` | Public unsafe function | **PROVED** under its complete `index < bytes.len()` precondition. |
| `make_indexer!` and `profile_index` | Private macro generating a public safe function | **PROVED**: the one expansion contains ordinary checked slice indexing and no unsafe operation. |
| `checked_first` | Safe function backed by unsafe indexing | **PROVED** by the derivation below. |

There are no public fields, exported macros, reexports, hidden public items,
unsafe traits or impls, custom `Drop`, or manual auto-trait impls.

## Invariants

- **INV-BYTEHANDLE:** While a `ByteHandle<'a>` is usable, `address` is a
  type-valid shared reference to a `u8` for `'a`. The field type establishes
  the property, its privacy prevents unchecked construction, and neither
  method mutates it.
- No global, temporal, concurrency, partial-initialization, or
  destruction-sensitive invariant exists.

## Obligation ledger

### OBL-1 — `item_unchecked` call to `get_unchecked`

**PROVED.** Its unsafe API contract requires `index < bytes.len()`. A `usize`
index is nonnegative, so this places it in the zero-based slice bounds. Rust
1.85.0 documents that `get_unchecked` returns a reference to the indexed
element and that an out-of-bounds index is undefined behavior. Therefore the
documented caller fact discharges the callee's only additional safety
condition. Dereferencing the resulting `&u8` copies that element without
extending an alias or ownership obligation.

### OBL-2 — `checked_first` call to `get_unchecked(0)`

**PROVED.**

- If `bytes.is_empty()` is true, the function returns before reaching unsafe
  code.
- Rust 1.85.0 specifies that `is_empty` reflects whether slice length is zero.
- Therefore, on the fallthrough path, `bytes.len() != 0`; because the length is
  a `usize`, `0 < bytes.len()`.
- No callback, mutation, panic point, or state transition intervenes.
- Thus index zero is in bounds and the unchecked access is permitted.

The resulting reference is immediately copied into `Some`; no obligation
escapes.

### OBL-3 — `item_unchecked` postcondition

**PROVED.** Rust 1.85.0 describes `get_unchecked` as returning a reference to
the selected element. Dereferencing that reference yields the same `u8` that
checked expression `bytes[index]` denotes under the function's in-bounds
precondition.

### OBL-4 — Safe-surface closure

**PROVED.** All remaining operations are safe Rust. Caller-controlled
`AddressSource` implementations are consumed only through their enforced
return type. Panic, reentrancy, or other safe implementation behavior cannot
expose an invalid local state.

## Configuration closure

The supported set is Rust/stdlib 1.85.0 with edition 2021, every compilation
target capable of supplying that standard library, all ordinary profiles,
debug assertions enabled or disabled, and normal unwind or abort panic
behavior.

Coverage is parametric:

- There is no conditional compilation or target-dependent representation.
- No pointer-width arithmetic, overflow-sensitive arithmetic, layout
  assumption, generated input, dependency feature, or debug assertion
  participates in a proof.
- Panic paths contain no unsafe operation or suspended invariant.
- The single macro invocation expands from a finite, directly inspected rule
  to a safe indexing function.

## TCB audit log

| ID | Accepted proposition | Exact authority | Consumers |
|---|---|---|---|
| `AXIOM-SLICE-GET-1.85` | For an in-bounds `usize`, `slice.get_unchecked` returns a reference to the indexed element; an out-of-bounds call is UB. | [Rust 1.85.0 `slice::get_unchecked`](https://doc.rust-lang.org/1.85.0/std/primitive.slice.html#method.get_unchecked) | OBL-1, OBL-2, OBL-3 |
| `AXIOM-SLICE-EMPTY-1.85` | `slice.is_empty()` is true exactly when the slice length is zero. | [Rust 1.85.0 `slice::is_empty`](https://doc.rust-lang.org/1.85.0/std/primitive.slice.html#method.is_empty) | OBL-2 |
| `AXIOM-INDEX-1.85` | Slice indices are zero-based. | [Rust 1.85.0 Reference, array and slice indexing](https://doc.rust-lang.org/1.85.0/reference/expressions/array-expr.html#array-and-slice-indexing-expressions) | OBL-1, OBL-2 |

The official Rust 1.85.0 authorities were opened and checked. No dependency,
implementation, platform, probabilistic, deployment, or tool-result
assumption is consumed.

## Maintenance finding

**DOC-M1 — Local unsafe proofs are less complete than the supplied skill
requires.**

- `item_unchecked` has a sufficient public safety contract but no adjacent
  `SAFETY` derivation for the internal unchecked call.
- `checked_first` correctly identifies the dominating check, but does not
  explicitly state the `get_unchecked` contract or its result.

The audit discharges both obligations above, so this is not an `UNPROVED` or
soundness finding for the frozen snapshot. The minimal maintenance remedy is to
record the corresponding derivations adjacent to those unsafe blocks.

## Residual scope and re-audit triggers

No binary/code-generation-backend theorem, performance property, panic-freedom
promise, or toolchain version other than 1.85.0 was audited. Independent human
review was not performed.

Re-audit is required for changes to source, public safety contracts, supported
Rust versions/configurations, macro invocations, dependencies/build machinery,
or consumed official documentation.
