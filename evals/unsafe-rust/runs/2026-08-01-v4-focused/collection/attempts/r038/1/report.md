# `last` source review

## Claim and verdict

**Implementation soundness: PROVED.** For the exact `target/lib.rs` supplied, every well-typed safe call to `last` is free of Rust undefined behavior under Rust 1.82.0 documented abstract semantics, on every target where this source and the used Rust 1.82.0 standard-library items exist, in every ordinary profile. There is no caller safety precondition and no additional TCB assumption.

**Existing `SAFETY` comment: deficient.** It discusses the result's lifetime, but `get_unchecked`'s material safety obligation is that the index not be out of bounds. The comment gives none of the branch-and-arithmetic derivation needed to establish that obligation. The missing derivation can be reconstructed, so this is a proof-artifact defect, not an implementation defect.

There are no documented postconditions on `last` and no additional robustness claim in the request; consequently no separate postcondition verdict is required.

## Snapshot, boundary, and domain closure

Scope is exactly `target/lib.rs`, lines 1–11. The sole language-reachable API surface is safe public free function `last(bytes: &[u8]) -> Option<&u8>`. Its sole unsafe operation is `bytes.get_unchecked(index)` at line 9. There are no fields, constructors for an invariant-bearing type, traits or impls, callbacks, macros, generated code, dependencies, `cfg`s, FFI, concurrency, allocation, or other unsafe sites. The only transient invariant is `INV-N`: in the `else` branch, for the unchanged receiver `bytes`, `n = bytes.len() > 0`.

The request directly defines

`Required = {exact source} × {Rust/std 1.82.0} × {targets on which the source and used items exist} × {ordinary profiles}`.

No normalization, exclusion, or finite target inventory is used. The proof below is parametric in the target-dependent `usize` value `n`; it assumes no pointer width. Profile-dependent overflow handling is immaterial because the subtraction is proved not to overflow. The source contains no configuration selection. Thus every premise applies throughout `Required`, `Covered = Required`, and `Required ⊆ Covered`.

No build, test, execution, expansion, or tool-derived evidence was used. This is a source-level result, not a claim about a particular compiler binary or backend.

## Obligation ledger and reconstructed proof

`OBL-1` (line 7, all of `Required`): prove `bytes.len() - 1` does not underflow or panic and produces `index = n - 1`. **PROVED.**

`OBL-2` (line 9, all of `Required`): prove `index` is not out of bounds for the same `bytes` passed to `get_unchecked`. **PROVED.**

Derivation:

1. Let `q` be the boolean returned by `bytes.is_empty()` at line 4. Execution reaches the `else` block only when `q = false` (AX-IF).
2. AX-EMPTY says `bytes.len() = 0 -> q = true`; by contraposition, `q = false -> bytes.len() != 0`. Both observations concern the same shared slice value, with no intervening mutation, call, callback, or state transition. Set `n = bytes.len()` at line 7, so `n != 0`.
3. `len` returns a `usize` and counts elements (AX-LEN). `usize` is unsigned (AX-USIZE), hence `n != 0` gives `n >= 1`.
4. Binary `-` on these primitive integer operands is subtraction (AX-SUB). Therefore line 7 computes `n - 1`. Since `n >= 1`, the result is nonnegative and no greater than the already representable `n`; it is representable as `usize`. It is not less than the type minimum, so AX-OVERFLOW's underflow case cannot occur under any ordinary overflow-check setting. Thus `index = n - 1` and `0 <= index < n`.
5. `n` is the number of elements of this same `bytes`, so `index` is in bounds. This discharges the sole documented `get_unchecked` safety requirement (AX-GET). The standard-library contract then supplies the returned shared reference. No later unsafe consumer exists.

The empty case never evaluates the `else` block, subtraction, or unsafe call. Hence `OBL-1` and `OBL-2` cover all reachable unsafe executions, and the implementation certificate is complete.

## Complete authoritative-premise inventory

All entries are Rust 1.82.0 axioms, apply on every target/profile in `Required`, and were verified on the linked versioned page. Quotations are the exact minimal prose fragments consumed.

- **AX-EMPTY** — [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty): “Returns `true` if … length of 0.” Verified proposition: zero length implies the returned boolean is true. Used in step 2.
- **AX-LEN** — [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len): “Returns the number of elements”. Together with the displayed return type `usize`, verified proposition: `bytes.len()` is the element count represented as `usize`. Used in steps 2–5.
- **AX-IF** — [if expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions): “If all `if` and `else if` conditions evaluate to `false` then any `else` block is executed.” Verified proposition: this single-condition `else` runs only for a false condition. Used in step 1 and to exclude unsafe evaluation on the empty branch.
- **AX-USIZE** — [numeric integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types): “The `usize` type is an unsigned integer type”. Verified proposition: `usize` values are nonnegative target-width integers. Used in steps 3–4.
- **AX-SUB** — [arithmetic binary operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators): the primitive-integer `-` entry is “Subtraction”. Verified proposition: line 7 performs integer subtraction. Used in step 4.
- **AX-OVERFLOW** — [overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow): binary subtraction overflows when it creates a value “less than the minimum value that can be stored”. Verified proposition: unsigned subtraction underflow is overflow; because the mathematical result is representable here, profile-controlled overflow behavior is unreachable. Used in step 4 and configuration closure.
- **AX-GET** — [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked): “Returns a reference to an element or subslice”; “out-of-bounds index is undefined behavior”. Verified proposition: the operation supplies an element reference without bounds checking, and its unsafe-call obligation is that the numeric index be in bounds. Used in step 5.

No other Rust semantic or standard-library proposition is materially consumed. In particular, the existing comment's lifetime assertion is not a precondition of `get_unchecked` and plays no role in the derivation. Every inventoried entry has a consumer above, and every nonlocal premise used above appears in this inventory. The TCB contains these authoritative Rust/std axioms only; there are no dependency, implementation, external-specification, deployment, tool, or out-of-band assumptions.

## Finding and replacement comment

**DOC-1 — inadequate local proof (implementation remains PROVED).** The current comment does not identify `get_unchecked`'s bounds obligation, the dominating false `is_empty` branch, the non-underflowing subtraction, or the conclusion `index < bytes.len()`. Replace it with:

```rust
// SAFETY: This branch is reached only when `bytes.is_empty()` is false, so
// `bytes.len() > 0`. Thus subtracting 1 cannot underflow and produces
// `index < bytes.len()` for this same slice, so `index` is in bounds as
// required by `get_unchecked`.
Some(unsafe { bytes.get_unchecked(index) })
```

This repair changes proof documentation only; it neither adds a caller obligation nor changes behavior. Re-audit if the source, function contract, support domain, Rust/std version, cited contracts, or overflow/index computation changes.
