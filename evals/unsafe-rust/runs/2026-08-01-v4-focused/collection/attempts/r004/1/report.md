# Local proof-artifact review: `last`

## Claim and results

**Implementation soundness: PROVED.** For the exact supplied `lib.rs`, Rust and standard library 1.82.0, every target on which this source and its used standard-library items exist, every ordinary profile, and every well-typed safe call `last(bytes)`, execution is free of Rust undefined behavior under the documented Rust abstract semantics. The TCB is `TCB-LAST-1` below: version-matched Rust authorities only, with no additional assumptions.

**Existing `SAFETY` comment: DEFICIENT.** “The returned reference cannot outlive `bytes`” does not establish the sole material caller obligation of `get_unchecked`: that `index` is in bounds. Reconstructing that omitted bounds proof is necessary to certify the implementation. This is a proof-artifact defect, not an implementation defect.

`last` has no documented behavioral postcondition, so no independent `CONTRACT-BROKEN` claim arises. Its safe signature imposes no caller-side safety precondition beyond a well-typed `&[u8]`.

## Snapshot, boundary, and domain

The audited artifact is exactly the supplied `target/lib.rs`; no revision or digest was supplied. Audit cutoff: 2026-08-01. The complete safe boundary is the public free function `pub fn last(bytes: &[u8]) -> Option<&u8>`. Its only unsafe site is `bytes.get_unchecked(index)`. There are no fields, traits, impls, callbacks, FFI, macros, generated artifacts, dependencies, persistent invariants, `cfg`s, features, or target-specific branches in the supplied source. No build, test, execution, or tool-derived evidence was used.

Let

`Required = {source exactly as supplied} × {Rust/std 1.82.0} × {targets where the source and used items exist} × {ordinary profiles} × {all valid &[u8] inputs}`.

The proof below is parametric in slice length, `usize` width, target, and profile. Hence `Covered = Required`, proving `Required ⊆ Covered`; no enumeration or exclusion is used. Debug/release overflow behavior is irrelevant because the subtraction is proved non-overflowing.

## Obligation ledger and reconstructed proof

Let `L = bytes.len()`.

1. **Control flow.** The unsafe site is reachable only through the `else` block, so `bytes.is_empty()` evaluated to `false` (A2).
2. **Nonzero length.** A1 states `L = 0 ⇒ is_empty() = true`; by contraposition with step 1, `L ≠ 0`. A3 identifies `L` as the slice's element count, and A4 identifies its type as unsigned, so `L ≥ 1`.
3. **Arithmetic.** Integer `-` is subtraction (A5). Therefore `index = L - 1` is representable and satisfies `0 ≤ index < L`. It neither creates a value below the type minimum nor overflows under A6, in any ordinary profile.
4. **Unsafe call.** Thus the `usize` index is in bounds. This discharges A7's safety requirement, and `get_unchecked` supplies the shared element reference described by its contract. Wrapping it in `Some` and returning it introduces no unsafe operation. The empty branch executes no unsafe operation.

These cases exhaust every boolean result and every valid slice, so every unsafe-site obligation is proved over `Required`.

## Authoritative premise inventory (`TCB-LAST-1`)

All entries apply exactly to Rust/std 1.82.0 on every target where the cited item and audited source exist. Each is accepted as a versioned Rust `AXIOM`; there are no other TCB categories or premises.

- **A1 — `is_empty`.** The docs say “`true` if the slice has a length of 0.” [Rust 1.82 slice `is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty). Verified proposition consumed in step 2: `L = 0 ⇒ is_empty() = true`.
- **A2 — `if`.** “If all `if` and `else if` conditions evaluate to `false` then any `else` block is executed.” [Rust 1.82 Reference, `if` expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions). Verified proposition consumed in step 1: this `else` execution entails the sole condition evaluated to `false`.
- **A3 — slice length.** `len` returns the “number of elements.” [Rust 1.82 slice `len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len). Verified proposition consumed in step 2: `L` is the slice's element count; its displayed return type is `usize`.
- **A4 — `usize`.** “The `usize` type is an unsigned integer type.” [Rust 1.82 Reference, numeric types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types). Verified proposition consumed in steps 2–3: `L` and `index` have no negative representable values; the proof is width-parametric.
- **A5 — subtraction.** The primitive-integer table defines `-` as “Subtraction.” [Rust 1.82 Reference, arithmetic operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators). Verified proposition consumed in step 3: `L - 1` denotes integer subtraction when representable.
- **A6 — overflow boundary.** Binary subtraction overflows when it creates a value “less than the minimum value that can be stored” (or above the maximum). [Rust 1.82 Reference, overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow). Verified proposition consumed in step 3: because `L ≥ 1`, `L - 1 ≥ 0`, so this subtraction does not overflow; overflow-check profile choices cannot change this path.
- **A7 — unchecked indexing.** The method “Returns a reference to an element or subslice”; an “out-of-bounds index is undefined behavior.” [Rust 1.82 slice `get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked). Verified proposition consumed in step 4: a `usize` index must be in bounds, and a contract-satisfying call returns the shared reference.

The derivation consumes A1–A7 exactly as mapped above and no unlisted Rust semantic premise material to the unsafe obligation.

## Finding and replacement comment

**FINDING-COMMENT-1 (proof documentation):** the current comment establishes no implication from the dominating branch to `index < bytes.len()`. Minimum resolution is to replace it with:

```rust
// SAFETY: This else branch is executed only when `bytes.is_empty()` is false.
// A zero-length slice makes `is_empty()` true, so `bytes.len() != 0` here.
// Thus `index = bytes.len() - 1` cannot underflow and is strictly less than
// `bytes.len()`, so it is in bounds as required by `get_unchecked`.
```

Re-audit if the source, function or callee contract, Rust/std version, support domain, or cited authoritative prose changes.
