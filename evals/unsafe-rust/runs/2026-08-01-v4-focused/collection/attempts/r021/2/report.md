# Audit of `last`

## Claim, snapshot, and verdict

**Soundness verdict: PROVED.** For the exact `lib.rs` supplied with this review, under Rust and standard library 1.82.0, every well-typed safe call to `last` on every target where this source and the used 1.82.0 slice APIs exist, in every ordinary profile, is free of Rust undefined behavior. The caller has no extra safety obligation. `Required(case)` is exactly that predicate over source identity, toolchain/stdlib, target, profile, input slice, and permitted execution. `Required_cfg(c)` is `Rust/std = 1.82.0 ∧ target has the used items ∧ profile ∈ Ordinary`. Audit cutoff: this supplied snapshot, reviewed 2026-08-01.

The only public/safe surface is `pub fn last(bytes: &[u8]) -> Option<&u8>` (`lib.rs:3-11`). Its only unsafe consumer is `bytes.get_unchecked(index)` at line 10. There are no unsafe declarations, fields, traits/impls, callbacks, macros, hidden APIs, dependencies, FFI, generated artifacts, `cfg` branches, or invariant-bearing state. `#![allow(dead_code)]` does not select or alter code. No documented postcondition or separately requested robustness property exists; the function name is not treated as normative documentation.

**Proof-artifact verdict: DEFICIENT.** The existing `SAFETY` comment says only that the returned reference cannot outlive `bytes`. That does not establish the actual `get_unchecked` obligation—an in-bounds index—and therefore is not an adequate local proof. The missing derivation is material and is reconstructed below. This is a documentation defect, not an implementation defect.

TCB log `TCB-LAST-1` consists only of the Rust 1.82.0 authoritative axioms A1-A5 below. There are no additional TCB assumptions, selected dependencies, tools, tests, or implementation/platform premises. This is a source-level result relative to documented Rust abstract semantics, not a compiler-backend or binary certificate.

## Complete premise inventory

Each semantic/std premise consumed by the derivation appears here; the remaining steps are inspected source facts or arithmetic/logic.

**A1 — slice length.** Rust 1.82.0 [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len), signature `pub const fn len(&self) -> usize`:

> “Returns the number of elements in the slice.”

Verified proposition: for the input slice, `bytes.len()` is a `usize` equal to its number of elements; call that value `n`.

**A2 — emptiness observation.** Rust 1.82.0 [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty):

> “Returns `true` if the slice has a length of 0.”

Verified proposition used: `n = 0 ⇒ bytes.is_empty() = true`; hence, by contraposition, `bytes.is_empty() = false ⇒ n ≠ 0`.

**A3 — branch execution.** Rust 1.82.0 [if expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions):

> “If a condition operand evaluates to `true`, the consequent block is executed and any subsequent `else if` or `else` block is skipped. If a condition operand evaluates to `false`, the consequent block is skipped … If all `if` and `else if` conditions evaluate to `false` then any `else` block is executed.”

Verified proposition: the unsafe call is reachable only when `bytes.is_empty()` evaluated to false; when it evaluates true, only `None` is evaluated.

**A4 — `usize` range and subtraction.** Rust 1.82.0 [integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types) states, under “The unsigned integer types consist of,” the table row:

> `usize` | minimum `0` | maximum `2^w − 1`

Rust 1.82.0 [binary-operator table](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators) gives the integer meaning of `-` as:

> “Subtraction”

and [Overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow) defines an overflow case as:

> “When `+`, `*` or binary `-` create a value greater than the maximum value, or less than the minimum value that can be stored.”

Verified proposition: a nonzero `usize` value `n` lies in `[1, 2^w−1]`; its integer subtraction `n−1` lies in `[0, 2^w−2]`, so `n - 1` does not overflow under any target width or overflow-check/profile setting, and its value is strictly less than `n`.

**A5 — unsafe operation contract and result.** Rust 1.82.0 [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked):

> “Returns a reference to an element or subslice, without doing bounds checking.”

> “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.”

The same safety section expressly gives `.get_unchecked(len)` as UB. Verified proposition: the caller must supply an in-bounds index; for a `usize` element index of a slice of length `n`, `0 ≤ index < n` discharges that condition, and the result is a reference to that indexed element.

## Obligation ledger and reconstructed derivation

**O1, reachability and arithmetic — PROVED over all `Required`.** Let `n = bytes.len()` (A1). A3 says reaching the `else` and unsafe call means the condition was false. A2 then yields `n ≠ 0`. By A4, `n ≥ 1`, `index = n - 1` is evaluated without overflow in every profile, and `0 ≤ index < n`.

**O2, `get_unchecked` precondition — PROVED over all `Required`.** O1 establishes exactly that `index` is in the slice's bounds. This discharges A5's sole safety condition. A5 supplies a shared reference to element `n-1`; no code, callback, mutation, or unwind point intervenes between computing `index` and the call.

**O3, other input/control-flow case — PROVED over all `Required`.** If the condition is true, A3 skips the `else`, so no unsafe operation executes and the function evaluates `None`. If false, O1-O2 apply. Boolean truth/falsity exhausts executions, so their union covers every input/execution.

For each obligation, the derivation is symbolic in target width `w` and profile. Every required configuration selects identical source, and A1-A5 contain no narrower target/profile qualification. Thus each obligation's covered predicate contains `Required`; pointwise intersection across O1-O3 still contains `Required`. This proves `Required ⊆ Covered` and certifies the verdict. Empty, one-element, and maximum-representable-length boundaries respectively take O3, produce index `0`, and produce `n-1` without overflow; none falsifies the proof.

## Required replacement comment

```rust
// SAFETY: Reaching this branch means `bytes.is_empty()` was false, so the
// slice length is nonzero. Therefore `index = bytes.len() - 1` does not
// overflow and satisfies `index < bytes.len()`, making it in bounds as
// required by `slice::get_unchecked`.
Some(unsafe { bytes.get_unchecked(index) })
```

This is the minimum acceptable repair: it names the callee obligation, the dominating branch fact, the arithmetic derivation, and the conclusion. The old lifetime sentence may be omitted because it does not discharge an unsafe precondition.

## Residual scope and review triggers

Nothing within the requested source-level domain remains uncovered. No target was built or executed, as required. Re-audit if the function, comment, signature, slice APIs/contracts, Rust/stdlib version, target-availability predicate, or profile scope changes. Compiler code generation, custom backend correctness, binaries, and behavior beyond any documented postcondition are outside this source review.
