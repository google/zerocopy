# Source review: `last`

## Claim, snapshot, and verdicts

Audited artifact: the exact `target/lib.rs` supplied for this review, containing one public safe function, `pub fn last(bytes: &[u8]) -> Option<&u8>`, and one unsafe operation, `bytes.get_unchecked(index)`. No generated code, dependencies, features, `cfg`, macros, FFI, traits, mutable state, or other API surfaces occur in the supplied target.

**Soundness — PROVED.** For Rust and standard library 1.82.0, every target on which this exact source and the used standard-library items exist, every ordinary profile, and every well-typed safe call with any valid `&[u8]`, every execution of `last` is free of Rust undefined behavior under the documented Rust abstract semantics. There is no caller-side safety precondition.

**Existing proof artifact — DEFICIENT.** The comment “The returned reference cannot outlive `bytes`” states a type-enforced lifetime property, but does not establish the sole safety precondition of the executed unsafe call: that `index` is in bounds. A material bounds-and-arithmetic derivation had to be reconstructed below. This is a documentation defect, not an implementation defect.

There is no source documentation specifying a caller-facing behavioral postcondition, so no separate documented-postcondition verdict is in scope. The standard-library return guarantee consumed by the soundness proof is covered below.

## Domain and boundary closure

Let `Required = {Rust/stdlib = 1.82.0} × {targets where this source and these items exist} × {ordinary profiles} × {all valid &[u8] inputs}`. This is the controlling expression stated by `REQUEST.md`; no normalization, exclusion, release interpolation, or finite target enumeration is used.

The only safe surface is `last`; its input type enforces a valid shared slice reference and its return type carries a shared element reference. The only unsafe consumer is `get_unchecked`. There is no invariant-bearing stored state. The local relation is that `n = bytes.len()` and `index = n - 1`, with the unchanged `bytes` value used as the call receiver.

Coverage partitions executions by the Boolean result of `bytes.is_empty()`, an exhaustive partition. The `true` case executes no unsafe operation. The `false` case is proved parametrically below for every slice length and every target pointer width. Because subtraction is proved non-overflowing, profile-dependent overflow checking is irrelevant. Thus `Covered = Required`, establishing `Required ⊆ Covered`.

## Authoritative premise inventory (Rust 1.82.0 only)

Each entry is an accepted, version-matched Rust axiom; its exact proposition is stated after the quotation.

**A-GET.** [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked):

> “Returns a reference to an element or subslice, without doing bounds checking.”
>
> “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.”

Proposition: for the `usize` call here, the caller must establish that `index` selects an element of this slice; when it does, the method returns a reference to that element. Consumed by O3–O4.

**A-LEN.** [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len), whose displayed signature returns `usize`:

> “Returns the number of elements in the slice.”

Proposition: `n = bytes.len()` is the slice's element count and has type `usize`. Consumed by O1–O4.

**A-EMPTY.** [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty):

> “Returns `true` if the slice has a length of 0.”

Proposition: `bytes.len() = 0` implies `bytes.is_empty() = true`; contraposition permits a false result to establish nonzero length. Consumed by O1.

**A-IF.** [if expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions):

> “If a condition operand evaluates to `true`, the consequent block is executed and any subsequent `else if` or `else` block is skipped.”
>
> “If all `if` and `else if` conditions evaluate to `false` then any `else` block is executed.”

Proposition: reaching this `else` block establishes that `bytes.is_empty()` evaluated to false; the other branch contains no unsafe call. Consumed by O1 and coverage.

**A-SUB.** [arithmetic and logical binary operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators):

> “Operators are defined for built in types by the Rust language.”

The table specifies binary `-` on integers as “Subtraction.” Proposition: the `usize` expression `n - 1` is integer subtraction when representable. Consumed by O2.

**A-OVERFLOW.** [overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow):

> “When `+`, `*` or binary `-` create a value greater than the maximum value, or less than the minimum value that can be stored”

is listed as overflow, and the section states that integer operators panic on overflow in debug mode. Proposition: if the mathematical result remains in the `usize` range, this subtraction does not overflow, so overflow-check configuration cannot alter this path. Consumed by O2 and configuration closure.

**A-USIZE.** [integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types):

> “The `usize` type is an unsigned integer type with the same number of bits as the platform’s pointer type.”

Proposition: `usize` values are nonnegative integers; therefore a nonzero `usize` is at least one. Consumed by O2. The proof is parametric in its target-dependent width.

No other Rust semantic or standard-library premise is consumed. Local source facts are the displayed types, the dominating branch, the assignments, the absence of any intervening mutation/reassignment, and the fact that the same `bytes` value is the receiver. Ordinary integer inequalities and contraposition are logical/mathematical inference, not additional Rust premises.

## Obligation ledger and reconstructed proof

**O1 — nonzero length (PROVED).** The unsafe call is reachable only in the `else` block. A-IF makes the observed condition false. A-EMPTY gives `len = 0 ⇒ is_empty = true`; contraposition gives `is_empty = false ⇒ n != 0`.

**O2 — arithmetic and bound (PROVED).** By A-LEN and A-USIZE, `n` is a nonnegative integer; O1 therefore gives `n ≥ 1`. Hence the mathematical value `n - 1` is nonnegative, is no greater than the representable `n`, and is strictly less than `n`. A-SUB and A-OVERFLOW therefore establish that `index = n - 1` is representable without underflow/overflow in every ordinary profile and that `index < bytes.len()`.

**O3 — unsafe-call precondition (PROVED).** `index` is a `usize`, so it is nonnegative; O2 gives `index < bytes.len()` for the unchanged receiver. It therefore selects an element of `bytes`, discharging A-GET's bounds requirement. No alias, mutation, temporal, panic, or unwind obligation is introduced by this shared-reference call.

**O4 — result (PROVED).** A-GET returns a reference to the selected element. The inspected method and function signatures carry that shared borrow into `Option<&u8>`; no unsafe lifetime extension, raw pointer, or stored state occurs. The empty/true branch returns `None` without unsafe execution.

## Finding and proposed repair

**F-DOC-1 — inadequate local `SAFETY` proof.** The current comment proves neither O1, O2, nor O3. Its lifetime statement does not imply in-bounds indexing and therefore cannot justify `get_unchecked`. Replace it with:

```rust
// SAFETY: Reaching this `else` branch means `bytes.is_empty()` was false.
// Since a zero-length slice makes `is_empty()` true, `bytes.len()` is nonzero.
// Thus `bytes.len() - 1` neither underflows nor overflows and is strictly less
// than `bytes.len()`, so `index` is in bounds as required by `get_unchecked`.
```

This repair changes no implementation or public contract and has no compatibility impact. Re-audit if the branch, index arithmetic, receiver, function signature, Rust/stdlib version, supported configuration domain, or `get_unchecked` contract changes.

## TCB, evidence, and residual scope

TCB revision `TCB-LAST-1` consists only of accepted A-GET through A-USIZE, each verified against the linked Rust 1.82.0 Reference or standard-library page and consumed exactly as mapped above. There are no additional TCB assumptions, dependencies, tools, tests, sampled executions, generated artifacts, or prior audits. No build, test, execution, or macro expansion was performed. The verdict is source-level; compiler/backend binary correctness and behavior outside the exact requested Rust/version/target/profile domain are excluded.
