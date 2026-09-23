# Source review: `last`

## Claim and verdicts

Snapshot: the complete supplied `target/lib.rs`, specifically safe public function
`last` at lines 3–10 and its sole unsafe operation at line 9. Review date/cutoff:
2026-08-01. No generated code, dependencies, build scripts, FFI, macros, traits,
mutable state, or prior audit are present in the supplied artifact.

**Soundness — PROVED.** For Rust 1.82.0, every well-typed safe call
`last(bytes)` on every target where this source and the cited Rust 1.82.0 slice
APIs exist, in every ordinary profile, is free of Rust undefined behavior. This
is a source-level result under documented Rust abstract semantics.

**Existing `SAFETY` comment — deficient.** It states a return-lifetime fact but
does not state or prove the only material caller obligation of the unsafe call:
that `index` is in bounds. The missing bounds derivation is material and is
reconstructed below. This documentation defect does not change the separately
proved implementation verdict.

There is no documented caller-facing postcondition in the supplied source, so
there is no separate mandatory postcondition verdict. No additional robustness
claim was requested. TCB `TCB-LAST-R1` consists only of the Rust 1.82.0
authoritative axioms inventoried below; there are no additional assumptions.

## Domain, boundary, and coverage

Let

`Required = {Rust 1.82.0} × {every target where the exact source and used 1.82.0 std items exist} × {every ordinary profile} × {every valid &[u8] value}`.

This is the controlling expression supplied by `REQUEST.md`; no normalization,
enumeration, or exclusion is applied. The only language-reachable in-scope API
surface is safe free function `last`. Its caller is adversarial subject only to
well-typed safe use. The only unsafe consumer is
`bytes.get_unchecked(index)`. There is no representation invariant beyond the
valid slice/reference properties enforced at the input type boundary.

The proof below is parametric in slice length, target `usize` width, and profile.
The source has no conditional compilation. It proves the same obligation for
every member of `Required`; hence `Covered = Required` and
`Required ⊆ Covered`. In particular, the subtraction is proved non-overflowing,
so profile-dependent overflow handling is unreachable and immaterial.

## Authoritative premise inventory (`TCB-LAST-R1`)

All entries apply exactly to Rust 1.82.0 and to the full required target/profile
domain. Each is accepted solely as version-matched Rust standard-library or
Reference authority. These, and only these, are the non-local premises consumed
by the derivation.

- **A1 — unchecked slice access.** [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked):
  “Returns a reference to an element or subslice, without doing bounds
  checking.” Its Safety section says: “Calling this method with an
  out-of-bounds index is undefined behavior even if the resulting reference is
  not used.” Verified proposition: a `usize` call must use an in-bounds element
  index; with that obligation met, the shown `&self -> &Output` API returns a
  reference to that element.

- **A2 — slice length.** [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len):
  “Returns the number of elements in the slice.” Its displayed return type is
  `usize`. Verified proposition: `bytes.len()` is the slice's element count `n`
  represented as `usize`.

- **A3 — emptiness test.** [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty):
  “Returns `true` if the slice has a length of 0.” Verified proposition:
  `bytes.is_empty()` reports whether the same slice's element count is zero;
  therefore a false result means `n != 0`.

- **A4 — selected `if` arm.** [If expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions):
  “If all `if` and `else if` conditions evaluate to false then any `else` block
  is executed.” Verified proposition: execution of lines 7–9 implies that the
  line-4 condition evaluated to false; the unsafe call is not executed on the
  true/empty path.

- **A5 — `usize` lower bound.** [Integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types):
  the unsigned-integer table gives `usize` minimum `0` (and maximum
  `2^ptr_size - 1`). Verified proposition: every `usize`, including `n`, is
  nonnegative; thus `n != 0` implies `n >= 1` on every target width.

- **A6 — subtraction and overflow boundary.** [Arithmetic binary operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators)
  identifies binary `-` as “Subtraction.” [Overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow)
  includes: “When `+`, `*` or binary `-` create a value greater than the maximum
  value, or less than the minimum value that can be stored.” Verified
  proposition: for `usize n >= 1`, `n - 1` is the mathematical difference,
  lies in `usize`'s range, and does not overflow in any ordinary profile.

Reconciliation: A4 and A3 establish non-emptiness; A2 and A5 turn it into the
integer bound; A6 establishes the exact index without overflow; A1 consumes the
resulting in-bounds fact and supplies the reference. No cited premise is unused.

## Obligation ledger and reconstructed proof

**O1, empty path (lines 4–5): PROVED.** By A4, when the condition is true only
the consequent path is selected. It returns `None` and executes no unsafe
operation.

**O2, arithmetic (line 7): PROVED.** Let `n = bytes.len()` (A2). Reaching the
`else` proves `is_empty() == false` (A4), hence `n != 0` (A3). Since `n: usize`
and its minimum is zero (A5), `n >= 1`. Therefore `n - 1` is representable and
non-overflowing by A6, and line 7 establishes `index = n - 1`.

**O3, `get_unchecked` (line 9): PROVED.** From O2,
`0 <= index = n - 1 < n = bytes.len()`. Thus `index` denotes an element within
`bytes`, satisfying A1's safety obligation. A1 then supplies a reference to that
element. The call neither mutates the slice nor crosses an intervening call,
callback, unwind point, or state transition. Its displayed borrow-returning
signature, composed with `last`'s borrow-returning signature, carries the
reference rather than fabricating or extending one. Wrapping that reference in
`Some` introduces no further unsafe operation.

The intersection of O1–O3 coverage is all of `Required`, establishing the
soundness certificate stated above.

## Finding DOC-PROOF-1 and replacement text

The existing comment—“The returned reference cannot outlive `bytes`.”—does not
name `get_unchecked`'s bounds requirement and supplies none of O2/O3. Moreover,
the lifetime statement is not the caller obligation identified by A1. A local
reviewer must reconstruct the branch, zero-length, unsigned-arithmetic, and
bounds chain to validate the unsafe call.

Minimal replacement comment:

```rust
// SAFETY: This branch is reached only when `bytes.is_empty()` is false, so
// `bytes.len() != 0`. Therefore `index = bytes.len() - 1` is representable and
// satisfies `index < bytes.len()`, making `index` in bounds for `bytes`.
Some(unsafe { bytes.get_unchecked(index) })
```

Required resolution is documentation-only; `lib.rs` was not edited. Re-audit
this result if the function, unsafe call contract, Rust version, supported
domain, or any cited authoritative text changes.
