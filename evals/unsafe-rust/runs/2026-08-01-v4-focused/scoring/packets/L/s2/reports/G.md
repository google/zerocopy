# Source audit: `lib.rs::last`

## Claim and verdict

**Implementation soundness: PROVED.** For the supplied 11-line `lib.rs`, every well-typed safe call to `last(bytes: &[u8])` under Rust/standard library 1.82.0 is free of Rust undefined behavior. `Required` is exactly the requested product of: Rust 1.82.0; every target on which this source and the used 1.82.0 slice items exist; every ordinary profile; and every valid `&[u8]` argument. The proof is source-level under documented Rust abstract semantics.

**Existing `SAFETY` comment: DEFICIENT.** “The returned reference cannot outlive `bytes`” is an accurate type/lifetime observation, but it does not establish the actual caller obligation of `get_unchecked`: that `index` is in bounds. Closing the implementation proof requires the material reconstruction below. This is a proof-artifact defect, not an implementation defect.

There is no caller-side safety precondition: `last` is public and safe. It has no documented behavioral postcondition, so none is silently inferred from its name. No additional robustness property is in scope.

## Surface, snapshot, and domain closure

The complete target contains only `#![allow(dead_code)]` and the public safe free function `last`; its sole unsafe operation is `bytes.get_unchecked(index)` at line 9. There are no fields, constructors, traits/impls, macros, generated artifacts, dependencies, callbacks, `cfg`s, target-specific operations, mutable state, or representation invariants.

The only profile-sensitive candidate is subtraction overflow. The proof below establishes mathematically that it cannot overflow, so overflow-check configuration, optimization, and debug assertions do not change coverage. Pointer width changes `usize`'s maximum but not the parametric argument. Consequently `Covered = Required`, proving `Required ⊆ Covered` without enumerating targets or profiles. No target was built, tested, executed, or expanded.

## Authoritative premise inventory (Rust 1.82.0)

These are all Rust/std premises consumed; each link is version-matched. The quoted excerpt is the minimum supplying the proposition.

1. **A1 — `get_unchecked` safety.** [Slice `get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked): “out-of-bounds index is undefined behavior”. Proposition: the unsafe call requires its `usize` index to be in bounds (even non-use of the result would not cure an out-of-bounds call). Consumer: OBL-1.
2. **A2 — length.** [Slice `len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len): “number of elements in the slice”. Proposition: `bytes.len()` equals the slice's element count. Consumers: OBL-1 and the bounds normalization.
3. **A3 — empty test.** [Slice `is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty): “true if the slice has a length of 0”. Proposition: length zero implies `is_empty() == true`; its contrapositive is consumed. Consumer: OBL-1.
4. **A4 — branch selection.** [If expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions): “If all if and else if conditions evaluate to false then any else block is executed.” Proposition: reaching lines 7–9 means `bytes.is_empty()` evaluated false. Consumer: OBL-1.
5. **A5 — binary minus.** [Arithmetic operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators): “- Subtraction”. Proposition: binary `-` on primitive integers denotes subtraction. Consumer: OBL-1.
6. **A6 — subtraction overflow criterion.** [Overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow): “binary - create a value greater than the maximum value, or less than the minimum value that can be stored.” Proposition: binary subtraction overflows when its mathematical result lies outside the integer type's range. Consumer: OBL-1 and profile closure.
7. **A7 — `usize` domain.** [Integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types): “The usize type is an unsigned integer type”. Proposition: `usize` values are nonnegative integers (with target-dependent width). Consumer: OBL-1 and target closure.

Facts read directly from the checked source/type signatures—`bytes: &[u8]`, `index: usize`, the shared-reference result, and the returned lifetime being limited by the sole input borrow—are local, compiler-enforced type facts rather than extra admitted premises. The TCB is **TCB-LAST-1**: exactly A1–A7 as authoritative Rust 1.82.0 axioms; no safe/unsafe dependencies, implementation assumptions, external specifications, tools, deployment restrictions, or other assumptions.

## Obligation ledger and reconstructed proof

**OBL-1 (line 9): satisfy A1 for every input/configuration.** Let `n = bytes.len()` (A2).

* If `bytes.is_empty()` is true, the first branch returns `None`; subtraction and the unsafe call are not executed (source plus A4). There is no unsafe obligation.
* Otherwise A4 gives `is_empty() == false`. If `n` were zero, A3 would make it true; hence `n != 0`. Because `n: usize` is unsigned (A7), `n >= 1`.
* By A5, line 7 computes the mathematical value `i = n - 1`. Thus `0 <= i < n`; since `n` itself is representable, `i` is also within the `usize` range. A6 therefore rules out subtraction overflow in every ordinary profile.
* A2 says the slice has exactly `n` elements. The integer positions of an `n`-element sequence are `0..n`, so `0 <= i < n` makes `i` in bounds. This discharges A1 before `get_unchecked(i)` executes. The shared result is tied by the method and function signatures to the `bytes` borrow, so returning it introduces no hidden lifetime or mutation obligation.

Every path is covered, and no premise appears above without a consumer or is consumed without appearing in A1–A7.

## Required replacement comment

```rust
// SAFETY: This branch is reached only when `bytes.is_empty()` is false.
// A zero-length slice is empty, so `bytes.len() != 0`. Therefore
// `index = bytes.len() - 1` cannot underflow and satisfies
// `index < bytes.len()`, making `index` in bounds for `get_unchecked`.
// The returned shared reference remains bounded by the `bytes` borrow.
Some(unsafe { bytes.get_unchecked(index) })
```

Review must be repeated if `last`, its signature/comment, Rust/std version, used std contracts, or the requested target/profile domain changes.
