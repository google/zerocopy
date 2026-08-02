# Review of `last`

## Claim, scope, and verdict

**Implementation soundness: PROVED.** For the exact supplied `lib.rs`, every well-typed safe call to `last` is free of Rust undefined behavior under Rust and standard library 1.82.0, for every input `bytes: &[u8]`, every target on which this source and the used 1.82.0 slice APIs exist, and every ordinary profile. The result uses only the authoritative 1.82.0 axioms inventoried below; there are no additional TCB assumptions.

**Existing `SAFETY` comment: deficient.** The comment's lifetime statement is not the safety precondition documented for `get_unchecked`. It omits the material derivation that `index` is in bounds. The implementation verdict and proof-artifact verdict are therefore intentionally different.

There is no documented caller precondition or documented postcondition on `last` itself. The documented `get_unchecked` result guarantee consumed by the wrapper is proved below.

## Domain and surface closure

Let `Required(case)` mean: exact supplied source; Rust/stdlib 1.82.0; any target where the source and `is_empty`, `len`, and `get_unchecked` exist; any ordinary profile; and any well-typed safe call with any valid shared byte slice and permitted execution. Its configuration projection changes none of the source: there is no `cfg`, feature, generated code, dependency, FFI, allocator, concurrency, or target-specific operation. The sole language-reachable surface in scope is the public safe free function `last`; its only unsafe obligation site is `bytes.get_unchecked(index)`.

Partition every required case by the natural number `n = bytes.len()`: `n = 0` or `n != 0`. These cases are exhaustive and the proof below is parametric in target and profile. Thus their union covers every configuration fiber and every input; the aggregate `Covered` predicate equals `Required` for the in-scope soundness obligation.

## Reconstructed proof and obligation ledger

**O1 — empty path.** If `bytes.is_empty()` evaluates to true, `if` semantics executes the consequent and skips the `else`. The function returns `None` and never reaches an unsafe operation. This path is covered.

**O2 — `get_unchecked` precondition.** On the `else` path, `if` semantics establishes that `bytes.is_empty()` evaluated to false. Axiom A1 states `n = 0 -> is_empty() = true`; its contrapositive gives `is_empty() != true -> n != 0`. A2 identifies `n` as the number of slice elements, hence a natural number, so `n != 0` gives `n >= 1`. Consequently the source assignment computes the representable value `index = n - 1`, with `0 <= index < n`. It is therefore not an out-of-bounds index, discharging A4's exact unsafe-call requirement. There is no underflow, so no overflow-check or optimization profile creates another case.

**O3 — consumed callee result.** By A4, the in-bounds call returns a reference to the selected element; with `index = n - 1`, that is the final element. The callee and wrapper signatures carry the returned shared reference from the input borrow, so no hidden caller obligation is introduced. `Some` wraps that reference. This establishes every documented callee postcondition consumed here.

O1 and O2 cover the exhaustive partition; O3 establishes the consumed result on O2. Therefore `Required subseteq Covered`, certifying the stated `PROVED` verdict. No test, build, compiler-backend claim, or unlisted premise participates.

## Authoritative premise inventory and reconciliation

All quotations and links are version-matched to 1.82.0 and apply throughout the required target/profile domain where the respective item exists.

- **A1 (`slice::is_empty`).** The documentation says it returns “true if the slice has a length of 0.” [Rust 1.82.0 `is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty). Verified proposition: for this slice, `len = 0 -> is_empty() = true`. O2 consumes its contrapositive.
- **A2 (`slice::len`).** It returns the “number of elements in the slice.” [Rust 1.82.0 `len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len). Verified proposition: `n = bytes.len()` is exactly the slice's element count. O2 consumes it.
- **A3 (`if`).** “If a condition operand evaluates to false, the consequent block is skipped”. [Rust 1.82.0 `if` expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions). Together with the same paragraph's branch rules, this verifies that only the true condition reaches O1 and only the false condition reaches the `else` containing O2.
- **A4 (`slice::get_unchecked`).** The contract identifies an “out-of-bounds index” as “undefined behavior” and says the method returns a “reference to an element”. [Rust 1.82.0 `get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked). Verified propositions: the call must use an in-bounds index even if the result were unused, and an admitted `usize` index returns a reference to its element. O2 consumes the former; O3 consumes the latter.

This list is complete for the derivation. The exhaustive two-case split, contrapositive, and `n >= 1 -> 0 <= n - 1 < n` are mathematical steps. Branch reachability and assignments are inspected local source facts. No overflow behavior, integer-width bound, target property, lifetime promise beyond the checked signatures, dependency behavior, or external specification is silently consumed; accordingly, unused allowlisted pages are not cited.

## Finding and replacement comment

The existing comment—“The returned reference cannot outlive `bytes`.”—does not mention A4's bounds obligation and does not connect the dominating branch to `len() - 1`. Removing the reconstructed A1/A3-to-bounds argument leaves no local proof of the unsafe precondition, so the omission is material. The statement is compatible with the typed signatures, but it is not an adequate `SAFETY` proof.

Replace it with:

```rust
// SAFETY: This `else` branch is reached only when `bytes.is_empty()` is
// false. Therefore `bytes.len() != 0`, so `index = bytes.len() - 1` is
// representable and satisfies `index < bytes.len()`. Thus `index` is in
// bounds, as required by `slice::get_unchecked`.
```

Re-audit if the source, function/callee contracts, Rust version, supported configuration predicate, or any cited 1.82.0 documentation changes.
