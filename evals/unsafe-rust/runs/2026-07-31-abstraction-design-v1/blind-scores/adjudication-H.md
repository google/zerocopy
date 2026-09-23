# Semantic adjudication — H tradeoff

## Decision

For the exact H fixture, **the current raw loop is UNSOUND for the stated
Rust 1.70+ support set**. Rust 1.70 is in that set, and its exact documented
`pointer::add` contract admits a valid empty-slice counterexample. This is not a
mere absence of proof. The nonempty loop has a substantially reconstructible
proof, but that does not repair the empty execution; one valid UB execution is
enough.

This adjudication preserves all blind raw scores. It recommends a semantic
overlay correcting the H1 assumptions; H2–H5 and the missing-performance-evidence
judgments are not changed.

## 1. Empty slice and `add(0)`

Rust 1.70 [`pointer::add`](https://doc.rust-lang.org/1.70.0/std/primitive.pointer.html#method.add)
states that “Both the starting and resulting pointer” must be in bounds or
one-past the same allocated object. Its three listed requirements have **no
zero-offset exception**, and violating one is documented as UB.

Rust 1.70 [`slice::from_raw_parts`](https://doc.rust-lang.org/1.70.0/std/slice/fn.from_raw_parts.html#safety)
expressly permits a non-null, aligned dangling pointer for a zero-length slice
and points to `NonNull::dangling` as “usable as data for zero-length slices.”
[`NonNull::dangling`](https://doc.rust-lang.org/1.70.0/std/ptr/struct.NonNull.html#method.dangling)
is documented as “dangling, but well-aligned.” Therefore this is a valid
witness:

```rust
let p = std::ptr::NonNull::<u32>::dangling().as_ptr();
let s = unsafe { std::slice::from_raw_parts(p, 0) }; // contract satisfied
let _ = total(s);                                   // safe call
```

`total` evaluates `ptr.add(0)` before testing `ptr != end`. The offset and
integer-wrap clauses hold, but the dangling pointer is not in or one-past any
allocated object, so the first 1.70 `add` clause fails. Skipping the loop body
does not undo UB already reached while constructing `end`.

Rust 1.97.1 now conditions allocation/range requirements on
“If the computed offset is non-zero”
([exact later page](https://doc.rust-lang.org/1.97.1/std/primitive.pointer.html#method.add)).
That later wording does not say it applies historically. Under the frozen
skill's version rules, it cannot be projected backward to Rust 1.70 without an
explicit historical/TCB premise. A stability badge is insufficient.

## 2. Slice byte length

The opposite disputed point is directly resolved in favor of the positive
proof. Rust 1.70's Reference says slices point to their entire dynamic range and
that a Rust value's dynamic size “must never exceed `isize::MAX`”
([Dangling pointers](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html#dangling-pointers)).
Thus, for valid `values: &[u32]`,

```text
values.len() * size_of::<u32>() <= isize::MAX.
```

This is a general valid-slice premise, not an inference limited to slices that
happen to originate in `Vec` or `Box`. `from_raw_parts` independently repeats
the same size requirement for that constructor. Accordingly, `r047`'s claimed
smallest missing `isize` implication is not missing. Reports should cite the
Reference for the general type-validity fact rather than promote the
`from_raw_parts` caller contract alone into a universal slice invariant.

## 3. End, loop, and dereference ledger

Let `base = values.as_ptr()`, `n = values.len()`, and at iteration `i` maintain
`ptr = base.add(i)`, `0 <= i <= n`, with `acc` the wrapping sum of `values[..i]`.
For `n > 0`:

- The byte-offset-isize obligation for `base.add(n)` follows from the Reference
  bound above. Slice validity/liveness puts all `n` aligned, valid `u32`
  elements in one live allocation; the end is within that allocation or
  one-past it.
- The distinct, non-wrapping offsets of non-ZST `u32` make `ptr != end` imply
  `i < n`. The live shared slice then supplies alignment, initialization,
  readability, and same-allocation provenance for `*ptr`. Rust 1.70 lists
  dereferencing a dangling or unaligned raw pointer as UB
  ([Reference](https://doc.rust-lang.org/1.70.0/reference/behavior-considered-undefined.html)).
- From `i < n`, advancing by one stays on an element or reaches the endpoint;
  it establishes the invariant for `i + 1`. Explicit `wrapping_add` proves the
  required modulo-`2^32` behavior in every ordinary profile.

Every `add` also has the separate 1.70 requirement that its infinite-precision
address sum fit `usize`. The inspected 1.70 general slice-validity text supplies
the byte-size bound but does not literally state that a slice's one-past address
is representable without address-space wrap. Reports asserting that this
follows automatically need to show the derivation or record the smallest extra
premise. This residual nonempty-region issue is unnecessary to the overall
`UNSOUND` verdict, which is already established by the empty witness.

## Report-by-report H1 corrections

| Report | Adjudicated correction |
|---|---|
| `r043` | Change current `PROVED` to `UNSOUND`. “Offset is zero” does not discharge the 1.70 same-allocation clause. Its iterator/performance recommendation remains sound. |
| `r044` | Change current `PROVED` to `UNSOUND` for the same reason. Retain its proof-documentation and benchmark findings. |
| `r045` | Retain `UNSOUND`; this report supplies the decisive valid empty-slice witness and should not be penalized as a false positive. Its nonempty sketch should additionally expose the address-wrap clause. |
| `r046` | Change current `PROVED` to `UNSOUND`. Its statement that Rust allocations cannot exceed `isize::MAX` is not the applicable 1.70 rule; the Reference caps the dynamic Rust value, while 1.70 `add` expressly warns some direct/mapped allocations may be larger. |
| `r047` | Change current `UNPROVED` to `UNSOUND` because it missed the empty witness. Also mark its alleged slice-byte-size gap resolved by the 1.70 Reference; retain only any distinct address-wrap gap. |
| `r048` | Change current `PROVED` to `UNSOUND`. `add(0)` not moving the address does not satisfy the old allocation-origin clause. Its later-release compatibility caveat and performance result remain useful. |

Any blind scoring assumption that treated `r043`, `r044`, `r046`, or `r048` as
H1-correct and `r045` as incorrectly alarmist should be reversed in the
adjudicated layer. `r047` deserves credit for fail-closed reasoning, but not for
identifying the right missing premise or final verdict. Do not overwrite the raw
numeric scores; record these as evaluator corrections. H1's wording—do not
condemn the loop *without a failed proof*—is compatible with this result because
`r045` supplies a failed proof and concrete valid-use witness.

## Correct next action

The safe `iter().copied().fold(0, u32::wrapping_add)` candidate remains the
preferred proof-surface reduction, but its designated-benchmark regression is
still **UNPROVED**. Benchmark that exact candidate before adoption. If the hard
2% gate rejects safe forms, any raw fallback must at minimum avoid calling
`add` on the empty dangling pointer and must locally discharge every
same-allocation, byte-offset, no-address-wrap, dereference, and progression
obligation. It then requires a fresh exact-source audit; the present loop is not
a sound fallback for the declared MSRV.
