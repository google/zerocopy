# Unsafe Rust Audit: `last`

## Claim and verdict

**Soundness: PROVED.** For the exact supplied `lib.rs`, Rust and standard
library 1.82.0, every target on which this source and the used standard-library
items exist, every ordinary profile, every valid `&[u8]`, and every permitted
source-level execution, every well-typed safe call to `last` is free of Rust
undefined behavior. There is no caller-side safety precondition. This result is
relative only to the Rust 1.82.0 authorities in TCB-R1 below; it adds no TCB
assumption.

**Existing `SAFETY` comment: DEFICIENT.** Its lifetime statement does not
establish the `get_unchecked` call's material requirement that `index` be in
bounds. Reconstructing that missing argument is necessary to reach the
implementation verdict. This is a proof-artifact defect, not an implementation
defect.

There is no documented postcondition on `last`, so no separate mandatory
postcondition verdict applies. In particular, the name `last` is not treated as
normative documentation.

## Snapshot, domain, and boundary

- Snapshot: the complete supplied `lib.rs`, lines 1--11; no generated source,
  dependencies, features, `cfg`, macros, FFI, assembly, build scripts, or prior
  audit are present in the supplied target.
- Surface inventory: one public safe free function,
  `pub fn last(bytes: &[u8]) -> Option<&u8>`. There are no representation
  fields, constructors, traits, methods, callbacks, hidden items, statics, or
  invariant-bearing state. The sole unsafe site is
  `bytes.get_unchecked(index)` at line 9.
- Let `Required(b,t,p,e)` mean: this exact source; Rust/std 1.82.0; `b` is any
  valid `&[u8]`; `t` is any target where the source and used items exist; `p` is
  any ordinary profile; and `e` is any permitted execution. This is exactly the
  request's controlling expression, so the normalization is equality in both
  directions. `Required_cfg(t,p) = target_exists(t) && ordinary_profile(p)`.
  There is no policy conflict, exclusion, or unresolved domain.
- Actual axes are slice length, target-dependent `usize` width, and arithmetic
  overflow-check configuration. The proof below is parametric in all three.
  Optimization, debug assertions, and panic strategy do not alter any consumed
  proposition. No build or generation pipeline selects another artifact.

## Obligation ledger and reconstructed proof

**O1 -- branch closure.** Partition executions by the branch actually selected
at lines 4--10. Rust's `if` semantics makes the two source paths exhaustive. If
the consequent executes, line 5 returns `None` and the unsafe operation is not
reached. If the `else` executes, `bytes.is_empty()` evaluated false.

**O2 -- arithmetic.** Put `n = bytes.len()` on the `else` path. AX-EMPTY says
that length zero would make `is_empty()` true; by contraposition, the observed
false result gives `n != 0`. AX-USIZE makes `n` an unsigned integer, hence
`n > 0`. Integer `-` is subtraction (AX-SUB), so line 7 computes
`index = n - 1`. Mathematically `0 <= n - 1 < n`; the result is neither below
the type minimum nor above its maximum, so AX-OVERFLOW shows that this
subtraction does not overflow. Thus this result and the absence of an
arithmetic panic are identical with overflow checks enabled or disabled.

**O3 -- unsafe call.** AX-LEN identifies `n` as the number of slice elements.
Consequently the integer index `n - 1`, with `n > 0`, is in the slice's index
range. AX-GET says an out-of-bounds call is UB and that the method returns a
reference to the selected element; O2 proves the excluded condition false.
The call therefore satisfies its safety contract and returns the in-bounds
`&u8` used to construct `Some`. There is no later mutation, callback,
interference, unwind point, or unsafe consumer.

For every `Required` case, O1 selects a covered path; the consequent path has no
unsafe operation, while O2--O3 cover every alternative path for every target
`usize` width and profile. Hence each obligation's covered domain contains
`Required`; their pointwise intersection does too. This is the
`Required ⊆ Covered` certificate for the verdict.

## Rust/std authority inventory (TCB-R1)

All entries are Rust 1.82.0 AXIOMs, checked at the linked versioned sections,
accepted as the request-authorized Rust authority, and applicable to every
`Required` target where the item exists. There are no dependencies, tools, or
additional admitted propositions.

- **AX-LEN.** [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len):
  “number of elements in the slice”. Verified proposition: `bytes.len()` is the
  slice's element count and has the shown return type `usize`. Consumers: O2,
  O3.
- **AX-EMPTY.** [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty):
  “`true` if the slice has a length of 0”. Verified proposition: if the element
  count is zero, this call returns true. Consumer: O2.
- **AX-IF.** [If expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions):
  “condition operand evaluates to `true`, the consequent block is executed”;
  “conditions evaluate to `false` then any `else` block is executed”. Verified
  proposition: for this one-condition `if`/`else`, the condition selects the
  consequent when true and the `else` when false. Consumer: O1.
- **AX-USIZE.** [Integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types):
  “The `usize` type is an unsigned integer type”. Verified proposition:
  `n: usize` is nonnegative and lies in that type's representable integer
  range, for every supported pointer width. Consumer: O2.
- **AX-SUB.** [Arithmetic operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators):
  the integer `-` table entry is “Subtraction”. Verified proposition: the
  built-in operation on these `usize` operands is integer subtraction.
  Consumer: O2.
- **AX-OVERFLOW.** [Overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow):
  “binary `-` create a value greater than the maximum value, or less than the
  minimum value that can be stored” is overflow. Verified proposition: a
  subtraction whose mathematical result remains in the `usize` range does not
  overflow. Consumer: O2.
- **AX-GET.** [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked):
  “reference to an element”; “out-of-bounds index is undefined behavior”.
  Verified proposition: the `usize` call returns a reference to the indexed
  element without a bounds check, and the caller must exclude an out-of-bounds
  index. Consumer: O3.

This inventory exactly matches the semantic leaves used above. The remaining
steps are inspected source syntax, contraposition, integer inequalities, and
set inclusion; no uncited Rust/std proposition or tool result supplies a
material inference.

## Finding PA-1 -- inadequate local proof

- **Affected artifact:** line 8's comment; implementation status **PROVED**,
  proof-artifact status **deficient**.
- **Defect:** “The returned reference cannot outlive `bytes`” neither states
  nor derives `index < bytes.len()`, the precondition consumed at line 9. It is
  not a substitute for O1--O3.
- **Required resolution:** replace the comment with locally reviewable bounds
  reasoning. No caller contract or code change is needed.

Proposed replacement text:

```rust
// SAFETY: This branch is reached only when `bytes.is_empty()` is false.
// A zero-length slice makes `is_empty()` true, so `bytes.len() > 0` here.
// Therefore `index = bytes.len() - 1` cannot underflow and satisfies
// `index < bytes.len()`, as required by `get_unchecked`.
```

## Evidence, residual scope, and review triggers

No build, test, execution, macro expansion, or tool-derived evidence was used.
This is a source-level Rust abstract-semantics result, not a claim about a
particular compiler backend, binary, platform implementation, undocumented
behavior, performance, or panic freedom outside the proved subtraction.
Re-audit if the source/comment, function or std contracts, Rust version,
supported domain, or any presently absent configuration/generation/dependency
mechanism changes.

**Final attestation:** every in-scope surface and unsafe obligation has a
status; the material reconstruction and proof-artifact defect are explicit;
the authority inventory is reconciled to the derivation; and no conclusion
rests on testing or absence of a counterexample.
