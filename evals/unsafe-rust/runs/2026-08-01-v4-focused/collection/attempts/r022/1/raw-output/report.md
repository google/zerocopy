# Audit of `last`

## Claim, snapshot, and verdict

**Soundness: PROVED.** For the supplied `lib.rs`, every well-typed safe call to
`last` under Rust 1.82.0 is free of Rust undefined behavior, on every target on
which this source and the used Rust 1.82.0 standard-library items exist, in
every ordinary profile. This is a source-level result under the documented
Rust 1.82.0 abstract semantics. There are no caller safety preconditions.

**Existing `SAFETY` comment: deficient.** Its lifetime statement is enforced by
the input, callee, and output reference types, but it omits the material
obligation imposed by `get_unchecked`: the index must be in bounds. The missing
argument can be reconstructed completely, so the proof-artifact defect does
not change the implementation verdict.

The reviewed snapshot consists of the supplied `lib.rs` (including
`#![allow(dead_code)]`) and its `REQUEST.md`; no generated artifacts,
dependencies, features, macros, FFI, concurrency, allocation, or prior audit
are involved. Scope is exactly the public safe free function `last` and its one
unsafe operation. No behavior is documented beyond the Rust type signature,
so there is no separate mandatory documented-postcondition claim.

## Boundary, invariant, and obligation ledger

The sole language-reachable surface is safe `pub fn last(bytes: &[u8]) ->
Option<&u8>`. There are no fields, constructors, traits, callbacks, hidden
items, reexports, or generated surfaces in the supplied source. The unsafe
consumer is `bytes.get_unchecked(index)`.

Let `L` be the number of elements in the same slice `bytes`. The temporary
branch invariant `NONEMPTY` is: in the `else` block, `L != 0`. It is established
by `is_empty` plus `if` control flow and remains true through the call: the
binding is immutable and no intervening operation can replace the slice or its
length.

| ID | Required proposition | Derivation | Status |
|---|---|---|---|
| O1 | Empty inputs execute no unsafe operation | `is_empty()` is true exactly at length zero; `if` executes the consequent and skips `else` | PROVED |
| O2 | `bytes.len() - 1` does not underflow in any profile | In `else`, `L != 0`; as a `usize` cardinality, `L >= 1`, so mathematical `L - 1` is representable | PROVED |
| O3 | `index` is in bounds | O2 gives `index = L - 1`, hence `0 <= index < L` for this same slice | PROVED |
| O4 | The unsafe call is UB-free | O3 discharges `get_unchecked`'s out-of-bounds prohibition | PROVED |
| O5 | The returned reference cannot be used beyond `bytes` | The inspected method signature returns a shared reference from `&self`; the inspected function signature carries that borrow through `Option`. This is compiler-enforced, not a caller obligation | PROVED |

On a nonempty slice the call therefore returns the reference to element
`L - 1`; on an empty slice it returns `None`. This observation is not promoted
to a separately documented contract.

## Material reconstructed proof

1. `bytes.is_empty()` is true iff `bytes` has length zero. The Reference says
   that when an `if` condition is false, its consequent is skipped and the
   `else` block executes. Therefore reaching this `else` proves `L != 0`.
2. `len()` returns the number of slice elements as `usize`. Thus `L >= 1` on
   this branch. Primitive binary `-` is subtraction, and `L - 1` remains inside
   the `usize` range; the overflow condition is false. Consequently the result
   is identical in all ordinary overflow-check/profile settings.
3. The resulting `index = L - 1` satisfies `index < L`, so it is in bounds.
   The exact `get_unchecked` UB condition is therefore false. Its return is a
   shared reference borrowed from this slice, as its signature records.

Suggested replacement text:

```rust
// SAFETY: This is the `else` branch of `bytes.is_empty()`, so
// `bytes.len() > 0`. Thus `bytes.len() - 1` cannot underflow, and
// `index == bytes.len() - 1 < bytes.len()`, making `index` in bounds
// for this same slice as required by `get_unchecked`.
```

## Exact Rust 1.82.0 premise inventory

These are all Rust/standard-library propositions materially consumed above.
Each URL is version-matched to 1.82.0; no later-documentation compatibility
premise is used.

- **AXIOM-GET.** [`slice::get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked): “Returns a reference to an element or subslice, without doing bounds checking.” “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” Verified proposition: the call returns the selected borrowed element reference, and an out-of-bounds index is forbidden on pain of UB. Consumers: O3–O5.

- **AXIOM-LEN.** [`slice::len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len): “Returns the number of elements in the slice.” The displayed signature returns `usize`. Verified proposition: both calls on unchanged `bytes` observe its element count `L` as `usize`. Consumers: O2–O3.

- **AXIOM-EMPTY.** [`slice::is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty): “Returns `true` if the slice has a length of 0.” Verified proposition: false implies `L != 0`. Consumers: O1–O2.

- **AXIOM-IF.** [If expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions): “If a condition operand evaluates to `true`, the consequent block is executed and any subsequent `else if` or `else` block is skipped.” It also states: “If a condition operand evaluates to `false`, the consequent block is skipped”. Verified proposition: only a false `is_empty()` result reaches this `else`. Consumers: O1–O2.

- **AXIOM-USIZE.** [Integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types), unsigned-integer table: `usize` has minimum `0` and maximum `2^ptr_bits - 1`. Verified proposition: a nonzero `usize` count is at least one and `L - 1` is representable. Consumer: O2.

- **AXIOM-SUB.** [Arithmetic and logical binary operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators), primitive-operator table: binary `-` is “Subtraction”. Verified proposition: the expression computes mathematical subtraction when representable. Consumer: O2.

- **AXIOM-OVERFLOW.** [Overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow): overflow includes when binary `-` creates “a value greater than the maximum value, or less than the minimum value that can be stored.” Verified proposition: because `0 <= L - 1 < L <= usize::MAX`, this subtraction does not overflow, independent of ordinary profile overflow behavior. Consumer: O2.

The derivation consumes no unlisted Rust proposition requiring an external
semantic premise. Ordinary logic/arithmetic and facts directly visible in the
inspected, well-typed source are local proof steps.

## Domain closure, TCB, and finding

`Required = {Rust 1.82.0} × {targets where this exact source and the named
1.82.0 items exist} × {ordinary profiles}`. `Covered` is the same predicate:
the proof is parametric in target and profile, uses no target-dependent layout
or conditional source, and establishes that overflow never occurs. Hence
`Required ⊆ Covered`. There are no exclusions or unresolved configurations.

TCB log `TCB-LAST-1` contains exactly AXIOM-GET, AXIOM-LEN, AXIOM-EMPTY,
AXIOM-IF, AXIOM-USIZE, AXIOM-SUB, and AXIOM-OVERFLOW, all verified against the
named Rust 1.82.0 normative pages and accepted as the requested Rust abstract
semantics. There are no additional assumptions, safe/unsafe dependencies,
external specifications, implementation claims, or tool-derived results.

**Finding DOC-1 (proof artifact, implementation still PROVED):** the current
comment states no fact implying `index < bytes.len()` and does not even name
the callee's controlling safety condition. Resolution is the replacement text
above; no API or implementation change is required. Re-audit on source/comment
changes, support-domain changes, or material changes to any consumed Rust
1.82.0 contract.
