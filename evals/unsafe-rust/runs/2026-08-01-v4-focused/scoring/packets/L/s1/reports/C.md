# Unsafe Rust review: `last`

## Claim and verdict

**Implementation soundness: PROVED.** For the exact `lib.rs`, every well-typed safe call to `last` is free of Rust undefined behavior under Rust and standard library 1.82.0 abstract semantics, on every target where this source and the used standard-library items exist, in every ordinary profile. This result is relative only to `TCB-R182-v1` below; there are no additional TCB assumptions.

**Existing proof artifact: DEFICIENT.** The `SAFETY` comment does not establish the actual `get_unchecked` precondition. A material bounds-and-arithmetic derivation had to be reconstructed below. This is a documentation finding, not an implementation defect.

No caller-facing postcondition is documented in the source. The derivation nevertheless establishes the implementation behavior: an empty slice produces `None`; a nonempty slice of length `L` produces `Some` referencing element `L - 1`.

## Snapshot, boundary, and domain

The reviewed artifact is the complete supplied `lib.rs`; no generated artifact, dependency, build script, macro-generated API, FFI, allocator, concurrency mechanism, target feature, or conditional source exists in scope. The only external safe surface is `pub fn last(bytes: &[u8]) -> Option<&u8>`. Its only unsafe obligation site is `bytes.get_unchecked(index)` at `lib.rs:10`. There is no representation invariant or unsafe public contract.

Let `Required(c)` mean: `c` uses this exact source, Rust/stdlib 1.82.0, an eligible target, an ordinary profile, any valid `&[u8]` (all contents, lengths, and lifetimes), and any permitted execution. Its configuration projection is

`Required_cfg = { (Rust 1.82.0, eligible target, ordinary profile) }`,

where “eligible” and “ordinary” retain the request's symbolic predicates. This is an identity normalization of the controlling request: each direction follows by the same conjuncts; no target/profile is enumerated or excluded by the audit.

## Rust 1.82 authority inventory (`TCB-R182-v1`)

Each entry applies to all `Required` cases and is consumed below. Quotations are from the exact versioned page.

- **AX-IF.** [If expressions](https://doc.rust-lang.org/1.82.0/reference/expressions/if-expr.html#if-expressions): “If a condition operand evaluates to `true`, the consequent block is executed and any subsequent `else if` or `else` block is skipped.” Also: “If all `if` and `else if` conditions evaluate to `false` then any `else` block is executed.” Verified proposition: with this single condition, the unsafe-containing `else` is reached only for a false condition.

- **AX-EMPTY.** [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty): “Returns true if the slice has a length of 0.” Verified proposition: length zero implies `is_empty()` is true; contrapositively, a false result implies nonzero length.

- **AX-LEN.** [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len): “Returns the number of elements in the slice.” Its displayed signature returns `usize`. Verified proposition: `bytes.len()` is the element count `L`, represented as `usize`.

- **AX-USIZE.** [Integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types): the unsigned-integer table gives the `usize` row as minimum `0` and maximum `2^ptr_size − 1`. Verified proposition: every `usize`, hence `L`, lies in that inclusive range.

- **AX-SUB.** [Arithmetic binary operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators): the operator table identifies “`-` Subtraction.” Verified proposition: binary `-` computes subtraction subject to the documented overflow rules.

- **AX-OVERFLOW.** [Overflow](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#overflow): “The following things are considered to be overflow: When `+`, `*` or binary `-` create a value greater than the maximum value, or less than the minimum value that can be stored.” Verified proposition: `L - 1` does not overflow when its mathematical result remains in the `usize` range; profile-dependent overflow handling is then irrelevant.

- **AX-GET.** [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked): “Returns a reference to an element or subslice, without doing bounds checking.” Safety: “Calling this method with an out-of-bounds index is undefined behavior even if the resulting reference is not used.” Verified proposition: the caller must supply an in-bounds index; for a permitted call with `usize`, the result is the referenced element under the displayed shared-reference signature.

These are authoritative Rust axioms, not added environmental or implementation assumptions. There are no safe/unsafe dependencies, external specifications, tool results, compiler-backend claims, or pending TCB entries.

## Reconstructed proof and obligation ledger

Let `L` be the element count returned by `bytes.len()` (AX-LEN). Both method calls inspect the same unchanged local slice value; there is no reassignment, callback, or intervening transition.

1. If `bytes.is_empty()` is true, AX-IF selects the consequent, which returns `None`; the unsafe operation is not reached.
2. If the unsafe operation is reached, AX-IF says the condition was false. AX-EMPTY's `L = 0 -> true` gives, by contraposition, `L != 0`.
3. AX-USIZE gives `L >= 0`; together with `L != 0`, this gives `1 <= L`. Therefore the mathematical result `L - 1` lies in `[0, L)` and also in the `usize` range.
4. AX-SUB and AX-OVERFLOW therefore establish that `index = bytes.len() - 1` is exactly that mathematical result without underflow in every ordinary profile. Hence `index < bytes.len()`.
5. Thus `index` is in bounds, discharging AX-GET's sole documented safety requirement. AX-GET returns the element reference, and safe `Some` construction returns it. No raw reference is constructed or lifetime extended by this function; the local and standard-library signatures carry the shared borrow.

The two boolean cases are exhaustive. The proof is parametric in slice contents, lifetime, `usize` width, eligible target, and ordinary profile. There is no `cfg` or generated/source-selection stage, and the one profile-sensitive arithmetic operation cannot overflow. Consequently every `Required` case is covered: `Covered = Required`, which certifies `Required ⊆ Covered`.

## Finding DOC-1: inadequate adjacent proof

The existing comment—“The returned reference cannot outlive `bytes`.”—does not mention `index`, bounds, nonemptiness, or subtraction. Even if its lifetime statement is true, it does not entail the actual AX-GET precondition. Replace it with:

```rust
// SAFETY: This branch is reached only when `bytes.is_empty()` is false.
// Thus `bytes.len() != 0`, so `index = bytes.len() - 1` is representable
// and satisfies `index < bytes.len()`. Therefore `index` is in bounds,
// as required by `get_unchecked`.
```

Minimum resolution is this proof-artifact change; the implementation need not change. Re-audit if the function/control flow, used Rust contracts, Rust version, support predicate, or arithmetic/indexing operation changes. Binary/compiler correctness and behavior not documented by this source remain outside this source-level review.
