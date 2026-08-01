# Unsafe Rust source review

## Claim and verdict

Snapshot: the supplied `lib.rs`, source-reviewed without execution, expansion, tests, dependencies, or generated artifacts. `Supported(c)` means Rust/stdlib exactly 1.82.0, every target where this source and the used items exist, and every ordinary profile. The claim is source-level freedom from Rust UB for every well-typed safe use, in a context satisfying any explicitly published out-of-scope unsafe obligations.

**Combined soundness verdict: UNSOUND** (`CBI-READ`, `CBI-WRITE`). Separately: `local_proof` implementation **PROVED**, with a deficient proof comment; `published_lane` **PROVED** for every valid `Lane` implementation. `High`'s complete published implementer contract is **PROVED**. There are no other documented postconditions. No conditional application claim is made.

TCB log `R058-TCB-1`: no additional assumptions or dependencies. The accepted Rust 1.82.0 axioms are:

- A1: slice `len` “Returns the number of elements in the slice”; `is_empty` “Returns `true` if the slice has a length of 0.” ([`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len), [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty)).
- A2: `get_unchecked` and `get_unchecked_mut` return references without bounds checking, and calling either with an out-of-bounds index is UB even if the reference is unused. ([shared](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked), [mutable](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)).
- A3: `usize` is unsigned (minimum zero), and binary `-` is subtraction; representable subtraction does not overflow. ([integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types), [operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators)).
- A4: an unsafe trait may impose conditions the compiler cannot verify; implementations must be unsafe and uphold its documented conditions. ([unsafe traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits), [`unsafe trait`](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait)).

These propositions apply throughout `Supported(c)`. Re-audit on source/contract changes, any Rust/stdlib or support-set change, or a change to these cited contracts.

## Boundary, invariant, and obligation coverage

All language-reachable surfaces were covered: `Position` and its safe caller implementations; safe `read`/`write`; safe `last`; public `Word` tuple construction/field access; unit construction of `High`; unsafe `Lane`, its associated constants and downstream unsafe impl boundary; the in-scope `unsafe impl` for `High`; and safe generic `published_lane::read`. There are no macros, hidden items, dependencies, FFI, generated APIs, or relevant custom drop/auto-trait behavior.

| ID | Exact obligation | Status |
|---|---|---|
| CBI-READ | Every safe `Position::position()` result used by shared `get_unchecked` is `< bytes.len()` | **UNSOUND** |
| CBI-WRITE | Every safe result used by mutable `get_unchecked_mut` is `< bytes.len()` | **UNSOUND** |
| LOCAL | On the nonempty branch, `bytes.len() - 1` is representable and in bounds | **PROVED**; comment deficient |
| LANE-IMPL | `High::INDEX < 2`; if index is 0/1, `NAME` is respectively `"low"`/`"high"` | **PROVED** |
| LANE-READ | Every valid `L: Lane` has an index in the two-element `Word::0` array | **PROVED** |

The only invariant consumed by `published_lane::read` is `LANE-INDEX`: every valid `Lane` implementation has `INDEX < 2`. It is owned by the unsafe trait boundary. `Word(pub [u32; 2])` needs no value invariant: arbitrary safe field replacement preserves the type-enforced length two.

Configuration closure is parametric. There is no conditional source selection. A1–A4 and the type/constant facts cover all targets in scope. Profile overflow behavior is irrelevant: LOCAL proves no underflow; the callback witnesses and lane proof use 0, 1, and length 2. No configurations were sampled.

## Findings

### CBI-READ / CBI-WRITE — safe callbacks do not establish bounds

Implementation and safe-surface classification: **UNSOUND**; proof artifacts are missing. `Position` is safe and caller-implementable, so its method may return any `usize`. No type, check, privacy boundary, or contract establishes either required inequality.

Two independent entirely safe witnesses are:

```rust
struct P;
impl callback_index::Position for P { fn position(&self) -> usize { 0 } }
let _ = callback_index::read(&[], &P); // shared out-of-bounds call
```

and an implementation returning `1` passed to `write(&mut [0], ..., 7)`. A2 makes each whole execution UB at its respective unchecked call. These UB executions do not establish any defined postcondition refutation.

Smallest requested repair: remove `Position`, accept `position: usize`, and use checked safe indexing while retaining both callable APIs:

```rust
pub fn read(bytes: &[u8], position: usize) -> u8 { bytes[position] }
pub fn write(bytes: &mut [u8], position: usize, value: u8) {
    bytes[position] = value;
}
```

Safe callers still choose every position; out-of-range input panics rather than causing UB. Removing the public trait and changing generic signatures is source-breaking, but the request authorizes abandoning that abstraction. This candidate is **not implemented and not certified**; freshly audit its exact implemented snapshot and specified panic/return behavior.

### LOCAL — correct operation, materially inadequate comment

The existing “This is the fast path” neither states A2's bounds obligation nor supplies a fact. Reconstruction: reaching `else` means `is_empty()` returned false. By A1's implication, contraposition gives `len != 0`. A3 then gives `len >= 1`, so `len - 1` is representable and strictly less than `len`. No call or mutation intervenes. A1 identifies that same `len` as the slice's element count; therefore the index is in bounds and A2 permits the shared unchecked access. Empty slices take the branch with no unsafe operation.

Proposed replacement:

```rust
// SAFETY: This branch establishes `bytes.len() != 0`. Because `len()` is a
// `usize`, `index = bytes.len() - 1` is representable and `index < bytes.len()`.
// No mutation intervenes, so `index` is in bounds for this same slice, as
// `get_unchecked` requires.
```

The current implementation obligation is **PROVED**; the current adjacent proof artifact remains **deficient**.

### LANE — current contract closes; evolution is constrained

`High` sets `(INDEX, NAME)` to `(1, "high")`, satisfying every literal conjunct. For arbitrary downstream `L`, validity of its unsafe impl supplies `INDEX < 2`; the array type supplies length exactly two, so A2's bound holds. `NAME` is not consumed by this function. An incorrect downstream `unsafe impl` violates an out-of-scope unsafe obligation and is not a safe-use counterexample.

Unknown downstream impls are covered parametrically, not presumed absent. Unknown consumers may rely on the published 1.x `NAME` relation, so deleting or weakening it can invalidate their reasoning; strengthening either obligation can invalidate existing impls. Do not “clean up” that clause based only on this repository-visible consumer. Any contract change needs the applicable breaking-change process and a fresh audit; no change is proposed or certified here.

## Residual scope and attestation

Compiler/backend binary correctness and contexts already violating an unsafe obligation are outside the source theorem. No documentation or skill gap was needed. Every in-scope obligation and safe surface has a disposition; no test result or absence of a counterexample supports any verdict.
