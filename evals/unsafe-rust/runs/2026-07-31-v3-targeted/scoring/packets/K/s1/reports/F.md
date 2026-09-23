# Focused unsafe-Rust audit

## Claim, snapshot, and verdict

Artifact: the exact supplied `lib.rs`. Scope: all public and unsafe surfaces in
`callback_index`, `local_proof`, and `published_lane`. `Supported(c)` means Rust
and standard library 1.82.0, every target where this source and its used 1.82.0
items exist, and every ordinary profile. There are no dependencies, `cfg`s,
macros, generated artifacts, FFI, concurrency, or build-time inputs in the
supplied artifact. No target was built, run, expanded, or tested.

The theorem is freedom from Rust UB for every well-typed safe call and every
unsafe-trait implementation satisfying its published safety contract, plus the
literal `Lane` implementer contract. TCB `TCB-R182-1` consists only of the
verified Rust 1.82 normative axioms listed below; there are no additional
assumptions.

**Combined soundness verdict: UNSOUND**, because both safe `callback_index`
operations admit UB. Separately: `local_proof::last` implementation **PROVED**;
its existing proof comment is deficient. `published_lane` implementation and
its mandatory `Lane` clauses are **PROVED**. There are no other documented
postconditions in the source. Proposed repairs below are **uncertified** until
implemented as a new snapshot and freshly audited.

## Authority / compact TCB log

All entries apply exactly to Rust/std 1.82.0 over `Supported(c)`, are accepted
as authoritative, and must be rechecked if the version or cited text changes.

- **A-SLICE:** [`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked)
  and [`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)
  require the supplied index to be in bounds; an out-of-bounds index is UB even
  if the resulting reference is unused. Consumers: CB-R, CB-W, LP-GET, PL-READ.
- **A-LENGTH:** [`len`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len)
  returns the element count, and [`is_empty`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty)
  is true exactly when that count is zero. Consumers: LP-SUB, LP-GET.
- **A-INTEGER:** the Reference defines integer subtraction and its overflow
  cases ([operators](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators));
  `usize` is an unsigned target-width integer
  ([integer types](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types)).
  Thus for a representable `n > 0`, `n - 1` is representable and less than
  `n`. Consumer: LP-SUB.
- **A-UNSAFE-TRAIT:** unsafe traits may impose compiler-unchecked implementer
  obligations and require unsafe implementation
  ([traits](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits),
  [`unsafe` keyword](https://doc.rust-lang.org/1.82.0/reference/unsafe-keyword.html#unsafe-traits-unsafe-trait)).
  Consumer: PL-IMPL and the quantification of PL-READ.

No tool-derived evidence or non-authoritative TCB entries were used.

## Boundary, invariant, and obligation coverage

| ID | Surface / obligation | Disposition |
|---|---|---|
| CB-P | Safe, downstream-implementable `Position::position -> usize` | No contract or type constraint relates its result to any slice. Safe implementations may return every `usize`. |
| CB-R | Safe `read`; unchecked shared access | **UNSOUND**: required `position() < bytes.len()` is not established. |
| CB-W | Safe `write`; unchecked mutable access | **UNSOUND**: the same missing bound. |
| LP | Safe `last`; subtraction and unchecked access | **PROVED** by the reconstruction below. |
| PL-W | Public `Word(pub [u32; 2])`, including literal construction and field read/write | **PROVED**: every field value has the fixed two-element representation; no hidden invariant exists. |
| PL-L | Public unsafe `Lane`, constants, and downstream unsafe impl boundary | Contract is exactly `INDEX < 2` and the stated `NAME` mapping; both clauses remain live. |
| PL-I | Public `High` and `unsafe impl Lane for High` | **PROVED**: `1 < 2`, and at index 1 the supplied name is exactly `"high"`. |
| PL-R | Safe generic `read<L: Lane>` and unchecked access | **PROVED** for every valid `L`: PL-L gives `L::INDEX < 2`; `word.0` has length 2, so A-SLICE is satisfied. |

The only safety-relevant cross-boundary invariant is **LANE-1**: throughout
use of a valid `Lane` implementation, `INDEX < 2`, and `NAME` equals `"low"`
for index 0 or `"high"` for index 1. Its owner is the unsafe implementation
boundary; implementations produce it and generic consumers may consume both
clauses. `High` establishes it syntactically. Unknown downstream unsafe impls
are quantified by, not silently trusted by, this theorem: an impl violating
LANE-1 fails its explicit out-of-scope unsafe obligation.

Configuration closure is parametric. The CB witnesses use index 0 and an empty
slice on every target. LP uses only `len > 0`, making overflow checks and
profile irrelevant. PL uses the type-level array length 2 and indices 0/1.
Panic strategy and optimization do not change these arguments. There are no
uncovered supported configurations.

## Findings and repairs

### F-CB — safe callers reach out-of-bounds unchecked access

**Status: UNSOUND** for both CB-R and CB-W; proof artifacts are missing and no
proof can exist for the current bodies. A valid all-safe witness implements
`Position` with `position() == 0`, then calls `read(&[], &p)`. The index is out
of bounds, so A-SLICE establishes UB. Independently, `let mut x = []; write(&mut
x, &p, 1)` reaches the mutable form of the same UB. These whole executions need
no caller `unsafe`. No documented-postcondition verdict is inferred from these
UB-containing executions.

Smallest proof-oriented repair, given that `Position` need not survive: remove
the trait and accept the chosen `usize` directly, using checked safe indexing:

```rust
pub fn read(bytes: &[u8], position: usize) -> u8 { bytes[position] }
pub fn write(bytes: &mut [u8], position: usize, value: u8) {
    bytes[position] = value;
}
```

Both operations remain callable by safe callers with caller-chosen positions;
an out-of-range position follows the safe indexing API's defined failure path
rather than forming an invalid reference. This removes the unsupported premise,
callback surface, and unsafe blocks. It changes the public signatures and
removes a public trait, so migration is source-breaking; the request expressly
does not require preserving that abstraction. This sketch is not certified.

### F-LP-DOC — correct code, non-proof `SAFETY` comment

**Implementation: PROVED. Proof artifact: deficient.** On the `else` branch,
A-LENGTH and `!bytes.is_empty()` give `n = bytes.len() > 0`. A-INTEGER gives a
defined `index = n - 1` with `index < n`. A-SLICE's sole relevant `usize`
index obligation is therefore met; dereferencing yields the initialized `u8`
last element. The empty branch performs no unsafe operation and returns `None`.
This covers every slice and profile on every supported target.

“This is the fast path” states neither the operation's obligation nor any fact
implying it. Replace it with:

```rust
// SAFETY: This branch establishes `!bytes.is_empty()`, so `bytes.len() > 0`.
// Hence `index = bytes.len() - 1` is representable and `index < bytes.len()`,
// satisfying `get_unchecked`'s in-bounds requirement.
```

### F-PL-DOC/COMPAT — preserve the full published unsafe-trait contract

The implementation is proved, but the two unsafe sites lack adjacent proof
artifacts. Suggested comments are: before the impl, “SAFETY: `INDEX` is 1,
which is less than 2, and its `NAME` is `"high"`”; before `get_unchecked`,
“SAFETY: every valid `L: Lane` guarantees `L::INDEX < 2`, and `word.0` has
length 2.”

`NAME` is not consumed by this repository-visible `read`, but it remains a
mandatory published 1.x implementer obligation and a guarantee available to
unknown generic consumers. It must not be silently weakened, removed, or
reinterpreted based on the visible consumer inventory; strengthening either
implementer clause could likewise invalidate unknown existing impls. Any
contract change requires an explicit breaking-version/migration decision and
fresh audits of implementations and consumers. No source repair is required
for current soundness.

## Residual scope and review triggers

Excluded: compiler-backend/binary correctness and any source, implementation,
consumer, or configuration not supplied. Re-audit on any source or safety-text
change; Rust/std or support-domain change; addition of cfg/generated code; or
implementation of either proposed proof/comment repair. No current-artifact
verdict transfers to a repaired snapshot.
