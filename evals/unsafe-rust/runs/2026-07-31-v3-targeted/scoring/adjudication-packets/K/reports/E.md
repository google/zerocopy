# Focused unsafe-Rust audit

## Claim, snapshot, and verdict

Snapshot: the supplied 53-line `target/lib.rs`, including `callback_index`,
`local_proof`, and `published_lane`. No generated code, dependencies, build
scripts, FFI, assembly, allocators, concurrency, or prior audit is present.
Review was source-only; nothing was built, executed, expanded, or modified.

Claim: under Rust/stdlib 1.82.0, on every target where this source and the used
stdlib items exist, in every ordinary profile, every well-typed safe use and
every unsafe-trait use satisfying its published safety contract is free of
Rust UB; additionally, every in-scope unsafe contract clause holds.

**Combined verdict: UNSOUND (F-1).** Component results:

- `callback_index::{read,write}`: **UNSOUND**, independently.
- `local_proof::last`: implementation **PROVED**; existing `SAFETY` comment
  deficient (F-2).
- `published_lane::High`'s unsafe impl and `published_lane::read`:
  implementation **PROVED** for every valid `Lane` implementation; local proof
  artifacts deficient (F-3).
- Documented contract clauses: **PROVED** for the in-scope `High` impl. There
  are no documented unsafe-function postconditions. No
  `CONTRACT-BROKEN` witness is claimed.

The TCB is `TCB-R1`: only the Rust 1.82 authoritative axioms cited below; there
are no additional assumptions, dependencies, tool theorems, or conditional
application claims.

## Boundary, contracts, and configuration closure

Safe surfaces exhaustively covered: the caller-implementable `Position` trait
and its safe `position` method; safe `read` and `write`; safe `last`; `Word`'s
public tuple constructor/field; `High`'s unit constructor; `Lane`'s associated
constants as exposed through an unsafe implementation boundary; and safe
`published_lane::read`. Unsafe surfaces are `Lane`, downstream `unsafe impl
Lane` declarations, and the in-scope `unsafe impl Lane for High`. There are no
macros, reexports, hidden APIs, custom trait behavior, or invariant-relevant
drop operations.

`Position` carries no bounds invariant. `Word` needs no abstraction invariant:
its public field always has type `[u32; 2]`. Contract `LANE-1`, owned by the
unsafe trait boundary, requires for every valid impl: `INDEX < 2`, plus
`NAME == "low"` when index 0 and `NAME == "high"` when index 1. Each generic
consumer may rely on that published contract.

Configuration coverage is parametric. The counterexamples use an empty slice
and index zero and therefore apply on every included target/profile. The proved
paths use only slice length, a fixed two-element array, and representable
`usize` subtraction after proving non-emptiness; pointer width, optimization,
overflow checks, and panic strategy do not alter the arguments. There is no
conditional compilation or generated artifact to partition.

## Obligation ledger and proofs

| ID | Site | Required proposition | Result |
|---|---|---|---|
| O-1 | callback `read` | callback result is in bounds before `get_unchecked` | false; F-1 |
| O-2 | callback `write` | callback result is in bounds before `get_unchecked_mut` | false; F-1 |
| O-3 | `last` | `len - 1 < len` and subtraction is representable | proved; F-2 |
| O-4 | `High` impl | both clauses of `LANE-1` | proved: `1 < 2`, name is `"high"` |
| O-5 | lane `read` | `L::INDEX < word.0.len()` | proved from `LANE-1` and array length 2; F-3 |

Rust 1.82 documents that an out-of-bounds call to
[`get_unchecked`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked)
or
[`get_unchecked_mut`](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.get_unchecked_mut)
is UB even if the resulting reference is unused. The remaining authoritative
premises are: [`len` returns the number of slice elements](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.len),
[`is_empty` means length zero](https://doc.rust-lang.org/1.82.0/std/primitive.slice.html#method.is_empty),
the Rust 1.82 [unsigned-integer domain](https://doc.rust-lang.org/1.82.0/reference/types/numeric.html#integer-types)
and [integer arithmetic rules](https://doc.rust-lang.org/1.82.0/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators),
and the rule that an unsafe trait may impose obligations which an
[`unsafe impl` must uphold](https://doc.rust-lang.org/1.82.0/reference/items/traits.html#unsafe-traits).
These are accepted AXIOM entries in `TCB-R1`, consumed by O-1 through O-5;
changing Rust version or any cited contract triggers re-audit.

For O-3, the `else` branch establishes `!bytes.is_empty()`, hence
`bytes.len() > 0`. Because length has type `usize`, subtracting one is
representable; `index = len - 1` therefore satisfies `index < len`. No call or
state transition intervenes. This exactly discharges `get_unchecked(index)`'s
bounds condition; the shared borrow keeps the initialized `u8` element alive
through the dereference. Thus empty input returns `None`, and nonempty input
returns its last element without UB.

For O-5, a valid `L: Lane` supplies `L::INDEX < 2`; `word.0` has exactly two
initialized `u32` elements by its type. Therefore the index is in bounds for
`get_unchecked`. `&Word` keeps the element alive and shared through the read.
O-4 establishes that the selected in-scope provider `High` is valid. Unknown
downstream implementations are not assumed correct: an implementation that
breaks `LANE-1` violates its caller-side unsafe obligation. The generic proof
covers every downstream implementation that does satisfy it.

## Findings and repairs

### F-1 — Safe caller controls an unchecked index (UNSOUND)

Safe code can define `struct P; impl Position for P { fn position(&self) ->
usize { 0 } }`. Calling `read(&[], &P)` is well-typed safe use and invokes
`get_unchecked(0)` on a length-zero slice. Independently, passing a mutable
empty slice to `write(..., &P, value)` invokes `get_unchecked_mut(0)`. Each
complete execution reaches the documented UB; no hidden caller obligation can
be added to a safe API.

Smallest repair: replace both unchecked expressions with checked slice
indexing, preserving signatures and caller-selected positions:

```rust
bytes[position.position()]
bytes[position.position()] = value;
```

Out-of-range positions then panic rather than cause UB. Since `Position` need
not be preserved, a later cleanup may accept `usize` directly, but that is a
larger, source-breaking change and is unnecessary for soundness. Neither
proposal is certified: implement it, document panic behavior as desired, and
freshly audit the new snapshot.

### F-2 — `last` proof comment is materially inadequate

“This is the fast path” states neither the unsafe operation's precondition nor
the derivation above. Implementation correctness is nevertheless proved by
O-3. Proposed adjacent replacement:

```rust
// SAFETY: This branch establishes that `bytes.len() > 0`. Therefore
// `index = bytes.len() - 1` is representable and `index < bytes.len()`,
// exactly the bound required by `get_unchecked`.
```

### F-3 — Lane implementation proofs are absent

The published contract is sufficient and the code satisfies it, but neither
the unsafe impl nor unchecked call records the proof. Add, without changing the
contract, comments equivalent to:

```rust
// SAFETY: INDEX is 1 (< 2), and NAME is "high" as required for index 1.
unsafe impl Lane for High { /* unchanged */ }

// SAFETY: Every valid Lane impl guarantees L::INDEX < 2, and word.0 is
// [u32; 2], so the index is in bounds for get_unchecked.
```

Because this is a published 1.x unsafe-trait contract with unknown impls and
consumers, do not strengthen implementer obligations or weaken/remove the
`NAME` guarantee merely because the visible consumer uses only `INDEX`; either
change can break downstream safety reasoning. Comment-only proof repair leaves
the contract unchanged. Any contract change requires compatibility handling
and a fresh audit.

## Residual scope and attestation

Downstream `Lane` implementations and consumers are not individually audited;
the result is deliberately parametric over contract-satisfying impls, and no
repository-visible inventory is treated as exhaustive. No tool-derived or test
evidence was used. Every in-scope unsafe operation, provider, safe boundary,
contract clause, target/profile class, and material reconstructed proof has a
disposition above. Re-audit on source or contract edits, Rust/stdlib or support
changes, new generated/configured code, or discovery of another consumer
obligation.
