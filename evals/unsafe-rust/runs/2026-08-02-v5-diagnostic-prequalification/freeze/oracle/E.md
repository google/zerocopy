# V5 Diagnostic Oracle — E: Semantic Proof Kernels

> **DRAFT / evaluator-only.** Do not expose this answer key, its atom IDs,
> expected verdicts, defect rules, or authority inventory to a report agent.

## Scoring contract

Score the direct propositions in `../atoms/E.json`, not wording, notation, or
organization. Apply only IDs in `../rules/defect-rules.json`. An omitted atom
is a direct failure, not automatically a hard error. Equivalent source facts,
logical derivations, and compact shared authority inventories are accepted.

E is controlled and deliberately asks for proof kernels. An endpoint answer
without the material Rust-semantic bridges does not pass the corresponding
atom. `CONFIG-MAP` supplies only the stated feature/target cfg mapping; it is
not Rust authority and does not prove source correctness.

## Exact results

The full domain is Rust 1.83.0, both listed targets, both `wide` states, every
Cargo profile, both debug-assertion states, and every valid input to each API.

### `record`

The omitted output type is `()`. Its reached function-body tail is the match;
the `true` and `false` literal patterns exhaust `bool`, and the first matching
arm runs. The assignments use contextually typed `u8` values. Thus:

```text
record(true, out)  normally stores 7, returns ()
record(false, out) normally stores 9, returns ()
```

The implementation and its documented postcondition are **PROVED** over the
full domain. The unit conclusion requires both the omitted-output and
function-body/block semantics; inspecting the absence of `->` or `return`
alone is not the semantic proof.

### `last_or`

On `bytes.len() == 0`, the consequent returns `fallback`. On the else path,
the equality is false, so `len != 0`. `len` is a `usize`; therefore `len > 0`.
The unsuffixed `1` in `len - 1` is uniquely inferred as `usize` and denotes
one. Hence the subtraction is representable in every profile and pointer
width, and `index = len - 1 < len`. This is the exact element-index obligation
for `get_unchecked`; its output reference is tied to the input borrow and is
dereferenced before returning the copied byte.

`last_or` implementation soundness and its stated return postcondition are
**PROVED** over the full domain.

### `boundary_or`

The empty branch returns `fallback`. For every nonempty input, the else branch
sets `index = len`; the context/type and lifetime facts do not alter that
`index < len` is false. A valid safe call such as
`boundary_or(&[5], 0)` reaches `get_unchecked(1)` on length 1. Rust 1.83 states
that an out-of-bounds call is UB even if the resulting reference is unused.

Therefore the safe API is **UNSOUND**. Its whole-domain documented return
postcondition is **UNPROVED**, not a defined-behavior counterexample theorem:
the nonempty witness contains UB. The empty regional result remains proved.

### `configured_lane`

Relative only to exact `CONFIG-MAP`:

```text
wide enabled and target aarch64  -> all(...) true  -> first definition only
every other supported case       -> not(all(...)) -> second definition only
```

The partition is exhaustive and disjoint because enabled and disabled feature
states are both mapped explicitly and the supported target set is exact. In
the first cell, contextually typed index 1 is in bounds for `[u16; 2]` and the
function returns `pair[1]`. In every complementary cell, index 0 is in bounds
and it returns `pair[0]`. Both selected implementations are sound and their
source-specific return results are **PROVED relative to `CONFIG-MAP`**.

## Proof and authority boundaries

Immediate locations, tokens, assignments, and cfg attributes are inspected
source facts. Integer implications after typed/value premises are mathematics.
Every Rust leaf consumed above must reconcile to an exact entry in
`../authority/propositions.json`, including contextual literal inference,
implicit return, branch/match selection, len/usize, subtraction/overflow,
unchecked indexing, lifetime elision, and cfg evaluation/retention. A nearby
page title, wrong implication direction, or TCB substitution does not close a
leaf.

The closed mode hard errors are exactly `EH1`–`EH6` in the defect-rule
inventory; common `GH*` and `GD*` rules apply independently.
