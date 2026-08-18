# V5 Diagnostic Oracle — R: Naturalistic Abstraction Redesign

> **DRAFT / evaluator-only.** Never expose this key, witness, expected verdict,
> atom IDs, or defect rules to a report agent.

## Scoring contract

R is a naturalistic design review. A concise report may pass without a formal
certificate layout, migration plan, code block, or exhaustive alternative
survey. Score the material criteria in `../atoms/R.json` wherever present and
apply only IDs from `../rules/defect-rules.json`. Equivalent safe
specializations pass; omission alone is not a hard error.

## Current-artifact result

`Slot` is a public ordinary safe trait. Valid use of public
`increment<S: Slot>` therefore ranges over arbitrary coherent downstream safe
implementations, not just crate-owned `Tail`. A downstream crate may define a
local type such as:

```rust
struct Outside;
impl Slot for Outside {
    fn index() -> usize { 2 }
}
increment::<Outside>(&mut [0, 0]);
```

Visibility/orphan rules permit this implementation. Context infers the return
literal as `usize` value 2 and the array elements as `u32`; implementing the
ordinary trait and calling the ordinary function require no unsafe act. The
complete valid safe call reaches `pair.get_unchecked_mut(2)` on a length-2
array. Index 2 is out of bounds and Rust 1.83 makes that call UB even if the
reference were unused.

The current public safe API is therefore **UNSOUND**. `Tail`, comments, design
intent, unpublished status, and absence of known callers do not narrow the
literal current safe API.

## Parsimonious redesign

The stated minimum behavior is only wrapping increment of element 1 of an
owned two-element `u32` array. It requires neither downstream index metadata
nor generic dispatch. The preferred design is equivalent to:

```rust
pub fn increment(pair: &mut [u32; 2]) {
    pair[1] = pair[1].wrapping_add(1);
}
```

Checked constant indexing is in bounds for `[u32; 2]`; `wrapping_add(1)` gives
the exact modular update in every profile. This removes the caller-controlled
implementation/index capability and the unsafe block while preserving all
required behavior.

Making `Slot` unsafe, adding prose to the safe trait, or retaining the generic
abstraction can be made defensible in a different contract, but is less
parsimonious here because no downstream generic behavior is required. The
crate's unpublished/no-downstream scope authorizes the removal and contract
delta without implying an unsupported migration guarantee.

The redesign remains a **conditional recommendation** pending implementation
and fresh audit. It neither certifies proposed code nor changes the current
UNSOUND verdict.

The closed mode hard errors are exactly `RH1`–`RH5`; common `GH*` and `GD*`
rules apply independently.
