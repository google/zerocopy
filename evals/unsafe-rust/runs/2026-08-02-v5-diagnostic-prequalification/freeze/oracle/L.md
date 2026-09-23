# V5 Diagnostic Oracle — L: Naturalistic Local Proof Review

> **DRAFT / evaluator-only.** Do not expose this key, expected result, atom
> IDs, defect rules, or authority packet to a report agent.

## Scoring contract

L is a naturalistic source review. It does not require a table, atom labels,
formal notation, URLs in an adjacent comment, or particular replacement
wording. Score the material propositions in `../atoms/L.json` wherever they
appear and accept an equivalent concise explanation. Apply only closed rules
from `../rules/defect-rules.json`; omission alone is not a hard error.

## Exact result

The implementation of `last` is sound throughout the requested Rust 1.83,
target, and profile scope.

On the unsafe-call path, the `if bytes.len() == 0` condition evaluated false.
The unsuffixed zero is uniquely inferred as `usize` and denotes zero, so the
false equality yields `len != 0`. Slice `len` returns a `usize`; the unsigned
domain therefore yields `len > 0`. In `bytes.len() - 1`, the unsuffixed one is
also uniquely `usize` and denotes one. Consequently subtraction is
representable without underflow/overflow in every profile and pointer width,
and:

```text
index = len - 1 < len.
```

That is the exact element-index obligation for `get_unchecked`. Its returned
reference is tied by the method receiver/elision rule to the input `bytes`
borrow, which is compatible with `Option<&u8>`'s returned lifetime. The full
implementation obligation is therefore **PROVED**.

The existing comment is nevertheless **materially deficient**. It says only
that the returned reference cannot outlive `bytes`. That addresses the
lifetime edge but neither states nor derives the callee's actual in-bounds
precondition. It must not cause the sound implementation to be mislabeled
UNSOUND or UNPROVED.

A sufficient repaired local proof artifact would expose, in any clear form:

```text
The else path proves len != 0; because len is usize, len > 0, so len - 1 is
representable and strictly below len. Therefore index is in bounds for this
same slice; get_unchecked returns a reference tied to the slice borrow.
```

The report need not reproduce that wording or propose an edit. It must make
the reconstructed material proof clear enough to diagnose and repair the
comment issue.

## Premise reconciliation

The material Rust leaves are contextual literal type/value, if selection,
usize equality, slice len/type, usize domain, subtraction and overflow,
`get_unchecked`, and lifetime elision. Immediate locations/assignments are
source facts; the inequality from positive integer length is mathematics. A
complete positive proof must use applicable Rust 1.83 propositions and must
not substitute builds/tests or silently add a TCB.

The closed mode hard errors are exactly `LH1`–`LH5`; common `GH*` and `GD*`
rules apply independently.
