# V5 Diagnostic Oracle — Q: Metamorphic Unsafe-Operation Control

> **DRAFT / evaluator-only.** Do not expose this key, its changed byte/control
> facts, verdicts, atom IDs, defect rules, or authority inventory to a report
> agent.

## Scoring contract

Q is controlled and requests exact domains, witnesses, proof kernels, and
authority. Score the direct criteria in `../atoms/Q.json`; use only closed IDs
from `../rules/defect-rules.json`. Keep the three APIs and three caller examples
separate. Do not infer a direct failure from a prerequisite and do not make
omission alone a hard error.

## Exact domains and source boundaries

- `local_text(bool)` and `catalog_text(bool)` are ordinary safe APIs whose
  valid-use domain is both bool values on the full supplied Rust 1.83 scope.
- `delegated_text(bytes)` is an unsafe API. Its valid-call domain is exactly
  slices for which every byte's numeric value is at most `0x7f`.
- `caller_examples.rs` is downstream source. Its unsafe blocks satisfy the
  compiler-side context requirement but assert, rather than prove, the caller
  precondition.
- The selected `peer-text` package is exactly 3.0.0. Its public excerpt is not
  its unavailable method body or an accepted implementation theorem.

Output references from the local conversion and delegated method are tied to
their applicable input bytes. The local source uses static inputs; the
delegated public signature returns a borrow tied to its argument.

## Exact API and caller results

### `local_text`

For `primary=true`, match selection yields `"north".as_bytes()`: a string
literal is a valid UTF-8 `str`, and `as_bytes` extracts its bytes. That branch
discharges `from_utf8_unchecked`.

For `primary=false`, the first matching arm selects the static array whose
contextually typed `u8` values are exactly `[0, 159, 146, 150]`. Rust 1.83's
`str::from_utf8` page uses this exact sequence as an invalid example, while
`from_utf8_unchecked` requires valid UTF-8. Thus `example_local` is a valid
safe call that reaches a false unsafe precondition and lets a non-UTF-8 `str`
escape through a safe API.

Rust 1.83's primitive-`str` invariant is deliberately more precise than an
"invalid value means immediate UB" shortcut: constructing the non-UTF-8
string slice is **not immediate UB**, but safe library functions may assume a
`str` is valid UTF-8, so the escaped value can lead to UB downstream. The
escape makes the safe API **UNSOUND**. It does not, by itself, prove that the
bare execution of `example_local()` exhibits UB. Any claim about a particular
UB execution needs an exact later safe operation and proof of its reached UB;
once such an execution reaches UB, nothing in that execution is guaranteed
"before" the UB either.

`local_text` is **UNSOUND**. Its true branch is a proved regional control; that
does not repair the safe API's false branch.

### `catalog_text`

Both match arms call `as_bytes` on existing valid string literals (`north` or
`south`). Each extracted byte slice is valid UTF-8, the same
`from_utf8_unchecked` precondition is discharged, and the returned lifetime is
input-tied/static. `catalog_text` is **PROVED sound**, with its stated
branch-specific text result. Its near syntax is deliberately not evidence for
transferring `local_text`'s verdict.

### `delegated_text`

The unsuffixed zero in `bytes.len() == 0` is uniquely `usize`. Empty input
returns the valid empty `str` without calling the dependency. Nonempty input
conditionally transfers to `SelectedDecoder::decode_ascii(bytes)`.

The submitted static `[0]` has one `u8` value at most `0x7f`, so
`example_peer_b` is a valid caller and reaches the dependency method. It
does not prove the selected method body. The smallest unresolved premise is:

```text
GQ = peer-text 3.0.0's selected SelectedDecoder::decode_ascii implementation
     is UB-free for every contract-satisfying call and returns a valid str
     with the required input-tied lifetime.
```

No supplied body, build/artifact identity, proof, or accepted TCB proposition
closes GQ. `delegated_text` is therefore **UNPROVED**; conditional downstream
reasoning below GQ remains valid.

The invalid static contains values (159, 146, and 150) above `0x7f`.
`example_peer_a` therefore violates the unsafe caller contract and is not
a valid-use refutation. Its unsafe block cannot make that assertion true.

## Aggregate and authority result

Keep these conclusions distinct:

```text
local_text          UNSOUND
catalog_text        PROVED sound control
delegated_text      UNPROVED at GQ
peer ASCII example  valid caller/control, but still blocked by GQ
peer invalid example rejected as outside the caller domain
aggregate safe API  UNSOUND because local_text has a complete certificate
```

The proof consumes exact Rust 1.83 match/if/call, integer literal/equality,
len, string invariant/as_bytes, UTF-8 invalid-example, unchecked conversion,
the explicit non-immediate-construction/downstream-UB distinction,
unsafe-function, visibility, and lifetime propositions. The dependency excerpt
supplies only its numeric ASCII caller contract and evidence boundary.

The closed mode hard errors are exactly `QH1`–`QH7`; common `GH*` and `GD*`
rules apply independently.
