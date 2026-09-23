# V5 Diagnostic Oracle — F: Root-Gap Fan-out

> **DRAFT / evaluator-only.** Do not disclose this key, root identity, expected
> dispositions, atom IDs, or defect rules to a report agent.

## Scoring contract

Score the direct criteria in `../atoms/F.json`. Apply only closed IDs from
`../rules/defect-rules.json`. Root-cause propagation is performed by the
harness from the frozen DAG; the scorer must still decide each dependent's
direct criterion independently.

## Exact missing root and theorem obligations

Use one stable evidence root, conventionally `G`: the exact selected
`peer-stage` 2.1.0 implementation/build/artifact and an applicable proof or
accepted TCB proposition are unavailable. That one absence blocks two distinct
propositions; it must not be rewritten as one overstrong theorem:

```text
G-SAFE = every selected next_nonzero(u8) call is UB-free and returns a
         nonzero u8.

G-WRAP = every selected next_nonzero(value) call returns the exact documented
         next-stage value, wrapping u8::MAX to 1.
```

`G-SAFE` is the minimal theorem needed to discharge `new_unchecked` and safe-API
soundness. `G-WRAP` is additionally needed for the exact documented result, but
is not a prerequisite for the nonzero safety proof. `DEPENDENCY-API.md` supplies
both public claims but no body, build identity, artifact, or proof. `TCB.md`
expressly accepts no implementation proposition. A pin and documentation close
neither proposition. Closing either requires recursive audit of the exact
selected implementation/build/artifact or a newly accepted proposition with
the needed applicability.

There is one missing-evidence root, two theorem obligations, and three API
consumers—not three independent roots and not one conflated theorem.

## Exact API ledger

| API | Direct disposition | Root / certificate |
|---|---|---|
| `staged_token` | **UNPROVED** | `G-SAFE` blocks sound construction; `G-WRAP` separately blocks the exact wrapping-result claim |
| `staged_value` | **UNPROVED** | distinct exported consumer, transitively blocked through `staged_token`; exact returned value also needs `G-WRAP` |
| `staged_is_nonzero` | **UNPROVED** | distinct exported consumer blocked by `G-SAFE`; its contextually typed `!= 0` does not prove the dependency result |
| `local_token` | **UNSOUND** | independent valid safe call `local_token(0)` reaches `NonZeroU8::new_unchecked(0)` and violates its exact precondition |
| `checked_token` | **PROVED / sound control** | safe `NonZeroU8::new`: zero produces `None`, nonzero produces `Some` |

Conditional reasoning remains valid and should be preserved separately. Under
`G-SAFE`, the staged unsafe constructor's nonzero obligation closes and both
downstream `.get()` consumers inherit a nonzero value. Under `G-SAFE` plus
`G-WRAP`, the documented exact values also follow. Neither conditional
certificate may be relabeled unconditional or counted as another evidence root.

The crate's exported safe API set is aggregate **UNSOUND** because the
independent `local_token(0)` certificate is complete. That existential result
does not change any of the three staged obligations from **UNPROVED** to
UNSOUND or PROVED.

## Evidence boundaries

The dependency excerpt is contract and boundary evidence, never Rust
authority or implementation proof. The Rust leaves are contextual literal and
equality semantics, ordinary/unsafe call rules, and exact `NonZeroU8::new` and
`new_unchecked` contracts. The TCB boundary must remain conspicuous.

The closed mode hard errors are exactly `FH1`–`FH7`; common `GH*` and `GD*`
rules apply independently.
