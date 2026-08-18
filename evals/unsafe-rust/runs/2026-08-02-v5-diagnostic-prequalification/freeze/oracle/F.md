# V5 Diagnostic Oracle — F: Root-Gap Fan-out

> **DRAFT / evaluator-only.** Do not disclose this key, root identity, expected
> dispositions, atom IDs, or defect rules to a report agent.

## Scoring contract

Score the direct criteria in `../atoms/F.json`. Apply only closed IDs from
`../rules/defect-rules.json`. Root-cause propagation is performed by the
harness from the frozen DAG; the scorer must still decide each dependent's
direct criterion independently.

## Exact missing root

Use one stable root, conventionally `G`:

```text
G = The selected peer-stage 2.1.0 implementation of next_nonzero is UB-free
    for every u8 call and fulfills the exact claimed result contract,
    including returning a nonzero u8 (and the claimed wrapping result).
```

`DEPENDENCY-API.md` supplies the selected public claim but no body, build
identity, artifact, or proof. `TCB.md` expressly accepts no implementation
proposition. A pin and documentation are not G. Closing G requires recursive
audit of the exact selected implementation/build/artifact or a newly accepted
exact TCB entry with the needed proposition and applicability.

There is one unavailable theorem and three consumers, not three independent
missing roots.

## Exact API ledger

| API | Direct disposition | Root / certificate |
|---|---|---|
| `staged_token` | **UNPROVED** | blocked by G: without its nonzero result theorem, `new_unchecked(candidate)` is not discharged |
| `staged_value` | **UNPROVED** | distinct exported consumer, transitively blocked by the same G through `staged_token` |
| `staged_is_nonzero` | **UNPROVED** | distinct exported consumer, transitively blocked by the same G; its contextually typed `!= 0` does not prove the dependency result |
| `local_token` | **UNSOUND** | independent valid safe call `local_token(0)` reaches `NonZeroU8::new_unchecked(0)` and violates its exact precondition |
| `checked_token` | **PROVED / sound control** | safe `NonZeroU8::new`: zero produces `None`, nonzero produces `Some` |

Conditional reasoning below G remains valid and should be preserved: if G is
true, the staged unsafe constructor's nonzero obligation closes and the two
downstream `.get()` consumers inherit the resulting value. That conditional
certificate must not be relabeled unconditional and is not a second root.

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
