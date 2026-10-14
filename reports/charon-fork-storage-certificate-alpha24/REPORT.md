# An actual Charon fork and storage certificate in the legacy alpha24 bundle

## Summary

The captured `certificate_probe::choose` function admits a Lean certificate relating its actual four-block unstructured body to the actual final structured body. The theorem quantifies every modeled initial state and every CFG fuel budget at least three. It preserves the entire local-value and liveness maps and the modeled copy, move, storage, and return events. A separate theorem removes the actual branch-ending `nop` instructions printed at the control-flow reconstruction boundary.

The certificate concerns an explicit imported fragment. Rust-to-MIR import, Charon's JSON/pretty-printer capture, and the consumer's Python decoder remain trusted. This standalone safe probe is not a zerocopy example and does not complete P128.

## Applicability

The examined producer is the official legacy Anneal alpha24 macOS aarch64 bundle: Charon `0.1.210`, binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`, with bundled rustc `1.98.0-nightly` revision `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`. The independent certificate uses Lean `4.31.0`, revision `68218e876d2a38b1985b8590fff244a83c321783`. This is not the current patched Charon/Aeneas PR stack.

The source contains exactly two safe functions; the first is `choose(b: bool, x: u8, y: u8) -> u8`. The certificate selects function ID 0, with locals `_0:u8`, `b_1:bool`, `x_2:u8`, `y_3:u8`, `_4:bool`. The second function is pinned in the full exports but is outside this certificate; its separate returned-update report handles it. The chosen body is call-free and has no helper, generic-instance, exceptional, or loop dependencies.

`support/capture-identities.json` records the original full export identities and operational commands. Captured JSON paths were sanitized in nonsemantic driver/file fields; selected declaration/body data are retained. The full original source SHA-256 is `cb328552754e6c54ac06e827dea6c52f12c23fa2d987b55e0c2644472faaf7d0`. The original raw export hash is `6eaeff5984f14a4a081b9573f58e9f852bd41e2fb3c7c1e90954f8ff54476196`; final export hash is `1337e82833904551d1762437233ad1d80edbb4579735790adcecb6ceda1d5764`.

## Findings

Basis: source + execution + derived.

The actual boundaries are distinct artifacts:

| Boundary | Preserved evidence | Selected choose operations |
| --- | --- | --- |
| Separate `raw-mir --ullbc` serialization | `raw.sanitized.ullbc` | live 4; copy 1→4; branch by moving 4; copy 2/3→0; dead 4; return |
| Aeneas-preset original ULLBC print | first section of `aeneas.stdout` | Same four blocks and operations |
| Final ULLBC before reconstruction | second section of `aeneas.stdout` | Same four blocks and operations |
| Built LLBC after reconstruction | `aeneas.stderr` | Structured `if`, with one trailing `nop` in each branch |
| Final LLBC print and serialization | third stdout section; `final.sanitized.llbc` | Structured `if` with those two `nop`s removed |

The stdout/stderr labels and recorded successful producer exits are operational evidence. The certificate independently checks the captured endpoints; it does not authenticate that every declared upstream stage actually ran. The two preset invocations also have different full option records. Equal selected choose descriptors are not a proof that the complete exports or preset semantics agree.

The difference matters for the other source function: the separate raw serialized `update_second` already contains an entry `_0 = ()`, whereas the Aeneas-preset original ULLBC print does not. Its later ULLBC and LLBC do contain that assignment. This report does not identify those two raw boundaries or assume the inserted initialization harmless.

`check_capture.py` admits the pinned full files, then decodes the selected JSON declaration using exhaustive key sets and types for the supported fragment: five typed locals, empty generics, copy assignments, `StorageLive/Dead`, moving a Boolean branch discriminator, exactly four blocks, branch targets 1/2, both gotos to 3, and the sole return at block 3. The pretty-print specimens are checked in full for the selected function's declaration/body lines. Unknown opcodes/fields, changed local types, missing storage/return structure, and missing bodies are rejected. Driver options, nonselected declarations, and source coordinates are pinned provenance rather than certified semantics.

`ForkModel.lean` defines separate CFG and structured evaluators. `graph_fork` proves their equality for any supported fork's prefix, branches, suffix, discriminator, initial state, and `fuel + 3`; `built_final` proves identity of the actual inserted `nop`s. `CapturedCertificate.lean` states the exact selected data terms together with the consumer-selected source and original export identity strings. Its `captured_claim` is accepted with assumptions `[propext, Quot.sound]`, without `sorryAx`, `Lean.ofReduceBool`, or a producer-added axiom. Identity-string equalities name the selected subject; they do not prove that a hash denotes bytes or that JSON bytes denote those terms. That relation remains the capture wrapper's obligation.

The state contains total local-value/liveness maps and an event list, so the theorem covers arbitrary prior return values, temporary contents/liveness, and outside locals. Copy requires live initialized source/destination locals; moving the Boolean consumes its stored value; live/dead clear the temporary; return requires a live byte result. Invalid entry states yield `none` in both evaluators. The model observes data/storage events, excluding CFG jumps and `nop`s. It does not retain distinct failure causes or partial failure traces.

Three concrete counterexamples are kernel checked. A changed true branch returns byte 2 instead of 1; deleting `StorageDead(4)` leaves the temporary live; moving argument 1 rather than temporary 4 preserves the returned byte but changes the argument state and event trace. Six actual decoder/binding mutation controls reject unsupported or different inputs. A semantically redundant `nop` is accepted by the proved identity theorem, rather than classified as a defect.

## Boundaries

- **Not examined:** actual zerocopy input; each internal micro-pass separately; loops, recursion/divergence, exceptions, calls, closures, renaming/substitution, raw pointers, nested borrows, and imported Rust semantic adequacy.
- **Unsupported by this decoder:** any function outside the exact call-free five-local four-block fork grammar. All exits inside that grammar are accounted for; this gives no theorem for omitted exceptional edges in a larger grammar.
- **Known not to establish:** validity of rustc/Charon import, the printed phase labels, a generic certified parser, or Charon implementation correctness. The kernel proves the captured relation under this explicitly chosen semantics.

The acyclic grammar makes three CFG blocks sufficient on every path. Quantification over extra fuel avoids presenting one bounded execution as a source termination proof; no loop-to-recursion result is claimed. P067/P068–P073/T069–T070 receive exact partial scopes in `support/coverage.json`; P128 retains its missing zerocopy requirement. Extending grammar, proving capture adequacy, and integrating witness emission are separate engineering obligations.

## Evidence

`support/` preserves the source, sanitized full JSON exports, original/postmicro/final stdout and built-LLBC stderr, exact identity/command records, strict decoder, Lean model and selected theorem, assumption output, mutation results, and fresh-scratch revalidation results. These are actual extraction artifacts and report-owned certificates, not source mirrors. `tool-identities.json` records exact binaries and host observations on 2026-10-14.

## Revalidation

Run `python3 -B support/revalidate.py --lean-bin /path/to/lean-4.31/bin/lean --out /new/task/scratch`. The script copies support into a new scratch directory, validates capture, and compiles both Lean units without modifying the toolchain or original package. Inspect the exact theorem and assumption output. For another producer revision or input, replace the captured artifacts, redo the restricted decoder/identity binding, and reconsider every admitted type, instruction, edge, and observation; rerunning the old theorem alone does not certify the new extraction.

*Authored by an AI agent acting on joshlf's behalf.*
