# Instrumented optimization certificates: Crellvm, verified validators, and refinement direction

## Summary

Compiler instrumentation can expose the witnesses that a relational checker needs without making the optimizer trusted. The reduction in trust depends on the accepted relation, proved rule set, and deployed acceptance path. Behavioral refinement from source to target does not imply that target safety proves source safety.

The exact Crellvm snapshot inspected here includes admitted rule soundness and CLI paths that report admission without reporting validation success. Its theorem interface and execution wrapper therefore require separate accounting.

## Applicability

The main subjects are the PLDI 2018 Crellvm paper, DOI `10.1145/3192366.3192377`, and `snu-sf/crellvm@668249b88756233f96b3ef21f12993501a348afc`. The paper targets LLVM 3.7.1. The main repository snapshot does not pin all external dependencies: its Makefile clones/pulls separate LLVM, Vellvm, and support repositories. No complete checkout or executable was built.

The POPL 2008 verified-validator paper and PLDI 2021 Alive2 paper supply distinct comparison relations. This report does not treat either as the current implementation of those tools, or establish that one checker covers another's semantics.

## Findings

### Instrumentation and relational evidence

Basis: **documentation** — [Crellvm paper](https://sf.snu.ac.kr/publications/crellvm.pdf), §§4–6.

ERHL checks relational assertions at matched instruction and CFG positions; compiler hints or checker automation supply inference-rule sequences. The top-level meaning is target behavior inclusion in source behavior:

```text
Beh(target) ⊆ Beh(source).
```

Local checks cover CFG compatibility, initial assertions, command/phi-node correspondence, postcondition calculation, and entailment. Custom rules must preserve the assertion interpretation. The paper distinguishes the Coq-verified non-arithmetic rule subset from arithmetic rules and uses a Vellvm memory model differing from informal LLVM. It excludes transformations requiring unsupported deep analyses or CFG changes in the examined coverage.

### The verified-validator contrast and its source-definedness premise

Basis: **documentation** — [Tristan and Leroy, POPL 2008](https://xavierleroy.org/publi/validation-scheduling.pdf), §2.1–2.2.

For a transformer `C` and boolean validator `V`:

```text
V(source,target) = true ⇒ RequiredRelation(source,target).
```

A wrapper returns the target only on acceptance; all other outcomes return compilation error. Their scheduling relation preserves the result of source executions that are well-defined and terminate. Symbolic validation tracks definedness constraints as well as final expressions. The optimizer need not be verified; the validator soundness theorem supplies the wrapper's pass relation.

### Alive2's comparison permits more-defined targets

Basis: **documentation** — [Alive2 PLDI 2021 paper](https://web.ist.utl.pt/nuno.lopes/pubs/alive2-pldi21.pdf), §§5.1–5.3, 7.

State refinement allows any target final state when the source final state is UB; otherwise it compares return values and memory. With nondeterminism, each admitted target outcome must have a compatible source witness. Target nondeterminism can be removed. Input/precondition constraints qualify the comparison. Loop/resource bounds limit coverage. This is LLVM optimization refinement, not an unbounded source-UB-freedom certificate.

### What the pinned Crellvm sources establish

Basis: **source** — immutable files in Evidence; no fresh Coq check.

`Adequacy.v` exports `sim(source_state,target_state) → behave(target_state) ⊆ behave(source_state)` and a module theorem under fitted-argument premises. `Behavior.v`'s `beh_error` admits every observation from an error state. Hence the source behavior set after an error is intentionally unrestricted; the inclusion theorem cannot exclude that source error merely from target behavior.

`SoundInfrules.v` splits interesting and other rules. `apply_not_interesting_infrule_sound` invokes `ADMIT` for arithmetic and InstCombine-only rule soundness. `TODOProof.v` defines polymorphic `ADMIT` with `Admitted`; this is a logical assumption, not an executable proof search result. The interesting-rule proof follows separately. The whole checker proof cannot be described as assumption-free without restricting used rules and examining its dependency closure.

`Validator.valid_module` returns `Some true` on matching layouts/types and successful product validation. Layout or named-type mismatch yields `Some false`; validation failure yields `None`. The OCaml wrapper bypasses validation on an `ADMITTED` hint. For `Some false` it prints an admission message; only `None` explicitly exits with failure in the inspected branch. This is source inspection, not a runtime observation. An exit status alone must not be treated as evidence of `Some true`.

### Which evidence is untrusted, and which premise remains

Basis: **derived** from the checker/semantic split.

An optimizer may emit candidate alignment points, invariants, value-number identities, memory facts, and rule names. A sound acceptance theorem must treat these as claims to check. The generator's result is not evidence that an alias, range, or purity analysis was sound unless its proposition is independently checked or covered by a verified analysis theorem.

Rule extension has three independent duties:

1. Prove the rule's semantic consequence with the exact arithmetic, memory, poison/error, and observation model used by the checker.
2. Check the concrete rule instance's premises; a theorem about guarded rewrites does not establish that the guard holds in this program.
3. Bind the rule schema, semantic library, and endpoint artifacts to the accepted run.

For a rule proved in another tool, an assertion that the tool can prove it is not the proof or a semantic bridge. A foreign solver's validity judgment must either be trusted explicitly or reconstructed in the accepted proof system. Changing an admitted rule to a proved rule is meaningful trust reduction; adding another heuristic to the producer is not.

### The direction mismatch for Anneal

Basis: **derived**.

If all source behaviors satisfy a universal property and target behaviors are a subset, the property transfers to the target. The reverse implication fails: the removed source choices may violate the property. If source UB admits every observation, a constant safe target trivially satisfies behavior inclusion even though the source has UB.

Anneal normally reasons about an extracted target model and wants a Rust claim. For source UB-freedom, its pass interface must additionally expose each first forbidden source step in the model. An optimizer relation preserving only defined source execution cannot supply that theorem. Keep three obligations distinct: target refinement, source failure reflection, and coverage of permitted source entries. Total contracts additionally need the relevant termination/progress connection.

Memory-injection facts can justify changed block representations under their specified semantics. They do not by themselves establish Rust provenance, access permission, or runtime typed-transfer behavior. The formal source language and memory relation are part of what the certificate means, not implementation details to omit from its identity.

### Maintenance and the first useful instrumentation experiment

Basis: **derived**, proposed work only.

Instrumentation has a latency advantage when a pass already knows correspondence that a post-hoc certifier would have to rediscover. Its maintenance cost is coupling to pass internals and witness serialization. An independent validator reduces that coupling but may need stronger invariant reconstruction. A mixed design can accept optional hints while keeping the semantic checking interface stable.

For Anneal, begin with one real before/after pass snapshot and one rule family. Record the effective import/configuration, endpoint ASTs, correspondence hints, and the exact theorem needed by the following stage. Mutate a rule premise and discard a failure-capable operation: the checker should reject even if final values agree. Report producer success, semantic validation success, unsupported/admitted classification, and process exit separately. Do not weaken the final acceptance path to accommodate producer incompleteness.

## Boundaries

- **Not examined:** executable Crellvm checker, complete external dependency closure, Coq assumption audit, or current LLVM/Alive2 source. No build/install was attempted.
- **Established by direct source inspection:** the named admission sites, `beh_error`, return variants, and OCaml branches at the exact revision. This is not a complete audit of every assumption or reachable rule.
- **Not established:** the unrestricted Crellvm checker is assumption-free; the verified-rule subset needs an explicit usage restriction and dependency audit.
- **Not established:** a stdout message or ordinary process return proves `valid_module = Some true`.
- **Known semantic distinction:** optimization refinement may remove source nondeterminism and exploit source UB. It is insufficient for reflecting model safety back to source safety.
- **Unknown:** engineering costs on Charon/Aeneas. The instrumentation experiment is proposed, not implemented.

## Evidence

Observed 2026-10-14. Primary papers were directly read; no PDF byte hashes were acquired. Source files were read using exact GitHub refs.

| Primary source | Narrow coordinates | Identity |
| --- | --- | --- |
| [Crellvm author PDF](https://sf.snu.ac.kr/publications/crellvm.pdf) | 28 PDF pages; §5 interpretation/rules (pp.10–11), §6 (p.11), appendix I (p.28) | DOI `10.1145/3192366.3192377` |
| [POPL 2008 validator PDF](https://xavierleroy.org/publi/validation-scheduling.pdf) | 11 PDF pages; §2.1/equations 1–2/Theorem 1 and §2.2 (pp.2–3) | DOI `10.1145/1328438.1328444` |
| [Alive2 author PDF](https://web.ist.utl.pt/nuno.lopes/pubs/alive2-pldi21.pdf) | 15 PDF pages; §5.1–5.3 (pp.7–8), §7 bounds | DOI `10.1145/3453483.3454030` |
| `snu-sf/crellvm` source | revision `668249b88756233f96b3ef21f12993501a348afc` | tree `0b62b6ab302501596f06f4b94181cc1c82df6aa7` |
| [Adequacy.v](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/coq/proof/Adequacy.v) | lines 25–28, 72–97 | blob `ecfae4591dd0975edc9edac1004385145a62ee3e` |
| [Behavior.v](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/coq/proof/Behavior.v) | lines 21–27, 61–64 | blob `ff32147504d3ae7f8fe479d038d6c54c5664c907` |
| [SoundInfrules.v](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/coq/proof/SoundInfrules.v) | lines 32–52, `apply_not_interesting_infrule_sound` | blob `5c3d417c392d71c6fa8cfe7ec2b4e4071f5f3596` |
| [TODOProof.v](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/coq/proof/TODOProof.v) | lines 467–468, `ADMIT` | blob `c6f0050509b787b90504039c36a6aa52699657c2` |
| [Validator.v](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/coq/def/Validator.v) | lines 335–346, `valid_module` | blob `e56bd51e4c621ee70c51a824bf118c0a8938ad1a` |
| [main.ml](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/ocaml/main.ml) | lines 84–115 | blob `d5f842d591b010276e7b9f6fcbfcef277a3dfb43` |
| [Makefile](https://github.com/snu-sf/crellvm/blob/668249b88756233f96b3ef21f12993501a348afc/Makefile) | lines 21–31, unpinned dependency clone/pull | blob `5830bda3dc2ea453c75fe5028731dbff8f01c7f6` |

The repository README points to `coq/proof/Refinement.v`, absent from the inspected complete tree. The actual adequacy/behavior files above were read instead; no theorem was inferred from the missing pathname.

## Revalidation

For another snapshot, first inspect behavior direction and source-error interpretation, `valid_module`, OCaml admission/error branches, rule soundness, and dependency pins. A theorem with the same name can have a different trust or semantic boundary.

With a compatible completed build, audit assumptions for the accepted checker theorem and record every rule used by a candidate certificate. Then test layouts/types mismatch, admitted hints, bad rule premises, unsupported analyses, and proof corruption. Only exact semantic acceptance should count as successful certification; process status alone is not that proposition.

*Authored by an AI agent acting on joshlf's behalf.*
