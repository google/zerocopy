# Selected Simuliris Tree Borrows proofs: fresh kernel replay and assumption closure

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Six selected original Simuliris proof seeds at `e3abfcdc301f92250d4227fc03c00463bf57b982` compiled, three unchanged observation files successfully checked and printed assumptions for 24 constants, and Rocq's recursive native checker successfully checked all 517 loaded libraries. The selection covers generic adequacy and fairness, Tree Borrows whole-program/contextual adequacy, allocation and retag/protector resources, two optimization examples, and a separate sequential read-reordering theorem.

The actual per-constant audit reports 19 constants closed under the global context and five depending on excluded middle plus constructive indefinite description. The checker-wide context additionally contains dependent functional extensionality; none of the selected 24 constants reports it as a dependency. These are different observations and must remain separate.

This establishes a bounded replay of existing calculus proofs. The concrete allocation, split/recombine, recursive-reborrow, Cell/callback and returned-reference ports required by E23 remain unconstructed. MiniRust correspondence, a byte-sensitive MiniRust lifetime logic, and safe Rust client soundness also remain open.

## Applicability

The source is the exact 185-file Simuliris archive with SHA256 `06dbeeb1ddda80ffe93b26fd20d8597f9c9a63767ae2a7e74e4dae696952fb9b`. All original source bytes matched before compilation, after the diagnosed harness failure, and after checking. The initial project contained no `.vo`, `.vos`, `.vok` or `.vio` files. The copied final project contains 78 compiled original libraries and three observation libraries; the other original examples were not built merely because they appear in `_RocqProject`.

The observed environment was Linux AArch64, OCaml 4.14.4, Dune 3.17.2, Rocq runtime/core/compat/stdlib 9.2.0, Equations `1.3.2+9.2`, Rocq-Elpi 3.5.1, Elpi 3.7.3, Iris `dev.2026-09-10.3.b3495ef9` at full revision `b3495ef9f0805b0dc7c1b1abbdc8cf473ede121b`, and stdpp `dev.2026-09-09.1.c3186aad` at `c3186aad493872e3a9774ac0b42ca2f591b05835`. The parent prepared this isolated environment and its dependency/source receipts. This replay freshly checked tool versions/hashes, installed switch state, original Simuliris sources, generated objects, assumptions and recursive checker results; it did not repeat dependency installation.

Compilation used the original project mapping `-Q theories simuliris`, warning settings and proof defaults, with `-j1` and ordinary full `.vo` compilation. The three owned files contain only imports, a printing-width setting, `Check`, and `Print Assumptions`; no new theorem, axiom or proof patch was introduced. Their historical “proposed/not compiled in this planning task” comments are unchanged planning provenance; the execution logs establish their subsequent actual compilation.

## Findings

### 1. Fresh proof checking succeeded after a diagnosed namespace correction

Basis: source + execution.

| Phase | Original seeds or observations | Exit | Wall seconds |
| --- | --- | --- | ---: |
| Generic, corrected | `simulation/adequacy.vo`, with both earlier partial objects explicitly forced to rebuild | 0 | 30.245 |
| Tree Borrows core | `tree_borrows/adequacy.vo`, `tree_borrows/examples/lib.vo` | 0 | 124.776 |
| Optimization examples | protected mutable write-up activated paper example; unprotected escaped shared-read deletion | 0 | 6.194 |
| Sequential reads | `tree_borrows/read_read_reorder/read_reorder.vo` | 0 | 4.189 |
| Framework audit | 7 constants | 0 | 10.198 |
| Resource audit | 12 constants | 0 | 6.171 |
| Example audit | 5 constants | 0 | 10.182 |
| Recursive checker | Six original seeds plus all three observation libraries | 0 | 38.249 |

The initial generic attempt failed in 2.138 seconds because the harness added top-level audit files to `rocq makefile`. That induced `-R . Top` alongside the original `-Q theories simuliris`; overriding load-path warnings culminated in `fairness.v` being unable to resolve `simuliris.simulation.language`. This was a setup failure, not a theorem rejection or kernel panic. The generated Makefile/config and both partial `.vo` files were preserved. After verifying every original source byte, the Makefile was regenerated from `_RocqProject` alone; a recorded regression check confirms that it retains `-Q theories simuliris` and has no overriding `Top` mapping. Both partial objects were explicitly forced to recompile with `make -W` before dependent work. The audits were then compiled separately with the original flags. The failed phase and corrected phase remain separate evidence.

The recursive command was `rocq check -Q theories simuliris -o -m` followed by the six original module names and three audit module names. It contained neither `-admit` nor `-norec`, and its full trace ends with “Modules were successfully checked.” Every one of the 24 selected constants occurs in the native check trace. The trace records 517 loaded and checked libraries: 78 original Simuliris, three owned observation libraries and 436 installed dependencies. Hashes of the exact 517 loaded objects were captured during checking and again after successful completion; both path sets and hash listings match byte for byte.

All phase caps were respected. The cumulative audit/checker driver took 64.953 seconds against its 20-minute allocation. Final project disk use was 32,109,248 bytes, below the 1 GiB additional-output cap. The checker reported total heap size 1,330,296 kbytes; that is its heap statistic, not a measured peak RSS. The final process snapshot contains no proof process. Routine opam root warnings are preserved separately from proof outcomes.

### 2. Per-constant assumptions differ from imported global context

Basis: execution. Exact printed types, assumptions, source coordinates/hashes and native-check sightings for all 24 constants are in `support/actual-results.json`; full original output is in `support/logs/audit-*.stdout`.

| Selected constants | Number | Actual `Print Assumptions` result |
| --- | ---: | --- |
| `slsls_adequacy`, `prog_rel_adequacy`, `log_rel_adequacy` | 3 | `Classical_Prop.classic` and `IndefiniteDescription.constructive_indefinite_description` |
| `sim_pool_preserves_fair_termination`; structural relation, reflexivity and context closure | 4 | Closed under the global context |
| `safe_reach`, allocation/write helpers, two retag laws, unprotect law, controlled-reborrow lemma, `array_tag`, two tag-mapping definitions | 12 | Closed under the global context |
| Protected and unprotected example logical-relation proofs | 2 | Closed under the global context |
| The corresponding two `_ctx` corollaries | 2 | The same two classical axioms |
| Sequential `read_reorder` | 1 | Closed under the global context |

“Closed” records the command's dependency result; it does not remove explicit quantified hypotheses or Iris typeclass premises from a theorem. Four of the selected constants (`safe_reach`, `array_tag` and the two pointer-kind mappings) are definitions, not adequacy theorems.

The native checker's context summary lists `Stdlib.Logic.IndefiniteDescription.constructive_indefinite_description`, `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` and `Stdlib.Logic.Classical_Prop.classic`. It reports predicative Set, rewrite rules disallowed, and no declarations relying on type-in-type, unsafe (co)fixpoints or assumed positivity. These global imported axioms are neither three dependencies of every result nor evidence of an admission-free whole repository. Successful native checking validates terms relative to this context and the checker implementation.

### 3. The adequacy direction and client domain retain substantial premises

Basis: source + execution + derived interpretation.

At `theories/simulation/adequacy.v:310`, `slsls_adequacy` requires the BI/satisfiability classes and a satisfiable assertion providing the initial-state relation, simulation resources, state interpretation, program resources, related entry argument and an observation bridge. Its `prog_ref` conclusion (`simulation/behavior.v:15`) assumes **source safety** and related initial states. It then says target fair divergence implies source fair divergence, every target main-thread return has a matching source return related by `O`, and the target is safe. It is not an unconditional termination or equivalence theorem.

`tree_borrows/adequacy.v:30` specializes this to Tree Borrows, with its Iris pre-state and program-relation premises. At line 50, a logical relation valid for every relevant Iris state yields `ctx_ref`. The latter (`tree_borrows/behavior.v:48`) quantifies over well-formed closing expression contexts and well-formed, closed other function bodies. Literal places/pointers are excluded by `treeborrows_wf`. These are calculus contexts, not a Rust type system's permitted safe clients.

The specialization starts from empty states and calls `main` with source poison. Its observation relation equates integer results, function names and call IDs, treats pointer details as unobservable, and permits any target scalar when the source scalar is poison (`behavior.v:8–33`). Replaying this relation does not establish target-byte equality or a Rust pointer/provenance observation relation.

The two selected examples prove optimized-to-unoptimized logical relations and contextual refinement in this calculus. The protected example's function calls, activation and end-call resource restoration are meaningful existing proof cases, but do not supply arbitrary Rust callbacks or trait-instance contracts.

### 4. The checked resources support concrete allocation/retag laws, with a visible API-port boundary

Basis: source + execution + derived interpretation.

`examples/lib.v:6–7` explicitly assigns one abstract memory slot to a scalar, including a pointer or integer. `sim_new_place_local` (line 35) relates allocation followed by initialization when source and target values have equal lengths, and provides local tag ownership, source/target heaplets and size facts to its continuation. `sim_alloc_local` (`step_laws/steps_local.v:322`) provides poison-initialized heaplets. These are existing allocation proof ingredients; they are not a Rust allocator implementation or a byte-layout theorem.

`new_place_safe_reach` (`lib.v:67`) recovers that the initializer is a value whose length matches the allocation. Its result uses `safe_reach`; the definition (`simulation/language.v:1056`) is `safe P e σ → ∃ e' σ', steps_no_fork … ∧ Φ e' σ'`. Thus the result extracts information **assuming safety**. It does not establish that arbitrary allocation/initialization inputs are safe.

`array_tag` (`logical_state.v:851–857`) is one ghost-map element keyed by `(tag, block)`, storing a whole offset map. Its source comment explicitly says the historical name is not an actual array. Ordinary fractional sharing preserves the same whole-map value; a proof of disjoint array splitting/recombination does not follow simply from the notation. This replay constructs no replacement splitting protocol and does not prove such a protocol impossible.

The checked `sim_retag_default` and `sim_retag_fnentry` (`step_laws/steps_retag.v:67,304`) retain pointer relations, lengths/ranges, ownership and continuation premises. Default retagging requires `pointer_kind_to_tag_unprotected … = Some …`; that mapping returns `None` for `InteriorMut`. The protected mapping accepts Box/MutRef cases, including their protected interior-mutability treatment, but returns `None` for a shared interior-mutable reference (`loc_controlled_laws.v:356–372`). The operational `retag_perm` has additional interior-mutable permission cases; their existence is not a complete Cell ownership/API proof.

`sim_protected_unprotect` (`steps_opt.v:310`) requires range coverage, a tag entry in the call map, call/tag ownership and conditional active-unique heaplets/value relation, then supplies a continuation with the protector removed. `loc_controlled_read_after_reborrow_creates` (`loc_controlled_laws.v:380`) requires successful child creation/read access, state/tree well-formedness, freshness, lookup, bounds, live call ID and a successful tag mapping. These checked premises make the outstanding recursive-reborrow, callback and returned-reference resource obligations concrete; replay alone does not discharge them.

### 5. Sequential read reordering has a separate conclusion

Basis: source + execution.

`tree_borrows/read_read_reorder/read_reorder.v:218` proves `eventually_equal` for distinct variable names. The proof chooses four primitive steps. The definition (`equivalence_def.v:9–35`) uses no-fork steps, nontermination within the prefix, and both inclusions between the states reachable after that prefix, for every well-formed initial state. This selected result is not the contextual-refinement theorem above and supplies no concurrent race-model composition. The repository documentation explicitly places integration of its Tree Borrows semantics with a race model outside this artifact's scope.

## Boundaries

| Milestone | Established here | Remaining acceptance obligation |
| --- | --- | --- |
| E03 | Actual selected Simuliris proof replay, per-result assumptions and recursive kernel check | E03's broader collection of Rust-logic/modular-effects/ISA artifacts is not completed by this selection alone |
| E18 | Actual Tree Borrows calculus definitions/laws and their checked adequacy | An unbounded relation connecting selected MiniRust/Miri/calculus transitions, retags, ranges and protectors |
| E20 | Checked existing scalar-slot state/resource laws | A byte- and alias-sensitive MiniRust lifetime logic, UnsafeCell masks and adequacy with declared imported relations |
| E23 | Existing calculus allocation/retag/protector and optimization proofs; explicit port prerequisites | Actual allocation, split/recombine, recursive-reborrow, Cell/callback and returned-reference proofs tied to chosen implementation identities |
| E24 | Calculus contextual refinement with recorded source-safety/context/observation premises | Functional/spatial transport and soundness for every permitted safe Rust client, lifetime and implementation/trait instance |

No new API port was attempted in this bounded replay, so there is no failed semantic port to report. The namespace failure is an actual failed setup attempt. Optional SimuLang non-atomic-invariant examples and repository proofs outside the selected dependency closure were not built. No MiniRust, minimize or Miri execution occurred. A complete Rust frontend, compiler, FFI, weak-memory, byte-layout or safe-client correspondence theorem is not established.

An [independent review](support/independent-review.md) refreshed all 24 exact type/assumption observations without recompiling objects and recursively checked the same 517 libraries in 42.339 seconds. The full checker trace is byte-identical; all 706 selected source/object hashes and six tool hashes remained unchanged. [The review record](support/independent-review.json) identifies the reviewed snapshots and actual commands/results. This approves the bounded replay and its stated premises; the broader milestones remain open.

## Evidence

All execution was performed on 2026-10-14. The immutable upstream source is [Simuliris at e3abfcdc](https://gitlab.mpi-sws.org/iris/simuliris/-/tree/e3abfcdc301f92250d4227fc03c00463bf57b982). The complete source archive and the exact Iris/stdpp source archives are preserved under `support/inputs/`, with original source identities in the materialization receipts and package manifest. Their respective SHA256 hashes are `06dbeeb1ddda80ffe93b26fd20d8597f9c9a63767ae2a7e74e4dae696952fb9b`, `3b45252c8b915dcee1149dd0d185391898cc836619b7c4e1fc1f636acb23057b`, and `e9588be3a78ad1b54a045a3237e5ae2ca7e0db8aebf1e0cfe8e90a6a64e0e6f2`.

- `support/checked-project/` preserves all 185 unchanged original files, three unchanged audits, generated Makefile/dependency files and checked objects. Every copied file was compared with the final container SHA256 inventory. `copied-project-file-manifest.json` binds all 591 copied files.
- `support/actual-results.json` contains 24 exact printed types/assumption results and source coordinates/hashes. `logs/recursive-native-checker.stderr` preserves the full 3,908,248-byte native trace; stdout preserves exit/heap information. `loaded-object-stability.json` and the two 517-object hash listings bind actual loaded artifacts.
- `support/logs/` preserves full invocation/status/time/hash records and original stdout/stderr, including installed CLI help, tool identity, source checks, phase monitoring and the failure diagnosis. `binding-failure-artifacts/` and `namespace-rebuild-bindings.json` preserve the failed configuration/objects and their corrected identities.
- `support/parent-runtime-receipts/` preserves the parent's dependency lock, installed/exported switch, source materialization and installation/source-verification receipts. `logs/installed-switch-state.stdout` is the fresh replay-side switch observation. The exact native checker executable SHA256 is `d24cd16bfb4d25f13eba4178ee33eabc128f3ae4c03bebe56bae7521a0081de9`; other tool hashes are in `logs/tool-identities.stdout` and match the final tool snapshot.
- `support/historical-plan/` and `observed-controllers/` retain planning/command provenance, including the diagnosed initial Makefile approach. Historical planning statuses are not current execution results. Nine JSON metadata records (eight invocation records and the historical archive inventory) use an explicit public display-path projection; `public-path-projection.json` records original/public hashes and replacement scope. All streams, source, program, archive and proof bytes are unchanged. Private raw invocation records remain preserved in the assigned execution scratch.

## Revalidation

Run `python3 -B support/verify_package.py` from the package root for the inexpensive package/source/object/audit/trace consistency check. It executes no proof tool and is not a new kernel replay.

For proof revalidation in an independently authorized environment with the exact recorded toolchain and dependency objects, use `support/REPLAY.md`. The cheapest substantive check is the recursive native checker over the preserved objects plus the three fresh observation audits, verifying the loaded-object hashes and the per-constant/global-context distinction. A fresh source replay must start with new owned output state, generate the Makefile from the original `_RocqProject` alone, run the same six full `.vo` seeds, and compile the audits separately with the preserved flags. Do not reuse the failed namespace objects.

After changing source, dependencies or model relations, repeat the 24 exact type/assumption observations and recursive check; successful compilation alone is insufficient. Closing E18/E20/E23/E24 additionally requires constructing and checking the missing correspondence or API proofs, rather than rerunning these existing optimization proofs.
