# Bounded Simuliris replay and E23 proof-port plan

The selected source is ready for a parent-reviewed runtime decision. **Nothing has been compiled or installed.** The immutable direct dependency chain is now resolved; the parent still needs to acquire/hash the exact dependency sources, review their build/install scripts, freeze the remaining solver-selected packages and issue READY. The existing Coq 8.19/Iris-2024/Elpi-2 prefix is not this environment.

The provided Simuliris archive names revision `e3abfcdc301f92250d4227fc03c00463bf57b982` and independently hashes to `06dbeeb1ddda80ffe93b26fd20d8597f9c9a63767ae2a7e74e4dae696952fb9b`: 636,691 compressed bytes, 185 regular files, 3,186,091 expanded regular-file bytes, including 172 `.v` sources. `archive-inventory.json` records every regular file. The parent's acquisition receipt identifies the full-revision GitLab archive URL. No archive script was executed; no source or container build, install, Git operation or cleanup occurred.

## Exact environment proposed for review

| Component | Exact proposed subject | Basis and material gate |
| --- | --- | --- |
| OCaml | 4.14.4, parent-selected | Source CI names 4.14.0. Rocq 9.2 requires ≥4.14.0; Elpi 3.7.3 requires ≥4.13; the proposed patch release satisfies the declared gates. Its Simuliris build has not been observed. |
| Dune | 3.17.2 | Satisfies Rocq runtime ≥3.8 and <3.24, Equations ≥3.13, and Rocq-Elpi ≥3.13 and <3.24. |
| Rocq | runtime/core 9.2.0, with `coq-core.9.2.0` compatibility binaries | README, CI and `_RocqProject` select 9.2; Equations needs the compatibility package for Dune's Coq language. The package file's Equations 9.1 alternative does not remove the 9.2-specific source requirements. |
| Rocq stdlib | 9.2.0, explicitly proposed | Iris/stdpp allow ≥9.0, Equations requires ≥9.1. This exact stdlib pin is a configuration choice, not a lockfile fact in Simuliris. |
| Iris | `rocq-iris.dev.2026-09-10.3.b3495ef9` | Full source commit `b3495ef9f0805b0dc7c1b1abbdc8cf473ede121b`, repository `rocq-iris/iris`. |
| stdpp | `rocq-stdpp.dev.2026-09-09.1.c3186aad` | Iris's exact dependency; full commit `c3186aad493872e3a9774ac0b42ca2f591b05835`, repository `rocq-iris/stdpp`. |
| Equations | `rocq-equations.1.3.2+9.2` | Requires Rocq ≥9.2 and <9.3, stdlib ≥9.1, OCaml ≥4.10. |
| Rocq-Elpi | `rocq-elpi.3.5.1` | Iris requires ≥3; this selected release accepts Rocq ≥9.0+rc1 and <9.4, OCaml ≥4.10, and Elpi ≥3.7.1 and <3.8. |
| Elpi | `elpi.3.7.3` | Fixed source checksum and OCaml ≥4.13; no substitution with the old 1.19/2.x environment. |

The parent-fetched Iris/stdpp package metadata comes from immutable Iris-opam snapshot `3c21518b509d33676776c36e160de1d76835b801`. Their raw SHA256s are respectively `bec95f6c10b8cf47a989e1bf88e35dfe05e2e6979ab57c7c8360689534b2b9d0` and `90373147396e6e5645375ac285e2a9739e01c8da7f7227bf04b86593fea58d16`. Both files are preserved here. Earlier web raw/blob/API frontend attempts were inaccessible through that tool; the parent's actual GitLab API retrieval resolved those route failures without changing the selected subjects.

I independently fetched the primary release-package metadata for Equations, Rocq-Elpi and Elpi. Their returned text reproduces Git blob SHA1s `0425d1c488ba32f54dbf3d58e21572da5507a3a2`, `91485f08c714e6c498a39c80408eb3120c419dd8`, and `1a800a40fef8d672ef073102f1a51a6306905947`. `primary-package-metadata.json` preserves that text, coordinates, archive URLs/checksums and the independent blob check. `DEPENDENCIES.json` consolidates exact subjects and remaining setup conditions. All compatibility conclusions above concern declared dependency gates; an actual successful build is still required.

Primary metadata: [Rocq runtime 9.2.0](https://opam.ocaml.org/packages/rocq-runtime/rocq-runtime.9.2.0/), [stdlib 9.2.0](https://opam.ocaml.org/packages/rocq-stdlib/rocq-stdlib.9.2.0/), [Equations metadata](https://github.com/rocq-prover/opam/blob/master/released/packages/rocq-equations/rocq-equations.1.3.2%2B9.2/opam), [Rocq-Elpi metadata](https://github.com/rocq-prover/opam/blob/master/released/packages/rocq-elpi/rocq-elpi.3.5.1/opam), [Elpi metadata](https://github.com/ocaml/opam-repository/blob/master/packages/elpi/elpi.3.7.3/opam). Moving repository URLs describe acquisition locations; preserved blob identities fix the inspected metadata.

## Selected existing proofs and their actual premises

The preferred first wave builds the following seeds, not the default full examples target. The comment-stripped static import graph estimates **78 project modules total**, 1,777,182 source bytes, for generic adequacy, Tree Borrows core, two contextual examples and the sequential read-reorder result. This is an estimate from source imports; actual `rocq dep`/generated Makefile closure after READY is authoritative. No selected imports need HeapLang, stdpp bitvector/unstable, ITree or Paco.

| Phase | Explicit original seeds | Existing result and limits |
| --- | --- | --- |
| Generic adequacy | `theories/simulation/adequacy.vo` | `slsls_adequacy` assumes its BI/satisfiability classes, initial-state relation, related programs, state interpretation, program ownership, related entry argument and observation bridge. `prog_ref` additionally assumes source safety and yields target safety, target-return → matching source-return, and target fair divergence → source fair divergence. |
| Tree Borrows core | `theories/tree_borrows/adequacy.vo`, `theories/tree_borrows/examples/lib.vo` | Actual whole-program/open-context adequacy, structural/reflexivity/context results and allocation helpers. Context quantification is over the calculus's well-formed closed function bodies and well-formed closing contexts, with no literal pointers. It is not a typed Rust safe-client theorem. |
| Protector/unknown-code examples | `.../examples/protected/mutable_reorder_write_up_activated_paper.vo`, `.../examples/unprotected/shared_delete_read_escaped.vo` | Each file has a logical-relation proof and a closed `ctx_ref` corollary. Unknown code/closure environments, activation, protector map and end-call restoration remain in the actual source proof; no premise is erased for the audit. |
| Sequential reads | `theories/tree_borrows/read_read_reorder/read_reorder.vo` | `read_reorder` requires distinct binder names and proves the defined `eventually_equal` relation. That relation quantifies over well-formed states and a finite no-termination/equal-reachable-state prefix with no forked step. It is not the concurrent Simuliris contextual-refinement theorem. |

The TB model includes explicit ranges, lazy per-location permissions, strong/weak protectors and `InteriorMut` semantics. Its memory stores scalar slots: `examples/lib.v:6–7` explicitly makes a pointer or integer occupy one slot. It supplies no MiniRust byte-layout/provenance import theorem.

`TARGETS.json` selects 24 actual constants with exact file/line/source hashes; three `PlannedAudit*.v` files propose only imports, full `Check @...` and `Print Assumptions`. These are uncompiled source-derived names, not claimed observations. They include the resource/retag/protector interfaces needed to assess E23 rather than only headline adequacy. Comment-stripped source inspection found no live axiom/admission declarations in the 172 project sources. Two aborted attempts exist outside the preferred closure; historical `Axioms:` text in example comments is not an active declaration or a fresh assumptions audit. The comments suggest classical/indefinite-description dependencies for some examples, but actual kernel assumption output must decide the result.

Optional later phase: SimuLang's `na_inv/adequacy.vo` adds roughly 22 project modules, bringing the estimated cumulative closure to 100. It examines that separate calculus's non-atomic/race-aware logic. It must not be cited as a proof that the Tree Borrows instance already has the same race model. It is excluded from the preferred initial allocation unless the parent approves the extra phase.

## E23 port frontier and milestone scope

`E23-PORT-PLAN.md` maps allocation, splitting/recombination, recursive reborrowing, Cell/callback and returned-reference obligations to existing interfaces and missing work. Two source facts prevent counting replay as a completed API port:

1. `new_place_safe_reach` is conditional. `simulation/language.v:1056` defines `safe_reach P e σ Φ` as **source safety implies** existence of a reachable state satisfying Φ. It does not establish allocation/API safety for arbitrary inputs.
2. `logical_state.v:855–857` explicitly says `array_tag` is not actually an array; it owns one ghost-map value for `(tag, block)`. A standard separating-conjunction array split is not supplied by that definition. Moreover `pointer_kind_to_tag_unprotected` returns `None` for `InteriorMut`; the protected shared-InteriorMut mapping also returns `None`. Semantics supporting `Cell` does not automatically supply the requested exclusive API resource rule.

The allocation helpers and callback-style refinement examples are useful existing proof subjects. This archive has no identified theorem proving the requested complete Rust allocation/split/reborrow/Cell/returned-reference API collection. Constructing those ports and preserving their actual implementation identities and failed proof obligations remains E23 work. A later named Rust implementation instance also needs the appropriate operational/resource correspondence before it can count as a Rust API port.

An E03 replay pass would establish only the selected actual Simuliris proof/assumption closure. It would not complete E03 across other artifacts, construct E18's MiniRust/Miri/calculus simulation, construct E20's byte/alias/lifetime logic, or discharge E24's safe-client proof transport. No MiniRust/minimize/Miri or stopped E05 execution is proposed.

## Bounds and acceptance method

Propose one proof worker, two container CPUs, 3 GiB memory and **≤1 GiB additional Simuliris outputs**. Suggested stop caps: generic 5 min; TB core 30 min; the two contextual examples 15 min; sequential reads 10 min; annotations plus recursive checker 20 min. These are stopping limits, not success/runtime predictions. Dependency installation is a separate parent allocation; a candidate cap is one installer/build worker, 60 min and 4 GiB new setup disk, subject to the parent's dry-run/source-size review.

After READY: verify exact source/tool/package identities and absence of project proof objects; generate the original project Makefile; use explicit full `.vo` targets at `-j1`; compile all three observation-only annotations; and recursively run native `rocq check`/`rocqchk` on the original seeds and annotations with no `-admit`, `-norec`, proof-skipping or unsafe-checking relaxation. Capture per-constant full types and assumptions separately from the checker's global import context, loaded-object hashes, all process statuses and complete logs. Do not infer the result from source `Qed` or a successful build alone. `BUILD-AND-AUDIT-COMMANDS.md` gives concrete proposed commands and identity gates. Unexpected panic/assertion/invariant failure stops the affected path for diagnosis; no silent source/compiler/dependency update or weakened theorem follows.
