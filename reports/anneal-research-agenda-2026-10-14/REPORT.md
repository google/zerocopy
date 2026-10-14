# Anneal research agenda, candidate grouping, and evidence interpretation

## Summary

The retained agenda contains 364 stable questions: 100 on unsafe Rust formal-methods foundations, 120 on internal trusted computing base minimization, and 144 on proof-producing compilation. Every question preserves its rationale and tracking issue. A provisional, many-to-many grouping proposes 58 report families; it is a hypothesis about useful publication boundaries, adjustable as research exposes shared evidence or missing distinctions.

The grouping does not certify research completion. The initial content audit identifies reusable portions of 15 existing report packages, with explicit limits; the other 643 baseline packages remain unassessed. New technical reports in this publication add primary-source investigations and bounded experiments while preserving their unproved Rust and toolchain obligations.

## Applicability

The agenda was derived for Anneal main at `8d8ed8dcc98c991d32cee3c3a84e129f29cba136` and the PR #3846 stack at `cce761ad53785973ec2f4a6b13715b770b340c87`. The source corpus baseline is `a0ff759e7d2d9a953f0ac40b326dd23197bd9188`, with 658 packages. These snapshots are distinct subjects; no compatibility of their toolchains is inferred.

Tracking: [formal methods #3865](https://github.com/google/zerocopy/issues/3865), [internal TCB #3866](https://github.com/google/zerocopy/issues/3866), [proof-producing compilation #3867](https://github.com/google/zerocopy/issues/3867), and [candidate grouping #3868](https://github.com/google/zerocopy/issues/3868). The package preserves the questions, rationales, groups, and obligations directly, so interpreting it does not require recovering issue bodies.

## Findings

### Stable questions and revisable report boundaries

`research-questions.json` retains each ID, title, question, rationale, and issue number. `candidate-groups.json` gives each group its scope, boundary, expected evidence, and question IDs. There are 449 memberships covering exactly 364 unique questions: repeated memberships are intentional. A group may split, merge, or become several reports without renumbering the original questions.

Revision 2 adds R084 to G030 because cross-assistant transport needs proof-kernel and statement-interface evidence as well as the SMT certificates covered by G031. G012's interior-mutation, pinning, and progress questions may eventually need separate reports. Neither adjustment changes the underlying question inventory.

Basis: **source**, preserved agenda representations; **derived**, publication organization.

### Anneal requires three connected assurance layers

Logical checking establishes a proposition under its actual assumptions. Semantic correspondence establishes that this proposition concerns the selected source executions, including relevant UB, memory, and progress obligations. Claim binding and coverage establish that the source, generated operations, dependencies, inputs, and configuration are the ones the consumer requested.

A small proof kernel can remove tactic search from logical authority. It cannot by itself justify a producer-selected source AST, decoder domain, layout description, omitted callee, or safety claim. `anneal-obligations.json` preserves O01–O24, including source identity, faithful lowering, source-failure exposure, caller coverage, runtime representation, assumption policy, and final acceptance. It is an engineering obligation inventory, not a proved complete semantics.

For every proposed trust reduction, name the previously trusted component, the replacement certificate or verified implementation, the checked proposition, and the assumptions remaining at its endpoint. This prevents transferring trust to an equally powerful but unnamed importer or acceptance wrapper.

Basis: **derived**, Anneal principles and admission design at the identified stack; bounded evidence in the accompanying source-safety and certification reports.

### Existing evidence is a lead with an exact supported scope

`existing-evidence-leads.json` records substantive inspection of Applicability, Findings, and Boundaries in 15 baseline packages. It contains 59 scoped findings and 217 question memberships touching 148 IDs. Heading references and content hashes identify the inspected evidence. These are partial leads: reading a report is not an upstream rerun or a new primary-source validation.

Absence from this sample means unassessed. It does not establish that a question lacks prior evidence. Conversely, a report title, retrieval label, or repeated question membership does not establish that a complete research question has been answered.

Basis: **source**, retained content-audit representation; **derived**, evidence interpretation.

### Published technical scopes and remaining gaps

`coverage/` preserves scoped question-to-report crosswalks for the certifying-model, proof-kernel, translation-pass, Iris/Rust verification, compiler-family and automation-certificate investigations. Each records what the actual report establishes and the remaining research or implementation scope. These crosswalks include partial evidence and unexamined questions; they are not blanket completion attestations.

The second tranche adds twelve packages: proof-construction/statement authority, verified checker endpoints, Lean admission/import/native controls, Iris adequacy, RustBelt/RustHornBelt contracts, RefinedRust operational/extraction boundaries, Plutus pass relations, Crellvm refinement, property-proof translation, Anneal acceptance/trust gates, exact-pin pure-model controls, and native zerocopy byte-domain controls. The latter enumerate 256 scalar and 65,536 pair encodings; the pure-library run audits 252 declarations under Lean 4.31. These results retain their exact scope and do not close the entire agenda.

Basis: **source**, preserved crosswalks; **execution**, identified technical reports; **derived**, completion interpretation.

The third tranche adds ten packages comparing HOL proof-producing synthesis, constructive imperative refinement, verified compiler endpoints, PCC/TAL, semantic refinement directions, SMT reconstruction, SAT/PB certificates, numerical witnesses, reflected resource gates, and minimal proof interchange. The full ESOP 2007 and LICS 2001 primary papers were acquired and inspected for their mechanism and semantic interfaces. The parent independently replayed the finite refinement witness and both Lean 4.34 certificate controls, reproducing their recorded outputs and axiom dependencies. These ten additions bring the initiative to 31 packages including this agenda; they do not imply 364 completed questions.

The fourth tranche adds nine packages: current Verus, Creusot, Gillian-Rust, symbolic tools and refinement/Horn/Lean-VC boundaries; Aeneas/Charon functionalization and the separate spatial draft; hax/Eurydice and RustCompCert source interfaces; C/resource/effect logics; and modular foreign contracts. Exact source pins, paper identities and archive-member hashes remain distinct. The parent independently checked the consequential primitive, result-status and admission findings, including Soteria's zero-exit partial result, Flux's transitive-sorry gate and selected active RustCompCert/VeriFFI admissions. No upstream verifier build or whole implementation theorem is inferred. The initiative now has 40 packages including this agenda, with additional scoped crosswalks under `coverage/`.

The fifth tranche adds five packages: three checking routes on one byte-arithmetic claim, field/slice frame certificates, data-certificate binding/assumption/failure controls, operational receipts/cache/containment design, and a two-target zerocopy case. The parent replayed all six selected Lean fixtures, both native controls and the complete 38-case protocol, reproducing the expected theorem dependencies and verdicts. The independent macOS containment control denied challenge writes while allowing producer output. Native arm64 and wasm32 zerocopy both passed the full Boolean/pair domains, with distinct recorded layout facts. These bring the initiative to 45 packages including this agenda; explicit frontend, wrapper, compiler and runtime boundaries remain.

### Exact checker versions are a material acceptance premise

The source path fixed by Lean PR #14577 is present without its final nested-parameter type check in both the selected 4.31.0 commit `68218e876d2a38b1985b8590fff244a83c321783` and legacy 4.30rc2 commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. The inspected 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52` contains that check. This comparison establishes source affectedness for the named omitted-validation path, not earliest introduction, exact exploit portability, or universal soundness of a newer kernel.

The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe an adversarial program accepted as a proof of False, including a comparator route and a combined independent-checker exploit. The [fix](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808) preserves and checks the nested parameter applications after restoring declarations. No exploit was executed here. Owned prototype statuses and dependency lists remain recorded observations under a checker-soundness premise; neither an empty axiom set nor agreement between checkers discharges that premise. A future Anneal consumer must pin, justify and revalidate its checker and full dependency closure.

Basis: **source**, independently inspected old/fixed `src/kernel/inductive.cpp`; **documentation**, official release and issue; **derived**, consequences for arbitrary producer acceptance. The affected initiative reports carry this qualification directly.

The eighth tranche adds six packages: exact Lean-Iris construction and adequacy interfaces; current RefinedC/Lithium and CN result paths; RustHorn/Stainless/SAW recursive and callee lifecycles; transfinite termination/refinement; a real legacy pass certificate for the unchanged zerocopy validity module in an owned wrapper; and a complete guarded unsafe Boolean API certificate. The parent reviewed all reports, independently checked consequential source exclusions, and replayed the original toolchain, actual-capture and native-domain controls. Source import, runtime correspondence, unperformed upstream builds and the known checker boundary remain explicit. The candidate now contains 71 initiative packages including this agenda, rather than 364 unconditional proofs.

`remaining-report-plan.json` revises the candidate publication grouping: six included packages, fourteen active investigations and four planned reports. Its original 101-ID gap list is a preserved planning snapshot; the final three audits refined that to 94 gaps before these additions. A report can answer multiple questions; current counts do not fix final boundaries.

The ninth tranche adds seven packages: selected GAT/dispatch laws, one SIMD/union control, whole Arc/hazard/weak-RCU protocol interfaces, a finite pointer-lease interpretation, actual unaligned unwind/vector growth controls, a composed two-target packet API with model/ABI receipt costs, and actual cvc5/Carcara generation/elaboration/checking/diagnostic controls. The parent replayed the original generic/SIMD/pointer specimens and independently inspected consequential framework/SC-fence boundaries. The weak-RCU artifact explicitly includes SC fences, so a limitation of a different named-model snapshot cannot be imported by name. Carcara's actual holey exit-zero result is retained as a distinct acceptance outcome. There are now 78 initiative packages including this agenda; the candidate remaining plan has eleven reports still to integrate/review.

### Research completion is separate from implementation feasibility

A report can resolve what a technique proves, expose a concrete limitation, and specify a discriminating future experiment without implementing an Anneal integration. A negative result can answer a research question when its evidence and scope are sufficient. Missing artifacts, failed access, and unavailable local dependencies must remain operational or epistemic limitations rather than system-level unsupported classifications.

For an experimental question, preserve the tested input, tool identity, complete configuration, statuses, outputs, and scope. An illustrative finite theorem answers its mathematical question while leaving concrete Rust import and operational adequacy open. A format validator establishes structural corpus invariants, not the technical truth or completeness of reports.

Basis: **derived**, research and evidence policy.

## Boundaries

- **Not established:** completion of all 364 questions, a final architecture recommendation, or a production implementation meeting all O01–O24 obligations.
- **Not examined:** a corpus-wide semantic audit of all 658 baseline packages. The bounded reuse audit covers 15 packages only.
- **Unknown:** future optimal report boundaries and the engineering cost of each integration. Group scopes remain provisional.
- **Known distinction:** whole-system external trust remains different from Anneal's internal division between search and checking. Minimizing internal trust does not claim to remove Anneal from an outside caller's TCB.

## Evidence

- **source:** `research-questions.json`, exact original 364 questions and rationales; SHA-256 is recorded in `REPORT.json`.
- **source:** `candidate-groups.json`, revision 2, 58 groups and 449 memberships.
- **source:** `anneal-obligations.json`, 24 explicit acceptance obligations.
- **source:** `existing-evidence-leads.json`, scoped content audit against the pinned baseline; report paths are corpus-relative and hashes identify the actual inspected text.
- **source/documentation:** [Anneal admission design](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/ADMISSION_DESIGN.md), original MIR and obligations preceding source UB.
- **derived:** grouping, completion rules, and assurance-layer synthesis. These organize evaluation and do not add proved Rust semantics.

## Revalidation

Check that the question IDs are exactly R001–R100, T001–T120, and P001–P144; group memberships must cover that set and contain no unknown IDs. When revising boundaries, preserve stable question text or explicitly record the change. Reinspect the cited Findings and Boundaries before promoting a lead to supported coverage; rerun or independently review primary evidence where the claim requires it.

Update the evidence crosswalk after integrating actual reports. Mark a tracking item complete only when its requested scope has a published answer with adequate evidence and explicitly characterized residual implementation work. Do not use topic presence, worker completion, or metadata validation as that test.

*Authored by an AI agent acting on joshlf's behalf.*
