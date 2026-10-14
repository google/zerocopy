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

`coverage/` preserves scoped question-to-report crosswalks for the certifying-model, proof-kernel, translation-pass and Iris/Rust verification investigations. Each records what the actual report establishes and the remaining research or implementation scope. These crosswalks include partial evidence and unexamined questions; they are not blanket completion attestations.

The second tranche adds twelve packages: proof-construction/statement authority, verified checker endpoints, Lean admission/import/native controls, Iris adequacy, RustBelt/RustHornBelt contracts, RefinedRust operational/extraction boundaries, Plutus pass relations, Crellvm refinement, property-proof translation, Anneal acceptance/trust gates, exact-pin pure-model controls, and native zerocopy byte-domain controls. The latter enumerate 256 scalar and 65,536 pair encodings; the pure-library run audits 252 declarations under Lean 4.31. These results retain their exact scope and do not close the entire agenda.

Basis: **source**, preserved crosswalks; **execution**, identified technical reports; **derived**, completion interpretation.

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
