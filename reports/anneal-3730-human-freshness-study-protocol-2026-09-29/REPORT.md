# Protocol for I141 human understanding of freshness and failure

## Summary

This package specifies a human comprehension study for [#3731 I141](support/issue-scope.md). It has **not been run**: no participants were recruited, no consent was obtained, no real Anneal UI was available for this package, and there are no response or outcome data. The protocol tests whether people identify the subject of a result, choose a safe next action, and avoid an overbroad verification claim across six failure states and two current-state controls.

## Applicability

The study is intended for a future Anneal Rust annotation interface that can truthfully expose source/model/import/proof generation and status. `support/stimuli.json` is a case specification and answer key, not evidence that Anneal implements these states or screens. Two candidate presentations must contain the **same factual content and actions**: A groups status inline with expandable provenance; B groups it in a structured subject/status/action panel. Their exact rendered wording, accessibility tree, and UI build hashes must be frozen after a separate comprehension pilot and before the scored sessions. If the product cannot truthfully render any case, defer that case and record the gap; do not invent a passing UI state.

The stimuli draw failure shapes from distinct local evidence: an old goal/proof card in the [agent workflow evaluation](../anneal-3730-agent-workflow-evaluation-v4-30-0-rc2/REPORT.md); stale imported artifacts and worker refresh reports; a late cancelled result in the [synthetic generation recovery run](../anneal-3730-generation-recovery-2026-09-29/REPORT.md); unsupported translation boundaries in the Charon/Aeneas and acceptance reports; an approximate generated-to-Rust anchor in the [projection provenance fixture](../anneal-3730-projection-provenance-2026-09-29/REPORT.md); and an expired handle in the [retention model](../anneal-3730-retention-economics-v4-30-0-rc2/REPORT.md). These sources motivate scenarios, not observed human error rates or integrated Anneal behavior.

## Findings

### Study question and tasks

The primary question is whether a participant can, from the presented UI, (1) identify which Rust/source/model/proof generation the visible result concerns, (2) choose a sound next step, and (3) state only the verification conclusion the result supports. The exact neutral prompt is in `support/stimuli.json`; it asks those three questions and allows uncertainty and requests for another view. It never says a particular case is stale or asks the participant to find a planted error.

The eight case specifications are S1 stale model, S2 pending imported artifact, S3 late cancelled work, S4 unsupported translation, S5 approximate location without edit authority, S6 expired goal handle, C1 current exact editable goal, and C2 current scoped checked claim. Each has three UI facts, expected subject, sound next step, and an unsafe inference kept out of participant-facing material. C1 and C2 check whether a design causes needless rejection of current usable results. S5 distinguishes safe navigation from authority to apply an automatic source patch. S4 asks people to recognize that an unsupported translation does not create a checked Rust claim. No task requires reading generated Lean to score correctly; requests to open it are recorded as a burden indicator.

### Assignment and participant selection

Plan 32 adult developer participants: 16 Rust-first developers who do not routinely author Lean proofs, and 16 developers with both Rust and Lean experience. Recruit across experience levels and accessibility needs without requiring employees, maintainers, or authors of this fixture. Screen experience before assigning slots; exclude anyone who authored the UI or answer key from scored participation. These are purposive strata for design feedback, not a representative sample of all Rust users. Offer the same compensation and time allowance in each stratum.

Within each stratum, assign eight participants to A and eight to B. A participant sees all eight cases once under one presentation, avoiding within-person A/B learning. In each stratum and presentation, the eight cyclic rotations put every case in every ordinal position once. `support/assignments.csv` provides 32 pseudonymous slots and the exact schedule; allocate the next unused slot within the screened stratum without choosing based on expected performance. Use a neutral practice task distinct from all eight scored cases. Give no correctness feedback until the end. Permit participants to inspect other UI views and record which they requested; do not instruct them to open generated Lean.

The within-condition Latin rotation and the equal A/B facts limit order and information-content confounding. They do not blind the visual presentation or make this small study an efficacy trial. If two variants differ in wording, warning strength, available action, or semantic status, repair the materials before recruitment; otherwise the comparison would mix layout with content.

### Consent, privacy, and session operation

The study owner must approve a consent/privacy procedure and determine whether organizational or institutional review applies **before recruitment**. `support/CONSENT_SCRIPT.md` is an unapproved draft. Participation and optional recording require separate affirmative choices. Use synthetic code and identities only; do not access or collect participant repositories, secrets, personal account content, or production data. Store consent and the identity-to-slot mapping separately from coded responses under access controls and a specified retention/deletion schedule. Default to no audio or screen recording. Offer withdrawal and deletion according to the approved procedure. Accommodations and skipped tasks are recorded without sensitive detail. The operator pauses when consent is absent, when a participant withdraws, or when accidental private data appears.

For each case, capture the three answers verbatim, elapsed time, confidence from 1–5, extra views requested, and whether generated Lean was opened. The operator uses neutral probes such as “What led you to that choice?” only after the initial answer and records their use. No leading corrections or hints are allowed during scored tasks. `support/RESULTS_FORM.md` and the empty `support/results-template.csv` provide fillable forms; participant data must be stored in approved study storage, not committed into this report package.

### Coding and analysis plan

Before opening the answer key, redact variant labels from verbatim answers where feasible. Two coders independently assign subject score 0/1/2, action score 0/1/2, overclaim 0/1, and (S5 only) location authority safe/unsafe; the anchors are in the form. Preserve both codes and adjudicate disagreements with a stated rationale. The primary per-task success indicator is `subject=2 AND action=2 AND overclaim=0` (and safe location authority for S5). Report the raw numerator/denominator **by case and presentation**, missing/skipped tasks separately, and the Rust-first stratum separately. Also report each component, unsafe-inference counts, time distribution, confidence, extra-view requests, and generated-Lean opens. Use descriptive uncertainty intervals if comparing proportions; do not interpret a small A/B difference as a powered significance result. Quote only de-identified examples with consent.

Predeclared decision rule: any uncorrected UI statement that labels an obsolete, pending, cancelled, unsupported, or expired result as current/verified is a semantic defect irrespective of participant scores. If two participants make the same high-severity unsafe verification inference in one case, pause that case, inspect the UI and notes, and decide whether to redesign and restart with a new protocol/UI version; do not pool pre- and post-change observations as one condition. Otherwise complete the planned 32 slots unless the study owner stops for consent/privacy/safety reasons. At the end, prioritize cases with observed unsafe actions or frequent requests for generated Lean, then revise interface wording/structure without weakening status semantics. Record all changes and rerun affected cases rather than silently recoding them.

## Boundaries

- **Pending human gate:** No participant has viewed these stimuli. The empty results template and generated slot schedule are planning artifacts, not observations or a simulated study.
- **Pending implementation gate:** A real Anneal UI, truthful end-to-end state labels, a frozen rendered A/B pair, and approved consent/privacy operations are needed before a result can address I141's human-understanding claim. A paper or agent card check is only a materials pilot.
- **Unknown:** Whether A or B is clearer, whether either avoids unsafe repairs or needless generated-Lean inspection, whether tasks are understandable to ordinary Rust users, and whether the proposed 32-person sample is sufficient for any particular effect size. No effect size or error rate is inferred here.
- **Not examined:** live production collaboration, accessibility testing beyond planned accommodations, screen-reader behavior until rendered UI exists, and long-term learning. The current scenario wording contains invented revision labels as controlled stimuli; it must be checked against the actual interface vocabulary and semantics before use.
- **Scope of controls:** C2's “checked” conclusion is restricted to the highlighted claim and identified generation; it never authorizes a whole-program claim. A goal visible in C1 does not imply a checked obligation.

## Evidence

The exact I141 text is preserved in `support/issue-scope.md`, SHA-256 `0b8eba07c4e1897fbe97ec5e5c2623a359cab9138b8a5a4b1ce3e09d8a9155f6`. `support/stimuli.json` (SHA-256 `e20a1c678c704af29040a45d83f0cd595cbcf3f9130984c6f6962749c50a72a6`) contains the eight keyed specifications and neutral participant prompt. `support/make_assignments.py` generates `support/assignments.csv` (SHA-256 `6df463c66307078814937fd84cf3e1112eaf5bdcc30713c10e6d41e79aa65b01`). `support/check.py` validates schema, class coverage, 32 slot assignments, full order/condition balance, and the absence of response rows. It returned `OK: eight keyed cases; 32 empty participant slots; full order/condition balance; no response rows` on 2026-09-29. The report metadata subject is the issue-text snapshot, not a tested UI implementation.

This package has no collected human data. Its evidence role is **derived protocol design** grounded in the cited component execution/model reports and the I141 research question. It is not **execution** or **user evaluation** evidence for I141.

## Revalidation

Run `python3 support/check.py` to validate internal completeness. Before recruitment, verify the latest I141 scope, review every scenario against the actual Anneal state machine, render A/B with identical facts and accessible language, pilot materials with separate volunteers, approve consent/privacy, freeze UI/protocol hashes, and record deviations. Only actual consenting participants using that frozen interface can produce the human comprehension evidence requested by I141.
