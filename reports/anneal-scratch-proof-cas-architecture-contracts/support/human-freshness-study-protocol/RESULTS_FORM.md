# Blank session and coding form

This form is a template, not a record of a participant. Use `results-template.csv` for one row per case. Store consent and any identity-to-slot mapping outside the report repository in approved, access-limited storage.

## Session

- Slot ID: ______
- Experience stratum (screened before assignment): Rust-first / Rust-and-Lean
- UI build and protocol revision/hash: ______
- Presentation assignment and eight-case order from `assignments.csv`: ______
- Date/time and operator: ______
- Consent recorded by approved process: yes / no (if no, stop)
- Recording optional consent: yes / no / no recording offered
- Accessibility needs or accommodations, without sensitive detail: ______
- Practice case completed before scored tasks: yes / no
- Protocol deviations, interruptions, and reasons: ______
- Withdrawal requested: yes / no; retained data disposition: ______

## Each case (repeat eight times)

Case ID: ____  Presentation: ____  Start time: ____  Elapsed seconds: ____

1. Which source/model/proof generation does this result concern? Participant's exact response: ______
2. What would you safely do next? Participant's exact response: ______
3. What would you trust as verified now? Participant's exact response: ______
4. Confidence (1 very unsure, 5 very sure): ____
5. Extra views requested; generated Lean opened voluntarily? ______
6. Observer notes about hesitation or misunderstanding, with identifying text removed: ______

Independent coder A: subject 0/1/2 ____; action 0/1/2 ____; overclaim 0/1 ____; location authority N/A/safe/unsafe ____.

Independent coder B: subject 0/1/2 ____; action 0/1/2 ____; overclaim 0/1 ____; location authority N/A/safe/unsafe ____.

Adjudicated values and short rationale: ______

## Debrief

- Which labels or states were confusing? ______
- Did any view suggest a result was current or verified when it was not? ______
- Did the UI require opening generated Lean to understand the next step? ______
- Preferred changes in participant's words: ______
- Operator notes and adverse events: ______

## Coding anchors

- **Subject 2:** explicitly identifies the case's expected generation and its relation to current Rust; **1:** identifies stale/current direction but omits a material model/import/handle distinction; **0:** chooses wrong subject or treats absent current output as present.
- **Action 2:** gives the case's sound next step or an equivalent safe path; **1:** safe but incomplete/deferred; **0:** follows the listed unsafe inference or proposes an unsound edit/claim.
- **Overclaim 1:** claims verification beyond the case's current scoped checked result, including stale, pending, cancelled, unsupported, open-goal, or whole-program claims; otherwise **0**.
- **Location authority:** for S5, **safe** means approximate navigation is not treated as authority for an automatic source patch; **unsafe** means it is. N/A for all other cases.
- The answer key in `stimuli.json` is unavailable to participants and is provided to coders only after verbatim responses are captured. Coders work independently, blind to A/B where text redaction permits, then adjudicate disagreements. Retain both original codes.
