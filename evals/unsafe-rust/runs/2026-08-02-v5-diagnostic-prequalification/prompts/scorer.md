# Blind Direct-Decision Scorer — DRAFT / UNSEALED

Score all 15 opaque report labels `A` through `O` for mode `{{MODE}}` in the
independently frozen `{{SCORER_ID}}` presentation order. You receive those
reports and every evaluator-only dependency only through the exact content-bound
packet at workspace-relative `input/{{INPUT_PACKET_PATH}}`. You do not receive a
condition map, package identity, schedule, another scorer's output, or prior
scores.

For every label and every manifest atom, decide only whether the atom's
`direct_criterion` is satisfied: `PASS` or `FAIL`. Attest every closed hard-error
and global-defect rule with `present: true/false`; unknown closed-rule IDs are
invalid. Cite report-local evidence for every decision. Give each genuinely
novel potentially material finding a stable ID scoped to this scorer, such as
`s1-N1`; the two independent consistency reviewers classify the normalized
union, and classification disagreements are routed to adjudication.

Do not infer a direct decision from a prerequisite, and do not compute
`blocked_by`, `certificate_decision`, or `root_failures`; the protocol computes
those from the frozen DAG after adjudication. Validate against the schema
`{{SCORE_SCHEMA_PATH}}` beneath that input alias. Emit one mode-level score containing
exactly A–O only at workspace-relative `output/{{OUTPUT_PATH}}`; return only the relative
output path.
