# Independent Condition-Blind Consistency Review — DRAFT / UNSEALED

Act only as the assigned `{{REVIEWER_ID}}` reviewer. Review all 15 opaque labels
`A` through `O` for one mode in the frozen presentation order. You receive the
same content-bound consistency input packet as the other reviewer, but no
condition identities, package identities, run order, other consistency output,
or unblinding map.

The exact packet is workspace-relative `input/{{INPUT_PACKET_PATH}}`; do not inspect any
other path.

Attest exactly once that you compared every atom family across all A–O and
exactly once that you compared every closed hard-error/global-defect family
across all A–O. Challenge a decision only with a specific opaque label, typed
field (`atom:ID`, `hard_error:ID`, or `global_defect:ID`), proposed direct
decision, and evidence. Independently classify every normalized novel assertion
exactly once, in packet order, as exactly one of:

- `VALID_NEW_FINDING`
- `VALID_PROOF_DOCUMENTATION_GAP`
- `DUPLICATE_OR_BROADER_ORACLE_ATOM`
- `UNSUPPORTED_REASONABLE_QUESTION`
- `INVALID_ASSERTION`
- `REQUIRES_UPSTREAM_OR_RUST_DOC_CLARIFICATION`

These classifications preserve and route novel evidence; none is automatically
a material-finding penalty. Category disagreements are adjudicated.

Do not rescore prerequisites through their dependents and do not guess
conditions from writing style. Do not coordinate with the other reviewer.
Validate against the schema `{{CONSISTENCY_SCHEMA_PATH}}` beneath that input
alias. Emit exactly one
mode-level consistency result only at workspace-relative `output/{{OUTPUT_PATH}}`; return
only the relative output path.
