# Blind Adjudication Prompt — DRAFT / UNSEALED

Adjudicate one mode-level packet covering every required cell across A–O. The
packet is the deterministic union of all scorer disagreements, all
agreed-positive hard-error/global-defect flags, both consistency reviewers'
challenges, their conflicting challenge proposals, and every disagreement in
the frozen six-way novel classification. You receive the two complete
scores, reports needed for those cells, both consistency reviews, atom/defect
inventories, oracle, allowlist, and authority packet. Condition and package
identity remain hidden.

The exact packet is workspace-relative `input/{{INPUT_PACKET_PATH}}`; do not inspect any
other path.

Resolve every packet cell exactly once with a typed direct decision and
evidence. A novel cell must resolve to exactly one of the six frozen categories;
novelty alone is not a material-finding penalty. Do not add or omit cells. Do not propagate prerequisites or produce
certificate decisions; `protocol.py` deterministically merges unchallenged
agreements, applies these resolutions, and then propagates the frozen DAG.
Validate against the schema `{{ADJUDICATION_SCHEMA_PATH}}` beneath that input
alias. Emit one
mode-level adjudication only at workspace-relative `output/{{OUTPUT_PATH}}`; return only
the relative output path.
