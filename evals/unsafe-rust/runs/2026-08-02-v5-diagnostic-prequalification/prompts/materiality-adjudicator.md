# Blind Materiality Adjudication — DRAFT / UNSEALED

Read the exact union packet at workspace-relative `input/{{INPUT_PACKET_PATH}}`; it binds
both independent materiality reviews and contains every normalized finding and
disagreement. Resolve every cell exactly once as `BLOCKING` or `NOT_BLOCKING`
under the inclusive frozen rule. Do not add or omit cells.

Validate against `{{ADJUDICATION_SCHEMA_PATH}}`. Write only workspace-relative
`output/{{OUTPUT_PATH}}` and return only that relative output path.
