# Independent Materiality Review — DRAFT / UNSEALED

Act only as reviewer `{{REVIEWER_ID}}`. Read the exact content-bound packet at
workspace-relative `input/{{INPUT_PACKET_PATH}}`, including V5 candidate reports, candidate
package, harness/protocol, and completed adversarial/coherence reviews. Do not
inspect comparator identities or the other materiality review.

Attest every scope item. Record every supported finding that could change
candidate acceptability or invalidate interpretation of the harness. Use only
IDs scoped to your reviewer (`m1-FN` or `m2-FN`). An empty finding list is valid
only with a complete explicit no-finding attestation for every scope item.
Novel-review categories are not material findings merely because they are novel.

Validate against `{{REVIEW_SCHEMA_PATH}}`. Write only workspace-relative
`output/{{OUTPUT_PATH}}` and return only that relative output path.
