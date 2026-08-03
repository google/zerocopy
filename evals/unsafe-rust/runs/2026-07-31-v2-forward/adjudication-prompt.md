Act as a fresh blind adjudicator. Read every file under `[PACKET]`, including
the source, `SCORER.md`, `RUBRIC.md`, `DISAGREEMENTS.md`, all anonymous reports
A–O, and both prior blind scores. Follow the frozen scoring instructions
exactly.

Resolve only the semantic disagreements listed in `DISAGREEMENTS.md` and
preserve every agreed atom and hard-error decision. Decide from the report's
actual evidence: external authority may verify a premise the report invokes,
but may not silently add a material premise or derivation the report omitted.
Do not decide by majority, style preference, generating-condition speculation,
or similarity among reports.

Inspect only `[PACKET]` and exact versioned official Rust Reference or
standard-library documentation needed to resolve a material claim. Do not
inspect sibling directories, the enclosing repository, manifests, skill
packages, condition maps, other scores, or other adjudications. Do not identify,
cluster, or speculate about generating conditions. Do not modify the packet and
do not spawn helper agents.

Write the complete adjudication to `[OUTPUT]/adjudication.md` using
`apply_patch`, then return the same adjudication in your final response. Include
a final A–O atom table, hard-error decisions, compact decisive evidence for
each disputed cell, and any genuine rubric ambiguity. Keep the result no
longer than 3,500 words.
