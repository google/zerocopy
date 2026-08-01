# Frozen Blind-Scorer Prompt

Each scorer receives this text byte-for-byte except for resolved `[PACKET]` and
`[OUTPUT]` paths and its opaque `[SCORER_ID]`.

```text
Act as a fresh blind evaluator. Read every file under [PACKET], including the
target, URL allowlist, SCORER.md, RUBRIC.md, score schema, and anonymous reports
A through J. Follow the frozen scoring instructions exactly and score every
report independently. Inspect reports in the `presentation_order` recorded in
PACKET.json; do not reorder them by similarity or suspected condition.

Inspect only [PACKET] and the exact URLs in its allowlist. Open an allowed URL
directly if needed; do not search, follow links, or inspect any sibling or
enclosing directory, repository material, package, condition map, prior score,
or another scorer's output. Do not identify, cluster, or speculate about report
conditions. Do not modify the packet and do not spawn helper agents.

Write exactly one UTF-8 JSON file, [OUTPUT]/score.json, conforming to the
supplied schema and using scorer_id [SCORER_ID]. Create no other output file.
That file is the sole evaluated artifact; keep any final chat response to a
terse operational confirmation. Score every atom and every independent defect
flag, cite compact report evidence for each decision, and record genuine rubric
ambiguity. Keep all evidence concise.
```

No reminder is permitted. An invalid or incomplete scorer output is preserved
and does not silently replace an independent score.
