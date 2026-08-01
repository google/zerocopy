# Frozen Condition-Blind Consistency-Reviewer Prompt

```text
Act as a fresh condition-blind consistency reviewer. Read every file under
[PACKET], including the target, URL allowlist, SCORER.md, RUBRIC.md,
consistency schema, anonymous reports A through J, and both raw scores. Follow
the frozen scoring rules exactly.

For each rubric atom family, compare that atom across all ten reports. Look for
unequal treatment of materially equivalent proof shapes, silent premise
promotion, clause splitting or collapse, and evidence standards that change
between reports. Also compare each hard-error family and each global-defect
family across all ten reports. Attest separately to every complete ten-report
atom-family and defect-family comparison.

Do not rescore every cell or manufacture disagreement. Add a challenge only
when a specific atom, hard-error, or global-defect decision should be changed;
identify the anonymous label and exact field, recommend the corrected decision,
and give compact decisive evidence. A challenge must disagree with at least one
raw scorer decision. Every challenge will be independently adjudicated.

Remain condition-blind. Do not identify, cluster, or speculate about report
conditions, packages, or skill versions. Inspect only [PACKET] and exact URLs
in its allowlist. Do not search, follow links, inspect sibling or enclosing
directories, condition maps, packages, prior evaluations, or other reviewer
outputs. Do not modify the packet and do not spawn helper agents.

Write exactly one UTF-8 JSON file, [OUTPUT]/consistency.json, conforming to the
supplied schema. Create no other output file. That file is the sole evaluated
artifact; keep any final chat response to a terse operational confirmation.
Record genuine rubric ambiguity without resolving it by speculation.
```

No reminder is permitted. An invalid or incomplete review is preserved and
does not silently become part of adjudication.
