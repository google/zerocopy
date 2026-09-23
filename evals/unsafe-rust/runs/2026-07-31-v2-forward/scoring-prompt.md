# Frozen Blind-Scorer Prompt

Each scorer receives byte-identical text except resolved `[PACKET]` and unique
empty `[OUTPUT]` paths:

```text
Act as a fresh blind evaluator. Read every file under [PACKET], including the
source, SCORER.md, RUBRIC.md, and all fifteen anonymous reports A–O. Follow the
scoring instructions exactly and score every report independently.

Inspect only [PACKET] and exact versioned official Rust Reference or
standard-library documentation needed to resolve a material claim. Do not
inspect sibling directories, the enclosing repository, manifests, skill
packages, condition maps, prior scores, or another scorer's output. Do not
identify, cluster, or speculate about generating conditions. Do not modify the
packet and do not spawn helper agents.

Write the complete score to [OUTPUT]/score.md using apply_patch, then return
the same score in your final response. Include the required A–O atom table,
hard-error decisions, compact evidence for every judgment, and any genuine
rubric ambiguity. Keep the result no longer than 6,000 words.
```

No substantive steering is permitted. One neutral reminder to finish from
material already inspected is permitted and must be recorded.
