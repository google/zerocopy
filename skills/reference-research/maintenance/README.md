# Standalone maintenance resources

The canonical common contract is `../references/format.md`. The canonical
Python 3.10+ standard-library checker and tests are `reference.py` and
`test_reference.py` in this directory. These paths resolve from this resource,
not from the working directory. The tests expect their native projection below;
stage that projection before running them.

A complete native maintenance materialization contains the whole selected
`reference-research/` skill at `skills/reference-research/`, plus these exact
copies from that leaf:

| Source in the research leaf | Corpus-root destination |
| --- | --- |
| `references/format.md` | `FORMAT.md` |
| `maintenance/reference.py` | `tools/reference.py` |
| `maintenance/test_reference.py` | `tests/test_reference.py` |

The navigator distribution carries another exact copy of `reference.py` for its
pure byte-validation functions. These are physical copies, with one canonical
source. Compare their full bytes and modes at release and materialization
boundaries; do not maintain independent parser forks. Native validation executes
the corpus's `tools/reference.py`, never an installed navigator or this source
file in its skill layout. It derives its own lexical candidate root and accepts
no external-root override.

The instance owns `AGENTS.md`, `CORPUS.md`, `CORPUS.json`, and its README. Record
the selected public source revision, managed paths, source-to-destination mapping,
modes, and baseline SHA-256 values in its maintenance record. Do not point public
copies to a private source repository. Updates compare baseline, local and proposed
resources; reconcile local edits and unknown files rather than replacing them.
This package supplies no automatic updater or permission to change policy.

From any working directory, use the candidate's selected absolute tool path:

```console
python3 /absolute/corpus/tools/reference.py check
python3 /absolute/corpus/tools/reference.py catalog
python3 /absolute/corpus/tools/reference.py check
python3 -m unittest discover -s /absolute/corpus/tests -v
```

Regenerate only when package names or metadata changed. Run the tests after
changing the checker or tests. Validate the exact prospective Git tree under
project policy; tool success does not inspect Git state or establish semantic
report quality. The checker remains usable without research resources or a
navigator, while research requires its complete bound guidance.
