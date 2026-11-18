# Reference corpus binding

This binding selects `zerocopy/reference` and `reference-corpus/1` only when the caller
supplies this file's absolute path, operation and stopping boundary. The corpus
root is its parent. Paths below resolve from that root; cwd and installation do
not select it. The shared-resource record binds the verified public release pin.

| Selection | Bound resource |
| --- | --- |
| Corpus identity and scope | `zerocopy/reference` |
| Interpretation | `reference-corpus/1` |
| Native project policy | `AGENTS.md` |
| Complete adopted report contract | `FORMAT.md` |
| Instance topic vocabulary | `CORPUS.json` |
| Candidate-local validator and tests | `tools/reference.py`, `tests/test_reference.py` |
| Complete research materialization | `skills/reference-research/` |
| Research entrypoint | `skills/reference-research/SKILL.md` |
| Research guidance and contract source | `skills/reference-research/references/research.md`, `skills/reference-research/references/format.md` |
| Existing coverage | `CATALOG.json` and original `reports/<package>/` files |
| Shared source disposition and managed baselines | `SHARED-RESOURCES.json` |

Read the complete selected policy, format, machine vocabulary, research
entrypoint and guidance before dependent work. The shared format owns report
meanings; project policy owns visibility, actions, additional requirements and
publication. Missing resources, unsupported interpretations or genuine semantic
conflicts block dependent operations. Keep separate bindings for separate scopes.

Planning stops at questions and investigation tracks. Maintenance produces final
packages and regenerates the catalog only when names or metadata change. This
binding grants no publication right. For authorized publication, reobserve native
policy and remote state, validate the exact candidate with its own checker, then
follow the sole-parent fast-forward/concurrency/readback protocol in `AGENTS.md`.

Basic research and maintenance need no navigator, index, global skill installation
or toolkit checkout. Optional navigation has a separately selected executable,
source/index, interpretation and cache. New indexes capture exact policy bytes.
Historical images and saved handles continue through their separately selected
qualified retained reader, outside the current runtime. Installing new skills
must not overwrite that reader. A rebuilt image cannot replace an old handle.
