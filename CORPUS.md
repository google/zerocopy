# Zerocopy reference corpus binding

This binding selects the `zerocopy/reference` corpus and the `reference/1`
interpretation. It applies when the caller explicitly selects the absolute path
to this `CORPUS.md` and names the operation and stopping boundary. The corpus root
is the directory containing that selected file. All paths below are relative to
that bound root; the working directory or an installed skill does not select it.

| Selection | Bound resource |
| --- | --- |
| Corpus ID and scope | `zerocopy/reference` |
| Interpretation | `reference/1` |
| Corpus root | Parent directory of the caller-selected absolute `CORPUS.md` |
| Native policy | `AGENTS.md` |
| Native report format | `FORMAT.md` |
| Candidate-local validator | `tools/reference.py` |
| Native validator tests | `tests/test_reference.py` |
| Complete research materialization | `skills/reference-research/` |
| Research entrypoint | `skills/reference-research/SKILL.md` |
| Common research guidance | `skills/reference-research/references/research.md` |
| Selected interpretation guidance | `skills/reference-research/references/reference-1.md` |
| Existing coverage | `CATALOG.json` and original `reports/<package>/` files |

Before relying on the research workflow, read the complete selected policy,
format, research entrypoint, common guidance and `reference/1` guidance. Missing
required resources, an unsupported requested interpretation or conflicting
bindings block that dependent operation. Carry a separate binding for each
selected corpus scope. Other bundled interpretation resources do not select a
different corpus or change this branch's report requirements.

The caller selects planning, report maintenance or an authorized publication
operation. Planning stops at questions and investigation tracks. Maintenance
produces report packages and regenerates the catalog when package names or
metadata change. This binding grants no publication right. For publication,
reobserve native policy and current remote state, then follow the candidate
validation, concurrency and readback protocol in `AGENTS.md`.

Native maintenance uses this branch's candidate-local standard-library validator
and complete research materialization. It needs no navigator, captured index,
toolkit checkout, packaging environment or host-global installation. Query the
catalog programmatically and read selected original reports with their
qualifications. Optional navigation receives its own explicit interpretation,
source/index, executable and cache binding; installation supplies no corpus
selection or publication authority.
