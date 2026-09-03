# Rust Audit

{{INVOCATION_BLOCK}}

Operational constraints: use one agent context for this request; do not create
helpers or sub-agents. Do not build, run, test, or edit the target. Inspect only
the declared input paths and provided Rust documentation. Write only the declared output
path.

Resolve the declared target and documentation paths only beneath the fixed
workspace-relative input alias `{{INPUT_ROOT}}`; write only beneath the fixed
workspace-relative fresh output alias `{{OUTPUT_ROOT}}`. Do not resolve or
report either alias as an absolute path.

Analyze `{{TARGET_PATH}}` for task mode `{{TASK_MODE}}`, using only the supplied
project inputs and Rust documentation. The provided Rust documentation is
`{{AUTHORITY_PATH}}`. Produce a complete audit report at the path named
`{{OUTPUT_PATH}}` beneath that output alias, no longer than `{{WORD_CAP}}`
counted words.
Separate inspected artifact facts from semantic propositions, reconcile every
material Rust premise to applicable authority, preserve unresolved root
blockers and their dependent fan-out, and state scoped conclusions without
widening them.

Write a self-contained technical report. Do not discuss how the request was
delivered, your execution environment, session/instruction/tool details, or
filesystem locations outside the declared project; cite project files only by
project-relative path.

Your final response should only confirm the report's declared relative path.
