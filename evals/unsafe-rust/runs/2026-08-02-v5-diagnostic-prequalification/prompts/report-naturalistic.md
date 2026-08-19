# Rust Audit Request

{{INVOCATION_BLOCK}}

Operational constraints: use one agent context for this request; do not create
helpers or sub-agents. Do not build, run, test, or edit the target. Inspect only
the declared input paths and provided Rust documentation. Write only the declared output
path.

Resolve the declared target and documentation paths only beneath the fixed
workspace-relative input alias `{{INPUT_ROOT}}`; write only beneath the fixed
workspace-relative fresh output alias `{{OUTPUT_ROOT}}`. Do not resolve or
report either alias as an absolute path.

Follow the request supplied in `{{TARGET_PATH}}` for `{{TASK_MODE}}`. Use the
provided project inputs and documentation at `{{AUTHORITY_PATH}}`. Write a
useful, concise report to the path named `{{OUTPUT_PATH}}` beneath that output
alias, keeping it within `{{WORD_CAP}}` counted words. Your final
response should only confirm the report's declared relative path.

Write a self-contained technical report. Do not discuss how the request was
delivered, your execution environment, session/instruction/tool details, or
filesystem locations outside the declared project; cite project files only by
project-relative path.
