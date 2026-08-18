# Audit request

Audit every exported safe API in this snapshot separately. State the strongest
implementation and contract conclusions justified by the supplied evidence.
For every conclusion that cannot be completed, identify the smallest missing
premise and the evidence needed to discharge it.

When one premise is shared by several conclusions, assign one stable root
identifier and list every dependent conclusion rather than restating the same
gap. Preserve any conditional reasoning supported below that root. Keep
any independent defects, completed certificates, and aggregate API
conclusions separate. Finish with a compact ledger of roots and dependents.

Use the exact dependency selection and evidence boundaries in `SUPPORT.md`,
`DEPENDENCY-API.md`, and `TCB.md`. Cite exact Rust 1.83 documentation for
language and standard-library premises. Do not modify, build, run, or test
the target.
