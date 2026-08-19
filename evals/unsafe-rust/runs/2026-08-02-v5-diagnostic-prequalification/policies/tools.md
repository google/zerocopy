# Tool Policy — DRAFT / UNSEALED

Report agents may use only tools explicitly provisioned inside their declared
attempt workspace. Network access, repository-wide discovery, Git history,
sibling-run inspection, process inspection, inter-agent messaging, and access
to coordinator state are forbidden. Rust authority and accepted TCB material
must be mounted as declared read-only inputs.

The coordinator may prepare opaque inputs, acquire leases, capture terminal
envelopes, and verify content addresses. Scorers and adjudicators receive only
their frozen blinded packets. This is a procedural policy in this shared
collaboration environment, not proof of enforcement.

Coordinator state after the prelaunch static lock is confined to
`runtime/state/**`. `runtime/` may have no sibling child, and the static
verifier rejects any other carve-out. Agent input/output roots remain outside
the run and are copied into content-addressed coordinator state only when an
attempt is sealed.
