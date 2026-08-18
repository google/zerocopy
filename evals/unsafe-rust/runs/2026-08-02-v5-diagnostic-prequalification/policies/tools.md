# Tool Policy — DRAFT / UNSEALED

Report agents may use only tools explicitly provisioned inside their declared
attempt workspace. Network access, repository-wide discovery, Git history,
sibling-run inspection, process inspection, inter-agent messaging, and access
to coordinator state are forbidden. Rust authority and accepted TCB material
must be mounted as declared read-only inputs.

The coordinator may prepare opaque inputs, acquire leases, capture terminal
envelopes, and verify content addresses. Scorers and adjudicators receive only
their frozen blinded packets. This is a procedural policy in this DRAFT shared
environment, not proof of enforcement.
