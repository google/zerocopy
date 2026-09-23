# Tool Policy — DRAFT / UNSEALED

Report agents may use only tools explicitly provisioned inside their declared
attempt workspace. Network access, repository-wide discovery, Git history,
sibling-run inspection, process inspection, inter-agent messaging, and access
to coordinator state are forbidden. Rust authority and accepted TCB material
must be mounted as declared read-only inputs.

The coordinator may prepare opaque inputs, claim the aggregation identity,
acquire leases, capture canonical envelopes, advance immutable aggregation
stages, and verify content addresses. Production evaluator input is
assignment-only: scorers, consistency reviewers, mode adjudicators, materiality
reviewers, and the materiality adjudicator receive only the packet and schema
tree rederived for that currently leaseable assignment from its committed
predecessor stage. No production caller may supply an evaluator packet, launch,
schema path, or workspace path. This is a procedural policy in this shared
collaboration environment, not proof of enforcement.

Coordinator state after the prelaunch static lock is confined to
`runtime/state/**`. `runtime/` may have no sibling child, and the static
verifier rejects any other carve-out. Agent input/output roots remain outside
the run. A lease owns one exact `input/` plus `output/` workspace; the seal route
revalidates its complete bound input tree before copying output into
content-addressed coordinator state. Preventing a same-UID agent from transiently
mutating and restoring input requires an OS-enforced read-only mount or separate
ownership and remains an explicit runner TCB premise.
