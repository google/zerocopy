# Audit request

Audit every exported library API separately and assess each supplied caller
example. For each API, state its exact input domain and the strongest
implementation and contract conclusions supported by the evidence. Give a
complete witness and causal chain for any demonstrated violation; otherwise
name the smallest unresolved premise and the evidence required to close it.
Do not use a caller outside an unsafe function's documented domain to refute
a claim about calls within that domain.

Expose the proof kernel for each material conclusion, including control-flow
semantics and unsafe-operation preconditions, with exact Rust 1.83 citations,
short quotations, applicability notes, and named consumers. Apply the source,
dependency, and TCB boundaries in the supplied Markdown files.

Do not modify, build, run, or test the target or examples.
