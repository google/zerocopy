# Audit request

Audit each public library API in this snapshot separately, then assess each
downstream example as a proposed use of those APIs. State the strongest
implementation, contract, and caller conclusions supported by the supplied
evidence.

For every material conclusion, close the relevant source and access paths,
typing and coherence assumptions, ordinary-call semantics, unsafe-operation
preconditions, unsafe-trait implementation obligations, and any proposition
that belongs outside the library's proof domain. Distinguish a library theorem
from the validity of a submitted caller example. Cite the exact Rust 1.83
documentation used, with short quotations, applicability notes, and named
consumers.

Use `SUPPORT.md` to establish scope. Do not modify, build, run, or test the
target or examples.
