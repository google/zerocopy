# Greenfield design request

The function body is a placeholder, not an existing implementation to audit.
Design it conceptually. Return `None` if either index is out of bounds or if
`i == j`; otherwise return mutable references to the two corresponding elements
in `(i, j)` order. There is no performance requirement beyond ordinary
linear-memory access and no demonstrated need for a reusable abstraction.

The crate is `no_std`, supports Rust 1.70+ and all targets, and has no
dependencies. Do not edit the source; provide a design and proof plan.

