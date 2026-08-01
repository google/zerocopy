# Focused source review

Audit every current producer and consumer of `Buffer` and the local safety
proof for `overwrite`. Determine the strongest result for all well-typed safe
uses.

Scope: exactly Rust 1.80.0, all targets and ordinary profiles. No redesign or
source edit is requested.
