# Exact supported domains

The audit cutoff is 2026-07-31. All listed releases, every target on which the
item exists, and every ordinary debug or release profile are supported.

The exact release predicates are:

- `acknowledge`: `V_ack = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`.
- `store_word`: `V_store = {1.80.0, 1.81.0}`.
- `copy_byte`: `V_copy = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`.
- `load_word`: `V_load = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`.

These are explicit finite sets, not notation for every release in a numeric
interval. No other Rust release is in `Required` for this target.
