# Configuration-preserving redesign

Review and redesign `decode` without changing either configuration-specific
signature or documented behavior. The published support set is Rust 1.70+,
every target and pointer width, every ordinary profile, and both independently
selectable values of feature `compact`. Dropping a configuration, raising the
MSRV, or changing a return type is not authorized. No source edit is requested.

