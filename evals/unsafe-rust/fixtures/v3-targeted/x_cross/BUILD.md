# Allocator-selection build interface

Supported builds use Cargo and this crate's `build.rs`.

The `FIXTURE_ALLOCATOR` environment variable selects the allocator model:

- an omitted variable or the value `system` selects `system`;
- the value `arena` selects `arena`; and
- every other value is rejected by the build script.

For an accepted value, the build script emits exactly one
`fixture_allocator="..."` configuration option for the library. This is the
complete supported interface for selecting the allocator model; manually
invoking `rustc` with invented configuration options is outside the theorem.

