# Ordered allocator-selection build interface

Supported builds use Cargo 1.85.1 and this crate's `build.rs`. The raw value of
`FIXTURE_ALLOCATOR` has this complete partition:

- an omitted variable and the Unicode value `system` are accepted and select
  the `system` allocator;
- the Unicode value `arena` is accepted and selects the `arena` allocator;
- the Unicode value `arena-stop` is a deliberately rejected freshness canary;
  the script writes the `arena` allocator directive and then panics;
- every other Unicode value is rejected before an allocator directive is
  attempted; and
- every non-Unicode value is rejected before an allocator directive is
  attempted.

The script first attempts to write
`cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR`. It then reads and classifies
the environment value. Each accepted path attempts exactly one
`cargo::rustc-cfg=fixture_allocator="..."` write and returns successfully if
that write succeeds. The `arena-stop` path attempts that same `arena` write and
then panics. A failure of any stdout write makes that `println!` panic at that
point; any earlier successfully written directive lines are therefore a
partial output prefix of an unsuccessful script execution.

The freshness guarantee is part of the supported build interface. In
particular, after a successful `arena` build in a Cargo target directory,
changing `FIXTURE_ALLOCATOR` to `arena-stop` must rerun the script and reject
the current build. A previously compiled `arena` library is not a result of
that current rejected build.

Only a successful script execution for an accepted selector supplies an
allocator configuration to a library compilation. Manually invoking `rustc`,
inventing configuration options, or overriding the build script is outside the
theorem.
