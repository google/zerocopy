# Exact replay scope and observer loader placement

`check_evidence.py` only reads package evidence. It does not start a compiler or
run a native subject. Use `python3 -B` to avoid writing Python caches beside
read-only support files.

An actual capture/check needs the exact retained observer and identified May 1
toolchain supplied explicitly. The observer binary is SHA256
`656fb5eaac61cecbed4b59b90ff5842cf2594551310084d599d66c9af817f636`.
Its Mach-O load command names `@rpath/librustc_driver-16d1e96e5b674978.dylib`;
its embedded LC_RPATH is:

```text
@loader_path/../toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib
```

The recorded original placement resolves that driver successfully. The actual
resolved driver has SHA256
`dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d`, the same
as the separately selected driver artifact. Merely copying the unchanged
observer to an unrelated directory does **not** preserve this loader relation.
An independent review's copied-observer attempt aborted in dyld before compiler
analysis because the relative library location was absent. That operational
failure is distinct from source unsupported status65 or a semantic rejection.

Use the original read-only observer path with its reviewed matching runtime
layout, or separately establish an equivalent hash-bound loader layout. Do not
silently patch the binary, use an arbitrary library override, or label a
relocated binary's unvalidated dependencies as the original runtime. The
consumer/request still trust compiler execution; this is not a general dynamic
loader or dependency-closure theorem. A newly built observer needs a distinct
reviewed identity/profile rather than weakening the old hash check.

`baseline-candidate.json` is a **projected display copy**, not the accepted raw
bytes: eight imported-core `origin.span`/`origin.call_site` strings contain the
declared compiler-prefix replacement. The consumer compares these fields too.
For the exact historical tool location, use `restore_baseline.py` with explicit
`--toolchain` and fresh `--output`; it verifies the prefix and restored raw packet
hash. It performs no compiler observation or acceptance. At another location,
first produce a fresh actual capture and use it as candidate under the same
caller-selected request. Do not claim that the public display bytes were accepted.

For the serial matrix, prepare a fresh caller-owned directory containing:

1. Exact `capture.py`, `packet_schema.py`, `capture_observer.rs` and the distinct
   `run_controls_explicit_observer.py` from this package.
2. `requests/base/request.json` and its exact `probe.rs`.
3. `producer-base/independent-capture.json`, restored to the historical raw
   packet or freshly produced under the independently selected request.

Invoke the reviewed observer explicitly; do not copy it into this directory:

```sh
python3 -B "$FRESH_ROOT/run_controls_explicit_observer.py" \
  --toolchain "$PINNED_TOOLCHAIN" --observer "$ORIGINAL_OBSERVER" \
  --matrix final-matrix
```

The distinct helper is source-reviewed; the completed independent 34-case replay used a different fixed-input review harness. No completed execution of this new helper is claimed.

The helper requires a new matrix directory, runs one observer at a time, and
preserves the same fixed source/control grammar. The added parameter changes
observer selection only; its implementation record names/hashes the distinct
helper actually run. The unchanged historical `run_controls.py` remains evidence
for the archived matrix and selects `ROOT/observer`; its copied-binary replay
must not be assumed to work under unrelated loader placement. Keep the two
helper identities and any fresh run receipts separate.

Check the observer and actual resolved matching driver/runtime identities at the
consuming boundary. Capture the exact runtime path, status and diagnostics.
Unknown status, dyld failure, compiler/observer panic or changed control outcome
stops the path for diagnosis. It must not become an expected semantic rejection.

Native replay is separate and optional. Read the exact valid selected sources
and wrappers, verify original library/binary identities, and run only on the
compatible selected arm64 Darwin target with bounded timeouts. Retain all 256
values for each of five cases. Native observations do not prove MIR capture
correctness, code-generation equivalence or source safety. Never execute
candidate JSON or projected packets as code.

The observation archive contains 409 safe regular data files. Inspect in memory
or validate names/types before extracting into a fresh owned directory. Original
source bytes, requests, operations, statuses and native values are unchanged by
publication; provenance display strings have the declared projection. Keep raw
stream hashes distinct from public display hashes.

A future authorized observer rebuild can use the preserved source with installed
pinned rustc-dev libraries and `-C rpath`, but its **actual** resulting loader
commands and binary hash must be inspected. The independent review did not
rebuild this observer, install anything or modify the historical caller profile.
