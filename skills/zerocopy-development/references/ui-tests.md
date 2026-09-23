# UI and Output Tests

Use this procedure when changing UI test files in `tests/ui-*` or
`zerocopy-derive/tests/ui-*`, or when behavior can change compiler diagnostics
or derive output.

Run:

```bash
../tools/update-expected-test-output.sh
```

The repository keeps separate MSRV, stable, and nightly UI expectations because
compiler output varies by toolchain. The update script handles those toolchains.

## Source and Symlink Layout

For each shared UI test:

1. `ui-nightly` contains the canonical `.rs` source file.
2. `ui-stable` and `ui-msrv` contain relative symlinks to that source file.
3. Each toolchain directory contains its own `.stderr` expectation.

For example, `tests/ui-stable/foo.rs` should point to
`../ui-nightly/foo.rs`.

## Add a Test

1. Create the `.rs` source in `ui-nightly`.
2. Create the corresponding relative symlinks in `ui-stable` and `ui-msrv`.
3. Run `../tools/update-expected-test-output.sh` to generate `.stderr` files.

## Modify a Test

1. Edit the canonical `.rs` file in `ui-nightly`.
2. Run `../tools/update-expected-test-output.sh` to update expectations.

## Remove a Test

1. Delete the canonical `.rs` file from `ui-nightly`.
2. Delete the symlinks from `ui-stable` and `ui-msrv`.
3. Delete the corresponding `.stderr` files from all three directories.

Never edit `.stderr` files directly. Update them only through
`../tools/update-expected-test-output.sh` or the commands that script invokes.
If tooling cannot produce the expected result, investigate the underlying test
or tooling failure instead of hand-editing the expectation.
