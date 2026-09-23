# Toolchains and Version Gating

## Cargo Wrapper

Run zerocopy Cargo commands through `./cargo.sh`. The wrapper resolves
repository-controlled
compiler versions so local commands use the same toolchains expected by CI and
UI tests.

Use:

```text
./cargo.sh +<toolchain> <command> [args]
```

The toolchain selector is mandatory. Supported selectors include:

- `msrv`: the Minimum Supported Rust Version.
- `stable`: the repository's stable toolchain.
- `nightly`: the repository's nightly toolchain.
- `all`: `msrv`, `stable`, and `nightly` in sequence.
- Version-gated selectors such as `no-zerocopy-core-error-1-81-0`; inspect
  `Cargo.toml` for the current set.

Do not copy toolchain version numbers into agent documentation. Read the current
MSRV from `Cargo.toml`'s `package.rust-version` and the current version-gate
thresholds from `[package.metadata.build-rs]`.

## Version-Dependent Features

Do not use a Rust feature stabilized after the current MSRV unless the behavior
is correctly version-gated. Ask the user before introducing a new
version-gated behavior.

The repository's version-gating convention is:

1. Add `no-zerocopy-<feature>-<version> = "<version>"` under
   `[package.metadata.build-rs]` in `Cargo.toml`.
2. Gate source code with
   `#[cfg(not(no_zerocopy_<feature>_<version>))]`, using underscores in the cfg
   name.
3. For public items, add
   `#[cfg_attr(doc_cfg, doc(cfg(rust = "<version>")))]` where appropriate.

Keep compiler versions represented in `.github/workflows/ci.yml` and
`Cargo.toml`'s `[package.metadata.build-rs]` synchronized when adding a new
version gate.
