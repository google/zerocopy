<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Building and testing the scaffold

This guide covers building the omnibus toolchain archive from a checkout,
installing it into an isolated cache, running the workspace and installed smoke
suites, selecting individual smoke cases, checking crate packaging, and
reproducing retained failure evidence. See the [alpha guide](alpha.md) for
`cargo anneal verify` usage and proof development.

The runtime workflow below runs in CI on `x86_64-linux` (`ubuntu-24.04` in
[the current checks](../../ci/checks.toml), and
`ubuntu-24.04` in [the release workflow](../../.github/workflows/release.yml)).
[`flake.nix`](../flake.nix) declares package outputs for `x86_64-linux`,
`aarch64-linux`, `x86_64-darwin`, and `aarch64-darwin`, and
`./ci/check_flake_eval.sh` instantiates all four. Flake evaluation and
packaging metadata alone do not establish that the built tools install or pass
tests on `aarch64-linux`, `x86_64-darwin`, or `aarch64-darwin`.

## Build and install the current archive

Use Bash on Linux with Nix flakes, Python 3, a host C linker, and an existing
Rust toolchain (Cargo and `rustc`) that can compile Rust 2024 crates and
`--locked` dependencies. The initial `cargo install` steps use that host
toolchain before switching to the archive's pinned compiler. Run these commands
from `anneal/` inside the Zerocopy checkout in one shell so later commands
reuse the shell variables (if you paste into an interactive shell, omit
`set -e` so an expected test failure does not exit the shell before you
inspect `$scaffold_root`; in scripts, enable `set -euo pipefail`); keep
`scaffold_root` outside the checkout so build outputs and test runs stay
isolated from the source tree.

```bash
repo_root="$(pwd -P)"
scaffold_root="$(mktemp -d /tmp/anneal-scaffold.XXXXXX)"

nix build .#omnibus-archive --max-jobs 1 --cores 4 \
  --out-link "$scaffold_root/archive"
archive="$(readlink -f "$scaffold_root/archive")"

cargo install --locked --debug --jobs 2 --path trusted/cargo-anneal \
  --root "$scaffold_root/cli"
env XDG_CACHE_HOME="$scaffold_root/cache" \
  "$scaffold_root/cli/bin/cargo-anneal" setup --local-archive "$archive"
```

`--max-jobs 1` limits concurrent Nix builds, and `--cores 4` bounds the cores
advertised to each build. The archive bundles the pinned Rust (`rust/`) and Lean
(`lean/`) toolchains, the capture driver (`bin/anneal-rustc-capture`), and the
packaged Lean and audit files under `share/anneal/`. `cargo-anneal` and
`anneal-audit` are not packaged in this archive; build them separately as shown
here. In CI, `cargo install --debug` also sets
`--config 'profile.dev.package.<pkg>.opt-level=3'` for `cpufeatures`,
`digest`, `sha2`, and `zstd-sys` so SHA-256 hashing and `.tar.zst` extraction
run at native speed.

`--local-archive` is required when installing from a source checkout: on `main`,
[`trusted/cargo-anneal/Cargo.toml`](../trusted/cargo-anneal/Cargo.toml) keeps
version `0.0.0-dev` with an empty URL and an all-zero `sha256` in
`[[package.metadata.exocrate]]`, so `setup` refuses remote downloads until a
published `cargo-anneal` release stamps a pinned archive (`x86_64` Linux with
glibc only). Using a fresh `XDG_CACHE_HOME` prevents an earlier installation
from satisfying `setup`, and `env` scopes that cache override to this command
alone.

Locate and validate the single installation produced by `setup` instead of
guessing its versioned directory name:

```bash
install_root="$(python3 - "$scaffold_root/cache" <<'PY'
import sys
from pathlib import Path

parent = Path(sys.argv[1]) / "anneal/toolchain"
roots = [path for path in parent.iterdir() if path.is_dir()]
if len(roots) != 1 or roots[0].is_symlink():
    raise SystemExit("setup must produce exactly one fresh installation")
root = roots[0].resolve()
for relative in (
    "rust/bin/rustc",
    "rust/bin/rustdoc",
    "rust/bin/cargo",
    "lean/bin/lean",
    "bin/anneal-rustc-capture",
    "share/anneal/trusted/audit/TrustedBoundary.lean",
):
    if not (root / relative).is_file():
        raise SystemExit(f"installed tool is missing: {root / relative}")
print(root)
PY
)"
```

For full symlink-confinement validation and shell exports matching CI, run
`python3 -I -B ci/check_bundle_tree.py` with
`--cache-root "$scaffold_root/cache" --discover-single`.

When `bin/anneal-rustc-capture` runs directly as a compiler driver, it defaults
`--sysroot` to its sibling `rust/` directory (for an unbundled binary, pass
`--sysroot "$install_root/rust"`). Pass `--` before compiler `--help` or
`--version` flags to distinguish them from driver flags. Without Anneal's
capture settings, compiling a crate directly with the driver emits
`note: anneal-rustc-capture: compiler analysis callback reached; verification not performed`
on stderr; that startup smoke diagnostic checks compiler integration, not proof
verification.

## Test the workspace and audit the boundary

`trusted/rustc-capture` links compiler-private `rustc_private` libraries, and
workspace tests execute both `lean` and `anneal-rustc-capture`. Export the
installed toolchain paths and run the non-ignored workspace checks from
`anneal/`:

```bash
export XDG_CACHE_HOME="$scaffold_root/cache"
export ANNEAL_TEST_INSTALL_ROOT="$install_root"
export ANNEAL_TEST_RUST_SYSROOT="$install_root/rust"
export ANNEAL_SYSROOT="$install_root/rust"
export ANNEAL_LEAN="$install_root/lean/bin/lean"
export ANNEAL_CAPTURE="$install_root/bin/anneal-rustc-capture"
export RUSTC="$install_root/rust/bin/rustc"
export RUSTDOC="$install_root/rust/bin/rustdoc"
export LD_LIBRARY_PATH="$install_root/rust/lib"
export RUSTFLAGS="-Lnative=$install_root/rust/lib -Clink-arg=-Wl,-rpath,$install_root/rust/lib"

cargo run --locked -p cargo-anneal --example regenerate_bundle -- --root . --check
cargo test --locked -p cargo-anneal --no-default-features \
  --lib --bin cargo-anneal --test cli
cargo test --workspace --locked --jobs 2 -- --test-threads=2
```

`cargo test --workspace` skips the `#[ignore]`d `installed_smoke` test, which
runs separately below.

Build the boundary auditor into its own tool root and run it against the
installed `lean` binary and checkout root (when `vendor/lean-miri/`,
`trusted/correspondence/`, or `correspondence/` exists under `--anneal-root`,
`anneal-audit` automatically runs Pass 2 correspondence verification inside
Linux bubblewrap at `/usr/bin/bwrap`; `--require-correspondence` prevents silent
fallback to Pass 1 if those directories are absent):

```bash
cargo install --locked --debug --jobs 2 --path trusted/audit \
  --root "$scaffold_root/auditor"

"$scaffold_root/auditor/bin/anneal-audit" \
  --lean "$install_root/lean/bin/lean" \
  --anneal-root "$repo_root" \
  --require-correspondence
```

`anneal-audit` embeds `TrustedBoundary.lean` internally and hashes the pinned
Lean binary, `foundation-lock.json`, and sysroot `.olean`/`.ir` manifest before
replaying declarations. To cache cold `vendor/lean-miri/` `.olean` builds across
runs, pass `--miri-cache-dir <dir>` pointing outside `--anneal-root`.

## Run installed smoke cases

The opt-in `installed_smoke` suite executes the installed tools from fresh
temporary directories created under `TMPDIR`. `TMPDIR` must resolve outside the
checkout; the harness aborts if a temporary run directory sits under the
checkout root so missing installed files cannot accidentally resolve against the
source tree.

Supply absolute paths to `cargo-anneal` and `anneal-audit`, a nonempty
caller-supplied `ANNEAL_TEST_SOURCE_REVISION` label (record `+worktree` and
retain `git diff` when uncommitted edits exist; this label does not attest
artifact provenance), and **either** `ANNEAL_TEST_ARCHIVE` (extracts a fresh
test-owned installation per run) **or** `ANNEAL_TEST_INSTALL_ROOT` (reuses an
existing installation without exercising archive installation). From `anneal/`:

```bash
source_revision="$(git rev-parse HEAD)"
if [ -n "$(git status --porcelain)" ]; then
  source_revision="$source_revision+worktree"
fi

env -u ANNEAL_TEST_INSTALL_ROOT -u ANNEAL_TEST_CASE \
  ANNEAL_TEST_SOURCE_REVISION="$source_revision" \
  ANNEAL_TEST_CARGO_ANNEAL="$scaffold_root/cli/bin/cargo-anneal" \
  ANNEAL_TEST_AUDITOR="$scaffold_root/auditor/bin/anneal-audit" \
  ANNEAL_TEST_ARCHIVE="$archive" \
  ANNEAL_TEST_DIAGNOSTICS="$scaffold_root/diagnostics" \
  cargo test --locked -p cargo-anneal --test installed_smoke -- \
    --ignored --exact installed_smoke --nocapture
```

In scripts, pass `-- --ignored --exact installed_smoke --list` first and assert
that `installed_smoke: test` appears, because Cargo exits zero when a filter
matches zero tests. To run against `$install_root` instead of reinstalling from
`$archive`, replace `ANNEAL_TEST_ARCHIVE="$archive"` with
`ANNEAL_TEST_INSTALL_ROOT="$install_root"` and add `-u ANNEAL_TEST_ARCHIVE` to
`env`.

Optional environment variables narrow a run or capture failure artifacts:

| Variable | Behavior |
| --- | --- |
| `ANNEAL_TEST_CASE` | Selects one exact case name; unset runs all cases. |
| `ANNEAL_TEST_JOBS` | Maximum concurrent cases and Lean compile workers; default `2`, range `1..=32` (CI sets `4`). |
| `ANNEAL_TEST_TIMEOUT_SECS` | Per-child deadline in seconds; default `120`, range `1..=3600`. |
| `ANNEAL_TEST_DIAGNOSTICS` | Exports retained failure evidence under this directory (omits `installation/`). |

Available `CASES` values:

| Case | What it checks |
| --- | --- |
| `audit-accepted` | Copies the packaged `lean-toolchain`, `foundation-lock.json`, `TrustedBoundary.lean`, and `library-lock.json`, writes a self-contained synthetic `Trusted` / `Trusted.*` + `Anneal.Wp` + `Anneal.MirWp` + `Anneal.MirWp.Canaries` fixture, and runs `anneal-audit --json`, expecting `replay: true` and at least `30` kernel declarations. |
| `audit-missing-lean` | Invokes `anneal-audit` with a nonexistent `--lean` path and expects exit `2` in phase `toolchain`. |
| `audit-rejected` | Runs `anneal-audit` on a `sorry` fixture and expects exit `1` in phase `preflight` with `Target execution began: false`. |
| `bundled-cargo-check` | Runs installed `rust/bin/cargo check --offline` with an owned `CARGO_HOME` and checks nonempty `.rmeta` output. |
| `cargo-arguments` | Runs `cargo-anneal unknown-scaffold-command` and expects exit `2`. |
| `cargo-help` | Checks `--help`, `anneal --help`, and `setup --help` on `cargo-anneal`. |
| `cargo-setup-invalid-archive` | On Unix, checks that v1 install followed by v2 reinstall replaces the toolchain in `XDG_CACHE_HOME` / `HOME` and corrupt/missing archives fail with exit `1` and empty stdout without harming the installed toolchain. |
| `cargo-version` | Checks `--version` and `anneal --version` on `cargo-anneal`. |
| `driver-callback` | Compiles a small crate with `bin/anneal-rustc-capture --sysroot ... --emit=metadata` and checks `.rmeta` output, empty stdout, and the callback stderr note. |
| `lean-file` | Stages `share/anneal/trusted/lean` and `share/anneal/theory`, parses `share/anneal/theory/bundle-manifest.json` and walks `share/anneal/theory` recursively to verify 1-for-1 `Anneal.*` parity across the installed tree (allowing only `bundle-manifest.json` and `Anneal.*` modules with zero `*Canaries*` and no retired `Anneal.lean`), `bundle-manifest.json`, and its transitive `Anneal.*` import closure, compiles the `bundle-manifest.json` and `Trusted` module graph with `ANNEAL_TEST_JOBS` workers, checks `Trusted.olean`, `Anneal/Scalar.olean`, and `Anneal/Wp.olean` (and the absence of `Anneal.olean`), and elaborates separate `SmallScalar.lean` (`import Anneal.Scalar`) and `SmallWp.lean` (`import Anneal.Wp`) smoke modules. |
| `rustdoc-html` | Runs `rust/bin/rustdoc --sysroot ...` on a small crate and checks `index.html` and `fn.identity.html`. |

For example, to rerun only `driver-callback` sequentially, place
`ANNEAL_TEST_CASE=driver-callback ANNEAL_TEST_JOBS=1` **after** the `env -u`
options (`env -u ANNEAL_TEST_INSTALL_ROOT -u ANNEAL_TEST_CASE
ANNEAL_TEST_CASE=driver-callback ANNEAL_TEST_JOBS=1 ...`) so `-u
ANNEAL_TEST_CASE` does not clear it. An unrecognized case name fails and prints
the valid catalog.

`ANNEAL_TEST_TIMEOUT_SECS` kills and reaps only the direct child process; it
does not terminate grandchildren or bound arbitrary Rust helper code, so CI uses
an outer deadline: `ci/run_anneal_check.sh` re-runs itself under `timeout`
(90 minutes for `ws-test`, the mode that runs these tests). The
`anneal-installed-smoke` check in
[the current checks](../../ci/checks.toml) also checks `ci/probe_alpha.py` and
`ci/verify_starnix_e2e.py` inside
bubblewrap, and [the release workflow](../../.github/workflows/release.yml)
runs `ci/probe_alpha.py` during release qualification.

## Inspect and replay a failure

On failure, `installed_smoke` preserves its temporary run directory (for
example `/tmp/anneal-integration-*`), writes `failure.txt`, and prints
`evidence retained at <dir>` (plus `evidence exported to <dir>` when
`ANNEAL_TEST_DIAGNOSTICS` is set). The run root contains `run.json`,
`supplied-inputs.json`, `selection.json`, `installation.json` (absent if archive
installation failed before completing), `failure.txt`, `installation/` (in the
original archive-mode directory only), and
`cases/<case>/commands/<NNNN>/` with `invocation.json`, `outcome.json`,
`stdout`, `stderr`, and `reproduce.py`.

From a retained command directory, run:

```bash
python3 reproduce.py
```

`reproduce.py` prints `run.json` to stderr, relocates paths inside the recorded
`original_run_root` to the current run root, clears the environment, applies
`process_timeout_seconds` to the direct child with null stdin, and reruns the
recorded executable, arguments, and working directory while preserving signal
termination. It does not restore external files: keep the recorded archive,
`ANNEAL_TEST_CARGO_ANNEAL`, `ANNEAL_TEST_AUDITOR`, `ANNEAL_TEST_INSTALL_ROOT`
(if existing-root mode was used), and the compiled `installed_smoke` test
binary (for archive-install commands) at their recorded paths before replaying.

`ANNEAL_TEST_DIAGNOSTICS` exports omit the multi-gigabyte `installation/`
directory. To replay from an exported bundle, copy the exported run directory
to a fresh scratch copy (keeping the original retained evidence and any partial
installation untouched). For archive-backed runs whose `installation.json` was
written, unpack the archive so the relocated `installation.json` `root`
(`installation/anneal/toolchain/<slug>/`) is populated — or run
`env XDG_CACHE_HOME="<copy>/installation" cargo-anneal setup --local-archive <archive>`
— before replaying case commands; when replaying an installation failure, move
aside any partial `installation/` directory inside `<copy>` before retrying.

## Check packaging and static checks

Check `cargo-anneal` crate packaging and task markers from `anneal/`:

```bash
cargo run --locked -p cargo-anneal --example regenerate_bundle -- --root . --stage-package
cargo publish --locked --dry-run --allow-dirty -p cargo-anneal
rm -rf trusted/cargo-anneal/packaged
./ci/check_todo.sh
```

`cargo publish --dry-run` requires `--allow-dirty` after staging
`trusted/cargo-anneal/packaged/{bundled_resources.rs,bundled_theory.json}`
(remove the transient `packaged/` directory afterward to keep the tree clean).
In CI, `anneal-installed-smoke` stages them in a scratch copy of the read-only
checkout instead. The packaging check also runs
`cargo test --locked --manifest-path "$prepared_manifest" --no-run` against the
unpacked `target/package/cargo-anneal-<version>/Cargo.toml` so missing excluded
fixtures fail the build. The remaining fast repository checks in CI are:

```bash
sha256sum --check --strict trusted/root-manifest.sha256
python3 -I -B ci/check_pr_hygiene.py --base origin/main
./ci/check_job_dependencies.sh
./ci/check_actions.sh
./ci/check_flake_eval.sh
./ci/check_non_stable_version.sh
python3 -B -m unittest discover -s ci -p 'test_*.py'
```

`ci/check_pr_hygiene.py` fails fast on mechanical defects that reviewers
otherwise report: commit-message layout and `Agent-authored-by:` trailers,
`git diff --check`, Markdown and comment lines that exceed 80 columns, missing
license headers on new files, review-round IDs, unpinned upstream citations in
`trusted/lean/` and `trusted/rustc-capture/`, the cumulative `AGENTS.md` byte
budget, the `Code Review Rules` mirror, and malformed or `#PENDING`
[`rustc` workaround anchors](rustc-workarounds.md#code-anchors). `ci-core`
checks cannot read Git history, so `.github/workflows/anneal-pr-hygiene.yml`
runs it as the required `PR hygiene` check on every `opened`, `synchronize`,
`reopened`, and `edited` pull-request event, against the PR's base and head and
with `--forbid-pr-title-regex '\b[T]ODO\b'` to reject PR titles containing that
marker. In the merge queue it exits 0 without checking out: `ci-core`'s
`skills-check` enforces the `AGENTS.md` budget and the rules mirror on every
tree, and `ci-core` rejects the marker in landed commit messages. The script
reads Git objects without checking out or running candidate code, so reviewers
can run a trusted base copy against a candidate head.

`PR hygiene` is soft-blocking. A trailer in the final trailer block of the
PR's `HEAD` commit waives every finding of the named checks:

```text
Skip-pr-hygiene: <check[,check...]> -- <reason>
```

The checks are `commit-message`, `diff-check`, `wrap`, `header`,
`review-round-id`, and `trusted-citation`. There is no `all`, and the
`AGENTS.md` budget, rules mirror, and workaround anchors are never waivable. The
reason needs at least five non-whitespace characters, and a named check without
findings is an error, as is the trailer on any other commit in the PR. Each
waived finding still emits a `::warning::` annotation and a step-summary entry.

Before publishing, also pass `--pr-body-file` and `--pr-title` to compare a
single-commit PR's description and title with its commit (`--emit-pr-body`
prints the expected description), and `--receipt-file` to check a Review
Receipt. Besides its prose
`Human review surface` block, a receipt carries one machine-checked footer,
`<!-- anneal-receipt:v1 {...} -->`, which binds `target_base`, `merge_base`,
`head`, and `tree` to full SHAs and lists every changed Human review surface
path; `--emit-receipt-footer` prints it. `--json` emits a report for tooling,
and `--skip-commit-messages` skips commit-message checks, which CI does for
PRs whose GitHub author is a bot.
