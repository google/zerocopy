<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Lean 4 LSP Tool (`anneal-lsp`)

Standalone zero-dependency Lean 4 LSP manager providing fast interactive
queries from both the command line and a stdio Model Context Protocol (MCP)
server.

## Why It Exists

Anneal verification units (`request.json`) and library trees under
`anneal/theory/` omit `lakefile.toml` and `.lake/` directories. Standard
`lake serve` editor sessions therefore fail to resolve imports such as
`Expected`, `Captured`, `Trusted.*`, and `Anneal.*`.

`anneal-lsp` walks parent directories from the target file and picks the
nearest matching workspace mode (checking `request.json` before `lakefile.*`
when both sit in the same directory):

1. **Anneal proof units** (`request.json`) and exported `--artifacts <dir>`
   (`lean-lib/`, `capture/`, `generated/`) run directly via `lean --server`
   without creating `.lake/`.
2. **Standard Lake workspaces** (`lakefile.toml` / `lakefile.lean`) invoke
   `lake serve --` with Lake's standard workspace `.lake/` setup. Under the
   default `bwrap` sandbox, a pre-existing `.lake/` directory is `--bind`
   mounted writable while the workspace root and `lake-manifest.json` remain
   `--ro-bind` read-only (pass `--no-sandbox` for initial `.lake/` creation
   or dependency updates).
3. **Standalone Lean directories** fall back to the `.git` root (or file parent
   directory), adding in-tree `anneal/` subdirs (`theory`, `trusted/lean`,
   `correspondence`, `trusted/audit`) and any installed bundle's
   `share/anneal/prebuilt` (`/lib`) paths (guiding users to `cargo anneal setup`
   or `ci/prebuild_bundled_oleans.py` when prebuilt `.olean`s are absent).

## Relationship to Other Anneal Tools

- **`anneal-lsp` (`anneal/ci/anneal-lsp`)**: Interactive authoring and proof
  iteration (`diagnostics`, `goal` before/after, in-memory `multi-attempt`,
  `hover`, `definition`, `completions`, `outline`, `search`). It never edits
  `.lean` source files on disk or produces verification receipts (passing
  `--no-sandbox` in a Lake workspace allows `lake serve` to update `.lake/` or
  `lake-manifest.json`).
  In-memory `multi-attempt` is **advisory only** for rapid proof iteration: it
  reports candidates as `CLOSED` (`0 goals, 0 errors; advisory`), `STEP`
  (`n remaining`), `INCOMPLETE` (tactic or declaration uses `sorry`/`admit`),
  `ERROR`, `TIMEOUT`, or `BLOCKED` (prior error before target line). Do not
  treat `CLOSED` as verification evidence — always run `cargo anneal verify`
  once finished.
- **`cargo anneal verify`**: Authoritative verification pipeline — captures
  Rust MIR, runs Lean under `TrustedBoundary`, audits axioms/vacuity, and
  emits Receipt v3 evidence. Once an interactive proof succeeds, always run
  `cargo anneal verify` to confirm the final untainted claim.
- **`anneal/ci/anneal-lean-run`**: Resource/memory-capped CLI wrapper
  (`systemd --user` cgroup slice / `-M` heap cap) for standalone `lean`,
  `lake`, and `cargo` builds outside interactive LSP sessions.
- **`anneal/ci/` verification & hygiene scripts**: Repository-level CI gates
  (e.g., guard-mutation and PR hygiene checks) that run non-interactively in
  CI rather than inside the editor LSP loop.

## Quickstart

Run CLI subcommands (automatically reusing a warm background Unix daemon on
POSIX hosts, or pass `--direct` for single-shot in-process execution):

```sh
./anneal/ci/anneal-lsp discover <unit>/Proof.lean

./anneal/ci/anneal-lsp \
  --artifacts /path/to/unit-artifacts \
  diag <unit>/Proof.lean

./anneal/ci/anneal-lsp \
  --artifacts /path/to/unit-artifacts \
  goal <unit>/Proof.lean 54

./anneal/ci/anneal-lsp \
  --artifacts /path/to/unit-artifacts \
  try <unit>/Proof.lean 54 \
  "rfl" "simp" "refine checkVal_scalar_of_toNat_lt ?_"
```

Expose an in-process warm workspace pool over stdio MCP (`tools/list`,
`tools/call`):

```sh
./anneal/ci/anneal-lsp mcp
```

## Configuration and Sandboxing

- On Linux with `bwrap` installed (resolved exclusively from trusted root-owned
  system paths, never workspace `PATH` entries), Lean LSP servers run inside a
  deny-by-default `--tmpfs /` sandbox with `--die-with-parent`, `--cap-drop`,
  `ALL`, `--new-session`, and IPC, PID, and network namespaces unshared,
  selectively binding read-only OS runtime prefixes (`/usr`, FHS
  `/bin`/`/sbin`/`/lib*`, `/nix/store`, `/nix/var/nix/profiles`,
  `/opt/anneal-nix`, `/run/current-system/sw`, and minimal `/etc`
  loader/NSS/CA/alternatives paths — excluding host daemon socket directories
  such as `/nix/var/nix/daemon-socket`), hiding `/tmp`, `/var/tmp`, `/run`,
  `/var/run`, `$HOME` and the caller's `/etc/passwd` home, `XDG_RUNTIME_DIR`,
  and any custom `ANNEAL_LSP_SOCKET` directory (overmounted with `--tmpfs`
  after selective workspace/toolchain `--ro-bind` and `.lake/` `--bind` mounts;
  when the Lean toolchain or explicit `lean_path` / `artifacts` live under
  `$HOME`, only the needed toolchain subdirectories such as `bin`, `lib/lean`,
  `src`, and `libexec` or explicit library/artifact paths outside socket
  directories are selectively bound read-only while `~/.local` and caller home
  directories themselves remain hidden), while filtering child environment
  variables through the explicit allowlist (`PATH`, `HOME`, `USER`, `LOGNAME`,
  `LANG`, `LC_ALL`, `LC_CTYPE`, `TERM`, `TZ`, `TMPDIR`, `TEMP`, `TMP`,
  `LEAN_PATH`, `LEAN_SRC_PATH`, plus `--unsetenv LD_LIBRARY_PATH` and
  `--setenv LD_LIBRARY_PATH` forwarding only absolute path segments when set in
  `--direct` mode; daemon mode strips `LD_*` and other loader variables on
  launch). User namespaces are not unshared (`bwrap` keeps the caller UID), so
  mounted workspace/toolchain files and allowlisted host OS runtime paths
  (including non-home subtrees of `/usr`) remain read-only visible inside the
  sandbox. System libraries remain read-only.
  Missing or failing `bwrap` on Linux fails closed unless `--no-sandbox` or
  `ANNEAL_LSP_NO_SANDBOX=1` is set (non-Linux hosts run unsandboxed). Targets
  whose workspace root resolves directly to a hidden directory (`/tmp`,
  `/var/tmp`, `/run`, `$HOME`, or a custom socket directory) require a dedicated
  subdirectory or `--no-sandbox` / `ANNEAL_LSP_NO_SANDBOX=1`, and pre-existing
  `.lake/` directories containing hardlinked regular files (`st_nlink > 1`) are
  rejected under sandboxing. Workspace discovery (`request.json`, `lakefile.*`,
  `lean-toolchain`) stops at sticky, world-writable, or non-caller-owned
  directory boundaries. Invoking `./anneal/ci/anneal-lsp` assumes a trusted
  host caller environment with respect to OS dynamic-linker hooks
  (`LD_PRELOAD`/`LD_AUDIT`), while isolating Python startup (`-I -B` + fixed
  system interpreter paths + sanitized `/bin/sh`) and isolating untrusted
  workspaces/Lean processes inside the sandbox.
- Explicitly configured `--artifacts <dir>` or `ANNEAL_LSP_ARTIFACTS=<dir>`
  paths must exist and resolve to non-symlink directories (missing or regular
  file paths fail loudly rather than falling back to workspace defaults).
- Toolchain resolution order: `ANNEAL_LEAN`, `ANNEAL_TEST_INSTALL_ROOT`,
  project `lean-toolchain` under `~/.elan/toolchains/` (fails closed if a
  non-pinned `lean-toolchain` is missing and no explicit override is set),
  platform caches (`~/Library/Caches/anneal/toolchain` on macOS, ignoring
  `XDG_CACHE_HOME`; `$XDG_CACHE_HOME/anneal/toolchain` or
  `~/.cache/anneal/toolchain` elsewhere) followed by `~/anneal/toolchain` and
  pinned `~/.elan/toolchains/` (preferring cached binaries matching
  `trusted/lean/foundation-lock.json` SHA-256 before newest mtime), then
  `PATH`.
- `ANNEAL_LSP_ARTIFACTS=<dir>` (or `--artifacts <dir>`),
  `ANNEAL_LSP_LEAN_PATH` / `LEAN_PATH`, `LEAN_SRC_PATH`,
  `ANNEAL_LSP_MEMORY_MB` (default `4096` MB Lean `-M` allocator hint, not a
  hard OS RSS cap — use `anneal-lean-run` for cgroup memory enforcement), and
  `ANNEAL_LSP_SOCKET` override defaults per invocation (with
  `ANNEAL_LSP_MEMORY_MB` read at startup for `mcp`).
- Once started, the Unix daemon validates matching sandbox mode and code build
  ID across requests (`diag` reports source errors with `fatal: false` —
  `fatal: true` on fatal import/build errors — and exits `0`); pass
  `--direct` (`--no-sandbox`) or run `stop-daemon` to switch or reload after
  source updates.

## Exported Artifacts for Anneal Units

If `Expected.olean` / `Captured.olean` are not yet present in `lean-lib/`, run
`cargo anneal verify --request <unit>/request.json --artifacts <dir>`
with `--export-lean-lib` once, then pass `--artifacts <dir>` or set
`ANNEAL_LSP_ARTIFACTS=<dir>`.
