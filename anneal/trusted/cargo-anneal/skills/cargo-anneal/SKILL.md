---
name: cargo-anneal
description: >-
  Use when running cargo-anneal setup or verify, preparing a request or starter
  proof, diagnosing verification exits, or interpreting a Receipt v3 file. Not
  for authoring or auditing specs at length (use spec-authoring), scaling Lean
  proofs past OOM or Tabu cliffs (use proof-scaling), or editing Anneal itself.
---

# Verify Rust code with Anneal

Anneal verifies a subset of Rust. Support depends on the installed version,
target triple, compilation flags, and scope. Check `cargo anneal --version` and
run the intended request to verify what that build accepts.

On Linux, `ExecSeal` sandboxes target Lean preflight, elaboration, and audit
by default (`linux_bwrap` or `linux_landlock_seccomp`, recorded in
`elaboration_sandbox`), whereas Rust compilation (`rustc`) runs as the caller.
Run the verifier in an isolated environment for untrusted Rust inputs or build
scripts, on non-Linux hosts, or when passing `--allow-unsandboxed-elaboration`.

## Companion skills

`cargo-anneal` bundles both companion skills; run `cargo anneal skill list` to
list every bundled topic.

- Authoring, translating, or auditing specifications (`Spec.lean` / `Spec.*`,
  vacuity, anti-echo, Intent Decisions): use **`spec-authoring`**
  (`cargo anneal skill spec-authoring`).
- Scaling proofs past bounded `execProg`, reducing Lean RSS/timeouts, or
  escaping verification cliffs: use **`proof-scaling`**
  (`cargo anneal skill proof-scaling`).

## Run the project's verification

Identify the Rust function or crate scope, intended property, and caller
preconditions. If setup is needed, run `cargo anneal setup` (reuses an existing
cached toolchain for that version) or `cargo anneal setup --local-archive <path>`
to install a local archive. Pass `--clear-old` (or redirect stdin from
`/dev/null`) in non-interactive shells so cleanup prompts cannot block. Use the
same user and `XDG_CACHE_HOME` across `setup` and `verify`. Builds compiled with
`--no-default-features` omit `setup` and require `--capture`, `--sysroot`, and
`--lean`.

To reuse compiled `.olean` files across crates and invocations (for example,
in a hermetic build system or CI), point `verify` at one shared cache with
`--olean-cache-dir <DIR>` or `ANNEAL_OLEAN_CACHE_DIR=<DIR>`. The flag overrides
the variable, an empty variable counts as unset, and either one replaces the
per-user default under `XDG_CACHE_HOME` (or `HOME`). Entries are keyed by
content (`<DIR>/v2/<merkle_key>/`) and published atomically, so concurrent runs
can share a directory. A cache hit is trusted on the strength of the entry's
own recorded digests, which detect corruption but not a malicious writer, so
everything that can write `<DIR>` must be trusted as much as the runs that read
it: keep it outside any checkout (`verify` refuses a root inside or containing
the working directory or any input directory: manifest, proof, request, or
`rustc` source directories, but accepts a root under the per-user cache base
(`XDG_CACHE_HOME`, `~/.cache`, or `~/Library/Caches`), as for the default,
when run from a directory such as `HOME` that strictly contains it), and give
runs on untrusted Rust inputs or with `--allow-unsandboxed-elaboration` their
own directory. `--olean-cache-dir` cannot be combined with `--no-cache`, and
`--receipt-out` must not point inside the cache directory in use.

When the prebuilt `.olean` bundle is not beside the Lean toolchain (for
example, in Nix or Bazel layouts, or with a `cargo-anneal` built separately
from its Lean tree), name it with `--prebuilt-dir <DIR>`, the directory holding
the bundle's `manifest.json`. It replaces the installed bundle's and the
`--lean` prefix's `share/anneal/prebuilt`, and works with explicit `--lean` and
`--no-default-features` builds. There is no environment variable. Like a shared
cache, the bundle is trusted as stored: `verify` refuses a directory inside or
containing the working directory or any input directory, a missing directory or
manifest, a symlinked directory, or a manifest for another cache format, and
fails rather than recompiling a module the bundle lists with different inputs.
Modules the bundle does not list still use the disk cache or compile.
`--prebuilt-dir` cannot be combined with `--no-cache`, and `--receipt-out` must
not point inside it.

Run verification (defaults to `--format human` on stdout), atomically write a
Receipt Schema v3 JSON file via `--receipt-out` (or pass `--format json` to
stream JSON on stdout), and treat the process exit code (`0` verified, `1`
verification failure, `2` operational/argument error, `3` `--fast-check`
elaboration passed without kernel replay) as authoritative alongside the
receipt file (`--receipt-out` clears any pre-existing non-input
regular file once inputs are validated so interrupted or failed runs cannot
leave a stale pass behind, while early argument/alias rejections exit `2`
without touching the destination):

```sh
cargo anneal verify --request path/to/request.json --receipt-out path/to/receipt.json
```

Output and diagnostic flags:
- `--format human|json|auto`: defaults to `human`, rendering a five-tier
  verdict card (`[OK]` only for untainted, warning-free whole-crate runs;
  `[SCOPED]` for `selected_unit`; `[WARN]` when `spec_warnings` are present;
  `[TAINTED]` under `--allow-*`; `[FAIL]` on failure). Pass `--format json`
  when piping Receipt v3 JSON on stdout, or `--receipt-out <path>` to persist
  JSON atomically alongside human output.
- `--color auto|always|never`, `-q`/`--quiet`, and `-v`/`--verbose`: control
  ANSI styling (`auto` follows stream `isatty`, `CARGO_TERM_COLOR`, `NO_COLOR`,
  and `TERM=dumb`), quiet summaries (never hiding taint or warning caveats),
  and untruncated diagnostics/line progress.

Other entrypoints:
- Cargo packages: `cargo anneal verify --manifest-path path/to/Cargo.toml --proof-dir path/to/proofs [--exclude-trait <trait> ...] [--no-default-features] [--features <list>] [--all-features]`
- Build systems with explicit inputs: `cargo anneal verify rustc <crate_root> --crate-name <name> [--exclude-trait <trait> ...] [--env KEY=VALUE ...] --spec-file <Mod>=<path> --proof-file <Mod>=<path> ...`

## Create a request and starter proof

Run `cargo anneal init` inside a Cargo package to scaffold `proof/Spec.lean`
and `proof/Proof.lean` (or `cargo anneal init --standalone` for a runnable
4-file example, or `cargo anneal skill --example` to print it). Pass
`--profile v2` (default `v1`; not with `--standalone`) for a `SpecsV2`
starter when capture emits MIR Profile v2. Save standalone
files in a temporary directory to test your environment; it proves termination
and a zero return for a safe no-argument function in the captured MIR model.

1. For request schema `1`, set `scope` to `{"kind": "selected_unit", "roots": ["mod::fn"]}`
   (`UnitTheorem`) or `{"kind": "crate"}` (`CrateTheorem`). Crate scope also
   accepts an optional `"excluded_traits"` list (or repeatable
   `--exclude-trait`) from the closed allowlist `core::fmt::Debug`,
   `core::fmt::Display`, and `core::error::Error`; capture excludes local impls
   of those traits only after proving they are unreachable from every verified
   body, and Receipt v3 discloses the excluded census items in `excluded_items`
   and appends an explicit unverified/unreachable note to `assumptions`. If
   capture emits MIR Profile v2 (`capture.json`,
   `program.mir_profile_version = 2`, e.g. for references, raw pointers, or
   slices), the roots are `UnitTheoremV2` / `CrateTheoremV2` over
   `Trusted.CrateV2`, so `specification` must name a
   `Trusted.MirSemantics.SpecsV2`. Set `edition`,
   `target`, `cfg`, optional `env` (`KEY -> VALUE` map for `env!`/`option_env!`),
   and `source_files` (including `crate_root`) inside clean relative paths
   under `source_root`. Only when verifying `library/core` itself, set
   `"stdlib_crate": "core"` (`verify rustc --stdlib-crate core`) with
   `crate_name` `core`, selected roots, and every staged `library/` file
   `core` reads; this admits `core`'s own language items, and the receipt's
   `configuration` records it.
2. Write the contract in `specification` modules (defaults `Spec.specs`,
   `Specs.safety`, `Specs.property`) and proofs in `proof` modules
   (`Proof.verify`).
   For `unsafe` functions, express real caller preconditions in `Specs.safety`;
   `False` vacuously admits zero callers. Keep `scope`, `cfg`, and specs fixed
   during proof debugging, and follow **`spec-authoring`** before any spec change.
3. Author Lean targets in `module` mode (matching
   `cargo anneal skill --example`, or omit `module` for legacy non-`module`
   files): start `Spec` with `module`, `prelude`,
   `public import Trusted.MirSemantics`, and `@[expose] public section ...
   end`, and start `Proof` with `module`, `prelude`,
   `public import Expected`, non-public `import Anneal.*`, and
   `public theorem Proof.verify : Expected.claim`. Proof modules (never
   `specification` modules) may import bundled 3-axiom `Anneal.*` libraries
   listed in `theory/bundle-manifest.json` (`Anneal.MirWp`, `Anneal.LoopInv`,
   `Anneal.BitVec`, `Anneal.LinearArith`, `Anneal.BitTrieLrat`), compiled and
   audited on demand when imported.
4. Keep Lean imports tight: import `prelude` plus only targeted `Init.*`
   modules (`~4` imports, `~152 MiB` peak RSS). Monolithic `import Init`
   (`~473 MiB`) fails closed in pinned `verify` unless `--allow-unpinned-lean`
   is passed. Pass `--lean-memory-mb <MB>` (or run inside a host cgroup memory
   cap such as `systemd-run --user --scope -p MemoryMax=...`), and pass
   `--max-inspector-output-bytes <BYTES>` (up to `1 GiB`) if a whole-crate
   inspector `result.json` exceeds the default `64 MiB` cap.

When adapting the example, pass `--artifacts <new-dir>`. Inspect `selected` and
`program` in `capture/capture.json` plus the goal in `generated/Expected.lean`.
Retention never writes into an existing path; to rerun into the same path, add
`--overwrite-artifacts`, which replaces only an empty directory or one carrying
the `.cargo-anneal-artifacts` marker that `verify` writes (never a symlink, a
directory containing the working directory or a verification input, or one
with unexpected entries) and first drops any earlier `result.json` and
`lean-lib/`.
Move to **`proof-scaling`** as soon as direct `execProg` / `simp` stalls.

## Scale crate proofs with Tarjan SCC sharding

When captured MIR exceeds `--shard-min-bodies` (default `20`), `cargo anneal`
automatically shards `Captured` along strongly connected components in
callee-first topological order (`Captured.Shard_000 .. Captured.Shard_<K-1>`)
and emits `generated/Proof/IdTree.lean` (`Proof.IdTree.idDecisionTree`) plus
`capture/capture_shards.json`. Sharding is transparent for `Proof` unless
`Proof/Shard_<k>.lean` is authored for incremental per-shard `.olean` caching:

- Tune thresholds with `--shard-min-bodies <N>` (default `20`),
  `--shard-max-bodies <N>` (default `20`, `>= 1`), and
  `--shard-max-ast-nodes <NODES>` (default `2500`, `>= 1`).
- Reserved top-level namespaces (`Captured.*`, `Expected.*`, `Trusted.*`,
  `Anneal.*`, `Init`, `Std`, `Lean`, `Lake`, `TrustedBoundary`) cannot be
  shadowed by authored files (which covers generated `Captured.Shard_*`). When
  sharding is active, `cargo anneal` generates `generated/Proof/IdTree.lean`
  (`Proof.IdTree`), and authors may provide `Proof/Shard_<k>.lean` modules to
  organize and cache per-shard proofs. Existing `>20`-body proofs referencing
  `Captured.body_N` or positional indices must switch to `Body.identity` keys
  or per-shard imports (or pass `--shard-min-bodies` to adjust the threshold).
- Generate or verify a static-DAG topology plan (`anneal-shards.json`) with
  `cargo anneal shard-plan` (`--request` or `--manifest-path`, plus `--write`
  or `--check`), and gate `cargo anneal verify` on a checked-in plan using
  `--verify-shard-plan <PATH>`:

```sh
cargo anneal shard-plan --manifest-path Cargo.toml --write anneal-shards.json
cargo anneal verify --manifest-path Cargo.toml --proof-dir proof --verify-shard-plan anneal-shards.json
```

Edits that preserve shard `identities`, `callee_shards`, `has_cycle`,
`oversized_scc`, and shard packing bounds keep `anneal-shards.json` unchanged,
whereas structural SCC or cross-shard edge changes or AST/body shard
re-packing fail closed with regeneration instructions. Sharded captures reorder
`program.bodies` into canonical callee-first Tarjan SCC order with
`entryDefId := 0` selecting canonical body `0`, so specs in sharded crates
should identify target bodies by `Body.identity` rather than `entryDefId` or
positional body indices. When sharding is active, Receipt v3 adds
`capture_shards_sha256` and `shards` (`total_sccs`, `cyclic_sccs`,
`total_shards`, `id_tree_sha256`, and per-shard metadata).

## Diagnose failures and read Receipt v3 honestly

Inspect `status`, `phase`, `detail`, and any actionable `hint` together; check
stderr if stdout is empty.

- `unsupported`: Fix invalid request/selector/path errors, or report exactly
  which target or Rust construct this version refused.
- `compiler_failed`: Fix the reported Rust diagnostics first.
- `tool_failed`: Diagnose the named setup, capture, sandbox, or artifact phase.
- `proof_failed`: **Step 0 — Day-2 Rust bug triage before proof hacking.**
  First check whether the receipt carries a structured `"reason"`
  (`"heartbeat_limit_exceeded"` or `"recursion_depth_exceeded"`): a
  `proof_failed` carrying `"reason"` is a deterministic Lean resource limit in
  an authored `Proof` module, not a proof or specification rejection, and must
  never be credited as a mutant kill. Otherwise, compare
  `generated/Expected.lean` and `capture/Captured.lean` (or
  `capture/Captured/Shard_*.lean` when sharded) against the Rust implementation
  to check whether the Rust code actually violates its specification (missing
  bounds/overflow guard, off-by-one, or unintended panic path). Never silently
  weaken `Specs.safety` or `Specs.property` to make a proof pass; escalate any
  implementation-vs-intent mismatch to the user.

For diagnostics, rerun with `--artifacts <dir>` (add `--export-lean-lib` to
copy Door-1-verified `.olean` files to `<dir>/lean-lib/`, omitting `proof`
`.olean`s on `proof_failed` exit `1` and exporting nothing on `tool_failed` exit
`2`). Receipt Schema v3 (`"schema_version": 3`) enforces a Uniform Flag-Driven
Taint Law across `--allow-unpinned-lean` (records `unpinned_lean`),
`--allow-unsandboxed-elaboration` (`"elaboration_sandbox": "none"`),
`--allow-sorry-in-proof` (records `sorry_declarations` in `proof` modules
only), and `--allow-unstable-feature <NAME>` (records `unstable_features`):
each flag prints `TAINTED` on stderr and appends `unpinned_lean`,
`unsandboxed_elaboration`, `sorry_in_proof`, or `unmodeled_unstable_features`
to `taint_reasons`.
For fast inner-loop proof iteration, `--fast-check` runs capture, toolchain
admission, specification preflight, and Lean elaboration while skipping `[6/6]`
kernel replay and target audit: it surfaces taint `fast_check_dev_mode` and
`UNVERIFIED_DEV_ONLY`, exits `3` (never `0`), never produces Receipt v3 JSON,
and refuses `--receipt-out`, `--artifacts`, `--overwrite-artifacts`,
`--export-lean-lib`, `--paranoid-quorum`, and `--format json`. Re-run without
`--fast-check` before claiming verification.

On exit `0` (`selected_unit_verified` / `crate_verified`, or `tainted_*` when
`taint_reasons` is non-empty), inspect `status`, `taint_reasons`,
`elaboration_sandbox`, `scope`, `configuration`, `audit.specificationClosure`,
and the spec declarations themselves. Report honestly: state exact verified
units, `cfg`/target triple, sandbox/taint qualifiers, non-vacuity (`Specs.safety`),
material assumptions, and any unverified callers or deferred checks.
