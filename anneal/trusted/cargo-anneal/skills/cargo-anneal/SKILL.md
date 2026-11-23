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

- Authoring, translating, or auditing specifications (`Spec.lean` / `Spec.*`,
  vacuity, anti-echo, Intent Decisions): use **`spec-authoring`**
  (`anneal/skills/spec-authoring/SKILL.md` in `google/zerocopy`).
- Scaling proofs past bounded `execProg`, reducing Lean RSS/timeouts, or
  escaping verification cliffs: use **`proof-scaling`**
  (`anneal/skills/proof-scaling/SKILL.md` in `google/zerocopy`).

## Run the project's verification

Identify the Rust function or crate scope, intended property, and caller
preconditions. If setup is needed, run `cargo anneal setup` (reuses an existing
cached toolchain for that version) or `cargo anneal setup --local-archive <path>`
to install a local archive. Pass `--clear-old` (or redirect stdin from
`/dev/null`) in non-interactive shells so cleanup prompts cannot block. Use the
same user and `XDG_CACHE_HOME` across `setup` and `verify`. Builds compiled with
`--no-default-features` omit `setup` and require `--capture`, `--sysroot`, and
`--lean`.

Run verification, save stdout to a receipt file, and keep its exit code:

```sh
cargo anneal verify --request path/to/request.json > path/to/receipt.json
```

Other entrypoints:
- Cargo packages: `cargo anneal verify --manifest-path path/to/Cargo.toml --proof-dir path/to/proofs`
- Build systems with explicit inputs: `cargo anneal verify rustc <crate_root> --crate-name <name> [--env KEY=VALUE ...] --spec-file <Mod>=<path> --proof-file <Mod>=<path> ...`

## Create a request and starter proof

Run `cargo anneal skill --example` to print a complete 4-file working example
from the installed CLI. Save the files together in a temporary directory to
test your environment; it proves termination and a zero return for a safe
no-argument function in the captured MIR model.

1. For request schema `1`, set `scope` to `{"kind": "selected_unit", "roots": ["mod::fn"]}`
   (`UnitTheorem`) or `{"kind": "crate"}` (`CrateTheorem`). Set `edition`,
   `target`, `cfg`, optional `env` (`KEY -> VALUE` map for `env!`/`option_env!`),
   and `source_files` (including `crate_root`) inside clean relative paths
   under `source_root`.
2. Write the contract in `specification` modules (defaults `Spec.specs`,
   `Specs.safety`, `Specs.property`) and proofs in `proof` modules (`Proof.verify`).
   For `unsafe` functions, express real caller preconditions in `Specs.safety`;
   `False` vacuously admits zero callers. Keep `scope`, `cfg`, and specs fixed
   during proof debugging, and follow **`spec-authoring`** before any spec change.
3. Import `Expected` in `Proof` and prove `Expected.claim`. Proof modules (never
   `specification` modules) may import bundled 3-axiom `Anneal.*` libraries
   listed in `theory/bundle-manifest.json` (`Anneal.MirWp`, `Anneal.LoopInv`,
   `Anneal.BitVec`, `Anneal.LinearArith`, `Anneal.BitTrieLrat`), compiled and
   audited on demand when imported.
4. Keep Lean imports tight: import `prelude` plus only targeted `Init.*`
   modules (`~4` imports, `~152 MiB` peak RSS). Monolithic `import Init`
   (`~473 MiB`) fails closed in pinned `verify` unless `--allow-unpinned-lean`
   is passed. Pass `--lean-memory-mb <MB>` (or run inside a host cgroup memory
   cap such as `systemd-run --user --scope -p MemoryMax=...`).

When adapting the example, pass `--artifacts <new-dir>`. Inspect `selected` and
`program` in `capture/capture.json` plus the goal in `generated/Expected.lean`.
Move to **`proof-scaling`** as soon as direct `execProg` / `simp` stalls.

## Diagnose failures and read Receipt v3 honestly

Inspect `status`, `phase`, and `detail` together; check stderr if stdout is empty.

- `unsupported`: Fix invalid request/selector/path errors, or report exactly
  which target or Rust construct this version refused.
- `compiler_failed`: Fix the reported Rust diagnostics first.
- `tool_failed`: Diagnose the named setup, capture, sandbox, or artifact phase.
- `proof_failed`: **Step 0 — Day-2 Rust bug triage before proof hacking.**
  Compare `generated/Expected.lean` and `capture/Captured.lean` against the
  Rust implementation to check whether the Rust code actually violates its
  specification (missing bounds/overflow guard, off-by-one, or unintended panic
  path). Never silently weaken `Specs.safety` or `Specs.property` to make a
  proof pass; escalate any implementation-vs-intent mismatch to the user.

For diagnostics, rerun with `--artifacts <dir>` (add `--export-lean-lib` to
copy Door-1-verified `.olean` files to `<dir>/lean-lib/`, omitting `proof`
`.olean`s on `proof_failed` exit `1` and exporting nothing on `tool_failed` exit
`2`). Receipt Schema v3 (`"schema_version": 3`) enforces a Uniform Flag-Driven
Taint Law across `--allow-unpinned-lean` (records `unpinned_lean`),
`--allow-unsandboxed-elaboration` (`"elaboration_sandbox": "none"`), and
`--allow-sorry-in-proof` (records `sorry_declarations` in `proof` modules
only): each flag prints `TAINTED` on stderr and appends `"unpinned_lean"`,
`"unsandboxed_elaboration"`, or `"sorry_in_proof"` to `taint_reasons`.

On exit `0` (`selected_unit_verified` / `crate_verified`, or `tainted_*` when
`taint_reasons` is non-empty), inspect `status`, `taint_reasons`,
`elaboration_sandbox`, `scope`, `configuration`, `audit.specificationClosure`,
and the spec declarations themselves. Report honestly: state exact verified
units, `cfg`/target triple, sandbox/taint qualifiers, non-vacuity (`Specs.safety`),
material assumptions, and any unverified callers or deferred checks.
