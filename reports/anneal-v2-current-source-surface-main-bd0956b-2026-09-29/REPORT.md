# Anneal V2 source surface at zerocopy `bd0956b`

## Summary

The current Anneal redesign has a callable `setup` command and source-level scaffolding for target selection, LLBC path naming, toolchain paths, and directory locking. It does **not** yet expose a verification command or connect those helpers to Charon, Aeneas, Lean proof generation, an editor, or MCP. The v21 #3730/#3731 audit's description of product-gated verification work remains substantively correct, but a blanket statement that there is no current V2 implementation misses these concrete source surfaces. Source presence does not convert component experiments into product acceptance evidence.

An offline build and default unit-test attempt both stopped before compilation because the pinned Charon git dependency was absent from the local Cargo cache. Neither attempt validates runtime behavior or test outcomes.

## Applicability

This report concerns the tracked `anneal/` redesign in `google/zerocopy` at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, inspected in a checkout whose only preexisting Anneal modification was `anneal/v1/Cargo.lock`. `anneal/v1/` is historical, as `anneal/AGENTS.md` and `anneal/README.md:15-18` explicitly say; no V1 behavior is attributed to V2. The v21 crosswalk, current at the time of this addendum on 2026-09-29, is used only to map source observations to investigation IDs and suggestion IDs. It is not evidence that the current source implements each requested behavior.

`anneal/PRINCIPLES.md` requires fail-closed UB verification and a meaningful TCB promise; `anneal/DESIGN.md` requires scoped success, justified Rust semantics, and a Rust-oriented ordinary path. Those are normative project constraints, not claims that this binary presently meets them. The checked-in source determines the current implementation.

## Findings

### Reachable CLI and dormant modules

`main.rs:21-33,81-96` defines a `cargo-anneal` CLI with one subcommand, `Setup`, including Cargo-plugin argument normalization. `main.rs:58-79` invokes exocrate resolution/install for a local archive or a configured remote archive. The remote platform URLs and hashes in `Cargo.toml:27-44` are expressly placeholders. `main.rs:12-19` compiles `resolve`, `scanner`, `setup`, and `util` with `allow(dead_code)`, but no call from `main` reaches their target resolver, scanner, toolchain command wrapper, or process helper. In particular, the `resolve::Args` verification selectors and `allow_sorry` flag at `resolve.rs:27-72` are structures only; they are not accepted by the current CLI. A source search over the five V2 Rust files found no verification command, Charon extraction call, Aeneas translation call, generated proof writer, LSP handler, or MCP handler. This is a finite source-scope observation, not a claim about future branches.

`main.rs:99-141` places the archive tests behind both `#[cfg(test)]` and feature `exocrate_tests`; the tests expect `target/anneal-exocrate.tar.zst` from a CI dependency builder. `main.rs:143-336` constructs a small generated Lake workspace, rewrites a relative manifest, then asks Lake to build `Generated` and run `lean --json`; it does not run a Lean server or proof query. That is meaningful test code for archive consumption, but its behavior was not executed here and it is not a production preparation path. The separate `setup.rs:16-30,61-71,127-153` defines another exocrate config/toolchain resolution path that is currently unreachable from `main`.

### Implemented helpers and their limits

| Surface | What source actually provides | Limit relevant to #3731 |
| --- | --- | --- |
| Cargo subject selection | `resolve.rs:204-269` uses managed Cargo/rustc for `cargo metadata`, forwards feature selectors, checks local path dependencies, and enumerates package targets. `resolve.rs:300-435` implements package and target selectors, including separate crate kinds. | No CLI call reaches it; the key does not include the complete compilation unit (profile, triple, cfg/build outputs, host role) or prove the Charon-producing invocation occurred. |
| Output locators | `resolve.rs:272-297` hashes workspace-root path into a run-directory locator. `scanner.rs:35-100` derives a Lean-compatible LLBC filename from manifest path, target name, and kind using a truncated SHA-256 hash. | These are locators, not authenticated source/model/tool/import generations. The 64-bit truncation reduces accidental collisions but cannot guarantee uniqueness as the source comment suggests. No LLBC-producing stage uses them yet. |
| Filesystem exclusion | `resolve.rs:166-201` requires a `LockedRoots` value for its LLBC path accessor; `util.rs:15-79` implements an OS file lock on a directory `.lock` file. `util.rs:223-282` contains exclusive/shared lock unit tests. | The run-root exclusive lock is not invoked by the current CLI; `resolve.rs:172-174,197-201` exposes a global shared Cargo target directory outside that run-root lock. This is not a product lock-order, single-flight, transaction, or cancellation contract. |
| Tool invocation utilities | `setup.rs:32-110` maps managed Cargo/rustc/Charon paths and prepares a sanitized process environment. `util.rs:82-141` streams a child process's output and status. | There is no Charon/Aeneas/Lean stage orchestration, structured stage identity, proof acceptance, or reuse path. |
| Prepared Lake fixture | `main.rs:143-190,220-336` validates a read-only Aeneas path and assembles a relative path manifest for a feature-gated archive test. | No actual archive was available in this run; no live setup-file/InfoView/RPC/plugin operation or complete production prepared-environment identity is established. |

These are source observations. The source comments often describe intended later Charon/Lean stages (`resolve.rs:17-22,207-209`; `scanner.rs:38-40`), but the comments do not make those stages operational.

### Item-level consequences for the v21 ledger

The table identifies where a residual should acknowledge current code. The recommended status is for the **requested investigation**, not a code maturity rating. In v21, all listed rows except I137 and I138 are `partial`; I137 and I138 are `complete` for their disposable-prototype scopes. Source inspection and a blocked build do not change any of those classifications.

| #3731 items; relevant mapped #3730 suggestions | Source-informed correction to the residual | Status consequence |
| --- | --- | --- |
| I020, I075, I076; D07 | Target/package/kind enumeration and a distinct LLBC filename are implemented as unconnected helpers (`resolve.rs:204-269,381-435`; `scanner.rs:35-100`). Still missing complete compilation subject and actual selected Charon run/LLBC collision rejection. | Retain partial; replace any “no V2 target selection” phrasing with this narrower gap. |
| I078, I080, I107, I108; D03, D06, F12, H09, J13 | `LockedRoots` and `DirLock` supply a single run-directory exclusion primitive (`resolve.rs:166-201`; `util.rs:15-79`). The global Cargo target path is separate, and no publication, multi-consumer ownership, cancellation, or lock ordering is wired. | Retain partial; do not count the lock primitive as a pipeline concurrency result. |
| I089, I090, I091, I092, I096, I150; F01, F02, F04, F05, F06, F07, F08 | `setup` and a feature-gated read-only Lake archive fixture exist (`main.rs:29-79,99-190,220-336`; `Cargo.toml:4-6,27-44`). The real archive, clean consumer, server first goal, loaded-environment attestation, and operation-specific prepared contract remain untested or absent. | Retain partial. Source test intent should be recorded separately from execution evidence. |
| I009, I079, I103, I123, I145; A01, A02, A08, F05 | Workspace/run and LLBC names encode some stable locators (`resolve.rs:272-297`; `scanner.rs:43-100`); they do not encode exact source, translation, generated tree, prepared Lean environment, worker/RPC incarnation, or trust state. | Retain partial; no full freshness or identity acceptance claim. |
| I129, I130, I137, I138, I149, I157, I159; I05-I08, E08, K02, L07-L08, N01-N12 | The CLI has no verify path (`main.rs:29-33,94-96`), generated obligation/claim manifest, checked result, live proof query, or Rust-hosted annotation projection. The Lake fixture's `import Aeneas` is not a generated proof (`main.rs:154-187`). | Retain v21's `complete` classification for the I137/I138 disposable prototypes and `partial` for the other listed items; the current V2 product integration remains open. |

The v21 ledger's `I072` existing-MCP-adapter experiment remains `not-run`; this source contains no MCP adapter. The `I137` and `I138` disposable vertical slices and Lean component rows `I046` and `I049` are `complete` within their stated investigation scopes. Those statuses do not establish implementation in the current Anneal binary. The mapped #3730 `F04` real-archive missing-manifest control remains `not-run` in v21; the source fixture is not an execution of it.

### Offline build and test result

On macOS, Homebrew `cargo 1.98.1` and `rustc 1.98.1`, both commands used the checked-in manifest, `--locked --offline`, and an external target directory under `.anneal-local-tools/`:

```text
cargo test --manifest-path /Users/josh/Codex/Projects/zerocopy/anneal/Cargo.toml --locked --offline --target-dir /Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/target-anneal-v2-source-audit
exit 101: failed to get `charon` ... can't checkout from https://github.com/AeneasVerif/charon.git?tag=nightly-2026.06.03#0c91ca1a ... offline mode

cargo build --manifest-path /Users/josh/Codex/Projects/zerocopy/anneal/Cargo.toml --locked --offline --target-dir /Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/target-anneal-v2-source-audit
exit 101: same pinned `charon` git checkout unavailable in offline mode
```

`Cargo.toml:64-65` declares the git dependency. Cargo stopped during dependency resolution, before compilation or any test. No dependency fetch, installation, or archive setup was attempted. The default unit-test run would also omit `main.rs`'s `exocrate_tests` module unless that feature were enabled; `util.rs:223-282` has default unit tests, but none ran.

## Boundaries

- **Not examined:** `anneal/v1/` implementation, the modified V1 lockfile, and untracked `anneal/research/` content. They are not current redesign authority.
- **Unexecuted:** Current V2 Rust code was not compiled or unit-tested here because the pinned git checkout was unavailable offline. The feature-gated archive test was not run, and a built Anneal archive was not inspected.
- **Not established:** Correctness of Cargo selection across real build matrices, collision freedom, lock behavior under cross-process failure, archive cache reuse, successful proof checking, batch/live equivalence, LSP/MCP behavior, generated-proof edit support, and Anneal's conditional TCB promise.
- **Status scope:** The audit v21 classifications measure investigation coverage; this report only adds a present-source implementation map. A later audit may change its wording without changing item status.

## Evidence

- **Normative:** `google/zerocopy` `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, `anneal/PRINCIPLES.md` (“Anneal's promise to its users”) and `anneal/DESIGN.md` (“Verification success has a precise meaning”; “Rust-level claims require justified Rust semantics”).
- **Source:** Same commit, `anneal/AGENTS.md`; `anneal/README.md:9-18`; `anneal/src/main.rs:12-96,99-336`; `anneal/src/resolve.rs:27-72,157-201,204-297,300-472`; `anneal/src/scanner.rs:12-102`; `anneal/src/setup.rs:16-153`; `anneal/src/util.rs:15-141,223-282`; `anneal/Cargo.toml:4-6,27-68`.
- **Crosswalk:** `google/zerocopy` reference revision `a5b4d034aa65aa44d85afc943c3caec26a5229ba`, `reports/anneal-3730-3731-final-coverage-audit-2026-09-29-v21/REPORT.md` and `support/investigation-final-v21.csv`, `support/3730-crosswalk-final-v21.csv`, observed 2026-09-29. v21 was the latest published audit at the time of this addendum. These preserve requested scopes and mapped suggestion IDs, not current implementation claims.
- **Execution:** The two exact offline Cargo invocations and results above, observed 2026-09-29. Repository status before/after showed the preexisting `anneal/v1/Cargo.lock` modification and untracked `.anneal-local-tools/`, `.local/`, and `anneal/research/`; this investigation did not edit those areas.

## Revalidation

At a later zerocopy revision, first inspect `anneal/AGENTS.md`, `PRINCIPLES.md`, `DESIGN.md`, then enumerate `anneal/src` and the actual CLI dispatch. Trace calls from each exposed command to Charon, Aeneas, Lean, acceptance, LSP, and MCP code; distinguish compiled helpers from reachable paths. Recheck the cited target/lock/locator regions and run `cargo test --locked --offline` with an external target directory only when all pinned dependencies are locally available. Run archive-feature tests only with a documented real archive and controlled consumer state. Update the #3731 row residuals from executed behavior and exact source reachability, not from comments or test names.
