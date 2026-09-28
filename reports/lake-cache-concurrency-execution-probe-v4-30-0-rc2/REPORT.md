# Lake cache equivalence and concurrency

## Summary

Two consumers succeeded concurrently against one frozen prebuilt dependency with relative manifests, while two consumers sharing a writable source-only producer both targeted the same build outputs. The report inventories artifact equivalence requirements and Mathlib cache behavior.

## Applicability

Small synthetic Lean/Lake packages on macOS arm64 with Lean 4.30.0-rc2. Mathlib conclusions are source inspection at the manifest-pinned revision; no Mathlib cache archive was downloaded in this probe. Related corpus reports: [lake-clean-cache-seeded-equivalence-v4-30-0-rc2](../lake-clean-cache-seeded-equivalence-v4-30-0-rc2/REPORT.md), [lake-artifact-cache-architecture-v4-30-0-rc2](../lake-artifact-cache-architecture-v4-30-0-rc2/REPORT.md), [mathlib-cache-artifact-format-v4-30-0-rc2](../mathlib-cache-artifact-format-v4-30-0-rc2/REPORT.md).

## Findings


### Scope and controls

This is a Nix-independent Lake study for Anneal's redesign. I read [Anneal's principles](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/PRINCIPLES.md), [design contract](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/DESIGN.md), and [agent guide](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/AGENTS.md). The experiment is synthetic; `v1/` is historical evidence, and a successful Lake build is not an Anneal verification result. In particular, Lean artifact reuse cannot by itself establish Rust semantics, complete obligation coverage, or a TCB audit log.

The host was macOS arm64 with **78 GiB free** before the probe. Scratch is [`support/lake-cache-concurrency`](support/lake-cache-concurrency); final size was **1.3 MiB**. No 6 GiB Mathlib tree was copied, no Nix or Docker was invoked, and no cache download or credential access occurred. Each Lake command was bounded to 30 seconds; the largest observed command took 3.728 seconds. There were at most two simultaneous Lake processes. `LEAN_NUM_THREADS=1`, `LAKE_CACHE_DIR=''`, and `MATHLIB_NO_CACHE_ON_UPDATE=1` were set. The fixture has a serial import chain, but these settings do **not** establish a global one-worker bound for an arbitrary Lake graph.

The environment came from `# Set PATH to the pinned local binaries identified above.` with `ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0-rc2`. The resolved local `lake` is version `5.0.0-src+3dc1a08` (Lean `4.30.0-rc2`); `lean` identifies commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, target `arm64-apple-darwin24.6.0`. SHA-256: `lake` binary `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; `lean` binary `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; [probe script](support/lake-cache-concurrency/probe.py) `04ce02b0df9d64ceda7e5a98365ff3c9348258ffe01d7d15704ee212eb198d05`. Lean/Lake source is the local checkout at the same commit. The vendored Mathlib manifest pins `mathlib` to `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; I used its source only.

### Exact fixture and commands

The producer package `probe_dep` has `Dep.lean` defining `depValue : Nat := 7`; each consumer has `Generated.lean` importing `Dep`, proving `depValue + 1 = 8` by `decide`, and evaluating it. Every consumer received a `lake-manifest.json` **before its first Lake invocation** with a path entry `"dir": "../producer"`; its SHA-256 is `3c7645369d322de36fde6c8056e660d5e8a32c511b81bb2e99d050737e1ecfe2`. All invocations used the pinned absolute `.../leanprover--lean4---v4.30.0-rc2/bin/lake`. [runs.json](support/lake-cache-concurrency/runs.json) records every exact executable, argument vector, working directory, selected environment, exit status, wall time, stdout, and stderr. The main command forms were:

```text
lake --keep-toolchain --no-cache --old build Generated
lake --keep-toolchain --no-cache setup-file Generated.lean
lake --keep-toolchain --no-cache env lean --json Generated.lean
```

`--no-cache` disables Lake cache use for these probes; it is not a network firewall. `--old` permits mtime reuse when dependency hashes have changed. It should not be treated as proof of content or semantic equivalence ([Lake's check](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean)).

### Observations

| Cell | Result | Interpretation limit |
|---|---|---|
| Clean source-only producer, fresh consumer | Build exit 0 in 3.728 seconds. `Dep` and `Generated` were built; theorem accepted and `#eval` printed `8`. `setup-file` and Lean `--json` both exited 0; Lean JSON reported `8`. | One tiny module pair, same host and toolchain. |
| Two fresh consumers, concurrently, against one copied and frozen producer build | Both builds exited 0 in 0.728 seconds and printed `8`; neither reported rebuilding `Dep`. Both `setup-file` calls exited 0 and pointed `importArts.Dep` to the seeded producer OLean. A subsequent `--old --no-build build Dep` exited 0 and said all targets were up to date; seeded Lean `--json` diagnostics exactly matched the clean run. The producer's full file SHA-256, byte size, and `mtime_ns` inventory remained identical through these calls. | One run with two processes, no native/plugin dependency, no real Aeneas/Mathlib graph. |
| Two fresh consumers, concurrently, sharing one writable source-only producer and build directory | Both exited 0 in about 0.87 seconds. Both reported **building `Dep`** and `Generated`, so they wrote the same producer build-product paths concurrently. | Success in one run does not establish collision safety or file integrity under interruption. |

The producer and consumer inventory files are [clean](support/lake-cache-concurrency/clean-inventory.json), [seeded](support/lake-cache-concurrency/seeded-inventory.json), and [shared writable](support/lake-cache-concurrency/shared-writable-inventory.json). In clean and both seeded consumers, `Generated.olean` has SHA-256 `6ec0c3b7d9ecaef15b5e5458b7a0de40f41f252868f4004d2b58d9c6eb3e8302`, `Generated.ilean` has `1046a5ab5df732122fbf1a4a6267904d1943ab002a3839e6a2d37289cddf8bf4`, and `Generated.c` has `d18ac49a927969b7fb46c06339291a1160c07ca38489acb819e14dac70038b2d`. The `Generated.trace` files differ bytewise because their logs contain absolute workspace paths, although each has the same `depHash` (`bf169a794ed0fefe`) and output descriptor set. `Generated.setup.json` differs by absolute dependency path. Byte identity of the three products is useful diagnostic evidence, **not** a proof of equal semantics; the accepted theorem, diagnostics, imported artifacts, and source/config identity are separate checks.

### Semantic equivalence inventory

For an Anneal build-cache acceptance test, compare these independently. The current fixture covers only the indicated subset.

| Layer | Required comparison and why | Fixture coverage |
|---|---|---|
| Source and configuration | Exact source, generated module, `lakefile`, relative manifest, toolchain, options, dependency revisions, and package identity. A different generated obligation is a different verification claim. | Tiny source and manifest were identical by construction; no real generated Rust model. |
| Compiled Lean declarations | Import the `.olean` in the intended dependency environment; type-check/rebuild a downstream theorem that actually relies on it. Include `.olean.server`/`.olean.private` for module-system packages. | The downstream `generatedEq` theorem was accepted; ordinary `.olean` bytes matched. No module-system facets. |
| Interactive references | Compare `.ilean` and editor reference/navigation behavior where promised. Equal file hash alone does not prove a live server resolves references after relocation. | `.ilean` bytes matched; reference RPCs were not exercised. Lean's LSP source describes reference information in `.ilean`/watchdog flow. |
| Traces and hash sidecars | Check trace dependency inputs, output descriptors, log meaning, path relocation, and `.hash` correspondence. Lake's hashes are not cryptographic attestations, and `--old` can bypass mismatched dependency hashes using mtimes. | Same `depHash`/descriptors; differing absolute-path logs. `.hash` files for three built outputs matched; no tamper or collision test. |
| Native products | Compare generated C/IR, `.o`, static/shared libraries, dynlibs/plugins, and target ABI when used. Native outputs and config traces may be platform-sensitive. | Generated `.c` matched; no native object or shared library in the fixture. |
| Server setup and diagnostics | `setup-file` must resolve import OLeans, plugins, dynlibs, options and package identity at the relocated path; test `lean --json` and, separately, actual LSP reference behavior. | `setup-file` resolved `Dep.olean` in each location; clean and seeded `lean --json` produced equal diagnostics with value `8`. No live LSP session. |
| Anneal proof claim | Re-check generated obligations, theorem coverage, kernel acceptance, source/model correspondence evidence, and the result's trust/TCB record. | Outside this Lake experiment. |

Lake's [module build code](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean) enumerates `.olean`, optional server/private OLeans, `.ilean`, `.c`, optional `.bc`, traces, and hash sidecars. It clears output artifacts before rebuilding and writes trace files after a successful action. [Configuration loading](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean) uses `.lake/config/<package>/lakefile.olean`, a `.trace`, and an `.olean.lock`; it takes a shared trace lock for valid configuration and exclusive locks for reconfiguration. The prior [Lake probe](../lake-generated-workspace-readonly-probe-v4-30-0-rc2/REPORT.md) observed a missing manifest triggering a write attempt to that lock in a read-only package. This probe deliberately seeded manifests first.

### Sharing and collision boundaries

**Observed:** Two consumers can read one frozen, prebuilt dependency tree in this fixture without changing it. Two concurrent builds against a writable, source-only shared package each built `Dep`; they targeted the same `.lake/build` outputs. Each generated consumer retained its own `.lake/build` and `.lake/config/[anonymous]`, so consumer-owned writes were separated.

**Source-backed:** Lake's configuration trace locking guards the `.olean`/trace reconfiguration pair, but that code explicitly says simultaneous reconfigurations may error; it is not a general package-build transaction lock. Module build actions clear and then regenerate output paths, hashes, and traces. Lake's system artifact-cache map uses shared/exclusive file locks for its JSON Lines map, but that does not make arbitrary shared package build directories safe for concurrent writers ([CacheMap](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Cache.lean)). The Mathlib-specific cache also writes `.ltar.part`, `curl.cfg`, and decompressed package artifacts when `get` runs; it was not run here.

**Proposed boundary:** Publish a dependency universe only after one staging build has completed and artifact/source/config checks pass. Consumers get distinct generated workspace directories and relative manifests preseeded before Lake starts. Freeze the dependency universe during consumer builds. If rebuilding shared dependencies is required, give one writer exclusive ownership or create an isolated new version and atomically publish it. Do not infer concurrency safety from duplicate successful writers. Avoid `--rehash` against read-only dependencies unless the needed sidecars have been precomputed, because Lake's `fetchFileHash` can write `.hash` files when missing or untrusted ([Common.lean](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Common.lean)).

### Mathlib cache architecture and platform behavior

This is from the vendored Mathlib source at the pinned manifest revision, not from a cache download. [`lake exe cache get-`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Main.lean) downloads linked `.ltar` files without decompressing; `get` downloads then decompresses. `MATHLIB_CACHE_DIR` defaults to `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib` ([Cache/IO.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean)). The cache file hash mixes a root hash from Mathlib's `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, and a generation counter with each module's relative path, normalized source text, and imported-file hashes ([Cache/Hashing.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Hashing.lean)). The README says the Lean compiler Git hash is also mixed directly; the inspected `getRootHash` implementation does not visibly do so, though `lean-toolchain` usually selects the compiler version. This discrepancy warrants a targeted upstream check before relying on the stronger claim.

The [pack list](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/IO.lean) requires trace, OLean and OLean hash, ILean and ILean hash, C and C hash, and optionally includes server/private OLeans, IR, and extras. It does not list native `.o` or shared libraries, so they need separate treatment. Unpacking compares an LTAR header's Lake dependency hash with the existing trace to decide whether to skip; a matching trace is a freshness heuristic, not semantic certification. Mathlib's downloader selects a repository and Azure/Cloudflare endpoint and writes files under `f/.../<hash>.ltar` ([Cache/Requests.lean](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Cache/Requests.lean)). Its `post_update` hook may run `cache get` unless `MATHLIB_NO_CACHE_ON_UPDATE=1` is set, so an offline design must control update behavior as well as ordinary build invocations ([Mathlib lakefile](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/lakefile.lean)).

Platform neutrality must not be assumed. The Mathlib module filename hash above does not visibly include host target, while Lake's config trace explicitly records `System.Platform.target` and Lake can mix a platform trace into module inputs. The [Anneal flake](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/flake.nix) pins different Mathlib cache-download hashes per host system and handles a separate native `leantar` binary. The sensible conclusion is **platform-specific validation and packaging**, not cross-platform interchangeability. The current probe ran only on macOS arm64; it did not compare Linux, x86_64, Mathlib `.ltar` contents, or native linkage.

### Setup/prompt adjustment

Require every generated workspace to receive its complete **relative** `lake-manifest.json` before the first Lake command. Treat a published dependency package source plus build products as an immutable, platform/toolchain-specific unit; allow concurrent readers with separate consumer workspaces, and serialize or isolate any producer writes. Ask the next real-archive probe to compare source/config identity, trace inputs and outputs, imported declarations, `.ilean`/references, native products, `setup-file`, Lean diagnostics, and final Anneal coverage/TCB evidence. Keep it bounded and Nix-independent, and distinguish `--no-cache` from verified network isolation.

## Boundaries

The concurrency result is one two-process trial, not a safety proof. No live LSP reference RPC, module-system private OLean, native object/shared-library comparison, Linux/x86_64 cache test, or multi-GiB Mathlib clone was run.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. Executed-probe support material is included under `support/lake-cache-concurrency/`; local home/checkout prefixes are redacted in text artifacts.

## Revalidation

Use the included probe script, manifests, and inventories. Keep dependency producers immutable during consumer runs; repeat read-only-consumer and shared-writer cells under process interruption and compare source, traces, sidecars, setup output, Lean diagnostics, and downstream imports.
