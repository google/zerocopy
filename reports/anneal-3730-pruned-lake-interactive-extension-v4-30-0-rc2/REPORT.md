# Prepared Lake pruning changes interactive extension behavior

## Summary

In one tiny pinned Lake project, deleting the compiled `Extra` and `Macro` OLeans and the native plugin dylib saved 102,240 bytes of 174,866 generated build bytes. The base proof and a proof using Lean's existing `decide` tactic still passed fresh batch checks. Proofs adding `Extra` or `Macro` imports and an explicit plugin load failed while those artifacts were absent. `lake --no-build build` reported both modules out of date. An ordinary `lake serve` session then rebuilt `Extra` from retained source when an unsaved scratch document imported it and returned its goal. Pruning therefore has different failure and recovery behavior depending on whether the consumer is allowed to build; a small artifact byte saving is not evidence of a complete interactive closure.

## Applicability

The fixture used cached Lean/Lake `v4.30.0-rc2` on macOS 26.6.2 arm64. A local Lake producer declared `Base`, `Extra`, `Macro`, and `Plugin`; a local consumer required it by relative path. `Base` defined `selected : Nat := 7`; `Extra` imported it; `Macro` defined a `new_tac` tactic macro expanding to `decide`; `Plugin` had a native initializer that wrote a marker. The producer built all four targets plus `+Plugin:dynlib` before the first consumer check. The script used no registry or remote dependency and set `LEAN_NUM_THREADS=1`, disabled Lake artifact cache, ran commands sequentially with 35-second limits (80 seconds for the initial build), and required 25% reported free memory and 5 GiB free disk. No guard fired.

The deletion was deliberately selective: only `Extra.olean`, `Macro.olean`, and the plugin dylib were removed. Source, `.ilean`, generated C, traces, `Base.olean`, and the Lean/Lake installation remained. The reported space fraction is therefore generated build-tree bytes in this fixture, not archive, installation, or total disk savings. This probes #3731 I120's module-pruning/new-interaction question and extends the earlier already-prepared tactic/plugin package; it does not exercise an Anneal archive.

## Findings

| Operation | Fully prepared | After selective pruning | Observation |
| --- | --- | --- | --- |
| Fresh batch proof importing `Base` | Exit 0 | Exit 0 | Selected base module remained available. |
| Fresh batch proof using built-in `decide` | Exit 0 | Exit 0 | This new proof tactic used the retained Lean core and base artifact. |
| Fresh batch proof importing `Extra` | Exit 0 | Exit 1, `unknown module prefix 'Extra'` | Retained source alone did not make the missing OLean importable in this no-build-style invocation. |
| Fresh batch proof importing `Macro` and using `new_tac` | Exit 0 | Exit 1, `unknown module prefix 'Macro'` | The new macro was unavailable without its compiled module. |
| Explicit `--plugin=<dylib>` load | Exit 0, initializer marker `plugin-loaded` | Exit 1, missing file; no marker | Native plugin availability is an operation-specific requirement. |
| `lake --no-build build Extra` / `Macro` | Not needed in full tree | Each exit 3, target out of date | A prepared consumer that forbids builds cannot supply these added imports from remaining source. |
| Unsaved `lake serve` scratch document importing `Base` | Not separately tested before deletion | Goal `⊢ selected = 7` | The retained base model remained queryable. |
| Unsaved `lake serve` scratch document importing `Extra` | Not separately tested before deletion | `Extra.olean` rebuilt; goal `⊢ extra = 8` | Ordinary Lake server preparation crossed the pruning boundary by rebuilding from source. |

Basis: **execution**, `support/results.json` command exits/stdout/stderr, versioned LSP messages, byte inventory, and initializer marker. The two unsaved scratch URIs had no physical source file. The `Extra` scratch document intentionally used `exact ?_`; its placeholder diagnostics do not negate the observed import and goal. The retained LSP event stream includes a progress diagnostic saying `Built Extra`; the post-session inventory newly contains `Extra.olean`. The `Macro.olean` and plugin dylib remained absent. The precise build policy of an Anneal consumer must be chosen explicitly; this run shows that an ordinary writable `lake serve` session can expand a selectively pruned universe when sources and compiler are present.

The generated build inventory was 39 files / 174,866 bytes before deletion and 36 files / 72,626 bytes immediately after. The three removed artifacts were `Extra.olean` 5,776 bytes, `Macro.olean` 45,344 bytes, and a plugin dylib 51,120 bytes, summing to 102,240 bytes. The checker confirms the arithmetic and the positive/negative command outcomes. A no-build command wrote its own trace marker after that inventory; the result records a separate after-no-build inventory before the live session so the later `Extra.olean` rebuild can be attributed to the live operation. Basis: **execution** for byte counts and file changes; **derived** for the policy implication.

## Boundaries

- This is a two-package local fixture, not a real Anneal generated archive or representative dependency universe. Its 102,240-byte reduction says nothing about Mathlib-scale or release distribution savings.
- Three individual artifacts were removed while source and other output families remained. A complete pruned archive might remove source, C, `.ilean`, traces, plugin OLean, or the compiler, changing both failure and recovery behavior.
- Only one added module, one tactic macro, one built-in tactic, one native initializer, and two unsaved scratch documents were tested. No arbitrary macro/plugin ABI or full interactive feature set was covered.
- The live `Extra` rebuild occurred in a writable producer tree under ordinary `lake serve`. A read-only/frozen prepared tree or strict no-build server may fail instead; that path was not run here.
- The native plugin was explicitly loaded by batch Lean. The live scratch session did not load or hot-swap it. No plugin failure recovery or server restart identity was measured.
- No Rust, Charon, Aeneas, Anneal, or proof-coverage oracle participated. The batch successes prove only the tiny stated Lean theorems.

## Evidence

- `support/probe.py`, SHA-256 `f7773f0e56164bfa2029aae5f78146b6537bd24fd266669a510ecc854902f036`, builds the local fixture, measures its exact files, removes the three artifacts, runs the operation matrix, and asserts the outcomes. It reuses the prior direct/Lake LSP framing harness, whose SHA-256 is recorded in the result.
- `support/results.json`, SHA-256 `4b106162cb62afcbb4d9385a1f9db70ecb4fbd5f29c74abb2acb68ec969205a1`, retains all source/build artifact hashes and sizes, command argv/exit/stdout/stderr, full/pruned/no-build/post-live inventories, two scratch query records, 55 server/client wire events, tool hashes, and preflight resource values.
- `support/check.py` verifies the retained result offline. `support/work/` contains the exact local producer/consumer sources and the post-live build state for replay and inspection. The prior `anneal-3730-lake-plugin-combined-family-mix-2026-09-29` report documents an already-prepared plugin/tactic combination, with no pruning operation.

## Revalidation

Run `python3 support/check.py` for the retained matrix. To recreate the local fixture with the cached binaries, run `python3 support/probe.py`, then the checker. The probe replaces only its own `support/work` and `support/results.json`. To decide an Anneal preparation contract, repeat the matrix with its actual archived graph and declared build policy, including read-only/no-build server startup, added imports, scratch documents, native plugin initialization, and a complete byte/operation inventory.
