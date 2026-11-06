# Aeneas Trait, Namespace-Move, and External-Model Invalidation, Restricted Module Reuse, and Last-Good Model Recovery

## Summary

Six execution experiments under pinned Charon `0.1.210`, Aeneas `nightly-2026.06.03`, Lean 4 `v4.30.0-rc2`, and Rust `nightly` establish how module moves, declaration reordering, output-file set shrinkage, trait body versus signature edits, external-model updates without codegen changes, and transient Rust compilation/translation failures affect generated Lean modules and downstream proof checking:

1. **Namespace moves, declaration reordering, output shrinkage, and `sorry` taint (`support/aeneas-namespace-move-proof-context/`, `support/aeneas-trait-output-shrink-matrix/`):**
   - Moving a Rust helper from `core::use_step` to `moved::core::use_step` while keeping its body and caller unchanged renamed the generated Lean definition from `move_probe.core.use_step` to `move_probe.moved.core.use_step` (changing `Funs.lean` while leaving `Types.lean` and the root entry file unchanged); `move_probe.caller` kept its name and passed its `rfl` proof, while referencing the old helper name failed as an unknown identifier.
   - Reordering unchanged Rust items in `trait_probe` changed the SHA-256 digests of `Types.lean`, `Funs.lean`, and `FunsExternal_Template.lean` (shifting `use_step` in `Funs.lean` from line 38, bytes `[1826,1876)` to line 50, bytes `[2571,2621)`) while preserving Lean declaration names and caller proof acceptance.
   - Removing `old` and `extern "C" external_double` (`shrink` variant) reduced a clean `-dest` directory from 4 files (`Types.lean`, `Funs.lean`, `FunsExternal_Template.lean`, entry) to 3 files (omitting `FunsExternal_Template.lean`), whereas regenerating into a reused `base` directory left the stale `FunsExternal_Template.lean` on disk.
   - Introducing an unsupported raw-pointer dereference (`error` variant) caused Aeneas to exit `1` while emitting `Types.lean`, entry, and a partial `Funs.lean` (`def bad ... := do sorry`) that compiled under Lean `v4.30.0-rc2` and tainted `bad` with `[sorryAx]`.
2. **Restricted compiled `.olean` reuse across trait body versus signature edits (`support/aeneas-restricted-reuse/`):**
   - In a split three-module graph (`Fixture.Types → Fixture.Funs → Fixture`), editing only a trait implementation body (`wrapping_add(1)` → `wrapping_add(2)`) left `Types.lean` and `Fixture.lean` source bytes identical while changing `Funs.lean`. A conservative recursive reuse rule safely reused `Fixture.Types.olean` and recompiled only `Fixture.Funs` and `Fixture` (2 Lean compiles instead of 3, passing updated proofs `3, 14, 11`), whereas reusing stale `Fixture.Funs.olean` failed the updated proof (`sorryAx`).
   - Editing the trait method signature (`step(self)` → `step(self, delta: u32)`) changed both `Types.lean` and `Funs.lean` (leaving `Fixture.lean` source text equal), permitting zero `.olean` reuse; attempting to reuse baseline `Fixture.Types.olean` when compiling the new `Funs.lean` failed with a Lean structure-field type mismatch.
3. **External Lean model mutation with byte-identical Aeneas codegen (`support/external-model-without-codegen-change/`):**
   - Holding Aeneas's generated `Types.lean`, `Funs.lean`, `FunsExternal_Template.lean`, and entry files byte-identical while swapping the user-authored `Source/FunsExternal.lean` between `external_double x = x + x` (proof of `external_call 1 = .ok 2` passes, 0 axioms), `x + 2` (proof fails), `axiom external_double` (proof fails, lists `external_double` axiom), and a missing declaration (`Funs.lean` fails to compile) changed verification outcomes without any codegen diff.
   - Pairing the wrong `FunsExternal.lean` source (`x + 2`) with stale `.olean` files compiled from `x + x` caused batch Lean to falsely accept `external_call 1 = .ok 2` (`exit 0`). Rebuilding `FunsExternal.lean` and its `.olean` files to the wrong model on disk while an existing `lean --server` and file-worker process stayed open left the live worker reporting the old concrete model's axioms and accepting the proof after a document edit, whereas a freshly spawned `lean --server` rejected the proof.
4. **Last-good model feedback during broken Rust states and signature-changing recovery (`support/last-good-model-after-rust-failure/`, `support/last-good-model-signature-recovery/`):**
   - After a valid model `A` (`inc(u32) -> u32`, `+1`), a Rust syntax failure (`Charon exit 2`, leaving `A`'s `current.llbc` on disk) or an Aeneas raw-pointer failure (`Aeneas exit 1`, writing partial `Funs.lean` with `sorry`) leaves no valid current model. Routing proof edits against retained model `A` returns `Lean exit 0`, which must be fenced as `provisional / stale` (`current_verified = false`) and invalidated once valid recovery model `B` (`inc(u64) -> u64`, `+2`, `Std.U64 → Result Std.U64`) is published—where old `U32` proofs fail with a type mismatch, adapted `U64` proofs pass, and late-completing `A` proof runs (`exit 0`) are rejected by model-generation digest mismatch.

## Applicability

All observations apply to the combined execution of:

- **Lean 4 and Lake `v4.30.0-rc2`** (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`);
- **Charon `0.1.210`** (`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`);
- **Aeneas `nightly-2026.06.03`** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, binary SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`);
- **Rust compiler `1.98.0-nightly` (`nightly`)** (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, binary SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`).

Only a single version of each subject is examined. All runs executed offline on macOS `arm64` using `charon rustc --preset aeneas`, one-shot `aeneas -backend lean -sequential -split-files -gen-lib-entry`, and Lean `v4.30.0-rc2` batch and `--server` processes linked against the prebuilt Aeneas Lean runtime (`LEAN_PATH`).

## Findings

### Namespace Moves, Declaration Reordering, Output Shrinkage, and Error Taint (`support/aeneas-namespace-move-proof-context/`, `support/aeneas-trait-output-shrink-matrix/`)

In `support/aeneas-namespace-move-proof-context/`, moving `use_step` from module `core` to `moved::core` while keeping its body and `caller` unchanged produced the following Lean proof-context transition:

| Variant | Generated helper identifier | Generated caller identifier | `Types.lean` / entry / `Funs.lean` digests | Fresh caller & current-helper `rfl` proofs | Lookup of old `move_probe.core.use_step` |
| --- | --- | --- | --- | --- | --- |
| Base | `move_probe.core.use_step` | `move_probe.caller` | Baseline | Pass (axioms: `propext`, `Classical.choice`, `Quot.sound`) | Present |
| Nested module move | `move_probe.moved.core.use_step` | `move_probe.caller` | `Types.lean` & entry equal; `Funs.lean` changed | Pass (no `sorryAx`) | Rejected (`unknown identifier`) |

In `support/aeneas-trait-output-shrink-matrix/` (36 chronological events / 35 command records, total wall time `51.65 s`, Charon `52–64 ms`, Aeneas `226–235 ms`), four variants of `trait_probe` (`Step::step` for `u32`, `use_step`, `old`, and `extern "C" external_double`) were translated into clean private directories and checked with fresh Lean processes:

| Variant | Charon / Aeneas exit | Clean generated file set | Generated Lean declaration heads | Fresh Lean batch verification outcome |
| --- | --- | --- | ---: | --- |
| `base` | `0 / 0` | `Types.lean`, `Funs.lean`, `FunsExternal_Template.lean`, entry | 7 | Module chain and `use_step 1 = .ok 2` passed (`rfl`); replacing `axiom external_double` with concrete `x + x` made `external_call 1 = .ok 2` pass with 0 axioms. |
| `reorder` | `0 / 0` | Same 4 filenames (all 3 content files changed SHA-256) | 7 | `use_step` moved from `Funs.lean` line 38 (`[1826,1876)`) to line 50 (`[2571,2621)`); `Types.lean` changed `Step` span comment; selected caller proof still passed. |
| `shrink` (remove `old` & `external_double`) | `0 / 0` | `Types.lean`, `Funs.lean`, entry (3 files; `FunsExternal_Template.lean` absent in clean dir, but retained as stale file when run in a copy of `base` dir) | 4 | `use_step 1 = .ok 2` passed; `#check old` and `#check external_call` failed as unknown identifiers. |
| `error` (raw-pointer dereference) | `0 / 1` | `Types.lean`, partial `Funs.lean`, entry | 5 | `Funs.lean` contained `def bad ... := do sorry`; Lean compiled the file and `#print axioms bad` reported `[sorryAx]`. |

Basis: **execution** in `support/aeneas-namespace-move-proof-context/raw-results.json` and `support/aeneas-trait-output-shrink-matrix/raw-results.json` (SHA-256 `d4891c9f4e990f817c4fceaeb2e7aaf316fdfd6d11cbb91e97266e804270d089`).

### Restricted Compiled-Module Reuse Under Trait Body versus Signature Changes (`support/aeneas-restricted-reuse/`)

In `support/aeneas-restricted-reuse/`, whole-crate Aeneas split output for `Fixture` (`core.Step::step`, `u32` impl, `core.use_step`, `side.untouched`, and `combine`) formed the linear import chain `Fixture.Types → Fixture.Funs → Fixture`. A conservative recursive `.olean` reuse fence (permitting reuse of a module's `.olean` if and only if its generated `.lean` bytes equal baseline and all its imported generated modules are also reusable) was tested against full fresh compilation and deliberate unsafe-reuse controls (`support/aeneas-restricted-reuse/results.json` SHA-256 `c1a7bd74f206b26adccfa0bd9fcda3bb503a0a9ae12782a27893665322dc6bb5`):

| Mutation vs baseline (`support/aeneas-restricted-reuse/source-base.rs`) | `Types.lean` / `Funs.lean` / `Fixture.lean` source bytes vs baseline | Guarded hybrid `.olean` reuse & Lean compile count | Full fresh vs guarded hybrid proof verification (`use_step 1`, `combine 1`, `untouched 1`) | Deliberate unsafe `.olean` reuse control |
| --- | --- | --- | --- | --- |
| Trait impl body `wrapping_add(1)` → `wrapping_add(2)` (`support/aeneas-restricted-reuse/source-body.rs`) | `Equal / Different / Equal` | Reused `Fixture.Types.olean`; compiled `Funs` and `Fixture` (2 compiles, `7.386 s` vs 3 compiles, `5.493 s` fresh) | Both proved `3, 14, 11` (vs baseline `2, 13, 11`) with axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. | Reusing baseline `Fixture.Funs.olean` failed updated `rfl` claims and introduced `sorryAx`. |
| Trait signature `step(self)` → `step(self, delta: u32)` (`support/aeneas-restricted-reuse/source-signature.rs`) | `Different / Different / Equal` | Reused **none** (`Fixture.lean` recompiled despite equal source text because imported `Funs` changed; 3 compiles, `18.216 s` vs `5.329 s` fresh) | Both proved `2, 13, 11` with no `sorryAx`. | Reusing baseline `Fixture.Types.olean` failed compiling new `Funs.lean` (2-argument impl vs 1-argument trait structure field). |

Basis: **execution** in `support/aeneas-restricted-reuse/results.json`.

### External Lean Model Changes Without Aeneas Codegen Changes (`support/external-model-without-codegen-change/`)

In `support/external-model-without-codegen-change/`, translating one LLBC containing `extern "C" external_double` before and after external-model edits produced **byte-identical** Aeneas files (`Types.lean`, `Funs.lean`, `FunsExternal_Template.lean`, and entry). Varying only the user-authored `Source/FunsExternal.lean` module across batch and live `lean --server` consumers demonstrated:

| `Source/FunsExternal.lean` state | Fresh batch build result | Proof of `external_call 1 = .ok 2` | `#print axioms external_call` | Stale-artifact / live `lean --server` worker negative control |
| --- | --- | --- | --- | --- |
| Concrete `external_double x = x + x` | All modules compile | Passes (`0`) | No axioms reported | Baseline state opened in `lean --server` + file worker. |
| Wrong concrete `external_double x = x + 2` | All modules compile | Fails (`1`) | Standard Lean axioms; no external axiom | Pairing wrong `x + 2` source with stale `x + x` `.olean` files made batch Lean exit `0` (false accept). Rebuilding `.olean` files to `x + 2` while `lean --server` stayed open left the live worker reporting 0 axioms and no proof error after a proof edit; a fresh `lean --server` rejected the proof. |
| `axiom external_double` | All modules compile | Fails (`1`) | Lists `external_double` | — |
| Missing `external_double` declaration | `Funs.lean` fails to compile | Not run | Unavailable | — |

Basis: **execution** in `support/external-model-without-codegen-change/results.json`.

### Provisional Last-Good Model Feedback and Signature-Changing Recovery (`support/last-good-model-after-rust-failure/`, `support/last-good-model-signature-recovery/`)

Two sequential state-machine probes exercised proof editing across broken intermediate Rust states and subsequent signature-changing recovery:

| Probe and revision state | Tool execution outcome | Stop-interaction policy | Explicit last-good / current-model freshness routing (`support/last-good-model-after-rust-failure/results.json`, `support/last-good-model-signature-recovery/results.json`) |
| --- | --- | --- | --- |
| Model `A`: `inc(x: u32) -> u32` (`x + 1`) | Charon `0`, Aeneas `0`; `Std.U32 → Result Std.U32`; proof v1 (`inc 0#u32 = .ok 1#u32`) exits `0` | Normal current feedback | `current_verified = true` under model `A` digest. |
| Broken revision `B` (syntax error appended to `x + 2` or `u64` edit) | Charon exits `2`; `current.llbc` on disk retains model `A` bytes | Suppresses Lean query (`current Rust model unavailable`) | Evaluates edited proof against retained model `A` (`Lean exit 0`), but labels envelope `provisional / stale` with `current_verified = false` and records both Rust `B` and model `A` hashes. |
| Broken revision `C` (valid syntax + unsupported raw-pointer dereference alongside `x + 2`) | Charon `0`, Aeneas exits `1` writing partial `Funs.lean` (`wrapping_add x 2#u32` + `sorry`) | Suppresses Lean query (`current Rust model unavailable`) | Rejects partial `C` output; evaluates proof v3 against retained model `A` (`Lean exit 0`) with `provisional / stale` and `current_verified = false`. |
| Recovery model `B`: valid `inc(x: u64) -> u64` (`x + 2`) | Charon `0`, Aeneas `0`; `Std.U64 → Result Std.U64` | Publishes model `B` as current | Ends provisional `A` feedback: old `U32` proof fails against `B` (`U32` vs `U64` type mismatch); adapted `U64` proof passes against `B` (`current_verified = true`); a late-arriving `exit 0` proof run against stale model `A` is rejected by model-identity comparison. |

Basis: **execution** in `support/last-good-model-after-rust-failure/results.json` and `support/last-good-model-signature-recovery/results.json`.

## Boundaries

- **Not examined:** Same-process OCaml Aeneas incremental translation APIs (the prototype in `support/aeneas-restricted-reuse/` still ran the whole-crate `aeneas` CLI to obtain generated `.lean` bytes before deciding `.olean` reuse, and its 2-module hybrid compile took `7.386 s` vs `5.493 s` for 3-module fresh compile on this tiny fixture).
- **Not examined:** Mutating Aeneas's compiled-in OCaml external-model registry or testing human/agent UI comprehension of `provisional / stale` badges.
- **Known not to apply:**
  - Generated Lean source digests alone do not fence against changes in imported user-authored external models (`FunsExternal.lean`) or stale in-memory `lean --server` file workers after on-disk `.olean` replacement.
  - Because `side.untouched` shares `Fixture.Funs` with `core.Step::step` under Aeneas's `-split-files` layout, unchanged functions in the same crate cannot be reused at `.olean` granularity when any function in `Funs.lean` changes.

## Evidence

- **Namespace-move, restricted-reuse, and trait/shrink/error matrix subprobes:**
  - `support/aeneas-namespace-move-proof-context/probe.py`, `support/aeneas-namespace-move-proof-context/check.py`, `support/aeneas-namespace-move-proof-context/raw-results.json`, and `support/aeneas-namespace-move-proof-context/work/`.
  - `support/aeneas-restricted-reuse/probe.py` (SHA-256 `5c0f5e6453c601881deded14b0f54122ac5e0613d27b2b9678a5a2e7e0055981`), `support/aeneas-restricted-reuse/check.py`, `support/aeneas-restricted-reuse/results.json` (SHA-256 `c1a7bd74f206b26adccfa0bd9fcda3bb503a0a9ae12782a27893665322dc6bb5`), `support/aeneas-restricted-reuse/source-base.rs`, `support/aeneas-restricted-reuse/source-body.rs`, `support/aeneas-restricted-reuse/source-signature.rs`, `support/aeneas-restricted-reuse/inputs/`, `support/aeneas-restricted-reuse/outputs/`, and `support/aeneas-restricted-reuse/work/`.
  - `support/aeneas-trait-output-shrink-matrix/probe.py` (SHA-256 `a0dfa2475bd3645a8068ce4740b900b42ed957ef28b819269cdd101856d8997b`), `support/aeneas-trait-output-shrink-matrix/check.py` (SHA-256 `34c689664d30556d8efe20b6a593c04cac401353983297ce754647362eb934ef`), `support/aeneas-trait-output-shrink-matrix/raw-results.json` (SHA-256 `d4891c9f4e990f817c4fceaeb2e7aaf316fdfd6d11cbb91e97266e804270d089`), `support/aeneas-trait-output-shrink-matrix/inputs/`, `support/aeneas-trait-output-shrink-matrix/outputs/`, and `support/aeneas-trait-output-shrink-matrix/work/`.
- **External-model and last-good-model recovery subprobes:**
  - `support/external-model-without-codegen-change/probe.py`, `support/external-model-without-codegen-change/check.py`, `support/external-model-without-codegen-change/results.json`, and `support/external-model-without-codegen-change/work/`.
  - `support/last-good-model-after-rust-failure/probe.py`, `support/last-good-model-after-rust-failure/check.py`, `support/last-good-model-after-rust-failure/results.json`, and `support/last-good-model-after-rust-failure/work/`.
  - `support/last-good-model-signature-recovery/probe.py`, `support/last-good-model-signature-recovery/check.py`, `support/last-good-model-signature-recovery/results.json`, and `support/last-good-model-signature-recovery/work/`.

## Revalidation

All six subprobes provide offline verification scripts that check every retained source/LLBC/Lean/.olean digest, import graph, negative control, and JSON-RPC server transcript without invoking Charon, Aeneas, or Lean:

```sh
python3 support/aeneas-namespace-move-proof-context/check.py
python3 support/aeneas-restricted-reuse/check.py
python3 support/aeneas-trait-output-shrink-matrix/check.py
python3 support/external-model-without-codegen-change/check.py
python3 support/last-good-model-after-rust-failure/check.py
python3 support/last-good-model-signature-recovery/check.py
```

To re-execute any subprobe on a host with the pinned binaries and cached `Aeneas.olean` runtime, run its `probe.py` followed by `check.py`.
