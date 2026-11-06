# Batch and Live Acceptance Oracles, Claim-Relative Import Taint, and Vertical Model-Transition Slices

## Summary

Across ten experimental packages spanning standalone Lean comparators, claim-relative import-taint fixtures, shared batch/live projection sinks, full Cargo→Charon→Aeneas→Lean golden verticals, paired-bundle upgrade matrices, and causally gated model-transition schedules, sound proof acceptance requires six orthogonal verification dimensions that cannot be collapsed into `lean --json` exit `0` or an interactive `no goals` reply:
1. **Expected-proposition and obligation-set completeness**: Weakening a theorem statement (`claim : True`) or omitting a required obligation (`obl_choose`) still compiles with Lean exit `0` and reports no extra axioms; only a fixed expected-proposition consumer and an explicit obligation-manifest gate reject them (`support/acceptance-oracle-matrix/`, `support/cross-layer-comparator-mutants/`, `support/rust-charon-aeneas-lean-golden-vertical/`).
2. **Claim-relative axiom and admission taint across compiled imports**: Admitted theorems (`sorryAx`), custom axioms (`cheat`, `model`, `external_double`), and downstream callers importing a stale axiom-backed `.olean` all exit `0` and satisfy type-level proposition checks. In `support/claim-relative-import-taint/`, editing `Dep.lean` from an axiom proof to a concrete `decide` proof without rebuilding `Dep.olean` left the downstream `caller` theorem tainted with `[model]` while a sibling `independent` theorem in the same module remained untainted.
3. **Complete transitive model-artifact identity**: In `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/`, mutating a Rust function from `wrapping_add(1)` to `wrapping_add(2)` changed Aeneas's `Current/Funs.olean` (`2320c012...` → `57bcadab...`) while leaving the top-level entry module `Current.olean` (`34547467...`) byte-identical—proving that an acceptance oracle must bind the full transitive module manifest rather than the root `.olean` alone.
4. **Shared generator plan across materialized file and live LSP sinks**: In `support/shared-generator-batch-live-sinks/`, driving a file sink and an in-memory `lean --server` stream (`didOpen` + two `didChange` steps to document version `3` before any disk file existed) from one deterministic `Plan` yielded byte-identical Lean source, identical coordinate maps, and matching batch/live diagnostics and elaborated declaration types across complete, incomplete (`skip`), import-mutated, and CRLF+Unicode specimens.
5. **Paired Charon/Aeneas bundle upgrades and narrow LLBC normalization**: In `support/compatible-bundle-upgrade-golden/`, both the June 1 (`Charon 0.1.208` + `Aeneas f95a80ab`) and June 3 (`Charon 0.1.210` + `Aeneas ac9f1bc5`) bundles produced byte-identical `Types.lean`, `Funs.lean`, and `Current.lean` outputs for base and mutated Rust crates while rejecting cross-bundle LLBC inputs (`0.1.208` vs `0.1.210`). Across cold, prepared, and clean directories (`support/rust-charon-aeneas-lean-golden-vertical/`), raw LLBC digests differed only in `translated.options.dest_file` and `translated.short_names` ordering.
6. **Causal revision fencing across failed intermediate and late completions**: Across `support/vertical-acceptance-v4-30-0-rc2/`, its independent driver reproduction (`support/independent-vertical-reproduction/`, matching `33/33` exact fields), and the real Charon/Aeneas model-transition schedule (`support/embedded-proof-generated-model-vertical-v4-30-0-rc2/`), an invalid intermediate generation (`F`) leaves the prior generation (`A`) labeled *last-known-good and stale for the current host*, and an in-flight `A` verification blocked at a `run_tac` file gate until after `B` is published is deterministically rejected by a monotonic revision fence.

## Applicability

All experiments ran offline on macOS arm64 (`26.6.2` / Darwin `25.6.0`) with CPython `3.14.7` and `LEAN_NUM_THREADS=1` against the pinned subjects in `REPORT.json`:
- **Lean 4 and Lake (multi-version inventory and shared behavior vs. version deltas)**:
  - `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) is the primary execution target across all ten subprobes and matches the prebuilt `Aeneas.olean` library (`67701a9e8bf68cf0d51a01a4cb5648e2981c08d09402c4c4ac7bb8452d6263cb`).
  - `leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740` (`v4.29.0`, `lean` SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`, `lake` SHA-256 `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b`) is cataloged in `support/compatible-bundle-upgrade-golden/local-pin-inventory.json`. **Shared behavior vs. version delta**: both `v4.29.0` and `v4.30.0-rc2` are cached locally, whereas only `v4.30.0-rc2` is binary-compatible with the prebuilt `Aeneas.olean` (`v4.30.0-rc2` header) used in the Charon/Aeneas golden verticals; no post-`4.30` (`4.31+`) Lean/Lake toolchain was present in the local cache to test later Lake workspace-ownership changes.
- **Charon and Aeneas (multi-version bundle comparison)**:
  - Primary June 3 bundle: `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (`0.1.210`, binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`, Aeneas-pinned source revision `a535e914f74db4fd9e6be7048f4233270d8945c0`) and `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`, binary SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`).
  - Comparison June 1 bundle (`support/compatible-bundle-upgrade-golden/`): Charon source pin `42836b36b666a980cbc9d438a8aed340ad3b848b` (LLBC version `0.1.208`, binary SHA-256 `6b53eb746f512191b8408cd9c1c71f674406232ffe3b44cbd50b777ae9e63ec6`) and Aeneas `f95a80abaf554d4612cb60ef9ec8e849139bec44` (binary SHA-256 `bfdb7610f994af03e0ad97ef640c7229880fc96a4a23cc4eda9a6b41c652bb22`). **Shared behavior vs. version delta**: both bundles emit byte-identical generated Lean (`Types.lean`, `Funs.lean`, `Current.lean`) and pass identical Lean proof checks, but emit incompatible LLBC schema versions (`0.1.208` vs `0.1.210`) that each other's Aeneas binaries strictly reject (exit `1`).
- **Rust compilers and Cargo (multi-version coverage)**:
  - `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`nightly`, SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) and `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` (`nightly`, SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`) drive the June 3 Charon `0.1.210` pipeline (`nightly` drives the June 1 Charon `0.1.208` binary).
  - `rust-lang/rust@48a229ceaefd4985c50990b14116b6d856af0985` (`1.98.1`, SHA-256 `2814fb55fb9cfb3eef5848a8104d77e3de7fd95394661144a12ee90cd4405340`) compiles the standalone Rust host and view in `support/generated-lean-canonical-source-challenge/`.
- **Anneal workspace**: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`.

## Findings

### Standalone Acceptance Oracle Matrix and Falsification of Simple Predicates

In `support/acceptance-oracle-matrix/probe.py` (`support/acceptance-oracle-matrix/transcript-run1.json`, `support/acceptance-oracle-matrix/transcript-run2.json`, `support/acceptance-oracle-matrix/acceptance-cases.csv`), seven disposable Lean fixtures were tested against a fixed consumer (`example : modelValue = 4 := claim` and `#print axioms claim`):

| Fixture | Proof source | Fixed consumer | Axiom report | What a simpler green predicate misses |
| --- | ---: | ---: | --- | --- |
| Good, model `4` | exit `0` | exit `0` | none | Baseline Lean-level accepted claim. |
| Weak `claim : True` | exit `0` | exit `1` | none | Compiler success does not preserve the intended proposition. |
| Admitted claim (`by sorry`) | exit `0` | exit `0` | `sorryAx` | Type acceptance does not satisfy a no-admission policy. |
| New `cheat` axiom | exit `0` | exit `0` | `cheat` | A matching type can rely on a newly introduced axiom. |
| Wrong imported model `5` | exit `1` | not run | unavailable | Same proof bytes under a different imported artifact can fail. |
| Missing second claim (`missingClaim`) | exit `0` | exit `1` | no axioms for first claim | One accepted theorem does not cover a required second obligation. |
| Instruction-shaped comment | exit `0` | exit `0` | none | The comment is source data; compiler acceptance gives it no task authority. |

- **Fresh re-elaboration vs. live LSP**: Copying the good proof (`43e0059e223d61b85eff2a2aac8247c21dd370b681898b982a93eb7d106d1df7`) and `Generated.olean` (`9ed8713387b59eaf45c0f261cb92ed8ad4663c86301973e57e73ea73f1441a38`) into a clean `fresh/` directory passed three fresh Lean processes (`lean --json Proof.lean`, `Proof.olean` emission, and fixed-consumer check). At the same URI, `lean --server` opened unsaved `exact ?_` bytes (`55e336d1cf04145d4d263a6429238dcfb1c835c4ed3794fff019fc5ab41b2a84`), reported `⊢ modelValue = 4` after `waitForDiagnostics(1)`, and reported `no goals` after a version-2 `didChange` to the good proof.
- **Interrupted verification and side-effect controls**: Killing `InterruptedOracle.lean` with `SIGKILL` (exit `-9`) after a file gate inside elaboration left the verification status **interrupted/unknown** despite the local proof goal being solved. A benign `run_tac` in `SideEffect.lean` wrote `TACTIC_EXECUTED` during `lean --json` (exit `0`), demonstrating that tactic execution occurs during batch checking. A synthetic redaction check replaced temporary paths with `$WORK` and fake tokens with `[synthetic-secret]`.

### Claim-Relative Axiom and Admission Taint Through Reused `.olean` Imports

In `support/claim-relative-import-taint/probe.py` (`support/claim-relative-import-taint/results.json`, `support/claim-relative-import-taint/check.py`), an isolated `Dep.lean` (`depValue : Nat := 7` and `base : depValue = 7`) was compiled in `axiom`, `concrete` (`decide`), and `admitted` (`sorry`) variants while a byte-identical `Proof.lean` proved `caller : depValue = 7 := base` and `independent : True := trivial`:

| Imported source and artifact | `caller` `#print axioms` output | `independent` `#print axioms` output |
| --- | --- | --- |
| Axiom source and axiom `Dep.olean` | `depends on axioms: [model]` | `does not depend on any axioms` |
| Concrete source (`decide`) but retained axiom `Dep.olean` | `depends on axioms: [model]` | `does not depend on any axioms` |
| Concrete source and rebuilt concrete `Dep.olean` | `does not depend on any axioms` | `does not depend on any axioms` |
| Admitted source (`sorry`) and rebuilt admitted `Dep.olean` | `depends on axioms: [sorryAx]` | `does not depend on any axioms` |

All four consumer runs exited `0`, proving that taint is claim-relative within a module and governed by the *consumed `.olean` artifact* rather than current source files on disk.

### Shared Generator Plan Across File and Live LSP Sinks

In `support/shared-generator-batch-live-sinks/probe.py` (`support/shared-generator-batch-live-sinks/results.json`, `support/shared-generator-batch-live-sinks/check.py`, `support/shared-generator-batch-live-sinks/artifacts/`), one typed `construct` function produced a deterministic `Plan` (header, annotation, footer, and UTF-8/UTF-16 boundary map) consumed by both a disk file sink and a live `lean --server` stream (`didOpen` + two `didChange` notifications reaching version `3` before disk persistence):

| Case | Import OLean | Generated SHA-256 | Both batch exits | Final batch/live declaration, error, axiom result |
| --- | --- | --- | ---: | --- |
| Complete proof | `Base` (`0d7cc920...`), value `7` | `85a39246572e2afdf59db30674f3272516b82b10fe4a3532ce66a244909aecaa` | `0` | `Generated.checked : depValue = 7`; no error; no axioms |
| Incomplete `skip` proof | `Base` (`0d7cc920...`), value `7` | `0ff077cc11fa4da10f3cd5be6965e6a75604711c126cb4d737160817114fca3e` | `1` | Same declared type; `unsolved goals`; `sorryAx` |
| Import edit | `Alt` (`f524eb22...`), value `9` | `f8088463eb04e121684b6e178c4db4a531c2fece73026f4a0189d43d4b31f73b` | `1` | Same declared type; `decide` finds proposition false; `sorryAx` |
| Unicode (`λ`, `😀`) and CRLF annotation | `Base` (`0d7cc920...`), value `7` | `562a988a9b4d68353699a998ca05e703f4088f5a046fbcdfae32a11147918e5a` | `0` | Same declared type; no error; no axioms (map advances emoji by `2` UTF-16 code units) |

### Full Cargo → Charon → Aeneas → Lean Golden Verticals, Comparator Mutants, and Bundle Upgrades

In `support/rust-charon-aeneas-lean-golden-vertical/probe.py` (`support/rust-charon-aeneas-lean-golden-vertical/results.json`), `support/cross-layer-comparator-mutants/probe.py` (`support/cross-layer-comparator-mutants/results.json`, `support/cross-layer-comparator-mutants/comparison-manifest.json`), and `support/compatible-bundle-upgrade-golden/probe.py` (`support/compatible-bundle-upgrade-golden/results.json`, `support/compatible-bundle-upgrade-golden/summary.json`), a three-function crate (`inc`, `twice`, `choose`) was verified end-to-end:

| Golden Vertical Case (`support/rust-charon-aeneas-lean-golden-vertical/`) | Captured Rust source SHA-256 prefix | LLBC SHA-256 prefix | Generated `Funs.lean` prefix | Selected Rust/Lean values |
| --- | --- | --- | --- | --- |
| Base cold | `4d39ee7a9118684c` | `7032ef983ec41624` | `e671fd230e9f048c` | `1, 2, 3` |
| Base prepared target | `4d39ee7a9118684c` | `b52420c828c10810` | `e671fd230e9f048c` | `1, 2, 3` |
| Base separate clean target | `4d39ee7a9118684c` | `d046ca6d94e1c980` | `e671fd230e9f048c` | `1, 2, 3` |
| Changed source (`wrapping_add(2)`), clean target | `e1d8e8151a057cdb` | `f26a590b0ad5f335` | `f45d572ab60869ad` | `2, 4, 5` |

| Comparator Mutant Case (`support/cross-layer-comparator-mutants/`) | Rust source SHA-256 prefix | LLBC prefix | Generated `Funs.lean` prefix | Compiled `Funs.olean` prefix | Selected Rust/Lean result |
| --- | --- | --- | --- | --- | --- |
| Base | `1e7af22d8ddc414b` | `ee36614785a52956` | `bc15e6198147e105` | `741d164fc7a832cb` | `1/2/3` |
| Reordered declarations (`choose`, `twice`, `inc`) | `5c47f32fcd6df506` | `734568088d01882d` | `61de570b374752a4` | `96645d3c18c93b48` | `1/2/3` |
| Changed addition (`wrapping_add(2)`) | `fc47ac0e8cb34679` | `ec7d0f808f778c29` | `287273a09e0f2cc0` | `92ca23323f42b72d` | `2/4/5` |
| Separate clean base rerun | `1e7af22d8ddc414b` | `aafae3a3fd8885c8` | `e2c59d8fd0ede7ab` | `20097a83eda4600f` | `1/2/3` |

| Compatible Bundle Cell (`support/compatible-bundle-upgrade-golden/`) | Rust selected values | Rust source SHA-256 | LLBC SHA-256 | Generated `Funs.lean` SHA-256 | Fresh Lean proof |
| --- | --- | --- | --- | --- | --- |
| June 1 (`0.1.208` / `f95a80ab`), base | `(1, 2, 3)` | `c571b242f56aea2c…` | `d821b046d03f6ff5…` | `9d85e4b057d5e995…` | Exit `0`; `3` obligations |
| June 1 (`0.1.208` / `f95a80ab`), changed | `(2, 4, 5)` | `dbc00097eb89527e…` | `eb710760439c8ba2…` | `ecc34d8ba16ff2f2…` | Exit `0`; `3` obligations |
| June 3 (`0.1.210` / `ac9f1bc5`), base | `(1, 2, 3)` | `c571b242f56aea2c…` | `7c7643ea2b4dbf61…` | `9d85e4b057d5e995…` | Exit `0`; `3` obligations |
| June 3 (`0.1.210` / `ac9f1bc5`), changed | `(2, 4, 5)` | `dbc00097eb89527e…` | `5e51de06bcc0eeb1…` | `ecc34d8ba16ff2f2…` | Exit `0`; `3` obligations |

In `support/compatible-bundle-upgrade-golden/`, `Types.lean` (`530` bytes, SHA-256 `4af6239d04ae98fa8cad6d1930e0d91fefa2a037635e9989cb671464e33e0a13`) and `Current.lean` (`20` bytes, SHA-256 `c62893d039c7c93787bb4c819c5fa40e6edef71cd0c3f9be5ff843df7616f49e`) were also byte-identical across both bundles, and every accepted theorem reported only `[propext, Classical.choice, Quot.sound]` without `sorryAx`. In `support/cross-layer-comparator-mutants/`, replacing an external function's Aeneas axiom template with a concrete user-authored Lean model changed `Source.Funs.olean` and removed `[external_double]` from `#print axioms comparator_probe.call`, demonstrating that external model source and `.olean` hashes must be tracked in the trust account.

### Generated Lean as Canonical Proof Source Challenge

In `support/generated-lean-canonical-source-challenge/probe.py` (`support/generated-lean-canonical-source-challenge/results.json`, `support/generated-lean-canonical-source-challenge/check.py`), a falsification experiment tested treating `Proof.lean` as the canonical user-editable proof source while `HostView.rs` embeds it as `//| ` comments via a proof-hash compare-and-swap guard:

| State / change | `Proof.lean` SHA-256 | `Model.lean` / `Model.olean` SHA-256 | Fresh Lean result | Authority observation |
| --- | --- | --- | --- | --- |
| Initial (`model_add(x) = x + 1`) | `38a52f636d36…` | `7d81f6be6037…` / `0e1b64ef7ecd…` | Exit `0` | Initial view parsed back to identical proof bytes; `rustc 1.98.1` compiled host. |
| Hosted UTF-16 comment edit `β` → `λ` after `🦀` | `ee3449eff1a1…` | Unchanged | Exit `0` | View range `[23,24)` UTF-16 mapped to proof range `[19,20)` and byte range `[35,37)`. |
| Hosted tactic edit `rfl` → `decide` | `28297317adf4…` | Unchanged | Exit `0` | Mapped proof file updated; regenerated view round-tripped exactly. |
| Direct canonical proof edit back to `rfl` | `ee3449eff1a1…` | Unchanged | Exit `0` | Regenerated view followed `Proof.lean`; stale-hash and scaffold edits rejected without mutating proof bytes. |
| Hosted claim edit `2` → `3` | `0f9dcdadf294…` | Unchanged | Exit `1` | Lean `rfl` failure at proof line `5`, col `2` mapped to 0-based hosted view line `8`, col `6`. |
| Hosted repair `3` → `2` | `ee3449eff1a1…` | Unchanged | Exit `0` | Proof repair restored acceptance. |
| Rust function edit `x + 1` → `x + 2` | `ee3449eff1a1…` (unchanged) | `fbaf2918d21c…` / `dc815811a2eb…` | Exit `1` | Unchanged proof failed against new model import; diagnostic pointed to proof tactic while model hashes identified the upstream cause. |
| Restore Rust and regenerate after tampering `Model.lean` (`x + 99`) | `ee3449eff1a1…` | Restored to `7d81f6be6037…` / `0e1b64ef7ecd…` | Exit `0` | Derivative model tamper overwritten from `RustSource.rs`; canonical proof preserved. |

### Vertical Acceptance Slices, Independent Reproduction, and Real Model-Change Schedules

In `support/vertical-acceptance-v4-30-0-rc2/run.py` (`transcript-run1.json`, `transcript-run2.json`, `transcript-run3.json`) and its independent second-worker reproduction `support/independent-vertical-reproduction/reproduce.py` (`reproduction-run1.json`, `reproduction-run2.json`, `compare.py`, `comparison.json`), a prototype drove both `lean --server` and fresh batch checks across model generation `A` (`modelValue = 3`), invalid generation `F` (`def modelValue : Nat :=`), and generation `B` (`modelValue = 4`), plus a causally gated `A-late` build:

| Captured case | Lean proof batch | Fixed expected-proposition consumer | Axiom query | Live goal where queried | Classification in fixture |
| --- | --- | --- | --- | --- | --- |
| `A` final, model `3`, claim `modelValue = 3` | exit `0` | exit `0` | no axioms reported | `⊢ modelValue = 3` (v1) → `no goals` (v2) | Lean-level claim accepted for `A` |
| `B` final, model `4`, claim `modelValue = 4` | exit `0` | exit `0` | no axioms reported | `no goals` | Lean-level claim accepted for `B` |
| `A` proof against `B` model | exit `1` (`rfl` mismatch) | not compiled | unavailable | `⊢ modelValue = 3` | Stale proof rejected |
| Weak `B` theorem `claim : True` | exit `0` | exit `1` (type mismatch) | no axioms reported | not queried | Compilation does not preserve intended statement |
| Admitted `B` theorem (`by sorry`) | exit `0` | exit `0` | `sorryAx` reported | not queried | Type matches, trust condition fails |
| `F` invalid generated module | module exit `1` | unavailable | unavailable | not queried | Preparation failed; `A` retained only as last-known-good |
| Late `A` output released after `B` published | exit `0` under `A` | exit `0` under `A` | no axioms reported | not queried | Valid old output, rejected from current pointer (revision `1 < 3`) |

`support/independent-vertical-reproduction/compare.py` verified **33/33 expected-exact fields equal** between the independent driver and `support/vertical-acceptance-v4-30-0-rc2/transcript-run3.json` (including identical `Generated.olean` hashes `9dd4d2a1c8cf7d909299d4bb92a45f8ff3f7c4593f8913b64eafa1eed800b4e5` and `9ed8713387b59eaf45c0f261cb92ed8ad4663c86301973e57e73f1441a38`, and identical `Proof.olean` hashes `24ff1eadf3b0456611ff00202c150f89980e801b5832d65fcf12f14bb39519e0` and `ba08ca066322195e2b2271b4c4eae8249a84eabdb18ea912ba210d98da8ff41b`), while documenting four expected source-layout hash differences where the independent driver placed the `run_tac` gate in `Proof.lean` (`aaa2040b…` vs `a1278057…`) rather than `Generated.lean` (`de1854df…` vs `fc40104c…`) and varied whitespace in the weak (`f72a7e7c…` vs `e9de96e0…`) and admitted (`56678542…` vs `96b39d63…`) control sources.

Finally, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/` (`probe.py`, `mutate_model.py`, `full_model_change.py`, `check.py`) connected an unsaved Rust-comment proof edit (`exact ?_` → `rfl` mapping projected bytes `[79,87)` to host bytes `[397,405)`, host SHA-256 `78331288...` → `64a14e2d...`, projected SHA-256 `d7741e8c...` → `1b0f94d5...`, compiled `Captured.olean` `29979cc2...`) to a real Charon/Aeneas generated model (`model-manifest.json` generation ID `b58c86ab...`), and then executed the full causal transition schedule (`old gate entered → F Charon exit 101 failed and old server queried as stale → B Charon complete, Aeneas gated and old server queried as stale → B model completed/selected [generation ID 6ce1f7d8...] and queried → old gate released/completed → old revision-1 publication rejected`).

## Boundaries

- **Not examined**: Production Anneal CLI/LSP/MCP integration, independent proof-kernel rechecking outside the pinned Lean `v4.30.0-rc2` binary, transitive rebuilds of `Aeneas.olean` from source during interactive sessions, OS-level sandboxing of untrusted Cargo `build.rs` / proc-macro / Lake configuration / Lean `run_tac` callbacks, or human comprehension studies of stale-model UI banners.
- **Unknown**: Whether post-`4.30` Lean/Lake releases (`4.31+`) alter workspace-ownership invariants under this consumer matrix (no post-`4.30` compatible Aeneas bundle was cached locally).
- **Known not to apply**: Local `no goals` LSP responses, batch `lean --json` exit `0`, or top-level entry `.olean` equality (`Current.olean` remaining `34547467...` while `Current/Funs.olean` changes) do not suffice as acceptance criteria; accepted `A` proofs do not apply to current host source during an invalid intermediate generation `F` or after generation `B` is published.

## Evidence

- **Acceptance oracle and claim-relative taint**:
  - `support/acceptance-oracle-matrix/probe.py` (SHA-256 `74b6ef237386a50b811733ddaae1168509767f36196ff88b8180d281ee47684d`), `support/acceptance-oracle-matrix/transcript-run1.json` (SHA-256 `0740ae23f16c9e285fdb9bb16277c58d814f7149e2e3216c888bab95b9e3a846`), `support/acceptance-oracle-matrix/transcript-run2.json` (SHA-256 `b695401385075d4171e163056d671ca265bbbfadb864f74391b5d866e0421aa0`), and `support/acceptance-oracle-matrix/acceptance-cases.csv` (SHA-256 `8112c56aa4cab9ca7c17723220c2cefaf17d297f4eb0f93341fa47c5d69dcaa9`).
  - `support/claim-relative-import-taint/probe.py` (SHA-256 `025d2027c85a7c144738bc8d67de9ed97392717fe076706bd6e3712ba5fa42ca`), `support/claim-relative-import-taint/results.json` (SHA-256 `7359ba6bdb0080698605ce1fc921cbce9f05e8700c102b31f37dfd28e5ec5f42`), and `support/claim-relative-import-taint/check.py`.
- **Golden verticals, comparator mutants, and bundle upgrades**:
  - `support/compatible-bundle-upgrade-golden/inventory.py`, `support/compatible-bundle-upgrade-golden/local-pin-inventory.json`, `support/compatible-bundle-upgrade-golden/probe.py`, `support/compatible-bundle-upgrade-golden/check.py`, `support/compatible-bundle-upgrade-golden/results.json`, `support/compatible-bundle-upgrade-golden/summary.json`, `support/compatible-bundle-upgrade-golden/fixture/`, and `support/compatible-bundle-upgrade-golden/work/`.
  - `support/cross-layer-comparator-mutants/probe.py`, `support/cross-layer-comparator-mutants/build_manifest.py`, `support/cross-layer-comparator-mutants/check.py`, `support/cross-layer-comparator-mutants/results.json`, `support/cross-layer-comparator-mutants/comparison-manifest.json`, and `support/cross-layer-comparator-mutants/work/`.
  - `support/rust-charon-aeneas-lean-golden-vertical/probe.py`, `support/rust-charon-aeneas-lean-golden-vertical/results.json`, and `support/rust-charon-aeneas-lean-golden-vertical/work/`.
- **Shared generator sinks, canonical-source challenge, and vertical slices**:
  - `support/shared-generator-batch-live-sinks/probe.py`, `support/shared-generator-batch-live-sinks/check.py`, `support/shared-generator-batch-live-sinks/results.json`, and `support/shared-generator-batch-live-sinks/artifacts/`.
  - `support/generated-lean-canonical-source-challenge/probe.py`, `support/generated-lean-canonical-source-challenge/check.py`, `support/generated-lean-canonical-source-challenge/results.json`, and `support/generated-lean-canonical-source-challenge/artifacts/`.
  - `support/vertical-acceptance-v4-30-0-rc2/run.py`, `support/vertical-acceptance-v4-30-0-rc2/transcript-run1.json`, `support/vertical-acceptance-v4-30-0-rc2/transcript-run2.json`, `support/vertical-acceptance-v4-30-0-rc2/transcript-run3.json` (SHA-256 `55e0dfc1083ee7d1a5ee5f71f9517a0018f2d4db81148a2843da4d97fd03bf80`), `support/vertical-acceptance-v4-30-0-rc2/transcript.json`, and `support/vertical-acceptance-v4-30-0-rc2/work/`.
  - `support/independent-vertical-reproduction/reproduce.py` (SHA-256 `80ba94089321454a35443a8d469870d4820ebb952f4a019f3a1d0609c99a29fa`), `support/independent-vertical-reproduction/reproduction-run1.json` (SHA-256 `4fb59f5002108823774acda77288593b6c603406cf1a7e3ae0af1d376541e6c0`), `support/independent-vertical-reproduction/reproduction-run2.json` (SHA-256 `0b8f70e8cd6d15194a338917e75e6b9c838b4b733bb214f517fff3ddb3534991`), `support/independent-vertical-reproduction/compare.py` (SHA-256 `8087416a9167908f18c79d8e9872a5d300f3506960f7fdf33380ce7bd58227e5`), and `support/independent-vertical-reproduction/comparison.json` (SHA-256 `9da6b7f2704df27ff566eccf737ce1fd20c6e7f8805f78ed4a35d8766cf679ad`).
  - `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/probe.py`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/mutate_model.py`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/full_model_change.py`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/check.py`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/transcript.json`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/mutation-transcript.json`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/full-model-change-transcript.json`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/model-manifest.json`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/new-model-manifest.json`, `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/model/`, and `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/new-model/`.

## Revalidation

Run the offline checkers to verify all retained transcripts, artifact digests, comparator rejections, and causal ordering invariants without re-invoking toolchains:
```sh
python3 support/claim-relative-import-taint/check.py
python3 support/compatible-bundle-upgrade-golden/check.py
python3 support/cross-layer-comparator-mutants/check.py
python3 support/generated-lean-canonical-source-challenge/check.py
python3 support/shared-generator-batch-live-sinks/check.py
python3 support/embedded-proof-generated-model-vertical-v4-30-0-rc2/check.py
```
To re-run live acquisition against the pinned Lean, Rust, Cargo, Charon, and Aeneas binaries in a disposable copy of the package, execute `support/acceptance-oracle-matrix/probe.py`, `support/claim-relative-import-taint/probe.py`, `support/compatible-bundle-upgrade-golden/probe.py`, `support/cross-layer-comparator-mutants/probe.py`, `support/generated-lean-canonical-source-challenge/probe.py`, `support/rust-charon-aeneas-lean-golden-vertical/probe.py`, `support/shared-generator-batch-live-sinks/probe.py`, `support/vertical-acceptance-v4-30-0-rc2/run.py`, `support/independent-vertical-reproduction/reproduce.py`, and `support/embedded-proof-generated-model-vertical-v4-30-0-rc2/full_model_change.py`, then re-run the offline checkers.
