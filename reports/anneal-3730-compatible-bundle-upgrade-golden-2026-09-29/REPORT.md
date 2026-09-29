# Compatible Charon/Aeneas bundle upgrade: Rust → LLBC → Lean golden

Observed 2026-09-29 on an AArch64 macOS host. This report addresses the locally executable M03/M04 upgrade replay in issue #3730's follow-up scope and investigation I158 in #3731. It also inventories the available Lean/Lake pins for F03. The experiment uses cached binaries and source only; it does not run an Anneal generator or service.

## Question and decision

Can the *same* small Rust crate travel through two locally cached, internally compatible Rust/Charon/Aeneas bundles and produce Lean files that pass a fresh proof checker? In this fixture, **yes**. Both bundles passed four end-to-end cells (base and changed Rust source in each). For each Rust source, the emitted Lean files match byte for byte across bundles, while LLBC bytes differ. Both cross-pair Aeneas/LLBC combinations were correctly rejected because the Charon LLBC versions differ. This supports a paired-bundle upgrade test, not independent substitution of either tool.

## Pinned local subjects

| Bundle | Aeneas source commit | Bundled Charon source pin / LLBC | Rust toolchain | Aeneas executable SHA-256 | Charon executable SHA-256 |
| --- | --- | --- | --- | --- | --- |
| June 1 | `f95a80abaf554d4612cb60ef9ec8e849139bec44` | `42836b36b666a980cbc9d438a8aed340ad3b848b` / `0.1.208` | `nightly-2026-04-18-aarch64-apple-darwin` | `bfdb7610f994af03e0ad97ef640c7229880fc96a4a23cc4eda9a6b41c652bb22` | `6b53eb746f512191b8408cd9c1c71f674406232ffe3b44cbd50b777ae9e63ec6` |
| June 3 | `ac9f1bc5262a5e4ff1e24ca78617121382202727` | `a535e914f74db4fd9e6be7048f4233270d8945c0` / `0.1.210` | `nightly-2026-05-31-aarch64-apple-darwin` | `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03` | `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b` |

Both bundled Lean backends name `leanprover/lean4:v4.30.0-rc2`; each cached `Aeneas.olean` has SHA-256 `67701a9e8bf68cf0d51a01a4cb5648e2981c08d09402c4c4ac7bb8452d6263cb`. The checker executable has SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. [The local inventory](support/local-pin-inventory.json) records paths, file sizes, Rust/Cargo/driver hashes, both Lean/Lake pins, and the two additional unpaired Charon executables. The older Charon executable required `DYLD_LIBRARY_PATH` to point at its *already installed* April Rust toolchain libraries; no files were fetched or installed.

## Procedure

The [fixture crate](support/fixture) has `inc`, `twice`, and `choose` functions and one Rust test of selected values. The changed variant replaces `wrapping_add(1)` with `wrapping_add(2)`. For each bundle/variant, the [replay script](support/probe.py) creates an isolated crate and Cargo target, runs `cargo generate-lockfile --offline`, invokes that bundle's Charon with `--preset aeneas` and locked offline Cargo, invokes its Aeneas with the Lean split-file backend, and runs the Rust behavior test. The target is deleted after its byte size is recorded.

The script then compiles generated `Types.lean`, `Funs.lean`, and `Current.lean` into a fresh private consumer root using Lean 4.30.0-rc2 and that bundle's cached Aeneas Lean backend. It checks three explicit theorems (`obl_inc`, `obl_twice`, `obl_choose`) with `lean --json` and records `#print axioms` output. The proof claims the selected results at zero; these are deliberately narrow obligations, not a semantic theorem for every input. All 52 command records, raw stdout/stderr, source/LLBC/Lean/olean hashes, and output files are retained in [results.json](support/results.json) and [work](support/work). [The offline checker](support/check.py) validates the retained files and writes [summary.json](support/summary.json).

## Results

| Cell | Rust selected values | Rust source SHA-256 | LLBC SHA-256 | Generated `Funs.lean` SHA-256 | Fresh Lean proof |
| --- | --- | --- | --- | --- | --- |
| June 1, base | `(1, 2, 3)` | `c571b242f56aea2c…` | `d821b046d03f6ff5…` | `9d85e4b057d5e995…` | Exit 0; 3 obligations |
| June 1, changed | `(2, 4, 5)` | `dbc00097eb89527e…` | `eb710760439c8ba2…` | `ecc34d8ba16ff2f2…` | Exit 0; 3 obligations |
| June 3, base | `(1, 2, 3)` | `c571b242f56aea2c…` | `7c7643ea2b4dbf61…` | `9d85e4b057d5e995…` | Exit 0; 3 obligations |
| June 3, changed | `(2, 4, 5)` | `dbc00097eb89527e…` | `5e51de06bcc0eeb1…` | `ecc34d8ba16ff2f2…` | Exit 0; 3 obligations |

The other generated files also match across bundles at each source state: `Types.lean` is 530 bytes with SHA-256 `4af6239d04ae98fa8cad6d1930e0d91fefa2a037635e9989cb671464e33e0a13`, and `Current.lean` is 20 bytes with SHA-256 `c62893d039c7c93787bb4c819c5fa40e6edef71cd0c3f9be5ff843df7616f49e`. The source edit changes `Funs.lean` in both bundles. Every Rust behavior test passes. Each Lean proof reports only the expected axioms `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The controls delimit what a green batch check means:

| Control | Observation | Consequence |
| --- | --- | --- |
| False result `99#u32` proved by `rfl` | Lean exit 1 in all four cells | Checker catches this incorrect selected claim. |
| File with only `obl_inc` | Lean exit 0 in all four cells | Success alone cannot prove the obligation set is complete; the manifest must enumerate expected theorems. |
| False result admitted with `sorry` | Lean exit 0 and `sorryAx` in all four cells | Success alone cannot prove admission-free proof; audit axioms. |
| Base generated import checked after the Rust source changes | Lean exit 0 for both bundles, despite different Rust source hashes | An external source-to-artifact identity gate is required; batch Lean cannot detect stale generation by itself. |
| June 1 Aeneas on June 3 LLBC, and reverse | Both exit 1, explicitly rejecting LLBC `0.1.208` versus `0.1.210` | Upgrade Charon and Aeneas as compatible pairs. |

The default Aeneas execution option, run twice on the base LLBC for each bundle, produced the same file hashes as the corresponding `-sequential` run. This is one tiny deterministic fixture; it does **not** justify removing `-sequential` as a general concurrency workaround. The cross-pair version rejection is direct evidence that the two releases cannot be used for a controlled *Aeneas-only* binary swap on one LLBC.

## F03 availability and residual

The known local Lean/Lake pins are 4.29.0 and 4.30.0-rc2; the available Nix Lean is the same 4.30.0-rc2 binary. No later-than-4.30 pin was present in the inspected cache, so the requested 4.30-versus-later Lake ownership cell cannot run without an additional toolchain. The existing `anneal-3730-lean-cross-version-equivalence-v4-29-v4-30-rc2-2026-09-29` package covers the locally available 4.29/4.30.0-rc2 submatrix; this report does not repeat it.

M03/M04 are satisfied only for this small, manually assembled paired-tool fixture. Residual I158 scope includes other Rust constructs, realistic crates, Anneal's generated workspace and manifests, external artifact/reference consumers, independent machine or architecture replay, and further compatible releases. The four results establish fresh selected Lean acceptance and byte-level equality for these two cached pairs, not general translation soundness or an upgrade compatibility promise.

## Reproduction and validation

From the repository root, with the listed local pins still present:

```sh
python3 reports/anneal-3730-compatible-bundle-upgrade-golden-2026-09-29/support/inventory.py
python3 reports/anneal-3730-compatible-bundle-upgrade-golden-2026-09-29/support/probe.py
python3 reports/anneal-3730-compatible-bundle-upgrade-golden-2026-09-29/support/check.py
```

The full probe uses only cached programs and its own `support/work` tree, preflights for more than 15 GiB of free disk, keeps Cargo to one build job, and removes each temporary target. The offline checker is sufficient to audit the retained run without executing the toolchain again. It passed for the retained four cases, 52 commands, six expected nonzero controls, and two explicit cross-pair rejections.
