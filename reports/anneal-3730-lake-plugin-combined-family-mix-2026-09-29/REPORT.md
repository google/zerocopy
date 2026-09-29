# Lake-discovered plugin, setup, and OLean family mix

## Result

On pinned Lean/Lake 4.30.0-rc2, a two-package fixture built two valid generations of an imported `Dep` module and native plugin. A third, disposable root mixed **v1 source, v1 OLean, v1 ILean and proof** with **v2 plugin dylib, v2 generated C file and v2 consumer Lake setup option**. A fresh `lake serve` session completed the proof, published `#eval selected` = 7, and ran the v2 plugin initializer (`plugin-v2` marker). `lake setup-file Proof.lean` named the mixed root's exact `Dep.olean` and plugin dylib paths and returned `"pp.universes": true`; archived hashes show those files remained unchanged before setup, after setup, and after the server. A direct `lake env lean Proof.lean` batch check returned 7 and exit 0.

The clean v1 and v2 controls each behaved as expected: v1 returned 7 with `plugin-v1`; v2 returned 9 with `plugin-v2`. Thus this **selected combination of individually valid, same-pinned-toolchain artifacts** was accepted, and the result exposes separate imported-module and plugin initializer identities. It does **not** establish that arbitrary cross-generation mixes are safe, that v2 generated C bytes were consumed by the server, or that the native ABI is generally compatible. The C file was present as a valid mixed family specimen; the dylib is the native artifact actually passed through Lake setup. There was no Anneal archive or Anneal-generated workspace.

## Reproduction and retained evidence

`support/probe.py` creates only private roots in `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r21-work`, pins `leanprover/lean4:v4.30.0-rc2`, disables Lake artifact-cache downloads, builds one tiny producer at a time, and then opens one fresh server per control. `support/transcript.json` retains ten CLI records, the `setup-file` JSON, client/server LSP frames, initializer markers and before/after artifact inventories. `support/artifacts/{v1,v2,mix}/` retains exact source, proof, Lake config, OLean, ILean, C and dylib specimens. Run `python3 support/check.py` for offline byte/outcome validation; `python3 support/probe.py` regenerates the experiment on the pinned host. The script owns and replaces only its named Meta scratch root and its own transcript/specimens.

The producer defines `selected := 7` or `9` and a `probe_tac` macro which expands to `decide`. Its native `Plugin.lean` initializer writes `plugin-v1` or `plugin-v2` to a private marker path. The consumer uses `plugins = ["@plugin_probe/+Plugin:dynlib"]` and a relative local `[[require]]`. The v2 consumer adds `leanOptions = [{name = "pp.universes", value = true}]`. This target spelling matters: `@plugin_probe/+Plugin:dynlib` resolves the module facet, and `lake setup-file` then lists the plugin dylib. The earlier `:shared` experiment was rejected as an unknown module facet and is not treated as an observed consumer result.

| Cell | Imported `Dep.olean` SHA-256 | Plugin dylib SHA-256 | Setup option | Fresh `lake serve` observation |
| --- | --- | --- | --- | --- |
| v1 | `078123f009c35edce8716cda15d83568dfbcb60c8840a0b74c26d47213ae02f2` | `5418363ec3b0d09e2cf5d8d058d088d9642da848531fb399cce6f863f2b63d3a` | none | No goals; info `7`; marker `plugin-v1` |
| v2 | `82056aa6634611238637e5c3d5dc166a1d0abc359ee14f61f2a12d5a541e8fd8` | `7e7f461e977f5f4cd22c6151ebeb3096fe40f08116e954527dce923ea6e01968` | `pp.universes=true` | No goals; info `9`; marker `plugin-v2` |
| mixed | v1 hash | v2 hash | `pp.universes=true` | No goals; info `7`; marker `plugin-v2` |

The mixed C hash equals v2 (`cddb20d2857b7998332e77a26aebac9123bbbec3f59814704fd4a6ed1a36ce18`), while its source and OLean equal v1; ILean bytes coincided in both clean generations. `support/check.py` asserts all retained byte identities, exact setup paths/options, the three fresh-server replies and markers, and unchanged mixed artifacts across setup/server. The LSP `textDocument/waitForDiagnostics` replies completed and `$/lean/plainGoal` returned `no goals`; the final diagnostics included the expected informational evaluation value. All three servers exited 0 after `shutdown` and `exit`. The marker proves execution of the selected plugin initializer, while the imported value and stable OLean hash give a bounded loaded-module oracle. There is no kernel-level trace of the OLean read syscall.

## Investigation coverage and remaining work

| Rows | New bounded contribution | Exact residual |
| --- | --- | --- |
| I089, I099 | Fresh local batch and Lake server agreed with each tiny generation and the selected mixed generation. | Real Anneal archive from empty home/cache; full clean-versus-prepared proof, diagnostics, goals, loaded-byte and producer-removed comparison. |
| I090, I091 | One relative two-package manifest; file-specific setup named imported OLean, plugin and option. | Package collision/order/version matrix; unsaved import-header changes and per-query setup attestation. |
| I092, I095 | Setup and server preserved all selected mixed artifact hashes, avoiding accidental rebuild in this case. | Broad no-build/no-cache and reuse/resource accounting, including actual prepared archive. |
| I093, I094 | Static TOML option and one exact pinned revision. | Dynamic Lean config and upgrade compatibility beyond earlier bounded reports. |
| I096, I097 | Exact local binaries, target selector, config, source, plugin and OLean digests retained. | Full CLI/editor/MCP discovery and sufficient keys across models, revisions and environments. |
| I098, I100 | One simultaneous valid setup/OLean/native-plugin/C family mix; exact consumed-value and initializer controls. | Systematic family and trace/mtime combinations, incompatible native ABI, complete integrity/rebuild policy. |
| I101, I103 | Copied same-name private package root with mixed generation bytes. | Relocation after producer removal and same-label archive replacement/interruption. |
| I102, I104 | Sequential local setup/server without downloads. | Concurrent/interrupted publication, enforced network isolation and filesystem attempt tracing. |
| I120 | Prepared plugin and tactic worked in fresh server. | Pruned module closure, new imports and scratch documents, space savings and failure behavior. |
| I125 | Lake-discovered v2 native plugin initialized in a fresh server beside v1 OLean. | Search-path variation, loaded-binary attestation, ABI replacement hazards and retained-process restart semantics. |
| I150 | Operation-specific specimen for `setup-file`, fresh `lake serve`, direct batch and plugin initialization. | Full batch/build/JSON/InfoView/RPC operation inventory, real Anneal prepared state and ownership policy. |

All rows remain partial. This is a local component experiment on macOS arm64, one Lake revision and tiny packages. It makes no cross-platform, power-loss, general cache-key, general native ABI, or production Anneal integration claim.
