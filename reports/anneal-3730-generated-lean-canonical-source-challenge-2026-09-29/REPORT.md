# Synthetic generated Lean as canonical proof source: authority and projection challenge

## Summary

A tiny executable alternative makes an initially generated `Proof.lean` the **canonical, user-editable proof source**. Rust remains canonical for function semantics; an experiment-owned generator derives `Model.lean` from a small Rust subset. A generated `HostView.rs` embeds the proof as Rust comments with a line/range map and routes hosted edits into `Proof.lean` through a proof-hash compare-and-swap. The view itself is never an independent proof copy. Pinned Lean batch checks passed before edits, after Unicode and tactic edits, and after repair. They failed when the hosted proof claimed the wrong value and when Rust semantics changed while proof bytes stayed fixed. The failing `lean --json` tactic position mapped to the corresponding Rust-hosted view line.

This is a bounded design/falsification experiment for #3730 **N08** and #3731 **I159**. It demonstrates one workable authority contract under a deliberately simple local generator. It does **not** implement Anneal V2, select this as its architecture, or establish that actual Charon/Aeneas-generated Lean can be safely promoted to canonical editable source.

## Authority contract and fixture

The source authorities are explicit:

| Surface | Role in this fixture | Edit handling |
| --- | --- | --- |
| `RustSource.rs` | Canonical Rust function body | Regenerates the derivative model on a fresh check. |
| `Proof.lean` | Canonical Lean proof text after its initial creation | Direct edits persist; hosted proof-range edits compare the expected proof hash and update this file. |
| `HostView.rs` | Generated Rust-hosted view of the canonical proof | Recreated from the two authorities; scaffold edits are rejected. |
| `Model.lean` / `Model.olean` | Derivative Lean model of the Rust subset | Rebuilt from `RustSource.rs`; a direct tamper is overwritten. |

`RustSource.rs` is a compilable tiny Rust function `model_add(x) = x + 1` (later `x + 2`). The Python fixture recognizes only this exact syntactic subset and writes `def modelAdd (x : Nat) : Nat := x + N`; it is **not** Charon or Aeneas translation. `Proof.lean` imports that model, includes a Unicode comment with an astral emoji, and proves `modelAdd 1 = 2` by `rfl`. `HostView.rs` appends each canonical Lean line as a `//| ` Rust comment below a generated header containing the proof SHA-256; the view itself also compiles as Rust. A source map records the 0-based proof and view lines, prefix width and per-line hashes. The original proof bytes can be reconstructed exactly by removing the prefix from the marked view region. This tests a Rust-hosted display/edit contract without a real editor extension.

The run used Lean `v4.30.0-rc2` at revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, Lean binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, and local `rustc 1.98.1 (48a229cea 2026-09-01)` on macOS arm64. Scratch stayed in one private directory on the internal filesystem, with about 51 GiB disk headroom and 55% host memory free at preflight. The proof was checked with a fresh direct `lean --json Proof.lean` process after compiling `Model.olean`; no Lake, MCP adapter, editor process, network service, installation, or Anneal code was used.

## Round-trip and provenance observations

| State/change | Proof source | Model source/OLean | Fresh Lean result | Authority observation |
| --- | --- | --- | --- | --- |
| Initial | SHA `38a52f636d36…` | `7d81f6be6037…` / `0e1b64ef7ecd…` | Exit 0 | Initial view parsed back to identical proof bytes; Rust host compiled. |
| Hosted UTF-16 comment edit `β` → `λ` after `🦀` | New proof SHA `ee3449eff1a1…` | Unchanged | Exit 0 | View range `[23,24)` UTF-16 mapped to proof range `[19,20)` and byte range `[35,37)`; no split inside the emoji or beta. |
| Hosted tactic edit `rfl` → `decide` | SHA `28297317adf4…` | Unchanged | Exit 0 | The mapped proof file changed, then a fresh view parsed back exactly; Rust host compiled. |
| Direct canonical proof edit back to `rfl` | SHA `ee3449eff1a1…` | Unchanged | Later fresh checks exit 0 | Regenerated view followed the Lean file. An edit using the old proof hash was rejected as stale; an edit to Rust/view scaffolding was rejected. Neither rejection changed proof bytes. |
| Hosted claim edit `2` → `3` | SHA `0f9dcdadf294…` | Unchanged | Exit 1 | Lean reported `rfl` failure at proof line 5, column 2. The map resolved it to hosted view line 8, column 6 (0-based view coordinates). |
| Hosted repair `3` → `2` | SHA `ee3449eff1a1…` | Unchanged | Exit 0 | Proof repair restored acceptance. |
| Rust function edit `x + 1` → `x + 2` | **Unchanged** SHA `ee3449eff1a1…` | Changed to `fbaf2918d21c…` / `dc815811a2eb…` | Exit 1 | Same proof text failed against a new model import. The diagnostic still pointed into the proof tactic; source/model hashes identify the changed dependency that must accompany attribution. |
| Restore Rust and regenerate after direct tamper of `Model.lean` to `x + 99` | Unchanged | Restored to original hashes | Exit 0 | Derivative model tamper was erased from the Rust authority; canonical proof was preserved and view round trip remained exact. |

All success/failure outcomes are retained with exact `rustc` and Lean command lines, exits, stdout/stderr, proof/model source and OLean hashes in [`support/results.json`](support/results.json). The initial, wrong-proof, changed-model and final Rust/Lean/view artifacts are retained under [`support/artifacts/`](support/artifacts/). The `wrong-proof` and `changed-model` controls both yielded the same tactical error location but different source-cause manifests: in one, proof bytes changed; in the other, only the Rust-derived model changed. A UI may point to the proof span while retaining the transitive model identity; the diagnostic location alone does not establish which upstream input caused the failure.

The range mapping is intentionally specific: UTF-16 columns are used for hosted edits, including one astral emoji preceding the edited beta; `lean --json`'s ASCII tactic diagnostic is mapped by the fixed four-character view prefix. The fixture does not claim a general sourcemap for macro expansion, generated declarations, `#line` directives, CRLF conversion, multiple files, or arbitrary Rust formatting. A direct `rustfmt` transformation of the projected comments was not tested. The stale-hash guard is a local compare-and-swap model, not a real editor revision protocol.

## Design consequence and residual

The strongest successful precondition for this alternative is that the Lean proof file keeps a durable independent identity while the Rust view is only a projection. Regenerating the Rust-derived model may change proof acceptance without changing proof text, so a proof result must identify both canonical proof bytes and the imported model OLean/source generation. Direct proof edits and hosted edits can coexist only with explicit stale-edit rejection and a stable source map. Generated scaffold must be read-only or separately governed to avoid silent overwrite of the canonical proof.

This local success does not decide whether Anneal should make generated Lean canonical. I159/N08 remain **partial**. A product experiment still needs actual Aeneas-generated modules, Rust annotations, declaration/obligation identities, cross-file imports, model/axiom checks, editor dirty-buffer behavior, source spans through generation, two-client races, regeneration/migration across tool revisions, and fresh batch plus live-server equivalence. It must compare the alternate topology with the proposed Rust-hosted/sidecar ownership under the same workload and user-facing edit/query contract. No such Anneal V2 integration was available in this checkout. The prototype's manually recognized Rust subset cannot make claims about Charon or Aeneas translation fidelity.

## Reproduction and validation

[`support/probe.py`](support/probe.py) builds the fixture, applies the accepted/rejected edits, runs local `rustc` and pinned `lean`, and writes the raw transcript/artifacts. [`support/check.py`](support/check.py) verifies every retained command outcome, content hash, exact view reconstruction, UTF-16/UTF-8 range, stale/scaffold rejection, diagnostic projection and model/proof provenance. It passed, and `reference._load_report` validated the package.

From this package, use a new owned scratch path and the already installed binaries:

```console
python3 support/probe.py --lean /absolute/path/to/pinned/lean --rustc /absolute/path/to/rustc --work /owned/absent/work --out support
python3 support/check.py
```

This reproduces only the synthetic contract, not Anneal's actual generated workspace.
