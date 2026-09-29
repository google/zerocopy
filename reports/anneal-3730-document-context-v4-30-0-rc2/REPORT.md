# Direct Lean document context, imported buffers, and module layout

## Summary

In a tiny Lean/Lake fixture, editing an open `A.lean` buffer from value `7` to `9` did not change the separately open `B.lean` worker's import of the compiled `A.olean` value `7`. Rebuilding that artifact made a fresh `B` proof of `marker = 7` fail. A clean Lake import cycle and the same cycle introduced after valid `.olean` outputs both failed; stale outputs did not make this Lake build graph accept the cycle. Moving a generated declaration after its use silently changed the type of an `axiom` under `autoImplicit`, while an incomplete scratch wrapper lost required namespace/section/notation context. These are direct Lean/Lake observations, not Anneal behavior.

## Applicability

Execution used Lean/Lake `v4.30.0-rc2`, `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, arm64 macOS, `LEAN_NUM_THREADS=1`, direct `lean --server` LSP and fresh `lean --json` batch controls. Lake built the tiny `A` library with `--keep-toolchain --no-cache`; no external package or plugin was installed. LSP file URIs and document versions are preserved in `raw.json` with one canonical path substitution (`file://$WORK/...`), so repeated same-URI comparisons remain visible without publishing a personal absolute path.

Prior [generated-file interactive workflows](../lean-generated-file-interactive-workflows-v4-30-0-rc2/REPORT.md) described the dependency lifecycle from source/documentation; [module import semantics](../lean-module-import-semantics-v4-30-0-rc2/REPORT.md) described `.olean` resolution from source. The [editor/MCP shadow-authority probe](../anneal-3730-editor-mcp-shadow-authority-v4-30-0-rc2/REPORT.md) executed unsaved text for independent core documents. This report adds an executed *cross-module* unsaved-buffer control, plus generated declaration, cycle, stable-URI, and scratch-context controls.

## Findings

### An open producer buffer was not the import artifact

`A.lean` initially defined `marker : Nat := 7`; Lake built `A.olean` SHA-256 `22562d8b3e1dee4dd9147b82c878beda118f3564ba91dc5225d07dbd0b70226a`. `B.lean` imported `A`, proved `marker = 7` by `decide`, and printed `7`. Fresh batch `B` exited 0. A direct LSP server opened both file URIs; changing only the open `A` document to `marker := 9` at version 2, then forcing `B` version 2 to re-elaborate by adding `#check marker`, still produced the `7` information diagnostic on `B`. Its source on disk and `A.olean` hashes remained the original values; fresh batch `B` still exited 0 and printed `7`. Basis: **execution**.

After writing `A.lean` value `9` to disk and rebuilding, `A.olean` SHA-256 became `f834768ca2518d8a2134d7e4e97433fa6b4d9b2d14fa4c560bdf2f7f4eed5ee3`. Fresh batch `B` exited 1, reporting `decide` had proved `marker = 7` false, and printed `9`; a fresh LSP `B` worker reported the same error and value. This is evidence for the tested direct server and artifact state, not a universal promise about how an existing worker refreshes dependencies. Basis: **execution**.

### A stable file URI did not determine an import environment

A separate neutral directory held byte-identical `B.lean` at one stable `file://$WORK/neutral/B.lean` URI and SHA-256 `3caf12ce355cf451fea23fa232d6579b4fde7478d4964d505549fdf2bec96f72`. Two fresh direct LSP workers used generation-specific `LEAN_PATH` directories. The value-7 artifact yielded a `7` information diagnostic and no proof error; the value-9 artifact yielded the failed `decide` error and `9`. Fresh batch controls agreed. Thus URI and source bytes alone did not identify the imported environment in this fixture. Basis: **execution**.

A useful negative control: when the same experiment kept `B.lean` inside the Lake project, both fresh server launches reported value `9` even when their parent process was given `LEAN_PATH` for the value-7 generation. A direct batch command in that project with the value-7 path printed `7`. The transcript does not isolate which Lean server/Lake setup step selected the project artifact, so this is a warning to verify the actual worker environment rather than assume the parent `LEAN_PATH` wins. It is not evidence that stable URI must always change when a generation changes.

### Source order and wrapper context can change the theorem

With `def later : Nat := 1` before `axiom early : later = 1`, `#print early` reported `axiom early : later = 1`. Moving the same axiom before the definition, with default `autoImplicit`, succeeded but printed `axiom early : ∀ {later : Nat}, later = 1`. The attempted forward *proof* failed. This is a concrete declaration-order hazard: success of a generated file did not guarantee the intended proposition when a name was unresolved at its use. Basis: **execution**.

A proof in `namespace N`, a `section` with `variable (n : Nat)`, local notation `myN => n`, and `set_option autoImplicit false` succeeded and printed `theorem N.proof : ∀ (n : Nat), n = n`. A scratch file retaining only the namespace and theorem text failed with unknown `myN`; restoring the full option/section/variable/notation context succeeded with the same printed theorem type. This checks one wrapper/scratch context mismatch. It does not cover local instances, macros, or all elaborated dependencies. Basis: **execution**.

### Lake rejected the tested cycles even with stale outputs

A clean `A.lean` importing `B` and `B.lean` importing `A` made `lake build A` exit 1 with `build cycle detected` and an import/export/setup target chain. In a second package, valid noncyclic `A.olean` and `B.olean` were first built; changing `A.lean` to import `B` made `lake build B` exit 1 with the same cycle class and a bad-import failure. The preserved old artifact hashes identify that negative control. Basis: **execution**. This is Lake build-graph rejection for these ordinary libraries; direct `lean` against manually selected stale `.olean` files and richer generated graphs were not tested.

## Boundaries

- **I033:** File-backed project URIs were exercised; custom schemes, nonexistent file URIs, `setup-file`, and untitled documents were covered only in the linked prior editor probe, not combined here with imports.
- **I034:** Fresh neutral workers with one stable URI and two generation paths were exercised. Existing-worker remapping, incremental reuse, and close/reopen publication were not measured.
- **I035:** Per-annotation, per-file, and per-artifact layouts, worker-count economics, and large model sizes were not examined.
- **I036:** An imported artifact changed and a dependent was re-elaborated, but Lean prefix reuse, cancellation, and separate early/late command changes were not measured.
- **I037:** The namespace/section/variable/notation/option specimen shows a wrapper fidelity pitfall; local instances, macros, and generated Rust annotations remain untested.
- **I038:** The cross-module unsaved `A`/`B` case is directly tested, but multiple overlapping packages, dependency refresh commands, and plugin-specific imports remain untested.
- **I039:** One two-node Lake cycle and one declaration-order capture were tested. General generation, compilation, and proof dependency graphs remain open.
- **I040:** One incomplete scratch context and one fully recreated context were tested. Tactic search services and pre-elaborated prefix transfer were not examined.

## Evidence

- [`probe.py`](probe.py), SHA-256 `1d5f6d29e7e91a434333f0b35e06b8de8926a30c10fad2f38199dfcfa996cced`, creates every fixture, builds artifacts, runs fresh batch controls, drives direct LSP JSON-RPC, and records sources/hashes/URIs/diagnostics.
- [`raw.json`](raw.json), SHA-256 `19f625d982f23ff77a075940593d962a359c5a6a268f387165f5a276c7e44069`, preserves the full normalized stream and command results. `$WORK`, `$LEAN_BIN`, `$LEAN_HOME`, and `$HOME` are path substitutions only; the same URI template and each document version remain identifiable.
- Pinned binary SHA-256: `lean` `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; `lake` `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`. `A.lean` value-7 SHA-256 `d177da0236aac251d167e324486d5cb936786bceec18bcee402e17c7ec2c71b0`; value-9 `0b6fcf458cac31c4f31f92b2cd7d1f9b8a79823cf923d311dfe6cb123fa33893`; `B.lean` `3caf12ce355cf451fea23fa232d6579b4fde7478d4964d505549fdf2bec96f72`.
- Acquired and replayed on 2026-09-29 from this report package; the generated disposable `work/` tree was removed after the replay. The script remains runnable.

## Revalidation

Run `python3 probe.py` from this package with the pinned Lean/Lake toolchain at the script's `BIN` path, or change `BIN` to another explicitly recorded installation. Compare `A.olean` hashes, `B` versioned diagnostics, neutral same-URI generation results, both cycle failures, and the two `#print` outputs. Re-run the neutral and Lake-project cases separately when changing worker setup, because their artifact selection differed here. The script recreates `work/` and `raw.json`; preserve any new transcript before cleaning the work tree.
