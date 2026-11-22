# Support material

All files here belong to the report in the parent directory. Nothing in this
directory is an instruction to a reader or to an agent; it is evidence and the
means to regenerate it.

| File | Role |
| :--- | :--- |
| `probe_sized_hierarchy_and_extern_types.py` | Self-contained probe. Embeds every Rust source it compiles, runs `rustc` and the `miri` driver as subprocesses, compares the fresh observations with pins, and writes a JSON record. |
| `probe_results_rustc_1_98_0_nightly_2026_05_31.json` | Output of the probe on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with its Miri, host `x86_64-unknown-linux-gnu`, run on 2026-11-22. Records the SHA-256 of the probe script that produced it. Host path prefixes are replaced by `<TMP>`, `<SYSROOT>`, `<MIRI_SYSROOT>`, `<HOME>`; thread ids by `<TID>`. |
| `prior_run_record_rustc_1_102_0_nightly_2026_11_11.json` | Output record of an earlier, smaller predecessor of the probe on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, dated 2026-11-21. The predecessor's Rust sources were not preserved (they are partly visible in the quoted diagnostics), and the run was not repeated for this report. Two edits were made to the record: one task-label key was dropped and a host toolchain path prefix was replaced by `<SYSROOT>`; thread ids were replaced by `<TID>`. Its `rust_repo_head_inspected` field is retained verbatim and is not used by the report. Treat it as corroboration only. |
| `SizedHierarchyAndExternTailSoundness.lean` | Lean 4 model and proofs (core library only, no imports). |
| `AxiomAudit.lean` | Walks every declaration the compiled module adds to the environment; fails unless only `propext` / `Quot.sound` are used, nothing is declared as an axiom or opaque constant, nothing is unsafe or partial, and the named theorems exist. |
| `verify_lean.sh` | Token scan, kernel check with warnings as errors, then the audit. |
| `lean_verification_output.txt` | Output of `verify_lean.sh` under Lean 4 v4.34.1 on 2026-11-22 (launcher noise removed, directory prefix stripped). |
| `compare_source_regions.py` | Downloads the cited `rust-lang/rust` files at the given revisions, extracts each cited region by anchor and brace matching, and records line ranges and text equality against the first revision. |
| `source_region_continuity.json` | Output of `compare_source_regions.py` for the three examined `rust-lang/rust` revisions. |
| `resolved_revisions.json` | Result of resolving every cited commit, pull request and issue through the GitHub REST API on 2026-11-22. |

Regenerating:

```sh
# rustc + Miri observations (needs the nightly with the miri component and a built Miri sysroot)
python3 probe_sized_hierarchy_and_extern_types.py --toolchain nightly-2026-06-01 --out fresh.json --check

# Lean check and audit (needs Lean 4 v4.34.1)
LEAN=/path/to/lean ./verify_lean.sh

# source-region comparison (needs network access to raw.githubusercontent.com)
python3 compare_source_regions.py --out fresh_regions.json \
  14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 \
  3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 \
  342d74463af7dd3018ef6aa04dd5500c2deb5bd1
```
