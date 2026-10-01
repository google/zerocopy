# Source-only reproduction

The R350 predecessor is frozen at `google/zerocopy@1b6f146d7951402e10102354a131b5cee9c5f855`. The working reference parent for this package is `1e87e9bf7b672c354b4c2903a372329ee61faf63`.

From the reference checkout, use this **offline data validator**:

```sh
python3 reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30/support/check_source.py
```

It reads frozen Git report objects, the ten retained old/new source files, their hashes and exact diffs, and the retained Rust Cargo gitlink records. It does not launch Cargo, rustc, or the R350 fixture. For an independent official-source refresh, resolve `refs/tags/1.98.1^{}` in `rust-lang/rust`; query `src/tools/cargo` at the resulting commit and confirm the `797e8a9bca276c1c9f9f738d2a20f484fa4eea9d` gitlink. Query the old Rust `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` tree's same path and confirm `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`. For every path in `source-observation.json`, fetch both commit-pinned raw URLs, compute SHA-256 and Git blob SHA-1, and make a three-context unified diff. The retained snapshots and recorded hashes specify every expected byte result.

Do not infer current-version runtime counts from the old `support/unit-graph-*.json`, `support/rustc-workspace.jsonl`, or `support/command-results.json` in R350. Those are separate pinned-nightly execution artifacts. The new source and the Cargo process-construction deltas would need a new fixture run for a runtime answer.
