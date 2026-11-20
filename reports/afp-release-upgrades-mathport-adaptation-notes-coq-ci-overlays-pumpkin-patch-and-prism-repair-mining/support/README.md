# Support material

Probe scripts and their recorded outputs for `REPORT.md`. All scripts use only the Python 3 standard library (or Bash plus an authenticated `gh` CLI for `history_counts.sh`).

Inputs, all at the revisions pinned in `REPORT.json`:

- Mathlib source tree: `https://codeload.github.com/leanprover-community/mathlib4/tar.gz/5fc503cdd50c2c198f54ccc97121ec82919e2930`, extracted.
- Mathport alignment tables: `https://raw.githubusercontent.com/leanprover-community/mathport/<rev>/Aligns/mathlib-align.json` and `.../mathlib-alignImport.json`.
- AFP metadata: `https://raw.githubusercontent.com/isabelle-prover/mirror-afp-devel/<rev>/metadata/releases.toml` and `.../metadata/release-dates`, plus a file listing obtained with `gh api repos/isabelle-prover/mirror-afp-devel/git/trees/<rev>?recursive=1 --jq '.tree[].path'`.
- Rocq overlays: every `dev/ci/user-overlays/*.sh` file and `dev/ci/ci-basic-overlay.sh` at the pinned Rocq revision.

| Script | Output |
|---|---|
| `adaptation_notes.py <mathlib-root>` | `adaptation_notes.out` |
| `deprecations.py <mathlib-root>` | `deprecations.out` |
| `mathport_aligns.py <align.json> <alignImport.json>` | `mathport_aligns.out` |
| `afp_releases.py <releases.toml> <release-dates> <tree-listing>` | `afp_releases.out` |
| `rocq_overlays.py <overlay-dir> <ci-basic-overlay.sh>` | `rocq_overlays.out` |
| `history_counts.sh` | `history_counts.out` (12-character abbreviated SHAs) |
| `toolchain_cadence.py history_counts.out` | `toolchain_cadence.out` |
