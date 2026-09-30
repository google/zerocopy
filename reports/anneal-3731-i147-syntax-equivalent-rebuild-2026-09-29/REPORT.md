# I147/C06: syntax edit, identical rebuilt OLean, different trace and ILean

## Summary

On pinned Lean/Lake `v4.30.0-rc2`, the fixture changed `def selected : Nat := 7` to `def selected:Nat := 0x7`. Both are 24 source bytes and evaluate to 7. Lake rebuilt `Dep` after the edit: the OLean mtime changed, while its 4,616 bytes remained **byte identical** (SHA-256 `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62`). The source SHA-256 changed from `a65f7080…` to `258b3e8a…`; the Lake trace and ILean bytes also changed. A resident server file, a newly opened file, the reopened file, a fresh server and fresh batch controls all agreed on the same proof result. **Basis: local execution.**

This is one syntax-level instance of [#3730 C06](../anneal-3730-3731-final-coverage-audit-2026-09-29-v31/support/3730-crosswalk-final-v31.csv) and [#3731 I147](../anneal-3730-3731-final-coverage-audit-2026-09-29-v31/support/investigation-final-v31.csv). It is distinct from the earlier [equal-length comment edit](../anneal-3731-i107-i159-independent-rereview-2026-09-29/REPORT.md): the numeral is spelled in hexadecimal and the declaration's spacing changes. C06 and I147 remain partial at their product scope.

## Method and controls

The same private Lake project, module name, and path were used before and after the edit. `Dep.lean` defined `selected`; `Proof.lean` imported it and contained a solved `rfl` theorem plus an intentionally unfinished scratch theorem for a second goal position. `Check.lean` imported `Dep`, evaluated `selected`, and proved `selected = 7` with `rfl`. The probe first ran `lake --keep-toolchain --no-cache build Dep` and fresh batch `lean --json Check.lean`, then opened `Proof.lean` in direct `lean --server`. It edited `Dep.lean`, sent a watched-file notification, queried the resident worker, opened `New.lean` to cause the new import build, queried the resident again, closed/reopened the original URI, stopped that server, launched a fresh server, ran `lake setup-file`, and finally ran fresh batch Lean. One server process tree was active at a time. No dependency was fetched or installed.

The executable identities match the cached project-local Lean/Lake toolchain: `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`, Lean revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. The parent `reference` checkout was `e26a9414ab48844eeb95b91ee8b743046c8a8982`; v31 was the local coverage reference, not a newly fetched issue snapshot.

The guard required at least 20% estimated free memory from `vm_stat`, sampled server-tree RSS at most 1.5 GiB, scratch below 1 GiB and total probe duration at most five minutes. Preflight was 24.40% free; the minimum sampled free estimate was 22.53%, maximum sampled tree RSS 1,013,760,000 bytes, maximum scratch 106,813 bytes, and total recorded duration 4.27 seconds. These are guard samples, not a peak-resource measurement.

## Observations

| Evidence | Baseline | Edited/rebuilt |
| --- | --- | --- |
| `Dep.lean` SHA-256 | `a65f708068d277a77a351c90927ac6b9e0d36f7d42376cd84caf4fba41cfcefc` | `258b3e8a5ffffa4c7edabc080a9c1af11b2d135019c5780e7248d7e0dc33cfbb` |
| `Dep.olean` SHA-256 | `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62` | same, byte comparison passed |
| `Dep.ilean` SHA-256 | `421fe1322bfa48a720510f38a7999947ed0c69c6d73b988305d06d848f934b3d` | `4cbf7fd491d156395a90e465c95654fa59d4e4272ea13a469a08e3b37ac84236` |
| `Dep.trace` SHA-256 | `8fb7b0023a194ac3a88db1faeb42848ada5a130fb7e732dbd5c13f570d9b5dfc` | `ea41d920856775f11ba2b49320aa2f2d6b92bfef8779dd503fa0003494e7a94c` |
| Solved `rfl` goal | `no goals` | `no goals` in resident, new, reopened, and fresh-server samples |
| Scratch goal | `⊢ selected = 7` | same in all six samples |
| Fresh batch `Check.lean` | exit 0; `#eval selected` printed 7 | exit 0; `#eval selected` printed 7 |

The trace's `outputs.o` reference stayed equal, while `outputs.i` changed. The OLean mtime changed between the baseline and new-file samples. Thus byte equality here is a measured compiled-artifact result following a rebuild, not simply an unchanged file left in place. The ordered [wire transcript](support/transcript.json) preserves requests, replies, diagnostics, goals, command output, artifact metadata, and all guard readings. The two source files, OLeans, ILeans, traces, proof control and final OLean are retained in [`support/`](support/).

The selected syntax was chosen from a small, retained direct-compiler screen. The longer `0x7` and `(7 : Nat)` variants compiled to OLean bytes different from the direct baseline; same-length `0x7` and `(7)` variants compiled to identical direct OLean bytes. `ℕ` failed in this minimal import. A first full Lake/server attempt using the longer `(7)` variant also produced a different OLean (two changed bytes), despite the same goals and batch value; its source, OLean, trace and transcript are retained in [`attempt-parentheses/`](support/attempt-parentheses/). These controls show why a semantic equivalence claim alone cannot substitute for byte comparison.

## Scope

The result supports a narrow C06/I147 component cell: one changed Lean source can rebuild to an identical OLean while trace and editor information differ. It does not supply a general semantic-sameness oracle, prove that all equivalent syntax edits preserve OLean bytes, or determine when an Anneal worker should reload. A byte-identical OLean alone does not establish identical ILean, trace, source provenance, tool options, native setup, or a complete proof environment. No Anneal V2 pipeline, archive, integrated freshness policy, or product acceptance gate was exercised.

## Revalidation

Run `python3 support/check.py` from this package directory. It reads only retained files and locates them relative to the checker, so the package can be moved. The retained Lake traces embed the original absolute worktree path; relocation checks them as evidence bytes rather than reusable build state. The checker validates exact evidence hashes, source/OLean/ILean/trace relationships, server and batch outcomes, candidate controls, and guard bounds. [`evidence-manifest.json`](support/evidence-manifest.json) records bytes and SHA-256 for 23 evidence files. To reacquire the fixture on the same cached pin, set `LEAN_BIN` to the project-local `.../v4.30.0-rc2/bin/lean` absolute path and run `python3 support/probe.py`; that replaces this package's `support/work/` and primary transcript/artifact copies. Reacquisition is a new observation and should be compared with this retained record before updating the claim.
