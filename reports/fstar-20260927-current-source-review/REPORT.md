# R400 F* source identity at 2026-09-30: no newer revision

## Summary

The [R400 matrix](support/matrix.json) freezes the exact first `## Summary` claim and complete summary, section locator, original subjects, report/metadata hashes, and claim-to-source mapping at reference `6b1af799ae4ed60744e98137033ab66e1d3b68a5`. Read-only official `git ls-remote` returned both `HEAD` and `master` at [`FStarLang/FStar@78bb239b54cc113be68fb1dc0cbdfeb19378766a`](https://github.com/FStarLang/FStar/commit/78bb239b54cc113be68fb1dc0cbdfeb19378766a)—**exactly R400's source pin**. Official commit metadata dates that commit `2026-09-29T23:36:07Z`; its [`version.txt`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/version.txt) remains `2026.09.27`. No newer official source commit was observed, so this is a **no-newer-source result**, not a new validation of F* behavior.

The direct [latest F* release page](https://github.com/FStarLang/FStar/releases/tag/v2026.09.27) identifies `v2026.09.27`; the annotated tag object is `48268f3522ec8da089bbeb5f4e1674d50280a9c7` and peels to `7deb38a27c86990664c6b41e4b6093597acdebd4`. The page places that release **22 commits before** the observed `master` tip. Thus the latest tagged release is also not a newer source target than R400's already-current development pin. The matching number in `version.txt` does not make the release commit and `master` commit identical.

## Applicability

R400's first summary paragraph distinguishes freedom to search for proofs from authority to decide what counts as proof. Its wider summary adds abstract proof-state transformations, SMT/Z3 trust, native tactic execution, Lean/Rocq certificate contrasts, and conditional Anneal extensibility analysis. The matrix preserves the full text and maps F* clauses to five groups: abstract tactic state/divergence, SMT acceptance, native tactic loading, stage-specific tactic hooks, and historical/cross-prover context. The last group is recorded as historical/comparative material, without pretending that a new F* commit rechecks Lean, Rocq, SMTCoq, or Anneal.

The original selector comes from the 581-row `version-inventory-ebcdcad-581.csv` at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The exact frozen reference has **592** report packages. The 11 post-inventory additions are separately listed and hashed; none changes R400's original path or source pin. Official source identity observations are preserved in [official-source-identity.json](support/official-source-identity.json), including the queried refs and commit timestamp. The offline checker verifies that saved observation's structure and hash, though it cannot independently refresh GitHub.

## Findings

| Frozen R400 clause group | Exact pinned F* source | Newer-version result |
| --- | --- | --- |
| Abstract proof state, primitive transformations, tactic divergence | [`part5_meta.rst`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/doc/book/PoP-in-FStar/book/part5/part5_meta.rst), [`FStar.Tactics.Effect.fsti`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/ulib/FStar.Tactics.Effect.fsti) | No newer source revision exists in the observed official `master`; no changed-file comparison is possible. |
| SMT discharge and encoding/Z3 trust | [`part1_prop_assertions.rst`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/doc/book/PoP-in-FStar/book/part1/part1_prop_assertions.rst), `part5_meta.rst` | Same source identity as R400; no new behavior conclusion. |
| Native plugin execution boundary | [`examples/native_tactics/README`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/examples/native_tactics/README), [`FStarC_Tactics_Native.ml`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/src/ml/FStarC_Tactics_Native.ml) | Same source identity as R400; no newly changed files or runtime evidence. |
| Proof-synthesis, assertion, preprocessing and postprocessing hooks | [`FStar.Tactics.Effect.fsti`](https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/ulib/FStar.Tactics.Effect.fsti) | Same source identity; no newer hook semantics checked. |
| Historical Meta-F* / Lean / Rocq / SMTCoq / Anneal comparisons | Original publication and cross-project subjects retained in matrix | Historical and derived analysis, outside this F* source refresh. |

There is **no old-to-current changed-file set**: the two commit IDs are identical. The release's older source commit does not create a forward source difference from R400. This review neither confirms nor refutes the original report's trust-boundary interpretation on a later implementation. It establishes only that the specific version-drift question has no newer official F* source at this observation.

## Boundaries

No F*, Z3, Lean, Rocq, SMTCoq, compiler, or plugin process was run or installed. Every mapped clause records `runtime_result: unexecuted_in_this_review`; Anneal's product result is `unassessed`. Raw new-source snapshots were not acquired, and their SHA-256 fields are null. R400's original Git blob identities remain frozen historical evidence in the matrix. An unchanged upstream ref is not a test of the old claim or a guarantee that external services, packages, documentation hosts, or Anneal behavior have stayed constant.

## Evidence

The package contains the [matrix](support/matrix.json), [single-row selector](support/frozen-cohort.csv), [baseline inventory](support/version-inventory-ebcdcad-581.csv), [baseline path set](support/baseline-report-paths.txt), [official ref/date observation](support/official-source-identity.json), and [offline checker](support/check_matrix.py). The checker validates the exact frozen Git report and metadata, full summary and locator, original subject identities and blob mentions, 581/592 corpus reconciliation with 11 hashed additions, recorded official ref/tag pin graph, and separate source/runtime/product outcomes.

## Revalidation

Run `python3 reports/fstar-20260927-current-source-review/support/check_matrix.py` from a checkout containing the baseline and frozen commits. Once a newer official F* source commit or release exists, resolve the new ref and annotated tag to full commits, compare the mapped F* files and any implementation paths behind the source-level abstractions, and classify each clause separately. A behavioral recheck needs a version-pinned F*/Z3/native-plugin fixture and recorded outcomes. Prompt/setup refinement: inspect upstream refs before allocating a version-comparison cell; when a report already pins current `master`, record a no-newer result instead of comparing it to an older same-numbered release tag.
