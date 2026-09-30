# R389 Dafny, Boogie, and Viper current-source review

## Summary

The six official default branches named in [R389](../dafny-boogie-viper-obligation-boundaries-2005-2026/REPORT.md) still pointed to R389's exact full source commits when observed on 2026-09-30. Each old-to-current default-branch comparison is therefore the **same commit** with zero forward commits and no changed paths. This is a bounded source-identity result. It is not a newer-version revalidation of Dafny, Boogie, Viper, runtime behavior, or Anneal's proposed semantic-obligation boundary.

## Frozen claims and independent repositories

The [matrix](support/matrix.json) freezes R389's exact five Summary paragraphs, seven Findings locators, six evidence-map claims, report/evidence-map hashes, original subjects, and section locator at reference `2720194c6f74fe5489428adecc1ded39df98b096`. R389 came from the 581-report version inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The frozen parent has 611 report packages; all 30 later packages are reconciled by path and hash.

The [official-source observation](support/official-source-observation.json) keeps six repository rows separate. Raw ref snapshots and the one claim-mapped source file from each repository are preserved under [`support/`](support/). All six preserved files reproduce the old report's Git blob IDs and have recorded content SHA-256 values:

| Repository and current `master` | R389 claim-mapped path | Default-branch result |
| --- | --- | --- |
| [`dafny-lang/dafny@5f717bf4…`](https://github.com/dafny-lang/dafny/commit/5f717bf447b19d38cad1b69b1bf9a9f102feccfb) | [`Source/DafnyCore/Verifier/BoogieGenerator.cs`](https://github.com/dafny-lang/dafny/blob/5f717bf447b19d38cad1b69b1bf9a9f102feccfb/Source/DafnyCore/Verifier/BoogieGenerator.cs) | Same commit and blob for translator provenance source. |
| [`boogie-org/boogie@fcecf73a…`](https://github.com/boogie-org/boogie/commit/fcecf73a49d11ad3ab16729abd03169e5ecfd938) | [`README.md`](https://github.com/boogie-org/boogie/blob/fcecf73a49d11ad3ab16729abd03169e5ecfd938/README.md) | Same commit and blob for IVL/VC architecture documentation. |
| [`viperproject/silver@da1c8993…`](https://github.com/viperproject/silver/commit/da1c8993b66feb39976e3609e2580a4661137a0f) | [`VerificationResult.scala`](https://github.com/viperproject/silver/blob/da1c8993b66feb39976e3609e2580a4661137a0f/src/main/scala/viper/silver/verifier/VerificationResult.scala) | Same commit and blob for shared error/result provenance. |
| [`viperproject/silicon@6ceff8be…`](https://github.com/viperproject/silicon/commit/6ceff8be6ba55d858b7d018fdfeb866b7e8aa0ed) | [`README.md`](https://github.com/viperproject/silicon/blob/6ceff8be6ba55d858b7d018fdfeb866b7e8aa0ed/README.md) | Same commit and blob for symbolic-execution backend description. |
| [`viperproject/carbon@6421cfda…`](https://github.com/viperproject/carbon/commit/6421cfda16d35f37cb9a7966f04fcd2d96abdda2) | [`README.md`](https://github.com/viperproject/carbon/blob/6421cfda16d35f37cb9a7966f04fcd2d96abdda2/README.md) | Same commit and blob for VC-generation backend description. |
| [`viperproject/viperserver@4cc5bbbe…`](https://github.com/viperproject/viperserver/commit/4cc5bbbe18d4a83e4b398da3904ba9696256611b) | [`README.md`](https://github.com/viperproject/viperserver/blob/4cc5bbbe18d4a83e4b398da3904ba9696256611b/README.md) | Same commit and blob for outer verification-service description. |

Silver and Silicon are separate repositories, revisions, and claim roles; Carbon and ViperServer remain separate as well. The exact evidence-map claims connect Dafny provenance, Boogie's IVL boundary, Silver results, Silicon/Carbon alternative backends, and ViperServer orchestration. Historical architecture papers, current Dafny web documentation, and Anneal's design pin are retained as their original evidence types and are not recast as a forward source comparison.

## Release identities are separate from default branches

The official GitHub `releases/latest` endpoint returned Dafny [`v4.11.0`](https://github.com/dafny-lang/dafny/releases/tag/v4.11.0), Boogie [`v3.5.7`](https://github.com/boogie-org/boogie/releases/tag/v3.5.7), Silver [`v.21.07-release`](https://github.com/viperproject/silver/releases/tag/v.21.07-release), and ViperServer [`v.26.08-release`](https://github.com/viperproject/viperserver/releases/tag/v.26.08-release). Their exact tag ref objects and peeled commits are recorded in separate raw snapshots. Silicon and Carbon each returned 404 at that endpoint, so no GitHub Release object was identified for them.

The Dafny release tag peels to `fcb2042d6d043a2634f0854338c08feeaaaf4ae2` and **diverges** from pinned/current `master`: comparing release to `master` gives 68 commits ahead and 3 behind. It is not a forward successor to R389's Dafny pin. Boogie's lightweight release tag is 14 commits behind its pinned/current `master`; Silver's peeled release is 905 behind; ViperServer's peeled release is 2 behind. The release observations do not change the zero-forward default-branch result or supply a new claim-specific source comparison.

## Limits and revalidation

No Dafny, Boogie, Silver, Silicon, Carbon, ViperServer, solver, or Anneal executable was installed or run. `runtime_result` is `unexecuted_in_this_review`; `anneal_product_result` is `unassessed`. No whole-repository archive or backend semantic audit was performed. The [offline checker](support/check_matrix.py) validates the exact frozen R389 claims, six independent source pins and blob snapshots, source/ref equality, release-tag peeling and ancestry metadata, and the 581-to-611 corpus reconciliation. It cannot refresh live refs or prove the original architectural judgment as product behavior.

Run `python3 reports/dafny-boogie-viper-current-source-review/support/check_matrix.py` from a checkout with the frozen corpus commits. A future version review should select each repository's exact successor independently and compare claim-mapped source on that forward line. Prompt/setup refinement: resolve all named repositories, preserve distinct Viper component pins, and treat an annotated release tag on a divergent line as a separate observation rather than a replacement for default-branch ancestry.
