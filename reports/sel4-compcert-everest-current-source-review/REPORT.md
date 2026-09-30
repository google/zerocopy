# R507 and R578 seL4, CompCert, and Everest current-source review

## Summary

The [matrix](support/matrix.json) freezes two distinct reports at reference `47d8250bff3ea17f1fbb4340370032e03692617b`: R507's proof-maintenance comparison across seL4, CompCert, and Project Everest, and R578's narrower CompCert 3.18 pass-composition analysis. Five of their six official repository default branches still point to the exact pins in R507. [`AbsInt/CompCert` `master`](https://github.com/AbsInt/CompCert/commit/66a9fd06ef88619cc94765ca995a1018f7259b5c) is four commits forward of the shared R507/R578 source pin [`74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`](https://github.com/AbsInt/CompCert/commit/74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6). Its complete five-path comparison does not include the three exact CompCert files cited by either report; those files retain their Git blob IDs. This establishes narrow source continuity for the mapped files, not proof replay or end-to-end semantic equivalence.

## Frozen rows and source lines

The original selectors are R507 and R578 in the 581-report version inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The frozen parent has 613 report packages; all 32 additions are reconciled by path and hash. R507 and R578 retain separate exact Summary excerpts, Findings locators, report subjects, source maps, and support JSON hashes. R578's inventory classification was `no_newer_release`; that historical classification is preserved. The currently observed CompCert GitHub Release remains `v3.18`, while development `master` has four later commits. A later development commit is not a new official release.

The [official-source observation](support/official-source-observation.json) keeps six repositories separate, with raw refs, old/current commit identity, changed-path lists and claim-mapped source snapshots:

| Source line | Exact report claim-mapped files | Observed source result |
| --- | --- | --- |
| [`seL4/l4v`](https://github.com/seL4/l4v/commit/6b4076aeb35f7803b7c232963e5f996545e3acb5) | `README.md`, `docs/setup.md` | `master` equals R507 pin; both blobs match. |
| [`seL4/verification-manifest`](https://github.com/seL4/verification-manifest/commit/f1f7a4289585e9610733ea041c1849e46af9701b) | `README.md` | `master` equals R507 pin; blob matches. |
| [`AbsInt/CompCert`](https://github.com/AbsInt/CompCert/commit/66a9fd06ef88619cc94765ca995a1018f7259b5c) | `VERSION`, `common/Smallstep.v`, `driver/Compiler.v` | Four commits forward; all three original 3.18 blobs match current `master`. Shared by R507 and R578, but their claims remain distinct. |
| [`hacl-star/hacl-star`](https://github.com/hacl-star/hacl-star/commit/504c2987452f87fe44bce9b9f12e19d6e051761f) | `README.md` | `main` equals R507 pin; blob matches. |
| [`FStarLang/karamel`](https://github.com/FStarLang/karamel/commit/9abbb865b10a0cd5c557da81c024c3965cb6ff53) | `README.md`, `DESIGN.md` | `master` equals R507 pin; both blobs match. |
| [`project-everest/everest`](https://github.com/project-everest/everest/commit/2a3f67dab56be02d1793b2801ef08f368423a3ac) | `README.md` | `master` equals R507 pin; blob matches. |

All ten files are preserved under [`support/snapshots/`](support/snapshots/) with Git blob SHA-1, content SHA-256, and commit-pinned source URL recorded in the observation. The five changed CompCert paths are `cfrontend/CPragmas.ml`, `common/Switch.v`, `common/Switchaux.ml`, `cparser/Lexer.mll`, and `test`; this review did not trace their full impact on CompCert. In particular, unchanged `Smallstep.v` and `Compiler.v` do not prove that current `master` preserves every R507 or R578 theorem in execution.

## Release observations and ancestry

GitHub `releases/latest` returned [seL4 L4.verified `seL4-16.0.0`](https://github.com/seL4/l4v/releases/tag/seL4-16.0.0), [CompCert `v3.18`](https://github.com/AbsInt/CompCert/releases/tag/v3.18), [HACL repository `ocaml-v0.4.5`](https://github.com/hacl-star/hacl-star/releases/tag/ocaml-v0.4.5), and [KaRaMeL `v0.9.6.0`](https://github.com/FStarLang/karamel/releases/tag/v0.9.6.0). The raw tag snapshots peel annotated refs before comparing commits. Their release commits precede the respective report pins by 92, 14, 2,898, and 3,002 commits. The HACL repository's `ocaml-v0.4.5` tag names an OCaml component and is not evidence of a newer HACL* library release. The verification-manifest and Everest integration repositories returned 404 at `releases/latest`; no GitHub Release object was identified for either.

These release refs are separate from the observed default-branch source lines. In particular, CompCert `v3.18` is still the endpoint's latest release even though development `master` is four commits ahead of the R507/R578 3.18 source pin.

## Limits and revalidation

No seL4 proof, CompCert theorem, HACL* proof, KaRaMeL extraction, Everest integration, compiler, or Anneal product was installed or executed. `runtime_result` is `unexecuted_in_this_review`; `anneal_product_result` is `unassessed`. No full repository archives were acquired. The [offline checker](support/check_matrix.py) verifies exact frozen report rows and source maps, six independent ref/release identities, CompCert ancestry/changed-path exclusion, preserved source blobs, and 581-to-613 corpus reconciliation. It cannot refresh upstream or establish proof validity.

Run `python3 reports/sel4-compcert-everest-current-source-review/support/check_matrix.py` from a checkout containing the frozen corpus commits. If a later decision depends on current proof maintenance or pass composition, inspect the exact changed CompCert dependencies and replay pinned proof/build configurations under a separately admitted experiment. Prompt/setup refinement: keep multi-repository proof stacks and shared CompCert evidence as separate graph nodes, and distinguish a development-branch successor from the latest released version.
