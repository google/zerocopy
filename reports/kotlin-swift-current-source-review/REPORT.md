# R410 Kotlin FIR and Swift SourceKit current-source review

## Summary

The [R410 matrix](support/matrix.json) freezes the exact four `## Summary` paragraphs, six source-map claims, original subjects, report/evidence bytes, and claim-to-file mapping at reference `0acbffd307e1d4288d784055f9883dd9fa5fd3b9`. Official Kotlin `master` is 106 commits forward from R410's pin, Swift compiler `main` is 36 commits forward, and SourceKit-LSP `main` still equals its pin. The 11 claim-mapped old/current Git blobs are unchanged. This is a **bounded source-file result**: it does not establish whole-project semantic continuity, runtime behavior, or any Anneal product guarantee.

## Three independent source histories

| R410 component | Exact old source | Selected official default-branch source | Relation |
| --- | --- | --- | --- |
| Kotlin FIR/Analysis API | [`JetBrains/kotlin@bce49f3701fb8dc461fb98240fdc7c3c81c592f2`](https://github.com/JetBrains/kotlin/commit/bce49f3701fb8dc461fb98240fdc7c3c81c592f2) | [`master@79b33f2836ef88425c100924bb8d29bcdf52bf48`](https://github.com/JetBrains/kotlin/commit/79b33f2836ef88425c100924bb8d29bcdf52bf48) | 106 ahead, zero behind. |
| Swift SourceKit-LSP | [`swiftlang/sourcekit-lsp@045c18e9e9ea35b896857b6cb982aa2373fb5816`](https://github.com/swiftlang/sourcekit-lsp/commit/045c18e9e9ea35b896857b6cb982aa2373fb5816) | Same `main` commit | No forward source revision. |
| Swift compiler SourceKit | [`swiftlang/swift@f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d`](https://github.com/swiftlang/swift/commit/f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d) | [`main@0fcad6fb60755587d39a758761b219bf433cf9dc`](https://github.com/swiftlang/swift/commit/0fcad6fb60755587d39a758761b219bf433cf9dc) | 36 ahead, zero behind. |

The three repositories and their pins are separate. A newer Swift compiler commit does not imply a newer SourceKit-LSP server; its source ref remained at `045c18e9…`. The original selector is R410 in the 581-row version inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. The frozen reference has 601 report packages, with all 20 additions reconciled and hashed in the matrix.

## Claim-mapped source findings

R410's [evidence map](../kotlin-swift-compiler-backed-ide-boundaries-2021-2026/evidence-map.json) has six exact claims. The matrix preserves them verbatim and maps each source claim to commit-pinned files:

- **Kotlin project and session authority (claims 1–2).** `KaModule.kt`, `KaFirSessionProvider.kt`, `KaSession.kt`, and `compiler/fir/checkers/module.md` have identical old/current Git blob SHA-1 values. This is source continuity in those files, including the module-context and lazy-session material R410 cited. It does not verify that all dependencies or runtime session invalidation behave identically.
- **Kotlin generated/plugin semantics (claim 3).** `KaResolveExtension.kt` and `KaSymbol.kt` have identical old/current blobs. The review did not run a plugin or generated-source fixture.
- **SourceKit-LSP build-system handoff (claim 4).** `Contributor Documentation/Implementing a BSP server.md` and `README.md` remain at the exact old server commit; there is no forward LSP code to compare.
- **Swift compiler AST reuse and LSP recovery (claim 5).** Swift compiler `SwiftASTManager.h` and `cursor_reuses_astcontext.swift` have identical old/current blobs across the 36-commit compiler range. SourceKit-LSP `Documentation/Configuration File.md` remains at the old server commit. The compiler test was inspected as source and not executed.
- **Anneal inference (claim 6).** This remains derived architecture analysis, not a source or product result.

Official GitHub compare metadata returned the complete 246-file list for the Swift compiler range; neither mapped compiler file appears in it. Kotlin's repository-wide comparison returned the 300-file API cap, so this report makes **no complete Kotlin changed-path claim**. It independently read each mapped Kotlin file at both exact commits and recorded Git blob SHA-1, content SHA-256, and size in the [official-source observation](support/official-source-observation.json). Those direct file snapshots support only the six mapped-file continuity result. The SourceKit-LSP same-commit result follows from its official ref and identical source bytes.

## Boundaries and revalidation

No Kotlin or Swift compiler, FIR/Analysis API session, SourceKit-LSP server, sourcekitd process, build server, or Anneal product was installed or executed. The matrix records `runtime_result: unexecuted_in_this_review` and `anneal_product_result: unassessed`. No full source archive was acquired. The [offline checker](support/check_matrix.py) validates exact frozen claims and map bytes, corpus reconciliation, official compare/ref observations, mapped file identities, and separate component statuses. It cannot refresh upstream refs or prove runtime equivalence.

Run `python3 reports/kotlin-swift-current-source-review/support/check_matrix.py` from a checkout containing the frozen corpus commits. A stronger review would trace changes through each claim's dependent call paths, compare a later SourceKit-LSP revision if one appears, and run version-pinned semantic/build fixtures. Prompt/setup refinement: require full repository-plus-commit identities for compiler and server, retain the source-map's six claim clauses, and treat compare API caps as a reason to narrow conclusions to directly inspected blobs.
