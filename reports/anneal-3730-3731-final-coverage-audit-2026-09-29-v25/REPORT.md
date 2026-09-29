# #3730/#3731 coverage audit v25: suggestion review and native plugin boundary

## Summary

The [v25 333-row challenge](support/row-challenge-v25.json), [159-investigation ledger](support/investigation-final-v25.csv), and [174-suggestion crosswalk](support/3730-crosswalk-final-v25.csv) incorporate the complete [post-publication suggestion audit](../anneal-3730-174-suggestion-postpublication-native-trust-audit-2026-09-29/REPORT.md) into [v24](../anneal-3730-3731-final-coverage-audit-2026-09-29-v24/REPORT.md). V24 and earlier reports remain dated records. V25 preserves all **345 exact destination links**, all statuses, and every prior v24 field. It adds the independent audit's original-request hash, full-scope decision, cached-only availability finding, evidence relationship, cited packages, residual and prerequisite to **each of the 174 suggestion rows**.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

Only **G09, I126, and I127** receive new residual wording. Their statuses remain partial, and no next prerequisite changes. I005's matched fake-backend replay, I076's same-name Charon LLBC collision, I126's earlier Lake configuration control, I127's first owned-path diagnostic, and I145's cross-layer identity implication remain linked through inherited v24 evidence and the [three range audits](support/source-package-inventory-v25.csv).

## Applicability

The base is published `reference@9d2426519c7eaaf58b13b109a2f4c16d84c51616`. Public [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731) bodies and comments were reread on 2026-09-29; their [live hashes](support/live-issue-hashes.json) match both v24 and the frozen source snapshot. #3730 was closed as a consolidation backlog, while #3731 remained open. Neither issue status is evidence that an investigation was completed.

The independent audit retained all 174 original #3730 request blocks and the #3731 crosswalk comment, checked each exact heading/text hash and 345 destination links, and examined 111 cited report packages. Its per-ID table distinguishes partial evidence from entire-request completion. The three complete suggestions remain C04, C13 and N11 at their specified direct-Lean or falsification scope; five distinguishing methods remain not-run and four conditional. The v25 [builder](support/build_audit.py) copies every v24 row, verifies these per-ID decisions, and overlays only new fields and the three supported residual refinements. It neither fetches nor changes source packages.

## Findings

The new [native plugin trial](../anneal-3730-174-suggestion-postpublication-native-trust-audit-2026-09-29/REPORT.md) extends I126's execution inventory. A pinned Lean 4.30.0-rc2 native plugin initializer wrote an owned outside-workspace marker when allowed under a network-denied sandbox. A targeted macOS write denial made the plugin proof exit 1 without the marker, while a no-plugin proof under the same denial exited 0. An earlier wrong-basename plugin attempt was excluded because Lean did not load that initializer; only the corrected three-case trial supports this finding. This establishes one native-extension execution and denial control, alongside the prior Cargo, Lean `run_cmd`, and Lake configuration controls. It does not establish full containment, resource policy, user authorization, or Anneal's trust-entry behavior. **I126 stays partial.**

The raw native-plugin denial named an absolute owned scratch path. Together with the earlier Lake denial, this supports a narrow I127 path-exposure observation; both report summaries normalize the owned root. No private source, credential, or product-log leakage test was run. **I127 stays partial.** The native control is directly relevant to G09's read-only versus mutating MCP tool taxonomy, so its residual now names both Lake and plugin writes and denials. An actual Anneal MCP broker, tier enforcement and untrusted-workspace authorization remain missing. **G09 stays partial.**

The other 173 suggestion residuals and all 174 prerequisites match v24. The ten suggestions linked to I145 still use I076's name-only identity witness as bounded evidence, D07 still links the I076 LLBC fixture directly, and no #3730 suggestion directly targets I005 or I127. Every v25 suggestion row cites the new independent audit's decision table; G09 additionally cites the retained native result and raw denial stream. The new audit found no other distinct cached-only experiment for an exact remaining suggestion gate. Its `entire_requested_scope_supported` field is true only for C04, C13 and N11.

## Boundaries

- The native sandbox denied writes to one owned outside directory and network access for the retained fixture. It does not prove broad native-code isolation, ABI safety, or safety when opening an arbitrary untrusted project.
- The owned absolute path in the denial stream demonstrates a disclosure channel for paths, not disclosure of private source or credentials.
- The new audit's per-ID availability conclusions are scoped to the pinned local tools and cited corpus. They do not establish that a later adapter, archive, toolchain, host, or consenting study cannot be supplied.
- No current integrated Anneal V2 verification, LSP, MCP, prepared-archive or claim-acceptance workflow is established by these component probes.

## Evidence

The [validation manifest](support/validation-v25.json) hashes the v24 source rows, live issue read, independent 174-row decision table, four derived files, status counts, and changes. The [source inventory](support/source-package-inventory-v25.csv) hashes **72 substantive files** across v24, the three range audits, and the suggestion/native audit, excluding Python bytecode caches. Their own checkers retain and validate the fake-backend schedule, two Charon LLBC outputs, Lake execution/denial cases, original suggestion blocks, three native plugin cases, and the excluded wrong-basename attempt. The [v25 checker](support/check.py) validates the exact 159/174 titles, 345 destination links, 174 per-suggestion decisions and full source inventory, and invokes the source package checkers/loaders offline.

## Revalidation

Run `python3 -B support/check.py` from this package. It is read-only and offline. The builder can regenerate v25's derived files deterministically, writing only inside this package. A future publication candidate must update CATALOG for the new packages before `tools/reference.py check` can pass; v25 itself does not edit CATALOG or an earlier report.
