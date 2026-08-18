# TCB Audit Log: `<project / audit>`

## Identity

- **Log ID/revision:** `<stable ID or digest>`
- **Audit/report:** `<link or ID>`
- **Skill revision:** `<unsafe-rust revision>`
- **Source snapshot:** `<repository + revision/digest>`
- **Generated artifacts:** `<identities/digests>`
- **Rust/toolchain scope:** `<versions>`
- **Supported configuration predicate:** `<certified domain ID/link in audit
  report>`
- **Theorem(s) supported:** `<exact soundness, postcondition, binary, or
  application claims>`
- **Owner/reviewer:** `<names or roles>`
- **Reviewed at:** `<date>`

## Trust Policy

`<State which premises may be admitted, the selected-safe-dependency policy,
the treatment of third-party unsafe APIs, and what kind of verdict this TCB can
support.>`

## Entry Index

| ID | Category | Exact trusted proposition | Identity/version | Scope/configurations | Contract channel | Consumers | Disposition | Re-audit trigger |
|---|---|---|---|---|---|---|---|---|
| `<AXIOM-...>` | `<category>` | `<one precise proposition>` | `<version/digest>` | `<quantification>` | `<authority/contract>` | `<proof IDs>` | `<accepted/rejected/pending>` | `<event>` |

## Detailed Entries

### `<ID>` — `<short name>`

- **Category:** `<AXIOM / SAFE-DEP / UNSAFE-DEP / EXTERNAL-SPEC /
  IMPLEMENTATION / TOOL / ENVIRONMENT/DEPLOYMENT / CRYPTO/PROBABILISTIC /
  OUT-OF-BAND / project category>`
- **Disposition:** `<accepted / rejected / pending / superseded>`
- **Exact proposition:** `<the smallest proposition accepted without further
  in-scope proof>`
- **Quantification and scope:** `<inputs, executions, exact release/version
  regions, targets, configurations, APIs, and time interval>`
- **Exact identity:** `<document URL + version, package + version/source,
  revision/digest, binary, model, tool, agreement, or environment>`
- **Source/contract:** `<narrow link, document section, agreement, audit, or
  other contract source>`
- **Relevant quotation:**  
  > `<minimum exact quotation, when a textual contract supplies the fact>`
- **Contract relationship:** `<Rust authority / SemVer range / exact pin /
  Rust backwards-compatibility commitment / in-tree fork / out-of-band
  agreement / consumer-specific promise / external specification / deployment
  condition / other>`
- **Why needed:** `<which proof cannot proceed without this proposition>`
- **Why admission is permitted:** `<project policy, authorized trust decision,
  contract relationship, or other basis for accepting rather than proving it>`
- **Consumers:** `<obligation and proof IDs>`
- **Verification performed:** `<citation check, source audit, certificate check,
  artifact digest, configuration check, human review, etc.>`
- **Residual trusted components:** `<implementation, translation, model, solver,
  proof checker, foreign system, parties, or none>`
- **Known limitations:** `<unsupported cases, bounds, ambiguity, expiration, or
  none>`
- **Owner/approver:** `<human or role authorized to accept this premise>`
- **Re-audit trigger:** `<version/configuration/contract/tool/environment change
  or date>`
- **Notes:** `<only information necessary to apply or review the entry>`

## Dependency Contract Summary

| Dependency | Safe/unsafe surface | Exact behavior relied upon | Contract relationship | Features/configuration | Implementation audit or TCB entry | Update trigger |
|---|---|---|---|---|---|---|
| `<package/source>` | `<surface>` | `<proposition>` | `<SemVer / pin / fork / agreement / other>` | `<scope>` | `<proof or ID>` | `<event>` |

## Rejected or Unresolved Premises

| Proposed ID | Proposition | Reason rejected/unproved | Blocked obligations | Required resolution |
|---|---|---|---|---|
| `<ID>` | `<claim>` | `<missing authority/proof>` | `<IDs>` | `<action>` |

## Review Attestation

- [ ] The audit's material semantic premises were reconciled against this
      index; every Rust axiom or admitted proposition it consumes appears with
      its exact source and applicability.
- [ ] Every consumed entry has an exact proposition rather than a vague trust
      statement.
- [ ] No entry merely assumes an in-scope conclusion or trusts code the declared
      audit scope purports to prove.
- [ ] Every identity, version, digest, and configuration scope was checked.
- [ ] Every quotation was opened and verified in context.
- [ ] Selected safe dependencies are distinguished from caller-controlled code.
- [ ] Exact pins are used only to freeze identity; every undocumented
      proposition has an audit, additional contract, or explicit admission.
- [ ] Every third-party unsafe implementation is recursively audited or
      explicitly admitted.
- [ ] Every version-spanning compatibility entry states the exact proposition
      preserved and its exact release/configuration region; pins, stability
      badges, and sampled documentation are not used as interval coverage.
- [ ] Tool-derived facts state their exact theorem and residual TCB.
- [ ] External, deployment, and probabilistic assumptions qualify the verdict
      conspicuously.
- [ ] Every entry has consumers and a re-audit trigger.
- [ ] Every consumed entry supporting `PROVED` is explicitly accepted; pending,
      rejected, and superseded entries support no proved claim.
- [ ] Rejected and unresolved premises appear in the audit findings.

**Reviewer:** `<name/role>`  
**Review result:** `<accepted / rejected / incomplete>`  
**Date:** `<date>`
