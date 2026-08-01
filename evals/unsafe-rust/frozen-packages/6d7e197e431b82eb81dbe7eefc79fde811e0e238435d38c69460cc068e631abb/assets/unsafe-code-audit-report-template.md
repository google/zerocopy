# Unsafe Rust Audit: `<project / scope>`

## Claims and Verdicts

| Claim ID | Exact theorem | Required-domain ID | Verdict | Certificate/proof/finding | TCB and qualification |
|---|---|---|---|---|---|
| `<CLAIM-SOUND-...>` | `<source- or binary-level absence-of-UB theorem>` | `<DOMAIN-...>` | `<PROVED / UNPROVED / UNSOUND>` | `<closure proof or finding IDs>` | `<TCB + assumptions>` |
| `<CLAIM-POST-...>` | `<documented postcondition>` | `<DOMAIN-...>` | `<PROVED / UNPROVED / CONTRACT-BROKEN>` | `<closure proof or finding IDs>` | `<TCB + assumptions>` |
| `<CLAIM-APP-...>` | `<conditional deployment/security/probabilistic theorem, or omit>` | `<DOMAIN-...>` | `<exact qualified result>` | `<proof/finding IDs>` | `<explicit conditional TCB>` |

- **Combined mandatory result:** `<PROVED only if every in-scope soundness and
  mandatory documented-postcondition obligation is proved; otherwise list all
  applicable component verdicts and finding IDs>`
- **Scope:** `<APIs/modules/packages/binaries>`
- **TCB log:** `<ID/revision/link>`
- **Skill revision:** `<unsafe-rust revision>`

## Audited Snapshot

- **Repository/source:** `<URL/path + revision/digest>`
- **Uncommitted changes:** `<identity or none>`
- **Generated/expanded artifacts:** `<identities/digests/locations>`
- **Rust/compiler/stdlib:** `<versions and range>`
- **Dependencies:** `<lockfile/resolution/source identity>`
- **Build inputs/tools:** `<relevant versions, environment, generators>`
- **Prior audit reused:** `<ID/revision or none>`
- **Auditor/reviewer/date:** `<identity>`

## Contracts in Scope

### Soundness

`<State valid uses/executions and the exact absence-of-UB theorem.>`

### Documented Postconditions

| Contract ID | API/entrypoint | Preconditions | Postconditions | Source/version |
|---|---|---|---|---|
| `<CONTRACT-...>` | `<item>` | `<P>` | `<Q>` | `<link/quote location>` |

### Additional Robustness Claims

| Claim ID | Exact proposition | Scope and authority | Result | Evidence/finding |
|---|---|---|---|---|
| `<ROBUST-...>` | `<claim>` | `<scope/contract/request>` | `<exact result>` | `<proof/finding IDs>` |

`<Write “none” if no additional robustness claim is in scope.>`

## Boundary and API Coverage

| Surface ID | Item/generated family | Safe/unsafe | Construction/access path | Configuration scope | Contract/proof status |
|---|---|---|---|---|---|
| `<API-...>` | `<item>` | `<safe/unsafe>` | `<how reached>` | `<scope>` | `<status/link>` |

Confirm coverage of:

This is a mandatory minimum, not an exhaustive surface list. Apply
[Enumerate every surface](../references/api-boundaries-and-evolution.md#enumerate-every-surface)
and record every additional language-reachable surface in the table above.

- [ ] safely accessible representation across the owning-module boundary,
      including `pub(super)`, `pub(crate)`, ancestor-visible, and generated
      access;
- [ ] public fields;
- [ ] constructors;
- [ ] safe methods;
- [ ] safe trait methods and caller-provided implementations;
- [ ] macros and macro-generated APIs;
- [ ] reexports and configuration-specific APIs;
- [ ] language-reachable `#[doc(hidden)]` safe items;
- [ ] associated items, safe free functions/statics, callbacks, FFI entrypoints,
      blanket/default/auto-trait behavior, operators, and destruction whenever
      language-reachable or semantically relevant.

## Invariant Inventory

| Invariant ID | Exact proposition | Owner/boundary | Must hold when | Producers/mutators | Consumers | Status |
|---|---|---|---|---|---|---|
| `<INV-...>` | `<predicate>` | `<module/type/field/etc.>` | `<interval>` | `<locations>` | `<locations>` | `<status>` |

## Obligation Ledger

| Obligation ID | Source/API | Exact proposition | Required domain | Derivation, material premises, and their applicability | Covered domain/cases | Proof location | Reviewer | Status |
|---|---|---|---|---|---|---|---|---|
| `<OBL-...>` | `<location>` | `<goal>` | `<required applicability>` | `<facts/invariants/TCB + domains>` | `<scope/partition>` | `<link>` | `<identity>` | `<status>` |

## Theorem-Domain and Configuration Closure

### Required Domain Recovery

| Step ID | Controlling source expression or prior predicate | Derived predicate/inventory/partition | Relation to prove (write symbolically) | Required certificate: containments/witnesses/derivation | Status |
|---|---|---|---|---|---|
| `<DOMAIN-...>` | `<exact source + expression>` | `<symbolic result>` | `<exact symbolic relation, e.g. derived = source or Required ⊆ union(cases)>` | `<derivation and source>` | `<proved / unresolved>` |

- **Audit cutoff:** `<date/revision and effect on dynamic policies>`
- **Exact `Required` predicate:** `<symbolic definition or link>`
- **Configuration projection:** `<Required_cfg(configuration)>`
- **Policy conflicts/authorized resolution:** `<conflicts, decision, or
  conservative audit domain without calling it the project promise>`
- **Unresolved domain:** `<none or exact remainder/finding IDs>`

### Build and Generation Pipeline

`<Use this table for a materially nontrivial claim-relevant build, generation,
expansion, linking, or artifact-selection pipeline. Otherwise record the simple
selection facts in the obligation ledger.>`

| Stage ID | Input/state region and predecessor | Ordered operation or transformation | Successful output/effect | Alternative exit and partial effects | Authority/TCB and applicability | Consumer |
|---|---|---|---|---|---|---|
| `<STAGE-...>` | `<exact cases in which reached>` | `<local source step or tool transition>` | `<exact consumed value/cardinality/identity/order, or universal output property>` | `<claim-relevant failure/rejection/other exit; later steps not reached>` | `<source proof + exact semantic premise>` | `<next stage/obligation>` |

- **Freshness/invalidation:** `<input-change to rerun/cache/output identity
  relation, or why irrelevant>`

### Covered Domain

- **Discovered axes:** `<features, cfg, targets, architectures, OSes, SIMD,
  allocators, debug assertions, panic modes, generated output, and other actual
  axes>`
- **Configuration-fiber proof:** `<how every full Required case in each
  Required_cfg fiber reaches its exact artifact/source or other in-scope build
  outcome, with findings for any remainder>`
- **Exact full-case `Covered` predicate:** `<union valid case regions within
  each obligation, then intersect across all claim-required obligations>`
- **Coverage proof:** `<parametric argument, justified exhaustive partition,
  justified finite enumeration, generator proof, or combination>`
- **Closure certificate:** `<proof of Required ⊆ aggregate Covered, or finding
  ID>`
- **Version-spanning premise basis:** `<parametric proof, exhaustive applicable
  cases, exact compatibility entry, or unresolved>`
- **Generated artifacts:** `<identity/proof>`
- **Enforced exclusions:** `<how unsupported combinations cannot ship>`
- **Sampled/tested configurations:** `<list and exact limited evidence provided>`
- **Uncovered full cases/configurations:** `<none or finding IDs>`

## TCB Summary

| Category | Entry IDs | Human disposition | Material limitations |
|---|---|---|---|
| `<category>` | `<IDs>` | `<accepted/rejected/pending>` | `<limitations>` |

Full log: `<link/ID>`

## Tool-Derived Evidence

| Proof ID | Proposition and entailment | Artifact/tool/model/options | Quantification and bounds | Non-vacuity and semantic fidelity | Trust, stubs, and residual TCB | Result/certificate | Consumers |
|---|---|---|---|---|---|---|---|
| `<TOOL-PROOF-...>` | `<exact theorem and why it implies the obligation>` | `<identities>` | `<scope/bounds/completeness>` | `<reachability + source/model correspondence>` | `<trusted functions/models/components + TCB IDs>` | `<terminal result/link/digest>` | `<obligation IDs>` |

## Findings

### `<FINDING-ID>` — `<short title>`

- **Status/severity:** `<UNPROVED / UNSOUND / CONTRACT-BROKEN / other>`
- **Implementation classification:** `<verdict/status for the implementation
  obligation>`
- **Proof-artifact classification:** `<adequate / deficient / missing / not
  applicable>`
- **Affected claim:** `<soundness/postcondition/compatibility/etc.>`
- **Source/API/configuration:** `<exact scope>`
- **Required proposition:** `<goal>`
- **Existing proof or behavior:** `<what was claimed/implemented>`
- **Reconstructed derivation:** `<material proof missing from the reviewed
  artifact, with citations/applicability; or none>`
- **Proposed proof-artifact repair:** `<replacement comment/canonical proof, or
  none>`
- **Defect:** `<smallest missing, false, circular, or unsupported implication>`
- **Authority/TCB involved:** `<citations/IDs>`
- **UB certificate — valid use:** `<why the use/execution is valid and in scope,
  or “not established”>`
- **UB certificate — reachability:** `<executed operation or semantic event,
  or “not established”>`
- **UB certificate — false safety proposition:** `<exact required clause and
  derivation of its falsity, or “not established”>`
- **UB certificate — consequence:** `<applicable authority/TCB derivation to
  UB, or “not established”>`
- **Defined postcondition refutation:** `<valid UB-free witness or equivalent
  proof that an in-scope UB-free execution falsifies the postcondition, or “not
  established”>`
- **Affected producers/consumers:** `<IDs/locations>`
- **Required resolution:** `<minimum proof, contract, implementation, privacy,
  configuration, or TCB change>`
- **Compatibility impact:** `<SemVer/contract implications>`
- **Re-audit scope:** `<what must be revisited>`

## Abstraction Design (Optional)

`<Omit unless design or redesign was requested. Preserve the current-artifact
findings above unchanged.>`

- **Required behavior and constraints:** `<exact consumer propositions,
  compatibility commitments, support domain, and authorized changes>`
- **Current literal result:** `<scoped finding/verdict, unchanged by proposal>`
- **Recommended candidate:** `<proposed contract, representation, and boundary>`
- **Proof simplification:** `<obligations and TCB premises eliminated,
  localized, or retained>`
- **Behavior delta:** `<behavior or guarantees added, lost, or unchanged>`
- **Compatibility and migration:** `<contract delta, affected parties, plan>`
- **Fresh-audit status:** `<not implemented / new snapshot + separate verdict>`

## Documentation and Skill Gaps

### Authoritative Rust Documentation

| Gap ID | Missing/ambiguous proposition | Attempted authoritative sources | Blocked obligations | Suggested upstream report |
|---|---|---|---|---|
| `<DOC-GAP-...>` | `<proposition>` | `<links>` | `<IDs>` | `<action>` |

### Skill Guidance

| Gap ID | Omission or ambiguity | Audit impact | Proposed maintainer follow-up |
|---|---|---|---|
| `<SKILL-GAP-...>` | `<gap>` | `<impact>` | `<action>` |

## Residual and Excluded Scope

`<List every inaccessible, unaudited, unsupported, conditionally proved, or
explicitly excluded region. Explain enforcement of exclusions.>`

## Re-audit Triggers

- `<source or contract changes>`
- `<configuration/support changes>`
- `<Rust or authoritative documentation changes>`
- `<dependency, generator, tool, TCB, environment, or agreement changes>`
- `<new incident or discovered obligation>`

## Final Attestation

- [ ] Every in-scope obligation has a status.
- [ ] Every conclusion used by a verdict or regional result and every claimed
      set relationship satisfies [Make every derivation
      reviewable](../references/proof-obligations.md#make-every-derivation-reviewable).
- [ ] Every controlling domain expression is preserved, and every asserted set
      relationship, normalization, enumeration, partition, merge, or exclusion
      has the certificate required by its exact relation.
- [ ] Every materially relevant build/generation path records required order,
      exits, and partial progress and proves each consumed tool-interpretation,
      output, and freshness proposition; no later-stage fact is used on a path
      that exited earlier.
- [ ] Every verdict has the certificate required by `SKILL.md`, including
      `Required ⊆ Covered` for `PROVED` and every existential link for
      `UNSOUND` or `CONTRACT-BROKEN`.
- [ ] Every material derivation reconstructed during review is exposed with its
      applicability, and deficient proof artifacts are reported separately.
- [ ] Every material semantic premise appears in the authority/TCB inventory,
      and every consumed citation and TCB entry was independently verified.
- [ ] Every consumed TCB entry supporting `PROVED` has an accepted human
      disposition.
- [ ] Every mandatory documented postcondition was reviewed in addition to UB
      freedom.
- [ ] Residual scope and conditional assumptions are conspicuous.
- [ ] The final verdict does not rely on lack of a counterexample or clean tests.

**Auditor:** `<identity>`  
**Independent reviewer (if performed):** `<identity or not performed>`  
**Date:** `<date>`
