# Anneal acceptance obligations and a replaceable trusted frontier

## Summary

Anneal's principles require mandatory UB-freedom, explicit trust, conservative failure and usable abstraction boundaries. A small logical checker can remove heuristic proof search from internal authority. It cannot alone justify Rust capture, semantic import, specification meaning, caller coverage or the final reported subject.

The PR #3846 stack implements a restricted admission and conditional-contract workflow with explicit compiler, importer, borrowing and external-interpretation premises. Its preserved-original-AST checks and failure-capable primitive models improve the observed boundary; they are not formal translation certificates or general unsafe-Rust operational adequacy. Eighteen admission controls pass against the exact source fixture suite in this report.

## Applicability

The current redesign subject is `google/zerocopy@8d8ed8dcc98c991d32cee3c3a84e129f29cba136`; its CLI implements setup only and labels V1 historical. The separate PR-stack subject is `cce761ad53785973ec2f4a6b13715b770b340c87`. Its selected Aeneas and Charon sources are `ca282ec2312a96f6a985a4d23a663690816d3f3e` and `cf02e3f228f97ee7be3a415be56989053063326d`. This report inspects downstream integration and the downstream lowering audit; it does not independently prove those upstream passes or rebuild the complete bundle.

The derived acceptance shape is a proposed formal interface, not a checked theorem about today's Anneal implementation. O01–O24 and all original question rationales are preserved in the sibling agenda package. R001/R002/R007, T061/T071/T118/T119 and P122/P144 receive architectural answers with an explicit current trust inventory. R012/T063–T068/P055–P064 receive a bounded capture/lowering analysis; verified parsing, typed elaboration and const-evaluation certificates remain unimplemented and unproved.

## Findings

### The required theorem fixes the source claim before accepting producer evidence

Let `Q` be a consumer-selected request containing a source/configuration subject, intended guarantees, accepted entry relation and permitted assumptions. Let `c` be arbitrary producer output. A proposed acceptance interface must establish these relationships:

```text
Accept(Q,c) implies:
  Checked(c)                         logical validity of the accepted evidence
  Bound(Q,c)                         same source, configuration, definitions and claim
  Assumptions(c) are permitted by Q  actual dependency closure, not labels alone
  Covered(Q,c)                       complete required operations, entries and outcomes
  Transfer(Q,c)                      modeled property entails the requested source property
```

The end-to-end theorem then concludes, under the *remaining* explicitly named trusted frontier, that every represented permitted source invocation satisfies mandatory finite-prefix safety and the selected additional guarantee. A total guarantee also requires progress/termination transfer. An unsafe API may declare caller requirements; a safe API may not silently restrict language-valid callers by choosing an incomplete decoder or an unproved ghost premise.

This factorization exposes engineering obligations. It is not itself a proof: `Covered` and `Transfer` must have definitions strong enough to exclude an omitted destructor, bad source branch, wrong instantiation or unrepresented incoming state. The premise cannot say that every internal access is already safe. That would assume the desired source-safety conclusion.

Basis: **normative**, Anneal principles/design contract; **derived**, proposed acceptance theorem and factorization.

### Current code supplies different parts of that interface

| Subject | Directly retained mechanism | Remaining claim boundary |
| --- | --- | --- |
| Main redesign | `Commands::Setup`; scanner/resolver code exists separately | No implemented redesign verification command is inferred from those modules |
| Historical V1 at main | `IsValid` predicate defaults to `True`; frontend/ABI/raw-pointer observations include axioms | Predicate checking and numerical facts do not imply complete Rust operational safety; V1 documents are not current design authority |
| PR-stack pure library | Layout, geometry, integer bytes and fixed-width initialized representations, with declared logical assumption policy | No physical allocation, pointer authority, storage event or Rust decoder-completeness theorem supplied by those values alone |
| PR-stack admission | Original imported ULLBC plus final LLBC; conservative effect/closure inspection and exact reviewed leaves | Inspection evidence from a trusted checker; rustc/importer/pass correctness remains an explicit premise |
| PR-stack contracts | Original raw calls, admitted mathematical inputs, requirements, total/partial WP and decoded outputs | Conditional invocation correctness; all safe clients and whole programs are not certified |
| PR-stack workflow | Fresh extraction, golden comparison, independent proof builds, compiled dependency audits, input checks | Soundness of binding, orchestration and final acceptance implementation is not formally proved here |

The pure library can be reused while changing frontends because its Rust correspondence premises stay with the consumer. V1's explicit ABI and raw-pointer assumptions can therefore remain scoped without contaminating the pure mathematical library's allowed-axiom set. This is a modular trust boundary; it is not removal of those assumptions from a V1 result that still uses them.

Basis: **source**, named implementation files; **documentation**, current/historical authority statements; **derived**, trust implications.

### Promoted MIR is an earlier inspection boundary, not verified source elaboration

`run.sh` selects promoted MIR, strict extraction and a patched Charon that saves imported unstructured ASTs before transformations. Admission follows function bindings and executable dependencies, including original dead/unwind blocks, and rejects drops before their relevant effects can disappear. The patch also rejects unavailable requested local MIR rather than falling back during admission. The pre-compilation input fingerprint is rechecked at binding and after proof checking.

This is stronger evidence than inspecting final LLBC alone. It still begins after Rust parsing, name resolution, expansion, type/borrow checking, constant processing and preceding MIR preparation. Earlier compiler erasure cannot be reconstructed by a final syntax check unless an independently justified original interpretation or certificate supplies it.

For a first certified representation, the choices have different residual premises:

- Source AST retains the earliest visible syntax, but requires certified resolution, elaboration, typing and implicit behavior to reach an executable semantics.
- Elaborated syntax or typed HIR reduces those obligations while trusting or certifying the stages producing it, including expansion and implementation selection.
- Promoted MIR offers executable structure and explicit operations, but retains compiler/importer and promotion/constant-processing premises.
- Later MIR or optimized code requires a relationship that retains source failures; ordinary preservation of already-defined executions can omit them.

A source digest binds bytes; it does not prove parsing or expansion. An AST schema check binds representation shape; it does not prove interpretation. A compiler typing judgment can justify only the exact guarantee established by that judgment. Each can remain an explicit initial trust premise with a replaceable certificate interface.

Basis: **source**, `run.sh`, `admission.py`, snapshot patch use; **documentation**, `ADMISSION_DESIGN.md` and `LOWERING_AUDIT.md`; **derived**, representation comparison.

### Failure exposure, entry coverage and specification adequacy remain independent

The stack's `.undef` primitive interpretations and total/partial judgments reject represented forbidden execution. Partial judgments permit divergence but still reject a bad operation before divergence. Guarded byte-copy, bit-validity and unchecked-arithmetic leaves preserve their failures; their source identities and generated failure-capable signatures participate in admission.

This establishes a useful model boundary only for represented operations. The downstream audit records missing general runtime storage events, destructor semantics, place-validity effects, source failure-kind distinctions, allocation effects and byte/provenance information. It also records which are rejected or remain supported under premises. Those gaps do not refute the proved numerical propositions; they constrain stronger Rust claims.

`SpecsSyntax.specBinding` requires the direct WP application to the original extracted function and original bound arguments. `abstractSpecContract` varies the execution outcome independently; `checkSpecContract` requires that complete abstract family to preserve the original premises and postcondition. This prevents selected forms of changed-goal or vacuous-family substitution. It does not establish that every permitted safe Rust caller satisfies the authored mathematical decoder, ghosts and requirements.

The invalid-source/safe-model and empty-decoder controls in sibling reports make the two distinctions concrete: valid target proof need not imply source safety, and valid conditional contract need not cover the requested caller population.

Basis: **source**, `SpecsSyntax.lean`, `SafetyTests.lean`, admission leaves; **documentation**, lowering audit; **derived**, semantic boundary.

### The trusted frontier can shrink component by component

| Initially trusted function | Candidate replacement evidence | Exact gate before claiming reduction |
| --- | --- | --- |
| Compilation-input selection | Checked input/configuration manifest with expansion/build provenance | Covers all effective inputs and selects the actually compiled subject |
| Parser/importer/elaboration | Verified implementation or per-run correspondence derivation | Connects consumer source bytes to the first formal representation |
| Transformation and analysis | Pass derivations plus semantic and admissibility theorems | Exposes every source failure and preserves observations/progress needed by the next stage |
| Memory/library interpretation | Proved operational rule and semantic contract | Adequate domain, frame, access and representation premises for the exact linked operation |
| Obligation generation | Checked derivation from program semantics to generated obligations | Mandatory safety/coverage cannot be omitted or weakened by user properties |
| Search/tactics/SMT | Proof terms, reflected checker witnesses or independently checked certificates | Exact original statement and all rule premises are checked |
| Aggregation/verdict wrapper | Checked closure/claim derivation and justified executable checker | No missing stage, stale artifact, tainted mode or operational failure becomes ordinary acceptance |

The producer may provide every candidate artifact and hint. The consumer must fix the requested subject and success meaning independently, then check the evidence. Independent checkers can reduce implementation risk but do not remove shared exporters, semantic assumptions, foreign encodings or a correlated wrong challenge.

The internally trusted component need not initially contain a complete Rust compiler. It may accept a narrow language and explicitly trusted capture frontier while rejecting unsupported behaviors. Extending that language should add proved rules and checked instances rather than granting new arbitrary producer assertions.

Basis: **derived**, constrained by the source and inspected certification systems; no proposed replacement is claimed implemented here.

### Measuring trust reduction requires more than trusted line count

Compare candidates along separate dimensions: code whose incorrectness can affect acceptance; semantic assumptions about Rust and the environment; privileges capable of bypassing checking; dependency/compiled-artifact closure; rule-extension and producer-change coupling; and evidence generation, storage, replay and revalidation cost.

A verified algorithm that still trusts reification and its compiled runtime differs from a per-run checked proof object. A small checker accepting powerful unrestricted axioms differs from a larger checker with constrained definitions. Removing optimizer heuristics can be valuable even when logical code size changes little. Moving an unchanged assumption to an upstream package changes ownership, not the dependency of the accepted theorem.

For each future gate, record the old unchecked proposition, replacement theorem, exact executable endpoint and residual assumptions. Count a reduction only when the accepted result ceases to rely on the old unchecked proposition. No numerical TCB-size or performance result was measured in this report.

Basis: **derived**, evaluation dimensions and acceptance criterion.

### Eighteen admission controls test the actual restricted implementation

The retained suite starts from the pinned original Boolean extraction fixture and mutates registration, executable closure, generic/supertrait dispatch, unsupported instantiation, drops/unwind cleanup, attributes/options, raw storage, invalid production, guarded signatures, compiler overrides, source inventory and mandatory snapshots. All 18 tests pass under Python 3.14.8 from an immutable private source archive.

The tests corroborate rejection sensitivity and supported fixture behavior. They are not an exhaustive schema/semantic audit, a verified admission implementation or an executed full compiler/proof pipeline. A few tests use mocked small source trees/configuration; the streams retain every test name so these can be distinguished from real fixture mutations.

Basis: **execution** + **source**, `support/admission-results.json`, complete streams and upstream fixture suite.

## Boundaries

- **Not established:** a checked aggregate acceptance theorem, a production isolated checking service, complete Rust semantics or removal of all Anneal code from outside users' TCB.
- **Not examined:** verified source parsing/elaboration, complete macro-generation ownership, independent rustc type/borrow certificates, or promotion/const-evaluation correctness.
- **Unknown:** optimal proof/certificate format, quantitative cost, cross-target matrix and proof maintenance for a final architecture.
- **Known scope:** the present contracts are conditional; a decoder or ghost premise may restrict inputs. The all-safe-client obligation needs additional evidence.
- **Not established:** full upstream pass soundness from downstream documentation, a hash, golden equality or these 18 controls.
- The source-inspected design and proposed gates are separate from implementation evidence. Prototypes may answer feasibility without becoming architecture policy.

## Evidence

- **normative:** [Anneal principles](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/PRINCIPLES.md), mandatory safety and conditional trust promise; [design contract](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/DESIGN.md), claim meaning, correspondence, abstraction and explicit trust.
- **source:** main `anneal/src/main.rs:30–32,95`; `anneal/v1/src/Anneal.lean`, `IsValid`, ABI/layout and raw-pointer axioms; current README's historical-V1 authority qualification.
- **source:** PR-stack `verification/aeneas/run.sh`, `admission.py:788–947`, `workspace.py:191–259`, `lean/SpecsSyntax.lean:280–385`, `lean/SafetyTests.lean`.
- **documentation:** PR-stack `ADMISSION_DESIGN.md`, `SEMANTICS.md`, `LOWERING_AUDIT.md` and `anneal/lean/README.md`. Upstream behavior discussed through that audit is not independently revalidated by this package.
- **execution:** `support/run_admission_controls.py`, source hashes, immutable archive hash, Python identity, status and complete 18-test output. No invalid Rust was executed by these tests.
- **derived:** proposed acceptance factorization, trust gates, capture alternatives and evaluation dimensions. These are research conclusions rather than new proved source semantics.

## Revalidation

Run `python3 -B support/run_admission_controls.py /path/to/zerocopy-clone`. Reinspect the current root-selection, pre/post snapshots, external registry, signature guards, input identity and final verification path before assigning a changed source snapshot the same frontier.

For a proposed architecture, freeze a consumer-owned request and mutate source/model/property/assumption/dependency/configuration identities independently. Obtain a theorem for each claimed trust reduction, then verify the actual execution path to its accepted result. A source-safety transfer must reject a discarded UB guard, a narrowed safe-caller domain, an omitted effectful callee and a changed required guarantee. Treat any unsupported input or incomplete checking as a distinct result, preserving the ordinary successful claim.

*Authored by an AI agent acting on joshlf's behalf.*
