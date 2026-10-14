# Property-proof translation and independently preserved specification meaning

## Summary

Transporting a proof of a selected property can require less than full behavioral equivalence. But a valid target proof must still prove the intended property: a generator that changes both the implementation and specification can produce a checked theorem about the wrong claim.

The useful certificate boundary separates target proof validity, specification meaning, and the relation to the source artifact. These duties also have different trust and maintenance costs.

## Applicability

The theory subjects are Barthe et al.'s SAS 2006 extended abstract, DOI `10.1007/11823230_20`, and Seo et al.'s ITP 2024 PotPie paper, DOI `10.4230/LIPIcs.ITP.2024.33`. The PotPie source subject is `uwplse/potpie@a57f960958901dee3b8075be0a312d6a194be456`, the v0.5 revision identified by the publication/archive reference. Source and paper propositions were directly inspected; no Coq proof was rebuilt.

No immutable source repository for the SAS prototype was located in the bounded primary-author/publisher search. That is a limitation of this investigation, not evidence that the prototype is unavailable. The report does not infer current behavior from the historical prototype description.

## Findings

### Barthe's property-certificate translation contract

Basis: **documentation** — [SAS 2006 author PDF](https://software.imdea.org/~ckunz/publications/certtrans-SAS06.pdf), §§1–4, 6.

Using local notation, certificate translation requires:

```text
Certifies(c,p,φ) ⇒ Certifies(Tcert(c),Tcode(p),Tspec(φ)).
```

The RTL setting distinguishes preserved/instantiated proof obligations, transformed obligations, and translation using certified analysis results. Analysis facts are expressed and certified in the policy logic; proof operations combine them with the source certificate. Ghost variables can retain assertions about deleted runtime registers. The abstract proof algebra specifies valid proof operations, not a concrete certificate-checking algorithm. The stated VCG guarantee concerns normally terminating executions satisfying the entry precondition.

### PotPie independently constrains specification meaning

Basis: **documentation** — [ITP 2024 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.33/LIPIcs.ITP.2024.33.pdf), Definitions 3–5, Table 1, §§3.1–3.2, 5–7.

Specification soundness for `P` requires, on related source stores/parameters and target stacks:

```text
source_state ⊨ P ⇔ target_state ⊨ Tspec(P).
```

Proof compilation yields a target Hoare proof, under workflow-specific obligations. CC requires structural commuting equations, well-formedness, stack preservation, and specification/implication-database conditions. Tree can produce a validity certificate, but target-tree validity alone does not guarantee preserved pre/post meaning; those obligations remain separate. Boolean-only plugin checking adds its own trust. General control-flow optimization, scalability, and target termination proof reuse are not established by this paper.

### What the pinned PotPie source binds

Basis: **source** — immutable files in Evidence.

`StkHoareTree.v` indexes `stk_valid_tree` by precondition, command, postcondition, function environment, fact environment, and tree. `valid_tree_can_construct_hl_stk` maps such evidence to the corresponding target Hoare derivation with the same indices. It establishes target proof validity, not an arbitrary relation to a source assertion.

`ProofCompilerCodeCompAgnostic.v`'s `induction_P` and `hl_compile` expose source proof, mapping/parameter checks, target code/specification equations, function well-formedness, and valid implication translation as inputs. `ProofCompilableCodeCompiler.v` separately lists substitution commutation, structure-preserving code equations, and target expression purity as module obligations. This is a conditional interface, not permission to instantiate an arbitrary compiler without proofs.

The README distinguishes a kernel-checkable `stk_valid_tree` certificate from a Coq boolean answer returned when certificate generation fails. It also tells users to verify that the generated certificate's triple is the intended triple. This report does not convert the boolean path into the kernel theorem or audit the entire plugin.

### Selected properties and source-safety direction

Basis: **derived**.

A property such as “the returned `x` is zero” can survive a change to an unobserved `y`; full output-state equivalence would reject it. A narrower certificate is legitimate if its claim names exactly the preserved observation and all required execution conditions.

For Anneal, the direction is crucial. Translating an existing source-property proof into a target-property proof does not, by itself, show that proving a generated target model proves the source property. A Rust claim needs either a checked theorem about the source itself, or a model-to-source transfer theorem for that selected property. A target proof cannot recreate a discarded source UB guard. Property-specific certification can reduce proof burden only after the missing transfer direction is supplied.

Specification preservation should include requirements, decoder admission, type instantiation, and outcome classes, not just successful result predicates. Weakening a precondition can enlarge the target claim; strengthening it can silently exclude legitimate callers. Changing a forbidden outcome to divergence can turn an invalid partial-safety claim into a trivially valid target claim. Either alteration needs the appropriate independent theorem before acceptance.

### The specification checker must fix meaning independently

Basis: **derived** + **execution** — report-owned `specification_witness.py`.

The witness constructs three finite examples:

1. Source and target both satisfy `x = 0`, while differing on an unobserved `y`. Selected-property preservation holds despite unequal full states.
2. Source output `x = 1` is translated to target output `x = 2`, and the original property `x = 1` is translated to `True`. The target satisfies the generated property, but an independent truth-equivalence check rejects its meaning on the finite domain.
3. A target precondition is translated to `False`. The Hoare-style target property becomes vacuous, but entry-domain meaning changes and is independently rejected.

These are complete finite observations for the constructed definitions. They are not PotPie tests, proof-assistant results, or a semantics for Rust. Their role is to distinguish target theorem validity from preservation of the user's claim.

An Anneal specification translation should therefore bind a separately authored expected claim or independently interpreted source specification. Checking both generator outputs against each other can miss a correlated mistake. For an exact certificate, the checker must know the original source property, target property, source/model artifact identities, and the semantic relation used to compare them.

### Analysis certificates, proof schemas, and maintenance costs

Basis: **derived**, proposed architecture.

Treat an analysis result as another certificate proposition. A range witness must state which arithmetic/type/target bounds it establishes; a liveness witness must say whether a value is dead in executable code, specifications, or both; an alias/frame witness must cover the concrete accesses the transformation changes. Proving a property of the optimized model cannot justify the analysis retrospectively if the analysis erased the required evidence.

Reusable proof schemas can encode a transformation's local rule plus named analysis premises. The checker must instantiate the schema on the concrete endpoints and independently discharge every premise. A schema reduces repeated proof representation; it does not remove analysis semantics or specification adequacy from the acceptance theorem.

Changing optimizer heuristics may leave schemas intact. Changing a rule, representation, specification compiler, or fact environment requires rechecking affected obligations. Narrow property certificates can be cheaper because they preserve fewer observations, but new properties may require new certificate rules and proof migration. A general correspondence theorem has higher initial cost and potentially broader reuse. No performance claim for Anneal follows from this comparison.

### A bounded Anneal adoption gate

Basis: **derived**, proposed experiment only.

Choose one arithmetic or padding-free byte contract already present at a pinned source/model pair. Freeze an independently stated expected contract, including accepted entries and all forbidden outcomes. Permit an untrusted generator to emit a property-specific proof or transformed obligations. Acceptance should require:

- a kernel-checked theorem for the exact target computation and generated property;
- checked agreement of specification meaning with the frozen expected claim;
- the source/model transfer theorem needed for the reported direction;
- every analysis/schema premise and executable dependency used by that transfer;
- exact source, configuration, model, and semantic-library binding.

Mutate code and specification together, narrow the precondition, drop a source guard, or replace a kernel certificate by a boolean success. Each mutation must fail the corresponding gate. An unsupported transformation may be rejected without proving it incorrect; ordinary certification success requires the evidence.

## Boundaries

- **Not examined:** the SAS prototype implementation, PotPie plugin execution, generated Coq certificates, or complete source assumption audit.
- **Not established:** full behavioral equivalence, total termination, source UB-freedom, or general control-flow optimization from the selected-property interface.
- **Known distinction:** target Hoare proof validity and original pre/post meaning are separate propositions; the latter can remain unsatisfied after a valid target proof is produced.
- **Unknown:** cost and scalability for actual Anneal contracts or changing Charon/Aeneas artifacts. The adoption gate is unimplemented.
- **Not established:** arbitrary proof translation across Lean, Coq, or incompatible memory semantics. The semantic bridge and assumption policy remain necessary.

## Evidence

Observed 2026-10-14. Paper identities use DOI, publication/version, author/publisher URL, and narrow section coordinates; no PDF byte hash was acquired. PotPie observations use the exact revision identified above.

| Primary source | Narrow coordinates | Identity |
| --- | --- | --- |
| [SAS author PDF](https://software.imdea.org/~ckunz/publications/certtrans-SAS06.pdf), extended abstract | 17 PDF pages; §1 translation implication (p.2), §2/proof algebra and normal-termination VCG (p.6), §3 categories (p.7), §4.3 ghost/liveness (pp.12–13) | DOI `10.1007/11823230_20`, LNCS 4134, pp.301–317 |
| [PotPie ITP paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.33/LIPIcs.ITP.2024.33.pdf) | 20 PDF pages; Definition 3–4/Table 1 (pp.6–7), Definition 5 and pre/post meaning (p.9), §5.2 trust (p.15), §7 boundaries (p.17) | DOI `10.4230/LIPIcs.ITP.2024.33` |
| [PotPie repository](https://github.com/uwplse/potpie/tree/a57f960958901dee3b8075be0a312d6a194be456) | publication/archive v0.5 subject | revision `a57f960958901dee3b8075be0a312d6a194be456` |
| [StkHoareTree.v](https://github.com/uwplse/potpie/blob/a57f960958901dee3b8075be0a312d6a194be456/Imp_LangTrick/Stack/StkHoareTree.v) | `stk_valid_tree`, lines 61–135; `valid_tree_can_construct_hl_stk`, lines 218–227 | blob `4cd9167805e89beff2690ae606d42e4109fec660` |
| [Compiler obligations](https://github.com/uwplse/potpie/blob/a57f960958901dee3b8075be0a312d6a194be456/Imp_LangTrick/ProofCompiler/ProofCompilableCodeCompiler.v) | lines 509–593, 634–665 | blob `0a4727e0218f726cbaec72dba199769d807da8e7` |
| [Generic proof compiler](https://github.com/uwplse/potpie/blob/a57f960958901dee3b8075be0a312d6a194be456/Imp_LangTrick/ProofCompiler/ProofCompilerCodeCompAgnostic.v) | lines 1270–1308, `induction_P`, `hl_compile`, `proof_compiler` | blob `4a0b9a379be26a92baf77738d6d01317d9c32a36` |
| [README](https://github.com/uwplse/potpie/blob/a57f960958901dee3b8075be0a312d6a194be456/README.md) | lines 30–65, certificate/boolean paths | blob `3e5c3d571a0f26c2b0dfd114e99c8a82c78f854a` |
| Finite witness | `specification_witness.py`, `specification-results.json` | Python execution only |

## Revalidation

Run `python3 -B specification_witness.py` to replay the finite separation examples. For a real proof compiler, check the exact target theorem indices, specification soundness on related states, valid implication database, and compiler commutation/purity obligations. Audit the source dependencies of the accepted certificate, then mutate the property and entry domain independently of the code.

A successful boolean check is not a preserved-specification theorem. A kernel-checked target proof is not a source/model theorem. Revalidation must inspect each of those propositions rather than repeating only target proof checking.

*Authored by an AI agent acting on joshlf's behalf.*
