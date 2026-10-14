# Resource interpretation adapters and the limits of proof transport

## Summary

Moving a checked derivation to another kernel does not automatically preserve its intended statement or resource model. Actual transport tools must preserve typing/conversion, expose imported assumptions, and separately justify interpretation of the source statement. This package inspects concrete HOL, Rocq and Lean transport paths and supplies a checked small adapter between partial cells and total values with an ownership mask.

The adapter is an original bounded semantic proof in Lean 4.31. It is conditional on that implementation, whose known nested-parameter checking boundary is recorded in [the kernel comparison](../independent-kernels-and-model-checking-certificates/REPORT.md). It is not a current Iris-to-Lean or Rocq-to-Lean library port.

## Applicability

The prototype uses a finite address space, natural values and exclusive Boolean ownership. The transport source subjects are HOLide, CoqInE, Lean2dk and selected lf-lean result-1 proof units at the immutable pins in REPORT.json. They are separate examples of transport architecture; no combined toolchain was installed or executed. A selected source proof is evidence about that unit and its declared imports, not an axiom audit of its full build.

## Findings

### A concrete adapter preserves the resource interpretation

Basis: **source**, **execution**.

`HeapCore.lean` defines disjoint partial heaps, separation and framed writes. `Adapter.lean` defines another schema: total value vectors plus Boolean ownership vectors. `decode` discards unowned values; `encode` supplies a canonical arbitrary value zero for absent cells. `roundtrip` proves decoding an encoded partial heap yields that heap.

`compatible` requires disjoint ownership masks. `combine_decode` identifies mask/value combination with partial-heap union, while `join_transport` adds compatibility to obtain a valid separation join. Equality of stored values does not make duplicate owners compatible. `entailment_transport` moves a resource entailment through the explicit decoding interpretation. `encoded_update_transport` transfers the exact framed-write judgment, not merely a type name or theorem label.

The actual run checks disjoint masks and rejects a duplicate mask. A vector containing 7 and 11 but owning neither location decodes to the empty heap. These observations expose why value equality alone cannot be used to import access authority.

The retained axiom output lists `propext`/`Quot.sound` for roundtrip, entailment and update transport; `join_transport` additionally lists `Classical.choice`. The latter is an observed dependency of that proof term, not an assertion that the mathematical result needs choice. No successful run contains `sorryAx`. This observation remains conditional on the exact checker implementation and imported core.

### Actual Lean/Rocq comparison requires an interpretation proof per definition

Basis: **source**.

At lf-lean `2c0d52ee93e808c9e09fb6852b43fe080adef8bb`, result-1's `Isomorphisms/U_nat__add__iso.v` proves `nat_to_imported_add_compat` by recursion and uses it to construct `Nat_add_iso`. The LF `plus` comparison similarly proves a relational result for corresponding inputs. This is substantive correspondence between definitions, beyond the fact that both assistants accept some theorem.

The neighboring factorial comparison is explicitly `Admitted`, with a comment that the original factorial is admitted too. Its Checker wrapper prints assumptions. Thus repository-wide translation headlines are not an adequate scope or assumption policy for an individual theorem. No broad failure conclusion follows for other checked comparisons.

An Anneal import should fix source/target definitions, their value/state relation, the actual theorem type and hypotheses, and every imported logical or primitive assumption. Generalizing this successful small pattern to resource logics is engineering plus the semantics-specific adapter proof, not a reason to trust generated theorem names.

### HOL and dependent-type export have different logical obligations

Basis: **source**, primary metatheorem.

HOLide `article.ml` interprets OpenTheory commands; `thm.ml` builds translated proof terms and checks final conclusion/hypothesis matching. The same unit exposes an `axiom` command and emits declarations for `defineConstList` and `defineTypeOp`. Those generated assumptions must be tracked or justified by an imported definition discipline. Dedukti checking alone does not erase them.

CoqInE's pinned translator explicitly encodes sorts, universe constraints, casts, inductives and dependent terms. Its encoding choices are part of the theory presented to the destination checker. One cannot identify Rocq cumulativity and Lean universe conversion merely because both use dependent functions.

[Blanqui and Vaishnav, arXiv:2609.24604v1](https://arxiv.org/pdf/2609.24604), Theorem 4, gives typability preservation for its Lean-minus translation under type-convertibility and universe-injectivity assumptions. Universe polymorphism uses a specified rewrite strategy; general confluence is not asserted. The implementation is preliminary. In Lean2dk `Trans.lean`, axioms become static declarations and quotient/inductive constructs have explicit translation branches. Destination acceptance concerns the encoded signature; recovering the intended source theorem needs the corresponding adequacy/assumption argument. This is a conditional metatheorem and inspected implementation, not a new cross-kernel run.

### Resource meanings and solver propositions must meet at one statement

Basis: **derived**, narrow primary reuse.

For a resource proposition, an adapter must map states, ownership composition, primitive transitions and entry premises. If it imports only an entailment theorem, it must not silently upgrade it to operational safety. If it maps a higher-order invariant into first-order syntax, it must state which quantifiers/connectives survive and prove interpretation of the resulting formula.

The existing [SMT reconstruction report](../smt-certificates-reconstruction-and-root-binding-2026-10-14/REPORT.md) traces SMTCoq, Alethe/Carcara, LFSC and Lean reconstruction against their original formulas. Those certificate mechanisms replay solver reasoning; they do not supply a missing Rust or resource-logic interpretation. Our adapter illustrates the additional interface with an actual checked finite model, while no SMT solver is called here.

### Encoding costs must identify the syntax and the shared obligations

Basis: **execution**, **derived** scope comparison.

`encoding-costs.json` records canonical JSON bytes for option-valued partial cells versus total values plus Boolean masks. For 3,16,64,256 addresses the respective sizes are 10/43, 55/143, 231/527 and 1039/2167 bytes. The data values and ownership pattern are fixed in the file. Both schemes are linear in address count; this is a representation measurement, not a comparison of complete proof sizes or kernel times.

The partial-heap checker report also measures identical direct versus certificate-based Lean statements under one shared model. Reifying the frame witnesses moves repeated reasoning into a generic theorem, but the model, interpretation proof, imports and checker execution remain required. Encoding the same higher-order resource logic in MM0/Metamath would additionally require an explicit foundational development of those semantics, substitutions and inference rules. No measured Iris/MM0 or arbitrary richer-logic port is claimed. The useful bounded conclusion is what that extra proof must preserve and which observed costs actually belong to the small schema.

## Boundaries

**Not examined:** executing the external transport tools, full closure/assumption validation of the selected Rocq build, general Iris/Lean/Rocq/HOL adapters, or richer-logic-to-MM0 proof-size benchmarks. **Known scope:** our schema has no fractions, invariant masks, step indices, impredicative resource predicates, physical memory or Rust adequacy theorem. The mechanism and local adapter are answered; selecting and implementing a general port remains separate.

## Evidence

support/evidence.json records immutable paths, normalized-text fingerprints and inspected symbols. support/HeapCore.lean and Adapter.lean contain all original prototype definitions; adapter.stdout/stderr and adapter-results.json retain invocation/status/axioms. encoding-costs.json identifies its exact measurement domain. External source mirrors are not included in the package.

## Revalidation

Compile HeapCore.lean to its local olean, then run Adapter.lean with `LEAN_PATH=.` using the selected toolchain. Recheck the three transport paths' axiom and universe handling and the exact selected lf-lean proof, including its imports and assumptions. A new source pin, logic interpretation or conversion strategy requires a new scoped observation.

*Authored by an AI agent acting on joshlf's behalf.*
