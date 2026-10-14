# Guarded abstraction certificates: AutoCorres and the Anneal source boundary

## Summary

A useful program-to-model certificate establishes both an observation relation and a failure implication. Successful-output agreement alone cannot transfer a model's safety proof to its source. A deliberately stronger abstract guard can make certification sound while making some otherwise valid source executions harder to verify. Those are different outcomes from unsupported translation or source UB.

This report gives the concrete AutoCorres proposition, then derives an Anneal certificate interface. It does not establish a Rust translation theorem.

## Applicability

The comparison uses Greenaway et al.'s PLDI 2014 paper, DOI `10.1145/2594291.2594296`, and the upstream AutoCorres project description. No release of AutoCorres was installed or executed. Publication coordinates identify the examined theory; they do not identify a modern implementation.

Anneal deductions refer only to `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, especially `verification/aeneas/ADMISSION_DESIGN.md`. The comparison interprets the paper through the source-safety requirement in that snapshot. The baseline reference reports at `a0ff759e7d2d9a953f0ac40b326dd23197bd9188` supply terminology, not independent primary evidence of this paper's results.

## Findings

### The published certificate includes nonfailure reflection

Basis: **documentation** — [PLDI 2014 author paper](https://trustworthy.systems/publications/nicta_full_text/7629.pdf), §§2, 3.3, 4.2–4.4.

In notation chosen here, the word-abstraction proposition is:

```text
P(s) ∧ NF(A(s)) ⇒ NF(C(s)) ∧
  ∀(r,t) ∈ Out(C(s)). (mapNormalException(rx,ex,r),t) ∈ Out(A(s)).
```

Heap abstraction instead maps state through `st`:

```text
NF(A(st(s))) ⇒ NF(C(s)) ∧
  ∀(r,t) ∈ Out(C(s)). (r,st(t)) ∈ Out(A(st(s))).
```

`NF` negates the monad's failure flag; results are sets. The heap projection returns an object only with valid type tags, alignment, and a non-null, nonwrapping footprint. Read and update rules justify the projection. Unsigned-to-natural abstraction can add overflow guards. Proved syntax-directed rules generate Isabelle LCF proofs. The C-to-Simpl parser remains trusted.

The [project description](https://trustworthy.systems/projects/OLD/autocorres/) separately describes an importer kept simple and later abstraction accompanied by correspondence proofs. That distinction is the useful architecture precedent.

### What the implication transfers, and what it does not

Basis: **derived** from the displayed propositions.

If a postcondition holds for every abstract result and the abstract failure flag is false, concrete nonfailure follows, and every concrete result satisfies the postcondition after the stated projection. The quantifier over concrete results prevents choosing one convenient concrete behavior. The abstract model can overapproximate: its additional results make universal postconditions harder to prove without invalidating transfer.

The `NF(C)` conjunct carries the safety work. Dropping it would leave only result inclusion, which is vacuous when a bad concrete execution has no successful result. A certificate about only already-defined concrete executions has the same defect for proving absence of the first invalid operation: its premise has excluded the execution that matters.

The equations must be read with their exact monad and loop semantics. The paper's list-reversal case study requires total correctness and adds a termination argument (§5.2, PDF p.9). This report has not inspected the loop implementation or independently characterized how divergence affects its failure flag. Do not identify that flag with Anneal's partial-contract predicate. For a new Anneal correspondence, agreement on terminating outputs alone cannot rule out erased infinite execution; its total contract needs the relevant progress/termination bridge, and its partial contract must exclude every bad finite prefix.

### A certificate boundary for Anneal

Basis: **derived** + **documentation** — pinned `ADMISSION_DESIGN.md`, “The correspondence rule,” lines 172–232.

Use explicit semantics for a conservative imported program `S` and executable model `M`; define a relation `R` between their states. A bounded first certificate should establish:

1. Entry coverage: every permitted concrete entry state has at least one related model entry, with the intended argument relation.
2. Normal-step preservation: each concrete safe step has a related model execution and preserves the required observations and caller frame.
3. Bad-step exposure: from related states reached before the first bad step, that step yields model failure before sequencing continues.
4. Progress: any erased concrete steps have a well-founded measure, or another proved progress condition sufficient for the total-contract theorem.

The first bad step must be exposed without a premise that the entire invocation is safe. “All accesses are valid” as a correspondence premise would assume the conclusion; valid incoming references or a caller-owned frame can be legitimate entry premises if stated independently of the body's behavior.

A normalized model may strengthen guards, but a stronger guard has a cost: the theorem then covers fewer invocations. A safe public API cannot acquire a hidden user obligation merely because a mathematical decoder admits a smaller domain. Coverage of the public API's permitted states is another theorem, independent of conditional correctness under the decoder.

### Generation, checking, and the remaining trust ledger

Basis: **derived**; the roles below are a proposed Anneal design, not an implemented result.

| Boundary | Producer's work | Acceptance evidence | Obligation still outside that evidence |
| --- | --- | --- | --- |
| Rust configuration → conservative import | Parsing, origin tracking, import | Exact configuration and import identities; later certificate may bind them | Fidelity of the importer until a source semantics or verified import leg is supplied |
| Imported operational model → simpler executable model | Heuristic abstraction and simplification | Kernel-checked relation, failure implication, and required progress theorem | Adequacy of the semantics and primitives named in that theorem |
| Executable model → user contract | Obligation generation and proof search | Checked proof that the exact model satisfies the exact contract | Public-domain coverage and adequacy of the written contract |
| Reported result | Coverage and dependency aggregation | Checked conjunction of the bound obligations | Parser, serialization, artifact binding, and executable checker wrapper unless separately justified |

An untrusted producer can propose `st`, guards, intermediate ASTs, and proof hints. Acceptance must check their semantic consequence for the exact endpoints. A file saying a trusted admission traversal succeeded is evidence of that traversal; it is not automatically a proof term relating Rust to Lean.

The pinned Anneal docs explicitly retain compiler/importer, borrow translation, builtin, and external-interpretation premises. A later proof-producing abstraction stage can reduce one of those premises without eliminating the others. The current pure memory geometry in `anneal/lean/README.md` supplies neither pointer provenance nor access permission, so importing those mathematical theorems cannot discharge the state relation by itself.

## Boundaries

- **Not examined:** AutoCorres release source, generated certificates, proof checking, or performance. The publication was inspected; its implementation was not rebuilt.
- **Unknown:** the effort to certify an actual Charon normalization or Aeneas translation using this pattern.
- **Not established:** Rust provenance, reference validity, destruction, concurrency, unwind recovery, or general runtime typed-copy behavior. The paper's C projection is not a Rust access-authority theorem.
- **Not established:** adequacy of every guard in an existing source importer. A theorem about an imported model still depends on that importer preserving the source operations that could fail.
- **Known distinction:** harmless strengthening can reject useful inputs; unsupported modeling, source UB, certificate search failure, and kernel rejection have different internal meanings. None supplies an ordinary successful certificate.

## Evidence

Observed 2026-10-14. Primary sources were directly read through the web PDF/text interface. A shell download failed at DNS resolution; this is an acquisition limitation, not evidence about AutoCorres. No PDF byte hash was obtained. DOI, author-hosted URL, paper section, and PDF page count are the strongest available paper identity here.

| Source | Identity and narrow coordinates | Role |
| --- | --- | --- |
| Greenaway, Lim, Andronick, Klein, PLDI 2014 | DOI `10.1145/2594291.2594296`; [author PDF](https://trustworthy.systems/publications/nicta_full_text/7629.pdf), 11 PDF pages; §2 monad/import, §3.3 word proposition (PDF p.4), §4.2 projection (p.6), §4.4 heap proposition (p.7), §5.2 total-correctness requirement (p.9) | documentation |
| AutoCorres project page | [upstream page](https://trustworthy.systems/projects/OLD/autocorres/), observed description; mutable page, no implementation revision inferred | documentation |
| Anneal model package | `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, `anneal/lean/README.md`, blob `9799e4c04818c085ac9b3e95bb79dc7ddbe78cc5`, lines 3–34 | documentation |
| Anneal correspondence design | same revision, `verification/aeneas/ADMISSION_DESIGN.md`, blob `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf`, lines 134–232, 234–276, 520–604 | documentation |
| Existing comparison reports | `google/zerocopy@a0ff759e7d2d9a953f0ac40b326dd23197bd9188`, `reports/proof-producing-versus-validating-translations-1997-2022/REPORT.md`, `reports/translation-validation-techniques-1998-2021/REPORT.md`, `reports/verified-compiler-pass-composition-compcert-3-18-popl-2008/REPORT.md` | documentation (secondary; terminology only) |

The operational equations were restated in local notation, without strengthening their premises. The Anneal certificate interface is an independent design deduction. No Isabelle or Lean run was performed.

## Revalidation

For a concrete implementation, inspect the actual correspondence theorem rather than its name: does abstract nonfailure imply concrete nonfailure, does it quantify over every concrete behavior, what entry relation is assumed, and what progress fact supports totality? Retain the source/import/model identities in the proposition or a checked binding layer.

The cheapest proposed Rust pilot is a discarded guarded operation, plus the same operation before divergence. A removed source guard must fail certificate construction even when the generated model trivially proves `True`. A real pilot must preserve the original operation and produce a kernel-checked statement over its chosen source semantics; a finite mathematical witness alone would not test the frontend.

*Authored by an AI agent acting on joshlf's behalf.*
