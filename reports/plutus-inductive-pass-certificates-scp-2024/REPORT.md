# Inductive pass relations, semantic consequences, and the inspected Plutus artifact

## Summary

A per-pass translation derivation certifies conformance to the pass relation. A separate theorem must connect that relation to the semantic property being reported. Neither a relation's name nor a boolean checker returning true supplies the missing theorem.

The inspected Plutus relation artifact also contains an admitted purity-check soundness lemma with a strict-`Error` counterexample by direct source analysis. Consequently, this artifact must not be presented as an assumption-free certified decision procedure. This is a finding about the exact inspected research artifact, not today's Plutus compiler.

## Applicability

The publication is Krijnen et al., Science of Computer Programming 233 (2024), article 103051, DOI `10.1016/j.scico.2023.103051`. The primary author PDF and its linked relation repository were directly inspected. The old `jaccokrijnen/2022-scp-translation-relations` URL redirects to `basetunnel/2022-scp-translation-relations`; the examined revision is `72e619f3243498a612d8c6c5090b88117c404489`.

Paper results and artifact observations are separate subjects. The repository revision does not identify a complete Plutus compiler, its importer, or a built certifier. This report proposes an Anneal interface; it does not certify Charon, Aeneas, or Rust semantics.

## Findings

### The paper's relation-checking architecture

Basis: **documentation** — [SCP author paper](https://webspace.science.uu.nl/~swier004/publications/2024-scp.pdf), §§2.1–2.4, 4, 5.4.

Each pass has an inductive AST relation `R`; a certificate carries intermediate ASTs and adjacent derivations. A reflected checker has an acceptance theorem:

```text
check(s,t) = true ⇒ R(s,t).
```

The semantic theorem is separate:

```text
R(s,t) ∧ semantic_side_conditions ⇒ SemRel(meaning(s),meaning(t)).
```

The paper's dead-code relation combines elimination, unique source binders, and a closed target. Removed strict computations require purity. The work focuses on PIR→Plutus Core; preceding GHC/import stages are outside that effort. Semantic verification remains ongoing, outside the paper's established scope. The paper discusses manual checker construction, functional specifications combined with relational renaming, and the extra intermediate witnesses needed for transitive local-step specifications.

### What is actually present in the pinned artifact

Basis: **source** — immutable files listed under Evidence.

`Transform/DeadCode.v` defines `dead_code(s,t)` as `elim(s,t) ∧ unique(s) ∧ closed(t)`. `elim_delete_let` requires every removed binding to satisfy `pure_binding []`. `DeadCode/DecideSound.v` proves `dec_elim_Term s t = true → elim s t`, not the full `dead_code` conjunction. Its proof uses `sound_dec_pure_binding`; `Analysis/Purity.v` ends that lemma with `Admitted`. `Analysis/Value.v` also has admitted value-check lemmas.

This distinction matters even before discussing operational semantics. A certificate for `elim` is not a certificate for uniqueness, closure, typing, or semantic equivalence. A checked theorem can depend on admitted declarations; inspecting a final `Qed` is not an assumption audit.

### A narrow counterexample to the admitted purity lemma

Basis: **source** + **derived**; **execution** only for the report-owned reduced witness.

Choose any variable declaration `vd` and error type `T`; let `b = TermBind Strict vd (Error T)`.

1. `Purity.dec_pure_binding [] b` reduces to `Value.dec_value (Error T)`.
2. `Value.dec_value` calls `dec_value' 0`; its `Error` branch returns true.
3. A derivation of `pure_binding [] b` must use the strict-term rule and therefore require `is_pure [] (Error T)`.
4. The value rule for `is_pure` requires the term not to be `is_error`; `IsError` supplies the contradiction. The other purity rules require a variable, so cannot derive purity for an `Error` constructor.

Thus the antecedent of the admitted lemma is true and its conclusion is false for this binding. This argument is syntactic reduction and constructor inversion; it does not depend on a disputed runtime semantics for errors. The whole-let branch in `dec_elim_Term` consults the same binding check, so merely proving the recursive decision procedure against an admitted premise does not repair the defect.

`purity_witness.py` checks the corresponding reduced checker/predicate pair on three constructors and records the strict-error discrepancy. It also exhibits a strict-let deletion changing a chosen error outcome into success. That latter execution is an illustrative semantics chosen for the witness, not execution of PIR or Coq. `coqc` was unavailable on PATH; no claim of fresh kernel verification is made.

### An Anneal pass certificate interface

Basis: **derived**, proposed design.

For pass `i`, retain five separately checkable components:

| Component | Concrete content | Required consequence |
| --- | --- | --- |
| Endpoints | Exact before/after ASTs and semantic configuration | The derivation applies to the artifacts subsequently consumed |
| Transformation derivation | An inhabitant of `R_i(before,after)` | This pair conforms to the specified transformations |
| Admissibility | Scope, binder/type identity, effect, guard, and frame witnesses used by the rule | Every semantic premise is established rather than assumed by a heuristic |
| Semantic theorem | A theorem from `R_i` and admissibility to the chosen behavior relation | The local certificate establishes the property needed by the next boundary |
| Assumption policy | Dependency closure of the proof and checked computation | Admissions or incompatible semantics cannot masquerade as discharged obligations |

A constructive translator may search for `∃target. R_i(source,target)` and emit the target with its derivation. An independent certifier instead receives both endpoints; an instrumented compiler can additionally provide witnesses. These change how evidence is found, not what the checker must establish. A witness may accelerate proof search without being trusted.

The relation should permit the compiler's useful choices without reproducing its heuristic algorithm. The cost is that each allowed choice needs a semantic rule. For a literal safe transformation, a function plus checked output equality can be simpler than a general relation. Fresh-name policy is a good candidate for a relational layer over otherwise functional translation, provided capture avoidance is checked.

### Safety-specific admissibility and maintenance

Basis: **derived** + **documentation** — Anneal `ADMISSION_DESIGN.md` at `cce761ad53785973ec2f4a6b13715b770b340c87`, “The correspondence rule.”

For Anneal, “unused result” does not justify deleting an operation that may expose UB, panic, divergence, or an observable effect. A dead-binding rule needs a justified safe/total/effect-free classification appropriate to the source semantics, or a certificate retaining the relevant bad-execution case. A purity witness is itself an obligation; it cannot be accepted merely because the optimizer computed it.

A source-safety claim additionally needs failure reflection through every accepted pass: the first forbidden source step must force a forbidden modeled execution. A relation that only preserves already-defined source executions can be perfectly sound for compiler optimization yet fail this requirement.

Keep the semantic interface stable while allowing heuristics to change. A new optimizer choice inside existing rules may require only new evidence generation; a new rule requires an admissibility proof and semantic consequence; a changed AST or semantic library requires identity migration and revalidation. Deriving a checker from constructors can reduce duplicated search code, but cannot derive the truth of an unsafe rule or eliminate an admitted helper theorem. Completeness and performance are independent of acceptance soundness.

## Boundaries

- **Established by source analysis:** the admitted helper and strict-error counterexample at the stated revision. This is not a finding about every paper version or current Plutus production software.
- **Not examined:** modern Plutus compiler source, complete parser/serialization path, certificate deployment, or Coq compilation of the repository.
- **Not established:** a complete, assumption-free PIR→PLC semantic certificate. The inspected relation source and publication-level architecture do not supply that stronger result.
- **Unknown:** whether a newer related repository fixes the purity issue or completes semantic verification; no continuity across revisions is inferred.
- **Not established:** Rust first-bad-step reflection or a feasible certified Charon pass sequence. Those remain proposed interfaces.

## Evidence

Observed 2026-10-14. Paper identity uses DOI, author URL, section, and 25-PDF-page count; no PDF byte hash was acquired. Repository claims use exact immutable revision and blob identities.

| Primary evidence | Narrow location | Identity |
| --- | --- | --- |
| [SCP paper](https://webspace.science.uu.nl/~swier004/publications/2024-scp.pdf) | §§2.2–2.4 (PDF pp.3–5), §4 (pp.13–20), §5.4 (pp.21–22), §7 (pp.23–24) | DOI `10.1016/j.scico.2023.103051` |
| [Dead-code relation](https://github.com/basetunnel/2022-scp-translation-relations/blob/72e619f3243498a612d8c6c5090b88117c404489/src/Language/PlutusIR/Transform/DeadCode.v) | lines 39–84 | blob `65da05418c6a310e2b4c32d831cecd037a8154a1` |
| [Decision procedure](https://github.com/basetunnel/2022-scp-translation-relations/blob/72e619f3243498a612d8c6c5090b88117c404489/src/Language/PlutusIR/Transform/DeadCode/Decide.v) | lines 31–34, 59–71 | blob `ebded9229af3833934b759f6996f31a383f26a1c` |
| [Decision proof](https://github.com/basetunnel/2022-scp-translation-relations/blob/72e619f3243498a612d8c6c5090b88117c404489/src/Language/PlutusIR/Transform/DeadCode/DecideSound.v) | lines 23–24, 33–48, 177–185, 201–276 | blob `95a0873b9ebdf3ee4d2bd3281fc5c1ead581d49a` |
| [Purity definitions/admission](https://github.com/basetunnel/2022-scp-translation-relations/blob/72e619f3243498a612d8c6c5090b88117c404489/src/Language/PlutusIR/Analysis/Purity.v) | lines 24–26, 44–57, 77–103 | blob `19d151e814725bae0d6d49d918f075ce925a7d17` |
| [Value checker](https://github.com/basetunnel/2022-scp-translation-relations/blob/72e619f3243498a612d8c6c5090b88117c404489/src/Language/PlutusIR/Analysis/Value.v) | `dec_value'`, `dec_value`, admitted value-check lemmas | blob `1666903f2244d5a658db523fc6528081b207c4ee` |
| Anneal design | `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, `verification/aeneas/ADMISSION_DESIGN.md`, lines 172–232 | blob `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf` |
| Report-owned reduced witness | `purity_witness.py`, `purity-results.json` | deterministic Python execution; not Coq/PIR execution |

The source repository README identifies Coq 8.13.2 as its tested toolchain. The paper's relation→semantics discussion is an architectural goal; the source dependency findings qualify this exact artifact's checker theorem independently.

## Revalidation

Run `python3 -B purity_witness.py`. This replays the reduced definitions only. To revalidate the real artifact, inspect `dec_value'`'s error branch, the strict branch in `dec_pure_binding`, all `is_pure` constructors, and the helper's proof. With the compatible source dependencies, compile a strict-error counterexample and run `Print Assumptions sound_dec_elim_Term`; proving the helper or rejecting errors should change the result.

For a new pass, mutate its side-condition witness, endpoints, binder/type identity, and semantic library independently. Acceptance must reject any mismatch, and a completed semantic theorem must be present before a syntactic certificate is described as preservation of program meaning.

*Authored by an AI agent acting on joshlf's behalf.*
