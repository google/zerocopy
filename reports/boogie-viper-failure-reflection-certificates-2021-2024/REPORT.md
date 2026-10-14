# Failure-reflecting frontend and obligation certificates: Boogie, Viper, and Anneal

## Summary

A checked theorem that a generated obligation implies the original program's correctness can remove the obligation generator from the trusted boundary. A checked source-to-IVL failure simulation can remove a frontend translation from that boundary. The two theorems compose only when their program semantics, global declarations, correctness predicates, and concrete artifact identities agree. An unchecked solver answer or an uncovered source import remains a separate premise.

This report supplies the published proposition shapes and derives an Anneal first-bad-step interface. A finite witness shows why successful-result inclusion, narrowed entry domains, and treating bad execution as divergence do not establish source safety.

## Applicability

The comparison concerns the CAV 2021 paper by Parthasarathy, Müller, and Summers, DOI `10.1007/978-3-030-81688-9_33`, and the PLDI 2024 paper by Parthasarathy, Dardinier, Bonneau, Müller, and Summers, DOI `10.1145/3656438`. The published proof architectures were inspected; no contemporary Boogie or Viper implementation was installed or executed.

Anneal-specific deductions use `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`. The correctness predicate is compared with that snapshot's total/partial failure-rejecting contract design, not claimed equivalent to its complete Rust semantics.

## Findings

### Boogie certifies the implication from VC validity

Basis: **documentation** — [CAV 2021 author paper](https://gauravpartha.ch/papers/boogie_certificates_cav21.pdf), §§2–6.

The generated Isabelle certificate composes:

```text
Valid(VC) ⇒ Correct(passified_DAG)
Correct(passified_DAG) ⇒ Correct(DAG)
Correct(DAG) ⇒ Correct(original_CFG).
```

Correctness excludes failing reachable traces under well-formed contexts and precondition/axiom-satisfying states; normal final states meet postconditions. Failed assertions reach failure; false assumptions reach magic. Divergence is permitted, but finite failure prefixes are excluded. CFG-to-DAG proof uses loop invariants; passification relates variable versions; VC certification connects shallow formula values to operational expression evaluation. SMT validity itself is assumed by this certificate. The supported subset omits direct maps and procedure type parameters; the examined implementation has option/attribute restrictions.

### Viper certifies source failure rather than only successful outputs

Basis: **documentation** — [PLDI 2024 author paper](https://gauravpartha.ch/papers/front_end_translation_certificates_pldi24.pdf), Fig.4, §§3.3, 4.1–4.5, 5.

For related input states, generic `sim` requires:

```text
Every successful source reduction has a target normal execution to
the designated output point and related output state;
any source failure has a target execution reaching failure.
```

The state relation connects stores, heap and permission masks. Interpretation witnesses satisfy generated background axioms. Each method certificate proves target correctness implies specification well-formedness, and—given all methods' well-formed specifications—source correctness. This resolves non-local call checks before deriving whole-program correctness. Input Viper AST is connected to Boogie's internal AST, avoiding trust in the Boogie parser. Isabelle checks generated proofs; the examined translator adjusts map encoding and disables unsupported simplifications.

### The direction needed for source safety

Basis: **derived** from the preceding propositions.

Let `Bad_S(s)` mean that some finite source execution prefix from `s` reaches its first forbidden operation. Let `Safe_M(m)` mean that no model execution from `m` reaches forbidden failure. The transfer needed by Anneal is:

```text
Entry(s) ⇒ ∃m. R(s,m)
R(s,m) ∧ Bad_S(s) ⇒ Bad_M(m)
Safe_M(m) ∧ R(s,m) ⇒ ¬Bad_S(s).
```

The second line exposes source failure; the third is its contrapositive. It must quantify over every permitted source entry and every failing source prefix. Existential matching of a failing target execution is enough when model safety excludes all failing target executions. Existential entry representation is enough only if the failure simulation holds for the chosen related entry and the model proof covers that entry. “Some successful source behavior matches” has neither property.

A convenient convention calls the source-to-target failure witness a forward simulation, while the final result reflects target safety back to the source. The name of the simulation is less important than its quantified direction and bad-outcome case. A compiler refinement that assumes source-defined execution can preserve all of its stated observations and still be insufficient for proving that a bad source step never occurs.

Successful simulation remains necessary for composition. Suppose the first source operation succeeds and the second fails. The first certificate must reach an intermediate normal target state related to the source state so that the second certificate can supply its failing target continuation. A translation that routes every successful source step to magic does not provide that bridge.

For a total Anneal contract, add divergence reflection or a suitable progress theorem. For a partial contract, divergence may be acceptable only when every finite concrete prefix is safe. A placeholder `.div` for unsupported or forbidden behavior is therefore unsound for a safety-transfer claim.

### Nondeterminism and initial-domain coverage

Basis: **derived**.

An overapproximating model can admit additional normal or failing outcomes. Universal safety/property proofs then become stronger obligations, which can reduce verification success while preserving soundness. Removing concrete bad choices to get a convenient deterministic model has the opposite effect: the source-safety implication is lost. The certificate must cover each concrete nondeterministic bad prefix, even if some source choices are safe.

Entry coverage must also be explicit. A relation that represents only input values `0` and `1` can support a conditional safety theorem while saying nothing about a permitted input `2`. Kernel acceptance of that conditional theorem cannot justify a safe API claim covering all three inputs. Caller requirements, mathematical decoder domains, and concrete well-formedness premises must be separately identified.

### Certified obligation generation for Anneal

Basis: **derived**; proposed interface only.

For an exact source artifact `S`, executable model `M`, contract `Q`, and generated obligations `O`, a proposed generator can be entirely heuristic if it emits a checkable theorem:

```text
Discharged(O) ⇒ ModelContract(M,Q).
TranslationCertificate(S,M,configuration) ⇒
  ModelContract(M,Q) ⇒ SourceClaim(S,Q,configuration).
```

The first implication establishes completeness of the obligation set for the model property. The second bridges the model to the source, including failure behavior and entry domain. They should be separate proof boundaries even if one tool emits both certificates. Reject missing obligations, unknown semantics, unresolved calls, producer failure, unsupported cases, timeouts, and checker failure as unestablished certification; a failed proof search does not by itself establish that the translation is wrong.

The aggregate certificate must bind root coverage and executable dependencies. If a caller certificate relies on a callee specification or a skipped check, carry the dependency and discharge it before reporting the caller's unconditional result. For mutually dependent contracts, use a justified simultaneous rule; do not allow certificates to assume each other's conclusion without such a rule.

Global axioms and external interpretations need special care. A target theorem conditioned on inconsistent generated axioms is vacuous. An explicit model satisfying them, compatible with the required source states and observations, can close that part of the bridge. In Lean, an ordinary definition can avoid new logical axioms yet still have a trusted Rust correspondence; the logical axiom audit does not establish that correspondence.

### Witnesses and pinned Anneal evidence

Basis: **execution** — `failure_witness.py` and `failure-results.json`; **source/documentation** — pinned `SafetyTests.lean` and `ADMISSION_DESIGN.md`.

The deterministic finite probe records four separations:

| Constructed pair | Successful-result inclusion | Missing source-safety obligation |
| --- | --- | --- |
| Bad guard removed, constant normal result | passes | Source failure has no model failure |
| Bad guard replaced by divergence | passes | Partial model contract accepts divergence despite prior source failure |
| One bad nondeterministic source choice omitted | passes | All concrete bad choices were not covered |
| Model entry relation omits the bad permitted input | holds on represented inputs | Public input-domain coverage fails |

The corresponding failure/coverage predicates reject each pair. These are finite mathematical witnesses, not Rust execution or Boogie/Viper regression tests.

The pinned Lean source contains `forbidden_bind`, `total_rejects_forbidden`, and `partial_rejects_forbidden`, plus invalid Boolean production before discard and divergence. They establish the intended target-level propositions in source form; this investigation did not rerun their Lean checking. The admission design describes preserving original imported operations, origin identity, complete dependencies, and exact external leaves. It also explicitly retains compiler/importer and primitive correspondence trust. Its stronger extension requirements remain obligations; the existence of the document is not a source-to-model certificate.

## Boundaries

- **Not examined:** generated Isabelle proof files, artifact VM, current Boogie/Viper source, or fresh proof checking. The PLDI artifact record was inspected only as an available reproduction coordinate.
- **Not established:** one fully checked Viper-to-VC chain combining these publications. The two work products require identical target AST, background declarations, map encoding, semantics, and relevant correctness interfaces before composition. Publication proximity supplies no bridge theorem.
- **Not established:** solver validity checking, Rust-to-Viper, Rust-to-LLBC, or LLBC-to-Lean fidelity. None follows from an IVL frontend or VCG certificate.
- **Not established:** total termination from the displayed partial-correctness chain, nor full unsafe Rust support.
- **Unknown:** practicality and cost of certifying an actual Anneal obligation generator or import pass. The witness verifies only its finite definitions.

## Evidence

Observed 2026-10-14. Source facts are a bounded paraphrase of directly inspected primary papers. Their byte hashes were unavailable; DOI, author URL, section/figure number, and PDF page count identify the copies.

| Source | Identity and narrow coordinates | Role |
| --- | --- | --- |
| CAV 2021 paper | DOI `10.1007/978-3-030-81688-9_33`; [author PDF](https://gauravpartha.ch/papers/boogie_certificates_cav21.pdf), 23 PDF pages; Fig.2 and §2 (p.4), §3.3 (pp.8–9), §§4–5, §6/Theorem 3 (pp.16–18), §7 limitations | documentation |
| PLDI 2024 paper, PACMPL article 208 | DOI `10.1145/3656438`; [author PDF](https://gauravpartha.ch/papers/front_end_translation_certificates_pldi24.pdf), 25 PDF pages; Fig.4 (p.10), composition Fig.5 (p.11), §4.1 state relation (p.14), §§4.4–4.5/Figs.9–10 (pp.17–19), §5 (p.19) | documentation |
| Reproduction artifact record | [Zenodo record](https://zenodo.org/records/10802176), DOI `10.5281/zenodo.10802176`; record inspected, VM not downloaded/run | documentation |
| Anneal source outcome controls | `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, `verification/aeneas/lean/SafetyTests.lean`, blob `554daab40a45110de721b18db84a00c6697e4f27`, lines 16–68 | source |
| Anneal admission/correspondence | same revision, `verification/aeneas/ADMISSION_DESIGN.md`, blob `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf`, lines 134–276, 461–604 | documentation |
| Anneal Rust boundary | same revision, `verification/aeneas/SEMANTICS.md`, blob `d89909750724dbafb76715e673626023b6cd49fd`, lines 92–167, 169–225 | documentation |
| Mathematical witness | `failure_witness.py`, Python standard library; `failure-results.json` records results and finite bounds | execution |

## Revalidation

Run `python3 failure_witness.py` from this package. Check that every source-safety counterexample passes only the intentionally weak predicate and fails the required bad-outcome/coverage predicate. This finite check is independent of a compiler implementation.

For a real certificate chain, inspect the exact proposition, formal semantics version, global declaration interpretation, and bound ASTs for every leg. Corrupt an omitted failure, add an `assume false`, omit a callee, weaken an obligation, narrow the entry domain, or substitute a stale model; the acceptance path must reject for the corresponding missing theorem. Separate proof reconstruction from SMT validity and from source import. Reread the generic success/failure simulation definition before using a theorem named “correct translation” as source-safety evidence.

*Authored by an AI agent acting on joshlf's behalf.*
