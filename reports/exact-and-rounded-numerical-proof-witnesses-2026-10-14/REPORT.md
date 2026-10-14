# Exact and rounded numerical proof witnesses

## Summary

A numerical analyzer can propose rational coefficients, sum-of-squares decompositions, ranges, or roundoff bounds. The acceptance endpoint must validate the proposed witness in a stated arithmetic model. A successful real-arithmetic proof is not automatically a proof about IEEE execution, and a floating-point estimate is not an exact proof until a checking path connects it to the requested bound.

The examined mathlib linarith and HOL Light SOS paths construct host proofs after obtaining proposed witnesses. FloVer's published IEEE64 theorem has an explicit no-subnormal-evaluation premise. The exact Gappa implementation and support-library proof rules were not acquired.

## Applicability

Source claims concern the four pinned repositories in REPORT.json; no joint build or numerical benchmark was run. FloVer claims are limited to the primary FMCAD 2018 paper's exact theorem statements, not current source. Gappa claims are limited to its upstream integration documentation observed2026-10-14. Access to the source hosts did not yield a usable immutable snapshot in this bounded audit; no claim about source adequacy follows from that access result.

This report answers numerical witness and arithmetic-boundary subquestions of T017, T012, T020, P051, and P054. It does not infer checking costs or current feature completeness.

## Findings

### Farkas-style arithmetic: verify the identity and the sign argument

Basis: **source**.

mathlib's proveFalseByLinarith receives a CertificateOracle and actual hypothesis proof expressions. It adds a proved -1<0 comparison and negated equality proofs where needed, quotes comparisons into linear forms, and requests a map of natural-number coefficients. It then builds a weighted sum from the selected actual hypotheses. Its acceptance path proves both that the sum equals zero (using a discharger, typically ring) and that it is strictly negative (using the hypothesis proof terms), finally obtaining False through lt_irrefl.

Thus the oracle need not be a verified decision procedure: a proposed coefficient map is useful only if the host proof construction can establish the algebraic identity and strict inequality. Natural coefficients supply nonnegativity, while selected comparisons must yield sufficient strictness. The identity normalization and ordered arithmetic lemmas, including their typeclass assumptions, matter; treating host integers, rationals, reals, or modular machine words as interchangeable would change the theorem.

Source: [Verification.lean](https://github.com/leanprover-community/mathlib4/blob/b16cf9ed26f2e49057943824f2f74f9783b7cb40/Mathlib/Tactic/Linarith/Verification.lean), proveFalseByLinarith and its preceding contract (179–255). This source review did not establish the implementation of every oracle or run mathlib on the available different Lean toolchain.

Carcara's bounded_farkas/la_generic_partial similarly parses rational coefficient arguments, normalizes a linear combination, and accepts only when the variable-side combination is empty and the remaining constant relation is contradictory. Its process_disequality code handles relation orientation and coefficient-dependent transformations. That is an inspected Rust arithmetic implementation rather than a theorem in Lean/Rocq. Moreover, the dispatcher's special lia_generic handling can mark a proof holey, and allowed_rules can bypass dispatch checking; the acceptance policy described in the companion SMT report is essential. Source: [linear_arithmetic.rs](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/linear_arithmetic.rs), process_disequality (near215–326), bounded_farkas/la_generic_partial (338–392). SMTCoq's [LIA.v](https://github.com/SMTCoq/smtcoq/blob/7b870140f2ff7e4547a7db614a305d8b2945afa3/theories/checker/small-checkers/lia/LIA.v) separately proves quotation-building relationships such as build_clause_correct; it is not evidence that arbitrary external coefficient encodings are interchangeable.

For Anneal, use this witness form for range and offset inequalities in their proven mathematical domains, with the conversion to Rust-sized arithmetic proved separately.

### SOS: reconstruct exact algebra from a numerical search result

Basis: **source**.

HOL Light's sumofsquares_general_symmetry obtains a raw optimization vector from an external tool and tries rationalized candidates. It builds a rational sum-of-squares decomposition and requires polynomial subtraction from the input polynomial to be identically zero; otherwise it raises Sanity. SOS_CONV constructs the original and proposed polynomial terms, uses REAL_POLY_CONV on each, and combines their equality theorems by TRANS/SYM. PURE_SOS_TAC proves nonnegativity of the rational-weighted square expression through real ordered-field inference.

The useful witness is the exact rational polynomial identity and sign proof. The optimization solver's floating-point output guides the search but does not replace those theorems. Rational recovery can fail even when a mathematical decomposition exists; an external solver error need not cause a false accepted theorem if proof reconstruction fails.

Source: [sos.ml](https://github.com/jrh13/hol-light/blob/233b83c3202370e03c54de2bd090e4d34f677e91/Examples/sos.ml), rational recovery and exact polynomial check (1561–1598), SOS_CONV/PURE_SOS_TAC (1605–1638), REAL_SOS (1311 onward). No solver executable or HOL Light run was performed. This concerns real polynomial reasoning, not direct rounded machine execution.

### Interval and finite-precision certificates need the rounding premises

Basis: **documentation**, published theorem statements.

FloVer's [FMCAD 2018 paper](https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD18/papers/paper2.pdf), Theorem 1 (p.5), relates a real function, its finite-precision counterpart, precondition, precision map, ranges, and proposed error bounds. Success combines type, real-range, machine-range, and error checks under an environment relation.

Theorem 2 (p.6) specializes to IEEE64 and explicitly assumes IEEEevalAvoidsSubnormals: every subexpression evaluates to a normal value or zero. The stated HOL4 route excludes casts/mixed precision in this connection. The paper distinguishes unverified Coq extraction from its CakeML compilation route. These are theorem- and version-specific premises; current source behavior and any supplied executable were not checked here.

The [Gappa integration documentation](https://gappa.gitlabpages.inria.fr/gappa/tools.html) shows a Rocq tactic invoking a Gappa executable and recognizing fully applied rounding_fixed/rounding_float operators. Generated proof/library imports and the exact rounding operator parameters therefore belong in the evidence identity. This audit does not prove the current support library's rules or its complete treatment of exceptional values.

### Proposed Anneal acceptance record

Basis: **derived**.

For each numerical obligation, the consumer should retain the original expression and domains, evaluation/rounding model, input ranges, denominator exclusions, overflow/exceptional-value policy, certificate, and the checked theorem connecting the certificate to the requested result.

A real equality alone does not justify a compiler rewrite under finite precision: rounding can destroy algebraic identities. Likewise, a safe real-valued denominator does not by itself establish that its rounded counterpart stays nonzero. These distinctions determine what must be encoded in a certificate interface; they are future integration obligations, not a claim that a particular analyzer is unsound.

An extension should supply a proved checking endpoint for its property domain and an adequacy proof for its primitive semantics. Search heuristics and staged specialization may be untrusted when their final numerical witness is checked under that endpoint.

## Boundaries

**Research scope still open:** immutable current FloVer/Gappa source theorem inspection, current exceptional-value support, extraction/binary assurance, integration compatibility, and costs on Anneal numerical obligations. The published FloVer theorem boundary is answered; it is not downgraded merely because Anneal has not implemented its adapter.

**Not established:** that all interval results are complete, that arbitrary rationalization of a solver vector succeeds, or that a real arithmetic theorem proves bitvector/IEEE behavior without a semantics bridge.

**Not examined:** numerical optimization performance, full SMTCoq LIA dispatch/solver combinations, or a fresh kernel axiom audit of the imported arithmetic libraries.

## Evidence

support/evidence.json records immutable source coordinates and retrieved-content hashes for the four source subjects. The FloVer paper is primary theorem evidence with venue, title, and exact public URL; no immutable repository snapshot or PDF hash was acquired. The Gappa integration page is descriptive upstream documentation with an observation date. No numerical execution is claimed.

## Revalidation

Diff the linarith proof construction, SOS exact identity check and theorem construction, and concrete Farkas arithmetic implementation. For FloVer/Gappa, acquire a compatible immutable source and inspect the actual soundness theorem and rounding imports before selecting an executable. Use a witness with an incorrect coefficient/sign and a rounded exceptional-value case when testing an adapter; preserve the consumer's original arithmetic model throughout.


*Authored by an AI agent acting on joshlf's behalf.*
