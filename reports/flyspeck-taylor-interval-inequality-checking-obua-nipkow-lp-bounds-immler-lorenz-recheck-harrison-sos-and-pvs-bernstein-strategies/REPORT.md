# Independent and formally verified checkers for real-number certificates: Flyspeck nonlinear inequalities and linear programs, the Lorenz-attractor re-check, sums-of-squares rounding, and interval/Taylor/Bernstein strategies

## Summary

- **One shape, several residual trust points.** Every system examined splits an expensive *untrusted producer* (C++/OCaml interval search, GLPK plus a dual-repair program, CSDP, Tucker's C++ ODE solver) from a *checker* whose result a proof assistant accepts. The checkers differ in what they still trust outside the logical kernel: nothing beyond the HOL Light kernel and the OCaml runtime for per-case nonlinear-inequality and LP replays, but an **MD5-digest import mechanism built on a deliberately scoped inconsistency** to join 23,242 separately proved inequality theorems into one session; Isabelle's **unverified code generator plus Poly/ML** (`eval`, `@{computation_check}`) for the tame-graph enumeration and the Lorenz computation; PVS's **ground evaluator** (`eval-expr`/`eval-formula`) for the Bernstein and interval strategies; and Coq's reduction machine for NLCertify.
- **What was actually re-checked.** (1) All Flyspeck nonlinear inequalities: 23,237 strict cases plus 5 "sharp" cases verified separately, digests listed in `theorem_nonlinear_digest.hl` (23,242 entries). (2) All 43,078 Flyspeck linear programs, in HOL Light with integer-scaled dual certificates (the earlier Isabelle effort by Obua and Nipkow refuted 2,565 of 2,771 graph systems, about 92.5%). (3) The tame-graph classification, in Isabelle by evaluation, imported into HOL Light as an *assumption* through hand-translated definitions. (4) The 400 initial rectangles of Tucker's Lorenz-attractor computation, by a verified Isabelle ODE solver, **conditional on Tucker's normal-form bounds near the origin (Immler's Assumption 14)**.
- **Checking cost relative to producing.** Formal Taylor-interval checking in HOL Light was reported as about 2,000–4,000× slower than the informal C++ search on small Flyspeck inequalities. The full 2014 run's per-case times sum to **5,006.1 CPU-hours** (re-derived here from the committed run logs; the paper says "approximately 5000 processor-hours"), and a second run sums to 9,274.9 CPU-hours (paper: "about 9370"). The verified Lorenz solver took 131 h 52 min CPU against 30 h 24 min CPU for Tucker's C++ program (about 4.3×, different machines). NLCertify's Coq check took 7.5–8.4× its SOS search time on two Flyspeck inequalities. All 43,078 LP certificates check in "about 15 hours".
- **Current upstream state differs from the papers.** At the pinned AFP mirror revision, the Lorenz C1 check is *not run*: `Lorenz_C1.thy` states the main theorem inside a locale that assumes `check_lines True ordered_lines`, and the interpretation ends in `oops` with the comment "very very slow: about 50 CPU hours".
- **SOS checkers fail closed but can fail to terminate.** HOL Light's `REAL_SOS` rounds CSDP's floating-point Gram matrix with common denominators 1..31 then 2^5..2^66, checks positive semidefiniteness by exact rational LDL^T, and replays the identity in the kernel. If no rounding is PSD it raises `Failure`, and the degree-deepening loop retries indefinitely (Harrison 2007 describes this loop as a known problem).

## Applicability

**Subjects and how they relate.** The report compares checkers and the computer-assisted results they re-checked; it does not evaluate any one system in isolation. The relationships are as follows.

- `flyspeck/flyspeck` at `32948714cdf06d700af2c993c9a92b7b551d7af5` (the original project repository; its README now points to a maintained port at `hol-light-family/Flyspeck`, which was **not examined**). It contains the HOL Light proof scripts (`text_formalization/`), the LP verifier and certificates (`formal_lp/`), a copy of the nonlinear-inequality verifier (`formal_ineqs/`), and the logs of the 2014 nonlinear runs (`azure/results/`).
- `monadius/formal_ineqs` at `2abe797285b3eb57e13988bc45d1747414e638f6` is the standalone, later-maintained version of the nonlinear verifier. Source citations for the verifier use this repository. The logs record that the Flyspeck runs used formal_ineqs SVN revisions 3527, 3550, 3629 and 3658 (printed `FormalIneq:` lines), not this Git revision.
- `isabelle-prover/mirror-afp-devel` at `523cdc72b5ae4a91c9ab8e1025d4a30b40472720` is a read-only mirror of the Archive of Formal Proofs (AFP). The JAR paper used Isabelle2017; the pinned AFP state is newer, and its Lorenz C1 session differs from the paper's run (see Finding 6).
- `jrh13/hol-light` at `1a0c0e6b182cd9e271946ba8d78f7942619f4acb`: only `Examples/sos.ml` was examined. Flyspeck itself was built against HOL Light SVN revision 193 (`azure/config.ml`), not this revision.
- `thery/nlcertify` at `939cc52ba65d09eceb5fc76d2f657a66ccbc60ea` is a copy of NLCertify updated for Coq 8.13. Timings come from the paper, which used older Coq on different hardware.
- `nasa/pvslib` at `d70ebfc8fcd562699aea4bcccbaf3d2c4d66796f`: only `Bernstein/` and `interval_arith/` were examined.

**Execution performed for this report.** (a) A census script fetched the 2,456 committed `stdout` logs and recomputed per-run totals (`support/flyspeck_log_census.py`). (b) The LP worked example from Hales et al. 2017 §9 was re-checked exactly (`support/lp_dual_check.py`). (c) Two **toy models**, labelled as such, were run: a pure-Python exact-rational branch-and-bound comparison of interval, second-order Taylor and Bernstein enclosures (`support/bounds_toy.py`), and an SOS round-and-check model (`support/sos_round_check.py`). Host class for (b) and (c): x86-64 Linux workstation, Intel Xeon @ 2.60 GHz, Python 3.13.15. **No proof assistant was run.** HOL Light, Isabelle, PVS and Coq timings are quoted from sources.

**Scope boundary.** Covered: certificate formats, division of labour between search and checking, in-logic arithmetic, what is trusted outside the kernel, and reported costs. Not covered: the mathematics of the Kepler or Lorenz proofs; floating-point roundoff certificate formats (FPTaylor, Gappa, Daisy); SAT, SMT and integer-programming proof checkers. These are covered by other reports in the corpus.

## Findings

### 1. Cross-system matrix

| System (examined revision) | Certificate (what the producer hands over) | Untrusted producer | In-logic checker and arithmetic | Trusted outside the kernel | Reported checking cost |
|---|---|---|---|---|---|
| formal_ineqs / Flyspeck nonlinear (HOL Light) | OCaml `result_tree` per case: `Result_glue` (bisection, optional convexity), `Result_mono` (monotonicity reduction), `Result_pass` (Taylor bound succeeds on a box), `Result_pass_mono`, `Result_pass_ref`, `Result_false` (search failure) — **kept in memory, not stored** | OCaml float search (`Informal_search.construct_certificate`, `max_width = 1e-10`, `max_depth = 200`) and an informal precision search | `m_verify_list` / `m_p_verify_list` replay the tree with formal floating point over base-200 natural numerals; every arithmetic step yields a theorem | HOL Light kernel and OCaml runtime per case. For the assembled result, also the MD5 import of Finding 3 | 23,237 cases, 5,006.1 CPU-h total (median 404 s, max 19,541 s per case) |
| Flyspeck LP (`formal_lp`, HOL Light) | `lp_certificate`: tree of `Lp_split` case splits and `Lp_terminal` leaves (decimal `precision`, `infeasible` flag, constraint/bound multipliers as `int64`); OCaml `Marshal` files | GLPK and a C# dual-repair program | Formal integer arithmetic sums the scaled constraints and checks that the result is contradictory | HOL Light kernel, OCaml runtime, and the `Marshal` reader running in the same process (Boundaries) | 43,078 LPs in about 15 h |
| Obua–Nipkow LP (Isabelle, superseded) | Dual certificates from GLPK | GLPK | Isabelle interval matrices bounding symbolic coefficients, then certificate check | Isabelle's computation mechanism (not examined) | 2,565 of 2,771 graph systems refuted (about 92.5%); time not examined |
| Tame classification (Isabelle AFP `Flyspeck-Tame`) | None: the enumeration is *run* inside Isabelle | Not applicable | Executable HOL evaluated to normal form | Isabelle code generator and ML; hand translation of definitions into HOL Light | about 2×10^9 graphs, "a few hours"; ROOT timeout 50,400 s |
| Immler Lorenz (Isabelle AFP `Ex/Lorenz`) | 400 `Result` records derived from Tucker's output (grid rectangle, cone angles, expansion factors, return-grid bounds) | Tucker's C++ program, which produced the data | Verified affine-arithmetic Runge–Kutta reachability, run by `eval` / `@{computation_check}` in Poly/ML | Code generator and Poly/ML; Assumption 14 (normal-form bounds near the origin) | 6 h 33 min elapsed, 131 h 52 min CPU on 22 threads |
| HOL Light `REAL_SOS` | Rational Positivstellensatz certificate (SOS blocks plus ideal multipliers) | CSDP (floating point) | Exact rational LDL^T PSD test in OCaml (search side), then kernel replay of the polynomial identity | HOL Light kernel; CSDP is untrusted | about 1 s for a 38×38-matrix example |
| NLCertify (Coq) | Rational SOS certificates plus semialgebraic approximations, emitted as Coq terms | SDP relaxations (the repository has SparsePOP and SDPA interfaces: `sparsepop.ml`, `param.sdpa`) and max-plus templates | `bigQ` reflexive polynomial normalisation (`sos_horner.v`, a ring-style checker), evaluated with `vm_compute` | Coq kernel and bytecode VM; emitted scripts print a Boolean via `Eval vm_compute` (Finding 8) | tf/ti = 7.5 and 8.4 on two Flyspeck inequalities |
| PVS `bernstein` / `interval` strategies | None explicit: a verified algorithm (`multipoly_strategy`, branch-and-bound) is *evaluated* | Not applicable | Ground evaluation of the verified algorithm, then a soundness lemma (`multipoly_strategy_true`) closes the goal | PVS ground evaluator (`eval-expr`, `eval-formula`) | Quoted only via Solovyev–Hales 2013 Table 1 (below) |

Basis: source (each repository at the pinned revision) + documentation (papers cited per row).

Two design families appear in this matrix. **Certificate replay** keeps the producer outside the logic: formal_ineqs, formal_lp, REAL_SOS and NLCertify. **Verified-algorithm evaluation** puts the producer's algorithm inside the logic, proves it sound, and runs it with a trusted evaluator: Isabelle tame enumeration, Immler's solver, and the PVS strategies. Replay keeps the evaluator out of the trusted base but pays for every arithmetic step in kernel inferences. Evaluation is faster, but it adds a compiler or evaluator to the trusted computing base (TCB). Basis: derived from the rows above.

### 2. Flyspeck nonlinear inequalities: pipeline, certificate, and measured cost

**Pipeline** (`monadius/formal_ineqs` `verifier/m_verifier_main.hl`, `verify_ineq0`, lines 530–598). For each inequality the verifier runs four steps in order:

1. **Search.** `Informal_search.construct_certificate opt0 dom_inf fs_inf` (line 571), with `max_width = 1e-10` and `max_depth = 200` (lines 564–565), builds the subdivision tree using OCaml floats.
2. **Informal precision search.** If `adaptive_precision` is set, `Informal_verifier.m_verify_list` (line 581) finds per-node precisions.
3. **Formal replay.** `m_p_verify_list` (line 586), or `m_verify_list` (line 593) when adaptive precision is off, replays the tree inside HOL Light.
4. **Timing.** The verifier returns `{total_time = finish -. total_start; formal_verification_time = finish -. start; ...}` (line 598).

`total_time` therefore covers search, precision search and replay. The Flyspeck driver prints exactly `time.total_time` (`azure/main_verifier.hl`, `Printf.sprintf "\nTheorem %s: %s\nTime %s: %f\nHash %s: %s\n"`). Basis: source.

**Certificate type** (`verifier/certificate.hl` lines 30–38):

```ocaml
type result_tree =
  | Result_false of (float list * float list)
  | Result_pass of (int * bool)
  | Result_pass_mono of mono_status
  | Result_pass_ref of int
  | Result_mono of mono_status list * result_tree
  | Result_glue of (int * bool * result_tree * result_tree);;
```

`Result_pass (_, true)` counts as `pass_raw`, meaning plain interval evaluation without a Taylor approximation (lines 103–105). Basis: source.

**In-logic arithmetic.** `arith_options.hl` line 17 sets `let base = ref 200;;`, with the comment "The base should be even in order to represent inv(2) exactly". Line 27 sets `min_exp = ref 50`. The bundled manual (`docs/FormalVerifier.tex`, §Global Options) still says "The default value of the base is 100". The run logs print `arith_num.hl loaded (base = 200)`. **Documentation and source disagree; the source and the logs agree on 200.** Hales et al. 2017 §5 adds: "The native floating point operations of the computer are not used in any formal proof." Basis: source + documentation + run-log text.

**Known weakness of the search side, as documented.** The `eps` parameter "might be used in cases when the certificate search procedure returns a wrong result due to rounding errors (this parameter will be eliminated when the search procedure is corrected)" (`docs/FormalVerifier.tex`, Verification Functions). This is a completeness issue, not a soundness one: a wrong search result makes replay fail; it cannot yield a false theorem. The tool handles only strict inequalities on rectangular domains with at most 8 variables (same document). Basis: documentation + derived.

**Re-derived run statistics** (`support/flyspeck_log_census.py` over `azure/results/` at the pinned Flyspeck revision; output in `support/flyspeck_log_census.out.txt`):

| Quantity | First run (`output/` + `out-extra/`) | Second run (`urban/out/`) |
|---|---|---|
| stdout files | 1,238 | 1,218 |
| distinct cases with a `Time` line | 23,237 | 23,237 (same case set) |
| sum of per-case `Time` | 18,021,958 s = **5,006.1 h** | 33,389,493 s = **9,274.9 h** |
| mean per case (derived: sum / 23,237) | 775.6 s | 1,436.9 s |
| median / p99 / max per case | 404.4 s / 6,252.0 s / 19,541.2 s | 839.2 s / 9,957.1 s / 32,676.4 s |
| `FAILURE` / `ERROR` lines | 85 / 23 | 0 / 0 |
| `Loading time` lines (mean; sum) | 873 (540.3 s; 131.0 h) | 609 (999.5 s; 169.1 h) |
| HOL Light / Flyspeck / formal_ineqs SVN revisions printed | 193 / 3534, 3546, 3560 / 3527, 3550, 3629 | 193 / 3560 / 3658 |

Interpretation, against the paper:

- Hales et al. 2017 §5 reports "approximately 5000 processor-hours" on Microsoft Azure in July–August 2014, "almost all" on 32 cores (5000 < 32 × 168).
- The paper also reports a recheck "at Radboud University on 60 hyperthreading Xeon 2.3GHz CPUs, in October 2014", which took "about 9370 processor-hours over a period of six days". The `urban/out` directory matches that recheck in case count and approximate total. Mapping the directory to the Radboud run is a derived identification: the logs do not name a host.
- The second-run total is 1.853× the first run's on identical cases (derived). Hardware was not recorded in the logs.
- `FAILURE` lines are producer-side or tactic-side failures, not soundness events. Examples: `FAILURE  346,(prep-TSKAJXY-WKGUESB sym,168): False result` (the search returned `Result_false`) and `FAILURE ... TAC_PROOF: Unsolved goals`. Every one of the 85 `FAILURE` case IDs has a successful `Time` entry in a later batch. Of the 23 `ERROR` IDs, 19 do too; the other 4 are four of the five sharp cases (for example `ERROR  0,(prep-TSKAJXY-RIBCYXU sharp,0)`), which raised `ERROR` in the strict verifier and which `filter-sharp` later removed from the strict run (checked by the same log parse). Failed attempts carry no `Time` line, so their cost is **not included** in the totals.

Basis: execution (census over upstream logs) + documentation (paper) + derived.

**Case accounting.** `text_formalization/general/theorem_nonlinear_digest.hl` lists 23,242 `(case-id, MD5)` pairs. The 23,237 logged cases are all in it. The five remaining entries (`prep-TSKAJXY-RIBCYXU sharp`, `prep-TSKAJXY-IYOUOBF sharp v2`, `prep-OMKYNLT 3336871894`, `prep-GRKIBMP B V2`, `prep-QZECFIC wt0 corner`) are exactly the five cases removed from `ineqs.txt` by the `filter-sharp` target in `azure/results/Makefile`. They are verified by a separate `sharp_verifier` (`azure/README.md`). Their logs are not among the committed `stdout` files examined here. For sharp inequalities, the bound is attained at a domain corner. Hales et al. 2017 §5 proves these cases by exact evaluation at the corner, a Taylor-interval proof away from a neighbourhood, and derivative-sign arguments inside it. Basis: source + documentation.

**Cost relative to the informal producer.** All ratios below compare different machines and different case sets; none is a like-for-like measurement.

| Comparison | Formal | Informal C++ | Ratio (derived) | Source |
|---|---|---|---|---|
| Inequality 3318775219 | 17,091 s total (15,226 s formal replay only) | 8.000 s | 2,136× (1,903× formal only) | Solovyev–Hales 2013 Table 2 |
| 35 inequalities with informal time 1–100 ms | 5,546 s (3,854 s formal) | 1.134 s | 4,891× (3,399×) | Table 3 |
| 11 inequalities, 101–500 ms | 12,098 s (10,451 s) | 3.944 s | 3,067× (2,650×) | Table 3 |
| 14 inequalities, 501–700 ms | 32,065 s (28,705 s) | 8.423 s | 3,807× (3,408×) | Table 3 |
| 9 inequalities, 701–1000 ms | 19,040 s (16,688 s) | 7.274 s | 2,618× (2,294×) | Table 3 |
| Whole project, order of magnitude only | 5,006 CPU-h (2014, Azure, 23,237 partitioned cases) | "about 10 hours" for 985 inequalities (§5.3; the introduction says "about 9 hours") | about 500× | not like-for-like |

Solovyev–Hales 2013 summarise these figures as "about 2000–4000 times slower". The tests ran on an "Intel Core i5, 2.67GHz running Ubuntu 9.10 inside Virtual Box". The same paper estimated that formal verification of all inequalities would take "more than 4 years ... on a single computer" (more than 35,064 h). The 2014 run needed 5,006 CPU-hours. It used compiled HOL Light ("Compiled HOL Light and FormalIneqs", `azure/README.md`) and later formal_ineqs revisions; which change caused the reduction was **not isolated**. Basis: documentation + execution (log census) + derived.

### 3. Assembling 23,242 theorems: the MD5 import and its scoped inconsistency

HOL Light theorems cannot cross sessions. Flyspeck therefore joins them through `text_formalization/general/serialization.hl`. The source comment (lines 536–560) is explicit:

> "We have two options about how to introduce the import of functions. (1) Modify the kernel, or (2) introduce and inconsistency into HOL Light to allow the creation of arbitrary theorems. ... We take the approach (2). However, we restrict the scope of the inconsistency using the scoping rules of Objective CAML, so that the inconsistency can only be invoked to create a theorem using mk_deserialization_thm, which checks that it is a legitimate import."

Mechanism, by line:

- `mk_local_inconsistency` (line 569) defines a fresh type `extern_bool` and derives `falsehood_thm`, a theorem of the form `deserialization ==> r`.
- `mk_deserialize_thm` (line 581) captures `falsehood_thm` in a closure and instantiates `r` to the requested term.
- It accepts the result only if `full_digest_thm` of the instantiated theorem is in the frozen set built from `Theorem_nonlinear_digest.digest_list_extern` (line 593: `St.mem d digest_set || failwith ("theorem digest not found "^d)`).
- `mk_ser_thm` (line 623) discharges the hypothesis with `deserialization_axiom`, which installs `Hol.new_axiom` on the constant `deserialization` on first use (line 601).
- `full_digest_thm` (line 434) MD5-hashes the sorted, de-duplicated serialization of the theorem's entire constant, type and axiom history: `Digest.to_hex (Digest.string h4)`.

Basis: source.

`text_formalization/nonlinear/mk_all_ineq.hl` turns on serialization only while proving the prepared cases (line 357, `prep_nonlinear_thml`, with `Serialization.use_serialization:= true` at line 359). It then proves `the_nonlinear_inequalities` (line 395) and records its expected digest (`"e607b9e5e7f4c495236c6546d6889963"`, line 415). Hales et al. 2017 §6: "the modified version of HOL Light is not used during the proof of any other result ... It is only used to assemble the small theorems from parallel sessions to produce this one master theorem." Basis: source + documentation.

**The top-level theorem keeps two parts as hypotheses.** In `text_formalization/general/the_kepler_conjecture.hl`, `kepler_conjecture_with_assumptions_and_archive` (line 69) proves `import_tame_classification /\ linear_programming_results /\ the_nonlinear_inequalities ==> the_kepler_conjecture`. `tame_nonlinear_imp_kepler_conjecture` (line 89) then rewrites with `Linear_programming_results.linear_programming_results_th`, discharging the LP part in-session. Hales et al. 2017 §3 states the single-session theorem as `|- the_nonlinear_inequalities /\ import_tame_classification ==> the_kepler_conjecture`. Basis: source + documentation.

**What remains trusted for the assembled nonlinear result** (derived from the above):

- the OCaml module-scoping argument that `falsehood_thm` is reachable only through the digest gate;
- that no two distinct histories share an MD5 digest. The threat model is accidental mismatch. A deliberate second-preimage forgery against MD5 is not publicly known to be practical, but MD5 collision resistance is broken (general cryptographic background, not examined here);
- that the 23,242 listed digests came from honest per-case runs, as evidenced by the committed logs;
- that the `deserialization` axiom appears only in the assembling session. HOL Light's `axioms()` would expose it there. The source warns "Deserialization axiom installed!" via `warn_axiom` (`has_deserialization_axiom` and `warn_axiom`, lines 603–611).

### 4. Linear programs: Obua–Nipkow in Isabelle, then integer-scaled dual certificates in HOL Light

- **Isabelle (superseded).** Hales et al. 2010 §7: symbolic matrices `A`, `b` from each tame graph's "graph system" are bounded by Isabelle interval arithmetic (`A' ≤ A ≤ A''`, `b ≤ b'`); a priori bounds `x' ≤ x ≤ x''` are proved; and a GLPK certificate refutes `Ax ≤ b`. "In this way, we proved the inconsistency of 2565 of the graph systems but failed to prove the inconsistency of the remaining 206. This yields a success rate of about 92.5%." The paper defers the remaining cases to "future work" that would "extend the notion of graph system". Basis: documentation (Hales et al. 2010, summarising Obua's thesis; the Obua–Nipkow 2009 article itself was not accessible, Boundaries).
- **HOL Light (used in the final proof).** Hales et al. 2017 §9 gives the method. Slack variables turn infeasibility into a positive optimum. An external LP solver gives an imprecise dual, which a procedure (Solovyev–Hales, CICM 2011) repairs into a "modified dual solution" whose variable coefficients cancel *exactly*. "All dual solutions are also converted to integer solutions by multiplying all coefficients by a sufficiently large power of 10." The formal check "reduces to the summation of inequalities ... and checking that the final result is inconsistent." The paper reports "There are 43,078 linear programs ... All these linear programs can be verified in about 15 hours on a 2.4GHz computer. The verification time does not include time for generating modified dual solutions." `formal_lp/README.txt` line 67 instead says "about 15 hours ... (on Mac mini 2GHz, 2GB)". **The two sources disagree on the machine.** Derived mean: 15 h × 3600 / 43,078 ≈ 1.25 s per LP. Basis: documentation + source + derived.
- **Certificate format** (`formal_lp/hypermap/main/lp_certificate.hl`). `terminal_case = {precision : int; infeasible : bool; constraints : constraint_type list; target_variables ...; variable_bounds ...}`, with `constraint_type = string * int list * int64 list` (lines 4–12). `lp_certificate_case = Lp_terminal of terminal_case | Lp_split of split_case * lp_certificate_case list` (lines 28–30). Files are written and read with `Marshal.to_channel` / `Marshal.from_channel` (lines 114, 120). `formal_lp/README.txt`: "All certificate files are binary files which contain serialized OCaml data structures. These files were prepared with OCaml 4.01." The 39 files in `formal_lp/glpk/binary/` total 423,745,951 bytes (sum of Git tree sizes at the pinned revision; derived ≈ 9.8 KB per LP). Basis: source + derived.
- **Exact re-check of the paper's worked example** (`support/lp_dual_check.py`, output `support/lp_dual_check.out.txt`). The system is `x − 1.42y ≤ 3.15, x + y ≤ 6, 5 ≤ x ≤ 10, 0 ≤ y ≤ 10`, with the published dual `(0.704, 1, −1.705, 0.001, −0.00032, 0, 0.296, 0)`. Exact rational summation gives `0*x + 0*y <= -1487/5000` (= −0.2974, matching the paper). The probe then perturbed each nonzero multiplier by ±10⁻⁵. Every perturbation of entries 1–5 left a nonzero residual coefficient and was rejected. Perturbing entry 7, which multiplies a slack bound that is zero once slacks are fixed, left the certificate valid. This shows that exact checking validates the certificate's *effect*, not the producer's numbers. Basis: execution (of the paper's data, not of HOL Light).

### 5. Tame classification: verified enumeration imported by hand

Hales et al. 2017 §7–§8 describe the setup:

- Isabelle runs the enumeration by evaluation: "about 2 × 10^9 intermediate and final graphs and an archive with 18762 graphs ... the enumeration again runs in a few hours." The formalization "uncovered and fixed a bug in the original Java program, related to symmetry optimizations"; the bug "caused two graphs to be missed in an early draft" of the revised proof.
- In HOL Light the result is an assumption, `import_tame_classification`. "All of the HOL Light terms PlaneGraphs, tame, archive, IN_simeq, fgraph are verbatim translations of the corresponding definitions in Isabelle ... These definitions and types were translated by hand."
- The paper argues transfer between the systems via a propositional (SAT) encoding: the quantifiers range over bounded discrete sets.
- AFP ROOT (`thys/Flyspeck-Tame/ROOT`) marks session `Flyspeck-Tame-Computation` as `(slow very_slow)` with `timeout = 50400` (a configured ceiling, not a measured time).

Basis: documentation + source.

### 6. Lorenz attractor: what the verified solver re-did, and what it imported

Immler 2018 (JAR 61:73–111, open access) is the source for the following unless noted.

- **Re-done in Isabelle.** The verified algorithm combines affine arithmetic, a second-order Runge–Kutta method with remainder, adaptive step size, splitting, and intermediate Poincaré sections. It checks, for each of 400 initial rectangles, return to the Poincaré section Σ (`z = 27`), forward invariance of `N`, and the propagation of cones and expansion bounds. `Parallel.forall (λres. check-line-c1 res) input-data` was run "with Isabelle/HOL's evaluation engine eval".
- **Imported as data.** "We therefore use the output of Tucker's program as a starting point to set up the input for our ODE solver." AFP `Ex/Lorenz/Result_File_Coarse.thy` holds `coarse_results`, a list of 400 `Result` records: `invoke_nf`, `min_deg`, `max_deg`, `expansion`, `preexpansion`, `gridx0/1`, `gridy0/1`, `inf_retx/rety`, `sup_retx/rety` (datatype in `Result_Elements.thy` lines 8–21; rectangle scale `FloatR 1 (-8)` at line 43). These records are *claims* that the verified solver checks, not trusted facts.
- **Trusted, not verified.** First, Assumption 14 (normal-form bounds): "Since we have not verified Tucker's normal form theory, we need to trust the following assumption" (flow from entry sets near the origin, `T ↷'_L (E1 ∪ E2)`). In the AFP it appears as the hypothesis `NF` (`Lorenz_Approximation.thy` line 956: `definition "NF = lorenz.flowsto (cube_entry - Γ × UNIV) {0..} (large_cube × UNIV) cube_exit"`). The final `lorenz_bounds` theorem carries `if NF`. Second, the code generator: "The translation of Isabelle/HOL terms to SML code is not verified. One needs to trust PolyML and its compiler" (§8.3). Third, the expansion sufficiency, "validated ... with a non-verified computation" (§8.1).
- **Reported cost.** On 22 threads (Intel Xeon E5-2699 v4 @ 2.20 GHz): elapsed 6 h 33 min 9 s, CPU 131 h 52 min 40 s, parallelization factor 20.13, GC 42 min 36 s. Tucker's C++ program, recompiled in a VM (gcc 3.3.4, 2.6 GHz Core i7): 30 h 24 min CPU. CPU ratio about 4.34× (derived; different machines). An earlier verified version needed "about 7000 CPU hours" for an enclosure without derivatives or cones; "about 3 CPU hours" with the 2018 algorithms. Size: Tucker's solver is 3,800 lines of C++ on an interval library about twice that size; the generated SML is of similar total size; the Lorenz-specific part is under 10% of the formalization (§8.2).
- **State of the pinned AFP mirror** (source):
  - `Ex/Lorenz/C0/Lorenz_C0.thy` lines 6–7 prove `check_lines False ordered_lines` by `parallel_check _ 15 9`.
  - `Ex/Lorenz/C1/Lorenz_C1.thy` lines 6–7 declare `locale check_lines_c1 = assumes check_lines_c1: "check_lines True ordered_lines"`. Lines 17–26 prove `lorenz_bounds` *inside that locale*. Lines 30–33 read `interpretation check_lines_c1 apply unfold_locales oops ‹very very slow: about 50 CPU hours›`, with the discharging call `by (parallel_check ... _ 60 20)` left commented out.
  - ROOT: session `Lorenz_C1` has `options [timeout = 300 (*360000*)]`.
  - Mirror history for `Lorenz_C1.thy`: a 2024-02-27 change "enable proof in session Lorenz_C1" was backed out on 2024-02-29 with the message "still requires approx. 8-10h elapsed time / 50h CPU time" (abbreviated commit IDs 737780454201 and 0174d0db88a0).
  - The routine AFP build therefore checks the C0 property only. The C1 result (cones and expansion) is a locale-conditional theorem at this revision.

  Basis: source + derived.
- **Evaluation mechanism.** `Lorenz_Approximation.thy` line 2890 defines `ML ‹val check_line = @{computation_check terms: Trueprop parallel_check ordered_lines check_line_core_impl check_line_lookup_out ...}›`. `ordered_lines = alternating (rev [0..<222]) ([222..<400])` orders "the hard ones first" (line 2874). Basis: source.

### 7. Interval and Taylor procedures inside proof assistants

- **formal_ineqs (HOL Light).** Uses Taylor intervals with second-order error terms: `f(x) ∈ f(y) + Σ f_i(y)(x_i − y_i) + error`, where the error is bounded through second partial derivatives on the box, plus monotonicity and convexity reductions (`verification_parameters` in `docs/FormalVerifier.tex`). The polynomial benchmarks bundled with it (`examples_poly.hl`: schwefel, rd, caprasse, lv, butcher, magnetism, heart) are the Muñoz–Narkawicz Bernstein benchmarks. Basis: source + documentation.
- **CoqInterval (Martin-Dorel–Melquiond 2016).** Only the abstract (HAL record hal-01086460) was examined: a Coq tactic "based on a formalization of floating-point and interval arithmetic, associated with an on-the-fly computation of Taylor expansions. All the computations are performed inside Coq's logic, in a reflexive setting." Its trust model is therefore the Coq kernel plus its reduction machine; NLCertify's install script depends on the same library. Benchmarks and timings: **not examined**. Basis: documentation (abstract only).
- **PVS `numerical` and `interval` strategies** (`nasa/pvslib` `interval_arith/README.md`; `interval_arith/pvs-strategies`). Branch and bound over interval arithmetic with `precision` (10^-precision per atomic step, "this accuracy is not guaranteed in the final result"), `maxdepth`, and variable/direction selectors. The strategy evaluates the verified algorithm with `(eval-expr ia-eval :safe? nil)` (pvs-strategies line 418) and closes goals with `eval-formula`. The major theorems are `Eval_fundamental` and `Eval_inclusion` in `interval_arith@interval_expr`. What `:safe? nil` admits during evaluation was **not examined**. Basis: source + documentation.

### 8. Sums of squares: producing in floating point, checking exactly

**HOL Light `Examples/sos.ml`** (pinned revision).

- **Producer.** The SDP is written in SDPA format and solved by external CSDP (`Sys.command("cd "^(!temp_path)^"; csdp "^input_file ...`, lines 614, 974, 1490). The return code 1 or 2 means "csdp: Problem is infeasible". Recent source distinguishes a structural `Csdp_error` exception (declared at lines 13–17) so that rejected inputs do not trigger endless deepening (comment after `deepen`, lines 1144–1146).
- **Rounding.** In `real_positivnullstellensatz_general`, `find_rounding` rounds the raw vector with `nice_rational n x = round_num (n */ x) // n` (line 662). It tries common denominators `map num (1--31) @ map pow2 (5--66)` (lines 1108–1109), rebuilds the block matrices exactly from the eliminated equality constraints, and diagonalises each block with `diag`. `diag` is exact LDL^T; it raises `"diagonalize: not PSD"` on a negative pivot, or on a zero pivot with a nonzero row (lines 837–858).
- **Kernel replay.** The rational certificate becomes a Positivstellensatz proof term (`Sum`, `Product`, `Eqmul`, SOS terms). The translator then proves it in HOL ("Translating proof certificate to HOL", line 1260). Only the kernel replay is trusted; CSDP and the OCaml LDL^T test are search-side.
- **Termination.** `let rec deepen f n = try ... f n with Failure _ -> deepen f (n + 1)` (lines 1140–1143). A rounding failure is a `Failure` from `tryfind`, so the degree bound keeps increasing.

Basis: source.

Harrison 2007 (author's copy of the TPHOLs paper) supplies the rationale and costs. Rounding to the exact rational a float denotes "very often" gives a not-quite-PSD matrix; hence the common-denominator schedule ("Once we reach 32 we start to go up by a multiple of 2 each time"). Minimising the trace tends to give "nicer rational numbers". One example needed a 38×38 matrix "in 8 block diagonal portions" with 143 variables; "the entire sequence of events takes around one second". Two lemmas took 1.25 s and 0.06 s. Known problems: (i) when no rounding is PSD "we end up in an infinite loop, exploring more complex certificates without any benefit", and the floating-point result "can be platform-dependent"; (ii) strict inequalities change the search, and one example became unsolvable when `≥` hypotheses were made strict. Basis: documentation.

**NLCertify (Coq)** (Magron, Allamigeon, Gaubert, Werner, JFR 2015; arXiv v4).

- Certificates are rational SOS. Coefficients use `bigQ` (arbitrary-size rationals) through a ring morphism, and checking is reflexive polynomial normalisation (`coq/sos_horner.v` in the pinned repository, adapted from a ring checker).
- The paper compares its checker with Coq's `micromega`, which also calls CSDP and uses a projection algorithm (Table I, Intel Core i5 2.40 GHz). For POP1 (n = 6): NLCertify ti = 0.04 s, tf = 0.16 s; micromega 18 s. For the n = 2, 3, 6 projections of POP2, the PDF-extracted rows read ti/tf = 0.06/0.18 s, 0.14/0.78 s, 4.8/26.4 s, with micromega at 0.72 s, then "–" (not within one hour) twice.
- Table II, two 6-variable Flyspeck inequalities: 9922699028 needed 39 boxes, ti = 295 s, tf = 2,218 s, (ti+tf)/ti = 8.5; 3318775219 needed 338 boxes, ti = 2,285 s, tf = 19,136 s, (ti+tf)/ti = 9.4. "About 7% of the total time" is SDP.
- Interval Taylor methods needed 9,370 and 25,994 subdivisions on the same inequalities (C++ "cells", per the Flyspeck benchmark log the paper cites).
- One example check took about 200 s with about 667 kbit of rational coefficients; "About 90% of the CPU time is spent verifying the correctness of SOS certificates, that is checking polynomial equalities with the ring tactic."
- The paper contrasts its formal/informal ratio ("does not exceed 10") with "about 2000∼4000" for Solovyev–Hales.

Basis: documentation + source (repository layout only).

**How NLCertify hands results to Coq, at the pinned copy** (source). The Coq script generator `coq_fsa.ml` emits, for a polynomial subproblem, `Definition cert := ... Time Eval vm_compute in checker_pop bnds hyps obj0 cert.` (`str_checker_pol`, line 243), and `Time Eval vm_compute in checker_fsa_itv bnds [::] f (...) true.` for semialgebraic ones (`test_checker_fsa`, line 211). `Eval vm_compute in e` computes and *prints* the value of `e`; it does not create a theorem. The Coq library contains the soundness lemmas that turn `checker ... = true` into a real-valued statement, for example `Lemma checker_fsa_itv_pol ... : conj_PExpr_nonneg l (bnds ++ hyps) -> checker_fsa_itv bnds hyps (Poly p itv cert) v is_root -> pol_in_itv l p itv` (`coq/fsa.v` line 617, proved `by apply Putinar_Psatz_correct_itv`). As emitted, acceptance therefore rests on reading the printed `true`, unless a separate step states a lemma and proves its checker premise by reflexivity. Whether the paper's timings include such a step was **not examined**.

**Toy SOS round-and-check** (`support/sos_round_check.py`; **toy model, not HOL Light**). Target: `p = 2x⁴ + 2x³y − x²y² + 5y⁴` with Gram form `Q(t) = [[2,1,t],[1,−1−2t,0],[t,0,5]]`.

- **Producer.** A float golden-section search for the largest minimum eigenvalue returned `t ≈ −1.6647` with 1e-9 noise (exact denominator 2^51), in 7.2 ms.
- **Checker.** Harrison's schedule accepted at common denominator 1 (`t = −2`). Exact LDL^T gave `p = 2(x² + ½xy − y²)² + 5/2(xy + 2/5 y²)² + 13/5 (y²)²`, in 0.14 ms (timings vary by a few percent between runs).
- **Mutation.** Values of `t` outside the PSD interval were rejected.

This shows only the shape of the split (a numerical producer, then a cheap exact checker whose accepted certificate need not equal the producer's output). Its timings say nothing about real tactics. Basis: execution (toy model).

### 9. Bernstein strategies (PVS) and Bernstein bounds for Flyspeck

- **Strategy** (`nasa/pvslib` `Bernstein/README.md`; `Bernstein/pvs-strategies` lines 599–707). `(bernstein (&optional (fnum 1) vars (depth 100) vardir (equiv? t)))` proves a universally quantified polynomial inequality on a box, or finds a counterexample for an existential one. It evaluates `multipoly_strategy(poly, vars, depth, vardir, proof)` with `(eval-expr bps :quiet? t)` (line 658). If the result is `IsTrue`, it instantiates lemma `multipoly_strategy_true` and finishes with `(eval-formula)`. On `Unknown` it prints "Inequality could not be proved or disproved. Try a depth higher than ~a." With `equiv? nil` it skips proving that the Bernstein representation equals the original polynomial. The README describes "formally verified algorithms for finding lower and upper bounds of the minimum and maximum values of a polynomial" and cites Muñoz and Narkawicz (JAR 51, 2013). Basis: source + documentation.
- **Comparison with formal Taylor intervals** (Solovyev–Hales 2013 Table 1; total time with formal-replay-only time in parentheses):

  | Problem | formal_ineqs | PVS Bernstein |
  |---|---|---|
  | schwefel | 26.33 s (19.15 s) | 10.23 s (3.18 s) |
  | caprasse | 8.06 s (1.29 s) | 11.44 s (1.25 s) |
  | magnetism | 7.01 s (1.35 s) | 160.44 s (82.87 s) |
  | heart | 17.30 s (1.28 s) | 79.68 s (26.14 s) |

  The paper says the PVS columns "show the corresponding verification time for the PVS procedure ... described in" the Muñoz–Narkawicz reference. Whether the PVS figures were re-measured on the same machine is **unknown**. Basis: documentation.
- **Bernstein in the Kepler revision (Coq, Zumkeller).** Hales et al. 2010 §5 reduces one nonpolynomial inequality to a rational-coefficient polynomial "of 12945 monomials and ... total degree 18". It can be converted to Bernstein form without rounding, divisions only by powers of 2 (dyadic numbers). "A prototype implementation in Haskell returns 0 as the maximum for p in about half a minute." This is an informal prototype figure, not a formal check. Basis: documentation.
- **Toy enclosure comparison** (`support/bounds_toy.py`, output `support/bounds_toy.out.txt`; **toy model, not PVS or HOL Light**). Pure-Python exact rationals, bisecting the widest side, cap 40,000 processed boxes per run, same seven benchmarks and bounds as `examples_poly.hl`. Leaves needed to prove each bound:

  | Problem | interval (natural extension) | second-order Taylor | Bernstein |
  |---|---|---|---|
  | schwefel | cap (≥ 19,992) | 11,409 | 640 |
  | rd | 1 | 1 | 1 |
  | caprasse | cap (≥ 19,969) | 428 | 136 |
  | lv | 369 | 160 | 3 |
  | butcher | 1 | 2 | 1 |
  | magnetism | cap (≥ 19,992) | cap (≥ 19,990) | 192 |
  | heart | cap (≥ 19,996) | 4,922 | 41 |

  Wall time per run was at most 10.8 s (`bounds_toy.out.txt`). What this toy shows: for polynomial targets, Bernstein coefficients give far smaller subdivision trees than either interval form under one naive policy. What it does not show: the real tools' relative speed. In Solovyev–Hales Table 1, formal_ineqs (which adds monotonicity, convexity and adaptive-precision refinements that the toy omits) had lower total time than PVS Bernstein on three of the four problems; which refinement accounts for that was not isolated. Basis: execution (toy model) + documentation.

### 10. Checking-to-producing cost ratios collected

| Workload | Producer cost | Checker cost | Ratio checker/producer | Basis |
|---|---|---|---|---|
| Small Flyspeck inequalities, Taylor intervals in HOL Light | C++ search (ms–s) | HOL Light replay | about 2,000–4,000× | documentation |
| 2 Flyspeck inequalities, SOS in Coq (NLCertify) | ti = 295 s, 2,285 s | tf = 2,218 s, 19,136 s | 7.5×, 8.4× (derived) | documentation + derived |
| Lorenz C1 computation | Tucker C++ 30.4 CPU-h | Verified solver 131.9 CPU-h | 4.34× (derived; different hosts) | documentation + derived |
| 43,078 Flyspeck LPs | GLPK + dual repair (not reported) | about 15 h | unknown | documentation |
| Harrison REAL_SOS examples | CSDP + rounding (included) | total about 0.06–1.25 s | not separable | documentation |
| LP worked example (this report) | not applicable | 57.4 µs exact Python | not applicable | execution |

### 11. Six-level resource coverage

| Level | Measured or cited values | Gaps (`not measured`) |
|---|---|---|
| L1 authoring and maintenance | Lorenz-specific code is under 10% of the formalization (Immler §8.2). The 2013 paper estimated more than 4 years of single-computer time; the 2014 run was distributed (32 cores) and used compiled HOL Light. The AFP disabled the C1 proof in 2024 for cost (mirror history). | person-months per component; repair cost when inputs change; LLM/agent budgets: `not measured` |
| L2 toolchain build | Main Kepler statement: about 5 h from scripts on 2 GHz, about 40 min in recorded-proof format (Hales et al. 2017 §1). HOL Light process loading in the 2014 run: mean 540.3 s first run, 999.5 s second run (logs). AFP ROOT timeouts (ceilings only): HOL-ODE-Numerics 10,800 s, Lorenz_C0 14,400 s, Flyspeck-Tame-Computation 50,400 s. | Isabelle/AFP build times at the pinned revision: `not measured` |
| L3 search / tactic latency | C++ informal search for 985 inequalities: about 9–10 h (Solovyev–Hales 2013). NLCertify SDP share about 7%. Harrison examples about 1 s end to end. | interactive latency of `bernstein`/`interval` in PVS: `not measured` |
| L4 generated-code performance | Verified Lorenz solver (generated SML, Poly/ML) 131.9 CPU-h vs C++ 30.4 CPU-h. Parallelization factor 20.13 on 22 threads. | cycles/byte, SIMD use: not applicable / `not measured` |
| L5 certificate checking | 5,006.1 CPU-h for 23,237 cases (median 404 s, p99 6,252 s, max 19,541 s). LPs about 1.25 s mean (derived). Coq SOS tf up to 19,136 s for one inequality. Embarrassingly parallel: 32 cores (Azure) and 60 hyperthreaded CPUs (recheck). | cold-start admission latency per certificate: only HOL Light loading (above) |
| L6 memory and artifacts | LP certificates 423,745,951 bytes / 39 files. Digest list 1,702,748 bytes for 23,242 MD5 entries (≈ 73 bytes each, derived). Nonlinear case data `ineqs.txt` 33,424,656 bytes. NLCertify example certificate about 667 kbit. Nonlinear certificates are not persisted (rebuilt in-process). | peak RSS of any checker; energy: `not measured` |

### 12. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1: what a human can audit.**
  - The *statements* are auditable. `the_nonlinear_inequalities` is a conjunction of several hundred named inequalities, and `import_tame_classification` is a short HOL Light term. Hales et al. 2017 §10 notes that auditing needs specialist mathematics "only ... for a small part".
  - The *residual trust* is harder to audit. The MD5 import (Finding 3) is about 100 lines of OCaml (`serialization.hl` lines 530–626) whose safety depends on module scoping, not on the kernel. A reader auditing only the kernel and the final theorem would miss it unless they inspect `axioms()` in the assembling session.
  - Assumption 14 in the Lorenz work is explicit (`if NF`), but the C1 locale at the pinned AFP revision is easy to misread as an unconditional theorem.
  - Failure diagnostics are legible where the producer reports them (`FAILURE ...: False result`, PVS's "Try a depth higher than ~a"). The SOS rounding failure, by contrast, appears only as non-termination.
- **C2: one invariant enforced by several mechanisms.**
  - Every checker discharges the same invariant: "for all `x` in a box (or semialgebraic set), `f(x) > b`". Subdivision trees (formal_ineqs, PVS, interval branch and bound), Gram matrices (SOS), dual multipliers (LP), and enclosure-propagation traces (ODE) are four certificate encodings of it.
  - A minimal common abstraction is "a finite tree of local witnesses, each checked by exact or outward-rounded arithmetic". Leaves can be Taylor boxes, Bernstein boxes, SOS blocks, or LP duals. This makes the LP case (one leaf per terminal case of an `Lp_split` tree) and the nonlinear case (`Result_glue` trees) ordinary instances.
  - The two genuinely different laws are that LP and SOS witnesses are *global algebraic identities* (an exact equality check), whereas interval, Taylor and Bernstein witnesses are *enclosures* (monotone over-approximations). Merging them would hide that difference.
  - Session-joining (MD5 import) and cross-system import (hand translation) are realization-medium accidents of HOL Light and Isabelle, not part of the certificate concept.

  Basis: derived from Findings 1–9.

### 13. Validation of checkers and their specifications (V1–V4)

- **V1 specification adequacy.** Assembly acts as a cross-check. After the LP part is discharged in-session, the final theorem's hypotheses are exactly the two imported parts (`the_kepler_conjecture.hl` line 89). For the LPs, `Verify_all.test_result` must report the union of all conclusions as `contravening V ==> F` and the union of assumptions, excluding the hypermap-isomorphism assumptions, as `[lp_ineqs; lp_main_estimate]` (`formal_lp/README.txt` lines 86–91). The nonlinear cases were cross-checked by digest-set equality (the `azure/README.md` procedure compares `hashes.txt` with the digest list). Re-execution gave identical results across two independent runs (Hales et al. 2017 §5). The tame enumeration's formalization found a real bug in the original Java program (§7). The toy LP mutation probe shows that the exact checker rejects perturbed duals unless the perturbation is irrelevant. No spec-mutation campaign over the nonlinear statements was found: `not examined`.
- **V2 checker fuzzing and differential checking.** No adversarial malformed-certificate fuzzing of formal_ineqs, formal_lp, REAL_SOS or NLCertify was found. Differential evidence: second run vs first run (identical digests); NLCertify vs micromega (Table I); formal_ineqs vs PVS Bernstein (Table 1). The `Marshal`-based LP certificate reader is an unfuzzed, memory-unsafe input path inside the prover process (Boundaries).
- **V3 concurrency, crash, physical.** Parallelism is process-level (GNU parallel, `Parallel.forall`). Results are joined by digest (HOL Light) or by evaluation (Isabelle). No weak-memory or crash-consistency question arises at this level: known not to apply.
- **V4 plant falsification and human mental models.** Not applicable to these mathematical results. The Lorenz work validates expansion sufficiency only by a non-verified computation (Immler §8.1).

## Boundaries

- **Not examined:**
  - the Obua–Nipkow 2009 article's own text (paywalled). Its numbers here come from Hales et al. 2010 §7;
  - Obua's thesis;
  - the CICM 2011 LP paper's text. Only its DOI and metadata were verified;
  - Melquiond 2008 (IJCAR), Brisebarre et al. 2012 (NFM, Taylor models in Coq), Roux 2016 (JAR, rounding-error bounds), Muñoz–Narkawicz 2013 (JAR), and Daumas–Lester–Muñoz 2009 (IEEE TC), beyond DOI and metadata verification;
  - Tucker 2002 (FoCM) content;
  - the `hol-light-family/Flyspeck` port;
  - the sharp-inequality logs;
  - the HOL Light kernel itself.
- **Not measured:** peak memory of any checker; energy; per-phase split (search vs replay) of the 2014 nonlinear run, because the logs record only `total_time`. Also not measured: Isabelle/AFP build times at the pinned revision; PVS strategy latencies; GLPK/dual-repair producer time for the LPs. **No proof assistant was executed for this report.**
- **Unknown:**
  - whether the PVS columns of Solovyev–Hales Table 1 were measured on the same machine;
  - the hardware of the logged runs (logs carry no host data);
  - why the paper's second-run figure (about 9,370 h) differs from the log sum (9,274.9 h; 9,444.0 h with the 169.1 h of logged loading time). Possible explanations: unlogged failed attempts, or different accounting;
  - what `(eval-expr ... :safe? nil)` permits in PVS;
  - whether the C1 Lorenz check would pass at the pinned AFP revision. The comment estimates about 50 CPU hours, but it was not run here or, apparently, in routine AFP builds.
- **Derived hypothesis, not examined:** OCaml `Marshal.from_channel` is not type-safe. A malformed LP certificate file read into the prover process could in principle corrupt the heap and so undermine the LCF abstraction for `thm`. No exploit or analysis of this was found, and the files are project-produced.
- **Unsupported:**
  - non-strict inequalities in formal_ineqs (handled separately as "sharp" cases), and more than 8 variables, both per its documentation;
  - non-polynomial targets in PVS `bernstein`, which requires a polynomial inequality ("doesn't seem to be a polynomial inequality").
- **Stronger conclusions the evidence does not support:**
  - "The Kepler conjecture is proved in one HOL Light session from the kernel alone." No: nonlinear theorems enter via the MD5 import, and the tame classification is an assumption checked in Isabelle;
  - "Tucker's Lorenz proof is fully formally verified." No: the normal-form bounds are assumed, expansion sufficiency is checked informally, and at the pinned AFP revision the C1 check is not discharged;
  - "Formal checking costs about 3,000× informal search" as a general law. The ratio spans about 4× (ODE, generated code) to about 4,000× (formal replay of interval arithmetic), and depends on whether arithmetic is replayed by inference or evaluated.

## Evidence

**Repositories (all at the revisions in `REPORT.json`; files read via `raw.githubusercontent.com` on 2026-11-21):**

- `flyspeck/flyspeck` @ `32948714cdf06d700af2c993c9a92b7b551d7af5`:
  - `azure/README.md`; `azure/main_verifier.hl` (`verify`, `Printf.sprintf "... Time %s: %f ..."`); `azure/config.ml` (HOL Light 193, Flyspeck 3560, formal_ineqs 3658); `azure/results/Makefile` (`filter-sharp`, `time`); `azure/results/**/stdout` (2,456 files);
  - `formal_lp/README.txt` lines 15–16, 67, 86–91; `formal_lp/hypermap/main/lp_certificate.hl` lines 4–12, 28–30, 114, 120; `formal_lp/glpk/binary/` (39 files, Git tree sizes);
  - `text_formalization/general/serialization.hl` lines 434–438, 536–601, 623; `text_formalization/nonlinear/mk_all_ineq.hl` lines 357–415; `text_formalization/general/the_kepler_conjecture.hl` lines 69–91; `text_formalization/general/theorem_nonlinear_digest.hl` (1,702,748 bytes).
- `monadius/formal_ineqs` @ `2abe797285b3eb57e13988bc45d1747414e638f6`: `verifier/certificate.hl` lines 23–38, 103–105; `verifier/m_verifier_main.hl` lines 530–598; `arith_options.hl` lines 17, 27; `docs/FormalVerifier.tex`.
- `isabelle-prover/mirror-afp-devel` @ `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`:
  - `thys/Ordinary_Differential_Equations/ROOT` (sessions `HOL-ODE-Numerics`, `Lorenz_C0`, `Lorenz_C1`);
  - `Ex/Lorenz/Lorenz_Approximation.thy` lines 956, 2870–2893, 3008–3047; `Ex/Lorenz/C0/Lorenz_C0.thy` lines 6–7; `Ex/Lorenz/C1/Lorenz_C1.thy` lines 6–33; `Ex/Lorenz/Result_Elements.thy` lines 8–46; `Ex/Lorenz/Result_File_Coarse.thy` (400 records);
  - `thys/Flyspeck-Tame/ROOT`;
  - GitHub commit-history API for `Lorenz_C1.thy` (2024-02-27 and 2024-02-29 entries).
- `jrh13/hol-light` @ `1a0c0e6b182cd9e271946ba8d78f7942619f4acb`: `Examples/sos.ml` lines 607–630, 662, 837–858, 1025–1110, 1140–1146, 1222–1262, 1311–1314.
- `thery/nlcertify` @ `939cc52ba65d09eceb5fc76d2f657a66ccbc60ea`: repository tree; `coq/_CoqProject`; `coq/sos_horner.v` (lemma inventory); `coq/fsa.v` line 617; `coq_fsa.ml` lines 211, 243; `install`.
- `nasa/pvslib` @ `d70ebfc8fcd562699aea4bcccbaf3d2c4d66796f`: `Bernstein/README.md`; `Bernstein/pvs-strategies` lines 543–707; `interval_arith/README.md`; `interval_arith/pvs-strategies` lines 410–507.

**Papers.** DOIs were verified on 2026-11-21 through the Crossref REST API, except `10.6092/issn.1972-5787/4319`, which Crossref did not serve to the fetcher; it was verified through the doi.org handle API (resolving to `jfr.unibo.it/article/view/4319`) plus the publisher landing page. arXiv identifiers were verified on arxiv.org abstract pages.

- Hales et al. 2017, `10.1017/fmp.2017.1`, read as arXiv:1501.02155v1 (§1, §3, §5, §6, §7, §8, §9, §10).
- Hales, Harrison, McLaughlin, Nipkow, Obua, Zumkeller 2010, `10.1007/s00454-009-9148-4`, read as arXiv:0902.0350v1 (§5, §6, §7).
- Solovyev–Hales 2013, `10.1007/978-3-642-38088-4_26`, read as arXiv:1301.1702v1 (intro, §5, Tables 1–3).
- Immler 2018, `10.1007/s10817-017-9448-y`, open-access full text (§1.3, §7, §8).
- Harrison 2007, `10.1007/978-3-540-74591-4_9`, author's PDF (§6).
- Magron et al. 2015, `10.6092/issn.1972-5787/4319`, read as arXiv:1404.7282v4 (Tables I–II and the surrounding text).
- Metadata only (title, authors, venue verified via Crossref): Obua–Nipkow 2009 `10.1007/s10472-009-9168-z`; Solovyev–Hales 2011 `10.1007/978-3-642-22673-1_9`; Muñoz–Narkawicz 2013 `10.1007/s10817-012-9256-3`; Melquiond 2008 `10.1007/978-3-540-71070-7_2`; Martin-Dorel–Melquiond 2016 `10.1007/s10817-015-9350-4` (plus HAL abstract hal-01086460); Brisebarre et al. 2012 `10.1007/978-3-642-28891-3_9`; Roux 2016 `10.1007/s10817-015-9339-z`; Daumas–Lester–Muñoz 2009 `10.1109/TC.2008.213`; Tucker 2002 `10.1007/s002080010018`.

**Execution (2026-11-21; x86-64 Linux workstation, Intel Xeon @ 2.60 GHz, Python 3.13.15, standard library only):**

- `python3 support/flyspeck_log_census.py <scratch-dir>` (default scratch directory `/tmp/flyspeck-logs`) → `support/flyspeck_log_census.out.txt` (network: GitHub API + raw files; about 46 s wall).
- `python3 support/lp_dual_check.py` → `support/lp_dual_check.out.txt`.
- `python3 support/sos_round_check.py` → `support/sos_round_check.out.txt` (toy).
- `python3 support/bounds_toy.py 40000` → `support/bounds_toy.out.txt` (toy; 1 min 8 s wall total).

## Revalidation

- **Nonlinear run totals:** rerun `support/flyspeck_log_census.py` against the pinned Flyspeck revision. It must print 23,237 cases per run, 5,006.1 h and 9,274.9 h, and the five sharp digests missing from both runs. Against a newer revision, first check whether `azure/results/` changed (`git diff --stat <old> <new> -- azure/results`).
- **Import mechanism:** inspect `text_formalization/general/serialization.hl` for `mk_local_inconsistency`, `mk_deserialize_thm` and `Hol.new_axiom`. In the maintained port, check whether the import was replaced by a kernel-level mechanism. That port is not covered by this report.
- **Lorenz status:** open `thys/Ordinary_Differential_Equations/Ex/Lorenz/C1/Lorenz_C1.thy` and check whether `interpretation check_lines_c1` still ends in `oops`. Also check the `Lorenz_C1` timeout in `ROOT`. If the interpretation is discharged, the C1 theorem becomes unconditional apart from `NF`.
- **SOS rounding and termination:** check `Examples/sos.ml` for the `tryfind find_rounding (map num (1--31) @ map pow2 (5--66))` schedule and the `deepen` handler. A change in either alters the failure modes described in Finding 8.
- **Toy probes:** `python3 support/bounds_toy.py 40000` and `python3 support/sos_round_check.py` are deterministic (fixed random-number initialisation). They revalidate only the toy observations.
- **Paper figures** (5000 and 9370 processor-hours; 43,078 LPs in 15 h; Lorenz 131 h 52 min CPU) need no rerun unless a corrected edition appears; check the publisher versions of record.
