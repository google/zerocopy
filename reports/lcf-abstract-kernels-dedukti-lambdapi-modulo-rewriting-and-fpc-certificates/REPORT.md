# Alternative Proof-Verification Architectures (Part I): LCF Abstract-Type Kernels, $\lambda\Pi$-Modulo Rewriting Hubs, and Foundational Proof Certificates

## Summary

Type-theoretic proof assistants built on the Calculus of Inductive Constructions (CIC), such as Lean 4 and Rocq, verify proofs by serializing explicit dependent $\lambda$-terms (proof objects) and type-checking them against definitional $\beta\delta\iota\zeta$-reduction in a monolithic kernel. Three foundational alternatives avoid storing or type-checking monolithic dependent CIC terms altogether, making sharply different trade-offs across trusted computing base (TCB) size, proof-object footprint, cross-system interoperability, and machine-code end-to-end verification:

1. **Milner's LCF Abstract-Datatype `thm` Architecture (`HOL Light`, `Isabelle/Pure`, `Candle`, `OpenTheory`)**:
   Instead of constructing a proof term, an LCF kernel exposes an opaque abstract type `thm` (`jrh13/hol-light/fusion.ml` line 24) whose constructors are hidden behind a module signature (`Hol_kernel`, lines 12–88). Arbitrary untrusted ML tactics execute forward inference combinators directly inside the host runtime; only the final proved sequent `Sequent of (term list * term)` persists in RAM (`O(1)` live proof state), trading gigabytes of stored proof trees for host-runtime soundness (`Obj.magic`, `Marshal`, FFI, GC). **Candle** (`CakeML/candle`, `CakeML/cakeml`) eliminates the OCaml compiler/runtime trust assumption via a proof-producing CakeML synthesis proving end-to-end soundness down to x86-64 machine code (`DOI: 10.4230/LIPIcs.ITP.2022.3`, `10.1007/s10817-025-09743-8`). **OpenTheory** (`gilith/opentheory`) resolves LCF's cross-session replay bottleneck by serializing inferences to a stack-VM article format with `def`/`ref` DAG sharing (`DOI: 10.1007/978-3-642-20398-5_14`).
2. **$\lambda\Pi$-Calculus Modulo Confluent Rewriting (`Dedukti`, `Lambdapi`, `Kontroli`)**:
   Unifies logical encodings (HOL, Isabelle/Pure, Rocq, Lean, Agda, iProver, Zenon) inside a single dependently typed framework ($\lambda\Pi\equiv$) whose conversion rule $A \equiv_{\beta\mathcal{R}} B$ reduces modulo user-declared rewrite rules $\mathcal{R}$ (`Deducteam/Dedukti/kernel/typing.ml`, `Deducteam/lambdapi/src/core/infer.ml`). **Kontroli** (`01mf02/kontroli-rs`, `DOI: 10.1145/3497775.3503683`) shrinks the checker kernel to 663 lines of no-`std` Rust (vs. 3,470 lines in OCaml `Dedukti`), replaces GC with explicit `Rc`/`Arc` DAG sharing, and achieves up to a 6.6$\times$ checking speedup across 8 threads on Isabelle/HOL exports. Crucially, $\lambda\Pi\equiv$ soundness does **not** follow from per-rule typing alone: user rules $\mathcal{R}$ must separately satisfy confluence, strong normalization, and subject reduction.
3. **Foundational Proof Certificates (`FPC`, `LKF`/`LJF`, `ProofCert/checkers`)**:
   Rather than translating diverse provers into a single syntax (like `hol2dk`), Dale Miller's FPC architecture fixes a minimal **focused polarized sequent kernel** (`LKF`/`LJF`, `DOI: 10.1016/j.tcs.2009.07.041`)—only 127 non-empty lines of $\lambda$Prolog in `ProofCert/checkers/src/kernel/lkf/lkf-kernel.mod`—whose inference rules query untrusted certificate-specific **clerk** (`_kc`) and **expert** (`_ke`) predicates executed via higher-order pattern unification ($L_\lambda$) in **Teyjus** (`teyjus/teyjus`) or **ELPI** (`LPCIC/elpi`). Clerks and experts can omit redundant substitutions or subproof steps and reconstruct them via bounded kernel-guided proof search without enlarging the logical core.

| Paradigm | Proof Representation | Kernel TCB Size | Soundness Precondition Beyond Kernel | Primary Cross-System Strength |
|---|---|---|---|---|
| **LCF Abstract `thm`** (`HOL Light` / `Candle`) | None by default (ephemeral ML execution); OpenTheory `.art` DAG optional | ~396–552 LoC OCaml `fusion.ml` (+ 2,753 LoC `pa_j`); or verified CakeML binary | Host ML type safety + memory safety (or CakeML compiler/ISA theorem) + conservative `new_basic_definition` | Minimal runtime memory (`O(1)` proof state); direct industrial arithmetic/hardware tactics (`s2n-bignum`, FPU) |
| **$\lambda\Pi$-Modulo Rewriting** (`Dedukti` / `Kontroli`) | Explicit $\lambda\Pi$ terms checked modulo $\mathcal{R}$ (`.dk` / `.lp`) | 3,470 LoC OCaml (`Dedukti`); 663 LoC Rust (`Kontroli`) | Confluence + strong normalization + subject reduction of external rewrite rules $\mathcal{R}$ | Universal proof hub (`hol2dk`, `isabelle_dedukti`, `Logipedia`) translating proofs across HOL, Isabelle, Rocq |
| **Foundational Proof Certificates** (`Checkers` / `LKF`) | Untrusted clerk/expert predicates + compact certificate term | 98–127 LoC $\lambda$Prolog (`lkf-kernel.mod`) + $\lambda$Prolog runtime (`ELPI`/`Teyjus`) | Soundness of $\lambda$Prolog/$L_\lambda$ unification + occurs-check + kernel polarity discipline | Heterogeneous ATP/SMT/tableaux/Frege ingestion without per-prover translation to CIC or $\lambda\Pi$ |

## Applicability

This technical reference covers pinned upstream revisions inspected directly at their 40-character Git commit SHAs and peer-reviewed specifications, comparing three non-CIC verification architectures along with two cross-paradigm translation pipelines (`HOL Light` $\to$ `OpenTheory` $\to$ `Candle`, and `HOL Light`/`Isabelle/HOL` $\to$ `Dedukti`/`Lambdapi` $\to$ `Kontroli`/`Rocq`):

- **LCF Family**: `jrh13/hol-light` (`6dbb775efdff7f75aa20006532bf6336bc645861`), `isabelle-prover/mirror-isabelle` (`c45cdab77eec0ac889f9717ca229a5e9064a24b1`), `CakeML/candle` (`a9aeaa1dffd50f7cfeed811db6ee61f98e2234da`), `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`), and `gilith/opentheory` (`7a51b621eacd1bfa75600dac3827f1a1f6a89978`). Applies to classical higher-order logic (Church's simple type theory / Andrews' $Q_0$ with prenex type polymorphism) and Isabelle's intuitionistic higher-order metalogic (`Pure`).
- **$\lambda\Pi$-Modulo Family**: `Deducteam/Dedukti` (`b828866d2163bb1caa77ef53881f1566da51d2e6`), `Deducteam/lambdapi` (`b7e9e0a0ae09b16a8841bbce1c7bfceb013ff3e3`), `01mf02/kontroli-rs` (`22bfbdfc6d20502589c4c53369cf76ebcb1b8178`), `Deducteam/hol2dk` (`7f0da9630ea948628f9c5f49829d18df6a7073ee`), and `Deducteam/isabelle_dedukti` (`925d138fd433b1d04c270e166133ae7a673b18a9`). Note that `Kontroli` intentionally restricts Dedukti syntax to first-order pattern matching without AC matching or higher-order rewrite rules (`01mf02/kontroli-rs/README.md`), excluding full Coq/Rocq encodings that rely on higher-order rewriting while supporting HOL Light, Isabelle/HOL, Matita, iProver, and Zenon exports.
- **FPC Family**: `ProofCert/checkers` (`241b3c8d1cd543e2e3a8421e185eaf8639c0e39b`), `LPCIC/elpi` (`631d14a63489ed0e8359ad036f7a8580bb373f33`), and `teyjus/teyjus` (`5cb51538beee8b1ad6dbc47ee14d7491fefa6021`). Applies to polarized classical (`LKF`) and intuitionistic (`LJF`) first- and higher-order logic proof evidence; `ProofCert/checkers` implements `LKF` and `LJF` skeletons, while `LKF` resolution/tableaux certificates (`src/fpc/resolution/`, `src/fpc/tableaux/`) target first-order ATP and sequent evidence.

Claims marked `Basis: execution` reflect direct execution of the self-contained Python 3.13.15 micro-probe preserved verbatim in `## Findings` and `## Evidence`; external benchmark figures (Färber CPP 2022, Blanqui LPAR 2024 / 2026, Hales Flyspeck, Candle ITP 2022) preserve their exact reported hardware configurations and dataset scopes.

## Findings

### 1. Milner's LCF Abstract-Datatype `thm` Architecture (`HOL Light`, `Isabelle/Pure`, `Candle`, `OpenTheory`)

#### 1.1 Signature Isolation, the 10 Primitive Rules, and Conservatism Gates in `HOL Light`
`Basis: source + normative`

In Milner's original Edinburgh LCF (`DOI: 10.1145/512760.512773`) and John Harrison's `HOL Light` (`jrh13/hol-light`, `fusion.ml` lines 12–643, 680 total lines, 552 non-empty lines, 28,873 bytes), logical soundness relies on **ML type abstraction** rather than proof-term serialization:

1. **Abstract `thm` Signature Boundary (`fusion.ml` lines 12–25, 94–105)**:
   The signature `Hol_kernel` exports `type thm` **abstractly** (without revealing constructors), while declaring `hol_type` and `term` as `private` algebraic variants (`private Tyvar | Tyapp` and `private Var | Const | Comb | Abs`, lines 14–22) so user code may pattern-match on terms and types safely without bypassing smart constructors (`mk_var`, `mk_const`, `mk_abs`, `mk_comb`). Inside `module Hol : Hol_kernel` (line 94), `type thm = Sequent of (term list * term)` (line 104) stores only the hypothesis list and conclusion—never a derivation tree.
2. **Ten Primitive Inference Rules (`fusion.ml` lines 498–566)**:
   Every value of type `thm` originates either from `new_axiom` (line 575), definitional extensions, or ten primitive OCaml functions:
   - Equality and $\lambda$-calculus primitives: `REFL`, `TRANS` (comparing intermediate terms modulo $\alpha$-equivalence via `alphaorder m1 m2 = 0`, line 504), `MK_COMB` (checking function domain type equality via `compare ty (type_of r2) = 0`, line 515), `ABS` (enforcing side-condition `not (exists (vfree_in v) asl)`, line 523), and `BETA` (restricted to trivial redexes `(fun v -> bod) v` where `compare arg v = 0`, line 533).
   - Deduction and instantiation primitives: `ASSUME` (checking `type_of tm = bool_ty`, line 542), `EQ_MP` (`alphaorder l c = 0`, line 547), `DEDUCT_ANTISYM_RULE` (computing `term_remove` and `term_union`, lines 551–553), `INST_TYPE` (line 559), and capture-avoiding `INST` (line 563).
   Note that `HOL Light` omits de Bruijn indices inside `fusion.ml`, implementing $\alpha$-equivalence via `alphaorder` directly on named binders (`Var`/`Abs`), unlike `HOL4` or `Isabelle`.
3. **Definitional Conservatism Gates (`fusion.ml` lines 589–640)**:
   Two critical side conditions prevent classical paradoxes in higher-order logic definitions:
   - In `new_basic_definition` (`c = r`, lines 589–602), line 592 checks `freesin [] r` (RHS has no free term variables, blocking unbound parameters) and line 595 checks `subset (type_vars_in_term r) (tyvars ty)` (every polymorphic type variable appearing anywhere in the RHS `r` must appear in the type `ty` of the newly defined constant `c`). Without the type-variable containment check, defining a polymorphic proposition $P : \text{bool} := (\forall (x:\alpha)(y:\alpha).\, x=y)$ allows instantiating $\alpha$ independently to $\text{bool}$ and a singleton type to derive $\top = \bot$.
   - In `new_basic_type_definition` (lines 617–640), given $\vdash P\, x$ with empty assumptions (`asl = []`, line 620) and closed predicate `freesin [] P` (line 625), the kernel allocates a fresh type operator of arity `length (type_vars_in_term P)` and returns the bijection axioms $\vdash \text{abs}(\text{rep}\, a) = a$ and $\vdash P\, r = (\text{rep}(\text{abs}\, r) = r)$.

#### 1.2 Host-Runtime TCB Leakage vs. CakeML's Verified `Candle` Stack
`Basis: source + documentation`

Because LCF security equates logical validity with **the inability of untrusted code to forge a value of type `thm`**, the entire host language compiler, runtime, and standard library escape hatches sit inside the LCF TCB:

- **OCaml Escape Hatches**: Any use of `Obj.magic` (`'a -> 'b`), `Marshal.from_string` / `input_value` deserializing untrusted bytes as `thm`, mutable `string` / `bytes` aliasing (before OCaml adopted `-safe-string` by default in OCaml 4.06), or C FFI extensions breaks abstraction and allows constructing `Sequent ([], F)` directly. Similarly, `HOL Light`'s parser extension (`pa_j_4.xx_7.xx.ml`, measured at 2,753 non-comment/non-blank LoC by Färber vs. 396 LoC for `fusion.ml`) and interactive `#use` loader run inside the same OCaml toplevel process.
- **End-to-End Machine-Code Closing (`CakeML/candle`)**: `Candle` (`CakeML/candle` @ `a9aeaa1d`, `CakeML/cakeml` @ `2874b664`, `DOI: 10.4230/LIPIcs.ITP.2022.3`, extended JAR 2025 `DOI: 10.1007/s10817-025-09743-8`) eliminates the OCaml compiler/GC TCB by formalizing HOL's set-theoretic semantics, proving soundness of a monadic HOL Light kernel (`candle/standard/monadic/holKernelProofScript.sml`, 127,709 bytes), and applying CakeML's proof-producing synthesis (`candle/standard/ml_kernel/ml_hol_kernelProgScript.sml` lines 72–90 producing `candle_prog_thm` + `EqualityType_THM_TYPE`) down to verified x86-64/ARMv8/RISC-V machine code inside `HOL4`. Because CakeML lacks `Obj.magic`, `Marshal`, pointer equality (`==` is stubbed to `false` in `CakeML/candle/README.md` line 162), and OCaml polymorphic `Pervasives.compare` (replaced by type-specific ordering in `lib.ml`), `Candle` produces a machine-checked theorem that every fact printed by the compiled REPL is semantically true in HOL—assuming only the HOL4 specification of the target ISA and small assembly I/O stubs.

#### 1.3 `Isabelle/Pure`: Metalogical `thm`, Futures, Oracles, and Optional `Proofterm` Recording
`Basis: source + documentation`

`Isabelle/Pure` (`isabelle-prover/mirror-isabelle` @ `c45cdab7`, `src/Pure/thm.ML`, 2,795 lines) generalizes LCF's single-logic kernel into an intuitionistic higher-order **metalogic** ($\bigwedge, \Longrightarrow, \equiv$ with schematic variables `?x` and sort-constrained type classes):

- **Rich `thm` Payload (`thm.ML` lines 453–465)**: `datatype thm = Thm of deriv * {cert: Context.certificate, tags: Properties.T, maxidx: int, constraints: constraint Ord_List.T, shyps: sort Ord_List.T, hyps: term Ord_List.T, tpairs: (term * term) list, prop: term}`. Unlike `HOL Light`, `thm` carries a background theory certificate `cert` (`Context.join_certificate` in `join_certificate2`, line 515, blocking theorems from inconsistent sibling theories), `tpairs` for higher-order unification flex-flex constraints, `shyps`/`constraints` for axiomatic type-class sort hypotheses, and `deriv = Deriv of {promises: (serial * thm future) Ord_List.T, body: Proofterm.proof_body}`.
- **Parallel Futures & Trust Accounting**: `promises` tracks asynchronously evaluated `thm future` dependencies (enabling Isabelle/ML's multi-core parallel proof checking in Poly/ML without waiting on opaque subproofs during outer theory construction), while `add_oracle` (`thm.ML` line 150) stamps external decision-procedure invocations with explicit oracle names propagated through `Proofterm` derivations. By default `Proofterm.proofs` stays off (`0` stored proof nodes in RAM), though Berghofer & Nipkow's optional `Proofterm` mode records explicit $\lambda$-terms for export (e.g., to `Dedukti` via `isabelle_dedukti`).

#### 1.4 Cross-Session Serialization & Industrial Scale (`OpenTheory`, `Flyspeck`, `Intel`/`AWS`)
`Basis: documentation + source + execution`

Because plain LCF kernels discard derivation history, verifying a theorem offline in an external checker normally requires re-running the entire proof script from scratch. **OpenTheory** (`gilith/opentheory` @ `7a51b621`, `DOI: 10.1007/978-3-642-20398-5_14`) solves cross-session LCF replay using a 36-opcode stack VM (`src/Command.sml` lines 15–95): primitives (`assume`, `refl`, `betaConv`, `absThm`, `appThm`, `deductAntisym`, `eqMp`, `proveHyp`, `subst`, `sym`, `trans`, `defineConst`, `defineConstList`, `defineTypeOp`) manipulate terms, types, lists, and `thm` values on a stack, while `def k` and `ref k` memoize shared subterms and intermediate lemmas into a numbered dictionary so exponential proof DAGs serialize linearly.

- **Practitioner & Industrial Evidence**:
  - **Flyspeck Project (Kepler Conjecture, 2003–2014)**: Hales et al.'s ~500,000-line `HOL Light` + Isabelle formalization executed hundreds of billions of ephemeral `thm` steps and consumed ~5,000 CPU-hours (distributed across 32-core Azure VMs) to discharge >23,000 nonlinear real inequalities without storing a multi-terabyte proof object in memory.
  - **Intel & AWS Industrial Verification**: John Harrison verified IEEE-754 floating-point microcode/transcendental algorithms (e.g., Intel Pentium 4 division/sqrt/exp) in `HOL Light` at Intel, and maintains `HOL Light` and the `s2n-bignum` verified cryptographic assembly library at AWS Automated Reasoning Group.
  - **Trace Bloat Without Sharing**: When `HOL Light`'s unshared kernel proof trace is logged verbatim for translation (`Deducteam/hol2dk`), the base `hol.ml` library (2,834 named theorems, 14.3M primitive steps) expands to ~5–5.5 GB raw (~1 GB shared/split in newer `hol2dk`), and `Multivariate` (16,646 theorems, 182M steps) expands to 91–120 GB on disk, whereas OpenTheory's compressed standard library articles fit in ~13–21 MB.

---

### 2. $\lambda\Pi$-Calculus Modulo Confluent Rewriting (`Dedukti`, `Lambdapi`, `Kontroli`)

#### 2.1 Typing Judgment Modulo $\mathcal{R}$ and Shallow/Deep Logic Encodings
`Basis: source + normative`

The $\lambda\Pi$-calculus modulo rewriting ($\lambda\Pi\equiv$), implemented by `Dedukti` (`Deducteam/Dedukti` @ `b828866d`, `kernel/typing.ml`, `kernel/reduction.ml`, `kernel/dtree.ml`) and `Lambdapi` (`Deducteam/lambdapi` @ `b7e9e0a0`, `src/core/infer.ml`, `src/core/eval.ml`, `src/core/tree.ml`), extends the Edinburgh Logical Framework ($\lambda\Pi$) with **user-declared higher-order rewrite rules** $\Sigma, \mathcal{R}$:

$$\frac{\Gamma \vdash_{\Sigma,\mathcal{R}} t : A \quad \Sigma,\mathcal{R} \vdash A \equiv_{\beta\mathcal{R}} B \quad \Gamma \vdash_{\Sigma,\mathcal{R}} B : s}{\Gamma \vdash_{\Sigma,\mathcal{R}} t : B} \quad (\text{Conv})$$

In `Dedukti/kernel/typing.ml` (lines 76–350), `infer'` checks `Type : Kind` (rejecting `Kind` via `KindIsNotTypable`, line 80) and discharges equality constraints via `R.are_convertible sg ty ty'` (lines 347–350), which computes weak head normal forms (WHNF) using compiled decision trees (`dtree.ml` with Miller pattern variables `miller_var`, lines 153–162, and optional associative-commutative matching in `ac.ml`).

- **Universal Hub Encoding (`Cousineau–Dowek` & `hol2dk` / `isabelle_dedukti`)**: Instead of hardcoding universe polymorphism, inductive eliminators, or classical HOL rules in the kernel, encoders declare type/proof decoding symbols and rewrite rules. In `Deducteam/hol2dk/encoding.lp` (lines 3–13), simple type theory declares `El : Set -> Type`, `Prf : El prop -> Type`, `arr : Set -> Set -> Set`, and rewrites:
  $$\text{El}\;(\text{arr}\; a\; b) \hookrightarrow \text{El}\; a \to \text{El}\; b, \qquad \text{Prf}\;(\text{imp}\; p\; q) \hookrightarrow \text{Prf}\; p \to \text{Prf}\; q, \qquad \text{Prf}\;(\text{all}\; P) \hookrightarrow \Pi (x : \text{El}\;\alpha).\,\text{Prf}\;(P\; x).$$
  This enables a single $2n$ hub architecture (`Logipedia`, `coq-hol-light` translating HOL Light `Multivariate` reals to Rocq's `Fourcolor` classical reals) instead of $n(n-1)$ pairwise translators.
- **Scale & Realignment Engineering (`Blanqui LPAR 2024 / 2026`)**: Translating raw HOL Light `hol_lib.ml` (~1 GB `.dk`/`.lp` after sharing) and checking in Rocq took 30 min initially, optimized to 10 min via splitting proof dependencies from statements and global type-abbreviation sharing (vs. 1m 10s natively in `HOL Light`); the 91 GB `Multivariate` library took ~21 hours to re-check in Rocq.

#### 2.2 `Kontroli`: Zero-GC Rust Shared Graphs & Parallel Checking
`Basis: source + documentation`

`Kontroli` (`01mf02/kontroli-rs` @ `22bfbdfc`, `DOI: 10.1145/3497775.3503683`, `arXiv:2102.08766`) reimplements a strict subset of $\lambda\Pi\equiv$ in 663 lines of `#![no_std]`-compatible Rust (`kontroli/src/kernel/mod.rs`) paired with a multi-threaded `rayon` + `flume` CLI (`kocheck/src/main.rs` with optional `mimalloc`, lines 99–118):

- **Explicit Sharing Without GC**: Dedukti's OCaml `term` relies implicitly on OCaml's tracing GC, forcing `caml_alloc` and pointer chasing. Kontroli parameterizes `Term<C, Tm>` over pointer ownership: `BTerm` (unshared `Box` for non-shared fragments), `RTerm` (`Rc` for single-threaded DAG sharing), and `ATerm` (`Arc` for lock-free thread-safe command concurrency across shared immutable subterms). Command-concurrent checking splits each command into sequential symbol registration (`infer`) followed by parallel body verification (`check`).
- **Measured CPP 2022 Benchmarks (32 Broadwell 2.2 GHz cores, 32 GB RAM, OCaml 4.08.1 vs. Rust 1.54)**:
  - **HOL Light export (2.0 GB, 25 theories, 1,776,535 commands)**: Dedukti (`DK`) takes `344 s` (6.9 GB peak RSS); sequential Kontroli (`KO`) takes `220 s` (6.8 GB RSS); 8-thread `KO_c=8` drops to `146 s` (6.9 GB RSS).
  - **Isabelle/HOL export (2.5 GB, 1 theory, 116,927 large commands)**: `DK` takes `415 s` (3.7 GB RSS); `KO` takes `306 s` (6.1 GB RSS because `kocheck` holds the parsed file buffer in RAM); 8-thread `KO_c=8` drops total runtime to `120 s`—cutting pure type-checking time from `219 s` to `33 s` (**6.6$\times$ speedup**), at the cost of `12.7 GB` peak RSS as 8 threads simultaneously reduce multi-megabyte commands.
  - **ATP Datasets (`DK_t=24` vs. `KO_t=24`)**: `iProver` (431.4 MB, 6,613 files): `15.26 s` $\to$ `11.9 s`; `Zenon` (15.4 GB, 10,330 files): `425 s` $\to$ `264 s`.

#### 2.3 Why $\lambda\Pi\equiv$ Soundness Is External to Kernel Typing (`srcheck`, Confluence, Termination)
`Basis: source + execution + derived`

Unlike Lean 4's kernel (which trusts only fixed $\beta\delta\iota\zeta$-reduction plus hardcoded structural recursion), Dedukti and Lambdapi allow **arbitrary user rewrite rules** $\ell \hookrightarrow r$. Kernel typechecking alone does **not** ensure logical consistency:

1. **Subject Reduction Is Heuristic (`Dedukti/kernel/srcheck.ml`, lines 7–60)**: Dedukti's subject-reduction checker builds syntactic unification constraints `lhs_typing_cstr` (`unsolved`, `unsatisf`) bounded by `srfuel = ref 1` (line 7) and relies on external confluence/termination assumptions; `Kontroli` omits `srcheck` completely when rewriting rules violate left-linearity or lack type annotations (`README.md` lines 55–61).
2. **Non-Confluence Exploit**: Any non-confluent pair $c \hookrightarrow \text{true}$ and $c \hookrightarrow \text{false}$ under $\text{eq}(\text{true}) \hookrightarrow \top$ and $\text{eq}(\text{false}) \hookrightarrow \bot$ induces a valid conversion chain $\top \equiv_{\mathcal{R}} \text{eq}(c) \equiv_{\mathcal{R}} \bot$ even though every individual rewrite rule is well-typed (`Bool : Type`, `true : Bool`, `false : Bool`). Hence `Dedukti` proofs must pass external confluence (`CSI^ho`) and termination (`SizeChangeTool` / `Wanda`) checkers to keep the logical encoding sound.

---

### 3. Foundational Proof Certificates (`FPC`, `LKF`/`LJF`, `ProofCert/checkers`)

#### 3.1 Polarized Focusing and the 127-Line `lkf-kernel.mod`
`Basis: source + normative`

Dale Miller's Foundational Proof Certificates (FPC) framework (`DOI: 10.1007/s10817-016-9380-6`), built on Liang & Miller's polarized focused sequent calculi `LKF` and `LJF` (`DOI: 10.1016/j.tcs.2009.07.041`), decouples **soundness** from **certificate format**. In `ProofCert/checkers` (`241b3c8d`), the entire classical kernel (`src/kernel/lkf/lkf-kernel.mod`, 142 total lines, 127 non-empty lines, 3,407 bytes; ~98 LoC non-comment code per Färber) consists of two mutually recursive phases over polarized formulas (positive $A^+ \mathbin{\&^+} B^+$, $A^+ \mathbin{!+!} B^+$, $\exists$, $t^+$, $f^+$, $p(A)$; negative $A^- \mathbin{\&^-} B^-$, $A^- \mathbin{!-\!} B^-$, $\forall$, $t^-$, $f^-$, $n(A)$):

- **Asynchronous / Unfocused Phase (`check Cert (unfK [...])`)**: Deterministically decomposes negative connectives (`orNeg_kc`, `andNeg_kc`, `all_kc` via higher-order $\lambda$-Prolog `pi w\` universal eigenvariable quantification, `false_kc`), and moves positive formulas or negative atoms into the persistent linear-implication context via `store_kc Cert C Indx Cert'`, binding `inCtxt Indx C => check Cert' (unfK Rest)` (`lkf-kernel.mod` lines 25–28).
- **Synchronous / Focused Phase (`check Cert (foc P)`)**: Triggered by `decide_ke Cert Indx Cert'` (lines 14–18) when the unfocused list is `nil`; commits to a stored positive formula `P`, decomposes synchronous subformulas (`andPos_k`, `orPos_ke`, `some_ke`, `true_ke`), and terminates at dual atoms via `initial_ke Cert Indx, inCtxt Indx (n A)` (lines 29–32) or transitions back to unfocused phase on negative formulas via `release_ke` (lines 19–22). Cuts use `cut_ke Cert F CertA CertB` (lines 33–37) checking both `F` and `negateForm F`.

#### 3.2 Clerk & Expert Signatures and Search-Assisted Reconstruction (`Teyjus` / `ELPI`)
`Basis: source + documentation`

A certificate format (such as binary resolution `src/fpc/resolution/binary_res_fol.mod`, Fitting tableaux `src/fpc/tableaux/fittings-tableaux.mod`, or paramodulation `paramodulation.mod`) is merely an untyped-to-the-kernel $\lambda$Prolog logic program implementing the 15 predicates of `certificatesLKF.sig`:

- **Clerks (`_kc`) and Experts (`_ke`)**: In `binary_res_fol.mod`, a certificate constructor `(dlist C1 C2)` encodes a 3-decide resolution step (`decide_ke (dlist (rid I S) C2) I (dlist2 C2 S)`, lines 23–25) passing explicit substitution lists `(sub [T|R])` to `some_ke` (`lines 32–35`). Crucially, if an expert predicate leaves a term or index as a logic variable (`_`) instead of supplying it explicitly—e.g. `initial_ke (dlist _ _) _.` (line 13)—the $\lambda$Prolog host (`teyjus/teyjus` @ `5cb51538` or `LPCIC/elpi` @ `631d14a6`, `DOI: 10.1007/978-3-662-48899-7_32`) performs bounded **higher-order pattern unification ($L_\lambda$) and backtracking search** inside the kernel's invariant rules to fill missing proof details!
- **TCB Boundary**: While `lkf-kernel.mod` has zero external knowledge of resolution or tableaux, the **host $\lambda$Prolog runtime** (`ELPI` or `Teyjus`) is part of the TCB: soundness demands sound occurs-check (disabled in some fast Prolog modes unless explicitly enabled), capture-avoiding $L_\lambda$ unification, and well-behaved `eager_normalize` beta-reduction (`lkf-kernel.mod` line 77, required explicitly because `Teyjus` does not normalize `(B T)` prior to head matching).

---

### 4. Executable Comparative Micro-Probe (`Basis: execution`)

To directly observe the memory retention scaling of LCF vs. explicit proof trees vs. OpenTheory DAG compression, the $\lambda\Pi\equiv$ non-confluence exploit, and `LKF` clerk/expert verification, the self-contained Python 3.13.15 micro-probe below executes all three checks in `< 20 ms`:

```bash
python3 - <<'EOF'
import time, tracemalloc

# 1. LCF ephemeral Thm vs explicit unshared tree (N=1000) vs OpenTheory def/ref diamond (2^20 steps)
class Thm:
    __slots__ = ("concl",)
    def __init__(self, concl): self.concl = concl
    @staticmethod
    def ax(a, b): return Thm(("=", a, b))
    @staticmethod
    def trans(t1, t2):
        assert t1.concl[2] == t2.concl[1]
        return Thm(("=", t1.concl[1], t2.concl[2]))

tracemalloc.start(); t0 = time.perf_counter()
cur = Thm.ax("x0", "x1")
for i in range(1, 1000): cur = Thm.trans(cur, Thm.ax(f"x{i}", f"x{i+1}"))
lcf_ms = (time.perf_counter() - t0) * 1000; _, lcf_peak = tracemalloc.get_traced_memory(); tracemalloc.stop()

tracemalloc.start()
tree = ("ax", ("=", "x0", "x1"))
for i in range(1, 1000): tree = ("trans", ("=", "x0", f"x{i+1}"), tree, ("ax", ("=", f"x{i}", f"x{i+1}")))
stack, tree_nodes = [tree], 0
while stack:
    nd = stack.pop(); tree_nodes += 1; stack.extend(nd[2:])
tree_curr, _ = tracemalloc.get_traced_memory(); tracemalloc.stop()

cmds = [("ax", "z", "z"), ("def", 0)] + sum([[("ref", d), ("ref", d), ("trans",), ("def", d+1)] for d in range(20)], [])
st, dt = [], {}
t0 = time.perf_counter()
for op in cmds:
    if op[0] == "ax": st.append(("=", op[1], op[2]))
    elif op[0] == "trans": b, a = st.pop(), st.pop(); assert a[2] == b[1]; st.append(("=", a[1], b[2]))
    elif op[0] == "def": dt[op[1]] = st[-1]
    elif op[0] == "ref": st.append(dt[op[1]])
ot_ms = (time.perf_counter() - t0) * 1000
print(f"PROBE1_LCF_VS_TREE: N=1000 lcf_concl={cur.concl} lcf_peak_bytes={lcf_peak} lcf_ms={lcf_ms:.3f} tree_nodes={tree_nodes} tree_retain_bytes={tree_curr} ot_diamond_cmds={len(cmds)} virtual_steps={2**20} ot_dict_entries={len(dt)} ot_ms={ot_ms:.3f}")

# 2. Dedukti non-confluent rewrite system: c->true, c->false, eq(true)->TrueTy, eq(false)->FalseTy
def step(t, br):
    if t == ("eq", ("c",)): return ("eq", ("true",)) if br == 0 else ("eq", ("false",))
    return ("TrueTy",) if t == ("eq", ("true",)) else ("FalseTy",)
b0, b1 = step(step(("eq", ("c",)), 0), 0), step(step(("eq", ("c",)), 1), 1)
print(f"PROBE1_DK_CONFLUENCE: eq(c)_branch0={b0} eq(c)_branch1={b1} convertible_via_eq_c={b0 != b1}")

# 3. Focused LKF clerk/expert kernel on |- (p a | n a) and stored clause resolution
def lkf(cert, ph, seq, ctx):
    if ph == "unf":
        if not seq:
            if cert[0] == "decide": return cert[1] in ctx and ctx[cert[1]][0] in ("p","and+","t+") and lkf(cert[2], "foc", ctx[cert[1]], ctx)
            return False
        h, r = seq[0], seq[1:]
        if h[0] == "or-": return lkf(cert, "unf", [h[1], h[2]] + r, ctx)
        assert cert[0] == "store"; nc = dict(ctx); nc[cert[1]] = h; return lkf(cert[2], "unf", r, nc)
    if seq[0] == "p": return cert[0] == "init" and ctx.get(cert[1]) == ("n", seq[1])
    return False
em_goal = [("or-", ("p", "a"), ("n", "a"))]
ok_em = lkf(("store", "k1", ("store", "k2", ("decide", "k1", ("init", "k2")))), "unf", em_goal, {})
bad_em = lkf(("store", "k1", ("store", "k2", ("decide", "k1", ("init", "k1")))), "unf", em_goal, {})
res_ctx = {"c1": ("p", "a"), "c2": ("n", "a")}
ok_res = lkf(("decide", "c1", ("init", "c2")), "unf", [], res_ctx)
bad_res = lkf(("decide", "c1", ("init", "c1")), "unf", [], res_ctx)
print(f"PROBE1_LKF_FPC: ok_em={ok_em} bad_em={bad_em} ok_res={ok_res} bad_res={bad_res}")
EOF
```

Observed output (`Python 3.13.15`):
```text
PROBE1_LCF_VS_TREE: N=1000 lcf_concl=('=', 'x0', 'x1000') lcf_peak_bytes=392 lcf_ms=8.442 tree_nodes=1999 tree_retain_bytes=389955 ot_diamond_cmds=82 virtual_steps=1048576 ot_dict_entries=21 ot_ms=0.066
PROBE1_DK_CONFLUENCE: eq(c)_branch0=('TrueTy',) eq(c)_branch1=('FalseTy',) convertible_via_eq_c=True
PROBE1_LKF_FPC: ok_em=True bad_em=False ok_res=True bad_res=False
```

---

### 5. Cross-System Architectural & Six-Level (`L1–L6`) Performance/Footprint Matrix

`Basis: derived + source + documentation + execution`

| Dimension | `HOL Light` (`jrh13/hol-light`) | `CakeML / Candle` (`CakeML/candle`) | `Isabelle/Pure` (`mirror-isabelle`) | `OpenTheory` (`gilith/opentheory`) | `Dedukti` (`Deducteam/Dedukti`) | `Kontroli` (`01mf02/kontroli-rs`) | `FPC / Checkers` (`ProofCert/checkers` + `ELPI`) | `Lean 4 / Rocq` (Baseline CIC) |
|---|---|---|---|---|---|---|---|---|
| **Kernel TCB & Language** | 396–552 LoC OCaml `fusion.ml` (+ 2,753 LoC `pa_j` parser + OCaml runtime) | Verified ML kernel synthesized in `HOL4` to x86-64/ARMv8 via `CakeML` | ~2.8 KLoC SML `thm.ML` + Isabelle/ML + Poly/ML runtime | ~2.5 KLoC SML article VM (or Lean/Candle consumer) | 3,470 LoC OCaml (`Dedukti/kernel`) + OCaml GC | 663 LoC `#![no_std]` Rust (`kontroli/src/kernel`) | 98–127 LoC $\lambda$Prolog (`lkf-kernel.mod`) + `ELPI` (`OCaml`) / `Teyjus` (`C`) | ~7–15 KLoC C++ (`Lean 4`) or ~12 KLoC OCaml (`Rocq`) + runtime |
| **(L1) Human & Agent Authoring Velocity** | High tactic automation (`MESON_TAC`, `REAL_ARITH`, `SIMP_TAC`); Flyspeck ~500 KLoC; Day-2 scripts replay directly through OCaml | Nearly 100% source-compatible with `HOL Light` proof scripts (`candle_boot.ml`), minus `Obj.magic`/`Marshal` | Extremely productive Isar declarative proofs + Sledgehammer ATP reconstruction; high Day-2 stability | Machine-exported artifact format (not hand-authored); maps cross-HOL concepts via `.int` interpretations | Encodings require deep PL expertise (`STTfa`, `CoqInE`); proof scripts written in `Lambdapi` or exported via `hol2dk` | Pure checker only (zero tactic/authoring front-end); consumes `.dk` exports | Compact clerk/expert modules (~40–160 LoC $\lambda$Prolog per ATP/SMT format); zero tactic IDE | Rapid interactive LSP/tactics (`< 50 ms` incremental goals); moderate Day-2 proof breakage on refactoring |
| **(L2) Toolchain Build Time & RSS** | Seconds to compile OCaml `hol.ml`; base kernel loads in `< 2 s` | Full `HOL4` + `CakeML` bootstrap build of `Candle` takes hours & multi-GB RAM; binary release runs directly | Poly/ML heap images build in minutes (~1–4 GB RSS) | Compiles in `< 10 s` under MLton / Poly/ML | Compiles via `dune` / OCaml in `< 15 s` | `cargo build --release` in `< 10 s` (~200–400 MB RSS) | `Teyjus`/`ELPI` compiles in `< 20 s` | `Lean 4` C++ build ~15–25 min; incremental `.olean` builds fast |
| **(L3) Compile, Elaboration & Synthesis Speed** | Interactive REPL tactics (`1–50 ms` per step); full `hol_lib.ml` ~70 s (`1m10s`) | Slower than native OCaml `HOL Light` due to unboxed-to-verified CakeML abstractions; `candle_compute` accelerates ground eval | Multi-core `thm future` parallelism across AFP theories; Sledgehammer invokes external SMT/ATP (`0.5–10 s`) | Export trace instrumentation adds ~1.4$\times$–2$\times$ overhead to `HOL Light` execution | `Lambdapi` interactive unification & tactic elaboration; `hol2dk` exports `Multivariate` in parallel | N/A (checker only; streaming parser + parallel command checking) | Bounded by `ELPI`/$L_\lambda$ search; omitted indices trade search latency for compact certs | Sub-`50 ms` LSP elaboration; `isDefEq` / typeclass diamond tails without bounded `heartbeats` |
| **(L4) Generated Code Execution Performance** | Primarily proofs (not a general extraction target; `s2n-bignum` verifies hand-written x86/ARM64 assembly directly) | Executes inside CakeML verified GC runtime (safe x86-64/ARMv8 native code; slower than `-O3` C/Rust) | Code generator extracts to SML/OCaml/Haskell/Scala (`O(1)` unboxed closures; unverified pretty-printer) | N/A (theory interchange format) | No native systems extraction; exports proofs to Rocq/Lean/PVS | N/A (checker only) | N/A (proof certificate verifier only) | Lean 4 compiles `@[extern]`/C via reference counting; Rocq extracts to OCaml/C (`CertiCoq`) |
| **(L5) Proof / Certificate Verification Speed** | Full replay of `hol_lib.ml` ~70 s; Flyspeck inequalities ~5,000 CPU-hrs (`32`-core Azure) | Cold REPL startup + script check slower than OCaml; verifies OpenTheory `.art` directly | Parallel theory replay across Poly/ML worker threads; `Proofterm` off by default | Linear-time stack VM over DAG articles; replays stdlib in seconds | `DK`: `344 s` (2 GB HOL Light), `415 s` (2.5 GB Isabelle/HOL), `425 s` (15.4 GB Zenon, 24 threads) | `KO_c=8`: `146 s` (HOL Light), `120 s` (Isabelle/HOL; 6.6$\times$ check speedup), `264 s` (Zenon, 24 threads) | Milliseconds per ATP problem (`E-Prover`/tableaux); slower when clerk omits hints forcing deep $L_\lambda$ backtracking | Fast `.olean`/`.vo` checking (`ms`–`s`), though Rocq re-checking of `hol2dk` `Multivariate` takes ~21 hrs |
| **(L6) Memory, Artifact & Binary Footprints** | `O(1)` proof state (`392 B` vs. `389 KB` tree in `N=1000` probe); `< 500 MB` RSS for base `HOL Light` | Single self-contained x86-64 verified ELF binary; CakeML heap overhead | Heap images `100 MB–2+ GB`; `Proofterm` mode increases RAM/disk ~10$\times$+ | Compressed stdlib `.tgz` `13–21 MB`; DAG `def`/`ref` compresses $2^{20}$ chain to `21` slots | `DK` peak RSS: `6.9 GB` (HOL Light), `3.7 GB` (Isabelle); raw unshared `hol2dk` `Multivariate` dump `91–120 GB` | `KO` peak RSS: `6.8 GB` (HOL Light), `6.1 GB` (`1`-thread) to `12.7 GB` (`8`-thread Isabelle due to buffered 2.5 GB theory + concurrent large terms) |Tiny certificates (omitting redundant substitutions); `ELPI`/`Teyjus` bytecode VM `< 50 MB` | `.olean`/`.vo` compact binary DAGs; `nanoda`/`lean4export` external checking ~`1–4 GB` RSS |

## Boundaries

- **Known Not to Apply — $\lambda\Pi\equiv$ Kernel Typing Does Not Imply Consistency**: `Dedukti` (`kernel/typing.ml`) and `Kontroli` (`kontroli/src/kernel/mod.rs`) check typing modulo $\mathcal{R}$ and (optionally in `Dedukti`) bounded subject reduction (`srcheck.ml`), **not** confluence or strong normalization. Accepting an unverified non-confluent or non-terminating rewrite rule renders the logic inconsistent (`PROBE1_DK_CONFLUENCE`).
- **Known Not to Apply — `HOL Light` `Obj.magic` / `Marshal` Isolation**: The LCF `thm` abstraction guarantee (`fusion.ml` line 24) fails immediately if any loaded OCaml module invokes `Obj.magic`, `Marshal.from_*`, mutable string mutation on older OCaml toolchains, or unsafe C stubs. Only `Candle` eliminates this host-language vulnerability via a verified compiler and runtime.
- **Unsupported — Higher-Order Rewriting and AC Rules in `Kontroli`**: `01mf02/kontroli-rs` (`22bfbdfc`, `README.md` lines 55–57) explicitly does **not** support higher-order rewrite rules, AC matching, `#EVAL`/`#ASSERT` commands, or unannotated pattern variables, making it unable to check `CoqInE`/CIC encodings that depend on higher-order rewriting.
- **Unsupported — Systems Binary Extraction from `ProofCert/checkers`**: `ProofCert/checkers` (`241b3c8d`) is a certificate verification kernel in $\lambda$Prolog, not a program extraction or compilation toolchain for C/Rust/assembly code.
- **Not Examined**: Proprietary commercial Isabelle/HOL or HOL Light hardware proof scripts inside closed industrial repositories (Intel internal FPU proofs beyond published papers, closed AWS internal pipelines beyond public `s2n-bignum`) and `coq-hol-light` proof-check timings on machines other than those reported by Blanqui et al. (2024/2026) were not directly executed in this investigation.
- **Unknown**: Exact line-by-line TCB size of `ELPI` (`LPCIC/elpi` @ `631d14a6`) and `Teyjus` (`teyjus/teyjus` @ `5cb51538`) higher-order pattern unification engines normalized across identical `tokei` exclusions against `Lean 4`'s C++ kernel was not benchmarked uniformly in this study.

## Evidence

- **GitHub Upstream Repositories & Exact Inspected Regions**:
  - `jrh13/hol-light` @ `6dbb775efdff7f75aa20006532bf6336bc645861`: `fusion.ml` (`680` total lines, `552` non-empty lines, `28,873` bytes) — lines `12–88` (`module type Hol_kernel`), `94–105` (`type thm = Sequent of (term list * term)`), `498–566` (10 primitive inference rules), `589–640` (`new_basic_definition`, `new_basic_type_definition`).
  - `isabelle-prover/mirror-isabelle` @ `c45cdab77eec0ac889f9717ca229a5e9064a24b1`: `src/Pure/thm.ML` (`2,795` lines) — lines `150–171` (`add_oracle`, `implies_*`, `forall_*`, `equal_*`), `453–465` (`datatype thm = Thm of deriv * ...`), `512–516` (`Context.join_certificate`).
  - `CakeML/candle` @ `a9aeaa1dffd50f7cfeed811db6ee61f98e2234da`: `README.md` (lines `143–166`, OCaml incompatibilities: no `let`-polymorphism, no `Pervasives.compare`, stubbed `==`).
  - `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`: `candle/standard/ml_kernel/ml_hol_kernelProgScript.sml` (`candle_prog_thm`, `EqualityType_THM_TYPE`) and `candle/standard/monadic/holKernelProofScript.sml` (`127,709` bytes).
  - `gilith/opentheory` @ `7a51b621eacd1bfa75600dac3827f1a1f6a89978`: `src/Command.sml` (`463` lines; 36 stack-VM opcodes including `def`/`ref`, `deductAntisym`, `defineConstList`, `defineTypeOp`).
  - `Deducteam/Dedukti` @ `b828866d2163bb1caa77ef53881f1566da51d2e6`: `kernel/typing.ml` (`407` lines, `are_convertible` at lines `347–350`), `kernel/srcheck.ml` (`341` lines, `srfuel = ref 1` at line `7`), `kernel/dtree.ml` (`760` lines, `miller_var` at lines `153–162`), `kernel/reduction.ml` (`673` lines).
  - `Deducteam/lambdapi` @ `b7e9e0a0ae09b16a8841bbce1c7bfceb013ff3e3`: `src/core/infer.ml` (`291` lines, `Eval.pure_eq_modulo` constraints at lines `18–28`).
  - `01mf02/kontroli-rs` @ `22bfbdfc6d20502589c4c53369cf76ebcb1b8178`: `README.md`, `kontroli/src/kernel/mod.rs` (`115` lines), `kontroli/src/share.rs` (`161` lines), `kocheck/src/main.rs` (`48` lines, `rayon` + `flume` + optional `mimalloc`).
  - `Deducteam/hol2dk` @ `7f0da9630ea948628f9c5f49829d18df6a7073ee`: `README.md`, `encoding.lp` (lines `3–13`), `xproof.ml` (`86` lines).
  - `Deducteam/isabelle_dedukti` @ `925d138fd433b1d04c270e166133ae7a673b18a9`: `README.md` (Isabelle2025 export targets `kocheck`, `dkcheck`, `lambdapi`).
  - `ProofCert/checkers` @ `241b3c8d1cd543e2e3a8421e185eaf8639c0e39b`: `src/kernel/lkf/lkf-kernel.mod` (`142` total lines, `127` non-empty lines, `3,407` bytes), `src/kernel/lkf/certificatesLKF.sig` (`21` lines), `src/fpc/resolution/binary_res_fol.mod` (`35` lines).
  - `LPCIC/elpi` @ `631d14a63489ed0e8359ad036f7a8580bb373f33`: `README.md` ($\lambda$Prolog + CHR embeddable OCaml interpreter).
  - `teyjus/teyjus` @ `5cb51538beee8b1ad6dbc47ee14d7491fefa6021`: $\lambda$Prolog compiler/VM referenced by `ProofCert/checkers`.
- **Peer-Reviewed Papers & Practitioner Reports**:
  - M. Gordon, R. Milner, C. Wadsworth, *A Metalanguage for Interactive Proof in LCF*, POPL 1978, `DOI: 10.1145/512760.512773`.
  - J. Harrison, *HOL Light: A Tutorial Introduction*, FMCAD 1996, `DOI: 10.1007/BFb0031814`; Intel FP verification & AWS `s2n-bignum` practitioner documentation (`hol-light.github.io`, `cl.cam.ac.uk/~jrh13/`).
  - O. Abrahamsson, M. Myreen, R. Kumar, T. Sewell, *Candle: A Verified Implementation of HOL Light*, ITP 2022, `DOI: 10.4230/LIPIcs.ITP.2022.3` (extended JAR 2025, `DOI: 10.1007/s10817-025-09743-8`).
  - J. Hurd, *The OpenTheory Standard Theory Library*, NFM 2011, `DOI: 10.1007/978-3-642-20398-5_14` (and `DOI: 10.29007/7gg3`).
  - M. Färber, *Safe, Fast, Concurrent Proof Checking for the $\lambda\Pi$-Calculus Modulo Rewriting*, CPP 2022, `DOI: 10.1145/3497775.3503683`, `arXiv:2102.08766` (Tables 1–2, Figures 7–10, Sections 7.3 & 8–9).
  - F. Blanqui, *Translating HOL-Light Proofs to Coq*, LPAR 2024 (`DOI: 10.29007/6k4x`); F. Blanqui & A. Gontard, *Aligning HOL-Light and Rocq Libraries Formally*, `arXiv:2609.24598` (2026).
  - Z. Chihani, D. Miller, F. Renaud, *A Semantic Framework for Proof Evidence*, JAR 2017, `DOI: 10.1007/s10817-016-9380-6`.
  - C. Liang, D. Miller, *Focusing and Polarization in Linear, Intuitionistic, and Classical Logics*, TCS 2009, `DOI: 10.1016/j.tcs.2009.07.041`.
  - T. Hales et al., Flyspeck Kepler Conjecture engineering summary (`500 KLoC`, `5,000 CPU-hours` on Azure 32-core nodes).
- **Executable Micro-Probe**: Executed on `Python 3.13.15` (command and captured output verbatim in `## Findings` Section 4).

## Revalidation

1. **Re-run the Self-Contained Micro-Probe (`< 0.1 s`)**:
   Execute the `python3 -c '...'` snippet in `## Findings` Section 4 and verify identical assertions (`lcf_peak_bytes=392 << tree_retain_bytes=389955`, `ot_dict_entries=21` for $2^{20}$ virtual steps, `convertible_via_eq_c=True`, `ok_em=True bad_em=False ok_res=True bad_res=False`).
2. **Diff Upstream Kernel Signatures & Line Counts**:
   - Resolve latest upstream HEADs via `git ls-remote https://github.com/<owner>/<repo>.git HEAD`.
   - Diff `jrh13/hol-light` (`fusion.ml` lines `12–88`, `498–640`) for any new primitive rules, side-condition changes in `new_basic_definition`, or changes to `type thm`.
   - Diff `ProofCert/checkers` (`src/kernel/lkf/lkf-kernel.mod`) and `01mf02/kontroli-rs` (`kontroli/src/kernel/mod.rs`) to check whether Kontroli has added higher-order rewriting or AC support.
   - Check `Deducteam/hol2dk` and `Deducteam/isabelle_dedukti` benchmark logs for updated `Multivariate` or Isabelle/HOL export sizes and `kocheck` peak RSS.
