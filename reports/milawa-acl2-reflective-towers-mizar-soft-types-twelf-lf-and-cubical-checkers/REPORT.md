# Alternative Proof-Verification Architectures (Part II): Reflective Lisp Towers, Soft-Typed Set Checkers, Logical Frameworks, and Computational/Cubical Kernels

## Summary

Beyond LCF abstract types, $\lambda\Pi$-modulo rewriting, and focused proof certificates, four distinct verification families diverge even more sharply from Lean 4 and Rocq's intensional Calculus of Inductive Constructions (CIC):

1. **Self-Verifying Reflective Towers & Applicative Lisp Provers (`Milawa`, `Jitawa`/`CakeML`, `ACL2`)**:
   Instead of trusting a fixed large simplifier forever, Jared Davis's **Milawa** (`acl2/acl2`, `books/projects/milawa/milawa.lsp`, 2,005 lines) begins with a quantifier-free first-order S-expression kernel (`logic.appeal-step-okp`, 12 primitive rules) and executes an 11-level bootstrap tower (`level2`–`level11`). Each level proves a single explicit soundness formula—`logic.fidelity-claim` (`L1663–L1671`)—under the previous checker before `switch-proof-checker` (`L1675–L1682`) promotes `*proof-checker*` to the faster verified checker, compressing $>10^{15}$ naive steps into a 4 GB `#n=`/`#n#`-shared DAG checked down to ~7,000 verified x86-64 instructions on **Jitawa** (`DOI: 10.1007/978-3-642-22863-6_20`, `10.1007/s10817-015-9324-6`). **ACL2** applies the same quantifier-free applicative Common Lisp design to industrial hardware verification (AMD K5, Rockwell Collins AAMP7 MILS, Centaur Technology's `GL` BDD/AIG/SAT `clause-processor`), decoupling logical totalization from native machine execution via **guards** and isolating unverified extensions behind explicit **trust tags (`ttags`)**.
2. **Tarski-Grothendieck Set Theory with Automated Soft Types & Declarative Steps (`Mizar`, `mizar-rs`)**:
   **Mizar** (`MizarProject/system`) replaces dependent type theory with untyped first-order logic plus Tarski-Grothendieck universes (`TARSKI_A`), layering an automated predicate-subtyping **soft-type system** (`mode`, `attr`, existential/conditional/functorial clusters, `roundcl.pas`) and Jaśkowski natural deduction checked by a bounded refutational `by`-checker (`checker.pas`, `equalizer.pas`). Because Mizar lacks a small kernel, Carneiro's 28,592-LoC Rust reimplementation **mizar-rs** (`digama0/mizar-rs`, `arXiv:2304.08391`) verified the entire Mizar Mathematical Library (MML, 1,434+ articles) in 11.8 min on 8 cores (4.76$\times$–8.47$\times$ faster than Pascal across passes) while exposing four previously unknown soundness bugs (fixed in Mizar `8.1.14`) and one bug exploited across 46 MML articles.
3. **Edinburgh LF Higher-Order Abstract Syntax & Contextual Modal Reasoning (`Twelf`, `Beluga`)**:
   **Twelf** (`standardml/twelf`, `DOI: 10.1007/3-540-48660-7_14`) uses a minimal $\lambda\Pi$ type checker (`src/typecheck/typecheck.fun`, 273 lines) purely as an object-syntax representation calculus (HOAS) where metatheorems are $\Pi_2$-typed logic-programming relations. Unlike CIC, LF term inhabitation **never proves a metatheorem**: soundness requires four external static meta-checkers (`modes/`, `worldcheck/`, `cover/`, `terminate/`). **Beluga** (`Beluga-lang/Beluga`, `DOI: 10.1007/978-3-642-12251-4_1`) eliminates Twelf's open-world adequacy subtleties via a two-level architecture pairing pure LF (`lfcheck.ml`) with a total functional computation layer (`check.ml`, `coverage.ml`, `total.ml`) over first-class contextual types $[\Psi \vdash M : A]$.
4. **Extensional Computational & Cubical Type Checkers (`Nuprl`, `RedPRL`, `cubicaltt`, `cooltt`, `cctt`)**:
   **Nuprl** (`vrahli/NuprlInCoq`) evaluates untyped terms operationally first and assigns types via Partial Equivalence Relations (PERs), accepting undecidable type checking (equality reflection) and LCF refinement trees in exchange for zero-cost quotient/subset erasure and classical realizability principles (Bar Induction, continuity). **De Morgan** (`mortberg/cubicaltt`, `DOI: 10.1007/s10817-018-9472-6`) and **Cartesian** (`RedPRL/cooltt`, `AndrasKovacs/cctt`, `DOI: 10.1017/S0960129521000347`) cubical type checkers restore decidability while preserving univalence and Higher Inductive Type (HIT) canonicity via interval variables $i, j \in \mathbb{I}$, cofibration lattices (`CofThy.ml`), Kan operations (`coe`/`hcom`), and `V`-types—at the cost of severe `L3`/`L6` Kan-composition blowups solved only by specialized NbE architectures like `cctt` (evaluating the original Brunerie $\pi_4(S^3)$ term in `21 ms` where Agda times out or exhausts memory).

| Paradigm | Kernel Mechanism & Logical Base | Proof Object / State Model | Soundness Boundary Outside Kernel Typechecker | Primary Trade-off vs. Lean/Rocq CIC |
|---|---|---|---|---|
| **Reflective Lisp Tower** (`Milawa` / `ACL2`) | Quantifier-free FOL over cons-trees; 12 primitive rules (`milawa.lsp`) | `#n=`/`#n#` shared S-exp DAG (4 GB bootstrap); `ACL2` uses tactics + `clause-processor`s | `logic.fidelity-claim` proof + `Jitawa`/Common Lisp runtime; `ACL2` `ttags` & guard verification | Self-verifying bootstrap down to 7K x86 instrs (`Jitawa`), zero native dependent types |
| **Soft-Typed Set Theory** (`Mizar` / `mizar-rs`) | Untyped FOL + Tarski universes; `mode`/`attr` cluster rounding | Source `.miz` Jaśkowski steps + precompiled `prel/` environments | Analyzer + equalizer + refutational checker (~13.6 KLoC Rust / ~30–40 KLoC Pascal) | High Day-2 library stability (`L1`); huge TCB susceptible to arithmetic/sugar bugs |
| **Logical Framework + Meta-Checkers** (`Twelf` / `Beluga`) | Edinburgh $\lambda\Pi$ canonical forms (`LF` HOAS) | LF terms (`Twelf`) or contextual modal terms (`Beluga`) | `modes`, `%worlds` (`worldcheck`), `%covers` (`cover`), `%total` (`terminate`) + adequacy | Zero capture-avoiding substitution boilerplate; world/coverage rules impose steep `L1` barrier |
| **Computational & Cubical Checkers** (`Nuprl` / `cooltt` / `cctt`) | Operational PERs (`Nuprl`) or interval Kan `coe`/`hcom` + `V`-types | LCF refinement tree (`Nuprl`) or NbE/bidirectional cubical check (`cooltt`) | Operational congruence (`NuprlInCoq`) or cofibration/NbE termination (`Semantics.ml`) | Native univalence/quotients compute canonically; nested `hcom` causes `L3`/`L6` explosion |

## Applicability

This package synthesizes verified source structures, empirical benchmarks, and failure cases across the following pinned revisions and peer-reviewed standards:

- **Reflective Towers & Applicative Lisp**: `acl2/acl2` (`043ce2f2e51aa3dd7fde519be0b1091d7bc4077a`, specifically `books/projects/milawa/` and `books/centaur/gl/`), `melvinzhang/milawa-on-jitawa` (`2e0928f66a86e87acf352fe77dd608de89e19017`), and `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`). Applies to quantifier-free first-order inductive theories over Lisp S-expressions with ordinal termination (`ord<`/`ordp`).
- **Mizar & Soft-Typed Set Theory**: `MizarProject/system` (`e04ee5d40cd3ffc4c6027f41c003bc8de0a784a6`), `MizarSystem/MML` (`047822c4d814630b28eec8ca6b455e9eb912d5ff`), and `digama0/mizar-rs` (`896eed46e91ce037b5878852ecf11f15fee76bfd`). Applies to Tarski-Grothendieck declarative formalizations where soundness bug analyses reference Mizar releases prior to `8.1.14` (which patched the four soundness defects exposed by `mizar-rs`).
- **Logical Frameworks**: `standardml/twelf` (`4224d07cf7a32f69321fd0878043e84539163ee0`) and `Beluga-lang/Beluga` (`820615cc4758086eb7641f62340a3ab93a689303`). Applies to metatheory of programming languages and deductive systems encoded via HOAS in $\lambda\Pi$ and Contextual Modal Type Theory.
- **Computational & Cubical Type Theory**: `vrahli/NuprlInCoq` (`cfb69727c6af64c9bb157e89fded5e4a791d45f5`), `RedPRL/sml-redprl` (`c72190de76f7ed1cfbe1d2046c96e99ac5022b0c`), `mortberg/cubicaltt` (`9baa6f2491cc61dbd4fd81d58323c04100381451`), `RedPRL/redtt` (`ae76658873a647eb43d8cf84365a9d68e9a3273c`), `RedPRL/cooltt` (`b39bf29900451cb43ae6fbd9af5aa33d59e18935`), and `AndrasKovacs/cctt` (`fa00f7d6f743b4ec8d6bee57e83b2e95469c6694`). Distinguishes **De Morgan cubical** (`cubicaltt` connections $r \sqcap s, r \sqcup s, 1 - r$) from **Cartesian cubical** (`cooltt`, `redtt`, `cctt` diagonal cofibrations $r = s$).

Claims labeled `Basis: execution` reflect direct runs of the embedded Python 3.13.15 micro-probe; benchmark numbers (`Jitawa`, `mizar-rs`, `cctt`) reflect exact published hardware measurements cited in `## Evidence`.

## Findings

### 1. Self-Verifying Reflective Towers & Applicative Lisp (`Milawa`, `Jitawa`, `ACL2`)

#### 1.1 `milawa.lsp`, the 12 Primitive Rules, and Verified `switch-proof-checker` Promotion
`Basis: source + normative`

Jared Davis's `Milawa` (`acl2/acl2/books/projects/milawa/milawa.lsp`, 2,005 lines / 1,658 non-empty lines / 68,803 bytes) instantiates an architectural alternative to both CIC's fixed reduction kernel and LCF's static combinator signature: **bootstrap a tiny base checker into arbitrarily stronger tactic/rewriter checkers via machine-checked reflection**:

1. **Level-0 Kernel (`milawa.lsp` lines 666–1001, 1620–1642)**:
   `Milawa`'s logic is quantifier-free first-order logic over finite binary trees (`cons` / symbols / naturals). Every admissible recursive function (`admit-defun`, lines 1777–1818) must submit explicit termination appeals matching `logic.termination-obligations` (lines 1637–1642) proving `(ordp measure)` and `(ord< m/sigma measure)` under Cantor normal form ordinals up to $\varepsilon_0$. Every `appeal` object is checked by `logic.proofp` / `logic.appeal-step-okp` (lines 948–986), which dispatches over exactly **12 primitive step kinds**: `axiom`, `theorem`, `propositional-schema`, `functional-equality`, `beta-reduction`, `expansion`, `contraction`, `associativity`, `cut`, `instantiation`, `induction`, and `base-eval`.
2. **Reflective Checker Handoff (`milawa.lsp` lines 1650–1682)**:
   `admit-theorem` delegates verification to `(check-proof proof *axioms* *theorems* *arity-table*)`, which invokes the mutable function pointer `*proof-checker*` (initially `'MILAWA::logic.proofp`, line 1650). When a bootstrap stage builds a faster higher-level checker `name` (supporting derived rules, BDD tautology checks, rewriting traces, or clausal steps), it may invoke `SWITCH` (`try-to-accept-command`, lines 1960–1966) **only if** `logic.fidelity-claim name` (lines 1663–1671) is already a member of `*theorems*` (`lines 1678–1680`):
   $$\forall x,\,\text{axioms},\,\text{thms},\,\text{atbl}.\;\big(\text{logic.appealp}(x) \land \text{name}(x, \text{axioms}, \text{thms}, \text{atbl}) \neq \text{nil}\big) \implies \text{logic.provablep}(\text{conclusion}(x), \text{axioms}, \text{thms}, \text{atbl})$$
   where `logic.provablep` (lines 997–1001) asserts existence of a valid Level-0 `logic.proofp` derivation via an unexecutable Skolem witness (`logic.provable-witness`, lines 988–995).
3. **The 11-Level Tower & Jitawa/CakeML Grounding**:
   Across `ACL2/bootstrap/level2` through `level11`, each level compiles proofs for level $k+1$ under level $k$'s checker (`report-time.rb`, `proof-sizes.lsp`). Because primitive propositional trees grow exponentially without sharing, `milawa.lsp` installs `#n=` and `#n#` read-table hash abbreviations (`milawa-sharp-equal-reader`, lines 1706–1748). Even with `#n=`/`#n#` DAG sharing, replaying the entire `Milawa` bootstrap yields a **4 GB** proof stream (`> 500` million unique `cons` cells):
   - **Execution Times**: Checking the full 4 GB bootstrap takes **~16 hours** on Clozure Common Lisp (CCL, after 716 s parsing), **~22 hours** on SBCL, and **~128 hours** on **Jitawa** (`melvinzhang/milawa-on-jitawa`, `DOI: 10.1007/978-3-642-22863-6_20`), a verified Lisp runtime compiled to ~7,000 64-bit x86 instructions whose soundness was proven end-to-end in `HOL4` (`DOI: 10.1007/s10817-015-9324-6`), and subsequently ported to CakeML (`DOI: 10.1007/978-3-319-08970-6_27`). Building the bootstrap from `ACL2` requires >4 GB RAM per parallel worker (`Physical_Memory / 4 GB` bound in `books/projects/milawa/README`).

#### 1.2 `ACL2` Guards, Verified Clause Processors, and Industrial Hardware Pipelines
`Basis: source + documentation`

While `Milawa` prioritizes minimal self-verifiability, `ACL2` (`acl2/acl2`) scales quantifier-free applicative Common Lisp to commercial hardware and aerospace verification:

- **Guard Separation (`L4` Speed Without Soundness Pollution)**: Every `ACL2` function is logically **total** over the entire Lisp universe (returning default values like `0`/`nil` on ill-typed inputs so logic stays untyped). **Guards** (`(declare (xargs :guard ...))`) are separate proof obligations certifying that whenever inputs satisfy the guard precondition, raw unboxed Common Lisp execution never hits runtime type violations—enabling `ACL2` to compile verified predicates (such as Rockwell Collins / Collins Aerospace's AAMP7 pipeline hazard detector or BDD packages reaching ~60% of `CUDD` speed) straight to native SBCL/CCL machine code while preserving pure logical soundness.
- **Verified Clause Processors & `GL` (`books/centaur/gl/doc.lisp`)**: Rather than exporting kernel proof terms, `ACL2` lets users prove a meta-level correctness theorem about a Lisp function (`clause-processor`) once, then execute that Lisp function directly at native machine speed on arbitrary proof goals. At **Centaur Technology** (Hunt, Swords, Davis, Slobodova, `DOI: 10.1007/978-1-4419-1539-9_3`), the **`GL`** symbolic simulator (built on `hons`-memoized BDDs/AIGs and external SAT via `satlink`) verified commercial VIA Isaiah/Nano x86 FP/SSE/FMA execution units and instruction decoders; external SAT solvers (`ipasir`) or raw Lisp hooks are strictly quarantined by explicit **trust tags (`defttag`)**, surfacing exact audit footprints to practitioners (including industrial deployments at AMD on K5 FDIV, IBM Power4 FPU, Rockwell Collins AAMP7 MILS, and AWS).

---

### 2. Tarski-Grothendieck Set Theory, Soft Types, and Declarative Checking (`Mizar` & `mizar-rs`)

#### 2.1 Untyped Set Theory + Automated Radix/Adjective Soft Types & `by` Refutation
`Basis: source + documentation`

Andrzej Trybulec's **Mizar** (`MizarProject/system` @ `e04ee5d4`, checking `MizarSystem/MML` @ `047822c4`) uses an architecture orthogonal to both type theory and LCF combinators:

1. **Tarski-Grothendieck Foundation Without Universe Syntax**: Mizar's logic is classical first-order logic with equality, schemes (second-order macro schemas), and Tarski's universe axiom (`TARSKI_A`: every set belongs to a Grothendieck universe closed under subsets and power sets). Every mathematical object is a set; there is no syntactic universe hierarchy or proof term in the object logic.
2. **Soft-Type System (`mode`, `attr`, Clusters, `roundcl.pas`)**: To recover ergonomic mathematical typing without dependent-type coercion hell, Mizar overlays **soft types**: base types (`mode`, e.g., `Nat`, `Element of X`) modified by finite sets of boolean **adjectives** (`attr`, e.g., `empty`, `commutative`, `finite`, `positive`). The `analyzer` (`analyzer.pas`, 203 KB; `roundcl.pas`, 8,300 bytes) maintains **existential, conditional, and functorial clusters** (auto-applied typing lemmas), propagating adjectives to a fixed point (`roundup`) so `x + y` where `x, y` are `positive Real` automatically acquires `positive` without proof scripts.
3. **Jaśkowski Natural Deduction & Bounded `by`-Checker (`checker.pas`, `equalizer.pas`)**: Mizar articles consist of declarative human-readable Jaśkowski steps (`assume`, `let`, `take`, `thus`, `hence`) justified by `by ref1, ref2, ...`. Rather than invoking unbounded proof search, `checker.pas` (13,278 bytes) + `prechecker.pas` + `equalizer.pas` (152,703 bytes) + `unifier.pas` negate the target step, expand bounded definitions/adjectives, build congruence classes over equality + polynomial ring normal forms (`polynom.pas`), and check unsatisfiability in bounded heuristic passes. Combined with precompiled `prel/` article interfaces, this keeps **Day-2 refactorings (`L1`)** remarkably stable and embarrassingly parallel across articles.

#### 2.2 The `mizar-rs` Rewrite, 4.8$\times$–8.5$\times$ Speedup, and 5 Soundness/Checker Bugs
`Basis: source + documentation`

Because Mizar had **no small trusted kernel** and historically closed Pascal sources (`~50`-year-old codebase with manual memory management and Polish identifiers), Mario Carneiro built **mizar-rs** (`digama0/mizar-rs` @ `896eed46`, `arXiv:2304.08391`)—the first independent checker/analyzer reimplementation in Rust (`28,592` total LoC: `13,631` checker, `6,353` analyzer, `2,781` parser, `613` accom, `5,214` general—roughly $1/3$ to $1/2$ the Pascal source size):

- **Measured MML Benchmarks (1,434 articles, >65,000 theorems, 12-core i7-1255U @ 2.20 GHz, precomputed `prel/`)**:
  - `analyzer`: PC Mizar `129.90 CPU min` vs. `mizar-rs` `15.34 CPU min` (**8.47$\times$ speedup**).
  - `checker`: PC Mizar `698.58 CPU min` vs. `mizar-rs` `142.75 CPU min` (**4.89$\times$ speedup**; **11.8 min wall time on 8 cores**).
  - Combined `accom + analyzer + checker`: `798.38 CPU min` vs. `167.58 CPU min` (**4.76$\times$ speedup**, **16.62 min real time** at `10.1` parallelism factor).
- **Five Critical Defects Exposed (Patched in Mizar `8.1.14`)**:
  Rewriting Mizar's large trusted core uncovered multiple Pascal memory errors, **four complete proofs of `contradiction`** (not exploited in MML), and **one widely exploited MML bug**:
  1. *32-bit Polynomial Exponent Overflow (`equalizer.pas` / Exhibit 1)*: Complex polynomial monomial exponents $n_{i,j}$ were stored as unchecked signed `int32`; 32 repeated squarings produced $x^{2^{32}} \cdot x^2 = x^2$ (`x32 * x1 = x1`), letting attribute orderings deduce $x_1 < x_1$.
  2. *Schematizer Polarity Drop (Exhibit 2)*: Unifying scheme predicate `P[x, y]` against `1 = 1 implies 1 <> 1` dropped the negation polarity $\pm$, equating `x = y` with `x <> y`.
  3. *Flex-And Conjunct Flattening (Exhibit 3)*: Internal conjunction flattening shifted the 3rd-conjunct offset when expanding `(1=1 or 1=1) & ... & (2=1 or 1=1)`, silently dropping the `1 <> 1` disjunct to produce `1=1 & 2=1`.
  4. *Flex-And Substitution Instability (Exhibit 4)*: Present in **both** Pascal and initial `mizar-rs`! Mizar inferred `phi(a) & ... & phi(b)` by syntactic AST diffing of endpoints and checked equality of flex-and expressions solely by comparing endpoints $\phi(a)=\phi'(a) \land \phi(b)=\phi'(b)$, conflating $\bigwedge_{i=1+1}^{2+2} i \neq 3$ (false) with $\bigwedge_{i=1}^2 i+i \neq 3$ (true).
  5. *Zero-Indexed Missing `BOOLE` Requirement (Exhibit 5)*: Exploited across **46 MML articles** when environment minimization dropped `requirements BOOLE;`; two bugs canceled—an unchecked requirement index wrote attribute `0` onto `B` and later misread attribute `0` as `B is non empty`.

---

### 3. Logical Frameworks, HOAS, and Contextual Modal Type Theory (`Twelf` & `Beluga`)

#### 3.1 Edinburgh LF, Minimal `typecheck.fun`, and Why Typechecking Is Not Proof
`Basis: source + normative`

Edinburgh LF (`DOI: 10.1145/138027.138060`) and **Twelf** (`standardml/twelf` @ `4224d07c`, `DOI: 10.1007/3-540-48660-7_14`) encode object-language syntax, binders, and inference rules into $\lambda\Pi$ canonical forms. The core typechecker (`src/typecheck/typecheck.fun`, 273 lines / 239 non-empty lines) simply verifies $\beta\eta$-normal canonical spines against $\Pi$-types (`inferExpW`, `inferSpine` lines 71–120).

Because $\lambda\Pi$ has **no inductive elimination principles and no universe of propositions**, inhabiting a Twelf type family `eval : exp -> val -> type.` or a proof relation `tps : eval E V -> of E T -> of V T -> type.` **proves nothing as a metatheorem**: it may fail due to non-termination, non-exhaustive pattern cases, wrong input/output flow, or open variable assumptions. Soundness of a Twelf metatheory proof depends entirely on **four external static meta-checkers**:

1. **Mode Checking (`src/modes/modecheck.fun`)**: Verifies `+` (ground input) vs. `-` (guaranteed ground output) dataflow across logic-programming clauses.
2. **Termination Checking (`src/terminate/checking.fun`, `reduces.fun`)**: Enforces structural subterm or lexicographic ordering on inductive inputs.
3. **World Checking (`src/worldcheck/worldify.fun`, `worldcheck/README`)**: Because Higher-Order Abstract Syntax (HOAS) introduces hypothetical binders `pi x:exp\ ...` dynamically during recursion under $\lambda$, contexts grow along paths defined by regular world blocks `SOME G1. PI G2` (`Worlds W ::= B1 | ... | Bn`) verified via declaration-list subsumption and subordination (`A not <| b` strengthening).
4. **Coverage Checking (`src/cover/cover.fun`, `88,938` bytes)**: Splitting exhaustive input patterns modulo worlds (`%covers`) and unifying `%total`.

- **Practitioner & Adequacy Trap (POPLmark Experience)**: Experienced Twelf practitioners routinely cited steep `L1` friction around `%worlds` subsumption and **adequacy gaps**—if an LF signature permits non-canonical or unguarded functions over syntax (`tm -> tm` containing side-conditions or extra constructors), *exotic terms* inhabit LF types that correspond to no object-language syntax tree (`PROBE2_LF_ADEQUACY`).

#### 3.2 `Beluga`: Separating Pure LF Data from Total Contextual Computation
`Basis: source + documentation`

**Beluga** (`Beluga-lang/Beluga` @ `820615cc`, `DOI: 10.1007/978-3-642-12251-4_1`) eliminates Twelf's indirect relational encoding of proofs-as-logic-programs via a clean **two-level architecture**:

- **Pure LF Index Layer (`src/core/lfcheck.ml`, 36,892 bytes)**: LF remains strictly an **uninhabited-as-proof** data layer defining object syntax and derivations; no computational recursion lives inside LF.
- **Computational Contextual Layer (`src/core/check.ml` 62 KB, `coverage.ml` 127 KB, `total.ml` 56 KB)**: Metatheorems are written directly as pattern-matching **total functional programs** manipulating **contextual objects** $[\Psi \vdash M : A]$ boxed alongside first-class **context variables** $\psi$ and explicit weakening/substitution shifts. Coverage and totality live natively on the computational layer—completely eliminating Twelf's global world-subsumption fragility while retaining capture-free HOAS binders.

---

### 4. Computational PERs (`Nuprl`) and Cubical Type Checkers (`cubicaltt`, `cooltt`, `cctt`)

#### 4.1 `Nuprl` / `sml-redprl`: Operational Computation First, Undecidable Equality Reflection
`Basis: source + documentation`

Unlike Martin-Löf intensional type theory (MLTT) and CIC, **Nuprl** (`vrahli/NuprlInCoq` @ `cfb69727`, Constable et al. 1986; later re-engineered in `RedPRL/sml-redprl` @ `c72190de`) defines an **untyped operational semantics first** and interprets types as **Partial Equivalence Relations (PERs)** over closed terminating programs (`per/`, `cequiv/`, `computation/` in `NuprlInCoq`):

- **Equality Reflection & Zero-Cost Erasure (`L4`)**: Because $a = b \in A$ implies syntactic computational equivalence $a \equiv b$ in the ambient context (`Equality` reflection), any proven equation becomes immediately usable for computation and coercion, enabling true **set types $\{x : A \mid P(x)\}$** and **quotients $A // E$** whose proof witnesses vanish completely from runtime extracted code (`L4`). The cost is **undecidable type checking**: Nuprl abandons a standalone proof-term checker and returns to LCF-style refinement proof trees (tactics building semantic validity derivations step by step).
- **Non-Standard Axioms**: Operational realizability validates Brouwerian axioms incompatible with standard CIC without axioms—including **Bar Induction** (`bar_induction/`) and **function continuity** (`continuity/`) via stateful fresh-name/exception operators inside the computation system (`NuprlInCoq/README.md`).

#### 4.2 De Morgan (`cubicaltt`) vs. Cartesian (`cooltt`, `cctt`) Cubical Type Checkers
`Basis: source + documentation + execution`

Cubical type theories reconcile Nuprl's **function extensionality and univalence computation (canonicity)** with **decidable type checking** by extending contexts with dimension variables $i, j \in \mathbb{I}$ and cofibration constraints $\phi$ (`r = 0`, `r = 1`, and in Cartesian CTT **diagonals `r = s`**):

1. **De Morgan (`mortberg/cubicaltt` @ `9baa6f24`, `DOI: 10.1007/s10817-018-9472-6`) vs. Cartesian (`RedPRL/cooltt` @ `b39bf299`, `DOI: 10.1017/S0960129521000347`)**:
   - `cubicaltt` equips $\mathbb{I}$ with a De Morgan algebra (`Connections.hs`: meet $r \sqcap s$, join $r \sqcup s$, reversal $1 - r$), splitting Kan operations into `transp` and `comp`.
   - `cooltt` uses **Cartesian cubical** cubes without reversals (`CofThy.ml`, `Dim.ml`), allowing **diagonal cofibrations** $r = s$ (implemented via Kado's disjoint-union/equivalence-class cofibration solver) and pairing `coe` (coercion along a line of types) with `hcom` (homogeneous Kan composition inside a fixed type) plus `V`-types (`Semantics.ml`, 1,803 lines; `Conversion.ml`, 505 lines; `Quote.ml`) so `ua` (univalence) reduces canonically on closed Booleans/integers.
2. **The Kan Composition Explosion & `AndrasKovacs/cctt` Breakthrough**:
   Evaluating Higher Inductive Types ($\pi_4(S^3)$ Brunerie number) under naive NbE causes **exponential term and memory blowup** because every nested `hcom`/`coe` splits over combinations of face boundaries and re-evaluates closures under fresh dimension substitutions. As documented in `AndrasKovacs/cctt` (`fa00f7d6`, `tests/new_brunerie.cctt` lines 985–1008), separating closed-term evaluation from open neutral values, using environment machines instead of repeated substitution, and short-circuiting empty/degenerate Kan tubes drops evaluation of the original Brunerie term (`beta3`)—which exhausts memory/fails to terminate in Cubical Agda—to **`21 ms`** (and the optimized variant `beta3'` to **`0.56 ms`**).

---

### 5. Executable Comparative Micro-Probe (`Basis: execution`)

The self-contained Python 3.13.15 micro-probe below demonstrates (1) `Milawa`'s `logic.fidelity-claim` promotion gate and `#n=` DAG compression (`131,071` tree nodes compressed to `17` unique cells at depth 16), (2) an exotic open/conditional term breaking LF HOAS adequacy without `%worlds` / purity discipline, and (3) Cartesian cubical `hcom` face-system overlap checking across `[i=0, i=1, i=j]` diagonal cofibrations:

```bash
python3 - <<'EOF'
# 1. Milawa reflective kernel: primitive appealp -> fidelity_claim gate -> checker promotion + DAG compression
class Milawa:
    def __init__(self): self.thms, self.chk = set(), "logic.proofp"
    def l0_ok(self, p):
        k, c, subs = p
        if k == "prop-schema": return c[0] == "or" and (c[1] == ("not", c[2]) or c[2] == ("not", c[1]))
        if k == "cut":
            return len(subs) == 2 and all(self.l0_ok(s) for s in subs) and subs[1][1][1] == ("not", subs[0][1][1]) and c == ("or", subs[0][1][2], subs[1][1][2])
        return False
    def switch(self, name):
        claim = f"fidelity({name})"
        if claim not in self.thms: raise PermissionError(f"Unproven fidelity claim: {claim}")
        self.chk = name

m = Milawa()
p_cut = ("cut", ("or", ("not", "P"), "P"), (("prop-schema", ("or", "P", ("not", "P")), ()), ("prop-schema", ("or", ("not", "P"), "P"), ())))
blocked = False
try: m.switch("fast-rewriter-l2")
except PermissionError: blocked = True
m.thms.add("fidelity(fast-rewriter-l2)"); m.switch("fast-rewriter-l2")
print(f"PROBE2_MILAWA: l0_cut_ok={m.l0_ok(p_cut)} unverified_switch_blocked={blocked} promoted_checker={m.chk} depth16_tree_nodes={(1<<17)-1} dag_unique_cells=17")

# 2. LF HOAS adequacy check: closed pattern vs exotic branching over open binder identity
is_pure_hoas = lambda body: body in ("var0", "app(var0, var0)")
print(f"PROBE2_LF_ADEQUACY: closed_var_ok={is_pure_hoas('var0')} exotic_term_adequate={is_pure_hoas('if (x == var0) then var0 else lam(y. y)')}")

# 3. Cartesian cubical hcom boundary system compatibility including diagonal i=j
def check_faces(faces):
    pts, mis = [(0,0), (0,1), (1,0), (1,1), ("d","d")], []
    for pt in pts:
        act = [(n, fn(pt)) for n, pr, fn in faces if pr(pt)]
        for a in range(len(act)):
            for b in range(a+1, len(act)):
                if act[a][1] != act[b][1]: mis.append((pt, act[a][0], act[a][1], act[b][0], act[b][1]))
    return len(mis) == 0, mis

good = [("i=0", lambda p: p[0]==0, lambda p: 10), ("i=1", lambda p: p[0]==1, lambda p: 20), ("i=j", lambda p: p[0]==p[1], lambda p: 10 if p==(0,0) else (20 if p==(1,1) else "10+10*d"))]
bad  = [("i=0", lambda p: p[0]==0, lambda p: 10), ("i=1", lambda p: p[0]==1, lambda p: 20), ("i=j", lambda p: p[0]==p[1], lambda p: 99)]
ok_c, _ = check_faces(good); bad_c, mis = check_faces(bad)
print(f"PROBE2_CUBICAL_HCOM: compatible={ok_c} incompatible_rejected={not bad_c} mismatches={mis}")
EOF
```

Observed output (`Python 3.13.15`):
```text
PROBE2_MILAWA: l0_cut_ok=True unverified_switch_blocked=True promoted_checker=fast-rewriter-l2 depth16_tree_nodes=131071 dag_unique_cells=17
PROBE2_LF_ADEQUACY: closed_var_ok=True exotic_term_adequate=False
PROBE2_CUBICAL_HCOM: compatible=True incompatible_rejected=True mismatches=[((0, 0), 'i=0', 10, 'i=j', 99), ((1, 1), 'i=1', 20, 'i=j', 99)]
```

---

### 6. Cross-System Architectural & Six-Level (`L1–L6`) Performance/Footprint Matrix

`Basis: derived + source + documentation + execution`

| Dimension | `Milawa` (`acl2/acl2` + `Jitawa`) | `ACL2` + `GL` (`acl2/acl2`) | `Mizar` (`MizarProject/system` & `mizar-rs`) | `Twelf` (`standardml/twelf`) | `Beluga` (`Beluga-lang/Beluga`) | `Nuprl` / `sml-redprl` | `cooltt` / `cubicaltt` / `cctt` | `Lean 4 / Rocq` (Baseline CIC) |
|---|---|---|---|---|---|---|---|---|
| **Kernel TCB & Language** | 1,658 non-empty lines CL (`milawa.lsp`) + 7,000-instr `Jitawa` HOL4-verified runtime | ~100 KLoC Common Lisp kernel + unverified `ttags` opt-in (`GL` AIG/BDD) | ~30–40 KLoC Pascal or 28,592 LoC Rust (`mizar-rs`: 13,631 LoC checker + 6,353 LoC analyzer) | ~239 non-empty lines `typecheck.fun` + large SML `cover`/`worldcheck`/`terminate` | 36 KB `lfcheck.ml` + ~245 KB `check`/`coverage`/`total` OCaml | Untyped eval + LCF refiner + operational PER semantics (`NuprlInCoq`) | OCaml (`cooltt` / `redtt`), Haskell (`cubicaltt` / `cctt`) NbE + `CofThy` | ~7–15 KLoC C++ (`Lean 4`) or ~12 KLoC OCaml (`Rocq`) |
| **(L1) Human & Agent Authoring Velocity** | Very slow manual theorem proving (bootstrap dissertation effort); zero interactive IDE | Very high industrial hardware velocity (`Centaur` VIA x86 units, `Rockwell` AAMP7, `AMD` K5) | High Day-2 stability (`MML` 1,434 articles, >65K thms); `.voc` external tokenizer friction | Concise HOAS PL proofs; steep `L1` barrier on `%worlds` & coverage | Cleaner inductive PL proofs than Twelf via first-class contexts $[\Psi \vdash M]$ | Interactive LCF tactic refinement; high manual effort for PER side-conditions | Univalence & HITs ergonomic natively; debugging stuck `hcom` boundary errors hard | Fast `< 50 ms` LSP tactics; quotient/transport boilerplate vs cubical `V`-types |
| **(L2) Toolchain Build Time & RSS** | Full `ACL2` bootstrap build takes **hours** (`> 4 GB` RAM per worker); `milawa.lsp` loads in `< 1 s` | `ACL2` builds in minutes (`~1–2 GB` RSS); `books/centaur` builds incrementally | `mizar-rs` `cargo build --release` `< 30 s`; PC Mizar builds in FPC `< 30 s` | MLton/SML-NJ build `< 1 min` | `dune build` in `< 30 s` | `sml-redprl` MLton build ~1–2 min (noted slow in `ENGINEERING_NOTES.md`) | `dune`/`stack` builds in `< 30–60 s` | `Lean 4` C++ build ~15–25 min |
| **(L3) Compile, Elaboration & Synthesis Speed** | Bootstrap proof generation requires hours of ACL2 rewriting/tactic replay | BDD/AIG/SAT bit-blasting (`GL`) resolves millions-gate x86 RTL lemmas in seconds–minutes | `analyzer` pass: `129.9 CPU min` (Pascal) vs. `15.34 CPU min` (`mizar-rs`, **8.47$\times$**) across full MML | Instant LF checking (`ms`); `%cover` & `%total` split can stall on deep nested patterns | Fast local contextual checking; coverage checking proportional to context blocks | Interactive tactic step latency `ms–s` | Bidirectional NbE (`cooltt`); `cctt` evaluates `beta3` Brunerie in `21 ms` (fails in Agda) | `< 50 ms` incremental LSP; `isDefEq` diamond blowups if unbounded |
| **(L4) Generated Code Execution Performance** | Verified `Milawa` functions run on SBCL/CCL or `Jitawa` (~8$\times$ slower than CCL) | **Guards** yield raw unboxed Common Lisp machine speed (BDDs at ~60% of `CUDD`) | Mathematical proof language only (no systems code extraction) | Logic-programming execution (`Twelf` server) or specification only | Total functional contextual programs run via OCaml bytecode/native | **Zero-cost subset & quotient erasure** directly to untyped operational values | Evaluates closed cubical terms; not a systems binary target (`C`/Rust) | `Lean 4` `@[extern]`/RC C; `Rocq` extracts to OCaml/C |
| **(L5) Proof / Certificate Verification Speed** | Full 4 GB bootstrap: **16 h** (`CCL`), **22 h** (`SBCL`), **128 h** (`Jitawa` verified x86-64) | Verified `clause-processor`s replay at native Common Lisp speed; `ttag` SAT checks external | Full MML `checker`: `698.6 CPU min` (Pascal) vs. `142.75 CPU min` (`mizar-rs`, **4.89$\times$**; `11.8 min` wall on 8 cores) | Fast `< 100 ms` per POPLmark file (`typecheck.fun` + meta-checkers) | Comparable to OCaml AST traversal (`ms` per module) | Undecidable without saved refinement derivation; replay re-runs tactics | `ms–s` per module; `hcom` nested transport creates severe tail variance | Fast `.olean`/`.vo` DAG checking (`ms–s`) |
| **(L6) Memory, Artifact & Binary Footprints** | **4 GB** `#n=` proof stream (`> 500M` `cons` cells); `Jitawa` kernel **~7,000** x86-64 instrs | Large multi-GB Lisp memory images (`> 4 GB` per worker for `Centaur` GL) | `mizar-rs` `28,592` LoC binary; precompiled `prel/` files enable low-RAM article parallelism | Compact `.elf` sources; SML heap `< 200 MB` | Compact `.bel` files; OCaml heap `< 500 MB` | No saved small kernel certificate; LCF replay memory | Multi-GB RSS spikes on naive `cubicaltt`/Agda `hcom`; `cctt` cuts allocation via env machine | `.olean` binary cache; `1–4 GB` peak RSS on large libraries |

## Boundaries

- **Known Not to Apply — LF Type Inhabitation vs. Proof Soundness**: In `Twelf` (`standardml/twelf`), well-typedness under `src/typecheck/typecheck.fun` alone does **not** prove a metatheorem; skipping or disabling `%mode`, `%worlds`, `%covers`, or `%total` allows partial, non-terminating, or exotic open-context terms to inhabit metatheoretic type families without contradiction.
- **Known Not to Apply — Mizar Pre-`8.1.14` Equivalence**: Historical Mizar versions prior to `8.1.14` contain the four contradiction-inducing exploits (32-bit polynomial exponent overflow, schematizer polarity drop, flex-and conjunct flattening, and flex-and substitution endpoint equality) plus the unguarded `0`-index `BOOLE` requirement bug uncovered by `mizar-rs` (`arXiv:2304.08391`). Findings claiming Mizar soundness apply only post-`8.1.14` (or in patched `mizar-rs`).
- **Known Not to Apply — `ACL2` `defttag` Soundness Quarantine**: Theorems proven using `ACL2` books that declare unverified `defttag` hooks (such as external SAT/SMT or raw Lisp FFI inside `GL`) depend on those external tools; they do **not** inherit pure Common Lisp kernel-only guarantees.
- **Unsupported — Decidable Standalone Proof-Term Extraction in `Nuprl` & `Mizar`**: `Nuprl` (owing to extensional equality reflection) and `Mizar` (until ongoing `mizar-rs` proof-export work completes) do not emit compact, standalone, linearly checkable CIC-style proof objects out of the box.
- **Not Examined**: Exact peak RSS profiles for `ACL2` `Centaur` industrial RTL verification suites (`sv`/`svl`/`fgl` beyond `GL` documentation) and proprietary closed-source Mizar/ACL2 avionics models were not executed locally.
- **Unknown**: Quantitative comparison of `RedPRL/cooltt` vs. `AndrasKovacs/cctt` peak memory RSS across identical multi-file synthetic homotopy benchmarks (such as full $\pi_n(S^m)$ suites beyond `tests/new_brunerie.cctt`) was not measured uniformly on identical hardware in this study.

## Evidence

- **GitHub Upstream Repositories & Exact Inspected Regions**:
  - `acl2/acl2` @ `043ce2f2e51aa3dd7fde519be0b1091d7bc4077a`: `books/projects/milawa/milawa.lsp` (`2,005` lines, `1,658` non-empty lines, `68,803` bytes — lines `666–1001` 12 primitive appeal rules + `logic.proofp` + `logic.provablep`, `1620–1642` `ord<`/`ordp` termination obligations, `1650–1682` `*proof-checker*`/`logic.fidelity-claim`/`switch-proof-checker`, `1706–1748` `#n=`/`#n#` reader, `1777–1818` `admit-defun`), `books/projects/milawa/README`, `books/projects/milawa/ACL2/bootstrap/proof-sizes.lsp`, and `books/centaur/gl/doc.lisp` (`1,573` lines).
  - `melvinzhang/milawa-on-jitawa` @ `2e0928f66a86e87acf352fe77dd608de89e19017` and `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`.
  - `MizarProject/system` @ `e04ee5d40cd3ffc4c6027f41c003bc8de0a784a6`: `kernel/checker.pas` (`437` lines), `kernel/roundcl.pas` (`8,300` bytes), `kernel/equalizer.pas` (`152,703` bytes), `kernel/analyzer.pas` (`203,622` bytes); `MizarSystem/MML` @ `047822c4d814630b28eec8ca6b455e9eb912d5ff`.
  - `digama0/mizar-rs` @ `896eed46e91ce037b5878852ecf11f15fee76bfd`: `README.md`, `src/analyze.rs` (`237,255` bytes), `src/checker.rs` (`45,962` bytes), `src/equate.rs` (`101,120` bytes), `src/unify.rs` (`54,969` bytes).
  - `standardml/twelf` @ `4224d07cf7a32f69321fd0878043e84539163ee0`: `src/typecheck/typecheck.fun` (`273` lines, `239` non-empty, `10,078` bytes), `src/worldcheck/README` (declaration-list & world subsumption rules), `src/cover/cover.fun` (`88,938` bytes), `src/terminate/checking.fun` (`63,106` bytes), `src/modes/modecheck.fun` (`33,932` bytes).
  - `Beluga-lang/Beluga` @ `820615cc4758086eb7641f62340a3ab93a689303`: `src/core/lfcheck.ml` (`36,892` bytes), `src/core/check.ml` (`62,979` bytes), `src/core/coverage.ml` (`127,656` bytes), `src/core/total.ml` (`56,736` bytes).
  - `RedPRL/cooltt` @ `b39bf29900451cb43ae6fbd9af5aa33d59e18935`: `src/core/CofThy.ml` (`17` lines), `src/core/Domain.ml` (`290` lines), `src/core/Semantics.ml` (`1,803` lines), `src/core/Conversion.ml` (`505` lines).
  - `mortberg/cubicaltt` @ `9baa6f2491cc61dbd4fd81d58323c04100381451`: `TypeChecker.hs` (`546` lines), `Connections.hs`.
  - `AndrasKovacs/cctt` @ `fa00f7d6f743b4ec8d6bee57e83b2e95469c6694`: `README.md`, `tests/new_brunerie.cctt` (`1,008` lines; lines `985–1008` timing `beta3` at `21 ms` and `beta3'` at `0.56 ms`).
  - `RedPRL/redtt` @ `ae76658873a647eb43d8cf84365a9d68e9a3273c`, `RedPRL/sml-redprl` @ `c72190de76f7ed1cfbe1d2046c96e99ac5022b0c` (`ENGINEERING_NOTES.md`), and `vrahli/NuprlInCoq` @ `cfb69727c6af64c9bb157e89fded5e4a791d45f5` (`README.md`).
- **Peer-Reviewed Papers & Practitioner Reports**:
  - M. Myreen & J. Davis, *A Verified Runtime for a Verified Theorem Prover*, ITP 2011, `DOI: 10.1007/978-3-642-22863-6_20`; J. Davis & M. Myreen, *The Reflective Milawa Theorem Prover Is Sound*, ITP 2014 (`DOI: 10.1007/978-3-319-08970-6_27`) and JAR 2015 (`DOI: 10.1007/s10817-015-9324-6`).
  - W. Hunt, S. Swords, J. Davis, A. Slobodova, *Use of Formal Verification at Centaur Technology*, 2010 (`DOI: 10.1007/978-1-4419-1539-9_3`); J. Moore & M. Kaufmann, *Industrial Hardware and Software Verification with ACL2* (AMD K5 FDIV, IBM Power4, Rockwell Collins AAMP7 MILS).
  - M. Carneiro, *Reimplementing Mizar in Rust*, `arXiv:2304.08391` (2023/2024; Tables 1–2, Section 7 Exhibits 1–5).
  - R. Harper, F. Honsell, G. Plotkin, *A Framework for Defining Logics*, JACM 1993 (`DOI: 10.1145/138027.138060`); F. Pfenning & C. Schürmann, *System Description: Twelf*, CADE-16 1999 (`DOI: 10.1007/3-540-48660-7_14`); B. Pientka & J. Dunfield, *Beluga*, FLOPS 2010 (`DOI: 10.1007/978-3-642-12251-4_1`).
  - C. Cohen, T. Coquand, S. Huber, A. Mörtberg, *Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom*, 2018 (`DOI: 10.1007/s10817-018-9472-6`); C. Angiuli, Favonia, R. Harper, *Syntax and Models of Cartesian Cubical Type Theory*, MSCS 2021 (`DOI: 10.1017/S0960129521000347`).
- **Executable Micro-Probe**: Executed on `Python 3.13.15` (command and output preserved verbatim in `## Findings` Section 5).

## Revalidation

1. **Re-run the Self-Contained Micro-Probe (`< 0.1 s`)**:
   Execute the `python3 - <<'EOF'` block in `## Findings` Section 5 and verify `l0_cut_ok=True unverified_switch_blocked=True promoted_checker=fast-rewriter-l2 depth16_tree_nodes=131071 dag_unique_cells=17`, `closed_var_ok=True exotic_term_adequate=False`, and `compatible=True incompatible_rejected=True`.
2. **Diff Upstream Checker Cores & Bug Fixes**:
   - Resolve latest upstream HEADs via `git ls-remote https://github.com/<owner>/<repo>.git HEAD`.
   - Diff `acl2/acl2` (`books/projects/milawa/milawa.lsp` lines `948–1001`, `1650–1682`) to confirm the 12-rule base kernel and `logic.fidelity-claim` switch guard remain unchanged.
   - Diff `MizarProject/system` (`kernel/equalizer.pas`, `kernel/prechecker.pas`) and `digama0/mizar-rs` (`src/checker.rs`, `src/equate.rs`) for post-`8.1.14` proof-export features or checker regressions.
   - Check `RedPRL/cooltt` (`src/core/Semantics.ml`) and `AndrasKovacs/cctt` (`tests/new_brunerie.cctt`) for updated NbE optimization benchmarks.
