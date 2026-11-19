# Empirical Programming-Language Human Factors, Cognitive Dimensions, and Prover Usability

## Summary

Empirical human-factors science of programming languages and formal verification tools demonstrates that designer intuition and syntactic folklore systematically mispredict developer performance, error rates, and cognitive load. Randomized controlled trials (RCTs), natural-programming elicitations, and contextual inquiries establish five load-bearing design laws:

1. **Conventional C-Style Syntax Offers No Baseline Advantage Over Random Punctuation for Novices**: Stefik and Siebert (2013) showed that novice accuracy in `Java` and `Perl` was statistically indistinguishable from **`Randomo`** (a placebo language with randomly sampled ASCII tokens), whereas evidence-oriented **`Quorum`**, `Python`, and `Ruby` achieved statistically significant accuracy gains. Similarly, Pane, Ratanamahatana, and Myers (2001) established that non-programmers naturally express solutions via event-driven rules and aggregate set operations rather than explicit index-counter loops.
2. **Cognitive Dimensions Are Governed by Irreducible Trade-Offs (Green & Petre 1996)**: No notation simultaneously minimizes **viscosity**, **premature commitment**, **hidden dependencies**, and **error-proneness**. Type inference lowers viscosity at the cost of hidden dependencies; explicit linear/typestate/ownership annotations (`Obsidian`, `Glacier`, Rust) improve local visibility while amplifying premature commitment and refactoring viscosity; live structure editors (`Hazel`) eliminate syntax errors while imposing structural-edit viscosity unless paired with fluid refactoring affordances.
3. **Ownership, Immutability, and Borrow-Checker Ergonomics Respond Strongly to Conceptual Grounding and Optional Relaxation**: Across Coblenz et al.'s `Glacier`, `Obsidian`, `PLIERS`, and `Bronze` studies—including a **$N = 428$** RCT where optional library GC (`Bronze`) cut Rust complex-aliasing completion time by $3\times$ (**4 hours vs. 12 hours**) with zero total-time penalty when later rewriting into standard Rust—and Crichton, Gray, and Krishnamurthi's **$N = 342$** evaluation of path-permission visualizations (`Aquascope`, **+9%** Ownership Inventory gain, Cohen's **$d = 0.56$**), explicit mental-model alignment and progressive disclosure dominate raw annotation density.
4. **Interactive vs. Auto-Active Provers Fail Along Orthogonal Human-Factors Axes**: Interactive theorem provers (`Rocq`, `Lean 4`) suffer tactic opacity, proof brittleness under refactoring, and library-search overhead (`QED at Large`; `QED in Context`, $N = 30$), whereas auto-active SMT verifiers (`Dafny`, `Verus`) suffer the **"cliff effect"** of opaque quantifier triggers and **SMT proof instability** (`Mariposa`, `Cazamariposas`) where irrelevant query perturbations unpredictably flip `unsat` to timeout.
5. **Statistical Rigor & Cognitive Budgets Are Mandatory Acceptance Gates**: Power calculations confirm that classic small between-subjects PL lab trials ($N = 20$) possess only **`20.1%` power** for medium effects ($d = 0.50$), while single-run CI verification catches only **`5.0%`** of `5%`-unstable SMT queries compared to **`95.4%`** across $M = 60$ perturbations.

## Applicability

This report synthesizes peer-reviewed empirical studies, conceptual frameworks, direct inspection of language/verifier implementations, and executable statistical/modeling probes:

- **Evidence-Based Syntax & Natural Programming**: `qorf/quorum-language` @ `1d907c10b24a4e98f62833ce990320b19c075243` (`Parser.quorum`), Stefik & Siebert (2013), and Pane, Ratanamahatana, & Myers (2001).
- **Cognitive Dimensions & Structure Editors**: Green & Petre (1996) and `hazelgrove/hazel` @ `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`.
- **User-Centered Ownership, Typestate & Immutability Studies**: `mcoblenz/Glacier` @ `4f2b3d9486d441483f3f8997feb03e134953a201`, `mcoblenz/Obsidian` @ `a32efc07b0a3c3128413999324f55f16fb349c1b`, `mcoblenz/bronze` @ `529a3e4ff83745265053441dbe2f131622d1c18b`, `cognitive-engineering-lab/aquascope` @ `f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`, Coblenz et al. (2017, 2020, 2021, 2022), Chasins et al. (2021), and Crichton et al. (2023/2026).
- **Interactive & Auto-Active Prover Usability**: `dafny-lang/dafny` @ `8c137ba351c60a521cfb122011770fdbea9a0453`, `leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`, `rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`, `verus-lang/verus` @ `a95764f23c6876b47500beda6118e2d142a87cc3`, Ringer et al. (2019), Shi et al. (2025), and Zhou et al. (2023/2025).

Empirical statistics apply strictly to the tested populations (novices in Stefik/Pane; university Rust students in Bronze; online *Rust Book* readers in Aquascope; experienced Rocq/Lean practitioners in *QED in Context*). Extrapolations from novices to industrial experts or from short lab tasks to multi-year codebase maintenance are bounded under **Boundaries**.

## Findings

### 1. Placebo-Controlled Syntax RCTs (`Stefik & Siebert 2013`, `Quorum`) and Natural Programming (`Pane et al. 2001`)

*Basis: normative literature (Stefik & Siebert 2013, DOI `10.1145/2534973`; Pane et al. 2001, DOI `10.1006/ijhc.2000.0410`) + source (`qorf/quorum-language@1d907c10b2`)*

#### 1.1 The `Randomo` Placebo Result & Token Accuracy Mapping (`Quorum`)

Stefik and Siebert (2013, ACM TOCE 13(4)) introduced clinical-trial discipline to PL syntax evaluation by constructing **`Randomo`**, a placebo programming language whose keywords and syntactic delimiters were sampled uniformly at random from the ASCII character set, and comparing novice code-writing accuracy across four studies (two intuitiveness surveys and two controlled performance trials) against `Java`, `Perl`, `Python`, `Ruby`, and **`Quorum`**:

- **Core Falsification**: Across novice writing tasks, C-derived languages—specifically **`Java` and `Perl`**—**did not yield accuracy rates statistically distinguishable from `Randomo`** ($p > 0.05$). By contrast, languages departing from C-style punctuation (`Quorum`, `Python`, `Ruby`) achieved statistically significant accuracy improvements over both `Randomo` and `Java`/`Perl` ($p < 0.05$).
- **Token Accuracy Mapping (TAM)**: Decomposing error rates to individual lexical tokens isolated the dominant friction points in C-family grammars: three-clause `for(int i=0; i<n; i++)` headers, overloaded punctuation (`=` vs. `==`, `!=`, `&&`), and terse non-word type/method keywords.
- **Primary-Source Manifestation in `Quorum`** (`qorf/quorum-language@1d907c10b2:Quorum/Library/Standard/Libraries/Language/Compile/Parser.quorum:12-89`): The self-hosted Quorum compiler directly operationalizes these RCT outcomes:
  - Explicit word-based equality negation (`if packageValue not= undefined ... end`, line 45) instead of `!=`.
  - Self-documenting method headers (`action GetClassesIterator returns Iterator<Class> ... end`, lines 34–36) and `me:` receiver dispatch (line 39) instead of C-style type-first signatures and `this.`.
  - Structured, sentence-form `CompilerError` diagnostics (`"The name \"" + name + "\" cannot end with an underscore (_)."`, lines 68–82) engineered specifically for screen-reader and novice comprehension.

#### 1.2 Natural Programming Elicitation (`Pane, Ratanamahatana, Myers 2001`)

Pane, Ratanamahatana, and Myers (2001, IJHCS 54(2), DOI `10.1006/ijhc.2000.0410`) studied how non-programmers (fifth-grade children and adults) naturally specify solutions to algorithmic and Pac-Man-like behavioral tasks before learning any programming language:

1. **Event-Driven / Rule-Based Dominance**: Participants predominantly wrote reactive rules (`"when Pac-Man eats a power pill, ghosts turn blue"`) rather than centralized imperative game-loop polling.
2. **Aggregate Set Operations Over Explicit Iteration**: Non-programmers routinely expressed bulk updates directly over collections (`"move all ghosts toward Pac-Man"`) rather than allocating loop counters and iterating element by element.
3. **Natural-Language Boolean & Scoping Divergences**: Participants frequently used `and` as union/sequencing (`"select circles and squares"` meaning `circle OR square`), relied on implicit contextual scoping, and omitted explicit upfront variable declarations—explaining why C-style strict boolean operators and declaration-before-use syntax produce systematic novice inversion bugs.

---

### 2. Cognitive Dimensions of Notations (`Green & Petre 1996`) and Structural Trade-Offs

*Basis: normative literature (Green & Petre 1996, DOI `10.1006/jvlc.1996.0009`) + source (`hazel@782249bbd0`) + execution*

Green and Petre (1996, JVLC 7(2)) formalized the **Cognitive Dimensions of Notations (CDs)** as a broad-brush analytic framework for evaluating information artifacts, notations, and programming environments across orthogonal usability axes. Rather than asserting a single "best" notation, CDs identify **structural trade-offs** where optimizing one axis necessarily stresses another:

| Cognitive Dimension | Operational Definition (`Green & Petre 1996`) | High-Friction Example in PL / Prover Design | Primary Trade-Off Partner |
|---|---|---|---|
| **Viscosity** | Resistance to local change (how many knock-on edits a small conceptual change demands) | Adding a lifetime `'a` to a Rust struct field cascading across dozens of impl blocks/callers; editing an inductive type breaking 40 Rocq tactic scripts | Trades off against **Visibility** and **Error-Proneness** |
| **Premature Commitment** | Constraints forcing the author to decide structure/order before having sufficient information | Choosing `Owned` vs. `Shared` ownership (`Obsidian`) or deciding exact heap/stack allocation before prototyping an algorithm | Trades off against **Consistency** and static guarantees |
| **Hidden Dependencies** | Important semantic links between entities that are not visible at the point of use | Global typeclass/coercion resolution (`Haskell`, `Lean 4`), implicit SMT quantifier triggers (`Dafny`/`Z3`), non-local unification constraints (`CUE`) | Trades off against **Diffuseness** (terseness) and **Viscosity** |
| **Visibility & Juxtaposability** | Ability to view required components easily and place related definitions side by side | Stepping through a 200-line tactic script where goal hypotheses scroll off-screen (`Coq`/`Lean` without InfoView) | Trades off against screen density / **Diffuseness** |
| **Progressive Evaluation** | Ability to evaluate/check an incomplete work-in-progress artifact at any moment | Batch-only compiler/verifier rejecting an entire file on one parse error vs. live typed-hole execution (`Hazel`, Lean `sorry`) | Trades off against strict whole-program completeness |
| **Role-Expressiveness** | Ease of inferring the purpose of a syntactic construct from its visual form | Cryptic ASCII sigils (`&'a mut [T]`, `<'_, '_>`, Perl `$_`) vs. Quorum/Obsidian named keywords | Trades off against **Diffuseness** |
| **Hard Mental Operations** | Demand on human working memory to mentally simulate nested abstractions | Tracking simultaneous borrow lifetimes + reborrowing + variance + drop order; nested `if`-branch SMT contexts | Directly constrained by working-memory capacity (`4 ± 1` chunks) |

#### 2.1 Structure Editors (`Hazel`) and Multi-Axis Modal Lattices

*Basis: source (`hazelgrove/hazel@782249bbd0`) + derived + execution (`probe_human_factors_metrics.py`, Section 2)*

- **Structure Editors (`Hazel`)**: `hazelgrove/hazel@782249bbd0` demonstrates how representing incomplete programs via **typed holes** (empty and non-empty holes preserving type errors locally inside well-formed ASTs) maximizes **progressive evaluation** and eliminates parse-error dead zones. However, CD analysis predicts—and empirical evaluations of projectional editors confirm—that rigid tree-only editing elevates **viscosity** and **premature commitment** whenever a user needs to transiently break tree balance (e.g., deleting a left parenthesis to move a binary operator's precedence boundary), necessitating hybrid tile/linear-token editing models.
- **Modal-Lattice Working-Memory Explosion**: When a systems or verification language exposes $k$ orthogonal static modal axes simultaneously in surface syntax (e.g., ownership `[3]`, aliasing/mutability `[3]`, effects `[4]`, linearity/typestate `[3]`, totality `[2]`, memory model `[3]`), our modeling probe (`probe_human_factors_metrics.py`, Section 2) shows the Cartesian disambiguation space exploding from `3` (1 axis) $\to$ `9` (2) $\to$ `36` (3) $\to$ `108` (4) $\to$ `216` (5) $\to$ **`648`** (6 axes), crossing Cowan's `4 ± 1` active working-memory chunk threshold by axis 5. **Progressive disclosure**—fixing safe defaults on 5 axes so ordinary code activates $\le 1\text{–}2$ concepts while exposing advanced axes opt-in—is required to prevent **premature commitment** paralysis.

---

### 3. Empirical Ownership, Immutability, and User-Centered PL Studies (`Coblenz`, `Crichton`)

*Basis: normative literature (Coblenz 2017, 2020, 2021, 2022; Chasins 2021; Crichton 2023/2026) + source (`Glacier`, `Obsidian`, `bronze`, `aquascope`)*

Michael Coblenz, Brad Myers, Jonathan Aldrich, Joshua Sunshine, Sarah Chasins, Will Crichton, and collaborators established a cumulative empirical research program (**PLIERS**, ACM TOCHI 2021, DOI `10.1145/3452379`; **PL and HCI**, CACM 2021, DOI `10.1145/3469279`) applying HCI methodology—contextual inquiry, iterative paper/wizard-of-oz prototyping, formative think-aloud studies, and large-scale RCTs—directly to type systems and ownership languages:

| System & Study | Verified Source & DOI | Mechanism Inspected in Source | Empirical Study Design & Quantitative / Qualitative Findings |
|---|---|---|---|
| **Glacier** (Java Transitive Immutability) | `mcoblenz/Glacier@4f2b3d9486` (`GlacierVisitor.java:51-85`); ICSE 2017 (`10.1109/ICSE.2017.52`) | Checker Framework pluggable type checker (`BaseTypeVisitor`) enforcing transitive `@Immutable` vs. `@Mutable` class qualifiers (`typeIsImmutable`) | Controlled user study comparing Glacier against Java `final` showed Java `final` fails to prevent transitive state mutation bugs (developers mistakenly assume shallow `final` implies deep immutability); Glacier enabled participants to enforce transitive immutability accurately with low annotation friction. |
| **Obsidian** (Typestate & Linear Assets) | `mcoblenz/Obsidian@a32efc07b0` (`ObsidianType.scala:4-105`); TOPLAS 2020 (`10.1145/3417516`) | Algebraic `TypeState` (`States(Set[String]) \| PermVar \| Permission`) with `Owned`, `Unowned`, `Shared`, `Inferred` (`lines 17-38`) and explicit `OwnershipConsumptionMode` transitions (`ConsumingOwnedGives{Shared,Unowned}`) | Iterative formative usability tests drove major type-system simplifications (notably adding `Inferred` local-variable permissions so programmers need not annotate every local reference). Summative evaluation vs. Solidity showed Obsidian prevented asset-loss and invalid-state bugs, while revealing that ownership/aliasing transitions still impose high **premature commitment** and debugging friction when aliasing requirements evolve. |
| **Bronze** (Optional Library GC for Rust) | `mcoblenz/bronze@529a3e4ff8` (`bronze_gc/src/lib.rs:68-100`); ICSE 2022 (`10.1145/3510003.3510107`, `arXiv:2110.01098v2`) | Library-based tracing GC (`GcRef<T>`, `GcBox<T>`) storing `GcBoxHeader { vtable, marked: Cell<bool> }` + runtime `Cell<BorrowFlag>` (copied from `core::cell.rs`, `is_writing(x<0)`, `is_reading(x>0)`) | Large-scale RCT recruiting from a **633-person** course (**$N = 428$** students analyzed). On a complex-aliasing task, Bronze users had higher completion rates and took **$1/3$ the time (4 hours vs. 12 hours)**! Crucially, **even after redoing the task in standard Rust without Bronze, total time showed no significant difference** vs. Rust-only controls—showing GC acts as an effective pedagogical/prototyping scaffold. Sentiment correlated more strongly with **frustration/stress** than total hours spent. |
| **Aquascope & Rust Permissions Model** | `cognitive-engineering-lab/aquascope@f2d0a06034` (`permissions/mod.rs:33-120`, `flow.rs:1-75`); OOPSLA 2023 (`10.1145/3622841`) / CACM 2026 (`10.1145/3796537`) | Compiler plugin lifting `rustc` MIR + Polonius facts (`AquascopeFacts`) to surface-level **Read/Write/Own** (`struct Permissions { read, write, drop }`) + region taint flow (`Θ ⊢ r_1 -> r_2` detecting missing universal constraints & local-outlives `borrowfail`) | Built the **Ownership Inventory** diagnostic instrument; discovered Rust learners fail to connect static borrow rules with dynamic UB—specifically failing to recognize **borrow-checker incompleteness** (safe programs rejected by conservative alias/field analysis). Integrating permissions visualizations + counterfactual UB execution into *The Rust Programming Language* improved Ownership Inventory scores by **+9% ($N = 342$, Cohen's $d = 0.56$)**! |

*Derived Design Synthesis*: Together, `Bronze` and `Aquascope` falsify the "tough love" hypothesis that forcing learners or rapid prototypers through raw compile-time borrow errors produces superior mastery. Scaffolding complex aliasing with optional relaxation (`Bronze`) or making the compiler's abstract-interpretation state legible in surface syntax (`Aquascope`'s `R`/`W`/`O` path permissions) dramatically lowers cognitive friction without sacrificing long-run competence.

---

### 4. Empirical Failure Modes of Interactive vs. Auto-Active Provers (HATRA & Verification UX)

*Basis: normative literature (`QED at Large` 2019; `QED in Context` 2025; `Mariposa` 2023; `Cazamariposas` 2025) + source (`dafny@8c137ba351`, `lean4@8009d0a64d`, `rocq@25f5b18a32`, `verus@a95764f23c`) + execution*

Human-factors research across the **HATRA** (Human Aspects of Types and Reasoning Assistants) community and large-scale verification engineering studies reveals a stark structural duality between **Interactive Theorem Provers (ITPs)** and **Auto-Active SMT Verifiers**:

#### 4.1 Interactive Theorem Provers (`Rocq/Coq`, `Lean 4`): High Tactile Control, High Maintenance Viscosity

- **Contextual Inquiry of Everyday Proof Engineering (`Shi et al. 2025`, PACMPL OOPSLA, DOI `10.1145/3720426`)**: Observing **$N = 30$** experienced Lean and Rocq practitioners performing their actual work overturned the assumption that proof engineering is primarily linear goal reduction. Practitioners spend substantial effort on:
  1. **Tight Trial-and-Error Feedback Loops**: Micro-probing tactics against the live InfoView / proof state to discover how elaboration, coercion, and implicit-argument unification behave ("challenging conversations" with the prover).
  2. **Heavy External & Library Search Overhead**: Navigating massive libraries (`Mathlib`, `Std`, `MathComp`) via signature search (`Search`, `Locate`, `Check`, LSP hover) because lemma naming conventions and implicit typeclass instances create severe **hidden dependencies**.
  3. **Non-`QED` Engineering Goals**: Experienced users actively invest extra effort beyond merely closing the proof—refactoring scripts for readability, fast incremental re-elaboration, and resistance to upstream breakage.
- **Proof Brittleness & Evolution (`Ringer et al. 2019`, DOI `10.1561/2500000045`)**: Tactic scripts encode *imperative state-machine deltas* whose names and subgoal ordering depend implicitly on definition bodies and automation heuristics. Small specification edits trigger cascading downstream proof failures (**high viscosity**), motivating proof-repair tooling and structured/declarative subgoal naming (`have`, `case`, `show`).

#### 4.2 Auto-Active SMT Verifiers (`Dafny`, `Verus`): Low Boilerplate, Severe "Cliff Effect" & SMT Instability

- **The "Cliff Effect" & Opaque Trigger Diagnostics**: In auto-active verifiers (`Dafny`, `Verus`, `F*`), the user supplies loop invariants, pre/postconditions, and ghost lemma calls, delegating logical discharge to an SMT solver (Z3/cvc5). Direct inspection of `dafny-lang/dafny@8c137ba351:Source/DafnyCore/Options/CommonOptionBag.cs:22-75` reveals the exact usability failure modes that forced Dafny to add specialized introspection flags:
  - `--manual-triggers` (`line 54`) and `--show-hints` (`line 59`, *"such as what triggers Dafny generates for quantifiers"*): E-matching quantifier instantiation loops or overly restrictive auto-inferred triggers cause silent timeouts or baffling verification failures invisible in the source code (**extreme hidden dependencies**).
  - `--show-assertions` (`line 65`, `None | Implicit | All`): implicit well-formedness / division-by-zero / array-bounds assertions fail without an explicit user `assert` statement on the line.
  - `--progress` (`Symbol | Batch`, `lines 22-27`) and `--manual-lemma-induction` (`line 73`): separating slow assertion batches and turning off unpredictable automatic induction heuristics.
- **Empirical SMT Proof Instability (`Mariposa`, Zhou et al. FMCAD 2023; `Cazamariposas`, Zhou, Shah, Lin 2025, DOI `10.1007/978-3-031-99984-0_5`)**:
  - Applying semantics-preserving query mutations (**symbol renaming**, **assertion reordering/shuffling**, and **solver random seeds**) to thousands of real-world Dafny and F* SMT-LIB queries proved that Z3 and cvc5 exhibit pervasive **proof instability** (several percentage points of real queries flip unpredictably between `unsat` and timeout/unknown, and newer solver upgrades frequently *regress* stability).
  - **Human-Factors Consequence**: SMT instability shatters developer mental models because progress becomes **non-monotonic**—renaming an unrelated variable or adding a helper lemma elsewhere in the file breaks an already-verified function, driving superstitious debugging ("assertion cargo-culting") and motivating automated context-pruning (`Shake`) and instability-root-cause localization (`Cazamariposas`).

| Usability Axis (Green & Petre CDs) | Interactive Provers (`Lean 4`, `Rocq`) | Auto-Active Verifiers (`Dafny`, `Verus`) | Emerging Hybrid Mitigation |
|---|---|---|---|
| **Feedback Granularity & Mental Model** | Explicit intermediate proof-state InfoView per cursor line; failures localize to exact failed tactic or unification mismatch | Binary pass/fail/timeout over entire assertion batch; solver counterexamples often spurious under incomplete quantifier axioms | Per-assertion isolation (`--isolate-assertions`), structured SMT profiler/trigger hints, or lowering stuck SMT goals into interactive tactics |
| **Monotonicity & Stability** | High determinism (kernel-checked proof terms); breaks primarily on *semantic/syntactic* definition edits | Vulnerable to **SMT butterfly effect** (`Mariposa`): irrelevant symbol renames or seed changes flip `unsat` $\leftrightarrow$ timeout | Perturbation stability CI (`Mariposa`), context pruning (`Shake`), deterministic rlimit budgets |
| **Viscosity & Authoring Effort** | High proof-to-code ratio (often $3\times\text{–}10\times$); high tactile burden for routine arithmetic/heap framing | Low boilerplate for linear arithmetic/bitvectors; abrupt **cliff effect** when crossing quantifier/nonlinear boundaries | Decidable SMT-backed tactics inside ITPs (`omega`, `bv_decide`, `grind`, `sledgehammer`) with kernel proof reconstruction |
| **Hidden Dependencies** | Implicit typeclass resolution, coercions, `simp`-set priority changes | Auto-inferred E-matching `{:trigger}` patterns, ambient fuel/axiom pollution | Explicit trigger hints (`--show-hints`), scoped axiom/fuel control, interactive permission/context views |

---

### 5. Methodological Requirements for Falsifiable PL & Prover Usability Evaluations

*Basis: execution (`probe_human_factors_metrics.py`, Sections 1 & 3) + normative literature (Stefik 2013; Coblenz 2021, 2022; Crichton 2023; Zhou 2023)*

Designing falsifiable empirical evaluations for programming languages or verification tools requires preventing two pervasive methodological failures quantified in our micro-probe:

1. **Statistical Power Collapse in Small Between-Subjects Lab Studies (`probe_human_factors_metrics.py`, Section 1)**: For a standard two-sided $\alpha = 0.05$ between-subjects test comparing two language designs (e.g., new annotation syntax vs. baseline):

   | Study Size ($N$ Total, Equal Arms) | Power at Small Effect ($d = 0.30$) | Power at Medium Effect ($d = 0.50$) | Power at `Aquascope` Effect ($d = 0.56$) | Power at Large Effect ($d = 0.80$) |
   |---|---:|---:|---:|---:|
   | Small lab RCT (`N = 20`, 10/arm) | `10.3%` | **`20.1%`** | **`24.0%`** | `43.2%` |
   | Medium RCT (`N = 60`, 30/arm) | `21.3%` | `49.1%` | `58.3%` | `87.3%` |
   | Large RCT (`N = 120`, 60/arm) | `37.6%` | `78.2%` | `86.6%` | `99.2%` |
   | Ownership Inventory (`N = 342`) | `79.2%` | `99.6%` | **`99.9%`** | `100.0%` |
   | Bronze RCT (`N = 428`) | `87.4%` | **`99.9%`** | `100.0%` | `100.0%` |

   A 20-participant between-subjects PL lab study fails to detect a true medium effect (`d = 0.50`) **nearly 80% of the time** (false negative) and inflates false-discovery / sign-error risk when significant! Consequently, small-$N$ studies ($N \le 30$) are appropriate for **formative qualitative discovery** (think-aloud usability bugs, contextual inquiry as in *QED in Context* and early `Obsidian`/`PLIERS` iterations) or **within-subjects crossover designs** controlling inter-programmer variance, whereas summative between-subjects claims require high-$N$ RCTs ($N \ge 120$, or course/textbook deployments like `Bronze` and `Aquascope`) with pre-registered primary outcomes and placebo/active controls (`Randomo`).

2. **SMT Verification Stability Perturbation Budgets (`probe_human_factors_metrics.py`, Section 3)**: Under Mariposa's mutant-perturbation model (where a brittle auto-active query fails with probability $p_{\text{fail}}$ across semantically equivalent symbol-rename/shuffle/seed perturbations), the probability of observing $\ge 1$ instability failure in $M$ runs is $1 - (1 - p_{\text{fail}})^M$:

   | Underlying Instability $p_{\text{fail}}$ | Single CI Run ($M = 1$) | $M = 10$ Mutants | $M = 30$ Mutants | $M = 60$ Mutants |
   |---:|---:|---:|---:|---:|
   | `0.02` (2% brittle) | `2.00%` | `18.29%` | `45.45%` | `70.24%` |
   | `0.05` (5% brittle) | **`5.00%`** | `40.13%` | `78.54%` | **`95.39%`** |
   | `0.15` (15% brittle) | `15.00%` | `80.31%` | `99.24%` | **`99.99%`** |
   | `0.30` (30% brittle) | `30.00%` | `97.18%` | `100.00%` | `100.00%` |

   Single-shot deterministic verification gives developers an illusion of stability (`95%` false calm on a `5%`-unstable proof obligation) until an unrelated refactoring triggers a mysterious CI outage. Usability evaluations of auto-active verifiers must therefore measure both **authoring time** and **perturbation stability** rather than one-shot verification success alone.

## Boundaries

- **Novice-to-Expert Longitudinal Transfer (`unknown` / `known not to apply` without qualification)**: Stefik & Siebert's `Randomo` RCTs (`2013`) and Pane et al.'s natural-programming study (`2001`) measured **novices and non-programmers** over short exposure windows. Whether syntax differences between `Quorum` and C-family languages persist after months or years of professional immersion is not established by novice RCTs (`unknown` long-term asymptotic effect size; naive extrapolation to senior engineers is `known not to apply` without longitudinal evidence).
- **Industrial-Scale Multi-Year Maintenance vs. Classroom Tasks (`not examined`)**: The `Bronze` RCT (`N = 428`, ICSE 2022) measured university students on a structured multi-part aliasing assignment, and `Aquascope` (`N = 342`, OOPSLA 2023) measured online textbook readers via the Ownership Inventory. Performance overhead, latency pauses, and team-scale maintenance trade-offs of optional GC (`Bronze`) in production Rust services over multi-year lifecycles were `not examined`.
- **LLM / Agentic Proof-Assistant Co-Reasoning Usability (`not examined`)**: While recent papers (e.g., neural/agentic proof automation for Rocq/Lean and natural-language autoformalization) intersect human proof engineering, controlled empirical RCTs measuring human cognitive load, over-reliance, and specification-validation error rates under AI-assisted theorem proving were `not examined` in depth here.
- **Exact Sample Sizes & Per-Task p-Values Across All Four Stefik & Siebert Sub-Experiments (`not examined` in full-text tables)**: The primary-source summary and Crossref record verify Stefik & Siebert's four-study structure, the `Java`/`Perl` vs. `Randomo` statistical equivalence, and Token Accuracy Mapping (`10.1145/2534973`); exact per-sub-experiment sample counts and pairwise `F`/`p` tables from the paywalled ACM TOCE PDF were not directly transcribed (`not examined`).
- **Beckert & Grebing Deductive-Verification Usability Studies (`not examined` directly)**: Early Cognitive Dimensions evaluations of the KeY interactive deductive verifier by Beckert and Grebing were noted via literature search but their primary full-text artifacts were not directly fetched.
- **Overclaiming From Cognitive Dimensions (`known not to apply`)**: Green & Petre's Cognitive Dimensions framework is explicitly a **broad-brush analytical vocabulary** for surfacing design trade-offs, not a quantitative predictive metric or substitute for empirical user trials (`known not to apply` as standalone proof of usability).

## Evidence

### Primary Git Repository Evidence (Observed `2026-11-19`)

1. **`qorf/quorum-language` @ `1d907c10b24a4e98f62833ce990320b19c075243`**
   - `Quorum/Library/Standard/Libraries/Language/Compile/Parser.quorum` (lines 12–89): self-hosted Quorum syntax (`action ... returns ... end`, `not=`, `undefined`, `me:` dispatch) and natural-language `CompilerError` construction (`CheckName`, lines 68–82).
2. **`mcoblenz/Glacier` @ `4f2b3d9486d441483f3f8997feb03e134953a201`**
   - `src/edu/cmu/cs/glacier/GlacierVisitor.java` (lines 51–85): Checker Framework `BaseTypeVisitor<GlacierAnnotatedTypeFactory>` implementing transitive class immutability (`typeIsImmutable`, `@Immutable`).
3. **`mcoblenz/Obsidian` @ `a32efc07b0a3c3128413999324f55f16fb349c1b`**
   - `src/main/scala/edu/cmu/cs/obsidian/typecheck/ObsidianType.scala` (lines 4–105): `TypeState` (`States`, `PermVar`, `Permission`), `Permission` (`Shared`, `Owned`, `Unowned`, `Inferred`), `OwnershipConsumptionMode`, and `ContractReferenceType::residualType`.
4. **`mcoblenz/bronze` @ `529a3e4ff83745265053441dbe2f131622d1c18b`**
   - `bronze_gc/src/lib.rs` (lines 68–100): `GcBoxHeader` (`vtable`, `marked: Cell<bool>`), `BorrowFlag` (`is_writing`, `is_reading` adapted from `core::cell.rs`), `GcBox<T>`, and `GcNullableBox<T>`.
5. **`cognitive-engineering-lab/aquascope` @ `f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`**
   - `crates/aquascope/src/analysis/permissions/mod.rs` (lines 32–120): `AquascopeFacts` implementing `polonius_engine::FactTypes`, `struct Permissions { read, write, drop }` (noting *drop* = *own*), and `PermissionsData`.
   - `crates/aquascope/src/analysis/permissions/flow.rs` (lines 1–75): abstract origin ($\varrho$) and local source ($S$) region taint graph $\Theta$, formal `borrowfail` rules for missing universal constraints and local-outlives-universal errors over Polonius `subset_base` facts.
6. **`hazelgrove/hazel` @ `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`**
   - Pinned upstream HEAD revision (`README.md`, `src/haz3lcore/statics/`).
7. **`dafny-lang/dafny` @ `8c137ba351c60a521cfb122011770fdbea9a0453`**
   - `Source/DafnyCore/Options/CommonOptionBag.cs` (lines 22–75): auto-active UX/diagnostic options `--progress` (`None|Symbol|Batch`), `--manual-triggers`, `--show-hints`, `--show-assertions` (`None|Implicit|All`), and `--manual-lemma-induction`.
8. **`leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e`**, **`rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`**, **`verus-lang/verus` @ `a95764f23c6876b47500beda6118e2d142a87cc3`**
   - Pinned upstream HEAD revisions for interactive and auto-active prover references.

### Peer-Reviewed Literature & Preprints (Crossref / arXiv Verified `2026-11-19`)

- T. R. G. Green, M. Petre, *"Usability Analysis of Visual Programming Environments: A 'Cognitive Dimensions' Framework"*, Journal of Visual Languages & Computing 7(2), 1996, DOI `10.1006/jvlc.1996.0009`.
- J. F. Pane, C. A. Ratanamahatana, B. A. Myers, *"Studying the language and structure in non-programmers' solutions to programming problems"*, International Journal of Human-Computer Studies 54(2), 2001, DOI `10.1006/ijhc.2000.0410`.
- A. Stefik, S. Siebert, *"An Empirical Investigation into Programming Language Syntax"*, ACM Transactions on Computing Education 13(4), 2013, DOI `10.1145/2534973`.
- M. Coblenz, W. Nelson, J. Aldrich, B. Myers, J. Sunshine, *"Glacier: Transitive Class Immutability for Java"*, ICSE 2017, DOI `10.1109/ICSE.2017.52`.
- T. Ringer, K. Palmskog, I. Sergey, M. Gligoric, Z. Tatlock, *"QED at Large: A Survey of Engineering of Formally Verified Software"*, Foundations and Trends in Programming Languages, 2019, DOI `10.1561/2500000045`.
- M. Coblenz, R. Oei, T. Etzel, P. Koronkevich, M. Baker, Y. Bloem, B. A. Myers, J. Sunshine, J. Aldrich, *"Obsidian: Typestate and Assets for Safer Blockchain Programming"*, ACM TOPLAS 42(3), 2020, DOI `10.1145/3417516`.
- M. Coblenz, G. Kambhatla, P. Koronkevich, J. L. Wise, C. Barnaby, J. Sunshine, J. Aldrich, B. A. Myers, *"PLIERS: A Process that Integrates User-Centered Methods into Programming Language Design"*, ACM TOCHI 28(4), 2021, DOI `10.1145/3452379`.
- S. E. Chasins, E. L. Glassman, J. Sunshine, *"PL and HCI: Better Together"*, Communications of the ACM 64(8), 2021, DOI `10.1145/3469279`.
- M. Coblenz, M. L. Mazurek, M. Hicks, *"Garbage Collection Makes Rust Easier to Use: A Randomized Controlled Trial of the Bronze Garbage Collector"*, ICSE 2022, DOI `10.1145/3510003.3510107` (full preprint abstract verified via `arXiv:2110.01098v2`: 633-person class, $N = 428$ students, 4 h vs. 12 h completion on complex aliasing).
- W. Crichton, G. Gray, S. Krishnamurthi, *"A Grounded Conceptual Model for Ownership Types in Rust"*, PACMPL (OOPSLA) 2023, DOI `10.1145/3622841` and CACM 2026, DOI `10.1145/3796537` (full preprint verified via `arXiv:2309.04134`: +9% Ownership Inventory score, $N = 342$, $d = 0.56$).
- Y. Zhou, J. Bosamiya, Y. Takashima, J. G. Li, M. Heule, B. Parno, *"Mariposa: Measuring SMT Instability in Automated Program Verification"*, FMCAD 2023 (and Y. Zhou, J. Shah, Z. Lin, *"Cazamariposas: Automated Instability Debugging in SMT-Based Program Verification"*, LNCS 2025, DOI `10.1007/978-3-031-99984-0_5`).
- J. Shi, C. Torczon, H. Goldstein, B. C. Pierce, A. Head, *"QED in Context: An Observation Study of Proof Assistant Users"*, PACMPL (OOPSLA) 2025, DOI `10.1145/3720426` ($N = 30$ experienced Rocq and Lean practitioners).

### Executable Micro-Probe (`Basis: execution`, `2026-11-19`, Python 3 Linux)

Executed exact Python calculations for (1) two-sample RCT statistical power across $N \in \{20, 60, 120, 342, 428\}$ and $d \in \{0.30, 0.50, 0.56, 0.80\}$, (2) Cartesian modal-lattice growth across 6 orthogonal axes vs. Cowan's `4 ± 1` chunk ceiling, and (3) Mariposa mutant-perturbation detection probability $1 - (1 - p_{\text{fail}})^M$:

```text
=== 1. Two-Sample PL RCT Statistical Power (alpha=0.05 two-sided, Cohen's d & proportion diff) ===
  Small lab RCT (N=20, 10/arm)   -> d=0.30:  10.3% | d=0.50:  20.1% | d=0.56:  24.0% | d=0.80:  43.2%
  Medium RCT (N=60, 30/arm)      -> d=0.30:  21.3% | d=0.50:  49.1% | d=0.56:  58.3% | d=0.80:  87.3%
  Large RCT (N=120, 60/arm)      -> d=0.30:  37.6% | d=0.50:  78.2% | d=0.56:  86.6% | d=0.80:  99.2%
  Ownership Inventory (N=342)    -> d=0.30:  79.2% | d=0.50:  99.6% | d=0.56:  99.9% | d=0.80: 100.0%
  Bronze RCT (N=428)             -> d=0.30:  87.4% | d=0.50:  99.9% | d=0.56: 100.0% | d=0.80: 100.0%

=== 2. Orthogonal Modal Lattice Cognitive State Explosion vs Progressive Disclosure ===
  Axes 1..4 (+linearity/typestate [3]): Cartesian combinations =  108 (exceeds Cowan 4+-1 chunk limit? False)
  Axes 1..5 (+totality/termination [2]): Cartesian combinations =  216 (exceeds Cowan 4+-1 chunk limit? True)
  Axes 1..6 (+memory-model [3]): Cartesian combinations =  648 (exceeds Cowan 4+-1 chunk limit? True)

=== 3. Auto-Active SMT Instability Detection Probability vs Perturbation Sample Size M (Mariposa model) ===
  True instability p_fail=0.05 -> M= 1:   5.00% | M=10:  40.13% | M=30:  78.54% | M=60:  95.39%
  True instability p_fail=0.15 -> M= 1:  15.00% | M=10:  80.31% | M=30:  99.24% | M=60:  99.99%
```

## Revalidation

1. **Inspect Upstream Diagnostic & Ownership Tooling**:
   - Check `Aquascope`: diff `crates/aquascope/src/analysis/permissions/{mod.rs,flow.rs}` against `f2d0a06034` to see whether `ENABLE_FLOW_DEFAULT` (currently `false` at `mod.rs:30`) or additional region-error categories (`hidden type` / `impl Trait`) have been enabled.
   - Check `Dafny`: diff `Source/DafnyCore/Options/CommonOptionBag.cs` against `8c137ba351` for changes to default trigger-hint visibility (`--show-hints`, `--show-assertions`) or built-in perturbation/stability checks.
   - Check `Quorum`: inspect `Quorum/Library/Standard/Libraries/Language/Compile/Parser.quorum` against `1d907c10b2` for grammar or diagnostic revisions driven by newer RCT rounds.
2. **Re-run the Self-Contained Power & Perturbation Verification Probe**:
   ```bash
   python3 - <<'PY'
   import math
   norm_cdf = lambda x: 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))
   z = 1.959963984540054
   pwr_20 = 1.0 - norm_cdf(z - 0.50 * math.sqrt(10.0/2.0)) + norm_cdf(-z - 0.50 * math.sqrt(10.0/2.0))
   pwr_342 = 1.0 - norm_cdf(z - 0.56 * math.sqrt(171.0/2.0)) + norm_cdf(-z - 0.56 * math.sqrt(171.0/2.0))
   det_60 = 1.0 - (1.0 - 0.05)**60
   assert abs(pwr_20 - 0.2009) < 1e-3 and pwr_342 > 0.998 and abs(det_60 - 0.9539) < 1e-3
   print(f"OK: power(N=20,d=0.50)={pwr_20:.4f}, power(N=342,d=0.56)={pwr_342:.4f}, det(M=60,p=0.05)={det_60:.4f}")
   PY
   ```
   A passing probe verifies only the analytical power and perturbation formulas; validating whether a new language surface or proof-assistant UI reduces real developer error rates requires conducting a pre-registered empirical user study following PLIERS/RCT guidelines.
