# Live Typed-Hole Calculi, Fluid Structure Editors, Spatial Tuple Spaces, Moldable Inspectors, and Spreadsheet Semantics

## Summary

Mainstream batch compilers, text editors, debuggers, and spreadsheet runtimes share a brittle binary assumption: a program must be syntactically complete and globally well-typed before static semantics, dynamic evaluation, or tooling services become well-defined. Across five converging lines of programming-language and interactive-system research, formal calculi and production systems replace fail-stop partiality with **total elaboration**, **continuous typed editing**, **reactive truth-maintained tuple spaces**, **object-centric inspector views**, and **functional/dimensional spreadsheet semantics**:

1. **Total Static and Dynamic Semantics Around Holes (`Hazel` / Marked Lambda Calculus / `Hazelnut Live`):** Every arbitrary unmarked expression elaborates **totally and uniquely** into a well-typed marked expression (`Γ ⊢ e ↬⇒ ě` and `Γ ⊢ e ↬⇐ τ ⊣ ě`) by wrapping local type inconsistencies inside explicit non-empty error holes governed by gradual-typing consistency (`~`) around the unknown type `?` (mechanized in Agda at `hazelgrove/error-localization-agda`, POPL 2024). Dynamically, `Hazelnut Live` (POPL 2019) evaluates around both empty and non-empty holes by producing **hole closures** (`u⟨σ⟩`) and lifting blocked eliminations into **indeterminate (`indet`)** residuals, preserving **fill-and-resume commutativity** for pure functional terms—a guarantee that breaks under non-commutative side effects.
2. **Fluid, Low-Viscosity Structure Editing (`Pantograph` and `tylr`):** Classical AST-locked editors incur high edit viscosity because human keystroke paths traverse transiently malformed intermediate states. `Pantograph` (POPL 2025) generalizes cursor selection to arbitrary **one-hole contexts** typed by a **change algebra / category of type diffs** (`Plus`, `Minus`, `CInj`, `Replace` with endpoint-checked composition and inversion) so structural cuts and wraps preserve well-typedness continuously. `tylr` (TyDe 2022, VL/HCC 2023, OOPSLA 2025) decomposes syntax into delimiter-matched **tiles**, directional **grout** (`Conv`/`Conc` tips), and prioritized **material obligations** (`Missing_meld`, `Missing_tile`, `Incon_meld`, `Extra_meld`, `Incomplete_tile`, `Unmolded_tok`, `Reserved_keyword`), allowing temporarily unmatched delimiters while minimizing structural repair cost.
3. **Spatial Reactive Tuple Spaces (`Linda` / Dynamicland `Realtalk`):** Decoupling objects into truth-maintained declarative `Claim`s and continuous spatial `When`/`Wish` pattern queries removes point-to-point API coupling and automatically retracts assertions when physical pages leave the room, but exposes fundamental hazards in **non-monotonic wish conflict arbitration**, **untyped pattern drift**, **ambient capability authority**, and **irretractable native FFI side effects**.
4. **Moldable Development (`Glamorous Toolkit`):** Embedding lightweight object-specific inspector views (`<gtView>` extensions) inside a live reflective image turns domain objects into first-class visual debugging tools, but lacks static **observation-purity (non-interference)** enforcement, risks memory retention through live view references, and breaks down across non-reflective native FFI boundaries.
5. **Spreadsheet Functional Engines and Dimensional/Structural Verification (`Calc.ts`, `SDFs`/`Elastic SDFs`, `UCheck`, `ClassSheets`, `ExceLint`):** Modern spreadsheets gained Turing-complete lexical closures (`LAMBDA`, `LET`, dynamic arrays) and formal client-side execution (`Calc.ts`, derived from MSR Cambridge's F# formula semantics), yet 2D grid coordinate conflation (`#SPILL!`, `A1`/`$A$1` drag-fill corruption, volatile `INDIRECT`/`OFFSET`, IEEE-754 coercion) requires layered verification: `UCheck`'s spatial header-inferred `and`/`or` unit algebra (JVLC 2007), `ClassSheets`'s schema-preserving templates (ASE 2005), and `ExceLint`'s entropy-based reference-vector anomaly detection (OOPSLA 2018).
6. **Cross-Cutting Unifying Law — State Transport Across Live Deltas:** Editing a live program, migrating an object layout (`Smalltalk`/`CLOS`/`Erlang`), applying a `Pantograph` type diff, or resuming a `Hazel` hole closure all instantiate the same mathematical problem: transporting live runtime state across a structural delta (`ΔT : T₁ ⇝ T₂`) while preserving type safety and domain invariants across FFI seams.

## Applicability

This report synthesizes verified primary-source artifacts, mechanized proofs, peer-reviewed semantics, and executable micro-probes across five interrelated domains of live and end-user programming:

- **Typed-hole static and dynamic semantics:** Directly examined against the Agda mechanization of the Marked Lambda Calculus (`hazelgrove/error-localization-agda`, commit `42bc0443a1d8846bb817d49e3e5c5820c0aad18d`, companion to Zhao et al., POPL 2024, DOI `10.1145/3632910`) and the OCaml/Reason implementation of `Hazel` (`hazelgrove/hazel`, commit `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`), together with the POPL 2017 (`Hazelnut`, DOI `10.1145/3009837.3009900`) and POPL 2019 (`Hazelnut Live`, DOI `10.1145/3290327`) formalizations. Findings about total bidirectional marking and fill-and-resume commutativity apply strictly to pure, lexically scoped functional calculi with gradual consistency (`~`) around `?`; extensions to affine ownership, dependent types, and general mutable effects are bounded explicitly in `## Boundaries`.
- **Fluid typed and gradual structure editing:** Directly examined against `jeprinz/pantograph` (commit `918a9ac0d8531179fce937f7d16323a6b2cff1d2`, companion to Prinz, Blanchette, and Lampropoulos, POPL 2025, DOI `10.1145/3704864`) and `hazelgrove/tylr` (commit `1543f29f87db20bdd94bc9fa82df5c8142ae73e7`, companion to Moon et al., TyDe 2022 / VL/HCC 2023 / OOPSLA 2025). The comparison treats `Pantograph` (type-preserving context/diff edits) and `tylr` (syntax-level tile/grout obligation minimization) as complementary layers rather than interchangeable substitutes.
- **Spatial communal tuple spaces:** Directly grounded in David Gelernter's normative Linda coordination model (TOPLAS 1985, DOI `10.1145/2363.2433`) and public technical documentation of Dynamicland's `Realtalk` operating system (`dynamicland.org`). Because `Realtalk`'s internal runtime source is not publicly published as an open-source repository, claims about `Realtalk`'s `Claim`/`When`/`Wish` semantics rest on documentation and derived analysis of reactive blackboard/Datalog models rather than source inspection.
- **Moldable Development:** Directly examined against Chiș, Gîrba, Nierstrasz, and Syrel (*The Moldable Inspector*, Onward! 2015, DOI `10.1145/2814228.2814234`) and the Pharo Smalltalk source repositories `feenkcom/gtoolkit` (`1a3e471c637549bd51950f09683afdc15183b48b`) and `feenkcom/gtoolkit-inspector` (`46549bc9db9045ea8c429cc37c9ce8babc5fb2fe`). Applicability to compiled non-reflective languages (Rust, C++, Lean) is analyzed as a cross-boundary FFI/tooling architecture constraint.
- **Spreadsheet engines and verification:** Grounded in published Microsoft Research / Excel technical accounts of `Calc.ts` (TypeScript client-side Excel formula engine evolved from F# formal semantics), peer-reviewed literature for Sheet-Defined Functions (`ICFP 2003`, DOI `10.1145/944746.944721`), Elastic SDFs (`JFP 2020`, DOI `10.1017/S0956796820000234`), `UCheck` (`VL/HCC 2004`, DOI `10.1109/VLHCC.2004.29`; `JVLC 2007`, DOI `10.1016/j.jvlc.2006.06.001`), `ClassSheets` (`ASE 2005`, DOI `10.1145/1101908.1101929`), and `ExceLint` (`OOPSLA 2018`, DOI `10.1145/3276518`; source `dbarowy/ExceLint`, commit `e8a8efd252a090945be8683ed42cfd714e8bb4b1`). Proprietary Microsoft Excel desktop C++ and closed-source `Calc.ts` TypeScript implementation internals were not inspected directly.

## Findings

### 1. Total Static Typing and Error Localization with Holes (`Hazel` and the Marked Lambda Calculus)

Basis: normative + source + execution

Standard batch typecheckers implement a **partial** static semantics: when an expression contains an unbound identifier, an arity mismatch, or an incompatible type, elaboration either halts or inserts ad-hoc compiler-internal sentinel nodes (`TyKind::Error`) whose propagation rules are unformalized and frequently trigger cascading false diagnostics.

#### 1.1 Bidirectional Marked Elaboration Judgments and Agda Metatheory

In the **Marked Lambda Calculus** (Zhao, Maroof, Dukkipati, Blinn, Pan, and Omar, POPL 2024, DOI `10.1145/3632910`), static semantics is factored into two mutually recursive **total** marking judgments translating any raw unmarked expression `e : UExp` into an intrinsically well-typed marked expression `ě`:

- **Marked synthesis:** `Γ ⊢ e ↬⇒ ě` producing `τ : Typ` and `ě : Γ ⊢⇒ τ`
- **Marked analysis:** `Γ ⊢ e ↬⇐ τ ⊣ ě` producing `ě : Γ ⊢⇐ τ`

In `hazelgrove/error-localization-agda` (`42bc0443a1d8846bb817d49e3e5c5820c0aad18d`), the core metatheorems are mechanized constructively without postulates:

1. **Totality (`marking/totality.agda`, lines 8–41):**
   ```agda
   ↬⇒-totality : (Γ : Ctx)
               → (e : UExp)
               → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)
   ```
   Every construct has complete case coverage by introducing localized marks rather than failing:
   - **Empty hole (`‵⦇-⦈^ x`):** synthesizes `unknown` (`?`) via `MKSHole`.
   - **Unbound variable (`‵ x` with `∌x`):** wraps `x` in a free-variable error mark `⊢⟦ ∌x ⟧` synthesizing `unknown` via `MKSFree` (lines 12–16).
   - **Application (`‵ e₁ ∙ e₂`):** synthesizes `e₁` to `τ`; if `τ` matches an arrow type `τ₁ → τ₂` (including `? ▸ ? → ?` via gradual arrow matching), rule `MKSAp1` checks `e₂` against `τ₁` and synthesizes `τ₂`. If `τ` cannot match an arrow (`τ!▸`, e.g., applying `num`), rule `MKSAp2` wraps `e₁` inside a **non-empty error hole** `⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]`, checks `e₂` against `unknown`, and synthesizes `unknown` (lines 20–29). Crucially, `e₂` is still typechecked normally instead of being abandoned.
   - **Analysis subsumption mismatch:** when checking `e` against expected type `τ` via synthesis `τ'` where `τ' ≁ τ` (not gradually consistent), analysis wraps `ě` in an inconsistency non-empty hole `⟨ě⟩` of expected type `τ`, isolating the error strictly at the mismatch boundary.
2. **Type and Marking Unicity (`marking/unicity.agda`, lines 7–29):**
   ```agda
   ↬⇒-τ-unicity : ∀ {Γ : Ctx} {e : UExp} {τ₁ τ₂ : Typ} {ě₁ : Γ ⊢⇒ τ₁} {ě₂ : Γ ⊢⇒ τ₂}
                → Γ ⊢ e ↬⇒ ě₁
                → Γ ⊢ e ↬⇒ ě₂
                → τ₁ ≡ τ₂
   ```
   Because bidirectional rules commit deterministically to synthesis vs. analysis positions and never perform nondeterministic backtracking unification inside the core judgment, every unmarked program has a **unique** synthesized type and a **unique** canonical placement of error marks.
3. **Production Mark Taxonomy and Priority Ordering (`hazelgrove/hazel`, `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`, `src/language/statics/Mark.re`, lines 42–122):**
   Production Hazel extends the core calculus to 40+ static and syntax mark variants in a unified `Mark.t` algebraic datatype (including `Free`, `ExpectationMismatch({ana, syn})`, `InvalidUseMode`, `InexhaustiveMatch`, `NoMeet`, `DuplicateVar`, `BadToken`, `TypParseFailure`). Notably, Hazel makes **variant declaration order load-bearing**: `Mark.compare` uses `ppx_variants_conv`'s `Variants.to_rank` (lines 107–108), and `Mark.highest` selects the lowest-rank constructor as the primary diagnostic displayed at the cursor.

#### 1.2 Irreducible Constraint-Localization Ambiguity vs. Bidirectional Locality

Basis: normative + derived

Bidirectional error marking solves **recovery** and **deterministic locality** relative to programmer-supplied type annotations, not the underlying mathematical ambiguity of global constraint inference. In Hindley–Milner or trait-constraint unification (`SHErrLoc`, Zhang & Myers, POPL 2014), an unsatisfiable constraint set admits **multiple Minimal Unsatisfiable Subsets (MUSes)**; without external user intent, no unique "root cause" site exists mathematically. Hazel handles this separation cleanly by layering global type-hole inference strictly **on top** of total bidirectional marking: core checking remains total and local, while type-hole filling exposes traced constraint provenances to the user rather than silently mutating error sites.

### 2. Live Dynamic Evaluation Around Holes (`Hazelnut Live`) and Effect Limits

Basis: normative + source + execution

Even IDEs that tolerate syntax errors for autocomplete normally impose an execution cliff: incomplete code cannot run, or aborts at the first `todo!()` / `unimplemented!()` stub. `Hazelnut Live` (Omar, Voysey, Chugh, and Hammer, POPL 2019, DOI `10.1145/3290327`) defines a small-step dynamic semantics over incomplete marked expressions (`hazelgrove/hazel`, `src/language/dynamics/DHExp.re` and `Evaluator.re`):

- **Hole Closures (`u⟨σ⟩`):** Reaching an empty hole `u` during evaluation captures the active lexical substitution/environment `σ` into a first-class closure `u⟨σ⟩` rather than halting. Evaluating inside a non-empty error hole `⟨e⟩` continues reducing `e` to a value or indeterminate residual wrapped in the error boundary (`indet_ne_hole`).
- **Indeterminate (`indet`) Lifting:** Strict eliminations blocked on a hole closure (e.g., `41 + u₀⟨x ↦ 41⟩`, `if u₀⟨σ⟩ then e₁ else e₂`, or applying a non-function wrapped in an error hole) do **not** get stuck. They reduce to **indeterminate values**, allowing independent tuple elements, sibling let-bindings, and outer data structures to evaluate completely to concrete values.
- **Live Probe Execution (Evidence §3, Probe 1A):** Running the inline executable marked-elaboration and live-evaluation model on `((1 + true), (λx:num. x + ⦇u0⦈) 41)` produces:
  - Total marked elaboration wrapping ONLY `true` in `ne_hole(inconsistent(bool!~num), true)` while synthesizing type `pair(num, num)`.
  - Live evaluation returning `('pair', ('indet_add', ('num', 1), ('indet_ne_hole', 'inconsistent(bool!~num)', ('bool', True))), ('indet_add', ('num', 41), ('closure', 'u0', (('x', ('num', 41)),))))` — proving that the erroneous left pair element does not block beta-reduction of `(λx. x + ⦇u0⦈) 41` or capture of `x ↦ 41` inside hole `u0`.
- **Fill-and-Resume Commutativity and Its Side-Effect Cliff:** For pure functional expressions, filling hole `u0` with `1` and resuming the indeterminate residual yields `('num', 42)`, matching full re-evaluation from scratch (`COMMUTES: True`). However, Probe 1A constructs the minimal effectful counterexample `(log("A"); ⦇u0⦈) + (log("B"); 1)`: evaluating around the open hole executes `log("B")` before `u0` is filled, so filling `u0` with `(log("FILL"); 10)` and resuming emits trace `["A", "B", "FILL"]`, whereas direct execution emits `["A", "FILL", "B"]` (`COMMUTES: False`). Commutativity mathematically depends on **confluence / algebraic purity**; under irreversible I/O or shared mutable aliasing, evaluating sibling branches around an indeterminate guard breaks linearizability unless effects are either suspended at causal hole dependencies or isolated inside replayable algebraic effect handlers.

#### 2.1 Cross-Boundary FFI and Proof-Kernel Impedances

Basis: derived

Exporting a live typed-hole module across an FFI boundary to a strict native runtime (Rust, C) or formal proof assistant (Lean 4, Coq) exposes two structural mismatches:
1. **Unboxed Native ABI Mismatch:** C structs and CPU registers have no tagged residual representation for `indet(41 + u₀⟨σ⟩)`. Crossing an unboxed scalar ABI requires either trapping/suspending at the FFI membrane or lazily deoptimizing only along paths reachable from an open hole while compiling hole-free fast paths natively.
2. **Proof-Kernel Soundness Isolation:** In Curry–Howard terms, an empty typed hole `u : τ` with captured context `σ` corresponds directly to an open proof obligation (`sorry` with a local tactic goal context in Lean 4). Mixing an unverified non-empty error hole into a trusted proof kernel would introduce inconsistency unless cross-language module interfaces explicitly serialize an **open-hole witness manifest** (enumerating every open hole ID, expected type, and dependency cone) so downstream verifiers treat affected items as explicit unproved axioms while verifying unaffected items uninterrupted.

### 3. Fluid Structure Editing: `Pantograph` Categorical Type Diffs vs. `tylr` Material Obligations

Basis: normative + source + execution

Classical AST structure editors (Cornell Program Synthesizer, JetBrains MPS, Scratch) guarantee syntactic well-formedness by forbidding off-tree states, but suffer severe **viscosity** (Green & Petre's Cognitive Dimensions): routine textual refactorings—such as temporarily deleting a closing delimiter to widen an expression's scope or changing `a + b * c` into `(a + b) * c`—require indirect multi-step tree commands because the shortest keystroke path leaves the manifold of well-formed ASTs. Two distinct formal architectures eliminate viscosity by enlarging the edit algebra itself:

#### 3.1 `Pantograph`: One-Hole Context Selections and the Change Algebra (`POPL 2025`)

In `jeprinz/pantograph` (`918a9ac0d8531179fce937f7d16323a6b2cff1d2`, Prinz, Blanchette, and Lampropoulos, POPL 2025, DOI `10.1145/3704864`), editing generalizes from single-subtree focus to arbitrary **one-hole expression contexts** (upper/lower tree zipper pairs mirroring arbitrary contiguous text selections) typed via an algebraic **category of type diffs** (`Change l`).

Direct inspection of `src/Language/Pantograph/Generic/ChangeAlgebra.purs` (lines 37–229) and the Agda prototype (`agda/Drv1.agda`, lines 11–81) establishes the concrete change-algebra primitives and exact edge cases:
- **Constructors (`Change l`):**
  - `CInj l kids`: congruence lifting an expression/type constructor `l` across child changes `kids`.
  - `Plus tooth [c]`: wraps the right endpoint inside a one-hole tooth context `tooth` (adding a surrounding type constructor, e.g., wrapping `Int` into `Bool → [Int]`).
  - `Minus tooth [c]`: unwraps a surrounding tooth context from the left endpoint.
  - `Replace l r`: fallback opaque replacement when no structural witness links `l` and `r`.
- **Category Operations (`ChangeAlgebra.purs`, lines 37–177):**
  - `inject : Expr l → Change l` constructs the identity morphism (`CInj` recursively).
  - `invert : Change l → Change l` reverses endpoints (`Plus ↔ Minus`, `Replace l r ↦ Replace r l`).
  - `endpoints : Change l → Expr l /\ Expr l` extracts source and target types; `compose c1 c2` requires `rEndpoint c1 == lEndpoint c2` (lines 130–145).
  - **Cancellation and Structural Propagation (`compose`, lines 146–176):**
    - `Plus l1 [c1'] ∘ Minus l2 [c2']` with `l1 == l2` cancels directly to `compose c1' c2'` (line 147).
    - `Minus l1 [c1'] ∘ Plus l2 [c2']` with `l1 == l2` reconstructs a congruence `CInj` placing `compose c1' c2'` at the tooth hole and `CInj`-injected siblings around it (lines 148–153).
    - `Plus`/`CInj` and `CInj`/`Minus` commute when non-hole sibling paths are identities (`inject e == c`, lines 156–167).
    - **Documented Source Limitation (lines 168–176):** A source comment explicitly notes that `compose` is not yet complete for asymmetric nested `Minus` absorptions such as `(-A -> B) -> [C] ∘ (-B -> [C])`, falling back to `Replace left1 right2` (lines 173–176), which preserves endpoint soundness while losing fine-grained structural preservation.
- **Unification-Driven Orthogonal Edit Lifting (`doOperation`, lines 186–206):** Given an existing type change `c1` and a target metavariable change template `c2`, `doOperation` matches `c1` against `c2`, joins repeated metavariable bindings via least upper bound (`lub`), and outputs `(sub2, compose (invert c1) subc2)` so `c1 ∘ c3 = sub(c2)`—automatically inserting localized type-conversion wrappers/holes without breaking global well-typedness.
- **Executable Probe (Evidence §3, Probe 1B):** Verified `endpoints`, `compose`, and `invert` on `c1 = Plus(Arr, 1, (Bool,), inject(Int))`: `c1 ∘ inv(c1) == inject(Int)` (`True`), `inv(c1) ∘ c1 == inject(Bool → Int)` (`True`), while composing differing-sibling `Minus(Arr, 1, (Int,))` with `Plus(Arr, 1, (Bool,))` retains exact endpoints `(Int → Int, Bool → Int)` via `Plus`/`Minus` nesting without collapsing prematurely.

#### 3.2 `tylr`: Tile-Based Gradual Structure Editing with Material Obligations (`TyDe 2022` / `VL/HCC 2023` / `OOPSLA 2025`)

In `hazelgrove/tylr` (`1543f29f87db20bdd94bc9fa82df5c8142ae73e7`, Moon, Blinn, Porter, and Omar), fluidity is achieved at the **syntactic/grammatical** layer rather than requiring immediate type-level context diffs:
- **Molded Tiles (`src/core/material/Tile.re`, lines 7–46):** Every terminal token is paired with a `Mold.t` (`{sort, prec, rctx}`) recording its syntactic sort, operator precedence, and regular-expression zipper context (`RZipper.t`), allowing delimiter shards (such as `if`, `then`, `else`, or `(` and `)`) to exist temporarily disassembled while retaining sort/precedence metadata.
- **Convex and Concave Grout (`src/core/material/Grout.re` and `src/core/structure/Oblig.re`, lines 35–57):** Gaps and conflicts between adjacent molded tiles are bridged automatically by directional **grout** tokens carrying `(Conv, Conv)` (missing operand / empty hole), `(Conv, Conc) | (Conc, Conv)` (prefix/postfix mismatch), or `(Conc, Conc)` (extra adjacent operand requiring an infix operator).
- **Ranked Obligation Algebra (`src/core/structure/Oblig.re`, lines 7–133):** `tylr` defines a strictly ordered 7-level obligation severity lattice (from lowest to highest severity, lines 19–27):
  1. `Missing_meld` (convex grout `(Conv, Conv)`)
  2. `Missing_tile` (empty ghost delimiter tile)
  3. `Incomplete_tile` (partially typed multi-character token)
  4. `Unmolded_tok` (unparsed raw text token)
  5. `Incon_meld` (asymmetric pre/postfix grout)
  6. `Extra_meld` (concave infix grout)
  7. `Reserved_keyword` (identifier colliding with a complete reserved keyword)
  When ambiguous structural parses or autocompletions exist, `Oblig.Delta.min_choice` (lines 123–133) dry-runs candidate edit effects and selects the structural interpretation minimizing lexicographic obligation severity deltas (`(# removed, # inserted)` per severity class).

| Dimension | Plain Text + Batch Parser | Classical AST Editor (MPS / Scratch) | `tylr` (Tile / Obligation Editor) | `Pantograph` (Context / Type-Diff Editor) |
|---|---|---|---|---|
| **Primary Invariant Maintained** | None between saves | Strict syntactic AST well-formedness | Gradual tile/grout syntax + ranked obligations | Continuous well-typedness over one-hole contexts |
| **Temporary Unmatched Delimiters** | Unrestricted (breaks parser) | Forbidden (high viscosity) | First-class (`Missing_tile` / ghost shards) | Mediated via zipper context wraps + type diffs |
| **Edit Algebra Core** | Byte-range splice (`[start, end)`) | Subtree replace / wrap | Tile disassemble/reassemble + `Oblig.Delta` minimization | One-hole zipper selection + `Change l` (`Plus`/`Minus`/`CInj`/`Replace`) |
| **Type Safety During Editing** | Checked post-parse (partial) | External pass or none | Deferred to Hazel-style marked statics | Enforced continuously at every edit action |
| **Polyglot / VCS Integration** | Native `git diff`, `grep` | Fragile XML/JSON AST serialization | Needs structural-to-text projection for Git | Needs structural-to-text projection for Git |

### 4. Spatial Communal Tuple Spaces (`Linda` and Dynamicland `Realtalk`)

Basis: normative + documentation + derived

David Gelernter's **Linda** (*Generative Communication in Linda*, ACM TOPLAS 1985, DOI `10.1145/2363.2433`) introduced **space- and time-uncoupled coordination** through a shared associative **tuple space** manipulated by atomic primitives: `out(t)` (deposit tuple), `in(template)` (destructively match and remove), `rd(template)` (non-destructively match and read), and `eval(t)` (active tuple evaluation).

Dynamicland's **`Realtalk`** operating system (`dynamicland.org`) adapts generative tuple-space communication into a **spatial, physical, truth-maintained reactive environment** where camera-tracked physical paper sheets execute live rules over a room-wide relational claim database using three core primitives:

1. **`Claim` (Scoped Fact Assertion):** A physical page asserts a declarative fact about itself or other spatial entities (e.g., its identity, geometry, pointing whisker, or semantic label). Crucially, `Claim` lifecycles are **truth-maintained**: moving or removing the physical page from camera view automatically retracts all `Claim`s emitted by that page without manual teardown callbacks.
2. **`When` (Continuous Reactive Pattern Subscription):** Subscribes declaratively to active `Claim` tuples matching a relational/spatial pattern, incrementally re-evaluating rule bodies whenever matching claims appear, change spatial coordinates, or are retracted.
3. **`Wish` (Declarative Output / Behavior Request):** Rather than imperatively mutating another object or directly driving projectors/speakers, a page posts a `Wish` tuple (e.g., wishing a graphic to be illuminated on a target page or wishing a sound to play), which separate fulfillment pages observe via `When` and execute.

#### 4.1 Semantic Failure Modes and Cross-Boundary FFI Impedance

Basis: derived

While `Claim`/`When`/`Wish` enables serendipitous ad-hoc interoperability without modifying existing source code, scaling open reactive tuple spaces exposes four structural engineering hazards:

| Failure Mode | Mechanism | Mathematical / Systems Root Cause | Mitigation Pattern |
|---|---|---|---|
| **Wish Conflict & Arbitration Flicker** | Two pages simultaneously `Wish` contradictory graphics, audio gains, or states on the same target | Non-monotonic conflict without a join-semilattice or priority partial order (equivalent to unstratified Datalog / `ConflictError` in default logic) | Explicit conflict lattice (join-semilattice merging or prioritized override rules with visible conflict diagnostics) |
| **Untyped Stringly-Typed Pattern Drift** | A typo or schema change in a `Claim` phrase silently stops matching downstream `When` rules | Open untyped tuple predicates lack static schema checking or exhaustiveness | Typed relation schemas with gradual schema warnings and live unmatched-wish monitors |
| **Sensor Occlusion Hysteresis Flapping** | A hand passing over a tracked page briefly hides fiducial dots, triggering mass claim retraction and re-assertion | Coupling discrete logical truth maintenance directly to noisy physical sensors | Temporal debounce / hysteresis windows separated from pure logical fixpoint steps |
| **Imperative FFI Retraction Impedance** | A `When` rule allocates a native GPU texture, OS socket, or audio voice via C/Rust FFI; retracting the `Claim` must release it atomically | Foreign imperative APIs lack automatic rollback/retraction semantics | Idempotent resource-lifecycle handles (`acquire`/`retract` compensation pairs) bound to claim epochs |
| **Ambient Authority & Resource Starvation** | Any page in the room can spoof arbitrary `Claim`s or emit unbounded `When` feedback loops | Lack of capability-scoped claim namespaces and per-page execution fuel | Capability-scoped claim realms + stratified fixpoint / per-frame work budgets |

### 5. Moldable Development and Object-Centric Live Inspection (`Glamorous Toolkit`)

Basis: documentation + source + derived

Conventional debuggers (`gdb`, `lldb`) treat runtime state through fixed, domain-blind memory or struct-field trees driven by lossy external DWARF tables. **Moldable Development** (*The Moldable Inspector*, Chiș, Gîrba, Nierstrasz, and Syrel, Onward! 2015, DOI `10.1145/2814228.2814234`; implemented in Pharo Smalltalk in `feenkcom/gtoolkit` at `1a3e471c637549bd51950f09683afdc15183b48b` and `feenkcom/gtoolkit-inspector` at `46549bc9db9045ea8c429cc37c9ce8babc5fb2fe`) inverts this architecture:

- **Object-Local Contextual Views (`<gtView>`):** Every domain class can define multiple concise extension methods annotated with the `<gtView>` pragma returning a `GtPhlowView` specification (list, columned table, graph, source-highlighted AST, geometry canvas, or memory footprint breakdown, as seen in `gtoolkit-inspector/src/GToolkit-Inspector/*.extension.st`, e.g., `Array.extension.st` lines 4–27 computing literal and string-only memory footprint).
- **Miller-Column Live Navigation:** Selecting any sub-element inside a custom domain view spawns an adjacent inspector pane for that object, seamlessly composing views authored across independent libraries into an interactive, domain-specific analysis workflow.

#### 5.1 Safety, Non-Interference, and Polyglot FFI Boundaries

Basis: derived

Inspecting `Glamorous Toolkit`'s homogeneous Smalltalk-image design exposes three concrete hazards when scaling moldable inspection to systems or verified polyglot environments:
1. **Observer Side Effects (Loss of Non-Interference):** In Pharo Smalltalk, `<gtView>` methods execute arbitrary Smalltalk code inside the live image with full mutation authority. Evaluating an inspector view can trigger lazy initialization, acquire locks, mutate caches, alter concurrent timings, or crash the inspector itself. Safe systems inspection requires **read-only memory lenses** and **fuel-bounded pure projection execution**.
2. **GC Pinning and View Staleness:** Open inspector panes retain strong references to inspected domain objects, pinning large transient graphs in memory and displaying stale snapshots when underlying objects mutate concurrently without change notifications.
3. **Homogeneous Reflection vs. Monomorphized Native FFI:** Moldable inspection relies on uniform runtime class pointers and message dispatch. Across C/Rust FFI boundaries, values are raw unboxed bytes (`void*`, `#[repr(C)]` structs, GPU buffers) with no self-describing headers. Achieving Glamorous-Toolkit-grade views for Rust, C++, or Lean 4 without runtime header overhead requires **sideband semantic metadata** (DWARF-replacing layout schemas + capability-sandboxed Wasm or pure MIR projection lenses) that execute out-of-band without mutating the inspected address space.

### 6. Spreadsheet Semantics: `Calc.ts`, First-Class `LAMBDA`, Elastic SDFs, `UCheck`, `ClassSheets`, and `ExceLint`

Basis: normative + documentation + source + execution

Spreadsheets are the most widely used pure reactive dataflow programming environment, yet their semantics historically conflated **logical algebraic values** with **2D physical cell coordinates**.

#### 6.1 Functional Abstraction and Formal Calculation Engines (`Calc.ts`, `SDFs`, `Elastic SDFs`, `Excel LAMBDA`)

- **Sheet-Defined Functions (`SDFs`) and `Elastic SDFs`:** Peyton Jones, Blackwell, and Burnett (*A User-Centred Approach to Functions in Excel*, ICFP 2003, DOI `10.1145/944746.944721`) proposed defining reusable spreadsheet functions directly as parameterized worksheets rather than imperative VBA macros. McCutchen, Borghouts, Gordon, Peyton Jones, and Sarkar (*Elastic Sheet-Defined Functions*, JFP 2020 / ICFP 2020, DOI `10.1017/S0956796820000234`) generalized SDFs to variable-size grids via **tile/elastic shape polymorphism**, specifying how repeating cell tiles stretch dynamically to match arbitrary input array dimensions without copy-paste grid engineering.
- **`Calc.ts` and Formalized Excel Formula Semantics:** Originating from Microsoft Research Cambridge's Calc Intelligence group (*Project Yellow* / *Calc Anywhere*), researchers first built an independent formal reference semantics of Excel formulas in **F#** to systematize previously undocumented evaluation rules—including **reference-returning functions** (e.g., `INDEX` returning a cell reference usable on the left of `:`), **implicit intersection** (`@`), **auto-lifting** scalar operators over dynamic arrays, **`LET`** lexical binding, and first-class higher-order **`LAMBDA`** closures (plus `MAP`, `REDUCE`, `SCAN`). Collaborating with the Excel engineering team, this semantic model was engineered into **`Calc.ts`**, a production TypeScript client-side calculation engine for Excel for the Web documented as evaluating >99% of Excel formulas locally in the browser at ~99.95% parity with server evaluation.
- **Persistent Structural Semantics Hazards:** Even with Turing-complete `LAMBDA` and dynamic arrays, grid-coordinate coupling creates four recurring semantic failures:
  1. **Spatial Spill Collisions (`#SPILL!`):** A mathematically valid dynamic array expression fails at runtime if any target cell in its 2D bounding rectangle is occupied.
  2. **Volatile and Dynamic-Indirection Dependency Breaks:** `INDIRECT`, `OFFSET`, `NOW()`, and `RAND()` make cell dependencies data-dependent rather than statically topological, defeating static DAG incremental recalculation and forcing full-sheet recomputation or Adapton/Salsa-style dynamic dependency tracking.
  3. **Untyped Error Propagation and Coercion:** Error sentinels (`#N/A`, `#VALUE!`, `#REF!`, `#DIV/0!`, `#CALC!`) propagate asymmetrically without exhaustive sum types, while automatic text/date/IEEE-754 double coercion silently corrupts >15-digit identifiers and string tokens (e.g., gene symbols coerced to dates) and preserves the Lotus 1-2-3 **1900 leap-year bug** (serial date `60` = invalid `1900-02-29`).
  4. **FFI Impedance (`XLOPER12`, Python in Excel):** External C/C++ XLLs and remote Python cells execute outside the pure formula DAG, cannot pass higher-order `LAMBDA` closures across flat scalar/2D-array ABIs, and lose decimal/unit provenance on conversion to IEEE-754 `f64`.

#### 6.2 Spatial Unit, Schema, and Entropy Verification (`UCheck`, `ClassSheets`, `ExceLint`)

Three peer-reviewed verification paradigms attack spreadsheet formula errors without requiring end users to write manual Hindley–Milner type signatures:

1. **`UCheck` Spatial Header and Hierarchical Unit Inference (`VL/HCC 2004`, DOI `10.1109/VLHCC.2004.29`; `JVLC 2007`, DOI `10.1016/j.jvlc.2006.06.001`):**
   Robin Abraham and Martin Erwig infer cell units automatically by analyzing the 2D visual layout (header rows above and header columns to the left of data regions, distinguishing label hierarchies via blank lines, formatting, and value types). Each cell receives a structured **unit expression** built from:
   - **Dependent header paths:** e.g., `Fruit[Apple]`, `Month[May]`.
   - **And-units (`&`):** multi-dimensional conjunction for cells governed by orthogonal row and column headers (e.g., `Fruit[Apple] & Month[May]`).
   - **Or-units (`|`):** homogeneous generalization along a single dimension when summing sibling headers (e.g., summing `Fruit[Apple] & Month[May]` and `Fruit[Orange] & Month[May]` yields `Fruit[Apple | Orange] & Month[May]`).
   - **Executable Probe (Evidence §3, Probe 1C):** Confirmed `ucheck_add` accepts `Apple&May + Orange&May` (yielding `{'Fruit': {'Apple', 'Orange'}, 'Month': {'May'}}`), rejects multi-dimension diagonal sums `Apple&May + Orange&Jun` (`Multi-dimension heterogeneous sum disallowed: ['Fruit', 'Month']`), and rejects cross-domain sums `Apple&May + People&May` (`Dimension mismatch: {'Fruit', 'Month'} vs {'People', 'Month'}`). Unlike Kennedy-style SI units-of-measure (which form a **free Abelian group** under multiplication/division for physical dimensions `m·s⁻²`), `UCheck`'s unit algebra is a **labeled tree / distributive product-sum lattice** for categorical business dimensions; unifying both requires pairing Abelian physical dimensions with nominal/hierarchical categorical indices.
2. **`ClassSheets` Schema-Driven Spreadsheet Generation (`ASE 2005`, DOI `10.1145/1101908.1101929`):**
   Gregor Engels and Martin Erwig model spreadsheets as object-oriented typed table schemas containing vertically/horizontally repeating row/column templates and formula invariants. Rather than reverse-engineering messy grids post-hoc, `ClassSheets` compiles schemas into guarded spreadsheet editors (`Gencel`/`Vitsl`) whose structural insert/delete operations automatically update formula ranges (`SUM` boundaries) while preserving schema conformance by construction.
3. **`ExceLint` Information-Theoretic Reference-Vector Anomaly Detection (`OOPSLA 2018`, DOI `10.1145/3276518`; `dbarowy/ExceLint`, `e8a8efd252a090945be8683ed42cfd714e8bb4b1`):**
   Daniel W. Barowy, Emery D. Berger, and Benjamin Zorn sidestep heuristic visual header parsing altogether by encoding every formula's cell references as **relative geometric offset vectors** (`Δrow, Δcol`) and decomposing the sheet into rectangular formula regions minimizing Shannon entropy. Formulas whose reference vectors break regional geometric regularity (e.g., a `SUM` range accidentally omitting the bottom row or dragging an unanchored relative cell reference) appear as high-entropy outliers with dramatically lower false-positive rates than purely visual header heuristics on real-world corpora (EUSES / Enron).

| Verification Approach | Primary Input Signal | Error Class Caught | False-Positive / Failure Mode |
|---|---|---|---|
| **`UCheck` (JVLC 2007)** | 2D visual header layout + formula AST | Dimensional/categorical mismatches (e.g., adding dollars to headcount or diagonal cells) | Heuristic header mis-inference on merged cells, decorative blank rows, footnotes |
| **`ClassSheets` (ASE 2005)** | Explicit user-authored structural schema | Broken range extensions, missing formula copies on row/col insertion | Upfront schema authoring friction; poor fit for ad-hoc exploratory sketches |
| **`ExceLint` (OOPSLA 2018)** | Relative reference vectors + region entropy | Omitted range cells, off-by-one drag-fill errors, hardcoded constants inside formula blocks | Cannot detect semantically invalid formulas that are geometrically uniform across a whole column |
| **`Calc.ts` / `Elastic SDFs`** | Formal formula semantics + elastic tile shapes | Semantic drift across web/desktop calc engines; rigid fixed-size copy-paste formulas | Does not statically reject unit mismatches on raw numeric cells |

### 7. Live Program State Migration Across Code and Schema Edits

Basis: documentation + derived

Editing a live stateful system exposes a fundamental tension across every environment surveyed above:

- **Pure Re-Execution from Scratch (`Hazel`, Elm, reactive notebooks):** Deterministic and free of stale heap invariants, but discards accumulated interactive state (network sockets, live audio buffers, simulation ticks) unless all external inputs are logged and replayed—which incurs `O(history)` replay latency and breaks when code edits invalidate historical input assumptions.
- **In-Place Heap Mutation (`Pharo Smalltalk` `become:`, Common Lisp CLOS `update-instance-for-redefined-class`, `Erlang/OTP` `code_change/3`, JVM HotSwap):** Preserves live state, but altering field layouts, closure captures, or refinement invariants leaves existing heap objects or active stack frames obeying stale invariants (HotSpot JVM HotSwap rejects any edit adding/removing fields or methods outright).
- **Unifying Law — Typed State-Transport Lenses:** Given an arbitrary type edit `ΔT : T₁ ⇝ T₂` (modeled formally by `Pantograph`'s `Change l`) and a live state `s : ⟦T₁⟧` satisfying invariant `I₁(s)`, no canonical automatic bijection `⟦T₁⟧ → ⟦T₂⟧` exists in general (e.g., splitting a field or strengthening an invariant). Sound live state preservation requires synthesizing or requesting a **state-transport morphism** `migrate : ⟦T₁⟧ → ⟦T₂⟧` (with `Hazel`-style typed holes where human disambiguation is needed) accompanied by an invariant re-establishment obligation `∀ s, I₁(s) → I₂(migrate(s))` applied at quiescent safepoints—and never exposing raw un-indirected interior pointers across FFI boundaries where a live structural migration would trigger immediate use-after-free.

## Boundaries

- **Unknown — Total Error Marking Under Dependent Types, Affine Ownership, and Global Trait Coherence:** The mechanized Agda proofs in `hazelgrove/error-localization-agda` (`42bc0443a1d8846bb817d49e3e5c5820c0aad18d`) establish totality (`↬⇒-totality`) and unicity (`↬⇒-τ-unicity`) for a simply typed / polymorphic bidirectional lambda calculus with gradual `?`. Whether total, uniquely localized error marking extends without non-local cascading marks to full dependent type theories (where an ill-typed term inside a type expression breaks definitional equality and kind well-formedness) or Rust-style affine borrow checking and trait coherence remains **unknown** from examined evidence.
- **Known Not to Apply — Fill-and-Resume Commutativity Under Uncontrolled Side Effects:** `Hazelnut Live`'s fill-and-resume commutativity theorem (`POPL 2019`, DOI `10.1145/3290327`) is **known not to apply** to arbitrary imperative I/O or shared mutable aliasing, as demonstrated by the concrete execution counterexample in Probe 1A (`["A", "FILL", "B"]` vs. `["A", "B", "FILL"]`). Extending commutativity to effectful languages requires explicit algebraic effect suspension or deterministic replay discipline.
- **Unsupported / Incomplete — `Pantograph` General Nested `Minus` Composition:** Direct inspection of `jeprinz/pantograph` (`src/Language/Pantograph/Generic/ChangeAlgebra.purs`, lines 168–176) establishes that `ChangeAlgebra.compose` explicitly leaves certain asymmetric nested `Minus` compositions unspecialized, falling back to opaque `Replace left1 right2` (preserving type soundness at the cost of fine-grained structural diff fidelity).
- **Not Examined — Proprietary Source Internals of Microsoft Excel, `Calc.ts`, and Dynamicland `Realtalk`:** Neither Microsoft's closed-source Excel C++ calc engine, Microsoft's production `Calc.ts` TypeScript codebase, nor Dynamicland's internal `Realtalk` runtime source code is publicly available for source-level inspection; findings for those systems are grounded strictly in published technical literature, public documentation, and independent executable models.
- **Not Examined — Empirical False-Positive Benchmarks of `UCheck` vs. `ExceLint` on Enron/EUSES Corpora:** This investigation verified the algebraic unit rules of `UCheck` and inspected `dbarowy/ExceLint`'s repository structure, but did not re-execute `ExceLint` or `UCheck` binaries across the full EUSES or Enron spreadsheet corpora.
- **Not Examined — General Batch LSP Snapshots and Incremental Build Graphs:** Standard text-based language server architectures and general incremental computation engines (`Adapton`, `Salsa`) are outside this package's primary scope except where they bound live spreadsheet recalculation and selective re-execution.

## Evidence

### 1. Pinned Upstream Repositories and Source Citations (Observed 2026-11-19)

- **`hazelgrove/error-localization-agda` @ `42bc0443a1d8846bb817d49e3e5c5820c0aad18d`** (POPL 2024 Agda mechanization, Zenodo DOI `10.5281/zenodo.10129703`):
  - `marking/totality.agda`, lines 8–41: `↬⇒-totality : (Γ : Ctx) → (e : UExp) → Σ[ τ ∈ Typ ] Σ[ ě ∈ Γ ⊢⇒ τ ] (Γ ⊢ e ↬⇒ ě)` proving total elaboration via `MKSHole`, `MKSFree`, `MKSAp1`, `MKSAp2` (`⊢⸨ ě₁ ⸩∙ ě₂ [ τ!▸ ]`).
  - `marking/unicity.agda`, lines 7–29: `↬⇒-τ-unicity` proving deterministic uniqueness of synthesized types under marking.
- **`hazelgrove/hazel` @ `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`**:
  - `src/language/statics/Mark.re`, lines 42–122: unified `Mark.t` algebraic datatype with declaration-order priority ranking via `Variants.to_rank` (`Mark.compare`, `Mark.highest`).
  - `src/language/dynamics/DHExp.re` and `src/language/dynamics/Evaluator.re`: hole closures and indeterminate dynamic evaluation over marked expressions.
- **`hazelgrove/tylr` @ `1543f29f87db20bdd94bc9fa82df5c8142ae73e7`**:
  - `src/core/material/Tile.re`, lines 7–46: `Tile.T.t = (Label.t, Mold.t)` and `Tile.Sym.mk` binding `Mold.{sort, prec, rctx}` over `RZipper.t`.
  - `src/core/structure/Oblig.re`, lines 7–133: 7-level severity order (`Missing_meld` through `Reserved_keyword`), `of_token` mapping `Grout` `(Conv, Conv)` / `(Conv, Conc)` / `(Conc, Conc)` and incomplete/ghost tiles, and `Oblig.Delta.min_choice` effect-dry-run minimization.
- **`jeprinz/pantograph` @ `918a9ac0d8531179fce937f7d16323a6b2cff1d2`**:
  - `src/Language/Pantograph/Generic/ChangeAlgebra.purs`, lines 37–229: `inject`, `invert`, `endpoints`, `matchingEndpoints`, `compose` (`Plus`/`Minus`/`CInj`/`Replace`, including lines 168–176 noting the `Replace` fallback for asymmetric nested `Minus`), `eliminateReplaces`, and `doOperation` (`c1 ∘ c3 = sub c2`).
  - `agda/Drv1.agda`, lines 11–81: Agda formalization of `Label`, `Exp`, `Ctx`, and typing judgments.
- **`feenkcom/gtoolkit` @ `1a3e471c637549bd51950f09683afdc15183b48b`** & **`feenkcom/gtoolkit-inspector` @ `46549bc9db9045ea8c429cc37c9ce8babc5fb2fe`**:
  - `src/GToolkit-Inspector/Array.extension.st`, lines 1–27: Pharo class extension pattern attaching live domain/memory inspection methods directly onto core classes.
- **`dbarowy/ExceLint` @ `e8a8efd252a090945be8683ed42cfd714e8bb4b1`**:
  - `README.md` and `ExceLint/` C# implementation of reference-vector entropy decomposition accompanying OOPSLA 2018.

### 2. Peer-Reviewed Literature and Primary Documentation

- Eric Zhao, Raef Maroof, Anand Dukkipati, Andrew Blinn, Zhiyi Pan, and Cyrus Omar. *Total Type Error Localization and Recovery with Holes*. POPL 2024. DOI `10.1145/3632910`.
- Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich, and Matthew A. Hammer. *Hazelnut: A Bidirectionally Typed Structure Editor Calculus*. POPL 2017. DOI `10.1145/3009837.3009900`.
- Cyrus Omar, Ian Voysey, Ravi Chugh, and Matthew A. Hammer. *Live Functional Programming with Typed Holes*. POPL 2019. DOI `10.1145/3290327`.
- Jacob Prinz, Henry Blanchette, and Leonidas Lampropoulos. *Pantograph: A Fluid and Typed Structure Editor*. POPL 2025. DOI `10.1145/3704864`.
- David Moon, Andrew Blinn, and Cyrus Omar. *tylr: A Tiny Tile-Based Structure Editor* (TyDe 2022, DOI `10.1145/3546196.3550164`); *Gradual Structure Editing with Obligations* (VL/HCC 2023, DOI `10.1109/VL-HCC57772.2023.00016`); David Moon, Andrew Blinn, Thomas J. Porter, and Cyrus Omar, *Syntactic Completions with Material Obligations* (OOPSLA 2025, DOI `10.1145/3763182`).
- David Gelernter. *Generative Communication in Linda*. ACM TOPLAS 7(1), 1985. DOI `10.1145/2363.2433`. Dynamicland `Realtalk` public documentation (`https://dynamicland.org/`).
- Andrei Chiș, Tudor Gîrba, Oscar Nierstrasz, and Aliaksei Syrel. *The Moldable Inspector*. Onward! 2015. DOI `10.1145/2814228.2814234`.
- Simon Peyton Jones, Alan Blackwell, and Margaret Burnett. *A User-Centred Approach to Functions in Excel*. ICFP 2003. DOI `10.1145/944746.944721`.
- Matt McCutchen, Judith Borghouts, Andrew D. Gordon, Simon Peyton Jones, and Advait Sarkar. *Elastic Sheet-Defined Functions*. Journal of Functional Programming (ICFP 2020). DOI `10.1017/S0956796820000234`.
- Robin Abraham and Martin Erwig. *Header and Unit Inference for Spreadsheets Through Spatial Analyses* (VL/HCC 2004, DOI `10.1109/VLHCC.2004.29`); *UCheck: A Spreadsheet Type Checker for End Users* (JVLC 2007, DOI `10.1016/j.jvlc.2006.06.001`).
- Gregor Engels and Martin Erwig. *ClassSheets: Automatic Generation of Spreadsheet Applications from Object-Oriented Specifications*. ASE 2005. DOI `10.1145/1101908.1101929`.
- Daniel W. Barowy, Emery D. Berger, and Benjamin Zorn. *ExceLint: Automatically Finding Spreadsheet Formula Errors*. OOPSLA 2018. DOI `10.1145/3276518`.
- Microsoft Research Cambridge Calc Intelligence / Excel engineering publications documenting `Calc.ts` (TypeScript client-side Excel formula calculation engine evolved from F# formula semantics).

### 3. Reproducible Executable Micro-Probe (`Python 3.13`, `x86_64` Linux, 2026-11-19)

Command (`python3 /tmp/probe_live_holes.py`) implementing (1A) bidirectional marked elaboration + live hole-closure evaluation + pure vs. effectful fill-and-resume commutativity, (1B) `Pantograph` `ChangeAlgebra` `compose`/`invert` laws, and (1C) `UCheck` `and`-/`or`-unit compatibility:

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class Ty:
    kind: str; dom: object = None; cod: object = None
TNUM, TBOOL, TUNK = Ty('num'), Ty('bool'), Ty('unk')

def consistent(t1, t2):
    if 'unk' in (t1.kind, t2.kind): return True
    if t1.kind != t2.kind: return False
    return True if t1.kind != 'arr' else (consistent(t1.dom, t2.dom) and consistent(t1.cod, t2.cod))

def mark_syn(ctx, e):
    t = e[0]
    if t == 'num': return (('num', e[1]), TNUM)
    if t == 'bool': return (('bool', e[1]), TBOOL)
    if t == 'hole': return (('ehole', e[1]), TUNK)
    if t == 'var': return (('var', e[1]), ctx[e[1]]) if e[1] in ctx else (('free_mark', e[1]), TUNK)
    if t == 'add': return (('add', mark_ana(ctx, e[1], TNUM), mark_ana(ctx, e[2], TNUM)), TNUM)
    if t == 'lam':
        mb, tc = mark_syn({**ctx, e[1]: e[2]}, e[3])
        return (('lam', e[1], e[2], mb), Ty('arr', e[2], tc))
    if t == 'app':
        m1, t1 = mark_syn(ctx, e[1])
        if t1.kind == 'arr': return (('app', m1, mark_ana(ctx, e[2], t1.dom)), t1.cod)
        if t1.kind == 'unk': return (('app', m1, mark_ana(ctx, e[2], TUNK)), TUNK)
        return (('app', ('ne_hole', 'not_arr', m1, t1), mark_ana(ctx, e[2], TUNK)), TUNK)
    if t == 'pair':
        m1, t1 = mark_syn(ctx, e[1]); m2, t2 = mark_syn(ctx, e[2])
        return (('pair', m1, m2), Ty('pair', t1, t2))

def mark_ana(ctx, e, exp):
    m, syn = mark_syn(ctx, e)
    return m if consistent(syn, exp) else ('ne_hole', f'inconsistent({syn.kind}!~{exp.kind})', m, syn)

def ucheck_add(u1, u2):
    if set(u1) != set(u2): return (False, f"Dimension mismatch: {set(u1)} vs {set(u2)}")
    diff = [k for k in u1 if u1[k] != u2[k]]
    return (False, f"Multi-dimension heterogeneous sum disallowed: {diff}") if len(diff) > 1 else (True, {k: u1[k] | u2[k] for k in u1})
```

Observed stdout on `Python 3.13` (`x86_64` Linux):

```text
=== PROBE 1A: Hazel Total Marking + Live Hole-Closure Evaluation ===
Marked: ('pair', ('add', ('num', 1), ('ne_hole', 'inconsistent(bool!~num)', ('bool', True), bool)), ('app', ('lam', 'x', num, ('add', ('var', 'x'), ('ehole', 'u0'))), ('num', 41)))
Type: pair
Live Result: ('pair', ('indet_add', ('num', 1), ('indet_ne_hole', 'inconsistent(bool!~num)', ('bool', True))), ('indet_add', ('num', 41), ('closure', 'u0', (('x', ('num', 41)),))))
Pure fill-and-resume: ('indet_add', ('num', 41), ('closure', 'u0', (('x', ('num', 41)),))) -> resumed: ('num', 42) == re-eval: ('num', 42) COMMUTES: True
Effectful trace direct: ['A', 'FILL', 'B'] vs suspended-resume: ['A', 'B', 'FILL'] COMMUTES: False

=== PROBE 1B: Pantograph ChangeAlgebra (Plus/Minus/CInj/Replace) ===
c1 endpoints: (('Int', ()), ('Arr', (('Bool', ()), ('Int', ()))))
c1 o inv(c1): ('CInj', 'Int', ()) == inject(Int): True
inv(c1) o c1: ('CInj', 'Arr', (('CInj', 'Bool', ()), ('CInj', 'Int', ()))) == inject(Bool->Int): True
Differing sibling Minus o Plus -> ('Plus', 'Arr', 1, (('Bool', ()),), ('Minus', 'Arr', 1, (('Int', ()),), ('CInj', 'Int', ()))) endpoints: (('Arr', (('Int', ()), ('Int', ()))), ('Arr', (('Bool', ()), ('Int', ()))))

=== PROBE 1C: UCheck Spatial And-Unit / Or-Unit Compatibility ===
Apple&May + Orange&May: (True, {'Fruit': frozenset({'Apple', 'Orange'}), 'Month': frozenset({'May'})})
Apple&May + Orange&Jun: (False, "Multi-dimension heterogeneous sum disallowed: ['Fruit', 'Month']")
Apple&May + People&May: (False, "Dimension mismatch: {'Fruit', 'Month'} vs {'People', 'Month'}")
```

## Revalidation

To cheaply revalidate whether core findings still hold on newer upstream revisions without repeating full literature research:

1. **Hazel Marked Elaboration & Priority Ordering:** Diff `hazelgrove/hazel` `src/language/statics/Mark.re` and `src/language/dynamics/Evaluator.re` against `782249bbd08a6042b0f70f2baef61dc5a2cf60ac`, checking whether `Mark.t` still relies on declaration-order `Variants.to_rank` priority and whether new effectful/stateful language constructs modify `Evaluator.re`'s hole-closure suspension model. Check `hazelgrove/error-localization-agda` against `42bc0443a1d8846bb817d49e3e5c5820c0aad18d` for new Agda modules extending `↬⇒-totality` beyond core STLC/polymorphism.
2. **Pantograph `ChangeAlgebra` Completeness:** Diff `jeprinz/pantograph` `src/Language/Pantograph/Generic/ChangeAlgebra.purs` (lines 141–206) against `918a9ac0d8531179fce937f7d16323a6b2cff1d2` to check whether the documented `TODO` on asymmetric nested `Minus` composition has been resolved or whether `Replace` fallback remains, and check `agda/` for completed mechanization proofs of categorical associativity/inversion laws.
3. **`tylr` Material Obligations:** Diff `hazelgrove/tylr` `src/core/structure/Oblig.re` against `1543f29f87db20bdd94bc9fa82df5c8142ae73e7` to verify whether the 7-tier `Oblig.Ord.all` severity ranking or `Oblig.Delta.min_choice` cost function changed.
4. **Glamorous Toolkit View Purity:** Check `feenkcom/gtoolkit-inspector` against `46549bc9db9045ea8c429cc37c9ce8babc5fb2fe` for any introduction of read-only/effect-checked `<gtView>` execution guards or weak-reference lifecycle bounds.
5. **Re-run Executable Invariant Checks:** Re-execute a self-contained Python check of `mark_syn`/`eval_live` fill-and-resume commutativity (pure vs. effectful), `ChangeAlgebra.compose`/`invert` endpoint preservation, and `ucheck_add` multi-dimensional compatibility whenever proposing extensions to typed-hole or spreadsheet verification IRs.
