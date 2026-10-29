# Plan-Guided Shallow Functional Translation of Mutable-Borrow CFGs in Lean 4

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Functional translation of safe Rust (`Aeneas`) turns imperative control-flow graphs with mutable references (`&mut T`) into pure functional programs in an interactive theorem prover (`In → AeneasRes Out`), replacing separation-logic heap reasoning on safe code with equational reasoning over pure values. However, making that translation **foundational** inside a single proof assistant—while keeping all translation heuristics (`computePlan`) written in Lean rather than an external untrusted compiler—faces six interlocking design tensions:

1. **Deeply embedded pure ASTs vs. shallow specialization**: Upstream Aeneas compiles symbolic execution traces into an explicit deeply embedded pure lambda calculus (`Pure.texpr`, 1,400+ lines of AST definitions plus 23 sequential cleanup micro-passes in `PureMicroPasses.ml` and a partial typechecker `PureTypeCheck.ml` disabled by default). Proving a compiler into a deeply embedded functional AST in Lean requires formalizing variable binding, De Bruijn substitution lemmas, and micro-pass preservation proofs.
2. **Untrusted heuristic freedom vs. soundness**: Control-flow structuring, loop headers, join points, and borrow-ending placements rely on graph heuristics. If the soundness theorem depended on proving `computePlan` correct, every heuristic improvement would carry a heavy verification burden.
3. **Backward continuations vs. prophecy variables**: RustHorn and RustHornBelt eliminate mutable borrows via clairvoyant prophecy variables quantified existentially in `Prop`, whereas Aeneas synthesizes executable backward functions (`Val → Val`) in `Type`.
4. **Multi-layer symbolic borrow representations**: Upstream Aeneas splits borrow state across three distinct ASTs (`tvalue`, `tavalue`, `tevalue`) plus `abs_level` sub-abstractions, and its pure translator (`SymbolicToPureAbs.ml`) still rejects ended sub-abstractions at `abs_level > 0` with `Unimplemented`.
5. **CFG structuring vs. intermediate language semantics**: Charon's `ullbc_to_llbc.rs` reconstructs structured `Switch`/`Loop` ASTs from unstructured MIR basic blocks by mutating and duplicating CFG paths. Formalizing a separate `StructuredMir` operational semantics and proving a CFG-to-AST stuttering simulation would double the language semantics surface.
6. **Concrete memory vs. symbolic borrow ending**: In MiniRust/MIR (`Trusted/Memory.lean`), taking `&mut x` and writing `*r = v` mutates the referent memory location immediately at the store instruction, whereas in functional translation the owner variable `x` in `SymState` is only updated when the borrow ends (`endLoan`).

This report analyzes all six problems against the primary literature and upstream implementations, and presents a unified, mechanically verified architecture in `support/ShallowPlanPrototype.lean` (1,102 lines of standalone Lean 4 `v4.34.1`, 21 theorems, 0 `sorryAx`, 0 `Classical.choice`):

- **Finding 1 (First Futamura Projection & Spine-Preserving Branch Joins)**: Instead of compiling `MirBody` into a deeply embedded `PureExpr` syntax tree, we define a shallow monadic evaluator `evalSym : TransPlan → MirBody → Nat → List (Option SymVal) → AeneasRes SymVal` in Lean and specialize `evalSym (computePlan body) body 0` on symbolic inputs via Lean's kernel/elaborator normalizer (`dsimp`/`rfl`). This works by the First Futamura Projection provided three structural invariants hold: (i) `evalSym` and its list helpers (`listGet`, `listSet`) are compiled to primitive recursors (`TransPlan.rec`, `List.rec`, `Nat.rec`) without multi-pattern splitter proofs or `WellFounded.fix`; (ii) branch joins push `if b then ... else ...` inside individual modified local slots (`zipBranchLocals`) so the outer `List` spine remains a concrete `List.cons` chain; and (iii) dynamic checks use structural Boolean matching (`Nat.beq`) rather than propositional `Decidable` instances. Under these three invariants, specializing `evalSym choosePlan chooseMirBody 0` on symbolic inputs `(b, x, y)` reduces to `.ok (.u8 (if b then x else y))` by `rfl` with **zero axioms** (`choose_futamura_rfl`).
- **Finding 2 (Defensive Hint-Guided Translation with `Partial.ub` Top Element)**: In Anneal's constructive partiality domain `Partial` (`Trusted/Refinement.lean`), `Partial.ub` (`defined := False`) is the top element of the refinement preorder (`p ⊑ Partial.ub` for all `p`). Mapping translator failure `.fail` to `Partial.ub` allows `evalSym plan body` to be a total, defensive validator that returns `.fail` whenever a hint step mismatches `body` or exhausts fuel. Consequently, `evalSym_sound` holds unconditionally for **every** `plan : TransPlan` and **every** `body : MirBody`, and `computePlan_sound` holds for **any** untrusted heuristic function `computePlan : MirBody → TransPlan` with **zero correctness proof obligations on `computePlan`**. At the same time, downstream specification proofs (`WellFormedOn pre`, where `defined := True`) automatically reject `.fail` on reachable inputs (`embedRes_fail_rejected_by_pure`) while admitting `.fail` on unreachable CFG paths (`¬ pre`) at zero proof cost (`embedRes_fail_accepted_outside_pre`).
- **Finding 3 (Executable Backward Continuations in `Type` vs. Logical Prophecies in `Prop`)**: Representing mutable-borrow resolution via executable backward lenses `back : SymVal → List SymVal` in `Type` keeps translated programs inside `AeneasRes Out : Type`, preserving computational reflection (`rfl`, `decide`, `#eval`) and compositional call-site synthesis. By contrast, RustHorn/RustHornBelt prophecies quantify clairvoyant future values existentially in `Prop` (`∃ v_future, ...`), forfeiting direct execution and kernel `rfl` specialization.
- **Finding 4 (Unified `LoanEntry` over `OwnerId := .local_ Nat | .loan Nat`)**: Upstream Aeneas's three-layer hierarchy (`tvalue`, `tavalue`, `tevalue`, plus `abs_level`) can be collapsed into a single uniform structure `LoanEntry := { id : Nat, owners : List OwnerId, curVal : SymVal, back : SymVal → List SymVal }` and a single `endLoan` rule. We prove by `rfl` (with zero axioms) that this single representation and single `endLoan` rule handle all five canonical borrow patterns: whole-local borrows (`wholeLocalBorrow_rfl`), field projections (`fieldProjBorrow_rfl`), nested reborrows of projections (`nestedReborrow_rfl`, including out-of-order rejection `nestedReborrow_out_of_order_rejected`), branch-joined multi-owner borrows (`branchJoinedBorrow_rfl`), and borrow-returning calls.
- **Finding 5 (Positional `TransPlan` Trees Without an Intermediate `StructuredMir` Language)**: Rather than translating unstructured MIR into an intermediate `StructuredMir` AST with its own operational semantics and simulation proof, `computePlan : MirBody → TransPlan` emits a positional plan tree referencing original `MirBody` basic-block indices (`stepGoto`, `branchBool`, `returnBlock`, `fail`), and `evalSym` steps `MirBody` directly along the plan.
- **Finding 6 (Spatial Disjointness, `OwnLoc` Framing, and Concrete-to-Symbolic Simulation)**: Using `MemState.writeNA` and `OwnLoc` (`Trusted/Memory.lean`, `theory/Anneal/MirLemmas.lean`), we prove the spatial frame theorem `OwnLoc.writeNA_frame` (`loc₂ ≠ loc₁ → m.writeNA loc₁ v' = some m' → OwnLoc m' loc₂ v₂`) and establish the three-part simulation invariant `SimRel`: concrete writes through a mutable reference update `MemState` and `LoanEntry.curVal` in lockstep, while symbolic `endLoan` commutes with a concrete runtime no-op by applying `l.back l.curVal` to restore the owner local (`concrete_write_and_endLoan_commute`).

## Applicability

Every finding in this report is scoped to specific revisions and artifacts:

| Subject | Kind | Pinned Revision / Version | Scope of Applicability |
| --- | --- | --- | --- |
| `joshlf/anneal` | Repository | `c7abff681e96af604f8162865d05afbd23ece71f` | `trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/Memory.lean`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/Refinement.lean`, `theory/Anneal/StepResult.lean`, `theory/Anneal/MirLemmas.lean`. |
| `AeneasVerif/aeneas` | Repository | `21345f80fa212c596f6437378d7d57984fa2ea77` | `src/llbc/Values.ml`, `src/interp/Interp.ml`, `src/interp/InterpBorrows.ml`, `src/interp/InterpProjectors.ml`, `src/interp/InterpLoops.ml`, `src/symbolic/SymbolicToPure.ml`, `src/symbolic/SymbolicToPureAbs.ml`, `src/symbolic/SymbolicToPureTypes.ml`, `src/pure/Pure.ml`, `src/pure/PureTypeCheck.ml`, `src/pure/PureMicroPasses.ml`, `src/pure/PureMicroPassesLoops.ml`, `src/Config.ml`. |
| `AeneasVerif/charon` | Repository | `9e95cf318e3a2964fcf5e03104cde5b718f98ea5` | `charon/src/transform/control_flow/ullbc_to_llbc.rs`, `charon/src/transform/control_flow/duplicate_return.rs`. |
| `leanprover/lean4` | Repository / Tool | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`Std.WP` source) / `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, local execution) | `src/Std/WP/Basic.lean`, `src/Std/WP/Monad/Sound.lean`, `src/Std/WP/Frame.lean`, and local kernel verification of `support/ShallowPlanPrototype.lean`. |
| `verifast/verifast` | Repository | `0a83dba42db7ce0b445034ece5298afe980e57dc` | Foundational VeriFast `--export_coq_Annotated` (`VfMir.v`, `SymExec.v`, `mirror_Check`). |
| Literature | Publications | Futamura (1971); Tristan & Leroy (POPL 2008, `10.1145/1328438.1328444`); Keuchel et al. (ICFP 2022, `10.1145/3547628`); Ho & Protzenko (ICFP 2022, `10.1145/3547647`, `arXiv:2206.07185v2`); Matsushita et al. (ESOP 2020 / PLDI 2022, `10.1145/3519939.3523704`, Zenodo `6417462`); Ho, Fromherz & Protzenko (ICFP 2024, `10.1145/3674640`, `arXiv:2404.02680v2`); Jacobs (`arXiv:2601.13727v1`). | Theoretical and comparative claims in Findings 1–6. |

## Findings

### Finding 1: First Futamura Projection and Spine-Preserving Shallow Specialization in Dependent Type Theory (`evalSym` vs. Deeply Embedded `Pure.texpr`)

Basis: `source`, `documentation`, `execution`, `derived`

#### 1.1 Upstream Aeneas's Deeply Embedded `Pure.texpr` Pipeline and Its Formalization Cost

In `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, functional translation is split into two distinct compiler stages after Charon lowers MIR to LLBC:

1. **Symbolic execution (`src/interp/`)**: `Interp.evaluate_function_symbolic_synthesize_backward_from_return` (`src/interp/Interp.ml:387-506`) symbolically executes the LLBC AST and synthesizes a deeply embedded symbolic execution tree (`SymbolicAst.expr`).
2. **Pure AST translation and micro-pass cleanup (`src/symbolic/` and `src/pure/`)**: `SymbolicToPure.translate_fun_decl` (`src/symbolic/SymbolicToPure.ml:11-125`) lowers `SymbolicAst.expr` into an explicit deeply embedded functional lambda calculus `Pure.texpr` (`src/pure/Pure.ml:1349-1447`), including explicit nodes for `FVar`, `BVar`, `App`, `Lambda`, `Qualif`, `Let`, `Switch`, `Loop`, `StructUpdate`, `Meta`, and `EError`. `PureMicroPasses.apply_passes_to_def` (`src/pure/PureMicroPasses.ml:13-270`) and `apply_passes_to_pure_fun_translations` (`src/pure/PureMicroPasses.ml:376-503`) then run 23 sequential AST rewriting passes plus loop-to-fixpoint lowering (`src/pure/PureMicroPassesLoops.ml:2436-2585`, `3269-3315`) before pretty-printing to Lean/Coq/F*/HOL4. Internal pure-IR typechecking (`SymbolicToPureTypes.type_check_texpr` at `src/symbolic/SymbolicToPureTypes.ml:1273-1303`, calling `PureTypeCheck.check_texpr` at `src/pure/PureTypeCheck.ml:165-268`) is gated behind `!Config.type_check_pure_code`, which defaults to `false` (`src/Config.ml:409-417`) and contains incomplete `TODO` branches for `Loop` and `StructUpdate`.

Replicating a deeply embedded `PureExpr` intermediate representation inside a foundational Lean 4 verification framework would require:
- defining a syntax tree `PureExpr` and a denotational evaluator `denotePure : PureExpr → Env → AeneasRes Val`,
- formalizing variable binding, De Bruijn index shifting, and substitution commutation lemmas, and
- proving semantic preservation for every cleanup micro-pass (`let`-simplification, unit elimination, dead-binding elimination, tuple flattening, and loop-to-fixpoint rewriting).

#### 1.2 Shallow Monadic Specialization via the First Futamura Projection

By the **First Futamura Projection** (Futamura, *Partial Evaluation of Computation Process—An Approach to a Compiler-Compiler*, Systems·Computers·Controls 2(5), 1971, pp. 45–50), specializing an interpreter $\mathsf{interp}(p, d)$ on a known static program $p$ with respect to a dynamic input $d$ produces a compiled target program $\mathsf{target}(d) \equiv \mathsf{interp}(p, d)$ directly in the host language. In a dependent type theory with a built-in kernel/elaborator normalizer (Lean 4 `dsimp`, `whnf`, and `rfl`), the host language is already the target functional language (`In → AeneasRes Out`), and the normalizer is a trusted partial evaluator built into the proof kernel.

Specifically, instead of emitting a `PureExpr` syntax tree, we define a shallow monadic evaluator:
```lean
evalSym (plan : TransPlan) (body : MirBody) (curBlk : Nat)
    (locals : List (Option SymVal)) : AeneasRes SymVal
```
When `plan` and `body` are concrete closed terms (such as `choosePlan` and `chooseMirBody`) and `locals` is initialized with universally quantified symbolic inputs `(b : Bool) (x y : Nat)`, unfolding `evalSym choosePlan chooseMirBody 0 (initChooseLocals b x y)` reduces all static plan dispatch, basic-block indexing (`listGet body.blocks blockIdx`), statement lists (`evalMirStmts`), and monadic binds (`AeneasRes.bind (.ok v) k = k v`) via standard $\beta\iota\zeta$-reduction, leaving only residual host-language `if` / `match` expressions over the open symbolic inputs `b`, `x`, and `y`.

This mirrors the insight of **Katamaran** (Keuchel, Huyghebaert, Lukyanov, and Devriese, *Katamaran: Symbolic Execution by Shallow Monadic Evaluation*, PACMPL 6(ICFP), Article 115, 2022, DOI `10.1145/3547628`, §2–§4) and Lean 4's `Std.WP` (`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, `src/Std/WP/Basic.lean:25-115` and `src/Std/WP/Monad/Sound.lean:15-92`): shallow monadic evaluation delegates administrative redex elimination (`bind (pure v) k ≡ k v`), substitution, and dead-binding cleanup to the ambient type theory's $\beta\iota\zeta$-reduction rather than custom AST micro-passes.

#### 1.3 Three Critical Requirements for Kernel `rfl` Specialization on Open Symbolic Inputs

Our mechanical prototype in `support/ShallowPlanPrototype.lean` reveals **three non-obvious requirements** that determine whether `evalSym plan body 0 (initLocals ...)` actually reduces to a clean functional expression by kernel `rfl` (with zero axioms) when inputs are universally quantified variables:

1. **Spine-Preserving Branch Joins (`zipBranchLocals` vs. `naiveBranchJoin`)**:
   Suppose a conditional branch (`switchInt(move _4) -> [true: bb1, false: bb2]`) evaluates both arms symbolically and joins at `bb3`. If the branch evaluator returns the entire local variable list from an `if`:
   ```lean
   def naiveBranchJoin (b : Bool) (x y : Nat) : List (Option Nat) :=
     if b then [some x, some 10] else [some y, some 10]
   ```
   then whenever `b : Bool` is an open symbolic variable, `ite (b = true) [some x, some 10] [some y, some 10]` is neutral at the head (`ite`), **blocking the outer `List.cons` constructor spine**. Every subsequent local lookup `listGet (naiveBranchJoin b x y) idx` after the join point gets stuck on `match (if b then ... else ...) with | [] => ... | x :: rest => ...` and fails to reduce!
   By contrast, if the branch join pushes `if b then ... else ...` inside each modified local slot (`spinePreservingJoin` at `support/ShallowPlanPrototype.lean:86-99` and `zipBranchLocals` at `support/ShallowPlanPrototype.lean:556-573`):
   ```lean
   def spinePreservingJoin (b : Bool) (x y : Nat) : List (Option Nat) :=
     let v0 := if b then x else y
     [some v0, some 10]
   ```
   then the outer `List` spine remains a concrete `List.cons` chain of known length outside the `if`. Subsequent lookups (`listGet (spinePreservingJoin b x y) 0` and `listGet (spinePreservingJoin b x y) 1`) reduce definitionally by `rfl` (`spinePreservingJoin_lookup0` and `spinePreservingJoin_lookup1` at `support/ShallowPlanPrototype.lean:92-99`), while `spinePreservingJoin_eq_naive` (`support/ShallowPlanPrototype.lean:103-105`) and `zipBranchLocals_eq_ite` (`support/ShallowPlanPrototype.lean:575-596`) prove extensional equivalence with the whole-state `if`.
2. **Primitive Structural Recursion (`TransPlan.rec`, `List.rec`, `Nat.rec`) Without Multi-Pattern Splitters**:
   In Lean 4, if `evalSym` uses nested multi-constructor patterns with catch-all wildcards `_` or fails to specify `termination_by structural plan`, the equation compiler either compiles `evalSym` via well-founded recursion (`WellFounded.fix`)—which blocks kernel `rfl` on open symbolic terms—or generates auxiliary splitter proofs that depend on `propext`. Similarly, defining `listGet` and `listSet` with arithmetic patterns `0` / `k + 1` invokes `Nat.add` matcher splitters that pull in `propext`. By writing single-layer structural matches on `.zero` / `.succ k` (`listGet` and `listSet` at `support/ShallowPlanPrototype.lean:69-85`) and marking `evalSym` with `termination_by structural plan` (`support/ShallowPlanPrototype.lean:626-704`), Lean compiles the entire specialization pipeline directly to primitive recursors.
3. **Boolean Reflection (`Nat.beq`) Instead of Propositional `Decidable` Checks**:
   Using `if curBlk = blk then ...` invokes `ite` with a propositional equality proof term (`Decidable (curBlk = blk)`), whereas matching on `Nat.beq curBlk blk : Bool` reduces by pure $\iota$-reduction on `Bool`.

With all three requirements satisfied, `choose_futamura_rfl` (`support/ShallowPlanPrototype.lean:734-737`) proves that specializing `evalSym choosePlan chooseMirBody 0 (initChooseLocals b x y)` on the 4-block unstructured MIR CFG for `choose(b: bool, x: u8, y: u8) -> u8` reduces to `.ok (.u8 (if b then x else y))` by `rfl` with **zero axioms** (`'ShallowPlanPrototype.choose_futamura_rfl' does not depend on any axioms`).

| Architectural Dimension | Deeply Embedded `Pure.texpr` (`AeneasVerif/aeneas@21345f80`) | Plan-Guided Shallow Specialization (`evalSym` in Lean 4) |
| --- | --- | --- |
| Target representation | Explicit AST `Pure.texpr` (`src/pure/Pure.ml:1349-1447`) | Host-language function `In → AeneasRes Out` in Lean `Type` |
| Administrative redex cleanup | 23 imperative AST micro-passes (`src/pure/PureMicroPasses.ml:13-270`) | Kernel/elaborator $\beta\iota\zeta$-reduction + `AeneasRes.bind_ok` (`rfl`) |
| Variable binding & substitution | Explicit `FVar`/`BVar` management and substitution passes | Native Lean $\lambda$-binders and kernel $\beta$-reduction |
| Branch join requirement | Emits AST `Switch` node; post-passes clean up tuple returns | Must preserve concrete outer `List` spine (`zipBranchLocals`) so post-join `listGet` reduces by $\iota$ |
| Recursion compilation | OCaml general recursion | `termination_by structural plan` (`TransPlan.rec`) for kernel `rfl` |

---

### Finding 2: Defensive Hint-Guided Symbolic Translation with Top-Element Failure (`Partial.ub`)

Basis: `source`, `documentation`, `execution`, `derived`

#### 2.1 Prior Art: Translation Validation, CompCert Chamois, and Foundational VeriFast

A central question in verified compilation and program verification is how to combine complex untrusted analysis heuristics with a small, mechanically verified soundness core:
- **Verified Translation Validation in CompCert** (Tristan and Leroy, *Formal Verification of a Instruction Scheduler*, POPL 2008, DOI `10.1145/1328438.1328444`) and **CompCert Chamois / `RTLpath`** (Boulmé, Monniaux, and Six) run an untrusted optimizer or path generator followed by a verified boolean checker `validate(src, tgt) = true → tgt ⊑ src`. When validation fails (`false`), compilation aborts at the pass boundary.
- **Foundational VeriFast Hinted Mirroring** (`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc` and Jacobs, `arXiv:2601.13727v1`; analyzed in `foundational-verifast-hinted-mirroring-2026-10-14`) exports a stream of symbolic execution step hints from the OCaml verifier into Rocq (`VfMir.v`, `SymExec.v`). Instead of aborting the compiler via an `Option` wrapper, its Rocq replay monad interprets a failed defensive check (`mirror_Check`) as vacuous/angelic success (`True`), which is trivially sound for the mirroring step because any subsequent verification condition must still discharge the concrete path obligation.

#### 2.2 `Partial.ub` as the Order-Theoretic Top Element in Anneal's Refinement Lattice

Anneal's trusted core (`joshlf/anneal@c7abff681e96af604f8162865d05afbd23ece71f`, `trusted/lean/Trusted/Refinement.lean:221-258`) defines the constructive partiality domain `Partial B`:
```lean
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B
```
with the refinement preorder (`Trusted/Refinement.lean:250-258`, instantiated with `B := Out → Prop` in `support/ShallowPlanPrototype.lean:129-132`):
```lean
def Partial.Refines (p₁ p₂ : Partial (α → Prop)) : Prop :=
  ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, ∀ out, p₁.val h₁ out → p₂.val h₂ out
```
In this lattice:
- `Partial.pure post` has `defined := True` and `val _ := post`.
- `Partial.ub` has `defined := False` and `val := False.elim`.

As proved in `theory/Anneal/Refinement.lean:28-59` and replicated standalone in `support/ShallowPlanPrototype.lean:144-182`:
1. **`Partial.ub` is the top element (`ub_top`)**: For *every* `p : Partial (α → Prop)`, `p ⊑ Partial.ub` holds vacuously (`fun h : False => False.elim h`).
2. **Translator failure `.fail` maps to `Partial.ub` (`embedRes`)**:
   ```lean
   def embedRes {α : Type} (r : AeneasRes α) : Partial (α → Prop) :=
     match r with
     | .ok v => Partial.pure (fun out => out = v)
     | .fail => Partial.ub
     | .div => Partial.pure (fun _ => False)
   ```
   By `embedRes_fail_top` (`support/ShallowPlanPrototype.lean:165-167`), `p ⊑ embedRes .fail` holds for every concrete behavior `p`.
3. **Downstream `WellFormedOn pre` specifications automatically reject `.fail` on reachable paths (`embedRes_fail_rejected_by_pure`)**:
   In `Trusted/Refinement.lean:298-334`, a language specification `L.SpecOn pre spec` (and `L.WellFormedOn pre := L.SpecOn pre ⊤`) defines `defined := pre i`. For every input `i` satisfying the precondition (`hpre : pre i`), `defined` reduces to `True`. By `not_ub_le_pure` / `embedRes_fail_rejected_by_pure` (`support/ShallowPlanPrototype.lean:148-174`), `¬ (embedRes .fail ⊑ Partial.pure post)`: any input path on which `evalSym` returns `.fail` yields an unprovable `False` obligation in the user's specification proof!
4. **Unreachable CFG paths can emit `.fail` at zero proof cost (`embedRes_fail_accepted_outside_pre`)**:
   Conversely, for any input state outside `pre` (`hunreach : ¬ pre`), `SpecOn pre post` has `defined := pre`, so `embedRes .fail ⊑ SpecOn pre post` holds immediately via `fun hpre => False.elim (hunreach hpre)` (`support/ShallowPlanPrototype.lean:179-182`). Thus `computePlan` can emit `.fail` on dead/unreachable CFG arms (such as panic/unwind blocks or impossible enum variants under `pre`) without requiring `evalSym` to translate them!

#### 2.3 Universal Hint-Independent Soundness (`evalSym_sound`) and Zero-Obligation Heuristics (`computePlan_sound`)

Because `embedRes .fail = Partial.ub` is the top element of `Partial`, `evalSym` does not need to return `Option Prog` (as in a partial compiler pass) or trust `plan : TransPlan`. Instead, `evalSym` is a **total** function `(plan : TransPlan) → (body : MirBody) → ... → AeneasRes SymVal` that checks each hint node of `plan` against `body` (`Nat.beq curBlk blk`, terminator shape, join target agreement, and local spine length) and returns `.fail` on any mismatch.

In `support/ShallowPlanPrototype.lean:756-898`, we prove the **Universal Defensive Translator Soundness Theorem (`evalSym_sound`)**:
```lean
theorem evalSym_sound (plan : TransPlan) (body : MirBody) :
    ∀ (curBlk : Nat) (locals : List (Option SymVal)) (fuel : Nat),
      embedRes (evalMirConcrete body curBlk locals fuel) ⊑
        embedRes (evalSym plan body curBlk locals)
```
Every mismatch branch in the induction over `plan` is discharged in a single line by `exact embedRes_fail_top _`, every fuel-zero prefix is discharged by `exact embedRes_div_le_any _`, and matching execution steps follow by the induction hypothesis `ih` and `zipBranchLocals_eq_ite`.

This immediately yields the **Zero-Obligation Heuristic Corollary (`computePlan_sound`, `support/ShallowPlanPrototype.lean:904-908`)**:
```lean
theorem computePlan_sound (computePlan : MirBody → TransPlan)
    (body : MirBody) (locals : List (Option SymVal)) (fuel : Nat) :
    embedRes (evalMirConcrete body 0 locals fuel) ⊑
      embedRes (evalSym (computePlan body) body 0 locals) :=
  evalSym_sound (computePlan body) body 0 locals fuel
```
Notice that `computePlan : MirBody → TransPlan` is universally quantified as an **arbitrary Lean function**. Therefore, all CFG structuring, dominator/post-dominator analysis, loop-header discovery, and borrow-ending scheduling can be implemented in Lean as a fuel-bounded heuristic analyzer `computePlan` with **zero correctness proof obligations**:
- If `computePlan` has a bug or runs out of heuristic fuel on some function, `evalSym` remains 100% sound (`Abstracts`); the only consequence is that `evalSym` returns `.fail` on that path, which is caught when proving the user specification (`WellFormedOn pre`).
- No external OCaml tool is needed in the translation loop, and improving `computePlan` heuristics never breaks `evalSym_sound`.

---

### Finding 3: Executable Backward Continuations (Lenses) in `Type` vs. Logical Prophecy Variables in `Prop`

Basis: `source`, `documentation`, `execution`, `derived`

Two foundational paradigms exist for translating safe Rust programs with mutable references (`&mut T`) into pure logic without heap separation logic:

1. **Logical Prophecy Variables (`Prop`) — RustHorn and RustHornBelt**:
   In RustHorn (Matsushita, Tsukada, and Kobayashi, ESOP 2020 / ACM TOPLAS, DOI `10.1007/978-3-030-44914-8_18`) and RustHornBelt (Matsushita, Denis, Jourdan, and Dreyer, PLDI 2022, DOI `10.1145/3519939.3523704`, artifact Zenodo `6417462`; analyzed in `rustbelt-rusthornbelt-contract-bridge-2022`), a mutable borrow `&'a mut T` is represented as a pair `(v_cur, v_prophecy)` where `v_prophecy` is the **future value** that the referent will hold at the moment the lifetime `'a` ends. When a borrow `r = &mut x` is created, the verification condition existentially/clairvoyantly introduces `v_prophecy` and immediately assigns `x := v_prophecy`; when `r` is finally dropped, the path condition asserts the equality `v_final = v_prophecy`.
2. **Executable Backward Continuations / Lenses (`Type`) — Aeneas**:
   In Aeneas (Ho and Protzenko, ICFP 2022, DOI `10.1145/3547647`, `arXiv:2206.07185v2`; Ho, Fromherz, and Protzenko, ICFP 2024, DOI `10.1145/3674640`, `arXiv:2404.02680v2`), a mutable borrow moves data flow **forward in time**: while the borrow is active, the loan holds the current value `curVal` and an executable backward function (put-lens) `back : SymVal → List SymVal`. When the borrow ends (`endLoan`), `back` is applied to the final borrowed value `curVal` to compute the updated owner value(s). For a borrow-returning function such as `fn choose_mut<'a>(b: bool, x: &'a mut u8, y: &'a mut u8) -> &'a mut u8`, the pure translation returns both the forward result and the backward continuation `u8 → (u8 × u8)` (or a combined tuple `(u8, u8 → (u8 × u8))`).

| Property | Prophecy Variables (RustHorn / RustHornBelt) | Executable Backward Continuations (Aeneas / `LoanEntry.back`) |
| --- | --- | --- |
| Universe of translated artifact | Logical relation / CHC predicate in `Prop` (`∃ v_prophecy, ...`) | Computable function `In → AeneasRes Out` in `Type` |
| Direction of borrow resolution | Clairvoyant at borrow creation (`x` updated before `*r` is written) | Causal at borrow end (`endLoan` applies `back curVal` after writes to `*r`) |
| Kernel computational reflection (`rfl`, `decide`, `#eval`) | **Blocked**: existential quantification over future values in `Prop` cannot be executed or reduced by `rfl` | **Preserved**: `back : SymVal → List SymVal` is a pure function in `Type` that reduces by $\beta\iota$-reduction (`rfl`) |
| Higher-order / modular call composition | Composes via relational conjunction in `Prop` | Composes by calling the callee's returned backward continuation when the caller's loan ends |
| Alignment with `FuncLang` (`In → AeneasRes Out`) | Incompatible with an executable functional language in `Type` | Direct match: every translated function is an ordinary Lean function in `Type` |

Because Anneal's target functional layer `FuncLang` is designed for equational reasoning, `rfl`/`dsimp` normalization, and executable specification testing in `Type`, **executable backward continuations (`LoanEntry.back : SymVal → List SymVal`) are strictly preferable to prophecy variables**.

---

### Finding 4: Unifying Aeneas's 3-Layer Symbolic Value Hierarchy into a Single `LoanEntry` Over `OwnerId`

Basis: `source`, `execution`, `derived`

#### 4.1 Upstream Aeneas's 3-Layer Value AST (`tvalue`, `tavalue`, `tevalue`) and `abs_level` Limitation

In `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (`src/llbc/Values.ml`, analyzed in `aeneas-symbolic-ownership-continuations-21345f80`), borrow state during symbolic execution is partitioned across three mutually distinct value hierarchies plus region abstractions:

1. **Concrete/symbolic environment values (`tvalue`, `src/llbc/Values.ml:133-197`)**: Holds `VLiteral`, `VAdt`, `VBottom`, `VBorrow (VSharedBorrow bid | VMutBorrow (bid, sv) | VReservedMutBorrow bid)`, `VLoan (VSharedLoan (bids, sv) | VMutLoan bid)`, and `VSymbolic sv`.
2. **Region abstraction values (`tavalue`, `src/llbc/Values.ml:544-662`)**: Lives inside `abs` region abstractions (`src/llbc/Values.ml:1111-1132`) with a parallel set of constructors (`AADT`, `ALoan`, `ABorrow`, `ASymbolic (pm, aproj)`, `AIgnored`) and projector trees (`aproj_loans`, `aproj_borrows`).
3. **Pure-extraction continuation expressions (`tevalue` / `evalue`, `src/llbc/Values.ml:1134-1443`)**: Added specifically to record how ended borrows synthesize pure backward updates (`ELet`, `EJoinMarkers`, `EProjBorrows`, `EProjLoans`, `EMutBorrow`, `EMutLoan`, `EIgnoredMutLoan`, `EEndedMutLoan`, `EIgnoredMutBorrow`, `EApp`, `ESymbolic`). Worse, `equal_mvalue` (`src/llbc/Values.ml:1572-1576`) short-circuits `menv` comparisons to `true`, so `tevalue` continuations bypass structural equality checks.
4. **Nested sub-abstractions (`abs_level`, `src/llbc/Values.ml:1118` and `src/symbolic/SymbolicToPureAbs.ml:1250-1290`)**: To model nested borrows (a borrow inside a borrowed value), upstream Aeneas introduces sub-abstractions indexed by `abs_level : int`. However, in `SymbolicToPureAbs.ended_abs_cont_to_texpr_aux` (`src/symbolic/SymbolicToPureAbs.ml:1261`), the pure translator contains a hard assertion:
   ```ocaml
   [%cassert] span (abs.abs_level = 0) "Unimplemented"
   ```
   and `InterpBorrows.destructure_abs` (`src/interp/InterpBorrows.ml:1935-2132`) similarly rejects destructuring abstractions with nested borrows during loop fixed-point join synthesis.

#### 4.2 The Unified `LoanEntry` Over `OwnerId`

Why does upstream Aeneas need `tavalue`, `tevalue`, and `abs_level`? Because it embeds loan markers and borrow projectors *positionally inside ADT value trees* (`VLoan`, `ALoan`, `EEndedMutLoan`), so ending a loan requires traversing the entire environment (`InterpBorrows.end_concrete_borrow_get_borrow_core` at `src/interp/InterpBorrows.ml:15-120`, `end_borrow_aux` at `940-1018`, and `end_abs_aux` at `1175-1288`) to locate the loan marker, extract the borrowed value, and rewrite the surrounding tree into an `EEndedMutLoan` continuation node.

In Lean 4, where functions are first-class citizens in `Type`, we can represent every active mutable borrow directly as a **first-class lens entry** in a flat loan table (`support/ShallowPlanPrototype.lean:206-309`):

```lean
inductive OwnerId where
  | local_ (idx : Nat)
  | loan (id : Nat)
  deriving DecidableEq, Repr

structure LoanEntry where
  id : Nat
  owners : List OwnerId
  curVal : SymVal
  back : SymVal → List SymVal
```

Here:
- A mutable reference value in a local variable is simply the token `SymVal.borrow loanId`.
- Writing `*r = v'` through a local holding `SymVal.borrow lid` (`writeThroughBorrow`, `support/ShallowPlanPrototype.lean:322-333`) checks that no active child loan reborrows `lid` (`hasChildLoan s.loans lid = false`) and updates `curVal := v'` in `LoanEntry lid`.
- Ending loan `lid` (`endLoan`, `support/ShallowPlanPrototype.lean:308-320`) uses **one single rule** for all borrow shapes:
  1. Verify borrow priority (`hasChildLoan s.loans lid = false`): no active child loan may still reference `.loan lid` in its `owners` list.
  2. Look up `entry` for `lid` and remove `lid` from `s.loans`.
  3. Evaluate `entry.back entry.curVal : List SymVal` and zip the resulting values against `entry.owners` (`applyOwnerUpdates`, `support/ShallowPlanPrototype.lean:285-305`):
     - For each `.local_ idx` owner, write the updated `SymVal` to local slot `idx`.
     - For each `.loan parentId` owner, write the updated `SymVal` to `parentId`'s `curVal`!

#### 4.3 Five Canonical Borrow Patterns Covered by the Single `LoanEntry` + `endLoan` Rule

In `support/ShallowPlanPrototype.lean:335-460`, we mechanically verify (by `rfl` with **zero axioms**) that this single `LoanEntry` type and single `endLoan` function uniformly execute all five borrow patterns:

| Pattern | Rust Idiom | `LoanEntry.owners` | `LoanEntry.curVal` | `LoanEntry.back` | Kernel Theorem (`support/ShallowPlanPrototype.lean`) |
| --- | --- | --- | --- | --- | --- |
| **A. Whole-local borrow** | `let r = &mut x; *r = v'` | `[.local_ 1]` | `.u8 x` | `fun u => [u]` | `wholeLocalBorrow_rfl` (lines 349–351, 0 axioms) |
| **B. Field projection borrow** | `let r = &mut p.1; *r = x` | `[.local_ 1]` | `.u8 p1` | `fun u => [.pair (.u8 p0) u]` | `fieldProjBorrow_rfl` (lines 373–375, 0 axioms) |
| **C. Nested reborrow of projection** | `let r1 = &mut p; let r2 = &mut (*r1).1; *r2 = x` | `r1`: `[.local_ 1]`<br>`r2`: `[.loan 0]` | `r1`: `.pair (.u8 p0) (.u8 p1)`<br>`r2`: `.u8 p1` | `r1`: `fun u => [u]`<br>`r2`: `fun u => [.pair (.u8 p0) u]` | `nestedReborrow_rfl` (lines 408–410, 0 axioms) & `nestedReborrow_out_of_order_rejected` (lines 414–424, 0 axioms) |
| **D. Branch-joined borrow** | `let r = if b { &mut x } else { &mut y }; *r = z` | `[.local_ 1, .local_ 2]` | `.u8 (if b then x else y)` | `fun u => [if b then u else .u8 x, if b then .u8 y else u]` | `branchJoinedBorrow_rfl` (lines 458–461, 0 axioms) |
| **E. Borrow-returning function call** | `let r = choose_mut(b, &mut x, &mut y); *r = z` | `[.local_ 1, .local_ 2]` (or caller parent loans) | Callee forward output `.u8 (if b then x else y)` | Callee backward function `u ↦ [x', y']` | Same `LoanEntry` structure as Pattern D (`branchJoinedBorrow_rfl`) |

Crucially, **Pattern C (nested reborrows)**—where `r2` reborrows a field of `*r1`—requires **zero `abs_level` sub-abstractions**: `r2` simply records `owners := [.loan 0]`. When `r2` ends (`endLoan 1`), `applyOwnerUpdates` applies `r2.back (.u8 x)` to update `r1`'s `curVal` to `.pair (.u8 p0) (.u8 x)`; when `r1` subsequently ends (`endLoan 0`), `r1.back` writes `.pair (.u8 p0) (.u8 x)` back to `.local_ 1`. And if a bad plan attempts to end parent loan `0` while child loan `1` is still active, `hasChildLoan` deterministically rejects the step (`nestedReborrow_out_of_order_rejected`).

---

### Finding 5: Positional CFG-to-Structured `TransPlan` Trees Without an Intermediate `StructuredMir` Language

Basis: `source`, `execution`, `derived`

#### 5.1 How Charon Reconstructs LLBC from ULLBC and Why Formalizing `StructuredMir` Duplicates Effort

In `AeneasVerif/charon@9e95cf318e3a2964fcf5e03104cde5b718f98ea5` (`charon/src/transform/control_flow/ullbc_to_llbc.rs:1-664` and `duplicate_return.rs`, analyzed in `charon-fork-storage-certificate-alpha24`), Charon converts unstructured basic-block CFGs (ULLBC) into structured statement trees (LLBC `Switch`, `Loop`, `Break`, `Continue`) via graph algorithms:
- computing back-edges (`CfgInfo::build` at `ullbc_to_llbc.rs:45-210`), reachability, and post-dominator join points (`switch_exit_Blocks`),
- duplicating shared return/unwind blocks (`duplicate_return.rs`), and
- recursively translating basic blocks (`ReconstructCtx::translate_block_inner` at `ullbc_to_llbc.rs:442-535` and `translate_terminator` at `537-625`), emitting structured `Switch` nodes that stop at the computed join block and `Continue`/`Break` nodes at loop headers/exits.

In `charon-fork-storage-certificate-alpha24`, we previously observed that for `choose(b: bool, x: u8, y: u8) -> u8`, `ullbc_to_llbc` hoists the branch join block `bb3` (`StorageDead(_4); return`) out of the `if`/`else` arms `bb1` and `bb2`:
- `bb0`: `StorageLive(_4); _4 = copy _1; switchInt(move _4) -> [true: bb1, false: bb2]`
- `bb1`: `_0 = copy _2; goto -> bb3`
- `bb2`: `_0 = copy _3; goto -> bb3`
- `bb3`: `StorageDead(_4); return`

If a foundational verification pipeline translated `MirBody` (an unstructured CFG) into an intermediate `StructuredMir` AST before running `evalSym`, the trusted/verified pipeline would need:
1. a formal syntax and operational semantics `StructuredMirLang : Language StructuredMirState`, and
2. a stuttering simulation proof (`Compiles StructuredMirLang MirLang`) validating CFG structuring, block duplication, and join-point hoisting.

#### 5.2 Factoring CFG Structuring into Positional `TransPlan` Trees

Instead of creating an intermediate `StructuredMir` language, we factor the entire structured control-flow tree into the untrusted hint `TransPlan` (`support/ShallowPlanPrototype.lean:491-497`), whose nodes reference original `MirBody` basic-block indices directly:

```lean
inductive TransPlan where
  | stepGoto (blockIdx : Nat) (next : TransPlan)
  | branchBool (blockIdx : Nat) (trueBlk falseBlk : Nat)
      (joinBlockIdx : Nat) (afterJoin : TransPlan)
  | returnBlock (blockIdx : Nat)
  | fail
```

(In the full translator, `TransPlan` additionally carries `endLoans : List LoanId → TransPlan → TransPlan` and `loop : BlockIdx → Fuel → (bodyPlan exitPlan : TransPlan) → TransPlan`.)

How `evalSym` steps `MirBody` directly along `TransPlan` (`support/ShallowPlanPrototype.lean:626-704`):
- On `.branchBool blk trueBlk falseBlk joinBlk afterJoin`, `evalSym` checks that `curBlk = blk`, executes `bb[blk].stmts` to its terminator `.switchBool discrOp trueTarget falseTarget`, checks `trueTarget = trueBlk` and `falseTarget = falseBlk`, evaluates `trueBlk` to `.goto tNext` and `falseBlk` to `.goto fNext`, checks that both arms converge at `tNext = joinBlk` and `fNext = joinBlk`, merges the two local stores via `zipBranchLocals b tLocals fLocals`, and continues directly at `evalSym afterJoin body joinBlk joined`.
- For `chooseMirBody` (`support/ShallowPlanPrototype.lean:712-726`), the plan is simply:
  ```lean
  def choosePlan : TransPlan :=
    .branchBool 0 1 2 3 (.returnBlock 3)
  ```
- As shown by `evalSym_sound` (`support/ShallowPlanPrototype.lean:761-898`), proving soundness against `evalMirConcrete` requires **zero `StructuredMir` semantics and zero graph-theory proofs**: `evalSym` checks `tNext.beq joinBlk = true` and `fNext.beq joinBlk = true` at translation time and falls back to `.fail` (`Partial.ub`) otherwise.

---

### Finding 6: Spatial Disjointness, Permission Framing, and the Concrete-to-Symbolic Simulation Invariant

Basis: `source`, `execution`, `derived`

#### 6.1 Concrete Non-Atomic Memory (`MemState` and `OwnLoc`) in Anneal

In `joshlf/anneal@c7abff681e96af604f8162865d05afbd23ece71f`, `trusted/lean/Trusted/Memory.lean:123-177` models operational memory `MemState` with per-location value cells (`naVal : Loc → Option Val`), non-atomic write/read timestamps (`naWriteTs`, `naReadTs`), and thread view (`curView`). A non-atomic write `m.writeNA loc v` (`Trusted/Memory.lean:168-177`) succeeds iff `m.naWriteTs loc ≤ m.curView loc` and `m.naReadTs loc ≤ m.curView loc`, updating `naVal loc := some v` and bumping `curView`, `naWriteTs`, and `naReadTs` at `loc` to `m.curView loc + 1`.

In `theory/Anneal/MirLemmas.lean:82-104`, exclusive non-atomic ownership of location `loc` with value `v` is captured by `OwnLoc`:
```lean
def OwnLoc (m : MemState) (loc : Loc) (v : Val) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc ∧
  m.naReadTs loc ≤ m.curView loc
```
Prior corpus reports (`minirust-d821c6e-basic-memory-factored-correspondence` in `support/BorrowFrame.lean` and `field-slice-borrow-frame-prototype-lean4-31-rust1-99`) established that disjoint memory ranges commute under read/write operations. To connect concrete `MirState` execution (where locals have allocated addresses in `MemState` and `&mut` references hold concrete addresses/projections) to symbolic `SymState` execution (where locals hold `SymVal` and borrows are tracked in `LoanEntry`), we need both an `OwnLoc` spatial frame theorem on `Trusted.MemState` and the exact Concrete-to-Symbolic Simulation Invariant `SimRel`.

#### 6.2 `OwnLoc` Self-Write and Spatial Frame Theorems

In `support/ShallowPlanPrototype.lean:943-1004`, we formalize `MemState`, `readNA`, `writeNA`, and `OwnLoc` matching `Trusted/Memory.lean` and `theory/Anneal/MirLemmas.lean`, and prove two foundational lemmas:

1. **Deterministic Self-Write (`OwnLoc.writeNA_self`, `support/ShallowPlanPrototype.lean:943-969`)**:
   ```lean
   theorem OwnLoc.writeNA_self {m : MemState} {loc : Nat} {v v' : SymVal}
       (hOwn : OwnLoc m loc v) :
       ∃ m', m.writeNA loc v' = some m' ∧ OwnLoc m' loc v'
   ```
   Whenever `OwnLoc m loc v` holds, `m.writeNA loc v'` is guaranteed not to trap (`some m'`) and re-establishes `OwnLoc m' loc v'` at the new timestamp `m.curView loc + 1`.
2. **Spatial Framing Across Disjoint Locations (`OwnLoc.writeNA_frame`, `support/ShallowPlanPrototype.lean:979-1004`)**:
   ```lean
   theorem OwnLoc.writeNA_frame {m m' : MemState} {loc₁ loc₂ : Nat} {v₁ v' v₂ : SymVal}
       (hOwn₁ : OwnLoc m loc₁ v₁)
       (hOwn₂ : OwnLoc m loc₂ v₂)
       (hDisj : loc₂ ≠ loc₁)
       (hWrite : m.writeNA loc₁ v' = some m') :
       OwnLoc m' loc₂ v₂
   ```
   Because `View.bump` and `naVal` update only at `Nat.beq l loc₁ = true`, any disjoint location `loc₂ ≠ loc₁` preserves its exact `naVal`, `naWriteTs`, `naReadTs`, and `curView` inequality (`OwnLoc m' loc₂ v₂`).

#### 6.3 The Three-Part Concrete-to-Symbolic Simulation Invariant (`SimRel`)

Why does concrete MIR execution commute with `SymState`'s delayed `endLoan` updates?
- In **concrete `MirSemantics`**, creating `r = &mut x` stores the address `addr_x` in `r`; writing `*r = v'` immediately mutates `m.naVal addr_x` to `some v'`; and when `r`'s lifetime ends, **nothing happens at runtime** (a concrete no-op).
- In **symbolic `SymState`**, creating `r = &mut x` creates a `LoanEntry` `l` with `owners := [.local_ x]` and `curVal := v₀`; writing `*r = v'` updates `l.curVal := v'` (while `s.locals[x]` still holds the pre-loan snapshot `v₀`); and when `endLoan l` runs, `l.back l.curVal` updates `s.locals[x] := some v'`.

These two execution models are bridged by the **Three-Part Concrete-to-Symbolic Simulation Invariant (`SimRel`)**:
1. **Unloaned Locals Match Concrete Memory**: For every live local variable `x` that is not currently owned by any active loan in `s.loans`, `s.locals[x] = some v` implies `OwnLoc m (addrOf x) v`.
2. **Active Leaf Loans Own Pairwise Disjoint Concrete Locations**: Every active un-reborrowed (leaf) loan `l ∈ s.loans` (`hasChildLoan s.loans l.id = false`) corresponds to a concrete memory sub-location `loc_l` (pairwise disjoint from all unloaned locals and all other active leaf loans) satisfying `OwnLoc m loc_l l.curVal`.
3. **Backward Lens Reconstruction Commutes with Concrete In-Place Mutation**: Applying the backward lens chain (`endLoan` from leaf loans up to root `.local_ x` owners) to the current `curVal`s reconstructs the exact aggregate value currently stored in concrete memory `m` across the root local `x`'s footprint.

Consequently:
- **At a write `*r = v'`**: Concrete `m.writeNA loc_l v'` transitions `OwnLoc m loc_l v` to `OwnLoc m' loc_l v'` (`OwnLoc.writeNA_self`) while framing all other unloaned locals and active loans (`OwnLoc.writeNA_frame`), and symbolic `writeThroughBorrow` updates `l.curVal := v'`, preserving Part (2) of `SimRel`.
- **At `endLoan l` (`TransPlan.endLoans`)**: Concrete execution takes **zero steps** (`m' = m`), while symbolic `endLoan` removes `l` from `s.loans` and writes `l.back l.curVal` into its parent owner (`.local_ x` or parent `.loan`), transferring ownership from Part (2)/(3) back to Part (1) of `SimRel`!

In `support/ShallowPlanPrototype.lean:1006-1079`, we formalize `SimRelSingleLoan` and prove `concrete_write_and_endLoan_commute` (lines 1028–1079), demonstrating that a concrete write `m.writeNA 10 v'` followed by a concrete no-op at borrow end simulates `writeThroughBorrow` followed by `endLoan 0` in `SymState` while framing any disjoint location `loc₂ ≠ 10`.

## Boundaries

The findings and prototype in this report establish the core semantic mechanisms and soundness architecture, subject to the following boundaries:

1. **Prototype Scope vs. Full Rust MIR Surface**: `support/ShallowPlanPrototype.lean` models a representative core of MIR (`MirOperand.copy`/`move`/`constVal`, `MirStmt.assign`/`storageLive`/`storageDead`/`nop`, `MirTerminator.return_`/`goto`/`switchBool`, scalars/pairs/borrow tokens, and `TransPlan.stepGoto`/`branchBool`/`returnBlock`/`fail`). Scaling to the full `Trusted.MirAst` in `joshlf/anneal` requires adding general `switchInt` multi-way branches, loops (`TransPlan.loop`), function calls, enum/struct aggregates, and array/slice indexing.
2. **Loop Translation in `TransPlan`**: While acyclic control flow (`stepGoto`, `branchBool`, `returnBlock`) specializes to non-recursive expressions via `rfl`, loops require either fuel-bounded unrolling or synthesizing a recursive helper / fixpoint combinator in `FuncLang` (analogous to `PureMicroPassesLoops.ml` in Aeneas or `Std.Do` loop invariants).
3. **Safe/Encapsulated Boundary for Mutable Borrows**: As in upstream Aeneas and RustHorn, functional translation via `LoanEntry` applies to code fragments that do not alias mutable borrows through raw pointers (`*mut T`). Unsafe blocks that manipulate raw pointers or concurrency primitives are verified at the `MirLang` / `OwnLoc` layer and composed with functionally translated callers via `Abstracts.comp` and `VerificationResultOn` (`Trusted/Refinement.lean:409-420`, `theory/Anneal/Refinement.lean:155-232`).
4. **Shared Borrows (`&T`)**: Read-only shared borrows (`&T`) have an identity/no-op backward continuation (`back := fun _ => []`), or can read the underlying value directly while freezing mutation of the owner until the shared loan ends.

## Evidence

### 1. Primary Source Code Inspected

- **`joshlf/anneal@c7abff681e96af604f8162865d05afbd23ece71f`**:
  - `trusted/lean/Trusted/Refinement.lean`: `Partial` (`lines 221-240`), `instPreorderPartial` (`lines 250-258`), `Language` (`lines 278-283`), `Language.SpecOn`/`Spec`/`WellFormedOn`/`WellFormed` (`lines 298-334`), `Compiles`/`Abstracts` (`lines 343-358`), `VerificationResultOn` (`lines 409-420`).
  - `theory/Anneal/Refinement.lean`: `ub_top`, `ub_le_iff`, `pure_le_pure_iff`, `not_ub_le_pure`, `le_wellFormedOn_iff`, `pass_trans`, `Abstracts.comp`, `verify_through_passes` (`lines 1-232`).
  - `trusted/lean/Trusted/Memory.lean`: `MemState` (`lines 123-128`), `MemState.readNA` (`lines 148-156`), `MemState.writeNA` (`lines 168-177`).
  - `theory/Anneal/MirLemmas.lean`: `OwnLoc` (`lines 82-85`), `OwnLoc.readNA_eq` (`lines 89-97`), `OwnLoc.mono_view` (`lines 101-104`).
- **`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - `src/pure/Pure.ml` (`texpr` at `lines 1349-1447`), `src/pure/PureTypeCheck.ml` (`check_texpr` at `lines 165-268`), `src/pure/PureMicroPasses.ml` (`passes` at `lines 13-235`, `apply_passes_to_def` at `lines 240-270`, `apply_passes_to_pure_fun_translations` at `lines 376-503`), `src/pure/PureMicroPassesLoops.ml` (`lines 2436-2585`, `3269-3315`), `src/Config.ml` (`type_check_pure_code` at `lines 409-417`).
  - `src/llbc/Values.ml` (`tvalue` at `lines 86-213`, `tavalue` at `lines 544-662`, `abs` and `abs_level` at `lines 1111-1132`, `tevalue` at `lines 1134-1443`, `equal_mvalue` at `lines 1572-1576`).
  - `src/interp/InterpBorrows.ml` (`end_concrete_borrow_get_borrow_core` at `lines 15-120`, `end_borrow_aux` at `lines 940-1018`, `end_abs_aux` at `lines 1175-1288`, `destructure_abs` at `lines 1935-2132`).
  - `src/symbolic/SymbolicToPure.ml` (`lines 11-125`), `src/symbolic/SymbolicToPureAbs.ml` (`abs.abs_level = 0` assertion at `line 1261`), `src/symbolic/SymbolicToPureTypes.ml` (`lines 1273-1303`).
- **`AeneasVerif/charon@9e95cf318e3a2964fcf5e03104cde5b718f98ea5`**:
  - `charon/src/transform/control_flow/ullbc_to_llbc.rs` (`CfgInfo::build` at `lines 45-210`, `ReconstructCtx::translate_block_inner` at `lines 442-535`, `translate_terminator` at `lines 537-625`) and `charon/src/transform/control_flow/duplicate_return.rs`.
- **`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`**:
  - `src/Std/WP/Basic.lean` (`lines 25-115`), `src/Std/WP/Monad/Sound.lean` (`lines 15-92`), `src/Std/WP/Frame.lean` (`lines 18-64`).

### 2. Mechanized Lean 4 Prototype (`support/ShallowPlanPrototype.lean`)

All 21 theorems in `support/ShallowPlanPrototype.lean` (SHA-256 `c3bedde36a08986a9d2d7adebe706cc4c141d74411f27d128dd2ec94b91cae3e`, 1,102 lines) were checked by Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) with exit code 0, zero `sorryAx`, and zero `Classical.choice` (`support/verification-results.json`):

| # | Theorem Name | Lines in `ShallowPlanPrototype.lean` | Finding | Axiom Footprint (`#print axioms`) |
| --- | --- | --- | --- | --- |
| 1 | `AeneasRes.bind_ok` | `62-64` | Finding 1 | None (`does not depend on any axioms`) |
| 2 | `spinePreservingJoin_lookup0` | `99-101` | Finding 1 | None (`does not depend on any axioms`) |
| 3 | `spinePreservingJoin_lookup1` | `104-106` | Finding 1 | None (`does not depend on any axioms`) |
| 4 | `spinePreservingJoin_eq_naive` | `110-112` | Finding 1 | None (`does not depend on any axioms`) |
| 5 | `ub_top` | `151-153` | Finding 2 | None (`does not depend on any axioms`) |
| 6 | `not_ub_le_pure` | `155-157` | Finding 2 | None (`does not depend on any axioms`) |
| 7 | `embedRes_fail_top` | `172-174` | Finding 2 | None (`does not depend on any axioms`) |
| 8 | `embedRes_fail_rejected_by_pure` | `179-181` | Finding 2 | None (`does not depend on any axioms`) |
| 9 | `embedRes_fail_accepted_outside_pre` | `186-189` | Finding 2 | None (`does not depend on any axioms`) |
| 10 | `embedRes_div_le_any` | `193-198` | Finding 2 | None (`does not depend on any axioms`) |
| 11 | `wholeLocalBorrow_rfl` | `349-351` | Finding 3 & 4 | None (`does not depend on any axioms`) |
| 12 | `fieldProjBorrow_rfl` | `373-375` | Finding 3 & 4 | None (`does not depend on any axioms`) |
| 13 | `nestedReborrow_rfl` | `408-410` | Finding 3 & 4 | None (`does not depend on any axioms`) |
| 14 | `nestedReborrow_out_of_order_rejected` | `414-424` | Finding 4 | None (`does not depend on any axioms`) |
| 15 | `branchJoinedBorrow_rfl` | `458-461` | Finding 3 & 4 | None (`does not depend on any axioms`) |
| 16 | `choose_futamura_rfl` | `734-737` | Finding 1 & 5 | None (`does not depend on any axioms`) |
| 17 | `evalSym_sound` | `761-898` | Finding 2 & 5 | `[propext]` |
| 18 | `computePlan_sound` | `904-908` | Finding 2 & 5 | `[propext]` |
| 19 | `OwnLoc.writeNA_self` | `943-969` | Finding 6 | `[propext]` |
| 20 | `OwnLoc.writeNA_frame` | `979-1004` | Finding 6 | `[propext]` |
| 21 | `concrete_write_and_endLoan_commute` | `1028-1079` | Finding 6 | `[propext]` |

## Revalidation

From the root of the `reference` worktree, run the self-contained verification harness and repository validator:

```bash
# 1. Re-verify ShallowPlanPrototype.lean with Lean 4.34.1 and check all 21 theorem axiom footprints:
python3 reports/plan-guided-shallow-functional-translation-2026-10-29/support/revalidate.py

# 2. Or invoke Lean 4.34.1 directly on the standalone prototype:
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 \
  reports/plan-guided-shallow-functional-translation-2026-10-29/support/ShallowPlanPrototype.lean

# 3. Validate the reference repository catalog and report formatting:
python3 tools/reference.py catalog
python3 tools/reference.py check
```

Expected output of `revalidate.py`: JSON summary with `"exit_code": 0`, `"has_sorryAx": false`, `"axioms_match_expected": true`, `"theorem_count": 21`, `"zero_axiom_theorem_count": 16`, `"propext_only_theorem_count": 5`, and `"passed": true`.
