<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Partial Compilation and Conditioning Refinement Algebra in Anneal

## Summary

Anneal's Layer 1A refinement framework (`Trusted/Refinement.lean` and
`theory/Anneal/Refinement.lean`) models compilation (`Compiles`), verification
abstraction (`Abstracts`), and crate verification envelopes
(`VerificationResultOn` and `VerificationResult`) inside a single refinement
preorder (`≤`) over `Behavior Query Out := Query → Partial (Out → Prop)`. At
`joshlf/anneal@e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`, `Trusted.Compiler`
models compilation as a total function `compile : L_src.Prog → L_tgt.Prog`.
However, both `rustc` (which can reject a captured `Runtime(PostCleanup)` MIR
body during monomorphization-time `const { assert!(...) }` evaluation, layout
overflow checks, or codegen) and executable Lean lowering passes (which return
`Option L_tgt.Prog`) are partial.

Generalizing `Compiler.compile` to `L_src.Prog → Partial L_tgt.Prog` models
compile-time partiality using the same two-field `Partial` structure
(`defined : Prop`, `val : defined → B`) that already models runtime Undefined
Behavior (UB) in `Trusted/Refinement.lean`. This representation introduces zero
new carrier types into `trusted/`, embeds computable `Option`-returning passes
via `Option.toPartial` (which is isomorphic to `Partial` up to structural
equivalence whenever `.defined` is decidable), and composes multi-stage partial
pipelines via `Partial.bind`.

Conditioning behaviors and partial programs across the refinement preorder is
governed by the **Harmonized Conditioning Triad** (`Behavior.when`,
`Behavior.given`, and `Behavior.require`) and its dependent liftings
(`Language.semIfCompiled` and `Language.semPartial`):

- `Behavior.when P b` (angelic program gating on the left of `≤`, mapping `¬ P`
  to `Partial.bot` / $\bot$) is left adjoint to `Behavior.given P spec`
  (precondition specification gating on the right of `≤`, mapping `¬ P` to
  `Partial.ub` / $\top$):
  $$\mathsf{Behavior.when}\; P\; b \le \mathsf{spec} \iff (P \to b \le \mathsf{spec}) \iff b \le \mathsf{Behavior.given}\; P\; \mathsf{spec}$$
  with
  `L.SpecOn (fun q => P ∧ pre q) post = Behavior.given P (L.SpecOn pre post)`
  holding definitionally (`rfl`).
- `Behavior.require P b` (demonic program gating on the left of `≤`, mapping
  `¬ P` to `Partial.ub` / $\top$) forces `P` to hold at every query where the
  right-hand specification is defined.
- `Compiler.SoundOn` must always use the conditional polarity
  (`∀ h : (C.compile s).defined, Compiles ...`, equivalent to
  `L_tgt.semIfCompiled (C.compile s) ≤ C.π (L_src.sem s)`), never the demonic
  `semPartial` polarity, which would assert `(C.compile s).defined` as an
  unproved TCB axiom and become inconsistent (`False`) on programs rejected by
  a Post-Monomorphization Error (PME).
- Among the three verification modes (`VerifiedTotal` $\implies$ `Verified`
  $\implies$ `VerifiedWhenCompiled`), Mode 1 (`Compiler.Verified`) is the sole
  `Verified` primitive needed in `Trusted/Refinement.lean`: it prevents the
  silent vacuity hazard of unguarded Mode 2 while expressing PME-conditioned
  verification explicitly via `Behavior.given`
  (`verifiedWhenCompiled_iff_verified_given`).
- Conjoining `(rustc body).defined → body.CompileAdmitted` into the meaning of
  `TCBItem.rustcLowering` (`RustcLoweringSound`) enables the target-level
  discharge theorem `target_discharges_compileAdmitted`: a source proof
  conditioned on `body.CompileAdmitted` automatically discharges
  `body.CompileAdmitted` for any target artifact `(rustc body).val h_comp` that
  `rustc` emits, establishing the un-gated target specification under the
  runtime precondition `pre` alone.

## Applicability

The findings in this report apply to the combination of the two subjects in
`REPORT.json`:

1. **Anneal verification framework** at
   `joshlf/anneal@e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`, specifically:
   - `trusted/lean/Trusted/Refinement.lean` (532 lines: Layer 1A refinement
     preorder, `Partial`, `Language`, `Compiler`, `Compiler.SoundOn`,
     `Compiler.Verified`, `VerificationResultOn`, and `VerificationResult`),
   - `theory/Anneal/Refinement.lean` (273 lines: `Partial` lattice lemmas,
     `SpecOn`/`WellFormedOn` characterizations, `pass_trans`, `Compiles.comp`,
     `Abstracts.comp`, `Compiler.SoundOn.verify`, `verify_through_passes`,
     `Compiler.Verified.mono`, and `Compiler.Verified.with_wellFormedOn`),
   - `trusted/lean/Trusted/MirAst.lean` (381 lines) and
     `trusted/lean/Trusted/MirSemantics.lean` (872 lines: `MirLang`, `rustc`,
     `TargetLang`, `RustcCompiler`, `TCBItem`, `CapturedFn`, `Crate`, and
     `CrateTheorem`), and
   - `trusted/audit/TrustedBoundary.lean` (1,014 lines) and
     `trusted/audit/src/lib.rs` (1,961 lines: `.olean` kernel replay, import
     DAG containment, inventory checks, axiom lock, and candidate-feature
     non-contamination).
2. **Lean 4 theorem prover** at
   `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`),
   invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` over standalone
   modules using only `prelude` and `import Init.NotationExtra` (matching
   `Trusted/Refinement.lean`).

All algebraic definitions, equivalences, bridge theorems, and discriminating
canaries in this report are kernel-verified in the preserved package artifacts
[PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) and
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean). Note on
terminology evolution between the two preserved files: in
[PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) (lines 384–389), the
right-hand specification precondition combinator
(`defined := P ∧ (b q).defined`) was initially named `Behavior.when`;
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
308–348) harmonizes the naming across all Anneal workstreams so that
`Behavior.when` denotes angelic left-hand program gating ($\bot$-on-false),
`Behavior.given` denotes right-hand specification gating ($\top$-on-false), and
`Behavior.require` denotes demonic left-hand program gating ($\top$-on-false).
This report uses the harmonized triad names throughout and cross-references both
mechanizations where names differ.

## Findings

### 1. Problem Framing and Partial `compile` Representations

`Basis: normative + source + execution + derived`

In `trusted/lean/Trusted/Refinement.lean` (lines 448–473), `Trusted.Compiler`
currently assumes that compilation is a total function:

```lean
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior
```

Real compilers and verification passes violate totality in two ways:

1. **Post-Monomorphization Errors (PMEs) and backend rejections in `rustc`:**
   `anneal-rustc-capture` extracts `Runtime(PostCleanup)` MIR before
   monomorphization-time `const { assert!(...) }` evaluation, layout and size
   overflow checks, inline-assembly constraint validation, and backend code
   generation. A captured `MirBody` (or a generic instantiation of it) can
   therefore be rejected by `rustc` during monomorphization or codegen.
2. **Partiality in computable Lean lowering passes:** Executable lowering
   passes written in Lean (returning `Option L_tgt.Prog`) can reject
   unsupported instructions or control-flow shapes.

Refining `Trusted/Refinement.lean` and `theory/Anneal/Refinement.lean` to
support partial `compile` must preserve five repository invariants
(`PRINCIPLES.md`, `AGENTS.md`, `trusted/audit/TrustedBoundary.lean`):

1. **No fail-open verification:** Anneal must never report that a function with
   reachable runtime UB is verified because of an unproved or vacuous compiler
   definedness assumption.
2. **TCB auditability and zero-theorem rule:** `Trusted/Refinement.lean` must
   contain only definitions, classes, structures, inductives, and named
   instances (zero theorems), with every declaration marked `@[vetted]` or
   `@[candidate refinement]`.
3. **Constructive, axiom-minimal preorder:** Core definitions and composition
   lemmas must not require `Classical.choice` or `Decidable` instances on
   semantic propositions.
4. **Transitive multi-pass composition:** Vertical compiler pipelines
   (`Compiler.comp`, `Compiles.comp`, `Compiler.Verified.comp`) and Y-diagram
   verification (`verify_through_passes`) must compose across partial passes.
5. **Backward compatibility with existing proofs:** Existing crate-discharge
   lemmas (`Compiler.SoundOn.verify`, `verify_through_passes`,
   `Compiler.Verified.mono`, `Compiler.Verified.with_wellFormedOn`) must retain
   their theorem signatures so existing proofs in `theory/Anneal/` and
   generated `.anneal/Proof.lean` scripts require no structural changes.

#### 1.1 Comparing `Partial L_tgt.Prog` and `Option L_tgt.Prog`

| Dimension | Baseline (`L_src.Prog → L_tgt.Prog`) | Design A (`L_src.Prog → Partial L_tgt.Prog`) | Design B (`L_src.Prog → Option L_tgt.Prog`) |
| :--- | :--- | :--- | :--- |
| **New types in `Trusted/Refinement.lean`** | 0 (baseline) | **0** (reuses existing `Partial`) | 0 (uses `Init` `Option`), but introduces a second partiality carrier alongside `Partial` |
| **Propositional definedness (PME predicates, `opaque rustc`)** | Requires subtype `Prog` or dummy target artifacts | **Native** (`defined : Prop`, `val : defined → L_tgt.Prog`) | Requires `Decidable` or `Classical.choice` to package a `Prop`-guarded compilation into `Option` |
| **Computable partial passes (`Option`)** | Not expressible without dummy values | **Direct via `Option.toPartial`** (`some t ↦ Partial.pure t`, `none ↦ Partial.ub`) | Native (`Option.bind`) |
| **Pass composition (`Compiler.comp`)** | Function composition `C₂.compile ∘ C₁.compile` | `Partial.bind (C₁.compile s) C₂.compile` | `Option.bind (C₁.compile s) C₂.compile` |
| **Proof ergonomics on `opaque rustc`** | Direct application `rustc body` | `h : (rustc body).defined` and `(rustc body).val h` (same `.defined`/`.val` API as `Behavior`) | `∀ t, rustc body = some t → ...` (equational unpacking) |

`Partial B` (`defined : Prop`, `val : defined → B`, `Trusted/Refinement.lean`
lines 292–295) is the semantic model of partiality in Anneal, whereas
`Option B` is the computable realization of `Partial B` when `.defined` is
decidable:

1. **Zero new carrier concepts in `Trusted/Refinement.lean`:** Using
   `compile : L_src.Prog → Partial L_tgt.Prog` represents both runtime
   partiality (UB at query `q`) and compile-time partiality (PME or lowering
   rejection of program `s`) with the same two-field structure.
2. **Dependent monadic bind (`Partial.bind`) and monad laws:** Sequential
   composition of partial values is defined in
   [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) (lines 135–138,
   238–266) and
   [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
   169–173, 203–240) by:
   ```lean
   def Partial.bind {B₁ : Type u} {B₂ : Type v}
       (p : Partial B₁) (f : B₁ → Partial B₂) : Partial B₂ where
     defined := ∃ h : p.defined, (f (p.val h)).defined
     val h := (f (p.val h.1)).val h.2
   ```
   Up to structural equivalence `Partial.Equiv p₁ p₂`
   (`(p₁.defined ↔ p₂.defined) ∧ ∀ h₁ h₂, p₁.val h₁ = p₂.val h₂`, which
   requires no `Preorder` on `B`), `Partial.bind` satisfies left
   identity (`Partial.bind_pure_left`), right identity
   (`Partial.bind_pure_right`), and associativity (`Partial.bind_assoc`), and
   is monotone in its continuation (`Partial.bind_mono_right`).
3. **Exact computable pass embedding (`Option.toPartial`) and decidable
   isomorphism:** Every computable `Option B` embeds into `Partial B` via
   ([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 275–370):
   ```lean
   def Option.toPartial {B : Type u} : Option B → Partial B
     | some b => Partial.pure b
     | none => Partial.ub

   def Partial.toOption {B : Type u} (p : Partial B) [Decidable p.defined] :
       Option B :=
     if h : p.defined then some (p.val h) else none
   ```
   Because `Option.toPartial` pattern-matches on `Option`,
   `Option.toPartial (some b) = Partial.pure b` (`Option.toPartial_some`) and
   `Option.toPartial none = Partial.ub` (`Option.toPartial_none`) hold by
   kernel `rfl`. Furthermore:
   - `Option.toPartial_defined_iff`:
     `(Option.toPartial o).defined ↔ ∃ b, o = some b`.
   - `Option.eq_some_iff_toPartial`: `o = some b` holds iff
     `∃ h : (Option.toPartial o).defined, (Option.toPartial o).val h = b`.
   - `Option.toPartial_bind`: `Option.toPartial (o.bind f)` is structurally
     equivalent (`Partial.Equiv`) to
     `Partial.bind (Option.toPartial o) (fun x => Option.toPartial (f x))`.
   - `Option.toOption_toPartial` and `Partial.toPartial_toOption`: whenever
     `[Decidable p.defined]` holds, `Option B` and `Partial B` are isomorphic
     up to `Partial.Equiv`.
   - Computable partial compilers `compile : L_src.Prog → Option L_tgt.Prog`
     lift via `Compiler.ofOption` (`compile s := Option.toPartial (compile s)`)
     and unfold directly to `compile s = some t` via
     `Compiler.ofOption_soundOn_iff` and `Compiler.ofOption_verified_iff`
     ([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 637–641,
     1397–1436).

---

### 2. The Harmonized Conditioning Triad and Dependent Liftings

`Basis: source + execution + derived`

#### 2.1 Lattice Extremals and the Polarity of Behavioral Conditioning

In `Trusted/Refinement.lean` (lines 326–333), `Partial B` is ordered by forward
simulation:

```lean
le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
```

At each query `q : L.Query`, the observation-predicate lattice
`Partial (L.Out → Prop)` has two extremal elements
([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 113–121,
191–235;
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
149–158, 193–200):

- **Top ($\top = \mathsf{Partial.ub}$):** `defined := False`,
  `val := False.elim`. On the **right-hand side** of `≤` (as a specification),
  `p ≤ Partial.ub` holds vacuously for every `p` (`ub_top`). On the **left-hand
  side** of `≤` (as a program), `Partial.ub ≤ p` holds if and only if
  `¬ p.defined` (`ub_le_iff`), and never refines `Partial.pure b`
  (`not_ub_le_pure`).
- **Bottom ($\bot = \mathsf{Partial.bot}$):** `defined := True`,
  `val := fun _ _ => False` (`Partial.pure (fun _ => False)`). On the
  **left-hand side** of `≤` (as a program), `Partial.bot ≤ p` holds vacuously
  for every `p : Partial (Out → Prop)` (`bot_le`). On the **right-hand side**
  of `≤`, `p ≤ Partial.bot ↔ ∃ h : p.defined, ∀ o, ¬ p.val h o` (`le_bot_iff`).

Conditioning a behavior on a compile-time proposition `P : Prop` (such as
`(C.compile s).defined` or `body.CompileAdmitted`) therefore has three distinct
operational roles depending on whether `¬ P` maps to $\bot$ or $\top$ and
whether the operator stands on the left or right of `≤`:

| Harmonized Operator | Definition at Query `q` | Limit when `¬ P` | Position in `≤` | Operational Role |
| :--- | :--- | :--- | :--- | :--- |
| `Behavior.when P b` | `defined := P → (b q).defined`, `val := fun h o => ∃ hp : P, (b q).val (h hp) o` | `Partial.bot` ($\bot$) | Left-hand side (`Behavior.when P b ≤ spec`) | Angelic / conditional program gating |
| `Behavior.given P spec` | `defined := P ∧ (spec q).defined`, `val := fun h => (spec q).val h.2` | `Partial.ub` ($\top$) | Right-hand side (`b ≤ Behavior.given P spec`) | Precondition specification gating |
| `Behavior.require P b` | `defined := P ∧ (b q).defined`, `val := fun h => (b q).val h.2` | `Partial.ub` ($\top$) | Left-hand side (`Behavior.require P b ≤ spec`) | Demonic program assertion |

#### 2.2 Algebraic Laws of the Harmonized Conditioning Triad

In [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
315–502), the three conditioning operators and their exact laws are mechanized
constructively:

```lean
def Behavior.when {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P → (b q).defined
    val := fun h o => ∃ hp : P, (b q).val (h hp) o
  }

def Behavior.given {Query Obs : Type} (P : Prop) (spec : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P ∧ (spec q).defined
    val := fun h => (spec q).val h.2
  }

def Behavior.require {Query Obs : Type} (P : Prop) (b : Behavior Query Obs) :
    Behavior Query Obs :=
  fun q => {
    defined := P ∧ (b q).defined
    val := fun h => (b q).val h.2
  }
```

Although `Behavior.given P` and `Behavior.require P` share the same underlying
term structure, giving them distinct names makes the lattice polarity of every
refinement inequality immediately legible to human auditors:

1. **Definitional specialization to `SpecOn` and `WellFormedOn`
   (`specOn_and_eq_given`, `wellFormedOn_and_eq_given`):** Conjoining `P` onto
   the query precondition `pre` of `L.SpecOn` or `L.WellFormedOn` is
   **definitionally equal** (`rfl`) to `Behavior.given P`
   ([UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
   352–362; also [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines
   455–468 as `specOn_and_eq_when` / `wellFormedOn_and_eq_when`):
   ```lean
   theorem specOn_and_eq_given (L : Language) (P : Prop)
       (pre : L.Query → Prop) (post : L.Query → L.Obs → Prop) :
       L.SpecOn (fun q => P ∧ pre q) post =
         Behavior.given P (L.SpecOn pre post) := rfl

   theorem wellFormedOn_and_eq_given (L : Language) (P : Prop)
       (pre : L.Query → Prop) :
       L.WellFormedOn (fun q => P ∧ pre q) =
         Behavior.given P (L.WellFormedOn pre) := rfl
   ```
2. **The Fundamental Galois Connection (`when` $\dashv$ `given`,
   `behavior_when_given_adjunction`):** `Behavior.when P` on the left of `≤` is
   left adjoint to `Behavior.given P` on the right of `≤`, with the meta-level
   implication `P → b ≤ spec` in the middle, proved with **zero axioms**
   ([UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
   366–414):
   ```lean
   theorem behavior_when_given_adjunction {Query Obs : Type} (P : Prop)
       (b spec : Behavior Query Obs) :
       (Behavior.when P b ≤ spec ↔ (P → b ≤ spec)) ∧
       ((P → b ≤ spec) ↔ b ≤ Behavior.given P spec)
   ```
   Once `hp : P` is established, `Behavior.le_of_le_given_of_true` discharges
   `Behavior.given P spec` to yield `b ≤ spec`.
3. **Universal property of `Behavior.require P` (`behavior_require_le_iff` and
   `behavior_require_le_iff_of_defined`):** Placing `Behavior.require P b` on
   the left of `≤` requires `P` to hold at every query where `spec` is defined
   ([UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
   420–453):
   ```lean
   theorem behavior_require_le_iff {Query Obs : Type} {P : Prop}
       {b spec : Behavior Query Obs} :
       Behavior.require P b ≤ spec ↔
         (∀ q, (spec q).defined → P) ∧ (P → b ≤ spec)

   theorem behavior_require_le_iff_of_defined {Query Obs : Type} {P : Prop}
       {b spec : Behavior Query Obs} {q₀ : Query} (hq₀ : (spec q₀).defined) :
       Behavior.require P b ≤ spec ↔ P ∧ b ≤ spec
   ```
4. **Lattice ordering and collapse under `P`:** For any `P : Prop` and
   `b : Behavior Query Obs`,
   `Behavior.when P b ≤ b ≤ Behavior.given P b = Behavior.require P b`
   (`when_le_self`, `self_le_given`, `self_le_require`, `when_le_require`), and
   when `hp : P` holds, all three are mutually refining (`≈`) with `b`
   (`when_equiv_of_true`, `given_equiv_of_true`, `require_equiv_of_true`).

#### 2.3 Dependent Liftings and Why `Compiler.SoundOn` Rejects `semPartial`

When a partial compiler `C : Compiler L_src L_tgt` produces
`p? := C.compile s : Partial L_tgt.Prog`, the target program
`(C.compile s).val h` depends on the proof `h : (C.compile s).defined`. The two
left-hand-side program-gating operators (`Behavior.when` and `Behavior.require`)
lift to dependent partial programs `p? : Partial L.Prog`
([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 478–584;
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
514–619):

```lean
/-- Lifting 1: Dependent angelic / conditional lifting (⊥-on-rejection). -/
def Language.semIfCompiled (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => {
    defined := ∀ h : p?.defined, (L.sem (p?.val h) q).defined
    val := fun hdef o => ∃ h : p?.defined, (L.sem (p?.val h) q).val (hdef h) o
  }

/-- Lifting 2: Dependent demonic / total lifting (⊤-on-rejection). -/
def Language.semPartial (L : Language) (p? : Partial L.Prog) : L.Behavior :=
  fun q => Partial.bind p? (fun p => L.sem p q)
```

These liftings satisfy the following zero-axiom laws:

- **Specialization to the propositional triad:** On a constant partial program
  `{ defined := P, val := fun _ => p }`, `L.semIfCompiled` equals
  `Behavior.when P (L.sem p)` by `rfl` (`semIfCompiled_const_eq_when`), and
  `L.semPartial` is mutually refining (`≈`) with
  `Behavior.require P (L.sem p)` (`semPartial_const_equiv_require`).
- **Universal property of `semIfCompiled` (`semIfCompiled_le_iff`):**
  $$\mathsf{L.semIfCompiled}\; p? \le \mathsf{spec} \iff \forall h : p?.\mathsf{defined},\; \mathsf{L.sem}\; (p?.\mathsf{val}\; h) \le \mathsf{spec}$$
  When `p? = Partial.ub`, `L.semIfCompiled Partial.ub ≤ (fun _ => Partial.bot)`
  (`semIfCompiled_ub_le_bot`). When `p? = Partial.pure p`,
  `L.semIfCompiled (Partial.pure p)` is refinement-equivalent to `L.sem p`
  (`semIfCompiled_pure_equiv`).
- **Universal property of `semPartial` (`semPartial_le_iff`):**
  $$\mathsf{L.semPartial}\; p? \le \mathsf{spec} \iff (\forall q,\; (\mathsf{spec}\; q).\mathsf{defined} \to p?.\mathsf{defined}) \wedge (\forall h : p?.\mathsf{defined},\; \mathsf{L.sem}\; (p?.\mathsf{val}\; h) \le \mathsf{spec})$$
  In particular, if `(spec q₀).defined` holds at even one query `q₀`,
  `L.semPartial p? ≤ spec` forces `p?.defined` (`semPartial_le_imp_defined`)
  and is equivalent to `∃ h : p?.defined, L.sem (p?.val h) ≤ spec`
  (`semPartial_le_iff_exists_of_defined` / `semPartial_le_iff_of_defined`).
- **Duality ordering:** `L.semIfCompiled p? ≤ L.semPartial p?` always holds
  (`semIfCompiled_le_semPartial`), and when `h : p?.defined` holds, they
  mutually refine each other (`semPartial_le_semIfCompiled_of_defined`).

**Why `Compiler.SoundOn` must use the `semIfCompiled` polarity rather than
`semPartial`:** In Anneal, `C.SoundOn s` is the semantic meaning of the trusted
compiler assumption `TCBItem.rustcLowering fnName s`
(`Trusted/MirSemantics.lean` line 829). If `C.SoundOn s` were defined using
`semPartial` (`L_tgt.semPartial (C.compile s) ≤ C.π (L_src.sem s)`), then by
`semPartial_le_imp_defined`, for every source program `s` whose mapped behavior
`C.π (L_src.sem s)` is defined at some query `q` (which includes step `0` of
any small-step operational machine), `TCBItem.rustcLowering` would assert
`(C.compile s).defined` as an **unproved TCB axiom**. For a program whose
compilation fails a PME (`¬ (C.compile s).defined`), that TCB assumption would
be `False`, allowing any theorem to be proved ex falso and violating
`PRINCIPLES.md`. Consequently, `Compiler.SoundOn` must always condition on
`h : (C.compile s).defined` (`CompilesPartial`, which is equivalent to
`L_tgt.semIfCompiled (C.compile s) ≤ C.π (L_src.sem s)` by
`compilesPartial_iff_semIfCompiled_le` and
`Compiler.soundOn_iff_semIfCompiled`).

For human comprehension in `trusted/` (`AGENTS.md`), `Trusted/Refinement.lean`
should state
`∀ h : (C.compile s).defined, Compiles L_src L_tgt C.π s ((C.compile s).val h)`
directly in first-order logic, while `Language.semIfCompiled` and
`Language.semPartial` reside in `theory/Anneal/Refinement.lean`.

---

### 3. Verification Modes, Vacuity Canaries, Composition, and `MonoMirSem`

`Basis: source + execution + derived`

#### 3.1 Algebraic Hierarchy of the Three Verification Modes

For a partial compiler `C : Compiler L_src L_tgt`, a source program
`s : L_src.Prog`, and a specification `spec : L_src.Behavior`, there are three
candidate definitions of end-to-end verification
([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 680–804;
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
694–758):

1. **Mode 1 (`Compiler.Verified` / `VerifiedIfCompiled` — Source-Unconditional,
   Target-Conditional):**
   ```lean
   def Compiler.Verified {L_src L_tgt : Language}
       (C : Compiler L_src L_tgt) (s : L_src.Prog)
       (spec : L_src.Behavior) : Prop :=
     L_src.sem s ≤ spec ∧
     ∀ h : (C.compile s).defined,
       Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
       L_tgt.sem ((C.compile s).val h) ≤ C.π spec
   ```
   (In [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean)
   lines 694–699, the second conjunct also packages `Monotone C.π` via
   `C.SoundOn s`.)
2. **Mode 2 (`Compiler.VerifiedWhenCompiled` — Both Source and Target
   Conditional on `(C.compile s).defined`):**
   ```lean
   def Compiler.VerifiedWhenCompiled {L_src L_tgt : Language}
       (C : Compiler L_src L_tgt) (s : L_src.Prog)
       (spec : L_src.Behavior) : Prop :=
     ∀ h : (C.compile s).defined,
       L_src.sem s ≤ spec ∧
       Compiles L_src L_tgt C.π s ((C.compile s).val h) ∧
       L_tgt.sem ((C.compile s).val h) ≤ C.π spec
   ```
3. **Mode 3 (`Compiler.VerifiedTotal` — Compilation Guaranteed plus Mode 1):**
   ```lean
   def Compiler.VerifiedTotal {L_src L_tgt : Language}
       (C : Compiler L_src L_tgt) (s : L_src.Prog)
       (spec : L_src.Behavior) : Prop :=
     (C.compile s).defined ∧ C.Verified s spec
   ```

We prove the strict implication chain
$$\mathsf{VerifiedTotal}\; C\; s\; \mathsf{spec} \implies \mathsf{Verified}\; C\; s\; \mathsf{spec} \implies \mathsf{VerifiedWhenCompiled}\; C\; s\; \mathsf{spec}$$
(`VerifiedTotal.to_verified`, `Verified.to_verifiedWhenCompiled`) together with
the exact characterizations:

- `Compiler.verified_iff_src_and_verifiedWhenCompiled`:
  `C.Verified s spec ↔ L_src.sem s ≤ spec ∧ C.VerifiedWhenCompiled s spec`.
- `Compiler.verifiedTotal_iff_defined_and_verifiedWhenCompiled`:
  `C.VerifiedTotal s spec` holds iff
  `(C.compile s).defined ∧ C.VerifiedWhenCompiled s spec`
  (once `(C.compile s).defined` is known, Mode 1 and Mode 2 coincide).
- `Compiler.verified_iff_semIfCompiled` and
  `Compiler.verifiedTotal_iff_semPartial`:
  Mode 1 corresponds to `L_tgt.semIfCompiled`, whereas Mode 3 corresponds to
  `(C.compile s).defined` plus `L_tgt.semPartial` (and by
  `Compiler.verifiedTotal_of_semPartial`,
  `L_tgt.semPartial (C.compile s) ≤ C.π spec` alone witnesses
  `(C.compile s).defined` whenever `(C.π spec q₀).defined` holds at a witness
  query `q₀`).
- **Conservative extension over total compilers (`Compiler.ofTotal`):** When a
  total compiler is lifted via `Partial.pure` (`Compiler.ofTotal compile π`),
  `SoundOn` (`Compiler.ofTotal_soundOn_iff`) and all three verification modes
  (`Compiler.ofTotal_verified_iff`, `Compiler.ofTotal_verifiedWhenCompiled_iff`,
  `Compiler.ofTotal_verifiedTotal_iff`,
  [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 1352–1394) are
  logically equivalent to the baseline total-compiler definitions in
  `Trusted/Refinement.lean`.

#### 3.2 Mode 2 Vacuity Hazard vs. PME Conditioning (Discriminating Canaries)

Section 5 of [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) (lines
840–953) mechanizes two families of discriminating canaries:

- **Canary Family 1 (`CanaryLang` and `rejectingCompiler`, lines 842–888):**
  `CanaryProg.ubProg` has unconditional runtime UB
  (`CanaryLang.sem .ubProg _ = Partial.ub`), and
  `rejectingCompiler.compile .ubProg = Partial.ub` (`defined := False`):
  - `canary_mode2_vacuous_on_rejected_ub`:
    `rejectingCompiler.VerifiedWhenCompiled .ubProg CanaryLang.WellFormed` holds
    **vacuously** (`fun h => False.elim h`). If `Compiler.Verified` were
    globally replaced by Mode 2 and a bug in the compiler model or PME
    extractor ever assigned `defined = False` (or an unsatisfiable compilation
    condition) to a function with reachable runtime UB, `VerificationResult`
    would silently pass without recording the conditionality in the theorem
    statement.
  - `canary_mode1_rejects_source_ub_even_when_uncompilable`:
    `¬ rejectingCompiler.Verified .ubProg CanaryLang.WellFormed`, because Mode 1
    checks `L_src.sem s ≤ spec` outside `∀ h : (C.compile s).defined`.
  - `canary_mode3_rejects_uncompilable`:
    `¬ rejectingCompiler.VerifiedTotal .ubProg CanaryLang.WellFormed`.
- **Canary Family 2 (`PmeLang` and `pmeCompiler`, lines 894–952):**
  Program `n : Nat` models a generic Rust function `first_elem<const N: usize>`
  with `const { assert!(N > 0); }` whose runtime semantics and compilation
  definedness both require `0 < n`:
  - `canary_pme_verified_with_pme_pre`: for all `n : Nat`,
    `pmeCompiler.Verified n (PmeLang.WellFormedOn (fun _ => 0 < n))` holds in
    Mode 1.
  - `canary_pme_verifiedWhenCompiled`: for all `n : Nat`,
    `pmeCompiler.VerifiedWhenCompiled n PmeLang.WellFormed` holds in Mode 2.
  - `canary_pme_zero_not_verifiedTotal` and `canary_pme_succ_verifiedTotal`:
    at `n = 0`, `¬ pmeCompiler.VerifiedTotal 0 PmeLang.WellFormed`; at
    `n = k + 1`, `pmeCompiler.VerifiedTotal (k + 1) PmeLang.WellFormed` holds.

#### 3.3 Mode Unification (`verifiedWhenCompiled_iff_verified_given`)

Mode 1 (`Compiler.Verified`) expresses Mode 2 (`Compiler.VerifiedWhenCompiled`)
without adding a second top-level verification primitive to
`Trusted/Refinement.lean`:

- In [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
  720–727, where `Verified` and `VerifiedWhenCompiled` state the target
  conclusion against `spec` and package `C.SoundOn s`),
  `verifiedWhenCompiled_iff_verified_given` proves directly from
  `Behavior.behavior_le_given_iff`:
  ```lean
  theorem verifiedWhenCompiled_iff_verified_given {S T : Language}
      (C : Compiler S T) (s : S.Prog) (spec : S.Behavior) :
      C.VerifiedWhenCompiled s spec ↔
        (S.sem s ≤ Behavior.given (C.compile s).defined spec ∧
         C.SoundOn s ∧
         ∀ h : (C.compile s).defined,
           T.sem ((C.compile s).val h) ⊑[C.π] spec)
  ```
- In [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) (lines 817–835,
  where `C.Verified s spec'` also substitutes `spec'` into the target
  obligation `L_tgt.sem ((C.compile s).val h) ≤ C.π spec'`),
  `Compiler.verifiedWhenCompiled_iff_verified_when` proves that under
  `Monotone C.π` (using `when_equiv_of_true hdef spec`),
  $$\mathsf{C.VerifiedWhenCompiled}\; s\; \mathsf{spec} \iff \mathsf{C.Verified}\; s\; (\mathsf{Behavior.given}\; (C.\mathsf{compile}\; s).\mathsf{defined}\; \mathsf{spec})$$
  and `verificationResultWhenCompiledOn_iff` (lines 1324–1343) lifts this
  equivalence to the full `VerificationResultOn` envelope:
  ```lean
  VerificationResultWhenCompiledOn C policy assumptions prog pre specs ↔
    VerificationResultOn C policy assumptions prog
      (fun q => (C.compile prog).defined ∧ pre q)
      (specs.map (Behavior.when (C.compile prog).defined))
  ```
  (where `Behavior.when` in `PartialCompileAlgebra.lean` is the right-hand
  specification-gating operator `Behavior.given`).

Consequently, Mode 1 (`Compiler.Verified`) is the sole `Verified` primitive
needed in `Trusted/Refinement.lean`: ordinary functions prove
`L_src.sem prog ≤ L_src.WellFormedOn pre` unconditionally with zero vacuity
hazard, while PME-dependent functions explicitly include the admissibility
predicate in `fn.pre` (`fun q => P_pme ∧ pre q`) and `fn.specs`.

#### 3.4 Multi-Pass Composition (`Compiler.comp` and `Verified.comp`)

Sequential composition of partial compilers uses `Partial.bind`
([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 961–964;
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
656–659):

```lean
def Compiler.comp {L₁ L₂ L₃ : Language}
    (C₁ : Compiler L₁ L₂) (C₂ : Compiler L₂ L₃) : Compiler L₁ L₃ where
  compile s := Partial.bind (C₁.compile s) C₂.compile
  π b := C₂.π (C₁.π b)
```

Mechanizing multi-pass composition exposes a structural distinction around
`Monotone C₂.π` when `(C₁.compile s).defined` is false: if we are given only
the dependent family
`h₂ : ∀ h : (C₁.compile s).defined, C₂.SoundOn ((C₁.compile s).val h)` and
`(C₁.compile s).defined` is `False`, `h₂` is an empty function from which an
unconditional proof of `Monotone C₂.π` cannot be extracted.
[PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) (lines 1018–1148)
mechanizes three ways to compose across stages:

1. **`Compiler.Verified.comp` (zero extra hypotheses, lines 1109–1121):**
   ```lean
   theorem Compiler.Verified.comp
       {L₁ L₂ L₃ : Language}
       {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃}
       {s : L₁.Prog} {spec : L₁.Behavior}
       (h_ver₁ : C₁.Verified s spec)
       (h_sound₂ : ∀ h : (C₁.compile s).defined,
         C₂.SoundOn ((C₁.compile s).val h)) :
       (C₁.comp C₂).Verified s spec
   ```
   Because `(C₁.comp C₂).Verified s spec` quantifies over
   `⟨hdef₁, hdef₂⟩ : ((C₁.comp C₂).compile s).defined`, `hdef₁` is always in
   context when proving the target obligation, so `(h_sound₂ hdef₁).1` supplies
   `Monotone C₂.π` without any external hypothesis.
2. **`Compiler.SoundOn.comp` and `Compiler.SoundOn.comp_of_defined` (lines
   1032–1054; also `SoundOn.comp` in
   [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
   677–688):** Composes `C₁.SoundOn s` and `h₂` given either `Monotone C₂.π`
   (which is a program-independent property of `C₂.π`) or
   `hdef₁ : (C₁.compile s).defined`.
3. **`Compiler.SoundOnWhenCompiled.comp` (lines 1018–1029):** Scoping
   `Monotone C.π` inside `∀ h : (C.compile s).defined` composes directly with
   zero extra hypotheses and still discharges `C.Verified s spec` via
   `Compiler.SoundOnWhenCompiled.verify` (lines 1071–1078).

Crucially, with `Compiler.SoundOn` and `Compiler.Verified` (Mode 1) generalized
to `Partial L_tgt.Prog`, every bridge theorem in `theory/Anneal/Refinement.lean`
(lines 213–271) retains its **exact theorem signature**
([PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) lines 1060–1067,
1158–1168, 1189–1198, 1243–1251):

- `Compiler.SoundOn.verify`:
  `C.SoundOn s → L_src.sem s ≤ spec → C.Verified s spec`
- `verify_through_passes`:
  `L_v.sem v ≤ spec → Abstracts L_v L_src π_v v s → Monotone π_v →`
  `C.SoundOn s → C.Verified s (π_v spec)`
- `Compiler.Verified.mono`:
  `C.Verified s spec₁ → spec₁ ≤ spec₂ → Monotone C.π → C.Verified s spec₂`
- `Compiler.Verified.with_wellFormedOn`:
  `C.Verified s spec → spec ≤ L_src.WellFormedOn pre → Monotone C.π →`
  `AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s))`

#### 3.5 Reconciling `Behavior.given` with `MonoMirSem` (`Behavior.require`)

Section 5 of
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
1214–1311) reconciles `MirLang`'s right-hand `Behavior.given` specification
gating with `MonoMirLang`'s left-hand demonic `MonoMirSem` gating:

- For a monomorphized compilation unit `u : MonoMirUnit` with PME admissibility
  predicate `u.pmeOk := u.body.CompileAdmitted`, the demonic monomorphized
  semantics is definitionally `Behavior.require`:
  ```lean
  def MonoMirSem (u : MonoMirUnit) : MirLang.Behavior :=
    Behavior.require u.pmeOk (MirSem u.body)

  theorem monoMirSem_eq_require (u : MonoMirUnit) :
      MonoMirSem u = Behavior.require u.pmeOk (MirSem u.body) := rfl
  ```
- In any small-step operational machine `M : SmallStepMachine`, `BehaviorOf M q`
  is **unconditionally defined at `q.steps = 0`** via `ReachesPrefix.zero`
  (`behaviorOf_defined_at_zero`, lines 896–902), regardless of whether `M`
  steps to `.stuck` at step `1`.
- Defining `unifiedTotalPre pre q := q.steps = 0 ∨ pre q` (lines 1246–1247)
  makes `(MirLang.SpecOn (unifiedTotalPre pre) post ⟨0, 0⟩).defined` hold
  unconditionally via `Or.inl rfl`. Applying
  `Behavior.behavior_require_le_iff_of_defined` at `q₀ := ⟨0, 0⟩` yields
  `monoMirSem_le_unifiedTotalPre_iff` (lines 1262–1292): under
  `PostZeroCompatible post` (`∀ init, post ⟨0, init⟩ .outOfFuel`),
  $$\mathsf{MonoMirSem}\; u \le \mathsf{MirLang.SpecOn}\; (\mathsf{unifiedTotalPre}\; \mathsf{pre})\; \mathsf{post} \iff u.\mathsf{pmeOk} \wedge \mathsf{MirSem}\; u.\mathsf{body} \le \mathsf{MirLang.SpecOn}\; \mathsf{pre}\; \mathsf{post}$$
- Conversely, gating the specification in `MonoMirLang` by
  `Behavior.given u.pmeOk` neutralizes the left-hand `Behavior.require u.pmeOk`,
  recovering the exact conditional obligation of `MirLang`
  (`monoMirSem_le_given_pmeOk_iff_mirSem_le_given`, lines 1299–1311):
  $$\mathsf{MonoMirSem}\; u \le \mathsf{Behavior.given}\; u.\mathsf{pmeOk}\; (\mathsf{MirLang.SpecOn}\; \mathsf{pre}\; \mathsf{post}) \iff \mathsf{MirSem}\; u.\mathsf{body} \le \mathsf{MirLang.SpecOn}\; (\mathsf{fun}\; q \Rightarrow u.\mathsf{body.CompileAdmitted} \wedge \mathsf{pre}\; q)\; \mathsf{post}$$

---

### 4. Unified `TCBItem.rustcLowering` and the Target-Level Discharge Bridge

`Basis: source + execution + derived`

#### 4.1 Modeling `CompileAdmitted`, Partial `rustc`, and `RustcLoweringSound`

In [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
914–1075), compile-time PME admissibility and partial `rustc` lowering are
modeled as follows:

1. **CTFE admissibility (`ConstMirBody`, `ConstMirMachine`, `CtfeAdmitted`):**
   Each inline `const { ... }` block (`mir::Const::Unevaluated`) is captured as
   a `ConstMirBody` evaluated by `ConstMirMachine cb`. `CtfeAdmitted cb` holds
   when `BehaviorOf (ConstMirMachine cb)` is defined at all fuel bounds `n` and
   reaches `some ()` at some fuel `n`
   (`ctfeAdmitted_iff_evalOk : CtfeAdmitted cb ↔ cb.evalOk = true`).
2. **Function compile-time admissibility (`MirBody.CompileAdmitted`):**
   ```lean
   def MirBody.CompileAdmitted (body : MirBody) : Prop :=
     body.localLayoutOk ∧ ∀ cb, cb ∈ body.requiredConsts → CtfeAdmitted cb
   ```
3. **Partial `rustc` lowering and `RustcLoweringSound`:**
   In `Trusted/MirSemantics.lean` (line 788), `rustc` is updated from
   `MirBody → TargetArtifact` to `MirBody → Partial TargetArtifact`, and the
   meaning of `TCBItem.rustcLowering fnName body` is defined as
   `RustcLoweringSound body`:
   ```lean
   def RustcLoweringSound (body : MirBody) : Prop :=
     RustcMirCompiler.SoundOn body ∧
     ((rustc body).defined → body.CompileAdmitted)
   ```

Why conjoining `(rustc body).defined → body.CompileAdmitted` into
`RustcLoweringSound` on `TCBItem.rustcLowering` (Approach A) is superior to
baking `CompileAdmitted` into `Language` / `Compiler.SoundOn` or replacing
`MirLang.sem` with demonic `MonoMirSem` (Approach B):

- **Zero contamination of Layer 1A (`Trusted/Refinement.lean`):** `Language`
  and `Compiler.SoundOn` remain generic across arbitrary languages `S` and `T`
  (including pure proof-side languages such as `FunctionalMirLang` that have no
  PME gate).
- **Orthogonal separation of runtime semantics and compile-time gates:**
  `MirSem body` remains the pure operational semantics of `body`'s runtime
  statements, while `body.CompileAdmitted` captures `rustc`'s compile-time
  checks.
- **Automatic target-level discharge:** Source proofs can assume
  `body.CompileAdmitted` via `Behavior.given`, while target-level theorems
  eliminate `body.CompileAdmitted` whenever `(rustc body).defined` holds.

#### 4.2 Target-Level Discharge (`target_discharges_compileAdmitted`)

Suppose a function `body : MirBody` is verified at the source level
conditionally on `body.CompileAdmitted`:

```lean
h_cond : body.CompileAdmitted → MirSem body ≤ MirLang.SpecOn pre post
```

By `mirSem_le_specOn_compileAdmitted_iff`
([UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) lines
1084–1089), `h_cond` is constructively equivalent to refining the PME-gated
specification:

```lean
h_src : MirSem body ≤ MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post
```

From `h_cond` (or `h_src`) and `h_lowering : RustcLoweringSound body`,
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) proves two
bridge theorems:

1. **Source/Crate Envelope Bridge (`verified_compileAdmitted_of_cond` and
   `verificationResultOn_compileAdmitted_of_cond`, lines 1096–1131):** Using
   `h_lowering.1 : RustcMirCompiler.SoundOn body`, `SoundOn.verify` and
   `Verified.with_wellFormedOn` establish `VerificationResultOn` over the
   PME-gated precondition `fun q => body.CompileAdmitted ∧ pre q`—even for
   uncompiled generic templates or dead functions where `body.CompileAdmitted`
   is false.
2. **Target-Level Discharge Bridge (`target_discharges_compileAdmitted`, lines
   1150–1183, and `target_verifiedTotal_unconditional_of_compiled`, lines
   1192–1204):** Whenever `rustc` compiles `body` to a target artifact
   (`h_comp : (rustc body).defined`), the second projection
   `h_lowering.2 : (rustc body).defined → body.CompileAdmitted` fires and
   **discharges `body.CompileAdmitted`** from both the source and target
   specifications:
   ```lean
   theorem target_discharges_compileAdmitted (body : MirBody)
       (pre : ExecQuery Nat → Prop) (post : ExecQuery Nat → ExecObs Nat → Prop)
       (h_lowering : RustcLoweringSound body)
       (h_src :
         MirSem body ≤
           MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post)
       (h_comp : (rustc body).defined) :
       body.CompileAdmitted ∧
       MirSem body ≤ MirLang.SpecOn pre post ∧
       Compiles MirLang TargetLang RustcMirCompiler.π
         body ((rustc body).val h_comp) ∧
       TargetLang.sem ((rustc body).val h_comp) ≤
         RustcMirCompiler.π (MirLang.SpecOn pre post)
   ```
   The proof proceeds in four constructive steps (zero axioms):
   - Extract `h_adm : body.CompileAdmitted := h_lowering.2 h_comp`.
   - Rewrite `MirLang.SpecOn (fun q => body.CompileAdmitted ∧ pre q) post` to
     `Behavior.given body.CompileAdmitted (MirLang.SpecOn pre post)` by `rfl`
     (`specOn_and_eq_given`) and apply
     `Behavior.le_of_le_given_of_true h_src h_adm` to obtain the un-gated
     source refinement `h_src_uncond : MirSem body ≤ MirLang.SpecOn pre post`.
   - Extract
     `Compiles MirLang TargetLang RustcMirCompiler.π body`
     `((rustc body).val h_comp)` from `h_lowering.1.2 h_comp`.
   - Push `h_src_uncond` through `Monotone RustcMirCompiler.π`
     (`h_lowering.1.1`) and `Preorder.le_trans` to obtain
     `TargetLang.sem ((rustc body).val h_comp) ≤`
     `RustcMirCompiler.π (MirLang.SpecOn pre post)` (and
     `RustcMirCompiler.VerifiedTotal body (MirLang.SpecOn pre post)` by
     `target_verifiedTotal_unconditional_of_compiled`).

Section 6 of
[UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
1317–1518) instantiates this bridge on a concrete generic function
`const_bounded_add<const N: usize>(x: usize) -> usize` with
`const { assert!(N < 1000); }`, caller precondition `x ≤ 500`, and
postcondition `ret < 1500`, proving:

- `constBoundedAdd_conditional_refines (N : Nat)` (for all `N : Nat`, including
  `N ≥ 1000`),
- `constBoundedAdd_target_discharged (N : Nat)` (proving that any compiled
  artifact `h_comp : (rustc (constBoundedAddBody N)).defined` satisfies
  `N < 1000` and the un-gated target specification under `x ≤ 500` alone), and
- `verify_exampleCrate (N : Nat) : CrateTheorem (exampleCrate N)`.

---

### 5. Audit Verification Against `TrustedBoundary.lean` and `audit/src/lib.rs`

`Basis: source + execution + derived`

#### 5.1 Exact Declaration Placement Across `trusted/` and `theory/`

| Declaration | Target File in `joshlf/anneal` | Trust / Candidate Attribute |
| :--- | :--- | :--- |
| `Partial.bot`, `Partial.map`, `Partial.bind`, `Option.toPartial` | `trusted/lean/Trusted/Refinement.lean` | `@[candidate refinement]` definitions |
| `Behavior.when`, `Behavior.given`, `Behavior.require` | `trusted/lean/Trusted/Refinement.lean` | `@[candidate refinement]` definitions |
| `Compiler` (`compile : L_src.Prog → Partial L_tgt.Prog`), `Compiler.id`, `Compiler.comp`, `Compiler.SoundOn`, `Compiler.Sound`, `Compiler.Verified`, `Compiler.VerifiedWhenCompiled`, `Compiler.VerifiedTotal` | `trusted/lean/Trusted/Refinement.lean` | `@[candidate refinement]` definitions |
| `ConstId`, `ConstMirBody`, `MirBody.requiredConsts` | `trusted/lean/Trusted/MirAst.lean` | `@[candidate mir_ast]` definitions |
| `ConstMirMachine`, `CtfeAdmitted`, `MirBody.CompileAdmitted` | `trusted/lean/Trusted/MirSemantics.lean` | `@[candidate mir_semantics]` definitions |
| `rustc : MirBody → Partial TargetArtifact`, `RustcLoweringSound`, updated `TCBItem` `TrustedAssumption` instance, `CapturedFn.isPublic`, updated `CrateTheorem` | `trusted/lean/Trusted/MirSemantics.lean` | `@[candidate rustc_capture]` / `@[candidate mir_semantics]` definitions |
| `Language.semIfCompiled`, `Language.semPartial`, and all algebraic, Galois-connection, composition, and target-discharge theorems | `theory/Anneal/Refinement.lean` (and `theory/Anneal/MirLemmas.lean`) | Pure definitions and kernel-checked theorems in `theory/` |

#### 5.2 Check-by-Check Audit Verification

1. **Module Import DAG Containment (`validateGraph` in
   `trusted/audit/TrustedBoundary.lean` lines 169–205; `auditVerifyPreflight`
   lines 869–877; `check_module_imports` in `trusted/audit/src/lib.rs` lines
   1384–1404, 1553–1585):**
   - `Trusted/Refinement.lean` imports only `foundation` (`prelude` +
     `Init.NotationExtra`).
   - `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` import only
     `foundation ++ trusted`.
   - `.anneal/Mir.lean` (`Mir`) imports only `Trusted.MirSemantics`
     (`foundation ++ trusted`). Because `MirBody.CompileAdmitted`,
     `ConstMirBody`, `CapturedFn`, `MirLang.SpecOn`, and `Behavior.given` all
     live in `Trusted.*`, `Mir.lean` requires zero imports from `Anneal.*`.
   - `.anneal/Proof.lean` (`Proof`) imports only
     `foundation ++ trusted ++ theory ++ {Mir}`.
2. **Zero Theorems in `trusted/` (`AGENTS.md` and `verifyAndCollectLocals` in
   `TrustedBoundary.lean` line 900):** Every declaration placed in
   `Trusted/Refinement.lean`, `Trusted/MirAst.lean`, and
   `Trusted/MirSemantics.lean` is a `def`, `abbrev`, `structure`, `inductive`,
   `opaque`, or `instance`; all `theorem` declarations reside in
   `theory/Anneal/*` or `.anneal/Proof.lean`.
3. **`checkMirCrate` and `checkVerifyCrate` (`TrustedBoundary.lean` lines
   945–959):** Updating `CapturedFn`, `MirBody`, and `CrateTheorem` inside
   `Trusted.MirSemantics` preserves the top-level constant names
   `Trusted.Crate` and `Trusted.CrateTheorem`. Therefore `Mir.crate` retains
   exact kernel type `Expr.const `Trusted.Crate []` and `Proof.verify_crate`
   retains exact kernel type
   `Expr.app (Expr.const `Trusted.CrateTheorem []) (Expr.const `Mir.crate [])`.
4. **Statement-Origin Separation:** The kernel type (`ci.type`) of
   `Proof.verify_crate` contains only two root constants:
   `Trusted.CrateTheorem` (origin `Trusted.MirSemantics ∈ trusted`) and
   `Mir.crate` (origin `Mir`). Because `Trusted.MirSemantics` and `Mir` import
   only `foundation ++ trusted` (enforced by `validateModuleImports` in
   `auditVerifyPreflight` at `TrustedBoundary.lean` line 875), every constant
   reachable from `Trusted.CrateTheorem` or `Mir.crate`—including every field of
   every `CapturedFn` in `Mir.crate.functions` and every `TCBItem` in
   `Mir.crate.tcb`—necessarily satisfies
   `origin env c ∈ foundation ∪ trusted ∪ {Mir}`. Untrusted definitions and
   lemmas in `theory/Anneal/*` and `.anneal/Proof.lean` appear exclusively in
   the proof term (`ci.value?`) of `Proof.verify_crate`.
5. **Axiom Lock and `native_decide` Prohibition (`inspectSyntax` and `closure`
   in `TrustedBoundary.lean` lines 318–340, 562–578, 933, 959):** Neither
   preserved Lean mechanization uses `native_decide`, `decide +native`,
   `Lean.ofReduceBool`, `Lean.trustCompiler`, `Classical.choice`, or `sorryAx`.
   The `#print axioms` audit at the end of
   [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (lines
   1524–1535) confirms:
   - **Zero axioms (`does not depend on any axioms`):**
     `Behavior.behavior_when_given_adjunction`,
     `Behavior.behavior_require_le_iff`, `Language.semIfCompiled_le_iff`,
     `Language.semPartial_le_iff`, `verify_through_passes`,
     `target_discharges_compileAdmitted`, and
     `target_verifiedTotal_unconditional_of_compiled`.
   - **`[propext]` only (permitted by `foundation-lock.json`):**
     `Behavior.behavior_require_le_iff_of_defined`,
     `Compiler.verifiedWhenCompiled_iff_verified_given`,
     `monoMirSem_le_unifiedTotalPre_iff`, `constBoundedAdd_target_discharged`,
     and `verify_exampleCrate`.
6. **Candidate-Feature Non-Contamination (`checkTrustedNonContamination` and
   `validCandidateFeatures` in `TrustedBoundary.lean` lines 65–72, 656–808):**
   All proposed `Trusted.*` declarations map to existing candidate feature names
   in `validCandidateFeatures` (`refinement`, `mir_ast`, `mir_semantics`,
   `rustc_capture`), requiring zero edits to `TrustedBoundary.lean` or
   `trusted/audit/src/lib.rs`.

## Boundaries

- **Standalone mechanization vs. in-tree migration (`not examined` as an applied
  worktree commit):** [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean)
  and
  [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) are
  self-contained Lean 4.34.1 modules (`prelude` + `import Init.NotationExtra`)
  that replicate the exact Layer 1A definitions of `Trusted/Refinement.lean`
  and `theory/Anneal/Refinement.lean` and verify the proposed extensions. This
  report does not modify the files inside the `joshlf/anneal` worktree itself.
- **Concrete `rustc` backend semantics (`known not to apply`):** Exactly as in
  `Trusted/MirSemantics.lean` (lines 788–794), `rustc`, `TargetArtifact`,
  `TargetSem`, and `π_c` remain `opaque` interfaces whose per-function
  soundness and PME gate (`RustcLoweringSound body`) are tracked explicitly in
  the crate's TCB audit log via `TCBItem.rustcLowering fnName body` rather than
  proved against a mechanized x86_64/AArch64/LLVM backend.
- **Demonic `semPartial` in `Compiler.SoundOn` (`known not to apply`):** Using
  `Language.semPartial` (`Partial.bind`) to define `Compiler.SoundOn` is sound
  only for total compilers; for partial compilers with non-empty query domains,
  it asserts `(C.compile s).defined` as an unproved TCB axiom and is
  unsound whenever compilation of `s` can fail.
- **Unguarded Mode 2 (`VerifiedWhenCompiled`) as the sole verification envelope
  (`known not to apply`):** Replacing Mode 1 (`Compiler.Verified`) globally by
  unguarded Mode 2 is vulnerable to silent vacuity whenever
  `(C.compile s).defined` is `False` (`canary_mode2_vacuous_on_rejected_ub`).
  Conditioning must instead be stated explicitly in `fn.pre` and `fn.specs` via
  `Behavior.given` / `L.SpecOn (fun q => P ∧ pre q) post`.

## Evidence

- **Primary repository sources (`joshlf/anneal` at commit
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
  - `trusted/lean/Trusted/Refinement.lean`: `Preorder` (lines 258–284),
    `Partial`, `Partial.pure`, `Partial.ub`, `Partial.map`,
    `instPreorderPartial` (lines 292–334), `Monotone`, `Behavior`, `Language`,
    `Language.SpecOn`, `Language.Spec`, `Language.WellFormedOn`,
    `Language.WellFormed` (lines 340–418), `Compiles`, `Abstracts`, `Compiler`,
    `Compiler.SoundOn`, `Compiler.Verified` (lines 427–473),
    `TrustedAssumption`, `TrustPolicy`, `AllHold`, `VerificationResultOn`,
    `VerificationResult` (lines 477–530).
  - `theory/Anneal/Refinement.lean`: `monotone_id`, `monotone_comp`,
    `Partial.monotone_map`, `ub_top`, `ub_le_iff`, `pure_le_pure_iff`,
    `not_ub_le_pure` (lines 51–100), `le_specOn_iff`, `le_wellFormedOn_iff`,
    `le_wellFormed_iff`, `specOn_le_wellFormedOn` (lines 104–164),
    `pass_trans`, `Compiles.comp`, `Abstracts.comp`, `Compiler.SoundOn.verify`,
    `verify_through_passes`, `Compiler.Verified.mono`,
    `Compiler.Verified.with_wellFormedOn` (lines 171–271).
  - `trusted/lean/Trusted/MirAst.lean` (lines 1–381) and
    `trusted/lean/Trusted/MirSemantics.lean`: `TargetArtifact`, `rustc`,
    `TargetSem`, `TargetLang`, `π_c`, `RustcCompiler`, `TCBItem`,
    `instTrustedAssumptionTCBItem`, `defaultTrustPolicy`, `CapturedFn`,
    `Crate`, `CrateTheorem` (lines 779–872).
  - `trusted/audit/TrustedBoundary.lean`: `validCandidateFeatures` (lines
    65–72), `validateGraph` (lines 169–205), `inspectSyntax` (lines 318–340),
    `closure` (lines 562–578), `checkTrustedNonContamination` (lines 656–808),
    `auditVerifyPreflight` (lines 869–877), `auditFull` (lines 892–938),
    `auditVerify`, `checkMirCrate`, `checkVerifyCrate` (lines 943–965).
  - `trusted/audit/src/lib.rs`: `run_setup_audit` and `trusted-roots.txt`
    validation (lines 973–984), `check_module_imports` (lines 1384–1404),
    `run_verify_audit` (lines 1553–1585).
- **Preserved mechanized Lean 4.34.1 support artifacts (observed 2026-10-30):**
  - [PartialCompileAlgebra.lean](PartialCompileAlgebra.lean) (1,438 lines;
    SHA-256:
    `fdd0c5a26c5c1bb85b80df84f72d617079f32947115a6496572bfdbe7445e27e`).
  - [UnifiedPmeConditionalSystem.lean](UnifiedPmeConditionalSystem.lean) (1,537
    lines; SHA-256:
    `e388b24a4b822408f29dd66987b884c3bff53778a108fa56ff4e753391f74763`).
- **Execution environment and verification commands (observed 2026-10-30):**
  Verified on Linux (`x86_64`) with Lean `v4.34.1`
  (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) using:
  ```console
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
    PartialCompileAlgebra.lean
  lean -DElab.async=false -Ddebug.skipKernelTC=false \
    UnifiedPmeConditionalSystem.lean
  ```
  Both commands exited with status `0`, zero warnings, zero `sorryAx`, and zero
  `Lean.ofReduceBool`.

## Revalidation

To revalidate the algebraic, bridge, and axiom-audit claims of this report
against Lean `v4.34.1` or a newer Lean toolchain, run the kernel typechecker
with asynchronous elaboration and kernel-skipping disabled on both preserved
files inside this report directory:

```console
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/anneal-partial-compile-and-conditioning-refinement-algebra-2026/PartialCompileAlgebra.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/anneal-partial-compile-and-conditioning-refinement-algebra-2026/UnifiedPmeConditionalSystem.lean
```

Confirm that:

1. `PartialCompileAlgebra.lean` exits with status `0` and produces no output.
2. `UnifiedPmeConditionalSystem.lean` exits with status `0` and its
   `#print axioms` block prints `does not depend on any axioms` for
   `behavior_when_given_adjunction`, `behavior_require_le_iff`,
   `semIfCompiled_le_iff`, `semPartial_le_iff`, `verify_through_passes`,
   `target_discharges_compileAdmitted`, and
   `target_verifiedTotal_unconditional_of_compiled`, and
   `depends on axioms: [propext]` for the remaining five equivalence-rewriting
   theorems.
3. If `Trusted/Refinement.lean`, `theory/Anneal/Refinement.lean`, or
   `trusted/audit/TrustedBoundary.lean` changes in `joshlf/anneal`, diff those
   files against `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` and re-run
   `cargo anneal --setup` and `cargo anneal --verify` to confirm that import
   DAG containment, `checkMirCrate`, `checkVerifyCrate`, and
   `foundation-lock.json` axiom checks continue to hold.

*Authored by an AI agent acting on joshlf's behalf.*
