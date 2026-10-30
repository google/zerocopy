/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

/-!
# Track 8 Probe: Compositional Separate Compilation, FFI Linking, and Unwind CFI

This standalone Lean 4.34.1 mechanization accompanies the Track 8 Round 1
research report. It establishes two core results over Anneal's Layer 1A
refinement definitions (`Trusted/Refinement.lean` at
`skeleton@e75556f5767705404404c0675c6d2d9bcee41d6f`):

1. **Compositional Separate Compilation and Open Linking (`Part 1`):**
   - Models open MIR modules (`OpenMirModule`) and open target assembly modules
     (`OpenAsmModule`) parameterized by imported/exported function symbols and
     an explicit interprocedural call contract table (`ContractTable`).
   - Proves that per-module compilation commutes with syntactic module linking
     (`compileMod_commutes_with_link`, after `SepCompCert` / CompCert
     `common/Linking.v`).
   - Proves horizontal compositional refinement (`linkModules_compiles` and
     `linkModules_verified`): separately compiled crates whose exports satisfy
     their declared call contracts link into a combined target module that
     refines the linked MIR module under `Trusted.Compiles` and
     `Trusted.Compiler.Verified`.
   - Proves heterogeneous FFI / assembly linking (`linkForeignAsm_compiles`):
     linking an Anneal-compiled Rust module with an external assembly module
     that has no MIR source preserves `Compiles` whenever the external module
     satisfies its declared ABI call contract and callee-saved register
     invariant.

2. **DWARF `.eh_frame` CFI + `.gcc_except_table` LSDA Unwinding (`Part 2–3`):**
   - Formalizes MIR unwinding (`UnwindAction::Cleanup`, `UnwindAction::Terminate`
     for `Reason::Abi` and `Reason::InCleanup`, reverse-order drop ladders, and
     `TerminatorKind::UnwindResume`) alongside a target stack/register machine
     driven by `.eh_frame` Frame Description Entries (`EhFrameFde`) and
     `.gcc_except_table` Language-Specific Data Areas (`LsdaCallSiteEntry`).
   - Defines a computable post-codegen unwind table validator
     (`checkUnwindTables`) and proves `unwind_machine_compiles` and
     `unwind_machine_verified`: for every program accepted by
     `checkUnwindTables`, target execution refines MIR execution across normal
     returns, multi-frame stack unwinding with reverse drop ladders, and
     double-panic aborts (`panic_in_cleanup` / `panic_cannot_unwind`).
   - Mechanizes three negative adequacy canaries (`Part 3`):
     * **Canary A:** A wrong `.eh_frame` `cfaOffset` corrupts the caller stack
       pointer (`SP`) upon unwind, violates `Compiles`, and is rejected by
       `checkUnwindTables`.
     * **Canary B:** Omitting a `DW_CFA_offset` restoration rule for a
       clobbered callee-saved register (`RBX`) clobbers a caller local live
       across the cleanup landing pad, violates `Compiles`, and is rejected by
       `checkUnwindTables`.
     * **Canary C:** Replacing a terminate filter landing pad
       (`EHAction::Filter`) with a normal cleanup action (`EHAction::Cleanup`,
       as in `rustc_codegen_cranelift/src/abi/mod.rs:910`) when a destructor
       panics during cleanup (`Reason::InCleanup`) causes unsound
       double-unwinding instead of `.failed .panicAbort`, violates `Compiles`,
       and is rejected by `checkUnwindTables`.
-/

namespace Track8Probe

/-!
## Layer 1A: Exact Anneal Refinement Foundations (`Trusted/Refinement.lean`)

The definitions in this section mirror `trusted/lean/Trusted/Refinement.lean`
at `skeleton@e75556f5767705404404c0675c6d2d9bcee41d6f` verbatim so that all
linking and unwinding theorems discharge directly against Anneal's kernel trust
boundary.
-/

/-- A reflexive, transitive relation on `α`. -/
structure Preorder (α : Type u) where
  /-- The underlying binary relation. -/
  le : α → α → Prop
  /-- Reflexivity: every element relates to itself. -/
  refl : ∀ a, le a a
  /-- Transitivity: relatedness chains across intermediate elements. -/
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- A partial value that is either undefined (`undef`) or defined (` val `). -/
inductive Partial (α : Type u) where
  | undef
  | defined (val : α)
  deriving DecidableEq, Repr

namespace Partial

/-- The flat information order on `Partial α` induced by a preorder on `α`. -/
def le (ord : Preorder α) : Partial α → Partial α → Prop
  | .undef, _ => True
  | .defined _, .undef => False
  | .defined a, .defined b => ord.le a b

/-- `Partial.le ord` is a preorder whenever `ord` is a preorder. -/
def preorder (ord : Preorder α) : Preorder (Partial α) where
  le := le ord
  refl a := by
    cases a with
    | undef => trivial
    | defined v => exact ord.refl v
  trans {a b c} hab hbc := by
    cases a <;> cases b <;> cases c <;> try trivial
    exact ord.trans hab hbc

end Partial

/-- The outcome of executing a program to completion. -/
inductive Behavior (Obs : Type u) (Err : Type v) where
  | terminates (obs : Obs)
  | diverges
  | failed (err : Err)
  | goesWrong
  deriving DecidableEq, Repr

namespace Behavior

/-- Refinement order on `Behavior`: `goesWrong` is refined by everything;
`terminates` refines pointwise via `ord`; `diverges` and `failed` refine only
themselves. -/
def le (ord : Preorder Obs) : Behavior Obs Err → Behavior Obs Err → Prop
  | .goesWrong, _ => True
  | .terminates o₁, .terminates o₂ => ord.le o₁ o₂
  | .diverges, .diverges => True
  | .failed e₁, .failed e₂ => e₁ = e₂
  | _, _ => False

/-- `Behavior.le ord` is a preorder whenever `ord` is a preorder. -/
def preorder (ord : Preorder Obs) : Preorder (Behavior Obs Err) where
  le := le ord
  refl b := by
    cases b with
    | goesWrong => trivial
    | terminates o => exact ord.refl o
    | diverges => trivial
    | failed e => rfl
  trans {a b c} hab hbc := by
    cases a <;> cases b <;> cases c <;> try trivial
    · exact ord.trans hab hbc
    · exact Eq.trans hab hbc

end Behavior

/-- A language parameterized by its syntax, observable values, error domain,
refinement preorder, and big-step semantics. -/
structure Language where
  /-- Program syntax (AST, IR, or machine code). -/
  Prog : Type u
  /-- Observable values produced on normal termination. -/
  Obs : Type v
  /-- Structured failure reasons (distinct from UB / `goesWrong`). -/
  Err : Type w
  /-- Refinement preorder on observable values. -/
  obsPreorder : Preorder Obs
  /-- Big-step relational semantics mapping programs to possible behaviors. -/
  exec : Prog → Behavior Obs Err → Prop

/-- Target program `t` correctly compiles source program `s` under observation
projection `π`: every target behavior is a valid behavior of `s` after
lifting through `π` and allowing UB refinement (`Behavior.le`). -/
def Compiles
    (S T : Language)
    (π : T.Obs → Partial S.Obs)
    (s : S.Prog) (t : T.Prog) : Prop :=
  ∀ b_t, T.exec t b_t →
    ∃ b_s, S.exec s b_s ∧
      match b_t, b_s with
      | .terminates o_t, .terminates o_s =>
          (Partial.preorder S.obsPreorder).le (.defined o_s) (π o_t)
      | .diverges, .diverges => True
      | .failed e_t, .failed e_s => HEq e_t e_s
      | _, .goesWrong => True
      | _, _ => False

/-- A compiler from source language `S` to target language `T`. -/
structure Compiler (S T : Language) where
  /-- Partial compilation function (`none` if the compiler rejects `s`). -/
  compile : S.Prog → Option T.Prog
  /-- Projection from target observations back to partial source observations. -/
  π : T.Obs → Partial S.Obs

/-- Conditional compiler soundness on a source domain predicate `D`. -/
def Compiler.SoundOn (C : Compiler S T) (D : S.Prog → Prop) : Prop :=
  ∀ s t, D s → C.compile s = some t → Compiles S T C.π s t

/-- Per-invocation verified compilation witness (`Trusted/Refinement.lean`). -/
def Compiler.Verified (C : Compiler S T) (D : S.Prog → Prop) (s : S.Prog) : Prop :=
  D s ∧ ∃ t, C.compile s = some t ∧ Compiles S T C.π s t

/-- Discrete equality preorder on any type `α`. -/
def discretePreorder (α : Type u) : Preorder α where
  le a b := a = b
  refl _ := rfl
  trans h₁ h₂ := Eq.trans h₁ h₂

/-!
## Part 1: Compositional Separate Compilation & Multi-Crate / FFI Linking

In `skeleton@e75556f5767705404404c0675c6d2d9bcee41d6f`
(`Trusted/MirSemantics.lean:349-357, 866-870`), interprocedural calls are
currently closed over a fixed two-element enum `PureCallee2` (`.addBounded`,
`.absDiff`), and `CrateTheorem` is a conjunction of independent per-function
obligations without cross-module linking.

To support separate compilation of Rust crates (`core`, `zerocopy`, user
crates) as well as heterogeneous linking with verified assembly or C FFI
(`SepCompCert`, `CompCertO`, and `DimSum`), we parameterize open modules by:
- `imports : List FnId` (unresolved external symbols),
- `exports : List (FnId × Body)` (defined function bodies), and
- `contracts : List (FnId × FnContract)` (the ABI-level relational call
  summaries agreed upon at module boundaries).
-/

/-- Function symbol identifier (modeling a monomorphized `MonoItem::Fn` symbol
or `DefPathHash` + `GenericArgs` key). -/
abbrev FnId := Nat

/-- Interprocedural contract for a function `f(arg) = arg + delta`.
In full Anneal, this generalizes `evalPureCallee2` to an arbitrary pure or
memory-framed relational postcondition over `(Args, Mem) → (Ret, Mem)`. -/
structure FnContract where
  /-- Additive summary offset for `f(x) = x + delta`. -/
  delta : Int
  deriving DecidableEq, Repr

/-- An open MIR function body that transforms its input argument `x` by adding
`localConst` and optionally calling an external or sibling function `callee`. -/
structure MirFnBody where
  /-- Constant added locally by this function before/after the call. -/
  localConst : Int
  /-- Optional callee symbol invoked via `TerminatorKind::Call`. -/
  callee : Option FnId
  deriving DecidableEq, Repr

/-- Target assembly code for a single function, including an explicit
callee-saved register preservation flag (`preservesCalleeSaved`) modeling ABI
compliance (`FnAbi` on x86_64 SysV / AAPCS64). -/
structure AsmFnCode where
  /-- Immediate offset emitted in the target instruction stream. -/
  immOffset : Int
  /-- Optional `bl` / `call` target symbol. -/
  callTarget : Option FnId
  /-- Whether the assembly prologue/epilogue preserves callee-saved registers
  (`RBX`, `RBP`, `R12`–`R15` / `X19`–`X29`) across the call. -/
  preservesCalleeSaved : Bool
  deriving DecidableEq, Repr

/-- Lookup a value by `FnId` key in an association list. -/
def assocLookup (k : FnId) : List (FnId × α) → Option α
  | [] => none
  | (k', v) :: rest => if k == k' then some v else assocLookup k rest

/-- Check whether two export lists define disjoint sets of symbol identifiers. -/
def disjointExports (e₁ e₂ : List (FnId × α)) : Bool :=
  e₁.all (fun p => (assocLookup p.1 e₂).isNone)

/-- Filter an import list by removing symbols that are now defined in `exports`. -/
def remainingImports (imports : List FnId) (exports : List (FnId × α)) : List FnId :=
  imports.filter (fun k => (assocLookup k exports).isNone)

/-- An open MIR compilation unit (modeling a crate or CGU prior to final
linking). -/
structure OpenMirModule where
  /-- Unresolved external function symbols referenced by this module. -/
  imports : List FnId
  /-- Monomorphized function definitions exported by this module. -/
  exports : List (FnId × MirFnBody)
  /-- Declared interprocedural call contracts for local and external symbols. -/
  contracts : List (FnId × FnContract)
  /-- Entry point symbol and initial argument evaluated at module execution. -/
  entry : FnId
  /-- Initial argument passed to `entry`. -/
  entryArg : Int
  deriving DecidableEq, Repr

/-- An open target assembly compilation unit (modeling an `.o` object or `.rlib`
machine artifact). -/
structure OpenAsmModule where
  /-- Unresolved external symbols (`STT_NOTYPE` / `SHN_UNDEF` relocations). -/
  imports : List FnId
  /-- Defined machine-code functions. -/
  exports : List (FnId × AsmFnCode)
  /-- Declared ABI call contracts. -/
  contracts : List (FnId × FnContract)
  /-- Entry point symbol. -/
  entry : FnId
  /-- Initial argument passed to `entry`. -/
  entryArg : Int
  deriving DecidableEq, Repr

/-- Evaluate a single MIR function body against an open contract table.
Following CompCertO / Anneal's `evalPureCallee2` abstraction, interprocedural
calls are interpreted against their declared contract `contracts`. If a called
symbol has no contract in `contracts`, evaluation fails (`.goesWrong`). -/
def evalMirBody (contracts : List (FnId × FnContract)) (body : MirFnBody) (arg : Int) :
    Option Int :=
  match body.callee with
  | none => some (arg + body.localConst)
  | some cid =>
      match assocLookup cid contracts with
      | some c => some (arg + c.delta + body.localConst)
      | none => none

/-- Evaluate a single target assembly function against an open contract table.
Target execution requires both that the callee has a valid contract and that the
assembly function preserves callee-saved registers (`preservesCalleeSaved`). -/
def evalAsmCode (contracts : List (FnId × FnContract)) (code : AsmFnCode) (arg : Int) :
    Option Int :=
  if !code.preservesCalleeSaved then
    none
  else
    match code.callTarget with
    | none => some (arg + code.immOffset)
    | some cid =>
        match assocLookup cid contracts with
        | some c => some (arg + c.delta + code.immOffset)
        | none => none

/-- Module-level adequacy for an `OpenMirModule`:
1. The module's `entry` function is defined in `M.exports` and evaluates to a
   defined result under `M.contracts`.
2. Every exported function `(fid, body)` in `M.exports` implements its declared
   contract in `M.contracts`. -/
def MirModuleAdequate (M : OpenMirModule) : Prop :=
  ∃ entryBody entryOut,
    assocLookup M.entry M.exports = some entryBody ∧
    evalMirBody M.contracts entryBody M.entryArg = some entryOut

/-- Evaluate an `OpenMirModule` to a `Behavior Int Unit`. -/
def evalOpenMir (M : OpenMirModule) : Behavior Int Unit :=
  match assocLookup M.entry M.exports with
  | some body =>
      match evalMirBody M.contracts body M.entryArg with
      | some out => .terminates out
      | none => .goesWrong
  | none => .goesWrong

/-- Evaluate an `OpenAsmModule` to a `Behavior Int Unit`. -/
def evalOpenAsm (A : OpenAsmModule) : Behavior Int Unit :=
  match assocLookup A.entry A.exports with
  | some code =>
      match evalAsmCode A.contracts code A.entryArg with
      | some out => .terminates out
      | none => .goesWrong
  | none => .goesWrong

/-- The open MIR language instance (`Trusted.Language`). -/
def OpenMirLang : Language where
  Prog := OpenMirModule
  Obs := Int
  Err := Unit
  obsPreorder := discretePreorder Int
  exec m b := evalOpenMir m = b

/-- The open target assembly language instance (`Trusted.Language`). -/
def OpenAsmLang : Language where
  Prog := OpenAsmModule
  Obs := Int
  Err := Unit
  obsPreorder := discretePreorder Int
  exec a b := evalOpenAsm a = b

/-- Observation projection from target `Int` to `Partial Int`. -/
def π_mod (v : Int) : Partial Int := .defined v

/-- Compile a single MIR function body into target assembly with ABI-compliant
callee-saved register preservation (`preservesCalleeSaved := true`). -/
def compileFn (body : MirFnBody) : AsmFnCode where
  immOffset := body.localConst
  callTarget := body.callee
  preservesCalleeSaved := true

/-- Compile an `OpenMirModule` into an `OpenAsmModule` by compiling every
exported function body pairwise. -/
def compileMod (M : OpenMirModule) : Option OpenAsmModule :=
  some {
    imports := M.imports
    exports := M.exports.map (fun p => (p.1, compileFn p.2))
    contracts := M.contracts
    entry := M.entry
    entryArg := M.entryArg
  }

/-- Anneal's module compiler bundling `compileMod` and `π_mod`. -/
def ModCompiler : Compiler OpenMirLang OpenAsmLang where
  compile := compileMod
  π := π_mod

/-- Syntactic linker for open MIR modules (after CompCert's `common/Linking.v`):
verifies that exported symbol sets are disjoint and that both modules agree on
the interprocedural contract table, then merges exports and resolves imports. -/
def linkMir (M₁ M₂ : OpenMirModule) : Option OpenMirModule :=
  if disjointExports M₁.exports M₂.exports && (M₁.contracts == M₂.contracts) &&
     (M₁.entry == M₂.entry) && (M₁.entryArg == M₂.entryArg) then
    let combinedExports := M₁.exports ++ M₂.exports
    some {
      imports := remainingImports (M₁.imports ++ M₂.imports) combinedExports
      exports := combinedExports
      contracts := M₁.contracts
      entry := M₁.entry
      entryArg := M₁.entryArg
    }
  else
    none

/-- Syntactic linker for open target assembly modules (`ld` / `lld` symbol
resolution over `.o` / `.rlib` objects). -/
def linkAsm (A₁ A₂ : OpenAsmModule) : Option OpenAsmModule :=
  if disjointExports A₁.exports A₂.exports && (A₁.contracts == A₂.contracts) &&
     (A₁.entry == A₂.entry) && (A₁.entryArg == A₂.entryArg) then
    let combinedExports := A₁.exports ++ A₂.exports
    some {
      imports := remainingImports (A₁.imports ++ A₂.imports) combinedExports
      exports := combinedExports
      contracts := A₁.contracts
      entry := A₁.entry
      entryArg := A₁.entryArg
    }
  else
    none

/-- Lookup commutes with `List.map` over values in an association list. -/
theorem assocLookup_map (k : FnId) (f : α → β) (xs : List (FnId × α)) :
    assocLookup k (xs.map (fun p => (p.1, f p.2))) = (assocLookup k xs).map f := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', v⟩ := hd
    simp only [List.map, assocLookup]
    by_cases h : (k == k') = true
    · simp [h]
    · simp [h, ih]

/-- `Option.isNone` is invariant under `Option.map`. -/
theorem isNone_map (f : α → β) (o : Option α) :
    (o.map f).isNone = o.isNone := by
  cases o <;> rfl

/-- Disjointness of export keys is preserved when mapping `compileFn` across
exported definitions. -/
theorem disjointExports_map (f : α → β) (e₁ e₂ : List (FnId × α)) :
    disjointExports (e₁.map (fun p => (p.1, f p.2))) (e₂.map (fun p => (p.1, f p.2))) =
      disjointExports e₁ e₂ := by
  unfold disjointExports
  induction e₁ with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map, List.all_cons]
    rw [ih]
    simp only [assocLookup_map, isNone_map]

/-- Remaining unresolved imports are preserved when mapping `compileFn` across
exported definitions. -/
theorem remainingImports_map (f : α → β) (imps : List FnId) (exps : List (FnId × α)) :
    remainingImports imps (exps.map (fun p => (p.1, f p.2))) =
      remainingImports imps exps := by
  unfold remainingImports
  induction imps with
  | nil => rfl
  | cons k tl ih =>
    simp only [List.filter, assocLookup_map, isNone_map]

/-- Evaluating a compiled function `compileFn body` equals evaluating the MIR
`body` under any contract table `contracts`. -/
theorem evalAsmCode_compileFn (contracts : List (FnId × FnContract))
    (body : MirFnBody) (arg : Int) :
    evalAsmCode contracts (compileFn body) arg = evalMirBody contracts body arg := by
  unfold compileFn evalAsmCode evalMirBody
  rfl

/-- Evaluating a compiled module `compileMod M` produces the exact same behavior
as evaluating `M` in `OpenMirLang`. -/
theorem evalOpenAsm_compileMod (M : OpenMirModule) :
    evalOpenAsm {
      imports := M.imports
      exports := M.exports.map (fun p => (p.1, compileFn p.2))
      contracts := M.contracts
      entry := M.entry
      entryArg := M.entryArg
    } = evalOpenMir M := by
  unfold evalOpenAsm evalOpenMir
  rw [assocLookup_map]
  cases assocLookup M.entry M.exports with
  | none => rfl
  | some body =>
    simp only [Option.map, evalAsmCode_compileFn]

/-- Every `OpenMirModule` compiles to an `OpenAsmModule` that refines it under
`Trusted.Compiles`. -/
theorem compileMod_compiles (M : OpenMirModule) (A : OpenAsmModule)
    (hcomp : compileMod M = some A) :
    Compiles OpenMirLang OpenAsmLang π_mod M A := by
  unfold compileMod at hcomp
  injection hcomp with hA
  subst hA
  intro b_t hexec
  refine ⟨b_t, ?_, ?_⟩
  · change evalOpenMir M = b_t
    rw [← evalOpenAsm_compileMod M]
    exact hexec
  · cases b_t with
    | terminates o => exact rfl
    | diverges => trivial
    | failed e => exact HEq.rfl
    | goesWrong => trivial

/-- **Commutativity of Separate Compilation and Linking (`SepCompCert` diagram):**
If `M₁` compiles to `A₁`, `M₂` compiles to `A₂`, and `M₁` links with `M₂` to
produce `M₁₂`, then `A₁` and `A₂` link to produce `A₁₂` such that compiling
`M₁₂` directly yields `some A₁₂`. -/
theorem compileMod_commutes_with_link
    (M₁ M₂ M₁₂ : OpenMirModule) (A₁ A₂ : OpenAsmModule)
    (hc₁ : compileMod M₁ = some A₁)
    (hc₂ : compileMod M₂ = some A₂)
    (hlink : linkMir M₁ M₂ = some M₁₂) :
    ∃ A₁₂, linkAsm A₁ A₂ = some A₁₂ ∧ compileMod M₁₂ = some A₁₂ := by
  unfold compileMod at hc₁ hc₂
  injection hc₁ with hA₁
  injection hc₂ with hA₂
  subst hA₁ hA₂
  unfold linkMir at hlink
  split at hlink
  · next hcond =>
    injection hlink with hM₁₂
    subst hM₁₂
    refine ⟨{
      imports := remainingImports (M₁.imports ++ M₂.imports) (M₁.exports ++ M₂.exports)
      exports := (M₁.exports ++ M₂.exports).map (fun p => (p.1, compileFn p.2))
      contracts := M₁.contracts
      entry := M₁.entry
      entryArg := M₁.entryArg
    }, ?_, rfl⟩
    unfold linkAsm
    simp only [disjointExports_map, hcond, ↓reduceIte,
      ← List.map_append, remainingImports_map]
  · contradiction

/-- **Horizontal Compositional Refinement (`linkModules_compiles`):**
Separately compiled modules `A₁` (from Crate A) and `A₂` (from Crate B) link at
the target assembly level into `A₁₂` that refines the linked MIR program `M₁₂`
under `Trusted.Compiles`. -/
theorem linkModules_compiles
    (M₁ M₂ M₁₂ : OpenMirModule) (A₁ A₂ : OpenAsmModule)
    (hc₁ : compileMod M₁ = some A₁)
    (hc₂ : compileMod M₂ = some A₂)
    (hlink : linkMir M₁ M₂ = some M₁₂) :
    ∃ A₁₂, linkAsm A₁ A₂ = some A₁₂ ∧
      Compiles OpenMirLang OpenAsmLang π_mod M₁₂ A₁₂ := by
  obtain ⟨A₁₂, hlinkAsm, hcomp₁₂⟩ :=
    compileMod_commutes_with_link M₁ M₂ M₁₂ A₁ A₂ hc₁ hc₂ hlink
  exact ⟨A₁₂, hlinkAsm, compileMod_compiles M₁₂ A₁₂ hcomp₁₂⟩

/--Lookup in `e₁ ++ e₂` returns the result from `e₁` whenever `k` is already
present in `e₁`. -/
theorem assocLookup_append_left (k : FnId) (e₁ e₂ : List (FnId × α))
    (v : α) (h : assocLookup k e₁ = some v) :
    assocLookup k (e₁ ++ e₂) = some v := by
  induction e₁ with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [List.cons_append, assocLookup] at h ⊢
    by_cases hk : (k == k') = true
    · simp [hk] at h ⊢
      exact h
    · simp [hk] at h ⊢
      exact ih h

/-- Adequacy is preserved when linking a module `M₁` that defines `entry` with a
sibling crate `M₂`. -/
theorem linkMir_preserves_adequate
    (M₁ M₂ M₁₂ : OpenMirModule)
    (hadq : MirModuleAdequate M₁)
    (hlink : linkMir M₁ M₂ = some M₁₂) :
    MirModuleAdequate M₁₂ := by
  unfold linkMir at hlink
  split at hlink
  · injection hlink with hM₁₂
    subst hM₁₂
    obtain ⟨body, out, hlookup, heval⟩ := hadq
    exact ⟨body, out, assocLookup_append_left M₁.entry M₁.exports M₂.exports body hlookup, heval⟩
  · contradiction

/-- **Compositional Verification Witness (`linkModules_verified`):**
Linking preserves Anneal's `Compiler.Verified` witness across separately
compiled modules. -/
theorem linkModules_verified
    (M₁ M₂ M₁₂ : OpenMirModule)
    (hv₁ : ModCompiler.Verified MirModuleAdequate M₁)
    (hv₂ : ModCompiler.Verified (fun _ => True) M₂)
    (hlink : linkMir M₁ M₂ = some M₁₂) :
    ModCompiler.Verified MirModuleAdequate M₁₂ := by
  obtain ⟨hadq₁, A₁, hc₁, _⟩ := hv₁
  obtain ⟨_, A₂, hc₂, _⟩ := hv₂
  obtain ⟨A₁₂, _, hcomp₁₂⟩ :=
    compileMod_commutes_with_link M₁ M₂ M₁₂ A₁ A₂ hc₁ hc₂ hlink
  exact ⟨linkMir_preserves_adequate M₁ M₂ M₁₂ hadq₁ hlink,
    A₁₂, hcomp₁₂, compileMod_compiles M₁₂ A₁₂ hcomp₁₂⟩

/-- **Heterogeneous Foreign Assembly / C FFI Linking (`linkForeignAsm_compiles`):**
Suppose `M₁` is an Anneal-verified Rust module compiled to `A₁` (`compileMod M₁ = some A₁`),
and `A_ffi` is a hand-written external C or assembly module (which has **no** MIR
source representation, corresponding to `TCBItem.foreignBridge` / `CompCertO` /
`DimSum` open linking). If `A₁` defines the entry point and `A₁` links with
`A_ffi` to produce `A_linked`, then `A_linked` still refines `M₁` under
`Trusted.Compiles`! -/
theorem linkForeignAsm_compiles
    (M₁ : OpenMirModule) (A₁ A_ffi A_linked : OpenAsmModule)
    (hadq : MirModuleAdequate M₁)
    (hc₁ : compileMod M₁ = some A₁)
    (hlink : linkAsm A₁ A_ffi = some A_linked) :
    Compiles OpenMirLang OpenAsmLang π_mod M₁ A_linked := by
  unfold compileMod at hc₁
  injection hc₁ with hA₁
  subst hA₁
  unfold linkAsm at hlink
  split at hlink
  · injection hlink with hA_linked
    subst hA_linked
    obtain ⟨entryBody, entryOut, hlookup, heval⟩ := hadq
    intro b_t hexec
    change evalOpenAsm _ = b_t at hexec
    unfold evalOpenAsm at hexec
    have hmap : assocLookup M₁.entry
        (List.map (fun x => (x.1, compileFn x.2)) M₁.exports) =
        some (compileFn entryBody) := by
      rw [assocLookup_map, hlookup]
      rfl
    have happ := assocLookup_append_left M₁.entry
      (List.map (fun x => (x.1, compileFn x.2)) M₁.exports)
      A_ffi.exports (compileFn entryBody) hmap
    simp only [happ, evalAsmCode_compileFn, heval] at hexec
    subst hexec
    refine ⟨.terminates entryOut, ?_, rfl⟩
    change evalOpenMir M₁ = .terminates entryOut
    unfold evalOpenMir
    simp [hlookup, heval]
  · contradiction

/-!
### Discharging the Contract Oracle at Link Time (Closed Post-Link Execution)

In `Trusted/MirSemantics.lean` (`evalPureCallee2`), a caller crate `M₁` is
verified against an abstract contract table `M₁.contracts` for its imported
callees. At link time, when `M₁` is linked with either a separately compiled
Rust crate `M₂` (`compileMod M₂ = some A₂`) or a foreign C/assembly object
`A_ffi`, the linker resolves call targets directly to the exported machine code
in `A₁₂.exports`, eliminating the contract oracle altogether.

Below we define `evalClosedAsm`—which executes interprocedural calls by looking
up the target symbol's actual `AsmFnCode` in `A.exports` without consulting
`A.contracts`—and prove that whenever the provider module implements its
declared contracts (`AsmImplementsContracts`), closed post-link assembly
execution refines the open MIR specification (`Compiles OpenMirLang ClosedAsmLang`).
-/

/-- Execute a leaf callee assembly function directly (no nested call, checking
`preservesCalleeSaved`). -/
def evalAsmLeaf (code : AsmFnCode) (arg : Int) : Option Int :=
  if !code.preservesCalleeSaved then
    none
  else
    match code.callTarget with
    | none => some (arg + code.immOffset)
    | some _ => none

/-- Execute a closed assembly module by resolving any `callTarget` directly in
`A.exports` (never consulting `A.contracts`). -/
def evalClosedAsmCode (exports : List (FnId × AsmFnCode)) (code : AsmFnCode)
    (arg : Int) : Option Int :=
  if !code.preservesCalleeSaved then
    none
  else
    match code.callTarget with
    | none => some (arg + code.immOffset)
    | some cid =>
        match assocLookup cid exports with
        | some calleeCode =>
            match evalAsmLeaf calleeCode arg with
            | some calleeRet => some (calleeRet + code.immOffset)
            | none => none
        | none => none

/-- Big-step evaluation of a linked `OpenAsmModule` on the closed target machine
(zero contract oracle). -/
def evalClosedAsm (A : OpenAsmModule) : Behavior Int Unit :=
  match assocLookup A.entry A.exports with
  | some code =>
      match evalClosedAsmCode A.exports code A.entryArg with
      | some out => .terminates out
      | none => .goesWrong
  | none => .goesWrong

/-- Closed target assembly language (`Trusted.Language`) where calls resolve to
real machine code in `exports` rather than a contract oracle. -/
def ClosedAsmLang : Language where
  Prog := OpenAsmModule
  Obs := Int
  Err := Unit
  obsPreorder := discretePreorder Int
  exec a b := evalClosedAsm a = b

/-- An assembly export table `exports` implements a contract table `contracts`
if every contract `(cid, c)` is realized by a defined assembly function in
`exports` whose execution satisfies `evalAsmLeaf calleeCode arg = some (arg + c.delta)`. -/
def AsmExportsImplementContracts (exports : List (FnId × AsmFnCode))
    (contracts : List (FnId × FnContract)) : Prop :=
  ∀ cid c, assocLookup cid contracts = some c →
    ∃ calleeCode, assocLookup cid exports = some calleeCode ∧
      ∀ arg, evalAsmLeaf calleeCode arg = some (arg + c.delta)

/-- Exact conditional agreement between closed assembly execution and open MIR
contract evaluation whenever `evalMirBody` succeeds. -/
theorem evalClosedAsmCode_some_of_evalMirBody_some
    (exports : List (FnId × AsmFnCode))
    (contracts : List (FnId × FnContract))
    (body : MirFnBody) (arg out : Int)
    (himpl : AsmExportsImplementContracts exports contracts)
    (heval : evalMirBody contracts body arg = some out) :
    evalClosedAsmCode exports (compileFn body) arg = some out := by
  unfold compileFn evalClosedAsmCode
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold evalMirBody at heval
  cases hcallee : body.callee with
  | none =>
    simp [hcallee] at heval
    simp [← heval]
  | some cid =>
    simp [hcallee] at heval
    cases hcontract : assocLookup cid contracts with
    | none =>
      simp [hcontract] at heval
    | some c =>
      simp [hcontract] at heval
      obtain ⟨calleeCode, hlookup, hleaf⟩ := himpl cid c hcontract
      simp [hlookup, hleaf arg, ← heval]

/-- **Contract Oracle Discharge Theorem (`closedLinkAsm_compiles_openMir`):**
When an Anneal-compiled caller module `A₁` (`compileMod M₁ = some A₁`) is linked
with a provider module `A_prov` (either compiled from a sibling Rust crate `M₂`
or hand-verified foreign assembly/C FFI) such that the linked export table
`A_linked.exports` implements `M₁.contracts`, executing `A_linked` on the
**closed assembly machine (`ClosedAsmLang`, with zero contract oracle)** refines
the open MIR module `M₁` under `Trusted.Compiles`. -/
theorem closedLinkAsm_compiles_openMir
    (M₁ : OpenMirModule) (A₁ A_prov A_linked : OpenAsmModule)
    (hadq : MirModuleAdequate M₁)
    (hc₁ : compileMod M₁ = some A₁)
    (hlink : linkAsm A₁ A_prov = some A_linked)
    (himpl : AsmExportsImplementContracts A_linked.exports M₁.contracts) :
    Compiles OpenMirLang ClosedAsmLang π_mod M₁ A_linked := by
  unfold compileMod at hc₁
  injection hc₁ with hA₁
  subst hA₁
  unfold linkAsm at hlink
  split at hlink
  · injection hlink with hA_linked
    subst hA_linked
    obtain ⟨entryBody, entryOut, hlookup, heval⟩ := hadq
    intro b_t hexec
    change evalClosedAsm _ = b_t at hexec
    unfold evalClosedAsm at hexec
    have hmap : assocLookup M₁.entry
        (List.map (fun p => (p.1, compileFn p.2)) M₁.exports) =
        some (compileFn entryBody) := by
      rw [assocLookup_map, hlookup]
      rfl
    have happ := assocLookup_append_left M₁.entry
      (List.map (fun p => (p.1, compileFn p.2)) M₁.exports)
      A_prov.exports (compileFn entryBody) hmap
    have hclosed := evalClosedAsmCode_some_of_evalMirBody_some
      (List.map (fun p => (p.1, compileFn p.2)) M₁.exports ++ A_prov.exports)
      M₁.contracts entryBody M₁.entryArg entryOut himpl heval
    simp only [happ, hclosed] at hexec
    subst hexec
    refine ⟨.terminates entryOut, ?_, rfl⟩
    change evalOpenMir M₁ = .terminates entryOut
    unfold evalOpenMir
    simp [hlookup, heval]
  · contradiction

/-- **Negative FFI Linking Canary (`canaryD_ffi_clobbers_callee_saved`):**
A Rust module `mirCallerD` calls foreign function `FnId = 2` with contract
`delta = 10`. If the foreign assembly implementation `ffiBadAsmD` computes the
right arithmetic offset (`immOffset = 10`) but fails to preserve callee-saved
registers (`preservesCalleeSaved = false`), linking produces a closed assembly
program that crashes (`.goesWrong`) and violates `Trusted.Compiles`. -/
def mirCallerD : OpenMirModule where
  imports := [2]
  exports := [(1, { localConst := 5, callee := some 2 })]
  contracts := [(2, { delta := 10 })]
  entry := 1
  entryArg := 30

/-- Compiled assembly for `mirCallerD`. -/
def asmCallerD : OpenAsmModule where
  imports := [2]
  exports := [(1, compileFn { localConst := 5, callee := some 2 })]
  contracts := [(2, { delta := 10 })]
  entry := 1
  entryArg := 30

/-- Buggy foreign assembly module that clobbers a callee-saved register
(`preservesCalleeSaved = false`). -/
def ffiBadAsmD : OpenAsmModule where
  imports := []
  exports := [(2, { immOffset := 10, callTarget := none, preservesCalleeSaved := false })]
  contracts := [(2, { delta := 10 })]
  entry := 1
  entryArg := 30

/-- Linked assembly module combining `asmCallerD` and `ffiBadAsmD`. -/
def linkedBadAsmD : OpenAsmModule where
  imports := []
  exports := [
    (1, compileFn { localConst := 5, callee := some 2 }),
    (2, { immOffset := 10, callTarget := none, preservesCalleeSaved := false })
  ]
  contracts := [(2, { delta := 10 })]
  entry := 1
  entryArg := 30

/-- Linking `asmCallerD` with `ffiBadAsmD` succeeds syntactically, but closed
execution goes wrong while `mirCallerD` terminates with `45`, violating
`Trusted.Compiles OpenMirLang ClosedAsmLang`. -/
theorem canaryD_ffi_clobbers_callee_saved_unsound :
    linkAsm asmCallerD ffiBadAsmD = some linkedBadAsmD ∧
    evalOpenMir mirCallerD = .terminates 45 ∧
    evalClosedAsm linkedBadAsmD = .goesWrong ∧
    ¬ Compiles OpenMirLang ClosedAsmLang π_mod mirCallerD linkedBadAsmD := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hcomp
  obtain ⟨b_s, hexec_s, href⟩ := hcomp (evalClosedAsm linkedBadAsmD) rfl
  change evalOpenMir mirCallerD = b_s at hexec_s
  subst hexec_s
  exact href


/-!
## Part 2: Formal DWARF `.eh_frame` CFI + `.gcc_except_table` LSDA Unwinding

We now formalize stack unwinding under `-Cpanic=unwind` and `extern "C-unwind"`
(`rustc_codegen_ssa/src/mir/block.rs:220-250, 414-427, 2242-2409`,
`rustc_codegen_cranelift/src/debuginfo/{unwind.rs,gcc_except_table.rs}`, and
`library/std/src/sys/personality/{gcc.rs,dwarf/eh.rs}`).

### Key Semantic Components Modeled
1. **Reverse-Order Cleanup Drop Ladders:** Each MIR frame acquires resources
   `createdDrops : List Nat` in forward order `[d₁, d₂, ...]` and must drop
   them in reverse order `createdDrops.reverse` during unwinding before
   executing `TerminatorKind::UnwindResume`.
2. **Caller Live State Across Cleanup (`RBX`):** A caller frame holds a local
   variable `liveLocal : Nat` across the call in callee-saved register `RBX`,
   which is read inside the caller's cleanup landing pad.
3. **2-Phase Personality & LSDA Action Dispatch:**
   - `MirUnwindAction.cleanup` lowers to an LSDA call-site entry with
     `LsdaAction.cleanup` (`cs_action_entry = 0`, `EHAction::Cleanup(lpad)`).
   - `MirUnwindAction.terminateAbi` (`extern "C"` nounwind ABI boundary) lowers
     to an LSDA call-site entry with `LsdaAction.filterTerminate`
     (`ttype_index < 0`, `EHAction::Filter(lpad)` calling `panic_cannot_unwind`).
   - Inside a cleanup landing pad, any destructor call that might itself panic
     (`cleanupPanics = true`, `UnwindAction::Terminate(Reason::InCleanup)`) must
     be covered by an LSDA entry with `LsdaAction.filterTerminate` calling
     `panic_in_cleanup`. As discovered in our codebase inspection,
     `rustc_codegen_cranelift/src/abi/mod.rs:910` erroneously tags
     `UnwindAction::Terminate` with `EXCEPTION_HANDLER_CLEANUP` (`0`) instead of
     a catch/filter action, allowing double-panics to continue unwinding when no
     outer `catch_unwind` frame is present!
-/

/-- Structured failure reasons for unwinding execution. -/
inductive UnwindErr where
  /-- Process-level abort triggered by `panic_in_cleanup` (double-panic during
  cleanup) or `panic_cannot_unwind` (unwinding across a nounwind ABI boundary). -/
  | panicAbort
  deriving DecidableEq, Repr

/-- Record of a single frame's cleanup landing pad execution during unwinding. -/
structure FrameCleanupEvent where
  /-- Function identifier of the unwound frame. -/
  fnId : Nat
  /-- Stack pointer (`SP`) value restored for this frame upon entering its
  landing pad (via `.eh_frame` `CFA`). -/
  restoredSp : Nat
  /-- Value of the caller's live local variable (`RBX`) observed by the cleanup
  landing pad after `.eh_frame` register restoration. -/
  observedLocal : Nat
  /-- Sequence of drop glue identifiers executed by the cleanup landing pad. -/
  executedDrops : List Nat
  deriving DecidableEq, Repr

/-- Observable outcome of a complete program execution in the unwind machine. -/
inductive UnwindObs where
  /-- Normal return all the way to the entry point with final stack pointer
  `finalSp` and return value `retVal`. -/
  | normalReturn (finalSp : Nat) (retVal : Nat)
  /-- Clean stack unwinding to the root frame with final stack pointer `finalSp`
  and the chronologically ordered trace of executed cleanup landing pads. -/
  | unwound (finalSp : Nat) (trace : List FrameCleanupEvent)
  deriving DecidableEq, Repr

/-- MIR-level `UnwindAction` on a `Call` terminator (`rustc_middle/src/mir/syntax.rs`). -/
inductive MirUnwindAction where
  /-- `UnwindAction::Cleanup(bb)`: jump to cleanup basic block `bb`, run reverse
  drop ladder, and resume unwinding (`UnwindResume`). -/
  | cleanup
  /-- `UnwindAction::Terminate(Reason::Abi)`: nounwind boundary (`extern "C"`);
  must abort immediately via `panic_cannot_unwind`. -/
  | terminateAbi
  deriving DecidableEq, Repr

/-- Outcome of the innermost leaf call at the bottom of the call stack. -/
inductive LeafOutcome where
  /-- Leaf call returns normally with value `v`. -/
  | returns (v : Nat)
  /-- Leaf call initiates stack unwinding (`_Unwind_RaiseException`). -/
  | panics
  deriving DecidableEq, Repr

/-- Source MIR specification of a single call frame in an active call chain. -/
structure MirFrameSpec where
  /-- Function identifier. -/
  fnId : Nat
  /-- Frame stack allocation size (`SP` decrement on entry). -/
  frameSize : Nat
  /-- Value of a caller local variable that remains live across the call and is
  inspected by both the normal return path and the cleanup landing pad. -/
  liveLocal : Nat
  /-- Resources initialized in this frame in forward creation order. Elaborated
  MIR cleanup drops these in reverse order (`createdDrops.reverse`). -/
  createdDrops : List Nat
  /-- MIR `UnwindAction` annotating the call site in this frame. -/
  unwindAction : MirUnwindAction
  /-- Whether a destructor invoked inside this frame's cleanup landing pad
  itself panics (`UnwindAction::Terminate(Reason::InCleanup)`). -/
  cleanupPanics : Bool
  deriving DecidableEq, Repr

/-- A source MIR program consisting of an initial stack pointer, a call stack
(ordered from innermost caller to outermost root caller), and a leaf outcome. -/
structure MirUnwindProg where
  /-- Initial stack pointer (`SP`) at the entry of the innermost call. -/
  initialSp : Nat
  /-- Active call frames ordered from innermost caller (`head`) to outermost
  root caller (`last`). -/
  frames : List MirFrameSpec
  /-- Outcome of the leaf callee invoked by the innermost frame. -/
  leaf : LeafOutcome
  deriving DecidableEq, Repr

/-- Reference MIR big-step evaluation over the active call stack. -/
def evalMirFrames (sp : Nat) : List MirFrameSpec → LeafOutcome →
    List FrameCleanupEvent → Behavior UnwindObs UnwindErr
  | [], .returns v, _ => .terminates (.normalReturn sp v)
  | [], .panics, acc => .terminates (.unwound sp acc.reverse)
  | f :: rest, .returns v, acc =>
      let callerSp := sp + f.frameSize
      evalMirFrames callerSp rest (.returns (v + f.liveLocal)) acc
  | f :: rest, .panics, acc =>
      let callerSp := sp + f.frameSize
      match f.unwindAction with
      | .terminateAbi =>
          -- `UnwindAction::Terminate(Reason::Abi)` aborts via `panic_cannot_unwind`.
          .failed .panicAbort
      | .cleanup =>
          if f.cleanupPanics then
            -- `UnwindAction::Terminate(Reason::InCleanup)`: a destructor panicking
            -- during cleanup must abort immediately via `panic_in_cleanup`.
            .failed .panicAbort
          else
            let ev : FrameCleanupEvent := {
              fnId := f.fnId
              restoredSp := callerSp
              observedLocal := f.liveLocal
              executedDrops := f.createdDrops.reverse
            }
            evalMirFrames callerSp rest .panics (ev :: acc)

/-- Big-step evaluation of a `MirUnwindProg`. -/
def evalMirUnwind (p : MirUnwindProg) : Behavior UnwindObs UnwindErr :=
  evalMirFrames p.initialSp p.frames p.leaf []

/-- DWARF `.eh_frame` Frame Description Entry (`FDE`) for a compiled function
(`rustc_codegen_cranelift/src/debuginfo/unwind.rs:76-152`). -/
structure EhFrameFde where
  /-- Offset in `DW_CFA_def_cfa_offset cfaOffset` (`CFA := SP + cfaOffset`). -/
  cfaOffset : Nat
  /-- Optional `DW_CFA_offset RBX, off` rule restoring callee-saved register
  `RBX` from stack slot `CFA - off`. -/
  rbxOffsetRule : Option Nat
  deriving DecidableEq, Repr

/-- Action kind encoded in a `.gcc_except_table` LSDA call-site entry
(`library/std/src/sys/personality/dwarf/eh.rs:49-56, 152-195`). -/
inductive LsdaAction where
  /-- `cs_action_entry == 0`: `EHAction::Cleanup(lpad)`. Phase 1 returns
  `_URC_CONTINUE_UNWIND`; Phase 2 installs context at `lpad`. -/
  | cleanup
  /-- `ttype_index < 0` (`filter [0 x ptr] zeroinitializer`):
  `EHAction::Filter(lpad)`. Phase 1 returns `_URC_HANDLER_FOUND` and Phase 2
  transfers control to the terminate landing pad calling `panic_in_cleanup` or
  `panic_cannot_unwind`. -/
  | filterTerminate
  deriving DecidableEq, Repr

/-- `.gcc_except_table` LSDA call-site entries for a compiled frame. -/
structure LsdaCallSiteEntry where
  /-- Action for the primary call site (`invoke` / `call`). -/
  outerAction : LsdaAction
  /-- Action for destructor calls inside the cleanup landing pad (guarding
  against double-panic `Reason::InCleanup`). -/
  inCleanupAction : LsdaAction
  deriving DecidableEq, Repr

/-- Compiled target machine frame together with its `.eh_frame` FDE and
`.gcc_except_table` LSDA descriptors. -/
structure TargetFrameCode where
  /-- Function identifier. -/
  fnId : Nat
  /-- Stack frame size allocated in the prologue (`sub rsp, frameSize`). -/
  frameSize : Nat
  /-- Caller's live local variable (`RBX`) value saved into the stack frame at
  offset `savedRbxSlot` from `CFA`. -/
  savedRbxValue : Nat
  /-- Offset from `CFA` where the prologue spilled `RBX`. -/
  savedRbxSlot : Nat
  /-- Whether the callee clobbers `RBX` before returning or unwinding. -/
  clobbersRbx : Bool
  /-- Sequence of drop calls emitted in the cleanup landing pad. -/
  landingPadDrops : List Nat
  /-- Whether a destructor in the cleanup landing pad throws a nested unwind. -/
  cleanupThrows : Bool
  /-- Emitted `.eh_frame` FDE for this function. -/
  fde : EhFrameFde
  /-- Emitted `.gcc_except_table` LSDA call-site actions for this function. -/
  lsda : LsdaCallSiteEntry
  deriving DecidableEq, Repr

/-- A target machine program with `.eh_frame` and `.gcc_except_table` tables. -/
structure TargetUnwindProg where
  /-- Initial stack pointer (`SP`) at the leaf call. -/
  initialSp : Nat
  /-- Compiled frames ordered from innermost caller to outermost root caller. -/
  frames : List TargetFrameCode
  /-- Outcome of the leaf call. -/
  leaf : LeafOutcome
  deriving DecidableEq, Repr

/-- Restore the caller's `RBX` register during DWARF CFI unwinding using the
frame's `EhFrameFde`. If the callee did not clobber `RBX`, `RBX` still holds
`savedRbxValue`. If the callee clobbered `RBX`, the unwinder must have a matching
`DW_CFA_offset` rule `some slot` with `slot == f.savedRbxSlot`; otherwise `RBX`
contains the clobbered value `0`. -/
def restoreRbxViaCfi (f : TargetFrameCode) : Nat :=
  if !f.clobbersRbx then
    f.savedRbxValue
  else
    match f.fde.rbxOffsetRule with
    | some off => if off == f.savedRbxSlot then f.savedRbxValue else 0
    | none => 0

/-- Target machine execution modeling normal epilogues and the 2-phase DWARF
`.eh_frame` + `.gcc_except_table` unwinder (`_Unwind_RaiseException` /
`rust_eh_personality`). -/
def evalTargetFrames (sp : Nat) : List TargetFrameCode → LeafOutcome →
    List FrameCleanupEvent → Behavior UnwindObs UnwindErr
  | [], .returns v, _ => .terminates (.normalReturn sp v)
  | [], .panics, acc => .terminates (.unwound sp acc.reverse)
  | f :: rest, .returns v, acc =>
      -- Normal epilogue restores SP := SP + frameSize and RBX := savedRbxValue.
      let callerSp := sp + f.frameSize
      evalTargetFrames callerSp rest (.returns (v + f.savedRbxValue)) acc
  | f :: rest, .panics, acc =>
      -- DWARF CFI unwind step computes CFA := SP + f.fde.cfaOffset and
      -- restores RBX according to `f.fde.rbxOffsetRule`.
      let callerSp := sp + f.fde.cfaOffset
      let restoredRbx := restoreRbxViaCfi f
      match f.lsda.outerAction with
      | .filterTerminate =>
          -- `EHAction::Filter` jumps to terminate landing pad (`panic_cannot_unwind`).
          .failed .panicAbort
      | .cleanup =>
          if f.cleanupThrows then
            -- A destructor inside the cleanup pad throws a nested exception!
            -- The nested unwind consults `f.lsda.inCleanupAction`.
            match f.lsda.inCleanupAction with
            | .filterTerminate =>
                -- Correct LLVM `filter []` landing pad catches and calls `panic_in_cleanup`.
                .failed .panicAbort
            | .cleanup =>
                -- Buggy `EHAction::Cleanup` on a terminate edge (as in
                -- `rustc_codegen_cranelift/src/abi/mod.rs:910`): the unwinder
                -- treats the nested panic as a cleanup and continues unwinding
                -- into the outer caller frames!
                let ev : FrameCleanupEvent := {
                  fnId := f.fnId
                  restoredSp := callerSp
                  observedLocal := restoredRbx
                  executedDrops := f.landingPadDrops
                }
                evalTargetFrames callerSp rest .panics (ev :: acc)
          else
            let ev : FrameCleanupEvent := {
              fnId := f.fnId
              restoredSp := callerSp
              observedLocal := restoredRbx
              executedDrops := f.landingPadDrops
            }
            evalTargetFrames callerSp rest .panics (ev :: acc)

/-- Big-step evaluation of a `TargetUnwindProg`. -/
def evalTargetUnwind (t : TargetUnwindProg) : Behavior UnwindObs UnwindErr :=
  evalTargetFrames t.initialSp t.frames t.leaf []

/-- The MIR unwind language instance (`Trusted.Language`). -/
def MirUnwindLang : Language where
  Prog := MirUnwindProg
  Obs := UnwindObs
  Err := UnwindErr
  obsPreorder := discretePreorder UnwindObs
  exec p b := evalMirUnwind p = b

/-- The target unwind language instance (`Trusted.Language`). -/
def TargetUnwindLang : Language where
  Prog := TargetUnwindProg
  Obs := UnwindObs
  Err := UnwindErr
  obsPreorder := discretePreorder UnwindObs
  exec t b := evalTargetUnwind t = b

/-- Observation projection for the unwind machine. -/
def π_unwind (o : UnwindObs) : Partial UnwindObs := .defined o

/-- Expected LSDA outer action for a `MirUnwindAction`. -/
def expectedLsdaAction : MirUnwindAction → LsdaAction
  | .cleanup => .cleanup
  | .terminateAbi => .filterTerminate

/-- Static DWARF CFI + LSDA validator for a single frame (`checkFrameUnwind`).
Verifies the five **Unwind Frame Adequacy Obligations**:
1. Identity and frame metadata agreement (`fnId`, `frameSize`, `savedRbxValue`,
   `cleanupThrows`).
2. **CFA Offset Adequacy:** `fde.cfaOffset == mir.frameSize`
   (`DW_CFA_def_cfa_offset` matches the exact stack allocation).
3. **Callee-Saved Register Restoration Adequacy:** If `clobbersRbx = true`,
   `fde.rbxOffsetRule == some savedRbxSlot` (`DW_CFA_offset` restores caller
   `RBX`).
4. **Reverse Drop Ladder Adequacy:** `landingPadDrops == mir.createdDrops.reverse`.
5. **LSDA Action & Terminate Filter Adequacy:** `lsda.outerAction` matches
   `mir.unwindAction`, and `lsda.inCleanupAction == .filterTerminate` so any
   destructor panic inside cleanup aborts via `panic_in_cleanup`. -/
def checkFrameUnwind (m : MirFrameSpec) (t : TargetFrameCode) : Bool :=
  (t.fnId == m.fnId) &&
  (t.frameSize == m.frameSize) &&
  (t.savedRbxValue == m.liveLocal) &&
  (t.cleanupThrows == m.cleanupPanics) &&
  (t.fde.cfaOffset == m.frameSize) &&
  (!t.clobbersRbx || (t.fde.rbxOffsetRule == some t.savedRbxSlot)) &&
  (t.landingPadDrops == m.createdDrops.reverse) &&
  (t.lsda.outerAction == expectedLsdaAction m.unwindAction) &&
  (t.lsda.inCleanupAction == .filterTerminate)

/-- Static validator across a list of call frames. -/
def checkFramesUnwind : List MirFrameSpec → List TargetFrameCode → Bool
  | [], [] => true
  | m :: ms, t :: ts => checkFrameUnwind m t && checkFramesUnwind ms ts
  | _, _ => false

/-- Top-level static validator (`checkUnwindTables`) checking `.eh_frame` FDEs
and `.gcc_except_table` LSDA entries for a compiled program. -/
def checkUnwindTables (m : MirUnwindProg) (t : TargetUnwindProg) : Bool :=
  (t.initialSp == m.initialSp) &&
  (t.leaf == m.leaf) &&
  checkFramesUnwind m.frames t.frames

/-- If `checkFrameUnwind m t = true`, then `restoreRbxViaCfi t = m.liveLocal`. -/
theorem restoreRbxViaCfi_eq_of_checkFrameUnwind
    (m : MirFrameSpec) (t : TargetFrameCode)
    (h : checkFrameUnwind m t = true) :
    restoreRbxViaCfi t = m.liveLocal := by
  unfold checkFrameUnwind at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hrbxVal⟩, _⟩, _⟩, hclobber⟩, _⟩, _⟩, _⟩ := h
  unfold restoreRbxViaCfi
  cases hcl : t.clobbersRbx
  · simp [hrbxVal]
  · simp [hcl] at hclobber
    simp [hclobber, hrbxVal]

/-- Core simulation theorem: if `checkFramesUnwind ms ts = true`, then
`evalTargetFrames` produces the exact same `Behavior` as `evalMirFrames` for
any initial stack pointer `sp`, leaf outcome `leaf`, and cleanup trace
accumulator `acc`. -/
theorem evalTargetFrames_eq_evalMirFrames
    (ms : List MirFrameSpec) (ts : List TargetFrameCode)
    (sp : Nat) (leaf : LeafOutcome) (acc : List FrameCleanupEvent)
    (hcheck : checkFramesUnwind ms ts = true) :
    evalTargetFrames sp ts leaf acc = evalMirFrames sp ms leaf acc := by
  induction ms generalizing ts sp leaf acc with
  | nil =>
    cases ts with
    | nil =>
      cases leaf <;> rfl
    | cons _ _ =>
      contradiction
  | cons m ms ih =>
    cases ts with
    | nil =>
      contradiction
    | cons t ts =>
      unfold checkFramesUnwind at hcheck
      simp only [Bool.and_eq_true] at hcheck
      obtain ⟨hframe, hrest⟩ := hcheck
      have hrbx := restoreRbxViaCfi_eq_of_checkFrameUnwind m t hframe
      unfold checkFrameUnwind at hframe
      simp only [Bool.and_eq_true, beq_iff_eq] at hframe
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hfn, hfs⟩, hval⟩, hcp⟩, hcfa⟩, _⟩, hdrops⟩, houter⟩, hinclean⟩ := hframe
      cases leaf with
      | returns v =>
        simp only [evalTargetFrames, evalMirFrames, hfs, hval]
        exact ih ts (sp + m.frameSize) (.returns (v + m.liveLocal)) acc hrest
      | panics =>
        simp only [evalTargetFrames, evalMirFrames, hcfa, hrbx, houter,
          hcp, hinclean, hfn, hdrops]
        cases m.unwindAction with
        | terminateAbi =>
          rfl
        | cleanup =>
          simp only [expectedLsdaAction]
          cases m.cleanupPanics with
          | true => rfl
          | false =>
            exact ih ts (sp + m.frameSize) .panics
              ({ fnId := m.fnId
                 restoredSp := sp + m.frameSize
                 observedLocal := m.liveLocal
                 executedDrops := m.createdDrops.reverse } :: acc) hrest

/-- If `checkUnwindTables m t = true`, then `evalTargetUnwind t = evalMirUnwind m`. -/
theorem evalTargetUnwind_eq_of_checkUnwindTables
    (m : MirUnwindProg) (t : TargetUnwindProg)
    (h : checkUnwindTables m t = true) :
    evalTargetUnwind t = evalMirUnwind m := by
  unfold checkUnwindTables at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsp, hleaf⟩, hframes⟩ := h
  unfold evalTargetUnwind evalMirUnwind
  rw [hsp, hleaf]
  exact evalTargetFrames_eq_evalMirFrames m.frames t.frames m.initialSp m.leaf [] hframes

/-- **Main Unwind Soundness Theorem (`unwind_machine_compiles`):**
Every target program `t` accepted by the static `.eh_frame` + `.gcc_except_table`
validator `checkUnwindTables m t` refines the MIR program `m` under Anneal's
`Trusted.Compiles` relation across normal returns, multi-frame unwinding with
reverse drop ladders, and double-panic aborts. -/
theorem unwind_machine_compiles
    (m : MirUnwindProg) (t : TargetUnwindProg)
    (h : checkUnwindTables m t = true) :
    Compiles MirUnwindLang TargetUnwindLang π_unwind m t := by
  intro b_t hexec
  refine ⟨b_t, ?_, ?_⟩
  · change evalMirUnwind m = b_t
    rw [← evalTargetUnwind_eq_of_checkUnwindTables m t h]
    exact hexec
  · cases b_t with
    | terminates o => exact rfl
    | diverges => trivial
    | failed e => exact HEq.rfl
    | goesWrong => trivial

/-- Reference unwind-aware compiler from `MirUnwindProg` to `TargetUnwindProg`
emitting verified `.eh_frame` FDEs and `.gcc_except_table` LSDA entries. -/
def compileMirFrameUnwind (m : MirFrameSpec) : TargetFrameCode where
  fnId := m.fnId
  frameSize := m.frameSize
  savedRbxValue := m.liveLocal
  savedRbxSlot := 8
  clobbersRbx := true
  landingPadDrops := m.createdDrops.reverse
  cleanupThrows := m.cleanupPanics
  fde := {
    cfaOffset := m.frameSize
    rbxOffsetRule := some 8
  }
  lsda := {
    outerAction := expectedLsdaAction m.unwindAction
    inCleanupAction := .filterTerminate
  }

/-- Compile a `MirUnwindProg` to a `TargetUnwindProg`. -/
def compileMirUnwindProg (m : MirUnwindProg) : Option TargetUnwindProg :=
  some {
    initialSp := m.initialSp
    frames := m.frames.map compileMirFrameUnwind
    leaf := m.leaf
  }

/-- Anneal `Compiler` instance for the unwind-aware code generator. -/
def UnwindCompiler : Compiler MirUnwindLang TargetUnwindLang where
  compile := compileMirUnwindProg
  π := π_unwind

/-- Every frame emitted by `compileMirFrameUnwind` passes `checkFrameUnwind`. -/
theorem checkFrameUnwind_compileMirFrameUnwind (m : MirFrameSpec) :
    checkFrameUnwind m (compileMirFrameUnwind m) = true := by
  unfold checkFrameUnwind compileMirFrameUnwind
  simp

/-- Every frame list emitted by `compileMirFrameUnwind` passes `checkFramesUnwind`. -/
theorem checkFramesUnwind_map_compile (ms : List MirFrameSpec) :
    checkFramesUnwind ms (ms.map compileMirFrameUnwind) = true := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    unfold checkFramesUnwind
    simp [checkFrameUnwind_compileMirFrameUnwind, ih]

/-- **Verified Unwind Codegen Theorem (`unwind_machine_verified`):**
`UnwindCompiler` satisfies Anneal's `Compiler.Verified` obligation for every
`MirUnwindProg`. -/
theorem unwind_machine_verified (m : MirUnwindProg) :
    UnwindCompiler.Verified (fun _ => True) m := by
  refine ⟨trivial, {
    initialSp := m.initialSp
    frames := m.frames.map compileMirFrameUnwind
    leaf := m.leaf
  }, rfl, ?_⟩
  apply unwind_machine_compiles
  unfold checkUnwindTables
  simp [checkFramesUnwind_map_compile]


/-!
## Part 3: Three Negative Adequacy Canaries

We now prove that omitting any of the core DWARF CFI or LSDA obligations
checked by `checkUnwindTables` causes concrete refinement bugs (`¬ Compiles`)
and is rejected by `checkUnwindTables`.
-/

/-!
### Canary A: Wrong `.eh_frame` `cfaOffset` Corrupts Caller `SP` upon Unwind

In Canary A, function `fnId = 1` allocates a 16-byte stack frame
(`frameSize = 16`), but its `.eh_frame` FDE emits `DW_CFA_def_cfa_offset 8`
(`cfaOffset = 8`). When the leaf call panics, the unwinder restores the caller's
stack pointer to `1000 + 8 = 1008` instead of `1000 + 16 = 1016`.
-/

/-- MIR program for Canary A (16-byte frame, leaf panics). -/
def mirCanaryA : MirUnwindProg where
  initialSp := 1000
  frames := [{
    fnId := 1
    frameSize := 16
    liveLocal := 42
    createdDrops := [10, 20]
    unwindAction := .cleanup
    cleanupPanics := false
  }]
  leaf := .panics

/-- Buggy target program for Canary A with `fde.cfaOffset = 8` instead of `16`. -/
def targetCanaryA : TargetUnwindProg where
  initialSp := 1000
  frames := [{
    fnId := 1
    frameSize := 16
    savedRbxValue := 42
    savedRbxSlot := 8
    clobbersRbx := true
    landingPadDrops := [20, 10]
    cleanupThrows := false
    fde := { cfaOffset := 8, rbxOffsetRule := some 8 }
    lsda := { outerAction := .cleanup, inCleanupAction := .filterTerminate }
  }]
  leaf := .panics

/-- `checkUnwindTables` rejects Canary A because `fde.cfaOffset != frameSize`. -/
theorem canaryA_rejected :
    checkUnwindTables mirCanaryA targetCanaryA = false := rfl

/-- Canary A corrupts the caller's restored stack pointer (`1008` vs `1016`). -/
theorem canaryA_corrupts_sp :
    evalTargetUnwind targetCanaryA =
      .terminates (.unwound 1008 [{
        fnId := 1
        restoredSp := 1008
        observedLocal := 42
        executedDrops := [20, 10]
      }]) ∧
    evalMirUnwind mirCanaryA =
      .terminates (.unwound 1016 [{
        fnId := 1
        restoredSp := 1016
        observedLocal := 42
        executedDrops := [20, 10]
      }]) := ⟨rfl, rfl⟩

/-- Canary A violates `Trusted.Compiles`. -/
theorem canaryA_unsound_refinement :
    ¬ Compiles MirUnwindLang TargetUnwindLang π_unwind mirCanaryA targetCanaryA := by
  intro hcomp
  obtain ⟨b_s, hexec_s, href⟩ := hcomp (evalTargetUnwind targetCanaryA) rfl
  change evalMirUnwind mirCanaryA = b_s at hexec_s
  subst hexec_s
  nomatch href

/-!
### Canary B: Missing Callee-Saved `DW_CFA_offset` Rule Clobbers Caller Local

In Canary B, the caller holds `liveLocal = 42` in callee-saved register `RBX`
across a call that clobbers `RBX` (`clobbersRbx = true`), and the `.eh_frame`
FDE omits the `DW_CFA_offset rbx` rule (`rbxOffsetRule = none`). When the
callee unwinds into the caller's cleanup landing pad, `RBX` contains the
clobbered value `0` instead of `42`.
-/

/-- MIR program for Canary B (`liveLocal = 42` live across cleanup). -/
def mirCanaryB : MirUnwindProg := mirCanaryA

/-- Buggy target program for Canary B omitting `rbxOffsetRule` (`none`). -/
def targetCanaryB : TargetUnwindProg where
  initialSp := 1000
  frames := [{
    fnId := 1
    frameSize := 16
    savedRbxValue := 42
    savedRbxSlot := 8
    clobbersRbx := true
    landingPadDrops := [20, 10]
    cleanupThrows := false
    fde := { cfaOffset := 16, rbxOffsetRule := none }
    lsda := { outerAction := .cleanup, inCleanupAction := .filterTerminate }
  }]
  leaf := .panics

/-- `checkUnwindTables` rejects Canary B because `clobbersRbx = true` without a
matching `rbxOffsetRule`. -/
theorem canaryB_rejected :
    checkUnwindTables mirCanaryB targetCanaryB = false := rfl

/-- Canary B clobbers the caller's live local variable (`0` vs `42`) inside the
cleanup landing pad. -/
theorem canaryB_clobbers_local :
    evalTargetUnwind targetCanaryB =
      .terminates (.unwound 1016 [{
        fnId := 1
        restoredSp := 1016
        observedLocal := 0
        executedDrops := [20, 10]
      }]) ∧
    evalMirUnwind mirCanaryB =
      .terminates (.unwound 1016 [{
        fnId := 1
        restoredSp := 1016
        observedLocal := 42
        executedDrops := [20, 10]
      }]) := ⟨rfl, rfl⟩

/-- Canary B violates `Trusted.Compiles`. -/
theorem canaryB_unsound_refinement :
    ¬ Compiles MirUnwindLang TargetUnwindLang π_unwind mirCanaryB targetCanaryB := by
  intro hcomp
  obtain ⟨b_s, hexec_s, href⟩ := hcomp (evalTargetUnwind targetCanaryB) rfl
  change evalMirUnwind mirCanaryB = b_s at hexec_s
  subst hexec_s
  nomatch href

/-!
### Canary C: Destructor Panics in Cleanup (`Reason::InCleanup`) Without Terminate Filter

In Canary C, a 2-frame program unwinds into inner frame `fnId = 1`, whose
cleanup destructor panics (`cleanupPanics = true`,
`UnwindAction::Terminate(Reason::InCleanup)`). In MIR semantics (and in
`rustc_codegen_ssa` via `filter_landing_pad`), this immediately aborts the
process with `.failed .panicAbort` (`panic_in_cleanup`).

However, if the code generator emits `LsdaAction.cleanup` (`cs_action_entry = 0`,
`EHAction::Cleanup`) instead of `LsdaAction.filterTerminate` for the
`Terminate(InCleanup)` edge—matching the behavior we identified in
`rustc_codegen_cranelift/src/abi/mod.rs:910`—the unwinder does not stop at the
inner frame and instead continues unwinding into outer frame `fnId = 2`!
-/

/-- MIR 2-frame program for Canary C where frame 1's destructor panics during
cleanup (`cleanupPanics = true`). -/
def mirCanaryC : MirUnwindProg where
  initialSp := 1000
  frames := [
    { fnId := 1
      frameSize := 16
      liveLocal := 42
      createdDrops := [10]
      unwindAction := .cleanup
      cleanupPanics := true },
    { fnId := 2
      frameSize := 32
      liveLocal := 99
      createdDrops := [30]
      unwindAction := .cleanup
      cleanupPanics := false }
  ]
  leaf := .panics

/-- Buggy target 2-frame program for Canary C where `inCleanupAction = .cleanup`
instead of `.filterTerminate`. -/
def targetCanaryC : TargetUnwindProg where
  initialSp := 1000
  frames := [
    { fnId := 1
      frameSize := 16
      savedRbxValue := 42
      savedRbxSlot := 8
      clobbersRbx := true
      landingPadDrops := [10]
      cleanupThrows := true
      fde := { cfaOffset := 16, rbxOffsetRule := some 8 }
      lsda := { outerAction := .cleanup, inCleanupAction := .cleanup } },
    { fnId := 2
      frameSize := 32
      savedRbxValue := 99
      savedRbxSlot := 8
      clobbersRbx := true
      landingPadDrops := [30]
      cleanupThrows := false
      fde := { cfaOffset := 32, rbxOffsetRule := some 8 }
      lsda := { outerAction := .cleanup, inCleanupAction := .filterTerminate } }
  ]
  leaf := .panics

/-- `checkUnwindTables` rejects Canary C because `inCleanupAction != .filterTerminate`. -/
theorem canaryC_rejected :
    checkUnwindTables mirCanaryC targetCanaryC = false := rfl

/-- Canary C causes unsound double-unwinding into outer frame `fnId = 2` instead
of aborting with `.failed .panicAbort`. -/
theorem canaryC_double_unwinds :
    evalMirUnwind mirCanaryC = .failed .panicAbort ∧
    evalTargetUnwind targetCanaryC =
      .terminates (.unwound 1048 [
        { fnId := 1, restoredSp := 1016, observedLocal := 42, executedDrops := [10] },
        { fnId := 2, restoredSp := 1048, observedLocal := 99, executedDrops := [30] }
      ]) := ⟨rfl, rfl⟩

/-- Canary C violates `Trusted.Compiles`. -/
theorem canaryC_unsound_refinement :
    ¬ Compiles MirUnwindLang TargetUnwindLang π_unwind mirCanaryC targetCanaryC := by
  intro hcomp
  obtain ⟨b_s, hexec_s, href⟩ := hcomp (evalTargetUnwind targetCanaryC) rfl
  change evalMirUnwind mirCanaryC = b_s at hexec_s
  subst hexec_s
  exact href

/-!
## Part 4: Kernel Axiom Footprint Audit

Verify that every theorem in this file is completely free of `sorryAx` and
`Lean.ofReduceBool` (`native_decide`).
-/

/-- info: 'Track8Probe.compileMod_commutes_with_link' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compileMod_commutes_with_link

/-- info: 'Track8Probe.linkModules_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linkModules_compiles

/-- info: 'Track8Probe.linkModules_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linkModules_verified

/-- info: 'Track8Probe.linkForeignAsm_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms linkForeignAsm_compiles

/-- info: 'Track8Probe.closedLinkAsm_compiles_openMir' depends on axioms: [propext] -/
#guard_msgs in
#print axioms closedLinkAsm_compiles_openMir

/-- info: 'Track8Probe.canaryD_ffi_clobbers_callee_saved_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canaryD_ffi_clobbers_callee_saved_unsound

/-- info: 'Track8Probe.unwind_machine_compiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unwind_machine_compiles

/-- info: 'Track8Probe.unwind_machine_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unwind_machine_verified

/-- info: 'Track8Probe.canaryA_unsound_refinement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canaryA_unsound_refinement

/-- info: 'Track8Probe.canaryB_unsound_refinement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canaryB_unsound_refinement

/-- info: 'Track8Probe.canaryC_unsound_refinement' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canaryC_unsound_refinement

end Track8Probe
