import ToyLink.Statements

/-!
# Definition examples, non-vacuity witnesses, and positive controls

All declarations in this file are fully proved without `sorry` (depending only on
standard Lean axioms).
Provides:
- at least one positive (`_pos`) and one negative (`_neg`) example for every core
  definition in `ToyLink.Defs` and `ToyLink.Spec`;
- a complete non-vacuity witness for every main theorem;
- a complete positive control for every counterexample / negative result.
-/

namespace Toy.Link.Examples

open Toy.Link

/-! ## Shared helper modules and specifications -/

/-- Minimal closed single-function identity module. -/
def idMod : Module := [(0, .var)]

/-- Module with two functions where `0` returns `1` and `1` returns `2`. -/
def twoFnMod : Module := [(0, .lit 1), (1, .lit 2)]

/-- Module defining `1` as `var + 10`. -/
def addTenMod : Module := [(1, .add .var (.lit 10))]

/-- Open module whose function `0` calls external function `1`. -/
def openCallerMod : Module := [(0, .call 1 .var)]

/-- Nondeterministic module choosing between `0` and `1`. -/
def choose01Mod : Module := [(0, .choose (.lit 0) (.lit 1))]

/-- Nondeterministic module choosing between `0`, `1`, and `2`. -/
def choose012Mod : Module := [(0, .choose (.lit 0) (.choose (.lit 1) (.lit 2)))]

/-- Deterministic module returning `0`. -/
def const0Mod : Module := [(0, .lit 0)]

/-- Deterministic module returning `1`. -/
def const1Mod : Module := [(0, .lit 1)]

/-- Non-terminating self-recursive loop module. -/
def selfLoopMod : Module := [(0, .call 0 .var)]

/-- Empty specification environment (false precondition everywhere). -/
def falseSpec : SpecEnv := fun _ => { pre := fun _ => False, post := fun _ _ => False }

/-- Trivial specification on function `0` (pre `True`, post `True`). -/
def trivZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ _ => True }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Exact equality specification on function `0`: `v = x`. -/
def idZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun x v => v = x }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Constant-zero specification on function `0`: `v = 0`. -/
def zeroOutSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Helper for constant-folding `0 + b ↦ b` and `a + 0 ↦ a`. -/
def foldAdd (a b : Expr) : Expr :=
  if a = .lit 0 then b else if b = .lit 0 then a else .add a b

/-- Constant-fold `x + 0 ↦ x` and `0 + x ↦ x` inside an expression. -/
def constFoldExpr : Expr → Expr
  | .lit n => .lit n
  | .var => .var
  | .add e₁ e₂ => foldAdd (constFoldExpr e₁) (constFoldExpr e₂)
  | .sub e₁ e₂ => .sub (constFoldExpr e₁) (constFoldExpr e₂)
  | .mul e₁ e₂ => .mul (constFoldExpr e₁) (constFoldExpr e₂)
  | .ifLe e₁ e₂ eT eE =>
    .ifLe (constFoldExpr e₁) (constFoldExpr e₂) (constFoldExpr eT) (constFoldExpr eE)
  | .choose e₁ e₂ => .choose (constFoldExpr e₁) (constFoldExpr e₂)
  | .call fn eArg => .call fn (constFoldExpr eArg)

/-- Non-identity module compiler applying `constFoldExpr` to every body. -/
def constFoldPass (M : Module) : Module :=
  M.map fun (fn, body) => (fn, constFoldExpr body)

/-! ## Positive and negative examples for every definition in `Defs.lean` -/

theorem lookup_pos : idMod.lookup 0 = some .var := rfl
theorem lookup_neg : idMod.lookup 1 = none := rfl

theorem defines_pos : idMod.Defines 0 := rfl
theorem defines_neg : ¬ idMod.Defines 1 := by decide

theorem sameDom_pos : SameDom choose01Mod const0Mod := by
  intro fn
  simp [Module.Defines, Module.lookup, choose01Mod, const0Mod]

theorem sameDom_neg : ¬ SameDom idMod twoFnMod := by
  intro h
  have h1 : twoFnMod.Defines 1 := by decide
  have h0 : idMod.Defines 1 := (h 1).2 h1
  exact defines_neg h0

theorem linkable_pos : Linkable openCallerMod addTenMod := by decide
theorem linkable_neg : ¬ Linkable idMod twoFnMod := by decide

theorem linkableBool_pos : linkableBool openCallerMod addTenMod = true := rfl
theorem linkableBool_neg : linkableBool idMod twoFnMod = false := rfl

theorem link_pos : (link openCallerMod addTenMod).lookup 1 = some (.add .var (.lit 10)) := rfl
theorem link_neg : (link openCallerMod addTenMod).lookup 2 = none := rfl

theorem calleesIn_pos : Expr.CalleesIn idMod.Defines (.add .var (.call 0 .var)) := by
  refine ⟨trivial, ?_, trivial⟩
  decide

theorem calleesIn_neg : ¬ Expr.CalleesIn idMod.Defines (.call 1 .var) := by
  intro h
  exact defines_neg h.1

theorem calleesInBool_pos :
    Expr.calleesInBool (fun fn => (idMod.lookup fn).isSome) (.call 0 .var) = true := rfl
theorem calleesInBool_neg :
    Expr.calleesInBool (fun fn => (idMod.lookup fn).isSome) (.call 1 .var) = false := rfl

theorem closedModule_pos : ClosedModule idMod := by decide
theorem closedModule_neg : ¬ ClosedModule openCallerMod := by decide

theorem closedModuleBool_pos : closedModuleBool idMod = true := rfl
theorem closedModuleBool_neg : closedModuleBool openCallerMod = false := rfl

theorem evalExprWith_pos :
    .val 42 ∈ evalExprWith (fun _ _ => [.val 42]) 0 (.call 1 .var) := by decide
theorem evalExprWith_neg :
    .val 0 ∉ evalExprWith (fun _ _ => [.val 42]) 0 (.call 1 .var) := by decide

theorem eval_pos : eval 1 idMod 0 7 = [.val 7] := rfl
theorem eval_neg : eval 1 idMod 1 7 = [.undefinedCall] := rfl

theorem hasBehavior_pos : HasBehavior 0 choose01Mod 1 0 (.val 1) := by decide
theorem hasBehavior_neg : ¬ HasBehavior 0 choose01Mod 1 0 (.val 2) := by decide

/-- Choosing `{0, 1}` is refined by deterministic `0` at entry `0`. -/
theorem entryRefines_pos : EntryRefines 0 choose01Mod const0Mod := by
  intro fuel arg out h
  cases fuel with
  | zero => simpa [HasBehavior, eval] using h
  | succ n =>
    simp only [HasBehavior, eval, const0Mod, Module.lookup, ite_true,
      evalExprWith, List.mem_singleton] at h
    subst h
    simp [HasBehavior, eval, choose01Mod, Module.lookup, evalExprWith]

/-- Deterministic `0` is not refined by deterministic `1` at entry `0`. -/
theorem entryRefines_neg : ¬ EntryRefines 0 const0Mod const1Mod := by
  intro h
  have h1 : HasBehavior 0 const1Mod 1 0 (.val 1) := by decide
  have h0 : HasBehavior 0 const0Mod 1 0 (.val 1) := h 1 0 (.val 1) h1
  exact absurd h0 (by decide)

/-- Resolving `choose 0 1` to `0` is a contextual refinement. -/
theorem ctxRefines_pos : CtxRefines choose01Mod const0Mod := by
  refine ctxRefines_of_pointwise_body_subset ?_
  intro fn
  by_cases h0 : fn = 0
  · subst h0
    right
    refine ⟨.choose (.lit 0) (.lit 1), .lit 0, rfl, rfl, fun _ _ _ x o ho => ?_⟩
    simp only [evalExprWith, List.mem_singleton] at ho
    subst ho
    simp [evalExprWith]
  · left
    simp [choose01Mod, const0Mod, Module.lookup, Ne.symm h0]

theorem ctxRefines_neg : ¬ CtxRefines const0Mod const1Mod := by
  intro h
  have h1 : HasBehavior 0 (link [] const1Mod) 1 0 (.val 1) := by decide
  have h0 : HasBehavior 0 (link [] const0Mod) 1 0 (.val 1) :=
    h [] (by decide) (by decide) 0 1 0 (.val 1) h1
  exact absurd h0 (by decide)

/-- Contextual refinement is not symmetric (`choose01Mod ⊑ const0Mod` holds, converse fails). -/
theorem cex_ctxRefines_not_symm :
    CtxRefines choose01Mod const0Mod ∧ ¬ CtxRefines const0Mod choose01Mod := by
  refine ⟨ctxRefines_pos, ?_⟩
  intro h
  have h1 : HasBehavior 0 (link [] choose01Mod) 1 0 (.val 1) := by decide
  have h0 : HasBehavior 0 (link [] const0Mod) 1 0 (.val 1) :=
    h [] (by decide) (by decide) 0 1 0 (.val 1) h1
  exact absurd h0 (by decide)

/-- Fuel sensitivity at a single fuel: adding a wrapper call shifts `fuel = 1` to
`.outOfFuel`. The full consequence for contextual refinement (failure in both directions)
is `Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`. -/
theorem extra_call_changes_fuel_one_outcome :
    let direct : Module := [(0, .lit 0), (1, .lit 0)]
    let viaCall : Module := [(0, .call 1 .var), (1, .lit 0)]
    SameDom direct viaCall ∧
    HasBehavior 0 viaCall 1 0 .outOfFuel ∧
    ¬ HasBehavior 0 direct 1 0 .outOfFuel := by
  refine ⟨?_, by decide, by decide⟩
  intro fn
  by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
    simp [Module.Defines, Module.lookup, h0, h1, Ne.symm]

/-- Standalone refinement admits resolving `choose 0 1` to `0`. -/
theorem standaloneRefines_pos : StandaloneRefines choose01Mod const0Mod :=
  standaloneRefines_of_ctxRefines ctxRefines_pos

/-- Standalone refinement rejects changing the returned constant. -/
theorem standaloneRefines_neg : ¬ StandaloneRefines const0Mod const1Mod :=
  fun h => entryRefines_neg (h 0)

/-- A self-loop may diverge: `outOfFuel` at every fuel. -/
theorem mayDiverge_pos : MayDiverge selfLoopMod 0 0 := by
  intro fuel
  induction fuel with
  | zero => simp [HasBehavior, eval]
  | succ n ih =>
    simpa [HasBehavior, eval, selfLoopMod, Module.lookup, evalExprWith] using ih

/-- A constant function cannot diverge: at fuel `1` it returns. -/
theorem mayDiverge_neg : ¬ MayDiverge const0Mod 0 0 := fun h =>
  absurd (h 1) (by decide)

/-! ## Positive and negative examples for every definition in `Spec.lean` -/

theorem fnPartialCorrect_pos : FnPartialCorrect idMod 0 (idZeroSpec 0) := by
  intro fuel x out _ hbeh
  cases fuel with
  | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
  | succ n =>
    simp [HasBehavior, eval, idMod, Module.lookup, evalExprWith] at hbeh
    exact .inr ⟨x, hbeh, rfl⟩

theorem fnPartialCorrect_neg : ¬ FnPartialCorrect const1Mod 0 (zeroOutSpec 0) := by
  intro h
  rcases h 1 0 (.val 1) trivial (by decide) with h1 | ⟨v, h2, hpost⟩
  · cases h1
  · cases h2
    cases hpost

theorem programPartialCorrect_pos : ProgramPartialCorrect idMod idZeroSpec := by
  intro fn
  by_cases h0 : fn = 0
  · subst h0; exact fnPartialCorrect_pos
  · intro fuel x out hpre _
    simp [idZeroSpec, h0] at hpre

theorem programPartialCorrect_neg : ¬ ProgramPartialCorrect const1Mod zeroOutSpec :=
  fun h => fnPartialCorrect_neg (h 0)

theorem fnTotalCorrect_pos : FnTotalCorrect idMod 0 (idZeroSpec 0) := by
  intro x _
  refine ⟨1, fun out hbeh => ?_⟩
  simp [HasBehavior, eval, idMod, Module.lookup, evalExprWith] at hbeh
  exact ⟨x, hbeh, rfl⟩

theorem fnTotalCorrect_neg : ¬ FnTotalCorrect selfLoopMod 0 (trivZeroSpec 0) := by
  intro h
  obtain ⟨fuel, htot⟩ := h 0 trivial
  have hof : HasBehavior 0 selfLoopMod fuel 0 .outOfFuel := by
    clear htot
    induction fuel with
    | zero => simp [HasBehavior, eval]
    | succ n ih =>
      simpa [HasBehavior, eval, selfLoopMod, Module.lookup, evalExprWith] using ih
  rcases htot .outOfFuel hof with ⟨_, heq, _⟩
  cases heq

theorem programTotalCorrect_pos : ProgramTotalCorrect idMod idZeroSpec := by
  intro fn
  by_cases h0 : fn = 0
  · subst h0; exact fnTotalCorrect_pos
  · intro x hpre; simp [idZeroSpec, h0] at hpre

theorem programTotalCorrect_neg : ¬ ProgramTotalCorrect selfLoopMod trivZeroSpec :=
  fun h => fnTotalCorrect_neg (h 0)

theorem specsImplemented_pos : SpecsImplemented idMod idZeroSpec := by
  intro fn x hpre
  by_cases h0 : fn = 0
  · subst h0; decide
  · simp [idZeroSpec, h0] at hpre

theorem specsImplemented_neg : ¬ SpecsImplemented const1Mod
    (fun fn => if fn = 1 then { pre := fun _ => True, post := fun _ _ => True }
               else { pre := fun _ => False, post := fun _ _ => False }) := by
  intro h
  have hdef : const1Mod.Defines 1 := h 1 0 (by simp)
  exact absurd hdef (by decide)

theorem wpPartial_pos : wpPartial idZeroSpec 5 (.call 0 .var) (fun v => v = 5) := by
  simp [wpPartial, idZeroSpec]

theorem wpPartial_neg : ¬ wpPartial idZeroSpec 5 (.call 0 .var) (fun v => v = 6) := by
  simp [wpPartial, idZeroSpec]

theorem bodyVerifiedPartial_pos : BodyVerifiedPartial idZeroSpec .var (idZeroSpec 0) := by
  intro x _
  simp [wpPartial, idZeroSpec]

theorem bodyVerifiedPartial_neg : ¬ BodyVerifiedPartial idZeroSpec (.lit 1) (zeroOutSpec 0) := by
  intro h
  have h0 := h 0 trivial
  simp [wpPartial, zeroOutSpec] at h0

theorem moduleVerifiedPartial_pos : ModuleVerifiedPartial idMod idZeroSpec idZeroSpec := by
  intro fn body hlu
  simp only [idMod, Module.lookup] at hlu
  by_cases h0 : fn = 0
  · subst h0
    simp only [ite_true, Option.some.injEq] at hlu
    subst hlu
    exact bodyVerifiedPartial_pos
  · simp [Ne.symm h0] at hlu

theorem moduleVerifiedPartial_neg : ¬ ModuleVerifiedPartial const1Mod idZeroSpec zeroOutSpec := by
  intro h
  have hb := h 0 (.lit 1) rfl 0 trivial
  simp [wpPartial, zeroOutSpec] at hb

theorem wpCallDec_pos :
    wpCallDec Nat.lt (fun _ x => x.toNat) trivZeroSpec 3 2 (.call 0 (.sub .var (.lit 1)))
      (fun _ => True) := by
  simp only [wpCallDec, trivZeroSpec, ite_true]
  refine ⟨?_, trivial, fun _ _ => trivial⟩
  change Int.toNat (2 - 1) < 3
  omega

theorem wpCallDec_neg :
    ¬ wpCallDec Nat.lt (fun _ x => x.toNat) trivZeroSpec 2 2 (.call 0 .var) (fun _ => True) := by
  simp only [wpCallDec, trivZeroSpec, ite_true]
  intro h
  exact Nat.lt_irrefl _ h.1

theorem bodyVerifiedTotal_pos :
    BodyVerifiedTotal Nat.lt (fun _ x => x.toNat) trivZeroSpec 0 (.lit 0) (trivZeroSpec 0) := by
  intro x _
  simp [wpCallDec, trivZeroSpec]

theorem bodyVerifiedTotal_neg :
    ¬ BodyVerifiedTotal Nat.lt (fun _ x => x.toNat) trivZeroSpec 0 (.call 0 .var) (trivZeroSpec 0) := by
  intro h
  have h0 := h 0 trivial
  simp only [wpCallDec, trivZeroSpec, ite_true] at h0
  exact Nat.lt_irrefl _ h0.1

theorem moduleVerifiedTotal_pos :
    ModuleVerifiedTotal Nat.lt (fun _ x => x.toNat) const0Mod zeroOutSpec zeroOutSpec := by
  intro fn body hlu
  simp only [const0Mod, Module.lookup] at hlu
  by_cases h0 : fn = 0
  · subst h0
    simp only [ite_true, Option.some.injEq] at hlu
    subst hlu
    intro x _
    simp [wpCallDec, zeroOutSpec]
  · simp [Ne.symm h0] at hlu

theorem moduleVerifiedTotal_neg :
    ¬ ModuleVerifiedTotal Nat.lt (fun _ x => x.toNat) selfLoopMod trivZeroSpec trivZeroSpec := by
  intro h
  have h0 := h 0 (.call 0 .var) rfl 0 trivial
  simp only [wpCallDec, trivZeroSpec, ite_true] at h0
  exact Nat.lt_irrefl _ h0.1

private def nonNegSpec : FnSpec := { pre := fun x => x ≥ 0, post := fun x v => v ≥ x }
private def allAddTenSpec : FnSpec := { pre := fun _ => True, post := fun x v => v = x + 10 }
private def geTenSpec : FnSpec := { pre := fun x => x ≥ 10, post := fun x v => v = x + 10 }

theorem weakensPre_pos : WeakensPre nonNegSpec allAddTenSpec := fun _ _ => trivial
theorem weakensPre_neg : ¬ WeakensPre nonNegSpec geTenSpec := by
  intro h
  have hge : (0 : Int) ≥ 10 := h 0 (by dsimp [nonNegSpec]; omega)
  omega

theorem strengthensPostUnderPre_pos : StrengthensPostUnderPre nonNegSpec allAddTenSpec := by
  intro x v hx hv
  dsimp [nonNegSpec, allAddTenSpec] at hx hv ⊢
  omega

theorem strengthensPostUnderPre_neg : ¬ StrengthensPostUnderPre allAddTenSpec nonNegSpec := by
  intro h
  have : (0 : Int) = 0 + 10 := h 0 0 trivial (by dsimp [nonNegSpec]; omega)
  omega

theorem preservesVerifiedPartial_pos : PreservesVerifiedPartial id trivZeroSpec :=
  fun _ h => h

theorem preservesVerifiedPartial_neg :
    ¬ PreservesVerifiedPartial (fun _ => [(0, .lit 1)]) zeroOutSpec := by
  intro h
  have hVer0 : ModuleVerifiedPartial const0Mod zeroOutSpec zeroOutSpec := by
    intro fn body hlu x _
    by_cases he : fn = 0
    · subst he
      simp only [const0Mod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpPartial, zeroOutSpec]
    · simp [const0Mod, Module.lookup, Ne.symm he] at hlu
  have h0 := h const0Mod hVer0 0 (.lit 1) rfl 0 trivial
  simp [wpPartial, zeroOutSpec] at h0

theorem preservesDefines_pos : PreservesDefines constFoldPass := by
  intro M fn hdef
  induction M with
  | nil => simp [Module.Defines, Module.lookup] at hdef
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [constFoldPass, List.map_cons, Module.Defines, Module.lookup] at hdef ⊢
    by_cases hk : k = fn
    · simp [hk]
    · simp only [hk, ite_false] at hdef ⊢
      exact ih hdef

theorem preservesDefines_neg : ¬ PreservesDefines (fun _ => []) := by
  intro h
  have hdef : Module.Defines ([] : Module) 0 := h idMod 0 defines_pos
  exact absurd hdef (by decide)

/-- `mixEnv` uses the module's own guarantee at a name the module defines. -/
theorem mixEnv_pos : mixEnv idMod idZeroSpec zeroOutSpec 0 = idZeroSpec 0 := by
  simp [mixEnv, defines_pos]

/-- `mixEnv` ignores the external interface at a name the module defines: at `0` the
assumption is `idZeroSpec 0` (`v = x`), not `zeroOutSpec 0` (`v = 0`). -/
theorem mixEnv_neg :
    ¬ (mixEnv idMod idZeroSpec zeroOutSpec 0).post 1 0 ∧ (zeroOutSpec 0).post 1 0 := by
  simp [mixEnv, defines_pos, idZeroSpec, zeroOutSpec]

/-- `mixEnv` uses the external interface at a name the module does not define. -/
theorem mixEnv_pos_external : mixEnv idMod idZeroSpec zeroOutSpec 1 = zeroOutSpec 1 := by
  simp [mixEnv, defines_neg]

/-- A pass that replaces every body by `lit 0`; it keeps every defined name. -/
def zeroBodies (M : Module) : Module := M.map fun p => (p.1, Expr.lit 0)

/-- `PassCtxRefines` rejects a pass that changes a returned value (`1 ↦ 0`). -/
theorem passCtxRefines_neg : ¬ PassCtxRefines zeroBodies := by
  intro h
  have h1 : HasBehavior 0 (link [] (zeroBodies const1Mod)) 1 0 (.val 0) := by decide
  exact absurd (h const1Mod [] (by decide) (by decide) 0 1 0 _ h1) (by decide)

/-! ## Non-vacuity witnesses for every main theorem -/

/-- Non-vacuity for `ctxRefines_refl` on a nontrivial open module. -/
theorem nonvacuous_ctxRefines_refl : CtxRefines openCallerMod openCallerMod :=
  ctxRefines_refl openCallerMod

private theorem ctxRefines_choose012_choose01 : CtxRefines choose012Mod choose01Mod := by
  refine ctxRefines_of_pointwise_body_subset ?_
  intro fn
  by_cases h0 : fn = 0
  · subst h0
    right
    refine ⟨.choose (.lit 0) (.choose (.lit 1) (.lit 2)), .choose (.lit 0) (.lit 1), rfl, rfl,
      fun _ _ _ x o ho => ?_⟩
    simp only [evalExprWith, List.mem_append, List.mem_singleton] at ho ⊢
    rcases ho with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · left
    simp [choose012Mod, choose01Mod, Module.lookup, Ne.symm h0]

/-- Non-vacuity for `ctxRefines_trans`: strict 3-module chain
`choose {0, 1, 2} ⊑ choose {0, 1} ⊑ const 0`. -/
theorem nonvacuous_ctxRefines_trans :
    CtxRefines choose012Mod choose01Mod ∧ CtxRefines choose01Mod const0Mod :=
  ⟨ctxRefines_choose012_choose01, ctxRefines_pos⟩

private def modA : Module := [(0, .call 1 .var)]
private def modB : Module := [(1, .choose (.lit 0) (.lit 1))]
private def modB' : Module := [(1, .lit 0)]

private theorem ctxRefines_modB_modB' : CtxRefines modB modB' := by
  refine ctxRefines_of_pointwise_body_subset ?_
  intro fn
  by_cases h1 : fn = 1
  · subst h1
    right
    refine ⟨.choose (.lit 0) (.lit 1), .lit 0, rfl, rfl, fun _ _ _ x o ho => ?_⟩
    simp only [evalExprWith, List.mem_singleton] at ho
    subst ho
    simp [evalExprWith]
  · left
    simp [modB, modB', Module.lookup, Ne.symm h1]

/-- Non-vacuity for `ctxRefines_link_congr`: two disjoint cross-calling modules. -/
theorem nonvacuous_ctxRefines_link_congr :
    CtxRefines modA modA ∧ CtxRefines modB modB' ∧ Linkable modA modB :=
  ⟨ctxRefines_refl modA, ctxRefines_modB_modB', by decide⟩

/-- Mutually recursive `even` (`0`) and `odd` (`1`) module pair. -/
def evenMod : Module := [(0, .ifLe .var (.lit 0) (.lit 1) (.call 1 (.sub .var (.lit 1))))]
def oddMod : Module := [(1, .ifLe .var (.lit 0) (.lit 0) (.call 0 (.sub .var (.lit 1))))]
def evenOddProg : Module := link evenMod oddMod

/-- Specification for `even` and `odd`: returns `0` or `1` on `x ≥ 0` matching parity. -/
def evenOddSpec : SpecEnv := fun fn =>
  if fn = 0 then
    { pre := fun x => x ≥ 0
      post := fun x v => (x % 2 = 0 ∧ v = 1) ∨ (x % 2 = 1 ∧ v = 0) }
  else if fn = 1 then
    { pre := fun x => x ≥ 0
      post := fun x v => (x % 2 = 1 ∧ v = 1) ∨ (x % 2 = 0 ∧ v = 0) }
  else
    { pre := fun _ => False, post := fun _ _ => False }

theorem evenOdd_specsImplemented : SpecsImplemented evenOddProg evenOddSpec := by
  intro fn x hpre
  by_cases h0 : fn = 0
  · subst h0; decide
  · by_cases h1 : fn = 1
    · subst h1; decide
    · simp [evenOddSpec, h0, h1] at hpre

theorem evenOdd_moduleVerifiedPartial :
    ModuleVerifiedPartial evenOddProg evenOddSpec evenOddSpec := by
  intro fn body hlu x hpre
  by_cases h0 : fn = 0
  · subst h0
    simp only [evenOddProg, link, evenMod, oddMod, List.cons_append, List.nil_append,
      Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp only [evenOddSpec, ite_true] at hpre ⊢
    simp only [wpPartial]
    refine ⟨fun hle => ?_, fun hgt => ?_⟩
    · have hx0 : x = 0 := by omega
      subst hx0
      left
      decide
    · simp only [evenOddSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
      refine ⟨by omega, fun vRes hres => ?_⟩
      obtain ⟨k, rfl | rfl⟩ : ∃ k : Int, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
      · have hm0 : (2 * k) % 2 = 0 := by omega
        have hm1 : (2 * k - 1) % 2 = 1 := by omega
        simp [hm0, hm1] at hres ⊢
        exact hres
      · have hm0 : (2 * k + 1) % 2 = 1 := by omega
        simp [hm0] at hres ⊢
        exact hres
  · by_cases h1 : fn = 1
    · subst h1
      simp only [evenOddProg, link, evenMod, oddMod, List.cons_append, List.nil_append,
        Module.lookup, show ¬ ((0 : Nat) = 1) by decide, ite_false, ite_true,
        Option.some.injEq] at hlu
      subst hlu
      simp only [evenOddSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true] at hpre ⊢
      simp only [wpPartial]
      refine ⟨fun hle => ?_, fun hgt => ?_⟩
      · have hx0 : x = 0 := by omega
        subst hx0
        right
        decide
      · simp only [evenOddSpec, ite_true]
        refine ⟨by omega, fun vRes hres => ?_⟩
        obtain ⟨k, rfl | rfl⟩ : ∃ k : Int, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
        · have hm0 : (2 * k) % 2 = 0 := by omega
          have hm1 : (2 * k - 1) % 2 = 1 := by omega
          simp [hm0, hm1] at hres ⊢
          exact hres
        · have hm0 : (2 * k + 1) % 2 = 1 := by omega
          simp [hm0] at hres ⊢
          exact hres
    · simp [evenOddProg, link, evenMod, oddMod, Module.lookup, Ne.symm h0, Ne.symm h1] at hlu

/-- Non-vacuity for `ag_partial_correctness` on mutually recursive `evenOddProg`. -/
theorem nonvacuous_ag_partial_correctness :
    SpecsImplemented evenOddProg evenOddSpec ∧
    ModuleVerifiedPartial evenOddProg evenOddSpec evenOddSpec :=
  ⟨evenOdd_specsImplemented, evenOdd_moduleVerifiedPartial⟩

/-- Non-vacuity for `ag_total_correctness_of_wf_call_measure` on mutually recursive `evenOddProg`
with `WellFounded Nat.lt` and measure `μ _ x := x.toNat`. -/
theorem nonvacuous_ag_total_correctness :
    WellFounded Nat.lt ∧
    SpecsImplemented evenOddProg evenOddSpec ∧
    ModuleVerifiedTotal Nat.lt (fun _ x => x.toNat) evenOddProg evenOddSpec evenOddSpec := by
  refine ⟨Nat.lt_wfRel.wf, evenOdd_specsImplemented, ?_⟩
  intro fn body hlu x hpre
  by_cases h0 : fn = 0
  · subst h0
    simp only [evenOddProg, link, evenMod, oddMod, List.cons_append, List.nil_append,
      Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp only [evenOddSpec, ite_true] at hpre ⊢
    simp only [wpCallDec]
    refine ⟨fun hle => ?_, fun hgt => ?_⟩
    · have hx0 : x = 0 := by omega
      subst hx0
      left
      decide
    · simp only [evenOddSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
      refine ⟨?_, by omega, fun vRes hres => ?_⟩
      · change Int.toNat (x - 1) < Int.toNat x
        omega
      · obtain ⟨k, rfl | rfl⟩ : ∃ k : Int, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
        · have hm0 : (2 * k) % 2 = 0 := by omega
          have hm1 : (2 * k - 1) % 2 = 1 := by omega
          simp [hm0, hm1] at hres ⊢
          exact hres
        · have hm0 : (2 * k + 1) % 2 = 1 := by omega
          simp [hm0] at hres ⊢
          exact hres
  · by_cases h1 : fn = 1
    · subst h1
      simp only [evenOddProg, link, evenMod, oddMod, List.cons_append, List.nil_append,
        Module.lookup, show ¬ ((0 : Nat) = 1) by decide, ite_false, ite_true,
        Option.some.injEq] at hlu
      subst hlu
      simp only [evenOddSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true] at hpre ⊢
      simp only [wpCallDec]
      refine ⟨fun hle => ?_, fun hgt => ?_⟩
      · have hx0 : x = 0 := by omega
        subst hx0
        right
        decide
      · simp only [evenOddSpec, ite_true]
        refine ⟨?_, by omega, fun vRes hres => ?_⟩
        · change Int.toNat (x - 1) < Int.toNat x
          omega
        · obtain ⟨k, rfl | rfl⟩ : ∃ k : Int, x = 2 * k ∨ x = 2 * k + 1 := ⟨x / 2, by omega⟩
          · have hm0 : (2 * k) % 2 = 0 := by omega
            have hm1 : (2 * k - 1) % 2 = 1 := by omega
            simp [hm0, hm1] at hres ⊢
            exact hres
          · have hm0 : (2 * k + 1) % 2 = 1 := by omega
            simp [hm0] at hres ⊢
            exact hres
    · simp [evenOddProg, link, evenMod, oddMod, Module.lookup, Ne.symm h0, Ne.symm h1] at hlu

/-- A recursive caller: `0(x)` recurses on `x - 1` until `x ≤ 0`, then calls the
external function `1`. Its body makes a reachable internal call (to `0`) and an external
call (to `1`). -/
def recCaller : Module :=
  [(0, .ifLe .var (.lit 0) (.call 1 .var) (.call 0 (.sub .var (.lit 1))))]

/-- External library: `1(x) = 10`. -/
def tenLib : Module := [(1, .lit 10)]

/-- Guarantee of the recursive caller: `0` returns at least `10`. -/
def recGuar : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v ≥ 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Interface the caller assumes for the import `1`: on `x ≤ 0` it returns at least `10`. -/
def recAssumed : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≤ 0, post := fun _ v => v ≥ 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Spec the library satisfies: on every input it returns exactly `10` (weaker
precondition and stronger postcondition than `recAssumed`). -/
def tenActual : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

theorem recCaller_verified :
    ModuleVerifiedPartial recCaller (mixEnv recCaller recGuar recAssumed) recGuar := by
  intro fn body hlu x _
  by_cases h0 : fn = 0
  · subst h0
    simp only [recCaller, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    have hd0 : recCaller.Defines 0 := by decide
    have hd1 : ¬ recCaller.Defines 1 := by decide
    have hA0 : mixEnv recCaller recGuar recAssumed 0 = recGuar 0 := by simp [mixEnv, hd0]
    have hA1 : mixEnv recCaller recGuar recAssumed 1 = recAssumed 1 := by simp [mixEnv, hd1]
    simp only [wpPartial, hA0, hA1]
    simp [recGuar, recAssumed]
  · simp [recCaller, Module.lookup, Ne.symm h0] at hlu

theorem tenLib_correct : ProgramPartialCorrect tenLib tenActual := by
  intro fn fuel x out hpre hbeh
  by_cases h1 : fn = 1
  · subst h1
    cases fuel with
    | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
    | succ n =>
      simp only [HasBehavior, eval, tenLib, Module.lookup, ite_true, evalExprWith,
        List.mem_singleton] at hbeh
      subst hbeh
      exact .inr ⟨10, rfl, by simp [tenActual]⟩
  · simp [tenActual, h1] at hpre

/-- Non-vacuity for `verified_recursive_caller_links_with_refined_callee`: the recursive
caller `recCaller` (reachable internal call to `0`, external call to `1`) with the library
`tenLib`, whose spec `tenActual` strictly refines the assumed `recAssumed`. -/
theorem nonvacuous_recursive_spec_refinement :
    Linkable recCaller tenLib ∧
    ModuleVerifiedPartial recCaller (mixEnv recCaller recGuar recAssumed) recGuar ∧
    ProgramPartialCorrect tenLib tenActual ∧
    (∀ g, ¬ recCaller.Defines g → WeakensPre (recAssumed g) (tenActual g)) ∧
    (∀ g, ¬ recCaller.Defines g → StrengthensPostUnderPre (recAssumed g) (tenActual g)) ∧
    ¬ WeakensPre (tenActual 1) (recAssumed 1) ∧
    ¬ StrengthensPostUnderPre (tenActual 1) (recAssumed 1) := by
  refine ⟨by decide, recCaller_verified, tenLib_correct, ?_, ?_, ?_, ?_⟩
  · intro g _ x hx
    by_cases h1 : g = 1
    · subst h1; simp [tenActual]
    · simp [recAssumed, h1] at hx
  · intro g _ x v hx hv
    by_cases h1 : g = 1
    · subst h1
      simp only [tenActual, ite_true] at hv
      simp only [recAssumed, ite_true]
      omega
    · simp [recAssumed, h1] at hx
  · intro h
    have := h 1 trivial
    simp [recAssumed] at this
  · intro h
    have := h 0 11 trivial (by simp [recAssumed])
    simp [tenActual] at this

private def sepMod1 : Module := [(0, .add (.call 1 .var) (.lit 0))]
private def sepMod2 : Module := [(1, .add (.lit 0) .var)]
private def sepSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun x v => v = x }
  else if fn = 1 then { pre := fun _ => True, post := fun x v => v = x }
  else { pre := fun _ => False, post := fun _ _ => False }

private theorem wpPartial_foldAdd (A : SpecEnv) (x : Int) (a b : Expr) (Q : Int → Prop)
    (h : wpPartial A x a (fun v₁ => wpPartial A x b (fun v₂ => Q (v₁ + v₂)))) :
    wpPartial A x (foldAdd a b) Q := by
  simp only [foldAdd]
  split
  · next ha =>
    subst ha
    simp only [wpPartial] at h
    exact wpPartial_mono_post (fun v₂ hv₂ => by simpa using hv₂) h
  · next hb =>
    split
    · next hb0 =>
      subst hb0
      simp only [wpPartial] at h
      exact wpPartial_mono_post (fun v₁ hv₁ => by simpa using hv₁) h
    · exact h

private theorem constFoldExpr_preserves_wpPartial (A : SpecEnv) (x : Int) (e : Expr) :
    ∀ Q : Int → Prop, wpPartial A x e Q → wpPartial A x (constFoldExpr e) Q := by
  induction e with
  | lit _ => intro Q h; exact h
  | var => intro Q h; exact h
  | add e₁ e₂ ih₁ ih₂ =>
    intro Q h
    simp only [constFoldExpr]
    exact wpPartial_foldAdd A x (constFoldExpr e₁) (constFoldExpr e₂) Q
      (ih₁ _ (wpPartial_mono_post (fun _ h₂ => ih₂ _ h₂) h))
  | sub e₁ e₂ ih₁ ih₂ =>
    intro Q h
    exact ih₁ _ (wpPartial_mono_post (fun _ => ih₂ _) h)
  | mul e₁ e₂ ih₁ ih₂ =>
    intro Q h
    exact ih₁ _ (wpPartial_mono_post (fun _ => ih₂ _) h)
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    intro Q h
    exact ih₁ _ (wpPartial_mono_post (fun _ h₂ => ih₂ _ (wpPartial_mono_post (fun _ ⟨hT, hE⟩ =>
      ⟨fun hle => ihT _ (hT hle), fun hle => ihE _ (hE hle)⟩) h₂)) h)
  | choose e₁ e₂ ih₁ ih₂ =>
    intro Q h
    exact ⟨ih₁ _ h.1, ih₂ _ h.2⟩
  | call fn eArg ihArg =>
    intro Q h
    exact ihArg _ h

private theorem lookup_constFoldPass (M : Module) (fn : Fname) :
    (constFoldPass M).lookup fn = (M.lookup fn).map constFoldExpr := by
  induction M with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [constFoldPass, List.map_cons, Module.lookup]
    by_cases hk : k = fn
    · simp [hk]
    · simp only [hk, ite_false]
      exact ih

private theorem constFoldPass_preservesVerified (S : SpecEnv) :
    PreservesVerifiedPartial constFoldPass S := by
  intro M hVer fn body hlu x hpre
  rw [lookup_constFoldPass] at hlu
  cases hm : M.lookup fn with
  | none => simp [hm] at hlu
  | some origBody =>
    simp only [hm, Option.map_some, Option.some.injEq] at hlu
    subst hlu
    exact constFoldExpr_preserves_wpPartial S x origBody ((S fn).post x) (hVer fn origBody hm x hpre)

private theorem map_zero_add_id (l : List Outcome) :
    l.map (fun o => match o with | .val v₂ => .val (0 + v₂) | o => o) = l := by
  induction l with
  | nil => rfl
  | cons o tl ih => rw [List.map_cons, ih]; cases o <;> simp

private theorem flatMap_add_zero_id (l : List Outcome) :
    l.flatMap (fun o => match o with
      | .val v₁ => [Outcome.val 0].map (fun o => match o with
          | .val v₂ => .val (v₁ + v₂) | o => o)
      | o => [o]) = l := by
  induction l with
  | nil => rfl
  | cons o tl ih => rw [List.flatMap_cons, ih]; cases o <;> simp

/-- Constant folding does not change the outcome list of any expression, for any call
handler (so it preserves call depth as well as results). -/
theorem constFoldExpr_evalExprWith (f : Fname → Int → List Outcome) (x : Int) (e : Expr) :
    evalExprWith f x (constFoldExpr e) = evalExprWith f x e := by
  induction e with
  | lit _ => rfl
  | var => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [constFoldExpr, foldAdd]
    split
    · next ha =>
      have h1 : evalExprWith f x e₁ = [.val 0] := by rw [← ih₁, ha]; rfl
      simp only [evalExprWith, h1, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [ih₂]; exact (map_zero_add_id _).symm
    · split
      · next hb =>
        have h2 : evalExprWith f x e₂ = [.val 0] := by rw [← ih₂, hb]; rfl
        simp only [evalExprWith, h2]
        rw [ih₁]; exact (flatMap_add_zero_id _).symm
      · simp only [evalExprWith, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ => simp only [constFoldExpr, evalExprWith, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp only [constFoldExpr, evalExprWith, ih₁, ih₂]
  | ifLe e₁ e₂ eT eE ih₁ ih₂ ihT ihE =>
    simp only [constFoldExpr, evalExprWith, ih₁, ih₂, ihT, ihE]
  | choose e₁ e₂ ih₁ ih₂ => simp only [constFoldExpr, evalExprWith, ih₁, ih₂]
  | call fn eArg ih => simp only [constFoldExpr, evalExprWith, ih]

/-- `PassCtxRefines` admits the (non-identity) constant folder `constFoldPass`. -/
theorem passCtxRefines_pos : PassCtxRefines constFoldPass := by
  intro M
  refine ctxRefines_of_pointwise_body_subset ?_
  intro fn
  cases hm : M.lookup fn with
  | none => left; rw [lookup_constFoldPass, hm]; rfl
  | some b =>
    right
    refine ⟨b, constFoldExpr b, rfl, by rw [lookup_constFoldPass, hm]; rfl,
      fun f₁ f₂ hsub x o ho => ?_⟩
    rw [constFoldExpr_evalExprWith] at ho
    exact evalExprWith_mono_mem hsub x b ho

/-- Non-vacuity for `separate_compilation_partial_correct_of_preserves_verified` using the
non-identity constant folder `constFoldPass`. -/
theorem nonvacuous_separate_compilation :
    constFoldPass sepMod1 ≠ sepMod1 ∧
    ModuleVerifiedPartial sepMod1 sepSpec sepSpec ∧
    ModuleVerifiedPartial sepMod2 sepSpec sepSpec ∧
    SpecsImplemented (link sepMod1 sepMod2) sepSpec ∧
    PreservesVerifiedPartial constFoldPass sepSpec ∧
    PreservesDefines constFoldPass := by
  refine ⟨by decide, ?_, ?_, ?_, constFoldPass_preservesVerified sepSpec, preservesDefines_pos⟩
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [sepMod1, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpPartial, sepSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
      exact ⟨trivial, fun v hv => by omega⟩
    · simp [sepMod1, Module.lookup, Ne.symm h0] at hlu
  · intro fn body hlu x _
    by_cases h1 : fn = 1
    · subst h1
      simp only [sepMod2, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpPartial, sepSpec]
    · simp [sepMod2, Module.lookup, Ne.symm h1] at hlu
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · by_cases h1 : fn = 1
      · subst h1; decide
      · simp [sepSpec, h0, h1] at hpre

/-! ## Positive controls for the counterexample / negative results -/

private def expSrc : Module := [(0, .call 1 (.lit 5)), (1, .add .var (.lit 0))]
private def expTgt : Module := [(0, .call 1 (.lit 5)), (1, .var)]

/-- Positive control for the main-entry-versus-contextual counterexamples: optimizing an
exported helper `x + 0 ↦ x` in place (no specialization to internal callers, no change of
domain) preserves `CtxRefines`, `SameDom`, and `EntryRefines`. -/
theorem positive_control_in_place_export_optimization :
    CtxRefines expSrc expTgt ∧ SameDom expSrc expTgt ∧ EntryRefines 0 expSrc expTgt := by
  have hDom : SameDom expSrc expTgt := by
    intro fn
    by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
      simp [Module.Defines, Module.lookup, expSrc, expTgt, h0, h1, Ne.symm]
  have hCtx : CtxRefines expSrc expTgt := by
    refine ctxRefines_of_pointwise_body_subset ?_
    intro fn
    by_cases h0 : fn = 0
    · subst h0; left; rfl
    · by_cases h1 : fn = 1
      · subst h1
        right
        refine ⟨.add .var (.lit 0), .var, rfl, rfl, fun _ _ hfg x o ho => ?_⟩
        simp only [evalExprWith, List.mem_singleton] at ho
        subst ho
        simp [evalExprWith]
      · left
        simp [expSrc, expTgt, Module.lookup, Ne.symm h0, Ne.symm h1]
  refine ⟨hCtx, hDom, ?_⟩
  exact hCtx [] (by decide) (by decide) 0

/-- Countdown function `f(x) = if x ≤ 0 then 0 else f(x - 1)` used as a positive control
for measure-indexed total correctness. -/
def countdownMod : Module :=
  [(0, .ifLe .var (.lit 0) (.lit 0) (.call 0 (.sub .var (.lit 1))))]

private theorem countdown_eval_total :
    ∀ k (x : Int), x ≥ 0 → x.toNat = k →
      ∀ out, HasBehavior 0 countdownMod (k + 1) x out → out = .val 0 := by
  intro k
  induction k with
  | zero =>
    intro x hx hk out hbeh
    have hx0 : x ≤ 0 := by omega
    simp only [HasBehavior, eval, countdownMod, Module.lookup, ite_true, evalExprWith,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hx0, ite_true,
      List.mem_singleton] at hbeh
    exact hbeh
  | succ m ih =>
    intro x hx hk out hbeh
    have hxPos : ¬ x ≤ 0 := by omega
    refine ih (x - 1) (by omega) (by omega) out ?_
    rw [HasBehavior, eval] at hbeh
    simpa [HasBehavior, countdownMod, Module.lookup, evalExprWith, hxPos] using hbeh

/-- Positive control for total correctness: adding a well-founded decreasing measure
`μ _ x := x.toNat` over `Nat.lt` proves `ProgramTotalCorrect` directly. -/
theorem positive_control_ag_total_with_wf_measure :
    WellFounded Nat.lt ∧
    SpecsImplemented countdownMod zeroOutSpec ∧
    ModuleVerifiedTotal Nat.lt (fun _ x => x.toNat) countdownMod zeroOutSpec zeroOutSpec ∧
    ProgramTotalCorrect countdownMod zeroOutSpec := by
  refine ⟨Nat.lt_wfRel.wf, ?_, ?_, ?_⟩
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · simp [zeroOutSpec, h0] at hpre
  · intro fn body hlu x hpre
    by_cases h0 : fn = 0
    · subst h0
      simp only [countdownMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpCallDec, zeroOutSpec]
      intro hgt
      omega
    · simp [countdownMod, Module.lookup, Ne.symm h0] at hlu
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0
      by_cases hx : x ≥ 0
      · refine ⟨x.toNat + 1, fun out hbeh => ⟨0, countdown_eval_total x.toNat x hx rfl out hbeh, rfl⟩⟩
      · have hxLe : x ≤ 0 := by omega
        refine ⟨1, fun out hbeh => ⟨0, ?_, rfl⟩⟩
        simpa [HasBehavior, eval, countdownMod, Module.lookup, evalExprWith, hxLe] using hbeh
    · simp [zeroOutSpec, h0] at hpre

/-- Positive control for link-time spec refinement (the conclusion is attainable): the
recursive caller linked with `tenLib` satisfies its guarantee `recGuar`. -/
theorem positive_control_spec_refinement_link :
    ∀ f, recCaller.Defines f → FnPartialCorrect (link recCaller tenLib) f (recGuar f) :=
  let ⟨hL, hV, hS, hW, hSt, _, _⟩ := nonvacuous_recursive_spec_refinement
  verified_recursive_caller_links_with_refined_callee hL hV hS hW hSt

private def ctrlSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun x => x ≥ 0, post := fun _ v => v ≥ 0 }
  else if fn = 1 then { pre := fun x => x ≥ 0, post := fun _ v => v ≥ 0 }
  else { pre := fun _ => False, post := fun _ _ => False }

private def ctrlCaller : Module := [(0, .add (.call 1 .var) (.lit 0))]
private def ctrlCallee1 : Module := [(1, .add .var (.lit 1))]
private def ctrlCallee2 : Module := [(1, .lit 0)]

private theorem ctrl_caller_ver : ModuleVerifiedPartial ctrlCaller ctrlSpec ctrlSpec := by
  intro fn body hlu x hpre
  by_cases h0 : fn = 0
  · subst h0
    simp only [ctrlCaller, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp only [ctrlSpec, ite_true] at hpre
    simp only [wpPartial, ctrlSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
    exact ⟨hpre, fun v hv => by omega⟩
  · simp [ctrlCaller, Module.lookup, Ne.symm h0] at hlu

private theorem ctrl_callee1_ver : ModuleVerifiedPartial ctrlCallee1 ctrlSpec ctrlSpec := by
  intro fn body hlu x hpre
  by_cases h1 : fn = 1
  · subst h1
    simp only [ctrlCallee1, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp only [ctrlSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true] at hpre ⊢
    simp only [wpPartial]
    omega
  · simp [ctrlCallee1, Module.lookup, Ne.symm h1] at hlu

private theorem ctrl_callee2_ver : ModuleVerifiedPartial ctrlCallee2 ctrlSpec ctrlSpec := by
  intro fn body hlu x hpre
  by_cases h1 : fn = 1
  · subst h1
    simp only [ctrlCallee2, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp only [ctrlSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true, wpPartial]
    omega
  · simp [ctrlCallee2, Module.lookup, Ne.symm h1] at hlu

/-- Positive control for the callee-dependent rewrite counterexample: an
interface-respecting optimization (`constFoldPass`) of the caller stays partially correct
when linked with either of two concrete callees `ctrlCallee1`, `ctrlCallee2` that satisfy
the shared spec `ctrlSpec`. (The statement covers these two callees only; the general
statement for every spec-compliant callee is `link_ag_partial_correctness`.) -/
theorem positive_control_interface_only_optimization_survives_replacement :
    ModuleVerifiedPartial ctrlCaller ctrlSpec ctrlSpec ∧
    ModuleVerifiedPartial ctrlCallee1 ctrlSpec ctrlSpec ∧
    ModuleVerifiedPartial ctrlCallee2 ctrlSpec ctrlSpec ∧
    ModuleVerifiedPartial (constFoldPass ctrlCaller) ctrlSpec ctrlSpec ∧
    ProgramPartialCorrect (link (constFoldPass ctrlCaller) ctrlCallee1) ctrlSpec ∧
    ProgramPartialCorrect (link (constFoldPass ctrlCaller) ctrlCallee2) ctrlSpec := by
  refine ⟨ctrl_caller_ver, ctrl_callee1_ver, ctrl_callee2_ver,
    constFoldPass_preservesVerified ctrlSpec ctrlCaller ctrl_caller_ver, ?_, ?_⟩
  · intro fn fuel x out hpre hbeh
    by_cases h0 : fn = 0
    · subst h0
      simp only [ctrlSpec, ite_true] at hpre
      cases fuel with
      | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
      | succ n =>
        cases n with
        | zero =>
          simp [HasBehavior, eval, link, constFoldPass, ctrlCaller, constFoldExpr,
            foldAdd, Module.lookup, evalExprWith] at hbeh
          exact .inl hbeh
        | succ m =>
          simp [HasBehavior, eval, link, constFoldPass, ctrlCaller, constFoldExpr,
            foldAdd, ctrlCallee1, Module.lookup, evalExprWith] at hbeh
          subst hbeh
          exact .inr ⟨x + 1, rfl, by simp [ctrlSpec]; omega⟩
    · by_cases h1 : fn = 1
      · subst h1
        simp only [ctrlSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true] at hpre
        cases fuel with
        | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
        | succ n =>
          simp [HasBehavior, eval, link, constFoldPass, ctrlCaller, constFoldExpr,
            foldAdd, ctrlCallee1, Module.lookup, evalExprWith] at hbeh
          subst hbeh
          exact .inr ⟨x + 1, rfl, by simp [ctrlSpec]; omega⟩
      · simp [ctrlSpec, h0, h1] at hpre
  · intro fn fuel x out hpre hbeh
    by_cases h0 : fn = 0
    · subst h0
      simp only [ctrlSpec, ite_true] at hpre
      cases fuel with
      | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
      | succ n =>
        cases n with
        | zero =>
          simp [HasBehavior, eval, link, constFoldPass, ctrlCaller, constFoldExpr,
            foldAdd, Module.lookup, evalExprWith] at hbeh
          exact .inl hbeh
        | succ m =>
          simp [HasBehavior, eval, link, constFoldPass, ctrlCaller, constFoldExpr,
            foldAdd, ctrlCallee2, Module.lookup, evalExprWith] at hbeh
          subst hbeh
          exact .inr ⟨0, rfl, by simp [ctrlSpec]⟩
    · by_cases h1 : fn = 1
      · subst h1
        simp only [ctrlSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true] at hpre
        cases fuel with
        | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
        | succ n =>
          simp [HasBehavior, eval, link, constFoldPass, ctrlCaller, constFoldExpr,
            foldAdd, ctrlCallee2, Module.lookup, evalExprWith] at hbeh
          subst hbeh
          exact .inr ⟨0, rfl, by simp [ctrlSpec]⟩
      · simp [ctrlSpec, h0, h1] at hpre

/-! ## Non-vacuity witnesses for the results about what contextual refinement observes -/

/-- Non-vacuity for `ctxRefines_sameDom`: a nontrivial contextual refinement. -/
theorem nonvacuous_ctxRefines_sameDom : CtxRefines choose01Mod const0Mod := ctxRefines_pos

/-- An open source module: `0(x)` returns `1` or calls the import `5`. -/
def openChooseMod : Module := [(0, .choose (.lit 1) (.call 5 .var))]

/-- Non-vacuity for `ctxRefines_iff_standaloneRefines_of_closed_source_or_target`, using
the closed-*target* disjunct with an open source: removing a nondeterministic branch that
calls an import. Standalone refinement holds, and the theorem then yields contextual
refinement. -/
theorem nonvacuous_collapse_closed_target :
    ¬ ClosedModule openChooseMod ∧ ClosedModule const1Mod ∧
    (ClosedModule openChooseMod ∨ ClosedModule const1Mod) ∧
    StandaloneRefines openChooseMod const1Mod := by
  refine ⟨by decide, by decide, .inr (by decide), ?_⟩
  intro entry fuel arg out h
  by_cases h0 : entry = 0
  · subst h0
    cases fuel with
    | zero => simpa [HasBehavior, eval] using h
    | succ n =>
      simp only [HasBehavior, eval, const1Mod, Module.lookup, ite_true, evalExprWith,
        List.mem_singleton] at h
      subst h
      simp [HasBehavior, eval, openChooseMod, Module.lookup, evalExprWith]
  · cases fuel with
    | zero => simpa [HasBehavior, eval] using h
    | succ n =>
      simpa [HasBehavior, eval, const1Mod, openChooseMod, Module.lookup, Ne.symm h0] using h

/-- Consequence of the previous witness (via the theorem): the open source is contextually
refined by the closed target. -/
theorem collapse_closed_target_ctxRefines : CtxRefines openChooseMod const1Mod :=
  (ctxRefines_iff_standaloneRefines_of_closed_source_or_target
    nonvacuous_collapse_closed_target.2.2.1).2 nonvacuous_collapse_closed_target.2.2.2

/-- `0(x)` either loops or returns `0`. -/
def chooseLoopMod : Module := [(0, .choose (.call 0 .var) (.lit 0))]

/-- Removing the terminating branch of `chooseLoopMod` is a contextual refinement. -/
theorem chooseLoop_ctxRefines_selfLoop : CtxRefines chooseLoopMod selfLoopMod := by
  refine ctxRefines_of_pointwise_body_subset ?_
  intro fn
  by_cases h0 : fn = 0
  · subst h0
    right
    refine ⟨.choose (.call 0 .var) (.lit 0), .call 0 .var, rfl, rfl,
      fun f₁ f₂ hsub x o ho => ?_⟩
    simp only [evalExprWith, List.mem_append]
    exact .inl (evalExprWith_mono_mem hsub x (.call 0 .var) ho)
  · left
    simp [chooseLoopMod, selfLoopMod, Module.lookup, Ne.symm h0]

/-- Non-vacuity for `ctxRefines_reflects_mayDiverge`: the target may diverge and the
hypotheses hold. -/
theorem nonvacuous_ctxRefines_reflects_mayDiverge :
    CtxRefines chooseLoopMod selfLoopMod ∧ Linkable [] chooseLoopMod ∧
    MayDiverge (link [] selfLoopMod) 0 0 :=
  ⟨chooseLoop_ctxRefines_selfLoop, by decide, mayDiverge_pos⟩

/-- Non-vacuity for `separate_compilation_ctxRefines_of_pass_ctxRefines`: the non-identity
constant folder is a contextually refining pass, and the two modules are disjoint. -/
theorem nonvacuous_separate_compilation_ctxRefines :
    PassCtxRefines constFoldPass ∧ Linkable sepMod1 sepMod2 ∧ constFoldPass sepMod1 ≠ sepMod1 :=
  ⟨passCtxRefines_pos, by decide, by decide⟩

/-- Positive control for `Cex.cex_verifiability_preservation_not_behavioural`: the constant
folder preserves verifiability against every interface *and* is a contextually refining
pass, so for it both separate-compilation theorems apply. -/
theorem positive_control_constFold_verifiable_and_behavioural (S : SpecEnv) :
    PreservesVerifiedPartial constFoldPass S ∧ PreservesDefines constFoldPass ∧
    PassCtxRefines constFoldPass :=
  ⟨constFoldPass_preservesVerified S, preservesDefines_pos, passCtxRefines_pos⟩

end Toy.Link.Examples
