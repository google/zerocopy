import Toy.BoundaryLicensing.Transfer

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Cospan Capture-and-Lowering Transfer -/

universe u v w e b

/-- Set of observable execution behaviors/traces over `B`. -/
abbrev TraceSet (B : Type b) := B → Prop

/-- Subset inclusion of behavior sets (`T₁ ⊆ T₂`). -/
def TraceSub {B : Type b} (T₁ T₂ : TraceSet B) : Prop :=
  ∀ x, T₁ x → T₂ x

/-- Downward/subset-closed hyperproperty (`T₁ ⊆ T₂ → H T₂ → H T₁`). -/
def SubsetClosed {B : Type b} (H : TraceSet B → Prop) : Prop :=
  ∀ T₁ T₂ : TraceSet B, TraceSub T₁ T₂ → H T₂ → H T₁

/-- Left-to-right sequential execution of a pre-capture pass pipeline `[f₁, …, fₖ]`. -/
def runPasses {Src : Type u} (passes : List (Src → Src)) (a : Src) : Src :=
  passes.foldl (fun acc f => f acc) a

/-- Every pass in `passes` preserves all existing behaviors at the actual input it receives from `a`. -/
def LosesNoBehaviourAtInputs {Src : Type u} {B : Type b} (semS : Src → TraceSet B) :
    List (Src → Src) → Src → Prop
  | [], _ => True
  | f :: fs, a => TraceSub (semS a) (semS (f a)) ∧ LosesNoBehaviourAtInputs semS fs (f a)

/-- Partial IR capture over-approximates behavior whenever capture succeeds (`.ok`). -/
def OverApproxOnOk {Src : Type u} {Ir : Type v} {Err : Type e} {B : Type b}
    (semS : Src → TraceSet B) (semIr : Ir → TraceSet B) (cap : Src → Except Err Ir) : Prop :=
  ∀ p q, cap p = .ok q → TraceSub (semS p) (semIr q)

/-- Post-capture lowering trace-refines the source artifact `a` (`Traces(lower a) ⊆ Traces(a)`). -/
def LowerRefinesAt {Src : Type u} {Exec : Type w} {B : Type b}
    (semS : Src → TraceSet B) (semExec : Exec → TraceSet B) (lower : Src → Exec) (a : Src) : Prop :=
  TraceSub (semExec (lower a)) (semS a)

theorem traceSub_refl {B : Type b} (T : TraceSet B) : TraceSub T T :=
  fun _ h => h

theorem traceSub_trans {B : Type b} {T₁ T₂ T₃ : TraceSet B}
    (h₁ : TraceSub T₁ T₂) (h₂ : TraceSub T₂ T₃) : TraceSub T₁ T₃ :=
  fun x hx => h₂ x (h₁ x hx)

theorem runPasses_preserves_behaviours {Src : Type u} {B : Type b} (semS : Src → TraceSet B)
    (passes : List (Src → Src)) (a : Src) (hpass : LosesNoBehaviourAtInputs semS passes a) :
    TraceSub (semS a) (semS (runPasses passes a)) := by
  induction passes generalizing a with
  | nil => exact traceSub_refl (semS a)
  | cons f fs ih =>
    rcases hpass with ⟨hf, hfs⟩
    exact traceSub_trans hf (ih (f a) hfs)

/-- Universe-polymorphic cospan capture-and-lowering transfer across heterogeneous carriers
`Src : Type u`, `Ir : Type v`, `Exec : Type w`, `Err : Type e`, and `B : Type b`:
if `cap` succeeds with `.ok a_ir`, pre-capture passes lose no behavior at their inputs, `cap`
over-approximates on `.ok`, post-capture `lower` trace-refines `a_src`, and `H` is subset-closed,
then `H` transfers from `semIr a_ir` to both `semS a_src` and `semExec (lower a_src)`. -/
theorem cospan_subsetClosed_transfer
    {Src : Type u} {Ir : Type v} {Exec : Type w} {Err : Type e} {B : Type b}
    (semS : Src → TraceSet B) (semIr : Ir → TraceSet B) (semExec : Exec → TraceSet B)
    (passes : List (Src → Src)) (cap : Src → Except Err Ir) (lower : Src → Exec)
    (a_src : Src) (a_ir : Ir) (H : TraceSet B → Prop)
    (hok : cap (runPasses passes a_src) = .ok a_ir)
    (hpass : LosesNoBehaviourAtInputs semS passes a_src)
    (hcap : OverApproxOnOk semS semIr cap)
    (hlow : LowerRefinesAt semS semExec lower a_src)
    (hsub : SubsetClosed H)
    (hir : H (semIr a_ir)) :
    H (semS a_src) ∧ H (semExec (lower a_src)) := by
  have h_src_mid : TraceSub (semS a_src) (semS (runPasses passes a_src)) :=
    runPasses_preserves_behaviours semS passes a_src hpass
  have h_mid_ir : TraceSub (semS (runPasses passes a_src)) (semIr a_ir) :=
    hcap (runPasses passes a_src) a_ir hok
  have h_src_ir : TraceSub (semS a_src) (semIr a_ir) :=
    traceSub_trans h_src_mid h_mid_ir
  have h_src_holds : H (semS a_src) := hsub (semS a_src) (semIr a_ir) h_src_ir hir
  have h_exec_holds : H (semExec (lower a_src)) :=
    hsub (semExec (lower a_src)) (semS a_src) hlow h_src_holds
  exact ⟨h_src_holds, h_exec_holds⟩

/-- Instantiation of `cospan_subsetClosed_transfer` on `Sys` for `EvalShape .hyperSubsetClosed`. -/
theorem cospan_sys_hyperSubsetClosed_transfer (s0 ir exec : Sys) (P : Spec)
    (passes : List (Sys → Sys)) (cap : Sys → Except Unit Sys) (lower : Sys → Sys)
    (hok : cap (runPasses passes s0) = .ok ir)
    (hpass : LosesNoBehaviourAtInputs HasTrace passes s0)
    (hcap : OverApproxOnOk HasTrace HasTrace cap)
    (hlow : LowerRefinesAt HasTrace HasTrace lower s0)
    (hexec : lower s0 = exec)
    (hir : EvalShape .hyperSubsetClosed ir P) :
    EvalShape .hyperSubsetClosed s0 P ∧ EvalShape .hyperSubsetClosed exec P := by
  let H : TraceSet Trace → Prop := fun T =>
    ∀ τ₁ τ₂, T τ₁ → T τ₂ → evalVal P (τ₁ 0) = evalVal P (τ₂ 0) → ∀ n, evalVal P (τ₁ n) = evalVal P (τ₂ n)
  have hsub : SubsetClosed H :=
    fun _ _ hT hH τ₁ τ₂ h₁ h₂ h0 n => hH τ₁ τ₂ (hT τ₁ h₁) (hT τ₂ h₂) h0 n
  have hboth := cospan_subsetClosed_transfer HasTrace HasTrace HasTrace passes cap lower s0 ir H
    hok hpass hcap hlow hsub hir
  rw [hexec] at hboth
  exact hboth

/-! ### Canonical Finite Fixtures, Non-Vacuity, Definition Tests, and 6 Tightness Counterexamples -/

/-- Toy two-bit trace set over `Bool` (`0` = safe behavior `false`, `1` = bad behavior `true`). -/
def bitSem : Nat → TraceSet Bool
  | 0 => fun b => b = false
  | 1 => fun b => b = true
  | _ => fun _ => True

/-- Subset-closed safety hyperproperty requiring every behavior in `T` to equal `false`. -/
def allSafeH : TraceSet Bool → Prop :=
  fun T => ∀ b, T b → b = false

/-- Non-subset-closed GNI-style hyperproperty requiring both `false` and `true` behaviors in `T`. -/
def bothBranchesH : TraceSet Bool → Prop :=
  fun T => T false ∧ T true

theorem allSafeH_subsetClosed : SubsetClosed allSafeH :=
  fun _ _ hsub hT b hb => hT b (hsub b hb)

theorem traceSub_pos : TraceSub (bitSem 0) (bitSem 2) := fun _ _ => trivial
theorem traceSub_neg : ¬ TraceSub (bitSem 2) (bitSem 0) := by
  intro h; have := h true trivial; cases this

theorem subsetClosed_pos : SubsetClosed allSafeH := allSafeH_subsetClosed
theorem subsetClosed_neg : ¬ SubsetClosed bothBranchesH := by
  intro h
  have hboth : bothBranchesH (bitSem 2) := ⟨trivial, trivial⟩
  have h0 : bothBranchesH (bitSem 0) := h (bitSem 0) (bitSem 2) (fun _ _ => trivial) hboth
  exact Bool.noConfusion h0.2

theorem runPasses_pos : runPasses ([fun n => n + 1, fun n => n * 2] : List (Nat → Nat)) 3 = 8 := rfl
theorem runPasses_neg : runPasses ([fun n => n + 1] : List (Nat → Nat)) 3 ≠ 3 := by decide

theorem losesNoBehaviourAtInputs_pos :
    LosesNoBehaviourAtInputs bitSem [fun _ => 2] 0 := ⟨fun _ _ => trivial, trivial⟩

theorem losesNoBehaviourAtInputs_neg :
    ¬ LosesNoBehaviourAtInputs bitSem [fun _ => 0] 2 := by
  rintro ⟨h, _⟩
  exact Bool.noConfusion (h true trivial)

theorem overApproxOnOk_pos : OverApproxOnOk bitSem bitSem (Except.ok : Nat → Except Unit Nat) := by
  intro p q hok; cases hok; exact traceSub_refl _

theorem overApproxOnOk_neg :
    ¬ OverApproxOnOk bitSem bitSem (fun _ => (.ok 0 : Except Unit Nat)) := by
  intro h
  exact Bool.noConfusion (h 2 0 rfl true trivial)

theorem lowerRefinesAt_pos : LowerRefinesAt bitSem bitSem (fun _ => 0) 2 :=
  fun _ _ => trivial

theorem lowerRefinesAt_neg : ¬ LowerRefinesAt bitSem bitSem (fun _ => 2) 0 := by
  intro h
  exact Bool.noConfusion (h true trivial)

/-- Cross-universe, partial-capture, strict-inclusion non-vacuity witness for
`cospan_subsetClosed_transfer` across `Src = Nat : Type 0`, `Ir = Sys : Type 1`,
`Exec = Bool : Type 0`, `Err = Unit : Type 0`, and `B = Trace : Type 0`, where:
- `cap` succeeds with `.ok a_ir` on `1` and fails closed with `.error ()` on `2`;
- `semExec (lower 0) ⊊ semS 0 ⊊ semS (runPasses [· + 1] 0) ⊆ HasTrace a_ir` (strict inclusions). -/
theorem nonvacuity_cospan_transfer :
    let vAlt : Valuation := fun a => a == 1
    let a_ir : Sys := threeBranchSys valFalse valFalse valFalse valTrue vAlt valTrue
    let semS : Nat → TraceSet Trace := fun n =>
      match n with
      | 0 => HasTrace (twoBranchSys valFalse valFalse valFalse valTrue)
      | 1 => HasTrace a_ir
      | _ => HasTrace (constSys valTrue)
    let semExec : Bool → TraceSet Trace := fun b =>
      if b then HasTrace (constSys valTrue) else HasTrace (oneBranchSys valFalse valFalse)
    let passes : List (Nat → Nat) := [fun n => n + 1]
    let cap : Nat → Except Unit Sys := fun n => if n == 1 then .ok a_ir else .error ()
    let lower : Nat → Bool := fun _ => false
    let H : TraceSet Trace → Prop := fun T => ∀ τ, T τ → evalVal specAtom0 (τ 0) = false
    cap (runPasses passes 0) = .ok a_ir ∧
    cap 2 = .error () ∧
    LosesNoBehaviourAtInputs semS passes 0 ∧
    OverApproxOnOk semS HasTrace cap ∧
    LowerRefinesAt semS semExec lower 0 ∧
    SubsetClosed H ∧
    H (HasTrace a_ir) ∧
    ¬ TraceSub (semS 0) (semExec (lower 0)) := by
  intro vAlt a_ir semS semExec passes cap lower H
  have hsub01 : TraceSub (semS 0) (semS 1) :=
    lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom (isEmbedFrom_two_three _ _ _ _ _ _))
  have hlow0 : TraceSub (semExec false) (semS 0) :=
    lockStepSimFrom_traceIncl (isEmbedFrom_lockStepSimFrom (isEmbedFrom_one_two _ _ _ _))
  refine ⟨rfl, rfl, ⟨hsub01, trivial⟩, ?_, hlow0, (fun _ _ hT hH τ hτ => hH τ (hT τ hτ)), ?_, ?_⟩
  · intro p q hok
    by_cases hp1 : p = 1
    · subst hp1
      simp [cap] at hok
      subst hok
      exact traceSub_refl _
    · simp [cap, hp1] at hok
  · intro τ hτ
    unfold a_ir threeBranchSys at hτ
    rw [hasTrace_maskedBranchSys_iff] at hτ
    rcases hτ with ⟨⟨c, hc⟩, h0, _⟩
    have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases hc' with rfl | rfl | rfl <;> simp [h0, evalVal, specAtom0, valFalse, vAlt]
  · intro hrev
    let τ₁ : Trace := fun n => match n with | 0 => valFalse | _ + 1 => valTrue
    have hτ₁ : semS 0 τ₁ := by
      change HasTrace (twoBranchSys valFalse valFalse valFalse valTrue) τ₁
      unfold twoBranchSys
      rw [hasTrace_maskedBranchSys_iff]
      exact ⟨⟨1, by omega⟩, rfl, fun _ => rfl⟩
    have hexec := hrev τ₁ hτ₁
    dsimp [semExec, lower] at hexec
    have h1 := (evalShape_oneBranch valFalse valFalse τ₁).1 hexec |>.2 0
    have h0eq := congrFun h1 0
    simp [τ₁, valTrue, valFalse] at h0eq

/-- Tightness counterexample 1 (`hok` dropped): `cap` returns `.error ()`, `a_ir = 0` satisfies `allSafeH`,
all other hypotheses hold, and `allSafeH (bitSem (lower 2))` fails. -/
theorem cex_cospan_without_capture_ok :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := fun _ => .error ()
    let lower : Nat → Nat := id
    LosesNoBehaviourAtInputs bitSem passes 2 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 2)) := by
  refine ⟨trivial, ?_, traceSub_refl _, allSafeH_subsetClosed, fun _ h => h, ?_⟩
  · intro _ _ hok; cases hok
  · intro h; exact Bool.noConfusion (h true trivial)

/-- Tightness counterexample 2 (`hpass` dropped): a behavior-erasing pre-capture pass `fun _ => 0`
deletes `true` before capture while `lower = id` preserves `true` into execution. -/
theorem cex_cospan_without_prepass_no_loss :
    let passes : List (Nat → Nat) := [fun _ => 0]
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := id
    cap (runPasses passes 2) = .ok 0 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 2)) := by
  refine ⟨rfl, overApproxOnOk_pos, traceSub_refl _, allSafeH_subsetClosed, fun _ h => h, ?_⟩
  intro h; exact Bool.noConfusion (h true trivial)

/-- Tightness counterexample 3 (`hcap` dropped): an under-approximating capture `fun _ => .ok 0`
drops behavior `true` while pre-passes and lowering are identity. -/
theorem cex_cospan_without_overApproxOnOk :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := fun _ => .ok 0
    let lower : Nat → Nat := id
    cap (runPasses passes 2) = .ok 0 ∧
    LosesNoBehaviourAtInputs bitSem passes 2 ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 2)) := by
  refine ⟨rfl, trivial, traceSub_refl _, allSafeH_subsetClosed, fun _ h => h, ?_⟩
  intro h; exact Bool.noConfusion (h true trivial)

/-- Tightness counterexample 4 (`hlow` dropped): a post-capture law-breaking lowering `fun _ => 1`
introduces behavior `true` absent from `a_src = 0` and `a_ir = 0`. -/
theorem cex_cospan_without_lowerRefines :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := fun _ => 1
    cap (runPasses passes 0) = .ok 0 ∧
    LosesNoBehaviourAtInputs bitSem passes 0 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    SubsetClosed allSafeH ∧
    allSafeH (bitSem 0) ∧
    ¬ allSafeH (bitSem (lower 0)) := by
  refine ⟨rfl, trivial, overApproxOnOk_pos, allSafeH_subsetClosed, fun _ h => h, ?_⟩
  intro h; exact Bool.noConfusion (h true rfl)

/-- Tightness counterexample 5 (`hsub` dropped): `lower` validly refines `{false, true}` (`2`) to `{false}` (`0`),
breaking the non-subset-closed hyperproperty `bothBranchesH`. -/
theorem cex_cospan_without_subsetClosed :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := fun _ => 0
    cap (runPasses passes 2) = .ok 2 ∧
    LosesNoBehaviourAtInputs bitSem passes 2 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 2 ∧
    bothBranchesH (bitSem 2) ∧
    ¬ bothBranchesH (bitSem (lower 2)) := by
  refine ⟨rfl, trivial, overApproxOnOk_pos, lowerRefinesAt_pos, ⟨trivial, trivial⟩, ?_⟩
  intro h; exact Bool.noConfusion h.2

/-- Tightness counterexample 6 (`hir` dropped): all cospan hypotheses and `SubsetClosed` hold,
`a_ir = 1` violates `allSafeH`, and `a_exec = 1` violates `allSafeH`. -/
theorem cex_cospan_without_ir_holds :
    let passes : List (Nat → Nat) := []
    let cap : Nat → Except Unit Nat := Except.ok
    let lower : Nat → Nat := id
    cap (runPasses passes 1) = .ok 1 ∧
    LosesNoBehaviourAtInputs bitSem passes 1 ∧
    OverApproxOnOk bitSem bitSem cap ∧
    LowerRefinesAt bitSem bitSem lower 1 ∧
    SubsetClosed allSafeH ∧
    ¬ allSafeH (bitSem (lower 1)) := by
  refine ⟨rfl, trivial, overApproxOnOk_pos, traceSub_refl _, allSafeH_subsetClosed, ?_⟩
  intro h; exact Bool.noConfusion (h true rfl)

end Toy.BoundaryLicensing
