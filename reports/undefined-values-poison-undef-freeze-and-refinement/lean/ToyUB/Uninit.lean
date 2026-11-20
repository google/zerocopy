import ToyUB.Lemmas

/-!
# Eagerly-UB uninitialised reads versus poison

A second reading of "uninitialised": each input is either an initialised integer
(`some v`) or uninitialised (`none`), and *reading* an uninitialised input at integer type
is immediate undefined behaviour (`semE`). This mirrors, in a memory-free setting, the rule
that an integer value must not be obtained from uninitialised memory; it is not a model of
any real language's semantics. Values never become undefined in this semantics, so
evaluation is deterministic, `let` only ever binds initialised values, and `freeze` is the
identity: in particular `freeze x` with `x` uninitialised is UB, because the read of `x`
happens first (`semE_freeze_uninit_example`). There is no byte-level or untyped copy of
uninitialised data.

Reading the same environment in the poison model (uninitialised ↦ `poison`,
`toPoisonEnv`) gives, for each fixed program `e`, an outcome-level refinement: either the
eager evaluation of `e` is UB, or both evaluations produce the same integer
(`poison_refines_eagerUninit_eq`). So evaluating a *fixed* program under the poison reading
never exhibits a behaviour the eager reading forbids; the converse fails (a program that
reads an uninitialised input and discards it is UB eagerly but well defined with poison).

This per-program fact does *not* transfer the soundness of rewrites between the two
readings, in either direction: inserting a dead read is sound with poison and unsound
eagerly (`dead_read_insertion_poison_sound_eager_unsound`), while turning `x * 0` into a
branch on `x` is sound eagerly and unsound with poison
(`mul_zero_to_branch_eager_sound_poison_unsound`).
-/

namespace Toy.UB

open Expr

/-- Eager-uninitialised semantics at width `w`: the environment maps a variable to
`some v` (initialised) or `none` (uninitialised); reading `none` is UB. -/
def semE (w : Nat) : (Var → Option (BitVec w)) → Expr → List (Outcome (BitVec w))
  | ρ, .var x => match ρ x with
    | none => [.ub]
    | some v => [.val v]
  | _, .const n => [.val (BitVec.ofNat w n)]
  | ρ, .add a b => bind2 (semE w ρ a) (semE w ρ b) fun u v => [.val (u + v)]
  | ρ, .mul a b => bind2 (semE w ρ a) (semE w ρ b) fun u v => [.val (u * v)]
  | ρ, .eq a b => bind2 (semE w ρ a) (semE w ρ b) fun u v => [.val (eqBit u v)]
  | ρ, .ite c t e => bind1 (semE w ρ c) fun z => if z ≠ 0#w then semE w ρ t else semE w ρ e
  | ρ, .letE x a b => bind1 (semE w ρ a) fun v => semE w (update ρ x (some v)) b
  | ρ, .freeze a => semE w ρ a
  | _, .ub => [.ub]

/-- The poison-model reading of an eager environment: uninitialised inputs are `poison`. -/
def toPoisonEnv {w : Nat} (ρ : Var → Option (BitVec w)) : Var → PVal w :=
  fun x => match ρ x with
    | none => .poison
    | some v => .int v

/-- Embedding of eager outcomes into poison-model outcomes. -/
def Outcome.toP {w : Nat} : Outcome (BitVec w) → Outcome (PVal w)
  | .ub => .ub
  | .val v => .val (.int v)

/-- Positive example: reading an initialised input is defined. Negative example: reading an
uninitialised input is UB even if the result is then multiplied by `0`. -/
theorem semE_examples :
    semE 2 (fun _ => some 3#2) (.add (.var 0) (.const 1)) = [.val 0#2] ∧
    semE 2 (fun _ => none) (.mul (.var 0) (.const 0)) = [.ub] := by decide

/-- Positive/negative example for `toPoisonEnv`: an uninitialised input becomes `poison`
(and not an integer), an initialised one keeps its integer (and is not `poison`). -/
theorem toPoisonEnv_examples :
    toPoisonEnv (w := 2) (fun _ => none) 0 = .poison ∧
    toPoisonEnv (w := 2) (fun _ => none) 0 ≠ .int 0#2 ∧
    toPoisonEnv (w := 2) (fun _ => some 1#2) 0 = .int 1#2 ∧
    toPoisonEnv (w := 2) (fun _ => some 1#2) 0 ≠ .poison := by decide

/-- Examples for `Outcome.toP`: UB maps to UB, an integer to the same integer; no eager
outcome maps to `poison`. -/
theorem outcome_toP_examples :
    Outcome.toP (w := 2) .ub = .ub ∧ Outcome.toP (w := 2) (.val 3#2) = .val (.int 3#2) ∧
    Outcome.toP (w := 2) (.val 3#2) ≠ .val .poison := by decide

/-- In the eager reading, `freeze x` with `x` uninitialised is UB (the read comes first). -/
theorem semE_freeze_uninit_example (w : Nat) :
    semE w (fun _ => none) (.freeze (.var 0)) = [.ub] := by simp [semE]

theorem toPoisonEnv_update {w : Nat} (ρ : Var → Option (BitVec w)) (x : Var) (v : BitVec w) :
    toPoisonEnv (update ρ x (some v)) = update (toPoisonEnv ρ) x (.int v) := by
  funext y
  simp only [toPoisonEnv, update]
  by_cases h : y = x
  · simp [h]
  · simp [h]

/-- The eager semantics is deterministic, and whenever it yields a value the poison
semantics on the translated environment yields the same integer. -/
theorem semE_spec (w : Nat) (e : Expr) :
    ∀ ρ : Var → Option (BitVec w), semE w ρ e = [.ub] ∨
      ∃ v, semE w ρ e = [.val v] ∧ semP w (toPoisonEnv ρ) e = [.val (.int v)] := by
  induction e with
  | var x =>
    intro ρ
    cases hx : ρ x with
    | none => left; simp [semE, hx]
    | some v => right; exact ⟨v, by simp [semE, hx], by simp [semP, toPoisonEnv, hx]⟩
  | const n => intro ρ; right; exact ⟨_, rfl, rfl⟩
  | add a b iha ihb =>
    intro ρ
    rcases iha ρ with ha | ⟨va, ha, hpa⟩
    · left; simp [semE, bind2, ha]
    · rcases ihb ρ with hb | ⟨vb, hb, hpb⟩
      · left; simp [semE, bind2, ha, hb]
      · right; exact ⟨va + vb, by simp [semE, bind2, ha, hb], by simp [semP, bind2, hpa, hpb, PVal.lift2]⟩
  | mul a b iha ihb =>
    intro ρ
    rcases iha ρ with ha | ⟨va, ha, hpa⟩
    · left; simp [semE, bind2, ha]
    · rcases ihb ρ with hb | ⟨vb, hb, hpb⟩
      · left; simp [semE, bind2, ha, hb]
      · right; exact ⟨va * vb, by simp [semE, bind2, ha, hb], by simp [semP, bind2, hpa, hpb, PVal.lift2]⟩
  | eq a b iha ihb =>
    intro ρ
    rcases iha ρ with ha | ⟨va, ha, hpa⟩
    · left; simp [semE, bind2, ha]
    · rcases ihb ρ with hb | ⟨vb, hb, hpb⟩
      · left; simp [semE, bind2, ha, hb]
      · right; exact ⟨eqBit va vb, by simp [semE, bind2, ha, hb], by simp [semP, bind2, hpa, hpb, PVal.lift2]⟩
  | ite c t e ihc iht ihe =>
    intro ρ
    rcases ihc ρ with hc | ⟨z, hc, hpc⟩
    · left; simp [semE, hc]
    · have hE : semE w ρ (.ite c t e) = if z ≠ 0#w then semE w ρ t else semE w ρ e := by
        simp only [semE, hc, bind1_val_singleton]
      have hP : semP w (toPoisonEnv ρ) (.ite c t e) =
          if z ≠ 0#w then semP w (toPoisonEnv ρ) t else semP w (toPoisonEnv ρ) e := by
        simp only [semP, hpc, bind1_val_singleton]
      rw [hE, hP]
      split
      · exact iht ρ
      · exact ihe ρ
  | letE x a b iha ihb =>
    intro ρ
    rcases iha ρ with ha | ⟨v, ha, hpa⟩
    · left; simp [semE, ha]
    · have hE : semE w ρ (.letE x a b) = semE w (update ρ x (some v)) b := by
        simp only [semE, ha, bind1_val_singleton]
      have hP : semP w (toPoisonEnv ρ) (.letE x a b) =
          semP w (toPoisonEnv (update ρ x (some v))) b := by
        simp only [semP, hpa, bind1_val_singleton, toPoisonEnv_update]
      rw [hE, hP]
      exact ihb _
  | freeze a iha =>
    intro ρ
    rcases iha ρ with ha | ⟨v, ha, hpa⟩
    · left; simp [semE, ha]
    · right; exact ⟨v, by simp [semE, ha], by simp [semP, hpa]⟩
  | ub => intro ρ; left; rfl

/-- Changing the value relation along an implication preserves `OutRef`. -/
theorem outRef_mono_rel {V : Type} {R R' : V → V → Prop} (hR : ∀ a b, R a b → R' a b)
    {T S : List (Outcome V)} (h : OutRef R T S) : OutRef R' T S := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun o ho => ?_
    obtain ⟨o', ho', hle⟩ := h o ho
    refine ⟨o', ho', ?_⟩
    cases o <;> cases o' <;> simp_all [Outcome.LeVal]

/-- **Poison evaluation refines eager-uninitialised evaluation, with equal values.** For
every width `w`, eager environment `ρ` and fixed program `e`: either the eager evaluation of
`e` may reach UB, or every poison-model outcome of `e` on the translated environment
(`uninitialised ↦ poison`) is *equal* to an eager outcome (no `poison` is ever produced
where the eager reading is defined). -/
theorem poison_refines_eagerUninit_eq (w : Nat) (ρ : Var → Option (BitVec w)) (e : Expr) :
    OutRef (fun a b => a = b) (semP w (toPoisonEnv ρ) e) ((semE w ρ e).map Outcome.toP) := by
  rcases semE_spec w e ρ with h | ⟨v, h, hp⟩
  · left; rw [mayUB_iff, h]; simp [Outcome.toP]
  · rw [h, hp]
    exact outRef_refl (fun _ => rfl) _

/-- **Poison semantics refines eager-uninitialised semantics** (with the poison model's
value refinement; a corollary of `poison_refines_eagerUninit_eq`, since the eager outcomes
never contain `poison`, so `PVal.Refines` is used only at equal integers). -/
theorem poison_refines_eagerUninit (w : Nat) (ρ : Var → Option (BitVec w)) (e : Expr) :
    OutRef PVal.Refines (semP w (toPoisonEnv ρ) e) ((semE w ρ e).map Outcome.toP) :=
  outRef_mono_rel (fun a _ h => h ▸ PVal.Refines.refl a) (poison_refines_eagerUninit_eq w ρ e)

/-- **The converse fails.** For every width `w`, with every input uninitialised, the
program `let y := x; 0` (which reads `x` and discards it) is UB in the eager semantics but
returns `0` in the poison semantics, so the eager outcomes do not refine the poison
outcomes. -/
theorem eagerUninit_not_refines_poison (w : Nat) :
    ¬ OutRef PVal.Refines ((semE w (fun _ => none) (.letE 1 (.var 0) (.const 0))).map Outcome.toP)
        (semP w (toPoisonEnv fun _ => none) (.letE 1 (.var 0) (.const 0))) := by
  intro h
  rcases h with hub | h
  · rw [mayUB_iff] at hub
    simp [semP, toPoisonEnv] at hub
  · obtain ⟨o', _, hle⟩ := h .ub (by simp [semE, Outcome.toP])
    cases o' <;> simp [Outcome.LeVal] at hle

/-- Refinement in the eager-uninitialised reading at width `w`: for every eager
environment, the source may reach UB or every target outcome equals a source outcome.
Used only to show that rewrite soundness does not transfer between the readings. -/
def RefinesE (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → Option (BitVec w), OutRef (fun a b => a = b) (semE w ρ tgt) (semE w ρ src)

/-- Positive example: every program eagerly refines itself. Negative example: reading
`x` does not refine the constant `0` (with `x` uninitialised the target is UB). -/
theorem refinesE_examples (w : Nat) :
    RefinesE w (.var 0) (.var 0) ∧ ¬ RefinesE w (.var 0) (.const 0) := by
  refine ⟨fun ρ => outRef_refl (fun _ => rfl) _, fun h => ?_⟩
  rcases h (fun _ => none) with hub | h
  · simp [mayUB_iff, semE] at hub
  · obtain ⟨o', _, hle⟩ := h .ub (by simp [semE])
    cases o' <;> simp [Outcome.LeVal] at hle

/-- **Rewrite soundness does not transfer from the poison reading to the eager reading.**
For every width `w`, inserting a dead read (`0 → let y := x; 0`) is a refinement in the
poison(+freeze) model but not in the eager reading (with `x` uninitialised the target is
UB). -/
theorem dead_read_insertion_poison_sound_eager_unsound (w : Nat) :
    RefinesP w (.letE 1 (.var 0) (.const 0)) (.const 0) ∧
    ¬ RefinesE w (.letE 1 (.var 0) (.const 0)) (.const 0) := by
  constructor
  · intro ρ
    have : semP w ρ (.letE 1 (.var 0) (.const 0)) = semP w ρ (.const 0) := by simp [semP]
    rw [this]
    exact outRef_refl PVal.Refines.refl _
  · intro h
    rcases h (fun _ => none) with hub | h
    · simp [mayUB_iff, semE] at hub
    · obtain ⟨o', _, hle⟩ := h .ub (by simp [semE])
      cases o' <;> simp [Outcome.LeVal] at hle

/-- **Rewrite soundness does not transfer from the eager reading to the poison reading.**
For every width `w`, rewriting `x * 0` to `if x then 0 else 0` is a refinement in the eager
reading (an uninitialised `x` already makes the source UB) but not in the poison(+freeze)
model (with `x ↦ poison` the source yields `poison`, the target branches on it). -/
theorem mul_zero_to_branch_eager_sound_poison_unsound (w : Nat) :
    RefinesE w (.ite (.var 0) (.const 0) (.const 0)) (.mul (.var 0) (.const 0)) ∧
    ¬ RefinesP w (.ite (.var 0) (.const 0) (.const 0)) (.mul (.var 0) (.const 0)) := by
  constructor
  · intro ρ
    cases h : ρ 0 with
    | none => left; simp [mayUB_iff, semE, bind2, h]
    | some v =>
      have h1 : semE w ρ (.ite (.var 0) (.const 0) (.const 0)) = [.val (BitVec.ofNat w 0)] := by
        simp [semE, h]
      have h2 : semE w ρ (.mul (.var 0) (.const 0)) = [.val (BitVec.ofNat w 0)] := by
        simp [semE, bind2, h]
      rw [h1, h2]
      exact outRef_refl (fun _ => rfl) _
  · intro h
    rcases h (fun _ => .poison) with hub | h
    · simp [mayUB_iff, semP, bind2, PVal.lift2] at hub
    · obtain ⟨o', _, hle⟩ := h .ub (by simp [semP])
      cases o' <;> simp [Outcome.LeVal] at hle

end Toy.UB
