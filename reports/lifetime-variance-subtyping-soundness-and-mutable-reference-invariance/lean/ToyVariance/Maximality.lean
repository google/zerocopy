import ToyVariance.Basic
import ToyVariance.Alg
import ToyVariance.Lang
import ToyVariance.Programs
import ToyVariance.Soundness

/-!
# Generic witness programs for the maximality of inferred variance

For a first-order data body `F` and a declared variance `v` that is not at most as permissive as
`inferVar rustTable F`, this file builds a program that is typed with the body rule
`BodyAx F v` and reaches the dangling-access state. Two attacks are used:

* `v` does not require the forward direction: the rule contains `F[&'sh nat] ≤ F[&'static nat]`.
  Build a value of `F[&'sh nat]` holding the short reference at every parameter position, coerce
  it, project down to a parameter position at type `&'static nat`, end `'sh`, and read.
* `v` requires the forward direction but `inferVar` also requires the backward one: the rule
  contains `F[&'static nat] ≤ F[&'sh nat]`, and `F` has a parameter occurrence under `&mut` or
  `Cell`. Build `x : F[&'static nat]`, coerce a copy `y`, navigate both to that `&mut`/`Cell`,
  store a value of the inner type built with the short reference through `y`, read it back
  through `x` at the `'static` type, project to a parameter position, end `'sh`, and read.
-/

set_option linter.unusedVariables false

namespace Toy.Variance

/-! ## Variance facts -/

theorem Variance.co_comp (w : Variance) : Variance.co.comp w = w := by cases w <;> rfl
theorem Variance.inv_comp_fwd (w : Variance) : (Variance.inv.comp w).fwd = (w.fwd || w.bwd) := by
  cases w <;> rfl
theorem Variance.inv_comp_bwd (w : Variance) : (Variance.inv.comp w).bwd = (w.fwd || w.bwd) := by
  cases w <;> rfl
theorem Variance.meet_fwd (v w : Variance) : (v.meet w).fwd = (v.fwd || w.fwd) := by
  cases v <;> cases w <;> rfl
theorem Variance.meet_bwd (v w : Variance) : (v.meet w).bwd = (v.fwd && false || v.bwd || w.bwd) := by
  cases v <;> cases w <;> rfl

/-- Types without function types and `PhantomData`. -/
def Ty.fo : Ty → Bool
  | .unit => true
  | .nat => true
  | .param => true
  | .prod T U => T.fo && U.fo
  | .ref _ T => T.fo
  | .refMut _ T => T.fo
  | .cell T => T.fo
  | .fn _ _ => false
  | .phantom _ => false

/-- Has a parameter occurrence under `refMut` or under `cell`. -/
def Ty.invOcc : Ty → Bool
  | .prod T U => T.invOcc || U.invOcc
  | .ref _ T => T.invOcc
  | .refMut _ T => !T.closed
  | .cell T => !T.closed
  | _ => false

theorem Ty.fo_of_dataBodyAt : ∀ (T : Ty) (b : Bool), T.dataBodyAt b = true → T.fo = true
  | .unit, _, _ => rfl
  | .nat, _, _ => rfl
  | .param, _, _ => rfl
  | .prod T U, _, h => by
    simp only [Ty.dataBodyAt, Bool.and_eq_true] at h
    simp [Ty.fo, Ty.fo_of_dataBodyAt T _ h.1, Ty.fo_of_dataBodyAt U _ h.2]
  | .ref _ T, _, h => by simp only [Ty.dataBodyAt] at h; simp [Ty.fo, Ty.fo_of_dataBodyAt T _ h]
  | .refMut _ T, _, h => by
    simp only [Ty.dataBodyAt] at h; simp [Ty.fo, Ty.fo_of_dataBodyAt T _ h]
  | .cell T, _, h => by
    simp only [Ty.dataBodyAt, Bool.and_eq_true] at h; simp [Ty.fo, Ty.fo_of_dataBodyAt T _ h.2]
  | .fn _ _, _, h => by simp [Ty.dataBodyAt] at h
  | .phantom _, _, h => by simp [Ty.dataBodyAt] at h

theorem inferVar_of_closed (tbl : Table) : ∀ (T : Ty), T.closed = true → inferVar tbl T = .bi := by
  intro T
  induction T with
  | unit => intro _; rfl
  | nat => intro _; rfl
  | param => intro h; simp [Ty.closed] at h
  | ref l T ih => intro h; simp only [Ty.closed] at h; simp [inferVar, ih h]; cases tbl .refTy <;> rfl
  | refMut l T ih =>
    intro h; simp only [Ty.closed] at h; simp [inferVar, ih h]; cases tbl .refMutTy <;> rfl
  | cell T ih => intro h; simp only [Ty.closed] at h; simp [inferVar, ih h]; cases tbl .cell <;> rfl
  | phantom T ih =>
    intro h; simp only [Ty.closed] at h; simp [inferVar, ih h]; cases tbl .phantom <;> rfl
  | fn T U ihT ihU =>
    intro h; simp only [Ty.closed, Bool.and_eq_true] at h
    simp [inferVar, ihT h.1, ihU h.2]; cases tbl .fnArg <;> cases tbl .fnRes <;> rfl
  | prod T U ihT ihU =>
    intro h; simp only [Ty.closed, Bool.and_eq_true] at h
    simp [inferVar, ihT h.1, ihU h.2]; cases tbl .prodL <;> cases tbl .prodR <;> rfl

theorem inferVar_fwd_of_not_closed : ∀ (T : Ty), T.fo = true → T.closed = false →
    (inferVar rustTable T).fwd = true := by
  intro T
  induction T with
  | unit => intro _ h; simp [Ty.closed] at h
  | nat => intro _ h; simp [Ty.closed] at h
  | param => intro _ _; rfl
  | ref l T ih =>
    intro hf hc; simp only [Ty.fo] at hf; simp only [Ty.closed] at hc
    simp only [inferVar, rustTable, Variance.co_comp]; exact ih hf hc
  | refMut l T ih =>
    intro hf hc; simp only [Ty.fo] at hf; simp only [Ty.closed] at hc
    simp only [inferVar, rustTable, Variance.inv_comp_fwd, ih hf hc, Bool.true_or]
  | cell T ih =>
    intro hf hc; simp only [Ty.fo] at hf; simp only [Ty.closed] at hc
    simp only [inferVar, rustTable, Variance.inv_comp_fwd, ih hf hc, Bool.true_or]
  | phantom T ih => intro hf; simp [Ty.fo] at hf
  | fn T U ihT ihU => intro hf; simp [Ty.fo] at hf
  | prod T U ihT ihU =>
    intro hf hc; simp only [Ty.fo, Bool.and_eq_true] at hf
    simp only [inferVar, rustTable, Variance.co_comp, Variance.meet_fwd]
    cases hT : T.closed
    · simp [ihT hf.1 hT]
    · have hU : U.closed = false := by simp [Ty.closed, hT] at hc; exact hc
      simp [ihU hf.2 hU]

theorem invOcc_of_inferVar_bwd : ∀ (T : Ty), T.fo = true →
    (inferVar rustTable T).bwd = true → T.invOcc = true := by
  intro T
  induction T with
  | unit => intro _ h; simp [inferVar, Variance.bwd] at h
  | nat => intro _ h; simp [inferVar, Variance.bwd] at h
  | param => intro _ h; simp [inferVar, Variance.bwd] at h
  | ref l T ih =>
    intro hf hb; simp only [Ty.fo] at hf
    simp only [inferVar, rustTable, Variance.co_comp] at hb
    exact ih hf hb
  | refMut l T ih =>
    intro hf hb; simp only [Ty.invOcc]
    cases hc : T.closed
    · rfl
    · simp [inferVar, rustTable, inferVar_of_closed rustTable T hc, Variance.comp,
        Variance.ofDirs, Variance.fwd, Variance.bwd] at hb
  | cell T ih =>
    intro hf hb; simp only [Ty.invOcc]
    cases hc : T.closed
    · rfl
    · simp [inferVar, rustTable, inferVar_of_closed rustTable T hc, Variance.comp,
        Variance.ofDirs, Variance.fwd, Variance.bwd] at hb
  | phantom T ih => intro hf; simp [Ty.fo] at hf
  | fn T U ihT ihU => intro hf; simp [Ty.fo] at hf
  | prod T U ihT ihU =>
    intro hf hb; simp only [Ty.fo, Bool.and_eq_true] at hf
    simp only [inferVar, rustTable, Variance.co_comp, Variance.meet_bwd] at hb
    simp only [Ty.invOcc, Bool.or_eq_true]
    cases hT : (inferVar rustTable T).bwd
    · simp [hT] at hb
      exact Or.inr (ihU hf.2 hb)
    · exact Or.inl (ihT hf.1 hT)

theorem Ty.subst_closed {A : Ty} (hA : A.closed = true) : ∀ (F : Ty), (F.subst A).closed = true := by
  intro F
  induction F with
  | param => exact hA
  | unit => rfl
  | nat => rfl
  | ref _ _ ih => exact ih
  | refMut _ _ ih => exact ih
  | cell _ ih => exact ih
  | phantom _ ih => exact ih
  | fn _ _ ih₁ ih₂ => simp [Ty.subst, Ty.closed, ih₁, ih₂]
  | prod _ _ ih₁ ih₂ => simp [Ty.subst, Ty.closed, ih₁, ih₂]

/-! ## Sequencing lemmas for the checker and the interpreter -/

/-- The top-level checking mode at time `0`. -/
def m₀ : Mode := ⟨0, false⟩

/-- `p` takes the checker from context `Γ` to `Γ'` at mode `m₀`, consuming one unit of fuel
per statement. -/
def ChkSeq (sub : Ty → Ty → Bool) (Γ : Ctx) (p : List Stmt) (Γ' : Ctx) : Prop :=
  ∀ f rest, chk (f + p.length) sub m₀ Γ (p ++ rest) = chk f sub m₀ Γ' rest

theorem ChkSeq.nil (sub : Ty → Ty → Bool) (Γ : Ctx) : ChkSeq sub Γ [] Γ := fun _ _ => rfl

theorem ChkSeq.append {sub : Ty → Ty → Bool} {Γ₁ Γ₂ Γ₃ : Ctx} {p q : List Stmt}
    (h₁ : ChkSeq sub Γ₁ p Γ₂) (h₂ : ChkSeq sub Γ₂ q Γ₃) : ChkSeq sub Γ₁ (p ++ q) Γ₃ := by
  intro f rest
  have e : f + (p ++ q).length = (f + q.length) + p.length := by
    simp only [List.length_append]; omega
  rw [e, List.append_assoc, h₁, h₂]

theorem ChkSeq.cons {sub : Ty → Ty → Bool} {Γ₁ Γ₂ Γ₃ : Ctx} {s : Stmt} {p : List Stmt}
    (h₁ : ChkSeq sub Γ₁ [s] Γ₂) (h₂ : ChkSeq sub Γ₂ p Γ₃) : ChkSeq sub Γ₁ (s :: p) Γ₃ :=
  ChkSeq.append h₁ h₂

/-- `p` takes the interpreter from heap `h` and environment `env` to `h'` and `env'` at time
`0`, consuming one unit of fuel per statement. -/
def ExecSeq (h : List (Lft × Val)) (env : Env) (p : List Stmt) (h' : List (Lft × Val))
    (env' : Env) : Prop :=
  ∀ f rest, exec (f + p.length) ⟨0, h⟩ env (p ++ rest) = exec f ⟨0, h'⟩ env' rest

theorem ExecSeq.nil (h : List (Lft × Val)) (env : Env) : ExecSeq h env [] h env := fun _ _ => rfl

theorem ExecSeq.append {h₁ h₂ h₃ : List (Lft × Val)} {e₁ e₂ e₃ : Env} {p q : List Stmt}
    (s₁ : ExecSeq h₁ e₁ p h₂ e₂) (s₂ : ExecSeq h₂ e₂ q h₃ e₃) : ExecSeq h₁ e₁ (p ++ q) h₃ e₃ := by
  intro f rest
  have e : f + (p ++ q).length = (f + q.length) + p.length := by
    simp only [List.length_append]; omega
  rw [e, List.append_assoc, s₁, s₂]

theorem ExecSeq.cons {h₁ h₂ h₃ : List (Lft × Val)} {e₁ e₂ e₃ : Env} {s : Stmt} {p : List Stmt}
    (s₁ : ExecSeq h₁ e₁ [s] h₂ e₂) (s₂ : ExecSeq h₂ e₂ p h₃ e₃) : ExecSeq h₁ e₁ (s :: p) h₃ e₃ :=
  ExecSeq.append s₁ s₂

theorem Lft.live_zero (l : Lft) : l.live 0 = true := by cases l <;> simp [Lft.live]

theorem m₀_lv (l : Lft) : m₀.lv l = true := by simp [m₀, Mode.lv, Lft.live_zero]

theorem m₀_inBody : m₀.inBody = false := rfl

theorem liveIn_m₀ (T : Ty) : T.liveIn m₀.lv = true := by
  induction T <;> simp_all [Ty.liveIn, m₀_lv]

theorem get_m₀ (Γ : Ctx) (y : Nat) : m₀.get Γ y = Γ y := by
  simp only [Mode.get]
  split <;> simp_all [liveIn_m₀]

@[simp] theorem Ctx.set_same (Γ : Ctx) (x : Nat) (T : Ty) : (Γ.set x T) x = some T := by
  simp [Ctx.set]
theorem Ctx.set_ne {Γ : Ctx} {x k : Nat} {T : Ty} (h : k ≠ x) : (Γ.set x T) k = Γ k := by
  simp [Ctx.set, h]
@[simp] theorem Env.set_same (e : Env) (x : Nat) (v : Val) : (e.set x v) x = some v := by
  simp [Env.set]
theorem Env.set_ne {e : Env} {x k : Nat} {v : Val} (h : k ≠ x) : (e.set x v) k = e k := by
  simp [Env.set, h]

section chkSteps
variable {sub : Ty → Ty → Bool} {Γ : Ctx}

theorem chk_unit (x : Nat) : ChkSeq sub Γ [.unit x] (Γ.set x .unit) := by
  intro f rest; simp [chk]
theorem chk_nat (x n : Nat) : ChkSeq sub Γ [.nat x n] (Γ.set x .nat) := by
  intro f rest; simp [chk]
theorem chk_copy {x y : Nat} {S T : Ty} (hy : Γ y = some S) (hT : T.closed = true)
    (hs : sub S T = true) : ChkSeq sub Γ [.copy x y T] (Γ.set x T) := by
  intro f rest; simp [chk, get_m₀, hy, hT, liveIn_m₀, hs]
theorem chk_alloc {x y : Nat} {l : Lft} {T : Ty} (hy : Γ y = some T) :
    ChkSeq sub Γ [.alloc x l y] (Γ.set x (.refMut l T)) := by
  intro f rest; simp [chk, get_m₀, hy, m₀_lv, m₀_inBody]
theorem chk_share {x y : Nat} {l : Lft} {T : Ty} (hy : Γ y = some (.refMut l T)) :
    ChkSeq sub Γ [.share x y] (Γ.set x (.ref l T)) := by
  intro f rest; simp [chk, get_m₀, hy]
theorem chk_newCell {x y : Nat} {l : Lft} {T : Ty} (hy : Γ y = some T) :
    ChkSeq sub Γ [.newCell x l y] (Γ.set x (.ref l (.cell T))) := by
  intro f rest; simp [chk, get_m₀, hy, m₀_lv, m₀_inBody]
theorem chk_read_ref {x y : Nat} {l : Lft} {T : Ty} (hy : Γ y = some (.ref l T)) :
    ChkSeq sub Γ [.read x y] (Γ.set x T) := by
  intro f rest; simp [chk, get_m₀, hy]
theorem chk_read_refMut {x y : Nat} {l : Lft} {T : Ty} (hy : Γ y = some (.refMut l T)) :
    ChkSeq sub Γ [.read x y] (Γ.set x T) := by
  intro f rest; simp [chk, get_m₀, hy]
theorem chk_write {y z : Nat} {l : Lft} {T : Ty} (hy : Γ y = some (.refMut l T))
    (hz : Γ z = some T) : ChkSeq sub Γ [.write y z] Γ := by
  intro f rest; simp [chk, get_m₀, hy, hz]
theorem chk_cellGet {x c : Nat} {l : Lft} {T : Ty} (hc : Γ c = some (.ref l (.cell T))) :
    ChkSeq sub Γ [.cellGet x c] (Γ.set x T) := by
  intro f rest; simp [chk, get_m₀, hc]
theorem chk_cellSet {c z : Nat} {l : Lft} {T : Ty} (hc : Γ c = some (.ref l (.cell T)))
    (hz : Γ z = some T) : ChkSeq sub Γ [.cellSet c z] Γ := by
  intro f rest; simp [chk, get_m₀, hc, hz]
theorem chk_pair {x y z : Nat} {A B : Ty} (hy : Γ y = some A) (hz : Γ z = some B) :
    ChkSeq sub Γ [.pair x y z] (Γ.set x (.prod A B)) := by
  intro f rest; simp [chk, get_m₀, hy, hz]
theorem chk_fst {x y : Nat} {A B : Ty} (hy : Γ y = some (.prod A B)) :
    ChkSeq sub Γ [.fst x y] (Γ.set x A) := by
  intro f rest; simp [chk, get_m₀, hy]
theorem chk_snd {x y : Nat} {A B : Ty} (hy : Γ y = some (.prod A B)) :
    ChkSeq sub Γ [.snd x y] (Γ.set x B) := by
  intro f rest; simp [chk, get_m₀, hy]

end chkSteps

section execSteps
variable {h : List (Lft × Val)} {env : Env}

theorem exec_unit (x : Nat) : ExecSeq h env [.unit x] h (env.set x .unit) := by
  intro f rest; simp [exec]
theorem exec_nat (x n : Nat) : ExecSeq h env [.nat x n] h (env.set x (.nat n)) := by
  intro f rest; simp [exec]
theorem exec_copy {x y : Nat} {T : Ty} {v : Val} (hy : env y = some v) :
    ExecSeq h env [.copy x y T] h (env.set x v) := by
  intro f rest; simp [exec, hy]
theorem exec_alloc {x y : Nat} {l : Lft} {v : Val} (hy : env y = some v) :
    ExecSeq h env [.alloc x l y] (h ++ [(l, v)]) (env.set x (.ptr h.length)) := by
  intro f rest; simp [exec, hy, Lft.live_zero]
theorem exec_share {x y : Nat} {v : Val} (hy : env y = some v) :
    ExecSeq h env [.share x y] h (env.set x v) := by
  intro f rest; simp [exec, hy]
theorem exec_newCell {x y : Nat} {l : Lft} {v : Val} (hy : env y = some v) :
    ExecSeq h env [.newCell x l y] (h ++ [(l, v)]) (env.set x (.ptr h.length)) := by
  intro f rest; simp [exec, hy, Lft.live_zero]
theorem exec_read {x y p : Nat} {r : Lft} {v : Val} (hy : env y = some (.ptr p))
    (hp : h[p]? = some (r, v)) : ExecSeq h env [.read x y] h (env.set x v) := by
  intro f rest; simp [exec, hy, hp, Lft.live_zero]
theorem exec_write {y z p : Nat} {r : Lft} {v w : Val} (hy : env y = some (.ptr p))
    (hz : env z = some v) (hp : h[p]? = some (r, w)) :
    ExecSeq h env [.write y z] (h.set p (r, v)) env := by
  intro f rest; simp [exec, hy, hz, hp, Lft.live_zero]
theorem exec_cellGet {x c p : Nat} {r : Lft} {v : Val} (hc : env c = some (.ptr p))
    (hp : h[p]? = some (r, v)) : ExecSeq h env [.cellGet x c] h (env.set x v) := by
  intro f rest; simp [exec, hc, hp, Lft.live_zero]
theorem exec_cellSet {c z p : Nat} {r : Lft} {v w : Val} (hc : env c = some (.ptr p))
    (hz : env z = some v) (hp : h[p]? = some (r, w)) :
    ExecSeq h env [.cellSet c z] (h.set p (r, v)) env := by
  intro f rest; simp [exec, hc, hz, hp, Lft.live_zero]
theorem exec_pair {x y z : Nat} {a b : Val} (hy : env y = some a) (hz : env z = some b) :
    ExecSeq h env [.pair x y z] h (env.set x (.pair a b)) := by
  intro f rest; simp [exec, hy, hz]
theorem exec_fst {x y : Nat} {a b : Val} (hy : env y = some (.pair a b)) :
    ExecSeq h env [.fst x y] h (env.set x a) := by
  intro f rest; simp [exec, hy]
theorem exec_snd {x y : Nat} {a b : Val} (hy : env y = some (.pair a b)) :
    ExecSeq h env [.snd x y] h (env.set x b) := by
  intro f rest; simp [exec, hy]

end execSteps

/-! ## Building values -/

/-- A bound on the number of variables the builders below use. -/
def Ty.sz : Ty → Nat
  | .prod T U => 1 + T.sz + U.sz
  | .ref _ T => 3 + T.sz
  | .refMut _ T => 3 + T.sz
  | .cell T => 3 + T.sz
  | .unit => 1
  | .nat => 1
  | .param => 1
  | .fn _ _ => 1
  | .phantom _ => 1

theorem Ty.one_le_sz (T : Ty) : 1 ≤ T.sz := by cases T <;> simp [Ty.sz] <;> omega

/-- Statements storing in variable `x` a value of type `F.subst A`, taking the value at every
parameter position from variable `a : A`, and writing only variables in `[x, x + F.sz)`. -/
def bld (A : Ty) (a : Nat) : Ty → Nat → List Stmt
  | .unit, x => [.unit x]
  | .nat, x => [.nat x 0]
  | .param, x => [.copy x a A]
  | .prod T U, x =>
    bld A a T (x + 1) ++ bld A a U (x + 1 + T.sz) ++ [.pair x (x + 1) (x + 1 + T.sz)]
  | .ref l T, x => bld A a T (x + 2) ++ [.alloc (x + 1) l (x + 2), .share x (x + 1)]
  | .refMut l T, x => bld A a T (x + 1) ++ [.alloc x l (x + 1)]
  | .cell T, x => bld A a T (x + 2) ++ [.newCell (x + 1) .static (x + 2), .read x (x + 1)]
  | .fn _ _, x => [.unit x]
  | .phantom _, x => [.unit x]

theorem bld_chk {sub : Ty → Ty → Bool} {A : Ty} (hA : A.closed = true) (hsub : sub A A = true)
    {a : Nat} : ∀ (F : Ty), F.fo = true → ∀ (x : Nat), a < x → ∀ (Γ : Ctx), Γ a = some A →
    ∃ Γ', ChkSeq sub Γ (bld A a F x) Γ' ∧ Γ' x = some (F.subst A) ∧
      ∀ k, (k < x ∨ x + F.sz ≤ k) → Γ' k = Γ k := by
  intro F
  induction F with
  | unit =>
    intro _ x _ Γ _
    exact ⟨_, chk_unit x, by simp [Ty.subst], fun k hk => Ctx.set_ne (by simp [Ty.sz] at hk; omega)⟩
  | nat =>
    intro _ x _ Γ _
    exact ⟨_, chk_nat x 0, by simp [Ty.subst], fun k hk => Ctx.set_ne (by simp [Ty.sz] at hk; omega)⟩
  | param =>
    intro _ x _ Γ hΓ
    exact ⟨_, chk_copy hΓ hA hsub, by simp [Ty.subst],
      fun k hk => Ctx.set_ne (by simp [Ty.sz] at hk; omega)⟩
  | fn _ _ _ _ => intro hf; simp [Ty.fo] at hf
  | phantom _ _ => intro hf; simp [Ty.fo] at hf
  | prod T U ihT ihU =>
    intro hf x hax Γ hΓ
    simp only [Ty.fo, Bool.and_eq_true] at hf
    have hT1 := T.one_le_sz
    obtain ⟨Γ₁, c₁, e₁, p₁⟩ := ihT hf.1 (x + 1) (by omega) Γ hΓ
    obtain ⟨Γ₂, c₂, e₂, p₂⟩ := ihU hf.2 (x + 1 + T.sz) (by omega) Γ₁
      (by rw [p₁ a (Or.inl (by omega))]; exact hΓ)
    have h1 : Γ₂ (x + 1) = some (T.subst A) := by rw [p₂ _ (Or.inl (by omega))]; exact e₁
    refine ⟨_, (c₁.append c₂).append (chk_pair h1 e₂), by simp [Ty.subst], fun k hk => ?_⟩
    simp only [Ty.sz] at hk
    rw [Ctx.set_ne (by omega), p₂ k (by omega), p₁ k (by omega)]
  | ref l T ih =>
    intro hf x hax Γ hΓ
    simp only [Ty.fo] at hf
    obtain ⟨Γ₁, c₁, e₁, p₁⟩ := ih hf (x + 2) (by omega) Γ hΓ
    have c₂ := chk_alloc (sub := sub) (x := x + 1) (l := l) e₁
    have c₃ := chk_share (sub := sub) (x := x) (Γ := Γ₁.set (x + 1) (.refMut l (T.subst A)))
      (Ctx.set_same _ _ _)
    refine ⟨_, c₁.append (c₂.cons (c₃.cons (ChkSeq.nil _ _))), by simp [Ty.subst],
      fun k hk => ?_⟩
    simp only [Ty.sz] at hk
    rw [Ctx.set_ne (by omega), Ctx.set_ne (by omega), p₁ k (by omega)]
  | refMut l T ih =>
    intro hf x hax Γ hΓ
    simp only [Ty.fo] at hf
    obtain ⟨Γ₁, c₁, e₁, p₁⟩ := ih hf (x + 1) (by omega) Γ hΓ
    have c₂ := chk_alloc (sub := sub) (x := x) (l := l) e₁
    refine ⟨_, c₁.append (c₂.cons (ChkSeq.nil _ _)), by simp [Ty.subst], fun k hk => ?_⟩
    simp only [Ty.sz] at hk
    rw [Ctx.set_ne (by omega), p₁ k (by omega)]
  | cell T ih =>
    intro hf x hax Γ hΓ
    simp only [Ty.fo] at hf
    obtain ⟨Γ₁, c₁, e₁, p₁⟩ := ih hf (x + 2) (by omega) Γ hΓ
    have c₂ := chk_newCell (sub := sub) (x := x + 1) (l := .static) e₁
    have c₃ := chk_read_ref (sub := sub) (x := x)
      (Γ := Γ₁.set (x + 1) (.ref .static (.cell (T.subst A)))) (Ctx.set_same _ _ _)
    refine ⟨_, c₁.append (c₂.cons (c₃.cons (ChkSeq.nil _ _))), by simp [Ty.subst],
      fun k hk => ?_⟩
    simp only [Ty.sz] at hk
    rw [Ctx.set_ne (by omega), Ctx.set_ne (by omega), p₁ k (by omega)]

/-- `Rep h b va F v`: the runtime value `v` has the shape of `F`, with `va` at every parameter
position, following heap locations `≥ b` for references. -/
def Rep (h : List (Lft × Val)) (b : Nat) (va : Val) : Ty → Val → Prop
  | .param, v => v = va
  | .prod T U, v => ∃ v₁ v₂, v = .pair v₁ v₂ ∧ Rep h b va T v₁ ∧ Rep h b va U v₂
  | .ref _ T, v => ∃ p r w, v = .ptr p ∧ b ≤ p ∧ h[p]? = some (r, w) ∧ Rep h b va T w
  | .refMut _ T, v => ∃ p r w, v = .ptr p ∧ b ≤ p ∧ h[p]? = some (r, w) ∧ Rep h b va T w
  | .cell T, v => Rep h b va T v
  | .unit, _ => True
  | .nat, _ => True
  | .fn _ _, _ => True
  | .phantom _, _ => True

theorem Rep.append {h : List (Lft × Val)} {b : Nat} {va : Val} (e : List (Lft × Val)) :
    ∀ (F : Ty) (v : Val), Rep h b va F v → Rep (h ++ e) b va F v := by
  intro F
  induction F with
  | param => intro v hv; exact hv
  | prod T U ihT ihU =>
    intro v ⟨v₁, v₂, hv, r₁, r₂⟩; exact ⟨v₁, v₂, hv, ihT v₁ r₁, ihU v₂ r₂⟩
  | ref _ T ih =>
    intro v ⟨p, r, w, hv, hb, hp, hr⟩; exact ⟨p, r, w, hv, hb, get_append_left h e p hp, ih w hr⟩
  | refMut _ T ih =>
    intro v ⟨p, r, w, hv, hb, hp, hr⟩; exact ⟨p, r, w, hv, hb, get_append_left h e p hp, ih w hr⟩
  | cell T ih => intro v hv; exact ih v hv
  | unit => intro _ _; trivial
  | nat => intro _ _; trivial
  | fn _ _ _ _ => intro _ _; trivial
  | phantom _ _ => intro _ _; trivial

theorem Rep.base_le {h : List (Lft × Val)} {b b' : Nat} {va : Val} (hb : b' ≤ b) :
    ∀ (F : Ty) (v : Val), Rep h b va F v → Rep h b' va F v := by
  intro F
  induction F with
  | param => intro v hv; exact hv
  | prod T U ihT ihU =>
    intro v ⟨v₁, v₂, hv, r₁, r₂⟩; exact ⟨v₁, v₂, hv, ihT v₁ r₁, ihU v₂ r₂⟩
  | ref _ T ih =>
    intro v ⟨p, r, w, hv, hp', hp, hr⟩; exact ⟨p, r, w, hv, by omega, hp, ih w hr⟩
  | refMut _ T ih =>
    intro v ⟨p, r, w, hv, hp', hp, hr⟩; exact ⟨p, r, w, hv, by omega, hp, ih w hr⟩
  | cell T ih => intro v hv; exact ih v hv
  | unit => intro _ _; trivial
  | nat => intro _ _; trivial
  | fn _ _ _ _ => intro _ _; trivial
  | phantom _ _ => intro _ _; trivial

theorem Rep.set {h : List (Lft × Val)} {b : Nat} {va : Val} {q : Nat} (e : Lft × Val)
    (hq : q < b) : ∀ (F : Ty) (v : Val), Rep h b va F v → Rep (h.set q e) b va F v := by
  intro F
  induction F with
  | param => intro v hv; exact hv
  | prod T U ihT ihU =>
    intro v ⟨v₁, v₂, hv, r₁, r₂⟩; exact ⟨v₁, v₂, hv, ihT v₁ r₁, ihU v₂ r₂⟩
  | ref _ T ih =>
    intro v ⟨p, r, w, hv, hb, hp, hr⟩
    exact ⟨p, r, w, hv, hb, by rw [get_set_ne h q p e (by omega)]; exact hp, ih w hr⟩
  | refMut _ T ih =>
    intro v ⟨p, r, w, hv, hb, hp, hr⟩
    exact ⟨p, r, w, hv, hb, by rw [get_set_ne h q p e (by omega)]; exact hp, ih w hr⟩
  | cell T ih => intro v hv; exact ih v hv
  | unit => intro _ _; trivial
  | nat => intro _ _; trivial
  | fn _ _ _ _ => intro _ _; trivial
  | phantom _ _ => intro _ _; trivial

theorem bld_exec {A : Ty} {a : Nat} {va : Val} : ∀ (F : Ty), F.fo = true → ∀ (x : Nat), a < x →
    ∀ (h : List (Lft × Val)) (env : Env), env a = some va →
    ∃ ext env' v, ExecSeq h env (bld A a F x) (h ++ ext) env' ∧ env' x = some v ∧
      (∀ k, (k < x ∨ x + F.sz ≤ k) → env' k = env k) ∧ Rep (h ++ ext) h.length va F v := by
  intro F
  induction F with
  | unit =>
    intro _ x _ h env _
    exact ⟨[], _, _, by rw [List.append_nil]; exact exec_unit x, Env.set_same _ _ _,
      fun k hk => Env.set_ne (by simp [Ty.sz] at hk; omega), trivial⟩
  | nat =>
    intro _ x _ h env _
    exact ⟨[], _, _, by rw [List.append_nil]; exact exec_nat x 0, Env.set_same _ _ _,
      fun k hk => Env.set_ne (by simp [Ty.sz] at hk; omega), trivial⟩
  | param =>
    intro _ x _ h env he
    exact ⟨[], _, _, by rw [List.append_nil]; exact exec_copy (T := A) (x := x) he, Env.set_same _ _ _,
      fun k hk => Env.set_ne (by simp [Ty.sz] at hk; omega), rfl⟩
  | fn _ _ _ _ => intro hf; simp [Ty.fo] at hf
  | phantom _ _ => intro hf; simp [Ty.fo] at hf
  | prod T U ihT ihU =>
    intro hf x hax h env he
    simp only [Ty.fo, Bool.and_eq_true] at hf
    have hT1 := T.one_le_sz
    obtain ⟨e₁, env₁, v₁, s₁, g₁, p₁, r₁⟩ := ihT hf.1 (x + 1) (by omega) h env he
    obtain ⟨e₂, env₂, v₂, s₂, g₂, p₂, r₂⟩ := ihU hf.2 (x + 1 + T.sz) (by omega) (h ++ e₁) env₁
      (by rw [p₁ a (Or.inl (by omega))]; exact he)
    have g₁' : env₂ (x + 1) = some v₁ := by rw [p₂ _ (Or.inl (by omega))]; exact g₁
    have s₃ := exec_pair (h := h ++ e₁ ++ e₂) (x := x) g₁' g₂
    refine ⟨e₁ ++ e₂, env₂.set x (.pair v₁ v₂), .pair v₁ v₂, ?_, Env.set_same _ _ _,
      fun k hk => ?_, ?_⟩
    · rw [← List.append_assoc]; exact (s₁.append s₂).append s₃
    · simp only [Ty.sz] at hk
      rw [Env.set_ne (by omega), p₂ k (by omega), p₁ k (by omega)]
    · rw [← List.append_assoc]
      refine ⟨v₁, v₂, rfl, Rep.append e₂ T v₁ r₁, Rep.base_le ?_ U v₂ r₂⟩
      simp
  | ref l T ih =>
    intro hf x hax h env he
    simp only [Ty.fo] at hf
    obtain ⟨e₁, env₁, w, s₁, g₁, p₁, r₁⟩ := ih hf (x + 2) (by omega) h env he
    have s₂ := exec_alloc (h := h ++ e₁) (x := x + 1) (l := l) g₁
    have s₃ := exec_share (h := h ++ e₁ ++ [(l, w)]) (x := x) (env := env₁.set (x + 1) (.ptr (h ++ e₁).length))
      (Env.set_same _ _ _)
    refine ⟨e₁ ++ [(l, w)], (env₁.set (x + 1) (.ptr (h ++ e₁).length)).set x
      (.ptr (h ++ e₁).length), .ptr (h ++ e₁).length, ?_, Env.set_same _ _ _, fun k hk => ?_, ?_⟩
    · rw [← List.append_assoc]; exact s₁.append (s₂.cons (s₃.cons (ExecSeq.nil _ _)))
    · simp only [Ty.sz] at hk
      rw [Env.set_ne (by omega), Env.set_ne (by omega), p₁ k (by omega)]
    · rw [← List.append_assoc]
      refine ⟨(h ++ e₁).length, l, w, rfl, by simp, get_append_len _ _, Rep.append _ T w r₁⟩
  | refMut l T ih =>
    intro hf x hax h env he
    simp only [Ty.fo] at hf
    obtain ⟨e₁, env₁, w, s₁, g₁, p₁, r₁⟩ := ih hf (x + 1) (by omega) h env he
    have s₂ := exec_alloc (h := h ++ e₁) (x := x) (l := l) g₁
    refine ⟨e₁ ++ [(l, w)], env₁.set x (.ptr (h ++ e₁).length), .ptr (h ++ e₁).length, ?_,
      Env.set_same _ _ _, fun k hk => ?_, ?_⟩
    · rw [← List.append_assoc]; exact s₁.append (s₂.cons (ExecSeq.nil _ _))
    · simp only [Ty.sz] at hk
      rw [Env.set_ne (by omega), p₁ k (by omega)]
    · rw [← List.append_assoc]
      refine ⟨(h ++ e₁).length, l, w, rfl, by simp, get_append_len _ _, Rep.append _ T w r₁⟩
  | cell T ih =>
    intro hf x hax h env he
    simp only [Ty.fo] at hf
    obtain ⟨e₁, env₁, w, s₁, g₁, p₁, r₁⟩ := ih hf (x + 2) (by omega) h env he
    have s₂ := exec_newCell (h := h ++ e₁) (x := x + 1) (l := .static) g₁
    have s₃ := exec_read (h := h ++ e₁ ++ [(.static, w)]) (x := x)
      (env := env₁.set (x + 1) (.ptr (h ++ e₁).length)) (Env.set_same _ _ _)
      (get_append_len _ _)
    refine ⟨e₁ ++ [(.static, w)], (env₁.set (x + 1) (.ptr (h ++ e₁).length)).set x w, w, ?_,
      Env.set_same _ _ _, fun k hk => ?_, ?_⟩
    · rw [← List.append_assoc]; exact s₁.append (s₂.cons (s₃.cons (ExecSeq.nil _ _)))
    · simp only [Ty.sz] at hk
      rw [Env.set_ne (by omega), Env.set_ne (by omega), p₁ k (by omega)]
    · rw [← List.append_assoc]
      exact Rep.append _ T w r₁

/-! ## Projecting to a parameter position -/

/-- Statements projecting the value in variable `x` (of type `F.subst B`) down to a parameter
position (the leftmost one that exists); bare cells are boxed and read with `cellGet`. -/
def navS : Ty → Nat → List Stmt
  | .prod T U, x =>
    if T.closed then .snd (x + 1) x :: navS U (x + 1) else .fst (x + 1) x :: navS T (x + 1)
  | .ref _ T, x => .read (x + 1) x :: navS T (x + 1)
  | .refMut _ T, x => .read (x + 1) x :: navS T (x + 1)
  | .cell T, x =>
    .alloc (x + 1) .static x :: .share (x + 2) (x + 1) :: .cellGet (x + 3) (x + 2) :: navS T (x + 3)
  | _, _ => []

/-- The variable holding the result of `navS F x`. -/
def navO : Ty → Nat → Nat
  | .prod T U, x => if T.closed then navO U (x + 1) else navO T (x + 1)
  | .ref _ T, x => navO T (x + 1)
  | .refMut _ T, x => navO T (x + 1)
  | .cell T, x => navO T (x + 3)
  | _, x => x

theorem nav_chk {sub : Ty → Ty → Bool} (B : Ty) : ∀ (F : Ty), F.fo = true → F.closed = false →
    ∀ (x : Nat) (Γ : Ctx), Γ x = some (F.subst B) →
    ∃ Γ', ChkSeq sub Γ (navS F x) Γ' ∧ Γ' (navO F x) = some B := by
  intro F
  induction F with
  | param => intro _ _ x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ⟩
  | unit => intro _ hc; simp [Ty.closed] at hc
  | nat => intro _ hc; simp [Ty.closed] at hc
  | fn _ _ _ _ => intro hf; simp [Ty.fo] at hf
  | phantom _ _ => intro hf; simp [Ty.fo] at hf
  | prod T U ihT ihU =>
    intro hf hc x Γ hΓ
    simp only [Ty.fo, Bool.and_eq_true] at hf
    cases hT : T.closed
    · have c₁ := chk_fst (sub := sub) (x := x + 1) hΓ
      obtain ⟨Γ', c₂, e⟩ := ihT hf.1 hT (x + 1) _ (Ctx.set_same _ _ _)
      exact ⟨Γ', by simp only [navS, hT]; exact c₁.cons c₂, by simp only [navO, hT]; exact e⟩
    · have hU : U.closed = false := by simp [Ty.closed, hT] at hc; exact hc
      have c₁ := chk_snd (sub := sub) (x := x + 1) hΓ
      obtain ⟨Γ', c₂, e⟩ := ihU hf.2 hU (x + 1) _ (Ctx.set_same _ _ _)
      exact ⟨Γ', by simp only [navS, hT]; exact c₁.cons c₂, by simp only [navO, hT]; exact e⟩
  | ref l T ih =>
    intro hf hc x Γ hΓ
    have c₁ := chk_read_ref (sub := sub) (x := x + 1) hΓ
    obtain ⟨Γ', c₂, e⟩ := ih hf hc (x + 1) _ (Ctx.set_same _ _ _)
    exact ⟨Γ', c₁.cons c₂, e⟩
  | refMut l T ih =>
    intro hf hc x Γ hΓ
    have c₁ := chk_read_refMut (sub := sub) (x := x + 1) hΓ
    obtain ⟨Γ', c₂, e⟩ := ih hf hc (x + 1) _ (Ctx.set_same _ _ _)
    exact ⟨Γ', c₁.cons c₂, e⟩
  | cell T ih =>
    intro hf hc x Γ hΓ
    have c₁ := chk_alloc (sub := sub) (x := x + 1) (l := .static) hΓ
    have c₂ := chk_share (sub := sub) (x := x + 2) (Ctx.set_same Γ (x + 1)
      (.refMut .static (.cell (T.subst B))))
    have c₃ := chk_cellGet (sub := sub) (x := x + 3) (Ctx.set_same
      (Γ.set (x + 1) (.refMut .static (.cell (T.subst B)))) (x + 2) (.ref .static (.cell (T.subst B))))
    obtain ⟨Γ', c₄, e⟩ := ih hf hc (x + 3) _ (Ctx.set_same _ _ _)
    exact ⟨Γ', c₁.cons (c₂.cons (c₃.cons c₄)), e⟩

theorem nav_exec {va : Val} : ∀ (F : Ty), F.fo = true → F.closed = false →
    ∀ (x : Nat) (h : List (Lft × Val)) (b : Nat) (env : Env) (v : Val), env x = some v →
    Rep h b va F v → ∃ ext env', ExecSeq h env (navS F x) (h ++ ext) env' ∧
      env' (navO F x) = some va := by
  intro F
  induction F with
  | param => intro _ _ x h b env v he hr; exact ⟨[], env, by rw [List.append_nil]; exact ExecSeq.nil h env, hr ▸ he⟩
  | unit => intro _ hc; simp [Ty.closed] at hc
  | nat => intro _ hc; simp [Ty.closed] at hc
  | fn _ _ _ _ => intro hf; simp [Ty.fo] at hf
  | phantom _ _ => intro hf; simp [Ty.fo] at hf
  | prod T U ihT ihU =>
    intro hf hc x h b env v he hr
    simp only [Ty.fo, Bool.and_eq_true] at hf
    obtain ⟨v₁, v₂, rfl, r₁, r₂⟩ := hr
    cases hT : T.closed
    · have s₁ := exec_fst (h := h) (x := x + 1) he
      obtain ⟨ext, env', s₂, e⟩ := ihT hf.1 hT (x + 1) h b _ v₁ (Env.set_same _ _ _) r₁
      exact ⟨ext, env', by simp only [navS, hT]; exact s₁.cons s₂, by simp only [navO, hT]; exact e⟩
    · have hU : U.closed = false := by simp [Ty.closed, hT] at hc; exact hc
      have s₁ := exec_snd (h := h) (x := x + 1) he
      obtain ⟨ext, env', s₂, e⟩ := ihU hf.2 hU (x + 1) h b _ v₂ (Env.set_same _ _ _) r₂
      exact ⟨ext, env', by simp only [navS, hT]; exact s₁.cons s₂, by simp only [navO, hT]; exact e⟩
  | ref l T ih =>
    intro hf hc x h b env v he hr
    obtain ⟨p, r, w, rfl, _, hp, hw⟩ := hr
    have s₁ := exec_read (x := x + 1) he hp
    obtain ⟨ext, env', s₂, e⟩ := ih hf hc (x + 1) h b _ w (Env.set_same _ _ _) hw
    exact ⟨ext, env', s₁.cons s₂, e⟩
  | refMut l T ih =>
    intro hf hc x h b env v he hr
    obtain ⟨p, r, w, rfl, _, hp, hw⟩ := hr
    have s₁ := exec_read (x := x + 1) he hp
    obtain ⟨ext, env', s₂, e⟩ := ih hf hc (x + 1) h b _ w (Env.set_same _ _ _) hw
    exact ⟨ext, env', s₁.cons s₂, e⟩
  | cell T ih =>
    intro hf hc x h b env v he hr
    have s₁ := exec_alloc (h := h) (x := x + 1) (l := .static) he
    have s₂ := exec_share (h := h ++ [(.static, v)]) (x := x + 2)
      (Env.set_same env (x + 1) (.ptr h.length))
    have s₃ := exec_cellGet (h := h ++ [(.static, v)]) (x := x + 3)
      (Env.set_same ((env.set (x + 1) (.ptr h.length))) (x + 2) (.ptr h.length))
      (get_append_len h (.static, v))
    obtain ⟨ext, env', s₄, e⟩ := ih hf hc (x + 3) (h ++ [(.static, v)]) b _ v (Env.set_same _ _ _)
      (Rep.append _ T v hr)
    refine ⟨[(.static, v)] ++ ext, env', ?_, e⟩
    rw [← List.append_assoc]
    exact s₁.cons (s₂.cons (s₃.cons s₄))

/-! ## Navigating to an invariant position -/

def Ty.isCell : Ty → Bool
  | .cell _ => true
  | _ => false

/-- Statements navigating from variable `x` to a `refMut` or `ref ℓ (cell _)` node that has a
parameter occurrence below it. -/
def invS : Ty → Nat → List Stmt
  | .prod T U, x =>
    if T.invOcc then .fst (x + 1) x :: invS T (x + 1) else .snd (x + 1) x :: invS U (x + 1)
  | .ref _ T, x => if T.isCell then [] else .read (x + 1) x :: invS T (x + 1)
  | _, _ => []

def invO : Ty → Nat → Nat
  | .prod T U, x => if T.invOcc then invO T (x + 1) else invO U (x + 1)
  | .ref _ T, x => if T.isCell then x else invO T (x + 1)
  | _, x => x

/-- The type of the node reached by `invS`. -/
def invTarget : Ty → Ty
  | .prod T U => if T.invOcc then invTarget T else invTarget U
  | .ref l T => if T.isCell then .ref l T else invTarget T
  | T => T

/-- The value reached by `invS`. -/
def invPtr (h : List (Lft × Val)) : Ty → Val → Val
  | .prod T U, .pair v₁ v₂ => if T.invOcc then invPtr h T v₁ else invPtr h U v₂
  | .ref _ T, .ptr p =>
    if T.isCell then .ptr p else
      match h[p]? with
      | some (_, w) => invPtr h T w
      | none => .ptr p
  | _, v => v

theorem invO_bounds : ∀ (F : Ty) (x : Nat), x ≤ invO F x ∧ invO F x < x + F.sz := by
  intro F
  induction F with
  | prod T U ihT ihU =>
    intro x
    have := T.one_le_sz; have := U.one_le_sz
    simp only [invO, Ty.sz]
    split
    · have := ihT (x + 1); omega
    · have := ihU (x + 1); omega
  | ref l T ih =>
    intro x
    simp only [invO, Ty.sz]
    split
    · omega
    · have := ih (x + 1); omega
  | unit => intro x; simp [invO, Ty.sz]
  | nat => intro x; simp [invO, Ty.sz]
  | param => intro x; simp [invO, Ty.sz]
  | refMut _ T _ => intro x; simp [invO, Ty.sz]; omega
  | cell T _ => intro x; simp [invO, Ty.sz]; omega
  | fn _ _ _ _ => intro x; simp [invO, Ty.sz]
  | phantom _ _ => intro x; simp [invO, Ty.sz]

theorem invS_chk {sub : Ty → Ty → Bool} (B : Ty) : ∀ (F : Ty), ∀ (x : Nat) (Γ : Ctx),
    Γ x = some (F.subst B) →
    ∃ Γ', ChkSeq sub Γ (invS F x) Γ' ∧ Γ' (invO F x) = some ((invTarget F).subst B) ∧
      ∀ k, (k ≤ x ∨ x + F.sz ≤ k) → Γ' k = Γ k := by
  intro F
  induction F with
  | prod T U ihT ihU =>
    intro x Γ hΓ
    have := T.one_le_sz; have := U.one_le_sz
    cases hT : T.invOcc
    · have c₁ := chk_snd (sub := sub) (x := x + 1) hΓ
      obtain ⟨Γ', c₂, e, p⟩ := ihU (x + 1) _ (Ctx.set_same _ _ _)
      refine ⟨Γ', by simp only [invS, hT]; exact c₁.cons c₂,
        by simp only [invO, invTarget, hT]; exact e, fun k hk => ?_⟩
      simp only [Ty.sz] at hk
      rw [p k (by omega), Ctx.set_ne (by omega)]
    · have c₁ := chk_fst (sub := sub) (x := x + 1) hΓ
      obtain ⟨Γ', c₂, e, p⟩ := ihT (x + 1) _ (Ctx.set_same _ _ _)
      refine ⟨Γ', by simp only [invS, hT]; exact c₁.cons c₂,
        by simp only [invO, invTarget, hT]; exact e, fun k hk => ?_⟩
      simp only [Ty.sz] at hk
      rw [p k (by omega), Ctx.set_ne (by omega)]
  | ref l T ih =>
    intro x Γ hΓ
    cases hT : T.isCell
    · have c₁ := chk_read_ref (sub := sub) (x := x + 1) hΓ
      obtain ⟨Γ', c₂, e, p⟩ := ih (x + 1) _ (Ctx.set_same _ _ _)
      refine ⟨Γ', by simp only [invS, hT]; exact c₁.cons c₂,
        by simp only [invO, invTarget, hT]; exact e, fun k hk => ?_⟩
      simp only [Ty.sz] at hk
      rw [p k (by omega), Ctx.set_ne (by omega)]
    · exact ⟨Γ, by simp only [invS, hT]; exact ChkSeq.nil _ _,
        by simp only [invO, invTarget, hT]; exact hΓ, fun _ _ => rfl⟩
  | unit => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩
  | nat => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩
  | param => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩
  | refMut _ _ _ => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩
  | cell _ _ => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩
  | fn _ _ _ _ => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩
  | phantom _ _ => intro x Γ hΓ; exact ⟨Γ, ChkSeq.nil _ _, hΓ, fun _ _ => rfl⟩

theorem invS_exec {va : Val} : ∀ (F : Ty), ∀ (x : Nat) (h : List (Lft × Val)) (b : Nat)
    (env : Env) (v : Val), env x = some v → Rep h b va F v →
    ∃ env', ExecSeq h env (invS F x) h env' ∧ env' (invO F x) = some (invPtr h F v) ∧
      ∀ k, (k ≤ x ∨ x + F.sz ≤ k) → env' k = env k := by
  intro F
  induction F with
  | prod T U ihT ihU =>
    intro x h b env v he hr
    have := T.one_le_sz; have := U.one_le_sz
    obtain ⟨v₁, v₂, rfl, r₁, r₂⟩ := hr
    cases hT : T.invOcc
    · have s₁ := exec_snd (h := h) (x := x + 1) he
      obtain ⟨env', s₂, e, p⟩ := ihU (x + 1) h b _ v₂ (Env.set_same _ _ _) r₂
      refine ⟨env', by simp only [invS, hT]; exact s₁.cons s₂,
        by simp only [invO, invPtr, hT]; exact e, fun k hk => ?_⟩
      simp only [Ty.sz] at hk
      rw [p k (by omega), Env.set_ne (by omega)]
    · have s₁ := exec_fst (h := h) (x := x + 1) he
      obtain ⟨env', s₂, e, p⟩ := ihT (x + 1) h b _ v₁ (Env.set_same _ _ _) r₁
      refine ⟨env', by simp only [invS, hT]; exact s₁.cons s₂,
        by simp only [invO, invPtr, hT]; exact e, fun k hk => ?_⟩
      simp only [Ty.sz] at hk
      rw [p k (by omega), Env.set_ne (by omega)]
  | ref l T ih =>
    intro x h b env v he hr
    obtain ⟨p, r, w, rfl, _, hp, hw⟩ := hr
    cases hT : T.isCell
    · have s₁ := exec_read (x := x + 1) he hp
      obtain ⟨env', s₂, e, pr⟩ := ih (x + 1) h b _ w (Env.set_same _ _ _) hw
      refine ⟨env', by simp only [invS, hT]; exact s₁.cons s₂,
        by simp only [invO, invPtr, hT, hp]; exact e, fun k hk => ?_⟩
      simp only [Ty.sz] at hk
      rw [pr k (by omega), Env.set_ne (by omega)]
    · exact ⟨env, by simp only [invS, hT]; exact ExecSeq.nil _ _,
        by simp only [invO, invPtr, hT]; exact he, fun _ _ => rfl⟩
  | unit => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩
  | nat => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩
  | param => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩
  | refMut _ _ _ => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩
  | cell _ _ => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩
  | fn _ _ _ _ => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩
  | phantom _ _ => intro x h b env v he _; exact ⟨env, ExecSeq.nil _ _, he, fun _ _ => rfl⟩

theorem Ty.dataBodyAt_flag {T : Ty} (hT : T.isCell = false) (b b' : Bool) :
    T.dataBodyAt b = T.dataBodyAt b' := by
  cases T <;> simp_all [Ty.dataBodyAt, Ty.isCell]

theorem invPtr_ptr {va : Val} : ∀ (F : Ty), F.dataBodyAt false = true → F.invOcc = true →
    ∀ (h : List (Lft × Val)) (b : Nat) (v : Val), Rep h b va F v →
    ∃ p r w, invPtr h F v = .ptr p ∧ b ≤ p ∧ h[p]? = some (r, w) := by
  intro F
  induction F with
  | prod T U ihT ihU =>
    intro hd hi h b v hr
    simp only [Ty.dataBodyAt, Bool.and_eq_true] at hd
    obtain ⟨v₁, v₂, rfl, r₁, r₂⟩ := hr
    cases hT : T.invOcc
    · have hU : U.invOcc = true := by simp [Ty.invOcc, hT] at hi; exact hi
      obtain ⟨p, r, w, e, hb, hp⟩ := ihU hd.2 hU h b v₂ r₂
      exact ⟨p, r, w, by simp only [invPtr, hT]; exact e, hb, hp⟩
    · obtain ⟨p, r, w, e, hb, hp⟩ := ihT hd.1 hT h b v₁ r₁
      exact ⟨p, r, w, by simp only [invPtr, hT]; exact e, hb, hp⟩
  | ref l T ih =>
    intro hd hi h b v hr
    simp only [Ty.dataBodyAt] at hd
    simp only [Ty.invOcc] at hi
    obtain ⟨p, r, w, rfl, hb, hp, hw⟩ := hr
    cases hT : T.isCell
    · rw [Ty.dataBodyAt_flag hT true false] at hd
      obtain ⟨p', r', w', e, hb', hp'⟩ := ih hd hi h b w hw
      exact ⟨p', r', w', by simp only [invPtr, hT, hp]; exact e, hb', hp'⟩
    · exact ⟨p, r, w, by simp only [invPtr, hT, ite_true], hb, hp⟩
  | refMut l T ih =>
    intro hd hi h b v hr
    obtain ⟨p, r, w, rfl, hb, hp, _⟩ := hr
    exact ⟨p, r, w, by simp [invPtr], hb, hp⟩
  | cell T _ => intro hd; simp [Ty.dataBodyAt] at hd
  | unit => intro _ hi; simp [Ty.invOcc] at hi
  | nat => intro _ hi; simp [Ty.invOcc] at hi
  | param => intro _ hi; simp [Ty.invOcc] at hi
  | fn _ _ _ _ => intro hd; simp [Ty.dataBodyAt] at hd
  | phantom _ _ => intro hd; simp [Ty.dataBodyAt] at hd

theorem invTarget_shape : ∀ (F : Ty), F.dataBodyAt false = true → F.invOcc = true →
    ∃ l G, G.closed = false ∧ G.fo = true ∧
      (invTarget F = .refMut l G ∨ invTarget F = .ref l (.cell G)) := by
  intro F
  induction F with
  | prod T U ihT ihU =>
    intro hd hi
    simp only [Ty.dataBodyAt, Bool.and_eq_true] at hd
    cases hT : T.invOcc
    · have hU : U.invOcc = true := by simp [Ty.invOcc, hT] at hi; exact hi
      obtain ⟨l, G, h₁, h₂, h₃⟩ := ihU hd.2 hU
      exact ⟨l, G, h₁, h₂, by simp only [invTarget, hT]; exact h₃⟩
    · obtain ⟨l, G, h₁, h₂, h₃⟩ := ihT hd.1 hT
      exact ⟨l, G, h₁, h₂, by simp only [invTarget, hT]; exact h₃⟩
  | ref l T ih =>
    intro hd hi
    simp only [Ty.dataBodyAt] at hd
    simp only [Ty.invOcc] at hi
    cases hT : T.isCell
    · rw [Ty.dataBodyAt_flag hT true false] at hd
      obtain ⟨l', G, h₁, h₂, h₃⟩ := ih hd hi
      exact ⟨l', G, h₁, h₂, by simp only [invTarget, hT]; exact h₃⟩
    · cases T with
      | cell G =>
        simp only [Ty.dataBodyAt, Bool.true_and] at hd
        simp only [Ty.invOcc, Bool.not_eq_true'] at hi
        exact ⟨l, G, hi, Ty.fo_of_dataBodyAt G false hd, Or.inr (by simp [invTarget, Ty.isCell])⟩
      | _ => simp [Ty.isCell] at hT
  | refMut l T _ =>
    intro hd hi
    simp only [Ty.dataBodyAt] at hd
    simp only [Ty.invOcc, Bool.not_eq_true'] at hi
    exact ⟨l, T, hi, Ty.fo_of_dataBodyAt T false hd, Or.inl rfl⟩
  | cell T _ => intro hd; simp [Ty.dataBodyAt] at hd
  | unit => intro _ hi; simp [Ty.invOcc] at hi
  | nat => intro _ hi; simp [Ty.invOcc] at hi
  | param => intro _ hi; simp [Ty.invOcc] at hi
  | fn _ _ _ _ => intro hd; simp [Ty.dataBodyAt] at hd
  | phantom _ _ => intro hd; simp [Ty.dataBodyAt] at hd

/-- Store through the reached node: `write` for `&mut`, `cellSet` for `&Cell`. -/
def invWrite : Ty → Nat → Nat → Stmt
  | .refMut _ _, o, z => .write o z
  | _, o, z => .cellSet o z

/-- Load through the reached node: `read` for `&mut`, `cellGet` for `&Cell`. -/
def invRead : Ty → Nat → Nat → Stmt
  | .refMut _ _, x, o => .read x o
  | _, x, o => .cellGet x o

section invSteps
variable {Tg G : Ty} {l : Lft}

theorem invWrite_chk {sub : Ty → Ty → Bool} {Γ : Ctx} {B : Ty} {o z : Nat}
    (hs : Tg = .refMut l G ∨ Tg = .ref l (.cell G)) (ho : Γ o = some (Tg.subst B))
    (hz : Γ z = some (G.subst B)) : ChkSeq sub Γ [invWrite Tg o z] Γ := by
  rcases hs with rfl | rfl
  · exact chk_write ho hz
  · exact chk_cellSet ho hz

theorem invRead_chk {sub : Ty → Ty → Bool} {Γ : Ctx} {B : Ty} {x o : Nat}
    (hs : Tg = .refMut l G ∨ Tg = .ref l (.cell G)) (ho : Γ o = some (Tg.subst B)) :
    ChkSeq sub Γ [invRead Tg x o] (Γ.set x (G.subst B)) := by
  rcases hs with rfl | rfl
  · exact chk_read_refMut ho
  · exact chk_cellGet ho

theorem invWrite_exec {h : List (Lft × Val)} {env : Env} {o z p : Nat} {r : Lft} {g w : Val}
    (hs : Tg = .refMut l G ∨ Tg = .ref l (.cell G)) (ho : env o = some (.ptr p))
    (hz : env z = some g) (hp : h[p]? = some (r, w)) :
    ExecSeq h env [invWrite Tg o z] (h.set p (r, g)) env := by
  rcases hs with rfl | rfl
  · exact exec_write ho hz hp
  · exact exec_cellSet ho hz hp

theorem invRead_exec {h : List (Lft × Val)} {env : Env} {x o p : Nat} {r : Lft} {g : Val}
    (hs : Tg = .refMut l G ∨ Tg = .ref l (.cell G)) (ho : env o = some (.ptr p))
    (hp : h[p]? = some (r, g)) : ExecSeq h env [invRead Tg x o] h (env.set x g) := by
  rcases hs with rfl | rfl
  · exact exec_read ho hp
  · exact exec_cellGet ho hp

end invSteps

/-! ## The two attacks -/

/-- The context after `prelude`. -/
def preludeCtx : Ctx :=
  ((((((Ctx.empty.set 0 .nat).set 1 (.refMut .static .nat)).set 2 rs).set 3 .nat).set 4
    (.refMut sh .nat)).set 5 rsh)

/-- The heap after `prelude`. -/
def preludeHeap : List (Lft × Val) := [] ++ [(.static, .nat 5)] ++ [(sh, .nat 7)]

/-- The environment after `prelude`. -/
def preludeEnv : Env :=
  ((((((Env.empty.set 0 (.nat 5)).set 1 (.ptr 0)).set 2 (.ptr 0)).set 3 (.nat 7)).set 4
    (.ptr 1)).set 5 (.ptr 1))

theorem prelude_chk (sub : Ty → Ty → Bool) : ChkSeq sub Ctx.empty prelude preludeCtx :=
  (chk_nat 0 5).cons ((chk_alloc rfl).cons ((chk_share rfl).cons ((chk_nat 3 7).cons
    ((chk_alloc rfl).cons ((chk_share rfl).cons (ChkSeq.nil _ _))))))

theorem prelude_exec : ExecSeq [] Env.empty prelude preludeHeap preludeEnv :=
  (exec_nat 0 5).cons ((exec_alloc rfl).cons ((exec_share rfl).cons ((exec_nat 3 7).cons
    ((exec_alloc rfl).cons ((exec_share rfl).cons (ExecSeq.nil _ _))))))

theorem chk_final {sub : Ty → Ty → Bool} {Γ : Ctx} {o : Nat} (ho : Γ o = some rs) :
    (chk 3 sub m₀ Γ [.endRegion 0, .read 0 o]).isSome = true := by
  simp [chk, m₀, Mode.get, ho, Ty.liveIn, Mode.lv, Lft.live]

theorem exec_final {H : List (Lft × Val)} {env : Env} {o : Nat} {w : Val}
    (ho : env o = some (.ptr 1)) (h1 : H[1]? = some (sh, w)) :
    exec 2 ⟨0, H⟩ env [.endRegion 0, .read 0 o] = .dangling := by
  simp [exec, ho, h1, Lft.live]

/-- Acceptance with the `subAlg` oracle extended by one derivable pair. -/
theorem typed_of_checks_one {tbl : Table} {ax : Ty → Ty → Prop} {P : List Stmt} {S₀ T₀ : Ty}
    (hax : SubGen tbl ax S₀ T₀) (fuel : Nat)
    (h : Checks (fun X Y => subAlg tbl true X Y || (X == S₀ && Y == T₀)) fuel P = true) :
    Typed (SubGen tbl ax) P := by
  refine ⟨_, ?_, fuel, h⟩
  intro X Y hxy
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hxy
  rcases hxy with h₁ | ⟨rfl, rfl⟩
  · exact SubGen.lift (Table.le_refl tbl) (fun _ _ h => h.elim) (subGen_of_subAlg tbl X Y true h₁)
  · exact hax

/-- A prefix that checks to a context in which `o : &'static nat`, followed by
`endRegion 0; read o`, is accepted. -/
theorem checks_of_chkSeq {sub : Ty → Ty → Bool} {Q : List Stmt} {Γ : Ctx} {o : Nat}
    (hq : ChkSeq sub Ctx.empty Q Γ) (ho : Γ o = some rs) :
    Checks sub (3 + Q.length) (Q ++ [.endRegion 0, .read 0 o]) = true := by
  show (chk (3 + Q.length) sub m₀ Ctx.empty (Q ++ [.endRegion 0, .read 0 o])).isSome = true
  rw [hq]; exact chk_final ho

/-- A prefix that runs to a state in which `o` holds the short reference (location `1`, region
`till 0`), followed by `endRegion 0; read o`, reaches the dangling-access state. -/
theorem dangling_of_execSeq {Q : List Stmt} {H : List (Lft × Val)} {env : Env} {o : Nat}
    {w : Val} (hq : ExecSeq [] Env.empty Q H env) (ho : env o = some (.ptr 1))
    (h1 : H[1]? = some (sh, w)) :
    (exec (2 + Q.length) St.init Env.empty (Q ++ [.endRegion 0, .read 0 o])).isDangling = true := by
  show (exec (2 + Q.length) ⟨0, []⟩ Env.empty (Q ++ [.endRegion 0, .read 0 o])).isDangling = true
  rw [hq, exec_final ho h1]; rfl

/-- The attack for a declared variance that does not require the forward direction: the
generator `F[&'sh nat] ≤ F[&'static nat]` admits a dangling access for every first-order `F`
with a parameter occurrence. -/
theorem admitsDanglingAccess_of_shrinkAx (F : Ty) (hf : F.fo = true) (hc : F.closed = false)
    {ax : Ty → Ty → Prop} (hax : SubGen rustTable ax (F.subst rsh) (F.subst rs)) :
    AdmitsDanglingAccess (SubGen rustTable ax) := by
  obtain ⟨N, hN⟩ : ∃ N, N = 10 + F.sz := ⟨_, rfl⟩
  let sub : Ty → Ty → Bool := fun X Y =>
    subAlg rustTable true X Y || (X == F.subst rsh && Y == F.subst rs)
  have hsub : sub rsh rsh = true := by simp [sub, subAlg_refl]
  have hsubF : sub (F.subst rsh) (F.subst rs) = true := by simp [sub]
  -- typing
  have c₀ := prelude_chk sub
  obtain ⟨Γ₁, c₁, e₁, _⟩ := bld_chk (sub := sub) (A := rsh) rfl hsub (a := 5) F hf 10 (by omega) preludeCtx rfl
  have c₂ := chk_copy (sub := sub) (x := N) e₁ (Ty.subst_closed rfl F) hsubF
  obtain ⟨Γ₃, c₃, e₃⟩ := nav_chk (sub := sub) rs F hf hc N _ (Ctx.set_same _ _ _)
  have hchk := checks_of_chkSeq (c₀.append (c₁.append (c₂.append c₃))) e₃
  -- execution
  have s₀ := prelude_exec
  obtain ⟨x₁, env₁, v, s₁, g₁, _, r₁⟩ :=
    bld_exec (A := rsh) (a := 5) (va := .ptr 1) F hf 10 (by omega) preludeHeap preludeEnv rfl
  have s₂ := exec_copy (h := preludeHeap ++ x₁) (x := N) (T := F.subst rs) g₁
  obtain ⟨x₃, env₃, s₃, e₃'⟩ := nav_exec F hf hc N _ _ _ v (Env.set_same _ _ _) r₁
  have hd := dangling_of_execSeq (s₀.append (s₁.append (s₂.append s₃))) e₃'
    (w := .nat 7) (get_append_left _ _ 1 (get_append_left _ _ 1 rfl))
  exact ⟨_, typed_of_checks_one hax _ hchk, _, hd⟩

/-- The attack for a declared variance that requires the forward direction where the inferred
variance also requires the backward one: the generator `F[&'static nat] ≤ F[&'sh nat]` admits a
dangling access for every data body `F` with a parameter occurrence under `&mut` or `Cell`. -/
theorem admitsDanglingAccess_of_growAx (F : Ty) (hF : F.dataBodyAt false = true)
    (hi : F.invOcc = true) {ax : Ty → Ty → Prop}
    (hax : SubGen rustTable ax (F.subst rs) (F.subst rsh)) :
    AdmitsDanglingAccess (SubGen rustTable ax) := by
  have hf := Ty.fo_of_dataBodyAt F false hF
  obtain ⟨l, G, hGc, hGf, hs⟩ := invTarget_shape F hF hi
  obtain ⟨N, hN⟩ : ∃ N, N = 10 + F.sz := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = N + F.sz := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = M + G.sz := ⟨_, rfl⟩
  have b₁ := invO_bounds F N
  have b₂ := invO_bounds F 10
  have hF1 := F.one_le_sz
  let sub : Ty → Ty → Bool := fun X Y =>
    subAlg rustTable true X Y || (X == F.subst rs && Y == F.subst rsh)
  have hsub₁ : sub rs rs = true := by simp [sub, subAlg_refl]
  have hsub₂ : sub rsh rsh = true := by simp [sub, subAlg_refl]
  have hsubF : sub (F.subst rs) (F.subst rsh) = true := by simp [sub]
  -- typing
  have c₀ := prelude_chk sub
  obtain ⟨Γ₁, c₁, e₁, p₁⟩ := bld_chk (sub := sub) (A := rs) rfl hsub₁ (a := 2) F hf 10 (by omega) preludeCtx rfl
  have c₂ := chk_copy (sub := sub) (x := N) e₁ (Ty.subst_closed rfl F) hsubF
  obtain ⟨Γ₃, c₃, e₃, p₃⟩ := invS_chk (sub := sub) rsh F N _ (Ctx.set_same _ _ _)
  have h₃ : Γ₃ 10 = some (F.subst rs) := by
    rw [p₃ 10 (Or.inl (by omega)), Ctx.set_ne (by omega)]; exact e₁
  obtain ⟨Γ₄, c₄, e₄, p₄⟩ := invS_chk (sub := sub) rs F 10 _ h₃
  have h₄N : Γ₄ (invO F N) = some ((invTarget F).subst rsh) := by
    rw [p₄ _ (Or.inr (by omega))]; exact e₃
  have h₄5 : Γ₄ 5 = some rsh := by
    rw [p₄ 5 (Or.inl (by omega)), p₃ 5 (Or.inl (by omega)), Ctx.set_ne (by omega),
      p₁ 5 (Or.inl (by omega))]; rfl
  obtain ⟨Γ₅, c₅, e₅, p₅⟩ := bld_chk (sub := sub) (A := rsh) rfl hsub₂ (a := 5) G hGf M (by omega) _ h₄5
  have h₅N : Γ₅ (invO F N) = some ((invTarget F).subst rsh) := by
    rw [p₅ _ (Or.inl (by omega))]; exact h₄N
  have h₅10 : Γ₅ (invO F 10) = some ((invTarget F).subst rs) := by
    rw [p₅ _ (Or.inl (by omega))]; exact e₄
  have c₆ := invWrite_chk (sub := sub) hs h₅N e₅
  have c₇ := invRead_chk (sub := sub) (x := K) hs h₅10
  obtain ⟨Γ₈, c₈, e₈⟩ := nav_chk (sub := sub) rs G hGf hGc K _ (Ctx.set_same _ _ _)
  have hchk := checks_of_chkSeq (c₀.append (c₁.append (c₂.append (c₃.append (c₄.append
    (c₅.append (c₆.append (c₇.append c₈)))))))) e₈
  -- execution
  have s₀ := prelude_exec
  obtain ⟨x₁, env₁, v, s₁, g₁, q₁, r₁⟩ :=
    bld_exec (A := rs) (a := 2) (va := .ptr 0) F hf 10 (by omega) preludeHeap preludeEnv rfl
  have s₂ := exec_copy (h := preludeHeap ++ x₁) (x := N) (T := F.subst rsh) g₁
  obtain ⟨env₃, s₃, g₃, q₃⟩ := invS_exec F N _ _ _ v (Env.set_same _ _ _) r₁
  have k₃ : env₃ 10 = some v := by
    rw [q₃ 10 (Or.inl (by omega)), Env.set_ne (by omega)]; exact g₁
  obtain ⟨env₄, s₄, g₄, q₄⟩ := invS_exec F 10 _ _ env₃ v k₃ r₁
  obtain ⟨p, r, w, hptr, hb, hp⟩ := invPtr_ptr F hF hi _ _ v r₁
  have k₄N : env₄ (invO F N) = some (.ptr p) := by
    rw [q₄ _ (Or.inr (by omega)), g₃, hptr]
  have k₄5 : env₄ 5 = some (.ptr 1) := by
    rw [q₄ 5 (Or.inl (by omega)), q₃ 5 (Or.inl (by omega)), Env.set_ne (by omega),
      q₁ 5 (Or.inl (by omega))]; rfl
  obtain ⟨x₅, env₅, g, s₅, g₅, q₅, r₅⟩ :=
    bld_exec (A := rsh) (a := 5) (va := .ptr 1) G hGf M (by omega) _ env₄ k₄5
  have k₅N : env₅ (invO F N) = some (.ptr p) := by rw [q₅ _ (Or.inl (by omega))]; exact k₄N
  have k₅10 : env₅ (invO F 10) = some (.ptr p) := by
    rw [q₅ _ (Or.inl (by omega)), g₄, hptr]
  have hp₅ := get_append_left _ x₅ p hp
  have s₆ := invWrite_exec hs k₅N g₅ hp₅
  have hlt := lt_len_of_get_some _ p hp₅
  have hp₆ := get_set_eq _ p (r, g) hlt
  have s₇ := invRead_exec (x := K) hs k₅10 hp₆
  have r₆ := Rep.set (r, g) (lt_len_of_get_some _ p hp) G g r₅
  obtain ⟨x₈, env₈, s₈, e₈'⟩ := nav_exec G hGf hGc K _ _ _ g (Env.set_same _ _ _) r₆
  have hb2 : 2 ≤ p := hb
  have h1 : (((preludeHeap ++ x₁ ++ x₅).set p (r, g)) ++ x₈)[1]? = some (sh, .nat 7) := by
    refine get_append_left _ _ 1 ?_
    rw [get_set_ne _ p 1 _ (by omega)]
    exact get_append_left _ _ 1 (get_append_left _ _ 1 rfl)
  have hd := dangling_of_execSeq (s₀.append (s₁.append (s₂.append (s₃.append (s₄.append
    (s₅.append (s₆.append (s₇.append s₈)))))))) e₈' h1
  exact ⟨_, typed_of_checks_one hax _ hchk, _, hd⟩

/-- Maximality of inferred variance for data bodies: the body rule at a variance not at most as
permissive as the inferred one admits a dangling access. -/
theorem admitsDanglingAccess_of_dataBody_not_le (F : Ty) (hF : F.dataBody = true)
    (v : Variance) (hv : v.le (inferVar rustTable F) = false) :
    AdmitsDanglingAccess (SubGen rustTable (BodyAx F v)) := by
  have hfo := Ty.fo_of_dataBodyAt F false hF
  cases hvf : v.fwd
  · have hc : F.closed = false := by
      cases hcl : F.closed
      · rfl
      · rw [inferVar_of_closed rustTable F hcl] at hv
        cases v <;> simp [Variance.le, Variance.fwd, Variance.bwd] at hv
    refine admitsDanglingAccess_of_shrinkAx F hfo hc (SubGen.base ⟨rsh, rs, rfl, rfl, rfl, rfl,
      fun h => absurd h (by simp [hvf]), fun _ => subGen_rust_rs_rsh⟩)
  · obtain ⟨hwb, hvb⟩ : (inferVar rustTable F).bwd = true ∧ v.bwd = false := by
      revert hv; generalize inferVar rustTable F = w
      cases w <;> cases v <;> simp_all [Variance.le, Variance.fwd, Variance.bwd]
    refine admitsDanglingAccess_of_growAx F hF (invOcc_of_inferVar_bwd F hfo hwb)
      (SubGen.base ⟨rs, rsh, rfl, rfl, rfl, rfl, fun _ => subGen_rust_rs_rsh,
        fun h => absurd h (by simp [hvb])⟩)

end Toy.Variance
