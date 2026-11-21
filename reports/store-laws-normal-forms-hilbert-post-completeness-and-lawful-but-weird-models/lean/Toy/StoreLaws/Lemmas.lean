import Toy.StoreLaws.Defs

/-!
# Store laws: basic lemmas

Monad laws for `Prog.bind`, how `run` and `Model.interp` compute, soundness of
`Derivable` and `ExtDerivable`, and derived laws.  These are supporting
lemmas used by the examples and witnesses; they are not the package's main
results.
-/

namespace Toy.StoreLaws

open Prog

namespace Prog

variable {S V W U : Type}

@[simp] theorem ret_bind (v : V) (f : V → Prog S W) : (ret v).bind f = f v := rfl

@[simp] theorem get_bind (k : S → Prog S V) (f : V → Prog S W) :
    (get k).bind f = get (fun s => (k s).bind f) := rfl

@[simp] theorem put_bind (s : S) (p : Prog S V) (f : V → Prog S W) :
    (put s p).bind f = put s (p.bind f) := rfl

/-- Right unit law of the free monad, as a literal equality of programs. -/
theorem bind_ret (p : Prog S V) : p.bind ret = p := by
  induction p with
  | ret v => rfl
  | get k ih => exact congrArg get (funext ih)
  | put s p ih => exact congrArg (put s) ih

/-- Associativity of bind, as a literal equality of programs. -/
theorem bind_assoc (p : Prog S V) (f : V → Prog S W) (g : W → Prog S U) :
    (p.bind f).bind g = p.bind (fun v => (f v).bind g) := by
  induction p with
  | ret v => rfl
  | get k ih => exact congrArg get (funext ih)
  | put s p ih => exact congrArg (put s) ih

end Prog

section RunInterp

variable {S V W X : Type}

@[simp] theorem run_ret (v : V) (s : S) : run (Prog.ret v) s = (v, s) := rfl
@[simp] theorem run_get (k : S → Prog S V) (s : S) : run (Prog.get k) s = run (k s) s := rfl
@[simp] theorem run_put (t : S) (p : Prog S V) (s : S) : run (Prog.put t p) s = run p t := rfl

/-- `run` of a substitution instance. -/
theorem run_bind (p : Prog S V) (f : V → Prog S W) (s : S) :
    run (p.bind f) s = run (f (run p s).1) (run p s).2 := by
  induction p generalizing s with
  | ret v => rfl
  | get k ih => exact ih s s
  | put t p ih => exact ih t

/-- The intended semantics of a canonical program. -/
@[simp] theorem run_canon (f : S → S) (g : S → V) (s : S) :
    run (canon f g) s = (g s, f s) := rfl

/-- The canonical program of `run p` has the same intended semantics as `p`. -/
theorem run_nf (o : S → V × S) : run (nf o) = o := by
  funext s; rfl

/-- `run` is the interpretation in the intended model. -/
theorem interp_intended (p : Prog S V) : (intended S V).interp intendedRet p = run p := by
  induction p with
  | ret v => rfl
  | get k ih => funext s; exact congrFun (ih s) s
  | put t p ih => funext s; exact congrFun ih t

end RunInterp

section Laws

variable {S X V : Type}

/-- The intended model satisfies all four laws strictly. -/
theorem intended_lawful : Lawful (intended S V) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem lawful_satisfiesAll {M : Model S X} (h : Lawful M) (L : LawSet) : SatisfiesAll L M := by
  intro l _
  cases l
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- Observational satisfaction through a constant observation holds for every
model: all four `...Via` laws hold for `obs := fun _ => ()`. -/
theorem laws_via_const_hold (M : Model S X) :
    GetGetVia (fun _ : X => ()) M ∧ GetPutVia (fun _ : X => ()) M ∧
    PutGetVia (fun _ : X => ()) M ∧ PutPutVia (fun _ : X => ()) M :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Get–put and put–get (strictly) imply that writing the same value twice is
writing it once. -/
theorem put_idem_of_getPut_putGet {M : Model S X} (hGP : GetPut M) (hPG : PutGet M)
    (s : S) (x : X) : M.put s (M.put s x) = M.put s x := by
  calc M.put s (M.put s x)
      = M.put s (M.get fun t => M.put t x) := (hPG s (fun t => M.put t x)).symm
    _ = M.put s x := by rw [hGP]

/-- The uniqueness half of freeness uses no law: every homomorphism from the
intended model to `M` extending `ρ` is `M.fromObs ρ`. -/
theorem isHom_eq_fromObs {V : Type} (M : Model S X) (ρ : V → X) (h : (S → V × S) → X)
    (hh : IsHom M ρ h) : h = M.fromObs ρ := by
  rcases hh with ⟨hret, hget, hput⟩
  funext o
  show h ((intended S V).get
      (fun s => (intended S V).put (o s).2 (intendedRet (o s).1))) = M.fromObs ρ o
  rw [hget]
  show M.get (fun s => h ((intended S V).put (o s).2 (intendedRet (o s).1))) =
    M.get (fun s => M.put (o s).2 (ρ (o s).1))
  simp only [hput, hret]

/-- Model-level derived law: a read whose continuation ignores the value and
immediately writes is that write (uses get–put and put–put). -/
theorem get_const_put_of {M : Model S X} (hGP : GetPut M) (hPP : PutPut M) (c : S) (y : X) :
    M.get (fun _ => M.put c y) = M.put c y := by
  have h1 : (fun _ : S => M.put c y) = (fun s => M.put s (M.put c y)) :=
    funext fun s => (hPP s c y).symm
  rw [h1, hGP]

end Laws

section Derivations

variable {S V : Type} {L : LawSet}

/-- `Derivable` is sound for every model of its law set, under every valuation. -/
theorem Derivable.sound {p q : Prog S V} (h : Derivable L p q) {X : Type} (M : Model S X)
    (hM : SatisfiesAll L M) (ρ : V → X) : M.interp ρ p = M.interp ρ q := by
  induction h with
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_congr _ ih =>
    show M.get _ = M.get _
    exact congrArg M.get (funext ih)
  | put_congr s _ ih =>
    show M.put s _ = M.put s _
    exact congrArg (M.put s) ih
  | getGet hl k => exact (hM .getGet hl) (fun s s' => M.interp ρ (k s s'))
  | getPut hl p => exact (hM .getPut hl) (M.interp ρ p)
  | putGet hl s k => exact (hM .putGet hl) s (fun s' => M.interp ρ (k s'))
  | putPut hl s s' p => exact (hM .putPut hl) s s' (M.interp ρ p)

/-- Derivable equations hold in the intended semantics. -/
theorem Derivable.run_eq {p q : Prog S V} (h : Derivable L p q) : run p = run q := by
  have := h.sound (intended S V) (lawful_satisfiesAll intended_lawful L) intendedRet
  rwa [interp_intended, interp_intended] at this

/-- Syntactic derived law: `get (fun _ => put c y)` is derivably `put c y`
from get–put and put–put. -/
theorem Derivable.get_const_put (hGP : L .getPut) (hPP : L .putPut) (c : S) (y : Prog S V) :
    Derivable L (.get fun _ => .put c y) (.put c y) :=
  (Derivable.get_congr fun s => (Derivable.putPut hPP s c y).symm).trans
    (Derivable.getPut hGP _)

/-- Syntactic derivation of get–get from get–put and put–get. -/
theorem Derivable.getGet_of (hGP : L .getPut) (hPG : L .putGet) (k : S → S → Prog S V) :
    Derivable L (.get fun s => .get fun s' => k s s') (.get fun s => k s s) := by
  have hl : Derivable L (.get fun s => .get fun s' => k s s')
      (.get fun t => .put t (k t t)) :=
    (Derivable.getPut hGP _).symm.trans
      (Derivable.get_congr fun t =>
        (Derivable.putGet hPG t _).trans (Derivable.putGet hPG t _))
  have hr : Derivable L (.get fun s => k s s) (.get fun t => .put t (k t t)) :=
    (Derivable.getPut hGP _).symm.trans
      (Derivable.get_congr fun t => Derivable.putGet hPG t _)
  exact hl.trans hr.symm

/-- `Derivable` is monotone in the law set. -/
theorem Derivable.mono {L L' : LawSet} (hLL : ∀ l, L l → L' l) {p q : Prog S V}
    (h : Derivable L p q) : Derivable L' p q := by
  induction h with
  | refl p => exact .refl p
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_congr _ ih => exact .get_congr ih
  | put_congr s _ ih => exact .put_congr s ih
  | getGet hl k => exact .getGet (hLL _ hl) k
  | getPut hl p => exact .getPut (hLL _ hl) p
  | putGet hl s k => exact .putGet (hLL _ hl) s k
  | putPut hl s s' p => exact .putPut (hLL _ hl) s s' p

/-- `Derivable` is closed under substitution (bind on the right of both sides). -/
theorem Derivable.bind_left {W : Type} {p q : Prog S V} (h : Derivable L p q)
    (σ : V → Prog S W) : Derivable L (p.bind σ) (q.bind σ) := by
  induction h with
  | refl p => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_congr _ ih => exact .get_congr ih
  | put_congr s _ ih => exact .put_congr s ih
  | getGet hl k => exact .getGet hl (fun s s' => (k s s').bind σ)
  | getPut hl p => exact .getPut hl (p.bind σ)
  | putGet hl s k => exact .putGet hl s (fun s' => (k s').bind σ)
  | putPut hl s s' p => exact .putPut hl s s' (p.bind σ)

/-- If every substitution instance of `p₀ = q₀` holds in the intended
semantics (e.g. when `run p₀ = run q₀`), the extended theory is sound for the
intended semantics. -/
theorem ExtDerivable.run_eq_of {p₀ q₀ : Prog S V}
    (h₀ : ∀ σ : V → Prog S V, run (p₀.bind σ) = run (q₀.bind σ))
    {p q : Prog S V} (h : ExtDerivable p₀ q₀ p q) : run p = run q := by
  induction h with
  | of_derivable hd => exact hd.run_eq
  | inst σ => exact h₀ σ
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_congr _ ih => funext s; exact congrFun (ih s) s
  | put_congr s _ ih => funext _; exact congrFun ih s

/-- The extended theory is closed under substitution. -/
theorem ExtDerivable.bind_left {p₀ q₀ p q : Prog S V} (h : ExtDerivable p₀ q₀ p q)
    (σ : V → Prog S V) : ExtDerivable p₀ q₀ (p.bind σ) (q.bind σ) := by
  induction h with
  | of_derivable hd => exact .of_derivable (hd.bind_left σ)
  | inst τ =>
    have := ExtDerivable.inst (p₀ := p₀) (q₀ := q₀) (fun v => (τ v).bind σ)
    rwa [← Prog.bind_assoc, ← Prog.bind_assoc] at this
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_congr _ ih => exact .get_congr ih
  | put_congr s _ ih => exact .put_congr s ih

/-- If every `put a z` is identified with every `put a z'` (same `a`), the
extended theory identifies all programs (via get–put). -/
theorem ExtDerivable.total_of_put {p₀ q₀ : Prog S V}
    (hput : ∀ (a : S) (z z' : Prog S V), ExtDerivable p₀ q₀ (.put a z) (.put a z'))
    (p q : Prog S V) : ExtDerivable p₀ q₀ p q :=
  (ExtDerivable.of_derivable (Derivable.getPut trivial p).symm).trans <|
    (ExtDerivable.get_congr fun s => hput s p q).trans
      (.of_derivable (Derivable.getPut trivial q))

/-- The extra equation itself is in the extended theory. -/
theorem ExtDerivable.base (p₀ q₀ : Prog S V) : ExtDerivable p₀ q₀ p₀ q₀ := by
  have h := ExtDerivable.inst (p₀ := p₀) (q₀ := q₀) Prog.ret
  rwa [Prog.bind_ret, Prog.bind_ret] at h

/-- `ExtDerivableNoSubst` is sound for every model satisfying all four laws and
every valuation under which `p₀` and `q₀` are interpreted equally. -/
theorem ExtDerivableNoSubst.sound {p₀ q₀ p q : Prog S V} (h : ExtDerivableNoSubst p₀ q₀ p q)
    {X : Type} (M : Model S X) (hM : Lawful M) (ρ : V → X)
    (h₀ : M.interp ρ p₀ = M.interp ρ q₀) : M.interp ρ p = M.interp ρ q := by
  induction h with
  | of_derivable hd => exact hd.sound M (lawful_satisfiesAll hM allLaws) ρ
  | base => exact h₀
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | get_congr _ ih =>
    show M.get _ = M.get _
    exact congrArg M.get (funext ih)
  | put_congr s _ ih =>
    show M.put s _ = M.put s _
    exact congrArg (M.put s) ih

end Derivations

/-! ## Degenerate cell types

On cells with at most one value the four laws are not independent. -/

section Degenerate

/-- On a one-element cell, get–put and put–get imply put–put. -/
theorem unit_cell_putPut_of_getPut_putGet {X : Type} (M : Model Unit X)
    (hGP : GetPut M) (hPG : PutGet M) : PutPut M := by
  intro s s' x
  cases s; cases s'
  exact put_idem_of_getPut_putGet hGP hPG () x

/-- On a one-element cell, get–put and put–put imply all four laws. -/
theorem unit_cell_lawful_of_getPut_putPut {X : Type} (M : Model Unit X)
    (hGP : GetPut M) (hPP : PutPut M) : Lawful M := by
  have hput_id : ∀ x : X, M.put () x = x := fun x => by
    have h1 := hGP (M.put () x)
    have h2 : (fun s : Unit => M.put s (M.put () x)) = (fun s : Unit => M.put s x) :=
      funext fun s => by cases s; exact hPP () () x
    rw [h2, hGP] at h1
    exact h1.symm
  have hget_id : ∀ k : Unit → X, M.get k = k () := fun k => by
    have h1 := hGP (k ())
    have h2 : (fun s : Unit => M.put s (k ())) = k :=
      funext fun s => by cases s; exact hput_id (k ())
    rw [h2] at h1
    exact h1
  refine ⟨?_, hGP, ?_, hPP⟩
  · intro k; simp only [hget_id]
  · intro s k; cases s; simp only [hput_id, hget_id]

/-- On an empty cell, get–put forces the carrier to have at most one element. -/
theorem empty_cell_subsingleton_of_getPut {X : Type} (M : Model Empty X) (hGP : GetPut M)
    (x y : X) : x = y := by
  have h1 : (fun s : Empty => M.put s x) = (fun s : Empty => M.put s y) :=
    funext fun s => Empty.elim s
  rw [← hGP x, ← hGP y, h1]

/-- On an empty cell, get–put alone implies all four laws. -/
theorem empty_cell_lawful_of_getPut {X : Type} (M : Model Empty X) (hGP : GetPut M) :
    Lawful M :=
  ⟨fun _ => empty_cell_subsingleton_of_getPut M hGP _ _, hGP,
   fun s => Empty.elim s, fun s => Empty.elim s⟩

end Degenerate

end Toy.StoreLaws
