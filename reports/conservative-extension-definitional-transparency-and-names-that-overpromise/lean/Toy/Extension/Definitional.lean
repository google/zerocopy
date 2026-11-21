/-
Signature extensions by one new symbol, structure expansions, explicit
definitions (definitional extensions), their unfolding, and delta-conversion
for a defined symbol. Main results: a definitional extension has exactly one
expansion of each model, is conservative, and unfolding the defined symbol
preserves truth exactly in the structures that satisfy the defining axiom.
-/
import Toy.Extension.Semantics

namespace Toy.Extension

variable {L : Sig} {α : Type}

/-! ### Adding one symbol -/

/-- `L` plus one fresh function symbol of arity `k`; the new symbol is `none`. -/
def Sig.addFn (L : Sig) (k : Nat) : Sig where
  Fn := Option L.Fn
  Rel := L.Rel
  fnArity := fun f => match f with
    | none => k
    | some f => L.fnArity f
  relArity := L.relArity

/-- `L` plus one fresh relation symbol of arity `k`; the new symbol is `none`. -/
def Sig.addRel (L : Sig) (k : Nat) : Sig where
  Fn := L.Fn
  Rel := Option L.Rel
  fnArity := L.fnArity
  relArity := fun r => match r with
    | none => k
    | some r => L.relArity r

/-- Inclusion of `L` into `L.addFn k`. -/
def SigHom.inclFn (L : Sig) (k : Nat) : SigHom L (L.addFn k) where
  fn := some
  rel := id
  fnArity := fun _ => rfl
  relArity := fun _ => rfl

/-- Inclusion of `L` into `L.addRel k`. -/
def SigHom.inclRel (L : Sig) (k : Nat) : SigHom L (L.addRel k) where
  fn := id
  rel := some
  fnArity := fun _ => rfl
  relArity := fun _ => rfl

/-- Expand an `L`-structure by an interpretation `g` of the new function symbol. -/
def Str.withFn {k : Nat} (S : Str L α) (g : (Fin k → α) → α) : Str (L.addFn k) α where
  fn := fun f => match f with
    | none => g
    | some f => S.fn f
  rel := S.rel

/-- Expand an `L`-structure by an interpretation `p` of the new relation symbol. -/
def Str.withRel {k : Nat} (S : Str L α) (p : (Fin k → α) → Prop) : Str (L.addRel k) α where
  fn := S.fn
  rel := fun r => match r with
    | none => p
    | some r => S.rel r

theorem reduct_withFn {k : Nat} (S : Str L α) (g : (Fin k → α) → α) :
    (S.withFn g).reduct (SigHom.inclFn L k) = S := rfl

theorem reduct_withRel {k : Nat} (S : Str L α) (p : (Fin k → α) → Prop) :
    (S.withRel p).reduct (SigHom.inclRel L k) = S := rfl

/-- Every `L.addFn k`-structure is the expansion of its reduct by its own
interpretation of the new symbol. -/
theorem withFn_reduct {k : Nat} (S' : Str (L.addFn k) α) :
    (S'.reduct (SigHom.inclFn L k)).withFn (S'.fn none) = S' := by
  cases S' with
  | mk fn rel =>
    unfold Str.withFn Str.reduct
    congr 1
    all_goals first | rfl | (funext f; cases f <;> rfl)

/-! ### Explicit definitions -/

/-- An explicit definition of one new symbol in terms of the old language:
either a function symbol `c(x₀,…,x_{k-1}) := e` for a term `e`, or a relation
symbol `c(x₀,…,x_{k-1}) :↔ e` for a formula `e`. Constants are the case `k = 0`. -/
inductive Defn (L : Sig) : Type where
  | fn (k : Nat) (e : Term L k)
  | rel (k : Nat) (e : Formula L k)

namespace Defn

/-- The extended signature. -/
def sig : Defn L → Sig
  | fn k _ => L.addFn k
  | rel k _ => L.addRel k

/-- The inclusion of the old signature. -/
def incl : (d : Defn L) → SigHom L d.sig
  | fn k _ => SigHom.inclFn L k
  | rel k _ => SigHom.inclRel L k

/-- The defining axiom `∀ x̄, c(x̄) = e(x̄)` or `∀ x̄, c(x̄) ↔ e(x̄)`. -/
def defAxiom : (d : Defn L) → Sentence d.sig
  | fn k e => Formula.closeAll k
      (.eq (.app (none : (L.addFn k).Fn) (fun i => .var i)) (e.map (SigHom.inclFn L k)))
  | rel k e => Formula.closeAll k
      (.iff (.rel (none : (L.addRel k).Rel) (fun i => .var i)) (e.map (SigHom.inclRel L k)))

/-- The definitional extension `T' = T + (c := e)`: the old axioms read in the
new vocabulary, plus the defining axiom. -/
def theory (T : Theory L) (d : Defn L) : Theory d.sig :=
  (T.map d.incl).union (Theory.ofList [d.defAxiom])

/-- The canonical expansion: interpret the new symbol by its definiens. -/
def expand : (d : Defn L) → Str L α → Str d.sig α
  | fn _ e, S => S.withFn (fun args => e.eval S args)
  | rel _ e, S => S.withRel (fun args => Sat S args e)

end Defn

/-- Replace every occurrence of the new function symbol by its definiens. -/
def unfoldFnTerm {k : Nat} (e : Term L k) {n : Nat} : Term (L.addFn k) n → Term L n
  | .var i => .var i
  | .app none ts => e.subst (fun j => unfoldFnTerm e (ts j))
  | .app (some f) ts => .app f (fun j => unfoldFnTerm e (ts j))

/-- Unfold a defined function symbol throughout a formula. -/
def unfoldFnFormula {k : Nat} (e : Term L k) : {n : Nat} → Formula (L.addFn k) n → Formula L n
  | _, .eq s t => .eq (unfoldFnTerm e s) (unfoldFnTerm e t)
  | _, .rel r ts => .rel r (fun j => unfoldFnTerm e (ts j))
  | _, .falsum => .falsum
  | _, .imp φ ψ => .imp (unfoldFnFormula e φ) (unfoldFnFormula e ψ)
  | _, .and φ ψ => .and (unfoldFnFormula e φ) (unfoldFnFormula e ψ)
  | _, .or φ ψ => .or (unfoldFnFormula e φ) (unfoldFnFormula e ψ)
  | _, .all φ => .all (unfoldFnFormula e φ)
  | _, .ex φ => .ex (unfoldFnFormula e φ)

/-- Terms over `L.addRel k` are terms over `L` (no new function symbol). -/
def relTermDown {k n : Nat} : Term (L.addRel k) n → Term L n
  | .var i => .var i
  | .app f ts => .app f (fun j => relTermDown (ts j))

/-- Unfold a defined relation symbol throughout a formula, substituting the
actual arguments into the definiens (capture-avoiding). -/
def unfoldRelFormula {k : Nat} (e : Formula L k) : {n : Nat} → Formula (L.addRel k) n → Formula L n
  | _, .eq s t => .eq (relTermDown s) (relTermDown t)
  | _, .rel none ts => e.subst (fun j => relTermDown (ts j))
  | _, .rel (some r) ts => .rel r (fun j => relTermDown (ts j))
  | _, .falsum => .falsum
  | _, .imp φ ψ => .imp (unfoldRelFormula e φ) (unfoldRelFormula e ψ)
  | _, .and φ ψ => .and (unfoldRelFormula e φ) (unfoldRelFormula e ψ)
  | _, .or φ ψ => .or (unfoldRelFormula e φ) (unfoldRelFormula e ψ)
  | _, .all φ => .all (unfoldRelFormula e φ)
  | _, .ex φ => .ex (unfoldRelFormula e φ)

/-- The unfolding `ψ[c := e]`, a formula of the old language. -/
def Defn.unfold : (d : Defn L) → {n : Nat} → Formula d.sig n → Formula L n
  | .fn _ e, _, ψ => unfoldFnFormula e ψ
  | .rel _ e, _, ψ => unfoldRelFormula e ψ

theorem withRel_reduct {k : Nat} (S' : Str (L.addRel k) α) :
    (S'.reduct (SigHom.inclRel L k)).withRel (S'.rel none) = S' := by
  cases S' with
  | mk fn rel =>
    unfold Str.withRel Str.reduct
    congr 1
    all_goals first | rfl | (funext r; cases r <;> rfl)

/-! ### Substitution lemmas (infrastructure) -/

theorem eval_rename (S : Str L α) {n m : Nat} (ρ : Fin n → Fin m) (v : Fin m → α) :
    ∀ t : Term L n, (t.rename ρ).eval S v = t.eval S (fun i => v (ρ i))
  | .var _ => rfl
  | .app f ts => congrArg (S.fn f) (funext fun j => eval_rename S ρ v (ts j))

theorem eval_subst (S : Str L α) {k n : Nat} (σ : Fin k → Term L n) (v : Fin n → α) :
    ∀ t : Term L k, (t.subst σ).eval S v = t.eval S (fun i => (σ i).eval S v)
  | .var _ => rfl
  | .app f ts => congrArg (S.fn f) (funext fun j => eval_subst S σ v (ts j))

theorem eval_liftSubst (S : Str L α) {k n : Nat} (σ : Fin k → Term L n) (a : α) (v : Fin n → α) :
    (fun i => (liftSubst σ i).eval S (scons a v)) = scons a (fun i => (σ i).eval S v) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact eval_rename S Fin.succ (scons a v) (σ j)

theorem sat_subst (S : Str L α) :
    ∀ {k : Nat} (φ : Formula L k) {n : Nat} (σ : Fin k → Term L n) (v : Fin n → α),
      Sat S v (φ.subst σ) ↔ Sat S (fun i => (σ i).eval S v) φ
  | _, .eq s t, _, σ, v => by simp only [Formula.subst, Sat, eval_subst]
  | _, .rel r ts, _, σ, v => by simp only [Formula.subst, Sat, eval_subst]
  | _, .falsum, _, _, _ => Iff.rfl
  | _, .imp φ ψ, _, σ, v => imp_congr (sat_subst S φ σ v) (sat_subst S ψ σ v)
  | _, .and φ ψ, _, σ, v => and_congr (sat_subst S φ σ v) (sat_subst S ψ σ v)
  | _, .or φ ψ, _, σ, v => or_congr (sat_subst S φ σ v) (sat_subst S ψ σ v)
  | _, .all φ, _, σ, v => by
    simp only [Formula.subst, Sat]
    exact forall_congr' fun a => (sat_subst S φ (liftSubst σ) (scons a v)).trans (by rw [eval_liftSubst])
  | _, .ex φ, _, σ, v => by
    simp only [Formula.subst, Sat]
    exact exists_congr fun a => (sat_subst S φ (liftSubst σ) (scons a v)).trans (by rw [eval_liftSubst])

/-! ### Expansions of a model by an explicit definition -/

/-- The canonical expansion satisfies the defining axiom (proved helper). -/
theorem expand_models_defAxiom (d : Defn L) (S : Str L α) :
    (d.expand S).Models d.defAxiom := by
  cases d with
  | fn k e =>
    refine (sat_closeAll (Defn.expand (.fn k e) S) k _).2 (fun v => ?_)
    show Term.eval S v e = (e.map (SigHom.inclFn L k)).eval (S.withFn _) v
    rw [eval_map, reduct_withFn]
  | rel k e =>
    refine (sat_closeAll (Defn.expand (.rel k e) S) k _).2 (fun v => ?_)
    refine (sat_iff _ v _ _).2 ?_
    show Sat S v e ↔ Sat (S.withRel _) v (e.map (SigHom.inclRel L k))
    rw [sat_map, reduct_withRel]

/-- The canonical expansion keeps the old symbols (proved helper). -/
theorem expand_reduct (d : Defn L) (S : Str L α) : (d.expand S).reduct d.incl = S := by
  cases d <;> rfl

/-- **Main result.** Uniqueness from the defining axiom alone, without a theory `T`: any
expansion of `S` (same carrier, old symbols unchanged) that satisfies the
defining axiom is the canonical expansion. -/
theorem defExt_expansion_unique_of_axiom (d : Defn L) (S : Str L α) (S' : Str d.sig α)
    (hred : S'.reduct d.incl = S) (hax : S'.Models d.defAxiom) :
    S' = d.expand S := by
  cases d with
  | fn k e =>
    change Str (L.addFn k) α at S'
    change S'.reduct (SigHom.inclFn L k) = S at hred
    have hax' := (sat_closeAll S' k _).1 hax
    have hg : S'.fn (none : Option L.Fn) = fun args : Fin k → α => e.eval S args := by
      funext args
      have h : S'.fn (none : Option L.Fn) args = (e.map (SigHom.inclFn L k)).eval S' args := hax' args
      exact h.trans ((eval_map (SigHom.inclFn L k) S' args e).trans (hred ▸ rfl))
    have h1 : (S'.reduct (SigHom.inclFn L k)).withFn (S'.fn (none : Option L.Fn)) = S' := withFn_reduct S'
    show S' = S.withFn (fun args => e.eval S args)
    rw [← h1, hg, hred]; rfl
  | rel k e =>
    change Str (L.addRel k) α at S'
    change S'.reduct (SigHom.inclRel L k) = S at hred
    have hax' := (sat_closeAll S' k _).1 hax
    have hp : S'.rel (none : Option L.Rel) = fun args : Fin k → α => Sat S args e := by
      funext args
      have h : S'.rel (none : Option L.Rel) args ↔ Sat S' args (e.map (SigHom.inclRel L k)) :=
        (sat_iff S' args _ _).1 (hax' args)
      exact propext (h.trans ((sat_map (SigHom.inclRel L k) S' args e).trans (hred ▸ Iff.rfl)))
    have h1 : (S'.reduct (SigHom.inclRel L k)).withRel (S'.rel (none : Option L.Rel)) = S' :=
      withRel_reduct S'
    show S' = S.withRel (fun args => Sat S args e)
    rw [← h1, hp, hred]; rfl

/-- Proved helper: the expansions of `S` satisfying the defining axiom are
exactly the canonical expansion (no theory `T` involved). -/
theorem defExt_expansion_iff_of_axiom (d : Defn L) (S : Str L α) (S' : Str d.sig α) :
    (S'.reduct d.incl = S ∧ S'.Models d.defAxiom) ↔ S' = d.expand S := by
  constructor
  · rintro ⟨hred, hax⟩; exact defExt_expansion_unique_of_axiom d S S' hred hax
  · rintro rfl; exact ⟨expand_reduct d S, expand_models_defAxiom d S⟩

/-- **Main result.** For a model `S` of `T`, the expansions of `S` (same carrier,
old symbols unchanged) that are models of the definitional extension
`T + (c := e)` are exactly one structure, the canonical expansion
`d.expand S`. -/
theorem defExt_expansions_eq_expand (T : Theory L) (d : Defn L) (S : Str L α)
    (hS : S.ModelsTh T) :
    ∀ S' : Str d.sig α, (S'.reduct d.incl = S ∧ S'.ModelsTh (d.theory T)) ↔ S' = d.expand S := by
  intro S'
  rw [← defExt_expansion_iff_of_axiom d S S']
  simp only [Defn.theory, modelsTh_union, modelsTh_map, modelsTh_ofList]
  constructor
  · rintro ⟨hred, ⟨_, hax⟩⟩; exact ⟨hred, hax _ (List.Mem.head _)⟩
  · rintro ⟨hred, hax⟩
    refine ⟨hred, hred.symm ▸ hS, fun φ hφ => ?_⟩
    cases hφ with
    | head => exact hax
    | tail _ h => cases h

/-- **Main result.** A definitional extension is conservative. -/
theorem defExt_conservative (T : Theory L) (d : Defn L) :
    Conservative d.incl T (d.theory T) := by
  intro φ h β S hS
  have hS' : (d.expand S).ModelsTh (d.theory T) :=
    ((defExt_expansions_eq_expand T d S hS) (d.expand S)).2 rfl |>.2
  have := (models_map d.incl (d.expand S) φ).1 (h β _ hS')
  rwa [expand_reduct] at this

/-! ### Unfolding a defined symbol -/

theorem eval_unfoldFnTerm {k : Nat} (e : Term L k)
    (S' : Str (L.addFn k) α) (hax : S'.Models (Defn.fn k e).defAxiom) {n : Nat} (v : Fin n → α) :
    ∀ t : Term (L.addFn k) n,
      ((unfoldFnTerm e t).map (SigHom.inclFn L k)).eval S' v = t.eval S' v
  | .var _ => rfl
  | .app none ts => by
    have hax' := (sat_closeAll S' k _).1 hax
    have ih : ∀ j : Fin k, (unfoldFnTerm e (ts j)).eval (S'.reduct (SigHom.inclFn L k)) v =
        (ts j).eval S' v :=
      fun j => (eval_map (SigHom.inclFn L k) S' v _).symm.trans (eval_unfoldFnTerm e S' hax v (ts j))
    have h1 := eval_map (SigHom.inclFn L k) S' v (e.subst (fun j => unfoldFnTerm e (ts j)))
    have h2 := eval_subst (S'.reduct (SigHom.inclFn L k)) (fun j => unfoldFnTerm e (ts j)) v e
    have h3 : (fun i => (unfoldFnTerm e (ts i)).eval (S'.reduct (SigHom.inclFn L k)) v) =
        (fun i => (ts i).eval S' v) := funext ih
    have hfn : S'.fn (none : Option L.Fn) (fun j => (ts j).eval S' v) =
        (e.map (SigHom.inclFn L k)).eval S' (fun j => (ts j).eval S' v) := hax' _
    have h4 := eval_map (SigHom.inclFn L k) S' (fun j => (ts j).eval S' v) e
    exact h1.trans (h2.trans ((congrArg (fun w => e.eval _ w) h3).trans (h4.symm.trans hfn.symm)))
  | .app (some f) ts => by
    have ih : ∀ j, ((unfoldFnTerm e (ts j)).map (SigHom.inclFn L k)).eval S' v = (ts j).eval S' v :=
      fun j => eval_unfoldFnTerm e S' hax v (ts j)
    exact congrArg (S'.fn (some f)) (funext ih)

theorem eval_relTermDown {k n : Nat} (S' : Str (L.addRel k) α) (v : Fin n → α) :
    ∀ t : Term (L.addRel k) n,
      ((relTermDown t).map (SigHom.inclRel L k)).eval S' v = t.eval S' v
  | .var _ => rfl
  | .app f ts => congrArg (S'.fn f) (funext fun j => eval_relTermDown S' v (ts j))

theorem sat_unfoldFnFormula {k : Nat} (e : Term L k)
    (S' : Str (L.addFn k) α) (hax : S'.Models (Defn.fn k e).defAxiom) :
    ∀ {n : Nat} (ψ : Formula (L.addFn k) n) (v : Fin n → α),
      Sat S' v ψ ↔ Sat S' v ((unfoldFnFormula e ψ).map (SigHom.inclFn L k))
  | _, .eq s t, v => by
    show s.eval S' v = t.eval S' v ↔
      ((unfoldFnTerm e s).map (SigHom.inclFn L k)).eval S' v =
      ((unfoldFnTerm e t).map (SigHom.inclFn L k)).eval S' v
    rw [eval_unfoldFnTerm e S' hax v s, eval_unfoldFnTerm e S' hax v t]
  | _, .rel r ts, v => by
    show S'.rel r (fun j => (ts j).eval S' v) ↔
      S'.rel r (fun j => ((unfoldFnTerm e (ts j)).map (SigHom.inclFn L k)).eval S' v)
    have heq : (fun j => ((unfoldFnTerm e (ts j)).map (SigHom.inclFn L k)).eval S' v) =
        (fun j => (ts j).eval S' v) := funext fun j => eval_unfoldFnTerm e S' hax v (ts j)
    rw [heq]
  | _, .falsum, _ => Iff.rfl
  | _, .imp φ χ, v => imp_congr (sat_unfoldFnFormula e S' hax φ v) (sat_unfoldFnFormula e S' hax χ v)
  | _, .and φ χ, v => and_congr (sat_unfoldFnFormula e S' hax φ v) (sat_unfoldFnFormula e S' hax χ v)
  | _, .or φ χ, v => or_congr (sat_unfoldFnFormula e S' hax φ v) (sat_unfoldFnFormula e S' hax χ v)
  | _, .all φ, v => forall_congr' fun a => sat_unfoldFnFormula e S' hax φ (scons a v)
  | _, .ex φ, v => exists_congr fun a => sat_unfoldFnFormula e S' hax φ (scons a v)

theorem sat_unfoldRelFormula {k : Nat} (e : Formula L k)
    (S' : Str (L.addRel k) α) (hax : S'.Models (Defn.rel k e).defAxiom) :
    ∀ {n : Nat} (ψ : Formula (L.addRel k) n) (v : Fin n → α),
      Sat S' v ψ ↔ Sat S' v ((unfoldRelFormula e ψ).map (SigHom.inclRel L k))
  | _, .eq s t, v => by
    show s.eval S' v = t.eval S' v ↔
      ((relTermDown s).map (SigHom.inclRel L k)).eval S' v =
      ((relTermDown t).map (SigHom.inclRel L k)).eval S' v
    rw [eval_relTermDown S' v s, eval_relTermDown S' v t]
  | _, .rel none ts, v => by
    have hax' := (sat_closeAll S' k _).1 hax (fun j => (ts j).eval S' v)
    have hiff : S'.rel (none : Option L.Rel) (fun j => (ts j).eval S' v) ↔
        Sat S' (fun j => (ts j).eval S' v) (e.map (SigHom.inclRel L k)) :=
      (sat_iff S' _ _ _).1 hax'
    show S'.rel (none : Option L.Rel) (fun j => (ts j).eval S' v) ↔
      Sat S' v ((e.subst (fun j => relTermDown (ts j))).map (SigHom.inclRel L k))
    have hsub := (sat_map (SigHom.inclRel L k) S' v (e.subst (fun j => relTermDown (ts j)))).trans
      (sat_subst (S'.reduct (SigHom.inclRel L k)) e (fun j => relTermDown (ts j)) v)
    have hev : (fun i : Fin k => (relTermDown (ts i)).eval (S'.reduct (SigHom.inclRel L k)) v) =
        (fun i : Fin k => (ts i).eval S' v) :=
      funext fun i => (eval_map (SigHom.inclRel L k) S' v _).symm.trans (eval_relTermDown S' v (ts i))
    have hsub' : Sat S' v ((e.subst (fun j => relTermDown (ts j))).map (SigHom.inclRel L k)) ↔
        Sat (S'.reduct (SigHom.inclRel L k)) (fun i : Fin k => (ts i).eval S' v) e :=
      hsub.trans (hev ▸ Iff.rfl)
    exact hiff.trans ((sat_map (SigHom.inclRel L k) S' _ e).trans hsub'.symm)
  | _, .rel (some r) ts, v => by
    show S'.rel (some r) (fun j => (ts j).eval S' v) ↔
      S'.rel (some r) (fun j => ((relTermDown (ts j)).map (SigHom.inclRel L k)).eval S' v)
    have heq : (fun j => ((relTermDown (ts j)).map (SigHom.inclRel L k)).eval S' v) =
        (fun j => (ts j).eval S' v) := funext fun j => eval_relTermDown S' v (ts j)
    rw [heq]
  | _, .falsum, _ => Iff.rfl
  | _, .imp φ χ, v => imp_congr (sat_unfoldRelFormula e S' hax φ v) (sat_unfoldRelFormula e S' hax χ v)
  | _, .and φ χ, v => and_congr (sat_unfoldRelFormula e S' hax φ v) (sat_unfoldRelFormula e S' hax χ v)
  | _, .or φ χ, v => or_congr (sat_unfoldRelFormula e S' hax φ v) (sat_unfoldRelFormula e S' hax χ v)
  | _, .all φ, v => forall_congr' fun a => sat_unfoldRelFormula e S' hax φ (scons a v)
  | _, .ex φ, v => exists_congr fun a => sat_unfoldRelFormula e S' hax φ (scons a v)

/-- Proved corollary (forward half of `models_defAxiom_iff_unfold_preserves_sat`):
in any structure satisfying the defining axiom, every formula of the extended
language has the same truth value as its unfolding read back along the
inclusion. -/
theorem defExt_unfold_equiv_of_axiom (d : Defn L) (S' : Str d.sig α)
    (hax : S'.Models d.defAxiom) {n : Nat} (ψ : Formula d.sig n) (v : Fin n → α) :
    Sat S' v ψ ↔ Sat S' v ((d.unfold ψ).map d.incl) := by
  cases d with
  | fn k e => exact sat_unfoldFnFormula e S' hax ψ v
  | rel k e => exact sat_unfoldRelFormula e S' hax ψ v

/-- Proved corollary (entailment form): the definitional extension
`T + (c := e)` entails the universal closure of `ψ ↔ ψ[c := e]` for every
formula `ψ` of the extended language. -/
theorem defExt_eliminable (T : Theory L) (d : Defn L) {n : Nat} (ψ : Formula d.sig n) :
    Entails (d.theory T) (Formula.closeAll n (ψ.iff ((d.unfold ψ).map d.incl))) := by
  intro β S' hS'
  have hax : S'.Models d.defAxiom := hS' _ (Or.inr (List.Mem.head _))
  exact (sat_closeAll S' n _).2 fun v => (sat_iff _ _ _ _).2
    (defExt_unfold_equiv_of_axiom d S' hax ψ v)

/-! ### Unfolding is the identity on old-language formulas -/

theorem unfoldFnTerm_map_incl {k n : Nat} (e : Term L k) :
    ∀ t : Term L n, unfoldFnTerm e (t.map (SigHom.inclFn L k)) = t
  | .var _ => rfl
  | .app f ts => congrArg (Term.app f) (funext fun j => unfoldFnTerm_map_incl e (ts j))

theorem unfoldFnFormula_map_incl {k : Nat} (e : Term L k) :
    ∀ {n : Nat} (φ : Formula L n), unfoldFnFormula e (φ.map (SigHom.inclFn L k)) = φ
  | _, .eq s t => by simp [Formula.map, unfoldFnFormula, unfoldFnTerm_map_incl]
  | _, .rel r ts => congrArg (Formula.rel r) (funext fun j => unfoldFnTerm_map_incl e (ts j))
  | _, .falsum => rfl
  | _, .imp φ ψ => by
    simp [Formula.map, unfoldFnFormula, unfoldFnFormula_map_incl e φ, unfoldFnFormula_map_incl e ψ]
  | _, .and φ ψ => by
    simp [Formula.map, unfoldFnFormula, unfoldFnFormula_map_incl e φ, unfoldFnFormula_map_incl e ψ]
  | _, .or φ ψ => by
    simp [Formula.map, unfoldFnFormula, unfoldFnFormula_map_incl e φ, unfoldFnFormula_map_incl e ψ]
  | _, .all φ => by simp [Formula.map, unfoldFnFormula, unfoldFnFormula_map_incl e φ]
  | _, .ex φ => by simp [Formula.map, unfoldFnFormula, unfoldFnFormula_map_incl e φ]

theorem relTermDown_map_incl {k n : Nat} :
    ∀ t : Term L n, relTermDown (t.map (SigHom.inclRel L k)) = t
  | .var _ => rfl
  | .app f ts => congrArg (Term.app f) (funext fun j => relTermDown_map_incl (ts j))

theorem unfoldRelFormula_map_incl {k : Nat} (e : Formula L k) :
    ∀ {n : Nat} (φ : Formula L n), unfoldRelFormula e (φ.map (SigHom.inclRel L k)) = φ
  | _, .eq s t => by simp [Formula.map, unfoldRelFormula, relTermDown_map_incl]
  | _, .rel r ts => congrArg (Formula.rel r) (funext fun j => relTermDown_map_incl (ts j))
  | _, .falsum => rfl
  | _, .imp φ ψ => by
    simp [Formula.map, unfoldRelFormula, unfoldRelFormula_map_incl e φ, unfoldRelFormula_map_incl e ψ]
  | _, .and φ ψ => by
    simp [Formula.map, unfoldRelFormula, unfoldRelFormula_map_incl e φ, unfoldRelFormula_map_incl e ψ]
  | _, .or φ ψ => by
    simp [Formula.map, unfoldRelFormula, unfoldRelFormula_map_incl e φ, unfoldRelFormula_map_incl e ψ]
  | _, .all φ => by simp [Formula.map, unfoldRelFormula, unfoldRelFormula_map_incl e φ]
  | _, .ex φ => by simp [Formula.map, unfoldRelFormula, unfoldRelFormula_map_incl e φ]

/-- Unfolding an old-language formula read in the extended language gives it back. -/
theorem Defn.unfold_map_incl (d : Defn L) {n : Nat} (φ : Formula L n) :
    d.unfold (φ.map d.incl) = φ := by
  cases d with
  | fn k e => exact unfoldFnFormula_map_incl e φ
  | rel k e => exact unfoldRelFormula_map_incl e φ

theorem subst_var_id {k : Nat} : ∀ t : Term L k, t.subst Term.var = t
  | .var _ => rfl
  | .app f ts => congrArg (Term.app f) (funext fun j => subst_var_id (ts j))

theorem liftSubst_var {k : Nat} :
    (liftSubst (Term.var : Fin k → Term L k)) = Term.var := by
  funext i
  cases i using Fin.cases <;> rfl

theorem formula_subst_var_id : ∀ {k : Nat} (φ : Formula L k), φ.subst Term.var = φ
  | _, .eq s t => by simp [Formula.subst, subst_var_id]
  | _, .rel r ts => congrArg (Formula.rel r) (funext fun j => subst_var_id (ts j))
  | _, .falsum => rfl
  | _, .imp φ ψ => by simp [Formula.subst, formula_subst_var_id φ, formula_subst_var_id ψ]
  | _, .and φ ψ => by simp [Formula.subst, formula_subst_var_id φ, formula_subst_var_id ψ]
  | _, .or φ ψ => by simp [Formula.subst, formula_subst_var_id φ, formula_subst_var_id ψ]
  | _, .all φ => by simp [Formula.subst, liftSubst_var, formula_subst_var_id φ]
  | _, .ex φ => by simp [Formula.subst, liftSubst_var, formula_subst_var_id φ]

theorem unfoldFn_closeAll {k : Nat} (e : Term L k) :
    ∀ (m : Nat) (φ : Formula (L.addFn k) m),
      unfoldFnFormula e (Formula.closeAll m φ) = Formula.closeAll m (unfoldFnFormula e φ)
  | 0, _ => rfl
  | m + 1, φ => unfoldFn_closeAll e m (.all φ)

theorem unfoldRel_closeAll {k : Nat} (e : Formula L k) :
    ∀ (m : Nat) (φ : Formula (L.addRel k) m),
      unfoldRelFormula e (Formula.closeAll m φ) = Formula.closeAll m (unfoldRelFormula e φ)
  | 0, _ => rfl
  | m + 1, φ => unfoldRel_closeAll e m (.all φ)

/-- The unfolded defining axiom, read back in the extended language, holds in
every structure (it says `∀ x̄, e(x̄) = e(x̄)` or `∀ x̄, e(x̄) ↔ e(x̄)`). -/
theorem models_unfold_defAxiom (d : Defn L) (S' : Str d.sig α) :
    S'.Models ((d.unfold d.defAxiom).map d.incl) := by
  cases d with
  | fn k e =>
    have hcl : ((Defn.fn k e).unfold (Defn.fn k e).defAxiom) =
        Formula.closeAll k (unfoldFnFormula e
          (.eq (.app (none : (L.addFn k).Fn) (fun i => .var i)) (e.map (SigHom.inclFn L k)))) :=
      unfoldFn_closeAll e k _
    refine (models_map (SigHom.inclFn L k) S' _).2 ?_
    rw [hcl]
    refine (sat_closeAll _ k _).2 fun v => ?_
    simp only [unfoldFnFormula, unfoldFnTerm, unfoldFnTerm_map_incl, Sat]
    exact congrArg (fun u : Term L k => u.eval _ v) (subst_var_id e)
  | rel k e =>
    have hcl : ((Defn.rel k e).unfold (Defn.rel k e).defAxiom) =
        Formula.closeAll k (unfoldRelFormula e
          (.iff (.rel (none : (L.addRel k).Rel) (fun i => .var i)) (e.map (SigHom.inclRel L k)))) :=
      unfoldRel_closeAll e k _
    refine (models_map (SigHom.inclRel L k) S' _).2 ?_
    rw [hcl]
    refine (sat_closeAll _ k _).2 fun v => ?_
    simp only [Formula.iff, unfoldRelFormula, relTermDown, unfoldRelFormula_map_incl, Sat]
    exact ⟨fun h => (formula_subst_var_id e) ▸ h, fun h => (formula_subst_var_id e).symm ▸ h⟩

/-! ### Delta-conversion for a defined symbol -/

/-- Delta-conversion for the symbol introduced by `d`: two formulas of the
extended language are convertible when unfolding the defined symbol (replacing
each occurrence by its definiens, `Defn.unfold`) makes them syntactically equal.
This models the "transparent" reading of a definition, in which a checker may
see through the name to its body. It is conversion for this one symbol only:
there is no beta, iota or eta, and no dependent typing. -/
def Defn.DeltaConv (d : Defn L) {n : Nat} (φ ψ : Formula d.sig n) : Prop :=
  d.unfold φ = d.unfold ψ

instance Defn.decDeltaConv [DecidableEq L.Fn] [DecidableEq L.Rel] (d : Defn L) {n : Nat}
    (φ ψ : Formula d.sig n) : Decidable (d.DeltaConv φ ψ) :=
  inferInstanceAs (Decidable (d.unfold φ = d.unfold ψ))

/-- **Main result (characterization).** For an explicit definition `d` and any
structure `S'` of the extended language: `S'` satisfies the defining axiom iff
unfolding preserves truth, i.e. every formula `ψ` has, under every assignment,
the same truth value in `S'` as its unfolding read back along the inclusion. -/
theorem models_defAxiom_iff_unfold_preserves_sat (d : Defn L) (S' : Str d.sig α) :
    S'.Models d.defAxiom ↔
      ∀ {n : Nat} (ψ : Formula d.sig n) (v : Fin n → α),
        Sat S' v ψ ↔ Sat S' v ((d.unfold ψ).map d.incl) := by
  refine ⟨fun hax _ ψ v => defExt_unfold_equiv_of_axiom d S' hax ψ v, fun hall => ?_⟩
  exact (hall d.defAxiom noVars).2 (models_unfold_defAxiom d S')

/-- **Main result (characterization).** For an explicit definition `d` and any
structure `S'` of the extended language: `S'` satisfies the defining axiom iff
delta-conversion is sound in `S'`, i.e. any two delta-convertible formulas have
the same truth value in `S'` under every assignment. -/
theorem models_defAxiom_iff_deltaConv_sound (d : Defn L) (S' : Str d.sig α) :
    S'.Models d.defAxiom ↔
      ∀ {n : Nat} (φ ψ : Formula d.sig n), d.DeltaConv φ ψ →
        ∀ v : Fin n → α, (Sat S' v φ ↔ Sat S' v ψ) := by
  constructor
  · intro hax n φ ψ hconv v
    have h1 := defExt_unfold_equiv_of_axiom d S' hax φ v
    have h2 := defExt_unfold_equiv_of_axiom d S' hax ψ v
    unfold Defn.DeltaConv at hconv
    rw [hconv] at h1
    exact h1.trans h2.symm
  · intro hsound
    have hconv : d.DeltaConv d.defAxiom ((d.unfold d.defAxiom).map d.incl) := by
      unfold Defn.DeltaConv
      rw [Defn.unfold_map_incl]
    exact (hsound _ _ hconv noVars).2 (models_unfold_defAxiom d S')

end Toy.Extension
