/-!
# First-order terms and finite substitutions

First-order terms over constructor symbols (named by natural numbers) and variables (also
named by natural numbers). A term models a type expression such as `Vec<Box<T>>` or
`(u8, T)`; constructor applications carry their argument list explicitly, so a symbol used with
two different argument counts simply yields two terms that never unify (an arity mismatch is a
clash).

Substitutions are finite association lists (`List (Nat × Term)`); lookup uses the first binding
for a variable, and unbound variables are left unchanged.
-/

namespace Toy.Unify

/-- First-order terms: a variable `var x`, or a constructor `f` applied to a list of argument
terms. Captures the syntax of (monomorphic or generic) type expressions in a type checker or
trait solver, without binders. -/
inductive Term where
  | var : Nat → Term
  | con : Nat → List Term → Term
  deriving Inhabited

mutual
/-- Display a term (structural recursion, so that no `partial` definition is needed). -/
def Term.format : Term → Std.Format
  | .var x => "var " ++ repr x
  | .con f ts => "con " ++ repr f ++ " [" ++ Term.formatList ts ++ "]"
/-- Display a list of terms, comma-separated (companion of `Term.format`). -/
def Term.formatList : List Term → Std.Format
  | [] => ""
  | [t] => Term.format t
  | t :: ts => Term.format t ++ ", " ++ Term.formatList ts
end

instance : Repr Term := ⟨fun t _ => Term.format t⟩

mutual
/-- Decidable equality on terms, by structural recursion (so that `decide` evaluates it). -/
def Term.decEq : (a b : Term) → Decidable (a = b)
  | .var x, .var y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun h' => h (Term.var.inj h'))
  | .var _, .con _ _ => isFalse nofun
  | .con _ _, .var _ => isFalse nofun
  | .con f ss, .con g ts =>
    if hf : f = g then
      match Term.decEqList ss ts with
      | isTrue h => isTrue (by subst hf; subst h; rfl)
      | isFalse h => isFalse (fun h' => h (Term.con.inj h').2)
    else isFalse (fun h' => hf (Term.con.inj h').1)
/-- Decidable equality on term lists (companion of `Term.decEq`). -/
def Term.decEqList : (a b : List Term) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | a :: as, b :: bs =>
    match Term.decEq a b with
    | isTrue h1 =>
      match Term.decEqList as bs with
      | isTrue h2 => isTrue (by subst h1; subst h2; rfl)
      | isFalse h2 => isFalse (fun h => h2 (List.cons.inj h).2)
    | isFalse h1 => isFalse (fun h => h1 (List.cons.inj h).1)
end

instance : DecidableEq Term := Term.decEq

/-! ## Example signature

Constructor symbols used in examples: `u8/0`, `u32/0`, `Box/1`, `Vec/1`, `Pair/2`. -/

/-- The nullary constructor `u8` (symbol 0). -/
def u8 : Term := .con 0 []
/-- The nullary constructor `u32` (symbol 1). -/
def u32 : Term := .con 1 []
/-- The unary constructor `Box` (symbol 2). -/
def box (t : Term) : Term := .con 2 [t]
/-- The unary constructor `Vec` (symbol 3). -/
def vec (t : Term) : Term := .con 3 [t]
/-- The binary constructor `Pair` (symbol 4). -/
def pair (a b : Term) : Term := .con 4 [a, b]

/-! ## Variables, constructors, groundness -/

mutual
/-- The variables occurring in a term, in left-to-right order (with repetitions). -/
def Term.vars : Term → List Nat
  | .var x => [x]
  | .con _ ts => Term.varsList ts
/-- The variables occurring in a list of terms (companion of `Term.vars`). -/
def Term.varsList : List Term → List Nat
  | [] => []
  | t :: ts => Term.vars t ++ Term.varsList ts
end

mutual
/-- The constructor symbols occurring in a term (with repetitions). -/
def Term.ctors : Term → List Nat
  | .var _ => []
  | .con f ts => f :: Term.ctorsList ts
/-- The constructor symbols occurring in a list of terms (companion of `Term.ctors`). -/
def Term.ctorsList : List Term → List Nat
  | [] => []
  | t :: ts => Term.ctors t ++ Term.ctorsList ts
end

/-- `occurs x t`: the variable `x` occurs in `t`. This is the test performed by the occurs
check. -/
def occurs (x : Nat) (t : Term) : Bool := t.vars.contains x

/-- A term is ground when it contains no variables (a fully concrete type). -/
def IsGround (t : Term) : Prop := t.vars = []

instance (t : Term) : Decidable (IsGround t) := inferInstanceAs (Decidable (t.vars = []))

/-- The two terms share no variable ("renamed apart"). -/
def VarsDisjoint (s t : Term) : Prop := ∀ x ∈ s.vars, x ∉ t.vars

instance (s t : Term) : Decidable (VarsDisjoint s t) :=
  inferInstanceAs (Decidable (∀ x ∈ s.vars, x ∉ t.vars))

/-! ## Substitutions -/

/-- A finite substitution: an association list from variables to terms. The first binding of a
variable is the one used; variables without a binding are mapped to themselves. -/
abbrev Subst := List (Nat × Term)

/-- The image of the variable `x` under `σ`. -/
def substVar (σ : Subst) (x : Nat) : Term :=
  match σ.lookup x with
  | some t => t
  | none => .var x

mutual
/-- Apply a substitution to a term (simultaneous replacement of variables). -/
def subst (σ : Subst) : Term → Term
  | .var x => substVar σ x
  | .con f ts => .con f (substList σ ts)
/-- Apply a substitution to each term of a list (companion of `subst`). -/
def substList (σ : Subst) : List Term → List Term
  | [] => []
  | t :: ts => subst σ t :: substList σ ts
end

/-- `iterSubst σ k t` applies `σ` to `t` exactly `k` times. For a substitution whose bindings
are cyclic (e.g. `x ↦ Box x`) this unfolds the (possibly infinite) tree it denotes. -/
def iterSubst (σ : Subst) : Nat → Term → Term
  | 0, t => t
  | k + 1, t => iterSubst σ k (subst σ t)

/-! ## Basic lemmas -/

theorem subst_var (σ : Subst) (x : Nat) : subst σ (.var x) = substVar σ x := rfl

theorem substList_eq_map (σ : Subst) : ∀ ts : List Term, substList σ ts = ts.map (subst σ)
  | [] => rfl
  | t :: ts => by simp only [substList, List.map_cons, substList_eq_map σ ts]

theorem subst_con (σ : Subst) (f : Nat) (ts : List Term) :
    subst σ (.con f ts) = .con f (ts.map (subst σ)) := by
  simp only [subst, substList_eq_map]

mutual
/-- Two substitutions that agree on the variables of `t` agree on `t`. -/
theorem subst_congr_vars {σ τ : Subst} :
    ∀ t : Term, (∀ x ∈ t.vars, substVar σ x = substVar τ x) → subst σ t = subst τ t
  | .var x, h => h x (by simp [Term.vars])
  | .con f ts, h => by
    simp only [subst]
    rw [substList_congr_vars ts (by simpa [Term.vars] using h)]
/-- List companion of `subst_congr_vars`. -/
theorem substList_congr_vars {σ τ : Subst} :
    ∀ ts : List Term, (∀ x ∈ Term.varsList ts, substVar σ x = substVar τ x) →
      substList σ ts = substList τ ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [substList]
    rw [subst_congr_vars t (fun x hx => h x (by simp [Term.varsList, hx])),
      substList_congr_vars ts (fun x hx => h x (by simp [Term.varsList, hx]))]
end

mutual
/-- Composition, pointwise: if `τ x = ρ (σ x)` for every variable of `t`, then
`τ t = ρ (σ t)`. -/
theorem subst_comp_of_vars {σ τ ρ : Subst} :
    ∀ t : Term, (∀ x ∈ t.vars, substVar τ x = subst ρ (substVar σ x)) →
      subst τ t = subst ρ (subst σ t)
  | .var x, h => h x (by simp [Term.vars])
  | .con f ts, h => by
    simp only [subst]
    rw [substList_comp_of_vars ts (by simpa [Term.vars] using h)]
/-- List companion of `subst_comp_of_vars`. -/
theorem substList_comp_of_vars {σ τ ρ : Subst} :
    ∀ ts : List Term, (∀ x ∈ Term.varsList ts, substVar τ x = subst ρ (substVar σ x)) →
      substList τ ts = substList ρ (substList σ ts)
  | [], _ => rfl
  | t :: ts, h => by
    simp only [substList]
    rw [subst_comp_of_vars t (fun x hx => h x (by simp [Term.varsList, hx])),
      substList_comp_of_vars ts (fun x hx => h x (by simp [Term.varsList, hx]))]
end

mutual
/-- A substitution that fixes every variable of `t` fixes `t`. -/
theorem subst_eq_self_of_vars {σ : Subst} :
    ∀ t : Term, (∀ x ∈ t.vars, substVar σ x = .var x) → subst σ t = t
  | .var x, h => h x (by simp [Term.vars])
  | .con f ts, h => by
    simp only [subst]
    rw [substList_eq_self_of_vars ts (by simpa [Term.vars] using h)]
/-- List companion of `subst_eq_self_of_vars`. -/
theorem substList_eq_self_of_vars {σ : Subst} :
    ∀ ts : List Term, (∀ x ∈ Term.varsList ts, substVar σ x = .var x) → substList σ ts = ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [substList]
    rw [subst_eq_self_of_vars t (fun x hx => h x (by simp [Term.varsList, hx])),
      substList_eq_self_of_vars ts (fun x hx => h x (by simp [Term.varsList, hx]))]
end

theorem substVar_nil (x : Nat) : substVar [] x = .var x := rfl

theorem substVar_cons (y : Nat) (u : Term) (σ : Subst) (x : Nat) :
    substVar ((y, u) :: σ) x = if x = y then u else substVar σ x := by
  by_cases h : x = y
  · subst h; simp [substVar, List.lookup]
  · have : (x == y) = false := by simpa using h
    simp [substVar, List.lookup, this, h]

/-- Composition of substitutions as a finite list: `Subst.comp θ σ` first applies `σ`, then
`θ` (see `subst_comp`). -/
def Subst.comp (θ σ : Subst) : Subst := σ.map (fun p => (p.1, subst θ p.2)) ++ θ

theorem substVar_comp (θ σ : Subst) (x : Nat) :
    substVar (Subst.comp θ σ) x = subst θ (substVar σ x) := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨y, w⟩ := p
    have e : Subst.comp θ ((y, w) :: σ) = (y, subst θ w) :: Subst.comp θ σ := rfl
    rw [e, substVar_cons, substVar_cons]
    by_cases h : x = y
    · simp [h]
    · simp [h, ih]

theorem subst_comp (θ σ : Subst) (t : Term) :
    subst (Subst.comp θ σ) t = subst θ (subst σ t) :=
  subst_comp_of_vars t (fun x _ => substVar_comp θ σ x)

theorem subst_nil (t : Term) : subst [] t = t :=
  subst_eq_self_of_vars t (fun _ _ => rfl)

theorem subst_of_isGround {t : Term} (h : IsGround t) (σ : Subst) : subst σ t = t :=
  subst_eq_self_of_vars t (fun x hx => by
    unfold IsGround at h
    rw [h] at hx
    simp at hx)

end Toy.Unify
