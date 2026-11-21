/-!
# Structures, formulas, satisfaction and syntactic classes

Toy setting: the signature has one binary relation symbol `R`, one unary predicate
symbol `P`, and equality. There are no nullary atoms (no `⊤`, no `⊥`), so there are no
quantifier-free sentences (`no_qf_sentences`). Structures may have empty carriers; this
differs from the classical convention of non-empty domains, under which, for example,
`∃x, x = x` is valid. Formulas are well scoped: `Fml n` has `n` free variables, written
as de Bruijn indices (inside a quantifier, index `0` is the newly bound variable).

The universal, existential, `∀∃` and `∃∀` classes are prenex (a quantifier prefix over a
quantifier-free matrix). The positive and positive existential classes are not prenex:
they allow quantifiers under `∧` and `∨`. So a positive existential formula such as
`(∃x, P x) ∧ (∃y, P y)` need not be existential in the prenex sense
(`posExist_not_subset_exist`).
-/

namespace Toy.Transfer

/-- A structure for the signature `{R, P}`: a carrier type (possibly empty), a binary
relation `R` and a unary predicate `P`. It stands for either side of a model–system
comparison whose claims are first-order statements about one relation and one property. -/
structure Str where
  carrier : Type
  R : carrier → carrier → Prop
  P : carrier → Prop

/-- First-order formulas over `R`, `P` and `=` with `n` free variables (de Bruijn
indices; inside `all`/`ex`, index `0` is the bound variable). The connectives are
`¬`, `∧`, `∨`; implication is the abbreviation `Fml.imp`. -/
inductive Fml : Nat → Type where
  | rel {n : Nat} : Fin n → Fin n → Fml n
  | pred {n : Nat} : Fin n → Fml n
  | eq {n : Nat} : Fin n → Fin n → Fml n
  | neg {n : Nat} : Fml n → Fml n
  | and {n : Nat} : Fml n → Fml n → Fml n
  | or {n : Nat} : Fml n → Fml n → Fml n
  | all {n : Nat} : Fml (n + 1) → Fml n
  | ex {n : Nat} : Fml (n + 1) → Fml n

/-- Implication `φ → ψ`, as the abbreviation `¬φ ∨ ψ`. -/
def Fml.imp {n : Nat} (φ ψ : Fml n) : Fml n := .or (.neg φ) ψ

/-- Extend an environment with a value for the newly bound variable (index `0`);
the old variable `i` becomes index `i + 1`. -/
def Env.cons {α : Type} {n : Nat} (a : α) (e : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => a
  | ⟨i + 1, hi⟩ => e ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Tarskian satisfaction `M ⊨ φ [e]` of a formula under an environment. -/
def Sat (M : Str) : {n : Nat} → Fml n → (Fin n → M.carrier) → Prop
  | _, .rel i j, e => M.R (e i) (e j)
  | _, .pred i, e => M.P (e i)
  | _, .eq i j, e => e i = e j
  | _, .neg φ, e => ¬ Sat M φ e
  | _, .and φ ψ, e => Sat M φ e ∧ Sat M ψ e
  | _, .or φ ψ, e => Sat M φ e ∨ Sat M ψ e
  | _, .all φ, e => ∀ a : M.carrier, Sat M φ (Env.cons a e)
  | _, .ex φ, e => ∃ a : M.carrier, Sat M φ (Env.cons a e)

/-- Satisfaction of a sentence (a formula with no free variables). -/
def SatS (M : Str) (φ : Fml 0) : Prop := Sat M φ Fin.elim0

theorem comp_cons {α β : Type} {n : Nat} (h : α → β) (a : α) (e : Fin n → α) :
    h ∘ Env.cons a e = Env.cons (h a) (h ∘ e) := by
  funext i
  rcases i with ⟨_ | i, hi⟩ <;> rfl

theorem comp_elim0 {α β : Type} (h : α → β) : h ∘ (Fin.elim0 : Fin 0 → α) = Fin.elim0 :=
  funext (fun i => i.elim0)

/-- For sentences, pushing the empty environment through a map changes nothing. -/
theorem sat_comp_elim0_iff {A B : Str} (h : A.carrier → B.carrier) (φ : Fml 0) :
    Sat B φ (h ∘ Fin.elim0) ↔ SatS B φ := by
  rw [comp_elim0]; rfl

/-! ## Syntactic classes -/

/-- Quantifier-free formulas (negation allowed). -/
inductive IsQF {n : Nat} : Fml n → Prop where
  | rel (i j : Fin n) : IsQF (.rel i j)
  | pred (i : Fin n) : IsQF (.pred i)
  | eq (i j : Fin n) : IsQF (.eq i j)
  | neg {φ : Fml n} : IsQF φ → IsQF (.neg φ)
  | and {φ ψ : Fml n} : IsQF φ → IsQF ψ → IsQF (.and φ ψ)
  | or {φ ψ : Fml n} : IsQF φ → IsQF ψ → IsQF (.or φ ψ)

/-- There are no quantifier-free sentences: every atom of `Fml 0` would need a variable
of `Fin 0`. -/
theorem no_qf_sentences : ∀ φ : Fml 0, ¬ IsQF φ := by
  intro φ hq
  induction hq with
  | rel i _ => exact i.elim0
  | pred i => exact i.elim0
  | eq i _ => exact i.elim0
  | neg _ ih => exact ih
  | and _ _ ih _ => exact ih
  | or _ _ ih _ => exact ih

/-- Equality-free formulas: no `=` atom anywhere. -/
inductive IsEqFree : {n : Nat} → Fml n → Prop where
  | rel {n : Nat} (i j : Fin n) : IsEqFree (.rel i j)
  | pred {n : Nat} (i : Fin n) : IsEqFree (.pred i)
  | neg {n : Nat} {φ : Fml n} : IsEqFree φ → IsEqFree (.neg φ)
  | and {n : Nat} {φ ψ : Fml n} : IsEqFree φ → IsEqFree ψ → IsEqFree (.and φ ψ)
  | or {n : Nat} {φ ψ : Fml n} : IsEqFree φ → IsEqFree ψ → IsEqFree (.or φ ψ)
  | all {n : Nat} {φ : Fml (n + 1)} : IsEqFree φ → IsEqFree (.all φ)
  | ex {n : Nat} {φ : Fml (n + 1)} : IsEqFree φ → IsEqFree (.ex φ)

/-- Universal formulas (prenex): a (possibly empty) prefix of `∀` over a quantifier-free
matrix. -/
inductive IsUniv : {n : Nat} → Fml n → Prop where
  | qf {n : Nat} {φ : Fml n} : IsQF φ → IsUniv φ
  | all {n : Nat} {φ : Fml (n + 1)} : IsUniv φ → IsUniv (.all φ)

/-- Existential formulas (prenex): a (possibly empty) prefix of `∃` over a quantifier-free
matrix. -/
inductive IsExist : {n : Nat} → Fml n → Prop where
  | qf {n : Nat} {φ : Fml n} : IsQF φ → IsExist φ
  | ex {n : Nat} {φ : Fml (n + 1)} : IsExist φ → IsExist (.ex φ)

/-- `∀∃` formulas: a (possibly empty) `∀` prefix over an existential formula. -/
inductive IsAE : {n : Nat} → Fml n → Prop where
  | exist {n : Nat} {φ : Fml n} : IsExist φ → IsAE φ
  | all {n : Nat} {φ : Fml (n + 1)} : IsAE φ → IsAE (.all φ)

/-- `∃∀` formulas: a (possibly empty) `∃` prefix over a universal formula. -/
inductive IsEA : {n : Nat} → Fml n → Prop where
  | univ {n : Nat} {φ : Fml n} : IsUniv φ → IsEA φ
  | ex {n : Nat} {φ : Fml (n + 1)} : IsEA φ → IsEA (.ex φ)

/-- Positive formulas: no negation anywhere; both quantifiers and equality allowed;
quantifiers may occur under `∧` and `∨` (not prenex). -/
inductive IsPos : {n : Nat} → Fml n → Prop where
  | rel {n : Nat} (i j : Fin n) : IsPos (.rel i j)
  | pred {n : Nat} (i : Fin n) : IsPos (.pred i)
  | eq {n : Nat} (i j : Fin n) : IsPos (.eq i j)
  | and {n : Nat} {φ ψ : Fml n} : IsPos φ → IsPos ψ → IsPos (.and φ ψ)
  | or {n : Nat} {φ ψ : Fml n} : IsPos φ → IsPos ψ → IsPos (.or φ ψ)
  | all {n : Nat} {φ : Fml (n + 1)} : IsPos φ → IsPos (.all φ)
  | ex {n : Nat} {φ : Fml (n + 1)} : IsPos φ → IsPos (.ex φ)

/-- Positive existential formulas: no negation and no `∀`; `∃` may occur under `∧` and
`∨` (not prenex). -/
inductive IsPosExist : {n : Nat} → Fml n → Prop where
  | rel {n : Nat} (i j : Fin n) : IsPosExist (.rel i j)
  | pred {n : Nat} (i : Fin n) : IsPosExist (.pred i)
  | eq {n : Nat} (i j : Fin n) : IsPosExist (.eq i j)
  | and {n : Nat} {φ ψ : Fml n} : IsPosExist φ → IsPosExist ψ → IsPosExist (.and φ ψ)
  | or {n : Nat} {φ ψ : Fml n} : IsPosExist φ → IsPosExist ψ → IsPosExist (.or φ ψ)
  | ex {n : Nat} {φ : Fml (n + 1)} : IsPosExist φ → IsPosExist (.ex φ)

/-! ### Boolean recognizers (proved equivalent to the inductive classes) -/

/-- Boolean recognizer for `IsQF`. -/
def Fml.qfB : {n : Nat} → Fml n → Bool
  | _, .rel _ _ => true
  | _, .pred _ => true
  | _, .eq _ _ => true
  | _, .neg φ => φ.qfB
  | _, .and φ ψ => φ.qfB && ψ.qfB
  | _, .or φ ψ => φ.qfB && ψ.qfB
  | _, .all _ => false
  | _, .ex _ => false

/-- Boolean recognizer for `IsUniv`. -/
def Fml.univB : {n : Nat} → Fml n → Bool
  | _, .all φ => φ.univB
  | _, .ex _ => false
  | _, .rel i j => (Fml.rel i j).qfB
  | _, .pred i => (Fml.pred i).qfB
  | _, .eq i j => (Fml.eq i j).qfB
  | _, .neg φ => (Fml.neg φ).qfB
  | _, .and φ ψ => (Fml.and φ ψ).qfB
  | _, .or φ ψ => (Fml.or φ ψ).qfB

/-- Boolean recognizer for `IsExist`. -/
def Fml.existB : {n : Nat} → Fml n → Bool
  | _, .ex φ => φ.existB
  | _, .all _ => false
  | _, .rel i j => (Fml.rel i j).qfB
  | _, .pred i => (Fml.pred i).qfB
  | _, .eq i j => (Fml.eq i j).qfB
  | _, .neg φ => (Fml.neg φ).qfB
  | _, .and φ ψ => (Fml.and φ ψ).qfB
  | _, .or φ ψ => (Fml.or φ ψ).qfB

/-- Boolean recognizer for `IsAE`. -/
def Fml.aeB : {n : Nat} → Fml n → Bool
  | _, .all φ => φ.aeB
  | _, .ex φ => (Fml.ex φ).existB
  | _, .rel i j => (Fml.rel i j).existB
  | _, .pred i => (Fml.pred i).existB
  | _, .eq i j => (Fml.eq i j).existB
  | _, .neg φ => (Fml.neg φ).existB
  | _, .and φ ψ => (Fml.and φ ψ).existB
  | _, .or φ ψ => (Fml.or φ ψ).existB

/-- Boolean recognizer for `IsEA`. -/
def Fml.eaB : {n : Nat} → Fml n → Bool
  | _, .ex φ => φ.eaB
  | _, .all φ => (Fml.all φ).univB
  | _, .rel i j => (Fml.rel i j).univB
  | _, .pred i => (Fml.pred i).univB
  | _, .eq i j => (Fml.eq i j).univB
  | _, .neg φ => (Fml.neg φ).univB
  | _, .and φ ψ => (Fml.and φ ψ).univB
  | _, .or φ ψ => (Fml.or φ ψ).univB

/-- Boolean recognizer for `IsPos`. -/
def Fml.posB : {n : Nat} → Fml n → Bool
  | _, .rel _ _ => true
  | _, .pred _ => true
  | _, .eq _ _ => true
  | _, .neg _ => false
  | _, .and φ ψ => φ.posB && ψ.posB
  | _, .or φ ψ => φ.posB && ψ.posB
  | _, .all φ => φ.posB
  | _, .ex φ => φ.posB

/-- Boolean recognizer for `IsPosExist`. -/
def Fml.posExistB : {n : Nat} → Fml n → Bool
  | _, .rel _ _ => true
  | _, .pred _ => true
  | _, .eq _ _ => true
  | _, .neg _ => false
  | _, .and φ ψ => φ.posExistB && ψ.posExistB
  | _, .or φ ψ => φ.posExistB && ψ.posExistB
  | _, .all _ => false
  | _, .ex φ => φ.posExistB

theorem qfB_iff {n : Nat} (φ : Fml n) : φ.qfB = true ↔ IsQF φ := by
  induction φ with
  | rel i j => exact ⟨fun _ => .rel i j, fun _ => rfl⟩
  | pred i => exact ⟨fun _ => .pred i, fun _ => rfl⟩
  | eq i j => exact ⟨fun _ => .eq i j, fun _ => rfl⟩
  | neg φ ih =>
    refine ⟨fun h => .neg (ih.1 h), fun h => ?_⟩
    cases h with
    | neg h => exact ih.2 h
  | and φ ψ ihφ ihψ =>
    simp only [Fml.qfB, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ => .and (ihφ.1 h1) (ihψ.1 h2), fun h => ?_⟩
    cases h with
    | and h1 h2 => exact ⟨ihφ.2 h1, ihψ.2 h2⟩
  | or φ ψ ihφ ihψ =>
    simp only [Fml.qfB, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ => .or (ihφ.1 h1) (ihψ.1 h2), fun h => ?_⟩
    cases h with
    | or h1 h2 => exact ⟨ihφ.2 h1, ihψ.2 h2⟩
  | all φ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | ex φ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem univB_iff {n : Nat} (φ : Fml n) : φ.univB = true ↔ IsUniv φ := by
  induction φ with
  | all φ ih =>
    refine ⟨fun h => .all (ih.1 h), fun h => ?_⟩
    cases h with
    | qf h => nomatch h
    | all h => exact ih.2 h
  | ex φ _ =>
    refine ⟨fun h => (nomatch h), fun h => ?_⟩
    cases h with
    | qf h => nomatch h
  | rel i j => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | pred i => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | eq i j => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | neg φ _ => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | and φ ψ _ _ => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | or φ ψ _ _ => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩

theorem existB_iff {n : Nat} (φ : Fml n) : φ.existB = true ↔ IsExist φ := by
  induction φ with
  | ex φ ih =>
    refine ⟨fun h => .ex (ih.1 h), fun h => ?_⟩
    cases h with
    | qf h => nomatch h
    | ex h => exact ih.2 h
  | all φ _ =>
    refine ⟨fun h => (nomatch h), fun h => ?_⟩
    cases h with
    | qf h => nomatch h
  | rel i j => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | pred i => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | eq i j => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | neg φ _ => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | and φ ψ _ _ => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩
  | or φ ψ _ _ => exact (qfB_iff _).trans ⟨.qf, fun h => by cases h; assumption⟩

theorem aeB_iff {n : Nat} (φ : Fml n) : φ.aeB = true ↔ IsAE φ := by
  induction φ with
  | all φ ih =>
    refine ⟨fun h => .all (ih.1 h), fun h => ?_⟩
    cases h with
    | exist h => cases h with | qf h => nomatch h
    | all h => exact ih.2 h
  | ex φ _ => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩
  | rel i j => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩
  | pred i => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩
  | eq i j => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩
  | neg φ _ => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩
  | and φ ψ _ _ => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩
  | or φ ψ _ _ => exact (existB_iff _).trans ⟨.exist, fun h => by cases h; assumption⟩

theorem eaB_iff {n : Nat} (φ : Fml n) : φ.eaB = true ↔ IsEA φ := by
  induction φ with
  | ex φ ih =>
    refine ⟨fun h => .ex (ih.1 h), fun h => ?_⟩
    cases h with
    | univ h => cases h with | qf h => nomatch h
    | ex h => exact ih.2 h
  | all φ _ => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩
  | rel i j => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩
  | pred i => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩
  | eq i j => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩
  | neg φ _ => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩
  | and φ ψ _ _ => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩
  | or φ ψ _ _ => exact (univB_iff _).trans ⟨.univ, fun h => by cases h; assumption⟩

theorem posB_iff {n : Nat} (φ : Fml n) : φ.posB = true ↔ IsPos φ := by
  induction φ with
  | rel i j => exact ⟨fun _ => .rel i j, fun _ => rfl⟩
  | pred i => exact ⟨fun _ => .pred i, fun _ => rfl⟩
  | eq i j => exact ⟨fun _ => .eq i j, fun _ => rfl⟩
  | neg φ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | and φ ψ ihφ ihψ =>
    simp only [Fml.posB, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ => .and (ihφ.1 h1) (ihψ.1 h2), fun h => ?_⟩
    cases h with
    | and h1 h2 => exact ⟨ihφ.2 h1, ihψ.2 h2⟩
  | or φ ψ ihφ ihψ =>
    simp only [Fml.posB, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ => .or (ihφ.1 h1) (ihψ.1 h2), fun h => ?_⟩
    cases h with
    | or h1 h2 => exact ⟨ihφ.2 h1, ihψ.2 h2⟩
  | all φ ih =>
    refine ⟨fun h => .all (ih.1 h), fun h => ?_⟩
    cases h with
    | all h => exact ih.2 h
  | ex φ ih =>
    refine ⟨fun h => .ex (ih.1 h), fun h => ?_⟩
    cases h with
    | ex h => exact ih.2 h

theorem posExistB_iff {n : Nat} (φ : Fml n) : φ.posExistB = true ↔ IsPosExist φ := by
  induction φ with
  | rel i j => exact ⟨fun _ => .rel i j, fun _ => rfl⟩
  | pred i => exact ⟨fun _ => .pred i, fun _ => rfl⟩
  | eq i j => exact ⟨fun _ => .eq i j, fun _ => rfl⟩
  | neg φ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | and φ ψ ihφ ihψ =>
    simp only [Fml.posExistB, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ => .and (ihφ.1 h1) (ihψ.1 h2), fun h => ?_⟩
    cases h with
    | and h1 h2 => exact ⟨ihφ.2 h1, ihψ.2 h2⟩
  | or φ ψ ihφ ihψ =>
    simp only [Fml.posExistB, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ => .or (ihφ.1 h1) (ihψ.1 h2), fun h => ?_⟩
    cases h with
    | or h1 h2 => exact ⟨ihφ.2 h1, ihψ.2 h2⟩
  | all φ _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | ex φ ih =>
    refine ⟨fun h => .ex (ih.1 h), fun h => ?_⟩
    cases h with
    | ex h => exact ih.2 h

instance {n : Nat} (φ : Fml n) : Decidable (IsQF φ) := decidable_of_iff _ (qfB_iff φ)
instance {n : Nat} (φ : Fml n) : Decidable (IsUniv φ) := decidable_of_iff _ (univB_iff φ)
instance {n : Nat} (φ : Fml n) : Decidable (IsExist φ) := decidable_of_iff _ (existB_iff φ)
instance {n : Nat} (φ : Fml n) : Decidable (IsAE φ) := decidable_of_iff _ (aeB_iff φ)
instance {n : Nat} (φ : Fml n) : Decidable (IsEA φ) := decidable_of_iff _ (eaB_iff φ)
instance {n : Nat} (φ : Fml n) : Decidable (IsPos φ) := decidable_of_iff _ (posB_iff φ)
instance {n : Nat} (φ : Fml n) : Decidable (IsPosExist φ) := decidable_of_iff _ (posExistB_iff φ)

end Toy.Transfer
