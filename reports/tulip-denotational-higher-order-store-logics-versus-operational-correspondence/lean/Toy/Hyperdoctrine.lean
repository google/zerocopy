/-
An indexed BI algebra ("BI-hyperdoctrine" in the sense of Biering, Birkedal and
Torp-Smith) over the category of types and functions.

Toy model. The base category is `Type` with ordinary functions; the fibre over `Γ`
is `Γ → SProp S` ordered pointwise; reindexing is precomposition.
-/
import Toy.BI

namespace Toy

/-- The fibre over `Γ`: step-indexed resource predicates depending on `Γ`. -/
def Pred (S : SepAlg) (Γ : Type) : Type := Γ → SProp S

namespace Pred

variable {S : SepAlg} {Γ Δ Θ X : Type}

/-- Entailment in the fibre over `Γ`. -/
def entails (φ ψ : Pred S Γ) : Prop := ∀ γ, φ γ ⊑ ψ γ

@[inherit_doc] infix:25 " ⊩ " => entails

theorem entails_refl (φ : Pred S Γ) : φ ⊩ φ := fun γ => SProp.entails_refl (φ γ)

theorem entails_trans {φ ψ χ : Pred S Γ} (h₁ : φ ⊩ ψ) (h₂ : ψ ⊩ χ) : φ ⊩ χ :=
  fun γ => SProp.entails_trans (h₁ γ) (h₂ γ)

theorem entails_antisymm {φ ψ : Pred S Γ} (h₁ : φ ⊩ ψ) (h₂ : ψ ⊩ φ) : φ = ψ :=
  funext fun γ => SProp.entails_antisymm (h₁ γ) (h₂ γ)

/-- Reindexing (substitution) along a base morphism. -/
def reidx (f : Δ → Γ) (φ : Pred S Γ) : Pred S Δ := fun δ => φ (f δ)

def top : Pred S Γ := fun _ => SProp.top
def bot : Pred S Γ := fun _ => SProp.bot
def emp : Pred S Γ := fun _ => SProp.emp
def and (φ ψ : Pred S Γ) : Pred S Γ := fun γ => SProp.and (φ γ) (ψ γ)
def or (φ ψ : Pred S Γ) : Pred S Γ := fun γ => SProp.or (φ γ) (ψ γ)
def imp (φ ψ : Pred S Γ) : Pred S Γ := fun γ => SProp.imp (φ γ) (ψ γ)
def sep (φ ψ : Pred S Γ) : Pred S Γ := fun γ => SProp.sep (φ γ) (ψ γ)
def wand (φ ψ : Pred S Γ) : Pred S Γ := fun γ => SProp.wand (φ γ) (ψ γ)
def later (φ : Pred S Γ) : Pred S Γ := fun γ => SProp.later (φ γ)

/-- Existential quantification along the projection `Γ × X → Γ`. -/
def ex (φ : Pred S (Γ × X)) : Pred S Γ := fun γ => SProp.ex fun x => φ (γ, x)

/-- Universal quantification along the projection `Γ × X → Γ`. -/
def all (φ : Pred S (Γ × X)) : Pred S Γ := fun γ => SProp.all fun x => φ (γ, x)

/-- The equality predicate on `X`. -/
def eqP (X : Type) : Pred S (X × X) := fun p => SProp.pure (p.1 = p.2)

/-! ### Functoriality: substitution is strictly functorial -/

theorem reidx_id (φ : Pred S Γ) : reidx id φ = φ := rfl

theorem reidx_comp (f : Δ → Γ) (g : Θ → Δ) (φ : Pred S Γ) :
    reidx (f ∘ g) φ = reidx g (reidx f φ) := rfl

theorem reidx_mono (f : Δ → Γ) {φ ψ : Pred S Γ} (h : φ ⊩ ψ) : reidx f φ ⊩ reidx f ψ :=
  fun δ => h (f δ)

/-- Equal base morphisms induce equal substitutions on every predicate. -/
theorem reidx_congr {f g : Δ → Γ} (h : f = g) (φ : Pred S Γ) : reidx f φ = reidx g φ := by
  subst h; rfl

/-! ### Reindexing is a BI-algebra homomorphism commuting with `▷` -/

theorem reidx_top (f : Δ → Γ) : reidx f (top : Pred S Γ) = top := rfl
theorem reidx_bot (f : Δ → Γ) : reidx f (bot : Pred S Γ) = bot := rfl
theorem reidx_emp (f : Δ → Γ) : reidx f (emp : Pred S Γ) = emp := rfl
theorem reidx_and (f : Δ → Γ) (φ ψ : Pred S Γ) :
    reidx f (and φ ψ) = and (reidx f φ) (reidx f ψ) := rfl
theorem reidx_or (f : Δ → Γ) (φ ψ : Pred S Γ) :
    reidx f (or φ ψ) = or (reidx f φ) (reidx f ψ) := rfl
theorem reidx_imp (f : Δ → Γ) (φ ψ : Pred S Γ) :
    reidx f (imp φ ψ) = imp (reidx f φ) (reidx f ψ) := rfl
theorem reidx_sep (f : Δ → Γ) (φ ψ : Pred S Γ) :
    reidx f (sep φ ψ) = sep (reidx f φ) (reidx f ψ) := rfl
theorem reidx_wand (f : Δ → Γ) (φ ψ : Pred S Γ) :
    reidx f (wand φ ψ) = wand (reidx f φ) (reidx f ψ) := rfl
theorem reidx_later (f : Δ → Γ) (φ : Pred S Γ) :
    reidx f (later φ) = later (reidx f φ) := rfl

/-! ### Fibrewise BI laws -/

theorem imp_adj {φ ψ χ : Pred S Γ} : (and φ ψ ⊩ χ) ↔ (φ ⊩ imp ψ χ) :=
  ⟨fun H γ => SProp.imp_adj.1 (H γ), fun H γ => SProp.imp_adj.2 (H γ)⟩

theorem wand_adj {φ ψ χ : Pred S Γ} : (sep φ ψ ⊩ χ) ↔ (φ ⊩ wand ψ χ) :=
  ⟨fun H γ => SProp.wand_adj.1 (H γ), fun H γ => SProp.wand_adj.2 (H γ)⟩

theorem sep_comm (φ ψ : Pred S Γ) : sep φ ψ ⊩ sep ψ φ := fun γ => SProp.sep_comm (φ γ) (ψ γ)

theorem sep_assoc (φ ψ χ : Pred S Γ) : sep (sep φ ψ) χ ⊩ sep φ (sep ψ χ) :=
  fun γ => SProp.sep_assoc (φ γ) (ψ γ) (χ γ)

theorem later_intro (φ : Pred S Γ) : φ ⊩ later φ := fun γ => SProp.later_intro (φ γ)

theorem loeb {φ : Pred S Γ} (H : later φ ⊩ φ) : top ⊩ φ := fun γ => SProp.loeb (H γ)

/-! ### Quantifiers as adjoints to weakening, with Beck–Chevalley and Frobenius -/

/-- `∃ ⊣ π*`. -/
theorem ex_adj {φ : Pred S (Γ × X)} {ψ : Pred S Γ} :
    (ex φ ⊩ ψ) ↔ (φ ⊩ reidx Prod.fst ψ) :=
  ⟨fun H p n h a => H p.1 n h ⟨p.2, a⟩,
   fun H γ n h ⟨x, a⟩ => H (γ, x) n h a⟩

/-- `π* ⊣ ∀`. -/
theorem all_adj {φ : Pred S (Γ × X)} {ψ : Pred S Γ} :
    (reidx Prod.fst ψ ⊩ φ) ↔ (ψ ⊩ all φ) :=
  ⟨fun H γ n h a x => H (γ, x) n h a,
   fun H p n h a => H p.1 n h a p.2⟩

/-- Beck–Chevalley for `∃`: substitution commutes with the quantifier. -/
theorem beck_chevalley_ex (s : Δ → Γ) (φ : Pred S (Γ × X)) :
    reidx s (ex φ) = ex (reidx (Prod.map s id) φ) := rfl

/-- Beck–Chevalley for `∀`: substitution commutes with the quantifier. -/
theorem beck_chevalley_all (s : Δ → Γ) (φ : Pred S (Γ × X)) :
    reidx s (all φ) = all (reidx (Prod.map s id) φ) := rfl

/-- Frobenius reciprocity for `∧`. -/
theorem frobenius_and (φ : Pred S (Γ × X)) (ψ : Pred S Γ) :
    ex (and φ (reidx Prod.fst ψ)) = and (ex φ) ψ :=
  entails_antisymm
    (fun _ _ _ ⟨x, a, b⟩ => ⟨⟨x, a⟩, b⟩)
    (fun _ _ _ ⟨⟨x, a⟩, b⟩ => ⟨x, a, b⟩)

/-- Frobenius reciprocity for the separating conjunction. -/
theorem frobenius_sep (φ : Pred S (Γ × X)) (ψ : Pred S Γ) :
    ex (sep φ (reidx Prod.fst ψ)) = sep (ex φ) ψ :=
  entails_antisymm
    (fun _ _ _ ⟨x, h₁, h₂, j, a, b⟩ => ⟨h₁, h₂, j, ⟨x, a⟩, b⟩)
    (fun _ _ _ ⟨h₁, h₂, j, ⟨x, a⟩, b⟩ => ⟨x, h₁, h₂, j, a, b⟩)

/-- Lawvere's characterisation of equality: `=_X` is the left adjoint to
reindexing along the diagonal, evaluated at `⊤`. -/
theorem lawvere_eq (A : Pred S (X × X)) :
    ((top : Pred S X) ⊩ reidx (fun x => (x, x)) A) ↔ (eqP X ⊩ A) := by
  constructor
  · intro H p n h e
    obtain ⟨x, y⟩ := p
    have e' : x = y := e
    subst e'
    exact H x n h True.intro
  · intro H x n h _
    exact H (x, x) n h rfl

/-- Leibniz substitution, derived from the Lawvere rule: equal points satisfy
the same predicates. -/
theorem eq_subst (φ : Pred S X) :
    and (eqP X) (reidx Prod.fst φ) ⊩ reidx Prod.snd φ := by
  intro p n h ⟨e, a⟩
  obtain ⟨x, y⟩ := p
  have e' : x = y := e
  subst e'
  exact a

end Pred

end Toy
