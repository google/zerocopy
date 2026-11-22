/-
A step-indexed BI algebra over an abstract separation algebra.

Toy model. Elements are `Nat`-indexed families of resource predicates that are
down-closed in the index ("uniform predicates"); the index plays the role of the
number of remaining computation steps. Nothing here depends on Mathlib.
-/
namespace Toy

/-- A separation algebra presented by the graph of its partially-defined multiplication:
`join a b c` reads "`c` is the (defined) combination of `a` and `b`". -/
structure SepAlg where
  M : Type
  join : M → M → M → Prop
  unit : M
  comm : ∀ {a b c : M}, join a b c → join b a c
  assoc : ∀ {a b c ab abc : M}, join a b ab → join ab c abc →
    ∃ bc, join b c bc ∧ join a bc abc
  unit_join : ∀ a : M, join unit a a
  unit_inv : ∀ {a b : M}, join unit a b → a = b

/-- Step-indexed propositions: families `Nat → M → Prop` down-closed in the index. -/
structure SProp (S : SepAlg) where
  holds : Nat → S.M → Prop
  down : ∀ {n m : Nat} {h : S.M}, m ≤ n → holds n h → holds m h

namespace SProp

variable {S : SepAlg}

theorem ext {φ ψ : SProp S} (h : ∀ n r, φ.holds n r ↔ ψ.holds n r) : φ = ψ := by
  cases φ with | mk f df => cases ψ with | mk g dg =>
  have : f = g := funext fun n => funext fun r => propext (h n r)
  subst this; rfl

/-- Entailment in the fibre. -/
def entails (φ ψ : SProp S) : Prop := ∀ n h, φ.holds n h → ψ.holds n h

@[inherit_doc] infix:25 " ⊑ " => entails

theorem entails_refl (φ : SProp S) : φ ⊑ φ := fun _ _ h => h

theorem entails_trans {φ ψ χ : SProp S} (h₁ : φ ⊑ ψ) (h₂ : ψ ⊑ χ) : φ ⊑ χ :=
  fun n h a => h₂ n h (h₁ n h a)

theorem entails_antisymm {φ ψ : SProp S} (h₁ : φ ⊑ ψ) (h₂ : ψ ⊑ φ) : φ = ψ :=
  ext fun n r => ⟨h₁ n r, h₂ n r⟩

/-! ### Heyting structure -/

def pure (P : Prop) : SProp S := ⟨fun _ _ => P, fun _ h => h⟩
def top : SProp S := pure True
def bot : SProp S := pure False

def and (φ ψ : SProp S) : SProp S :=
  ⟨fun n h => φ.holds n h ∧ ψ.holds n h, fun le H => ⟨φ.down le H.1, ψ.down le H.2⟩⟩

def or (φ ψ : SProp S) : SProp S :=
  ⟨fun n h => φ.holds n h ∨ ψ.holds n h,
   fun le H => H.elim (fun a => Or.inl (φ.down le a)) (fun b => Or.inr (ψ.down le b))⟩

/-- Implication quantifies over all smaller indices so that it stays down-closed. -/
def imp (φ ψ : SProp S) : SProp S :=
  ⟨fun n h => ∀ m, m ≤ n → φ.holds m h → ψ.holds m h,
   fun le H m hm => H m (Nat.le_trans hm le)⟩

def all {X : Type} (Φ : X → SProp S) : SProp S :=
  ⟨fun n h => ∀ x, (Φ x).holds n h, fun le H x => (Φ x).down le (H x)⟩

def ex {X : Type} (Φ : X → SProp S) : SProp S :=
  ⟨fun n h => ∃ x, (Φ x).holds n h, fun le H => H.elim fun x a => ⟨x, (Φ x).down le a⟩⟩

theorem top_intro (φ : SProp S) : φ ⊑ top := fun _ _ _ => True.intro
theorem bot_elim (φ : SProp S) : bot ⊑ φ := fun _ _ h => h.elim

theorem and_intro {φ ψ χ : SProp S} (h₁ : χ ⊑ φ) (h₂ : χ ⊑ ψ) : χ ⊑ and φ ψ :=
  fun n h a => ⟨h₁ n h a, h₂ n h a⟩
theorem and_elim_l (φ ψ : SProp S) : and φ ψ ⊑ φ := fun _ _ h => h.1
theorem and_elim_r (φ ψ : SProp S) : and φ ψ ⊑ ψ := fun _ _ h => h.2

theorem or_intro_l (φ ψ : SProp S) : φ ⊑ or φ ψ := fun _ _ h => Or.inl h
theorem or_intro_r (φ ψ : SProp S) : ψ ⊑ or φ ψ := fun _ _ h => Or.inr h
theorem or_elim {φ ψ χ : SProp S} (h₁ : φ ⊑ χ) (h₂ : ψ ⊑ χ) : or φ ψ ⊑ χ :=
  fun n h a => a.elim (h₁ n h) (h₂ n h)

/-- `∧ ⊣ ⇒`: the fibre is a Heyting algebra. -/
theorem imp_adj {φ ψ χ : SProp S} : (and φ ψ ⊑ χ) ↔ (φ ⊑ imp ψ χ) :=
  ⟨fun H _ h a m hm b => H m h ⟨φ.down hm a, b⟩,
   fun H n h a => H n h a.1 n (Nat.le_refl n) a.2⟩

/-! ### BI (separation) structure -/

def emp : SProp S := ⟨fun _ h => h = S.unit, fun _ h => h⟩

def sep (φ ψ : SProp S) : SProp S :=
  ⟨fun n h => ∃ h₁ h₂, S.join h₁ h₂ h ∧ φ.holds n h₁ ∧ ψ.holds n h₂,
   fun le H => match H with
     | ⟨h₁, h₂, j, a, b⟩ => ⟨h₁, h₂, j, φ.down le a, ψ.down le b⟩⟩

def wand (φ ψ : SProp S) : SProp S :=
  ⟨fun n h => ∀ m, m ≤ n → ∀ h₁ h', S.join h h₁ h' → φ.holds m h₁ → ψ.holds m h',
   fun le H m hm => H m (Nat.le_trans hm le)⟩

theorem sep_mono {φ φ' ψ ψ' : SProp S} (h₁ : φ ⊑ φ') (h₂ : ψ ⊑ ψ') : sep φ ψ ⊑ sep φ' ψ' :=
  fun n _ ⟨a, b, j, ha, hb⟩ => ⟨a, b, j, h₁ n a ha, h₂ n b hb⟩

theorem sep_comm (φ ψ : SProp S) : sep φ ψ ⊑ sep ψ φ :=
  fun _ _ ⟨a, b, j, ha, hb⟩ => ⟨b, a, S.comm j, hb, ha⟩

theorem sep_assoc (φ ψ χ : SProp S) : sep (sep φ ψ) χ ⊑ sep φ (sep ψ χ) :=
  fun _ _ ⟨_, c, j, ⟨a, b, jab, ha, hb⟩, hc⟩ =>
    match S.assoc jab j with
    | ⟨bc, jbc, ja⟩ => ⟨a, bc, ja, ha, b, c, jbc, hb, hc⟩

theorem emp_sep_elim (φ : SProp S) : sep emp φ ⊑ φ := by
  intro n h ⟨a, b, j, ha, hb⟩
  have ha' : a = S.unit := ha
  subst ha'
  have := S.unit_inv j
  subst this
  exact hb

theorem emp_sep_intro (φ : SProp S) : φ ⊑ sep emp φ :=
  fun _ h a => ⟨S.unit, h, S.unit_join h, rfl, a⟩

/-- `∗ ⊣ −∗`: together with the Heyting structure this makes each fibre a BI algebra. -/
theorem wand_adj {φ ψ χ : SProp S} : (sep φ ψ ⊑ χ) ↔ (φ ⊑ wand ψ χ) :=
  ⟨fun H _ h a m hm h₁ h' j b => H m h' ⟨h, h₁, j, φ.down hm a, b⟩,
   fun H n h ⟨h₁, h₂, j, a, b⟩ => H n h₁ a n (Nat.le_refl n) h₂ h j b⟩

/-! ### The later modality -/

/-- `▷φ` holds at index `n` when `φ` holds at every strictly smaller index. -/
def later (φ : SProp S) : SProp S :=
  ⟨fun n h => ∀ m, m < n → φ.holds m h, fun le H m hm => H m (Nat.lt_of_lt_of_le hm le)⟩

theorem later_intro (φ : SProp S) : φ ⊑ later φ :=
  fun _ _ a _ hm => φ.down (Nat.le_of_lt hm) a

theorem later_mono {φ ψ : SProp S} (h : φ ⊑ ψ) : later φ ⊑ later ψ :=
  fun _ r a m hm => h m r (a m hm)

theorem later_and (φ ψ : SProp S) : and (later φ) (later ψ) ⊑ later (and φ ψ) :=
  fun _ _ a m hm => ⟨a.1 m hm, a.2 m hm⟩

theorem later_sep (φ ψ : SProp S) : sep (later φ) (later ψ) ⊑ later (sep φ ψ) :=
  fun _ _ ⟨a, b, j, ha, hb⟩ m hm => ⟨a, b, j, ha m hm, hb m hm⟩

theorem later_wand (φ ψ : SProp S) : wand φ ψ ⊑ wand (later φ) (later ψ) :=
  fun _ _ H _ hm h₁ h' j a k hk =>
    H k (Nat.le_trans (Nat.le_of_lt hk) hm) h₁ h' j (a k hk)

theorem later_all {X : Type} (Φ : X → SProp S) :
    all (fun x => later (Φ x)) ⊑ later (all Φ) :=
  fun _ _ a m hm x => a x m hm

theorem ex_later {X : Type} (Φ : X → SProp S) :
    ex (fun x => later (Φ x)) ⊑ later (ex Φ) :=
  fun _ _ ⟨x, a⟩ m hm => ⟨x, a m hm⟩

/-- The converse of `ex_later` needs an inhabitant (index `0` knows nothing). -/
theorem later_ex_of_inhabited {X : Type} (x₀ : X) (Φ : X → SProp S) :
    later (ex Φ) ⊑ ex (fun x => later (Φ x)) := by
  intro n h a
  cases n with
  | zero => exact ⟨x₀, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ k =>
    obtain ⟨x, hx⟩ := a k (Nat.lt_succ_self k)
    exact ⟨x, fun m hm => (Φ x).down (Nat.le_of_lt_succ hm) hx⟩

/-- `▷` does not preserve `⊥`: at index `0` every later-proposition holds. -/
theorem later_bot_not_bot : ¬ (later (bot : SProp S) ⊑ bot) :=
  fun H => H 0 S.unit (fun m hm => absurd hm (Nat.not_lt_zero m))

/-- Löb induction, external form. -/
theorem loeb {φ : SProp S} (H : later φ ⊑ φ) : top ⊑ φ := by
  intro n h _
  have key : ∀ k, φ.holds k h := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih => exact H k h (fun m hm => ih m hm)
  exact key n

/-- Löb induction, internal form `(▷φ ⇒ φ) ⊢ φ`. -/
theorem loeb_internal (φ : SProp S) : imp (later φ) φ ⊑ φ := by
  intro n h H
  have key : ∀ m, m ≤ n → φ.holds m h := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro hm
      exact H m hm (fun k hk => ih k hk (Nat.le_trans (Nat.le_of_lt hk) hm))
  exact key n (Nat.le_refl n)

/-! ### The finite-step ultrametric and guarded fixed points -/

/-- `distLt n φ ψ`: the two families agree at every index `< n`
(distance at most `2⁻ⁿ` in the bisected ultrametric reading). -/
def distLt (n : Nat) (φ ψ : SProp S) : Prop := ∀ m, m < n → ∀ h, φ.holds m h ↔ ψ.holds m h

theorem distLt_zero (φ ψ : SProp S) : distLt 0 φ ψ :=
  fun m hm => absurd hm (Nat.not_lt_zero m)

theorem distLt_symm {n : Nat} {φ ψ : SProp S} (H : distLt n φ ψ) : distLt n ψ φ :=
  fun m hm h => (H m hm h).symm

theorem distLt_trans {n : Nat} {φ ψ χ : SProp S} (H₁ : distLt n φ ψ) (H₂ : distLt n ψ χ) :
    distLt n φ χ :=
  fun m hm h => (H₁ m hm h).trans (H₂ m hm h)

theorem distLt_mono {n k : Nat} {φ ψ : SProp S} (hk : k ≤ n) (H : distLt n φ ψ) :
    distLt k φ ψ :=
  fun m hm h => H m (Nat.lt_of_lt_of_le hm hk) h

theorem eq_of_forall_distLt {φ ψ : SProp S} (H : ∀ n, distLt n φ ψ) : φ = ψ :=
  ext fun n r => H (n + 1) n (Nat.lt_succ_self n) r

/-- A map is contractive when agreement below `n` gives agreement below `n + 1`. -/
def Contractive (F : SProp S → SProp S) : Prop :=
  ∀ n φ ψ, distLt n φ ψ → distLt (n + 1) (F φ) (F ψ)

/-- `▷` is contractive. -/
theorem later_contractive : Contractive (later : SProp S → SProp S) := by
  intro n φ ψ H m hm h
  constructor
  · intro a k hk
    exact (H k (Nat.lt_of_lt_of_le hk (Nat.le_of_lt_succ hm)) h).1 (a k hk)
  · intro a k hk
    exact (H k (Nat.lt_of_lt_of_le hk (Nat.le_of_lt_succ hm)) h).2 (a k hk)

/-- Guarded fixed points are unique. -/
theorem guarded_fixpoint_unique {F : SProp S → SProp S} (hF : Contractive F)
    {φ ψ : SProp S} (hφ : F φ = φ) (hψ : F ψ = ψ) : φ = ψ := by
  apply eq_of_forall_distLt
  intro n
  induction n with
  | zero => exact distLt_zero φ ψ
  | succ n ih =>
    have := hF n φ ψ ih
    rw [hφ, hψ] at this
    exact this

/-- Finite approximants `Fᵏ(⊤)`. -/
def iter (F : SProp S → SProp S) : Nat → SProp S
  | 0 => top
  | k + 1 => F (iter F k)

theorem iter_stable {F : SProp S → SProp S} (hF : Contractive F) :
    ∀ k j, distLt k (iter F k) (iter F (k + j)) := by
  intro k
  induction k with
  | zero => intro j; exact distLt_zero _ _
  | succ k ih =>
    intro j
    have h := hF k _ _ (ih j)
    have e : k + 1 + j = (k + j) + 1 := Nat.succ_add k j
    rw [e]
    exact h

/-- The diagonal of the approximants: the guarded fixed point. -/
def gfix (F : SProp S → SProp S) (hF : Contractive F) : SProp S :=
  ⟨fun n h => (iter F (n + 1)).holds n h, by
    intro n m h le H
    have H' : (iter F (n + 1)).holds m h := (iter F (n + 1)).down le H
    obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
    have e : m + j + 1 = m + 1 + j := by omega
    rw [e] at H'
    exact (iter_stable hF (m + 1) j m (Nat.lt_succ_self m) h).2 H'⟩

theorem gfix_approx {F : SProp S → SProp S} (hF : Contractive F) :
    ∀ n, distLt n (gfix F hF) (iter F n) := by
  intro n m hm h
  obtain ⟨j, rfl⟩ : ∃ j, n = m + 1 + j := ⟨n - (m + 1), by omega⟩
  exact iter_stable hF (m + 1) j m (Nat.lt_succ_self m) h

/-- Banach-style existence: `gfix F` is a fixed point of a contractive `F`. -/
theorem gfix_unfold {F : SProp S → SProp S} (hF : Contractive F) :
    F (gfix F hF) = gfix F hF := by
  apply eq_of_forall_distLt
  intro n
  cases n with
  | zero => exact distLt_zero _ _
  | succ n =>
    have h₁ : distLt (n + 1) (F (gfix F hF)) (iter F (n + 1)) :=
      hF n _ _ (gfix_approx hF n)
    exact distLt_trans h₁ (distLt_symm (gfix_approx hF (n + 1)))

end SProp

/-! ### A concrete separation algebra (non-vacuity) -/

/-- Natural numbers under addition: a counting resource. -/
def natAlg : SepAlg where
  M := Nat
  join a b c := a + b = c
  unit := 0
  comm := by intro a b c h; omega
  assoc := by intro a b c ab abc h₁ h₂; exact ⟨b + c, rfl, by omega⟩
  unit_join := by intro a; exact Nat.zero_add a
  unit_inv := by intro a b h; omega

/-- "The resource is exactly one unit." -/
def isOne : SProp natAlg := ⟨fun _ (h : Nat) => h = 1, fun _ h => h⟩

/-- In `natAlg` separating conjunction is not ordinary conjunction, so the BI
structure of the fibres is not the degenerate cartesian one. -/
theorem sep_ne_and : ¬ (SProp.and isOne isOne ⊑ SProp.sep isOne isOne) := by
  intro H
  obtain ⟨a, b, j, ha, hb⟩ := H 0 (1 : Nat) ⟨rfl, rfl⟩
  have key : ∀ x y : Nat, x = 1 → y = 1 → x + y = 1 → False := by
    intro x y h₁ h₂ h₃; omega
  exact key a b ha hb j

end Toy
