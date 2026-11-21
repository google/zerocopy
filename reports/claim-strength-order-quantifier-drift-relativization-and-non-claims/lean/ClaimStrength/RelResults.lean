import ClaimStrength.PrefixResults

/-!
# Relativized shapes: decision procedure, a concrete signature, completeness failures,
tightness, and non-vacuity

The concrete signature has base type `Nat`, four domain classes (`empty = ∅`, `zero = {0}`,
`zeroOne = {0, 1}`, `all = Nat`) with exact inclusion and overlap tables, and three premises
(`top`, `bot`, `atMostOne` = "every variable is at most 1") with an exact implication table.
-/

namespace Toy.ClaimStrength

variable {n : Nat} {K P : Type} {α : Type}

/-! ## Deciding the domain conditions -/

/-- Check a condition on the binders of each variable bound on both sides. -/
def pairAllB (c : Binder n K → Binder n K → Bool) (φ ψ : List (Binder n K)) : Bool :=
  (List.finRange n).all fun v =>
    match bOf φ v, bOf ψ v with
    | some b, some b' => c b b'
    | _, _ => true

theorem pairAllB_iff (c : Binder n K → Binder n K → Bool) (φ ψ : List (Binder n K)) :
    pairAllB c φ ψ = true ↔
      ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → c b b' = true := by
  simp only [pairAllB, List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro h v b b' hb hb'
    have := h v
    rw [hb, hb'] at this
    exact this
  · intro h v
    split
    · next b b' hb hb' => exact h v b b' hb hb'
    · rfl

theorem univDomains_iff_pairAllB (incl : K → K → Bool) (φ ψ : List (Binder n K)) :
    UnivDomainsContravariant incl φ ψ ↔
      pairAllB (fun b b' => !decide (b'.q = .all) || incl b'.dom b.dom) φ ψ = true := by
  rw [pairAllB_iff]
  refine forall_congr' fun v => forall_congr' fun b => forall_congr' fun b' => ?_
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  cases b'.q <;> simp

theorem exDomains_iff_pairAllB (incl : K → K → Bool) (φ ψ : List (Binder n K)) :
    ExDomainsCovariant incl φ ψ ↔
      pairAllB (fun b b' => !decide (b.q = .ex) || incl b.dom b'.dom) φ ψ = true := by
  rw [pairAllB_iff]
  refine forall_congr' fun v => forall_congr' fun b => forall_congr' fun b' => ?_
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  cases b.q <;> simp

theorem meet_iff_pairAllB (meets : K → K → Bool) (φ ψ : List (Binder n K)) :
    InstantiatedDomainsMeet meets φ ψ ↔
      pairAllB (fun b b' => !(decide (b.q = .all) && decide (b'.q = .ex)) ||
        meets b.dom b'.dom) φ ψ = true := by
  rw [pairAllB_iff]
  refine forall_congr' fun v => forall_congr' fun b => forall_congr' fun b' => ?_
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  cases b.q <;> cases b'.q <;> simp

/-- A Boolean implementation of the combined criterion. -/
def rcritB (incl meets : K → K → Bool) (impl : P → P → Bool) (φ ψ : Shape n K P) : Bool :=
  prefixCritB φ.pre ψ.pre &&
  pairAllB (fun b b' => !decide (b'.q = .all) || incl b'.dom b.dom) φ.pre ψ.pre &&
  pairAllB (fun b b' => !decide (b.q = .ex) || incl b.dom b'.dom) φ.pre ψ.pre &&
  pairAllB (fun b b' => !(decide (b.q = .all) && decide (b'.q = .ex)) || meets b.dom b'.dom)
    φ.pre ψ.pre &&
  impl ψ.prem φ.prem

/-- The combined criterion is decidable (given decidable relations). -/
theorem rcritB_iff (incl meets : K → K → Bool) (impl : P → P → Bool) (φ ψ : Shape n K P) :
    rcritB incl meets impl φ ψ = true ↔ RCrit incl meets impl φ ψ := by
  simp only [rcritB, Bool.and_eq_true, RCrit, PremiseContravariant, prefixCritB_iff,
    univDomains_iff_pairAllB, exDomains_iff_pairAllB, meet_iff_pairAllB, and_assoc]

/-! ## A concrete signature -/

/-- Domain classes over `Nat`. -/
inductive Cls
  | empty
  | zero
  | zeroOne
  | all
  deriving DecidableEq, Repr

/-- Interpretation of the domain classes. -/
def clsI : Cls → Nat → Prop
  | .empty, _ => False
  | .zero, a => a = 0
  | .zeroOne, a => a ≤ 1
  | .all, _ => True

/-- Exact inclusion table. -/
def clsIncl : Cls → Cls → Bool
  | .empty, _ => true
  | .zero, .zero => true
  | .zero, .zeroOne => true
  | .zero, .all => true
  | .zeroOne, .zeroOne => true
  | .zeroOne, .all => true
  | .all, .all => true
  | _, _ => false

/-- Exact overlap table. -/
def clsMeets : Cls → Cls → Bool
  | .empty, _ => false
  | _, .empty => false
  | _, _ => true

/-- Named premises. -/
inductive Prem
  | top
  | bot
  | atMostOne
  deriving DecidableEq, Repr

/-- Interpretation of the premises over assignments of `m + 1` variables. -/
def premJ (m : Nat) : Prem → (Fin (m + 1) → Nat) → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atMostOne, σ => ∀ v, σ v ≤ 1

/-- Exact implication table. -/
def premImpl : Prem → Prem → Bool
  | .bot, _ => true
  | _, .top => true
  | .atMostOne, .atMostOne => true
  | _, _ => false

theorem clsIncl_exact : InclExact clsI clsIncl := by
  intro k k'
  cases k <;> cases k' <;>
    simp only [clsIncl, clsI, Bool.false_eq_true, true_iff, false_iff] <;>
    first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | exact fun _ h => h.elim
    | exact fun a (h : a = 0) => by omega
    | exact fun h => h 0 rfl
    | exact fun h => h 0 (by omega)
    | exact fun h => h 0 trivial
    | exact fun h => absurd (h 1 (by omega)) (by omega)
    | exact fun h => absurd (h 1 trivial) (by omega)
    | exact fun h => absurd (h 2 trivial) (by omega)

theorem clsMeets_exact : MeetsExact clsI clsMeets := by
  intro k k'
  cases k <;> cases k' <;>
    simp only [clsMeets, clsI, Bool.false_eq_true, true_iff, false_iff] <;>
    first
    | exact ⟨0, rfl, rfl⟩
    | exact ⟨0, rfl, by omega⟩
    | exact ⟨0, rfl, trivial⟩
    | exact ⟨0, by omega, rfl⟩
    | exact ⟨0, by omega, by omega⟩
    | exact ⟨0, by omega, trivial⟩
    | exact ⟨0, trivial, rfl⟩
    | exact ⟨0, trivial, by omega⟩
    | exact ⟨0, trivial, trivial⟩
    | exact fun ⟨_, h, _⟩ => h
    | exact fun ⟨_, _, h⟩ => h

theorem premImpl_exact (m : Nat) : ImplExact (premJ m) premImpl := by
  intro p p'
  cases p <;> cases p' <;>
    simp only [premImpl, premJ, Bool.false_eq_true, true_iff, false_iff] <;>
    first
    | exact fun _ h => h
    | exact fun _ _ => trivial
    | exact fun _ h => h.elim
    | exact fun h => h (fun _ => 0) trivial
    | exact fun h => absurd (h (fun _ => 2) trivial 0) (by omega)
    | exact fun h => h (fun _ => 0) (fun _ => by omega)

theorem twoPoint_zeroOne : TwoPoint (clsI .zeroOne) := ⟨0, 1, by omega, by simp [clsI], by simp [clsI]⟩

theorem twoPoint_all : TwoPoint (clsI .all) := ⟨0, 1, by omega, trivial, trivial⟩

theorem not_twoPoint_empty : ¬ TwoPoint (clsI .empty) := fun ⟨_, _, _, h, _⟩ => h

theorem not_twoPoint_zero : ¬ TwoPoint (clsI .zero) := fun ⟨a, b, hab, ha, hb⟩ =>
  hab ((show a = 0 from ha).trans (show b = 0 from hb).symm)

/-- One-binder shapes evaluate by a single relativized quantifier. -/
theorem holds_single {I : K → α → Prop} {J : P → (Fin n → α) → Prop} (b : Binder n K) (p : P)
    (M : (Fin n → α) → Prop) (ρ : Fin n → α) :
    Holds I J ⟨[b], p⟩ M ρ ↔
      quantify b.q (I b.dom) (fun a => J p (upd ρ b.var a) → M (upd ρ b.var a)) := Iff.rfl

theorem fin1_eq_zero (v : Fin 1) : v = 0 := Fin.ext (by have := v.isLt; omega)

/-- Normal form for shapes: prenex (by construction), one premise (by construction), every
variable bound exactly once, and every binder's domain `k` satisfies `meets k k = true` (so
`ShapeNF` excludes every domain that the overlap relation flags as empty). -/
def ShapeNF (meets : K → K → Bool) (s : Shape n K P) : Prop :=
  WF s.pre ∧ ∀ b ∈ s.pre, meets b.dom b.dom = true

/-- Two-point classes of the concrete signature. -/
def clsTwo : Cls → Bool
  | .zeroOne => true
  | .all => true
  | _ => false

theorem twoPoint_of_clsTwo {k : Cls} (h : clsTwo k = true) : TwoPoint (clsI k) := by
  cases k
  · cases h
  · cases h
  · exact twoPoint_zeroOne
  · exact twoPoint_all

/-- Every existential binder has a two-point class (Boolean check). -/
def exTwoB {n : Nat} (pre : List (Binder n Cls)) : Bool :=
  pre.all (fun b => !decide (b.q = .ex) || clsTwo b.dom)

/-- Every universal binder has a two-point class (Boolean check). -/
def allTwoB {n : Nat} (pre : List (Binder n Cls)) : Bool :=
  pre.all (fun b => !decide (b.q = .all) || clsTwo b.dom)

theorem exTwo_of_B {n : Nat} {pre : List (Binder n Cls)} (h : exTwoB pre = true) :
    ∀ b ∈ pre, b.q = .ex → TwoPoint (clsI b.dom) := by
  intro b hb hq
  have := List.all_eq_true.1 h b hb
  simp [hq] at this
  exact twoPoint_of_clsTwo this

theorem allTwo_of_B {n : Nat} {pre : List (Binder n Cls)} (h : allTwoB pre = true) :
    ∀ b ∈ pre, b.q = .all → TwoPoint (clsI b.dom) := by
  intro b hb hq
  have := List.all_eq_true.1 h b hb
  simp [hq] at this
  exact twoPoint_of_clsTwo this

theorem implSound_premImpl (m : Nat) : ImplSound (premJ m) premImpl :=
  fun p p' h => (premImpl_exact m p p').1 h

theorem fin2_cases (v : Fin 2) : v = 0 ∨ v = 1 := by
  rcases v with ⟨_ | _ | k, hk⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

theorem nat_nonempty : Nonempty Nat := ⟨0⟩

/-! ## Definition examples -/

theorem holds_example_pos :
    Holds clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], Prem.top⟩ (fun σ => σ 0 ≤ 1) (fun _ => 5) := by
  rw [holds_single]; intro a ha _; show upd (fun _ => 5) 0 a 0 ≤ 1; rw [upd_same]; exact ha

theorem holds_example_neg :
    ¬ Holds clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], Prem.top⟩ (fun σ => σ 0 ≤ 1) (fun _ => 5) := by
  rw [holds_single]; intro h; have := h 2 trivial trivial; simp [upd] at this

theorem rEntails_example_pos :
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], Prem.top⟩ ⟨[⟨.all, 0, .zeroOne⟩], Prem.top⟩ :=
  fun _ _ h a _ hp => h a trivial hp

theorem rEntails_example_neg :
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], Prem.top⟩ ⟨[⟨.all, 0, .all⟩], Prem.top⟩ :=
  fun h => holds_example_neg (h _ _ holds_example_pos)

theorem rcrit_example_pos :
    RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩], Prem.top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], Prem.top⟩ :=
  (rcritB_iff _ _ _ _ _).1 (by decide)

theorem rcrit_example_neg :
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩], Prem.top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], Prem.top⟩ :=
  fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)

theorem univDomains_example_pos :
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))
      [⟨.all, 0, .zeroOne⟩] := (univDomains_iff_pairAllB _ _ _).2 (by decide)

theorem univDomains_example_neg :
    ¬ UnivDomainsContravariant clsIncl ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))
      [⟨.all, 0, .all⟩] := fun h => absurd ((univDomains_iff_pairAllB _ _ _).1 h) (by decide)

theorem exDomains_example_pos :
    ExDomainsCovariant clsIncl ([⟨.ex, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .zeroOne⟩] :=
  (exDomains_iff_pairAllB _ _ _).2 (by decide)

theorem exDomains_example_neg :
    ¬ ExDomainsCovariant clsIncl ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .zero⟩] :=
  fun h => absurd ((exDomains_iff_pairAllB _ _ _).1 h) (by decide)

theorem meet_example_pos :
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .zero⟩] := (meet_iff_pairAllB _ _ _).2 (by decide)

theorem meet_example_neg :
    ¬ InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .empty⟩] := fun h => absurd ((meet_iff_pairAllB _ _ _).1 h) (by decide)

theorem premise_example_pos :
    PremiseContravariant premImpl (⟨[], Prem.top⟩ : Shape 1 Cls Prem) ⟨[], Prem.atMostOne⟩ := rfl

theorem premise_example_neg :
    ¬ PremiseContravariant premImpl (⟨[], Prem.atMostOne⟩ : Shape 1 Cls Prem) ⟨[], Prem.top⟩ := by
  simp [PremiseContravariant, premImpl]

theorem inclSound_example_pos : InclSound clsI clsIncl :=
  fun k k' h => (clsIncl_exact k k').1 h

theorem inclSound_example_neg : ¬ InclSound clsI (fun _ _ => true) :=
  fun h => h .all .empty rfl 0 trivial

theorem meetsSound_example_pos : MeetsSound clsI clsMeets :=
  fun k k' h => (clsMeets_exact k k').1 h

theorem meetsSound_example_neg : ¬ MeetsSound clsI (fun _ _ => true) :=
  fun h => let ⟨_, ha, _⟩ := h .empty .empty rfl; ha

theorem implSound_example_pos : ImplSound (premJ 0) premImpl :=
  fun p p' h => (premImpl_exact 0 p p').1 h

theorem implSound_example_neg : ¬ ImplSound (premJ 0) (fun _ _ => true) :=
  fun h => h .top .bot rfl (fun _ => 0) trivial

theorem inclExact_example_pos : InclExact clsI clsIncl := clsIncl_exact

theorem inclExact_example_neg : ¬ InclExact clsI (fun k k' => decide (k = k')) := by
  intro h
  have := (h .zero .all).2 (fun _ _ => trivial)
  simp at this

theorem meetsExact_example_pos : MeetsExact clsI clsMeets := clsMeets_exact

theorem meetsExact_example_neg : ¬ MeetsExact clsI (fun _ _ => false) := by
  intro h
  have := (h .all .all).2 ⟨0, trivial, trivial⟩
  simp at this

theorem implExact_example_pos : ImplExact (premJ 0) premImpl := premImpl_exact 0

theorem implExact_example_neg : ¬ ImplExact (premJ 0) (fun _ _ => false) := by
  intro h
  have := (h .top .top).2 (fun _ hσ => hσ)
  simp at this

theorem twoPoint_example_pos : TwoPoint (clsI .zeroOne) := twoPoint_zeroOne

theorem twoPoint_example_neg : ¬ TwoPoint (clsI .zero) := not_twoPoint_zero

theorem shapeNF_example_pos :
    ShapeNF clsMeets (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) := by
  refine ⟨(wfB_iff _).1 (by decide), ?_⟩
  intro b hb; simp at hb; subst hb; rfl

theorem shapeNF_example_neg :
    ¬ ShapeNF clsMeets (⟨[⟨.ex, 0, .empty⟩], .top⟩ : Shape 1 Cls Prem) := by
  rintro ⟨-, h⟩
  exact absurd (h ⟨.ex, 0, .empty⟩ (by simp)) (by decide)

/-! ## The premise sits inside existential scopes -/

/-- A premise that constrains an existentially bound variable trivializes the shape: over `Nat`,
`∀x ∈ {0,1} ∃y ∈ Nat (x ≤ 1 ∧ y ≤ 1 → M)` holds for every matrix `M` (take `y := 2`), including
`M = False`. -/
theorem holds_premise_on_existential_trivial (M : (Fin 2 → Nat) → Prop) (ρ : Fin 2 → Nat) :
    Holds clsI (premJ 1) ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .all⟩], .atMostOne⟩ M ρ := by
  intro x _
  refine ⟨2, trivial, fun hp => ?_⟩
  have h2 : upd (upd ρ 0 x) 1 2 1 ≤ 1 := hp 1
  simp [upd] at h2

/-! ## Non-vacuity -/

/-- The shapes `∃y ∈ {0,1} ∀x ∈ Nat (⊤ → M)` and `∀x ∈ Nat ∃y ∈ {0,1} (x ≤ 1 ∧ y ≤ 1 → M)`
(variables `x = 0`, `y = 1`): the second has a reordered prefix and a stronger premise, which
restricts the universal variable `x` (on the existential variable `y` it is implied by the
domain `{0,1}`). -/
def nvφ : Shape 2 Cls Prem := ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .all⟩], .top⟩
/-- See `nvφ`. -/
def nvψ : Shape 2 Cls Prem := ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .zeroOne⟩], .atMostOne⟩
/-- `∃y ∈ {0} ∀x ∈ Nat (⊤ → M)`: an existential domain that grows in `nvψD`. -/
def nvφD : Shape 2 Cls Prem := ⟨[⟨.ex, 1, .zero⟩, ⟨.all, 0, .all⟩], .top⟩
/-- `∀x ∈ {0,1} ∃y ∈ {0,1} (⊤ → M)`: reordered prefix, shrunk universal domain, grown existential
domain. -/
def nvψD : Shape 2 Cls Prem := ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩], .top⟩
/-- `∀x ∈ {0,1} ∃y ∈ Nat (⊤ → M)`: the target used for completeness. -/
def nvψTop : Shape 2 Cls Prem := ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .all⟩], .top⟩

/-- Non-vacuity of `rcrit_sound`: every hypothesis holds for `nvφ`, `nvψ`; moreover the
entailment is not degenerate: `nvφ` holds for the matrix `True` and `nvψ` fails for `False`. -/
theorem rcrit_sound_nonvacuous :
    WF nvφ.pre ∧ WF nvψ.pre ∧ InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧
    ImplSound (premJ 1) premImpl ∧ RCrit clsIncl clsMeets premImpl nvφ nvψ ∧
    Holds clsI (premJ 1) nvφ (fun _ => True) (fun _ => 0) ∧
    ¬ Holds clsI (premJ 1) nvψ (fun _ => False) (fun _ => 0) := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 1, (rcritB_iff _ _ _ _ _).1 (by decide),
    ⟨0, by simp [clsI], fun _ _ _ => trivial⟩, fun h => ?_⟩
  obtain ⟨y, hy, hm⟩ := h 0 trivial
  apply hm
  intro v
  rcases fin2_cases v with rfl | rfl
  · simp [upd]
  · simp only [upd]; simpa [clsI] using hy

/-- A second non-vacuity witness for `rcrit_sound`, exercising domain variance: `nvφD`, `nvψD`
satisfy every hypothesis, `nvφD` holds for `True`, and `nvψD` fails for `False`. -/
theorem rcrit_sound_nonvacuous_domains :
    WF nvφD.pre ∧ WF nvψD.pre ∧ InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧
    ImplSound (premJ 1) premImpl ∧ RCrit clsIncl clsMeets premImpl nvφD nvψD ∧
    Holds clsI (premJ 1) nvφD (fun _ => True) (fun _ => 0) ∧
    ¬ Holds clsI (premJ 1) nvψD (fun _ => False) (fun _ => 0) := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 1, (rcritB_iff _ _ _ _ _).1 (by decide),
    ⟨0, rfl, fun _ _ _ => trivial⟩, fun h => ?_⟩
  obtain ⟨_, _, hm⟩ := h 0 (by simp [clsI])
  exact hm trivial

/-- Non-vacuity of `rcrit_complete_polarized_two_point_premise_free` and of
`nonempty_domains_of_rEntails`: every hypothesis of both holds for `nvφ`, `nvψTop` (the entailment
is obtained from soundness), and `nvψTop` fails for `False`. -/
theorem rcrit_complete_nonvacuous :
    (bvars nvφ.pre).Nodup ∧ (bvars nvψTop.pre).Nodup ∧ InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧
    ImplExact (premJ 1) premImpl ∧ Nonempty Nat ∧
    (∀ b ∈ nvφ.pre, b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ nvψTop.pre, b.q = .all → TwoPoint (clsI b.dom)) ∧ (∀ σ, premJ 1 nvφ.prem σ) ∧
    (∀ σ, premJ 1 nvψTop.prem σ) ∧ REntails clsI (premJ 1) nvφ nvψTop ∧
    ¬ Holds clsI (premJ 1) nvψTop (fun _ => False) (fun _ => 0) := by
  have hwφ : WF nvφ.pre := (wfB_iff _).1 (by decide)
  have hwψ : WF nvψTop.pre := (wfB_iff _).1 (by decide)
  refine ⟨hwφ.1, hwψ.1, clsIncl_exact, clsMeets_exact, premImpl_exact 1, nat_nonempty,
    exTwo_of_B (by decide), allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial, ?_,
    fun h => ?_⟩
  · exact rcrit_sound hwφ hwψ inclSound_example_pos meetsSound_example_pos
      (implSound_premImpl 1) ((rcritB_iff _ _ _ _ _).1 (by decide))
  · obtain ⟨_, _, hm⟩ := h 0 (by simp [clsI])
    exact hm trivial

/-! ## Completeness: tightness of each hypothesis, and failures outside the fragment

Each theorem below states that all hypotheses of
`rcrit_complete_polarized_two_point_premise_free` except the named one hold (over `Nat`, with
the exact tables `clsIncl`, `clsMeets`, `premImpl` unless the named hypothesis is an exactness
hypothesis), that the entailment holds, and that the criterion fails. -/

/-- Tightness of `h2φ` (witness class: one variable over `Nat`, an empty existential domain in
`φ`): `∃x ∈ ∅` is unsatisfiable, so it entails `∀x ∈ {0,1}`; the criterion fails (part (i)). -/
theorem rcrit_incomplete_empty_domain :
    (bvars ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    ¬ (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .empty⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, fun h => not_twoPoint_empty (h ⟨.ex, 0, .empty⟩ (by simp) rfl),
    allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h
  rw [holds_single] at h
  obtain ⟨a, ha, _⟩ := h
  exact (ha : False).elim

/-- Tightness of `h2φ` with a nonempty existential domain (witness class: two variables over
`Nat`, a singleton existential domain in `φ`): `∀u ∈ {0,1} ∃v ∈ {0} M ⊨ ∃v ∈ {0,1} ∀u ∈ {0,1} M`,
and the criterion fails (part (ii)). -/
theorem rcrit_incomplete_singleton_existential :
    (bvars ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩] : List (Binder 2 Cls))).Nodup ∧
    (bvars ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩] : List (Binder 2 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 1) premImpl ∧
    Nonempty Nat ∧
    ¬ (∀ b ∈ ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩] : List (Binder 2 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩] : List (Binder 2 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 1 .top σ) ∧ (∀ σ, premJ 1 .top σ) ∧
    REntails clsI (premJ 1) ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩], .top⟩
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zero⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zeroOne⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 1, nat_nonempty, fun h => not_twoPoint_zero (h ⟨.ex, 1, .zero⟩ (by simp) rfl),
    allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h
  refine ⟨0, by simp [clsI], fun a ha _ => ?_⟩
  obtain ⟨v, hv, hm⟩ := h a ha
  have hv0 : v = 0 := hv
  subst hv0
  rw [upd_comm ρ (by decide : (1 : Fin 2) ≠ 0) 0 a]
  exact hm trivial

/-- Tightness of `h2ψ` (witness class: one variable over `Nat`, an empty universal domain in
`ψ`): `∀x ∈ ∅` is valid, so anything entails it; the criterion fails (part (i)). -/
theorem rcrit_incomplete_empty_universal_domain :
    (bvars ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .empty⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .empty⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide),
    fun h => not_twoPoint_empty (h ⟨.all, 0, .empty⟩ (by simp) rfl), fun _ => trivial, fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ _ b hb
  exact (hb : False).elim

/-- Tightness of `h2ψ` with a nonempty universal domain (witness class: two variables over `Nat`,
a singleton universal domain in `ψ`): `∀u ∈ {0,1} ∃v ∈ {0,1} M ⊨ ∃v ∈ {0,1} ∀u ∈ {0} M`, and the
criterion fails (part (ii)). -/
theorem rcrit_incomplete_singleton_universal :
    (bvars ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls))).Nodup ∧
    (bvars ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩] : List (Binder 2 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 1) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    ¬ (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩] : List (Binder 2 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 1 .top σ) ∧ (∀ σ, premJ 1 .top σ) ∧
    REntails clsI (premJ 1) ⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩], .top⟩
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩, ⟨.ex, 1, .zeroOne⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.ex, 1, .zeroOne⟩, ⟨.all, 0, .zero⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 1, nat_nonempty, exTwo_of_B (by decide),
    fun h => not_twoPoint_zero (h ⟨.all, 0, .zero⟩ (by simp) rfl),
    fun _ => trivial, fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h
  obtain ⟨v, hv, hm⟩ := h 0 (by simp [clsI])
  refine ⟨v, hv, fun a ha _ => ?_⟩
  have ha0 : a = 0 := ha
  subst ha0
  rw [upd_comm ρ (by decide : (1 : Fin 2) ≠ 0) v 0]
  exact hm trivial

/-- On a singleton domain `∃` and `∀` coincide (one variable over `Nat`): `∃x ∈ {0} ⊨ ∀x ∈ {0}`
and the criterion fails (part (i)). This instance violates both `h2φ` and `h2ψ`; single-violation
witnesses are `rcrit_incomplete_singleton_existential` and
`rcrit_incomplete_singleton_universal`. -/
theorem rcrit_incomplete_singleton_domain :
    (bvars ([⟨.ex, 0, .zero⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    ¬ TwoPoint (clsI .zero) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zero⟩], .top⟩ ⟨[⟨.all, 0, .zero⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zero⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, not_twoPoint_zero, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h b hb
  rw [holds_single] at h
  obtain ⟨a, ha, hm⟩ := h
  have e : a = b := (show a = 0 from ha).trans (show b = 0 from hb).symm
  subst e
  exact hm

/-- The normal form does not restore completeness: the singleton-domain failure is in normal
form on both sides. -/
theorem rcrit_incomplete_in_normal_form :
    ShapeNF clsMeets (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ∧
    ShapeNF clsMeets (⟨[⟨.all, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zero⟩], .top⟩ ⟨[⟨.all, 0, .zero⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zero⟩], .top⟩ := by
  refine ⟨shapeNF_example_pos, ⟨(wfB_iff _).1 (by decide), ?_⟩,
    rcrit_incomplete_singleton_domain.2.2.2.2.2.2.1,
    rcrit_incomplete_singleton_domain.2.2.2.2.2.2.2⟩
  intro b hb; simp at hb; subst hb; rfl

/-- Tightness of `hpφ` (witness class: one variable over `Nat`, a premise of `φ` restricting its
universal variable): `∀x ∈ Nat (x ≤ 1 → M)` entails `∀x ∈ {0,1} (⊤ → M)`, but the premise part
of the criterion fails. -/
theorem rcrit_incomplete_premise_as_domain :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ σ, premJ 0 .atMostOne σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩], .atMostOne⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun h => absurd (h (fun _ => 2) 0) (by decide), fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h b hb _
  refine h b trivial (fun v => ?_)
  rw [fin1_eq_zero v, upd_same]
  exact hb

/-- Tightness of `hpφ` with an existential binder (witness class: one variable over `Nat`, a
premise of `φ` that is implied by the existential domain): `∃x ∈ {0,1} (x ≤ 1 → M)` entails
`∃x ∈ {0,1} (⊤ → M)`, but the premise part of the criterion fails. -/
theorem rcrit_incomplete_redundant_existential_premise :
    (bvars ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ σ, premJ 0 .atMostOne σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zeroOne⟩], .atMostOne⟩ ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .zeroOne⟩], .atMostOne⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun h => absurd (h (fun _ => 2) 0) (by decide), fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h
  obtain ⟨a, ha, hm⟩ := h
  refine ⟨a, ha, fun _ => hm (fun v => ?_)⟩
  rw [fin1_eq_zero v, upd_same]
  exact ha

/-- Tightness of `hpψ` (witness class: one variable over `Nat`, a premise of `ψ` restricting its
universal variable): `∀x ∈ {0,1} (⊤ → M)` entails `∀x ∈ Nat (x ≤ 1 → M)`, but the domain part of
the criterion fails. -/
theorem rcrit_incomplete_target_premise_as_domain :
    (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ ¬ (∀ σ, premJ 0 .atMostOne σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun _ => trivial, fun h => absurd (h (fun _ => 2) 0) (by decide), ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h b _ hp
  have hb : b ≤ 1 := by have := hp 0; rwa [upd_same] at this
  exact h b hb trivial

/-- Tightness of `hpψ` with an unsatisfiable premise (witness class: one variable over `Nat`,
`ψ.prem = ⊥`): `∀x ∈ Nat (⊥ → M)` is valid, so `∃x ∈ Nat (⊤ → M)` entails it, but part (i) of the
criterion fails. Here `φ` plays no role: every shape entails `ψ`. -/
theorem rcrit_incomplete_false_target_premise :
    (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ ¬ (∀ σ, premJ 0 .bot σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .bot⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .bot⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun _ => trivial, fun h => h (fun _ => 0), ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ _ b _ hbot
  exact (hbot : False).elim

/-- Tightness of `hpψ` with a premise on an existential variable of `ψ` (witness class: two
variables over `Nat`): `∀x ∈ Nat ∃y ∈ Nat (x ≤ 1 ∧ y ≤ 1 → M)` is valid (take `y := 2`), so
`∃x ∈ Nat ∃y ∈ Nat (⊤ → M)` entails it, but part (i) of the criterion fails. -/
theorem rcrit_incomplete_target_premise_on_existential :
    (bvars ([⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))).Nodup ∧
    (bvars ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 1) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 1 .top σ) ∧ ¬ (∀ σ, premJ 1 .atMostOne σ) ∧
    REntails clsI (premJ 1) ⟨[⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩
      ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .atMostOne⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .atMostOne⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 1, nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun _ => trivial, fun h => absurd (h (fun _ => 2) 0) (by decide), ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ _ x _
  refine ⟨2, trivial, fun hp => ?_⟩
  have h2 : upd (upd ρ 0 x) 1 2 1 ≤ 1 := hp 1
  simp [upd] at h2

/-- Tightness of `hI` (witness class: one variable over `Nat`, the sound but inexact inclusion
relation "equal classes"): the entailment `∀x ∈ Nat ⊨ ∀x ∈ {0,1}` holds but the criterion over
that relation fails. -/
theorem rcrit_incomplete_inexact_incl :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))).Nodup ∧
    InclSound clsI (fun k k' => decide (k = k')) ∧ ¬ InclExact clsI (fun k k' => decide (k = k')) ∧
    MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧ Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ RCrit (fun k k' => decide (k = k')) clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ := by
  refine ⟨by decide, by decide, fun k k' h a ha => ?_,
    inclExact_example_neg, clsMeets_exact, premImpl_exact 0, nat_nonempty,
    exTwo_of_B (by decide), allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial,
    rEntails_example_pos, fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  have : k = k' := of_decide_eq_true h
  subst this; exact ha

/-- Tightness of `hM` (witness class: one variable over `Nat`, the sound but inexact overlap
relation "never"): `∀x ∈ Nat ⊨ ∃x ∈ Nat` holds but the criterion over that relation fails. -/
theorem rcrit_incomplete_inexact_meets :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧
    MeetsSound clsI (fun _ _ => false) ∧ ¬ MeetsExact clsI (fun _ _ => false) ∧
    ImplExact (premJ 0) premImpl ∧ Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.ex, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl (fun _ _ => false) premImpl
      (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .all⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact,
    fun _ _ h => absurd h Bool.false_ne_true, meetsExact_example_neg, premImpl_exact 0,
    nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide), fun _ => trivial,
    fun _ => trivial, ?_, fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h
  exact ⟨0, trivial, h 0 trivial⟩

/-- Tightness of `hJ` (witness class: one variable over `Nat`, the sound but inexact premise
relation "never"): `∀x ∈ Nat ⊨ ∀x ∈ Nat` holds but the criterion over that relation fails. -/
theorem rcrit_incomplete_inexact_impl :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧
    ImplSound (premJ 0) (fun _ _ => false) ∧ ¬ ImplExact (premJ 0) (fun _ _ => false) ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets (fun _ _ => false)
      (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ :=
  ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    fun _ _ h => absurd h Bool.false_ne_true, implExact_example_neg, nat_nonempty,
    exTwo_of_B (by decide), allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial,
    fun _ _ h => h, fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩

/-- Tightness of `hφ` (witness class: one variable over `Nat`, a repeated binder in `φ`):
`∃x ∀x` (which means `∀x`) entails `∀x`, but the criterion reads the first binder. -/
theorem rcrit_incomplete_not_wf :
    ¬ (bvars ([⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex →
      TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨by decide, by decide,
    clsIncl_exact, clsMeets_exact, premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide),
    allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h b _
  obtain ⟨a, _, ha⟩ := h
  have h2 : premJ 0 Prem.top (upd (upd ρ 0 a) 0 b) → M (upd (upd ρ 0 a) 0 b) := ha b trivial
  have e : upd (upd ρ 0 a) 0 b = upd ρ 0 b := by funext z; simp only [upd]; split <;> rfl
  rw [e] at h2
  exact h2

/-- Tightness of `hψ` (witness class: one variable over `Nat`, a repeated binder in `ψ`):
`∃x ⊨ ∀x ∃x` (which means `∃x`), but the criterion reads the first binder. -/
theorem rcrit_incomplete_not_wf_target :
    (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    ¬ (bvars ([⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all →
      TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ := by
  refine ⟨by decide, by decide,
    clsIncl_exact, clsMeets_exact, premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide),
    allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial, ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  intro M ρ h b _
  obtain ⟨a, _, ha⟩ := h
  refine ⟨a, trivial, ?_⟩
  have e : upd (upd ρ 0 b) 0 a = upd ρ 0 a := by funext z; simp only [upd]; split <;> rfl
  show premJ 0 Prem.top (upd (upd ρ 0 b) 0 a) → M (upd (upd ρ 0 b) 0 a)
  rw [e]
  exact ha

/-- The trivial class interpretation over the empty type. -/
def emptyI : Unit → Empty → Prop := fun _ _ => True
/-- The trivial premise interpretation over the empty type. -/
def emptyJ : Unit → (Fin 1 → Empty) → Prop := fun _ _ => True
/-- `∀x` over the empty type. -/
def emptyφ : Shape 1 Unit Unit := ⟨[⟨.all, 0, ()⟩], ()⟩
/-- `∃x` over the empty type. -/
def emptyψ : Shape 1 Unit Unit := ⟨[⟨.ex, 0, ()⟩], ()⟩

/-- Tightness of `hα : Nonempty α` (witness class: the empty base type, one variable): with the
exact relations over `Empty` (every class includes every class, no two classes overlap, every
premise implies every premise), `∀x ⊨ ∃x` holds vacuously but the overlap part of the criterion
fails. -/
theorem rcrit_complete_hα_tight :
    (bvars emptyφ.pre).Nodup ∧ (bvars emptyψ.pre).Nodup ∧ InclExact emptyI (fun _ _ => true) ∧
    MeetsExact emptyI (fun _ _ => false) ∧ ImplExact emptyJ (fun _ _ => true) ∧
    ¬ Nonempty Empty ∧
    (∀ b ∈ emptyφ.pre, b.q = .ex → TwoPoint (emptyI b.dom)) ∧
    (∀ b ∈ emptyψ.pre, b.q = .all → TwoPoint (emptyI b.dom)) ∧
    (∀ σ, emptyJ emptyφ.prem σ) ∧ (∀ σ, emptyJ emptyψ.prem σ) ∧
    REntails emptyI emptyJ emptyφ emptyψ ∧
    ¬ RCrit (fun _ _ => true) (fun _ _ => false) (fun _ _ => true) emptyφ emptyψ := by
  refine ⟨by decide, by decide,
    fun _ _ => ⟨fun _ a => (nomatch a), fun _ => rfl⟩,
    fun _ _ => ⟨fun h => absurd h Bool.false_ne_true, fun ⟨a, _⟩ => (nomatch a)⟩,
    fun _ _ => ⟨fun _ σ => (nomatch σ 0), fun _ => rfl⟩, fun ⟨a⟩ => (nomatch a), ?_, ?_,
    fun _ => trivial, fun _ => trivial, rEntails_of_isEmpty (fun a => (nomatch a)) _ _,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  · intro b hb hq; simp [emptyφ] at hb; subst hb; cases hq
  · intro b hb hq; simp [emptyψ] at hb; subst hb; cases hq

/-- Tightness of the entailment hypothesis `h` in completeness (witness class: one variable over
`Nat`): every other hypothesis holds, the entailment and the criterion both fail. -/
theorem rcrit_complete_hE_tight :
    (bvars ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧ (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨by decide, by decide, clsIncl_exact, clsMeets_exact,
    premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun _ => trivial, fun _ => trivial, fun h => ?_,
    fun h => absurd ((rcritB_iff _ _ _ _ _).2 h) (by decide)⟩
  have := h (fun σ => σ 0 = 0) (fun _ => 0) ⟨0, trivial, fun _ => by simp [upd]⟩
  have := this 1 trivial trivial
  simp [upd] at this

/-- Non-vacuity of `rcrit_complete_polarized_two_point_premise_free` for a shape that leaves a
variable unbound (witness class: one variable over `Nat`, `φ = ∀x ∈ Nat`, `ψ` the empty prefix
with `x` free): every hypothesis holds although `ψ` is not well formed; the entailment and the
criterion hold. -/
theorem rcrit_complete_nonvacuous_free_variable :
    (bvars ([⟨.all, 0, .all⟩] : List (Binder 1 Cls))).Nodup ∧
    (bvars ([] : List (Binder 1 Cls))).Nodup ∧ ¬ WF ([] : List (Binder 1 Cls)) ∧
    InclExact clsI clsIncl ∧ MeetsExact clsI clsMeets ∧ ImplExact (premJ 0) premImpl ∧
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧ (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .top⟩ ⟨[], .top⟩ ∧
    RCrit clsIncl clsMeets premImpl (⟨[⟨.all, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[], .top⟩ := by
  refine ⟨by decide, by decide, fun h => absurd ((wfB_iff _).2 h) (by decide), clsIncl_exact,
    clsMeets_exact, premImpl_exact 0, nat_nonempty, exTwo_of_B (by decide),
    allTwo_of_B (by decide), fun _ => trivial, fun _ => trivial, ?_,
    (rcritB_iff _ _ _ _ _).1 (by decide)⟩
  intro M ρ h _
  have := h (ρ 0) trivial trivial
  rwa [upd_self] at this

/-! ## Nonemptiness of the domains: tightness of each hypothesis

Each theorem below states that all hypotheses of `nonempty_domains_of_rEntails` except the named
one hold and that its conclusion fails (some domain of `φ` or `ψ` is empty). -/

/-- Tightness of `hα` in `nonempty_domains_of_rEntails` (witness class: the empty base type, one
variable, `φ = ∀x`, `ψ = ∃x`): the entailment holds vacuously and the domains are empty. -/
theorem nonempty_domains_hα_tight :
    ¬ Nonempty Empty ∧
    (∀ b ∈ emptyφ.pre, b.q = .ex → TwoPoint (emptyI b.dom)) ∧
    (∀ b ∈ emptyψ.pre, b.q = .all → TwoPoint (emptyI b.dom)) ∧
    (∀ σ, emptyJ emptyψ.prem σ) ∧ REntails emptyI emptyJ emptyφ emptyψ ∧
    ¬ ((∀ b ∈ emptyφ.pre, ∃ a, emptyI b.dom a) ∧ (∀ b ∈ emptyψ.pre, ∃ a, emptyI b.dom a)) := by
  refine ⟨fun ⟨a⟩ => (nomatch a), ?_, ?_, fun _ => trivial,
    rEntails_of_isEmpty (fun a => (nomatch a)) _ _, fun h => ?_⟩
  · intro b hb hq; simp [emptyφ] at hb; subst hb; cases hq
  · intro b hb hq; simp [emptyψ] at hb; subst hb; cases hq
  · obtain ⟨a, _⟩ := h.1 ⟨.all, 0, ()⟩ (by simp [emptyφ])
    exact nomatch a

/-- Tightness of `h2φ` in `nonempty_domains_of_rEntails` (witness class: one variable over `Nat`,
`φ = ∃x ∈ ∅`, `ψ = ∀x ∈ {0,1}`): `φ` is unsatisfiable, so the entailment holds, and the domain of
`φ` is empty. -/
theorem nonempty_domains_h2φ_tight :
    Nonempty Nat ∧
    ¬ (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ ((∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a)) := by
  refine ⟨nat_nonempty, fun h => not_twoPoint_empty (h ⟨.ex, 0, .empty⟩ (by simp) rfl),
    allTwo_of_B (by decide), fun _ => trivial, ?_, fun h => ?_⟩
  · intro M ρ h
    rw [holds_single] at h
    obtain ⟨a, ha, _⟩ := h
    exact (ha : False).elim
  · obtain ⟨a, ha⟩ := h.1 ⟨.ex, 0, .empty⟩ (by simp)
    exact (ha : False).elim

/-- Tightness of `h2ψ` in `nonempty_domains_of_rEntails` (witness class: one variable over `Nat`,
`φ = ∃x ∈ {0,1}`, `ψ = ∀x ∈ ∅`): `ψ` is valid, so the entailment holds, and the domain of `ψ` is
empty. -/
theorem nonempty_domains_h2ψ_tight :
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .empty⟩], .top⟩ ∧
    ¬ ((∀ b ∈ ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a)) := by
  refine ⟨nat_nonempty, exTwo_of_B (by decide),
    fun h => not_twoPoint_empty (h ⟨.all, 0, .empty⟩ (by simp) rfl), fun _ => trivial, ?_,
    fun h => ?_⟩
  · intro M ρ _ b hb
    exact (hb : False).elim
  · obtain ⟨a, ha⟩ := h.2 ⟨.all, 0, .empty⟩ (by simp)
    exact (ha : False).elim

/-- Tightness of `hpψ` in `nonempty_domains_of_rEntails` (witness class: one variable over `Nat`,
`φ = ∀x ∈ ∅ (⊤ → M)`, `ψ = ∀x ∈ Nat (⊥ → M)`): both shapes are valid, so the entailment holds,
and the domain of `φ` is empty. -/
theorem nonempty_domains_hpψ_tight :
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    ¬ (∀ σ, premJ 0 .bot σ) ∧
    REntails clsI (premJ 0) ⟨[⟨.all, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .bot⟩ ∧
    ¬ ((∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a)) := by
  refine ⟨nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide),
    fun h => h (fun _ => 0), ?_, fun h => ?_⟩
  · intro M ρ _ b _ hbot
    exact (hbot : False).elim
  · obtain ⟨a, ha⟩ := h.1 ⟨.all, 0, .empty⟩ (by simp)
    exact (ha : False).elim

/-- Tightness of the entailment hypothesis `h` in `nonempty_domains_of_rEntails` (witness class:
one variable over `Nat`, `φ = ∀x ∈ ∅`, `ψ = ∀x ∈ {0,1}`): the entailment fails (for the matrix
`False`) and the domain of `φ` is empty. -/
theorem nonempty_domains_hE_tight :
    Nonempty Nat ∧
    (∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), b.q = .ex → TwoPoint (clsI b.dom)) ∧
    (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), b.q = .all → TwoPoint (clsI b.dom)) ∧
    (∀ σ, premJ 0 .top σ) ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .empty⟩], .top⟩ ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ∧
    ¬ ((∀ b ∈ ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
      (∀ b ∈ ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a)) := by
  refine ⟨nat_nonempty, exTwo_of_B (by decide), allTwo_of_B (by decide), fun _ => trivial,
    fun h => ?_, fun h => ?_⟩
  · exact h (fun _ => False) (fun _ => 0) (fun _ hb => (hb : False).elim) 0 (by simp [clsI])
      trivial
  · obtain ⟨a, ha⟩ := h.1 ⟨.all, 0, .empty⟩ (by simp)
    exact (ha : False).elim

/-! ## Soundness: tightness of each hypothesis

Each theorem below states that all hypotheses of `rcrit_sound` except the named one hold (over
`Nat`, with the sound tables `clsIncl`, `clsMeets`, `premImpl` unless the named hypothesis is a
soundness hypothesis), and that the entailment fails. -/

/-- Tightness of `hψ`, duplicate half (witness class: one variable over `Nat`, `ψ = ∃x ∀x`). -/
theorem rcrit_sound_hψ_tight :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧
    ¬ WF ([⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl
      (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.ex, 0, .all⟩, ⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), fun h => absurd ((wfB_iff _).2 h) (by decide),
    inclSound_example_pos, meetsSound_example_pos, implSound_premImpl 0,
    (rcritB_iff _ _ _ _ _).1 (by decide), fun h => ?_⟩
  have := h (fun σ => σ 0 = 0) (fun _ => 0) ⟨0, trivial, fun _ => by simp [upd]⟩
  obtain ⟨a, _, ha⟩ := this
  have := ha 1 trivial trivial
  simp [upd] at this

/-- Tightness of `hψ`, covering half (witness class: one variable over `Nat`, `ψ` the empty
prefix with `x` free). -/
theorem rcrit_sound_hψ_tight_missing :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧ ¬ WF ([] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), fun h => absurd ((wfB_iff _).2 h) (by decide),
    inclSound_example_pos, meetsSound_example_pos, implSound_premImpl 0,
    (rcritB_iff _ _ _ _ _).1 (by decide), fun h => ?_⟩
  have := h (fun σ => σ 0 = 0) (fun _ => 1) ⟨0, trivial, fun _ => by simp [upd]⟩ trivial
  simp at this

/-- Tightness of `hφ`, duplicate half (witness class: one variable over `Nat`, `φ = ∀x ∃x`). -/
theorem rcrit_sound_hφ_tight :
    ¬ WF ([⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧
    WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl
      (⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩, ⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨fun h => absurd ((wfB_iff _).2 h) (by decide), (wfB_iff _).1 (by decide),
    inclSound_example_pos, meetsSound_example_pos, implSound_premImpl 0,
    (rcritB_iff _ _ _ _ _).1 (by decide), fun h => ?_⟩
  have := h (fun σ => σ 0 = 0) (fun _ => 0) (fun a _ => ⟨0, trivial, fun _ => by simp [upd]⟩)
  have := this 1 trivial trivial
  simp [upd] at this

/-- Tightness of `hφ`, covering half (witness class: one variable over `Nat`, `φ` the empty
prefix with `x` free, `ψ = ∃x ∈ {0}`). Unlike the unrelativized criterion, where a free variable
of `φ` is harmless, here the environment's value need not lie in the domain. -/
theorem rcrit_sound_hφ_tight_missing :
    ¬ WF ([] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .zero⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl clsMeets premImpl (⟨[], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .zero⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[], .top⟩ ⟨[⟨.ex, 0, .zero⟩], .top⟩ := by
  refine ⟨fun h => absurd ((wfB_iff _).2 h) (by decide), (wfB_iff _).1 (by decide),
    inclSound_example_pos, meetsSound_example_pos, implSound_premImpl 0,
    (rcritB_iff _ _ _ _ _).1 (by decide), fun h => ?_⟩
  obtain ⟨a, ha, hm⟩ := h (fun σ => σ 0 = 1) (fun _ => 1) (fun _ => rfl)
  have ha0 : a = 0 := ha
  have hm1 : upd (fun _ : Fin 1 => 1) 0 a 0 = 1 := hm trivial
  rw [upd_same, ha0] at hm1
  omega

/-- Tightness of `hI` (witness class: one variable over `Nat`, the unsound inclusion relation
"everything is included"): the criterion holds and the entailment fails. -/
theorem rcrit_sound_hI_tight :
    WF ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    ¬ InclSound clsI (fun _ _ => true) ∧ MeetsSound clsI clsMeets ∧
    ImplSound (premJ 0) premImpl ∧
    RCrit (fun _ _ => true) clsMeets premImpl
      (⟨[⟨.all, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ :=
  ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_neg,
    meetsSound_example_pos, implSound_premImpl 0, (rcritB_iff _ _ _ _ _).1 (by decide),
    rEntails_example_neg⟩

/-- Tightness of `hM` (witness class: one variable over `Nat`, the unsound overlap relation
"everything overlaps"): the criterion holds and the entailment `∀x ∈ ∅ ⊨ ∃x ∈ ∅` fails. -/
theorem rcrit_sound_hM_tight :
    WF ([⟨.all, 0, .empty⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ ¬ MeetsSound clsI (fun _ _ => true) ∧
    ImplSound (premJ 0) premImpl ∧
    RCrit clsIncl (fun _ _ => true) premImpl
      (⟨[⟨.all, 0, .empty⟩], .top⟩ : Shape 1 Cls Prem) ⟨[⟨.ex, 0, .empty⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .empty⟩], .top⟩ ⟨[⟨.ex, 0, .empty⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_neg, implSound_premImpl 0, (rcritB_iff _ _ _ _ _).1 (by decide),
    fun h => ?_⟩
  have := h (fun _ => True) (fun _ => 0) (fun _ ha _ => (ha : False).elim)
  obtain ⟨_, ha, _⟩ := this
  exact (ha : False)

/-- Tightness of `hJ` (witness class: one variable over `Nat`, the unsound premise relation
"every premise implies every other"): the criterion holds and the entailment fails. -/
theorem rcrit_sound_hJ_tight :
    WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧
    ¬ ImplSound (premJ 0) (fun _ _ => true) ∧
    RCrit clsIncl clsMeets (fun _ _ => true)
      (⟨[⟨.all, 0, .all⟩], .atMostOne⟩ : Shape 1 Cls Prem) ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_example_neg, (rcritB_iff _ _ _ _ _).1 (by decide),
    fun h => ?_⟩
  have := h (fun σ => σ 0 ≤ 1) (fun _ => 0) (fun a _ hp => by simpa [upd] using hp 0)
  have := this 2 trivial trivial
  simp [upd] at this

/-- Tightness of part (i) of `h` (witness class: one variable over `Nat`): every other hypothesis
and criterion part holds, the entailment `∃x ⊨ ∀x` fails. -/
theorem rcrit_part_i_tight :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    SkolemOrderPreserved ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ UnivReflected ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 0, by unfold SkolemOrderPreserved; decide,
    (univDomains_iff_pairAllB _ _ _).2 (by decide), (exDomains_iff_pairAllB _ _ _).2 (by decide),
    (meet_iff_pairAllB _ _ _).2 (by decide), rfl, by unfold UnivReflected; decide, fun h => ?_⟩
  have := h (fun σ => σ 0 = 0) (fun _ => 0) ⟨0, trivial, fun _ => by simp [upd]⟩
  have := this 1 trivial trivial
  simp [upd] at this

/-- Tightness of part (ii) of `h` (witness class: two variables over `Nat`): every other
hypothesis and criterion part holds, the entailment `∀x ∃y ⊨ ∃y ∀x` fails. -/
theorem rcrit_part_ii_tight :
    WF ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls)) ∧
    WF ([⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] : List (Binder 2 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 1) premImpl ∧
    UnivReflected ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    PremiseContravariant premImpl
      (⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩ : Shape 2 Cls Prem)
      ⟨[⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ SkolemOrderPreserved ([⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩] : List (Binder 2 Cls))
      [⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩] ∧
    ¬ REntails clsI (premJ 1) ⟨[⟨.all, 0, .all⟩, ⟨.ex, 1, .all⟩], .top⟩
      ⟨[⟨.ex, 1, .all⟩, ⟨.all, 0, .all⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 1, by unfold UnivReflected; decide,
    (univDomains_iff_pairAllB _ _ _).2 (by decide), (exDomains_iff_pairAllB _ _ _).2 (by decide),
    (meet_iff_pairAllB _ _ _).2 (by decide), rfl, by unfold SkolemOrderPreserved; decide,
    fun h => ?_⟩
  have := h (fun σ => σ 1 = σ 0) (fun _ => 0)
    (fun a _ => ⟨a, trivial, fun _ => by simp [upd]⟩)
  obtain ⟨b, _, hb⟩ := this
  have := hb (b + 1) trivial trivial
  simp [upd] at this

/-- Tightness of the universal-domain part of `h` (witness class: one variable over `Nat`):
every other hypothesis and criterion part holds, the entailment `∀x ∈ {0,1} ⊨ ∀x ∈ Nat` fails. -/
theorem rcrit_univ_domain_tight :
    WF ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))
      [⟨.all, 0, .all⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.all, 0, .zeroOne⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ UnivDomainsContravariant clsIncl ([⟨.all, 0, .zeroOne⟩] : List (Binder 1 Cls))
      [⟨.all, 0, .all⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zeroOne⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ :=
  ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 0, (prefixCritB_iff _ _).1 (by decide),
    (exDomains_iff_pairAllB _ _ _).2 (by decide), (meet_iff_pairAllB _ _ _).2 (by decide), rfl,
    univDomains_example_neg, rEntails_example_neg⟩

/-- Tightness of the existential-domain part of `h` (witness class: one variable over `Nat`):
every other hypothesis and criterion part holds, the entailment `∃x ∈ Nat ⊨ ∃x ∈ {0,1}` fails. -/
theorem rcrit_ex_domain_tight :
    WF ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .zeroOne⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .zeroOne⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .zeroOne⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .zeroOne⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.ex, 0, .all⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ ∧
    ¬ ExDomainsCovariant clsIncl ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .zeroOne⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.ex, 0, .zeroOne⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 0, (prefixCritB_iff _ _).1 (by decide),
    (univDomains_iff_pairAllB _ _ _).2 (by decide), (meet_iff_pairAllB _ _ _).2 (by decide), rfl,
    fun h => absurd ((exDomains_iff_pairAllB _ _ _).1 h) (by decide), fun h => ?_⟩
  have := h (fun σ => σ 0 = 2) (fun _ => 0) ⟨2, trivial, fun _ => by simp [upd]⟩
  obtain ⟨a, ha, hm⟩ := this
  have := hm trivial
  simp [upd] at this
  have : a ≤ 1 := ha
  omega

/-- Tightness of the overlap part of `h` (witness class: one variable over `Nat`): every other
hypothesis and criterion part holds, the entailment `∀x ∈ {0} ⊨ ∃x ∈ ∅` fails. -/
theorem rcrit_meet_tight :
    WF ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .empty⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .empty⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls)) [⟨.ex, 0, .empty⟩] ∧
    PremiseContravariant premImpl (⟨[⟨.all, 0, .zero⟩], .top⟩ : Shape 1 Cls Prem)
      ⟨[⟨.ex, 0, .empty⟩], .top⟩ ∧
    ¬ InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .zero⟩] : List (Binder 1 Cls))
      [⟨.ex, 0, .empty⟩] ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .zero⟩], .top⟩ ⟨[⟨.ex, 0, .empty⟩], .top⟩ := by
  refine ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 0, (prefixCritB_iff _ _).1 (by decide),
    (univDomains_iff_pairAllB _ _ _).2 (by decide), (exDomains_iff_pairAllB _ _ _).2 (by decide),
    rfl, meet_example_neg, fun h => ?_⟩
  have := h (fun _ => True) (fun _ => 0) (fun _ _ _ => trivial)
  obtain ⟨_, ha, _⟩ := this
  exact (ha : False)

/-- Tightness of the premise part of `h` (witness class: one variable over `Nat`): every other
hypothesis and criterion part holds, the entailment `∀x (x ≤ 1 → M) ⊨ ∀x (⊤ → M)` fails. -/
theorem rcrit_premise_tight :
    WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧ WF ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) ∧
    InclSound clsI clsIncl ∧ MeetsSound clsI clsMeets ∧ ImplSound (premJ 0) premImpl ∧
    PrefixCrit ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    UnivDomainsContravariant clsIncl ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ExDomainsCovariant clsIncl ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    InstantiatedDomainsMeet clsMeets ([⟨.all, 0, .all⟩] : List (Binder 1 Cls)) [⟨.all, 0, .all⟩] ∧
    ¬ PremiseContravariant premImpl (⟨[⟨.all, 0, .all⟩], .atMostOne⟩ : Shape 1 Cls Prem)
      ⟨[⟨.all, 0, .all⟩], .top⟩ ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.all, 0, .all⟩], .atMostOne⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ :=
  ⟨(wfB_iff _).1 (by decide), (wfB_iff _).1 (by decide), inclSound_example_pos,
    meetsSound_example_pos, implSound_premImpl 0, (prefixCritB_iff _ _).1 (by decide),
    (univDomains_iff_pairAllB _ _ _).2 (by decide), (exDomains_iff_pairAllB _ _ _).2 (by decide),
    (meet_iff_pairAllB _ _ _).2 (by decide), premise_example_neg, rcrit_sound_hJ_tight.2.2.2.2.2.2⟩

/-- Tightness of `hα` in `rEntails_of_isEmpty` (witness class: `Nat`, one variable): `Nat` is
inhabited and `∃x ∈ Nat ⊭ ∀x ∈ Nat`. -/
theorem rEntails_of_isEmpty_tight :
    ¬ (Nat → False) ∧
    ¬ REntails clsI (premJ 0) ⟨[⟨.ex, 0, .all⟩], .top⟩ ⟨[⟨.all, 0, .all⟩], .top⟩ :=
  ⟨fun h => h 0, rcrit_complete_hE_tight.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Tightness of `hne` in `evalR_premise_pull_out` (witness class: one existential variable over
`Nat` with empty domain): with `H = False` the left side `∃x ∈ ∅ (False → L)` fails while the
right side `False → …` holds. -/
theorem evalR_premise_pull_out_hne_tight :
    ¬ (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
    (∀ b ∈ ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)), ∀ (σ : Fin 1 → Nat) (a : Nat),
      (fun _ => False) (upd σ b.var a) ↔ (fun _ : Fin 1 → Nat => False) σ) ∧
    ¬ (evalR clsI ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls))
        (fun σ => (fun _ => False) σ → (fun _ => False) σ) (fun _ => 0) ↔
      ((fun _ : Fin 1 → Nat => False) (fun _ => 0) →
        evalR clsI ([⟨.ex, 0, .empty⟩] : List (Binder 1 Cls)) (fun _ => False) (fun _ => 0))) := by
  refine ⟨fun h => let ⟨a, ha⟩ := h ⟨.ex, 0, .empty⟩ (by simp); (ha : False), ?_, ?_⟩
  · intro b _ σ a; exact Iff.rfl
  · intro h
    obtain ⟨a, ha, _⟩ := h.2 (fun f => f.elim)
    exact (ha : False)

/-- Tightness of the independence hypothesis in `evalR_premise_pull_out` (witness class: one
existential variable over `Nat`, domain `Nat`, premise `x ≤ 1`): `∃x (x ≤ 1 → False)` holds
(take `x := 2`) while `0 ≤ 1 → ∃x False` fails. -/
theorem evalR_premise_pull_out_hind_tight :
    (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), ∃ a, clsI b.dom a) ∧
    ¬ (∀ b ∈ ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)), ∀ (σ : Fin 1 → Nat) (a : Nat),
      (fun τ : Fin 1 → Nat => τ 0 ≤ 1) (upd σ b.var a) ↔ (fun τ : Fin 1 → Nat => τ 0 ≤ 1) σ) ∧
    ¬ (evalR clsI ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls))
        (fun σ => σ 0 ≤ 1 → False) (fun _ => 0) ↔
      ((fun τ : Fin 1 → Nat => τ 0 ≤ 1) (fun _ => 0) →
        evalR clsI ([⟨.ex, 0, .all⟩] : List (Binder 1 Cls)) (fun _ => False) (fun _ => 0))) := by
  refine ⟨fun b hb => by simp at hb; subst hb; exact ⟨0, trivial⟩, fun h => ?_, fun h => ?_⟩
  · have := (h ⟨.ex, 0, .all⟩ (by simp) (fun _ => 0) 2).2 (Nat.zero_le 1)
    simp [upd] at this
  · obtain ⟨_, _, hf⟩ := h.1 ⟨2, trivial, fun hp => by simp [upd] at hp⟩ (Nat.zero_le 1)
    exact hf

/-- Non-vacuity of `evalR_premise_pull_out`, with a premise that depends on a variable the
prefix leaves free (two variables over `Nat`, prefix `∃y ∈ {0,1}`, premise `x ≤ 1`, which is not
true at every assignment): both hypotheses hold. -/
theorem evalR_premise_pull_out_nonvacuous :
    (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls)), ∃ a, clsI b.dom a) ∧
    (∀ b ∈ ([⟨.ex, 1, .zeroOne⟩] : List (Binder 2 Cls)), ∀ (σ : Fin 2 → Nat) (a : Nat),
      (fun τ : Fin 2 → Nat => τ 0 ≤ 1) (upd σ b.var a) ↔ (fun τ : Fin 2 → Nat => τ 0 ≤ 1) σ) ∧
    ¬ (∀ σ : Fin 2 → Nat, (fun τ : Fin 2 → Nat => τ 0 ≤ 1) σ) := by
  refine ⟨fun b hb => by simp at hb; subst hb; exact ⟨0, by simp [clsI]⟩, ?_,
    fun h => absurd (h (fun _ => 2)) (by decide)⟩
  intro b hb σ a
  simp at hb; subst hb
  simp [upd]

end Toy.ClaimStrength
