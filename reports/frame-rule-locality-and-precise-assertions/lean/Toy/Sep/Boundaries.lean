import Toy.Sep.Examples

/-!
# Boundary witnesses (all proved)

Small facts that delimit what the main results of the package say.

* The Hoare conjunction rule holds for every command without any precision or
  cancellativity assumption; the distribution law `ConjDistrib` is about
  commuting `*` past `∧`, not about the conjunction rule.
* Locality does not preserve termination: a local command may terminate on the
  empty heap and have no outcome on every larger heap.
* Degenerate separation structures make locality and precision vacuous: for the
  empty-disjointness structure on `Unit` every command is local and every assertion
  precise; without a unit even the always-true assertion can be precise.
* `Precise`, `UniqueFrame` and `ConjDistrib` put `R` on the right of `*`. Their
  left-handed variants coincide with them under `DisjSymm` and `UnionComm`, and
  can differ without these laws, even in right- or left-cancellative structures.
-/

namespace Toy.Sep

open SepStruct

/-! ## The Hoare conjunction rule needs no precision -/

/-- The conjunction rule `{P₁} c {Q₁}, {P₂} c {Q₂} ⊢ {P₁ ∧ P₂} c {Q₁ ∧ Q₂}` holds for
every command and all assertions over any state space; it needs no precision or
cancellativity. -/
theorem triple_conj {S : Type u} {P₁ P₂ Q₁ Q₂ : Assn S} {c : Cmd S}
    (h₁ : Triple P₁ c Q₁) (h₂ : Triple P₂ c Q₂) : Triple (conj P₁ P₂) c (conj Q₁ Q₂) :=
  fun h hP => ⟨(h₁ h hP.1).1, fun h' hr => ⟨(h₁ h hP.1).2 h' hr, (h₂ h hP.2).2 h' hr⟩⟩

/-! ## Locality does not preserve termination -/

/-- Tightness of `Safe c emp` in `not_safetyMono_of_safe_emp_of_faults`:
`assertAlloc 0` faults from `emp` and is safety-monotone. -/
theorem assertAlloc_faults_and_safetyMono :
    assertAlloc (V := Nat) 0 Heap.emp .fault ∧ SafetyMono (assertAlloc (V := Nat) 0) :=
  ⟨Or.inl ⟨rfl, rfl⟩, assertAlloc_safetyMono 0⟩

/-- Tightness of the faulting run in `not_safetyMono_of_safe_emp_of_faults`:
`skip` is safe on `emp` (and never faults) and is safety-monotone. -/
theorem skip_safe_emp_and_safetyMono :
    Safe (skip : Cmd (Heap Nat)) Heap.emp ∧ SafetyMono (skip : Cmd (Heap Nat)) :=
  ⟨safe_skip _, skip_safetyMono⟩

/-- Terminates, unchanged, from the empty heap; has no outcome from any other heap. -/
def skipOnEmp {V : Type} : Cmd (Heap V) := fun h o => h = Heap.emp ∧ o = .ok Heap.emp

/-- `skipOnEmp` is local, terminates from `emp`, and has no outcome from any
non-empty heap: locality (safety monotonicity and the frame property) says
nothing about termination under framing. -/
theorem skipOnEmp_local_and_no_outcome_on_nonempty :
    Local (skipOnEmp : Cmd (Heap Nat)) ∧ (skipOnEmp : Cmd (Heap Nat)) Heap.emp (.ok Heap.emp) ∧
    ∀ h : Heap Nat, h ≠ Heap.emp → ∀ o, ¬ (skipOnEmp : Cmd (Heap Nat)) h o := by
  refine ⟨⟨(fun _ _ _ _ ⟨_, hf⟩ => nomatch hf), ?_⟩, ⟨rfl, rfl⟩, fun h hne _ ⟨he, _⟩ => hne he⟩
  intro h h' h'' _ _ ⟨he, ho⟩
  have hboth : ∀ k, h.val k = none ∧ h'.val k = none := by
    intro k
    have := congrArg (fun x : Heap Nat => x.val k) he
    simp only [Heap.union_eq, Heap.join_val, Heap.emp_val] at this
    cases e1 : h.val k <;> cases e2 : h'.val k <;> simp_all
  have hh : h = Heap.emp := Heap.ext fun k => (hboth k).1
  have hh' : h' = Heap.emp := Heap.ext fun k => (hboth k).2
  subst hh; subst hh'
  injection ho with ho
  exact ⟨Heap.emp, ⟨rfl, rfl⟩, fun _ => Or.inr rfl, by rw [ho]; exact (Heap.join_emp _).symm⟩

/-! ## Degenerate separation structures -/

/-- With empty disjointness (`emptyDisjSepStruct`), `sep P R` is unsatisfiable:
every command is safety-monotone, has the frame property and satisfies the frame
rule, and every assertion is precise, has unique frames and satisfies the
distribution law, all vacuously. -/
theorem emptyDisj_degenerate (c : Cmd Unit) (R : Assn Unit) :
    @SafetyMono Unit emptyDisjSepStruct c ∧ @FrameProp Unit emptyDisjSepStruct c ∧
    @FrameRuleSound Unit emptyDisjSepStruct c ∧ @Precise Unit emptyDisjSepStruct R ∧
    @UniqueFrame Unit emptyDisjSepStruct R ∧ @ConjDistrib Unit emptyDisjSepStruct R :=
  ⟨fun _ _ hd _ => hd.elim, fun _ _ _ hd _ _ => hd.elim,
    fun _ _ _ _ _ ⟨_, _, hd, _⟩ => hd.elim, fun _ _ _ _ hd _ _ _ _ => hd.elim,
    fun _ _ _ _ hd _ _ _ _ => hd.elim, fun _ _ _ ⟨_, _, hd, _⟩ _ => hd.elim⟩

/-- A non-unital structure on `Nat`: only `1 ⊥ 1`, with `a ∘ b = a + b`. -/
@[reducible] def onePairSepStruct : SepStruct Nat := ⟨fun a b => a = 1 ∧ b = 1, fun a b => a + b⟩

/-- **Without a unit, even the always-true assertion can be precise.**
`onePairSepStruct` has symmetric disjointness, commutative and (vacuously)
associative union, and no unit; its only decomposition is `1 ∘ 1`, so
`Precise (fun _ => True)` holds although `True` holds of every state. -/
theorem onePair_true_precise :
    @DisjSymm Nat onePairSepStruct ∧ @UnionComm Nat onePairSepStruct ∧
    @UnionAssoc Nat onePairSepStruct ∧ (¬ ∃ e, @UnitLaw Nat onePairSepStruct e) ∧
    @Precise Nat onePairSepStruct (fun _ => True) := by
  refine ⟨fun _ _ ⟨h1, h2⟩ => ⟨h2, h1⟩, fun a b _ => Nat.add_comm a b, ?_, ?_, ?_⟩
  · intro a b c ⟨ha, hb⟩ ⟨hab, _⟩
    have : a + b = 1 := hab
    omega
  · rintro ⟨e, he⟩
    have := (he 0).1.2
    cases this
  · intro _ _ _ _ ⟨_, h1⟩ ⟨_, h2⟩ _ _ _
    exact h1.trans h2.symm

/-! ## Left-handed precision and distribution -/

/-- Left-handed precision: decompositions `r₁ ∘ f₁ = r₂ ∘ f₂` with the `R`-parts
on the left have the same `R`-part. This is the orientation of the precision
definitions in O'Hearn, Yang and Reynolds 2004 and in Calcagno, O'Hearn and Yang
2007. -/
def PreciseLeft {S : Type u} [SepStruct S] (R : Assn S) : Prop :=
  ∀ r₁ f₁ r₂ f₂ : S, disj r₁ f₁ → disj r₂ f₂ → union r₁ f₁ = union r₂ f₂ →
    R r₁ → R r₂ → r₁ = r₂

/-- Left-handed distribution law `(R * P) ∧ (R * Q) ⊢ R * (P ∧ Q)` for all `P`, `Q`. -/
def ConjDistribLeft {S : Type u} [SepStruct S] (R : Assn S) : Prop :=
  ∀ (P Q : Assn S) (h : S), sep R P h → sep R Q h → sep R (conj P Q) h

section Orientation

variable {S : Type u} [SepStruct S]

theorem sep_comm_of_disjSymm_of_unionComm (hs : DisjSymm S) (hc : UnionComm S)
    {P Q : Assn S} {h : S} (hh : sep P Q h) : sep Q P h := by
  obtain ⟨a, b, hab, he, hP, hQ⟩ := hh
  exact ⟨b, a, hs a b hab, he.trans (hc a b hab), hQ, hP⟩

/-- Under symmetric disjointness and commutative union, right- and left-handed
precision coincide. -/
theorem precise_iff_preciseLeft_of_disjSymm_of_unionComm (hs : DisjSymm S)
    (hc : UnionComm S) (R : Assn S) : Precise R ↔ PreciseLeft R := by
  constructor
  · intro hp r₁ f₁ r₂ f₂ d₁ d₂ he h1 h2
    exact hp f₁ r₁ f₂ r₂ (hs _ _ d₁) (hs _ _ d₂)
      ((hc _ _ (hs _ _ d₁)).trans (he.trans (hc _ _ d₂))) h1 h2
  · intro hp f₁ r₁ f₂ r₂ d₁ d₂ he h1 h2
    exact hp r₁ f₁ r₂ f₂ (hs _ _ d₁) (hs _ _ d₂)
      ((hc _ _ (hs _ _ d₁)).trans (he.trans (hc _ _ d₂))) h1 h2

/-- Under symmetric disjointness and commutative union, the right- and left-handed
distribution laws coincide. -/
theorem conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm (hs : DisjSymm S)
    (hc : UnionComm S) (R : Assn S) : ConjDistrib R ↔ ConjDistribLeft R := by
  constructor
  · intro hd P Q h h1 h2
    exact sep_comm_of_disjSymm_of_unionComm hs hc
      (hd P Q h (sep_comm_of_disjSymm_of_unionComm hs hc h1)
        (sep_comm_of_disjSymm_of_unionComm hs hc h2))
  · intro hd P Q h h1 h2
    exact sep_comm_of_disjSymm_of_unionComm hs hc
      (hd P Q h (sep_comm_of_disjSymm_of_unionComm hs hc h1)
        (sep_comm_of_disjSymm_of_unionComm hs hc h2))

end Orientation

/-- **Orientation matters without commutativity (right cancellation).** In
`projLeftSepStruct` (`a ∘ b = a`, all pairs disjoint), the structure is
right-cancellative and `{0}` is precise, yet the left-handed distribution law
fails for `{0}`; and the always-true assertion is left-precise but not precise. -/
theorem projLeft_rightCancel_precise_not_conjDistribLeft :
    @RightCancel Nat projLeftSepStruct ∧
    @Precise Nat projLeftSepStruct (sing 0) ∧
    ¬ @ConjDistribLeft Nat projLeftSepStruct (sing 0) ∧
    @PreciseLeft Nat projLeftSepStruct (fun _ => True) ∧
    ¬ @Precise Nat projLeftSepStruct (fun _ => True) := by
  refine ⟨fun _ _ _ _ _ he => he, @sing_precise Nat projLeftSepStruct 0, ?_,
    fun _ _ _ _ _ _ he _ _ => he, ?_⟩
  · intro hd
    obtain ⟨_, f, _, _, _, ⟨e0, e1⟩⟩ :=
      hd (sing 0) (sing 1) 0 ⟨0, 0, trivial, rfl, rfl, rfl⟩ ⟨0, 1, trivial, rfl, rfl, rfl⟩
    have : (0 : Nat) = 1 := (e0 : f = 0).symm.trans e1
    cases this
  · intro hp
    have : (0 : Nat) = 1 := hp 0 0 0 1 trivial trivial rfl trivial trivial
    cases this

/-- **Orientation matters without commutativity (left cancellation).** In
`projRightSepStruct` (`a ∘ b = b`, all pairs disjoint), the structure is
left-cancellative and the always-true assertion is precise, yet it neither
satisfies the distribution law nor is left-precise. -/
theorem projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft :
    @LeftCancel Nat projRightSepStruct ∧
    @Precise Nat projRightSepStruct (fun _ => True) ∧
    ¬ @ConjDistrib Nat projRightSepStruct (fun _ => True) ∧
    ¬ @PreciseLeft Nat projRightSepStruct (fun _ => True) := by
  refine ⟨fun _ _ _ _ _ he => he, fun _ _ _ _ _ _ he _ _ => he, ?_, ?_⟩
  · intro hd
    obtain ⟨f, _, _, _, ⟨e0, e1⟩, _⟩ :=
      hd (sing 0) (sing 1) 0 ⟨0, 0, trivial, rfl, rfl, trivial⟩ ⟨1, 0, trivial, rfl, rfl, trivial⟩
    have : (0 : Nat) = 1 := (e0 : f = 0).symm.trans e1
    cases this
  · intro hp
    have : (0 : Nat) = 1 := hp 0 0 1 0 trivial trivial rfl trivial trivial
    cases this

/-- In `projRightSepStruct`, every assertion satisfies the left-handed
distribution law (a positive example for `ConjDistribLeft`). -/
theorem projRight_conjDistribLeft (R : Assn Nat) : @ConjDistribLeft Nat projRightSepStruct R := by
  intro P Q h ⟨a, b, _, hb, hR, hP⟩ ⟨_, b', _, hb', _, hQ⟩
  refine ⟨a, h, trivial, rfl, hR, ?_, ?_⟩
  · have hb : h = b := hb
    rw [hb]; exact hP
  · have hb' : h = b' := hb'
    rw [hb']; exact hQ

/-! ### Tightness of the hypotheses of the orientation equivalences (canonical form) -/

/-- `UnionComm` cannot be dropped from
`precise_iff_preciseLeft_of_disjSymm_of_unionComm`: `projLeftSepStruct` has
symmetric disjointness, and the always-true assertion is left-precise but not
precise. -/
theorem projLeft_disjSymm_and_not_precise_iff_preciseLeft :
    @DisjSymm Nat projLeftSepStruct ∧
    ¬ (@Precise Nat projLeftSepStruct (fun _ => True) ↔
        @PreciseLeft Nat projLeftSepStruct (fun _ => True)) :=
  ⟨fun _ _ _ => trivial, fun h =>
    projLeft_rightCancel_precise_not_conjDistribLeft.2.2.2.2
      (h.2 projLeft_rightCancel_precise_not_conjDistribLeft.2.2.2.1)⟩

/-- `DisjSymm` cannot be dropped from
`precise_iff_preciseLeft_of_disjSymm_of_unionComm`: in `orDisjRightSepStruct`
(`a ⊥ b` iff `b = true`, union `||`) union is commutative, and the always-true
assertion is precise but not left-precise. -/
theorem orDisjRight_unionComm_and_not_precise_iff_preciseLeft :
    @UnionComm Bool orDisjRightSepStruct ∧
    @Precise Bool orDisjRightSepStruct (fun _ => True) ∧
    ¬ @PreciseLeft Bool orDisjRightSepStruct (fun _ => True) ∧
    ¬ (@Precise Bool orDisjRightSepStruct (fun _ => True) ↔
        @PreciseLeft Bool orDisjRightSepStruct (fun _ => True)) := by
  have hp : @Precise Bool orDisjRightSepStruct (fun _ => True) := by
    intro _ r₁ _ r₂ h1 h2 _ _ _
    have h1 : r₁ = true := h1
    have h2 : r₂ = true := h2
    rw [h1, h2]
  have hnl : ¬ @PreciseLeft Bool orDisjRightSepStruct (fun _ => True) := by
    intro hl
    have : false = true := hl false true true true rfl rfl rfl trivial trivial
    cases this
  exact ⟨fun a b _ => Bool.or_comm a b, hp, hnl, fun h => hnl (h.1 hp)⟩

/-- `UnionComm` cannot be dropped from
`conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm`: `projRightSepStruct`
has symmetric disjointness, and the always-true assertion satisfies the
left-handed but not the right-handed distribution law. -/
theorem projRight_disjSymm_and_not_conjDistrib_iff_conjDistribLeft :
    @DisjSymm Nat projRightSepStruct ∧
    ¬ (@ConjDistrib Nat projRightSepStruct (fun _ => True) ↔
        @ConjDistribLeft Nat projRightSepStruct (fun _ => True)) :=
  ⟨fun _ _ _ => trivial, fun h =>
    projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft.2.2.1
      (h.2 (projRight_conjDistribLeft _))⟩

/-- `DisjSymm` cannot be dropped from
`conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm`: in
`orDisjRightSepStruct` union is commutative, and the always-true assertion
satisfies the left-handed but not the right-handed distribution law. -/
theorem orDisjRight_unionComm_and_not_conjDistrib_iff_conjDistribLeft :
    @UnionComm Bool orDisjRightSepStruct ∧
    @ConjDistribLeft Bool orDisjRightSepStruct (fun _ => True) ∧
    ¬ @ConjDistrib Bool orDisjRightSepStruct (fun _ => True) ∧
    ¬ (@ConjDistrib Bool orDisjRightSepStruct (fun _ => True) ↔
        @ConjDistribLeft Bool orDisjRightSepStruct (fun _ => True)) := by
  have hl : @ConjDistribLeft Bool orDisjRightSepStruct (fun _ => True) := by
    intro P Q h ⟨a, b, hab, he, _, hP⟩ ⟨_, b', hab', _, _, hQ⟩
    have hb : b = true := hab
    have hb' : b' = true := hab'
    subst hb; subst hb'
    exact ⟨a, true, rfl, he, trivial, hP, hQ⟩
  have hnr : ¬ @ConjDistrib Bool orDisjRightSepStruct (fun _ => True) := by
    intro hd
    obtain ⟨f, _, _, _, ⟨e0, e1⟩, _⟩ :=
      hd (sing false) (sing true) true ⟨false, true, rfl, rfl, rfl, trivial⟩
        ⟨true, true, rfl, rfl, rfl, trivial⟩
    have : false = true := (e0 : f = false).symm.trans e1
    cases this
  exact ⟨fun a b _ => Bool.or_comm a b, hl, hnr, fun h => hnr (h.2 hl)⟩

/-- Non-vacuity of the hypotheses of the boundary lemmas: the heap model has
symmetric disjointness and commutative union (the hypotheses of the orientation
equivalences), and `allocAt 0 1` is safe on `emp` and faults from `0 ↦ 2` (the
hypotheses of `not_safetyMono_of_safe_emp_of_faults`). -/
theorem boundary_witnesses_nonvacuous :
    (DisjSymm (Heap Nat) ∧ UnionComm (Heap Nat)) ∧
    (Safe (allocAt 0 (1 : Nat)) Heap.emp ∧ allocAt 0 (1 : Nat) (Heap.pt 0 2) .fault) :=
  ⟨⟨heap_disjSymm Nat, heap_unionComm Nat⟩, (safe_allocAt_iff 0 1 _).2 rfl, Or.inl ⟨by simp, rfl⟩⟩

end Toy.Sep
