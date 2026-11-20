import Toy.Sep.Boundaries
import Toy.Sep.NonVacuity

/-!
# Supplementary results

* Under symmetric disjointness the two directions of partial associativity coincide,
  so the frame rule for frame-quantified triples needs only `DisjSymm` and
  `UnionAssoc` (no commutativity of union).
* A least-free-address function `leastFree`, defined by well-founded recursion on the
  finiteness of heaps (no `Classical.choice`), witnesses the freshness hypotheses of the
  predictable-allocation results.
* Tightness of the premise `FQTriple P c Q` in the frame-quantified frame rule and in the
  adequacy theorem, and of `DisjSymm` and `UnionComm` in the left-unit adequacy corollary.
* Over `Heap Empty` every command is safety-monotone and has the frame property.
* Tightness of `DisjSymm` and of `UnionAssoc` in the frame-rule corollaries that assume
  `DisjSymm` (with or without `UnionComm`), and tightness and non-vacuity of the two
  premises of the conjunction rule `triple_conj`.
-/

namespace Toy.Sep

open SepStruct

/-! ## Two-sided associativity from one direction plus symmetric disjointness

Commutativity of union is not needed to derive `UnionAssocRev` from `UnionAssoc`:
symmetric disjointness suffices. -/

/-- Under `DisjSymm` alone (with NO `UnionComm` assumption), left-to-right partial
associativity `UnionAssoc` implies right-to-left `UnionAssocRev` by three cyclic
applications `(b, c, a) → (c, a, b) → (a, b, c)`. -/
theorem unionAssocRev_of_disjSymm_of_unionAssoc {S : Type u} [SepStruct S]
    (hs : DisjSymm S) (ha : UnionAssoc S) : UnionAssocRev S := by
  intro a b c hbc ha_bc
  obtain ⟨hca, hb_ca, _⟩ := ha b c a hbc (hs a (union b c) ha_bc)
  obtain ⟨hab, hc_ab, _⟩ := ha c a b hca (hs b (union c a) hb_ca)
  have hab_c : disj (union a b) c := hs c (union a b) hc_ab
  obtain ⟨_, _, heq⟩ := ha a b c hab hab_c
  exact ⟨hab, hab_c, heq.symm⟩

/-- Symmetrically, `DisjSymm` + `UnionAssocRev` implies `UnionAssoc`. -/
theorem unionAssoc_of_disjSymm_of_unionAssocRev {S : Type u} [SepStruct S]
    (hs : DisjSymm S) (har : UnionAssocRev S) : UnionAssoc S := by
  intro a b c hab hab_c
  obtain ⟨hca, hca_b, _⟩ := har c a b hab (hs (union a b) c hab_c)
  obtain ⟨hbc, hbc_a, _⟩ := har b c a hca (hs (union c a) b hca_b)
  have ha_bc : disj a (union b c) := hs (union b c) a hbc_a
  obtain ⟨_, _, heq⟩ := har a b c hbc ha_bc
  exact ⟨hbc, ha_bc, heq.symm⟩

/-- Under `DisjSymm` alone, the two directions of partial associativity coincide. -/
theorem unionAssoc_iff_unionAssocRev_of_disjSymm {S : Type u} [SepStruct S]
    (hs : DisjSymm S) : UnionAssoc S ↔ UnionAssocRev S :=
  ⟨unionAssocRev_of_disjSymm_of_unionAssoc hs, unionAssoc_of_disjSymm_of_unionAssocRev hs⟩

/-- Consequently, the frame rule for frame-quantified triples holds under `DisjSymm` and
`UnionAssoc` alone,
without `UnionComm`. -/
theorem fqTriple_frame_of_disjSymm_of_unionAssoc {S : Type u} [SepStruct S]
    (hs : DisjSymm S) (ha : UnionAssoc S) (c : Cmd S) {P Q R : Assn S}
    (ht : FQTriple P c Q) : FQTriple (sep P R) c (sep Q R) :=
  fqTriple_frame_of_unionAssoc_of_unionAssocRev ha
    (unionAssocRev_of_disjSymm_of_unionAssoc hs ha) c ht

/-- Non-commutative witness: `projLeftSepStruct` (`a ∘ b = a`, all pairs disjoint)
satisfies `DisjSymm`, `UnionAssoc`, and `UnionAssocRev`, yet fails `UnionComm`. -/
theorem projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm :
    @DisjSymm Nat projLeftSepStruct ∧
    @UnionAssoc Nat projLeftSepStruct ∧
    @UnionAssocRev Nat projLeftSepStruct ∧
    ¬ @UnionComm Nat projLeftSepStruct := by
  have hs : @DisjSymm Nat projLeftSepStruct := fun _ _ _ => trivial
  have ha : @UnionAssoc Nat projLeftSepStruct := fun _ _ _ _ _ => ⟨trivial, trivial, rfl⟩
  refine ⟨hs, ha, @unionAssocRev_of_disjSymm_of_unionAssoc Nat projLeftSepStruct hs ha, ?_⟩
  intro hc
  have h01 : (0 : Nat) = 1 := hc 0 1 trivial
  cases h01

/-! ## A least-free-address allocator (defined without `Classical.choice`)

Witnesses that the freshness hypothesis of `detAllocInto_not_frameProp_of_fresh` and
the hypotheses of `not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied` are met by a
genuinely fresh deterministic allocator. -/

private theorem leastFree_acc_from_bound {V : Type} (h : Heap V) (n : Nat)
    (hn : ∀ j, n ≤ j → h.val j = none) :
    ∀ k i, i + k = n → Acc (fun j i => j = i + 1 ∧ h.val i ≠ none) i
  | 0, i, hik => Acc.intro i fun _ ⟨_, hi⟩ => absurd (hn i (by omega)) hi
  | k + 1, i, hik =>
    Acc.intro i fun j ⟨hj, _⟩ => hj ▸ leastFree_acc_from_bound h n hn k (i + 1) (by omega)

private theorem leastFree_acc0 {V : Type} (h : Heap V) :
    Acc (fun j i => j = i + 1 ∧ h.val i ≠ none) 0 :=
  let ⟨n, hn⟩ := h.finite
  leastFree_acc_from_bound h n hn n 0 (Nat.zero_add n)

/-- Constructive (zero `Classical.choice`) least-free-address function on `Heap V`. -/
def leastFree {V : Type} (h : Heap V) : Nat :=
  (@Acc.rec Nat (fun j i => j = i + 1 ∧ h.val i ≠ none)
    (fun i _ => { k : Nat // i ≤ k ∧ h.val k = none ∧ ∀ j, i ≤ j → j < k → h.val j ≠ none })
    (fun i _ ih =>
      match e : h.val i with
      | none =>
        ⟨i, Nat.le_refl i, e, fun _ hij hji =>
          absurd (Nat.lt_of_le_of_lt hij hji) (Nat.lt_irrefl _)⟩
      | some _ =>
        let ⟨k, hik, hk, hmin⟩ := ih (i + 1) ⟨rfl, by simp [e]⟩
        ⟨k, Nat.le_of_lt hik, hk, fun j hij hjk => by
          by_cases hji : j = i
          · subst hji; simp [e]
          · exact hmin j (by omega) hjk⟩)
    0 (leastFree_acc0 h)).1

theorem leastFree_spec {V : Type} (h : Heap V) :
    h.val (leastFree h) = none ∧ ∀ j, j < leastFree h → h.val j ≠ none := by
  let res := @Acc.rec Nat (fun j i => j = i + 1 ∧ h.val i ≠ none)
    (fun i _ => { k : Nat // i ≤ k ∧ h.val k = none ∧ ∀ j, i ≤ j → j < k → h.val j ≠ none })
    (fun i _ ih =>
      match e : h.val i with
      | none =>
        ⟨i, Nat.le_refl i, e, fun _ hij hji =>
          absurd (Nat.lt_of_le_of_lt hij hji) (Nat.lt_irrefl _)⟩
      | some _ =>
        let ⟨k, hik, hk, hmin⟩ := ih (i + 1) ⟨rfl, by simp [e]⟩
        ⟨k, Nat.le_of_lt hik, hk, fun j hij hjk => by
          by_cases hji : j = i
          · subst hji; simp [e]
          · exact hmin j (by omega) hjk⟩)
    0 (leastFree_acc0 h)
  exact ⟨res.2.2.1, fun j hj => res.2.2.2 j (Nat.zero_le j) hj⟩

/-- Non-vacuity of `detAllocInto_not_frameProp_of_fresh`'s `hfresh` hypothesis and of
`not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied` with a genuinely fresh allocator. -/
theorem detAllocInto_fresh_nonvacuous (r : Nat) :
    (∀ h : Heap Nat, h.val r ≠ none → h.val (leastFree h) = none) ∧
    Safe (detAlloc leastFree (1 : Nat)) Heap.emp ∧
    (Heap.emp : Heap Nat).val 0 = none ∧
    AlwaysAllocatesAt (detAlloc leastFree (1 : Nat)) Heap.emp 0 ∧
    RunsWhenOccupied (detAlloc leastFree (1 : Nat)) Heap.emp 0 1 := by
  refine ⟨fun h _ => (leastFree_spec h).1, safe_detAlloc _ _ _, rfl, ?_, ⟨_, rfl⟩⟩
  intro h₀ hr
  injection hr with hr
  subst hr
  have h0 : leastFree (Heap.emp : Heap Nat) = 0 := by
    cases hk : leastFree (Heap.emp : Heap Nat) with
    | zero => rfl
    | succ m => exact absurd rfl ((leastFree_spec (Heap.emp : Heap Nat)).2 0 (by omega))
  simp [h0]

/-! ## Tightness of the rule premise of the frame-quantified results, and of the
hypotheses of the left-unit corollary -/

/-- Tightness of the premise `FQTriple P c Q` of
`fqTriple_frame_of_unionAssoc_of_unionAssocRev`: in the heap model both associativity
directions hold, yet for `c = skip`, `P = true`, `Q = false`, `R = true` the conclusion
`FQTriple (P * R) c (Q * R)` fails. -/
theorem fqTriple_frame_premise_tight :
    UnionAssoc (Heap Nat) ∧ UnionAssocRev (Heap Nat) ∧
    ¬ FQTriple (sep (fun _ => True) (fun _ => True)) (skip : Cmd (Heap Nat))
        (sep (fun _ => False) (fun _ => True)) := by
  refine ⟨heap_unionAssoc Nat, heap_unionAssocRev Nat, ?_⟩
  intro hFQ
  have hpre : sep (sep (fun _ : Heap Nat => True) (fun _ => True)) (sing Heap.emp) Heap.emp :=
    ⟨Heap.emp, Heap.emp, fun _ => Or.inl rfl, (Heap.join_emp _).symm,
      ⟨Heap.emp, Heap.emp, fun _ => Or.inl rfl, (Heap.join_emp _).symm, trivial, trivial⟩, rfl⟩
  obtain ⟨_, _, _, _, ⟨_, _, _, _, hf, _⟩, _⟩ := (hFQ (sing Heap.emp) Heap.emp hpre).2 Heap.emp rfl
  exact hf

/-- Tightness of the premise `FQTriple P c Q` of `triple_of_fqTriple_of_rightUnitLaw`:
`emp` is a right unit of the heap model, yet `{true} skip {false}` fails. -/
theorem triple_of_fqTriple_premise_tight :
    RightUnitLaw (Heap.emp : Heap Nat) ∧
    ¬ Triple (fun _ : Heap Nat => True) (skip : Cmd (Heap Nat)) (fun _ => False) := by
  refine ⟨heap_rightUnitLaw Nat, ?_⟩
  intro ht
  exact (ht Heap.emp trivial).2 Heap.emp rfl

/-- Tightness of `UnionComm` in `triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw`. -/
theorem projRight_disjSymm_unitLaw_and_fqTriple_adequacy_fails :
    @DisjSymm Nat projRightSepStruct ∧
    @UnitLaw Nat projRightSepStruct 0 ∧
    @FQTriple Nat projRightSepStruct (sing 1) skip (sing 0) ∧
    ¬ @Triple Nat (sing 1) skip (sing 0) := by
  refine ⟨fun _ _ _ => trivial, fun _ => ⟨trivial, rfl⟩, ?_, ?_⟩
  · intro R x ⟨_, r, _, he, _, hR⟩
    have he' : x = r := he
    rw [he']
    refine ⟨safe_skip r, fun h' hr => ?_⟩
    have hr' : h' = r := by injection hr
    rw [hr']
    exact ⟨0, r, trivial, rfl, rfl, hR⟩
  · intro ht
    have h10 : (1 : Nat) = 0 := (ht 1 rfl).2 1 rfl
    cases h10

/-- A separation structure on `Bool` in which only `false` may appear on the left of a
disjoint pair (so disjointness is not symmetric) and union is `||`. -/
@[reducible] def leftDisjCommUnit : SepStruct Bool := ⟨fun x _ => x = false, fun x y => x || y⟩

/-- Tightness of `DisjSymm` in `triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw`:
union is commutative and `false` is a left unit, `FQTriple {true} abort false` holds
vacuously (no state of the form `true ∘ r` is defined), but `{true} abort {false}` fails. -/
theorem leftDisjCommUnit_unionComm_unitLaw_and_fqTriple_adequacy_fails :
    @UnionComm Bool leftDisjCommUnit ∧
    @UnitLaw Bool leftDisjCommUnit false ∧
    @FQTriple Bool leftDisjCommUnit (sing true) abort (fun _ => False) ∧
    ¬ @Triple Bool (sing true) abort (fun _ => False) := by
  refine ⟨fun a b _ => Bool.or_comm a b, fun a => ⟨rfl, Bool.false_or a⟩, ?_, ?_⟩
  · intro R _ ⟨a, _, hd, _, ha, _⟩
    have ha' : a = true := ha
    have hd' : a = false := hd
    rw [ha'] at hd'
    cases hd'
  · intro ht
    exact (ht true rfl).1 rfl

/-- Tightness of `UnitLaw` in `triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw`:
with empty disjointness, disjointness is symmetric and union is commutative (vacuously),
there is no left unit, `FQTriple true abort false` holds vacuously, and
`{true} abort {false}` fails. -/
theorem emptyDisj_disjSymm_unionComm_no_unit_and_fqTriple_adequacy_fails :
    @DisjSymm Unit emptyDisjSepStruct ∧ @UnionComm Unit emptyDisjSepStruct ∧
    (¬ ∃ e, @UnitLaw Unit emptyDisjSepStruct e) ∧
    @FQTriple Unit emptyDisjSepStruct (fun _ => True) abort (fun _ => False) ∧
    ¬ Triple (fun _ : Unit => True) abort (fun _ => False) := by
  obtain ⟨_, hs, hc, _, _, _, _, hfq, hnt⟩ := emptyDisj_no_rightUnit_and_fqTriple_adequacy_fails
  exact ⟨hs, hc, fun ⟨e, he⟩ => (he e).1, hfq, hnt⟩

/-! ## Edge case: over an uninhabited value type every command is local -/

/-- Over the uninhabited value type `Empty` the only heap is `emp`, so every command is
safety-monotone and has the frame property. -/
theorem heap_empty_all_commands_local (c : Cmd (Heap Empty)) :
    SafetyMono c ∧ FrameProp c := by
  have huniq : ∀ h : Heap Empty, h = Heap.emp := fun h =>
    Heap.ext fun k => by cases e : h.val k with | none => rfl | some v => exact v.elim
  refine ⟨fun h h' _ hs => ?_, fun h h' h'' _ _ hrun => ?_⟩
  · rw [huniq h] at hs; rw [huniq (union h h')]; exact hs
  · rw [huniq (union h h'), huniq h''] at hrun
    rw [huniq h, huniq h', huniq h'']
    exact ⟨Heap.emp, hrun, fun _ => Or.inl rfl, (Heap.join_emp Heap.emp).symm⟩

/-! ## Tightness of `DisjSymm` in the frame rule from one-directional associativity

`OneWayAssoc` (in `Toy.Sep.FrameQuantified`) already shows that `UnionAssoc` alone does
not give the frame rule. `CommOneWay` keeps its disjointness table but makes union
commutative, so `DisjSymm` is the only hypothesis of
`fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc` that fails. -/

/-- A three-element structure `s0, s1, s2` with the disjointness of `OneWayAssoc`
(`s0 ⊥ s0`, `s0 ⊥ s2`, `s1 ⊥ s2`, and no other pair) and a commutative union:
`s2` absorbs on either side, and every other union is `s0`. -/
inductive CommOneWay where
  | s0 | s1 | s2
  deriving DecidableEq

namespace CommOneWay

/-- Disjointness of `CommOneWay` as a boolean function (the table of `OneWayAssoc`). -/
def disjB : CommOneWay → CommOneWay → Bool
  | .s0, .s0 => true
  | .s0, .s2 => true
  | .s1, .s2 => true
  | _, _ => false

/-- Union of `CommOneWay`: `x ∘ s2 = s2 ∘ x = s2`, and `x ∘ y = s0` otherwise. -/
def op : CommOneWay → CommOneWay → CommOneWay
  | .s2, _ => .s2
  | _, .s2 => .s2
  | _, _ => .s0

/-- Diverges at `s0` and `s1`; terminates in `s2` from `s2`. -/
def step2 : Cmd CommOneWay
  | .s2, o => o = .ok .s2
  | _, _ => False

end CommOneWay

instance : SepStruct CommOneWay where
  disj x y := CommOneWay.disjB x y = true
  union := CommOneWay.op

instance (x y : CommOneWay) : Decidable (disj x y) :=
  inferInstanceAs (Decidable (CommOneWay.disjB x y = true))

/-- **Tightness of `DisjSymm` in `fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc`
and `unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc`**: `CommOneWay` satisfies
`UnionComm` and `UnionAssoc` but neither `DisjSymm` nor `UnionAssocRev`, and
`FQTriple {s0} step2 {s1}` holds while its framed version with frame `{s0}` fails (the
postcondition `s1 ∘ (s0 ∘ s2)` cannot be re-associated, because `s1 ⊥ s0` fails). -/
theorem commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails :
    UnionComm CommOneWay ∧ UnionAssoc CommOneWay ∧ ¬ DisjSymm CommOneWay ∧
    ¬ UnionAssocRev CommOneWay ∧
    FQTriple (sing CommOneWay.s0) CommOneWay.step2 (sing CommOneWay.s1) ∧
    ¬ FQTriple (sep (sing CommOneWay.s0) (sing CommOneWay.s0)) CommOneWay.step2
        (sep (sing CommOneWay.s1) (sing CommOneWay.s0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y; cases x <;> cases y <;> decide
  · intro x y z; cases x <;> cases y <;> cases z <;> decide
  · intro hs
    exact absurd (hs .s0 .s2 (by decide)) (by decide)
  · intro har
    have := (har .s1 .s0 .s2 (by decide) (by decide)).1
    exact absurd this (by decide)
  · intro F h ⟨a, f, hdf, h_eq, ha, hF⟩
    have ha' : a = .s0 := ha
    subst ha'; subst h_eq
    cases f with
    | s0 => exact ⟨fun hf => hf, fun _ hr => hr.elim⟩
    | s1 => cases hdf
    | s2 =>
      refine ⟨(fun hf => nomatch hf), fun h' hr => ?_⟩
      cases hr
      exact ⟨.s1, .s2, rfl, rfl, rfl, hF⟩
  · intro hFQ
    have hpre : sep (sep (sing CommOneWay.s0) (sing CommOneWay.s0))
        (sing CommOneWay.s2) CommOneWay.s2 :=
      ⟨.s0, .s2, rfl, rfl, ⟨.s0, .s0, rfl, rfl, rfl, rfl⟩, rfl⟩
    have hpost := (hFQ (sing CommOneWay.s2) CommOneWay.s2 hpre).2 CommOneWay.s2 rfl
    obtain ⟨_, _, _, _, ⟨a, b, hab, _, ha, hb⟩, _⟩ := hpost
    have ha' : a = .s1 := ha
    have hb' : b = .s0 := hb
    subst ha'; subst hb'
    cases hab

/-! ## Tightness of `UnionAssoc` in the `DisjSymm` corollaries

`AssocGap` (in `Toy.Sep.FrameQuantified`) does not satisfy `DisjSymm`, so it witnesses
tightness of `UnionAssoc` only for `fqTriple_frame_of_unionAssoc_of_unionAssocRev`.
`SymmAssocGap` is its symmetric, commutative version. -/

/-- A five-element structure `p, r, s, m, t` in which `p ⊥ r` and `r ⊥ p` with
`p ∘ r = r ∘ p = m`, `m ⊥ s` and `s ⊥ m` with `m ∘ s = s ∘ m = t`, and no other pair is
disjoint. -/
inductive SymmAssocGap where
  | p | r | s | m | t
  deriving DecidableEq

namespace SymmAssocGap

/-- Disjointness of `SymmAssocGap` as a boolean function. -/
def disjB : SymmAssocGap → SymmAssocGap → Bool
  | .p, .r => true
  | .r, .p => true
  | .m, .s => true
  | .s, .m => true
  | _, _ => false

/-- Union of `SymmAssocGap` (junk value `p` on non-disjoint arguments). -/
def unionG : SymmAssocGap → SymmAssocGap → SymmAssocGap
  | .p, .r => .m
  | .r, .p => .m
  | .m, .s => .t
  | .s, .m => .t
  | _, _ => .p

/-- The command that faults exactly at `t` and has no outcome elsewhere. -/
def faultAtT : Cmd SymmAssocGap := fun x o => x = .t ∧ o = .fault

end SymmAssocGap

instance : SepStruct SymmAssocGap where
  disj x y := SymmAssocGap.disjB x y = true
  union := SymmAssocGap.unionG

instance (x y : SymmAssocGap) : Decidable (disj x y) :=
  inferInstanceAs (Decidable (SymmAssocGap.disjB x y = true))

/-- **Tightness of `UnionAssoc` in the four `DisjSymm` corollaries**
(`fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc`,
`unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc`,
`fqTriple_frame_of_disjSymm_of_unionAssoc`, `unionAssocRev_of_disjSymm_of_unionAssoc`):
`SymmAssocGap` satisfies `DisjSymm` and `UnionComm` but neither `UnionAssoc` nor
`UnionAssocRev`, and `FQTriple {p} faultAtT false` holds while its framed version with
frame `{r}` fails (the framed precondition contains `(p ∘ r) ∘ s = t`). -/
theorem symmAssocGap_disjSymm_unionComm_and_fqTriple_frame_fails :
    DisjSymm SymmAssocGap ∧ UnionComm SymmAssocGap ∧ ¬ UnionAssoc SymmAssocGap ∧
    ¬ UnionAssocRev SymmAssocGap ∧
    FQTriple (sing SymmAssocGap.p) SymmAssocGap.faultAtT (fun _ => False) ∧
    ¬ FQTriple (sep (sing SymmAssocGap.p) (sing SymmAssocGap.r)) SymmAssocGap.faultAtT
        (sep (fun _ => False) (sing SymmAssocGap.r)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y; cases x <;> cases y <;> decide
  · intro x y; cases x <;> cases y <;> decide
  · intro ha
    have := (ha .p .r .s (by decide) (by decide)).1
    exact absurd this (by decide)
  · intro har
    have := (har .s .p .r (by decide) (by decide)).1
    exact absurd this (by decide)
  · intro R x ⟨a, b, hab, hx, ha, _⟩
    have ha : a = SymmAssocGap.p := ha
    subst ha; subst hx
    refine ⟨?_, fun _ ⟨_, hf⟩ => nomatch hf⟩
    rintro ⟨hb, _⟩
    cases b <;> first | exact absurd hab (by decide) | cases hb
  · intro hFQ
    have hpre : sep (sep (sing SymmAssocGap.p) (sing SymmAssocGap.r))
        (sing SymmAssocGap.s) SymmAssocGap.t :=
      ⟨.m, .s, by decide, rfl, ⟨.p, .r, by decide, rfl, rfl, rfl⟩, rfl⟩
    exact (hFQ (sing SymmAssocGap.s) SymmAssocGap.t hpre).1 ⟨rfl, rfl⟩

/-! ## Tightness and non-vacuity of the conjunction rule `triple_conj` -/

/-- **Tightness of `h₁` in `triple_conj`**: on `Unit` with `c = skip`, the second premise
`{true} skip {true}` holds while the conclusion `{true ∧ true} skip {false ∧ true}`
fails. -/
theorem triple_conj_premise1_tight :
    Triple (fun _ : Unit => True) skip (fun _ => True) ∧
    ¬ Triple (conj (fun _ : Unit => True) (fun _ => True)) skip
        (conj (fun _ => False) (fun _ => True)) :=
  ⟨fun h _ => ⟨safe_skip h, fun _ _ => trivial⟩,
   fun ht => ((ht () ⟨trivial, trivial⟩).2 () rfl).1⟩

/-- **Tightness of `h₂` in `triple_conj`**: on `Unit` with `c = skip`, the first premise
`{true} skip {true}` holds while the conclusion `{true ∧ true} skip {true ∧ false}`
fails. -/
theorem triple_conj_premise2_tight :
    Triple (fun _ : Unit => True) skip (fun _ => True) ∧
    ¬ Triple (conj (fun _ : Unit => True) (fun _ => True)) skip
        (conj (fun _ => True) (fun _ => False)) :=
  ⟨fun h _ => ⟨safe_skip h, fun _ _ => trivial⟩,
   fun ht => ((ht () ⟨trivial, trivial⟩).2 () rfl).2⟩

/-- **Non-vacuity of `triple_conj`**: in the heap model both premises hold for
`c = skip` with the different preconditions `ptAny 0` (cell `0` allocated, any value)
and `{0 ↦ 1}`, the conjoined precondition is satisfiable (by `0 ↦ 1`), and the rule
gives the conjoined triple. -/
theorem triple_conj_nonvacuous :
    Triple (ptAny 0) skip (ptAny 0) ∧
    Triple (sing (Heap.pt 0 (1 : Nat))) skip (sing (Heap.pt 0 1)) ∧
    conj (ptAny 0) (sing (Heap.pt 0 (1 : Nat))) (Heap.pt 0 1) ∧
    Triple (conj (ptAny 0) (sing (Heap.pt 0 (1 : Nat)))) skip
      (conj (ptAny 0) (sing (Heap.pt 0 1))) := by
  have hskip : ∀ P : Assn (Heap Nat), Triple P skip P := fun P h hP =>
    ⟨safe_skip h, fun h' hr => by
      have hr : h' = h := by injection hr
      subst hr; exact hP⟩
  exact ⟨hskip _, hskip _, ⟨⟨1, rfl⟩, rfl⟩, triple_conj (hskip _) (hskip _)⟩

end Toy.Sep
