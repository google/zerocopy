import Toy.Sep.NonLocal

/-!
# Frame-quantified triples (all proved)

An alternative to a separate frame rule is to *bake the frame into the
specification*: `FQTriple P c Q` means `{P * R} c {Q * R}` for every frame `R`.

* In any separation structure with two-sided partial associativity
  (`UnionAssoc` and `UnionAssocRev`), frame-quantified triples satisfy the frame
  rule for **every** command, local or not. Each of the two associativity
  directions is necessary.
* In any separation structure with a right unit, a frame-quantified triple
  implies the plain triple (instantiate the frame with the unit). The right unit
  is necessary.
* In the heap model both hold. For a non-local command the converse fails:
  `{emp} allocLeast 1 {0 ↦ 1}` holds but is not frame-quantified, while the
  weaker `{emp} allocLeast 1 {∃ k. k ↦ 1}` is.

For local commands the plain triple implies the frame-quantified one: that is
exactly `Toy.Sep.frame_rule_of_safetyMono_of_frameProp`.
-/

namespace Toy.Sep

open SepStruct

variable {V : Type}

/-- Frame-quantified triple: `{P * R} c {Q * R}` for every frame `R`. -/
def FQTriple {S : Type u} [SepStruct S] (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ R : Assn S, Triple (sep P R) c (sep Q R)

section Generic

variable {S : Type u} [SepStruct S]

theorem sep_assoc_mp_of_unionAssoc (ha : UnionAssoc S) {P R R' : Assn S} {h : S}
    (hh : sep (sep P R) R' h) : sep P (sep R R') h := by
  obtain ⟨x, r', hxr', hx, ⟨p, r, hpr, hp, hP, hR⟩, hR'⟩ := hh
  subst hx; subst hp
  obtain ⟨hrr', hp_rr', he⟩ := ha p r r' hpr hxr'
  exact ⟨p, union r r', hp_rr', he, hP, ⟨r, r', hrr', rfl, hR, hR'⟩⟩

theorem sep_assoc_mpr_of_unionAssocRev (ha : UnionAssocRev S) {Q R R' : Assn S} {h : S}
    (hh : sep Q (sep R R') h) : sep (sep Q R) R' h := by
  obtain ⟨q, y, hqy, hq, hQ, ⟨r, r', hrr', hy, hR, hR'⟩⟩ := hh
  subst hq; subst hy
  obtain ⟨hqr, hqr_r', he⟩ := ha q r r' hrr' hqy
  exact ⟨union q r, r', hqr_r', he, ⟨q, r, hqr, rfl, hQ, hR⟩, hR'⟩

/-- **The frame rule holds for frame-quantified triples, for every command**,
in every separation structure with two-sided partial associativity (no
locality, commutativity, unit or cancellativity needed). The left-to-right
direction re-associates the precondition, the right-to-left direction the
postcondition. -/
theorem fqTriple_frame_of_unionAssoc_of_unionAssocRev (ha : UnionAssoc S)
    (har : UnionAssocRev S) (c : Cmd S) {P Q R : Assn S}
    (ht : FQTriple P c Q) : FQTriple (sep P R) c (sep Q R) := by
  intro R' h hpre
  obtain ⟨hs, hpost⟩ := ht (sep R R') h (sep_assoc_mp_of_unionAssoc ha hpre)
  exact ⟨hs, fun h' hr => sep_assoc_mpr_of_unionAssocRev har (hpost h' hr)⟩

/-- Corollary in partial commutative monoids: symmetric disjointness, commutative
union and (one-way) partial associativity suffice. -/
theorem fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc (hs : DisjSymm S)
    (hc : UnionComm S) (ha : UnionAssoc S) (c : Cmd S) {P Q R : Assn S}
    (ht : FQTriple P c Q) : FQTriple (sep P R) c (sep Q R) :=
  fqTriple_frame_of_unionAssoc_of_unionAssocRev ha
    (unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc hs hc ha) c ht

/-- **A frame-quantified triple implies the plain triple**, in every separation
structure with a right unit `e` (instantiate the frame with `{e}`). -/
theorem triple_of_fqTriple_of_rightUnitLaw {e : S} (hu : RightUnitLaw e) (c : Cmd S)
    {P Q : Assn S} (ht : FQTriple P c Q) : Triple P c Q := by
  intro h hP
  obtain ⟨hs, hpost⟩ := ht (sing e) h ⟨h, e, (hu h).1, (hu h).2.symm, hP, rfl⟩
  refine ⟨hs, fun h' hr => ?_⟩
  obtain ⟨q, e', _, heq, hQ, he'⟩ := hpost h' hr
  have he'' : e' = e := he'
  subst he''
  rw [heq, (hu q).2]
  exact hQ

/-- Corollary in partial commutative monoids: a (left) unit together with
symmetric disjointness and commutative union suffices. -/
theorem triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw {e : S} (hs : DisjSymm S)
    (hc : UnionComm S) (hu : UnitLaw e) (c : Cmd S) {P Q : Assn S}
    (ht : FQTriple P c Q) : Triple P c Q :=
  triple_of_fqTriple_of_rightUnitLaw (rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw hs hc hu)
    c ht

end Generic

/-! ## Heap model corollaries -/

theorem heap_sep_assoc_mp {P R R' : Assn (Heap V)} {h : Heap V}
    (hh : sep (sep P R) R' h) : sep P (sep R R') h :=
  sep_assoc_mp_of_unionAssoc (heap_unionAssoc V) hh

theorem heap_sep_assoc_mpr {Q R R' : Assn (Heap V)} {h : Heap V}
    (hh : sep Q (sep R R') h) : sep (sep Q R) R' h :=
  sep_assoc_mpr_of_unionAssocRev (heap_unionAssocRev V) hh

theorem heap_sep_emp_iff {P : Assn (Heap V)} {h : Heap V} :
    sep P (sing Heap.emp) h ↔ P h := by
  constructor
  · rintro ⟨f, e, _, he, hP, hE⟩
    have hE : e = Heap.emp := hE
    subst hE
    have : h = f := by rw [he]; exact Heap.join_emp f
    subst this
    exact hP
  · intro hP
    exact ⟨h, Heap.emp, fun _ => Or.inr rfl, (Heap.join_emp h).symm, hP, rfl⟩

/-- **The frame rule holds for frame-quantified triples, for every command**
(heap model). -/
theorem heap_fqTriple_frame (c : Cmd (Heap V)) {P Q R : Assn (Heap V)}
    (ht : FQTriple P c Q) : FQTriple (sep P R) c (sep Q R) :=
  fqTriple_frame_of_unionAssoc_of_unionAssocRev (heap_unionAssoc V) (heap_unionAssocRev V) c ht

/-- **A frame-quantified triple implies the plain triple** (heap model;
instantiate the frame with `emp`). -/
theorem heap_triple_of_fqTriple (c : Cmd (Heap V)) {P Q : Assn (Heap V)}
    (ht : FQTriple P c Q) : Triple P c Q :=
  triple_of_fqTriple_of_rightUnitLaw (heap_rightUnitLaw V) c ht

/-- **For non-local commands frame-quantified triples are strictly stronger**:
`{emp} allocLeast 1 {0 ↦ 1}` holds as a plain triple but not as a
frame-quantified one. -/
theorem allocLeast_triple_and_not_fqTriple :
    Triple (sing Heap.emp) (allocLeast (1 : Nat)) (sing (Heap.pt 0 1)) ∧
    ¬ FQTriple (sing Heap.emp) (allocLeast (1 : Nat)) (sing (Heap.pt 0 1)) := by
  obtain ⟨_, ht, hnot⟩ := allocLeast_safetyMono_and_framed_triple_fails
  exact ⟨ht, fun H => hnot (H _)⟩

/-- Frame-quantified triples do support *some* specification of the non-local
`allocLeast`: `{emp} allocLeast 1 {∃ k. k ↦ 1}` holds for every frame. The
address is no longer determined by the specification. -/
theorem allocLeast_fqTriple_someCell :
    FQTriple (sing Heap.emp) (allocLeast (1 : Nat)) (fun h => ∃ k, h = Heap.pt k 1) := by
  intro R h ⟨e, r, _, he, hE, hR⟩
  have hE : e = Heap.emp := hE
  subst hE
  have hh : h = r := by rw [he, Heap.union_eq, Heap.emp_join]
  subst hh
  refine ⟨safe_allocLeast 1 _, ?_⟩
  rintro h' ⟨k, hk, _, he'⟩
  injection he' with he'
  subst he'
  refine ⟨Heap.pt k 1, h, fun j => ?_, ?_, ⟨k, rfl⟩, hR⟩
  · by_cases hj : j = k
    · subst hj; exact Or.inr hk
    · exact Or.inl (by simp [hj])
  · apply Heap.ext; intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]

/-! ## Tightness of the algebraic hypotheses (canonical form) -/

/-- A five-element structure `p, r, s, m, t` in which `p ⊥ r` with `p ∘ r = m`,
`m ⊥ s` with `m ∘ s = t`, and no other pair is disjoint. -/
inductive AssocGap where
  | p | r | s | m | t
  deriving DecidableEq

namespace AssocGap

/-- Disjointness of `AssocGap` as a boolean function. -/
def disjB : AssocGap → AssocGap → Bool
  | .p, .r => true
  | .m, .s => true
  | _, _ => false

/-- Union of `AssocGap` (junk value `p` on non-disjoint arguments). -/
def unionG : AssocGap → AssocGap → AssocGap
  | .p, .r => .m
  | .m, .s => .t
  | _, _ => .p

end AssocGap

instance : SepStruct AssocGap where
  disj x y := AssocGap.disjB x y = true
  union := AssocGap.unionG

instance (x y : AssocGap) : Decidable (disj x y) :=
  inferInstanceAs (Decidable (AssocGap.disjB x y = true))

/-- The command that faults exactly at `t` and has no outcome elsewhere. -/
def AssocGap.faultAtT : Cmd AssocGap := fun x o => x = .t ∧ o = .fault

/-- **Tightness of `UnionAssoc` in `fqTriple_frame_of_unionAssoc_of_unionAssocRev`**:
`AssocGap` satisfies `UnionAssocRev` (vacuously) but not `UnionAssoc`, and
`FQTriple {p} faultAtT false` holds while its framed version with frame `{r}`
fails (the framed precondition contains `(p ∘ r) ∘ s = t`, which is not of the
form `p ∘ y`). -/
theorem assocGap_unionAssocRev_and_fqTriple_frame_fails :
    UnionAssocRev AssocGap ∧ ¬ UnionAssoc AssocGap ∧
    FQTriple (sing AssocGap.p) AssocGap.faultAtT (fun _ => False) ∧
    ¬ FQTriple (sep (sing AssocGap.p) (sing AssocGap.r)) AssocGap.faultAtT
        (sep (fun _ => False) (sing AssocGap.r)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c; cases a <;> cases b <;> cases c <;> decide
  · intro ha
    have := (ha .p .r .s (by decide) (by decide)).1
    exact absurd this (by decide)
  · intro R x ⟨a, b, hab, hx, ha, _⟩
    have ha : a = AssocGap.p := ha
    subst ha; subst hx
    refine ⟨?_, fun _ ⟨_, hf⟩ => nomatch hf⟩
    rintro ⟨hb, _⟩
    cases b <;> first | exact absurd hab (by decide) | cases hb
  · intro hFQ
    have hpre : sep (sep (sing AssocGap.p) (sing AssocGap.r)) (sing AssocGap.s) AssocGap.t :=
      ⟨.m, .s, by decide, rfl, ⟨.p, .r, by decide, rfl, rfl, rfl⟩, rfl⟩
    exact (hFQ (sing AssocGap.s) AssocGap.t hpre).1 ⟨rfl, rfl⟩

/-- A three-element structure `s0, s1, s2` with `s0 ⊥ s0`, `s0 ⊥ s2`, `s1 ⊥ s2`,
`x ∘ s2 = s2` and `x ∘ y = s0` otherwise. -/
inductive OneWayAssoc where
  | s0 | s1 | s2
  deriving DecidableEq

namespace OneWayAssoc

/-- Disjointness of `OneWayAssoc` as a boolean function. -/
def disjB : OneWayAssoc → OneWayAssoc → Bool
  | .s0, .s0 => true
  | .s0, .s2 => true
  | .s1, .s2 => true
  | _, _ => false

/-- Union of `OneWayAssoc`. -/
def op : OneWayAssoc → OneWayAssoc → OneWayAssoc
  | _, .s2 => .s2
  | _, _ => .s0

end OneWayAssoc

instance : SepStruct OneWayAssoc where
  disj x y := OneWayAssoc.disjB x y = true
  union := OneWayAssoc.op

instance (x y : OneWayAssoc) : Decidable (disj x y) :=
  inferInstanceAs (Decidable (OneWayAssoc.disjB x y = true))

/-- Diverges at `s0` and `s1`; terminates in `s2` from `s2`. -/
def OneWayAssoc.step2 : Cmd OneWayAssoc
  | .s2, o => o = .ok .s2
  | _, _ => False

/-- **Tightness of `UnionAssocRev` in `fqTriple_frame_of_unionAssoc_of_unionAssocRev`**:
`OneWayAssoc` satisfies `UnionAssoc` but not `UnionAssocRev`, and
`FQTriple {s0} step2 {s1}` holds while its framed version with frame `{s0}` fails
(the postcondition `s1 ∘ (s0 ∘ s2)` cannot be re-associated, because `s1 ⊥ s0`
fails). -/
theorem oneWayAssoc_unionAssoc_and_fqTriple_frame_fails :
    UnionAssoc OneWayAssoc ∧ ¬ UnionAssocRev OneWayAssoc ∧
    FQTriple (sing OneWayAssoc.s0) OneWayAssoc.step2 (sing OneWayAssoc.s1) ∧
    ¬ FQTriple (sep (sing OneWayAssoc.s0) (sing OneWayAssoc.s0)) OneWayAssoc.step2
        (sep (sing OneWayAssoc.s1) (sing OneWayAssoc.s0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z; cases x <;> cases y <;> cases z <;> decide
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
    have hpre : sep (sep (sing OneWayAssoc.s0) (sing OneWayAssoc.s0))
        (sing OneWayAssoc.s2) OneWayAssoc.s2 :=
      ⟨.s0, .s2, rfl, rfl, ⟨.s0, .s0, rfl, rfl, rfl, rfl⟩, rfl⟩
    have hpost := (hFQ (sing OneWayAssoc.s2) OneWayAssoc.s2 hpre).2 OneWayAssoc.s2 rfl
    obtain ⟨_, _, _, _, ⟨a, b, hab, _, ha, hb⟩, _⟩ := hpost
    have ha' : a = .s1 := ha
    have hb' : b = .s0 := hb
    subst ha'; subst hb'
    cases hab

/-- The separation structure on `Unit` in which nothing is disjoint. -/
@[reducible] def emptyDisjSepStruct : SepStruct Unit := ⟨fun _ _ => False, fun a _ => a⟩

/-- **Tightness of `RightUnitLaw` in `triple_of_fqTriple_of_rightUnitLaw`**: with
empty disjointness there is no right unit (although symmetry, commutativity, both
associativity directions and both cancellation laws hold), and the
frame-quantified triple `FQTriple true abort false` holds vacuously while the
plain triple `{true} abort {false}` fails. -/
theorem emptyDisj_no_rightUnit_and_fqTriple_adequacy_fails :
    (¬ ∃ e, @RightUnitLaw Unit emptyDisjSepStruct e) ∧
    @DisjSymm Unit emptyDisjSepStruct ∧ @UnionComm Unit emptyDisjSepStruct ∧
    @UnionAssoc Unit emptyDisjSepStruct ∧ @UnionAssocRev Unit emptyDisjSepStruct ∧
    @RightCancel Unit emptyDisjSepStruct ∧ @LeftCancel Unit emptyDisjSepStruct ∧
    @FQTriple Unit emptyDisjSepStruct (fun _ => True) abort (fun _ => False) ∧
    ¬ Triple (fun _ : Unit => True) abort (fun _ => False) := by
  refine ⟨fun ⟨e, he⟩ => (he e).1, fun _ _ h => h, fun _ _ h => h.elim,
    fun _ _ _ h _ => h.elim, fun _ _ _ h _ => h.elim, fun _ _ _ h _ _ => h.elim,
    fun _ _ _ h _ _ => h.elim, ?_, ?_⟩
  · intro R _ ⟨_, _, hd, _⟩; exact hd.elim
  · intro ht; exact (ht () trivial).1 rfl

/-- Non-vacuity: a frame-quantified triple for `skip`. -/
theorem skip_fqTriple :
    FQTriple (sing (Heap.pt 0 1 : Heap Nat)) skip (sing (Heap.pt 0 1)) := by
  intro R h ⟨h₁, h₂, hd, he, hP, hR⟩
  refine ⟨safe_skip h, fun h' hr => ?_⟩
  have hr : h' = h := by injection hr
  subst hr
  exact ⟨h₁, h₂, hd, he, hP, hR⟩

end Toy.Sep
