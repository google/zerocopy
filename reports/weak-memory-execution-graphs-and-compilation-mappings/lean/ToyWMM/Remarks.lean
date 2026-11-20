import ToyWMM.SourceExec
import ToyWMM.StraightLine
import ToyWMM.Tightness

/-!
# Supplementary facts about hypotheses and quantifier domains

* `forall_prog_exists_wf_sc_exec`: every straight-line program (including `[]` and `[[]]`) has a
  well-formed SC-consistent candidate execution, so the universal quantifiers over well-formed
  SC executions in the straight-line race characterizations never range over an empty set.
* `Exec.rfFunctional_of_perLocSC`, `Exec.coTrans_of_perLocSC`: under SC per location, two of
  the nine conjuncts of `Exec.RfCoWf` (`RfFunctional` and `CoTrans`) follow from the others.
* `storeFenceExtraRfOnInserted_check`: `RfCoWf` constrains inserted fences too, although the
  source execution never sees them.
* `exists_sc_execution_hb_unordered_needs_conflict`: the premise `hc` of
  `exists_sc_execution_hb_unordered_of_conflict` cannot be dropped.
* `coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds`: the corollary form of
  shared-location fencing assumes more than the primary theorem.
* `fenceBetweenSharedWR_needs_*`: each hypothesis of that corollary is nevertheless needed; the
  executions refuting the primary theorem's hypotheses also satisfy the corollary's stronger
  `CoKinds` and `FenceBetweenSharedWR`.
-/

namespace Toy.WMM

open Litmus Event

/-! ## Every straight-line program has a well-formed SC execution -/

/-- The sequential execution of `P` in layout order: events of `skel P`, each read returning the
value of the latest earlier same-location write in the layout (initialisation writes come
first), `rf` from that write, and `co` the layout order on same-location writes. -/
def seqSCExec (P : Prog) : Exec (layout P).length where
  ev i :=
    if ((skel P).ev i).isRead then
      { (skel P).ev i with
        val :=
          let ws := (List.finRange (layout P).length).filter fun w =>
            ((skel P).ev w).isWrite && (skel P).sameLoc w i && decide (w.val < i.val)
          match ws.getLast? with
          | some w => ((skel P).ev w).val
          | none => 0 }
    else (skel P).ev i
  po := (skel P).po
  rf w r :=
    let ws := (List.finRange (layout P).length).filter fun u =>
      ((skel P).ev u).isWrite && (skel P).sameLoc u r && decide (u.val < r.val)
    ((skel P).ev r).isRead && (ws.getLast? == some w)
  co w1 w2 :=
    ((skel P).ev w1).isWrite && ((skel P).ev w2).isWrite &&
      (skel P).sameLoc w1 w2 && decide (w1.val < w2.val)

theorem emptyProg_has_wf_sc_exec :
    ExecOf [] (seqSCExec []) ∧ (seqSCExec []).Wf ∧ (seqSCExec []).SCConsistent :=
  ⟨⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide⟩

theorem emptyThreadProg_has_wf_sc_exec :
    ExecOf [[]] (seqSCExec [[]]) ∧ (seqSCExec [[]]).Wf ∧ (seqSCExec [[]]).SCConsistent :=
  ⟨⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide⟩

private theorem foldr_max_ge' (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

private theorem threadEvents_not_init' (t : Nat) (P : Prog) :
    ∀ e ∈ threadEvents t P, e.isInit = false := by
  induction P generalizing t with
  | nil => intro e he; simp [threadEvents] at he
  | cons th rest ih =>
    intro e he
    simp only [threadEvents, List.mem_append, List.mem_map] at he
    rcases he with ⟨ins, _, rfl⟩ | he
    · cases ins <;> rfl
    · exact ih (t + 1) e he

private theorem threadEvents_loc_mem' (t : Nat) (P : Prog) :
    ∀ e ∈ threadEvents t P, e.loc ∈ P.flatten.map Instr.loc := by
  induction P generalizing t with
  | nil => intro e he; simp [threadEvents] at he
  | cons th rest ih =>
    intro e he
    simp only [threadEvents, List.mem_append, List.mem_map] at he
    simp only [List.flatten_cons, List.map_append, List.mem_append]
    rcases he with ⟨ins, hins, rfl⟩ | he
    · exact Or.inl (List.mem_map.mpr ⟨ins, hins, by cases ins <;> rfl⟩)
    · exact Or.inr (ih (t + 1) e he)

private theorem layout_init_lt (P : Prog) (i : Fin (layout P).length) :
    (((skel P).ev i).isInit = true ↔ i.val < P.numLocs) ∧
      (i.val < P.numLocs → (skel P).ev i = Event.initW i.val) ∧
      ((skel P).ev i).loc < P.numLocs := by
  have h1 : ∀ k, k < P.numLocs → (hk : k < (layout P).length) → (layout P)[k] = Event.initW k := by
    intro k hk _
    have hlen : k < ((List.range P.numLocs).map Event.initW).length := by simp [hk]
    simp only [layout]; rw [List.getElem_append_left hlen]; simp
  by_cases hk : i.val < P.numLocs
  · have heq := h1 i.val hk i.isLt
    refine ⟨⟨fun _ => hk, fun _ => by simp [skel, heq, Event.initW, Event.isInit]⟩,
      fun _ => heq, by simp [skel, heq, Event.initW, hk]⟩
  · have hlen : ((List.range P.numLocs).map Event.initW).length ≤ i.val := by simp; omega
    have hmem : (layout P)[i.val] ∈ threadEvents 0 P := by
      simp only [layout]; rw [List.getElem_append_right hlen]; exact List.getElem_mem _
    have hni := threadEvents_not_init' 0 P _ hmem
    have hlmem := threadEvents_loc_mem' 0 P _ hmem
    have hle := foldr_max_ge' _ _ hlmem
    refine ⟨⟨fun hi => by change ((layout P)[i.val]).isInit = true at hi; rw [hni] at hi; simp at hi,
      fun h => absurd h hk⟩, fun h => absurd h hk, ?_⟩
    change ((layout P)[i.val]).loc < P.numLocs
    simp only [Prog.numLocs]; omega

private theorem finRange_filter_pairwise {N : Nat} (p : Fin N → Bool) :
    List.Pairwise (fun a b : Fin N => a.val < b.val) ((List.finRange N).filter p) := by
  apply List.Pairwise.filter
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using hij

private theorem getLast?_ge_of_pairwise {N : Nat} {l : List (Fin N)} {w : Fin N}
    (hpw : List.Pairwise (fun a b : Fin N => a.val < b.val) l)
    (hl : l.getLast? = some w) : w ∈ l ∧ ∀ u ∈ l, u.val ≤ w.val := by
  induction l with
  | nil => simp at hl
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp at hl; subst hl
      exact ⟨by simp, fun u hu => by simp at hu; subst hu; exact Nat.le_refl _⟩
    | cons y ys =>
      have hl' : (y :: ys).getLast? = some w := by simpa using hl
      rw [List.pairwise_cons] at hpw
      obtain ⟨hw_mem, hw_ge⟩ := ih hpw.2 hl'
      refine ⟨List.mem_cons_of_mem x hw_mem, fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact Nat.le_of_lt (hpw.1 w hw_mem)
      · exact hw_ge u hu'

/-- For **every** straight-line program `P : Prog`, `seqSCExec P` is a well-formed SC-consistent
candidate execution of `P`. Thus the universal quantifiers over well-formed SC executions in
the straight-line race characterizations (`hbRaceFree_sc_executions_iff_noConflict` and its two variants) are non-empty for every `P : Prog`. -/
theorem forall_prog_exists_wf_sc_exec (P : Prog) :
    ExecOf P (seqSCExec P) ∧ (seqSCExec P).Wf ∧ (seqSCExec P).SCConsistent := by
  let Y := seqSCExec P
  have hkind : ∀ i, (Y.ev i).kind = ((skel P).ev i).kind := fun i => by
    simp only [Y, seqSCExec]; split <;> rfl
  have htid : ∀ i, (Y.ev i).tid = ((skel P).ev i).tid := fun i => by
    simp only [Y, seqSCExec]; split <;> rfl
  have hloc : ∀ i, (Y.ev i).loc = ((skel P).ev i).loc := fun i => by
    simp only [Y, seqSCExec]; split <;> rfl
  have hisInit : ∀ i, (Y.ev i).isInit = ((skel P).ev i).isInit := fun i => by
    unfold Event.isInit; rw [hkind]
  have hisRead : ∀ i, (Y.ev i).isRead = ((skel P).ev i).isRead := fun i => by
    unfold Event.isRead; rw [hkind]
  have hisWrite : ∀ i, (Y.ev i).isWrite = ((skel P).ev i).isWrite := fun i => by
    unfold Event.isWrite; rw [hkind]
  have hsameLoc : ∀ a b, Y.sameLoc a b = (skel P).sameLoc a b := fun a b => by
    unfold Exec.sameLoc; rw [hloc, hloc]
  have hget : ∀ i : Fin (layout P).length, (layout P).getD i.val default = (layout P)[i] := by
    intro i; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]; rfl
  have hY : ExecOf P Y := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; rw [hkind, hget]; rfl
    · intro i; rw [htid, hget]; rfl
    · intro i; rw [hloc, hget]; rfl
    · intro i hnr; rw [hisRead] at hnr; simp [Y, seqSCExec, hnr]; rfl
    · intro a b
      change (skel P).po a b = (Y.sameThread a b && decide (a.val < b.val))
      unfold Exec.sameThread; rw [hisInit, hisInit, htid, htid]; rfl
  let wsOf (r : Fin (layout P).length) :=
    (List.finRange (layout P).length).filter fun u =>
      ((skel P).ev u).isWrite && (skel P).sameLoc u r && decide (u.val < r.val)
  have hrf_info : ∀ w r, Y.rf w r = true →
      ((skel P).ev r).isRead = true ∧ (wsOf r).getLast? = some w ∧
      ((skel P).ev w).isWrite = true ∧ (skel P).sameLoc w r = true ∧ w.val < r.val ∧
      ∀ u ∈ wsOf r, u.val ≤ w.val := by
    intro w r hrf
    simp only [Y, seqSCExec, Bool.and_eq_true, beq_iff_eq] at hrf
    obtain ⟨hw_mem, hw_ge⟩ := getLast?_ge_of_pairwise (finRange_filter_pairwise _) hrf.2
    have hwf := hw_mem
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact ⟨hrf.1, hrf.2, hwf.2.1.1, hwf.2.1.2, hwf.2.2, hw_ge⟩
  have hsc_lt : ∀ a b, Y.scRel a b = true → a.val < b.val := by
    intro a b hab
    rcases Y.scRel_cases hab with h | h | h | h
    · simp only [Y, seqSCExec, skel, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    · exact (hrf_info a b h).2.2.2.2.1
    · simp only [Y, seqSCExec, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
    · obtain ⟨w, hwa, hwb⟩ := Y.fr_iff.mp h
      obtain ⟨hra, _, _, hslwa, _, hw_ge⟩ := hrf_info w a hwa
      simp only [Y, seqSCExec, Bool.and_eq_true, decide_eq_true_eq] at hwb
      obtain ⟨⟨⟨_, hwb_w⟩, hslwb⟩, hw_lt_b⟩ := hwb
      have hslba : (skel P).sameLoc b a = true :=
        (skel P).sameLoc_trans ((skel P).sameLoc_symm hslwb) hslwa
      by_cases hlt : b.val < a.val
      · have hb_mem : b ∈ wsOf a := by simp [wsOf, List.mem_finRange, hwb_w, hslba, hlt]
        have := hw_ge b hb_mem; omega
      · by_cases heq : b.val = a.val
        · have hba := Fin.ext heq; subst hba
          revert hwb_w hra; simp only [Event.isWrite, Event.isRead]
          cases ((skel P).ev b).kind <;> simp
        · omega
  have hsc : Y.SCConsistent := by
    have hpath : ∀ a b, Rel.Path Y.scRel a b → a.val < b.val := by
      intro a b hp
      induction hp with
      | single hab => exact hsc_lt _ _ hab
      | tail _ hbc ih => exact Nat.lt_trans ih (hsc_lt _ _ hbc)
    exact fun a ha => Nat.lt_irrefl _ (hpath a a ha)
  refine ⟨hY, ⟨hY.poIrrefl, hY.poTrans, hY.poWithinThread, hY.poTotal,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hsc⟩
  · intro a b h; rw [hsameLoc]; exact (hrf_info a b h).2.2.2.1
  · intro a b h; rw [hisWrite, hisRead]; exact ⟨(hrf_info a b h).2.2.1, (hrf_info a b h).1⟩
  · intro a b h
    obtain ⟨hrb, hlast, hwa, _, _, _⟩ := hrf_info a b h
    have hna : ((skel P).ev a).isRead = false := by
      revert hwa; simp only [Event.isWrite, Event.isRead]; cases ((skel P).ev a).kind <;> simp
    simp only [seqSCExec, hna, Bool.false_eq_true, ↓reduceIte, hrb, wsOf] at hlast ⊢
    rw [hlast]
  · intro b hrb
    rw [hisRead] at hrb
    have hbi : ((skel P).ev b).isInit = false := by
      revert hrb; simp only [Event.isRead, Event.isInit]; cases ((skel P).ev b).kind <;> simp
    obtain ⟨hinit_iff, hinit_ev, hloc_lt⟩ := layout_init_lt P b
    have hb_ge : P.numLocs ≤ b.val := by
      by_cases hlt : b.val < P.numLocs
      · rw [hinit_iff.mpr hlt] at hbi; simp at hbi
      · omega
    have hw0_lt_len : ((skel P).ev b).loc < (layout P).length := by simp [layout]; omega
    let w0 : Fin (layout P).length := ⟨((skel P).ev b).loc, hw0_lt_len⟩
    have hw0_ev : (skel P).ev w0 = Event.initW ((skel P).ev b).loc :=
      (layout_init_lt P w0).2.1 hloc_lt
    have hw0_mem : w0 ∈ wsOf b := by
      have hw0_lt_b : w0.val < b.val := Nat.lt_of_lt_of_le hloc_lt hb_ge
      simp [wsOf, List.mem_finRange, hw0_ev, Event.initW, Event.isWrite, Exec.sameLoc, hw0_lt_b]
    have hne_nil : wsOf b ≠ [] := List.ne_nil_of_mem hw0_mem
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne_nil)
    exact ⟨w, by simp [seqSCExec, hrb, wsOf] at hw ⊢; simp [hw]⟩
  · intro a a' b ha ha'
    have h1 := (hrf_info a b ha).2.1
    have h2 := (hrf_info a' b ha').2.1
    rw [h1] at h2; injection h2
  · intro a b h
    simp only [seqSCExec, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hisWrite, hisWrite, hsameLoc]; exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
  · intro a; simp [seqSCExec]
  · intro a b c hab hbc
    simp only [seqSCExec, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
    exact ⟨⟨⟨hab.1.1.1, hbc.1.1.2⟩, (skel P).sameLoc_trans hab.1.2 hbc.1.2⟩,
      Nat.lt_trans hab.2 hbc.2⟩
  · intro a b hne ha hb hsl
    rw [hisWrite] at ha hb; rw [hsameLoc] at hsl
    have hvne : a.val ≠ b.val := fun h => hne (Fin.ext h)
    simp only [seqSCExec, ha, hb, hsl, (skel P).sameLoc_symm hsl, Bool.and_self, Bool.true_and,
      decide_eq_true_eq]
    omega
  · intro a b hai hwb hsl hne
    rw [hisInit] at hai; rw [hisWrite] at hwb; rw [hsameLoc] at hsl
    have hwa : ((skel P).ev a).isWrite = true := by
      revert hai; simp only [Event.isInit, Event.isWrite]; cases ((skel P).ev a).kind <;> simp
    have ha_lt := (layout_init_lt P a).1.mp hai
    have hb_ge : P.numLocs ≤ b.val := by
      by_cases hb_lt : b.val < P.numLocs
      · exfalso
        have ha_ev := (layout_init_lt P a).2.1 ha_lt
        have hb_ev := (layout_init_lt P b).2.1 hb_lt
        simp only [Exec.sameLoc, beq_iff_eq, ha_ev, hb_ev, Event.initW] at hsl
        exact hne (Fin.ext hsl)
      · omega
    simp only [seqSCExec, hwa, hwb, hsl, Bool.and_self, Bool.true_and, decide_eq_true_eq]
    omega

/-! ## Two conjuncts of `RfCoWf` are implied under SC per location -/

/-- Under `PerLocSC`, `RfSameLoc`, `RfKinds` and `CoTotal`, `RfFunctional` holds automatically. -/
theorem Exec.rfFunctional_of_perLocSC {n : Nat} (X : Exec n)
    (hloc : X.PerLocSC) (hrfl : X.RfSameLoc) (hrfk : X.RfKinds) (hcot : X.CoTotal) :
    X.RfFunctional := by
  intro a a' b ha ha'
  by_cases hne : a = a'
  · exact hne
  · exfalso
    have hwa := (hrfk a b ha).1
    have hwa' := (hrfk a' b ha').1
    have hsl : X.sameLoc a a' = true :=
      X.sameLoc_trans (hrfl a b ha) (X.sameLoc_symm (hrfl a' b ha'))
    rcases hcot a a' hne hwa hwa' hsl with hco | hco
    · have hfr : X.fr b a' = true := X.fr_iff.mpr ⟨a, ha, hco⟩
      exact hloc a' (Rel.Path.tail (Rel.Path.single (X.uniprocRel_of_rf ha'))
        (X.uniprocRel_of_fr hfr))
    · have hfr : X.fr b a = true := X.fr_iff.mpr ⟨a', ha', hco⟩
      exact hloc a (Rel.Path.tail (Rel.Path.single (X.uniprocRel_of_rf ha))
        (X.uniprocRel_of_fr hfr))

/-- Under `PerLocSC`, `CoKinds` and `CoTotal`, `CoTrans` holds automatically. -/
theorem Exec.coTrans_of_perLocSC {n : Nat} (X : Exec n)
    (hloc : X.PerLocSC) (hcok : X.CoKinds) (hcot : X.CoTotal) :
    X.CoTrans := by
  intro a b c hab hbc
  by_cases hac_eq : a = c
  · subst hac_eq
    exfalso
    exact hloc a (Rel.Path.tail (Rel.Path.single (X.uniprocRel_of_co hab))
      (X.uniprocRel_of_co hbc))
  · have hwa := (hcok a b hab).1
    have hwc := (hcok b c hbc).2.1
    have hsl : X.sameLoc a c = true :=
      X.sameLoc_trans (hcok a b hab).2.2 (hcok b c hbc).2.2
    cases h : X.co a c with
    | true => rfl
    | false =>
      exfalso
      rcases hcot a c hac_eq hwa hwc hsl with h' | hca
      · rw [h] at h'; exact absurd h' (by decide)
      · exact hloc a (Rel.Path.tail
          (Rel.Path.tail (Rel.Path.single (X.uniprocRel_of_co hab)) (X.uniprocRel_of_co hbc))
          (X.uniprocRel_of_co hca))

/-- Also on compiled programs with stores, an ill-formed `rf` edge into an *inserted* fence
violates `X.RfCoWf` while `X.comap f` still satisfies the conclusion (since `f` skips the inserted
fence). -/
def storeFenceExtraRfOnInserted : Exec 3 :=
  Exec.ofList [initW 0, W 0 0 1, F 0] [(0, 2)] [(0, 1)]

theorem storeFenceExtraRfOnInserted_check :
    ExecOf (fenceAfterStores [[.store 0 1]]) storeFenceExtraRfOnInserted ∧
      storeFenceExtraRfOnInserted.TSOConsistent ∧
      ¬ storeFenceExtraRfOnInserted.RfCoWf ∧
      ∃ f : Fin (layout [[.store 0 1]]).length → Fin 3,
        (∀ a b, a < b ↔ f a < f b) ∧
        (∀ e, (storeFenceExtraRfOnInserted.ev e).isAccess = true → ∃ a, f a = e) ∧
        ExecOf [[.store 0 1]] (storeFenceExtraRfOnInserted.comap f) ∧
        (storeFenceExtraRfOnInserted.comap f).Wf ∧
        (storeFenceExtraRfOnInserted.comap f).SCConsistent := by
  refine ⟨⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide, ?_⟩
  let f : Fin 2 → Fin 3 := fun i => ⟨i.val, by omega⟩
  exact ⟨f, by decide, by decide,
    ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide⟩

/-! ## The premise of `exists_sc_execution_hb_unordered_of_conflict` is needed -/

/-- The conflict premise `hc` of `exists_sc_execution_hb_unordered_of_conflict` is needed: in
`loadStoreSameProg` (`r := x; x := 1` in one thread) the load and the store (layout indices `1`
and `2`) do not conflict, and no well-formed SC execution of the program satisfies the
theorem's conclusion for them (they are always `po`-, hence `hb`-, ordered). -/
theorem exists_sc_execution_hb_unordered_needs_conflict :
    ¬ (skel loadStoreSameProg).Conflict ⟨1, by decide⟩ ⟨2, by decide⟩ ∧
      ¬ ∃ Y : Exec (layout loadStoreSameProg).length,
        ExecOf loadStoreSameProg Y ∧ Y.Wf ∧ Y.SCConsistent ∧
        Y.Conflict ⟨1, by decide⟩ ⟨2, by decide⟩ ∧
        ¬ Y.HB ⟨1, by decide⟩ ⟨2, by decide⟩ ∧ ¬ Y.HB ⟨2, by decide⟩ ⟨1, by decide⟩ := by
  refine ⟨by decide, ?_⟩
  rintro ⟨Y, hY, _, _, _, hnab, _⟩
  apply hnab
  apply Rel.Path.single
  have hpo : Y.po ⟨1, by decide⟩ ⟨2, by decide⟩ = true := by
    obtain ⟨hpo_eq, _, _, _⟩ := hY.skel_facts
    rw [hpo_eq]; decide
  simp [Exec.hbRel, hpo]

/-! ## The corollary form of shared-location fencing assumes more than the primary form -/

/-- Two reads of location `0` by different threads, with a `co` edge between the two reads. -/
def coBetweenReadsSameLoc : Exec 3 :=
  Exec.ofList [initW 0, R 0 0 0, R 1 0 0] [(0, 1), (0, 2)] [(1, 2)]

/-- The `CoKinds` premise of the corollary `scConsistentErased_of_tso_of_fenceBetweenSharedWR` is
stronger than the `CoSameLoc` premise of the primary theorem
`scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`: `coBetweenReadsSameLoc` satisfies every
premise of the primary theorem and `FenceBetweenSharedWR`, fails `CoKinds`, and is SC after
fence erasure. -/
theorem coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds :
    coBetweenReadsSameLoc.PoTrans ∧ coBetweenReadsSameLoc.PoWithinThread ∧
      coBetweenReadsSameLoc.PoTotal ∧ coBetweenReadsSameLoc.RfSameLoc ∧
      coBetweenReadsSameLoc.CoSameLoc ∧ ¬ coBetweenReadsSameLoc.CoKinds ∧
      coBetweenReadsSameLoc.FenceBetweenSharedWR ∧ coBetweenReadsSameLoc.PerLocSC ∧
      coBetweenReadsSameLoc.TsoGhbAcyclic ∧ coBetweenReadsSameLoc.SCConsistentErased := by
  decide

/-! ## Each hypothesis of the corollary `scConsistentErased_of_tso_of_fenceBetweenSharedWR` is needed

Each theorem below states that every other hypothesis of the corollary holds, the named one
fails, and the conclusion `SCConsistentErased` fails. The executions are those used for the
primary theorem `scConsistentErased_of_tso_of_fenceBetweenBothSharedWR`. -/

theorem fenceBetweenSharedWR_needs_poTrans :
    poTwoCycle.PoWithinThread ∧ poTwoCycle.PoTotal ∧ poTwoCycle.RfSameLoc ∧ poTwoCycle.CoKinds ∧
      poTwoCycle.FenceBetweenSharedWR ∧ poTwoCycle.PerLocSC ∧ poTwoCycle.TsoGhbAcyclic ∧
      ¬ poTwoCycle.PoTrans ∧ ¬ poTwoCycle.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_poWithinThread :
    poIntoInit.PoTrans ∧ poIntoInit.PoTotal ∧ poIntoInit.RfSameLoc ∧ poIntoInit.CoKinds ∧
      poIntoInit.FenceBetweenSharedWR ∧ poIntoInit.PerLocSC ∧ poIntoInit.TsoGhbAcyclic ∧
      ¬ poIntoInit.PoWithinThread ∧ ¬ poIntoInit.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_poTotal :
    poPartial.PoTrans ∧ poPartial.PoWithinThread ∧ poPartial.RfSameLoc ∧ poPartial.CoKinds ∧
      poPartial.FenceBetweenSharedWR ∧ poPartial.PerLocSC ∧ poPartial.TsoGhbAcyclic ∧
      ¬ poPartial.PoTotal ∧ ¬ poPartial.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_rfSameLoc :
    rfWrongLoc.PoTrans ∧ rfWrongLoc.PoWithinThread ∧ rfWrongLoc.PoTotal ∧ rfWrongLoc.CoKinds ∧
      rfWrongLoc.FenceBetweenSharedWR ∧ rfWrongLoc.PerLocSC ∧ rfWrongLoc.TsoGhbAcyclic ∧
      ¬ rfWrongLoc.RfSameLoc ∧ ¬ rfWrongLoc.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_coKinds :
    coAcrossLocs.PoTrans ∧ coAcrossLocs.PoWithinThread ∧ coAcrossLocs.PoTotal ∧
      coAcrossLocs.RfSameLoc ∧ coAcrossLocs.FenceBetweenSharedWR ∧ coAcrossLocs.PerLocSC ∧
      coAcrossLocs.TsoGhbAcyclic ∧ ¬ coAcrossLocs.CoKinds ∧
      ¬ coAcrossLocs.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_fenceBetweenSharedWR :
    sbWeak.PoTrans ∧ sbWeak.PoWithinThread ∧ sbWeak.PoTotal ∧ sbWeak.RfSameLoc ∧ sbWeak.CoKinds ∧
      sbWeak.PerLocSC ∧ sbWeak.TsoGhbAcyclic ∧ ¬ sbWeak.FenceBetweenSharedWR ∧
      ¬ sbWeak.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_perLocSC :
    readOwnLaterWrite.PoTrans ∧ readOwnLaterWrite.PoWithinThread ∧ readOwnLaterWrite.PoTotal ∧
      readOwnLaterWrite.RfSameLoc ∧ readOwnLaterWrite.CoKinds ∧
      readOwnLaterWrite.FenceBetweenSharedWR ∧ readOwnLaterWrite.TsoGhbAcyclic ∧
      ¬ readOwnLaterWrite.PerLocSC ∧ ¬ readOwnLaterWrite.SCConsistentErased := by
  decide

theorem fenceBetweenSharedWR_needs_tsoGhbAcyclic :
    sbFencedWeak.PoTrans ∧ sbFencedWeak.PoWithinThread ∧ sbFencedWeak.PoTotal ∧
      sbFencedWeak.RfSameLoc ∧ sbFencedWeak.CoKinds ∧ sbFencedWeak.FenceBetweenSharedWR ∧
      sbFencedWeak.PerLocSC ∧ ¬ sbFencedWeak.TsoGhbAcyclic ∧
      ¬ sbFencedWeak.SCConsistentErased := by
  decide

end Toy.WMM
