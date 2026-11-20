import ToyWMM.Programs

/-!
# Race freedom of straight-line programs collapses to a static condition

Programs here have no control flow, so every event of a program occurs in every execution and
every SC interleaving of the threads is an SC execution. Consequently every conflicting pair
of accesses is unordered by `hb = (po ∪ rf)⁺` in some well-formed SC execution
(`exists_sc_execution_hb_unordered_of_conflict`), and:

* `hb`-race freedom of all SC executions holds exactly for programs without conflicting
  accesses (`hbRaceFree_sc_executions_iff_noConflict`);
* race freedom with the exemption "both accesses satisfy `NoUnfencedWRIncident`" over all SC
  executions is equivalent to the static condition `Prog.ConflictsWRFenced`
  (`raceFree_sc_executions_iff_conflictsWRFenced`), and with the "either access" exemption to
  `Prog.ConflictsWRFencedEither` (`raceFreeEither_sc_executions_iff_conflictsWRFencedEither`);
* `Prog.ConflictsWRFenced` implies `FenceBetweenSharedWR` on every execution of the program
  (`fenceBetweenSharedWR_of_conflictsWRFenced`), so its SC guarantee on TSO
  (`scConsistent_of_tso_of_conflictsWRFenced`) is a corollary of shared-location fencing
  soundness; `Prog.ConflictsWRFencedEither` gives no such guarantee
  (`conflictsWRFencedEither_does_not_imply_sc`, in `ToyWMM.Tightness`).
-/

namespace Toy.WMM

open Litmus

section Construction

private theorem foldr_max_ge (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

private theorem toEvent_loc (t : Nat) (ins : Instr) : (Instr.toEvent t ins).loc = ins.loc := by
  cases ins <;> rfl

private theorem toEvent_not_init (t : Nat) (ins : Instr) : (Instr.toEvent t ins).isInit = false := by
  cases ins <;> rfl

private theorem threadEvents_not_init (t : Nat) (P : Prog) :
    ∀ e ∈ threadEvents t P, e.isInit = false := by
  induction P generalizing t with
  | nil => intro e he; simp [threadEvents] at he
  | cons th rest ih =>
    intro e he
    simp only [threadEvents, List.mem_append, List.mem_map] at he
    rcases he with ⟨ins, _, rfl⟩ | he
    · exact toEvent_not_init t ins
    · exact ih (t + 1) e he

private theorem threadEvents_loc_mem (t : Nat) (P : Prog) :
    ∀ e ∈ threadEvents t P, e.loc ∈ P.flatten.map Instr.loc := by
  induction P generalizing t with
  | nil => intro e he; simp [threadEvents] at he
  | cons th rest ih =>
    intro e he
    simp only [threadEvents, List.mem_append, List.mem_map] at he
    simp only [List.flatten_cons, List.map_append, List.mem_append]
    rcases he with ⟨ins, hins, rfl⟩ | he
    · exact Or.inl (List.mem_map.mpr ⟨ins, hins, (toEvent_loc t ins).symm⟩)
    · exact Or.inr (ih (t + 1) e he)

private theorem layout_getElem_lt_numLocs (P : Prog) (k : Nat) (hk : k < P.numLocs)
    (hlt : k < (layout P).length) : (layout P)[k] = Event.initW k := by
  have h1 : k < ((List.range P.numLocs).map Event.initW).length := by simp [hk]
  simp only [layout]
  rw [List.getElem_append_left h1]
  simp

private theorem layout_isInit_iff (P : Prog) (i : Fin (layout P).length) :
    ((layout P)[i]).isInit = true ↔ i.val < P.numLocs := by
  by_cases hk : i.val < P.numLocs
  · constructor
    · intro _; exact hk
    · intro _
      have := layout_getElem_lt_numLocs P i.val hk i.isLt
      simp [this, Event.initW, Event.isInit]
  · constructor
    · intro hi
      exfalso
      have hlen : ((List.range P.numLocs).map Event.initW).length ≤ i.val := by simp; omega
      have hmem : (layout P)[i.val] ∈ threadEvents 0 P := by
        simp only [layout]
        rw [List.getElem_append_right hlen]
        exact List.getElem_mem _
      have hni := threadEvents_not_init 0 P _ hmem
      change ((layout P)[i.val]).isInit = true at hi
      rw [hni] at hi
      exact absurd hi (by decide)
    · intro h; exact absurd h hk

private theorem layout_loc_lt_numLocs (P : Prog) (i : Fin (layout P).length) :
    ((layout P)[i]).loc < P.numLocs := by
  by_cases hk : i.val < P.numLocs
  · have := layout_getElem_lt_numLocs P i.val hk i.isLt
    simp [this, Event.initW, hk]
  · have hlen : ((List.range P.numLocs).map Event.initW).length ≤ i.val := by simp; omega
    have hmem : (layout P)[i.val] ∈ threadEvents 0 P := by
      simp only [layout]
      rw [List.getElem_append_right hlen]
      exact List.getElem_mem _
    have hlmem := threadEvents_loc_mem 0 P _ hmem
    have hle := foldr_max_ge _ _ hlmem
    change ((layout P)[i.val]).loc < P.numLocs
    simp only [Prog.numLocs]
    omega

private theorem numLocs_le_layout_length (P : Prog) : P.numLocs ≤ (layout P).length := by
  simp [layout]

private def maxByRank {N : Nat} (rank : Fin N → Nat) : List (Fin N) → Option (Fin N)
  | [] => none
  | x :: xs =>
    match maxByRank rank xs with
    | none => some x
    | some y => if rank x < rank y then some y else some x

private theorem maxByRank_mem {N : Nat} (rank : Fin N → Nat) :
    ∀ {l : List (Fin N)} {w : Fin N}, maxByRank rank l = some w → w ∈ l
  | [], _, h => by simp [maxByRank] at h
  | x :: xs, w, h => by
    simp only [maxByRank] at h
    cases hm : maxByRank rank xs with
    | none =>
      rw [hm] at h; simp at h; subst h; exact List.mem_cons_self
    | some y =>
      rw [hm] at h
      by_cases hlt : rank x < rank y
      · simp [hlt] at h; subst h; exact List.mem_cons_of_mem x (maxByRank_mem rank hm)
      · simp [hlt] at h; subst h; exact List.mem_cons_self

private theorem maxByRank_ge {N : Nat} (rank : Fin N → Nat) :
    ∀ {l : List (Fin N)} {w : Fin N}, maxByRank rank l = some w → ∀ u ∈ l, rank u ≤ rank w
  | [], _, h, _, hu => by cases hu
  | x :: xs, w, h, u, hu => by
    simp only [maxByRank] at h
    simp only [List.mem_cons] at hu
    cases hm : maxByRank rank xs with
    | none =>
      rw [hm] at h; simp at h; subst h
      rcases hu with rfl | hu
      · exact Nat.le_refl _
      · exfalso
        cases xs with
        | nil => cases hu
        | cons z zs =>
          simp only [maxByRank] at hm
          cases hm' : maxByRank rank zs <;> simp [hm'] at hm
          split at hm <;> simp at hm
    | some y =>
      rw [hm] at h
      have ihy := maxByRank_ge rank hm
      by_cases hlt : rank x < rank y
      · simp [hlt] at h; subst h
        rcases hu with rfl | hu
        · exact Nat.le_of_lt hlt
        · exact ihy u hu
      · simp [hlt] at h; subst h
        rcases hu with rfl | hu
        · exact Nat.le_refl _
        · exact Nat.le_trans (ihy u hu) (by omega)

private theorem maxByRank_isSome {N : Nat} (rank : Fin N → Nat) :
    ∀ {l : List (Fin N)} {x : Fin N}, x ∈ l → ∃ w, maxByRank rank l = some w
  | [], _, hx => by cases hx
  | a :: xs, _, _ => by
    simp only [maxByRank]
    cases maxByRank rank xs with
    | none => exact ⟨a, rfl⟩
    | some y =>
      by_cases hlt : rank a < rank y
      · exact ⟨y, by simp [hlt]⟩
      · exact ⟨a, by simp [hlt]⟩

/-- Candidate writes to the same location as `r` that precede `r` in `rank`. -/
private def earlierWrites (P : Prog) (rank : Fin (layout P).length → Nat)
    (r : Fin (layout P).length) : List (Fin (layout P).length) :=
  (List.finRange (layout P).length).filter fun w =>
    ((skel P).ev w).isWrite && (skel P).sameLoc w r && decide (rank w < rank r)

/-- Canonical SC execution of `P` induced by a linearisation `rank` that puts init events
first and extends `po`. -/
private def mkSCExec (P : Prog) (rank : Fin (layout P).length → Nat) : Exec (layout P).length where
  ev i :=
    if ((skel P).ev i).isRead then
      { (skel P).ev i with
        val := match maxByRank rank (earlierWrites P rank i) with
          | some w => ((skel P).ev w).val
          | none => 0 }
    else (skel P).ev i
  po := (skel P).po
  rf w r := ((skel P).ev r).isRead && (maxByRank rank (earlierWrites P rank r) == some w)
  co w1 w2 :=
    ((skel P).ev w1).isWrite && ((skel P).ev w2).isWrite &&
      (skel P).sameLoc w1 w2 && decide (rank w1 < rank w2)

private theorem mkSCExec_kind (P : Prog) (rank : Fin (layout P).length → Nat)
    (i : Fin (layout P).length) : ((mkSCExec P rank).ev i).kind = ((skel P).ev i).kind := by
  simp only [mkSCExec]; split <;> rfl

private theorem mkSCExec_tid (P : Prog) (rank : Fin (layout P).length → Nat)
    (i : Fin (layout P).length) : ((mkSCExec P rank).ev i).tid = ((skel P).ev i).tid := by
  simp only [mkSCExec]; split <;> rfl

private theorem mkSCExec_loc (P : Prog) (rank : Fin (layout P).length → Nat)
    (i : Fin (layout P).length) : ((mkSCExec P rank).ev i).loc = ((skel P).ev i).loc := by
  simp only [mkSCExec]; split <;> rfl

private theorem mkSCExec_isInit (P : Prog) (rank : Fin (layout P).length → Nat)
    (i : Fin (layout P).length) : ((mkSCExec P rank).ev i).isInit = ((skel P).ev i).isInit := by
  unfold Event.isInit; rw [mkSCExec_kind]

private theorem mkSCExec_isRead (P : Prog) (rank : Fin (layout P).length → Nat)
    (i : Fin (layout P).length) : ((mkSCExec P rank).ev i).isRead = ((skel P).ev i).isRead := by
  unfold Event.isRead; rw [mkSCExec_kind]

private theorem mkSCExec_isWrite (P : Prog) (rank : Fin (layout P).length → Nat)
    (i : Fin (layout P).length) : ((mkSCExec P rank).ev i).isWrite = ((skel P).ev i).isWrite := by
  unfold Event.isWrite; rw [mkSCExec_kind]

private theorem mkSCExec_sameLoc (P : Prog) (rank : Fin (layout P).length → Nat)
    (a b : Fin (layout P).length) : (mkSCExec P rank).sameLoc a b = (skel P).sameLoc a b := by
  unfold Exec.sameLoc; rw [mkSCExec_loc, mkSCExec_loc]

private theorem mkSCExec_execOf (P : Prog) (rank : Fin (layout P).length → Nat) :
    ExecOf P (mkSCExec P rank) := by
  have hget : ∀ i : Fin (layout P).length, (layout P).getD i.val default = (layout P)[i] := by
    intro i; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]; rfl
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; rw [mkSCExec_kind, hget]; rfl
  · intro i; rw [mkSCExec_tid, hget]; rfl
  · intro i; rw [mkSCExec_loc, hget]; rfl
  · intro i hnr
    rw [mkSCExec_isRead] at hnr
    simp only [mkSCExec, hnr, Bool.false_eq_true, ↓reduceIte, hget]; rfl
  · intro a b
    change (skel P).po a b = ((mkSCExec P rank).sameThread a b && decide (a.val < b.val))
    unfold Exec.sameThread
    rw [mkSCExec_isInit, mkSCExec_isInit, mkSCExec_tid, mkSCExec_tid]
    rfl

private theorem mkSCExec_wf_and_sc (P : Prog) (rank : Fin (layout P).length → Nat)
    (hinj : ∀ i j, rank i = rank j → i = j)
    (hinit_lt : ∀ i j, ((skel P).ev i).isInit = true → ((skel P).ev j).isInit = false →
      rank i < rank j)
    (hpo_lt : ∀ i j, (skel P).po i j = true → rank i < rank j) :
    (mkSCExec P rank).Wf ∧ (mkSCExec P rank).SCConsistent ∧
      ∀ a b, (mkSCExec P rank).scRel a b = true → rank a < rank b := by
  let Y := mkSCExec P rank
  have hY : ExecOf P Y := mkSCExec_execOf P rank
  have hrf_mem : ∀ w r, Y.rf w r = true →
      ((skel P).ev r).isRead = true ∧ maxByRank rank (earlierWrites P rank r) = some w ∧
      ((skel P).ev w).isWrite = true ∧ (skel P).sameLoc w r = true ∧ rank w < rank r := by
    intro w r hrf
    simp only [Y, mkSCExec, Bool.and_eq_true, beq_iff_eq] at hrf
    have hmem := maxByRank_mem rank hrf.2
    simp only [earlierWrites, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hmem
    exact ⟨hrf.1, hrf.2, hmem.2.1.1, hmem.2.1.2, hmem.2.2⟩
  have hsc_lt : ∀ a b, Y.scRel a b = true → rank a < rank b := by
    intro a b hab
    rcases Y.scRel_cases hab with h | h | h | h
    · exact hpo_lt a b h
    · exact (hrf_mem a b h).2.2.2.2
    · simp only [Y, mkSCExec, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    · obtain ⟨w, hwa, hwb⟩ := Y.fr_iff.mp h
      obtain ⟨hra, hmax, _, hslwa, _⟩ := hrf_mem w a hwa
      simp only [Y, mkSCExec, Bool.and_eq_true, decide_eq_true_eq] at hwb
      obtain ⟨⟨⟨_, hwb_w⟩, hslwb⟩, hrwb⟩ := hwb
      have hslba : (skel P).sameLoc b a = true :=
        (skel P).sameLoc_trans ((skel P).sameLoc_symm hslwb) hslwa
      by_cases hlt : rank b < rank a
      · have hbmem : b ∈ earlierWrites P rank a := by
          simp [earlierWrites, List.mem_finRange, hwb_w, hslba, hlt]
        have hle := maxByRank_ge rank hmax b hbmem
        omega
      · by_cases heq : rank b = rank a
        · have hab_eq := hinj b a heq
          subst hab_eq
          revert hwb_w hra; simp only [Event.isWrite, Event.isRead]
          cases ((skel P).ev b).kind <;> simp
        · omega
  have hsc : Y.SCConsistent := by
    have hpath : ∀ a b, Rel.Path Y.scRel a b → rank a < rank b := by
      intro a b h
      induction h with
      | single hab => exact hsc_lt _ _ hab
      | tail _ hbc ih => exact Nat.lt_trans ih (hsc_lt _ _ hbc)
    intro a ha
    exact Nat.lt_irrefl _ (hpath a a ha)
  refine ⟨⟨hY.poIrrefl, hY.poTrans, hY.poWithinThread, hY.poTotal,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hsc, hsc_lt⟩
  · -- RfSameLoc
    intro a b hab; rw [mkSCExec_sameLoc]; exact (hrf_mem a b hab).2.2.2.1
  · -- RfKinds
    intro a b hab
    rw [mkSCExec_isWrite, mkSCExec_isRead]
    exact ⟨(hrf_mem a b hab).2.2.1, (hrf_mem a b hab).1⟩
  · -- RfSameVal
    intro a b hab
    obtain ⟨hrb, hmax, hwa, _, _⟩ := hrf_mem a b hab
    have hna : ((skel P).ev a).isRead = false := by
      revert hwa; simp only [Event.isWrite, Event.isRead]; cases ((skel P).ev a).kind <;> simp
    simp only [mkSCExec, hna, Bool.false_eq_true, ↓reduceIte, hrb, hmax]
  · -- RfTotal
    intro b hrb
    rw [mkSCExec_isRead] at hrb
    have hbi : ((skel P).ev b).isInit = false := by
      revert hrb; simp only [Event.isRead, Event.isInit]; cases ((skel P).ev b).kind <;> simp
    have hloc := layout_loc_lt_numLocs P b
    have hlt : ((skel P).ev b).loc < (layout P).length :=
      Nat.lt_of_lt_of_le hloc (numLocs_le_layout_length P)
    let w0 : Fin (layout P).length := ⟨((skel P).ev b).loc, hlt⟩
    have hw0_eq : (skel P).ev w0 = Event.initW ((skel P).ev b).loc :=
      layout_getElem_lt_numLocs P _ hloc hlt
    have hw0_init : ((skel P).ev w0).isInit = true := by simp [hw0_eq, Event.initW, Event.isInit]
    have hw0_w : ((skel P).ev w0).isWrite = true := by simp [hw0_eq, Event.initW, Event.isWrite]
    have hw0_loc : (skel P).sameLoc w0 b = true := by
      simp [Exec.sameLoc, hw0_eq, Event.initW]
    have hw0_rank : rank w0 < rank b := hinit_lt w0 b hw0_init hbi
    have hw0_mem : w0 ∈ earlierWrites P rank b := by
      simp [earlierWrites, List.mem_finRange, hw0_w, hw0_loc, hw0_rank]
    obtain ⟨w, hw⟩ := maxByRank_isSome rank hw0_mem
    exact ⟨w, by simp [mkSCExec, hrb, hw]⟩
  · -- RfFunctional
    intro a a' b ha ha'
    have h1 := (hrf_mem a b ha).2.1
    have h2 := (hrf_mem a' b ha').2.1
    rw [h1] at h2; injection h2
  · -- CoKinds
    intro a b hab
    simp only [mkSCExec, Bool.and_eq_true, decide_eq_true_eq] at hab
    rw [mkSCExec_isWrite, mkSCExec_isWrite, mkSCExec_sameLoc]
    exact ⟨hab.1.1.1, hab.1.1.2, hab.1.2⟩
  · -- CoIrrefl
    intro a; simp [mkSCExec]
  · -- CoTrans
    intro a b c hab hbc
    simp only [mkSCExec, Bool.and_eq_true, decide_eq_true_eq] at hab hbc ⊢
    exact ⟨⟨⟨hab.1.1.1, hbc.1.1.2⟩, (skel P).sameLoc_trans hab.1.2 hbc.1.2⟩,
      Nat.lt_trans hab.2 hbc.2⟩
  · -- CoTotal
    intro a b hne ha hb hsl
    rw [mkSCExec_isWrite] at ha hb
    rw [mkSCExec_sameLoc] at hsl
    have hrne : rank a ≠ rank b := fun h => hne (hinj a b h)
    simp only [mkSCExec, ha, hb, hsl, (skel P).sameLoc_symm hsl, Bool.and_self, Bool.true_and,
      decide_eq_true_eq]
    omega
  · -- CoInitFirst
    intro a b hai hwb hsl hne
    rw [mkSCExec_isInit] at hai
    rw [mkSCExec_isWrite] at hwb
    rw [mkSCExec_sameLoc] at hsl
    have hwa : ((skel P).ev a).isWrite = true := by
      revert hai; simp only [Event.isInit, Event.isWrite]; cases ((skel P).ev a).kind <;> simp
    have hbi : ((skel P).ev b).isInit = false := by
      cases hb : ((skel P).ev b).isInit with
      | false => rfl
      | true =>
        exfalso
        have ha_lt := (layout_isInit_iff P a).mp hai
        have hb_lt := (layout_isInit_iff P b).mp hb
        have ha_eq := layout_getElem_lt_numLocs P a.val ha_lt a.isLt
        have hb_eq := layout_getElem_lt_numLocs P b.val hb_lt b.isLt
        simp only [Exec.sameLoc, skel, beq_iff_eq] at hsl
        change ((layout P)[a.val]).loc = ((layout P)[b.val]).loc at hsl
        rw [ha_eq, hb_eq] at hsl
        simp only [Event.initW] at hsl
        exact hne (Fin.ext hsl)
    simp only [mkSCExec, hwa, hwb, hsl, Bool.and_self, Bool.true_and, decide_eq_true_eq]
    exact hinit_lt a b hai hbi

/-- Bucket function placing `a` immediately before `b` in the linear order. -/
private def adjBucket (P : Prog) (a b i : Fin (layout P).length) : Nat :=
  let S := skel P
  if (S.ev i).isInit then 0
  else if (S.ev i).tid = (S.ev a).tid then
    if i.val < a.val then 1 else if i.val = a.val then 3 else 5
  else if (S.ev i).tid = (S.ev b).tid then
    if i.val < b.val then 2 else if i.val = b.val then 4 else 6
  else 7

private def adjRank (P : Prog) (a b i : Fin (layout P).length) : Nat :=
  adjBucket P a b i * ((layout P).length + 1) + i.val

/-- **Every conflict of a straight-line program is an `hb`-race in some SC execution.** For
every program `P` and every conflicting pair `(a, b)` of its skeleton, some well-formed
SC-consistent execution `Y` of `P` leaves `a` and `b` unordered by `hb = (po ∪ rf)⁺`. The
execution is the sequential interleaving that runs the initialisation writes, then the
`po`-prefixes of both threads, then the two accesses adjacently (the write second), then the
rest; each read reads the latest earlier write to its location. -/
theorem exists_sc_execution_hb_unordered_of_conflict (P : Prog)
    {a b : Fin (layout P).length} (hc : (skel P).Conflict a b) :
    ∃ Y : Exec (layout P).length,
      ExecOf P Y ∧ Y.Wf ∧ Y.SCConsistent ∧ Y.Conflict a b ∧ ¬ Y.HB a b ∧ ¬ Y.HB b a := by
  -- Helper when the second element is a write.
  have core : ∀ {u v : Fin (layout P).length},
      (skel P).Conflict u v → ((skel P).ev v).isWrite = true →
      ∃ Y : Exec (layout P).length,
        ExecOf P Y ∧ Y.Wf ∧ Y.SCConsistent ∧ ¬ Y.HB u v ∧ ¬ Y.HB v u := by
    intro u v hcu hvw
    obtain ⟨_, _, hui, hvi, htid, _, _⟩ := hcu
    let N := (layout P).length
    let rank := adjRank P u v
    have h_step : ∀ {b1 b2 x y : Nat}, b1 < b2 → x < N + 1 →
        b1 * (N + 1) + x < b2 * (N + 1) + y := by
      intro b1 b2 x y hb hx
      have h1 : (b1 + 1) * (N + 1) ≤ b2 * (N + 1) := Nat.mul_le_mul_right (N + 1) hb
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    have hinj : ∀ i j, rank i = rank j → i = j := by
      intro i j hij
      simp only [rank, adjRank] at hij
      have hi : i.val < (layout P).length + 1 := Nat.lt_succ_of_lt i.isLt
      have hj : j.val < (layout P).length + 1 := Nat.lt_succ_of_lt j.isLt
      have hmod : i.val = j.val := by
        have h1 := congrArg (· % ((layout P).length + 1)) hij
        simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h1
      exact Fin.ext hmod
    have hinit_lt : ∀ i j, ((skel P).ev i).isInit = true → ((skel P).ev j).isInit = false →
        rank i < rank j := by
      intro i j hi hj
      have hbi : adjBucket P u v i = 0 := by simp [adjBucket, hi]
      have hbj : 0 < adjBucket P u v j := by
        simp only [adjBucket, hj, Bool.false_eq_true, ↓reduceIte]
        repeat (first | split | omega)
      simp only [rank, adjRank, hbi]
      exact h_step hbj (Nat.lt_succ_of_lt i.isLt)
    have hpo_lt : ∀ i j, (skel P).po i j = true → rank i < rank j := by
      intro i j hij
      simp only [skel, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hij
      obtain ⟨⟨⟨hi, hj⟩, hteq⟩, hlt⟩ := hij
      change ((skel P).ev i).isInit = false at hi
      change ((skel P).ev j).isInit = false at hj
      change ((skel P).ev i).tid = ((skel P).ev j).tid at hteq
      have hble : adjBucket P u v i ≤ adjBucket P u v j := by
        simp only [adjBucket, hi, hj, Bool.false_eq_true, ↓reduceIte, hteq]
        by_cases h1 : ((skel P).ev j).tid = ((skel P).ev u).tid
        · simp only [h1, ↓reduceIte]
          split <;> split <;> (try split) <;> (try split) <;> omega
        · simp only [h1, ↓reduceIte]
          by_cases h2 : ((skel P).ev j).tid = ((skel P).ev v).tid
          · simp only [h2, ↓reduceIte]
            split <;> split <;> (try split) <;> (try split) <;> omega
          · simp only [h2, ↓reduceIte]; exact Nat.le_refl _
      simp only [rank, adjRank]
      rcases Nat.eq_or_lt_of_le hble with hbeq | hblt
      · rw [hbeq]; omega
      · exact h_step hblt (Nat.lt_succ_of_lt i.isLt)
    have hbu : adjBucket P u v u = 3 := by simp [adjBucket, hui]
    have hbv : adjBucket P u v v = 4 := by simp [adjBucket, hvi, Ne.symm htid]
    have huv_lt : rank u < rank v := by
      simp only [rank, adjRank, hbu, hbv]
      exact h_step (by omega) (Nat.lt_succ_of_lt u.isLt)
    have hno_mid : ∀ c : Fin N, ¬ (rank u < rank c ∧ rank c < rank v) := by
      intro c ⟨huc, hcv⟩
      have hbc : adjBucket P u v c ≠ 3 ∧ adjBucket P u v c ≠ 4 := by
        constructor
        · intro h3
          have hcu_eq : c = u := by
            simp only [adjBucket] at h3
            split at h3
            · omega
            · split at h3
              · split at h3
                · omega
                · split at h3
                  · exact Fin.ext (by assumption)
                  · omega
              · split at h3
                · split at h3
                  · omega
                  · split at h3 <;> omega
                · omega
          subst hcu_eq; exact Nat.lt_irrefl _ huc
        · intro h4
          have hcv_eq : c = v := by
            simp only [adjBucket] at h4
            split at h4
            · omega
            · split at h4
              · split at h4
                · omega
                · split at h4 <;> omega
              · split at h4
                · split at h4
                  · omega
                  · split at h4
                    · exact Fin.ext (by assumption)
                    · omega
                · omega
          subst hcv_eq; exact Nat.lt_irrefl _ hcv
      simp only [rank, adjRank, hbu, hbv] at huc hcv
      by_cases hle2 : adjBucket P u v c < 3
      · have hcu' : adjBucket P u v c * (N + 1) + c.val < 3 * (N + 1) + u.val :=
          h_step hle2 (Nat.lt_succ_of_lt c.isLt)
        exact Nat.lt_asymm huc hcu'
      · have hgt4 : 4 < adjBucket P u v c := by omega
        have hvc' : 4 * (N + 1) + v.val < adjBucket P u v c * (N + 1) + c.val :=
          h_step hgt4 (Nat.lt_succ_of_lt v.isLt)
        exact Nat.lt_asymm hcv hvc'
    let Y := mkSCExec P rank
    obtain ⟨hYwf, hYsc, hsc_lt⟩ := mkSCExec_wf_and_sc P rank hinj hinit_lt hpo_lt
    have hhb_lt : ∀ x y, Y.HB x y → rank x < rank y := by
      intro x y h
      induction h with
      | single hxy =>
        simp only [Exec.hbRel, Bool.or_eq_true] at hxy
        rcases hxy with hxy | hxy
        · exact hsc_lt _ _ (by show Y.scRel _ _ = true; simp [Exec.scRel, hxy])
        · exact hsc_lt _ _ (by show Y.scRel _ _ = true; simp [Exec.scRel, hxy])
      | tail _ hcy ih =>
        simp only [Exec.hbRel, Bool.or_eq_true] at hcy
        rcases hcy with hcy | hcy
        · exact Nat.lt_trans ih (hsc_lt _ _ (by show Y.scRel _ _ = true; simp [Exec.scRel, hcy]))
        · exact Nat.lt_trans ih (hsc_lt _ _ (by show Y.scRel _ _ = true; simp [Exec.scRel, hcy]))
    refine ⟨Y, mkSCExec_execOf P rank, hYwf, hYsc, ?_, ?_⟩
    · intro hhb
      cases hhb with
      | single huv =>
        simp only [Exec.hbRel, Bool.or_eq_true] at huv
        rcases huv with hpo | hrf
        · have hst := hYwf.2.2.1 u v hpo
          simp only [Exec.sameThread, Bool.and_eq_true, beq_iff_eq] at hst
          rw [mkSCExec_tid, mkSCExec_tid] at hst
          exact htid hst.2
        · have hvr := (hYwf.2.2.2.2.2.1 u v hrf).2
          rw [mkSCExec_isRead] at hvr
          revert hvw hvr; simp only [Event.isWrite, Event.isRead]
          cases ((skel P).ev v).kind <;> simp
      | @tail c _ huc hcv =>
        have h1 : rank u < rank c := hhb_lt u c huc
        have h2 : rank c < rank v := hhb_lt c v (Rel.Path.single hcv)
        exact hno_mid c ⟨h1, h2⟩
    · intro hhb
      have := hhb_lt v u hhb
      omega
  rcases hc.2.2.2.2.2.2 with haw | hbw
  · have hcsym : (skel P).Conflict b a :=
      ⟨hc.2.1, hc.1, hc.2.2.2.1, hc.2.2.1, Ne.symm hc.2.2.2.2.1, hc.2.2.2.2.2.1.symm, Or.inr haw⟩
    obtain ⟨Y, hY, hYwf, hYsc, hba, hab⟩ := core hcsym haw
    have hYc : Y.Conflict a b := by
      obtain ⟨_, hk, ht, hl⟩ := hY.skel_facts
      exact (Exec.conflict_congr hk ht hl a b).mpr hc
    exact ⟨Y, hY, hYwf, hYsc, hYc, hab, hba⟩
  · obtain ⟨Y, hY, hYwf, hYsc, hab, hba⟩ := core hc hbw
    have hYc : Y.Conflict a b := by
      obtain ⟨_, hk, ht, hl⟩ := hY.skel_facts
      exact (Exec.conflict_congr hk ht hl a b).mpr hc
    exact ⟨Y, hY, hYwf, hYsc, hYc, hab, hba⟩

end Construction

/-! ## The characterizations -/

/-- **`hb`-race freedom is degenerate for straight-line programs.** Every well-formed
SC-consistent execution of `P` orders each conflicting pair by `hb = (po ∪ rf)⁺` if and only
if `P` has no conflicting pair of accesses at all. -/
theorem hbRaceFree_sc_executions_iff_noConflict (P : Prog) :
    (∀ (m : Nat) (Y : Exec m), ExecOf P Y → Y.Wf → Y.SCConsistent →
        ∀ a b, Y.Conflict a b → Y.HB a b ∨ Y.HB b a) ↔
      (∀ a b, ¬ (skel P).Conflict a b) := by
  constructor
  · intro h a b hc
    obtain ⟨Y, hY, hYwf, hYsc, hYc, hnab, hnba⟩ :=
      exists_sc_execution_hb_unordered_of_conflict P hc
    rcases h _ Y hY hYwf hYsc a b hYc with h1 | h2
    · exact hnab h1
    · exact hnba h2
  · intro h m Y hY _ _ a b hc
    exact absurd hc (hY.noConflict_of_skel h a b)

/-- **Race freedom with the both-sides exemption is a static condition.** Every well-formed
SC-consistent execution of `P` is `RaceFree` (conflicting accesses `hb`-ordered or both
satisfying `NoUnfencedWRIncident`) if and only if `P.ConflictsWRFenced`; `hb` plays no role. -/
theorem raceFree_sc_executions_iff_conflictsWRFenced (P : Prog) :
    (∀ (m : Nat) (Y : Exec m), ExecOf P Y → Y.Wf → Y.SCConsistent → Y.RaceFree) ↔
      P.ConflictsWRFenced := by
  unfold Prog.ConflictsWRFenced
  constructor
  · intro hdrf a b hc
    obtain ⟨Y, hY, hYwf, hYsc, hYc, hnab, hnba⟩ :=
      exists_sc_execution_hb_unordered_of_conflict P hc
    have hrf := hdrf _ Y hY hYwf hYsc a b
    have hf : Y.NoUnfencedWRIncident a ∧ Y.NoUnfencedWRIncident b :=
      Classical.byContradiction fun hnf => hrf ⟨hYc, hnab, hnba, hnf⟩
    obtain ⟨hpo, hk, _, _⟩ := hY.skel_facts
    exact ⟨(Exec.noUnfencedWRIncident_congr hpo hk a).mp hf.1,
      (Exec.noUnfencedWRIncident_congr hpo hk b).mp hf.2⟩
  · intro hstat m Y hY _ _ a b ⟨hc, _, _, hnf⟩
    have hn := hY.length; subst hn
    obtain ⟨hpo, hk, ht, hl⟩ := hY.skel_facts
    have hcs := (Exec.conflict_congr hk ht hl a b).mp hc
    obtain ⟨hfa, hfb⟩ := hstat a b hcs
    exact hnf ⟨(Exec.noUnfencedWRIncident_congr hpo hk a).mpr hfa,
      (Exec.noUnfencedWRIncident_congr hpo hk b).mpr hfb⟩

/-- **Race freedom with the either-side exemption is a static condition.** Every well-formed
SC-consistent execution of `P` is `RaceFreeEither` if and only if
`P.ConflictsWRFencedEither`. -/
theorem raceFreeEither_sc_executions_iff_conflictsWRFencedEither (P : Prog) :
    (∀ (m : Nat) (Y : Exec m), ExecOf P Y → Y.Wf → Y.SCConsistent → Y.RaceFreeEither) ↔
      P.ConflictsWRFencedEither := by
  unfold Prog.ConflictsWRFencedEither
  constructor
  · intro hdrf a b hc
    obtain ⟨Y, hY, hYwf, hYsc, hYc, hnab, hnba⟩ :=
      exists_sc_execution_hb_unordered_of_conflict P hc
    have hrf := hdrf _ Y hY hYwf hYsc a b
    have hf : Y.NoUnfencedWRIncident a ∨ Y.NoUnfencedWRIncident b :=
      Classical.byContradiction fun hnf => hrf ⟨hYc, hnab, hnba, hnf⟩
    obtain ⟨hpo, hk, _, _⟩ := hY.skel_facts
    rcases hf with h1 | h2
    · exact Or.inl ((Exec.noUnfencedWRIncident_congr hpo hk a).mp h1)
    · exact Or.inr ((Exec.noUnfencedWRIncident_congr hpo hk b).mp h2)
  · intro hstat m Y hY _ _ a b ⟨hc, _, _, hnf⟩
    exact hnf (hY.fencedSide_of_skel hstat a b hc)

/-- **The both-sides static condition implies shared-location fencing.** If
`P.ConflictsWRFenced`, then every candidate execution of `P` fences every `po` write→read
pair whose write is to a location accessed (excluding initialisation) by two or more
threads. -/
theorem fenceBetweenSharedWR_of_conflictsWRFenced (P : Prog) (h : P.ConflictsWRFenced)
    {n : Nat} (X : Exec n) (hX : ExecOf P X) : X.FenceBetweenSharedWR := by
  have hn := hX.length; subst hn
  obtain ⟨hpo, hk, ht, hl⟩ := hX.skel_facts
  intro a b hab hwa hrb hsh
  have hst := hX.poWithinThread a b hab
  simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst
  have hai : (X.ev a).isInit = false := hst.1.1
  have ha_acc : (X.ev a).isAccess = true := by
    revert hwa; simp only [Event.isWrite, Event.isAccess, Event.isFence]
    cases (X.ev a).kind <;> simp
  have hex : ∃ c : Fin (layout P).length, X.Conflict a c :=
    Classical.byContradiction fun hno =>
      hsh fun u v hu hv hui hvi hlu hlv =>
        let htu : (X.ev u).tid = (X.ev a).tid :=
          Classical.byContradiction fun hne =>
            hno ⟨u, ha_acc, hu, hai, hui, Ne.symm hne, hlu.symm, Or.inl hwa⟩
        let htv : (X.ev v).tid = (X.ev a).tid :=
          Classical.byContradiction fun hne =>
            hno ⟨v, ha_acc, hv, hai, hvi, Ne.symm hne, hlv.symm, Or.inl hwa⟩
        htu.trans htv.symm
  obtain ⟨c, hac⟩ := hex
  have hcs := (Exec.conflict_congr hk ht hl a c).mp hac
  have hfa : X.NoUnfencedWRIncident a :=
    (Exec.noUnfencedWRIncident_congr hpo hk a).mpr (h a c hcs).1
  exact hfa.1 hwa b hab hrb

/-- **SC on TSO from the both-sides static condition** (a corollary of shared-location
fencing soundness and fence erasure). If `P.ConflictsWRFenced`, then every candidate execution
of `P` whose `rf` goes from writes to reads of the same location, whose `co` relates
same-location writes, and which is TSO-consistent, is SC-consistent. -/
theorem scConsistent_of_tso_of_conflictsWRFenced (P : Prog) (h : P.ConflictsWRFenced)
    {n : Nat} (X : Exec n) (hX : ExecOf P X) (hrfl : X.RfSameLoc) (hrfk : X.RfKinds)
    (hcok : X.CoKinds) (htso : X.TSOConsistent) : X.SCConsistent :=
  scConsistent_of_scConsistentErased X hX.poIrrefl hX.poTrans hrfk hcok
    (scConsistentErased_of_tso_of_fenceBetweenSharedWR X hX.poTrans hX.poWithinThread
      hX.poTotal hrfl hcok (fenceBetweenSharedWR_of_conflictsWRFenced P h X hX) htso.1 htso.2)

end Toy.WMM
