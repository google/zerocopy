import ToySendSync.Characterize

/-!
# Results: definitional link, structural soundness, primitives, false rules,
unsafe-impl obligations, and the checker/semantics gap
-/

namespace Toy.SendSync

/-! ## Examples for the core definitions -/

/-- Positive example of `Race`: an unprotected write races with an unprotected read. -/
theorem race_example_write_read : Race [rootEv .wr] [rootEv .rd] :=
  ⟨rootEv .wr, by simp, rootEv .rd, by simp, by decide, compatible_nil_nil⟩

/-- Negative example of `Race`: two reads never race. -/
theorem not_race_example_read_read : ¬ Race [rootEv .rd] [rootEv .rd] :=
  not_race_of_no_conflict (by decide)

/-- Negative example of `Race`: two atomic accesses never race. -/
theorem not_race_example_atomic_atomic : ¬ Race [rootEv .atomic] [rootEv .atomic] :=
  not_race_of_no_conflict (by decide)

/-- Negative example of `Race`: two writes each made under a fresh acquisition of the
same lock are never simultaneously enabled. -/
theorem not_race_example_locked_writes :
    ¬ Race [rootEv .wr [.held [] .fresh]] [rootEv .wr [.held [] .fresh]] := by
  rintro ⟨e₁, h₁, e₂, h₂, _, hc⟩
  rw [List.mem_singleton.mp h₁, List.mem_singleton.mp h₂] at hc
  exact not_compatible_fresh_fresh [] hc

/-- Positive example of `Race`: a lock-protected write races with an unprotected write. -/
theorem race_example_locked_vs_unlocked : Race [rootEv .wr [.held [] .fresh]] [rootEv .wr] :=
  ⟨_, List.mem_singleton.mpr rfl, _, List.mem_singleton.mpr rfl, by decide,
    compatible_single_nil _⟩

/-- Positive example of `Compatible`: both threads hold handles to one allocation. -/
theorem compatible_example_via_via : Compatible [.via []] [.via []] := compatible_via_via []

/-- Negative example of `Compatible`: the other thread cannot be the unique holder of an
allocation the origin thread holds a handle to. -/
theorem not_compatible_example_uniq_via : ¬ Compatible [.uniq []] [.via []] :=
  not_compatible_uniq_via []

/-- Positive example of `NoForeignRelease`: a list without releases. -/
theorem nfr_example : NoForeignRelease .other [rootEv .rd, rootEv .wr] := nfr_cellRoot _

/-- Positive example of `NoForeignRelease`: releasing an acquisition the executing thread
made itself (a `fresh` acquisition). -/
theorem nfr_example_fresh_release : NoForeignRelease .other [rootEv .rel [.held [] .fresh]] :=
  nfr_mutexRoot _

/-- Positive example of `NoForeignRelease`: a `fresh` release of the lock at `[0]` whose
precondition is that a guard holds the lock at `[]`; only the claim on the released lock
(the event's own location) names the released acquisition. -/
theorem nfr_example_precondition :
    NoForeignRelease .other [⟨.rel, [0], [.held [] (.guard []), .held [0] .fresh]⟩] := by
  intro e he a _ hm
  rw [List.mem_singleton.mp he] at hm
  simp only [List.mem_cons, Claim.held.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨h, _⟩ | ⟨_, rfl⟩
  · cases h
  · rfl

/-- Negative example of `NoForeignRelease`: the other thread releasing a guard's
acquisition. -/
theorem not_nfr_example : ¬ NoForeignRelease .other [rootEv .rel [.held [] (.guard [])]] :=
  not_nfr_guardRoot

/-- Negative example of `NoForeignRelease`: releasing the acquisition of a guard at `[0]`
while holding the lock at `[]` by a `fresh` acquisition is still a foreign release. -/
theorem not_nfr_example_placed :
    ¬ NoForeignRelease .other [⟨.rel, [0], [.held [] .fresh, .held [0] (.guard [0])]⟩] := by
  intro h
  have := h _ (List.mem_singleton.mpr rfl) (.guard [0]) rfl (by simp)
  cases this

/-- Example of `View.expose`: a read-only view keeps the non-atomic reads and drops
writes, atomic read-modify-writes and releases. -/
theorem expose_readOnly_example :
    View.expose .readOnly [rootEv .rd, rootEv .wr, rootEv .atomic, rootEv .rel] = [rootEv .rd] :=
  rfl

/-- Example of `View.expose`: a read-only view drops a read that runs under an acquisition
made by the executing thread (a `fresh` claim) and keeps a read under a guard's
acquisition. -/
theorem expose_readOnly_example_acquires :
    View.expose .readOnly [rootEv .rd [.held [] .fresh], rootEv .rd [.held [] (.guard [])]] =
      [rootEv .rd [.held [] (.guard [])]] :=
  rfl

/-- Example of `View.expose`: a read-only view exposes nothing of the shared footprint of
`Mutex<&Cell<plain>>`, since every access to the content runs under a `fresh`
acquisition and the release is not a read. -/
theorem expose_readOnly_mutex_example :
    View.expose .readOnly (fp (.mutex (.ref (.cell .plain)))).shr = [] :=
  rfl

/-- Positive example of `NoForeignRelease` that holds vacuously: a release event without a
`held` claim on its own location names no acquisition, so release affinity does not
constrain it; it is a negative example of `RelNamesAcq`. -/
theorem nfr_example_unnamed_release :
    NoForeignRelease .other [rootEv .rel []] ∧ ¬ RelNamesAcq [rootEv .rel []] := by
  refine ⟨fun e he a _ hm => ?_, fun h => ?_⟩
  · rw [List.mem_singleton.mp he] at hm
    cases hm
  · obtain ⟨a, ha⟩ := h _ (List.mem_singleton.mpr rfl) rfl
    cases ha

/-- Positive example of `RelNamesAcq`: the release of a guard's acquisition. -/
theorem relNamesAcq_example : RelNamesAcq [rootEv .rel [.held [] (.guard [])]] := by
  intro e he _
  rw [List.mem_singleton.mp he]
  exact ⟨.guard [], List.mem_singleton.mpr rfl⟩

theorem relNamesAcq_append {L₁ L₂ : List Ev} (h₁ : RelNamesAcq L₁) (h₂ : RelNamesAcq L₂) :
    RelNamesAcq (L₁ ++ L₂) := by
  intro e he hk
  rcases List.mem_append.mp he with h | h
  · exact h₁ e h hk
  · exact h₂ e h hk

theorem relNamesAcq_place (r : List Claim) (i : Nat) {L : List Ev} (h : RelNamesAcq L) :
    RelNamesAcq (place r i L) := by
  intro e' he' hk
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
  obtain ⟨a, ha⟩ := h e he hk
  exact ⟨a.reloc i, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨.held e.loc a, ha, rfl⟩))⟩

theorem relNamesAcq_of_no_rel {L : List Ev} (h : ∀ e ∈ L, e.kind ≠ .rel) : RelNamesAcq L :=
  fun e he hk => absurd hk (h e he)

/-- Every release event of every footprint names the acquisition it releases, so on the
footprints of the model `NoForeignRelease` never holds vacuously for a release
(compare `nfr_example_unnamed_release`). -/
theorem fp_relNamesAcq (T : Ty) :
    RelNamesAcq (fp T).own ∧ RelNamesAcq (fp T).shr ∧ RelNamesAcq (fp T).alias := by
  induction T with
  | plain => exact ⟨relNamesAcq_of_no_rel (by decide), relNamesAcq_of_no_rel (by decide),
      relNamesAcq_of_no_rel (by decide)⟩
  | cell t ih =>
    obtain ⟨ho, _, ha⟩ := ih
    have hs := relNamesAcq_append (relNamesAcq_of_no_rel (L := [rootEv .rd, rootEv .wr])
      (by decide)) (relNamesAcq_place [] 0 ho)
    exact ⟨hs, hs, relNamesAcq_place [] 0 ha⟩
  | refCell t ih =>
    obtain ⟨ho, hsh, ha⟩ := ih
    have hs := relNamesAcq_append (relNamesAcq_append (relNamesAcq_of_no_rel
      (L := [rootEv .rd, rootEv .wr]) (by decide)) (relNamesAcq_place [] 0 hsh))
      (relNamesAcq_place [.held [] .fresh] 0 ho)
    exact ⟨relNamesAcq_append (relNamesAcq_place [] 0 ho) hs, hs, relNamesAcq_place [] 0 ha⟩
  | rc t ih =>
    obtain ⟨ho, hs, ha⟩ := ih
    have hh := relNamesAcq_append (relNamesAcq_append (relNamesAcq_of_no_rel
      (L := [rootEv .rd [.via []], rootEv .wr [.via []]]) (by decide))
      (relNamesAcq_place [.via []] 0 hs)) (relNamesAcq_place [.uniq []] 0 ho)
    exact ⟨hh, hh, relNamesAcq_append hh (relNamesAcq_place [] 0 ha)⟩
  | arc t ih =>
    obtain ⟨ho, hs, ha⟩ := ih
    have hh := relNamesAcq_append (relNamesAcq_append (relNamesAcq_of_no_rel
      (L := [rootEv .atomic [.via []]]) (by decide))
      (relNamesAcq_place [.via []] 0 hs)) (relNamesAcq_place [.uniq []] 0 ho)
    exact ⟨hh, hh, relNamesAcq_append hh (relNamesAcq_place [] 0 ha)⟩
  | mutex t ih =>
    obtain ⟨ho, _, ha⟩ := ih
    have hrel : RelNamesAcq [rootEv .rel [.held [] .fresh]] := by
      intro e he _
      rw [List.mem_singleton.mp he]
      exact ⟨.fresh, List.mem_singleton.mpr rfl⟩
    have hs := relNamesAcq_append (relNamesAcq_place [.held [] .fresh] 0 ho) hrel
    exact ⟨relNamesAcq_append (relNamesAcq_place [] 0 ho) hs, hs, relNamesAcq_place [] 0 ha⟩
  | guard t ih =>
    obtain ⟨ho, hs, ha⟩ := ih
    exact ⟨relNamesAcq_append (relNamesAcq_place [.held [] (.guard [])] 0 ho) relNamesAcq_example,
      relNamesAcq_place [.held [] (.guard [])] 0 hs,
      relNamesAcq_append (relNamesAcq_place [.held [] .fresh] 0 ho) (relNamesAcq_place [] 0 ha)⟩
  | box t ih => exact ih
  | ref t ih =>
    obtain ⟨_, hs, ha⟩ := ih
    exact ⟨hs, hs, relNamesAcq_append hs ha⟩
  | refMut t ih => exact ih
  | prod a b iha ihb =>
    exact ⟨relNamesAcq_append (relNamesAcq_place [] 0 iha.1) (relNamesAcq_place [] 1 ihb.1),
      relNamesAcq_append (relNamesAcq_place [] 0 iha.2.1) (relNamesAcq_place [] 1 ihb.2.1),
      relNamesAcq_append (relNamesAcq_place [] 0 iha.2.2) (relNamesAcq_place [] 1 ihb.2.2)⟩
  | sum a b iha ihb =>
    exact ⟨relNamesAcq_append (relNamesAcq_place [] 0 iha.1) (relNamesAcq_place [] 1 ihb.1),
      relNamesAcq_append (relNamesAcq_place [] 0 iha.2.1) (relNamesAcq_place [] 1 ihb.2.1),
      relNamesAcq_append (relNamesAcq_place [] 0 iha.2.2) (relNamesAcq_place [] 1 ihb.2.2)⟩
  | wrap f v u ih =>
    exact ⟨ih.1, fun e he hk => ih.2.1 e (expose_subset v _ e he) hk, ih.2.2⟩

/-- The footprint of `Cell<plain>`: owner and sharer can read and write the cell's
storage and the content; nothing aliases it. -/
theorem fp_cell_plain :
    fp (.cell .plain) =
      ⟨[rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩],
        [rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩], []⟩ := rfl

/-- The footprint of `RefCell<plain>`: the owner reaches the content without the flag; a
shared reference reads and writes the borrow flag, reads the content through a shared
borrow, and reads and writes it under a mutable borrow (claim `held [] .fresh`). -/
theorem fp_refCell_plain :
    fp (.refCell .plain) =
      ⟨[⟨.rd, [0], []⟩, ⟨.wr, [0], []⟩, rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩,
          ⟨.rd, [0], [.held [] .fresh]⟩, ⟨.wr, [0], [.held [] .fresh]⟩],
        [rootEv .rd, rootEv .wr, ⟨.rd, [0], []⟩, ⟨.rd, [0], [.held [] .fresh]⟩,
          ⟨.wr, [0], [.held [] .fresh]⟩], []⟩ := rfl

/-- The shared footprints of `Cell<plain>` and `RefCell<plain>` differ. -/
theorem fp_shr_cell_ne_refCell_plain : (fp (.cell .plain)).shr ≠ (fp (.refCell .plain)).shr := by
  decide

/-- Positive examples of `SemSend`. -/
theorem semSend_examples :
    SemSend .plain ∧ SemSend (.cell .plain) ∧ SemSend (.arc .plain) ∧
      SemSend (.mutex (.cell .plain)) ∧ SemSend (.ref (.mutex (.cell .plain))) :=
  ⟨semSend_plain, (semSend_cell_iff _).mpr semSend_plain,
    (semSend_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩,
    (semSend_mutex_iff _).mpr ((semSend_cell_iff _).mpr semSend_plain),
    (semSync_mutex_iff _).mpr ((semSend_cell_iff _).mpr semSend_plain)⟩

/-- Negative examples of `SemSend`. -/
theorem not_semSend_examples :
    ¬ SemSend (.rc .plain) ∧ ¬ SemSend (.guard .plain) ∧ ¬ SemSend (.ref (.cell .plain)) :=
  ⟨not_semSend_rc _, not_semSend_guard _, not_semSync_cell _⟩

/-- Positive examples of `SemSync`. -/
theorem semSync_examples :
    SemSync .plain ∧ SemSync (.mutex (.cell .plain)) ∧ SemSync (.arc .plain) ∧
      SemSync (.guard .plain) :=
  ⟨semSync_plain, (semSync_mutex_iff _).mpr ((semSend_cell_iff _).mpr semSend_plain),
    (semSync_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩, (semSync_guard_iff _).mpr semSync_plain⟩

/-- Negative examples of `SemSync`. -/
theorem not_semSync_examples :
    ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.refCell .plain) ∧ ¬ SemSync (.rc .plain) :=
  ⟨not_semSync_cell _, not_semSync_refCell _, not_semSync_rc _⟩

/-- Examples of `autoCheck` with the standard table. -/
theorem autoCheck_examples :
    autoCheck stdTable (.arc .plain) = (true, true) ∧
      autoCheck stdTable (.arc (.cell .plain)) = (false, false) ∧
      autoCheck stdTable (.mutex (.cell .plain)) = (true, true) ∧
      autoCheck stdTable (.guard .plain) = (false, true) ∧
      autoCheck stdTable (.ref (.cell .plain)) = (false, false) ∧
      autoCheck stdTable (.wrap (.cell .plain) .readOnly false) = (true, false) ∧
      autoCheck stdTable (.wrap (.cell .plain) .readOnly true) = (true, true) := by
  decide

/-- `OwnReadsRaceFree` is preserved and reflected by a guard: the guard's reads of its
content run under the guard's acquisition, which excludes the other lockers. -/
theorem ownReadsRaceFree_guard_iff (U : Ty) : OwnReadsRaceFree (.guard U) ↔ OwnReadsRaceFree U := by
  unfold OwnReadsRaceFree
  show ¬ Race (View.expose .readOnly
      (place [.held [] (.guard [])] 0 (fp U).own ++ [rootEv .rel [.held [] (.guard [])]]))
      (place [.held [] .fresh] 0 (fp U).own ++ place [] 0 (fp U).alias) ↔ _
  have hrel : View.expose .readOnly [rootEv .rel [.held [] (.guard [])]] = [] := rfl
  rw [expose_readOnly_append, expose_readOnly_place _ rfl, hrel]
  simp only [race_append_left, race_append_right, race_place_guard_nil,
    not_race_place_guard_fresh, race_nil_left, false_or, or_false]

/-- Positive and negative examples of `OwnReadsRaceFree`. -/
theorem ownReadsRaceFree_examples :
    OwnReadsRaceFree .plain ∧ OwnReadsRaceFree (.guard .plain) ∧
      ¬ OwnReadsRaceFree (.ref (.cell .plain)) ∧ ¬ OwnReadsRaceFree (.rc .plain) := by
  have hp : OwnReadsRaceFree .plain := race_nil_right _
  refine ⟨hp, (ownReadsRaceFree_guard_iff _).mpr hp, ?_, ?_⟩
  · intro h
    exact h ⟨rootEv .rd, by decide, rootEv .wr, by decide, by decide, compatible_nil_nil⟩
  · intro h
    exact h ⟨rootEv .rd [.via []], by decide, rootEv .wr [.via []], by decide, by decide,
      compatible_via_via []⟩

/-- Positive and negative examples of `ShrReadsRaceFree`. The second positive example is a
wrapper around `&Cell<plain>` that exposes nothing through a shared reference. -/
theorem shrReadsRaceFree_examples :
    ShrReadsRaceFree .plain ∧ ShrReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ¬ ShrReadsRaceFree (.ref (.cell .plain)) ∧ ¬ ShrReadsRaceFree (.rc .plain) := by
  refine ⟨race_nil_right _, race_nil_left _, ?_, ?_⟩
  · intro h
    exact h ⟨rootEv .rd, by decide, rootEv .wr, by decide, by decide, compatible_nil_nil⟩
  · intro h
    exact h ⟨rootEv .rd [.via []], by decide, rootEv .wr [.via []], by decide, by decide,
      compatible_via_via []⟩

/-! ## The definitional link -/

/-- In the model, `SemSync T` and `SemSend (&T)` are the same proposition. -/
theorem semSync_iff_semSend_ref (T : Ty) : SemSync T ↔ SemSend (.ref T) := Iff.rfl

/-- Non-vacuity of the link: an instance where both sides hold. -/
theorem semSync_iff_semSend_ref_nonvacuous : SemSync .plain ∧ SemSend (.ref .plain) :=
  ⟨semSync_plain, semSync_plain⟩

/-! ## Library primitives: concrete instances and witnesses -/

/-- `Cell<plain>` is semantically `Send` and not semantically `Sync`. -/
theorem cell_plain_semSend_not_semSync : SemSend (.cell .plain) ∧ ¬ SemSync (.cell .plain) :=
  ⟨(semSend_cell_iff _).mpr semSend_plain, not_semSync_cell _⟩

/-- `Cell<U>` and `RefCell<U>` have the same semantic `Send` and the same semantic `Sync`,
for every `U` (both are `Send` exactly when `U` is, and neither is `Sync`); they differ
under a read-only wrapper (`wrap_readOnly_cell_refCell_differ`). -/
theorem cell_refCell_semSend_semSync_agree (U : Ty) :
    (SemSend (.cell U) ↔ SemSend (.refCell U)) ∧ (SemSync (.cell U) ↔ SemSync (.refCell U)) :=
  ⟨(semSend_cell_iff U).trans (semSend_refCell_iff U).symm,
    ⟨fun h => absurd h (not_semSync_cell U), fun h => absurd h (not_semSync_refCell U)⟩⟩

/-- `Rc<plain>` is neither semantically `Send` nor semantically `Sync`. -/
theorem rc_plain_neither : ¬ SemSend (.rc .plain) ∧ ¬ SemSync (.rc .plain) :=
  ⟨not_semSend_rc _, not_semSync_rc _⟩

/-- The `SemSync U` conjunct of `semSend_arc_iff` and `semSync_arc_iff` is not implied
by the other: `Cell<plain>` is semantically `Send` and not semantically `Sync`, and
`Arc<Cell<plain>>` is neither. -/
theorem arc_cell_plain_content_not_semSync_arc_neither :
    SemSend (.cell .plain) ∧ ¬ SemSync (.cell .plain) ∧
      ¬ SemSend (.arc (.cell .plain)) ∧ ¬ SemSync (.arc (.cell .plain)) :=
  ⟨(semSend_cell_iff _).mpr semSend_plain, not_semSync_cell _,
    fun h => not_semSync_cell .plain ((semSend_arc_iff _).mp h).2,
    fun h => not_semSync_cell .plain ((semSync_arc_iff _).mp h).2⟩

/-- The `SemSend U` conjunct of `semSend_arc_iff` and `semSync_arc_iff` is not implied
by the other: `MutexGuard<plain>` is semantically `Sync` and not semantically `Send`
(a release-affinity failure), and `Arc<MutexGuard<plain>>` is neither. -/
theorem arc_guard_plain_content_not_semSend_arc_neither :
    SemSync (.guard .plain) ∧ ¬ SemSend (.guard .plain) ∧
      ¬ SemSend (.arc (.guard .plain)) ∧ ¬ SemSync (.arc (.guard .plain)) :=
  ⟨(semSync_guard_iff _).mpr semSync_plain, not_semSend_guard _,
    fun h => not_semSend_guard .plain ((semSend_arc_iff _).mp h).1,
    fun h => not_semSend_guard .plain ((semSync_arc_iff _).mp h).1⟩

/-- A guard-free witness for the `SemSend U` conjunct of `semSync_arc_iff`, failing by a
data race: a wrapper around `Rc<plain>` exposing nothing is semantically `Sync` and not
semantically `Send`; `Arc` of it is neither, and the transfer of the `Arc` makes no
foreign release (so its failure to be `SemSend` is the race part). -/
theorem arc_wrap_rc_none_content_not_semSend_arc_neither (u : Bool) :
    SemSync (.wrap (.rc .plain) .none u) ∧ ¬ SemSend (.wrap (.rc .plain) .none u) ∧
      ¬ SemSend (.arc (.wrap (.rc .plain) .none u)) ∧ ¬ SemSync (.arc (.wrap (.rc .plain) .none u)) ∧
      NoForeignRelease .other (fp (.arc (.wrap (.rc .plain) .none u))).own :=
  ⟨semSync_wrap_none _ _, not_semSend_rc .plain,
    fun h => not_semSend_rc .plain ((semSend_arc_iff _).mp h).1,
    fun h => not_semSend_rc .plain ((semSync_arc_iff _).mp h).1,
    nfr_of_no_rel (by decide +revert)⟩

/-- Non-vacuity of `semSend_arc_iff` and `semSync_arc_iff`. -/
theorem arc_plain_nonvacuous :
    SemSend (.arc .plain) ∧ SemSync (.arc .plain) ∧ SemSend .plain ∧ SemSync .plain :=
  ⟨(semSend_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩,
    (semSync_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩, semSend_plain, semSync_plain⟩

/-- `Rc<plain>` is not semantically `Send`, and `Mutex<Rc<plain>>` is neither semantically
`Sync` nor semantically `Send`. -/
theorem mutex_rc_plain_content_not_semSend_mutex_neither :
    ¬ SemSend (.rc .plain) ∧ ¬ SemSync (.mutex (.rc .plain)) ∧ ¬ SemSend (.mutex (.rc .plain)) :=
  ⟨not_semSend_rc .plain, fun h => not_semSend_rc .plain ((semSync_mutex_iff _).mp h),
    fun h => not_semSend_rc .plain ((semSend_mutex_iff _).mp h)⟩

/-- `Cell<plain>` is semantically `Send`, and `Mutex<Cell<plain>>` is semantically `Sync`
although `Cell<plain>` is not: the mutex does not need its content to be `Sync`. -/
theorem mutex_cell_plain_semSync_content_not_semSync :
    SemSend (.cell .plain) ∧ SemSync (.mutex (.cell .plain)) ∧ ¬ SemSync (.cell .plain) :=
  ⟨(semSend_cell_iff _).mpr semSend_plain,
    (semSync_mutex_iff _).mpr ((semSend_cell_iff _).mpr semSend_plain), not_semSync_cell _⟩

/-- A mutex does not make every cell type semantically `Sync`: `Mutex<Cell<Rc<plain>>>`
is not, because `Cell<Rc<plain>>` is not semantically `Send`. -/
theorem mutex_cell_rc_plain_not_semSync : ¬ SemSync (.mutex (.cell (.rc .plain))) :=
  fun h => not_semSend_rc .plain ((semSend_cell_iff _).mp ((semSync_mutex_iff _).mp h))

/-- `MutexGuard<plain>` is semantically `Sync`; `Cell<plain>` is not semantically `Sync`,
and neither is `MutexGuard<Cell<plain>>`. -/
theorem guard_sync_examples :
    SemSync (.guard .plain) ∧ ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.guard (.cell .plain)) :=
  ⟨(semSync_guard_iff _).mpr semSync_plain, not_semSync_cell _,
    fun h => not_semSync_cell .plain ((semSync_guard_iff _).mp h)⟩

/-- `plain` is semantically `Sync`; `MutexGuard<plain>` is semantically `Sync` and not
semantically `Send`. -/
theorem guard_plain_semSync_not_semSend :
    SemSync .plain ∧ SemSync (.guard .plain) ∧ ¬ SemSend (.guard .plain) :=
  ⟨semSync_plain, (semSync_guard_iff _).mpr semSync_plain, not_semSend_guard _⟩

/-- The transfer race check of a guard reduces to its content's. Consequently, for content
`U` whose transfer is race-free (for example any semantically `Send` `U`), a guard's failure
to be semantically `Send` comes from the release-affinity conjunct (`NoForeignRelease`)
alone; for content whose transfer races (for example `Rc<plain>`,
`guard_rc_plain_transfer_race`), the guard's transfer races as well. -/
theorem guard_transfer_race_iff (U : Ty) :
    Race (fp (.guard U)).own (fp (.guard U)).alias ↔ Race (fp U).own (fp U).alias := by
  simp only [fp, race_append_left, race_append_right, race_place_guard_nil,
    not_race_place_guard_fresh, not_race_root_place loc_guardRoot, false_or, or_false]

/-- Positive control for `not_semSend_guard`: without the release-affinity conjunct, the
transfer of `MutexGuard<plain>` is race-free. -/
theorem guard_plain_transfer_race_free : ¬ Race (fp (.guard .plain)).own (fp (.guard .plain)).alias :=
  fun h => semSend_plain.1 ((guard_transfer_race_iff _).mp h)

/-- Without the release-affinity conjunct, the transfer of `MutexGuard<Rc<plain>>` still
races: dropping release affinity does not make a guard over non-`Send` content `Send`. -/
theorem guard_rc_plain_transfer_race :
    Race (fp (.guard (.rc .plain))).own (fp (.guard (.rc .plain))).alias :=
  (guard_transfer_race_iff _).mpr ⟨rootEv .wr [.via []], by simp [fp], rootEv .wr [.via []],
    by simp [fp], by decide, compatible_via_via []⟩

/-- Positive control for `not_semSync_cell`: for `Cell<plain>`, hiding the cell's writes
behind a read-only wrapper, or putting the cell behind a mutex, yields semantically `Sync`
types. -/
theorem cell_positive_control :
    SemSync (.wrap (.cell .plain) .readOnly false) ∧ SemSync (.mutex (.cell .plain)) :=
  ⟨⟨not_race_of_no_conflict (by decide), nfr_expose_readOnly _ _⟩,
   (semSync_mutex_iff _).mpr ((semSend_cell_iff _).mpr semSend_plain)⟩

/-- `Rc<U>` is neither semantically `Send` nor semantically `Sync`, for every `U`. -/
theorem not_semSend_rc_and_not_semSync_rc (U : Ty) : ¬ SemSend (.rc U) ∧ ¬ SemSync (.rc U) :=
  ⟨not_semSend_rc U, not_semSync_rc U⟩

/-- Non-vacuity of `semSend_prod_iff` and `semSync_prod_iff`. -/
theorem prod_plain_nonvacuous :
    SemSend (.prod .plain .plain) ∧ SemSync (.prod .plain .plain) ∧ SemSend .plain ∧ SemSync .plain :=
  ⟨(semSend_prod_iff _ _).mpr ⟨semSend_plain, semSend_plain⟩,
    (semSync_prod_iff _ _).mpr ⟨semSync_plain, semSync_plain⟩, semSend_plain, semSync_plain⟩

/-- Sums are modelled with the footprint of the product of their variants (no
discriminant, no variant exclusivity). -/
theorem fp_sum_eq_prod (A B : Ty) : fp (.sum A B) = fp (.prod A B) := rfl

/-! ## False rules and their positive controls -/

/-- "`SemSync` implies `SemSend`" is false in the model. -/
theorem not_forall_semSync_imp_semSend : ¬ ∀ T : Ty, SemSync T → SemSend T :=
  fun h => not_semSend_guard .plain (h _ ((semSync_guard_iff _).mpr semSync_plain))

/-- A guard-free witness against "`SemSync` implies `SemSend`": a wrapper around `Rc`
exposing nothing through a shared reference. -/
theorem wrap_rc_none_semSync_not_semSend (u : Bool) :
    SemSync (.wrap (.rc .plain) .none u) ∧ ¬ SemSend (.wrap (.rc .plain) .none u) :=
  ⟨semSync_wrap_none _ _, not_semSend_rc .plain⟩

/-- "`SemSend` implies `SemSync`" is false in the model. -/
theorem not_forall_semSend_imp_semSync : ¬ ∀ T : Ty, SemSend T → SemSync T :=
  fun h => not_semSync_cell .plain (h _ ((semSend_cell_iff _).mpr semSend_plain))

/-- Positive control: when the shared capabilities contain no write, `SemSend`
implies `SemSync`. -/
theorem semSend_imp_semSync_of_shr_no_write (T : Ty)
    (hro : ∀ e ∈ (fp T).shr, e.kind.isWrite = false) (hs : SemSend T) : SemSync T := by
  obtain ⟨hr, hn⟩ := hs
  refine ⟨?_, nfr_shr_of_own _ T hn⟩
  intro h
  rcases (race_append_right _ _ _).mp h with h | h
  · obtain ⟨e₁, h₁, e₂, h₂, hc, _⟩ := h
    rcases hc.2.2.2.1 with hw | hw
    · rw [hro e₁ h₁] at hw; cases hw
    · rw [hro e₂ h₂] at hw; cases hw
  · exact hr (race_mono (shr_subset_own T) (fun _ h => h) h)

/-- Non-vacuity of `semSend_imp_semSync_of_shr_no_write`: `plain` has a write-free
shared footprint and is semantically `Send`. -/
theorem semSend_imp_semSync_of_shr_no_write_nonvacuous :
    (∀ e ∈ (fp .plain).shr, e.kind.isWrite = false) ∧ SemSend .plain :=
  ⟨by decide, semSend_plain⟩

/-- Tightness of `SemSend T` in `semSend_imp_semSync_of_shr_no_write`: a read-only wrapper
around `Rc<plain>` has a write-free shared footprint and is not semantically `Sync` (its
exposed count read races with count writes through other handles). -/
theorem semSend_imp_semSync_of_shr_no_write_semSend_tight :
    (∀ e ∈ (fp (.wrap (.rc .plain) .readOnly false)).shr, e.kind.isWrite = false) ∧
      ¬ SemSync (.wrap (.rc .plain) .readOnly false) := by
  refine ⟨by decide, fun h => h.1 ?_⟩
  exact ⟨rootEv .rd [.via []], by decide, rootEv .wr [.via []], by decide, by decide,
    compatible_via_via []⟩

/-- A write-free shared footprint is not necessary for `SemSync`: `Arc<plain>` has an
atomic write in its shared footprint and is semantically `Sync`. -/
theorem arc_plain_shr_has_write_semSync :
    ¬ (∀ e ∈ (fp (.arc .plain)).shr, e.kind.isWrite = false) ∧ SemSync (.arc .plain) :=
  ⟨by decide, (semSync_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩⟩

/-- Positive control: when every owner capability is also a shared capability,
`SemSync` implies `SemSend`. -/
theorem semSync_imp_semSend_of_own_subset_shr (T : Ty)
    (hsub : ∀ e ∈ (fp T).own, e ∈ (fp T).shr) (hy : SemSync T) : SemSend T := by
  obtain ⟨hr, hn⟩ := hy
  refine ⟨fun h => hr ?_, nfr_mono hsub hn⟩
  exact race_mono hsub (fun e he => List.mem_append.mpr (Or.inr he)) h

/-- Non-vacuity of `semSync_imp_semSend_of_own_subset_shr`: `Arc<plain>`. -/
theorem semSync_imp_semSend_of_own_subset_shr_nonvacuous :
    (∀ e ∈ (fp (.arc .plain)).own, e ∈ (fp (.arc .plain)).shr) ∧ SemSync (.arc .plain) :=
  ⟨fun _ h => h, (semSync_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩⟩

/-- Tightness of `SemSync T` in `semSync_imp_semSend_of_own_subset_shr`: `Rc<plain>` has
equal owner and shared footprints and is not semantically `Send`. -/
theorem semSync_imp_semSend_of_own_subset_shr_semSync_tight :
    (∀ e ∈ (fp (.rc .plain)).own, e ∈ (fp (.rc .plain)).shr) ∧ ¬ SemSend (.rc .plain) :=
  ⟨fun _ h => h, not_semSend_rc .plain⟩

/-- `own ⊆ shr` is not necessary for `SemSend`: `plain` has an owner-only write and is
semantically `Send`. -/
theorem plain_own_not_subset_shr_semSend :
    ¬ (∀ e ∈ (fp .plain).own, e ∈ (fp .plain).shr) ∧ SemSend .plain :=
  ⟨by decide, semSend_plain⟩

/-- The hypothesis of `semSend_imp_semSync_of_shr_no_write` is not met by `Cell<plain>`,
the witness of `not_forall_semSend_imp_semSync`. -/
theorem cell_plain_shr_has_write : ¬ ∀ e ∈ (fp (.cell .plain)).shr, e.kind.isWrite = false := by
  decide

/-- The hypothesis of `semSync_imp_semSend_of_own_subset_shr` is not met by
`MutexGuard<plain>`, the witness of `not_forall_semSync_imp_semSend`. -/
theorem guard_plain_own_not_subset_shr :
    ¬ ∀ e ∈ (fp (.guard .plain)).own, e ∈ (fp (.guard .plain)).shr := by
  decide

/-! ## Structural soundness of the checker -/

theorem rule_holds_of_eval {r : Rule} {s y : Bool} {S Y : Prop} (hs : s = true → S)
    (hy : y = true → Y) (h : r.eval s y = true) : r.Holds S Y := by
  obtain ⟨a, ns, ny⟩ := r
  cases a <;> cases ns <;> cases ny <;> cases s <;> cases y <;>
    simp_all [Rule.eval, Rule.Holds]

/-- Structural soundness: if the impl table is semantically sound for every primitive
and every unsafe `Sync` impl inside `T` is semantically justified, then the checker's
verdicts for `T` are semantically true. -/
theorem autoCheck_sound_of_tableSound_of_implsSound (tb : Table) (htb : TableSound tb) :
    ∀ T : Ty, ImplsSound T →
      ((autoCheck tb T).1 = true → SemSend T) ∧ ((autoCheck tb T).2 = true → SemSync T) := by
  intro T
  induction T with
  | plain => intro _; exact ⟨fun _ => semSend_plain, fun _ => semSync_plain⟩
  | cell t ih =>
    intro hI
    obtain ⟨ih₁, ih₂⟩ := ih hI
    exact ⟨fun h => (htb .cell t).1 (rule_holds_of_eval ih₁ ih₂ h),
      fun h => (htb .cell t).2 (rule_holds_of_eval ih₁ ih₂ h)⟩
  | refCell t ih =>
    intro hI
    obtain ⟨ih₁, ih₂⟩ := ih hI
    exact ⟨fun h => (htb .refCell t).1 (rule_holds_of_eval ih₁ ih₂ h),
      fun h => (htb .refCell t).2 (rule_holds_of_eval ih₁ ih₂ h)⟩
  | rc t ih =>
    intro hI
    obtain ⟨ih₁, ih₂⟩ := ih hI
    exact ⟨fun h => (htb .rc t).1 (rule_holds_of_eval ih₁ ih₂ h),
      fun h => (htb .rc t).2 (rule_holds_of_eval ih₁ ih₂ h)⟩
  | arc t ih =>
    intro hI
    obtain ⟨ih₁, ih₂⟩ := ih hI
    exact ⟨fun h => (htb .arc t).1 (rule_holds_of_eval ih₁ ih₂ h),
      fun h => (htb .arc t).2 (rule_holds_of_eval ih₁ ih₂ h)⟩
  | mutex t ih =>
    intro hI
    obtain ⟨ih₁, ih₂⟩ := ih hI
    exact ⟨fun h => (htb .mutex t).1 (rule_holds_of_eval ih₁ ih₂ h),
      fun h => (htb .mutex t).2 (rule_holds_of_eval ih₁ ih₂ h)⟩
  | guard t ih =>
    intro hI
    obtain ⟨ih₁, ih₂⟩ := ih hI
    exact ⟨fun h => (htb .guard t).1 (rule_holds_of_eval ih₁ ih₂ h),
      fun h => (htb .guard t).2 (rule_holds_of_eval ih₁ ih₂ h)⟩
  | box t ih => exact ih
  | ref t ih =>
    intro hI
    obtain ⟨_, ih₂⟩ := ih hI
    exact ⟨ih₂, fun h => (semSync_ref_iff t).mpr (ih₂ h)⟩
  | refMut t ih => exact ih
  | prod a b iha ihb =>
    rintro ⟨ha, hb⟩
    obtain ⟨ha₁, ha₂⟩ := iha ha
    obtain ⟨hb₁, hb₂⟩ := ihb hb
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [autoCheck, Bool.and_eq_true] at h
      exact (semSend_prod_iff a b).mpr ⟨ha₁ h.1, hb₁ h.2⟩
    · simp only [autoCheck, Bool.and_eq_true] at h
      exact (semSync_prod_iff a b).mpr ⟨ha₂ h.1, hb₂ h.2⟩
  | sum a b iha ihb =>
    rintro ⟨ha, hb⟩
    obtain ⟨ha₁, ha₂⟩ := iha ha
    obtain ⟨hb₁, hb₂⟩ := ihb hb
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [autoCheck, Bool.and_eq_true] at h
      exact (semSend_sum_iff a b).mpr ⟨ha₁ h.1, hb₁ h.2⟩
    · simp only [autoCheck, Bool.and_eq_true] at h
      exact (semSync_sum_iff a b).mpr ⟨ha₂ h.1, hb₂ h.2⟩
  | wrap f v u ih =>
    rintro ⟨hu, hf⟩
    obtain ⟨ih₁, ih₂⟩ := ih hf
    refine ⟨ih₁, fun h => ?_⟩
    cases u with
    | true => exact hu rfl
    | false =>
      simp only [autoCheck, Bool.false_or] at h
      exact semSync_wrap_of_semSync f v false (ih₂ h)

/-- The standard table is semantically sound. -/
theorem stdTable_sound : TableSound stdTable := by
  intro p U
  cases p with
  | cell =>
    exact ⟨fun h => (semSend_cell_iff U).mpr (h.2.1 rfl), fun h => absurd h.1 (by decide)⟩
  | refCell =>
    exact ⟨fun h => (semSend_refCell_iff U).mpr (h.2.1 rfl), fun h => absurd h.1 (by decide)⟩
  | rc => exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide)⟩
  | arc =>
    exact ⟨fun h => (semSend_arc_iff U).mpr ⟨h.2.1 rfl, h.2.2 rfl⟩,
      fun h => (semSync_arc_iff U).mpr ⟨h.2.1 rfl, h.2.2 rfl⟩⟩
  | mutex =>
    exact ⟨fun h => (semSend_mutex_iff U).mpr (h.2.1 rfl),
      fun h => (semSync_mutex_iff U).mpr (h.2.1 rfl)⟩
  | guard =>
    exact ⟨fun h => absurd h.1 (by decide), fun h => (semSync_guard_iff U).mpr (h.2.2 rfl)⟩

/-- A table with no positive rule (every rule has `allowed = false`). -/
def noImplTable : Table := ⟨fun _ => ⟨false, false, false⟩, fun _ => ⟨false, false, false⟩⟩

/-- `TableSound` constrains positive rules alone: the table with no positive rule is sound. -/
theorem tableSound_noImplTable : TableSound noImplTable :=
  fun p _ => by cases p <;> exact ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide)⟩

/-- Every positive rule of `stdTable` (`allowed = true`: `Send` for `Cell`, `RefCell`,
`Arc`, `Mutex`; `Sync` for `Arc`, `Mutex`, `MutexGuard`) has its condition met at the
argument `plain`, and the primitive type over `plain` has the semantic property. -/
theorem stdTable_positive_rules_nonvacuous :
    ∀ p : Prim,
      ((stdTable.send p).allowed = true →
          (stdTable.send p).Holds (SemSend .plain) (SemSync .plain) ∧ SemSend (p.apply .plain)) ∧
      ((stdTable.sync p).allowed = true →
          (stdTable.sync p).Holds (SemSend .plain) (SemSync .plain) ∧ SemSync (p.apply .plain)) := by
  intro p
  have hh : ∀ r : Rule, r.allowed = true → r.Holds (SemSend .plain) (SemSync .plain) :=
    fun _ ha => ⟨ha, fun _ => semSend_plain, fun _ => semSync_plain⟩
  exact ⟨fun ha => ⟨hh _ ha, (stdTable_sound p .plain).1 (hh _ ha)⟩,
    fun ha => ⟨hh _ ha, (stdTable_sound p .plain).2 (hh _ ha)⟩⟩

/-- `stdTable` gives `Cell` and `RefCell` the same rules, so the checker gives `Cell<U>` and
`RefCell<U>` the same verdicts, for every `U`. -/
theorem autoCheck_std_cell_eq_refCell (U : Ty) :
    autoCheck stdTable (.cell U) = autoCheck stdTable (.refCell U) := rfl

/-- Non-vacuity of `autoCheck_sound_of_tableSound_of_implsSound`: the standard table is
sound, `Arc<Mutex<Cell<plain>>>` has no unsafe impls, and the checker accepts it for both
traits. -/
theorem autoCheck_sound_nonvacuous :
    TableSound stdTable ∧ ImplsSound (.arc (.mutex (.cell .plain))) ∧
      autoCheck stdTable (.arc (.mutex (.cell .plain))) = (true, true) :=
  ⟨stdTable_sound, trivial, by decide⟩

/-- A table that wrongly declares `Rc<T>: Send` for every `T`. -/
def rcSendTable : Table := { stdTable with send := fun p => if p = .rc then ⟨true, false, false⟩ else stdTable.send p }

/-- Tightness of `TableSound` in `autoCheck_sound_of_tableSound_of_implsSound`: with the
table `rcSendTable`, `Rc<plain>` has no unsafe impls and is accepted as `Send`, but is not
semantically `Send`. -/
theorem autoCheck_sound_tableSound_tight :
    ImplsSound (.rc .plain) ∧ (autoCheck rcSendTable (.rc .plain)).1 = true ∧
      ¬ SemSend (.rc .plain) :=
  ⟨trivial, by decide, not_semSend_rc _⟩

/-- Tightness of `ImplsSound` in `autoCheck_sound_of_tableSound_of_implsSound`: with the
sound standard table, a wrapper over `Cell<plain>` that exposes the cell's full shared API
and carries an unsafe `Sync` impl is accepted as `Sync` but is not semantically `Sync`. -/
theorem autoCheck_sound_implsSound_tight :
    TableSound stdTable ∧ (autoCheck stdTable (.wrap (.cell .plain) .full true)).2 = true ∧
      ¬ SemSync (.wrap (.cell .plain) .full true) :=
  ⟨stdTable_sound, by decide, not_semSync_cell .plain⟩

/-- Corollary for the standard table. -/
theorem autoCheck_std_sound_of_implsSound (T : Ty) (hT : ImplsSound T) :
    ((autoCheck stdTable T).1 = true → SemSend T) ∧ ((autoCheck stdTable T).2 = true → SemSync T) :=
  autoCheck_sound_of_tableSound_of_implsSound stdTable stdTable_sound T hT

/-- For wrapper-free types, the standard-table checker is exact: its verdicts coincide
with the semantic predicates. -/
theorem autoCheck_std_exact_of_wrapFree :
    ∀ T : Ty, WrapFree T →
      ((autoCheck stdTable T).1 = true ↔ SemSend T) ∧ ((autoCheck stdTable T).2 = true ↔ SemSync T) := by
  intro T
  induction T with
  | plain => intro _; exact ⟨⟨fun _ => semSend_plain, fun _ => rfl⟩, ⟨fun _ => semSync_plain, fun _ => rfl⟩⟩
  | cell t ih =>
    intro hW
    obtain ⟨ih₁, ih₂⟩ := ih hW
    refine ⟨⟨fun h => (semSend_cell_iff t).mpr (ih₁.mp ?_), fun h => ?_⟩,
      ⟨fun h => absurd h (by simp [autoCheck, stdTable, Rule.eval]), fun h => absurd h (not_semSync_cell t)⟩⟩
    · simpa [autoCheck, stdTable, Rule.eval] using h
    · simpa [autoCheck, stdTable, Rule.eval] using ih₁.mpr ((semSend_cell_iff t).mp h)
  | refCell t ih =>
    intro hW
    obtain ⟨ih₁, ih₂⟩ := ih hW
    refine ⟨⟨fun h => (semSend_refCell_iff t).mpr (ih₁.mp ?_), fun h => ?_⟩,
      ⟨fun h => absurd h (by simp [autoCheck, stdTable, Rule.eval]),
        fun h => absurd h (not_semSync_refCell t)⟩⟩
    · simpa [autoCheck, stdTable, Rule.eval] using h
    · simpa [autoCheck, stdTable, Rule.eval] using ih₁.mpr ((semSend_refCell_iff t).mp h)
  | rc t _ =>
    intro _
    exact ⟨⟨fun h => absurd h (by simp [autoCheck, stdTable, Rule.eval]), fun h => absurd h (not_semSend_rc t)⟩,
      ⟨fun h => absurd h (by simp [autoCheck, stdTable, Rule.eval]), fun h => absurd h (not_semSync_rc t)⟩⟩
  | arc t ih =>
    intro hW
    obtain ⟨ih₁, ih₂⟩ := ih hW
    have key : ((stdTable.send .arc).eval (autoCheck stdTable t).1 (autoCheck stdTable t).2 = true ↔
        SemSend t ∧ SemSync t) := by
      simp only [stdTable, Rule.eval, Bool.true_and, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      exact ⟨fun h => ⟨ih₁.mp h.1, ih₂.mp h.2⟩, fun h => ⟨ih₁.mpr h.1, ih₂.mpr h.2⟩⟩
    have key' : ((stdTable.sync .arc).eval (autoCheck stdTable t).1 (autoCheck stdTable t).2 = true ↔
        SemSend t ∧ SemSync t) := key
    exact ⟨key.trans (semSend_arc_iff t).symm, key'.trans (semSync_arc_iff t).symm⟩
  | mutex t ih =>
    intro hW
    obtain ⟨ih₁, _⟩ := ih hW
    have key : ((stdTable.send .mutex).eval (autoCheck stdTable t).1 (autoCheck stdTable t).2 = true ↔
        SemSend t) := by
      simp only [stdTable, Rule.eval, Bool.true_and, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.and_true]
      exact ih₁
    have key' : ((stdTable.sync .mutex).eval (autoCheck stdTable t).1 (autoCheck stdTable t).2 = true ↔
        SemSend t) := key
    exact ⟨key.trans (semSend_mutex_iff t).symm, key'.trans (semSync_mutex_iff t).symm⟩
  | guard t ih =>
    intro hW
    obtain ⟨_, ih₂⟩ := ih hW
    have key : ((stdTable.sync .guard).eval (autoCheck stdTable t).1 (autoCheck stdTable t).2 = true ↔
        SemSync t) := by
      simp only [stdTable, Rule.eval, Bool.true_and, Bool.not_true, Bool.false_or, Bool.not_false,
        Bool.true_or]
      exact ih₂
    exact ⟨⟨fun h => absurd h (by simp [autoCheck, stdTable, Rule.eval]),
        fun h => absurd h (not_semSend_guard t)⟩, key.trans (semSync_guard_iff t).symm⟩
  | box t ih => exact ih
  | ref t ih =>
    intro hW
    obtain ⟨_, ih₂⟩ := ih hW
    exact ⟨ih₂, ih₂.trans (semSync_ref_iff t).symm⟩
  | refMut t ih => exact ih
  | prod a b iha ihb =>
    rintro ⟨ha, hb⟩
    obtain ⟨ha₁, ha₂⟩ := iha ha
    obtain ⟨hb₁, hb₂⟩ := ihb hb
    simp only [autoCheck, Bool.and_eq_true]
    exact ⟨(and_congr ha₁ hb₁).trans (semSend_prod_iff a b).symm,
      (and_congr ha₂ hb₂).trans (semSync_prod_iff a b).symm⟩
  | sum a b iha ihb =>
    rintro ⟨ha, hb⟩
    obtain ⟨ha₁, ha₂⟩ := iha ha
    obtain ⟨hb₁, hb₂⟩ := ihb hb
    simp only [autoCheck, Bool.and_eq_true]
    exact ⟨(and_congr ha₁ hb₁).trans (semSend_sum_iff a b).symm,
      (and_congr ha₂ hb₂).trans (semSync_sum_iff a b).symm⟩
  | wrap f v u _ => intro h; exact absurd h id

/-- Non-vacuity of `autoCheck_std_exact_of_wrapFree`. -/
theorem autoCheck_std_exact_nonvacuous : WrapFree (.arc (.mutex (.cell .plain))) := trivial

/-- Tightness of `WrapFree` in `autoCheck_std_exact_of_wrapFree`: a read-only wrapper over
`Cell<plain>` without an unsafe impl is semantically `Sync` but rejected by the checker. -/
theorem autoCheck_std_exact_wrapFree_tight :
    ¬ ((autoCheck stdTable (.wrap (.cell .plain) .readOnly false)).2 = true ↔
        SemSync (.wrap (.cell .plain) .readOnly false)) := by
  intro h
  have := h.mpr cell_positive_control.1
  revert this
  decide

/-! ## The obligation of an unsafe `Sync` impl -/

/-- An unsafe `Sync` impl on a wrapper is semantically justified exactly when the
explicit invariant `SyncObligation` holds; the impl flag itself is irrelevant. -/
theorem semSync_wrap_iff_syncObligation (f : Ty) (v : View) (u : Bool) :
    SemSync (.wrap f v u) ↔ SyncObligation f v := by
  unfold SemSync SyncObligation Race
  show (¬ ∃ e₁ ∈ v.expose (fp f).shr, ∃ e₂ ∈ v.expose (fp f).shr ++ (fp f).alias,
      Conflicting e₁ e₂ ∧ Concurrent e₁ e₂) ∧ NoForeignRelease .other (v.expose (fp f).shr) ↔ _
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun e₁ he₁ e₂ he₂ hc hcc => h₁ ⟨e₁, he₁, e₂, he₂, hc, hcc⟩, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun ⟨e₁, he₁, e₂, he₂, hc, hcc⟩ => h₁ e₁ he₁ e₂ he₂ hc hcc, h₂⟩

/-- A wrapper exposing the full shared API of `Cell<U>` is never semantically `Sync`. -/
theorem not_semSync_wrap_cell_full (U : Ty) (u : Bool) : ¬ SemSync (.wrap (.cell U) .full u) :=
  fun h => not_semSync_cell U ((semSync_wrap_full_iff _ _).mp h)

/-- For a read-only wrapper over `Cell<U>`, the obligation holds exactly when reads through
the owner capabilities of the content race with no alias capability of the content: a
shared reference to the cell reaches the content's owner capabilities (`Cell::get`,
`Cell::replace`), and the view keeps their reads. -/
theorem semSync_wrap_cell_readOnly_iff_ownReadsRaceFree (U : Ty) (u : Bool) :
    SemSync (.wrap (.cell U) .readOnly u) ↔ OwnReadsRaceFree U := by
  have hE : View.expose .readOnly (fp (.cell U)).shr =
      [rootEv .rd] ++ place [] 0 (View.expose .readOnly (fp U).own) := by
    show View.expose .readOnly ([rootEv .rd, rootEv .wr] ++ place [] 0 (fp U).own) = _
    rw [expose_readOnly_append, expose_readOnly_place _ rfl]
    rfl
  unfold SemSync OwnReadsRaceFree
  show (¬ Race (View.expose .readOnly (fp (.cell U)).shr)
      (View.expose .readOnly (fp (.cell U)).shr ++ place [] 0 (fp U).alias) ∧
      NoForeignRelease .other (View.expose .readOnly (fp (.cell U)).shr)) ↔ _
  rw [race_append_right]
  simp only [not_race_expose_readOnly, false_or, nfr_expose_readOnly, and_true]
  rw [hE, race_append_left, race_place_nil_nil]
  simp only [not_race_root_place (R := [rootEv .rd]) (by decide), false_or]

/-- A sufficient condition: semantically `Send` content has race-free owner reads. -/
theorem ownReadsRaceFree_of_semSend (U : Ty) (h : SemSend U) : OwnReadsRaceFree U :=
  fun hr => h.1 (race_mono (expose_subset .readOnly _) (fun _ h => h) hr)

/-- Non-vacuity of `semSync_wrap_cell_readOnly_iff_ownReadsRaceFree`: a read-only wrapper
over `Cell<plain>` is semantically `Sync`, and `plain` has race-free owner reads. -/
theorem wrap_cell_plain_readOnly_nonvacuous (u : Bool) :
    OwnReadsRaceFree .plain ∧ SemSync (.wrap (.cell .plain) .readOnly u) :=
  ⟨ownReadsRaceFree_examples.1,
    (semSync_wrap_cell_readOnly_iff_ownReadsRaceFree _ _).mpr ownReadsRaceFree_examples.1⟩

/-- The content condition is not vacuous: a read-only wrapper over `Cell<&Cell<plain>>` is
not semantically `Sync` (reading the inner cell through the copied-out reference races with
writes by the lender of that reference). -/
theorem wrap_cell_ref_cell_readOnly_not_semSync (u : Bool) :
    ¬ OwnReadsRaceFree (.ref (.cell .plain)) ∧ ¬ SemSync (.wrap (.cell (.ref (.cell .plain))) .readOnly u) :=
  ⟨ownReadsRaceFree_examples.2.2.1,
    fun h => ownReadsRaceFree_examples.2.2.1
      ((semSync_wrap_cell_readOnly_iff_ownReadsRaceFree _ _).mp h)⟩

/-- `SemSend U` is sufficient and not necessary for the content condition: `MutexGuard<plain>`
is not semantically `Send`, has race-free owner reads, and a read-only wrapper over
`Cell<MutexGuard<plain>>` is semantically `Sync`. -/
theorem wrap_cell_guard_plain_readOnly_semSync (u : Bool) :
    ¬ SemSend (.guard .plain) ∧ OwnReadsRaceFree (.guard .plain) ∧
      SemSync (.wrap (.cell (.guard .plain)) .readOnly u) :=
  ⟨not_semSend_guard _, ownReadsRaceFree_examples.2.1,
    (semSync_wrap_cell_readOnly_iff_ownReadsRaceFree _ _).mpr ownReadsRaceFree_examples.2.1⟩

/-- Hiding writes on a wrapper does not help when the cell is itself shared through other
handles: a read-only wrapper over `Arc<Cell<plain>>` is not semantically `Sync`. -/
theorem wrap_arc_cell_readOnly_not_semSync (u : Bool) :
    ¬ SemSync (.wrap (.arc (.cell .plain)) .readOnly u) := by
  intro h
  apply h.1
  refine ⟨⟨.rd, [0], [.via []]⟩, ?_, ⟨.wr, [0], [.via []]⟩, ?_, by decide, compatible_via_via []⟩
  · clear h; decide +revert
  · clear h; decide +revert

/-- The read-only view keeps no write and no access under a mutable borrow: in particular
a read-only wrapper over `RefCell<plain>` (whose view keeps the flag read and the content
read through a shared borrow) is semantically `Sync`. -/
theorem semSync_wrap_refCell_plain_readOnly (u : Bool) :
    SemSync (.wrap (.refCell .plain) .readOnly u) :=
  ⟨not_race_of_no_conflict (by decide +revert), nfr_expose_readOnly _ _⟩

/-- The read-only view of the shared footprint of `RefCell<U>`: the borrow-flag read and the
read-only view of the shared capabilities of `U` (shared borrow); the flag write and every
access under a mutable borrow (claim `held [] .fresh`) are dropped. -/
theorem expose_readOnly_refCell_shr (U : Ty) :
    View.expose .readOnly (fp (.refCell U)).shr =
      [rootEv .rd] ++ place [] 0 (View.expose .readOnly (fp U).shr) := by
  show View.expose .readOnly ([rootEv .rd, rootEv .wr] ++ place [] 0 (fp U).shr ++
    place [.held [] .fresh] 0 (fp U).own) = _
  rw [expose_readOnly_append, expose_readOnly_append, expose_readOnly_place _ rfl,
    expose_readOnly_place_fresh, List.append_nil]
  rfl

/-- For a read-only wrapper over `RefCell<U>`, the obligation holds exactly when reads
through the shared capabilities of the content race with no alias capability of the
content: the view drops the borrow-flag writes and every access under a mutable borrow
(which needs a flag write), and keeps the flag reads and the reads through a shared borrow
(as reached by the unsafe `RefCell::try_borrow_unguarded`). -/
theorem semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree (U : Ty) (u : Bool) :
    SemSync (.wrap (.refCell U) .readOnly u) ↔ ShrReadsRaceFree U := by
  have hE := expose_readOnly_refCell_shr U
  unfold SemSync ShrReadsRaceFree
  show (¬ Race (View.expose .readOnly (fp (.refCell U)).shr)
      (View.expose .readOnly (fp (.refCell U)).shr ++ place [] 0 (fp U).alias) ∧
      NoForeignRelease .other (View.expose .readOnly (fp (.refCell U)).shr)) ↔ _
  rw [race_append_right]
  simp only [not_race_expose_readOnly, false_or, nfr_expose_readOnly, and_true]
  rw [hE, race_append_left, race_place_nil_nil]
  simp only [not_race_root_place (R := [rootEv .rd]) (by decide), false_or]

/-- The `RefCell` content condition is weaker than the `Cell` content condition: a shared
capability is also an owner capability (`shr_subset_own`). -/
theorem shrReadsRaceFree_of_ownReadsRaceFree (U : Ty) (h : OwnReadsRaceFree U) :
    ShrReadsRaceFree U := by
  refine fun hr => h (race_mono ?_ (fun _ h => h) hr)
  intro e he
  obtain ⟨hm, hp⟩ := List.mem_filter.mp he
  exact List.mem_filter.mpr ⟨shr_subset_own U e hm, hp⟩

/-- Non-vacuity of `semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree`: `plain` has
race-free shared reads, and a read-only wrapper over `RefCell<plain>` is semantically
`Sync`. -/
theorem wrap_refCell_plain_readOnly_nonvacuous (u : Bool) :
    ShrReadsRaceFree .plain ∧ SemSync (.wrap (.refCell .plain) .readOnly u) :=
  ⟨shrReadsRaceFree_examples.1, semSync_wrap_refCell_plain_readOnly u⟩

/-- The `RefCell` content condition is not vacuous: a read-only wrapper over
`RefCell<&Cell<plain>>` is not semantically `Sync` (reading the inner cell through the
shared borrow races with writes by the lender of the reference). -/
theorem wrap_refCell_ref_cell_readOnly_not_semSync (u : Bool) :
    ¬ ShrReadsRaceFree (.ref (.cell .plain)) ∧
      ¬ SemSync (.wrap (.refCell (.ref (.cell .plain))) .readOnly u) :=
  ⟨shrReadsRaceFree_examples.2.2.1,
    fun h => shrReadsRaceFree_examples.2.2.1
      ((semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree _ _).mp h)⟩

/-- `Cell` and `RefCell` differ under a read-only wrapper. For the content
`W = .wrap (.ref (.cell .plain)) .none false` (a wrapper around `&Cell<plain>` exposing
nothing through a shared reference, whose owner can use the inner cell): a read-only
wrapper over `Cell<W>` reaches `W`'s owner capabilities and is not semantically `Sync`,
while a read-only wrapper over `RefCell<W>` reaches `W`'s shared capabilities alone and is
semantically `Sync`. -/
theorem wrap_readOnly_cell_refCell_differ (u : Bool) :
    ¬ OwnReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ShrReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) ∧
      ¬ SemSync (.wrap (.cell (.wrap (.ref (.cell .plain)) .none false)) .readOnly u) ∧
      SemSync (.wrap (.refCell (.wrap (.ref (.cell .plain)) .none false)) .readOnly u) := by
  have hown : ¬ OwnReadsRaceFree (.wrap (.ref (.cell .plain)) .none false) := fun h =>
    h ⟨rootEv .rd, by decide, rootEv .wr, by decide, by decide, compatible_nil_nil⟩
  exact ⟨hown, shrReadsRaceFree_examples.2.1,
    fun h => hown ((semSync_wrap_cell_readOnly_iff_ownReadsRaceFree _ _).mp h),
    (semSync_wrap_refCell_readOnly_iff_shrReadsRaceFree _ _).mpr shrReadsRaceFree_examples.2.1⟩

/-- For a wrapper over `Rc<U>`, the obligation holds exactly when nothing is exposed:
even a read-only view races with count updates made through other handles. -/
theorem semSync_wrap_rc_iff (U : Ty) (v : View) (u : Bool) :
    SemSync (.wrap (.rc U) v u) ↔ v = .none := by
  cases v with
  | full =>
    simp only [reduceCtorEq, iff_false]
    exact not_semSync_rc U
  | readOnly =>
    simp only [reduceCtorEq, iff_false]
    intro h
    apply h.1
    refine ⟨rootEv .rd [.via []], ?_, rootEv .wr [.via []], ?_, by decide, compatible_via_via []⟩
    · simp [fp, View.expose, List.mem_filter, rootEv, Kind.isRead, Ev.acquires, Claim.isFresh]
    · simp [fp]
  | none =>
    simp only [iff_true]
    exact semSync_wrap_none _ _

/-- Counterexample for a violated obligation: the checker accepts an unsafe `Sync` impl on
a wrapper exposing `Cell<plain>`'s full shared API, and two threads race on the cell. -/
theorem unsafeSync_wrap_cell_full_accepted_but_racy :
    (autoCheck stdTable (.wrap (.cell .plain) .full true)).2 = true ∧
      Race (fp (.wrap (.cell .plain) .full true)).shr
        ((fp (.wrap (.cell .plain) .full true)).shr ++ (fp (.wrap (.cell .plain) .full true)).alias) :=
  ⟨by decide, rootEv .wr, by simp [fp, View.expose], rootEv .wr, by simp [fp, View.expose],
    by decide, compatible_nil_nil⟩

/-- Non-vacuity of the obligation: a read-only wrapper over `Cell<plain>` with an unsafe
`Sync` impl meets it. -/
theorem syncObligation_nonvacuous : SyncObligation (.cell .plain) .readOnly :=
  (semSync_wrap_iff_syncObligation _ _ true).mp (wrap_cell_plain_readOnly_nonvacuous true).2

/-- Tightness of `SemSync f` in `semSync_wrap_of_semSync` (no other hypothesis): for the field
`Cell<plain>`, which is not semantically `Sync`, the wrapper with the full view and no unsafe
impl is not semantically `Sync`. -/
theorem semSync_wrap_of_semSync_tight :
    ¬ SemSync (.cell .plain) ∧ ¬ SemSync (.wrap (.cell .plain) .full false) :=
  ⟨not_semSync_cell .plain, not_semSync_wrap_cell_full .plain false⟩

/-- Non-vacuity of `semSync_wrap_of_semSync`: `Arc<plain>` is semantically `Sync`, and so is a
read-only wrapper over it without an unsafe impl. -/
theorem semSync_wrap_of_semSync_nonvacuous :
    SemSync (.arc .plain) ∧ SemSync (.wrap (.arc .plain) .readOnly false) :=
  ⟨(semSync_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩,
    semSync_wrap_of_semSync _ _ _ ((semSync_arc_iff _).mpr ⟨semSend_plain, semSync_plain⟩)⟩

/-! ## The checker is sound and incomplete -/

/-- Incompleteness: a read-only wrapper over `Cell<plain>` without an unsafe impl is
semantically `Sync`, its shared reference is semantically `Send`, and the standard-table
checker rejects both. -/
theorem autoCheck_std_incomplete :
    SemSync (.wrap (.cell .plain) .readOnly false) ∧
      (autoCheck stdTable (.wrap (.cell .plain) .readOnly false)).2 = false ∧
      SemSend (.ref (.wrap (.cell .plain) .readOnly false)) ∧
      (autoCheck stdTable (.ref (.wrap (.cell .plain) .readOnly false))).1 = false := by
  have hs : SemSync (.wrap (.cell .plain) .readOnly false) := cell_positive_control.1
  exact ⟨hs, by decide, hs, by decide⟩

end Toy.SendSync

namespace Toy.SendSync

/-! ## Examples for the checker-side definitions -/

/-- Negative example of `TableSound`: `rcSendTable` is not sound. -/
theorem not_tableSound_rcSendTable : ¬ TableSound rcSendTable := by
  intro h
  exact not_semSend_rc .plain ((h .rc .plain).1 ⟨rfl, fun h => absurd h (by decide),
    fun h => absurd h (by decide)⟩)

/-- Positive and negative examples of `ImplsSound`. -/
theorem implsSound_examples :
    ImplsSound (.wrap (.cell .plain) .readOnly true) ∧ ¬ ImplsSound (.wrap (.cell .plain) .full true) :=
  ⟨⟨fun _ => (wrap_cell_plain_readOnly_nonvacuous true).2, trivial⟩,
    fun h => not_semSync_cell .plain (h.1 rfl)⟩

/-- Positive and negative examples of `WrapFree`. -/
theorem wrapFree_examples : WrapFree (.arc (.mutex (.cell .plain))) ∧ ¬ WrapFree (.wrap .plain .full false) :=
  ⟨trivial, id⟩

/-- Negative example of `SyncObligation`: exposing the full shared API of `Cell<plain>`. -/
theorem not_syncObligation_cell_full : ¬ SyncObligation (.cell .plain) .full :=
  fun h => not_semSync_cell .plain ((semSync_wrap_iff_syncObligation _ _ true).mpr h)

end Toy.SendSync
