import ToyWMM.Fence

/-!
# Races in straight-line programs

Happens-before `hb := (po ∪ rf)⁺`, conflicting accesses, and data races, where a conflicting
pair may be exempted when both of its accesses satisfy `NoUnfencedWRIncident` (no unfenced
`po` write→read pair has the access as an endpoint). That predicate is purely syntactic: a
write with no `po`-later read in its thread, and a read with no `po`-earlier write in its
thread, satisfy it vacuously even in a program with no fences at all.

Because programs here are straight-line (no control flow), every conflicting pair of a
program is `hb`-unordered in some well-formed SC execution
(`exists_sc_execution_hb_unordered_of_conflict`, in `ToyWMM.StraightLine`), so race freedom
over all SC executions collapses to a static condition on the program
(`Prog.ConflictsWRFenced`).
-/

namespace Toy.WMM

namespace Exec

variable {n : Nat} (X : Exec n)

/-- The happens-before generators `po ∪ rf`. -/
def hbRel : Rel n := fun a b => X.po a b || X.rf a b

/-- Happens-before `hb := (po ∪ rf)⁺`. -/
def HB (a b : Fin n) : Prop := Rel.Path X.hbRel a b

instance (a b : Fin n) : Decidable (X.HB a b) := decidable_of_iff _ Rel.warshall_iff_path

/-- Conflicting accesses: memory accesses (not initialisation writes) of different threads
to the same location, at least one of them a write. -/
def Conflict (a b : Fin n) : Prop :=
  (X.ev a).isAccess = true ∧ (X.ev b).isAccess = true ∧ (X.ev a).isInit = false ∧
    (X.ev b).isInit = false ∧ (X.ev a).tid ≠ (X.ev b).tid ∧ (X.ev a).loc = (X.ev b).loc ∧
    ((X.ev a).isWrite = true ∨ (X.ev b).isWrite = true)

/-- No unfenced write→read pair is incident to `a`: if `a` is a write, a fence separates it
from every `po`-later read; if `a` is a read, a fence separates every `po`-earlier write from
it. Holds vacuously for a write with no `po`-later read and for a read with no `po`-earlier
write, and trivially for fences. -/
def NoUnfencedWRIncident (a : Fin n) : Prop :=
  ((X.ev a).isWrite = true →
      ∀ b, X.po a b = true → (X.ev b).isRead = true → X.fenceOrd a b = true) ∧
    ((X.ev a).isRead = true →
      ∀ b, X.po b a = true → (X.ev b).isWrite = true → X.fenceOrd b a = true)

/-- A data race: conflicting accesses unordered by `hb`, not both satisfying
`NoUnfencedWRIncident`. -/
def Race (a b : Fin n) : Prop :=
  X.Conflict a b ∧ ¬ X.HB a b ∧ ¬ X.HB b a ∧ ¬ (X.NoUnfencedWRIncident a ∧ X.NoUnfencedWRIncident b)

/-- No data race. -/
def RaceFree : Prop := ∀ a b, ¬ X.Race a b

/-- Variant: a conflicting pair is exempt when *either* access satisfies
`NoUnfencedWRIncident`. -/
def RaceEither (a b : Fin n) : Prop :=
  X.Conflict a b ∧ ¬ X.HB a b ∧ ¬ X.HB b a ∧ ¬ (X.NoUnfencedWRIncident a ∨ X.NoUnfencedWRIncident b)

/-- No data race in the "either side" sense. -/
def RaceFreeEither : Prop := ∀ a b, ¬ X.RaceEither a b

instance (a b : Fin n) : Decidable (X.Conflict a b) := inferInstanceAs (Decidable (_ ∧ _))
instance (a : Fin n) : Decidable (X.NoUnfencedWRIncident a) := inferInstanceAs (Decidable (_ ∧ _))
instance (a b : Fin n) : Decidable (X.Race a b) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable X.RaceFree := inferInstanceAs (Decidable (∀ _ _, _))
instance (a b : Fin n) : Decidable (X.RaceEither a b) := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable X.RaceFreeEither := inferInstanceAs (Decidable (∀ _ _, _))

/-- `NoUnfencedWRIncident` depends only on `po` and event kinds. -/
theorem noUnfencedWRIncident_congr {X Y : Exec n} (hpo : X.po = Y.po)
    (hk : ∀ i, (X.ev i).kind = (Y.ev i).kind) (a : Fin n) :
    X.NoUnfencedWRIncident a ↔ Y.NoUnfencedWRIncident a := by
  have hw : ∀ i, (X.ev i).isWrite = (Y.ev i).isWrite := fun i => by
    unfold Event.isWrite; rw [hk i]
  have hr : ∀ i, (X.ev i).isRead = (Y.ev i).isRead := fun i => by
    unfold Event.isRead; rw [hk i]
  have hf : ∀ i, (X.ev i).isFence = (Y.ev i).isFence := fun i => by
    unfold Event.isFence; rw [hk i]
  have hacc : ∀ i, (X.ev i).isAccess = (Y.ev i).isAccess := fun i => by
    unfold Event.isAccess; rw [hf i]
  simp only [NoUnfencedWRIncident, fenceOrd, hw, hr, hf, hacc, hpo]

/-- `Conflict` depends only on event kinds, threads and locations. -/
theorem conflict_congr {X Y : Exec n} (hk : ∀ i, (X.ev i).kind = (Y.ev i).kind)
    (ht : ∀ i, (X.ev i).tid = (Y.ev i).tid) (hl : ∀ i, (X.ev i).loc = (Y.ev i).loc)
    (a b : Fin n) : X.Conflict a b ↔ Y.Conflict a b := by
  have hw : ∀ i, (X.ev i).isWrite = (Y.ev i).isWrite := fun i => by
    unfold Event.isWrite; rw [hk i]
  have hi : ∀ i, (X.ev i).isInit = (Y.ev i).isInit := fun i => by
    unfold Event.isInit; rw [hk i]
  have hacc : ∀ i, (X.ev i).isAccess = (Y.ev i).isAccess := fun i => by
    unfold Event.isAccess Event.isFence; rw [hk i]
  simp only [Conflict, hw, hi, hacc, ht, hl]

end Exec

/-! ## The skeleton execution of a program -/

/-- The events and `po` of a program, with empty `rf` and `co`. Fencing and conflict depend
only on this skeleton. -/
def skel (P : Prog) : Exec (layout P).length where
  ev i := (layout P)[i]
  po a b := (!((layout P)[a]).isInit && !((layout P)[b]).isInit &&
    ((layout P)[a]).tid == ((layout P)[b]).tid) && decide (a.val < b.val)
  rf _ _ := false
  co _ _ := false

theorem ExecOf.skel_facts {P : Prog} {X : Exec (layout P).length} (hX : ExecOf P X) :
    X.po = (skel P).po ∧ (∀ i, (X.ev i).kind = ((skel P).ev i).kind) ∧
      (∀ i, (X.ev i).tid = ((skel P).ev i).tid) ∧ (∀ i, (X.ev i).loc = ((skel P).ev i).loc) := by
  have hget : ∀ i : Fin (layout P).length, (layout P).getD i.val default = (layout P)[i] := by
    intro i; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]; rfl
  have hk : ∀ i, (X.ev i).kind = ((skel P).ev i).kind := fun i => by
    rw [hX.kind, hget]; rfl
  have ht : ∀ i, (X.ev i).tid = ((skel P).ev i).tid := fun i => by rw [hX.tid, hget]; rfl
  have hl : ∀ i, (X.ev i).loc = ((skel P).ev i).loc := fun i => by rw [hX.loc, hget]; rfl
  refine ⟨?_, hk, ht, hl⟩
  funext a b
  rw [hX.po]
  have hi : ∀ i, (X.ev i).isInit = ((layout P)[i]).isInit := fun i => by
    unfold Event.isInit; rw [hk i]; rfl
  simp only [Exec.sameThread, hi, ht]
  rfl

/-- Transfer of "every access is fenced" from the skeleton to every execution. -/
theorem ExecOf.noUnfencedWRIncident_of_skel {P : Prog} {n : Nat} {X : Exec n} (hX : ExecOf P X)
    (h : ∀ a, (skel P).NoUnfencedWRIncident a) : ∀ a, X.NoUnfencedWRIncident a := by
  have hn := hX.length
  subst hn
  obtain ⟨hpo, hk, _, _⟩ := hX.skel_facts
  exact fun a => (Exec.noUnfencedWRIncident_congr hpo hk a).mpr (h a)

/-- Transfer of "every conflicting pair has a fenced side" from the skeleton. -/
theorem ExecOf.fencedSide_of_skel {P : Prog} {n : Nat} {X : Exec n} (hX : ExecOf P X)
    (h : ∀ a b, (skel P).Conflict a b → (skel P).NoUnfencedWRIncident a ∨ (skel P).NoUnfencedWRIncident b) :
    ∀ a b, X.Conflict a b → X.NoUnfencedWRIncident a ∨ X.NoUnfencedWRIncident b := by
  have hn := hX.length
  subst hn
  obtain ⟨hpo, hk, ht, hl⟩ := hX.skel_facts
  intro a b hc
  rcases h a b ((Exec.conflict_congr hk ht hl a b).mp hc) with h' | h'
  · exact Or.inl ((Exec.noUnfencedWRIncident_congr hpo hk a).mpr h')
  · exact Or.inr ((Exec.noUnfencedWRIncident_congr hpo hk b).mpr h')

/-- Transfer of "no conflicting pair" from the skeleton to every execution. -/
theorem ExecOf.noConflict_of_skel {P : Prog} {n : Nat} {X : Exec n} (hX : ExecOf P X)
    (h : ∀ a b, ¬ (skel P).Conflict a b) : ∀ a b, ¬ X.Conflict a b := by
  have hn := hX.length
  subst hn
  obtain ⟨_, hk, ht, hl⟩ := hX.skel_facts
  exact fun a b hc => h a b ((Exec.conflict_congr hk ht hl a b).mp hc)

/-! ## Static conditions on programs -/

/-- Every conflicting pair of accesses of `P` has both accesses satisfying
`NoUnfencedWRIncident` (checked on the skeleton execution, which fixes events and `po`). -/
def Prog.ConflictsWRFenced (P : Prog) : Prop :=
  ∀ a b, (skel P).Conflict a b → (skel P).NoUnfencedWRIncident a ∧ (skel P).NoUnfencedWRIncident b

/-- Every conflicting pair of accesses of `P` has at least one access satisfying
`NoUnfencedWRIncident`. -/
def Prog.ConflictsWRFencedEither (P : Prog) : Prop :=
  ∀ a b, (skel P).Conflict a b → (skel P).NoUnfencedWRIncident a ∨ (skel P).NoUnfencedWRIncident b

instance (P : Prog) : Decidable P.ConflictsWRFenced := inferInstanceAs (Decidable (∀ _ _, _))
instance (P : Prog) : Decidable P.ConflictsWRFencedEither :=
  inferInstanceAs (Decidable (∀ _ _, _))

end Toy.WMM
