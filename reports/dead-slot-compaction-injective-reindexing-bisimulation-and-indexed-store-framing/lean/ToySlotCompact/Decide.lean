import ToySlotCompact.WP
import ToySlotCompact.Liveness

/-!
# Decision helpers for concrete instances

Boolean checks that imply the hypotheses of the main results on concrete programs, determinism
of `exec`, and a family of simple postconditions. Used by the examples, counterexamples and
non-vacuity witnesses.
-/

namespace Toy.SlotCompact

variable {N M : Nat}

/-- Boolean check implying `DbgReadsLive`. -/
def checkDbgLive (p : Prog N) (L : Ann N) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => match ins with
      | .dbg e => (List.finRange N).all fun i => !e.reads i || L pc i
      | _ => true

theorem dbgReadsLive_of_check {p : Prog N} {L : Ann N} (h : checkDbgLive p L = true) :
    DbgReadsLive p L := by
  intro pc e hins i hi
  have := (all_points_iff p _).mp h pc _ hins
  have := List.all_eq_true.mp this i (List.mem_finRange i)
  simpa [hi] using this

/-- Boolean check implying `DbgReadsKept`. -/
def checkDbgKept (p : Prog N) (L : Ann N) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => match ins with
      | .dbg e => (List.finRange N).all fun i => !e.reads i || Kept p L i
      | _ => true

theorem dbgReadsKept_of_check {p : Prog N} {L : Ann N} (h : checkDbgKept p L = true) :
    DbgReadsKept p L := by
  intro pc e hins i hi
  have := (all_points_iff p _).mp h pc _ hins
  have := List.all_eq_true.mp this i (List.mem_finRange i)
  simpa [hi] using this

/-- Boolean check implying `NoAssignClobber`. -/
def checkNoAssignClobber (p : Prog N) (L : Ann N) (π : Compaction p L M) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => match ins with
      | .assign d _ => (List.finRange N).all fun i =>
          decide (i = d) || !L (pc + 1) i || !Kept p L i || !Kept p L d ||
            decide (π.get? i ≠ π.get? d)
      | _ => true

theorem noAssignClobber_of_check {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : checkNoAssignClobber p L π = true) : NoAssignClobber p L π := by
  intro pc d e hins hd i hi hne hl heq
  have := (all_points_iff p _).mp h pc _ hins
  have := List.all_eq_true.mp this i (List.mem_finRange i)
  simp [hne, hl, hi, hd, π.get?_of_kept hi, π.get?_of_kept hd, heq] at this

/-- Per-marker part of `checkNoMarkerClobber`. -/
def markerOK (p : Prog N) (L : Ann N) (π : Compaction p L M) (pc : Nat) (j : Fin N) : Bool :=
  (List.finRange N).all fun i =>
    decide (i = j) || !L (pc + 1) i || !Kept p L i || !Kept p L j ||
      decide (π.get? i ≠ π.get? j)

/-- Boolean check implying `NoMarkerClobber`. -/
def checkNoMarkerClobber (p : Prog N) (L : Ann N) (π : Compaction p L M) : Bool :=
  (List.range p.length).all fun pc =>
    match p[pc]? with
    | none => true
    | some ins => match ins with
      | .storageLive j => markerOK p L π pc j
      | .storageDead j => markerOK p L π pc j
      | _ => true

theorem noMarkerClobber_of_check {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : checkNoMarkerClobber p L π = true) : NoMarkerClobber p L π := by
  intro pc j hins hj i hi hne hl heq
  rcases hins with hins | hins
  · have := (all_points_iff p _).mp h pc _ hins
    have := List.all_eq_true.mp this i (List.mem_finRange i)
    simp [hne, hl, hi, hj, π.get?_of_kept hi, π.get?_of_kept hj, heq] at this
  · have := (all_points_iff p _).mp h pc _ hins
    have := List.all_eq_true.mp this i (List.mem_finRange i)
    simp [hne, hl, hi, hj, π.get?_of_kept hi, π.get?_of_kept hj, heq] at this

/-- Boolean check implying `Function.Injective π`. -/
def checkInjective (p : Prog N) (L : Ann N) (π : Compaction p L M) : Bool :=
  (List.finRange N).all fun i => (List.finRange N).all fun j =>
    decide (i = j) || !Kept p L i || !Kept p L j || decide (π.get? i ≠ π.get? j)

theorem injective_of_check {p : Prog N} {L : Ann N} {π : Compaction p L M}
    (h : checkInjective p L π = true) : Function.Injective π := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
  apply Subtype.ext
  apply Classical.byContradiction
  intro hne
  have := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j
    (List.mem_finRange j)
  simp [hne, hi, hj, π.get?_of_kept hi, π.get?_of_kept hj, heq] at this

/-- Boolean check implying `InjOnLiveAt p L π pc`. -/
def checkInjOnLiveAt (p : Prog N) (L : Ann N) (π : Compaction p L M) (pc : Nat) : Bool :=
  (List.finRange N).all fun i => (List.finRange N).all fun j =>
    decide (i = j) || !L pc i || !L pc j || !Kept p L i || !Kept p L j ||
      decide (π.get? i ≠ π.get? j)

theorem injOnLiveAt_of_check {p : Prog N} {L : Ann N} {π : Compaction p L M} {pc : Nat}
    (h : checkInjOnLiveAt p L π pc = true) : InjOnLiveAt p L π pc := by
  intro i j hi hj hli hlj heq
  apply Classical.byContradiction
  intro hne
  have := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j
    (List.mem_finRange j)
  simp [hne, hi, hj, hli, hlj, π.get?_of_kept hi, π.get?_of_kept hj, heq] at this

/-! ## Determinism of `exec` -/

theorem exec_mono {p : Prog N} : ∀ {n k : Nat} {s sf : State N}, exec p n s = some sf →
    exec p (n + k) s = some sf := by
  intro n
  induction n with
  | zero => intro k s sf h; simp [exec] at h
  | succ n ih =>
    intro k s sf h
    rw [Nat.succ_add]
    simp only [exec] at h ⊢
    cases hs : step p s with
    | running s' e => rw [hs] at h; exact ih h
    | halted s' _ => rw [hs] at h; exact h
    | stuck => rw [hs] at h; simp at h

theorem exec_det {p : Prog N} {n m : Nat} {s a b : State N} (ha : exec p n s = some a)
    (hb : exec p m s = some b) : a = b := by
  have h1 := exec_mono (k := m) ha
  have h2 := exec_mono (k := n) hb
  rw [Nat.add_comm] at h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- When the run is known, the weakest precondition is the postcondition of the final state. -/
theorem wp_iff_of_exec {p : Prog N} {n : Nat} {s sf : State N} (h : exec p n s = some sf)
    (Q : State N → Prop) : wp p Q s ↔ Q sf := by
  constructor
  · rintro ⟨m, sf', hm, hq⟩
    rw [exec_det h hm]
    exact hq
  · intro hq
    exact ⟨n, sf, h, hq⟩

/-! ## Simple postconditions -/

/-- "When halted at `h`, slot `j` holds `v`." -/
def postAt (h : Nat) (j : Fin N) (v : Nat) : State N → Prop := fun s => s.pc = h → s.st j = v

theorem dependsOnlyOnLive_postAt {p : Prog N} {L : Ann N} {h : Nat} {j : Fin N} (v : Nat)
    (hL : L h j = true) : DependsOnlyOnLive p L (postAt h j v) := by
  intro s t _ hpc hag
  unfold postAt
  rw [← hpc]
  constructor
  · intro H h1
    rw [← hag j (h1 ▸ hL)]
    exact H h1
  · intro H h1
    rw [hag j (h1 ▸ hL)]
    exact H h1

/-- `postAt` of a kept slot corresponds to its transport under the kept-slot relation. -/
theorem keptRel_postAt_iff {p : Prog N} {L : Ann N} {π : Compaction p L M} {h : Nat} {j : Fin N}
    (v : Nat) (hk : Kept p L j = true) :
    ∀ s s', IsHalt p s.pc → KeptRel p L π s s' → (postAt h j v s ↔ pullPost π (postAt h j v) s') := by
  intro s s' _ ⟨hpc, hst⟩
  unfold pullPost postAt
  simp only [pullStore_kept π s'.st hk, hst j hk, hpc]

end Toy.SlotCompact
