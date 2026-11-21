import ToyDropFlags.AnalysisFacts

/-!
# Helpers for the necessity results

Path witnesses from the one-pass analyses, a simulation of elaborated runs along source paths,
and the behaviour of drop ladders under an exhausted input.
-/

namespace Toy.DropFlags

/-! ## Types, atoms, units -/

theorem Ty.atoms_isMovePath : ∀ (t : Ty) (r : Path), r ∈ t.atoms → t.isMovePath r = true := by
  intro t
  induction t with
  | leaf => intro r hr; simp [Ty.atoms] at hr; subst hr; rfl
  | pair dd a b iha ihb =>
    intro r hr
    cases dd with
    | true => simp [Ty.atoms] at hr; subst hr; rfl
    | false =>
      simp only [Ty.atoms, List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
      · simpa [Ty.isMovePath] using iha r' hr'
      · simpa [Ty.isMovePath] using ihb r' hr'

theorem Ty.atom_prefix_eq : ∀ (t : Ty) (r q : Path), r ∈ t.atoms → t.isMovePath q = true →
    r <+: q → r = q := by
  intro t
  induction t with
  | leaf =>
    intro r q hr hq _
    simp [Ty.atoms] at hr; subst hr
    cases q with
    | nil => rfl
    | cons x xs => simp [Ty.isMovePath] at hq
  | pair dd a b iha ihb =>
    intro r q hr hq hpre
    cases dd with
    | true =>
      simp [Ty.atoms] at hr; subst hr
      cases q with
      | nil => rfl
      | cons x xs => simp [Ty.isMovePath] at hq
    | false =>
      simp only [Ty.atoms, List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
      · cases q with
        | nil => simp at hpre
        | cons x q' =>
          rw [List.cons_prefix_cons] at hpre
          obtain ⟨rfl, hp'⟩ := hpre
          simp only [Ty.isMovePath] at hq
          rw [iha r' q' hr' hq hp']
      · cases q with
        | nil => simp at hpre
        | cons x q' =>
          rw [List.cons_prefix_cons] at hpre
          obtain ⟨rfl, hp'⟩ := hpre
          simp only [Ty.isMovePath] at hq
          rw [ihb r' q' hr' hq hp']

theorem Ty.atom_has_unit : ∀ (t : Ty) (r : Path), r ∈ t.atoms → ∃ q ∈ t.units, r <+: q := by
  intro t
  induction t with
  | leaf => intro r hr; simp [Ty.atoms] at hr; subst hr; exact ⟨[], by simp [Ty.units], List.prefix_refl _⟩
  | pair dd a b iha ihb =>
    intro r hr
    cases dd with
    | true =>
      simp [Ty.atoms] at hr; subst hr
      exact ⟨[], by simp [Ty.units], List.prefix_refl _⟩
    | false =>
      simp only [Ty.atoms, List.mem_append, List.mem_map] at hr
      rcases hr with ⟨r', hr', rfl⟩ | ⟨r', hr', rfl⟩
      · obtain ⟨q, hq, hp⟩ := iha r' hr'
        refine ⟨false :: q, ?_, ?_⟩
        · simp [Ty.units, hq]
        · rw [List.cons_prefix_cons]; exact ⟨rfl, hp⟩
      · obtain ⟨q, hq, hp⟩ := ihb r' hr'
        refine ⟨true :: q, ?_, ?_⟩
        · simp [Ty.units, hq]
        · rw [List.cons_prefix_cons]; exact ⟨rfl, hp⟩

theorem mem_placesFrom (f : Ty → List Path) :
    ∀ (ls : List Ty) (i : Nat) (q : Place), q ∈ placesFrom f i ls →
      i ≤ q.loc ∧ ∃ t, ls[q.loc - i]? = some t ∧ q.path ∈ f t := by
  intro ls
  induction ls with
  | nil => intro i q h; simp [placesFrom] at h
  | cons t ts ih =>
    intro i q h
    simp only [placesFrom, List.mem_append, List.mem_map] at h
    rcases h with ⟨r, hr, rfl⟩ | h
    · exact ⟨Nat.le_refl _, t, by simp, hr⟩
    · obtain ⟨hle, t', ht', hp⟩ := ih (i + 1) q h
      refine ⟨by omega, t', ?_, hp⟩
      have : q.loc - i = (q.loc - (i + 1)) + 1 := by omega
      rw [this]
      simpa using ht'

theorem placesFrom_mem (f : Ty → List Path) :
    ∀ (ls : List Ty) (i k : Nat) (t : Ty) (r : Path), ls[k]? = some t → r ∈ f t →
      (⟨i + k, r⟩ : Place) ∈ placesFrom f i ls := by
  intro ls
  induction ls with
  | nil => intro i k t r h; simp at h
  | cons t0 ts ih =>
    intro i k t r hk hr
    simp only [placesFrom, List.mem_append, List.mem_map]
    cases k with
    | zero =>
      simp at hk; subst hk
      exact Or.inl ⟨r, hr, by simp⟩
    | succ k =>
      right
      have h := ih (i + 1) k t r (by simpa using hk) hr
      have : i + (k + 1) = i + 1 + k := by omega
      rw [this]; exact h

theorem mem_allAtoms_iff (ls : List Ty) (b : Place) (h : b ∈ allAtoms ls) :
    ∃ t, ls[b.loc]? = some t ∧ b.path ∈ t.atoms := by
  have := mem_placesFrom Ty.atoms ls 0 b h
  simpa using this.2

theorem mem_allUnits_of (ls : List Ty) (l : Nat) (t : Ty) (r : Path) (h : ls[l]? = some t)
    (hr : r ∈ t.units) : (⟨l, r⟩ : Place) ∈ allUnits ls := by
  have := placesFrom_mem Ty.units ls 0 l t r h hr
  unfold allUnits
  simpa using this

theorem covers_iff (p q : Place) : p.covers q = true ↔ p.loc = q.loc ∧ p.path <+: q.path := by
  simp [Place.covers, List.isPrefixOf_iff_prefix]

theorem covers_trans {p q r : Place} (h1 : p.covers q = true) (h2 : q.covers r = true) :
    p.covers r = true := by
  rw [covers_iff] at *
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem mem_unitsUnder (ls : List Ty) (p u : Place) :
    u ∈ unitsUnder ls p ↔ u ∈ allUnits ls ∧ p.covers u = true := by
  simp [unitsUnder]

theorem mem_atomsOf (ls : List Ty) (p b : Place) :
    b ∈ atomsOf ls p ↔ b ∈ allAtoms ls ∧ p.overlaps b = true := by
  simp [atomsOf]

/-- Two places covering a common unit overlap. -/
theorem overlaps_of_covers_common {p b u : Place} (hp : p.covers u = true) (hb : b.covers u = true) :
    p.overlaps b = true := by
  rw [covers_iff] at hp hb
  simp only [Place.overlaps, Bool.or_eq_true]
  rcases List.prefix_or_prefix_of_prefix hp.2 hb.2 with h | h
  · left; rw [covers_iff]; exact ⟨hp.1.trans hb.1.symm, h⟩
  · right; rw [covers_iff]; exact ⟨hb.1.trans hp.1.symm, h⟩

/-- A move place covers every atom it overlaps. -/
theorem covers_of_mem_atomsOf (ls : List Ty) (p b : Place) (hp : isMovePlace ls p = true)
    (hb : b ∈ atomsOf ls p) : p.covers b = true := by
  rw [mem_atomsOf] at hb
  obtain ⟨hbA, hov⟩ := hb
  simp only [Place.overlaps, Bool.or_eq_true] at hov
  rcases hov with h | h
  · exact h
  · rw [covers_iff] at h ⊢
    obtain ⟨t, ht, hbt⟩ := mem_allAtoms_iff ls b hbA
    unfold isMovePlace at hp
    rw [← h.1, ht] at hp
    simp only at hp
    have := Ty.atom_prefix_eq t b.path p.path hbt hp h.2
    exact ⟨h.1.symm, by rw [this]; exact List.prefix_refl _⟩

/-- Distinct atoms share no unit. -/
theorem atom_eq_of_common_unit (ls : List Ty) (b c u : Place) (hb : b ∈ allAtoms ls)
    (hc : c ∈ allAtoms ls) (hbu : b.covers u = true) (hcu : c.covers u = true) : b = c := by
  obtain ⟨t, ht, hbt⟩ := mem_allAtoms_iff ls b hb
  obtain ⟨t', ht', hct⟩ := mem_allAtoms_iff ls c hc
  rw [covers_iff] at hbu hcu
  have hloc : b.loc = c.loc := hbu.1.trans hcu.1.symm
  rw [hloc, ht'] at ht
  cases ht
  have hpath : b.path = c.path := by
    rcases List.prefix_or_prefix_of_prefix hbu.2 hcu.2 with h | h
    · exact Ty.atom_prefix_eq t _ _ hbt (Ty.atoms_isMovePath t _ hct) h
    · exact (Ty.atom_prefix_eq t _ _ hct (Ty.atoms_isMovePath t _ hbt) h).symm
  cases b; cases c
  simp_all

/-- Every atom has a unit. -/
theorem exists_unit_of_atom (ls : List Ty) (b : Place) (hb : b ∈ allAtoms ls) :
    ∃ u, u ∈ unitsUnder ls b := by
  obtain ⟨t, ht, hbt⟩ := mem_allAtoms_iff ls b hb
  obtain ⟨q, hq, hpre⟩ := Ty.atom_has_unit t b.path hbt
  refine ⟨⟨b.loc, q⟩, ?_⟩
  rw [mem_unitsUnder]
  exact ⟨mem_allUnits_of ls b.loc t q ht hq, by rw [covers_iff]; exact ⟨rfl, hpre⟩⟩

/-- A unit of an atom not overlapping `p` is not under `p`. -/
theorem not_mem_unitsUnder_of_not_mem_atomsOf (ls : List Ty) (p b u : Place)
    (hb : b ∈ allAtoms ls) (hnb : b ∉ atomsOf ls p) (hu : u ∈ unitsUnder ls b) :
    u ∉ unitsUnder ls p := by
  intro hup
  rw [mem_unitsUnder] at hu hup
  apply hnb
  rw [mem_atomsOf]
  exact ⟨hb, overlaps_of_covers_common hup.2 hu.2⟩

/-- A unit of an atom inside move place `p` is under `p`. -/
theorem mem_unitsUnder_of_mem_atomsOf (ls : List Ty) (p b u : Place)
    (hp : isMovePlace ls p = true) (hb : b ∈ atomsOf ls p) (hu : u ∈ unitsUnder ls b) :
    u ∈ unitsUnder ls p := by
  rw [mem_unitsUnder] at hu ⊢
  exact ⟨hu.1, covers_trans (covers_of_mem_atomsOf ls p b hp hb) hu.2⟩

/-! ## Logs -/

theorem destroyCount_append (l1 l2 : List Event) (v : Nat) :
    destroyCount (l1 ++ l2) v = destroyCount l1 v + destroyCount l2 v := by
  simp [destroyCount, List.countP_append]

theorem createdIds_append (l1 l2 : List Event) :
    createdIds (l1 ++ l2) = createdIds l1 ++ createdIds l2 := by
  simp [createdIds, List.filterMap_append]

theorem mem_createdIds_append_left {l1 : List Event} (l2 : List Event) {v : Nat}
    (h : v ∈ createdIds l1) : v ∈ createdIds (l1 ++ l2) := by
  rw [createdIds_append]; exact List.mem_append_left _ h

theorem destroyCount_pos_of_mem_drop {l : List Event} {v : Nat} (h : Event.drop v ∈ l) :
    1 ≤ destroyCount l v := by
  unfold destroyCount
  exact List.countP_pos_iff.2 ⟨_, h, by simp⟩

theorem destroyCount_pos_of_mem_consume {l : List Event} {v : Nat} (h : Event.consume v ∈ l) :
    1 ≤ destroyCount l v := by
  unfold destroyCount
  exact List.countP_pos_iff.2 ⟨_, h, by simp⟩

theorem mem_destroyedIds_of_pos {l : List Event} {v : Nat} (h : 1 ≤ destroyCount l v) :
    v ∈ destroyedIds l := by
  unfold destroyCount at h
  obtain ⟨e, he, hp⟩ := List.countP_pos_iff.1 h
  unfold destroyedIds
  rw [List.mem_filterMap]
  refine ⟨e, he, ?_⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with rfl | rfl <;> rfl

theorem destroyCount_eq_zero_of {l : List Event} {v : Nat}
    (h : ∀ e ∈ l, e ≠ .consume v ∧ e ≠ .drop v) : destroyCount l v = 0 := by
  unfold destroyCount
  rw [List.countP_eq_zero]
  intro e he hp
  simp only [Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with hp | hp
  · exact (h e he).1 hp
  · exact (h e he).2 hp

theorem mem_destroyEvents {mk : Nat → Event} {mem : Place → Option Nat} {us : List Place}
    {e : Event} (h : e ∈ destroyEvents mk mem us) :
    ∃ u ∈ us, (mem u = none ∧ e = .garbage) ∨ ∃ v, mem u = some v ∧ e = mk v := by
  unfold destroyEvents at h
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h
  refine ⟨u, hu, ?_⟩
  cases hm : mem u with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some v => exact Or.inr ⟨v, rfl, rfl⟩

theorem garbage_mem_destroyEvents {mk : Nat → Event} {mem : Place → Option Nat} {us : List Place}
    {u : Place} (hu : u ∈ us) (hm : mem u = none) : Event.garbage ∈ destroyEvents mk mem us := by
  unfold destroyEvents
  rw [List.mem_map]
  exact ⟨u, hu, by rw [hm]⟩

theorem mk_mem_destroyEvents {mk : Nat → Event} {mem : Place → Option Nat} {us : List Place}
    {u : Place} {v : Nat} (hu : u ∈ us) (hm : mem u = some v) : mk v ∈ destroyEvents mk mem us := by
  unfold destroyEvents
  rw [List.mem_map]
  exact ⟨u, hu, by rw [hm]⟩

theorem destroyCount_consumeEvents_zero {mem : Place → Option Nat} {us : List Place} {v : Nat}
    (h : ∀ u ∈ us, mem u ≠ some v) : destroyCount (destroyEvents .consume mem us) v = 0 := by
  apply destroyCount_eq_zero_of
  intro e he
  obtain ⟨u, hu, ⟨_, rfl⟩ | ⟨w, hw, rfl⟩⟩ := mem_destroyEvents he
  · exact ⟨by simp, by simp⟩
  · refine ⟨?_, by simp⟩
    intro heq
    cases heq
    exact h u hu hw

theorem destroyCount_dropEvents_zero {mem : Place → Option Nat} {us : List Place} {v : Nat}
    (h : ∀ u ∈ us, mem u ≠ some v) : destroyCount (destroyEvents .drop mem us) v = 0 := by
  apply destroyCount_eq_zero_of
  intro e he
  obtain ⟨u, hu, ⟨_, rfl⟩ | ⟨w, hw, rfl⟩⟩ := mem_destroyEvents he
  · exact ⟨by simp, by simp⟩
  · refine ⟨by simp, ?_⟩
    intro heq
    cases heq
    exact h u hu hw

theorem writeFresh_spec :
    ∀ (us : List Place) (mem : Place → Option Nat) (n : Nat) (log : List Event)
      (mem' : Place → Option Nat) (n' : Nat) (log' : List Event),
      writeFresh us mem n log = (mem', n', log') →
      (∀ u u' v, mem u = some v → mem u' = some v → u = u') →
      (∀ u v, mem u = some v → v < n) →
      (∀ u u' v, mem' u = some v → mem' u' = some v → u = u') ∧
      (∀ u v, mem' u = some v → v < n') ∧
      n ≤ n' ∧
      (∃ cs, log' = log ++ cs ∧ ∀ e ∈ cs, ∃ v, e = .create v) ∧
      (∀ q, q ∉ us → mem' q = mem q) ∧
      (∀ q ∈ us, ∃ v, mem' q = some v ∧ v ∈ createdIds log' ∧ n ≤ v) := by
  intro us
  induction us with
  | nil =>
    intro mem n log mem' n' log' hw hinj hlt
    simp only [writeFresh, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    refine ⟨hinj, hlt, Nat.le_refl _, ⟨[], by simp, by simp⟩, fun _ _ => rfl, by simp⟩
  | cons u us ih =>
    intro mem n log mem' n' log' hw hinj hlt
    simp only [writeFresh] at hw
    have hinj1 : ∀ a b v, (fun q => if q = u then some n else mem q) a = some v →
        (fun q => if q = u then some n else mem q) b = some v → a = b := by
      intro a b v ha hb
      simp only at ha hb
      by_cases hau : a = u <;> by_cases hbu : b = u
      · rw [hau, hbu]
      · simp only [hau, ite_true, Option.some.injEq] at ha
        simp only [hbu, ite_false] at hb
        subst ha
        exact absurd (hlt b n hb) (Nat.lt_irrefl _)
      · simp only [hbu, ite_true, Option.some.injEq] at hb
        simp only [hau, ite_false] at ha
        subst hb
        exact absurd (hlt a n ha) (Nat.lt_irrefl _)
      · simp only [hau, hbu, ite_false] at ha hb
        exact hinj a b v ha hb
    have hlt1 : ∀ a v, (fun q => if q = u then some n else mem q) a = some v → v < n + 1 := by
      intro a v ha
      simp only at ha
      by_cases hau : a = u
      · simp only [hau, ite_true, Option.some.injEq] at ha; omega
      · simp only [hau, ite_false] at ha; have := hlt a v ha; omega
    obtain ⟨h1, h2, h3, ⟨cs, hcs, hcse⟩, h5, h6⟩ := ih _ _ _ _ _ _ hw hinj1 hlt1
    refine ⟨h1, h2, by omega, ⟨.create n :: cs, by simp [hcs], ?_⟩, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨n, rfl⟩
      · exact hcse e he
    · intro q hq
      rw [h5 q (fun h => hq (List.mem_cons_of_mem _ h))]
      have : q ≠ u := fun h => hq (h ▸ List.mem_cons_self)
      simp [this]
    · intro q hq
      by_cases hqs : q ∈ us
      · obtain ⟨v, hv, hc, hle⟩ := h6 q hqs
        exact ⟨v, hv, hc, by omega⟩
      · have hqu : q = u := by
          rcases List.mem_cons.1 hq with h | h
          · exact h
          · exact absurd h hqs
        refine ⟨n, ?_, ?_, Nat.le_refl _⟩
        · rw [h5 q hqs]; simp [hqu]
        · rw [hcs, createdIds_append, createdIds_append]
          simp [createdIds]

/-! ## The machine invariant along a source path -/

/-- Invariant of the memory and log of a run that has followed a source path whose tracked
initialized-atom set is `live`. -/
structure Inv (ls : List Ty) (mem : Place → Option Nat) (fresh : Nat) (log : List Event)
    (live : Place → Prop) : Prop where
  inj : ∀ u u' v, mem u = some v → mem u' = some v → u = u'
  lt : ∀ u v, mem u = some v → v < fresh
  hi : ∀ v, fresh ≤ v → destroyCount log v = 0
  liveU : ∀ b ∈ allAtoms ls, live b → ∀ u ∈ unitsUnder ls b,
    ∃ v, mem u = some v ∧ v ∈ createdIds log ∧ destroyCount log v = 0
  deadU : ∀ b ∈ allAtoms ls, ¬ live b → ∀ u ∈ unitsUnder ls b,
    mem u = none ∨ ∃ v, mem u = some v ∧ 1 ≤ destroyCount log v

theorem Inv.congr {ls : List Ty} {mem : Place → Option Nat} {n : Nat} {log : List Event}
    {live live' : Place → Prop} (h : ∀ b, live b ↔ live' b) (hi : Inv ls mem n log live) :
    Inv ls mem n log live' := by
  have : live = live' := funext fun b => propext (h b)
  subst this; exact hi

theorem Inv.initial (ls : List Ty) :
    Inv ls (fun _ => none) 0 [] (fun b => b ∈ ([] : List Place)) where
  inj := by intro u u' v h; cases h
  lt := by intro u v h; cases h
  hi := by intro v _; rfl
  liveU := by intro b _ h; cases h
  deadU := by intro b _ _ u _; exact Or.inl rfl

theorem Inv.writeInit {ls : List Ty} {mem : Place → Option Nat} {n : Nat} {log : List Event}
    {live : Place → Prop} {p : Place} (hinv : Inv ls mem n log live)
    (hp : isMovePlace ls p = true) {mem' : Place → Option Nat} {n' : Nat} {log' : List Event}
    (hw : writeFresh (unitsUnder ls p) mem n log = (mem', n', log')) :
    Inv ls mem' n' log' (fun b => live b ∨ b ∈ atomsOf ls p) := by
  obtain ⟨h1, h2, h3, ⟨cs, hcs, hcse⟩, h5, h6⟩ :=
    writeFresh_spec _ _ _ _ _ _ _ hw hinv.inj hinv.lt
  have hdc : ∀ v, destroyCount log' v = destroyCount log v := by
    intro v
    rw [hcs, destroyCount_append]
    have : destroyCount cs v = 0 := by
      apply destroyCount_eq_zero_of
      intro e he
      obtain ⟨w, rfl⟩ := hcse e he
      exact ⟨by simp, by simp⟩
    omega
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro v hv
    rw [hdc]
    exact hinv.hi v (by omega)
  · intro b hb hlive u hu
    by_cases hbp : b ∈ atomsOf ls p
    · obtain ⟨v, hv, hc, hle⟩ := h6 u (mem_unitsUnder_of_mem_atomsOf ls p b u hp hbp hu)
      exact ⟨v, hv, hc, by rw [hdc]; exact hinv.hi v hle⟩
    · have hl : live b := by
        rcases hlive with h | h
        · exact h
        · exact absurd h hbp
      have hnu := not_mem_unitsUnder_of_not_mem_atomsOf ls p b u hb hbp hu
      obtain ⟨v, hv, hc, h0⟩ := hinv.liveU b hb hl u hu
      refine ⟨v, by rw [h5 u hnu]; exact hv, ?_, by rw [hdc]; exact h0⟩
      rw [hcs]; exact mem_createdIds_append_left _ hc
  · intro b hb hdead u hu
    have hl : ¬ live b := fun h => hdead (Or.inl h)
    have hbp : b ∉ atomsOf ls p := fun h => hdead (Or.inr h)
    have hnu := not_mem_unitsUnder_of_not_mem_atomsOf ls p b u hb hbp hu
    rw [h5 u hnu]
    rcases hinv.deadU b hb hl u hu with h | ⟨v, hv, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, by rw [hdc]; exact hc⟩

theorem Inv.consume {ls : List Ty} {mem : Place → Option Nat} {n : Nat} {log : List Event}
    {live : Place → Prop} {p : Place} (hinv : Inv ls mem n log live)
    (hp : isMovePlace ls p = true) :
    Inv ls mem n (log ++ destroyEvents .consume mem (unitsUnder ls p))
      (fun b => live b ∧ b ∉ atomsOf ls p) := by
  refine ⟨hinv.inj, hinv.lt, ?_, ?_, ?_⟩
  · intro v hv
    rw [destroyCount_append, hinv.hi v hv, destroyCount_consumeEvents_zero]
    intro u _ hu
    have := hinv.lt u v hu
    omega
  · intro b hb hlive u hu
    obtain ⟨v, hv, hc, h0⟩ := hinv.liveU b hb hlive.1 u hu
    refine ⟨v, hv, mem_createdIds_append_left _ hc, ?_⟩
    rw [destroyCount_append, h0, destroyCount_consumeEvents_zero]
    intro u' hu' hu'v
    have := hinv.inj u u' v hv hu'v
    subst this
    exact not_mem_unitsUnder_of_not_mem_atomsOf ls p b u hb hlive.2 hu hu'
  · intro b hb hdead u hu
    by_cases hbp : b ∈ atomsOf ls p
    · have hup := mem_unitsUnder_of_mem_atomsOf ls p b u hp hbp hu
      cases hm : mem u with
      | none => exact Or.inl rfl
      | some v =>
        refine Or.inr ⟨v, rfl, ?_⟩
        rw [destroyCount_append]
        have := destroyCount_pos_of_mem_consume (mk_mem_destroyEvents (mk := Event.consume) hup hm)
        omega
    · have hl : ¬ live b := fun h => hdead ⟨h, hbp⟩
      rcases hinv.deadU b hb hl u hu with h | ⟨v, hv, hc⟩
      · exact Or.inl h
      · refine Or.inr ⟨v, hv, ?_⟩
        rw [destroyCount_append]; omega

theorem Inv.consumeAll {ls : List Ty} {mem : Place → Option Nat} {n : Nat} :
    ∀ (args : List Place) (log : List Event) (live : Place → Prop),
      Inv ls mem n log live → (∀ p ∈ args, isMovePlace ls p = true) →
      Inv ls mem n (log ++ args.flatMap (fun p => destroyEvents .consume mem (unitsUnder ls p)))
        (fun b => live b ∧ b ∉ args.flatMap (atomsOf ls)) := by
  intro args
  induction args with
  | nil =>
    intro log live hinv _
    simp only [List.flatMap_nil, List.append_nil]
    exact hinv.congr (fun b => by simp)
  | cons p rest ih =>
    intro log live hinv hargs
    have h1 := hinv.consume (hargs p List.mem_cons_self)
    have h2 := ih _ _ h1 (fun q hq => hargs q (List.mem_cons_of_mem _ hq))
    simp only [List.flatMap_cons, ← List.append_assoc]
    refine h2.congr (fun b => ?_)
    simp only [List.mem_append, not_or]
    exact and_assoc

/-! ## Runs -/

/-- `n` steps lead from `m` with input `inp` to `m'` with input `inp'`. -/
def Reach {L : Type} (rule : PanicRule) (P : TProg L) (n : Nat) (inp : List Bool) (m : Mach L)
    (inp' : List Bool) (m' : Mach L) : Prop :=
  ∀ k, runAux rule P (k + n) inp m = runAux rule P k inp' m'

theorem Reach.refl {L : Type} {rule : PanicRule} {P : TProg L} {inp : List Bool} {m : Mach L} :
    Reach rule P 0 inp m inp m := fun _ => rfl

theorem Reach.trans {L : Type} {rule : PanicRule} {P : TProg L} {n1 n2 : Nat}
    {inp1 inp2 inp3 : List Bool} {m1 m2 m3 : Mach L}
    (h1 : Reach rule P n1 inp1 m1 inp2 m2) (h2 : Reach rule P n2 inp2 m2 inp3 m3) :
    Reach rule P (n1 + n2) inp1 m1 inp3 m3 := by
  intro k
  rw [show k + (n1 + n2) = (k + n2) + n1 by omega, h1, h2]

theorem runAux_succ_nc {L : Type} {rule : PanicRule} {P : TProg L} {k : Nat} {inp : List Bool}
    {m m' : Mach L} (hc : (P.node m.pc).isChoice = false) (hs : step rule P m false = .next m') :
    runAux rule P (k + 1) inp m = runAux rule P k inp m' := by
  simp only [runAux, hc, hs, Bool.false_eq_true, ite_false]

theorem runAux_succ_nc_done {L : Type} {rule : PanicRule} {P : TProg L} {k : Nat}
    {inp : List Bool} {m : Mach L} {r : Result} (hc : (P.node m.pc).isChoice = false)
    (hs : step rule P m false = .done r) :
    runAux rule P (k + 1) inp m = r := by
  simp only [runAux, hc, hs, Bool.false_eq_true, ite_false]

theorem runAux_succ_ch {L : Type} {rule : PanicRule} {P : TProg L} {k : Nat} {inp : List Bool}
    {m m' : Mach L} (hc : (P.node m.pc).isChoice = true)
    (hs : step rule P m (inp.headD false) = .next m') :
    runAux rule P (k + 1) inp m = runAux rule P k inp.tail m' := by
  simp only [runAux, hc, hs, ite_true]

theorem Reach.nc {L : Type} {rule : PanicRule} {P : TProg L} {inp : List Bool} {m m' : Mach L}
    (hc : (P.node m.pc).isChoice = false) (hs : step rule P m false = .next m') :
    Reach rule P 1 inp m inp m' := by
  intro k
  exact runAux_succ_nc hc hs

theorem Reach.ch {L : Type} {rule : PanicRule} {P : TProg L} {b : Bool} {inp : List Bool}
    {m m' : Mach L} (hc : (P.node m.pc).isChoice = true) (hs : step rule P m b = .next m') :
    Reach rule P 1 (b :: inp) m inp m' := by
  intro k
  exact runAux_succ_ch (inp := b :: inp) hc hs

theorem Reach.chNil {L : Type} {rule : PanicRule} {P : TProg L} {m m' : Mach L}
    (hc : (P.node m.pc).isChoice = true) (hs : step rule P m false = .next m') :
    Reach rule P 1 [] m [] m' := by
  intro k
  exact runAux_succ_ch (inp := []) hc hs

section steps
variable {L : Type} {rule : PanicRule} {P : TProg L} {m : Mach L} {b : Bool}

theorem step_init {p : Place} {nx : L} (hn : P.node m.pc = .init p nx) :
    step rule P m b = .next { m with pc := nx,
                                     mem := (writeFresh (unitsUnder P.locals p) m.mem m.fresh m.log).1,
                                     fresh := (writeFresh (unitsUnder P.locals p) m.mem m.fresh m.log).2.1,
                                     log := (writeFresh (unitsUnder P.locals p) m.mem m.fresh m.log).2.2 } := by
  unfold step; rw [hn]

theorem step_move {p : Place} {nx : L} (hn : P.node m.pc = .move p nx) :
    step rule P m b = .next { m with pc := nx,
                                     log := m.log ++ destroyEvents .consume m.mem (unitsUnder P.locals p) } := by
  unfold step; rw [hn]

theorem step_branch {l1 l2 : L} (hn : P.node m.pc = .branch l1 l2) :
    step rule P m b = .next { m with pc := if b then l1 else l2 } := by
  unfold step; rw [hn]

theorem step_goto {l : L} (hn : P.node m.pc = .goto l) :
    step rule P m b = .next { m with pc := l } := by
  unfold step; rw [hn]

theorem step_setFlags {us : List (Place × Bool)} {nx : L} (hn : P.node m.pc = .setFlags us nx) :
    step rule P m b = .next { m with pc := nx, flags := applyFlags us m.flags } := by
  unfold step; rw [hn]

theorem step_test {a : Place} {l1 l2 : L} (hn : P.node m.pc = .test a l1 l2) :
    step rule P m b = .next { m with pc := if m.flags a then l1 else l2 } := by
  unfold step; rw [hn]

theorem step_call_true {args : List Place} {dest : Option Place} {nx un : L}
    (hn : P.node m.pc = .call args dest nx un) :
    step rule P m true = .next { m with pc := un, unwinding := true,
                                        log := m.log ++ args.flatMap (fun p => destroyEvents .consume m.mem (unitsUnder P.locals p)) } := by
  unfold step; rw [hn]; rfl

theorem step_call_false_none {args : List Place} {nx un : L}
    (hn : P.node m.pc = .call args none nx un) :
    step rule P m false = .next { m with pc := nx,
                                         log := m.log ++ args.flatMap (fun p => destroyEvents .consume m.mem (unitsUnder P.locals p)) } := by
  unfold step; rw [hn]; rfl

theorem step_call_false_some {args : List Place} {dd : Place} {nx un : L}
    (hn : P.node m.pc = .call args (some dd) nx un) :
    step rule P m false =
      let log₁ := m.log ++ args.flatMap (fun p => destroyEvents .consume m.mem (unitsUnder P.locals p))
      let w := writeFresh (unitsUnder P.locals dd) m.mem m.fresh log₁
      .next { m with pc := nx, mem := w.1, fresh := w.2.1, log := w.2.2 } := by
  unfold step; rw [hn]; rfl

theorem step_drop_false {a : Place} {nx : L} {un : Option L} (hn : P.node m.pc = .drop a nx un) :
    step rule P m false = .next { m with pc := nx,
                                         log := m.log ++ destroyEvents .drop m.mem (unitsUnder P.locals a) } := by
  unfold step; rw [hn]; rfl

theorem step_ret (hn : P.node m.pc = .ret) : step rule P m b = .done ⟨.returned, m.log⟩ := by
  unfold step; rw [hn]

theorem step_resume (hn : P.node m.pc = .resume) : step rule P m b = .done ⟨.unwound, m.log⟩ := by
  unfold step; rw [hn]

end steps

/-! ## Source edges and their simulation -/

/-- A source edge from node `i` to node `j` that removes the atoms `K` from the tracked set, adds
the atoms `G`, and is selected by the input bits `eb`. -/
inductive Edge (s : SProg) (i : Nat) : Nat → List Place → List Place → List Bool → Prop
  | init {p : Place} {nx : Nat} : s.node i = .init p nx → Edge s i nx [] (atomsOf s.locals p) []
  | move {p : Place} {nx : Nat} : s.node i = .move p nx →
      Edge s i nx (killSet s.locals .fine p) [] []
  | br1 {l1 l2 : Nat} : s.node i = .branch l1 l2 → Edge s i l1 [] [] [true]
  | br2 {l1 l2 : Nat} : s.node i = .branch l1 l2 → Edge s i l2 [] [] [false]
  | callN {args : List Place} {dest : Option Place} {nx un : Nat} :
      s.node i = .call args dest nx un →
      Edge s i nx (args.flatMap (killSet s.locals .fine)) (destAtoms s.locals dest) [false]
  | callU {args : List Place} {dest : Option Place} {nx un : Nat} :
      s.node i = .call args dest nx un →
      Edge s i un (args.flatMap (killSet s.locals .fine)) [] [true]

theorem killSet_fine (ls : List Ty) : killSet ls .fine = atomsOf ls := rfl

theorem edge_sim (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg)
    (hplaces : PlacesAreMovePaths s) {i j : Nat} {K G : List Place} {eb : List Bool}
    (he : Edge s i j K G eb) (hi : i < s.nodes.length) (m : Mach Lbl) (hpc : m.pc = .src i)
    (live : Place → Prop) (hinv : Inv s.locals m.mem m.fresh m.log live) (rest : List Bool) :
    ∃ n m', n ≤ 3 ∧ Reach rule (elaborate .std d s) n (eb ++ rest) m rest m' ∧
      m'.pc = .src j ∧ Inv s.locals m'.mem m'.fresh m'.log (fun b => (live b ∧ b ∉ K) ∨ b ∈ G) := by
  cases he with
  | @init p _ h =>
    have hp : isMovePlace s.locals p = true := hplaces i hi p (by simp [SNode.places, h])
    have hn1 : (elaborate .std d s).node m.pc = .init p (.post i) := by
      rw [hpc]; simp [elaborate, elabNode, hi, h]
    let w := writeFresh (unitsUnder s.locals p) m.mem m.fresh m.log
    let m1 : Mach Lbl := { m with pc := .post i, mem := w.1, fresh := w.2.1, log := w.2.2 }
    obtain ⟨us, hn2⟩ : ∃ us, (elaborate .std d s).node m1.pc = .setFlags us (.src j) := by
      simp only [m1, elaborate, elabNode, h]; exact ⟨_, rfl⟩
    refine ⟨2, { m1 with pc := .src j, flags := applyFlags us m1.flags }, by omega, ?_, rfl, ?_⟩
    · exact (Reach.nc (by rw [hn1]; rfl) (step_init hn1)).trans
        (Reach.nc (by rw [hn2]; rfl) (step_setFlags hn2))
    · exact (hinv.writeInit hp (mem' := w.1) (n' := w.2.1) (log' := w.2.2) rfl).congr
        (fun b => by simp)
  | @move p _ h =>
    have hp : isMovePlace s.locals p = true := hplaces i hi p (by simp [SNode.places, h])
    have hn1 : (elaborate .std d s).node m.pc = .move p (.post i) := by
      rw [hpc]; simp [elaborate, elabNode, hi, h]
    let m1 : Mach Lbl :=
      { m with pc := .post i, log := m.log ++ destroyEvents .consume m.mem (unitsUnder s.locals p) }
    obtain ⟨us, hn2⟩ : ∃ us, (elaborate .std d s).node m1.pc = .setFlags us (.src j) := by
      simp only [m1, elaborate, elabNode, h]; exact ⟨_, rfl⟩
    refine ⟨2, { m1 with pc := .src j, flags := applyFlags us m1.flags }, by omega, ?_, rfl, ?_⟩
    · exact (Reach.nc (by rw [hn1]; rfl) (step_move hn1)).trans
        (Reach.nc (by rw [hn2]; rfl) (step_setFlags hn2))
    · exact (hinv.consume hp).congr (fun b => by simp [killSet_fine])
  | @br1 _ l2 h =>
    have hn1 : (elaborate .std d s).node m.pc = .branch (.src j) (.src l2) := by
      rw [hpc]; simp [elaborate, elabNode, hi, h]
    refine ⟨1, { m with pc := .src j }, by omega, ?_, rfl, ?_⟩
    · exact Reach.ch (by rw [hn1]; rfl) (by rw [step_branch hn1]; rfl)
    · exact hinv.congr (fun b => by simp)
  | @br2 l1 _ h =>
    have hn1 : (elaborate .std d s).node m.pc = .branch (.src l1) (.src j) := by
      rw [hpc]; simp [elaborate, elabNode, hi, h]
    refine ⟨1, { m with pc := .src j }, by omega, ?_, rfl, ?_⟩
    · exact Reach.ch (by rw [hn1]; rfl) (by rw [step_branch hn1]; rfl)
    · exact hinv.congr (fun b => by simp)
  | @callN args dest _ un h =>
    have hargs : ∀ p ∈ args, isMovePlace s.locals p = true :=
      fun p hp => hplaces i hi p (by simp [SNode.places, h, hp])
    obtain ⟨us1, hn1⟩ : ∃ us, (elaborate .std d s).node m.pc = .setFlags us (.pre i) := by
      rw [hpc]; simp only [elaborate, elabNode, hi, h, ite_true]; exact ⟨_, rfl⟩
    let m1 : Mach Lbl := { m with pc := .pre i, flags := applyFlags us1 m.flags }
    have hn2 : (elaborate .std d s).node m1.pc = .call args dest (.post i) (.unw i) := by
      simp only [m1, elaborate, elabNode, h]
    have hc1 := hinv.consumeAll args m.log live hargs
    cases dest with
    | none =>
      let m2 : Mach Lbl := { m1 with pc := .post i,
                                     log := m1.log ++ args.flatMap
                                       (fun p => destroyEvents .consume m1.mem (unitsUnder s.locals p)) }
      obtain ⟨us3, hn3⟩ : ∃ us, (elaborate .std d s).node m2.pc = .setFlags us (.src j) := by
        simp only [m2, elaborate, elabNode, h]; exact ⟨_, rfl⟩
      refine ⟨3, { m2 with pc := .src j, flags := applyFlags us3 m2.flags }, by omega, ?_, rfl, ?_⟩
      · exact ((Reach.nc (by rw [hn1]; rfl) (step_setFlags hn1)).trans
          (Reach.ch (by rw [hn2]; rfl) (step_call_false_none hn2))).trans
          (Reach.nc (by rw [hn3]; rfl) (step_setFlags hn3))
      · exact hc1.congr (fun b => by simp [killSet_fine, destAtoms])
    | some dd =>
      have hpd : isMovePlace s.locals dd = true := hplaces i hi dd (by simp [SNode.places, h])
      let log₁ := m1.log ++ args.flatMap
        (fun p => destroyEvents .consume m1.mem (unitsUnder s.locals p))
      let w := writeFresh (unitsUnder s.locals dd) m1.mem m1.fresh log₁
      let m2 : Mach Lbl := { m1 with pc := .post i, mem := w.1, fresh := w.2.1, log := w.2.2 }
      obtain ⟨us3, hn3⟩ : ∃ us, (elaborate .std d s).node m2.pc = .setFlags us (.src j) := by
        simp only [m2, elaborate, elabNode, h]; exact ⟨_, rfl⟩
      refine ⟨3, { m2 with pc := .src j, flags := applyFlags us3 m2.flags }, by omega, ?_, rfl, ?_⟩
      · exact ((Reach.nc (by rw [hn1]; rfl) (step_setFlags hn1)).trans
          (Reach.ch (by rw [hn2]; rfl) (step_call_false_some hn2))).trans
          (Reach.nc (by rw [hn3]; rfl) (step_setFlags hn3))
      · exact (hc1.writeInit hpd (mem' := w.1) (n' := w.2.1) (log' := w.2.2) rfl).congr
          (fun b => by simp [killSet_fine, destAtoms])
  | @callU args dest nx _ h =>
    have hargs : ∀ p ∈ args, isMovePlace s.locals p = true :=
      fun p hp => hplaces i hi p (by simp [SNode.places, h, hp])
    obtain ⟨us1, hn1⟩ : ∃ us, (elaborate .std d s).node m.pc = .setFlags us (.pre i) := by
      rw [hpc]; simp only [elaborate, elabNode, hi, h, ite_true]; exact ⟨_, rfl⟩
    let m1 : Mach Lbl := { m with pc := .pre i, flags := applyFlags us1 m.flags }
    have hn2 : (elaborate .std d s).node m1.pc = .call args dest (.post i) (.unw i) := by
      simp only [m1, elaborate, elabNode, h]
    have hc1 := hinv.consumeAll args m.log live hargs
    let m2 : Mach Lbl := { m1 with pc := .unw i, unwinding := true,
                                   log := m1.log ++ args.flatMap
                                     (fun p => destroyEvents .consume m1.mem (unitsUnder s.locals p)) }
    have hn3 : (elaborate .std d s).node m2.pc = .goto (.src j) := by
      simp only [m2, elaborate, elabNode, h]
    refine ⟨3, { m2 with pc := .src j }, by omega, ?_, rfl, ?_⟩
    · exact ((Reach.nc (by rw [hn1]; rfl) (step_setFlags hn1)).trans
        (Reach.ch (by rw [hn2]; rfl) (step_call_true hn2))).trans
        (Reach.nc (by rw [hn3]; rfl) (step_goto hn3))
    · exact hc1.congr (fun b => by simp [killSet_fine])

/-! ## Source paths and the run along them -/

/-- Source paths from the entry along index-increasing edges from in-range nodes, with the tracked
initialized-atom set on arrival and the input bits selecting the path. -/
inductive SPath (s : SProg) : Nat → List Place → List Bool → Prop
  | entry : SPath s 0 [] []
  | step {i j : Nat} {P K G : List Place} {bits eb : List Bool} :
      SPath s i P bits → i < s.nodes.length → i < j → Edge s i j K G eb →
      SPath s j (minus P K ++ G) (bits ++ eb)

theorem mem_minus_iff {P K : List Place} {b : Place} : b ∈ minus P K ↔ b ∈ P ∧ b ∉ K := by
  simp [minus]

theorem mem_minus_append {P K G : List Place} {b : Place} :
    b ∈ minus P K ++ G ↔ (b ∈ P ∧ b ∉ K) ∨ b ∈ G := by
  rw [List.mem_append, mem_minus_iff]

theorem path_sim (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg)
    (hplaces : PlacesAreMovePaths s) {j : Nat} {P : List Place} {bits : List Bool}
    (hp : SPath s j P bits) :
    ∀ rest : List Bool, ∃ n m, n ≤ 3 * j ∧
      Reach rule (elaborate .std d s) n (bits ++ rest) (initMach (elaborate .std d s)) rest m ∧
      m.pc = .src j ∧ Inv s.locals m.mem m.fresh m.log (· ∈ P) := by
  induction hp with
  | entry => intro rest; exact ⟨0, _, by omega, Reach.refl, rfl, Inv.initial s.locals⟩
  | @step i j P K G bits eb _ hi hij he ih =>
    intro rest
    obtain ⟨n1, m1, hn1, hr1, hpc1, hinv1⟩ := ih (eb ++ rest)
    obtain ⟨n2, m2, hn2, hr2, hpc2, hinv2⟩ :=
      edge_sim rule d s hplaces he hi m1 hpc1 _ hinv1 rest
    refine ⟨n1 + n2, m2, by omega, ?_, hpc2, hinv2.congr (fun b => mem_minus_append.symm)⟩
    rw [List.append_assoc]; exact hr1.trans hr2

theorem runAux_succ_ch_nil {L : Type} {rule : PanicRule} {P : TProg L} {k : Nat}
    {m m' : Mach L} (hc : (P.node m.pc).isChoice = true)
    (hs : step rule P m false = .next m') :
    runAux rule P (k + 1) [] m = runAux rule P k [] m' :=
  runAux_succ_ch (inp := []) hc hs

/-! ## Drop ladders under an exhausted input -/

theorem ladder_run (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg) (j : Nat) :
    ∀ (n k : Nat) (m : Mach Lbl) (f : Nat), k + n = (dropOrder s.locals).length →
      m.pc = .lad j k → 2 * n + 1 ≤ f →
      ∃ L oc, runAux rule (elaborate .std d s) f [] m = ⟨oc, m.log ++ L⟩ ∧
        oc.complete = true ∧
        (∀ k' c, k ≤ k' → (dropOrder s.locals)[k']? = some c → d j c = .drop →
          ∀ e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c), e ∈ L) ∧
        (∀ e ∈ L, ∃ c ∈ dropOrder s.locals, d j c ≠ .skip ∧
          e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c)) := by
  intro n
  induction n with
  | zero =>
    intro k m f hk hpc hf
    have hnone : (dropOrder s.locals)[k]? = none := List.getElem?_eq_none (by omega)
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hA : ∀ k' c, k ≤ k' → (dropOrder s.locals)[k']? = some c → d j c = .drop →
        ∀ e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c), e ∈ ([] : List Event) := by
      intro k' c hk' hc
      rw [List.getElem?_eq_none (by omega)] at hc
      cases hc
    by_cases hret : (s.node j == .ret) = true
    · have hn : (elaborate .std d s).node m.pc = .ret := by
        rw [hpc]; simp [elaborate, elabNode, ladderStep, hnone, hret]
      refine ⟨[], .returned, ?_, rfl, hA, fun e he => by cases he⟩
      rw [runAux_succ_nc_done (by rw [hn]; rfl) (step_ret hn)]; simp
    · have hn : (elaborate .std d s).node m.pc = .resume := by
        rw [hpc]; simp [elaborate, elabNode, ladderStep, hnone, hret]
      refine ⟨[], .unwound, ?_, rfl, hA, fun e he => by cases he⟩
      rw [runAux_succ_nc_done (by rw [hn]; rfl) (step_resume hn)]; simp
  | succ n ih =>
    intro k m f hk hpc hf
    have hlt : k < (dropOrder s.locals).length := by omega
    obtain ⟨c, hc⟩ : ∃ c, (dropOrder s.locals)[k]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hcmem : c ∈ dropOrder s.locals := List.mem_of_getElem? hc
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    -- After a drop of `c` from a machine `m0` with the same memory, the ladder continues at
    -- step `k + 1`.
    have afterDrop : ∀ (m0 : Mach Lbl) (f0 : Nat), m0.mem = m.mem → m0.log = m.log →
        (∃ un, (elaborate .std d s).node m0.pc = .drop c (.lad j (k + 1)) un) →
        2 * n + 1 ≤ f0 →
        ∃ L oc, runAux rule (elaborate .std d s) (f0 + 1) [] m0 = ⟨oc, m.log ++ L⟩ ∧
          oc.complete = true ∧
          (∀ k' c', k + 1 ≤ k' → (dropOrder s.locals)[k']? = some c' → d j c' = .drop →
            ∀ e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c'), e ∈ L) ∧
          (∀ e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c), e ∈ L) ∧
          (∀ e ∈ L, e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c) ∨
            ∃ c' ∈ dropOrder s.locals, d j c' ≠ .skip ∧
              e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c')) := by
      intro m0 f0 hmem hlog ⟨un, hn⟩ hf0
      let m1 : Mach Lbl := { m0 with pc := .lad j (k + 1),
                                     log := m0.log ++ destroyEvents .drop m0.mem
                                       (unitsUnder s.locals c) }
      obtain ⟨L', oc, hrun, hoc, hA, hB⟩ := ih (k + 1) m1 f0 (by omega) rfl hf0
      refine ⟨destroyEvents .drop m.mem (unitsUnder s.locals c) ++ L', oc, ?_, hoc, ?_, ?_, ?_⟩
      · rw [runAux_succ_ch_nil (m' := m1) (by rw [hn]; rfl) (step_drop_false hn), hrun]
        simp [m1, hmem, hlog]
      · intro k' c' hk' hc' hdc' e he
        exact List.mem_append_right _ (hA k' c' hk' hc' hdc' e (by simpa [m1, hmem] using he))
      · intro e he; exact List.mem_append_left _ he
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact Or.inl he
        · obtain ⟨c', hc'm, hdc', he'⟩ := hB e he
          exact Or.inr ⟨c', hc'm, hdc', by simpa [m1, hmem] using he'⟩
    cases hd : d j c with
    | drop =>
      have hn : ∃ un, (elaborate .std d s).node m.pc = .drop c (.lad j (k + 1)) un := by
        rw [hpc]; simp only [elaborate, elabNode, ladderStep, hc, hd, ladderDrop]
        exact ⟨_, rfl⟩
      obtain ⟨L, oc, hrun, hoc, hA, hDE, hB⟩ := afterDrop m f' rfl rfl hn (by omega)
      refine ⟨L, oc, hrun, hoc, ?_, ?_⟩
      · intro k' c' hk' hc' hdc'
        by_cases hkk : k' = k
        · subst hkk; rw [hc] at hc'; cases hc'; exact hDE
        · exact hA k' c' (by omega) hc' hdc'
      · intro e he
        rcases hB e he with h | h
        · exact ⟨c, hcmem, by rw [hd]; simp, h⟩
        · exact h
    | skip =>
      have hn : (elaborate .std d s).node m.pc = .goto (.lad j (k + 1)) := by
        rw [hpc]; simp only [elaborate, elabNode, ladderStep, hc, hd]; rfl
      let m1 : Mach Lbl := { m with pc := .lad j (k + 1) }
      obtain ⟨L, oc, hrun, hoc, hA, hB⟩ := ih (k + 1) m1 f' (by omega) rfl (by omega)
      refine ⟨L, oc, ?_, hoc, ?_, hB⟩
      · rw [runAux_succ_nc (by rw [hn]; rfl) (step_goto hn), hrun]
      · intro k' c' hk' hc' hdc'
        by_cases hkk : k' = k
        · subst hkk; rw [hc] at hc'; cases hc'; rw [hd] at hdc'; cases hdc'
        · exact hA k' c' (by omega) hc' hdc'
    | test =>
      have hn : (elaborate .std d s).node m.pc = .test c (.dropAt j k) (.lad j (k + 1)) := by
        rw [hpc]; simp only [elaborate, elabNode, ladderStep, hc, hd]; rfl
      cases hfl : m.flags c with
      | true =>
        let m1 : Mach Lbl := { m with pc := .dropAt j k }
        have hs : step rule (elaborate .std d s) m false = .next m1 := by
          rw [step_test hn, hfl]; rfl
        have hn1 : ∃ un, (elaborate .std d s).node m1.pc = .drop c (.lad j (k + 1)) un := by
          simp only [m1, elaborate, elabNode, ladderGuarded, hc, ladderDrop]
          exact ⟨_, rfl⟩
        obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
        obtain ⟨L, oc, hrun, hoc, hA, _, hB⟩ := afterDrop m1 f'' rfl rfl hn1 (by omega)
        refine ⟨L, oc, ?_, hoc, ?_, ?_⟩
        · rw [runAux_succ_nc (by rw [hn]; rfl) hs, hrun]
        · intro k' c' hk' hc' hdc'
          by_cases hkk : k' = k
          · subst hkk; rw [hc] at hc'; cases hc'; rw [hd] at hdc'; cases hdc'
          · exact hA k' c' (by omega) hc' hdc'
        · intro e he
          rcases hB e he with h | h
          · exact ⟨c, hcmem, by rw [hd]; simp, h⟩
          · exact h
      | false =>
        let m1 : Mach Lbl := { m with pc := .lad j (k + 1) }
        have hs : step rule (elaborate .std d s) m false = .next m1 := by
          rw [step_test hn, hfl]; rfl
        obtain ⟨L, oc, hrun, hoc, hA, hB⟩ := ih (k + 1) m1 f' (by omega) rfl (by omega)
        refine ⟨L, oc, ?_, hoc, ?_, hB⟩
        · rw [runAux_succ_nc (by rw [hn]; rfl) hs, hrun]
        · intro k' c' hk' hc' hdc'
          by_cases hkk : k' = k
          · subst hkk; rw [hc] at hc'; cases hc'; rw [hd] at hdc'; cases hdc'
          · exact hA k' c' (by omega) hc' hdc'

/-! ## Runs to a drop point and through its ladder -/

theorem src_dropPoint_node (d : Nat → Place → Decision) (s : SProg) (j : Nat)
    (hj : isDropPoint s j = true) :
    (elaborate .std d s).node (.src j) = .goto (.lad j 0) := by
  have hlt := lt_of_isDropPoint s j hj
  simp only [isDropPoint, Bool.or_eq_true, beq_iff_eq] at hj
  rcases hj with h | h <;> simp [elaborate, elabNode, hlt, h]

theorem run_to_ladder (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg)
    (hplaces : PlacesAreMovePaths s) {j : Nat} {P : List Place} {bits : List Bool}
    (hp : SPath s j P bits) (hj : isDropPoint s j = true) :
    ∃ (m : Mach Lbl) (L : List Event) (oc : Outcome),
      Inv s.locals m.mem m.fresh m.log (· ∈ P) ∧
      runElab rule .std d s bits = ⟨oc, m.log ++ L⟩ ∧ oc.complete = true ∧
      (∀ c ∈ dropOrder s.locals, d j c = .drop →
        ∀ e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c), e ∈ L) ∧
      (∀ e ∈ L, ∃ c ∈ dropOrder s.locals, d j c ≠ .skip ∧
        e ∈ destroyEvents .drop m.mem (unitsUnder s.locals c)) := by
  obtain ⟨n, m, hn, hr, hpc, hinv⟩ := path_sim rule d s hplaces hp []
  have hlt := lt_of_isDropPoint s j hj
  have hlen : (dropOrder s.locals).length = (allAtoms s.locals).length := by
    simp [dropOrder]
  let f := fuelFor s - n - 1
  have hfuel : fuelFor s = (f + 1) + n := by
    simp only [f, fuelFor]; omega
  have hgoto : (elaborate .std d s).node m.pc = .goto (.lad j 0) := by
    rw [hpc]; exact src_dropPoint_node d s j hj
  let m1 : Mach Lbl := { m with pc := .lad j 0 }
  obtain ⟨L, oc, hrun, hoc, hA, hB⟩ :=
    ladder_run rule d s j (dropOrder s.locals).length 0 m1 f (by omega) rfl
      (by simp only [f, fuelFor]; omega)
  refine ⟨m, L, oc, hinv, ?_, hoc, ?_, hB⟩
  · unfold runElab run
    rw [hfuel, ← List.append_nil bits, hr (f + 1),
      runAux_succ_nc (m' := m1) (by rw [hgoto]; rfl) (step_goto hgoto), hrun]
  · intro c hc hdc
    obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 hc
    exact hA k' c (Nat.zero_le _) hk' hdc

/-- **Drop half.** An unconditional drop at a drop point reached along a source path on which the
atom is not initialized violates `NoDoubleDrop`. -/
theorem drop_fails (d : Nat → Place → Decision) (s : SProg) (hplaces : PlacesAreMovePaths s)
    {j : Nat} {P : List Place} {bits : List Bool} (hp : SPath s j P bits)
    (hj : isDropPoint s j = true) {a : Place} (ha : a ∈ allAtoms s.locals) (haP : a ∉ P)
    (hd : d j a = .drop) :
    ¬ NoDoubleDrop (runElab .abort .std d s bits).log := by
  obtain ⟨m, L, oc, hinv, hrun, _, hA, _⟩ := run_to_ladder .abort d s hplaces hp hj
  rw [hrun]
  intro hnd
  dsimp only at hnd
  obtain ⟨u, hu⟩ := exists_unit_of_atom s.locals a ha
  have haD : a ∈ dropOrder s.locals := by unfold dropOrder; exact List.mem_reverse.2 ha
  rcases hinv.deadU a ha haP u hu with hnone | ⟨v, hv, hc⟩
  · exact hnd.2.2 (List.mem_append_right _ (hA a haD hd _ (garbage_mem_destroyEvents hu hnone)))
  · have hdrop : Event.drop v ∈ L := hA a haD hd _ (mk_mem_destroyEvents hu hv)
    have h2 : 2 ≤ destroyCount (m.log ++ L) v := by
      rw [destroyCount_append]
      have := destroyCount_pos_of_mem_drop hdrop
      omega
    have := hnd.1 v (mem_destroyedIds_of_pos (by omega))
    omega

/-- **Skip half.** Doing nothing at a drop point reached along a source path on which the atom
is initialized yields a complete run that leaks. -/
theorem skip_fails (d : Nat → Place → Decision) (s : SProg) (hplaces : PlacesAreMovePaths s)
    {j : Nat} {P : List Place} {bits : List Bool} (hp : SPath s j P bits)
    (hj : isDropPoint s j = true) {a : Place} (ha : a ∈ allAtoms s.locals) (haP : a ∈ P)
    (hd : d j a = .skip) :
    (runElab .abort .std d s bits).outcome.complete = true ∧
      ¬ NoLeak (runElab .abort .std d s bits).log := by
  obtain ⟨m, L, oc, hinv, hrun, hcomp, _, hB⟩ := run_to_ladder .abort d s hplaces hp hj
  rw [hrun]
  refine ⟨hcomp, ?_⟩
  intro hnl
  obtain ⟨u, hu⟩ := exists_unit_of_atom s.locals a ha
  obtain ⟨v, hv, hc, h0⟩ := hinv.liveU a ha haP u hu
  have hL : destroyCount L v = 0 := by
    apply destroyCount_eq_zero_of
    intro e he
    obtain ⟨c, hcD, hdc, hec⟩ := hB e he
    obtain ⟨u', hu', ⟨_, rfl⟩ | ⟨v', hv', rfl⟩⟩ := mem_destroyEvents hec
    · exact ⟨by simp, by simp⟩
    · refine ⟨by simp, ?_⟩
      intro heq
      have hvv : v' = v := by injection heq
      rw [hvv] at hv'
      have huu : u = u' := hinv.inj u u' v hv hv'
      subst huu
      have hcA : c ∈ allAtoms s.locals := by unfold dropOrder at hcD; exact List.mem_reverse.1 hcD
      have hac : a = c := atom_eq_of_common_unit s.locals a c u ha hcA
        ((mem_unitsUnder _ _ _).1 hu).2 ((mem_unitsUnder _ _ _).1 hu').2
      subst hac
      exact hdc hd
  have := hnl v (mem_createdIds_append_left _ hc)
  rw [destroyCount_append, h0, hL] at this
  omega

/-! ## Path witnesses from the analyses -/

/-- The in-set computed at node `j` from the incoming sets `ins` (as in `analysisAux`). -/
def joinIns (s : SProg) (may : Bool) (j : Nat) (ins : List (List Place)) : List Place :=
  if j = 0 then []
  else match ins with
    | [] => if may then [] else allAtoms s.locals
    | x :: xs =>
        if may then xs.foldl (· ++ ·) x
        else xs.foldl (fun acc' y => acc'.filter (y.contains ·)) x

theorem analysisAux_succ (s : SProg) (g : Granularity) (may : Bool) (reach : List Bool) (k : Nat)
    (acc : List (List Place)) :
    analysisAux s g may reach (k + 1) acc =
      analysisAux s g may reach k
        (acc ++ [joinIns s may acc.length (flowIn s g reach acc.length acc)]) := rfl

theorem analysisAux_prefix (s : SProg) (g : Granularity) (may : Bool) (reach : List Bool) :
    ∀ (k : Nat) (acc : List (List Place)) (i : Nat) (dflt : List Place), i < acc.length →
      (analysisAux s g may reach k acc).getD i dflt = acc.getD i dflt := by
  intro k
  induction k with
  | zero => intro acc i dflt _; rfl
  | succ k ih =>
    intro acc i dflt hi
    rw [analysisAux_succ, ih _ i dflt (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem flatMap_congr_mem {α β : Type} :
    ∀ (l : List α) (f g : α → List β), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
  intro l
  induction l with
  | nil => intro f g _; rfl
  | cons x xs ih =>
    intro f g h
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih f g (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem flowIn_congr (s : SProg) (g : Granularity) (reach : List Bool) (j : Nat)
    (prev prev' : List (List Place)) (h : ∀ i < j, prev.getD i [] = prev'.getD i []) :
    flowIn s g reach j prev = flowIn s g reach j prev' := by
  unfold flowIn
  apply flatMap_congr_mem
  intro i hi
  rw [List.mem_range] at hi
  rw [h i hi]

theorem analysis_spec (s : SProg) (g : Granularity) (may : Bool) (j : Nat)
    (hj : j < s.nodes.length) (dflt : List Place) :
    (analysis s g may).getD j dflt =
      joinIns s may j (flowIn s g (reachList s) j (analysis s g may)) := by
  unfold analysis
  have stepTo : ∀ m acc, acc.length + m = s.nodes.length → acc.length ≤ j →
      (analysisAux s g may (reachList s) m acc).getD j dflt =
        joinIns s may j (flowIn s g (reachList s) j (analysisAux s g may (reachList s) m acc)) := by
    intro m
    induction m with
    | zero => intro acc hsum hge; omega
    | succ m ih =>
      intro acc hsum hge
      by_cases heq : j = acc.length
      · subst heq
        rw [analysisAux_succ, analysisAux_prefix s g may _ m _ acc.length dflt (by simp)]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        congr 1
        apply flowIn_congr
        intro i hi
        rw [analysisAux_prefix s g may _ m _ i [] (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [analysisAux_succ]
        exact ih _ (by simp; omega) (by simp; omega)
  exact stepTo s.nodes.length [] (by simp) (Nat.zero_le j)

theorem analysis_length (s : SProg) (g : Granularity) (may : Bool) :
    (analysis s g may).length = s.nodes.length := by
  unfold analysis
  simpa using analysisAux_length s g may (reachList s) s.nodes.length []

theorem reachList_length (s : SProg) : (reachList s).length = s.nodes.length := by
  unfold reachList
  simpa using reachAux_length s s.nodes.length []

theorem joinIns_zero (s : SProg) (may : Bool) (ins : List (List Place)) :
    joinIns s may 0 ins = [] := by
  simp [joinIns]

theorem joinIns_may_mem (s : SProg) (j : Nat) (ins : List (List Place)) (a : Place)
    (h : a ∈ joinIns s true j ins) : ∃ y ∈ ins, a ∈ y := by
  unfold joinIns at h
  by_cases hj : j = 0
  · simp [hj] at h
  · simp only [hj, ite_false] at h
    cases ins with
    | nil => simp at h
    | cons x xs =>
      simp only [ite_true] at h
      rcases foldl_append_mem xs x a h with hx | ⟨y, hy, hay⟩
      · exact ⟨x, List.mem_cons_self, hx⟩
      · exact ⟨y, List.mem_cons_of_mem x hy, hay⟩

theorem foldl_filter_mem (a : Place) :
    ∀ (xs : List (List Place)) (init : List Place), a ∈ init → (∀ y ∈ xs, a ∈ y) →
      a ∈ xs.foldl (fun acc' y => acc'.filter (y.contains ·)) init := by
  intro xs
  induction xs with
  | nil => intro init h _; exact h
  | cons y ys ih =>
    intro init h hall
    simp only [List.foldl_cons]
    apply ih
    · rw [List.mem_filter]
      exact ⟨h, List.contains_iff_mem.2 (hall y List.mem_cons_self)⟩
    · intro z hz; exact hall z (List.mem_cons_of_mem y hz)

theorem joinIns_must_not_mem (s : SProg) (j : Nat) (hj : j ≠ 0) (ins : List (List Place))
    (a : Place) (ha : a ∈ allAtoms s.locals) (h : a ∉ joinIns s false j ins) :
    ∃ y ∈ ins, a ∉ y := by
  unfold joinIns at h
  simp only [hj, ite_false] at h
  cases ins with
  | nil => exact absurd ha h
  | cons x xs =>
    simp only [Bool.false_eq_true, ite_false] at h
    apply Classical.byContradiction
    intro hno
    apply h
    apply foldl_filter_mem
    · exact Classical.byContradiction fun hx => hno ⟨x, List.mem_cons_self, hx⟩
    · intro y hy
      exact Classical.byContradiction fun hay => hno ⟨y, List.mem_cons_of_mem x hy, hay⟩

theorem mem_flowIn (s : SProg) (g : Granularity) (reach : List Bool) (j : Nat)
    (prev : List (List Place)) (y : List Place) (h : y ∈ flowIn s g reach j prev) :
    ∃ i < j, reach.getD i false = true ∧
      (j, y) ∈ edgeOut s.locals g (s.node i) (prev.getD i []) := by
  unfold flowIn at h
  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.1 h
  rw [List.mem_range] at hi
  by_cases hr : reach.getD i false = true
  · simp only [hr, ↓reduceIte] at hy
    rw [List.mem_map] at hy
    obtain ⟨pair, hpair, rfl⟩ := hy
    rw [List.mem_filter] at hpair
    have hj : pair.1 = j := eq_of_beq hpair.2
    refine ⟨i, hi, hr, ?_⟩
    have : pair = (j, pair.2) := by rw [← hj]
    rw [← this]; exact hpair.1
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hy
    cases hy

theorem node_eq_abort_of_ge (s : SProg) (i : Nat) (h : s.nodes.length ≤ i) : s.node i = .abort := by
  simp only [SProg.node, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none h]
  rfl

theorem Edge.lt {s : SProg} {i j : Nat} {K G : List Place} {eb : List Bool}
    (he : Edge s i j K G eb) : i < s.nodes.length := by
  apply Classical.byContradiction
  intro hge
  have hab := node_eq_abort_of_ge s i (by omega)
  cases he <;> simp_all

theorem edgeOut_edge (s : SProg) (i j : Nat) (Q y : List Place)
    (h : (j, y) ∈ edgeOut s.locals .fine (s.node i) Q) :
    ∃ K G eb, Edge s i j K G eb ∧ ∀ a, a ∈ y ↔ ((a ∈ Q ∧ a ∉ K) ∨ a ∈ G) := by
  revert h
  cases hn : s.node i with
  | init p nx =>
    intro h
    simp only [edgeOut, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], _, [], Edge.init hn, fun a => by simp⟩
  | move p nx =>
    intro h
    simp only [edgeOut, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, [], [], Edge.move hn, fun a => by simp [mem_minus_iff]⟩
  | branch l1 l2 =>
    intro h
    simp only [edgeOut, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨[], [], [true], Edge.br1 hn, fun a => by simp⟩
    · exact ⟨[], [], [false], Edge.br2 hn, fun a => by simp⟩
  | call args dest nx un =>
    intro h
    simp only [edgeOut, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨_, _, [false], Edge.callN hn, fun a => ?_⟩
      cases dest <;> simp [mem_minus_iff, destAtoms]
    · exact ⟨_, [], [true], Edge.callU hn, fun a => by simp [mem_minus_iff]⟩
  | ret => intro h; simp [edgeOut] at h
  | resume => intro h; simp [edgeOut] at h
  | abort => intro h; simp [edgeOut] at h

theorem succ_edge (s : SProg) (i j : Nat) (h : j ∈ (s.node i).succs) :
    ∃ K G eb, Edge s i j K G eb := by
  revert h
  cases hn : s.node i with
  | init p nx =>
    intro h; simp only [SNode.succs, List.mem_singleton] at h; subst h
    exact ⟨_, _, _, Edge.init hn⟩
  | move p nx =>
    intro h; simp only [SNode.succs, List.mem_singleton] at h; subst h
    exact ⟨_, _, _, Edge.move hn⟩
  | branch l1 l2 =>
    intro h; simp only [SNode.succs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨_, _, _, Edge.br1 hn⟩
    · exact ⟨_, _, _, Edge.br2 hn⟩
  | call args dest nx un =>
    intro h; simp only [SNode.succs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨_, _, _, Edge.callN hn⟩
    · exact ⟨_, _, _, Edge.callU hn⟩
  | ret => intro h; simp [SNode.succs] at h
  | resume => intro h; simp [SNode.succs] at h
  | abort => intro h; simp [SNode.succs] at h

/-- Every forward-reachable node is the end of a source path. -/
theorem reach_path (s : SProg) :
    ∀ j, (reachList s).getD j false = true → ∃ P bits, SPath s j P bits := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hr
    by_cases hj0 : j = 0
    · subst hj0; exact ⟨[], [], SPath.entry⟩
    · have hlt : j < s.nodes.length := by
        apply Classical.byContradiction
        intro hge
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [reachList_length]; omega)] at hr
        cases hr
      rw [reachList_spec s j hlt] at hr
      simp only [hj0, decide_false, Bool.false_or, List.any_eq_true, List.mem_range,
        Bool.and_eq_true] at hr
      obtain ⟨i, hij, hri, hsucc⟩ := hr
      obtain ⟨P, bits, hp⟩ := ih i hij hri
      obtain ⟨K, G, eb, he⟩ := succ_edge s i j (List.contains_iff_mem.1 hsucc)
      exact ⟨_, _, SPath.step hp he.lt hij he⟩

/-- May-init yields a source path on which the atom is initialized. -/
theorem may_path (s : SProg) :
    ∀ j a, a ∈ (analysis s .fine true).getD j [] → ∃ P bits, SPath s j P bits ∧ a ∈ P := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro a ha
    have hlt : j < s.nodes.length := by
      apply Classical.byContradiction
      intro hge
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [analysis_length]; omega)] at ha
      cases ha
    rw [analysis_spec s .fine true j hlt] at ha
    by_cases hj0 : j = 0
    · subst hj0; rw [joinIns_zero] at ha; cases ha
    obtain ⟨y, hy, hay⟩ := joinIns_may_mem s j _ a ha
    obtain ⟨i, hij, hri, hedge⟩ := mem_flowIn s .fine (reachList s) j _ y hy
    obtain ⟨K, G, eb, he, hmem⟩ := edgeOut_edge s i j _ y hedge
    rcases (hmem a).1 hay with ⟨haQ, haK⟩ | haG
    · obtain ⟨P, bits, hp, haP⟩ := ih i hij a haQ
      exact ⟨_, _, SPath.step hp he.lt hij he, mem_minus_append.2 (Or.inl ⟨haP, haK⟩)⟩
    · obtain ⟨P, bits, hp⟩ := reach_path s i hri
      exact ⟨_, _, SPath.step hp he.lt hij he, mem_minus_append.2 (Or.inr haG)⟩

/-- Not must-init at a forward-reachable node yields a source path on which the atom is not
initialized. -/
theorem must_path (s : SProg) :
    ∀ j a, a ∈ allAtoms s.locals → (reachList s).getD j false = true →
      a ∉ (analysis s .fine false).getD j (allAtoms s.locals) →
      ∃ P bits, SPath s j P bits ∧ a ∉ P := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro a ha hr hna
    have hlt : j < s.nodes.length := by
      apply Classical.byContradiction
      intro hge
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [reachList_length]; omega)] at hr
      cases hr
    by_cases hj0 : j = 0
    · subst hj0; exact ⟨[], [], SPath.entry, by simp⟩
    rw [analysis_spec s .fine false j hlt] at hna
    obtain ⟨y, hy, hay⟩ := joinIns_must_not_mem s j hj0 _ a ha hna
    obtain ⟨i, hij, hri, hedge⟩ := mem_flowIn s .fine (reachList s) j _ y hy
    obtain ⟨K, G, eb, he, hmem⟩ := edgeOut_edge s i j _ y hedge
    have hnot : ¬ ((a ∈ (analysis s .fine false).getD i [] ∧ a ∉ K) ∨ a ∈ G) :=
      fun h => hay ((hmem a).2 h)
    have haG : a ∉ G := fun h => hnot (Or.inr h)
    by_cases haK : a ∈ K
    · obtain ⟨P, bits, hp⟩ := reach_path s i hri
      refine ⟨_, _, SPath.step hp he.lt hij he, ?_⟩
      rw [mem_minus_append]
      rintro (⟨_, h⟩ | h)
      · exact h haK
      · exact haG h
    · have haQ : a ∉ (analysis s .fine false).getD i (allAtoms s.locals) := by
        intro h
        apply hnot
        left
        refine ⟨?_, haK⟩
        have hil : i < (analysis s .fine false).length := by rw [analysis_length]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil] at h ⊢
        exact h
      obtain ⟨P, bits, hp, haP⟩ := ih i hij a ha hri haQ
      refine ⟨_, _, SPath.step hp he.lt hij he, ?_⟩
      rw [mem_minus_append]
      rintro (⟨h, _⟩ | h)
      · exact haP h
      · exact haG h

/-! ## The two necessity statements, for an arbitrary decision map -/

theorem drop_fails_of_not_mustInit (d : Nat → Place → Decision) (s : SProg)
    (hplaces : PlacesAreMovePaths s) (i : Nat) (hdrop : isDropPoint s i = true)
    (hreach : ForwardReachable s i = true) (a : Place) (ha : a ∈ allAtoms s.locals)
    (hmust : mustInit s .fine i a = false) (hd : d i a = .drop) :
    ∃ inp, ¬ NoDoubleDrop (runElab .abort .std d s inp).log := by
  have hna : a ∉ (analysis s .fine false).getD i (allAtoms s.locals) := by
    intro h
    unfold mustInit at hmust
    rw [List.contains_iff_mem.2 h] at hmust
    cases hmust
  obtain ⟨P, bits, hp, haP⟩ := must_path s i a ha hreach hna
  exact ⟨bits, drop_fails d s hplaces hp hdrop ha haP hd⟩

theorem skip_fails_of_mayInit (d : Nat → Place → Decision) (s : SProg)
    (hplaces : PlacesAreMovePaths s) (i : Nat) (hdrop : isDropPoint s i = true) (a : Place)
    (hmay : mayInit s .fine i a = true) (hd : d i a = .skip) :
    ∃ inp, (runElab .abort .std d s inp).outcome.complete = true ∧
      ¬ NoLeak (runElab .abort .std d s inp).log := by
  have ha := (forwardReachable_and_mem_allAtoms_of_mayInit s i a hmay).2
  have hmem : a ∈ (analysis s .fine true).getD i [] := List.contains_iff_mem.1 hmay
  obtain ⟨P, bits, hp, haP⟩ := may_path s i a hmem
  exact ⟨bits, skip_fails d s hplaces hp hdrop ha haP hd⟩

end Toy.DropFlags
