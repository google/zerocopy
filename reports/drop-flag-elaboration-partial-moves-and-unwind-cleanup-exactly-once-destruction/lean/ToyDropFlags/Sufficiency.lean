import ToyDropFlags.Necessity

/-!
# Helpers for the sufficiency results

An invariant-based simulation of elaborated runs on every input: duplicate-freeness of units and
atoms, the unit/atom partition, destruction and creation steps on logs, flag bookkeeping,
soundness of the one-pass analyses along edges, and the machine invariants at source nodes and
inside drop ladders.
-/

namespace Toy.DropFlags

/-! ## Duplicate-freeness and the unit/atom partition -/

theorem nodup_map_of_injective {α β : Type} {f : α → β} (hf : ∀ x y, f x = f y → x = y)
    {l : List α} (h : l.Nodup) : (l.map f).Nodup :=
  List.pairwise_map.2 (h.imp (fun hne heq => hne (hf _ _ heq)))

theorem Ty.units_nodup : ∀ t : Ty, t.units.Nodup := by
  intro t
  induction t with
  | leaf => simp [Ty.units]
  | pair dd a b iha ihb =>
    simp only [Ty.units]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨by cases dd <;> simp, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact nodup_map_of_injective (fun x y h => (List.cons.inj h).2) iha
    · exact nodup_map_of_injective (fun x y h => (List.cons.inj h).2) ihb
    · intro x hx y hy
      simp only [List.mem_map] at hx hy
      obtain ⟨x', _, rfl⟩ := hx
      obtain ⟨y', _, rfl⟩ := hy
      simp
    · intro x hx y hy
      cases dd
      · simp at hx
      · simp only [ite_true, List.mem_singleton] at hx
        subst hx
        simp only [List.mem_append, List.mem_map] at hy
        rcases hy with ⟨y', _, rfl⟩ | ⟨y', _, rfl⟩ <;> simp

theorem Ty.atoms_nodup : ∀ t : Ty, t.atoms.Nodup := by
  intro t
  induction t with
  | leaf => simp [Ty.atoms]
  | pair dd a b iha ihb =>
    cases dd with
    | true => simp [Ty.atoms]
    | false =>
      simp only [Ty.atoms]
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact nodup_map_of_injective (fun x y h => (List.cons.inj h).2) iha
      · exact nodup_map_of_injective (fun x y h => (List.cons.inj h).2) ihb
      · intro x hx y hy
        simp only [List.mem_map] at hx hy
        obtain ⟨x', _, rfl⟩ := hx
        obtain ⟨y', _, rfl⟩ := hy
        simp

theorem placesFrom_nodup (f : Ty → List Path) (hf : ∀ t, (f t).Nodup) :
    ∀ (ls : List Ty) (i : Nat), (placesFrom f i ls).Nodup := by
  intro ls
  induction ls with
  | nil => intro i; simp [placesFrom]
  | cons t ts ih =>
    intro i
    simp only [placesFrom]
    rw [List.nodup_append]
    refine ⟨?_, ih (i + 1), ?_⟩
    · exact nodup_map_of_injective (fun x y h => by cases h; rfl) (hf t)
    · intro x hx y hy hxy
      simp only [List.mem_map] at hx
      obtain ⟨r, _, rfl⟩ := hx
      have := (mem_placesFrom f ts (i + 1) y hy).1
      rw [← hxy] at this
      simp at this
      omega

theorem allUnits_nodup (ls : List Ty) : (allUnits ls).Nodup :=
  placesFrom_nodup Ty.units Ty.units_nodup ls 0

theorem allAtoms_nodup (ls : List Ty) : (allAtoms ls).Nodup :=
  placesFrom_nodup Ty.atoms Ty.atoms_nodup ls 0

theorem unitsUnder_nodup (ls : List Ty) (p : Place) : (unitsUnder ls p).Nodup :=
  (allUnits_nodup ls).filter _

theorem dropOrder_nodup (ls : List Ty) : (dropOrder ls).Nodup := by
  unfold dropOrder
  exact List.pairwise_reverse.2 ((allAtoms_nodup ls).imp (fun h h' => h h'.symm))

theorem Ty.unit_has_atom : ∀ (t : Ty) (q : Path), q ∈ t.units → ∃ r ∈ t.atoms, r <+: q := by
  intro t
  induction t with
  | leaf =>
    intro q hq
    simp [Ty.units] at hq; subst hq
    exact ⟨[], by simp [Ty.atoms], List.prefix_refl _⟩
  | pair dd a b iha ihb =>
    intro q hq
    cases dd with
    | true => exact ⟨[], by simp [Ty.atoms], List.nil_prefix⟩
    | false =>
      simp only [Ty.units, Bool.false_eq_true, ite_false, List.nil_append, List.mem_append,
        List.mem_map] at hq
      rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
      · obtain ⟨r, hr, hpre⟩ := iha q' hq'
        refine ⟨false :: r, by simp [Ty.atoms, hr], ?_⟩
        rw [List.cons_prefix_cons]; exact ⟨rfl, hpre⟩
      · obtain ⟨r, hr, hpre⟩ := ihb q' hq'
        refine ⟨true :: r, by simp [Ty.atoms, hr], ?_⟩
        rw [List.cons_prefix_cons]; exact ⟨rfl, hpre⟩

/-- Every unit lies inside some atom. -/
theorem atom_of_unit (ls : List Ty) (u : Place) (hu : u ∈ allUnits ls) :
    ∃ b ∈ allAtoms ls, b.covers u = true := by
  obtain ⟨_, t, ht, hut⟩ := mem_placesFrom Ty.units ls 0 u hu
  simp only [Nat.sub_zero] at ht
  obtain ⟨r, hr, hpre⟩ := Ty.unit_has_atom t u.path hut
  refine ⟨⟨u.loc, r⟩, ?_, ?_⟩
  · have := placesFrom_mem Ty.atoms ls 0 u.loc t r ht hr
    unfold allAtoms
    simpa using this
  · rw [covers_iff]; exact ⟨rfl, hpre⟩

/-- Every unit under a place lies under some atom of that place. -/
theorem exists_atom_of_mem_unitsUnder (ls : List Ty) (p u : Place) (hu : u ∈ unitsUnder ls p) :
    ∃ b ∈ atomsOf ls p, u ∈ unitsUnder ls b := by
  rw [mem_unitsUnder] at hu
  obtain ⟨b, hb, hbu⟩ := atom_of_unit ls u hu.1
  refine ⟨b, ?_, ?_⟩
  · rw [mem_atomsOf]; exact ⟨hb, overlaps_of_covers_common hu.2 hbu⟩
  · rw [mem_unitsUnder]; exact ⟨hu.1, hbu⟩

/-- The only atom overlapping an atom is itself. -/
theorem eq_of_mem_atomsOf_atom (ls : List Ty) (c b : Place) (hc : c ∈ allAtoms ls)
    (hb : b ∈ atomsOf ls c) : b = c := by
  rw [mem_atomsOf] at hb
  obtain ⟨hbA, hov⟩ := hb
  simp only [Place.overlaps, Bool.or_eq_true] at hov
  rcases hov with h | h
  · obtain ⟨u, hu⟩ := exists_unit_of_atom ls b hbA
    have hbu := ((mem_unitsUnder _ _ _).1 hu).2
    exact atom_eq_of_common_unit ls b c u hbA hc hbu (covers_trans h hbu)
  · obtain ⟨u, hu⟩ := exists_unit_of_atom ls c hc
    have hcu := ((mem_unitsUnder _ _ _).1 hu).2
    exact atom_eq_of_common_unit ls b c u hbA hc (covers_trans h hcu) hcu

theorem atom_isMovePlace (ls : List Ty) (c : Place) (hc : c ∈ allAtoms ls) :
    isMovePlace ls c = true := by
  obtain ⟨t, ht, hct⟩ := mem_allAtoms_iff ls c hc
  unfold isMovePlace
  rw [ht]
  exact Ty.atoms_isMovePath t c.path hct

/-- Two disjoint move places have no common atom. -/
theorem not_mem_atomsOf_of_disjoint (ls : List Ty) (p q b : Place)
    (hp : isMovePlace ls p = true) (hq : isMovePlace ls q = true)
    (hpq : p.overlaps q = false) (hbq : b ∈ atomsOf ls q) : b ∉ atomsOf ls p := by
  intro hbp
  have hbA := mem_atomsOf_mem_allAtoms ls q b hbq
  obtain ⟨u, hu⟩ := exists_unit_of_atom ls b hbA
  have hbu := ((mem_unitsUnder _ _ _).1 hu).2
  have h1 := covers_trans (covers_of_mem_atomsOf ls p b hp hbp) hbu
  have h2 := covers_trans (covers_of_mem_atomsOf ls q b hq hbq) hbu
  rw [overlaps_of_covers_common h1 h2] at hpq
  cases hpq

/-! ## Destruction and creation steps on logs -/

theorem destroyCount_destroyEvents {mk : Nat → Event} (hmk : mk = Event.consume ∨ mk = Event.drop)
    (mem : Place → Option Nat) (us : List Place) (v : Nat) :
    destroyCount (destroyEvents mk mem us) v = us.countP (fun u => mem u == some v) := by
  unfold destroyCount destroyEvents
  rw [List.countP_map]
  congr 1
  funext u
  simp only [Function.comp]
  cases mem u with
  | none => simp
  | some w => rcases hmk with rfl | rfl <;> rw [Bool.eq_iff_iff] <;> simp [beq_iff_eq]

theorem destroyCount_destroyEvents_zero {mk : Nat → Event}
    (hmk : mk = Event.consume ∨ mk = Event.drop) {mem : Place → Option Nat} {us : List Place}
    {v : Nat} (h : ∀ u ∈ us, mem u ≠ some v) : destroyCount (destroyEvents mk mem us) v = 0 := by
  rw [destroyCount_destroyEvents hmk, List.countP_eq_zero]
  intro u hu hm
  exact h u hu (by simpa using hm)

theorem destroyCount_destroyEvents_pos {mk : Nat → Event}
    (hmk : mk = Event.consume ∨ mk = Event.drop) {mem : Place → Option Nat} {us : List Place}
    {v : Nat} {u : Place} (hu : u ∈ us) (hm : mem u = some v) :
    1 ≤ destroyCount (destroyEvents mk mem us) v := by
  rw [destroyCount_destroyEvents hmk]
  exact List.countP_pos_iff.2 ⟨u, hu, by simp [hm]⟩

theorem createdIds_destroyEvents {mk : Nat → Event} (hmk : mk = Event.consume ∨ mk = Event.drop)
    (mem : Place → Option Nat) (us : List Place) : createdIds (destroyEvents mk mem us) = [] := by
  unfold createdIds destroyEvents
  rw [List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨u, _, rfl⟩ := List.mem_map.1 he
  cases mem u with
  | none => rfl
  | some w => rcases hmk with rfl | rfl <;> rfl

theorem destroyedIds_append (l1 l2 : List Event) :
    destroyedIds (l1 ++ l2) = destroyedIds l1 ++ destroyedIds l2 := by
  simp [destroyedIds, List.filterMap_append]

theorem pos_of_mem_destroyedIds {l : List Event} {v : Nat} (h : v ∈ destroyedIds l) :
    1 ≤ destroyCount l v := by
  unfold destroyedIds at h
  obtain ⟨e, he, hev⟩ := List.mem_filterMap.1 h
  cases e with
  | create w => cases hev
  | consume w => cases hev; exact destroyCount_pos_of_mem_consume he
  | drop w => cases hev; exact destroyCount_pos_of_mem_drop he
  | garbage => cases hev

theorem countP_le_one {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) →
      l.countP p ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x xs ih =>
    intro hnd hu
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    by_cases hpx : p x = true
    · have h0 : xs.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro y hy hpy
        have := hu x List.mem_cons_self y (List.mem_cons_of_mem x hy) hpx hpy
        subst this
        exact hnd.1 hy
      simp [hpx, h0]
    · have := ih hnd.2 (fun a ha b hb => hu a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))
      simp [hpx]; omega

/-- Destroying the units of a place (by consumption or drop) preserves the path invariant. -/
theorem Inv.destroy {ls : List Ty} {mem : Place → Option Nat} {n : Nat} {log : List Event}
    {live : Place → Prop} {p : Place} {mk : Nat → Event}
    (hmk : mk = Event.consume ∨ mk = Event.drop) (hinv : Inv ls mem n log live)
    (hp : isMovePlace ls p = true) :
    Inv ls mem n (log ++ destroyEvents mk mem (unitsUnder ls p))
      (fun b => live b ∧ b ∉ atomsOf ls p) := by
  refine ⟨hinv.inj, hinv.lt, ?_, ?_, ?_⟩
  · intro v hv
    rw [destroyCount_append, hinv.hi v hv, destroyCount_destroyEvents_zero hmk]
    intro u _ hu
    have := hinv.lt u v hu
    omega
  · intro b hb hlive u hu
    obtain ⟨v, hv, hc, h0⟩ := hinv.liveU b hb hlive.1 u hu
    refine ⟨v, hv, mem_createdIds_append_left _ hc, ?_⟩
    rw [destroyCount_append, h0, destroyCount_destroyEvents_zero hmk]
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
        have := destroyCount_destroyEvents_pos hmk hup hm
        omega
    · have hl : ¬ live b := fun h => hdead ⟨h, hbp⟩
      rcases hinv.deadU b hb hl u hu with h | ⟨v, hv, hc⟩
      · exact Or.inl h
      · refine Or.inr ⟨v, hv, ?_⟩
        rw [destroyCount_append]; omega

/-- Destroying the units of a place all of whose atoms are live keeps the log free of double
destruction. -/
theorem ndd_destroy {ls : List Ty} {mem : Place → Option Nat} {n : Nat} {log : List Event}
    {live : Place → Prop} {p : Place} {mk : Nat → Event}
    (hmk : mk = Event.consume ∨ mk = Event.drop) (hinv : Inv ls mem n log live)
    (hndd : NoDoubleDrop log) (hlive : ∀ b ∈ atomsOf ls p, live b) :
    NoDoubleDrop (log ++ destroyEvents mk mem (unitsUnder ls p)) := by
  have hU : ∀ u ∈ unitsUnder ls p,
      ∃ v, mem u = some v ∧ v ∈ createdIds log ∧ destroyCount log v = 0 := by
    intro u hu
    obtain ⟨b, hb, hub⟩ := exists_atom_of_mem_unitsUnder ls p u hu
    exact hinv.liveU b (mem_atomsOf_mem_allAtoms ls p b hb) (hlive b hb) u hub
  refine ⟨?_, ?_, ?_⟩
  · intro v _
    rw [destroyCount_append, destroyCount_destroyEvents hmk]
    by_cases h0 : (unitsUnder ls p).countP (fun u => mem u == some v) = 0
    · rw [h0]
      by_cases hl : 1 ≤ destroyCount log v
      · have := hndd.1 v (mem_destroyedIds_of_pos hl); omega
      · omega
    · obtain ⟨u, hu, hmu⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero h0)
      obtain ⟨w, hw, _, h0'⟩ := hU u hu
      have hwv : w = v := by rw [hw] at hmu; simpa using hmu
      subst hwv
      rw [h0']
      have := countP_le_one (p := fun u => mem u == some w) (unitsUnder_nodup ls p)
        (fun x _ y _ hx hy => hinv.inj x y w (by simpa using hx) (by simpa using hy))
      omega
  · intro v hv
    rw [destroyedIds_append] at hv
    rcases List.mem_append.1 hv with h | h
    · exact mem_createdIds_append_left _ (hndd.2.1 v h)
    · have hpos := pos_of_mem_destroyedIds h
      rw [destroyCount_destroyEvents hmk] at hpos
      obtain ⟨u, hu, hmu⟩ := List.countP_pos_iff.1 hpos
      obtain ⟨w, hw, hc, _⟩ := hU u hu
      have hwv : w = v := by rw [hw] at hmu; simpa using hmu
      subst hwv
      exact mem_createdIds_append_left _ hc
  · intro hg
    rcases List.mem_append.1 hg with h | h
    · exact hndd.2.2 h
    · obtain ⟨u, hu, ⟨hnone, _⟩ | ⟨w, _, hw⟩⟩ := mem_destroyEvents h
      · obtain ⟨v, hv, _⟩ := hU u hu
        rw [hv] at hnone; cases hnone
      · rcases hmk with rfl | rfl <;> cases hw

/-- Consuming pairwise-disjoint call arguments whose atoms are all live keeps the log free of
double destruction. -/
theorem ndd_destroyAll {ls : List Ty} {mem : Place → Option Nat} {n : Nat} :
    ∀ (args : List Place) (log : List Event) (live : Place → Prop),
      Inv ls mem n log live → NoDoubleDrop log → (∀ p ∈ args, isMovePlace ls p = true) →
      (∀ p ∈ args, ∀ b ∈ atomsOf ls p, live b) → pairwiseDisjoint args = true →
      NoDoubleDrop (log ++ args.flatMap (fun p => destroyEvents .consume mem (unitsUnder ls p))) := by
  intro args
  induction args with
  | nil => intro log live _ hndd _ _ _; simpa using hndd
  | cons p rest ih =>
    intro log live hinv hndd hmp hlive hdisj
    simp only [pairwiseDisjoint, Bool.and_eq_true, List.all_eq_true] at hdisj
    have h1 := ndd_destroy (Or.inl rfl) hinv hndd (hlive p List.mem_cons_self)
    have hinv1 := hinv.destroy (Or.inl rfl) (hmp p List.mem_cons_self)
    have h2 := ih _ _ hinv1 h1 (fun q hq => hmp q (List.mem_cons_of_mem _ hq))
      (by
        intro q hq b hb
        refine ⟨hlive q (List.mem_cons_of_mem _ hq) b hb, ?_⟩
        exact not_mem_atomsOf_of_disjoint ls p q b (hmp p List.mem_cons_self)
          (hmp q (List.mem_cons_of_mem _ hq)) (by simpa using hdisj.1 q hq) hb)
      hdisj.2
    simpa only [List.flatMap_cons, List.append_assoc] using h2

theorem ndd_creates {log cs : List Event} (hndd : NoDoubleDrop log)
    (hcs : ∀ e ∈ cs, ∃ v, e = .create v) : NoDoubleDrop (log ++ cs) := by
  have hdc : ∀ v, destroyCount cs v = 0 := by
    intro v
    apply destroyCount_eq_zero_of
    intro e he
    obtain ⟨w, rfl⟩ := hcs e he
    exact ⟨by simp, by simp⟩
  have hdi : destroyedIds cs = [] := by
    unfold destroyedIds
    rw [List.filterMap_eq_nil_iff]
    intro e he
    obtain ⟨w, rfl⟩ := hcs e he
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [destroyedIds_append, hdi, List.append_nil] at hv
    rw [destroyCount_append, hdc]
    have := hndd.1 v hv; omega
  · intro v hv
    rw [destroyedIds_append, hdi, List.append_nil] at hv
    exact mem_createdIds_append_left _ (hndd.2.1 v hv)
  · intro hg
    rcases List.mem_append.1 hg with h | h
    · exact hndd.2.2 h
    · obtain ⟨w, hw⟩ := hcs _ h; cases hw

/-! ## Leak accounting -/

/-- Every created value has been destroyed or is still held by a unit of a live atom. -/
def Acct (ls : List Ty) (mem : Place → Option Nat) (log : List Event) (live : Place → Prop) :
    Prop :=
  ∀ v ∈ createdIds log, 1 ≤ destroyCount log v ∨
    ∃ b ∈ allAtoms ls, live b ∧ ∃ u ∈ unitsUnder ls b, mem u = some v

theorem Acct.congr {ls : List Ty} {mem : Place → Option Nat} {log : List Event}
    {live live' : Place → Prop} (h : ∀ b, live b ↔ live' b) (ha : Acct ls mem log live) :
    Acct ls mem log live' := by
  have : live = live' := funext fun b => propext (h b)
  subst this; exact ha

theorem Acct.initial (ls : List Ty) (mem : Place → Option Nat) (live : Place → Prop) :
    Acct ls mem [] live := by
  intro v hv; simp [createdIds] at hv

theorem Acct.destroy {ls : List Ty} {mem : Place → Option Nat} {log : List Event}
    {live : Place → Prop} {p : Place} {mk : Nat → Event}
    (hmk : mk = Event.consume ∨ mk = Event.drop) (hacct : Acct ls mem log live)
    (hp : isMovePlace ls p = true) :
    Acct ls mem (log ++ destroyEvents mk mem (unitsUnder ls p))
      (fun b => live b ∧ b ∉ atomsOf ls p) := by
  intro v hv
  rw [createdIds_append, createdIds_destroyEvents hmk, List.append_nil] at hv
  rcases hacct v hv with h | ⟨b, hb, hl, u, hu, hm⟩
  · left; rw [destroyCount_append]; omega
  · by_cases hbp : b ∈ atomsOf ls p
    · left
      rw [destroyCount_append]
      have := destroyCount_destroyEvents_pos hmk (mem_unitsUnder_of_mem_atomsOf ls p b u hp hbp hu) hm
      omega
    · exact Or.inr ⟨b, hb, ⟨hl, hbp⟩, u, hu, hm⟩

theorem Acct.destroyAll {ls : List Ty} {mem : Place → Option Nat} :
    ∀ (args : List Place) (log : List Event) (live : Place → Prop),
      Acct ls mem log live → (∀ p ∈ args, isMovePlace ls p = true) →
      Acct ls mem (log ++ args.flatMap (fun p => destroyEvents .consume mem (unitsUnder ls p)))
        (fun b => live b ∧ b ∉ args.flatMap (atomsOf ls)) := by
  intro args
  induction args with
  | nil =>
    intro log live hacct _
    simp only [List.flatMap_nil, List.append_nil]
    exact hacct.congr (fun b => by simp)
  | cons p rest ih =>
    intro log live hacct hargs
    have h1 := hacct.destroy (Or.inl rfl) (hargs p List.mem_cons_self)
    have h2 := ih _ _ h1 (fun q hq => hargs q (List.mem_cons_of_mem _ hq))
    simp only [List.flatMap_cons, ← List.append_assoc]
    refine h2.congr (fun b => ?_)
    simp only [List.mem_append, not_or]
    exact and_assoc

theorem writeFresh_frame :
    ∀ (us : List Place) (mem : Place → Option Nat) (n : Nat) (log : List Event) (q : Place),
      q ∉ us → (writeFresh us mem n log).1 q = mem q := by
  intro us
  induction us with
  | nil => intro mem n log q _; rfl
  | cons u us ih =>
    intro mem n log q hq
    simp only [writeFresh]
    rw [ih _ _ _ q (fun h => hq (List.mem_cons_of_mem _ h))]
    have : q ≠ u := fun h => hq (h ▸ List.mem_cons_self)
    simp [this]

theorem writeFresh_created :
    ∀ (us : List Place) (mem : Place → Option Nat) (n : Nat) (log : List Event), us.Nodup →
      ∀ v ∈ createdIds (writeFresh us mem n log).2.2,
        v ∈ createdIds log ∨ ∃ q ∈ us, (writeFresh us mem n log).1 q = some v := by
  intro us
  induction us with
  | nil => intro mem n log _ v hv; exact Or.inl hv
  | cons u us ih =>
    intro mem n log hnd v hv
    rw [List.nodup_cons] at hnd
    simp only [writeFresh] at hv ⊢
    rcases ih _ _ _ hnd.2 v hv with h | ⟨q, hq, hqv⟩
    · rw [createdIds_append] at h
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · simp [createdIds] at h
        subst h
        refine Or.inr ⟨u, List.mem_cons_self, ?_⟩
        rw [writeFresh_frame _ _ _ _ u hnd.1]
        simp
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqv⟩

theorem writeFresh_log :
    ∀ (us : List Place) (mem : Place → Option Nat) (n : Nat) (log : List Event),
      ∃ cs, (writeFresh us mem n log).2.2 = log ++ cs ∧ ∀ e ∈ cs, ∃ v, e = .create v := by
  intro us
  induction us with
  | nil => intro mem n log; exact ⟨[], by simp [writeFresh], by simp⟩
  | cons u us ih =>
    intro mem n log
    simp only [writeFresh]
    obtain ⟨cs, hcs, hcse⟩ := ih (fun q => if q = u then some n else mem q) (n + 1)
      (log ++ [.create n])
    refine ⟨.create n :: cs, by simp [hcs], ?_⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨n, rfl⟩
    · exact hcse e he

theorem Acct.write {ls : List Ty} {mem : Place → Option Nat} {n : Nat} {log : List Event}
    {live : Place → Prop} {p : Place} (hacct : Acct ls mem log live)
    (hdead : ∀ b ∈ atomsOf ls p, ¬ live b) :
    Acct ls (writeFresh (unitsUnder ls p) mem n log).1 (writeFresh (unitsUnder ls p) mem n log).2.2
      (fun b => live b ∨ b ∈ atomsOf ls p) := by
  intro v hv
  obtain ⟨cs, hcs, hcse⟩ := writeFresh_log (unitsUnder ls p) mem n log
  have hdc : ∀ w, destroyCount (writeFresh (unitsUnder ls p) mem n log).2.2 w =
      destroyCount log w := by
    intro w
    rw [hcs, destroyCount_append]
    have : destroyCount cs w = 0 := by
      apply destroyCount_eq_zero_of
      intro e he
      obtain ⟨x, rfl⟩ := hcse e he
      exact ⟨by simp, by simp⟩
    omega
  rcases writeFresh_created _ mem n log (unitsUnder_nodup ls p) v hv with hold | ⟨q, hq, hmq⟩
  · rcases hacct v hold with h | ⟨b, hb, hl, u, hu, hm⟩
    · left; rw [hdc]; exact h
    · right
      have hbp : b ∉ atomsOf ls p := fun h => hdead b h hl
      have hnu := not_mem_unitsUnder_of_not_mem_atomsOf ls p b u hb hbp hu
      refine ⟨b, hb, Or.inl hl, u, hu, ?_⟩
      rw [writeFresh_frame _ _ _ _ u hnu]; exact hm
  · right
    obtain ⟨b, hb, hqb⟩ := exists_atom_of_mem_unitsUnder ls p q hq
    exact ⟨b, mem_atomsOf_mem_allAtoms ls p b hb, Or.inr hb, q, hqb, hmq⟩

/-! ## Flags -/

theorem applyFlags_append :
    ∀ (us1 us2 : List (Place × Bool)) (f : Place → Bool),
      applyFlags (us1 ++ us2) f = applyFlags us2 (applyFlags us1 f) := by
  intro us1
  induction us1 with
  | nil => intro us2 f; rfl
  | cons x xs ih => intro us2 f; obtain ⟨a, b⟩ := x; simp only [List.cons_append, applyFlags]; rw [ih]

theorem applyFlags_flagsFor :
    ∀ (ps : List Place) (b : Bool) (f : Place → Bool) (q : Place),
      applyFlags (flagsFor ps b) f q = if q ∈ ps then b else f q := by
  intro ps
  induction ps with
  | nil => intro b f q; simp [flagsFor, applyFlags]
  | cons a ps ih =>
    intro b f q
    simp only [flagsFor, List.map_cons, applyFlags] at ih ⊢
    rw [ih]
    by_cases hq : q ∈ ps
    · simp [hq]
    · by_cases hqa : q = a <;> simp [hq, hqa]

/-! ## Normal reachability -/

theorem normalReachAux_prefix (s : SProg) :
    ∀ (k : Nat) (acc : List Bool) (i : Nat), i < acc.length →
      (normalReachAux s k acc).getD i false = acc.getD i false := by
  intro k
  induction k with
  | zero => intro acc i _; rfl
  | succ k ih =>
    intro acc i hi
    unfold normalReachAux
    rw [ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem normalReach_spec (s : SProg) (j : Nat) (hj : j < s.nodes.length) :
    NormalReachable s j =
      (decide (j = 0) ||
        (List.range j).any fun i => NormalReachable s i && (s.node i).normalSuccs.contains j) := by
  unfold NormalReachable
  have hsplit : ∀ k acc, j = acc.length →
      (normalReachAux s (k + 1) acc).getD j false =
        (decide (j = 0) ||
          (List.range j).any fun i => acc.getD i false && (s.node i).normalSuccs.contains j) := by
    intro k acc hlen
    unfold normalReachAux
    rw [normalReachAux_prefix s k _ j (by simp; omega)]
    subst hlen
    simp [List.getD_eq_getElem?_getD]
  have stepTo : ∀ m acc, acc.length + m = s.nodes.length → j ≥ acc.length →
      (normalReachAux s m acc).getD j false =
        (decide (j = 0) ||
          (List.range j).any fun i =>
            (normalReachAux s m acc).getD i false && (s.node i).normalSuccs.contains j) := by
    intro m
    induction m with
    | zero => intro acc hsum hge; omega
    | succ m ih =>
      intro acc hsum hge
      by_cases heq : j = acc.length
      · rw [hsplit m acc heq]
        congr 1
        apply any_eq_of_forall_mem
        intro i hi
        have hilt : i < acc.length := by rw [List.mem_range] at hi; omega
        rw [normalReachAux_prefix s (m + 1) acc i hilt]
      · unfold normalReachAux
        exact ih _ (by simp; omega) (by simp; omega)
  exact stepTo s.nodes.length [] (by simp) (Nat.zero_le j)

theorem normalReach_zero (s : SProg) (h : 0 < s.nodes.length) : NormalReachable s 0 = true := by
  rw [normalReach_spec s 0 h]; rfl

theorem normalReach_step (s : SProg) {i j : Nat} (hj : j < s.nodes.length) (hij : i < j)
    (hi : NormalReachable s i = true) (hs : j ∈ (s.node i).normalSuccs) :
    NormalReachable s j = true := by
  rw [normalReach_spec s j hj]
  apply Bool.or_eq_true_iff.2
  right
  apply List.any_eq_true.2
  exact ⟨i, List.mem_range.2 hij, by simp [hi, hs]⟩

/-! ## Soundness of the one-pass analyses along an edge -/

theorem foldl_append_mem_of {α : Type} :
    ∀ (xs : List (List α)) (init : List α) (a : α),
      (a ∈ init ∨ ∃ y ∈ xs, a ∈ y) → a ∈ xs.foldl (· ++ ·) init := by
  intro xs
  induction xs with
  | nil =>
    intro init a h
    rcases h with h | ⟨y, hy, _⟩
    · exact h
    · cases hy
  | cons y ys ih =>
    intro init a h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨z, hz, hza⟩
    · exact Or.inl (List.mem_append_left _ h)
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact Or.inl (List.mem_append_right _ hza)
      · exact Or.inr ⟨z, hz, hza⟩

theorem foldl_filter_mem_all (a : Place) :
    ∀ (xs : List (List Place)) (init : List Place),
      a ∈ xs.foldl (fun acc' y => acc'.filter (y.contains ·)) init →
      a ∈ init ∧ ∀ y ∈ xs, a ∈ y := by
  intro xs
  induction xs with
  | nil => intro init h; exact ⟨h, by simp⟩
  | cons y ys ih =>
    intro init h
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ h
    rw [List.mem_filter] at h1
    refine ⟨h1.1, ?_⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact List.contains_iff_mem.1 h1.2
    · exact h2 z hz

theorem mem_joinIns_may {s : SProg} {j : Nat} {ins : List (List Place)} {y : List Place}
    {a : Place} (hj : j ≠ 0) (hy : y ∈ ins) (ha : a ∈ y) : a ∈ joinIns s true j ins := by
  unfold joinIns
  simp only [hj, ite_false]
  cases ins with
  | nil => cases hy
  | cons x xs =>
    simp only [ite_true]
    apply foldl_append_mem_of
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl ha
    · exact Or.inr ⟨y, hy, ha⟩

theorem mem_of_mem_joinIns_must {s : SProg} {j : Nat} {ins : List (List Place)}
    {y : List Place} {a : Place} (hj : j ≠ 0) (hy : y ∈ ins) (ha : a ∈ joinIns s false j ins) :
    a ∈ y := by
  unfold joinIns at ha
  simp only [hj, ite_false] at ha
  cases ins with
  | nil => cases hy
  | cons x xs =>
    simp only [Bool.false_eq_true, ite_false] at ha
    obtain ⟨h1, h2⟩ := foldl_filter_mem_all a xs x ha
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h1
    · exact h2 y hy

/-- The analyses are sound along every edge out of a forward-reachable node: the reachability
flag propagates, the may-init set at the target contains the may-transfer, and the must-init set
at the target is contained in the must-transfer. -/
theorem analysis_step (s : SProg) {i j : Nat} (hj : j < s.nodes.length) (hij : i < j)
    (hreach : (reachList s).getD i false = true) {Qm QM : List Place}
    (hm : (j, Qm) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine true).getD i []))
    (hM : (j, QM) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine false).getD i [])) :
    (reachList s).getD j false = true ∧
      (∀ a ∈ Qm, a ∈ (analysis s .fine true).getD j []) ∧
      (∀ a ∈ (analysis s .fine false).getD j [], a ∈ QM) := by
  have hflow : ∀ (may : Bool) (Q : List Place),
      (j, Q) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine may).getD i []) →
      Q ∈ flowIn s .fine (reachList s) j (analysis s .fine may) := by
    intro may Q h
    unfold flowIn
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_range.2 hij, ?_⟩
    simp only [hreach, ite_true]
    rw [List.mem_map]
    exact ⟨(j, Q), List.mem_filter.2 ⟨h, by simp⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [reachList_spec s j hj]
    have hs := edgeOut_fst_mem_succs _ _ _ _ _ hm
    apply Bool.or_eq_true_iff.2
    right
    apply List.any_eq_true.2
    simp only at hs
    exact ⟨i, List.mem_range.2 hij, by rw [Bool.and_eq_true]; exact ⟨hreach, by simp [hs]⟩⟩
  · intro a ha
    rw [analysis_spec s .fine true j hj]
    exact mem_joinIns_may (by omega) (hflow true Qm hm) ha
  · intro a ha
    rw [analysis_spec s .fine false j hj] at ha
    exact mem_of_mem_joinIns_must (by omega) (hflow false QM hM) ha

/-! ## Good results -/

/-- The property of a run result established by the simulation: no double destruction, termination,
and, under the abort rule and the two remaining move-checker hypotheses, no leak on a complete
run. -/
def Good (s : SProg) (rule : PanicRule) (r : Result) : Prop :=
  NoDoubleDrop r.log ∧ r.outcome.terminated = true ∧
    (rule = .abort → InitsIntoUninit s → NoNormalPathToResume s →
      r.outcome.complete = true → NoLeak r.log)

theorem Acct.noLeak {ls : List Ty} {mem : Place → Option Nat} {log : List Event}
    {live : Place → Prop} (hacct : Acct ls mem log live) (hdead : ∀ b, ¬ live b) : NoLeak log := by
  intro v hv
  rcases hacct v hv with h | ⟨b, _, hl, _⟩
  · exact h
  · exact absurd hl (hdead b)

theorem step_drop_true_abort {L : Type} {rule : PanicRule} {P : TProg L} {m : Mach L}
    {a : Place} {nx : L} {un : Option L} (hn : P.node m.pc = .drop a nx un)
    (hab : (m.unwinding && rule == .abort) = true) :
    step rule P m true =
      .done ⟨.aborted, m.log ++ destroyEvents .drop m.mem (unitsUnder P.locals a)⟩ := by
  unfold step; rw [hn]; simp [hab]

theorem step_drop_true_some {L : Type} {rule : PanicRule} {P : TProg L} {m : Mach L}
    {a : Place} {nx l : L} (hn : P.node m.pc = .drop a nx (some l))
    (hab : (m.unwinding && rule == .abort) = false) :
    step rule P m true =
      .next { m with pc := l, unwinding := true,
                     log := m.log ++ destroyEvents .drop m.mem (unitsUnder P.locals a) } := by
  unfold step; rw [hn]; simp [hab]

theorem step_drop_true_none {L : Type} {rule : PanicRule} {P : TProg L} {m : Mach L}
    {a : Place} {nx : L} (hn : P.node m.pc = .drop a nx none)
    (hab : (m.unwinding && rule == .abort) = false) :
    step rule P m true =
      .done ⟨.unwound, m.log ++ destroyEvents .drop m.mem (unitsUnder P.locals a)⟩ := by
  unfold step; rw [hn]; simp [hab]

/-! ## Drop ladders -/

/-- State invariant inside the ladder (normal-return ladder if `cleanup = false`, cleanup
ladder if `cleanup = true`) at drop point `i`, step `k`, for the initialized-atom set `P` on
arrival at the drop point. -/
structure LInv (s : SProg) (d : Nat → Place → Decision) (i k : Nat) (cleanup : Bool)
    (P : List Place) (m : Mach Lbl) : Prop where
  dp : isDropPoint s i = true
  atoms : ∀ a ∈ P, a ∈ allAtoms s.locals
  dec : ∀ c ∈ allAtoms s.locals, (d i c = .drop → c ∈ P) ∧ (d i c = .skip → c ∉ P)
  inv : Inv s.locals m.mem m.fresh m.log (fun b => b ∈ P ∧ b ∉ (dropOrder s.locals).take k)
  ndd : NoDoubleDrop m.log
  acct : InitsIntoUninit s →
    Acct s.locals m.mem m.log (fun b => b ∈ P ∧ b ∉ (dropOrder s.locals).take k)
  flags : ∀ b, m.flags b = true ↔ b ∈ P
  cl : cleanup = true → m.unwinding = true
  unw : m.unwinding = false → NormalReachable s i = true

theorem LInv.setPc {s : SProg} {d : Nat → Place → Decision} {i k : Nat} {cleanup : Bool}
    {P : List Place} {m : Mach Lbl} (hL : LInv s d i k cleanup P m) (x : Lbl) :
    LInv s d i k cleanup P { m with pc := x } :=
  ⟨hL.dp, hL.atoms, hL.dec, hL.inv, hL.ndd, hL.acct, hL.flags, hL.cl, hL.unw⟩

theorem ladderStep_node (d : Nat → Place → Decision) (s : SProg) (i k : Nat) (cleanup : Bool) :
    (elaborate .std d s).node (if cleanup then .ulad i k else .lad i k) =
      ladderStep d s i k cleanup := by
  cases cleanup <;> rfl

theorem ladderGuarded_node (d : Nat → Place → Decision) (s : SProg) (i k : Nat) (cleanup : Bool) :
    (elaborate .std d s).node (if cleanup then .udropAt i k else .dropAt i k) =
      ladderGuarded s i k cleanup := by
  cases cleanup <;> rfl

theorem not_mem_take_of_getElem? {α : Type} {l : List α} (hnd : l.Nodup) {k : Nat} {c : α}
    (hc : l[k]? = some c) : c ∉ l.take k := by
  intro h
  rw [List.mem_take_iff_getElem] at h
  obtain ⟨j, hj, hjc⟩ := h
  obtain ⟨hk, hkc⟩ := List.getElem?_eq_some_iff.1 hc
  have hjk : j < k := by omega
  have := List.pairwise_iff_getElem.1 hnd j k (by omega) hk hjk
  exact this (hjc.trans hkc.symm)

theorem take_succ_of_getElem? {α : Type} {l : List α} {k : Nat} {c : α} (hc : l[k]? = some c) :
    l.take (k + 1) = l.take k ++ [c] := by
  rw [List.take_add_one, hc]; rfl

/-- Passing an atom that is not initialized leaves the ladder state unchanged. -/
theorem LInv.skip {s : SProg} {d : Nat → Place → Decision} {i k : Nat} {cleanup : Bool}
    {P : List Place} {m : Mach Lbl} {c : Place} (hL : LInv s d i k cleanup P m)
    (hc : (dropOrder s.locals)[k]? = some c) (hcP : c ∉ P) :
    LInv s d i (k + 1) cleanup P m := by
  have hiff : ∀ b, (b ∈ P ∧ b ∉ (dropOrder s.locals).take k) ↔
      (b ∈ P ∧ b ∉ (dropOrder s.locals).take (k + 1)) := by
    intro b
    rw [take_succ_of_getElem? hc]
    constructor
    · rintro ⟨hb, hbt⟩
      refine ⟨hb, ?_⟩
      rw [List.mem_append, List.mem_singleton]
      rintro (h | rfl)
      · exact hbt h
      · exact hcP hb
    · rintro ⟨hb, hbt⟩
      exact ⟨hb, fun h => hbt (List.mem_append_left _ h)⟩
  exact ⟨hL.dp, hL.atoms, hL.dec, hL.inv.congr hiff, hL.ndd,
    fun hii => (hL.acct hii).congr hiff, hL.flags, hL.cl, hL.unw⟩

/-- Dropping an initialized atom advances the ladder state. -/
theorem LInv.drop {s : SProg} {d : Nat → Place → Decision} {i k : Nat} {cleanup : Bool}
    {P : List Place} {m : Mach Lbl} {c : Place} (hL : LInv s d i k cleanup P m)
    (hc : (dropOrder s.locals)[k]? = some c) (hcP : c ∈ P) (cleanup' : Bool) (m' : Mach Lbl)
    (hmem : m'.mem = m.mem) (hfresh : m'.fresh = m.fresh)
    (hlog : m'.log = m.log ++ destroyEvents .drop m.mem (unitsUnder s.locals c))
    (hflags : m'.flags = m.flags) (hcl : cleanup' = true → m'.unwinding = true)
    (hunw : m'.unwinding = false → NormalReachable s i = true) :
    LInv s d i (k + 1) cleanup' P m' := by
  have hcA := hL.atoms c hcP
  have hct : c ∉ (dropOrder s.locals).take k := not_mem_take_of_getElem? (dropOrder_nodup _) hc
  have hiff : ∀ b, ((b ∈ P ∧ b ∉ (dropOrder s.locals).take k) ∧ b ∉ atomsOf s.locals c) ↔
      (b ∈ P ∧ b ∉ (dropOrder s.locals).take (k + 1)) := by
    intro b
    rw [take_succ_of_getElem? hc]
    constructor
    · rintro ⟨⟨hb, hbt⟩, hbc⟩
      refine ⟨hb, ?_⟩
      rw [List.mem_append, List.mem_singleton]
      rintro (h | rfl)
      · exact hbt h
      · rw [mem_atomsOf] at hbc
        exact hbc ⟨hcA, by simp [Place.overlaps, Place.covers, List.isPrefixOf_iff_prefix]⟩
    · rintro ⟨hb, hbt⟩
      refine ⟨⟨hb, fun h => hbt (List.mem_append_left _ h)⟩, ?_⟩
      intro hbc
      have := eq_of_mem_atomsOf_atom s.locals c b hcA hbc
      subst this
      exact hbt (List.mem_append_right _ (List.mem_singleton_self _))
  have hlive : ∀ b ∈ atomsOf s.locals c, b ∈ P ∧ b ∉ (dropOrder s.locals).take k := by
    intro b hb
    have := eq_of_mem_atomsOf_atom s.locals c b hcA hb
    subst this
    exact ⟨hcP, hct⟩
  have hmp := atom_isMovePlace s.locals c hcA
  refine ⟨hL.dp, hL.atoms, hL.dec, ?_, ?_, ?_, ?_, hcl, hunw⟩
  · rw [hmem, hfresh, hlog]
    exact (hL.inv.destroy (Or.inr rfl) hmp).congr hiff
  · rw [hlog]
    exact ndd_destroy (Or.inr rfl) hL.inv hL.ndd hlive
  · intro hii
    rw [hmem, hlog]
    exact ((hL.acct hii).destroy (Or.inr rfl) hmp).congr hiff
  · rw [hflags]; exact hL.flags

theorem ladder_good (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg) (i : Nat)
    (P : List Place) :
    ∀ (n k : Nat) (cleanup : Bool) (m : Mach Lbl) (inp : List Bool) (f : Nat),
      k + n = (dropOrder s.locals).length → LInv s d i k cleanup P m →
      m.pc = (if cleanup then .ulad i k else .lad i k) → 2 * n + 1 ≤ f →
      Good s rule (runAux rule (elaborate .std d s) f inp m) := by
  intro n
  induction n with
  | zero =>
    intro k cleanup m inp f hk hL hpc hf
    have hnone : (dropOrder s.locals)[k]? = none := List.getElem?_eq_none (by omega)
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hnoLeak : InitsIntoUninit s → NoLeak m.log := by
      intro hii
      apply (hL.acct hii).noLeak
      rintro b ⟨hbP, hbt⟩
      apply hbt
      rw [List.take_of_length_le (by omega)]
      unfold dropOrder; exact List.mem_reverse.2 (hL.atoms b hbP)
    have hn : (elaborate .std d s).node m.pc =
        (if (s.node i == .ret && !cleanup) = true then .ret else .resume) := by
      rw [hpc, ladderStep_node]; simp only [ladderStep, hnone]
    by_cases hr : (s.node i == .ret && !cleanup) = true
    · rw [ite_eq_left hr] at hn
      rw [runAux_succ_nc_done (by rw [hn]; rfl) (step_ret hn)]
      exact ⟨hL.ndd, rfl, fun _ hii _ _ => hnoLeak hii⟩
    · rw [ite_eq_right hr] at hn
      rw [runAux_succ_nc_done (by rw [hn]; rfl) (step_resume hn)]
      exact ⟨hL.ndd, rfl, fun _ hii _ _ => hnoLeak hii⟩
  | succ n ih =>
    intro k cleanup m inp f hk hL hpc hf
    have hlt : k < (dropOrder s.locals).length := by omega
    obtain ⟨c, hc⟩ : ∃ c, (dropOrder s.locals)[k]? = some c :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hcA : c ∈ allAtoms s.locals := by
      have := List.mem_of_getElem? hc
      unfold dropOrder at this; exact List.mem_reverse.1 this
    -- The drop of `c` from a machine with the state of `m`.
    have hdrop : c ∈ P → ∀ (m0 : Mach Lbl) (f0 : Nat) (inp0 : List Bool),
        LInv s d i k cleanup P m0 →
        (elaborate .std d s).node m0.pc = ladderDrop s i k cleanup c → 2 * n + 2 ≤ f0 →
        Good s rule (runAux rule (elaborate .std d s) f0 inp0 m0) := by
      intro hcP m0 f0 inp0 hL0 hn0 hf0
      obtain ⟨f1, rfl⟩ : ∃ f1, f0 = f1 + 1 := ⟨f0 - 1, by omega⟩
      have hch : ((elaborate .std d s).node m0.pc).isChoice = true := by
        rw [hn0]; rfl
      simp only [ladderDrop] at hn0
      have hlog₁ := ndd_destroy (Or.inr rfl) hL0.inv hL0.ndd (fun b hb => by
        have := eq_of_mem_atomsOf_atom s.locals c b hcA hb
        subst this
        exact ⟨hcP, not_mem_take_of_getElem? (dropOrder_nodup _) hc⟩)
      unfold runAux
      rw [ite_eq_left hch]
      cases hb : inp0.headD false with
      | false =>
        rw [step_drop_false hn0]
        simp only
        apply ih (k + 1) cleanup _ inp0.tail f1 (by omega) _ (by simp) (by omega)
        exact hL0.drop hc hcP cleanup _ rfl rfl rfl rfl hL0.cl hL0.unw
      | true =>
        by_cases hab : (m0.unwinding && rule == .abort) = true
        · rw [step_drop_true_abort hn0 hab]
          exact ⟨hlog₁, rfl, fun _ _ _ h => by cases h⟩
        · have hab' : (m0.unwinding && rule == .abort) = false := by simpa using hab
          by_cases hnr : (s.node i == .ret && !cleanup) = true
          · rw [ite_eq_left hnr] at hn0
            rw [step_drop_true_some hn0 hab']
            simp only
            apply ih (k + 1) true _ inp0.tail f1 (by omega) _ rfl (by omega)
            exact hL0.drop hc hcP true _ rfl rfl rfl rfl (fun _ => rfl) (fun h => by cases h)
          · rw [ite_eq_right hnr] at hn0
            rw [step_drop_true_none hn0 hab']
            refine ⟨hlog₁, rfl, ?_⟩
            intro hrule _ hnn _
            subst hrule
            have hu : m0.unwinding = false := by
              cases hm : m0.unwinding
              · rfl
              · rw [hm] at hab; exact absurd rfl hab
            have hcl : cleanup = false := by
              cases hcl : cleanup
              · rfl
              · rw [hL0.cl hcl] at hu; cases hu
            subst hcl
            have hres : s.node i = .resume := by
              have hdp := hL0.dp
              simp only [isDropPoint, Bool.or_eq_true, beq_iff_eq] at hdp
              rcases hdp with h | h
              · exact absurd (by simp [h]) hnr
              · exact h
            exact absurd hres (hnn i (lt_of_isDropPoint s i hL0.dp) (hL0.unw hu))
    have hnext : ∀ (x : Lbl), x = (if cleanup then .ulad i (k + 1) else .lad i (k + 1)) →
        ∀ (m1 : Mach Lbl) (f1 : Nat) (inp1 : List Bool), LInv s d i (k + 1) cleanup P m1 →
        m1.pc = x → 2 * n + 1 ≤ f1 → Good s rule (runAux rule (elaborate .std d s) f1 inp1 m1) := by
      intro x hx m1 f1 inp1 hL1 hpc1 hf1
      exact ih (k + 1) cleanup m1 inp1 f1 (by omega) hL1 (by rw [hpc1, hx]) hf1
    have hdec := hL.dec c hcA
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    cases hd : d i c with
    | drop =>
      apply hdrop (hdec.1 hd) m (f' + 1) inp hL _ (by omega)
      rw [hpc, ladderStep_node]; simp only [ladderStep, hc, hd]
    | skip =>
      have hn : (elaborate .std d s).node m.pc =
          .goto (if cleanup then .ulad i (k + 1) else .lad i (k + 1)) := by
        rw [hpc, ladderStep_node]; simp only [ladderStep, hc, hd]
      rw [runAux_succ_nc (by rw [hn]; rfl) (step_goto hn)]
      exact hnext _ rfl _ f' inp ((hL.skip hc (hdec.2 hd)).setPc _) rfl (by omega)
    | test =>
      have hn : (elaborate .std d s).node m.pc =
          .test c (if cleanup then .udropAt i k else .dropAt i k)
            (if cleanup then .ulad i (k + 1) else .lad i (k + 1)) := by
        rw [hpc, ladderStep_node]; simp only [ladderStep, hc, hd]
      by_cases hcP : c ∈ P
      · have hfl : m.flags c = true := (hL.flags c).2 hcP
        rw [runAux_succ_nc (by rw [hn]; rfl) (step_test hn)]
        simp only [hfl, ite_true]
        apply hdrop hcP _ f' inp (hL.setPc _) _ (by omega)
        simp only
        rw [ladderGuarded_node]; simp only [ladderGuarded, hc]
      · have hfl : m.flags c = false := by
          cases h : m.flags c
          · rfl
          · exact absurd ((hL.flags c).1 h) hcP
        rw [runAux_succ_nc (by rw [hn]; rfl) (step_test hn)]
        simp only [hfl, Bool.false_eq_true, ite_false]
        exact hnext _ rfl _ f' inp ((hL.skip hc hcP).setPc _) rfl (by omega)

/-! ## Source nodes -/

/-- State invariant at source node `i` for an initialized-atom set `P`. -/
structure SInv (s : SProg) (i : Nat) (P : List Place) (m : Mach Lbl) : Prop where
  lt : i < s.nodes.length
  reach : (reachList s).getD i false = true
  may : ∀ a ∈ P, a ∈ (analysis s .fine true).getD i []
  must : ∀ a ∈ (analysis s .fine false).getD i [], a ∈ P
  inv : Inv s.locals m.mem m.fresh m.log (· ∈ P)
  ndd : NoDoubleDrop m.log
  acct : InitsIntoUninit s → Acct s.locals m.mem m.log (· ∈ P)
  flags : ∀ b, m.flags b = true ↔ b ∈ P
  unw : m.unwinding = false → NormalReachable s i = true

theorem mayInit_iff (s : SProg) (i : Nat) (a : Place) :
    mayInit s .fine i a = true ↔ a ∈ (analysis s .fine true).getD i [] := by
  unfold mayInit; exact List.contains_iff_mem

theorem mustInit_iff (s : SProg) (i : Nat) (hi : i < s.nodes.length) (a : Place) :
    mustInit s .fine i a = true ↔ a ∈ (analysis s .fine false).getD i [] := by
  unfold mustInit
  have hl : i < (analysis s .fine false).length := by rw [analysis_length]; exact hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  exact List.contains_iff_mem

theorem SInv.atoms {s : SProg} {i : Nat} {P : List Place} {m : Mach Lbl} (hS : SInv s i P m) :
    ∀ a ∈ P, a ∈ allAtoms s.locals := fun a ha =>
  (forwardReachable_and_mem_allAtoms_of_mayInit s i a ((mayInit_iff s i a).2 (hS.may a ha))).2

theorem SInv.notMem_of_mayInit_false {s : SProg} {i : Nat} {P : List Place} {m : Mach Lbl}
    (hS : SInv s i P m) {a : Place} (h : mayInit s .fine i a = false) : a ∉ P := by
  intro ha
  rw [(mayInit_iff s i a).2 (hS.may a ha)] at h
  cases h

/-- Assembling the invariant at a successor node. -/
theorem SInv.next {s : SProg} (hfwd : Forward s) {i j : Nat} {P P' : List Place}
    {m m' : Mach Lbl} (hS : SInv s i P m) (hsucc : j ∈ (s.node i).succs) {Qm QM : List Place}
    (hm : (j, Qm) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine true).getD i []))
    (hM : (j, QM) ∈ edgeOut s.locals .fine (s.node i) ((analysis s .fine false).getD i []))
    (hPm : ∀ a ∈ P', a ∈ Qm) (hPM : ∀ a ∈ QM, a ∈ P')
    (hinv : Inv s.locals m'.mem m'.fresh m'.log (· ∈ P')) (hndd : NoDoubleDrop m'.log)
    (hacct : InitsIntoUninit s → Acct s.locals m'.mem m'.log (· ∈ P'))
    (hflags : ∀ b, m'.flags b = true ↔ b ∈ P')
    (hunw : m'.unwinding = false → NormalReachable s j = true) :
    SInv s j P' m' := by
  have hij := hfwd.2 i hS.lt j hsucc
  obtain ⟨hr, hmay, hmust⟩ := analysis_step s hij.2 hij.1 hS.reach hm hM
  exact ⟨hij.2, hr, fun a ha => hmay a (hPm a ha), fun a ha => hPM a (hmust a ha), hinv, hndd,
    hacct, hflags, hunw⟩

theorem step_abort {L : Type} {rule : PanicRule} {P : TProg L} {m : Mach L} {b : Bool}
    (hn : P.node m.pc = .abort) : step rule P m b = .done ⟨.aborted, m.log⟩ := by
  unfold step; rw [hn]

theorem src_good (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg) (hfwd : Forward s)
    (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s) (hcompat : AllCompatible s d) :
    ∀ (n i : Nat) (P : List Place) (m : Mach Lbl) (inp : List Bool) (f : Nat),
      s.nodes.length - i ≤ n → SInv s i P m → m.pc = .src i →
      3 * (s.nodes.length - i) + 2 * (allAtoms s.locals).length + 2 ≤ f →
      Good s rule (runAux rule (elaborate .std d s) f inp m) := by
  intro n
  induction n with
  | zero => intro i P m inp f hn hS; have := hS.lt; omega
  | succ n ih =>
    intro i P m inp f hlen hS hpc hf
    have hi := hS.lt
    have IH : ∀ (j : Nat) (P' : List Place) (m' : Mach Lbl) (inp' : List Bool) (f' : Nat),
        j ∈ (s.node i).succs → SInv s j P' m' → m'.pc = .src j →
        3 * (s.nodes.length - i) + 2 * (allAtoms s.locals).length + 2 ≤ f' + 3 →
        Good s rule (runAux rule (elaborate .std d s) f' inp' m') := by
      intro j P' m' inp' f' hsucc hS' hpc' hf'
      have hij := hfwd.2 i hi j hsucc
      exact ih j P' m' inp' f' (by omega) hS' hpc' (by omega)
    have hsrc : ∀ (x : TNode Lbl), (match s.node i with
        | .init p _ => TNode.init p (.post i)
        | .move p _ => .move p (.post i)
        | .branch a b => .branch (.src a) (.src b)
        | .call args _ _ _ => .setFlags (flagsFor (argKill s.locals .fine args) false) (.pre i)
        | .ret | .resume => .goto (.lad i 0)
        | .abort => .abort) = x → (elaborate .std d s).node m.pc = x := by
      intro x hx
      rw [hpc, ← hx]
      simp only [elaborate, elabNode, hi, ite_true]
      cases s.node i <;> rfl
    have hladder : isDropPoint s i = true → (elaborate .std d s).node m.pc = .goto (.lad i 0) →
        Good s rule (runAux rule (elaborate .std d s) f inp m) := by
      intro hdp hn1
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [runAux_succ_nc (by rw [hn1]; rfl) (step_goto hn1)]
      apply ladder_good rule d s i P (dropOrder s.locals).length 0 false _ inp f' (by omega) _ rfl
        (by simp only [dropOrder, List.length_reverse]; omega)
      have hiff : ∀ b, b ∈ P ↔ (b ∈ P ∧ b ∉ (dropOrder s.locals).take 0) := by simp
      refine ⟨hdp, hS.atoms, ?_, hS.inv.congr hiff, hS.ndd, fun hii => (hS.acct hii).congr hiff,
        hS.flags, (fun h => by cases h), hS.unw⟩
      intro c hc
      have hcomp := hcompat i hi hdp hS.reach c hc
      constructor
      · intro hd
        rw [hd] at hcomp
        exact hS.must c ((mustInit_iff s i hi c).1 hcomp)
      · intro hd
        rw [hd] at hcomp
        apply hS.notMem_of_mayInit_false
        simpa [Compatible] using hcomp
    cases hn : s.node i with
    | init p nx =>
      have hp : isMovePlace s.locals p = true := hplaces i hi p (by simp [SNode.places, hn])
      have hn1 := hsrc (.init p (.post i)) (by rw [hn])
      let w := writeFresh (unitsUnder s.locals p) m.mem m.fresh m.log
      let m1 : Mach Lbl := { m with pc := .post i, mem := w.1, fresh := w.2.1, log := w.2.2 }
      have hn2 : (elaborate .std d s).node m1.pc =
          .setFlags (flagsFor (atomsOf s.locals p) true) (.src nx) := by
        simp only [m1, elaborate, elabNode, hn]; rfl
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      rw [show f' + 2 = (f' + 1) + 1 by omega,
        runAux_succ_nc (m' := m1) (by rw [hn1]; rfl) (step_init hn1),
        runAux_succ_nc (by rw [hn2]; rfl) (step_setFlags hn2)]
      have hsucc : nx ∈ (s.node i).succs := by simp [hn, SNode.succs]
      have hij := hfwd.2 i hi nx hsucc
      apply IH nx (P ++ atomsOf s.locals p) _ inp f' hsucc _ rfl (by omega)
      refine hS.next hfwd hsucc (Qm := (analysis s .fine true).getD i [] ++ atomsOf s.locals p)
        (QM := (analysis s .fine false).getD i [] ++ atomsOf s.locals p)
        (by simp [hn, edgeOut]) (by simp [hn, edgeOut]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rcases List.mem_append.1 ha with h | h
        · exact List.mem_append_left _ (hS.may a h)
        · exact List.mem_append_right _ h
      · intro a ha
        rcases List.mem_append.1 ha with h | h
        · exact List.mem_append_left _ (hS.must a h)
        · exact List.mem_append_right _ h
      · exact (hS.inv.writeInit hp (mem' := w.1) (n' := w.2.1) (log' := w.2.2) rfl).congr
          (fun b => by simp)
      · obtain ⟨cs, hcs, hcse⟩ := writeFresh_log (unitsUnder s.locals p) m.mem m.fresh m.log
        show NoDoubleDrop w.2.2
        rw [hcs]; exact ndd_creates hS.ndd hcse
      · intro hii
        have hdead : ∀ b ∈ atomsOf s.locals p, ¬ b ∈ P := by
          intro b hb
          have h := hii i hi
          simp only [hn] at h
          exact hS.notMem_of_mayInit_false (h b hb)
        exact (Acct.write (hS.acct hii) hdead).congr (fun b => by simp)
      · intro b
        show applyFlags (flagsFor (atomsOf s.locals p) true) m.flags b = true ↔ _
        rw [applyFlags_flagsFor, List.mem_append]
        by_cases hb : b ∈ atomsOf s.locals p
        · simp [hb]
        · simp only [hb, ite_false, or_false]; exact hS.flags b
      · intro hu
        exact normalReach_step s hij.2 hij.1 (hS.unw hu) (by simp [hn, SNode.normalSuccs])
    | move p nx =>
      have hp : isMovePlace s.locals p = true := hplaces i hi p (by simp [SNode.places, hn])
      have hn1 := hsrc (.move p (.post i)) (by rw [hn])
      let log1 := m.log ++ destroyEvents .consume m.mem (unitsUnder s.locals p)
      let m1 : Mach Lbl := { m with pc := .post i, log := log1 }
      have hn2 : (elaborate .std d s).node m1.pc =
          .setFlags (flagsFor (atomsOf s.locals p) false) (.src nx) := by
        simp only [m1, elaborate, elabNode, hn]; rfl
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      rw [show f' + 2 = (f' + 1) + 1 by omega,
        runAux_succ_nc (m' := m1) (by rw [hn1]; rfl) (step_move hn1),
        runAux_succ_nc (by rw [hn2]; rfl) (step_setFlags hn2)]
      have hsucc : nx ∈ (s.node i).succs := by simp [hn, SNode.succs]
      have hij := hfwd.2 i hi nx hsucc
      have hlive : ∀ b ∈ atomsOf s.locals p, b ∈ P := by
        intro b hb
        have h := hmoves i hi
        simp only [hn] at h
        exact hS.must b ((mustInit_iff s i hi b).1 (h b hb))
      apply IH nx (minus P (atomsOf s.locals p)) _ inp f' hsucc _ rfl (by omega)
      refine hS.next hfwd hsucc
        (Qm := minus ((analysis s .fine true).getD i []) (atomsOf s.locals p))
        (QM := minus ((analysis s .fine false).getD i []) (atomsOf s.locals p))
        (by simp [hn, edgeOut, killSet]) (by simp [hn, edgeOut, killSet]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [mem_minus_iff] at ha ⊢
        exact ⟨hS.may a ha.1, ha.2⟩
      · intro a ha
        rw [mem_minus_iff] at ha ⊢
        exact ⟨hS.must a ha.1, ha.2⟩
      · exact (hS.inv.destroy (Or.inl rfl) hp).congr (fun b => mem_minus_iff.symm)
      · exact ndd_destroy (Or.inl rfl) hS.inv hS.ndd hlive
      · intro hii
        exact ((hS.acct hii).destroy (Or.inl rfl) hp).congr (fun b => mem_minus_iff.symm)
      · intro b
        show applyFlags (flagsFor (atomsOf s.locals p) false) m.flags b = true ↔ _
        rw [applyFlags_flagsFor, mem_minus_iff]
        by_cases hb : b ∈ atomsOf s.locals p
        · simp [hb]
        · simp only [hb, ite_false, not_false_eq_true, and_true]; exact hS.flags b
      · intro hu
        exact normalReach_step s hij.2 hij.1 (hS.unw hu) (by simp [hn, SNode.normalSuccs])
    | branch l1 l2 =>
      have hn1 := hsrc (.branch (.src l1) (.src l2)) (by rw [hn])
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [runAux_succ_ch (by rw [hn1]; rfl) (step_branch hn1)]
      have key : ∀ (j : Nat), j ∈ (s.node i).succs → j ∈ (s.node i).normalSuccs →
          (j, (analysis s .fine true).getD i []) ∈
            edgeOut s.locals .fine (s.node i) ((analysis s .fine true).getD i []) →
          (j, (analysis s .fine false).getD i []) ∈
            edgeOut s.locals .fine (s.node i) ((analysis s .fine false).getD i []) →
          ∀ m' : Mach Lbl, m'.pc = .src j → m'.mem = m.mem → m'.fresh = m.fresh →
            m'.log = m.log → m'.flags = m.flags → m'.unwinding = m.unwinding →
            Good s rule (runAux rule (elaborate .std d s) f' inp.tail m') := by
        intro j hsucc hnorm hm hM m' hpc' hmem hfresh hlog hflags hunw
        have hij := hfwd.2 i hi j hsucc
        apply IH j P m' inp.tail f' hsucc _ hpc' (by omega)
        refine hS.next hfwd hsucc hm hM (fun a ha => hS.may a ha) (fun a ha => hS.must a ha)
          ?_ ?_ ?_ ?_ ?_
        · rw [hmem, hfresh, hlog]; exact hS.inv
        · rw [hlog]; exact hS.ndd
        · intro hii; rw [hmem, hlog]; exact hS.acct hii
        · rw [hflags]; exact hS.flags
        · intro hu
          rw [hunw] at hu
          exact normalReach_step s hij.2 hij.1 (hS.unw hu) hnorm
      cases hb : inp.headD false with
      | true =>
        exact key l1 (by simp [hn, SNode.succs]) (by simp [hn, SNode.normalSuccs])
          (by simp [hn, edgeOut]) (by simp [hn, edgeOut]) _ rfl rfl rfl rfl rfl rfl
      | false =>
        exact key l2 (by simp [hn, SNode.succs]) (by simp [hn, SNode.normalSuccs])
          (by simp [hn, edgeOut]) (by simp [hn, edgeOut]) _ rfl rfl rfl rfl rfl rfl
    | call args dest nx un =>
      have hargs : ∀ q ∈ args, isMovePlace s.locals q = true :=
        fun q hq => hplaces i hi q (by simp [SNode.places, hn, hq])
      have hmv := hmoves i hi
      simp only [hn] at hmv
      obtain ⟨hmust, hdisj⟩ := hmv
      have hlive : ∀ q ∈ args, ∀ b ∈ atomsOf s.locals q, b ∈ P :=
        fun q hq b hb => hS.must b ((mustInit_iff s i hi b).1 (hmust q hq b hb))
      have hK : argKill s.locals .fine args = args.flatMap (atomsOf s.locals) := rfl
      have hn1 := hsrc (.setFlags (flagsFor (argKill s.locals .fine args) false) (.pre i))
        (by rw [hn])
      let m1 : Mach Lbl :=
        { m with pc := .pre i, flags := applyFlags (flagsFor (argKill s.locals .fine args) false) m.flags }
      have hn2 : (elaborate .std d s).node m1.pc = .call args dest (.post i) (.unw i) := by
        simp only [m1, elaborate, elabNode, hn]
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 3 := ⟨f - 3, by omega⟩
      rw [show f' + 3 = (f' + 2) + 1 by omega,
        runAux_succ_nc (m' := m1) (by rw [hn1]; rfl) (step_setFlags hn1)]
      let K := args.flatMap (atomsOf s.locals)
      let log₁ := m.log ++ args.flatMap (fun q => destroyEvents .consume m.mem (unitsUnder s.locals q))
      have hinv1 : Inv s.locals m.mem m.fresh log₁ (fun b => b ∈ P ∧ b ∉ K) :=
        hS.inv.consumeAll args m.log _ hargs
      have hndd1 : NoDoubleDrop log₁ := ndd_destroyAll args m.log _ hS.inv hS.ndd hargs hlive hdisj
      have hacct1 : InitsIntoUninit s → Acct s.locals m.mem log₁ (fun b => b ∈ P ∧ b ∉ K) :=
        fun hii => (hS.acct hii).destroyAll args m.log _ hargs
      have hflags1 : ∀ b, m1.flags b = true ↔ (b ∈ P ∧ b ∉ K) := by
        intro b
        show applyFlags (flagsFor (argKill s.locals .fine args) false) m.flags b = true ↔ _
        rw [applyFlags_flagsFor, hK]
        by_cases hb : b ∈ args.flatMap (atomsOf s.locals)
        · simp [K, hb]
        · simp only [hb, ite_false, K, not_false_eq_true, and_true]; exact hS.flags b
      have hch : ((elaborate .std d s).node m1.pc).isChoice = true := by rw [hn2]; rfl
      rw [show f' + 2 = (f' + 1) + 1 by omega]
      cases hb : inp.headD false with
      | true =>
        let m2 : Mach Lbl := { m1 with pc := .unw i, unwinding := true, log := log₁ }
        have hs2 : step rule (elaborate .std d s) m1 (inp.headD false) = .next m2 := by
          rw [hb]; exact step_call_true hn2
        rw [runAux_succ_ch hch hs2]
        have hn3 : (elaborate .std d s).node m2.pc = .goto (.src un) := by
          simp only [m2, elaborate, elabNode, hn]
        rw [runAux_succ_nc (by rw [hn3]; rfl) (step_goto hn3)]
        have hsucc : un ∈ (s.node i).succs := by simp [hn, SNode.succs]
        apply IH un (minus P K) _ inp.tail f' hsucc _ rfl (by omega)
        refine hS.next hfwd hsucc (Qm := minus ((analysis s .fine true).getD i []) K)
          (QM := minus ((analysis s .fine false).getD i []) K)
          (by simp [hn, edgeOut, killSet_fine, K]) (by simp [hn, edgeOut, killSet_fine, K]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro a ha; rw [mem_minus_iff] at ha ⊢; exact ⟨hS.may a ha.1, ha.2⟩
        · intro a ha; rw [mem_minus_iff] at ha ⊢; exact ⟨hS.must a ha.1, ha.2⟩
        · exact hinv1.congr (fun b => mem_minus_iff.symm)
        · exact hndd1
        · intro hii; exact (hacct1 hii).congr (fun b => mem_minus_iff.symm)
        · intro b; rw [mem_minus_iff]; exact hflags1 b
        · intro h; cases h
      | false =>
        have hsucc : nx ∈ (s.node i).succs := by simp [hn, SNode.succs]
        have hij := hfwd.2 i hi nx hsucc
        have hunw' : m.unwinding = false → NormalReachable s nx = true := fun hu =>
          normalReach_step s hij.2 hij.1 (hS.unw hu) (by simp [hn, SNode.normalSuccs])
        cases dest with
        | none =>
          let m2 : Mach Lbl := { m1 with pc := .post i, log := log₁ }
          have hs2 : step rule (elaborate .std d s) m1 (inp.headD false) = .next m2 := by
            rw [hb]; exact step_call_false_none hn2
          rw [runAux_succ_ch hch hs2]
          have hn3 : (elaborate .std d s).node m2.pc =
              .setFlags ([] ++ flagsFor [] true) (.src nx) := by
            simp only [m2, elaborate, elabNode, hn]; rfl
          rw [runAux_succ_nc (by rw [hn3]; rfl) (step_setFlags hn3)]
          apply IH nx (minus P K) _ inp.tail f' hsucc _ rfl (by omega)
          refine hS.next hfwd hsucc (Qm := minus ((analysis s .fine true).getD i []) K)
            (QM := minus ((analysis s .fine false).getD i []) K)
            (by simp [hn, edgeOut, killSet_fine, K]) (by simp [hn, edgeOut, killSet_fine, K])
            ?_ ?_ ?_ ?_ ?_ ?_ hunw'
          · intro a ha; rw [mem_minus_iff] at ha ⊢; exact ⟨hS.may a ha.1, ha.2⟩
          · intro a ha; rw [mem_minus_iff] at ha ⊢; exact ⟨hS.must a ha.1, ha.2⟩
          · exact hinv1.congr (fun b => mem_minus_iff.symm)
          · exact hndd1
          · intro hii; exact (hacct1 hii).congr (fun b => mem_minus_iff.symm)
          · intro b
            show applyFlags ([] ++ flagsFor [] true) m1.flags b = true ↔ _
            simp only [List.nil_append, flagsFor, List.map_nil, applyFlags]
            rw [mem_minus_iff]; exact hflags1 b
        | some dd =>
          have hpd : isMovePlace s.locals dd = true := hplaces i hi dd (by simp [SNode.places, hn])
          let w := writeFresh (unitsUnder s.locals dd) m.mem m.fresh log₁
          let m2 : Mach Lbl := { m1 with pc := .post i, mem := w.1, fresh := w.2.1, log := w.2.2 }
          have hs2 : step rule (elaborate .std d s) m1 (inp.headD false) = .next m2 := by
            rw [hb]; exact step_call_false_some hn2
          rw [runAux_succ_ch hch hs2]
          have hn3 : (elaborate .std d s).node m2.pc =
              .setFlags ([] ++ flagsFor (atomsOf s.locals dd) true) (.src nx) := by
            simp only [m2, elaborate, elabNode, hn]; rfl
          rw [runAux_succ_nc (by rw [hn3]; rfl) (step_setFlags hn3)]
          apply IH nx (minus P K ++ atomsOf s.locals dd) _ inp.tail f' hsucc _ rfl (by omega)
          refine hS.next hfwd hsucc
            (Qm := minus ((analysis s .fine true).getD i []) K ++ atomsOf s.locals dd)
            (QM := minus ((analysis s .fine false).getD i []) K ++ atomsOf s.locals dd)
            (by simp [hn, edgeOut, killSet_fine, K]) (by simp [hn, edgeOut, killSet_fine, K])
            ?_ ?_ ?_ ?_ ?_ ?_ hunw'
          · intro a ha
            rw [mem_minus_append] at ha ⊢
            rcases ha with ⟨h1, h2⟩ | h
            · exact Or.inl ⟨hS.may a h1, h2⟩
            · exact Or.inr h
          · intro a ha
            rw [mem_minus_append] at ha ⊢
            rcases ha with ⟨h1, h2⟩ | h
            · exact Or.inl ⟨hS.must a h1, h2⟩
            · exact Or.inr h
          · exact (hinv1.writeInit hpd (mem' := w.1) (n' := w.2.1) (log' := w.2.2) rfl).congr
              (fun b => mem_minus_append.symm)
          · obtain ⟨cs, hcs, hcse⟩ := writeFresh_log (unitsUnder s.locals dd) m.mem m.fresh log₁
            show NoDoubleDrop w.2.2
            rw [hcs]; exact ndd_creates hndd1 hcse
          · intro hii
            have hdead : ∀ b ∈ atomsOf s.locals dd, ¬ (b ∈ P ∧ b ∉ K) := by
              intro b hb ⟨hbP, hbK⟩
              have h := hii i hi
              simp only [hn] at h
              rcases h b hb with h | h
              · exact hS.notMem_of_mayInit_false h hbP
              · obtain ⟨q, hq, hov⟩ := List.any_eq_true.1 h
                exact hbK (List.mem_flatMap.2 ⟨q, hq, (mem_atomsOf _ _ _).2
                  ⟨mem_atomsOf_mem_allAtoms _ _ _ hb, hov⟩⟩)
            exact (Acct.write (hacct1 hii) hdead).congr (fun b => mem_minus_append.symm)
          · intro b
            show applyFlags ([] ++ flagsFor (atomsOf s.locals dd) true) m1.flags b = true ↔ _
            rw [List.nil_append, applyFlags_flagsFor, mem_minus_append]
            by_cases hbd : b ∈ atomsOf s.locals dd
            · simp [hbd]
            · simp only [hbd, ite_false, or_false]; exact hflags1 b
    | ret => exact hladder (by simp [isDropPoint, hn]) (hsrc _ (by rw [hn]))
    | resume => exact hladder (by simp [isDropPoint, hn]) (hsrc _ (by rw [hn]))
    | abort =>
      have hn1 := hsrc .abort (by rw [hn])
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [runAux_succ_nc_done (by rw [hn1]; rfl) (step_abort hn1)]
      exact ⟨hS.ndd, rfl, fun _ _ _ h => by cases h⟩

/-! ## Every run of the elaboration -/

theorem SInv.initial (d : Nat → Place → Decision) (s : SProg) (hfwd : Forward s) :
    SInv s 0 [] (initMach (elaborate .std d s)) := by
  refine ⟨hfwd.1, ?_, (fun a ha => by cases ha), ?_, Inv.initial s.locals, ?_,
    (fun _ => Acct.initial _ _ _), (fun b => by simp [initMach]),
    (fun _ => normalReach_zero s hfwd.1)⟩
  · rw [reachList_spec s 0 hfwd.1]; rfl
  · intro a ha
    rw [analysis_spec s .fine false 0 hfwd.1 [], joinIns_zero] at ha
    cases ha
  · exact ⟨by simp [destroyedIds, initMach], by simp [destroyedIds, initMach], by simp [initMach]⟩

/-- **Every run of the elaboration is good.** For a forward program whose places are move paths
and which moves only definitely-initialized places, and for a decision map compatible with the
fine analyses at every forward-reachable drop point (standard flag maintenance, either panic
rule), every run of the elaboration terminates and destroys no value twice (nor an uncreated
value, nor unwritten memory); if in addition the panic rule is `abort`, the program initializes
only definitely-uninitialized places and no `resume` node is reachable along normal edges only,
then every complete run leaks nothing. -/
theorem runElab_good (rule : PanicRule) (d : Nat → Place → Decision) (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hcompat : AllCompatible s d) (inp : List Bool) :
    Good s rule (runElab rule .std d s inp) := by
  unfold runElab run
  exact src_good rule d s hfwd hplaces hmoves hcompat _ 0 [] _ inp _ (Nat.le_refl _)
    (SInv.initial d s hfwd) rfl (by unfold fuelFor; omega)

end Toy.DropFlags
