import ToyCoalesce.Inv

/-!
# Proofs: the access-log certificate and `MoveSem.deinit` upgrades
-/

namespace Toy.Coalesce.Obs

open Toy.Coalesce Toy.Coalesce.Inv

/-! ## First accesses in a log -/

/-- The first access to cell `(l, o)` in `d` (if any) is not a read. -/
abbrev ft (l o : Nat) (d : List Access) : Bool := firstTouchNotRead (fun _ => true) l o d

/-- Some entry of `d` accesses cell `(l, o)`. -/
def touched (d : List Access) (l o : Nat) : Bool := d.any (fun e => e.loc == l && e.off == o)

theorem ft_append (l o : Nat) (d1 d2 : List Access) :
    ft l o (d1 ++ d2) = if touched d1 l o = true then ft l o d1 else ft l o d2 := by
  induction d1 with
  | nil => simp [touched]
  | cons e d1 ih =>
    simp only [List.cons_append, firstTouchNotRead, Bool.true_and, touched, List.any_cons,
      Bool.or_eq_true] at ih ⊢
    by_cases he : (e.loc == l && e.off == o) = true
    · simp [he]
    · simp only [he]
      simpa [touched] using ih

theorem touched_of_ft_false {l o : Nat} {d : List Access} (h : ft l o d = false) :
    touched d l o = true := by
  induction d with
  | nil => simp [firstTouchNotRead] at h
  | cons e d ih =>
    simp only [firstTouchNotRead, Bool.true_and] at h
    simp only [touched, List.any_cons, Bool.or_eq_true]
    by_cases he : (e.loc == l && e.off == o) = true
    · exact Or.inl he
    · simp only [he] at h
      exact Or.inr (by simpa [touched] using ih h)

theorem ft_of_not_touched {l o : Nat} {d : List Access} (h : touched d l o = false) :
    ft l o d = true := by
  cases hf : ft l o d
  · rw [touched_of_ft_false hf] at h; cases h
  · rfl

/-- If no entry of `d` reads cell `(l, o)`, the first access (if any) is not a read. -/
theorem firstTouchNotRead_of_noRead (after : Access → Bool) {l o : Nat} {d : List Access}
    (h : ∀ e ∈ d, e.loc = l → e.off = o → e.kind ≠ .read) :
    firstTouchNotRead after l o d = true := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    simp only [firstTouchNotRead]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have := h e (List.mem_cons_self ..) hc.1.2 hc.2
      simpa using this
    · exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- Entries not selected by `after` can be skipped. -/
theorem firstTouchNotRead_skip (after : Access → Bool) (l o : Nat) {d1 : List Access}
    (h : ∀ e ∈ d1, after e = false) (d2 : List Access) :
    firstTouchNotRead after l o (d1 ++ d2) = firstTouchNotRead after l o d2 := by
  induction d1 with
  | nil => rfl
  | cons e d1 ih =>
    simp only [List.cons_append, firstTouchNotRead, h e (List.mem_cons_self ..), Bool.false_and,
      Bool.false_eq_true, ↓reduceIte]
    exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- If every entry accessing `(l, o)` is selected by `after`, the selection does not matter. -/
theorem firstTouchNotRead_all (after : Access → Bool) (l o : Nat) {d : List Access}
    (h : ∀ e ∈ d, e.loc = l → e.off = o → after e = true) :
    firstTouchNotRead after l o d = ft l o d := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    simp only [firstTouchNotRead, Bool.true_and]
    have ih' := ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    by_cases hc : (e.loc == l && e.off == o) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp [h e (List.mem_cons_self ..) hc.1 hc.2, hc.1, hc.2]
    · have hc' : (after e && e.loc == l && e.off == o) = false := by
        simp only [Bool.and_assoc]; cases after e <;> simp_all
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ih'

/-! ## Simulation against a run with some cells uninitialized -/

/-- A set of cells. -/
abbrev Cells := Nat → Nat → Bool

/-- The cells of `X` not accessed in `d`. -/
def Cells.after (X : Cells) (d : List Access) : Cells := fun l o => X l o && !touched d l o

/-- A state with memory and log forgotten. -/
def erase (s : St) : St := { s with mem := fun _ _ => .uninit, log := [] }

/-- `s'` is `s` with the cells of `X` uninitialized (logs may differ). -/
def Rel (X : Cells) (s s' : St) : Prop :=
  erase s = erase s' ∧ ∀ l o, s'.mem l o = if X l o = true then .uninit else s.mem l o

/-- No cell of `X` is first accessed by a read in `d`. -/
def OK (X : Cells) (d : List Access) : Prop := ∀ l o, X l o = true → ft l o d = true

/-- Some cell of `X` is first accessed by a read in `d`. -/
def Bad (X : Cells) (d : List Access) : Prop := ∃ l o, X l o = true ∧ ft l o d = false

/-- The recorded pairs of `s'` are among those of `s`. -/
def Sub (s' s : St) : Prop := ∀ c ∈ s'.conflicts, c ∈ s.conflicts

/-- Simulation result for a state transformer run from `s` (source) / a related state (target),
ending in `t` (source) / `t'` (target). -/
def SimS (X : Cells) (s t t' : St) : Prop :=
  ∃ d, t.log = s.log ++ d ∧
    ((OK X d ∧ Rel (X.after d) t t') ∨ (Bad X d ∧ t'.status = .ub ∧ Sub t' t))

/-- Simulation result for a value-returning operation. -/
def SimV (X : Cells) (s : St) (r r' : St × Option (List Val)) : Prop :=
  ∃ d, r.1.log = s.log ++ d ∧
    ((OK X d ∧ Rel (X.after d) r.1 r'.1 ∧ r.2 = r'.2) ∨
     (Bad X d ∧ r'.1.status = .ub ∧ r'.2 = none ∧ Sub r'.1 r.1))


theorem Cells.after_append (X : Cells) (d1 d2 : List Access) :
    X.after (d1 ++ d2) = (X.after d1).after d2 := by
  funext l o
  simp [Cells.after, touched, List.any_append, Bool.and_assoc]

theorem Rel.status {X : Cells} {s s' : St} (h : Rel X s s') : s.status = s'.status := by
  have h1 := congrArg St.status h.1; exact h1
theorem Rel.live {X : Cells} {s s' : St} (h : Rel X s s') : s.live = s'.live := by
  have h1 := congrArg St.live h.1; exact h1
theorem Rel.alias {X : Cells} {s s' : St} (h : Rel X s s') : s.alias = s'.alias := by
  have h1 := congrArg St.alias h.1; exact h1
theorem Rel.trace {X : Cells} {s s' : St} (h : Rel X s s') : s.trace = s'.trace := by
  have h1 := congrArg St.trace h.1; exact h1
theorem Rel.conflicts {X : Cells} {s s' : St} (h : Rel X s s') : s.conflicts = s'.conflicts := by
  have h1 := congrArg St.conflicts h.1; exact h1
theorem Rel.tick {X : Cells} {s s' : St} (h : Rel X s s') : s.tick = s'.tick := by
  have h1 := congrArg (fun z : St => z.tick) h.1; exact h1
theorem Rel.inCall {X : Cells} {s s' : St} (h : Rel X s s') : s.inCall = s'.inCall := by
  have h1 := congrArg (fun z : St => z.inCall) h.1; exact h1

theorem rel_resolvePlace {X : Cells} {s s' : St} (h : Rel X s s') (P : Prog) (q : Place) :
    resolvePlace P s q = resolvePlace P s' q := by
  unfold resolvePlace; rw [h.alias, h.live]


theorem ft_of_noRead {l o : Nat} {d : List Access} (h : ∀ e ∈ d, e.kind ≠ .read) :
    ft l o d = true := by
  induction d with
  | nil => rfl
  | cons e d ih =>
    simp only [firstTouchNotRead, Bool.true_and]
    split
    · have := h e (List.mem_cons_self ..); simpa using this
    · exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem after_nil (X : Cells) : X.after [] = X := by
  funext l o; simp [Cells.after, touched]

theorem ok_nil (X : Cells) : OK X [] := fun _ _ _ => rfl

theorem ok_append {X : Cells} {d1 d2 : List Access} (h1 : OK X d1) (h2 : OK (X.after d1) d2) :
    OK X (d1 ++ d2) := by
  intro l o hx
  rw [ft_append]
  split
  · exact h1 l o hx
  · rename_i ht
    exact h2 l o (by simp [Cells.after, hx, ht])

theorem bad_append_left {X : Cells} {d1 : List Access} (h : Bad X d1) (d2 : List Access) :
    Bad X (d1 ++ d2) := by
  obtain ⟨l, o, hx, hf⟩ := h
  exact ⟨l, o, hx, by
    rw [ft_append, ite_eq_left (touched_of_ft_false hf)]; exact hf⟩

theorem bad_append_right {X : Cells} (d1 : List Access) {d2 : List Access}
    (h : Bad (X.after d1) d2) : Bad X (d1 ++ d2) := by
  obtain ⟨l, o, hx, hf⟩ := h
  simp only [Cells.after, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hx
  exact ⟨l, o, hx.1, by
    rw [ft_append, ite_eq_right (by simp [hx.2])]; exact hf⟩

/-! ## Helpers: the relation -/

theorem rel_intro {X : Cells} {s s' : St} (h1 : s.live = s'.live) (h2 : s.alias = s'.alias)
    (h3 : s.trace = s'.trace) (h4 : s.tick = s'.tick) (h5 : s.inCall = s'.inCall)
    (h6 : s.status = s'.status) (h7 : s.conflicts = s'.conflicts)
    (hm : ∀ l o, s'.mem l o = if X l o = true then .uninit else s.mem l o) : Rel X s s' := by
  refine ⟨?_, hm⟩
  cases s; cases s'
  simp_all [erase]

theorem Rel.mem {X : Cells} {s s' : St} (h : Rel X s s') (l o : Nat) :
    s'.mem l o = if X l o = true then .uninit else s.mem l o := h.2 l o

theorem Rel.fail {X : Cells} {s s' : St} (h : Rel X s s') (k : Status) :
    Rel X (s.fail k) (s'.fail k) :=
  ⟨by show (erase s).fail k = (erase s').fail k; rw [h.1], h.2⟩

theorem Rel.logAcc {X : Cells} {s s' : St} (h : Rel X s s') (l o : Nat) (k k' : AccKind) :
    Rel X (s.logAcc l o k) (s'.logAcc l o k') :=
  ⟨by show erase s = erase s'; exact h.1, h.2⟩

theorem Rel.emit {X : Cells} {s s' : St} (h : Rel X s s') (e : Event) :
    Rel X (s.emit e) (s'.emit e) :=
  ⟨by show (erase s).emit e = (erase s').emit e; rw [h.1], h.2⟩

theorem Rel.setInCall {X : Cells} {s s' : St} (h : Rel X s s') (c : Bool) :
    Rel X { s with inCall := c } { s' with inCall := c } :=
  ⟨by show { erase s with inCall := c } = { erase s' with inCall := c }; rw [h.1], h.2⟩

theorem Rel.setCtx {X : Cells} {s s' : St} (h : Rel X s s') (a : Option (Nat × Place)) (c : Bool) :
    Rel X { s with alias := a, inCall := c } { s' with alias := a, inCall := c } :=
  ⟨by show { erase s with alias := a, inCall := c } = { erase s' with alias := a, inCall := c }
      rw [h.1], h.2⟩

theorem Rel.setTick {X : Cells} {s s' : St} (h : Rel X s s') (n : Nat) :
    Rel X { s with tick := n } { s' with tick := n } :=
  ⟨by show { erase s with tick := n } = { erase s' with tick := n }; rw [h.1], h.2⟩

/-! ## Helpers: growth of logs and recorded pairs -/

/-- `u` extends the log of `t` and keeps its recorded pairs. -/
def Grow (t u : St) : Prop := (∃ d, u.log = t.log ++ d) ∧ ∀ c ∈ t.conflicts, c ∈ u.conflicts

theorem Grow.refl (t : St) : Grow t t := ⟨⟨[], by simp⟩, fun _ h => h⟩

theorem Grow.trans {s t u : St} (h1 : Grow s t) (h2 : Grow t u) : Grow s u := by
  obtain ⟨⟨d1, e1⟩, c1⟩ := h1
  obtain ⟨⟨d2, e2⟩, c2⟩ := h2
  exact ⟨⟨d1 ++ d2, by rw [e2, e1, List.append_assoc]⟩, fun c hc => c2 c (c1 c hc)⟩

theorem grow_of_step {s t : St} (h : Step s t) : Grow s t := by
  obtain ⟨d, hd, -⟩ := h.log
  obtain ⟨e, he, -⟩ := h.conf
  exact ⟨⟨d, hd⟩, fun c hc => by rw [he]; exact List.mem_append_left _ hc⟩

theorem grow_of_stepT {s t : St} (h : StepT s t) : Grow s t := by
  obtain ⟨d, hd, -⟩ := h.log
  obtain ⟨e, he, -⟩ := h.conf
  exact ⟨⟨d, hd⟩, fun c hc => by rw [he]; exact List.mem_append_left _ hc⟩

theorem grow_setInCall (s : St) (c : Bool) : Grow s { s with inCall := c } :=
  ⟨⟨[], by simp⟩, fun _ h => h⟩

theorem grow_setCtx (s : St) (a : Option (Nat × Place)) (c : Bool) :
    Grow s { s with alias := a, inCall := c } :=
  ⟨⟨[], by simp⟩, fun _ h => h⟩

/-! ## Helpers: composing simulations -/

theorem simS_refl {X : Cells} {s s' : St} (h : Rel X s s') : SimS X s s s' :=
  ⟨[], by simp, Or.inl ⟨ok_nil X, by rw [after_nil]; exact h⟩⟩

theorem simV_refl {X : Cells} {s s' : St} (h : Rel X s s') (a : Option (List Val)) :
    SimV X s (s, a) (s', a) :=
  ⟨[], by simp, Or.inl ⟨ok_nil X, by rw [after_nil]; exact h, rfl⟩⟩

theorem simS_of_ok {X : Cells} {s t t' : St} {d : List Access} (hl : t.log = s.log ++ d)
    (hok : OK X d) (h : Rel (X.after d) t t') : SimS X s t t' := ⟨d, hl, Or.inl ⟨hok, h⟩⟩

theorem SimS.start {X : Cells} {s s1 t t' : St} (hl : s1.log = s.log) (h : SimS X s1 t t') :
    SimS X s t t' := by
  obtain ⟨d, hd, h⟩ := h; exact ⟨d, by rw [hd, hl], h⟩

theorem SimS.extend {X : Cells} {s t u u' : St} {d1 : List Access} (hl : t.log = s.log ++ d1)
    (hok : OK X d1) (h : SimS (X.after d1) t u u') : SimS X s u u' := by
  obtain ⟨d2, hl2, (⟨hok2, hr⟩ | ⟨hb, hs, hsub⟩)⟩ := h
  · refine ⟨d1 ++ d2, by rw [hl2, hl, List.append_assoc], Or.inl ⟨ok_append hok hok2, ?_⟩⟩
    rw [Cells.after_append]; exact hr
  · exact ⟨d1 ++ d2, by rw [hl2, hl, List.append_assoc], Or.inr ⟨bad_append_right d1 hb, hs, hsub⟩⟩

theorem SimV.extend {X : Cells} {s t : St} {r r' : St × Option (List Val)} {d1 : List Access}
    (hl : t.log = s.log ++ d1) (hok : OK X d1) (h : SimV (X.after d1) t r r') : SimV X s r r' := by
  obtain ⟨d2, hl2, (⟨hok2, hr, he⟩ | ⟨hb, hs, hn, hsub⟩)⟩ := h
  · refine ⟨d1 ++ d2, by rw [hl2, hl, List.append_assoc], Or.inl ⟨ok_append hok hok2, ?_, he⟩⟩
    rw [Cells.after_append]; exact hr
  · exact ⟨d1 ++ d2, by rw [hl2, hl, List.append_assoc],
      Or.inr ⟨bad_append_right d1 hb, hs, hn, hsub⟩⟩

theorem SimV.bindS {X : Cells} {s t t' : St} {a a' : Option (List Val)}
    (h : SimV X s (t, a) (t', a')) {u u' : St} (hgood : ∀ Y, Rel Y t t' → a = a' → SimS Y t u u')
    (hbad : a' = none → u' = t') (hg : Grow t u) : SimS X s u u' := by
  obtain ⟨d, hl, (⟨hok, hr, he⟩ | ⟨hb, hs, hn, hsub⟩)⟩ := h
  · exact SimS.extend hl hok (hgood _ hr he)
  · obtain ⟨⟨d2, hd2⟩, hc⟩ := hg
    dsimp only at hl hs hn hsub
    rw [hbad hn]
    exact ⟨d ++ d2, by rw [hd2, hl, List.append_assoc],
      Or.inr ⟨bad_append_left hb d2, hs, fun c hc' => hc c (hsub c hc')⟩⟩

theorem SimV.bindV {X : Cells} {s t t' : St} {a a' : Option (List Val)}
    (h : SimV X s (t, a) (t', a')) {r r' : St × Option (List Val)}
    (hgood : ∀ Y, Rel Y t t' → a = a' → SimV Y t r r')
    (hbad : a' = none → r' = (t', none)) (hg : Grow t r.1) : SimV X s r r' := by
  obtain ⟨d, hl, (⟨hok, hr, he⟩ | ⟨hb, hs, hn, hsub⟩)⟩ := h
  · exact SimV.extend hl hok (hgood _ hr he)
  · obtain ⟨⟨d2, hd2⟩, hc⟩ := hg
    dsimp only at hl hs hn hsub
    rw [hbad hn]
    exact ⟨d ++ d2, by rw [hd2, hl, List.append_assoc],
      Or.inr ⟨bad_append_left hb d2, hs, rfl, fun c hc' => hc c (hsub c hc')⟩⟩

theorem SimS.bind {X : Cells} {s t t' u u' : St} (h : SimS X s t t')
    (hgood : ∀ Y, Rel Y t t' → SimS Y t u u')
    (hbad : t'.status = .ub → u'.status = .ub ∧ ∀ c ∈ u'.conflicts, c ∈ t'.conflicts)
    (hg : Grow t u) : SimS X s u u' := by
  obtain ⟨d, hl, (⟨hok, hr⟩ | ⟨hb, hs, hsub⟩)⟩ := h
  · exact SimS.extend hl hok (hgood _ hr)
  · obtain ⟨⟨d2, hd2⟩, hc⟩ := hg
    obtain ⟨hs', hc'⟩ := hbad hs
    exact ⟨d ++ d2, by rw [hd2, hl, List.append_assoc],
      Or.inr ⟨bad_append_left hb d2, hs', fun c h1 => hc c (hsub c (hc' c h1))⟩⟩

theorem SimV.map {X : Cells} {s t t' : St} {a a' : Option (List Val)} (f : List Val → List Val)
    (h : SimV X s (t, a) (t', a')) : SimV X s (t, a.map f) (t', a'.map f) := by
  obtain ⟨d, hl, (⟨hok, hr, he⟩ | ⟨hb, hs, hn, hsub⟩)⟩ := h
  · exact ⟨d, hl, Or.inl ⟨hok, hr, by dsimp only at he ⊢; rw [he]⟩⟩
  · dsimp only at hn
    exact ⟨d, hl, Or.inr ⟨hb, hs, by dsimp only; rw [hn]; rfl, hsub⟩⟩

theorem simS_same {X : Cells} {s t t' : St} (hl : t.log = s.log) (h : Rel X t t') :
    SimS X s t t' :=
  ⟨[], by simp [hl], Or.inl ⟨ok_nil X, by rw [after_nil]; exact h⟩⟩

theorem simV_same {X : Cells} {s t t' : St} (hl : t.log = s.log) (h : Rel X t t')
    (a : Option (List Val)) : SimV X s (t, a) (t', a) :=
  ⟨[], by simp [hl], Or.inl ⟨ok_nil X, by rw [after_nil]; exact h, rfl⟩⟩

/-! ## Helpers: logs that avoid `X` -/

theorem touched_iff {d : List Access} {l o : Nat} :
    touched d l o = true ↔ ∃ e ∈ d, e.loc = l ∧ e.off = o := by
  simp [touched]

theorem not_touched_of_nonX {X : Cells} {d : List Access} (h : ∀ e ∈ d, X e.loc e.off = false)
    {l o : Nat} (hx : X l o = true) : touched d l o = false := by
  cases ht : touched d l o
  · rfl
  · obtain ⟨e, he, rfl, rfl⟩ := touched_iff.1 ht
    rw [h e he] at hx; cases hx

theorem ok_of_nonX {X : Cells} {d : List Access} (h : ∀ e ∈ d, X e.loc e.off = false) : OK X d :=
  fun _ _ hx => ft_of_not_touched (not_touched_of_nonX h hx)

theorem after_of_nonX {X : Cells} {d : List Access} (h : ∀ e ∈ d, X e.loc e.off = false) :
    X.after d = X := by
  funext l o
  cases hx : X l o
  · simp [Cells.after, hx]
  · simp [Cells.after, hx, not_touched_of_nonX h hx]

theorem ft_reads_false {t : Nat} {c : Bool} {loc off m : Nat} (hm : 0 < m) :
    ft loc off ((List.range m).map fun i => (⟨t, c, loc, off + i, .read⟩ : Access)) = false := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ_eq_map]
  simp [firstTouchNotRead]

theorem touched_writes {t : Nat} {c : Bool} {loc off n : Nat} {k : AccKind} (l o : Nat) :
    touched ((List.range n).map fun i => (⟨t, c, loc, off + i, k⟩ : Access)) l o =
      decide (l = loc ∧ off ≤ o ∧ o < off + n) := by
  apply Bool.eq_iff_iff.2
  simp only [touched_iff, List.mem_map, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨i, hi, rfl⟩, rfl, rfl⟩; dsimp only; exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨_, ⟨o - off, by omega, rfl⟩, rfl, by show off + (o - off) = o; omega⟩

/-! ## Operations -/

theorem sim_readCells {X : Cells} {s s' : St} (h : Rel X s s') (loc off n : Nat) :
    SimV X s (readCells s loc off n) (readCells s' loc off n) := by
  induction n generalizing s s' off with
  | zero => exact simV_refl h _
  | succ n ih =>
    by_cases hX : X loc off = true
    · have hv' : s'.mem loc off = .uninit := by rw [h.mem]; simp [hX]
      obtain ⟨-, -, m, hm, hlog, -, h5, h6⟩ := readCells_spec s loc off (n + 1)
      have hm0 : 0 < m := by
        by_cases hall : ∀ i, i < n + 1 → s.mem loc (off + i) ≠ .uninit
        · rw [h5 hall]; omega
        · exact (h6 hall).1
      obtain ⟨h1', h2', -⟩ := readCells_spec s' loc off (n + 1)
      have hn' : ¬ ∀ i, i < n + 1 → s'.mem loc (off + i) ≠ .uninit :=
        fun hall => hall 0 (by omega) (by simpa using hv')
      simp only [hn', ↓reduceIte] at h1' h2'
      have hc' : (readCells s' loc off (n + 1)).1.conflicts = s'.conflicts := by
        have e := congrArg St.conflicts (readCells_frame s' loc off (n + 1)); exact e
      refine ⟨_, hlog, Or.inr ⟨⟨loc, off, hX, ft_reads_false hm0⟩, h2', h1', ?_⟩⟩
      intro c hc
      rw [hc', ← h.conflicts] at hc
      exact (grow_of_step (step_readCells s loc off (n + 1))).2 c hc
    · have hX' : X loc off = false := by simpa using hX
      have hv : s'.mem loc off = s.mem loc off := by rw [h.mem]; simp [hX']
      have hnx : ∀ e ∈ [(⟨s.tick, s.inCall, loc, off, .read⟩ : Access)], X e.loc e.off = false := by
        simp [hX']
      simp only [readCells]
      rw [hv]
      by_cases hu : s.mem loc off = .uninit
      · simp only [hu, ↓reduceIte]
        refine ⟨[⟨s.tick, s.inCall, loc, off, .read⟩], rfl, Or.inl ⟨ok_of_nonX hnx, ?_, rfl⟩⟩
        rw [after_of_nonX hnx]; exact (h.logAcc _ _ _ _).fail _
      · simp only [hu, ↓reduceIte]
        have ih' := ih (h.logAcc loc off .read .read) (off + 1)
        rcases hr : readCells (s.logAcc loc off .read) loc (off + 1) n with ⟨t, a⟩
        rcases hr' : readCells (s'.logAcc loc off .read) loc (off + 1) n with ⟨t', a'⟩
        rw [hr, hr'] at ih'
        rw [← after_of_nonX hnx] at ih'
        have h2 := SimV.map (s.mem loc off :: ·) (SimV.extend (rfl : (s.logAcc loc off .read).log =
          s.log ++ [⟨s.tick, s.inCall, loc, off, .read⟩]) (ok_of_nonX hnx) ih')
        cases a <;> cases a' <;> exact h2

theorem sim_writeCellsK {X : Cells} {s s' : St} (h : Rel X s s') (k : AccKind) (hk : k ≠ .read)
    (loc off : Nat) (vs : List Val) :
    ∃ d, (writeCellsK k s loc off vs).log = s.log ++ d ∧ OK X d ∧
      Rel (X.after d) (writeCellsK k s loc off vs) (writeCellsK k s' loc off vs) := by
  rw [writeCellsK_eq, writeCellsK_eq]
  refine ⟨_, rfl, fun l o _ => ft_of_noRead ?_, ?_⟩
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    exact hk
  · refine ⟨by show erase s = erase s'; exact h.1, ?_⟩
    intro l o
    simp only [Cells.after, touched_writes]
    by_cases hin : l = loc ∧ off ≤ o ∧ o < off + vs.length
    · simp [hin]
    · simp [hin, h.mem]

theorem sim_evalOp {X : Cells} {s s' : St} (h : Rel X s s') (ms : MoveSem) (P : Prog)
    (o : Operand) : SimV X s (evalOp ms P s o) (evalOp ms P s' o) := by
  cases o with
  | lit n => exact simV_refl h _
  | addrOf q =>
    simp only [evalOp]; rw [rel_resolvePlace h]
    split
    · exact simV_refl h _
    · exact simV_same rfl (h.fail _) _
  | copy q =>
    simp only [evalOp]; rw [rel_resolvePlace h]
    split
    · exact sim_readCells h _ _ _
    · exact simV_same rfl (h.fail _) _
  | move q =>
    simp only [evalOp]; rw [rel_resolvePlace h]
    split
    · rename_i r _
      have h1 := sim_readCells h r.base r.off r.len
      rcases hr : readCells s r.base r.off r.len with ⟨t, a⟩
      rcases hr' : readCells s' r.base r.off r.len with ⟨t', a'⟩
      rw [hr, hr'] at h1
      refine SimV.bindV h1 ?_ ?_ ?_
      · intro Y hY he; subst he
        cases a with
        | none => exact simV_refl hY _
        | some vs =>
          dsimp only
          split
          · obtain ⟨d, hl, hok, hr2⟩ := sim_writeCellsK hY .write (by decide) r.base r.off
              (List.replicate r.len .uninit)
            exact ⟨d, hl, Or.inl ⟨hok, hr2, rfl⟩⟩
          · exact simV_refl hY _
      · intro hn; subst hn; rfl
      · cases a with
        | none => exact Grow.refl _
        | some vs =>
          dsimp only
          split
          · exact grow_of_step (step_writeCells _ _ _ _)
          · exact Grow.refl _
    · exact simV_same rfl (h.fail _) _
  | load p len =>
    simp only [evalOp]; rw [rel_resolvePlace h]
    split
    · rename_i r _
      split
      · have h1 := sim_readCells h r.base r.off 1
        rcases hr : readCells s r.base r.off 1 with ⟨t, a⟩
        rcases hr' : readCells s' r.base r.off 1 with ⟨t', a'⟩
        rw [hr, hr'] at h1
        refine SimV.bindV h1 ?_ ?_ ?_
        · intro Y hY he; subst he
          rcases a with _ | _ | ⟨v, _ | ⟨w, rest⟩⟩
          · exact simV_refl hY _
          · exact simV_same rfl (hY.fail _) _
          · cases v with
            | ptr l o =>
              dsimp only
              rw [← hY.live]
              split
              · exact sim_readCells hY _ _ _
              · exact simV_same rfl (hY.fail _) _
            | _ => exact simV_same rfl (hY.fail _) _
          · cases v <;> exact simV_same rfl (hY.fail _) _
        · intro hn; subst hn; rfl
        · rcases a with _ | _ | ⟨v, _ | ⟨w, rest⟩⟩
          · exact Grow.refl _
          · exact grow_of_step (step_fail _ _)
          · cases v with
            | ptr l o =>
              dsimp only
              split
              · exact grow_of_step (step_readCells _ _ _ _)
              · exact grow_of_step (step_fail _ _)
            | _ => exact grow_of_step (step_fail _ _)
          · cases v <;> exact grow_of_step (step_fail _ _)
      · exact simV_same rfl (h.fail _) _
    · exact simV_same rfl (h.fail _) _

theorem sim_evalOps {X : Cells} {s s' : St} (h : Rel X s s') (ms : MoveSem) (P : Prog)
    (os : List Operand) : SimV X s (evalOps ms P s os) (evalOps ms P s' os) := by
  induction os generalizing X s s' with
  | nil => exact simV_refl h _
  | cons o os ih =>
    simp only [evalOps]
    have h1 := sim_evalOp h ms P o
    rcases hr : evalOp ms P s o with ⟨t, a⟩
    rcases hr' : evalOp ms P s' o with ⟨t', a'⟩
    rw [hr, hr'] at h1
    refine SimV.bindV h1 ?_ ?_ ?_
    · intro Y hY he; subst he
      cases a with
      | none => exact simV_refl hY _
      | some vs =>
        dsimp only
        have h2 := ih hY
        rcases hr2 : evalOps ms P t os with ⟨u, b⟩
        rcases hr2' : evalOps ms P t' os with ⟨u', b'⟩
        rw [hr2, hr2'] at h2
        have h3 := SimV.map (vs ++ ·) h2
        cases b <;> cases b' <;> exact h3
    · intro hn; subst hn; rfl
    · cases a with
      | none => exact Grow.refl _
      | some vs =>
        dsimp only
        have g := grow_of_step (step_evalOps ms P t os)
        rcases hr2 : evalOps ms P t os with ⟨u, b⟩
        rw [hr2] at g
        cases b <;> exact g

theorem sim_writeInOrder {X : Cells} {s s' : St} (h : Rel X s s') (ms : MoveSem) (P : Prog)
    (loc off : Nat) (os : List Operand) :
    SimS X s (writeInOrder ms P s loc off os) (writeInOrder ms P s' loc off os) := by
  induction os generalizing X s s' off with
  | nil => exact simS_refl h
  | cons o os ih =>
    simp only [writeInOrder]
    have h1 := sim_evalOp h ms P o
    rcases hr : evalOp ms P s o with ⟨t, a⟩
    rcases hr' : evalOp ms P s' o with ⟨t', a'⟩
    rw [hr, hr'] at h1
    refine SimV.bindS h1 ?_ ?_ ?_
    · intro Y hY he; subst he
      cases a with
      | none => exact simS_refl hY
      | some vs =>
        dsimp only
        obtain ⟨d, hl, hok, hr2⟩ := sim_writeCellsK hY .write (by decide) loc off vs
        exact SimS.extend hl hok (ih hr2 _)
    · intro hn; subst hn; rfl
    · cases a with
      | none => exact Grow.refl _
      | some vs =>
        dsimp only
        exact (grow_of_step (step_writeCells _ _ _ _)).trans
          (grow_of_step (step_writeInOrder _ _ _ _ _ _))

theorem sim_allocate {X : Cells} {s s' : St} (h : Rel X s s') (P : Prog) (x : Nat) :
    ∃ d, (allocate P s x).log = s.log ++ d ∧ OK X d ∧
      Rel (X.after d) (allocate P s x) (allocate P s' x) := by
  have hlo : liveOthers P s x = liveOthers P s' x := by unfold liveOthers; rw [h.live]
  unfold allocate
  split
  · refine sim_writeCellsK ?_ .reset (by decide) x 0 _
    refine rel_intro ?_ h.alias h.trace h.tick h.inCall h.status ?_ h.mem
    · simp only [h.live]
    · simp only [h.conflicts, hlo]
  · exact ⟨[], by simp [St.fail], ok_nil X, by rw [after_nil]; exact h.fail _⟩

theorem sim_deallocate {X : Cells} {s s' : St} (h : Rel X s s') (P : Prog) (x : Nat) :
    ∃ d, (deallocate P s x).log = s.log ++ d ∧ OK X d ∧
      Rel (X.after d) (deallocate P s x) (deallocate P s' x) := by
  have hx' : s'.live x = s.live x := (congrFun h.live x).symm
  by_cases hx : s.live x = true
  · obtain ⟨d, hl, hok, hr⟩ := sim_writeCellsK h .reset (by decide) x 0
      (List.replicate (P.size x) .uninit)
    simp only [deallocate, hx, hx', resetCells, ↓reduceIte]
    refine ⟨d, hl, hok, rel_intro ?_ hr.alias hr.trace hr.tick hr.inCall hr.status hr.conflicts
      hr.mem⟩
    simp only [hr.live]
  · simp only [deallocate, hx, hx', Bool.false_eq_true, ↓reduceIte]
    exact ⟨[], by simp, ok_nil X, by rw [after_nil]; exact h⟩

theorem sim_cmpOp {X : Cells} {s s' : St} (h : Rel X s s') (ms : MoveSem) (P : Prog) (A : Layout)
    (a b : Operand) (f : Nat → Nat → Bool) :
    SimS X s (cmpOp ms P A s a b f) (cmpOp ms P A s' a b f) := by
  unfold cmpOp
  have h1 := sim_evalOp h ms P a
  rcases hr : evalOp ms P s a with ⟨t, x⟩
  rcases hr' : evalOp ms P s' a with ⟨t', x'⟩
  rw [hr, hr'] at h1
  refine SimV.bindS h1 ?_ ?_ ?_
  · intro Y hY he; subst he
    rcases x with _ | _ | ⟨va, _ | ⟨w, rest⟩⟩
    · exact simS_refl hY
    · exact simS_same rfl (hY.fail _)
    · dsimp only
      have h2 := sim_evalOp hY ms P b
      rcases hr2 : evalOp ms P t b with ⟨u, y⟩
      rcases hr2' : evalOp ms P t' b with ⟨u', y'⟩
      rw [hr2, hr2'] at h2
      refine SimV.bindS h2 ?_ ?_ ?_
      · intro Z hZ he2; subst he2
        rcases y with _ | _ | ⟨vb, _ | ⟨w2, rest2⟩⟩
        · exact simS_refl hZ
        · exact simS_same rfl (hZ.fail _)
        · dsimp only
          split
          · exact simS_same rfl (hZ.emit _)
          · exact simS_same rfl (hZ.fail _)
        · exact simS_same rfl (hZ.fail _)
      · intro hn; subst hn; rfl
      · rcases y with _ | _ | ⟨vb, _ | ⟨w2, rest2⟩⟩
        · exact Grow.refl _
        · exact grow_of_step (step_fail _ _)
        · dsimp only
          split
          · exact grow_of_step (step_emit _ _)
          · exact grow_of_step (step_fail _ _)
        · exact grow_of_step (step_fail _ _)
    · exact simS_same rfl (hY.fail _)
  · intro hn; subst hn; rfl
  · rcases x with _ | _ | ⟨va, _ | ⟨w, rest⟩⟩
    · exact Grow.refl _
    · exact grow_of_step (step_fail _ _)
    · dsimp only
      have g := grow_of_step (step_evalOp ms P t b)
      rcases hr2 : evalOp ms P t b with ⟨u, y⟩
      rw [hr2] at g
      rcases y with _ | _ | ⟨vb, _ | ⟨w2, rest2⟩⟩
      · exact g
      · exact g.trans (grow_of_step (step_fail _ _))
      · dsimp only
        split
        · exact g.trans (grow_of_step (step_emit _ _))
        · exact g.trans (grow_of_step (step_fail _ _))
      · exact g.trans (grow_of_step (step_fail _ _))
    · exact grow_of_step (step_fail _ _)

theorem deallocate_status (P : Prog) (s : St) (x : Nat) : (deallocate P s x).status = s.status := by
  unfold deallocate; split <;> simp [resetCells, writeCellsK_eq]

theorem deallocate_conflicts (P : Prog) (s : St) (x : Nat) :
    (deallocate P s x).conflicts = s.conflicts := by
  unfold deallocate; split <;> simp [resetCells, writeCellsK_eq]

theorem grow_callBody (sem : Sem) (P : Prog) (A : Layout) (t : St) (c : Callee) (vs : List Val) :
    Grow t (deallocate P { execCallee sem P A { writeCells (allocate P t c.prm) c.prm 0 vs with
      inCall := true } c.body with inCall := false } c.prm) :=
  (grow_of_step (step_allocate _ _ _)).trans ((grow_of_step (step_writeCells _ _ _ _)).trans
    ((grow_setInCall _ _).trans ((grow_of_step (step_execCallee _ _ _ _ _)).trans
      ((grow_setInCall _ _).trans (grow_of_step (step_deallocate _ _ _))))))

theorem grow_execStmt (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt) :
    Grow s (execStmt sem P A s st) := by
  unfold execStmt
  split
  · exact Grow.refl s
  · cases st with
    | call fn arg =>
      dsimp only
      split
      · split
        · exact grow_of_step (step_fail _ _)
        · split
          · exact grow_of_step (step_fail _ _)
          · exact (grow_setCtx _ _ _).trans ((grow_of_step (step_execCallee _ _ _ _ _)).trans
              (grow_setCtx _ _ _))
      · rename_i arg _ _ _
        have g := grow_of_step (step_evalOp sem.move P s arg)
        rcases hr : evalOp sem.move P s arg with ⟨t, a⟩
        rw [hr] at g
        cases a with
        | none => exact g
        | some vs =>
          dsimp only
          split
          · exact g.trans (grow_of_step (step_fail _ _))
          · exact g.trans (grow_callBody _ _ _ _ _ _)
    | _ => exact grow_of_step (step_execBasic _ _ _ _ _)

theorem sim_execBasic {X : Cells} {s s' : St} (h : Rel X s s') (sem : Sem) (P : Prog) (A : Layout)
    (st : Stmt) : SimS X s (execBasic sem P A s st) (execBasic sem P A s' st) := by
  have hs : s'.status = s.status := h.status.symm
  by_cases hrun : s.status ≠ .running
  · rw [execBasic_of_not_running st hrun, execBasic_of_not_running st (by rw [hs]; exact hrun)]
    exact simS_refl h
  · have hrun' : ¬ s'.status ≠ .running := by rw [hs]; exact hrun
    unfold execBasic
    rw [ite_eq_right hrun, ite_eq_right hrun']
    have hc : s'.inCall = s.inCall := h.inCall.symm
    cases st with
    | storageLive x =>
      dsimp only
      rw [hc]
      split
      · exact simS_same rfl (h.fail _)
      · obtain ⟨d, hl, hok, hr⟩ := sim_allocate h P x
        exact simS_of_ok hl hok hr
    | storageDead x =>
      dsimp only
      rw [hc]
      split
      · exact simS_same rfl (h.fail _)
      · obtain ⟨d, hl, hok, hr⟩ := sim_deallocate h P x
        exact simS_of_ok hl hok hr
    | assign lhs rhs =>
      dsimp only
      split
      · exact simS_same rfl (h.fail _)
      · rw [rel_resolvePlace h]
        split
        · exact simS_same rfl (h.fail _)
        · rename_i r _
          split
          · have h1 := sim_evalOps h sem.move P rhs
            rcases hr : evalOps sem.move P s rhs with ⟨t, a⟩
            rcases hr' : evalOps sem.move P s' rhs with ⟨t', a'⟩
            rw [hr, hr'] at h1
            refine SimV.bindS h1 ?_ ?_ ?_
            · intro Y hY he; subst he
              cases a with
              | none => exact simS_refl hY
              | some vs =>
                dsimp only
                obtain ⟨d, hl, hok, hr2⟩ := sim_writeCellsK hY .write (by decide) r.base r.off vs
                exact simS_of_ok hl hok hr2
            · intro hn; subst hn; rfl
            · cases a with
              | none => exact Grow.refl _
              | some vs => exact grow_of_step (step_writeCells _ _ _ _)
          · exact sim_writeInOrder h _ _ _ _ _
    | store p v =>
      dsimp only
      rw [rel_resolvePlace h]
      split
      · rename_i r _
        split
        · have h1 := sim_readCells h r.base r.off 1
          rcases hr : readCells s r.base r.off 1 with ⟨t, a⟩
          rcases hr' : readCells s' r.base r.off 1 with ⟨t', a'⟩
          rw [hr, hr'] at h1
          refine SimV.bindS h1 ?_ ?_ ?_
          · intro Y hY he; subst he
            rcases a with _ | _ | ⟨v0, _ | ⟨w, rest⟩⟩
            · exact simS_refl hY
            · exact simS_same rfl (hY.fail _)
            · cases v0 with
              | ptr l o =>
                dsimp only
                have h2 := sim_evalOp hY sem.move P v
                rcases hr2 : evalOp sem.move P t v with ⟨u, b⟩
                rcases hr2' : evalOp sem.move P t' v with ⟨u', b'⟩
                rw [hr2, hr2'] at h2
                refine SimV.bindS h2 ?_ ?_ ?_
                · intro Z hZ he2; subst he2
                  cases b with
                  | none => exact simS_refl hZ
                  | some vs =>
                    dsimp only
                    rw [← hZ.live]
                    split
                    · obtain ⟨d, hl, hok, hr3⟩ := sim_writeCellsK hZ .write (by decide) l o vs
                      exact simS_of_ok hl hok hr3
                    · exact simS_same rfl (hZ.fail _)
                · intro hn; subst hn; rfl
                · cases b with
                  | none => exact Grow.refl _
                  | some vs =>
                    dsimp only
                    split
                    · exact grow_of_step (step_writeCells _ _ _ _)
                    · exact grow_of_step (step_fail _ _)
              | _ => exact simS_same rfl (hY.fail _)
            · cases v0 <;> exact simS_same rfl (hY.fail _)
          · intro hn; subst hn; rfl
          · rcases a with _ | _ | ⟨v0, _ | ⟨w, rest⟩⟩
            · exact Grow.refl _
            · exact grow_of_step (step_fail _ _)
            · cases v0 with
              | ptr l o =>
                dsimp only
                have g := grow_of_step (step_evalOp sem.move P t v)
                rcases hr2 : evalOp sem.move P t v with ⟨u, b⟩
                rw [hr2] at g
                cases b with
                | none => exact g
                | some vs =>
                  dsimp only
                  split
                  · exact g.trans (grow_of_step (step_writeCells _ _ _ _))
                  · exact g.trans (grow_of_step (step_fail _ _))
              | _ => exact grow_of_step (step_fail _ _)
            · cases v0 <;> exact grow_of_step (step_fail _ _)
        · exact simS_same rfl (h.fail _)
      · exact simS_same rfl (h.fail _)
    | ptrEq a b => exact sim_cmpOp h _ _ _ _ _ _
    | ptrInRange a b n => exact sim_cmpOp h _ _ _ _ _ _
    | out o =>
      dsimp only
      have h1 := sim_evalOp h sem.move P o
      rcases hr : evalOp sem.move P s o with ⟨t, a⟩
      rcases hr' : evalOp sem.move P s' o with ⟨t', a'⟩
      rw [hr, hr'] at h1
      refine SimV.bindS h1 ?_ ?_ ?_
      · intro Y hY he; subst he
        cases a with
        | none => exact simS_refl hY
        | some vs => exact simS_same rfl (hY.emit _)
      · intro hn; subst hn; rfl
      · cases a with
        | none => exact Grow.refl _
        | some vs => exact grow_of_step (step_emit _ _)
    | call fn a => exact simS_same rfl (h.fail _)
    | nop => exact simS_refl h

theorem sim_execCallee {X : Cells} {s s' : St} (h : Rel X s s') (sem : Sem) (P : Prog)
    (A : Layout) (b : List Stmt) :
    SimS X s (execCallee sem P A s b) (execCallee sem P A s' b) := by
  induction b generalizing X s s' with
  | nil => exact simS_refl h
  | cons st b ih =>
    show SimS X s (execCallee sem P A (execBasic sem P A s st) b)
      (execCallee sem P A (execBasic sem P A s' st) b)
    refine SimS.bind (sim_execBasic h sem P A st) (fun Y hY => ih hY) (fun hu => ?_)
      (grow_of_step (step_execCallee _ _ _ _ _))
    rw [execCallee_of_not_running b (by rw [hu]; decide)]
    exact ⟨hu, fun c hc => hc⟩

theorem sim_execStmt {X : Cells} {s s' : St} (h : Rel X s s') (sem : Sem) (P : Prog) (A : Layout)
    (st : Stmt) : SimS X s (execStmt sem P A s st) (execStmt sem P A s' st) := by
  have hs : s'.status = s.status := h.status.symm
  by_cases hrun : s.status ≠ .running
  · rw [execStmt_of_not_running st hrun, execStmt_of_not_running st (by rw [hs]; exact hrun)]
    exact simS_refl h
  · have hrun' : ¬ s'.status ≠ .running := by rw [hs]; exact hrun
    unfold execStmt
    rw [ite_eq_right hrun, ite_eq_right hrun']
    cases st with
    | call fn arg =>
      dsimp only
      split
      · rw [rel_resolvePlace h]
        split
        · exact simS_same rfl (h.fail _)
        · rename_i r _
          split
          · exact simS_same rfl (h.fail _)
          · have h1 := sim_execCallee (h.setCtx (some ((P.fn fn).prm, r)) true) sem P A
              (P.fn fn).body
            refine SimS.start rfl (SimS.bind h1 (fun Y hY => ?_) (fun hu => ⟨hu, fun c hc => hc⟩)
              (grow_setCtx _ _ _))
            exact simS_same rfl (hY.setCtx _ _)
      · rename_i arg _ _ _
        have h1 := sim_evalOp h sem.move P arg
        rcases hr : evalOp sem.move P s arg with ⟨t, a⟩
        rcases hr' : evalOp sem.move P s' arg with ⟨t', a'⟩
        rw [hr, hr'] at h1
        refine SimV.bindS h1 ?_ ?_ ?_
        · intro Y hY he; subst he
          cases a with
          | none => exact simS_refl hY
          | some vs =>
            dsimp only
            rw [← hY.live]
            split
            · exact simS_same rfl (hY.fail _)
            · obtain ⟨d1, hl1, hok1, hr1⟩ := sim_allocate hY P (P.fn fn).prm
              refine SimS.extend hl1 hok1 ?_
              obtain ⟨d2, hl2, hok2, hr2⟩ := sim_writeCellsK hr1 .write (by decide) (P.fn fn).prm 0 vs
              refine SimS.extend hl2 hok2 ?_
              have h3 := sim_execCallee (hr2.setInCall true) sem P A (P.fn fn).body
              refine SimS.start rfl (SimS.bind h3 (fun Z hZ => ?_) (fun hu => ?_) ?_)
              · obtain ⟨d3, hl3, hok3, hr3⟩ := sim_deallocate (hZ.setInCall false) P (P.fn fn).prm
                exact simS_of_ok hl3 hok3 hr3
              · rw [deallocate_status, deallocate_conflicts]
                exact ⟨hu, fun c hc => hc⟩
              · exact (grow_setInCall _ _).trans (grow_of_step (step_deallocate _ _ _))
        · intro hn; subst hn; rfl
        · cases a with
          | none => exact Grow.refl _
          | some vs =>
            dsimp only
            split
            · exact grow_of_step (step_fail _ _)
            · exact grow_callBody _ _ _ _ _ _
    | _ => exact sim_execBasic h sem P A _

theorem sim_execTop {X : Cells} {s s' : St} (h : Rel X s s') (sem : Sem) (P : Prog) (A : Layout)
    (st : Stmt) : SimS X s (execTop sem P A s st) (execTop sem P A s' st) := by
  show SimS X s { execStmt sem P A s st with tick := (execStmt sem P A s st).tick + 1 }
    { execStmt sem P A s' st with tick := (execStmt sem P A s' st).tick + 1 }
  refine SimS.bind (sim_execStmt h sem P A st) (fun Y hY => ?_) (fun hu => ⟨hu, fun c hc => hc⟩)
    ⟨⟨[], by simp⟩, fun c hc => hc⟩
  rw [← hY.tick]
  exact simS_same rfl (hY.setTick _)

/-- Once the target has failed, further top-level steps keep it failed with recorded pairs among
the source's. -/
theorem fail_execTop {t t' : St} (ht : t'.status = .ub) (hs : Sub t' t) (sem : Sem) (P : Prog)
    (A : Layout) (st : Stmt) :
    (execTop sem P A t' st).status = .ub ∧ Sub (execTop sem P A t' st) (execTop sem P A t st) := by
  have hne : t'.status ≠ .running := by rw [ht]; decide
  have e1 : execTop sem P A t' st = { t' with tick := t'.tick + 1 } := by
    simp only [execTop, execStmt_of_not_running st hne]
  rw [e1]
  exact ⟨ht, fun c hc => (grow_execStmt sem P A t st).2 c (hs c hc)⟩

/-! ## Which cells an operation may access -/

/-- Local `l` may be read by operand `o` under the alias `al`, when pointers have provenance in
`S`. -/
def opRd (S : Nat → Prop) (al : Option (Nat × Place)) : Operand → Nat → Prop
  | .copy q, l => aliasBase al q.base = l
  | .move q, l => aliasBase al q.base = l
  | .load p _, l => aliasBase al p.base = l ∨ S l
  | _, _ => False

/-- Local `l` may be read by the (non-call) statement `st` under the alias `al`. -/
def stRd (S : Nat → Prop) (al : Option (Nat × Place)) (st : Stmt) (l : Nat) : Prop :=
  (∃ o ∈ st.operands, opRd S al o l) ∨ (∃ p v, st = .store p v ∧ aliasBase al p.base = l)

/-- `t` arises from `s` without changing allocation or alias, and every logged access is to an
allocated local, in bounds, and (if a read) to a local satisfying `R`. -/
structure G (P : Prog) (R : Nat → Prop) (s t : St) : Prop where
  live : t.live = s.live
  alias : t.alias = s.alias
  log : ∃ d, t.log = s.log ++ d ∧
    ∀ e ∈ d, s.live e.loc = true ∧ e.off < P.size e.loc ∧ (e.kind = .read → R e.loc)

theorem G.refl (P : Prog) (R : Nat → Prop) (s : St) : G P R s s :=
  ⟨rfl, rfl, ⟨[], by simp, by simp⟩⟩

theorem G.trans {P : Prog} {R : Nat → Prop} {s t u : St} (h1 : G P R s t) (h2 : G P R t u) :
    G P R s u := by
  obtain ⟨l1, a1, d1, hd1, he1⟩ := h1
  obtain ⟨l2, a2, d2, hd2, he2⟩ := h2
  refine ⟨l2.trans l1, a2.trans a1, d1 ++ d2, by rw [hd2, hd1, List.append_assoc], ?_⟩
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact he1 e he
  · have := he2 e he; rw [l1] at this; exact this

theorem G.mono {P : Prog} {R R' : Nat → Prop} {s t : St} (h : G P R s t)
    (hR : ∀ l, R l → R' l) : G P R' s t := by
  obtain ⟨l1, a1, d1, hd1, he1⟩ := h
  exact ⟨l1, a1, d1, hd1, fun e he => let h := he1 e he; ⟨h.1, h.2.1, fun hk => hR _ (h.2.2 hk)⟩⟩

theorem G_fail (P : Prog) (R : Nat → Prop) (s : St) (k : Status) : G P R s (s.fail k) :=
  ⟨rfl, rfl, ⟨[], by simp [St.fail], by simp⟩⟩

theorem G_emit (P : Prog) (R : Nat → Prop) (s : St) (e : Event) : G P R s (s.emit e) :=
  ⟨rfl, rfl, ⟨[], by simp [St.emit], by simp⟩⟩

theorem G_readCells (P : Prog) (s : St) (loc off n : Nat) (hl : s.live loc = true)
    (hb : off + n ≤ P.size loc) :
    G P (· = loc) s (readCells s loc off n).1 ∧
    ((readCells s loc off n).2 = none → (readCells s loc off n).1.status = .ub) := by
  obtain ⟨h1, h2, m, hm, h3, -⟩ := readCells_spec s loc off n
  rcases hr : readCells s loc off n with ⟨s', r⟩
  rw [hr] at h1 h2 h3
  obtain ⟨-, hlv, hal, -⟩ := readCells_eq hr
  refine ⟨⟨hlv, hal, _, h3, ?_⟩, ?_⟩
  · intro e he
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    exact ⟨hl, by simp only; omega, fun _ => rfl⟩
  · intro hn
    simp only at hn h1 h2 ⊢
    rw [h2]
    split
    · rename_i hc; rw [ite_eq_left hc, hn] at h1; cases h1
    · rfl

theorem G_writeCellsK (P : Prog) (R : Nat → Prop) (k : AccKind) (hk : k ≠ .read) (s : St)
    (loc off : Nat) (vs : List Val) (hl : s.live loc = true) (hb : off + vs.length ≤ P.size loc) :
    G P R s (writeCellsK k s loc off vs) := by
  rw [writeCellsK_eq]
  refine ⟨rfl, rfl, _, rfl, ?_⟩
  intro e he
  simp only [List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨hl, by simp only; omega, fun h => absurd h hk⟩

theorem G_evalOp (S : Nat → Prop) (ms : MoveSem) (P : Prog) (s : St) (o : Operand)
    (hp : PtrsIn S s) :
    G P (opRd S s.alias o) s (evalOp ms P s o).1 ∧
    ((evalOp ms P s o).2 = none → (evalOp ms P s o).1.status ≠ .running) ∧
    (∀ vs, (evalOp ms P s o).2 = some vs → vs.length = o.len) := by
  cases o with
  | lit n => exact ⟨G.refl _ _ _, by simp [evalOp], by simp [evalOp, Operand.len]⟩
  | addrOf q =>
    simp only [evalOp]
    split
    · exact ⟨G.refl _ _ _, by simp, by simp [Operand.len]⟩
    · exact ⟨G_fail _ _ _ _, by simp [St.fail], by simp⟩
  | copy q =>
    simp only [evalOp]
    split
    · rename_i r hr
      obtain ⟨hl, hb, hlen⟩ := resolvePlace_spec hr
      have hbase := resolvePlace_base hr
      obtain ⟨g, hn⟩ := G_readCells P s r.base r.off r.len hl hb
      refine ⟨g.mono (fun l hl' => by simp only [opRd]; rw [hl', hbase]),
        fun h => by rw [hn h]; simp, ?_⟩
      intro vs hvs
      rcases hrc : readCells s r.base r.off r.len with ⟨s', w⟩
      rw [hrc] at hvs; simp only at hvs; subst hvs
      rw [readCells_len hrc, hlen]; rfl
    · exact ⟨G_fail _ _ _ _, by simp [St.fail], by simp⟩
  | move q =>
    simp only [evalOp]
    split
    · rename_i r hr
      obtain ⟨hl, hb, hlen⟩ := resolvePlace_spec hr
      have hbase := resolvePlace_base hr
      obtain ⟨g, hn⟩ := G_readCells P s r.base r.off r.len hl hb
      have g' := g.mono (R' := opRd S s.alias (.move q))
        (fun l hl' => by simp only [opRd]; rw [hl', hbase])
      rcases hrc : readCells s r.base r.off r.len with ⟨s', _ | vs⟩
      · rw [hrc] at g' hn
        exact ⟨g', fun _ => by rw [hn rfl]; simp, by simp⟩
      · rw [hrc] at g'
        have hlen' := readCells_len hrc
        simp only
        split
        · refine ⟨g'.trans (G_writeCellsK P _ .write (by decide) s' r.base r.off _ ?_ ?_), by simp, ?_⟩
          · rw [g'.live]; exact hl
          · simp only [List.length_replicate]; omega
          · intro vs' h; simp only [Option.some.injEq] at h; subst h; rw [hlen', hlen]; rfl
        · exact ⟨g', by simp, by
            intro vs' h; simp only [Option.some.injEq] at h; subst h; rw [hlen', hlen]; rfl⟩
    · exact ⟨G_fail _ _ _ _, by simp [St.fail], by simp⟩
  | load p len =>
    simp only [evalOp]
    split
    · rename_i r hr
      obtain ⟨hl, hb, hlen⟩ := resolvePlace_spec hr
      have hbase := resolvePlace_base hr
      split
      · rename_i hr1
        obtain ⟨g, hn⟩ := G_readCells P s r.base r.off 1 hl (by omega)
        have g' := g.mono (R' := opRd S s.alias (.load p len))
          (fun l hl' => by simp only [opRd]; left; rw [hl', hbase])
        split
        · rename_i s1 l o heq
          rw [heq] at g'
          have hm := (readCells_eq heq).2.2.2 _ rfl
          simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
            List.cons.injEq, and_true] at hm
          have hSl : S l := hp _ _ _ _ hm.symm
          split
          · rename_i hc
            obtain ⟨g2, hn2⟩ := G_readCells P s1 l o len hc.1 hc.2
            refine ⟨g'.trans (g2.mono (fun l' hl' => by simp only [opRd]; right; rw [hl']; exact hSl)),
              fun h => by rw [hn2 h]; simp, ?_⟩
            intro vs hvs
            rcases hrc : readCells s1 l o len with ⟨s2, w⟩
            rw [hrc] at hvs; simp only at hvs; subst hvs
            rw [readCells_len hrc]; rfl
          · exact ⟨g'.trans (G_fail _ _ _ _), by simp [St.fail], by simp⟩
        · rename_i s1 x _ heq
          rw [heq] at g'
          exact ⟨g'.trans (G_fail _ _ _ _), by simp [St.fail], by simp⟩
        · rename_i s1 heq
          rw [heq] at g' hn
          exact ⟨g', fun _ => by rw [hn rfl]; simp, by simp⟩
      · exact ⟨G_fail _ _ _ _, by simp [St.fail], by simp⟩
    · exact ⟨G_fail _ _ _ _, by simp [St.fail], by simp⟩

theorem G_evalOps (S : Nat → Prop) (ms : MoveSem) (P : Prog) (os : List Operand) :
    ∀ s : St, PtrsIn S s → (∀ o ∈ os, ∀ b, o.takesAddr b = true → S (aliasBase s.alias b)) →
    G P (fun l => ∃ o ∈ os, opRd S s.alias o l) s (evalOps ms P s os).1 ∧
    ((evalOps ms P s os).2 = none → (evalOps ms P s os).1.status ≠ .running) ∧
    (∀ vs, (evalOps ms P s os).2 = some vs → vs.length = (os.map Operand.len).sum) := by
  induction os with
  | nil => intro s _ _; exact ⟨G.refl _ _ _, by simp [evalOps], by simp [evalOps]⟩
  | cons o os ih =>
    intro s hp hta
    obtain ⟨g, hn, hl⟩ := G_evalOp S ms P s o hp
    have g' := g.mono (R' := fun l => ∃ o' ∈ o :: os, opRd S s.alias o' l)
      (fun l h => ⟨o, List.mem_cons_self .., h⟩)
    simp only [evalOps]
    rcases he : evalOp ms P s o with ⟨s1, _ | vs⟩
    · rw [he] at g' hn
      exact ⟨g', hn, by simp⟩
    · rw [he] at g' hl
      simp only
      have hp1 := (ptrsIn_evalOp he hp (hta o (List.mem_cons_self ..))).1
      have hal : s1.alias = s.alias := g'.alias
      obtain ⟨g2, hn2, hl2⟩ := ih s1 hp1 (fun o' ho' b hb => by
        rw [hal]; exact hta o' (List.mem_cons_of_mem _ ho') b hb)
      have g2' := g2.mono (R' := fun l => ∃ o' ∈ o :: os, opRd S s.alias o' l)
        (fun l ⟨o', ho', h⟩ => ⟨o', List.mem_cons_of_mem _ ho', by rw [← hal]; exact h⟩)
      rcases he2 : evalOps ms P s1 os with ⟨s2, _ | ws⟩
      · rw [he2] at g2' hn2
        exact ⟨g'.trans g2', hn2, by simp⟩
      · rw [he2] at g2' hl2
        refine ⟨g'.trans g2', by simp, ?_⟩
        intro vs' h; simp only [Option.some.injEq] at h; subst h
        simp only [List.length_append, hl vs rfl, hl2 ws rfl, List.map_cons, List.sum_cons]

theorem G_writeInOrder (S : Nat → Prop) (ms : MoveSem) (P : Prog) (loc : Nat) (os : List Operand) :
    ∀ (s : St) (off : Nat), PtrsIn S s →
    (∀ o ∈ os, ∀ b, o.takesAddr b = true → S (aliasBase s.alias b)) →
    s.live loc = true → off + (os.map Operand.len).sum ≤ P.size loc →
    G P (fun l => ∃ o ∈ os, opRd S s.alias o l) s (writeInOrder ms P s loc off os) := by
  induction os with
  | nil => intro s off _ _ _ _; exact G.refl _ _ _
  | cons o os ih =>
    intro s off hp hta hlv hb
    obtain ⟨g, -, hl⟩ := G_evalOp S ms P s o hp
    have g' := g.mono (R' := fun l => ∃ o' ∈ o :: os, opRd S s.alias o' l)
      (fun l h => ⟨o, List.mem_cons_self .., h⟩)
    simp only [writeInOrder]
    rcases he : evalOp ms P s o with ⟨s1, _ | vs⟩
    · rw [he] at g'; exact g'
    · rw [he] at g' hl
      simp only
      have hpv := ptrsIn_evalOp he hp (hta o (List.mem_cons_self ..))
      have hal : s1.alias = s.alias := g'.alias
      have hlen := hl vs rfl
      simp only [List.map_cons, List.sum_cons] at hb
      have gw := G_writeCellsK P (fun l => ∃ o' ∈ o :: os, opRd S s.alias o' l) .write (by decide)
        s1 loc off vs (by rw [g'.live]; exact hlv) (by omega)
      have hp2 := ptrsIn_writeCellsK (s := s1) .write loc off vs hpv.1 (hpv.2 vs rfl)
      have g3 := ih (writeCells s1 loc off vs) (off + vs.length) hp2
        (fun o' ho' b hb' => by
          rw [show (writeCells s1 loc off vs).alias = s.alias by
            rw [(step_writeCells s1 loc off vs).alias, hal]]
          exact hta o' (List.mem_cons_of_mem _ ho') b hb')
        (by rw [show (writeCells s1 loc off vs).live = s.live by
            rw [writeCells, writeCellsK_live, g'.live]]; exact hlv)
        (by omega)
      refine g'.trans (gw.trans (g3.mono ?_))
      intro l ⟨o', ho', h⟩
      refine ⟨o', List.mem_cons_of_mem _ ho', ?_⟩
      rwa [show (writeCells s1 loc off vs).alias = s.alias by
        rw [(step_writeCells s1 loc off vs).alias, hal]] at h

theorem G_cmpOp (S : Nat → Prop) (ms : MoveSem) (P : Prog) (A : Layout) (s : St) (a b : Operand)
    (f : Nat → Nat → Bool) (hp : PtrsIn S s)
    (ha : ∀ x, a.takesAddr x = true → S (aliasBase s.alias x)) :
    G P (fun l => opRd S s.alias a l ∨ opRd S s.alias b l) s (cmpOp ms P A s a b f) := by
  obtain ⟨g, -, -⟩ := G_evalOp S ms P s a hp
  have g' := g.mono (R' := fun l => opRd S s.alias a l ∨ opRd S s.alias b l) (fun l h => Or.inl h)
  unfold cmpOp
  split
  · rename_i s1 va he1
    rw [he1] at g'
    have hp1 := (ptrsIn_evalOp he1 hp ha).1
    have hal : s1.alias = s.alias := g'.alias
    obtain ⟨g2, -, -⟩ := G_evalOp S ms P s1 b hp1
    have g2' := g2.mono (R' := fun l => opRd S s.alias a l ∨ opRd S s.alias b l)
      (fun l h => Or.inr (by rw [← hal]; exact h))
    split
    · rename_i s2 vb he2
      rw [he2] at g2'
      split
      · exact g'.trans (g2'.trans (G_emit _ _ _ _))
      · exact g'.trans (g2'.trans (G_fail _ _ _ _))
    · rename_i s2 _ _ he2
      rw [he2] at g2'
      exact g'.trans (g2'.trans (G_fail _ _ _ _))
    · rename_i s2 he2
      rw [he2] at g2'
      exact g'.trans g2'
  · rename_i s1 _ _ he1
    rw [he1] at g'
    exact g'.trans (G_fail _ _ _ _)
  · rename_i s1 he1
    rw [he1] at g'
    exact g'

theorem G_execBasic (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (hp : PtrsIn S s) (hta : ∀ x, st.takesAddr x = true → S (aliasBase s.alias x))
    (hst : ∀ x, (st = .storageLive x ∨ st = .storageDead x) → s.inCall = true) :
    G P (stRd S s.alias st) s (execBasic sem P A s st) := by
  unfold execBasic
  split
  · exact G.refl _ _ _
  · cases st with
    | storageLive x =>
      simp only [hst x (Or.inl rfl), ↓reduceIte]; exact G_fail _ _ _ _
    | storageDead x =>
      simp only [hst x (Or.inr rfl), ↓reduceIte]; exact G_fail _ _ _ _
    | assign lhs rhs =>
      have htr : ∀ o ∈ rhs, ∀ b, o.takesAddr b = true → S (aliasBase s.alias b) :=
        fun o ho b hb => hta b (by simp only [Stmt.takesAddr]; exact List.any_eq_true.2 ⟨o, ho, hb⟩)
      have hR : ∀ l, (∃ o ∈ rhs, opRd S s.alias o l) → stRd S s.alias (.assign lhs rhs) l :=
        fun l h => Or.inl (by simpa [Stmt.operands] using h)
      simp only
      split
      · exact G_fail _ _ _ _
      · rename_i hsum
        split
        · exact G_fail _ _ _ _
        · rename_i r hr
          obtain ⟨hl, hb, hlen⟩ := resolvePlace_spec hr
          split
          · obtain ⟨g, -, hvl⟩ := G_evalOps S sem.move P rhs s hp htr
            rcases he : evalOps sem.move P s rhs with ⟨s', _ | vs⟩
            · rw [he] at g; exact g.mono hR
            · rw [he] at g hvl
              simp only
              have hv := hvl vs rfl
              exact (g.trans (G_writeCellsK P (fun l => ∃ o ∈ rhs, opRd S s.alias o l) .write
                (by decide) s' r.base r.off vs (by rw [g.live]; exact hl) (by omega))).mono hR
          · exact (G_writeInOrder S sem.move P r.base rhs s r.off hp htr hl (by omega)).mono hR
    | store p v =>
      simp only
      split
      · rename_i r hr
        obtain ⟨hl, hb, hlen⟩ := resolvePlace_spec hr
        have hbase := resolvePlace_base hr
        split
        · rename_i hr1
          obtain ⟨g, -⟩ := G_readCells P s r.base r.off 1 hl (by omega)
          have g' := g.mono (R' := stRd S s.alias (.store p v))
            (fun l hl' => Or.inr ⟨p, v, rfl, by rw [hl', hbase]⟩)
          split
          · rename_i s1 l o heq
            rw [heq] at g'
            have hp1 : PtrsIn S s1 := ptrsIn_congr (readCells_eq heq).1 hp
            have hal : s1.alias = s.alias := g'.alias
            obtain ⟨g2, -, -⟩ := G_evalOp S sem.move P s1 v hp1
            have g2' := g2.mono (R' := stRd S s.alias (.store p v))
              (fun l h => Or.inl ⟨v, by simp [Stmt.operands], by rw [← hal]; exact h⟩)
            split
            · rename_i s2 vs heq2
              rw [heq2] at g2'
              split
              · rename_i hc
                exact g'.trans (g2'.trans
                  (G_writeCellsK P _ .write (by decide) s2 l o vs hc.1 hc.2))
              · exact g'.trans (g2'.trans (G_fail _ _ _ _))
            · rename_i s2 heq2
              rw [heq2] at g2'
              exact g'.trans g2'
          · rename_i s1 _ _ heq; rw [heq] at g'; exact g'.trans (G_fail _ _ _ _)
          · rename_i s1 heq; rw [heq] at g'; exact g'
        · exact G_fail _ _ _ _
      · exact G_fail _ _ _ _
    | ptrEq a b =>
      exact (G_cmpOp S sem.move P A s a b _ hp (fun x hx => hta x (by simp [Stmt.takesAddr, hx]))).mono
        (fun l h => Or.inl (by
          rcases h with h | h
          · exact ⟨a, by simp [Stmt.operands], h⟩
          · exact ⟨b, by simp [Stmt.operands], h⟩))
    | ptrInRange a b n =>
      exact (G_cmpOp S sem.move P A s a b _ hp (fun x hx => hta x (by simp [Stmt.takesAddr, hx]))).mono
        (fun l h => Or.inl (by
          rcases h with h | h
          · exact ⟨a, by simp [Stmt.operands], h⟩
          · exact ⟨b, by simp [Stmt.operands], h⟩))
    | out o =>
      simp only
      obtain ⟨g, -, -⟩ := G_evalOp S sem.move P s o hp
      have g' := g.mono (R' := stRd S s.alias (.out o))
        (fun l h => Or.inl ⟨o, by simp [Stmt.operands], h⟩)
      rcases he : evalOp sem.move P s o with ⟨s', _ | vs⟩
      · rw [he] at g'; exact g'
      · rw [he] at g'; exact g'.trans (G_emit _ _ _ _)
    | call fn a => exact G_fail _ _ _ _
    | nop => exact G.refl _ _ _

theorem G_execCallee (S : Nat → Prop) (sem : Sem) (P : Prog) (A : Layout) (b : List Stmt) :
    ∀ s : St, PtrsIn S s → s.inCall = true →
    (∀ st ∈ b, ∀ x, st.takesAddr x = true → S (aliasBase s.alias x)) →
    G P (fun l => ∃ st ∈ b, stRd S s.alias st l) s (execCallee sem P A s b) := by
  induction b with
  | nil => intro s _ _ _; exact G.refl _ _ _
  | cons st b ih =>
    intro s hp hc hta
    simp only [execCallee, List.foldl_cons]
    have g := G_execBasic S sem P A s st hp (hta st (List.mem_cons_self ..)) (fun _ _ => hc)
    have hstep := step_execBasic sem P A s st
    have hal : (execBasic sem P A s st).alias = s.alias := hstep.alias
    have g2 := ih (execBasic sem P A s st)
      (ptrsIn_execBasic S sem P A s st hp (hta st (List.mem_cons_self ..)))
      (by rw [hstep.inCall]; exact hc)
      (fun st' h' x hx => by rw [hal]; exact hta st' (List.mem_cons_of_mem _ h') x hx)
    exact (g.mono (fun l h => ⟨st, List.mem_cons_self .., h⟩)).trans
      (g2.mono (fun l ⟨st', h', hr⟩ => ⟨st', List.mem_cons_of_mem _ h', by rw [← hal]; exact hr⟩))

/-! ## One top-level statement: read soundness and allocation discipline -/

theorem touched_append (d1 d2 : List Access) (l o : Nat) :
    touched (d1 ++ d2) l o = (touched d1 l o || touched d2 l o) := by
  simp [touched, List.any_append]

theorem touched_false_of_ne {d : List Access} {u : Nat} (h : ∀ e ∈ d, e.loc ≠ u) (c : Nat) :
    touched d u c = false := by
  simp only [touched, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
  intro e he h1; exact absurd h1 (h e he)

theorem pos_size_lt_nloc {P : Prog} {u c : Nat} (h : c < P.size u) : u < P.nloc := by
  unfold Prog.size at h; unfold Prog.nloc
  rw [List.getD_eq_getElem?_getD] at h
  by_cases hu : u < P.sizes.length
  · exact hu
  · rw [List.getElem?_eq_none (by omega)] at h; simp at h

/-- The facts established for (a piece of) one top-level statement `st`: every logged access is in
bounds and every read is licensed by `st.mayRead`; and a deallocated local is first accessed by a
non-read, or stays deallocated if it is not accessed. -/
structure Pc (P : Prog) (st : Stmt) (s t : St) : Prop where
  log : ∃ d, t.log = s.log ++ d ∧
    ∀ e ∈ d, e.off < P.size e.loc ∧ (e.kind = .read → st.mayRead P e.loc = true)
  dead : ∀ u c, c < P.size u → s.live u = false → ∃ d, t.log = s.log ++ d ∧
    ft u c d = true ∧ (touched d u c = false → t.live u = false)

theorem Pc.refl (P : Prog) (st : Stmt) (s : St) : Pc P st s s :=
  ⟨⟨[], by simp, by simp⟩, fun _ _ _ h => ⟨[], by simp, rfl, fun _ => h⟩⟩

theorem Pc.of_eq {P : Prog} {st : Stmt} {s t : St} (hl : t.log = s.log) (hv : t.live = s.live) :
    Pc P st s t :=
  ⟨⟨[], by simp [hl], by simp⟩, fun _ _ _ h => ⟨[], by simp [hl], rfl, fun _ => by rw [hv]; exact h⟩⟩

theorem Pc.trans {P : Prog} {st : Stmt} {s t u : St} (h1 : Pc P st s t) (h2 : Pc P st t u) :
    Pc P st s u := by
  refine ⟨?_, ?_⟩
  · obtain ⟨d1, hd1, he1⟩ := h1.log
    obtain ⟨d2, hd2, he2⟩ := h2.log
    refine ⟨d1 ++ d2, by rw [hd2, hd1, List.append_assoc], fun e he => ?_⟩
    rcases List.mem_append.1 he with he | he
    · exact he1 e he
    · exact he2 e he
  · intro x c hc hx
    obtain ⟨d1, hd1, hf1, ht1⟩ := h1.dead x c hc hx
    cases htd : touched d1 x c
    · obtain ⟨d2, hd2, hf2, ht2⟩ := h2.dead x c hc (ht1 htd)
      refine ⟨d1 ++ d2, by rw [hd2, hd1, List.append_assoc], ?_, ?_⟩
      · rw [ft_append, htd]; exact hf2
      · rw [touched_append, htd]; exact ht2
    · obtain ⟨d2, hd2, -⟩ := h2.log
      refine ⟨d1 ++ d2, by rw [hd2, hd1, List.append_assoc], ?_, ?_⟩
      · rw [ft_append, htd]; exact hf1
      · rw [touched_append, htd]; simp

theorem Pc.of_G {P : Prog} {st : Stmt} {R : Nat → Prop} {s t : St} (g : G P R s t)
    (hR : ∀ l, R l → st.mayRead P l = true) : Pc P st s t := by
  obtain ⟨hlv, -, d, hd, he⟩ := g
  refine ⟨⟨d, hd, fun e h => ⟨(he e h).2.1, fun hk => hR _ ((he e h).2.2 hk)⟩⟩, ?_⟩
  intro u c _ hu
  have hne : ∀ e ∈ d, e.loc ≠ u := fun e h h' => by
    have := (he e h).1; rw [h', hu] at this; cases this
  have ht := touched_false_of_ne hne c
  exact ⟨d, hd, ft_of_not_touched ht, fun _ => by rw [hlv]; exact hu⟩

theorem Pc.fail (P : Prog) (st : Stmt) (s : St) (k : Status) : Pc P st s (s.fail k) :=
  Pc.of_eq rfl rfl

theorem Pc_allocate (P : Prog) (st : Stmt) (s : St) (x : Nat) : Pc P st s (allocate P s x) := by
  unfold allocate
  split
  · rename_i hx
    rw [resetCells, writeCellsK_eq]
    refine ⟨⟨_, rfl, ?_⟩, ?_⟩
    · intro e he
      simp only [List.mem_map, List.mem_range, List.length_replicate] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨by simp only; omega, fun h => by cases h⟩
    · intro u c hc hu
      refine ⟨_, rfl, ?_, ?_⟩
      · apply firstTouchNotRead_of_noRead
        intro e he; simp only [List.mem_map] at he
        obtain ⟨i, -, rfl⟩ := he; intro _ _ h; cases h
      · intro ht
        by_cases hux : u = x
        · subst hux
          exfalso
          simp [touched] at ht
          exact ht c hc rfl
        · simp only [hux, ↓reduceIte]; exact hu
  · exact Pc.fail _ _ _ _

theorem Pc_deallocate (P : Prog) (st : Stmt) (s : St) (x : Nat) :
    Pc P st s (deallocate P s x) := by
  unfold deallocate
  split
  · rename_i hx
    simp only [resetCells, writeCellsK_eq]
    refine ⟨⟨_, rfl, ?_⟩, ?_⟩
    · intro e he
      simp only [List.mem_map, List.mem_range, List.length_replicate] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨by simp only; omega, fun h => by cases h⟩
    · intro u c hc hu
      refine ⟨_, rfl, ?_, ?_⟩
      · apply firstTouchNotRead_of_noRead
        intro e he; simp only [List.mem_map] at he
        obtain ⟨i, -, rfl⟩ := he; intro _ _ h; cases h
      · intro _
        by_cases hux : u = x
        · subst hux; simp
        · simp only [hux, ↓reduceIte]; exact hu
  · exact Pc.refl _ _ _

theorem execStmt_of_not_call (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (h : ∀ fn a, st ≠ .call fn a) : execStmt sem P A s st = execBasic sem P A s st := by
  unfold execStmt
  split
  · rename_i hs; exact (execBasic_of_not_running st hs).symm
  · cases st <;> first | rfl | exact absurd rfl (h _ _)

theorem resolvePlace_eq_of_none {P : Prog} {s : St} {q r : Place} (ha : s.alias = none)
    (h : resolvePlace P s q = some r) : r = q := by
  simp only [resolvePlace, ha] at h
  split at h
  · cases h; rfl
  · cases h

theorem aliasBase_none (b : Nat) : aliasBase none b = b := rfl

theorem mayReadNoCall_of_stRd {P : Prog} {st : Stmt} {l : Nat}
    (h : stRd (AddrTaken P) none st l) : st.mayReadNoCall P l = true := by
  simp only [Stmt.mayReadNoCall, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true]
  rcases h with ⟨o, ho, hr⟩ | ⟨p, v, rfl, hp⟩
  · cases o with
    | copy q =>
      simp only [opRd, aliasBase_none] at hr
      exact Or.inl (Or.inl ⟨_, ho, by simp [Operand.readsName, hr]⟩)
    | move q =>
      simp only [opRd, aliasBase_none] at hr
      exact Or.inl (Or.inl ⟨_, ho, by simp [Operand.readsName, hr]⟩)
    | load p n =>
      simp only [opRd, aliasBase_none] at hr
      rcases hr with hr | hr
      · exact Or.inl (Or.inl ⟨_, ho, by simp [Operand.readsName, hr]⟩)
      · exact Or.inr ⟨hr, _, ho, rfl⟩
    | lit n => cases hr
    | addrOf q => cases hr
  · exact Or.inl (Or.inr (by simp [← hp, aliasBase_none]))

theorem stRd_some {S : Nat → Prop} {prm : Nat} {r : Place} {st : Stmt} {l : Nat}
    (h : stRd S (some (prm, r)) st l) : stRd S none st l ∨ r.base = l := by
  have key : ∀ b, aliasBase (some (prm, r)) b = l → aliasBase none b = l ∨ r.base = l := by
    intro b hb
    simp only [aliasBase] at hb ⊢
    split at hb
    · exact Or.inr hb
    · exact Or.inl hb
  rcases h with ⟨o, ho, hr⟩ | ⟨p, v, hst, hp⟩
  · cases o with
    | copy q => rcases key _ hr with h | h; exact Or.inl (Or.inl ⟨_, ho, h⟩); exact Or.inr h
    | move q => rcases key _ hr with h | h; exact Or.inl (Or.inl ⟨_, ho, h⟩); exact Or.inr h
    | load p n =>
      rcases hr with hr | hr
      · rcases key _ hr with h | h
        · exact Or.inl (Or.inl ⟨_, ho, Or.inl h⟩)
        · exact Or.inr h
      · exact Or.inl (Or.inl ⟨_, ho, Or.inr hr⟩)
    | lit n => cases hr
    | addrOf q => cases hr
  · rcases key _ hp with h | h
    · exact Or.inl (Or.inr ⟨p, v, hst, h⟩)
    · exact Or.inr h

theorem mayRead_of_noCall {P : Prog} {st : Stmt} {l : Nat} (h : st.mayReadNoCall P l = true) :
    st.mayRead P l = true := by
  simp [Stmt.mayRead, h]

theorem Pc_execStmt (sem : Sem) (P : Prog) (A : Layout) (s : St) (st : Stmt)
    (hst : st ∈ P.code) (ha : s.alias = none) (hc : s.inCall = false)
    (hp : PtrsIn (AddrTaken P) s) : Pc P st s (execStmt sem P A s st) := by
  have hd := addrDisc_addrTaken P
  by_cases hrun : s.status ≠ .running
  · rw [execStmt_of_not_running st hrun]; exact Pc.refl _ _ _
  have hbasic : (∀ fn a, st ≠ .call fn a) → (∀ x, st ≠ .storageLive x ∧ st ≠ .storageDead x) →
      Pc P st s (execStmt sem P A s st) := by
    intro hnc hns
    rw [execStmt_of_not_call _ _ _ _ _ hnc]
    refine Pc.of_G (G_execBasic (AddrTaken P) sem P A s st hp
      (fun x hx => by rw [ha]; exact hd.1 st hst x hx)
      (fun x h => by rcases h with h | h; exact absurd h (hns x).1; exact absurd h (hns x).2)) ?_
    intro l h
    rw [ha] at h
    exact mayRead_of_noCall (mayReadNoCall_of_stRd h)
  cases st with
  | storageLive x =>
    rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)]
    unfold execBasic
    simp only [hrun, hc, ↓reduceIte, Bool.false_eq_true]
    exact Pc_allocate _ _ _ _
  | storageDead x =>
    rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)]
    unfold execBasic
    simp only [hrun, hc, ↓reduceIte, Bool.false_eq_true]
    exact Pc_deallocate _ _ _ _
  | assign lhs rhs => exact hbasic (by intros; simp) (by intros; simp)
  | store p v => exact hbasic (by intros; simp) (by intros; simp)
  | ptrEq a b => exact hbasic (by intros; simp) (by intros; simp)
  | ptrInRange a b n => exact hbasic (by intros; simp) (by intros; simp)
  | out o => exact hbasic (by intros; simp) (by intros; simp)
  | nop => exact hbasic (by intros; simp) (by intros; simp)
  | call fn arg =>
    unfold execStmt
    simp only [hrun, ↓reduceIte]
    split
    · rename_i _ _ q hm
      split
      · exact Pc.fail _ _ _ _
      · rename_i r hr
        split
        · exact Pc.fail _ _ _ _
        · have hrb : r.base = q.base := by rw [resolvePlace_base hr, ha]; rfl
          have g := G_execCallee (AddrTaken P) sem P A (P.fn fn).body
            { s with alias := some ((P.fn fn).prm, r), inCall := true } hp rfl (by
              intro st' h' x hx
              show AddrTaken P (aliasBase (some ((P.fn fn).prm, r)) x)
              simp only [aliasBase]
              split
              · rename_i hxp
                rw [hrb]
                exact hd.2.2 fn q hst (List.any_eq_true.2 ⟨st', h', by rw [← hxp]; exact hx⟩)
              · exact hd.2.1 fn st' h' x hx)
          have p1 := Pc.of_G g (st := .call fn (.move q)) (by
            intro l ⟨st', h', hr'⟩
            rcases stRd_some hr' with h | h
            · simp only [Stmt.mayRead, Bool.or_eq_true, List.any_eq_true]
              exact Or.inr ⟨st', h', mayReadNoCall_of_stRd h⟩
            · apply mayRead_of_noCall
              simp [Stmt.mayReadNoCall, Stmt.operands, Operand.readsName, ← h, hrb])
          refine Pc.trans ?_ (p1.trans ?_)
          · exact Pc.of_eq rfl rfl
          · exact Pc.of_eq rfl rfl
    · rename_i arg _ _ _
      have hta : ∀ x, arg.takesAddr x = true → AddrTaken P (aliasBase s.alias x) := by
        intro x hx; rw [ha]; exact hd.1 _ hst x (by simpa [Stmt.takesAddr] using hx)
      obtain ⟨g, -, hvl⟩ := G_evalOp (AddrTaken P) sem.move P s arg hp
      have hR1 : ∀ l, opRd (AddrTaken P) s.alias arg l → (Stmt.call fn arg).mayRead P l = true := by
        intro l h; rw [ha] at h
        exact mayRead_of_noCall (mayReadNoCall_of_stRd (Or.inl ⟨arg, by simp [Stmt.operands], h⟩))
      rcases he : evalOp sem.move P s arg with ⟨s1, _ | vs⟩
      · rw [he] at g; exact Pc.of_G g hR1
      · rw [he] at g hvl
        have p1 := Pc.of_G g hR1
        have hpv := ptrsIn_evalOp he hp hta
        simp only
        split
        · exact p1.trans (Pc.fail _ _ _ _)
        · rename_i hif
          have hlen : vs.length = P.size (P.fn fn).prm := by
            simp only [not_or] at hif; omega
          have p2 := Pc_allocate P (.call fn arg) s1 (P.fn fn).prm
          have p3 : Pc P (.call fn arg) (allocate P s1 (P.fn fn).prm)
              (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs) := by
            rcases allocate_live_or P s1 (P.fn fn).prm with hl | hz
            · exact Pc.of_G (G_writeCellsK P (fun _ => False) .write (by decide) _ _ 0 vs hl
                (by omega)) (fun _ h => h.elim)
            · have : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
              subst this; exact Pc.refl _ _ _
          have hal3 : (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias = none := by
            rw [(step_writeCells _ _ _ _).alias, (step_allocate _ _ _).alias, g.alias, ha]
          have hp3 : PtrsIn (AddrTaken P)
              (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs) :=
            ptrsIn_writeCellsK .write _ 0 vs (ptrsIn_allocate P s1 _ hpv.1) (hpv.2 vs rfl)
          have g4 := G_execCallee (AddrTaken P) sem P A (P.fn fn).body
            { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
            hp3 rfl (by
              intro st' h' x hx
              simp only [hal3]
              exact hd.2.1 fn st' h' x hx)
          have p4 := Pc.of_G g4 (st := .call fn arg) (by
            intro l ⟨st', h', hr'⟩
            have hr2 : stRd (AddrTaken P) none st' l := by simpa only [hal3] using hr'
            simp only [Stmt.mayRead, Bool.or_eq_true, List.any_eq_true]
            exact Or.inr ⟨st', h', mayReadNoCall_of_stRd hr2⟩)
          refine p1.trans (p2.trans (p3.trans (Pc.trans ?_ (p4.trans (Pc.trans ?_ (Pc_deallocate _ _ _ _))))))
          · exact Pc.of_eq rfl rfl
          · exact Pc.of_eq rfl rfl

/-! ## Re-initializing statements -/

theorem touched_writeCellsK (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    ∃ d, (writeCellsK k s loc off vs).log = s.log ++ d ∧
      ∀ i < vs.length, touched d loc (off + i) = true := by
  rw [writeCellsK_eq]
  refine ⟨_, rfl, fun i hi => ?_⟩
  simp only [touched, List.any_map, List.any_eq_true, List.mem_range, Function.comp_def,
    Bool.and_eq_true, beq_iff_eq]
  exact ⟨i, hi, by simp⟩

theorem trivPtrs (s : St) : PtrsIn (fun _ => True) s := fun _ _ _ _ _ => trivial

theorem writeInOrder_touch (ms : MoveSem) (P : Prog) (loc : Nat) (os : List Operand) :
    ∀ (s : St) (off : Nat), (writeInOrder ms P s loc off os).status = .running →
    ∃ d, (writeInOrder ms P s loc off os).log = s.log ++ d ∧
      ∀ i < (os.map Operand.len).sum, touched d loc (off + i) = true := by
  induction os with
  | nil => intro s off _; exact ⟨[], by simp [writeInOrder], by simp⟩
  | cons o os ih =>
    intro s off hst
    obtain ⟨g, hn, hl⟩ := G_evalOp (fun _ => True) ms P s o (trivPtrs s)
    simp only [writeInOrder] at hst ⊢
    rcases he : evalOp ms P s o with ⟨s1, _ | vs⟩
    · rw [he] at hn hst; exact absurd hst (hn rfl)
    · rw [he] at hl g hst
      simp only at hst ⊢
      obtain ⟨d1, hd1, -⟩ := g.log
      obtain ⟨d2, hd2, ht2⟩ := touched_writeCellsK .write s1 loc off vs
      obtain ⟨d3, hd3, ht3⟩ := ih _ _ hst
      refine ⟨d1 ++ d2 ++ d3, ?_, ?_⟩
      · rw [hd3]; simp only [writeCells]; rw [hd2, hd1]; simp
      · intro i hi
        have hlen := hl vs rfl
        simp only [List.map_cons, List.sum_cons] at hi
        simp only [touched_append, Bool.or_eq_true]
        by_cases hiv : i < vs.length
        · exact Or.inl (Or.inr (ht2 i hiv))
        · right
          have := ht3 (i - vs.length) (by omega)
          rwa [show off + vs.length + (i - vs.length) = off + i by omega] at this

theorem kills_cases {P : Prog} {u : Nat} {st : Stmt} (h : st.kills P u = true) :
    st = .storageLive u ∨ st = .storageDead u ∨
      ∃ lhs rhs, st = .assign lhs rhs ∧ lhs.base = u ∧ lhs.off = 0 ∧ lhs.len = P.size u := by
  cases st with
  | storageLive x => simp only [Stmt.kills, beq_iff_eq] at h; subst h; exact Or.inl rfl
  | storageDead x => simp only [Stmt.kills, beq_iff_eq] at h; subst h; exact Or.inr (Or.inl rfl)
  | assign lhs rhs =>
    simp only [Stmt.kills, Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inr (Or.inr ⟨lhs, rhs, rfl, h.1.1, h.1.2, h.2⟩)
  | _ => simp [Stmt.kills] at h

theorem kill_storageLive (sem : Sem) (P : Prog) (A : Layout) (s : St) (u : Nat)
    (hc : s.inCall = false) (hrun : s.status = .running) (hu : u < P.nloc) :
    ∃ d, (execStmt sem P A s (.storageLive u)).log = s.log ++ d ∧
      ∀ c < P.size u, touched d u c = true := by
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)]
  unfold execBasic
  simp only [hrun, hc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true]
  unfold allocate
  simp only [hu, ↓reduceIte, resetCells]
  obtain ⟨d, hd, ht⟩ := touched_writeCellsK .reset
    { s with conflicts := s.conflicts ++ (liveOthers P s u).map fun z => (u, z),
             live := fun z => if z = u then true else s.live z } u 0
    (List.replicate (P.size u) .uninit)
  refine ⟨d, hd, fun c hc' => ?_⟩
  have := ht c (by simpa using hc'); simpa using this

theorem kill_storageDead (sem : Sem) (P : Prog) (A : Layout) (s : St) (u : Nat)
    (hc : s.inCall = false) (hrun : s.status = .running) (hl : s.live u = true) :
    ∃ d, (execStmt sem P A s (.storageDead u)).log = s.log ++ d ∧
      ∀ c < P.size u, touched d u c = true := by
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)]
  unfold execBasic
  simp only [hrun, hc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true]
  unfold deallocate
  simp only [hl, ↓reduceIte, resetCells]
  obtain ⟨d, hd, ht⟩ := touched_writeCellsK .reset s u 0 (List.replicate (P.size u) .uninit)
  refine ⟨d, hd, fun c hc' => ?_⟩
  have := ht c (by simpa using hc'); simpa using this

theorem kill_assign (sem : Sem) (P : Prog) (A : Layout) (s : St) (lhs : Place) (rhs : List Operand)
    (ha : s.alias = none) (hrun : s.status = .running)
    (hst : (execStmt sem P A s (.assign lhs rhs)).status = .running) :
    ∃ d, (execStmt sem P A s (.assign lhs rhs)).log = s.log ++ d ∧
      ∀ i < lhs.len, touched d lhs.base (lhs.off + i) = true := by
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)] at hst ⊢
  unfold execBasic at hst ⊢
  simp only [hrun, ne_eq, not_true_eq_false, ↓reduceIte] at hst ⊢
  split
  · rename_i h; rw [ite_eq_left h] at hst; simp [St.fail] at hst
  · rename_i hsum
    rw [ite_eq_right hsum] at hst
    split
    · rename_i h; rw [h] at hst; simp [St.fail] at hst
    · rename_i r hr
      rw [hr] at hst
      have hrq := resolvePlace_eq_of_none ha hr
      subst hrq
      simp only at hst ⊢
      split
      · rename_i hm
        rw [hm] at hst
        simp only at hst
        obtain ⟨g, hn, hl⟩ := G_evalOps (fun _ => True) sem.move P rhs s (trivPtrs s)
          (fun _ _ _ _ => trivial)
        rcases he : evalOps sem.move P s rhs with ⟨s', _ | vs⟩
        · rw [he] at hst hn; exact absurd hst (hn rfl)
        · rw [he] at hst hl g
          simp only at hst ⊢
          obtain ⟨d1, hd1, -⟩ := g.log
          obtain ⟨d2, hd2, ht2⟩ := touched_writeCellsK .write s' r.base r.off vs
          refine ⟨d1 ++ d2, by simp only [writeCells]; rw [hd2, hd1, List.append_assoc], ?_⟩
          intro i hi
          rw [touched_append, ht2 i (by have := hl vs rfl; omega)]; simp
      · rename_i hm
        rw [hm] at hst
        simp only at hst
        obtain ⟨d, hd, ht⟩ := writeInOrder_touch sem.move P r.base rhs s r.off hst
        exact ⟨d, hd, fun i hi => ht i (by omega)⟩

/-! ## The run, tick by tick -/

theorem tick_pc (sem : Sem) (P : Prog) (A : Layout) (t : Nat) (ht : t < P.code.length) :
    Pc P P.code[t] (runAt sem P A t) (runAt sem P A (t + 1)) := by
  obtain ⟨_, hc, ha, _⟩ := runAt_frame sem P A t (by omega)
  have hp := ptrsIn_runAt (AddrTaken P) sem P A (addrDisc_addrTaken P) t
  have pc := Pc_execStmt sem P A (runAt sem P A t) P.code[t] (List.getElem_mem ht) ha hc hp
  rw [runAt_succ _ _ _ _ ht]
  exact pc.trans (Pc.of_eq rfl rfl)

theorem runAt_inBounds (sem : Sem) (P : Prog) (A : Layout) (t : Nat) :
    ∀ e ∈ (runAt sem P A t).log, e.off < P.size e.loc := by
  induction t with
  | zero => simp [runAt_zero, St.init]
  | succ t ih =>
    by_cases ht : t < P.code.length
    · obtain ⟨d, hd, he⟩ := (tick_pc sem P A t ht).log
      intro e h; rw [hd] at h
      rcases List.mem_append.1 h with h | h
      · exact ih e h
      · exact (he e h).1
    · rw [runAt_of_le _ _ _ _ (by omega), ← runAt_of_le sem P A t (by omega)]; exact ih

theorem runAt_succ_stuck (sem : Sem) (P : Prog) (A : Layout) (t : Nat)
    (h : (runAt sem P A t).status ≠ .running) :
    (runAt sem P A (t + 1)).log = (runAt sem P A t).log ∧
      (runAt sem P A (t + 1)).status ≠ .running := by
  by_cases ht : t < P.code.length
  · rw [runAt_succ _ _ _ _ ht]
    refine ⟨?_, ?_⟩
    · simp [execTop, execStmt_of_not_running _ h]
    · simpa [execTop, execStmt_of_not_running _ h] using h
  · rw [runAt_of_le _ _ _ (t + 1) (by omega), ← runAt_of_le sem P A t (by omega)]
    exact ⟨rfl, h⟩

theorem T1_back (sem : Sem) (P : Prog) (O : ObsMask) (hcert : ObsCert P O) (A : Layout)
    (u c : Nat) (hc : c < P.size u) (k : Nat) (n : Nat) :
    ∀ t, t + n = P.code.length → k < t →
    (O t u = false ∨ (runAt sem P A t).live u = false ∨ (runAt sem P A t).status ≠ .running) →
    ∀ E, (run sem P A).log = (runAt sem P A t).log ++ E → ft u c E = true := by
  have hu := pos_size_lt_nloc hc
  induction n with
  | zero =>
    intro t ht _ _ E hE
    rw [run_eq_runAt, ← ht, Nat.add_zero] at hE
    have : E = [] := by simpa using hE
    subst this; rfl
  | succ n ih =>
    intro t ht hkt hcond E hE
    have htl : t < P.code.length := by omega
    obtain ⟨E', hE', -, -⟩ := run_log_split sem P A (t + 1) (by omega)
    have pc := tick_pc sem P A t htl
    have hsplit : ∀ d, (runAt sem P A (t + 1)).log = (runAt sem P A t).log ++ d → E = d ++ E' := by
      intro d hd
      rw [hE', hd, List.append_assoc] at hE
      exact (List.append_cancel_left hE).symm
    have ih' := ih (t + 1) (by omega) (by omega)
    have step : ∀ d, (runAt sem P A (t + 1)).log = (runAt sem P A t).log ++ d →
        (touched d u c = true → ft u c d = true) →
        (touched d u c = false → (O (t + 1) u = false ∨ (runAt sem P A (t + 1)).live u = false ∨
          (runAt sem P A (t + 1)).status ≠ .running)) →
        ft u c E = true := by
      intro d hd h1 h2
      rw [hsplit d hd, ft_append]
      cases htd : touched d u c
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih' (h2 htd) E' hE'
      · simp only [↓reduceIte]; exact h1 htd
    have deadcase : (runAt sem P A t).live u = false → ft u c E = true := by
      intro hl
      obtain ⟨d, hd, hft, hnt⟩ := pc.dead u c hc hl
      exact step d hd (fun _ => hft) (fun h => Or.inr (Or.inl (hnt h)))
    have stuckcase : (runAt sem P A t).status ≠ .running → ft u c E = true := by
      intro hs
      obtain ⟨hl, hs'⟩ := runAt_succ_stuck sem P A t hs
      exact step [] (by rw [hl]; simp) (by simp [touched]) (fun _ => Or.inr (Or.inr hs'))
    rcases hcond with hO | hl | hs
    · obtain ⟨hgen, htr⟩ := hcert t htl u hu
      have hget : P.code.getD t .nop = P.code[t] := by simp [List.getD_eq_getElem?_getD, htl]
      rw [hget] at hgen htr
      have hmr : P.code[t].mayRead P u = false := by
        cases h : P.code[t].mayRead P u
        · rfl
        · rw [hgen h] at hO; cases hO
      by_cases hrun' : (runAt sem P A t).status ≠ .running
      · exact stuckcase hrun'
      have hrun : (runAt sem P A t).status = .running := by simpa using hrun'
      obtain ⟨d, hd, he⟩ := pc.log
      have hnr : ∀ e ∈ d, e.loc = u → e.off = c → e.kind ≠ .read := by
        intro e h hl _ hk
        have := (he e h).2 hk
        rw [hl, hmr] at this; cases this
      have hlog : (runAt sem P A (t + 1)).log =
          (execStmt sem P A (runAt sem P A t) P.code[t]).log := by
        rw [runAt_succ _ _ _ _ htl]; rfl
      have hstat : (runAt sem P A (t + 1)).status =
          (execStmt sem P A (runAt sem P A t) P.code[t]).status := by
        rw [runAt_succ _ _ _ _ htl]; rfl
      have heqd : ∀ d', (execStmt sem P A (runAt sem P A t) P.code[t]).log =
          (runAt sem P A t).log ++ d' → d' = d := by
        intro d' hd'
        rw [← hlog, hd] at hd'
        exact (List.append_cancel_left hd').symm
      refine step d hd (fun _ => firstTouchNotRead_of_noRead _ hnr) (fun hnt => ?_)
      cases hO1 : O (t + 1) u
      · exact Or.inl rfl
      · have hk : P.code[t].kills P u = true := by
          cases h : P.code[t].kills P u
          · rw [htr hO1 h] at hO; cases hO
          · rfl
        obtain ⟨_, hci, hai, _⟩ := runAt_frame sem P A t (by omega)
        rcases kills_cases hk with hst | hst | ⟨lhs, rhs, hst, hb, ho, hlen⟩
        · obtain ⟨d', hd', ht'⟩ := kill_storageLive sem P A _ u hci hrun hu
          rw [← hst, heqd d' hd'] at *
          rw [ht' c hc] at hnt; cases hnt
        · by_cases hlv : (runAt sem P A t).live u = true
          · obtain ⟨d', hd', ht'⟩ := kill_storageDead sem P A _ u hci hrun hlv
            rw [← hst, heqd d' hd'] at *
            rw [ht' c hc] at hnt; cases hnt
          · simp only [Bool.not_eq_true] at hlv
            obtain ⟨d'', hd'', -, hnt''⟩ := pc.dead u c hc hlv
            have : d'' = d := by
              rw [hd] at hd''; exact (List.append_cancel_left hd'').symm
            subst this
            exact Or.inr (Or.inl (hnt'' hnt))
        · by_cases hs1 : (runAt sem P A (t + 1)).status = .running
          · rw [hstat, hst] at hs1
            obtain ⟨d', hd', ht'⟩ := kill_assign sem P A _ lhs rhs hai hrun hs1
            rw [← hst] at hd'
            rw [heqd d' hd'] at ht'
            have := ht' c (by omega)
            rw [hb, ho, Nat.zero_add] at this
            rw [this] at hnt; cases hnt
          · exact Or.inr (Or.inr hs1)
    · exact deadcase hl
    · exact stuckcase hs

/-! ## The upgraded program -/

theorem modifyAt_append (f : Stmt → Stmt) (l1 l2 : List Stmt) (k : Nat) (hk : k < l1.length) :
    modifyAt f (l1 ++ l2) k = modifyAt f l1 k ++ l2 := by
  induction l1 generalizing k with
  | nil => simp at hk
  | cons st l1 ih =>
    cases k with
    | zero => simp [modifyAt]
    | succ k => simp [modifyAt, ih k (by simpa using hk)]

theorem modifyAt_length (f : Stmt → Stmt) (l : List Stmt) (k : Nat) :
    (modifyAt f l k).length = l.length := by
  induction l generalizing k with
  | nil => simp [modifyAt]
  | cons st l ih => cases k <;> simp [modifyAt, ih]

theorem modifyAt_take (f : Stmt → Stmt) (l : List Stmt) (k t : Nat) (ht : t ≤ k) :
    (modifyAt f l k).take t = l.take t := by
  induction l generalizing k t with
  | nil => simp [modifyAt]
  | cons st l ih =>
    cases t with
    | zero => simp
    | succ t =>
      cases k with
      | zero => omega
      | succ k => simp [modifyAt, ih k t (by omega)]

theorem modifyAt_getElem? (f : Stmt → Stmt) (l : List Stmt) (k t : Nat) :
    (modifyAt f l k)[t]? = if t = k then (l[t]?).map f else l[t]? := by
  induction l generalizing k t with
  | nil => simp [modifyAt]
  | cons st l ih =>
    cases k with
    | zero => cases t <;> simp [modifyAt]
    | succ k =>
      cases t with
      | zero => simp [modifyAt]
      | succ t => simp [modifyAt, ih]

theorem upgradeAt_code (P : Prog) (k : Nat) (hk : k < P.body.length) :
    (P.upgradeAt k).code = modifyAt Stmt.upgradeCopy P.code k := by
  simp [Prog.code, Prog.upgradeAt, modifyAt_append _ _ _ _ hk]

theorem execTop_upgradeAt (sem : Sem) (P : Prog) (k : Nat) (A : Layout) :
    execTop sem (P.upgradeAt k) A = execTop sem P A :=
  execTop_congr (P := P.upgradeAt k) (P' := P) rfl rfl sem A

theorem runAt_upgradeAt_le (sem : Sem) (P : Prog) (k : Nat) (hk : k < P.body.length) (A : Layout)
    (t : Nat) (ht : t ≤ k) : runAt sem (P.upgradeAt k) A t = runAt sem P A t := by
  unfold runAt
  rw [execTop_upgradeAt, upgradeAt_code P k hk, modifyAt_take _ _ _ _ ht]

theorem runAt_upgradeAt_succ (sem : Sem) (P : Prog) (k : Nat) (hk : k < P.body.length) (A : Layout)
    (t : Nat) (ht : t < P.code.length) :
    runAt sem (P.upgradeAt k) A (t + 1) =
      execTop sem P A (runAt sem (P.upgradeAt k) A t)
        (if t = k then P.code[t].upgradeCopy else P.code[t]) := by
  have hl : (P.upgradeAt k).code.length = P.code.length := by
    rw [upgradeAt_code P k hk, modifyAt_length]
  rw [runAt_succ sem (P.upgradeAt k) A t (by omega), execTop_upgradeAt]
  congr 1
  have h1 := modifyAt_getElem? Stmt.upgradeCopy P.code k t
  rw [← upgradeAt_code P k hk, List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem ht] at h1
  split
  · rename_i htk; rw [ite_eq_left htk] at h1; simpa using h1
  · rename_i htk; rw [ite_eq_right htk] at h1; simpa using h1

/-! ## The use at tick `k` -/

/-- The cells of `q`. -/
def qCells (q : Place) : Cells := fun l o => decide (l = q.base ∧ q.off ≤ o ∧ o < q.off + q.len)

theorem copy_move_deinit (P : Prog) (s : St) (q : Place) (ha : s.alias = none) (s1 : St)
    (vs : List Val) (h : evalOp .deinit P s (.copy q) = (s1, some vs)) :
    evalOp .deinit P s (.move q) = (writeCells s1 q.base q.off (List.replicate q.len .uninit), some vs) ∧
    Rel (qCells q) s1 (writeCells s1 q.base q.off (List.replicate q.len .uninit)) ∧
    vs.length = q.len ∧
    ∃ L, s1.log = s.log ++ L ∧ ∀ e ∈ L, e.tick = s.tick ∧ e.inCall = s.inCall := by
  simp only [evalOp] at h ⊢
  rcases hr : resolvePlace P s q with _ | r
  · rw [hr] at h; simp at h
  · rw [hr] at h
    have hrq := resolvePlace_eq_of_none ha hr
    subst hrq
    simp only at h ⊢
    rw [h]
    simp only [↓reduceIte, true_and]
    refine ⟨?_, readCells_len h, ?_⟩
    · refine rel_intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [writeCells, writeCellsK_eq]
      intro l o
      simp only [qCells, List.length_replicate, decide_eq_true_eq]
      split
      · rw [getD_replicate_uninit]
      · rfl
    · have hst := step_readCells s r.base r.off r.len
      rw [h] at hst
      obtain ⟨d, hd, he⟩ := hst.log
      exact ⟨d, hd, he⟩

theorem evalOp_none_stuck (ms : MoveSem) (P : Prog) (s : St) (o : Operand) (s1 : St)
    (h : evalOp ms P s o = (s1, none)) : s1.status ≠ .running := by
  have := (G_evalOp (fun _ => True) ms P s o (trivPtrs s)).2.1
  rw [h] at this; exact this rfl

theorem allocate_locs (P : Prog) (s : St) (x : Nat) :
    ∃ d, (allocate P s x).log = s.log ++ d ∧ ∀ e ∈ d, e.loc = x := by
  unfold allocate
  split
  · rw [resetCells, writeCellsK_eq]
    refine ⟨_, rfl, fun e he => ?_⟩
    simp only [List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he; rfl
  · exact ⟨[], by simp [St.fail], by simp⟩

theorem deallocate_locs (P : Prog) (s : St) (x : Nat) :
    ∃ d, (deallocate P s x).log = s.log ++ d ∧ ∀ e ∈ d, e.loc = x := by
  unfold deallocate
  split
  · simp only [resetCells, writeCellsK_eq]
    refine ⟨_, rfl, fun e he => ?_⟩
    simp only [List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he; rfl
  · exact ⟨[], by simp, by simp⟩

theorem writeCellsK_locs (k : AccKind) (s : St) (loc off : Nat) (vs : List Val) :
    ∃ d, (writeCellsK k s loc off vs).log = s.log ++ d ∧
      ∀ e ∈ d, e.loc = loc ∧ off ≤ e.off ∧ e.off < off + vs.length := by
  rw [writeCellsK_eq]
  refine ⟨_, rfl, fun e he => ?_⟩
  simp only [List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact ⟨rfl, by simp only; omega, by simp only; omega⟩

theorem running_of_execStmt {sem : Sem} {P : Prog} {A : Layout} {s : St} {st : Stmt}
    (h : (execStmt sem P A s st).status = .running) : s.status = .running := by
  cases hs : s.status with
  | running => rfl
  | ub => rw [execStmt_of_not_running _ (by rw [hs]; decide), hs] at h; cases h

/-- The effect of the upgraded statement at tick `k`, relative to the original one. -/
def BaseRes (k0 : Nat) (q : Place) (s t t' : St) : Prop :=
  ∃ L D, t.log = s.log ++ L ++ D ∧
    (∀ e ∈ L, e.tick = k0 ∧ e.inCall = false) ∧
    (∀ e ∈ D, qCells q e.loc e.off = true → e.tick = k0 ∧ e.inCall = true) ∧
    ((OK (qCells q) D ∧ Rel ((qCells q).after D) t t') ∨
     (Bad (qCells q) D ∧ t'.status = .ub ∧ Sub t' t))

theorem base_out (am : AssignMode) (P : Prog) (A : Layout) (s : St) (q : Place)
    (ha : s.alias = none) (hc : s.inCall = false)
    (hrun : (execStmt ⟨.deinit, am⟩ P A s (.out (.copy q))).status = .running) :
    BaseRes s.tick q s (execStmt ⟨.deinit, am⟩ P A s (.out (.copy q)))
      (execStmt ⟨.deinit, am⟩ P A s (.out (.move q))) := by
  have hs : s.status = .running := running_of_execStmt hrun
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)] at hrun ⊢
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)]
  unfold execBasic at hrun ⊢
  simp only [hs, ne_eq, not_true_eq_false, ↓reduceIte] at hrun ⊢
  rcases he : evalOp MoveSem.deinit P s (.copy q) with ⟨s1, _ | vs⟩
  · rw [he] at hrun; exact absurd hrun (evalOp_none_stuck _ _ _ _ _ he)
  · obtain ⟨hm, hrel, -, L, hL, hLe⟩ := copy_move_deinit P s q ha s1 vs he
    rw [hm]
    simp only
    refine ⟨L, [], by simp [St.emit, hL], fun e h => ⟨(hLe e h).1, by rw [(hLe e h).2, hc]⟩,
      by simp, Or.inl ⟨ok_nil _, ?_⟩⟩
    rw [after_nil]; exact hrel.emit _

theorem base_write (s s1 : St) (q lhs : Place) (vs' : List Val)
    (hdisj : WindowsDisjoint lhs q) (hlen : lhs.len = q.len) (hvl : vs'.length = q.len)
    (hrel : Rel (qCells q) s1 (writeCells s1 q.base q.off (List.replicate q.len .uninit)))
    (L : List Access) (hL : s1.log = s.log ++ L) (hLe : ∀ e ∈ L, e.tick = s.tick ∧ e.inCall = false) :
    BaseRes s.tick q s (writeCells s1 lhs.base lhs.off vs')
      (writeCells (writeCells s1 q.base q.off (List.replicate q.len .uninit)) lhs.base lhs.off vs') := by
  obtain ⟨dW, hdW, hok, hR⟩ := sim_writeCellsK hrel .write (by decide) lhs.base lhs.off vs'
  obtain ⟨dW', hdW', hlocs⟩ := writeCellsK_locs .write s1 lhs.base lhs.off vs'
  have : dW' = dW := by
    rw [hdW] at hdW'; exact (List.append_cancel_left hdW').symm
  subst this
  refine ⟨L, dW', ?_, hLe, ?_, Or.inl ⟨hok, hR⟩⟩
  · show (writeCellsK .write s1 lhs.base lhs.off vs').log = _
    rw [hdW, hL]
  intro e he hq
  exfalso
  obtain ⟨h1, h2, h3⟩ := hlocs e he
  simp only [qCells, decide_eq_true_eq] at hq
  unfold WindowsDisjoint at hdisj
  omega

theorem base_assign (am : AssignMode) (P : Prog) (A : Layout) (s : St) (q lhs : Place)
    (hdisj : WindowsDisjoint lhs q) (ha : s.alias = none) (hc : s.inCall = false)
    (hrun : (execStmt ⟨.deinit, am⟩ P A s (.assign lhs [.copy q])).status = .running) :
    BaseRes s.tick q s (execStmt ⟨.deinit, am⟩ P A s (.assign lhs [.copy q]))
      (execStmt ⟨.deinit, am⟩ P A s (.assign lhs [.move q])) := by
  have hs : s.status = .running := running_of_execStmt hrun
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)] at hrun ⊢
  rw [execStmt_of_not_call _ _ _ _ _ (by intros; simp)]
  unfold execBasic at hrun ⊢
  simp only [hs, ne_eq, not_true_eq_false, ↓reduceIte, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Operand.len, Nat.add_zero] at hrun ⊢
  by_cases hsum0 : ¬ q.len = lhs.len
  · rw [ite_eq_left hsum0] at hrun; simp [St.fail] at hrun
  rw [ite_eq_right hsum0] at hrun ⊢
  have hsum : q.len = lhs.len := by omega
  rcases hr : resolvePlace P s lhs with _ | r
  · rw [hr] at hrun; simp [St.fail] at hrun
  rw [hr] at hrun
  have hrl := resolvePlace_eq_of_none ha hr
  subst hrl
  simp only at hrun ⊢
  rcases he : evalOp MoveSem.deinit P s (.copy q) with ⟨s1, _ | vs⟩
  · cases am <;> simp only [evalOps, writeInOrder, he] at hrun <;>
      exact absurd hrun (evalOp_none_stuck _ _ _ _ _ he)
  obtain ⟨hm, hrel, hvl, L, hL, hLe⟩ := copy_move_deinit P s q ha s1 vs he
  have hLe' : ∀ e ∈ L, e.tick = s.tick ∧ e.inCall = false :=
    fun e h => ⟨(hLe e h).1, by rw [(hLe e h).2, hc]⟩
  rw [ite_eq_right (show ¬¬q.len = r.len from fun h => h hsum)]
  cases am
  · simp only [evalOps, he, hm]
    exact base_write s s1 q r (vs ++ []) hdisj hsum.symm (by simp [hvl]) hrel L hL hLe'
  · simp only [writeInOrder, he, hm]
    exact base_write s s1 q r vs hdisj hsum.symm hvl hrel L hL hLe'

theorem base_call (am : AssignMode) (P : Prog) (A : Layout) (s : St) (q : Place) (fn : Nat)
    (hprm : (P.fn fn).prm ≠ q.base) (ha : s.alias = none) (hc : s.inCall = false)
    (hrun : (execStmt ⟨.deinit, am⟩ P A s (.call fn (.copy q))).status = .running) :
    BaseRes s.tick q s (execStmt ⟨.deinit, am⟩ P A s (.call fn (.copy q)))
      (execStmt ⟨.deinit, am⟩ P A s (.call fn (.move q))) := by
  have hs : s.status = .running := running_of_execStmt hrun
  unfold execStmt at hrun ⊢
  simp only [hs, ne_eq, not_true_eq_false, ↓reduceIte] at hrun ⊢
  rcases he : evalOp MoveSem.deinit P s (.copy q) with ⟨s1, _ | vs⟩
  · rw [he] at hrun; exact absurd hrun (evalOp_none_stuck _ _ _ _ _ he)
  obtain ⟨hm, hrel, hvl, L, hL, hLe⟩ := copy_move_deinit P s q ha s1 vs he
  simp only [he] at hrun
  simp only [hm]
  by_cases hif : ¬vs.length = P.size (P.fn fn).prm ∨ s1.live (P.fn fn).prm = true
  · rw [ite_eq_left hif] at hrun; simp [St.fail] at hrun
  rw [ite_eq_right hif] at hrun ⊢
  rw [ite_eq_right (by rwa [← hrel.live])]
  simp only [writeCells] at hrel ⊢
  obtain ⟨d2, hd2, ok2, R2⟩ := sim_allocate hrel P (P.fn fn).prm
  obtain ⟨d3, hd3, ok3, R3⟩ := sim_writeCellsK R2 .write (by decide) (P.fn fn).prm 0 vs
  obtain ⟨d4, hd4, hgb⟩ := sim_execCallee (R3.setInCall true) ⟨.deinit, am⟩ P A (P.fn fn).body
  obtain ⟨d2', hd2', hl2⟩ := allocate_locs P s1 (P.fn fn).prm
  obtain ⟨d3', hd3', hl3⟩ := writeCellsK_locs .write (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs
  have e2 : d2' = d2 := by rw [hd2] at hd2'; exact (List.append_cancel_left hd2').symm
  have e3 : d3' = d3 := by rw [hd3] at hd3'; exact (List.append_cancel_left hd3').symm
  subst e2 e3
  have hstep4 := step_execCallee ⟨.deinit, am⟩ P A
    { writeCellsK .write (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
    (P.fn fn).body
  obtain ⟨d4', hd4', hl4⟩ := hstep4.log
  have e4 : d4' = d4 := by rw [hd4] at hd4'; exact (List.append_cancel_left hd4').symm
  subst e4
  have htick : (writeCellsK .write (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).tick =
      s.tick := by
    rw [(step_writeCellsK _ _ _ _ _).tick, (step_allocate _ _ _).tick]
    have := (step_evalOp .deinit P s (.copy q)).tick; rw [he] at this; exact this
  obtain ⟨d5, hd5, hl5⟩ := deallocate_locs P
    { execCallee ⟨.deinit, am⟩ P A
      { writeCellsK .write (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with inCall := true }
      (P.fn fn).body with inCall := false } (P.fn fn).prm
  have hLe' : ∀ e ∈ L, e.tick = s.tick ∧ e.inCall = false :=
    fun e h => ⟨(hLe e h).1, by rw [(hLe e h).2, hc]⟩
  refine ⟨L, d2' ++ d3' ++ d4' ++ d5, ?_, hLe', ?_, ?_⟩
  · rw [hd5]
    show (execCallee _ P A _ _).log ++ d5 = _
    rw [hd4]
    show (writeCellsK .write (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).log ++ _ ++ d5 = _
    rw [hd3, hd2, hL]
    simp only [List.append_assoc]
  · intro e he' hq
    simp only [qCells, decide_eq_true_eq] at hq
    rcases List.mem_append.1 he' with he' | he'
    · rcases List.mem_append.1 he' with he' | he'
      · rcases List.mem_append.1 he' with he' | he'
        · exact absurd (hl2 e he') (by rw [hq.1]; exact fun h => hprm h.symm)
        · exact absurd (hl3 e he').1 (by rw [hq.1]; exact fun h => hprm h.symm)
      · obtain ⟨h1, h2⟩ := hl4 e he'
        exact ⟨by rw [h1]; exact htick, h2⟩
    · exact absurd (hl5 e he') (by rw [hq.1]; exact fun h => hprm h.symm)
  · rcases hgb with ⟨ok4, R4⟩ | ⟨bad4, hst4, hsub4⟩
    · obtain ⟨d5', hd5', ok5, R5⟩ := sim_deallocate (R4.setInCall false) P (P.fn fn).prm
      have e5 : d5' = d5 := by rw [hd5] at hd5'; exact (List.append_cancel_left hd5').symm
      subst e5
      left
      refine ⟨?_, ?_⟩
      · rw [List.append_assoc, List.append_assoc]
        exact ok_append ok2 (ok_append ok3 (ok_append ok4 ok5))
      · simp only [Cells.after_append]; exact R5
    · right
      refine ⟨?_, ?_, ?_⟩
      · refine bad_append_left (bad_append_right (d2' ++ d3') ?_) d5
        rw [Cells.after_append]; exact bad4
      · rw [deallocate_status]; exact hst4
      · intro c hc'
        rw [deallocate_conflicts] at hc' ⊢
        exact hsub4 c hc'

/-! ## The whole run -/

/-- Invariant relating the source and the upgraded run after the use at tick `k`: the source log
splits into entries before the use and entries `D` after it, and either no cell of `q` is first
read in `D` and the target equals the source except for the untouched cells of `q`, or some cell
of `q` is first read in `D` and the target has failed. -/
def DInv (k : Nat) (q : Place) (s s' : St) : Prop :=
  ∃ L D, s.log = L ++ D ∧ (∀ e ∈ L, afterUse true k e = false) ∧
    (∀ e ∈ D, qCells q e.loc e.off = true → afterUse true k e = true) ∧
    ((OK (qCells q) D ∧ Rel ((qCells q).after D) s s') ∨
     (Bad (qCells q) D ∧ s'.status = .ub ∧ Sub s' s))

theorem upgradeSite_lt {P : Prog} {k : Nat} {q : Place} (hsite : UpgradeSite P k q) :
    k < P.body.length := by
  rcases hsite with ⟨_, h, _⟩ | ⟨_, h, _⟩ | h <;>
    exact (List.getElem?_eq_some_iff.1 h).1

theorem dinv_base (am : AssignMode) (P : Prog) (k : Nat) (q : Place) (hsite : UpgradeSite P k q)
    (A : Layout) (hrun : (runAt ⟨.deinit, am⟩ P A (k + 1)).status = .running) :
    DInv k q (runAt ⟨.deinit, am⟩ P A (k + 1)) (runAt ⟨.deinit, am⟩ (P.upgradeAt k) A (k + 1)) := by
  have hk := upgradeSite_lt hsite
  have hkc : k < P.code.length := by simp only [Prog.code, List.length_append]; omega
  have hcode : P.code[k] = P.body[k] := by
    simp only [Prog.code]; exact List.getElem_append_left hk
  rw [runAt_upgradeAt_succ _ P k hk A k hkc, ite_eq_left rfl, runAt_upgradeAt_le _ P k hk A k (Nat.le_refl _)]
  rw [runAt_succ _ _ _ _ hkc] at hrun ⊢
  obtain ⟨htk, hc, ha, hlt⟩ := runAt_frame ⟨.deinit, am⟩ P A k (by omega)
  have hrun' : (execStmt ⟨.deinit, am⟩ P A (runAt ⟨.deinit, am⟩ P A k) P.code[k]).status =
      .running := hrun
  have hres : BaseRes (runAt ⟨.deinit, am⟩ P A k).tick q (runAt ⟨.deinit, am⟩ P A k)
      (execStmt ⟨.deinit, am⟩ P A (runAt ⟨.deinit, am⟩ P A k) P.code[k])
      (execStmt ⟨.deinit, am⟩ P A (runAt ⟨.deinit, am⟩ P A k) P.code[k].upgradeCopy) := by
    rw [hcode] at hrun' ⊢
    rcases hsite with ⟨lhs, h, hdisj⟩ | ⟨fn, h, hprm⟩ | h
    · rw [List.getElem?_eq_getElem hk, Option.some.injEq] at h
      rw [h] at hrun' ⊢
      exact base_assign am P A _ q lhs hdisj ha hc hrun'
    · rw [List.getElem?_eq_getElem hk, Option.some.injEq] at h
      rw [h] at hrun' ⊢
      exact base_call am P A _ q fn hprm ha hc hrun'
    · rw [List.getElem?_eq_getElem hk, Option.some.injEq] at h
      rw [h] at hrun' ⊢
      exact base_out am P A _ q ha hc hrun'
  rw [htk] at hres
  obtain ⟨L, D, hlog, hL, hD, hgb⟩ := hres
  refine ⟨(runAt ⟨.deinit, am⟩ P A k).log ++ L, D, hlog, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · have := hlt e he; simp [afterUse]; omega
    · obtain ⟨h1, h2⟩ := hL e he; simp [afterUse, h1, h2]
  · intro e he hq
    obtain ⟨h1, h2⟩ := hD e he hq; simp [afterUse, h1, h2]
  · rcases hgb with ⟨hok, hR⟩ | ⟨hbad, hst, hsub⟩
    · left; refine ⟨hok, ?_⟩
      show Rel _ { execStmt _ P A _ _ with tick := _ } { execStmt _ P A _ _ with tick := _ }
      rw [← hR.tick]; exact hR.setTick _
    · right; exact ⟨hbad, hst, hsub⟩

theorem runAt_stuck_mono (sem : Sem) (P : Prog) (A : Layout) (t : Nat)
    (h : (runAt sem P A t).status ≠ .running) (n : Nat) :
    (runAt sem P A (t + n)).status ≠ .running := by
  induction n with
  | zero => exact h
  | succ n ih => exact (runAt_succ_stuck sem P A (t + n) ih).2

theorem dinv_step (am : AssignMode) (P : Prog) (k : Nat) (q : Place) (hk : k < P.body.length)
    (A : Layout) (t : Nat) (hkt : k < t) (ht : t < P.code.length)
    (h : DInv k q (runAt ⟨.deinit, am⟩ P A t) (runAt ⟨.deinit, am⟩ (P.upgradeAt k) A t)) :
    DInv k q (runAt ⟨.deinit, am⟩ P A (t + 1)) (runAt ⟨.deinit, am⟩ (P.upgradeAt k) A (t + 1)) := by
  obtain ⟨d0, hd0, ht0⟩ := runAt_succ_log ⟨.deinit, am⟩ P A t ht
  rw [runAt_upgradeAt_succ _ P k hk A t ht, ite_eq_right (by omega)]
  rw [runAt_succ _ _ _ _ ht] at hd0 ⊢
  obtain ⟨L, D, hlog, hL, hD, hgb⟩ := h
  have hd0' : ∀ e ∈ d0, afterUse true k e = true := by
    intro e he; have := ht0 e he; simp [afterUse]; omega
  have hlog' : (execTop ⟨.deinit, am⟩ P A (runAt ⟨.deinit, am⟩ P A t) P.code[t]).log =
      L ++ (D ++ d0) := by rw [hd0, hlog, List.append_assoc]
  refine ⟨L, D ++ d0, hlog', hL, ?_, ?_⟩
  · intro e he hq
    rcases List.mem_append.1 he with he | he
    · exact hD e he hq
    · exact hd0' e he
  · rcases hgb with ⟨hok, hR⟩ | ⟨hbad, hst, hsub⟩
    · obtain ⟨d, hd, hgb'⟩ := sim_execTop hR ⟨.deinit, am⟩ P A P.code[t]
      have : d = d0 := by rw [hd0] at hd; exact (List.append_cancel_left hd).symm
      subst this
      rcases hgb' with ⟨hok', hR'⟩ | ⟨hbad', hst', hsub'⟩
      · left
        refine ⟨ok_append hok hok', ?_⟩
        rw [Cells.after_append]; exact hR'
      · right
        exact ⟨bad_append_right D hbad', hst', hsub'⟩
    · right
      obtain ⟨hst', hsub'⟩ := fail_execTop hst hsub ⟨.deinit, am⟩ P A P.code[t]
      exact ⟨bad_append_left hbad d0, hst', hsub'⟩

theorem dinv_run (am : AssignMode) (P : Prog) (k : Nat) (q : Place) (hsite : UpgradeSite P k q)
    (A : Layout) (hrun : (run ⟨.deinit, am⟩ P A).status = .running) :
    DInv k q (run ⟨.deinit, am⟩ P A) (run ⟨.deinit, am⟩ (P.upgradeAt k) A) := by
  have hk := upgradeSite_lt hsite
  have hkc : k < P.code.length := by simp only [Prog.code, List.length_append]; omega
  have hTl : (P.upgradeAt k).code.length = P.code.length := by
    rw [upgradeAt_code P k hk, modifyAt_length]
  have hrunk : (runAt ⟨.deinit, am⟩ P A (k + 1)).status = .running := by
    cases h : (runAt ⟨.deinit, am⟩ P A (k + 1)).status with
    | running => rfl
    | ub =>
      have := runAt_stuck_mono ⟨.deinit, am⟩ P A (k + 1) (by rw [h]; decide)
        (P.code.length - (k + 1))
      rw [show k + 1 + (P.code.length - (k + 1)) = P.code.length by omega, ← run_eq_runAt] at this
      exact absurd hrun this
  have key : ∀ n, k + 1 + n ≤ P.code.length →
      DInv k q (runAt ⟨.deinit, am⟩ P A (k + 1 + n))
        (runAt ⟨.deinit, am⟩ (P.upgradeAt k) A (k + 1 + n)) := by
    intro n
    induction n with
    | zero => intro _; exact dinv_base am P k q hsite A hrunk
    | succ n ih =>
      intro hn
      rw [show k + 1 + (n + 1) = (k + 1 + n) + 1 by omega]
      exact dinv_step am P k q hk A _ (by omega) (by omega) (ih (by omega))
  have := key (P.code.length - (k + 1)) (by omega)
  rw [show k + 1 + (P.code.length - (k + 1)) = P.code.length by omega] at this
  rw [run_eq_runAt, run_eq_runAt, hTl]
  exact this

theorem noRead_iff_ok (k : Nat) (q : Place) (L D : List Access)
    (hL : ∀ e ∈ L, afterUse true k e = false)
    (hD : ∀ e ∈ D, qCells q e.loc e.off = true → afterUse true k e = true) :
    NoReadBeforeReinit (L ++ D) k true q ↔ OK (qCells q) D := by
  have key : ∀ j, j < q.len →
      firstTouchNotRead (afterUse true k) q.base (q.off + j) (L ++ D) = ft q.base (q.off + j) D := by
    intro j hj
    rw [firstTouchNotRead_skip _ _ _ hL, firstTouchNotRead_all]
    intro e he h1 h2
    exact hD e he (by simp only [qCells, decide_eq_true_eq]; exact ⟨h1, by omega, by omega⟩)
  constructor
  · intro h l o hx
    simp only [qCells, decide_eq_true_eq] at hx
    have := h (o - q.off) (by omega)
    rw [key _ (by omega), show q.off + (o - q.off) = o by omega, ← hx.1] at this
    exact this
  · intro h j hj
    rw [key j hj]
    exact h q.base (q.off + j) (by simp only [qCells, decide_eq_true_eq]; exact ⟨trivial, by omega, by omega⟩)

theorem not_ok_of_bad {X : Cells} {d : List Access} (h : Bad X d) : ¬ OK X d := by
  obtain ⟨l, o, hx, hf⟩ := h
  intro hok; rw [hok l o hx] at hf; cases hf

theorem layoutOK_upgradeAt (P : Prog) (k : Nat) (A : Layout) (cs : List (Nat × Nat)) :
    layoutOK (P.upgradeAt k) A cs = layoutOK P A cs := rfl

theorem outcome_upgradeAt_eq_of_rel (sem : Sem) (P : Prog) (k : Nat) (A : Layout) {X : Cells}
    (h : Rel X (run sem P A) (run sem (P.upgradeAt k) A)) :
    outcome sem (P.upgradeAt k) A = outcome sem P A := by
  dsimp only [outcome]
  rw [layoutOK_upgradeAt, ← h.conflicts, ← h.status, ← h.trace]

theorem outcome_upgradeAt_ub (sem : Sem) (P : Prog) (k : Nat) (A : Layout)
    (hst : (run sem (P.upgradeAt k) A).status = .ub)
    (hsub : Sub (run sem (P.upgradeAt k) A) (run sem P A))
    (hlay : layoutOK P A (run sem P A).conflicts = true) :
    outcome sem (P.upgradeAt k) A = .ub := by
  dsimp only [outcome]
  rw [layoutOK_upgradeAt, layoutOK_of_subset P A hsub hlay, hst]
  rfl

end Toy.Coalesce.Obs

namespace Toy.Coalesce

/-- Soundness of the certificate: if `O` is a certificate and `q.base ∉ O (k+1)`, then on every
layout, under every semantics, no cell of `q` is read at a tick after `k` before it is written or
reset (the no-read-before-re-initialization condition restricted to later ticks). -/
theorem noReadBeforeReinit_of_obsCert (sem : Sem) (P : Prog) (O : ObsMask) (hcert : ObsCert P O)
    (k : Nat) (q : Place) (hO : O (k + 1) q.base = false) (A : Layout) :
    NoReadBeforeReinit (run sem P A).log k false q := by
  intro j hj
  by_cases hc : q.off + j < P.size q.base
  · by_cases hk : k + 1 ≤ P.code.length
    · obtain ⟨E, hE, hpre, hpost⟩ := run_log_split sem P A (k + 1) hk
      rw [hE, Obs.firstTouchNotRead_skip _ _ _ (fun e he => by
          have := hpre e he; simp [afterUse]; omega)]
      rw [Obs.firstTouchNotRead_all _ _ _ (fun e he _ _ => by
          have := hpost e he; simp [afterUse]; omega)]
      exact Obs.T1_back sem P O hcert A q.base (q.off + j) hc k (P.code.length - (k + 1)) (k + 1)
        (by omega) (by omega) (Or.inl hO) E hE
    · have hall : ∀ e ∈ (run sem P A).log, afterUse false k e = false := by
        intro e he
        have := (runAt_frame sem P A P.code.length (Nat.le_refl _)).2.2.2 e
          (by rw [← run_eq_runAt]; exact he)
        simp [afterUse]; omega
      have := Obs.firstTouchNotRead_skip (afterUse false k) q.base (q.off + j) hall []
      rw [List.append_nil] at this
      rw [this]; rfl
  · apply Obs.firstTouchNotRead_of_noRead
    intro e he hl ho _
    have := Obs.runAt_inBounds sem P A P.code.length e (by rw [← run_eq_runAt]; exact he)
    rw [hl, ho] at this; exact hc this

/-- Under `MoveSem.deinit`, for an upgrade site and a layout on which the source run is neither
excluded nor undefined: the upgraded program has the same outcome iff no cell of `q` is read
after the use before it is re-initialized (reads inside the callee of a call site, through
pointers, and in the destructor block included). -/
theorem upgrade_moveDeinit_outcome_eq_iff_noReadBeforeReinit (am : AssignMode) (P : Prog)
    (k : Nat) (q : Place) (hsite : UpgradeSite P k q) (A : Layout)
    (hub : outcome ⟨.deinit, am⟩ P A ≠ .ub) (hbad : outcome ⟨.deinit, am⟩ P A ≠ .badLayout) :
    outcome ⟨.deinit, am⟩ (P.upgradeAt k) A = outcome ⟨.deinit, am⟩ P A ↔
      NoReadBeforeReinit (run ⟨.deinit, am⟩ P A).log k true q := by
  have hlay : layoutOK P A (run ⟨.deinit, am⟩ P A).conflicts = true := layoutOK_of_outcome_ne hbad
  have hrun : (run ⟨.deinit, am⟩ P A).status = .running := by
    cases h : (run ⟨.deinit, am⟩ P A).status with
    | running => rfl
    | ub =>
      exfalso; apply hub
      unfold outcome; simp [hlay, h]
  obtain ⟨L, D, hlog, hL, hD, hgb⟩ := Obs.dinv_run am P k q hsite A hrun
  rw [hlog, Obs.noRead_iff_ok k q L D hL hD]
  rcases hgb with ⟨hok, hrel⟩ | ⟨hbad', hst, hsub⟩
  · exact ⟨fun _ => hok, fun _ => Obs.outcome_upgradeAt_eq_of_rel _ P k A hrel⟩
  · refine ⟨fun heq => ?_, fun hok => absurd hok (Obs.not_ok_of_bad hbad')⟩
    rw [Obs.outcome_upgradeAt_ub _ P k A hst hsub hlay] at heq
    exact absurd heq.symm hub

/-- Under `MoveSem.deinit`, if no cell of `q` is read after the use before re-initialization on
every layout whose source run is neither excluded nor undefined, the upgrade is a refinement. -/
theorem upgrade_moveDeinit_refines_of_noReadBeforeReinit (am : AssignMode) (P : Prog)
    (k : Nat) (q : Place) (hsite : UpgradeSite P k q)
    (hno : ∀ A, outcome ⟨.deinit, am⟩ P A ≠ .ub → outcome ⟨.deinit, am⟩ P A ≠ .badLayout →
      NoReadBeforeReinit (run ⟨.deinit, am⟩ P A).log k true q) :
    Refines ⟨.deinit, am⟩ (P.upgradeAt k) ⟨.deinit, am⟩ P := by
  apply refines_of_running
  intro A hA hrunAll
  obtain ⟨L, D, hlog, hL, hD, hgb⟩ := Obs.dinv_run am P k q hsite A (hrunAll A)
  have hno' : NoReadBeforeReinit (run ⟨.deinit, am⟩ P A).log k true q := by
    have hgood := hno (goodLayout P)
      (by rw [outcome_of_running (layoutOK_goodLayout_run _ _ _) (hrunAll _)]; simp)
      (outcome_goodLayout_ne_badLayout _ _)
    rw [(run_teq ⟨.deinit, am⟩ P A (goodLayout P)).log]
    exact hgood
  rw [hlog, Obs.noRead_iff_ok k q L D hL hD] at hno'
  rcases hgb with ⟨-, hrel⟩ | ⟨hbad', -, -⟩
  · have heq := Obs.outcome_upgradeAt_eq_of_rel _ P k A hrel
    exact ⟨A, heq.symm, hA⟩
  · exact absurd hno' (Obs.not_ok_of_bad hbad')

end Toy.Coalesce
