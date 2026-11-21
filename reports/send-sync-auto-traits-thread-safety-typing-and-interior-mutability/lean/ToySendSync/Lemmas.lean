import ToySendSync.Model

/-!
# Algebra of races over capability footprints

Decomposition lemmas used by the results: races over appended lists, relocation
invariance, independence of root claims from relocated claims, and a handful of
concrete compatibility facts about root claims.
-/

namespace Toy.SendSync

/-! ## Races over lists -/

theorem race_append_left (B₁ B₂ A : List Ev) :
    Race (B₁ ++ B₂) A ↔ Race B₁ A ∨ Race B₂ A := by
  unfold Race
  constructor
  · rintro ⟨e₁, h₁, e₂, h₂, hc⟩
    rcases List.mem_append.mp h₁ with h | h
    · exact Or.inl ⟨e₁, h, e₂, h₂, hc⟩
    · exact Or.inr ⟨e₁, h, e₂, h₂, hc⟩
  · rintro (⟨e₁, h₁, e₂, h₂, hc⟩ | ⟨e₁, h₁, e₂, h₂, hc⟩)
    · exact ⟨e₁, List.mem_append.mpr (Or.inl h₁), e₂, h₂, hc⟩
    · exact ⟨e₁, List.mem_append.mpr (Or.inr h₁), e₂, h₂, hc⟩

theorem race_append_right (B A₁ A₂ : List Ev) :
    Race B (A₁ ++ A₂) ↔ Race B A₁ ∨ Race B A₂ := by
  unfold Race
  constructor
  · rintro ⟨e₁, h₁, e₂, h₂, hc⟩
    rcases List.mem_append.mp h₂ with h | h
    · exact Or.inl ⟨e₁, h₁, e₂, h, hc⟩
    · exact Or.inr ⟨e₁, h₁, e₂, h, hc⟩
  · rintro (⟨e₁, h₁, e₂, h₂, hc⟩ | ⟨e₁, h₁, e₂, h₂, hc⟩)
    · exact ⟨e₁, h₁, e₂, List.mem_append.mpr (Or.inl h₂), hc⟩
    · exact ⟨e₁, h₁, e₂, List.mem_append.mpr (Or.inr h₂), hc⟩

theorem race_mono {B B' A A' : List Ev} (hB : ∀ e ∈ B, e ∈ B') (hA : ∀ e ∈ A, e ∈ A') :
    Race B A → Race B' A' := by
  rintro ⟨e₁, h₁, e₂, h₂, hc⟩
  exact ⟨e₁, hB e₁ h₁, e₂, hA e₂ h₂, hc⟩

theorem not_race_of_no_conflict {B A : List Ev}
    (h : ∀ e₁ ∈ B, ∀ e₂ ∈ A, ¬ Conflicting e₁ e₂) : ¬ Race B A := by
  rintro ⟨e₁, h₁, e₂, h₂, hc, _⟩
  exact h e₁ h₁ e₂ h₂ hc

theorem race_nil_right (B : List Ev) : ¬ Race B [] := by
  rintro ⟨_, _, _, h, _⟩
  cases h

theorem race_nil_left (A : List Ev) : ¬ Race [] A := by
  rintro ⟨_, h, _⟩
  cases h

/-! ## No foreign release over lists -/

theorem nfr_nil (t : Tid) : NoForeignRelease t [] := fun _ h => by cases h

theorem nfr_of_no_rel {t : Tid} {L : List Ev} (h : ∀ e ∈ L, e.kind ≠ .rel) :
    NoForeignRelease t L := fun e he _ hk _ => absurd hk (h e he)

theorem nfr_append (t : Tid) (L₁ L₂ : List Ev) :
    NoForeignRelease t (L₁ ++ L₂) ↔ NoForeignRelease t L₁ ∧ NoForeignRelease t L₂ := by
  unfold NoForeignRelease
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append.mpr (Or.inl he)),
      fun e he => h e (List.mem_append.mpr (Or.inr he))⟩
  · rintro ⟨h₁, h₂⟩ e he
    rcases List.mem_append.mp he with h | h
    · exact h₁ e h
    · exact h₂ e h

theorem nfr_mono {t : Tid} {L L' : List Ev} (h : ∀ e ∈ L, e ∈ L') :
    NoForeignRelease t L' → NoForeignRelease t L := fun h' e he => h' e (h e he)

theorem acq_maker_reloc (t : Tid) (i : Nat) (a : Acq) : (a.reloc i).maker t = a.maker t := by
  cases a <;> rfl

theorem nfr_place (t : Tid) (r : List Claim) (hr : ∀ c ∈ r, c.path = []) (i : Nat) (L : List Ev) :
    NoForeignRelease t (place r i L) ↔ NoForeignRelease t L := by
  unfold NoForeignRelease place
  constructor
  · intro h e he a hk hm
    have := h (e.place r i) (List.mem_map.mpr ⟨e, he, rfl⟩) (a.reloc i) hk
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hm, rfl⟩)))
    rwa [acq_maker_reloc] at this
  · intro h e' he' a hk hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    rcases List.mem_append.mp hm with hm | hm
    · have := hr _ hm
      simp [Claim.path, Ev.place] at this
    · obtain ⟨c, hc, hce⟩ := List.mem_map.mp hm
      cases c with
      | held p a' =>
        simp only [Claim.reloc, Ev.place, Claim.held.injEq, List.cons.injEq] at hce
        obtain ⟨⟨_, rfl⟩, rfl⟩ := hce
        rw [acq_maker_reloc]
        exact h e he a' hk hc
      | via p => simp [Claim.reloc] at hce
      | uniq p => simp [Claim.reloc] at hce

theorem place_subset {L L' : List Ev} (r : List Claim) (i : Nat) (h : ∀ e ∈ L, e ∈ L') :
    ∀ e ∈ place r i L, e ∈ place r i L' := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨e', h e' he', rfl⟩

theorem expose_subset (v : View) (L : List Ev) : ∀ e ∈ v.expose L, e ∈ L := by
  intro e he
  cases v with
  | full => exact he
  | readOnly => exact (List.mem_filter.mp he).1
  | none => cases he

theorem expose_readOnly_kind (L : List Ev) : ∀ e ∈ View.expose .readOnly L, e.kind = .rd := by
  intro e he
  have := (List.mem_filter.mp he).2
  simp only [Bool.and_eq_true] at this
  have h := this.1
  cases hk : e.kind <;> simp_all [Kind.isRead]

theorem expose_readOnly_append (L₁ L₂ : List Ev) :
    View.expose .readOnly (L₁ ++ L₂) = View.expose .readOnly L₁ ++ View.expose .readOnly L₂ :=
  List.filter_append _ _

theorem claim_isFresh_reloc (i : Nat) (c : Claim) : (c.reloc i).isFresh = c.isFresh := by
  cases c with
  | held p a => cases a <;> rfl
  | via p => rfl
  | uniq p => rfl

theorem acquires_place (r : List Claim) (i : Nat) (e : Ev) :
    (Ev.place r i e).acquires = (r.any Claim.isFresh || e.acquires) := by
  simp only [Ev.acquires, Ev.place, List.any_append, List.any_map]
  congr 1
  induction e.claims with
  | nil => rfl
  | cons c cs ih => simp only [List.any_cons, Function.comp, claim_isFresh_reloc] at ih ⊢; rw [ih]

theorem expose_readOnly_place (r : List Claim) (hr : r.any Claim.isFresh = false) (i : Nat)
    (L : List Ev) :
    View.expose .readOnly (place r i L) = place r i (View.expose .readOnly L) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [View.expose, place, List.map_cons, List.filter_cons] at ih ⊢
    have ha := acquires_place r i e
    rw [hr, Bool.false_or] at ha
    cases h : (e.kind.isRead && !e.acquires) <;> simp [Ev.place, ha, h, ih] at * <;> simp_all

/-- A read-only view exposes nothing that runs under an acquisition made by the executing
thread. -/
theorem expose_readOnly_place_fresh (i : Nat) (L : List Ev) :
    View.expose .readOnly (place [.held [] .fresh] i L) = [] := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [View.expose, place, List.map_cons, List.filter_cons] at ih ⊢
    have ha : (Ev.place [.held [] .fresh] i e).acquires = true := by
      rw [acquires_place]; rfl
    simp [ha, ih]

theorem not_race_expose_readOnly (L L' : List Ev) :
    ¬ Race (View.expose .readOnly L) (View.expose .readOnly L') := by
  apply not_race_of_no_conflict
  intro e₁ h₁ e₂ h₂ hc
  have hw := hc.2.2.2.1
  rw [expose_readOnly_kind L e₁ h₁, expose_readOnly_kind L' e₂ h₂] at hw
  simp [Kind.isWrite] at hw

theorem nfr_expose_readOnly (t : Tid) (L : List Ev) : NoForeignRelease t (View.expose .readOnly L) :=
  nfr_of_no_rel (fun e he => by rw [expose_readOnly_kind L e he]; decide)

/-! ## Snapshots and relocation -/

/-- Inverse of `Holder.reloc` on its image (junk elsewhere). -/
def Holder.unreloc (i : Nat) : Holder → Holder
  | .thread t => .thread t
  | .guard [] => .guard []
  | .guard (j :: g) => if j = i then .guard g else .guard (j :: g)

/-- The view of a snapshot from inside child `i`. -/
def Snap.unplace (i : Nat) (σ : Snap) : Snap where
  lock q := (σ.lock (i :: q)).map (Holder.unreloc i)
  holds q t := σ.holds (i :: q) t

/-- A snapshot agreeing with `σr` at the root path and with `σc`, relocated, under
child `i`. -/
def Snap.glue (i : Nat) (σr σc : Snap) : Snap where
  lock p := match p with
    | [] => σr.lock []
    | j :: q => if j = i then (σc.lock q).map (Holder.reloc i) else none
  holds p t := match p with
    | [] => σr.holds [] t
    | j :: q => if j = i then σc.holds q t else false

theorem holder_reloc_acq (i : Nat) (t : Tid) (a : Acq) :
    Holder.reloc i (a.holder t) = (a.reloc i).holder t := by
  cases a <;> rfl

theorem holder_unreloc_acq (i : Nat) (t : Tid) (a : Acq) :
    Holder.unreloc i ((a.reloc i).holder t) = a.holder t := by
  cases a <;> simp [Acq.reloc, Acq.holder, Holder.unreloc]

theorem sat_unplace {σ : Snap} {t : Tid} {i : Nat} {c : Claim} (h : Sat σ t (c.reloc i)) :
    Sat (σ.unplace i) t c := by
  cases c with
  | held p a =>
    simp only [Claim.reloc, Sat] at h
    simp only [Sat, Snap.unplace, h, Option.map_some, holder_unreloc_acq]
  | via p => simpa [Claim.reloc, Sat, Snap.unplace] using h
  | uniq p => simpa [Claim.reloc, Sat, Snap.unplace] using h

theorem sat_glue_reloc {σr σc : Snap} {t : Tid} {i : Nat} {c : Claim} (h : Sat σc t c) :
    Sat (Snap.glue i σr σc) t (c.reloc i) := by
  cases c with
  | held p a =>
    simp only [Sat] at h
    simp [Claim.reloc, Sat, Snap.glue, h, holder_reloc_acq]
  | via p => simpa [Claim.reloc, Sat, Snap.glue] using h
  | uniq p => simpa [Claim.reloc, Sat, Snap.glue] using h

theorem sat_glue_root {σr σc : Snap} {t : Tid} {i : Nat} {c : Claim} (hc : c.path = []) :
    Sat (Snap.glue i σr σc) t c ↔ Sat σr t c := by
  cases c with
  | held p a =>
    simp only [Claim.path] at hc
    subst hc
    simp [Sat, Snap.glue]
  | via p =>
    simp only [Claim.path] at hc
    subst hc
    simp [Sat, Snap.glue]
  | uniq p =>
    simp only [Claim.path] at hc
    subst hc
    simp [Sat, Snap.glue]

/-- Root claims and claims relocated under a child constrain disjoint parts of a
snapshot, so their joint satisfiability splits. -/
theorem compatible_place (i : Nat) (r₁ r₂ cs₁ cs₂ : List Claim)
    (h₁ : ∀ c ∈ r₁, c.path = []) (h₂ : ∀ c ∈ r₂, c.path = []) :
    Compatible (r₁ ++ cs₁.map (Claim.reloc i)) (r₂ ++ cs₂.map (Claim.reloc i)) ↔
      Compatible r₁ r₂ ∧ Compatible cs₁ cs₂ := by
  constructor
  · rintro ⟨σ, hA, hB⟩
    refine ⟨⟨σ, fun c hc => hA c (List.mem_append.mpr (Or.inl hc)),
        fun c hc => hB c (List.mem_append.mpr (Or.inl hc))⟩, ⟨σ.unplace i, ?_, ?_⟩⟩
    · intro c hc
      exact sat_unplace (hA _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c, hc, rfl⟩))))
    · intro c hc
      exact sat_unplace (hB _ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c, hc, rfl⟩))))
  · rintro ⟨⟨σr, hr₁, hr₂⟩, ⟨σc, hc₁, hc₂⟩⟩
    refine ⟨Snap.glue i σr σc, ?_, ?_⟩
    · intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact (sat_glue_root (h₁ c h)).mpr (hr₁ c h)
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
        exact sat_glue_reloc (hc₁ d hd)
    · intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact (sat_glue_root (h₂ c h)).mpr (hr₂ c h)
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
        exact sat_glue_reloc (hc₂ d hd)

theorem conflicting_place (r₁ r₂ : List Claim) (i j : Nat) (e₁ e₂ : Ev) :
    Conflicting (e₁.place r₁ i) (e₂.place r₂ j) ↔ i = j ∧ Conflicting e₁ e₂ := by
  simp only [Conflicting, Ev.place, List.cons.injEq]
  constructor
  · rintro ⟨⟨hij, hl⟩, h⟩
    exact ⟨hij, hl, h⟩
  · rintro ⟨hij, hl, h⟩
    exact ⟨⟨hij, hl⟩, h⟩

/-- Races between two relocated capability lists: they must sit under the same
child, the added root claims must be compatible, and the children must race. -/
theorem race_place (r₁ r₂ : List Claim) (i j : Nat) (B A : List Ev)
    (h₁ : ∀ c ∈ r₁, c.path = []) (h₂ : ∀ c ∈ r₂, c.path = []) :
    Race (place r₁ i B) (place r₂ j A) ↔ i = j ∧ Compatible r₁ r₂ ∧ Race B A := by
  unfold Race place
  constructor
  · rintro ⟨e₁', he₁', e₂', he₂', hconf', hconc⟩
    obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp he₁'
    obtain ⟨e₂, he₂, rfl⟩ := List.mem_map.mp he₂'
    obtain ⟨rfl, hconf⟩ := (conflicting_place r₁ r₂ i j e₁ e₂).mp hconf'
    obtain ⟨hr, hc⟩ := (compatible_place i r₁ r₂ e₁.claims e₂.claims h₁ h₂).mp hconc
    exact ⟨rfl, hr, e₁, he₁, e₂, he₂, hconf, hc⟩
  · rintro ⟨rfl, hr, e₁, he₁, e₂, he₂, hconf, hc⟩
    refine ⟨e₁.place r₁ i, List.mem_map.mpr ⟨e₁, he₁, rfl⟩, e₂.place r₂ i,
      List.mem_map.mpr ⟨e₂, he₂, rfl⟩, (conflicting_place r₁ r₂ i i e₁ e₂).mpr ⟨rfl, hconf⟩, ?_⟩
    exact (compatible_place i r₁ r₂ e₁.claims e₂.claims h₁ h₂).mpr ⟨hr, hc⟩

theorem not_race_root_place {R : List Ev} (hR : ∀ e ∈ R, e.loc = []) (r : List Claim) (i : Nat)
    (A : List Ev) : ¬ Race R (place r i A) := by
  rintro ⟨e₁, h₁, e₂, h₂, hc, _⟩
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp h₂
  have := hc.1
  rw [hR e₁ h₁] at this
  cases this

theorem not_race_place_root {R : List Ev} (hR : ∀ e ∈ R, e.loc = []) (r : List Claim) (i : Nat)
    (B : List Ev) : ¬ Race (place r i B) R := by
  rintro ⟨e₁, h₁, e₂, h₂, hc, _⟩
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp h₁
  have := hc.1
  rw [hR e₂ h₂] at this
  cases this

/-! ## Concrete compatibility facts for root claims -/

theorem compatible_nil_nil : Compatible [] [] :=
  ⟨⟨fun _ => none, fun _ _ => false⟩, (fun _ h => by cases h), (fun _ h => by cases h)⟩

/-- A snapshot satisfying one claim for a given thread. -/
def Snap.just (t : Tid) : Claim → Snap
  | .held _ a => ⟨fun _ => some (a.holder t), fun _ _ => false⟩
  | .via _ => ⟨fun _ => none, fun _ _ => true⟩
  | .uniq _ => ⟨fun _ => none, fun _ t' => t' == t⟩

theorem sat_just (t : Tid) (c : Claim) : Sat (Snap.just t c) t c := by
  cases c with
  | held p a => rfl
  | via p => rfl
  | uniq p => cases t <;> simp [Sat, Snap.just, Tid.flip]

theorem compatible_single_nil (c : Claim) : Compatible [c] [] :=
  ⟨Snap.just .other c, fun d hd => by
    rw [List.mem_singleton.mp hd]
    exact sat_just .other c, (fun _ h => by cases h)⟩

theorem compatible_via_via (p : Path) : Compatible [.via p] [.via p] :=
  ⟨⟨fun _ => none, fun _ _ => true⟩, fun d hd => by
    rw [List.mem_singleton.mp hd]
    rfl, fun d hd => by
    rw [List.mem_singleton.mp hd]
    rfl⟩

theorem compatible_guard_guard (p g : Path) :
    Compatible [.held p (.guard g)] [.held p (.guard g)] :=
  ⟨⟨fun _ => some (.guard g), fun _ _ => false⟩, fun d hd => by
    rw [List.mem_singleton.mp hd]
    rfl, fun d hd => by
    rw [List.mem_singleton.mp hd]
    rfl⟩

theorem not_compatible_via_uniq (p : Path) : ¬ Compatible [.via p] [.uniq p] := by
  rintro ⟨σ, h₁, h₂⟩
  have a := h₁ _ (List.mem_singleton.mpr rfl)
  have b := h₂ _ (List.mem_singleton.mpr rfl)
  simp only [Sat, Tid.flip] at a b
  rw [a] at b
  cases b.2

theorem not_compatible_uniq_via (p : Path) : ¬ Compatible [.uniq p] [.via p] := by
  rintro ⟨σ, h₁, h₂⟩
  have a := h₁ _ (List.mem_singleton.mpr rfl)
  have b := h₂ _ (List.mem_singleton.mpr rfl)
  simp only [Sat, Tid.flip] at a b
  rw [b] at a
  cases a.2

theorem not_compatible_uniq_uniq (p : Path) : ¬ Compatible [.uniq p] [.uniq p] := by
  rintro ⟨σ, h₁, h₂⟩
  have a := h₁ _ (List.mem_singleton.mpr rfl)
  have b := h₂ _ (List.mem_singleton.mpr rfl)
  simp only [Sat, Tid.flip] at a b
  rw [b.1] at a
  cases a.2

theorem not_compatible_fresh_fresh (p : Path) :
    ¬ Compatible [.held p .fresh] [.held p .fresh] := by
  rintro ⟨σ, h₁, h₂⟩
  have a := h₁ _ (List.mem_singleton.mpr rfl)
  have b := h₂ _ (List.mem_singleton.mpr rfl)
  simp only [Sat, Acq.holder] at a b
  rw [a] at b
  cases b

theorem not_compatible_guard_fresh (p g : Path) :
    ¬ Compatible [.held p (.guard g)] [.held p .fresh] := by
  rintro ⟨σ, h₁, h₂⟩
  have a := h₁ _ (List.mem_singleton.mpr rfl)
  have b := h₂ _ (List.mem_singleton.mpr rfl)
  simp only [Sat, Acq.holder] at a b
  rw [a] at b
  cases b

/-! ## Owners can do what sharers can -/

theorem shr_subset_own : ∀ T : Ty, ∀ e ∈ (fp T).shr, e ∈ (fp T).own := by
  intro T
  induction T with
  | plain =>
    intro e he
    simp only [fp, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    exact Or.inl he
  | cell t _ => intro e he; exact he
  | refCell t _ =>
    intro e he
    exact List.mem_append.mpr (Or.inr he)
  | rc t _ => intro e he; exact he
  | arc t _ => intro e he; exact he
  | mutex t _ =>
    intro e he
    exact List.mem_append.mpr (Or.inr he)
  | guard t ih =>
    intro e he
    exact List.mem_append.mpr (Or.inl (place_subset _ _ ih e he))
  | box t ih => exact ih
  | ref t _ => intro e he; exact he
  | refMut t ih => exact ih
  | prod a b iha ihb =>
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append.mpr (Or.inl (place_subset _ _ iha e h))
    · exact List.mem_append.mpr (Or.inr (place_subset _ _ ihb e h))
  | sum a b iha ihb =>
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append.mpr (Or.inl (place_subset _ _ iha e h))
    · exact List.mem_append.mpr (Or.inr (place_subset _ _ ihb e h))
  | wrap f v u ih =>
    intro e he
    exact ih e (expose_subset v _ e he)

theorem nfr_shr_of_own (t : Tid) (T : Ty) :
    NoForeignRelease t (fp T).own → NoForeignRelease t (fp T).shr :=
  nfr_mono (shr_subset_own T)

end Toy.SendSync
