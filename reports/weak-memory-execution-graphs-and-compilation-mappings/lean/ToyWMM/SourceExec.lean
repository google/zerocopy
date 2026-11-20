import ToyWMM.Fence

/-!
# Compilation correctness of the fence-insertion mapping, stated on source executions

The program-level soundness theorem `scConsistentErased_of_tso_fenceAfterStores` speaks about
the target execution only (its SC relation restricted to memory accesses). The statement a
compiler correctness argument needs is about the *source* program: every well-formed
TSO-consistent execution of `fenceAfterStores P` arises from a well-formed SC-consistent
execution of `P` with the same reads-from, coherence and read values. Here the source
execution is `X.comap f` for an order-preserving index map `f` from the events of `P` into the
events of the compiled execution that hits every memory access (so it misses only inserted
fences); the events, `po`, `rf` and `co` of `X.comap f` are those of `X` at the images, so read
values and the final (co-maximal) writes agree by construction.
-/

namespace Toy.WMM

open Litmus Event

/-- The execution `X` seen through an index map `f`: the events, `po`, `rf` and `co` of `X`
at the images of `f`. -/
def Exec.comap {m n : Nat} (X : Exec n) (f : Fin m → Fin n) : Exec m where
  ev a := X.ev (f a)
  po a b := X.po (f a) (f b)
  rf a b := X.rf (f a) (f b)
  co a b := X.co (f a) (f b)


/-! ## Supporting lemmas -/

/-- SC per location implies `CoIrrefl`. -/
theorem Exec.coIrrefl_of_perLocSC {n : Nat} (X : Exec n) (h : X.PerLocSC) : X.CoIrrefl := by
  intro a
  cases hc : X.co a a with
  | false => rfl
  | true => exact absurd (Rel.Path.single (X.uniprocRel_of_co hc)) (h a)

/-- If `f` is injective and hits every memory access of `X`, and `rf` only leaves writes,
then SC-consistency of `X.comap f` implies SC-consistency of `X` after fence erasure. -/
theorem Exec.scConsistentErased_of_comap {m n : Nat} (X : Exec n) (f : Fin m → Fin n)
    (hinj : ∀ a b, f a = f b → a = b)
    (hcov : ∀ e, (X.ev e).isAccess = true → ∃ a, f a = e) (hrfk : X.RfKinds)
    (h : (X.comap f).SCConsistent) : X.SCConsistentErased := by
  have hacc_w : ∀ e : Event, e.isWrite = true → e.isAccess = true := by
    intro e he; revert he; simp only [Event.isWrite, Event.isAccess, Event.isFence]
    cases e.kind <;> simp
  have edge : ∀ a' b', X.scRel (f a') (f b') = true → (X.comap f).scRel a' b' = true := by
    intro a' b' hs
    rcases X.scRel_cases hs with h' | h' | h' | h'
    · simp [Exec.scRel, Exec.comap, h']
    · simp [Exec.scRel, Exec.comap, h']
    · simp [Exec.scRel, Exec.comap, h']
    · obtain ⟨w, hw₁, hw₂⟩ := X.fr_iff.mp h'
      obtain ⟨w', hw'⟩ := hcov w (hacc_w _ (hrfk w _ hw₁).1)
      have : (X.comap f).fr a' b' = true :=
        (X.comap f).fr_iff.mpr ⟨w', by simp [Exec.comap, hw', hw₁], by simp [Exec.comap, hw', hw₂]⟩
      simp [Exec.scRel, this]
  have key : ∀ u v, Rel.Path (X.eraseFences X.scRel) u v → ∀ a', f a' = u →
      ∃ b', f b' = v ∧ Rel.Path (X.comap f).scRel a' b' := by
    intro u v hp
    induction hp with
    | single huv =>
      intro a' ha'
      obtain ⟨hs, _, hva⟩ := X.eraseFences_scRel_iff.mp huv
      obtain ⟨b', hb'⟩ := hcov _ hva
      subst ha'; subst hb'
      exact ⟨b', rfl, Rel.Path.single (edge a' b' hs)⟩
    | tail _ hvw ih =>
      intro a' ha'
      obtain ⟨b', hb', hp'⟩ := ih a' ha'
      obtain ⟨hs, _, hwa⟩ := X.eraseFences_scRel_iff.mp hvw
      obtain ⟨c', hc'⟩ := hcov _ hwa
      subst hb'; subst hc'
      exact ⟨c', rfl, Rel.Path.tail hp' (edge b' c' hs)⟩
  intro a ha
  have ha_acc : (X.ev a).isAccess = true := by
    cases ha with
    | single h₁ => exact (X.eraseFences_scRel_iff.mp h₁).2.2
    | tail _ h₁ => exact (X.eraseFences_scRel_iff.mp h₁).2.2
  obtain ⟨a', ha'⟩ := hcov a ha_acc
  obtain ⟨b', hb', hp⟩ := key a a ha a' ha'
  have : b' = a' := hinj _ _ (hb'.trans ha'.symm)
  subst this
  exact h b' hp

theorem injective_of_strictMono {m n : Nat} {f : Fin m → Fin n}
    (hmono : ∀ a b, a < b ↔ f a < f b) : ∀ a b, f a = f b → a = b := by
  intro a b hab
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · have := (hmono a b).mp h; rw [hab] at this; exact absurd this (Nat.lt_irrefl _)
  · exact Fin.ext h
  · have := (hmono b a).mp h; rw [hab] at this; exact absurd this (Nat.lt_irrefl _)

/-! ## The source-event map

`SourceMap.validEmbed_layout P` builds the list of indices at which the events of `layout P`
occur inside `layout (fenceAfterStores P)`: strictly increasing, event-preserving, and hitting
every memory access (it skips exactly the fences inserted after stores). The main theorem turns
this list into the map `f`. -/

namespace SourceMap

theorem max_zero_foldr_fenceThread :
    ∀ th : List Instr,
      ((fenceThread th).map Instr.loc).foldr max 0 = (th.map Instr.loc).foldr max 0
  | [] => rfl
  | .store l v :: rest => by
    simp only [fenceThread, List.map_cons, Instr.loc, List.foldr_cons]
    rw [max_zero_foldr_fenceThread rest]
    have h0 : max 0 ((List.map Instr.loc rest).foldr max 0) =
        (List.map Instr.loc rest).foldr max 0 := Nat.zero_max _
    rw [h0]
  | .load l :: rest => by
    simp only [fenceThread, List.map_cons, Instr.loc, List.foldr_cons,
      max_zero_foldr_fenceThread rest]
  | .mfence :: rest => by
    simp only [fenceThread, List.map_cons, Instr.loc, List.foldr_cons,
      max_zero_foldr_fenceThread rest]

theorem foldr_max_append (xs ys : List Nat) :
    (xs ++ ys).foldr max 0 = max (xs.foldr max 0) (ys.foldr max 0) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.cons_append, List.foldr_cons, ih, Nat.max_assoc]

theorem numLocs_fenceAfterStores (P : Prog) :
    (fenceAfterStores P).numLocs = P.numLocs := by
  suffices h : ((fenceAfterStores P).flatten.map Instr.loc).foldr max 0 =
      (P.flatten.map Instr.loc).foldr max 0 by
    simp only [Prog.numLocs, h]
  induction P with
  | nil => rfl
  | cons th rest ih =>
    have hcons : fenceAfterStores (th :: rest) = fenceThread th :: fenceAfterStores rest := rfl
    rw [hcons]
    simp only [List.flatten_cons, List.map_append, foldr_max_append,
      max_zero_foldr_fenceThread th, ih]

/-- `ValidEmbed src tgt idxs`: `idxs` is a strictly increasing index map from `src` into `tgt`
preserving events identically and hitting every memory-access event of `tgt`. -/
structure ValidEmbed (src tgt : List Event) (idxs : List Nat) : Prop where
  len : idxs.length = src.length
  pw : List.Pairwise (· < ·) idxs
  bound : ∀ k (hk : k < idxs.length), idxs[k] < tgt.length
  eq_ev : ∀ k (hk : k < idxs.length) (hks : k < src.length),
    tgt[idxs[k]]'(bound k hk) = src[k]
  cov : ∀ j (hj : j < tgt.length), (tgt[j]).isAccess = true → j ∈ idxs

theorem ValidEmbed.nil : ValidEmbed [] [] [] where
  len := rfl
  pw := List.Pairwise.nil
  bound := fun _ hk => absurd hk (Nat.not_lt_zero _)
  eq_ev := fun _ hk _ => absurd hk (Nat.not_lt_zero _)
  cov := fun _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem ValidEmbed.single_same (e : Event) : ValidEmbed [e] [e] [0] where
  len := rfl
  pw := by simp
  bound := fun k hk => by simp at hk; subst hk; simp
  eq_ev := fun k hk _ => by simp at hk; subst hk; rfl
  cov := fun j hj _ => by simp at hj; subst hj; simp

theorem ValidEmbed.store_fence (t l v : Nat) :
    ValidEmbed [Instr.toEvent t (.store l v)]
      [Instr.toEvent t (.store l v), Instr.toEvent t .mfence] [0] where
  len := rfl
  pw := by simp
  bound := fun k hk => by simp at hk; subst hk; simp
  eq_ev := fun k hk _ => by simp at hk; subst hk; rfl
  cov := fun j hj hacc => by
    simp only [List.length_cons, List.length_nil] at hj
    match j with
    | 0 => simp
    | 1 => simp [Instr.toEvent, Event.isAccess, Event.isFence] at hacc
    | k + 2 => omega

theorem ValidEmbed.append {s₁ t₁ s₂ t₂ : List Event} {i₁ i₂ : List Nat}
    (h₁ : ValidEmbed s₁ t₁ i₁) (h₂ : ValidEmbed s₂ t₂ i₂) :
    ValidEmbed (s₁ ++ s₂) (t₁ ++ t₂) (i₁ ++ i₂.map (· + t₁.length)) where
  len := by simp [h₁.len, h₂.len]
  pw := by
    rw [List.pairwise_append]
    refine ⟨h₁.pw, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact h₂.pw.imp (by omega)
    · intro a ha b hb
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
      have hlt := h₁.bound k hk
      omega
  bound := by
    intro k hk
    simp only [List.length_append, List.length_map] at hk ⊢
    by_cases hk₁ : k < i₁.length
    · rw [List.getElem_append_left hk₁]
      have := h₁.bound k hk₁
      omega
    · have hle : i₁.length ≤ k := by omega
      rw [List.getElem_append_right hle, List.getElem_map]
      have hk₂ : k - i₁.length < i₂.length := by omega
      have := h₂.bound (k - i₁.length) hk₂
      omega
  eq_ev := by
    intro k hk hks
    by_cases hk₁ : k < i₁.length
    · have hks₁ : k < s₁.length := h₁.len ▸ hk₁
      have hbt : (i₁ ++ i₂.map (· + t₁.length))[k] < t₁.length := by
        rw [List.getElem_append_left hk₁]; exact h₁.bound k hk₁
      rw [List.getElem_append_left hbt, List.getElem_append_left hks₁]
      have hidx : (i₁ ++ i₂.map (· + t₁.length))[k] = i₁[k] := List.getElem_append_left hk₁
      simp only [hidx]
      exact h₁.eq_ev k hk₁ hks₁
    · have hle : i₁.length ≤ k := by omega
      have hles : s₁.length ≤ k := h₁.len ▸ hle
      have hk₂ : k - i₁.length < i₂.length := by simp at hk; omega
      have hks₂ : k - s₁.length < s₂.length := by simp at hks; omega
      have hidx : (i₁ ++ i₂.map (· + t₁.length))[k] = i₂[k - i₁.length] + t₁.length := by
        rw [List.getElem_append_right hle, List.getElem_map]
      have hbt : t₁.length ≤ (i₁ ++ i₂.map (· + t₁.length))[k] := by omega
      rw [List.getElem_append_right hbt, List.getElem_append_right hles]
      have hsub : (i₁ ++ i₂.map (· + t₁.length))[k] - t₁.length = i₂[k - i₁.length] := by omega
      have hksub : k - s₁.length = k - i₁.length := by rw [h₁.len]
      simp only [hsub, hksub]
      exact h₂.eq_ev (k - i₁.length) hk₂ (hksub ▸ hks₂)
  cov := by
    intro j hj hacc
    simp only [List.length_append] at hj
    by_cases hj₁ : j < t₁.length
    · rw [List.getElem_append_left hj₁] at hacc
      exact List.mem_append_left _ (h₁.cov j hj₁ hacc)
    · have hle : t₁.length ≤ j := by omega
      rw [List.getElem_append_right hle] at hacc
      have hj₂ : j - t₁.length < t₂.length := by omega
      have hmem := h₂.cov (j - t₁.length) hj₂ hacc
      apply List.mem_append_right
      rw [List.mem_map]
      exact ⟨j - t₁.length, hmem, by omega⟩

theorem validEmbed_refl : ∀ l : List Event, ∃ idxs, ValidEmbed l l idxs
  | [] => ⟨[], ValidEmbed.nil⟩
  | e :: rest => by
    obtain ⟨idxs, h⟩ := validEmbed_refl rest
    exact ⟨0 :: idxs.map (· + 1), ValidEmbed.append (ValidEmbed.single_same e) h⟩

theorem validEmbed_fenceThread (t : Nat) :
    ∀ th : List Instr,
      ∃ idxs, ValidEmbed (th.map (Instr.toEvent t)) ((fenceThread th).map (Instr.toEvent t)) idxs
  | [] => ⟨[], ValidEmbed.nil⟩
  | .store l v :: rest => by
    obtain ⟨idxs, h⟩ := validEmbed_fenceThread t rest
    simpa [fenceThread] using
      ⟨0 :: idxs.map (· + 2), ValidEmbed.append (ValidEmbed.store_fence t l v) h⟩
  | .load l :: rest => by
    obtain ⟨idxs, h⟩ := validEmbed_fenceThread t rest
    simpa [fenceThread] using
      ⟨0 :: idxs.map (· + 1), ValidEmbed.append (ValidEmbed.single_same (Instr.toEvent t (.load l))) h⟩
  | .mfence :: rest => by
    obtain ⟨idxs, h⟩ := validEmbed_fenceThread t rest
    simpa [fenceThread] using
      ⟨0 :: idxs.map (· + 1), ValidEmbed.append (ValidEmbed.single_same (Instr.toEvent t .mfence)) h⟩

theorem validEmbed_threadEvents (P : Prog) :
    ∀ t : Nat, ∃ idxs, ValidEmbed (threadEvents t P) (threadEvents t (fenceAfterStores P)) idxs := by
  induction P with
  | nil => intro _; exact ⟨[], ValidEmbed.nil⟩
  | cons th rest ih =>
    intro t
    obtain ⟨i₁, h₁⟩ := validEmbed_fenceThread t th
    obtain ⟨i₂, h₂⟩ := ih (t + 1)
    exact ⟨_, ValidEmbed.append h₁ h₂⟩

theorem validEmbed_layout (P : Prog) :
    ∃ idxs, ValidEmbed (layout P) (layout (fenceAfterStores P)) idxs := by
  unfold layout
  rw [numLocs_fenceAfterStores P]
  obtain ⟨i₁, h₁⟩ := validEmbed_refl ((List.range P.numLocs).map Event.initW)
  obtain ⟨i₂, h₂⟩ := validEmbed_threadEvents P 0
  exact ⟨_, ValidEmbed.append h₁ h₂⟩

theorem scConsistent_comap_of_scConsistent {m n : Nat} (X : Exec n) (f : Fin m → Fin n)
    (hsc : X.SCConsistent) : (X.comap f).SCConsistent := by
  have hedge : ∀ a b, (X.comap f).scRel a b = true → X.scRel (f a) (f b) = true := by
    intro a b hab
    rcases (X.comap f).scRel_cases hab with h | h | h | h
    · simp [Exec.scRel, Exec.comap] at h ⊢; exact Or.inl (Or.inl (Or.inl h))
    · simp [Exec.scRel, Exec.comap] at h ⊢; exact Or.inl (Or.inl (Or.inr h))
    · simp [Exec.scRel, Exec.comap] at h ⊢; exact Or.inl (Or.inr h)
    · obtain ⟨w, hw₁, hw₂⟩ := (X.comap f).fr_iff.mp h
      have hfr : X.fr (f a) (f b) = true := X.fr_iff.mpr ⟨f w, hw₁, hw₂⟩
      simp [Exec.scRel, hfr]
  have hpath : ∀ a b, Rel.Path (X.comap f).scRel a b → Rel.Path X.scRel (f a) (f b) := by
    intro a b hp
    induction hp with
    | single hab => exact Rel.Path.single (hedge _ _ hab)
    | tail _ hbc ih => exact Rel.Path.tail ih (hedge _ _ hbc)
  exact fun a ha => hsc (f a) (hpath a a ha)

end SourceMap

open SourceMap in
/-- **Fence-mapping correctness on source executions.** For every program `P` and every
TSO-consistent candidate execution `X` of `fenceAfterStores P` whose `rf` and `co` are well
formed (`RfCoWf`; the `po` conditions of `Wf` follow from `ExecOf`, and `CoIrrefl` from SC per
location), there is an order-preserving map `f` from the events of `P` into the events of `X`,
hitting every memory access of `X`, such that `X.comap f` is a well-formed SC-consistent
candidate execution of `P`. -/
theorem exists_sc_source_execution_of_tso_fenceAfterStores (P : Prog) {n : Nat} (X : Exec n)
    (hX : ExecOf (fenceAfterStores P) X) (hwf : X.RfCoWf) (htso : X.TSOConsistent) :
    ∃ f : Fin (layout P).length → Fin n,
      (∀ a b, a < b ↔ f a < f b) ∧ (∀ e, (X.ev e).isAccess = true → ∃ a, f a = e) ∧
      ExecOf P (X.comap f) ∧ (X.comap f).Wf ∧ (X.comap f).SCConsistent := by
  obtain ⟨idxs, hv⟩ := validEmbed_layout P
  have ha_idx : ∀ a : Fin (layout P).length, a.val < idxs.length := fun a => by
    have := hv.len; have := a.isLt; omega
  have ha_tgt : ∀ a : Fin (layout P).length, idxs[a.val]'(ha_idx a) < n := fun a => by
    have := hv.bound a.val (ha_idx a); have := hX.length; omega
  let f : Fin (layout P).length → Fin n := fun a => ⟨idxs[a.val]'(ha_idx a), ha_tgt a⟩
  have hmono_lt : ∀ a b : Fin (layout P).length, a < b → f a < f b := by
    intro a b hab
    exact List.pairwise_iff_getElem.mp hv.pw a.val b.val (ha_idx a) (ha_idx b) hab
  have hmono : ∀ a b : Fin (layout P).length, a < b ↔ f a < f b := by
    intro a b
    constructor
    · exact hmono_lt a b
    · intro hfab
      rcases Nat.lt_trichotomy a.val b.val with h | h | h
      · exact h
      · have heq : a = b := Fin.ext h; subst heq; exact absurd hfab (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_trans hfab (hmono_lt b a h)) (Nat.lt_irrefl _)
  have hinj : ∀ a b, f a = f b → a = b := injective_of_strictMono hmono
  have hgetP : ∀ a : Fin (layout P).length,
      (layout P).getD a.val default = (layout P)[a.val] := by
    intro a; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem a.isLt]; rfl
  have he_lt : ∀ e : Fin n, e.val < (layout (fenceAfterStores P)).length := fun e => by
    have := hX.length; have := e.isLt; omega
  have hgetFP : ∀ e : Fin n,
      (layout (fenceAfterStores P)).getD e.val default =
        (layout (fenceAfterStores P))[e.val]'(he_lt e) := by
    intro e
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (he_lt e)]; rfl
  have hev_eq : ∀ a : Fin (layout P).length,
      (layout (fenceAfterStores P)).getD (f a).val default = (layout P).getD a.val default := by
    intro a
    rw [hgetFP (f a), hgetP a]
    exact hv.eq_ev a.val (ha_idx a) a.isLt
  have hcov : ∀ e : Fin n, (X.ev e).isAccess = true → ∃ a, f a = e := by
    intro e hacc
    have hk : (X.ev e).kind = ((layout (fenceAfterStores P))[e.val]'(he_lt e)).kind := by
      rw [hX.kind e, hgetFP e]
    have hacc' : ((layout (fenceAfterStores P))[e.val]'(he_lt e)).isAccess = true := by
      revert hacc; simp only [Event.isAccess, Event.isFence, hk]; exact id
    have hmem := hv.cov e.val (he_lt e) hacc'
    obtain ⟨k, hklt, hkeq⟩ := List.getElem_of_mem hmem
    have hkp : k < (layout P).length := by have := hv.len; omega
    refine ⟨⟨k, hkp⟩, Fin.ext hkeq⟩
  have hexec : ExecOf P (X.comap f) := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro a; simp only [Exec.comap]; rw [hX.kind (f a), hev_eq a]
    · intro a; simp only [Exec.comap]; rw [hX.tid (f a), hev_eq a]
    · intro a; simp only [Exec.comap]; rw [hX.loc (f a), hev_eq a]
    · intro a hnr; simp only [Exec.comap] at hnr ⊢; rw [hX.val (f a) hnr, hev_eq a]
    · intro a b
      simp only [Exec.comap]
      rw [hX.po (f a) (f b)]
      have hlt_eq : decide ((f a).val < (f b).val) = decide (a.val < b.val) :=
        decide_eq_decide.mpr (hmono a b).symm
      rw [hlt_eq]
      rfl
  obtain ⟨hrfl, hrfk, hrfv, hrft, hrff, hcok, hcotr, hcotot, hcoinit⟩ := hwf
  have hcoirr : X.CoIrrefl := X.coIrrefl_of_perLocSC htso.1
  have hacc_w : ∀ e : Event, e.isWrite = true → e.isAccess = true := by
    intro e he; revert he; simp only [Event.isWrite, Event.isAccess, Event.isFence]
    cases e.kind <;> simp
  have hwf_src : (X.comap f).Wf := by
    refine ⟨hexec.poIrrefl, hexec.poTrans, hexec.poWithinThread, hexec.poTotal,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab; exact hrfl (f a) (f b) hab
    · intro a b hab; exact hrfk (f a) (f b) hab
    · intro a b hab; exact hrfv (f a) (f b) hab
    · intro b hrb
      obtain ⟨w, hw⟩ := hrft (f b) hrb
      obtain ⟨a, rfl⟩ := hcov w (hacc_w _ (hrfk w (f b) hw).1)
      exact ⟨a, hw⟩
    · intro a a' b h1 h2; exact hinj a a' (hrff (f a) (f a') (f b) h1 h2)
    · intro a b hab; exact hcok (f a) (f b) hab
    · intro a; exact hcoirr (f a)
    · intro a b c h1 h2; exact hcotr (f a) (f b) (f c) h1 h2
    · intro a b hne ha hb hsl
      exact hcotot (f a) (f b) (fun h => hne (hinj a b h)) ha hb hsl
    · intro a b hai hwb hsl hne
      exact hcoinit (f a) (f b) hai hwb hsl (fun h => hne (hinj a b h))
  have hscX : X.SCConsistent :=
    scConsistent_of_scConsistentErased X hX.poIrrefl hX.poTrans hrfk hcok
      (scConsistentErased_of_tso_fenceAfterStores P X hX hrfl htso.1 htso.2)
  exact ⟨f, hmono, hcov, hexec, hwf_src, scConsistent_comap_of_scConsistent X f hscX⟩

/-! ## Non-vacuity and tightness -/

/-- Non-vacuity: `sbFencedSC` is a TSO-consistent execution of `fenceAfterStores sbProg` with
well-formed `rf` and `co`. -/
theorem nonvacuity_exists_sc_source_execution_of_tso_fenceAfterStores :
    ExecOf (fenceAfterStores sbProg) sbFencedSC ∧ sbFencedSC.RfCoWf ∧
      sbFencedSC.TSOConsistent :=
  ⟨sbFencedSC_execOf, by decide⟩

/-- The source-event map of `fenceAfterStores sbProg`: `0, 1, 2, 4, 5, 7` (indices `3` and `6`
are the inserted fences). -/
def sbSrcIdx : Fin (layout sbProg).length → Fin 8 :=
  fun a => ⟨([0, 1, 2, 4, 5, 7] : List Nat).getD a.val 0 % 8, Nat.mod_lt _ (by decide)⟩

/-- The conclusion holds on the non-vacuity instance with the explicit map `sbSrcIdx`; the
source execution is the SC outcome `sbSC` of SB. -/
theorem sbFencedSC_source_execution :
    (∀ a b, a < b ↔ sbSrcIdx a < sbSrcIdx b) ∧
      (∀ e, (sbFencedSC.ev e).isAccess = true → ∃ a, sbSrcIdx a = e) ∧
      ExecOf sbProg (sbFencedSC.comap sbSrcIdx) ∧ (sbFencedSC.comap sbSrcIdx).Wf ∧
      (sbFencedSC.comap sbSrcIdx).SCConsistent :=
  ⟨by decide, by decide, ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩,
    by decide, by decide⟩

/-- Being an execution of the compiled program is needed: the SB weak-outcome execution of the
*unfenced* program is well formed and TSO-consistent, but it is not an execution of
`fenceAfterStores sbProg` and has no SC source execution. -/
theorem sourceExec_needs_execOf :
    ¬ ExecOf (fenceAfterStores sbProg) sbWeak ∧ sbWeak.RfCoWf ∧ sbWeak.TSOConsistent ∧
      ¬ ∃ f : Fin (layout sbProg).length → Fin 6,
        (∀ a b, a < b ↔ f a < f b) ∧ (∀ e, (sbWeak.ev e).isAccess = true → ∃ a, f a = e) ∧
        ExecOf sbProg (sbWeak.comap f) ∧ (sbWeak.comap f).Wf ∧ (sbWeak.comap f).SCConsistent := by
  refine ⟨fun h => absurd h.length (by decide), by decide, by decide, ?_⟩
  rintro ⟨f, hmono, hcov, _, _, hsc⟩
  have hrfk : sbWeak.RfKinds := by decide
  exact (by decide : ¬ sbWeak.SCConsistentErased)
    (sbWeak.scConsistentErased_of_comap f (injective_of_strictMono hmono) hcov hrfk hsc)

/-- An ill-formed execution of the store-free program `r0 := x`: the read has no `rf` source. -/
def loadNoRf : Exec 2 := Exec.ofList [initW 0, R 0 0 0] [] []

/-- Well-formedness of `rf` and `co` is needed: `loadNoRf` is a TSO-consistent execution of
`fenceAfterStores [[.load 0]]` whose read has no `rf` source, and no source execution read
through any covering map is well formed. -/
theorem sourceExec_needs_rfCoWf :
    ExecOf (fenceAfterStores [[.load 0]]) loadNoRf ∧ loadNoRf.TSOConsistent ∧
      ¬ loadNoRf.RfCoWf ∧
      ¬ ∃ f : Fin (layout [[.load 0]]).length → Fin 2,
        (∀ a b, a < b ↔ f a < f b) ∧ (∀ e, (loadNoRf.ev e).isAccess = true → ∃ a, f a = e) ∧
        ExecOf [[.load 0]] (loadNoRf.comap f) ∧ (loadNoRf.comap f).Wf ∧
        (loadNoRf.comap f).SCConsistent := by
  refine ⟨⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide, ?_⟩
  rintro ⟨f, _, hcov, _, hwf', _⟩
  obtain ⟨a, ha⟩ := hcov ⟨1, by decide⟩ (by decide)
  have hread : ((loadNoRf.comap f).ev a).isRead = true := by
    simp only [Exec.comap, ha]; decide
  obtain ⟨w, hw⟩ := hwf'.2.2.2.2.2.2.2.1 a hread
  simp only [Exec.comap] at hw
  revert hw
  generalize f w = v
  generalize f a = u
  revert u v
  decide

/-- TSO-consistency of `X` is needed: the SB+mfences weak-outcome execution is a well-formed
execution of `fenceAfterStores sbProg` that is not TSO-consistent and has no SC source
execution. -/
theorem sourceExec_needs_tso :
    ExecOf (fenceAfterStores sbProg) sbFencedWeak ∧ sbFencedWeak.RfCoWf ∧
      ¬ sbFencedWeak.TSOConsistent ∧
      ¬ ∃ f : Fin (layout sbProg).length → Fin 8,
        (∀ a b, a < b ↔ f a < f b) ∧ (∀ e, (sbFencedWeak.ev e).isAccess = true → ∃ a, f a = e) ∧
        ExecOf sbProg (sbFencedWeak.comap f) ∧ (sbFencedWeak.comap f).Wf ∧
        (sbFencedWeak.comap f).SCConsistent := by
  refine ⟨sbFencedWeak_execOf, by decide, by decide, ?_⟩
  rintro ⟨f, hmono, hcov, _, _, hsc⟩
  have hrfk : sbFencedWeak.RfKinds := by decide
  exact (by decide : ¬ sbFencedWeak.SCConsistentErased)
    (sbFencedWeak.scConsistentErased_of_comap f (injective_of_strictMono hmono) hcov hrfk hsc)

end Toy.WMM
