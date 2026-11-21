import ToyCoalesce.PfCoalesce

/-!
# Proof: soundness of lexical intervals for address-taken locals
-/

namespace Toy.Coalesce

namespace Pol

open Toy.Coalesce.Inv

/-! ## The scan state of `clobberFreeAux` -/

/-- The last-write map after scanning a log (data writes only). -/
def lwOf (μ : Forest) : List Access → (Nat × Nat → Option (Nat × Nat)) →
    Nat × Nat → Option (Nat × Nat)
  | [], lw => lw
  | e :: es, lw =>
    match e.kind with
    | .write => lwOf μ es fun t => if t = μ.tcell e.loc e.off then some (e.loc, e.off) else lw t
    | _ => lwOf μ es lw

theorem clobber_append (μ : Forest) (L L' : List Access) :
    ∀ lw, clobberFreeAux μ (L ++ L') lw =
      (clobberFreeAux μ L lw && clobberFreeAux μ L' (lwOf μ L lw)) := by
  induction L with
  | nil => intro lw; simp [clobberFreeAux, lwOf]
  | cons e L ih =>
    intro lw
    cases hk : e.kind <;> simp [clobberFreeAux, lwOf, hk, ih, Bool.and_assoc]

theorem lwOf_append (μ : Forest) (L L' : List Access) :
    ∀ lw, lwOf μ (L ++ L') lw = lwOf μ L' (lwOf μ L lw) := by
  induction L with
  | nil => intro lw; rfl
  | cons e L ih =>
    intro lw
    cases hk : e.kind <;> simp [lwOf, hk, ih]

theorem clobber_single_write (μ : Forest) (e : Access) (he : e.kind = .write) (lw) :
    clobberFreeAux μ [e] lw = true := by
  simp [clobberFreeAux, he]

theorem clobber_single_reset (μ : Forest) (e : Access) (he : e.kind = .reset) (lw) :
    clobberFreeAux μ [e] lw = true := by
  simp [clobberFreeAux, he]

theorem lwOf_single_write (μ : Forest) (e : Access) (he : e.kind = .write) (lw) :
    lwOf μ [e] lw =
      fun t => if t = μ.tcell e.loc e.off then some (e.loc, e.off) else lw t := by
  simp [lwOf, he]

theorem lwOf_single_reset (μ : Forest) (e : Access) (he : e.kind = .reset) (lw) :
    lwOf μ [e] lw = lw := by
  simp [lwOf, he]

theorem lwOf_single_read (μ : Forest) (e : Access) (he : e.kind = .read) (lw) :
    lwOf μ [e] lw = lw := by
  simp [lwOf, he]

/-! ## Forest facts -/

theorem parentOf_none_of_not_inClass (μ : Forest) (x : Nat) (h : μ.inClass x = false) :
    μ.parentOf x = none := by
  unfold Forest.parentOf
  cases hf : μ.find? (·.child == x) with
  | none => rfl
  | some e =>
    exfalso
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    have : μ.inClass x = true := by
      unfold Forest.inClass
      exact List.any_eq_true.mpr ⟨e, hm, by simp [hp]⟩
    rw [h] at this; cases this

theorem resolveF_of_parentOf_none (μ : Forest) (x : Nat) (h : μ.parentOf x = none) :
    ∀ n, μ.resolveF n x = (x, 0) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [Forest.resolveF, h]

theorem resolveF_root (μ : Forest) :
    ∀ n x, (μ.resolveF n x).1 = x ∨ μ.inClass (μ.resolveF n x).1 = true := by
  intro n
  induction n with
  | zero => intro x; left; rfl
  | succ n ih =>
    intro x
    cases hp : μ.parentOf x with
    | none => left; simp [Forest.resolveF, hp]
    | some e =>
      right
      simp only [Forest.resolveF, hp]
      rcases ih e.parent with h1 | h1
      · rw [h1]
        unfold Forest.parentOf at hp
        have hm := List.mem_of_find?_eq_some hp
        unfold Forest.inClass
        exact List.any_eq_true.mpr ⟨e, hm, by simp⟩
      · exact h1

theorem root_of_not_inClass (μ : Forest) (x : Nat) (h : μ.inClass x = false) :
    μ.root x = x ∧ μ.offset x = 0 := by
  have := resolveF_of_parentOf_none μ x (parentOf_none_of_not_inClass μ x h) μ.length
  simp [Forest.root, Forest.offset, Forest.resolve, this]

theorem root_cases (μ : Forest) (x : Nat) : μ.root x = x ∨ μ.inClass (μ.root x) = true :=
  resolveF_root μ μ.length x

theorem tcell_eq (μ : Forest) {u o v o' : Nat} (h : μ.tcell u o = μ.tcell v o')
    (hne : (v, o') ≠ (u, o)) :
    u ≠ v ∧ μ.sameClass u v = true ∧ μ.offset u + o = μ.offset v + o' := by
  simp only [Forest.tcell, Prod.mk.injEq] at h
  obtain ⟨hr, ho⟩ := h
  have huv : u ≠ v := by
    intro huv; subst huv; apply hne; simp; omega
  refine ⟨huv, ?_, ho⟩
  have hu : μ.inClass u = true := by
    cases hc : μ.inClass u with
    | true => rfl
    | false =>
      exfalso
      rw [(root_of_not_inClass μ u hc).1] at hr
      rcases root_cases μ v with h1 | h1
      · exact huv (hr.trans h1)
      · rw [← hr, hc] at h1; cases h1
  have hv : μ.inClass v = true := by
    cases hc : μ.inClass v with
    | true => rfl
    | false =>
      exfalso
      rw [(root_of_not_inClass μ v hc).1] at hr
      rcases root_cases μ u with h1 | h1
      · exact huv (h1.symm.trans hr)
      · rw [hr, hc] at h1; cases h1
  simp [Forest.sameClass, hu, hv, hr]

theorem lt_nloc_of_lt_size (P : Prog) {u o : Nat} (h : o < P.size u) : u < P.nloc := by
  unfold Prog.size at h
  unfold Prog.nloc
  rcases Nat.lt_or_ge u P.sizes.length with hc | hc
  · exact hc
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc] at h
    simp at h

/-! ## Intervals -/

theorem inIv_precise (P : Prog) {u p a pk : Nat} (ha : a ≤ p) (hA : AccessPt P u a = true)
    (hpk : p ≤ pk) (hpk2 : pk < 2 * P.code.length + 2) (hB : AccessPt P u pk = true) :
    InIv .precise P u p = true := by
  simp only [InIv, Bool.and_eq_true, List.any_eq_true, List.mem_range, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨⟨a, by omega, hA⟩, ⟨pk, ⟨by omega, hpk⟩, hB⟩⟩

/-- The notion of `x` under `pol` is precise. -/
abbrev Prec (pol : Policy) (P : Prog) (x : Nat) : Prop := pol (decide (AddrTaken P x)) = .precise

/-- An access to a cell of `x` at point `p` is licensed: if `x` is a precise class member,
then `p` is one of its access points. -/
def Acc (pol : Policy) (P : Prog) (μ : Forest) (p x : Nat) : Prop :=
  μ.inClass x = true → Prec pol P x → AccessPt P x p = true

/-- `u` is a precise class member without access points at or after `p`. -/
def DeadAfter (pol : Policy) (P : Prog) (μ : Forest) (u p : Nat) : Prop :=
  μ.inClass u = true ∧ Prec pol P u ∧
    ∀ pk, p ≤ pk → pk < 2 * P.code.length + 2 → AccessPt P u pk = true → False

theorem deadAfter_mono {pol : Policy} {P : Prog} {μ : Forest} {u p p' : Nat}
    (h : DeadAfter pol P μ u p) (hp : p ≤ p') : DeadAfter pol P μ u p' :=
  ⟨h.1, h.2.1, fun pk h1 h2 h3 => h.2.2 pk (by omega) h2 h3⟩

theorem acc_of_addrTaken {pol : Policy} (hpol : pol true = .lexical) {P : Prog} {μ : Forest}
    {p x : Nat} (h : AddrTaken P x) : Acc pol P μ p x := by
  intro _ hp
  unfold Prec at hp
  rw [decide_eq_true h, hpol] at hp
  cases hp

theorem notion_lexical {pol : Policy} {P : Prog} {x : Nat} (h : ¬ Prec pol P x) :
    pol (decide (AddrTaken P x)) = .lexical := by
  unfold Prec at h
  cases hn : pol (decide (AddrTaken P x)) with
  | lexical => rfl
  | precise => exact absurd hn h

/-- The key conflict lemma: a data write to `(v, o')` that shares its coalesced cell with an
initialized cell `(u, o)` makes `u` dead from point `p` on. -/
theorem conflict {pol : Policy} {P : Prog} {μ : Forest} (hpc : PolicyCheck pol P μ)
    {u o v o' p : Nat} (hp : p < 2 * P.code.length + 2)
    (htc : μ.tcell u o = μ.tcell v o') (hne : (v, o') ≠ (u, o))
    (hou : o < P.size u) (hov : o' < P.size v)
    (hu1 : Prec pol P u → ∃ a, a ≤ p ∧ AccessPt P u a = true)
    (hu2 : ¬ Prec pol P u → LexLiveAt P u (p / 2) = true)
    (hv : InIv (pol (decide (AddrTaken P v))) P v p = true) :
    DeadAfter pol P μ u p := by
  obtain ⟨huv, hsc, hoff⟩ := tcell_eq μ htc hne
  have hcu : μ.inClass u = true := by
    simp only [Forest.sameClass, Bool.and_eq_true] at hsc; exact hsc.1.1
  have hwo : μ.windowsOverlap P u v = true := by
    simp only [Forest.windowsOverlap, decide_eq_true_eq]; omega
  have hpcuv := hpc u (lt_nloc_of_lt_size P hou) v (lt_nloc_of_lt_size P hov) huv hsc hwo
  by_cases hPu : Prec pol P u
  · refine ⟨hcu, hPu, fun pk hpk hpk2 hB => hpcuv ⟨p, hp, ?_, hv⟩⟩
    rw [hPu]
    obtain ⟨a, ha, hA⟩ := hu1 hPu
    exact inIv_precise P ha hA hpk hpk2 hB
  · exfalso
    apply hpcuv ⟨p, hp, ?_, hv⟩
    rw [notion_lexical hPu]
    exact hu2 hPu

theorem inIv_at {pol : Policy} {P : Prog} {μ : Forest} {v p : Nat}
    (hp : p < 2 * P.code.length + 2) (hc : μ.inClass v = true) (hacc : Acc pol P μ p v)
    (hlex : LexLiveAt P v (p / 2) = true) :
    InIv (pol (decide (AddrTaken P v))) P v p = true := by
  by_cases hPv : Prec pol P v
  · rw [hPv]
    have hA := hacc hc hPv
    exact inIv_precise P (Nat.le_refl p) hA (Nat.le_refl p) hp hA
  · rw [notion_lexical hPv]; exact hlex

/-! ## The run invariant -/

/-- The run invariant at phase point `p`, with `L` over-approximating the allocated class
members. -/
structure Good (pol : Policy) (P : Prog) (μ : Forest) (L : Nat → Bool) (p : Nat) (s : St) :
    Prop where
  live : LiveInv P s
  ptrs : PtrsIn (AddrTaken P) s
  run : s.status = .running →
    clobberFreeAux μ s.log (fun _ => none) = true ∧
    (∀ x, μ.inClass x = true → s.live x = true → L x = true) ∧
    (∀ u o, s.mem u o ≠ .uninit → μ.inClass u = true → Prec pol P u →
      ∃ a, a ≤ p ∧ AccessPt P u a = true) ∧
    (∀ u o c, s.mem u o ≠ .uninit → lwOf μ s.log (fun _ => none) (μ.tcell u o) = some c →
      c ≠ (u, o) → DeadAfter pol P μ u p)

section Prims

variable {pol : Policy} {P : Prog} {μ : Forest}

theorem good_congr {L : Nat → Bool} {p : Nat} {s t : St} (h : Good pol P μ L p s)
    (hm : t.mem = s.mem) (hlog : t.log = s.log) (hl : t.live = s.live)
    (hs : t.status = s.status) : Good pol P μ L p t := by
  refine ⟨liveInv_of_eq hm hl h.live, ptrsIn_congr hm h.ptrs, fun hr => ?_⟩
  rw [hs] at hr
  rw [hm, hlog, hl]
  exact h.run hr

theorem good_mono {L L' : Nat → Bool} {p p' : Nat} {s : St} (h : Good pol P μ L p s)
    (hL : ∀ x, L x = true → L' x = true) (hp : p ≤ p') : Good pol P μ L' p' s := by
  refine ⟨h.live, h.ptrs, fun hr => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.run hr
  refine ⟨h1, fun x hx hl => hL x (h2 x hx hl), fun u o hm hc hP => ?_,
    fun u o c hm hlw hne => deadAfter_mono (h4 u o c hm hlw hne) hp⟩
  obtain ⟨a, ha, hA⟩ := h3 u o hm hc hP
  exact ⟨a, by omega, hA⟩

theorem good_fail {L L' : Nat → Bool} {p p' : Nat} {s : St} (h : Good pol P μ L p s) :
    Good pol P μ L' p' (s.fail .ub) :=
  ⟨h.live, h.ptrs, fun hr => by simp [St.fail] at hr⟩

theorem good_read {L : Nat → Bool} {p : Nat} {s : St} {loc off : Nat}
    (h : Good pol P μ L p s) (hm : s.mem loc off ≠ .uninit) (hacc : Acc pol P μ p loc)
    (hp : p < 2 * P.code.length + 2) : Good pol P μ L p (s.logAcc loc off .read) := by
  refine ⟨h.live, h.ptrs, fun hr => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.run hr
  have hlog : (s.logAcc loc off .read).log = s.log ++ [⟨s.tick, s.inCall, loc, off, .read⟩] := rfl
  have hlw : lwOf μ (s.logAcc loc off .read).log (fun _ => none) =
      lwOf μ s.log (fun _ => none) := by
    rw [hlog, lwOf_append, lwOf_single_read _ _ rfl]
  refine ⟨?_, h2, h3, ?_⟩
  · rw [hlog, clobber_append, h1]
    simp only [clobberFreeAux, Bool.true_and, Bool.and_true]
    cases hc : lwOf μ s.log (fun _ => none) (μ.tcell loc off) with
    | none => rfl
    | some c =>
      simp only [beq_iff_eq]
      by_cases hce : c = (loc, off)
      · exact hce
      · exfalso
        have hd := h4 loc off c hm hc hce
        exact hd.2.2 p (Nat.le_refl p) hp (hacc hd.1 hd.2.1)
  · rw [hlw]; exact h4

theorem good_wr_write {L : Nat → Bool} {p : Nat} {s : St} {loc off : Nat} {v : Val}
    (hpc : PolicyCheck pol P μ) (h : Good pol P μ L p s) (hl : s.live loc = true)
    (hb : off < P.size loc) (hacc : Acc pol P μ p loc)
    (hv : ∀ l' o', v = .ptr l' o' → AddrTaken P l') (hp : p < 2 * P.code.length + 2)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p / 2) = true) :
    Good pol P μ L p (s.wr .write loc off v) := by
  have hlive : LiveInv P (writeCellsK .write s loc off [v]) :=
    liveInv_writeCellsK .write loc off [v] h.live
      (fun i hi _ => ⟨hl, by simp at hi; omega⟩)
  have hptrs : PtrsIn (AddrTaken P) (writeCellsK .write s loc off [v]) :=
    ptrsIn_writeCellsK .write loc off [v] h.ptrs (fun w hw l' o' he => by
      simp only [List.mem_singleton] at hw; subst hw; exact hv l' o' he)
  refine ⟨hlive, hptrs, fun hr => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.run hr
  have hlog : (s.wr .write loc off v).log = s.log ++ [⟨s.tick, s.inCall, loc, off, .write⟩] := rfl
  have hmem : (s.wr .write loc off v).mem =
      fun l o => if l = loc ∧ o = off then v else s.mem l o := rfl
  have hlw : lwOf μ (s.wr .write loc off v).log (fun _ => none) =
      fun t => if t = μ.tcell loc off then some (loc, off)
        else lwOf μ s.log (fun _ => none) t := by
    rw [hlog, lwOf_append, lwOf_single_write _ _ rfl]
  refine ⟨?_, h2, ?_, ?_⟩
  · rw [hlog, clobber_append, h1, clobber_single_write _ _ rfl]; rfl
  · intro u o hm hc hP
    rw [hmem] at hm
    by_cases hu : u = loc ∧ o = off
    · obtain ⟨rfl, rfl⟩ := hu
      exact ⟨p, Nat.le_refl p, hacc hc hP⟩
    · simp only [hu, ↓reduceIte] at hm
      exact h3 u o hm hc hP
  · intro u o c hm hlwc hne
    rw [hmem] at hm
    rw [hlw] at hlwc
    by_cases hu : u = loc ∧ o = off
    · obtain ⟨rfl, rfl⟩ := hu
      simp only [↓reduceIte, Option.some.injEq] at hlwc
      exact absurd hlwc.symm hne
    · simp only [hu, ↓reduceIte] at hm
      by_cases ht : μ.tcell u o = μ.tcell loc off
      · simp only [ht, ↓reduceIte, Option.some.injEq] at hlwc
        subst hlwc
        obtain ⟨-, hsc, -⟩ := tcell_eq μ ht hne
        simp only [Forest.sameClass, Bool.and_eq_true] at hsc
        obtain ⟨⟨hcu, hcl⟩, -⟩ := hsc
        obtain ⟨hlu, hou⟩ := h.live u o hm
        exact conflict hpc hp ht hne hou hb (fun hP => h3 u o hm hcu hP)
          (fun _ => hL u hcu (h2 u hcu hlu))
          (inIv_at hp hcl hacc (hL loc hcl (h2 loc hcl hl)))
      · simp only [ht, ↓reduceIte] at hlwc
        exact h4 u o c hm hlwc hne

theorem good_wr_reset {L : Nat → Bool} {p : Nat} {s : St} {loc off : Nat}
    (h : Good pol P μ L p s) : Good pol P μ L p (s.wr .reset loc off .uninit) := by
  have hlive : LiveInv P (writeCellsK .reset s loc off (List.replicate 1 .uninit)) :=
    liveInv_writeUninit .reset loc off 1 h.live
  have hptrs : PtrsIn (AddrTaken P) (writeCellsK .reset s loc off (List.replicate 1 .uninit)) :=
    ptrsIn_writeCellsK .reset loc off _ h.ptrs (valsIn_replicate 1)
  refine ⟨hlive, hptrs, fun hr => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.run hr
  have hlog : (s.wr .reset loc off .uninit).log =
      s.log ++ [⟨s.tick, s.inCall, loc, off, .reset⟩] := rfl
  have hmem : (s.wr .reset loc off .uninit).mem =
      fun l o => if l = loc ∧ o = off then .uninit else s.mem l o := rfl
  have hlw : lwOf μ (s.wr .reset loc off .uninit).log (fun _ => none) =
      lwOf μ s.log (fun _ => none) := by
    rw [hlog, lwOf_append, lwOf_single_reset _ _ rfl]
  have hm' : ∀ u o, (s.wr .reset loc off .uninit).mem u o ≠ .uninit → s.mem u o ≠ .uninit := by
    intro u o hm
    rw [hmem] at hm
    by_cases hu : u = loc ∧ o = off
    · simp [hu] at hm
    · simpa [hu] using hm
  refine ⟨?_, h2, fun u o hm => h3 u o (hm' u o hm), fun u o c hm => ?_⟩
  · rw [hlog, clobber_append, h1, clobber_single_reset _ _ rfl]; rfl
  · rw [hlw]; exact h4 u o c (hm' u o hm)

theorem good_writeCells {L : Nat → Bool} {p : Nat} (hpc : PolicyCheck pol P μ) {loc : Nat}
    (hacc : Acc pol P μ p loc) (hp : p < 2 * P.code.length + 2)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p / 2) = true) :
    ∀ (vs : List Val) (s : St) (off : Nat), Good pol P μ L p s → s.live loc = true →
      off + vs.length ≤ P.size loc → ValsIn (AddrTaken P) vs →
      Good pol P μ L p (writeCellsK .write s loc off vs) := by
  intro vs
  induction vs with
  | nil => intro s off h _ _ _; exact h
  | cons v vs ih =>
    intro s off h hl hb hv
    simp only [List.length_cons] at hb
    exact ih _ _ (good_wr_write hpc h hl (by omega) hacc (hv v (List.mem_cons_self ..)) hp hL)
      hl (by omega) (fun w hw => hv w (List.mem_cons_of_mem _ hw))

theorem good_resetCells {L : Nat → Bool} {p : Nat} {loc : Nat} :
    ∀ (n : Nat) (s : St) (off : Nat), Good pol P μ L p s →
      Good pol P μ L p (writeCellsK .reset s loc off (List.replicate n .uninit)) := by
  intro n
  induction n with
  | zero => intro s off h; exact h
  | succ n ih =>
    intro s off h
    exact ih _ _ (good_wr_reset h)

theorem good_allocate {L L' : Nat → Bool} {p : Nat} {s : St} {x : Nat}
    (h : Good pol P μ L p s) (hLL : ∀ z, z ≠ x → L z = true → L' z = true)
    (hx : μ.inClass x = true → L' x = true) : Good pol P μ L' p (allocate P s x) := by
  unfold allocate
  split
  · apply good_resetCells
    refine ⟨liveInv_congr (s := s) rfl (fun l hl => ?_) h.live, ptrsIn_congr (s := s) rfl h.ptrs,
      fun hr => ?_⟩
    · by_cases hlx : l = x <;> simp [hlx, hl]
    · obtain ⟨h1, h2, h3, h4⟩ := h.run hr
      refine ⟨h1, fun z hz hlz => ?_, h3, h4⟩
      by_cases hzx : z = x
      · subst hzx; exact hx hz
      · simp only [hzx, ↓reduceIte] at hlz
        exact hLL z hzx (h2 z hz hlz)
  · exact good_fail h

theorem good_deallocate {L L' : Nat → Bool} {p : Nat} {s : St} {x : Nat}
    (h : Good pol P μ L p s) (hLL : ∀ z, z ≠ x → L z = true → L' z = true) :
    Good pol P μ L' p (deallocate P s x) := by
  have hlive := liveInv_deallocate P s x h.live
  revert hlive
  unfold deallocate
  split
  · intro hlive
    have h1 := good_resetCells (loc := x) (P.size x) s 0 h
    refine ⟨hlive, ptrsIn_congr rfl h1.ptrs, fun hr => ?_⟩
    obtain ⟨a, b, c, d⟩ := h1.run hr
    refine ⟨a, fun z hz hlz => ?_, c, d⟩
    by_cases hzx : z = x
    · subst hzx; simp at hlz
    · simp only [hzx, ↓reduceIte] at hlz
      exact hLL z hzx (b z hz hlz)
  · rename_i hx
    intro _
    refine ⟨h.live, h.ptrs, fun hr => ?_⟩
    obtain ⟨a, b, c, d⟩ := h.run hr
    refine ⟨a, fun z hz hlz => ?_, c, d⟩
    by_cases hzx : z = x
    · subst hzx; exact absurd hlz hx
    · exact hLL z hzx (b z hz hlz)

end Prims

section Ops

variable {pol : Policy} {P : Prog} {μ : Forest}

theorem good_readCells {L : Nat → Bool} {p loc : Nat} (hacc : Acc pol P μ p loc)
    (hp : p < 2 * P.code.length + 2) :
    ∀ (n : Nat) (s : St) (off : Nat), Good pol P μ L p s →
      Good pol P μ L p (readCells s loc off n).1 := by
  intro n
  induction n with
  | zero => intro s off h; exact h
  | succ n ih =>
    intro s off h
    unfold readCells
    by_cases hv : s.mem loc off = .uninit
    · simp only [hv, ↓reduceIte]
      exact ⟨h.live, h.ptrs, fun hr => by simp [St.fail] at hr⟩
    · simp only [hv, ↓reduceIte]
      have := ih (s.logAcc loc off .read) (off + 1) (good_read h hv hacc hp)
      rcases hr : readCells (s.logAcc loc off .read) loc (off + 1) n with ⟨s', _ | vs⟩ <;>
        rw [hr] at this <;> exact this

theorem good_readCells_eq {L : Nat → Bool} {p loc off n : Nat} {s s' : St}
    {r : Option (List Val)} (he : readCells s loc off n = (s', r)) (h : Good pol P μ L p s)
    (hacc : Acc pol P μ p loc) (hp : p < 2 * P.code.length + 2) : Good pol P μ L p s' := by
  have := good_readCells hacc hp n s off h
  rw [he] at this; exact this

theorem good_evalOp (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ) {L : Nat → Bool}
    {p : Nat} (hp : p < 2 * P.code.length + 2)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p / 2) = true)
    {ms : MoveSem} {s s' : St} {o : Operand} {r : Option (List Val)}
    (he : evalOp ms P s o = (s', r)) (h : Good pol P μ L p s)
    (hR : ∀ b, o.readsName b = true → Acc pol P μ p (aliasBase s.alias b)) :
    Good pol P μ L p s' := by
  cases o with
  | lit n =>
    simp only [evalOp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h
  | addrOf q =>
    simp only [evalOp] at he
    split at he
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact good_fail h
  | copy q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      have hacc : Acc pol P μ p r0.base := by
        rw [resolvePlace_base hr0]; exact hR q.base (by simp [Operand.readsName])
      exact good_readCells_eq he h hacc hp
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact good_fail h
  | move q =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      have hacc : Acc pol P μ p r0.base := by
        rw [resolvePlace_base hr0]; exact hR q.base (by simp [Operand.readsName])
      obtain ⟨hl0, hb0, -⟩ := resolvePlace_spec hr0
      split at he
      · rename_i s1 vs1 hrd
        have h1 := good_readCells_eq hrd h hacc hp
        obtain ⟨-, hl, -, -⟩ := readCells_eq hrd
        split at he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact good_writeCells hpc hacc hp hL _ s1 r0.off h1 (by rw [hl]; exact hl0)
            (by simp; omega) (valsIn_replicate _)
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact h1
      · rename_i s1 hrd
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact good_readCells_eq hrd h hacc hp
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact good_fail h
  | load q len =>
    simp only [evalOp] at he
    split at he
    · rename_i r0 hr0
      have hacc : Acc pol P μ p r0.base := by
        rw [resolvePlace_base hr0]; exact hR q.base (by simp [Operand.readsName])
      split at he
      · split at he
        · rename_i s1 l o hrd
          have h1 := good_readCells_eq hrd h hacc hp
          obtain ⟨-, -, -, hv⟩ := readCells_eq hrd
          have hat : AddrTaken P l := by
            have := hv [.ptr l o] rfl
            simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true,
              Nat.add_zero] at this
            exact h.ptrs r0.base r0.off l o this.symm
          split at he
          · exact good_readCells_eq he h1 (acc_of_addrTaken hpol hat) hp
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact good_fail h1
        · rename_i s1 x _ hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact good_fail (good_readCells_eq hrd h hacc hp)
        · rename_i s1 hrd
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact good_readCells_eq hrd h hacc hp
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact good_fail h
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact good_fail h

theorem good_evalOps (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ) {L : Nat → Bool}
    {p : Nat} (hp : p < 2 * P.code.length + 2)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p / 2) = true)
    {ms : MoveSem} (os : List Operand) :
    ∀ {s s' : St} {r : Option (List Val)}, evalOps ms P s os = (s', r) →
      Good pol P μ L p s →
      (∀ o ∈ os, ∀ b, o.readsName b = true → Acc pol P μ p (aliasBase s.alias b)) →
      Good pol P μ L p s' := by
  induction os with
  | nil =>
    intro s s' r he h _
    simp only [evalOps, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h
  | cons o os ih =>
    intro s s' r he h hos
    simp only [evalOps] at he
    split at he
    · rename_i s1 vs1 he1
      have h1 := good_evalOp hpol hpc hp hL he1 h (hos o (List.mem_cons_self ..))
      have hal := evalOp_alias he1
      split at he
      · rename_i s2 ws he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ih he2 h1 (fun o' ho' b hb => by
          rw [hal]; exact hos o' (List.mem_cons_of_mem _ ho') b hb)
      · rename_i s2 he2
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ih he2 h1 (fun o' ho' b hb => by
          rw [hal]; exact hos o' (List.mem_cons_of_mem _ ho') b hb)
    · rename_i s1 he1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact good_evalOp hpol hpc hp hL he1 h (hos o (List.mem_cons_self ..))

theorem good_emit {L : Nat → Bool} {p : Nat} {s : St} (e : Event) (h : Good pol P μ L p s) :
    Good pol P μ L p (s.emit e) :=
  good_congr h rfl rfl rfl rfl

theorem good_cmpOp (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ) {L : Nat → Bool}
    {p : Nat} (hp : p < 2 * P.code.length + 2)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p / 2) = true)
    (ms : MoveSem) (A : Layout) (s : St) (a b : Operand) (f : Nat → Nat → Bool)
    (h : Good pol P μ L p s)
    (ha : ∀ c, a.readsName c = true → Acc pol P μ p (aliasBase s.alias c))
    (hb : ∀ c, b.readsName c = true → Acc pol P μ p (aliasBase s.alias c)) :
    Good pol P μ L p (cmpOp ms P A s a b f) := by
  unfold cmpOp
  split
  · rename_i s1 va he1
    have h1 := good_evalOp hpol hpc hp hL he1 h ha
    have hb1 : ∀ c, b.readsName c = true → Acc pol P μ p (aliasBase s1.alias c) := by
      rw [evalOp_alias he1]; exact hb
    split
    · rename_i s2 vb he2
      have h2 := good_evalOp hpol hpc hp hL he2 h1 hb1
      split
      · exact good_emit _ h2
      · exact good_fail h2
    · rename_i s2 _ _ he2; exact good_fail (good_evalOp hpol hpc hp hL he2 h1 hb1)
    · rename_i s2 he2; exact good_evalOp hpol hpc hp hL he2 h1 hb1
  · rename_i s1 _ _ he1; exact good_fail (good_evalOp hpol hpc hp hL he1 h ha)
  · rename_i s1 he1; exact good_evalOp hpol hpc hp hL he1 h ha

end Ops

/-! ## Statements -/

/-- The by-name reads of `st` (operands and the pointer cell of a `store`) are licensed at
`p` under the alias `al`. -/
def CtxR (pol : Policy) (P : Prog) (μ : Forest) (p : Nat) (al : Option (Nat × Place))
    (st : Stmt) : Prop :=
  (∀ o ∈ st.operands, ∀ b, o.readsName b = true → Acc pol P μ p (aliasBase al b)) ∧
  (∀ q v, st = .store q v → Acc pol P μ p (aliasBase al q.base))

/-- The left side of an assignment `st` is licensed at `p` under the alias `al`. -/
def CtxW (pol : Policy) (P : Prog) (μ : Forest) (p : Nat) (al : Option (Nat × Place))
    (st : Stmt) : Prop :=
  ∀ lhs rhs, st = .assign lhs rhs → Acc pol P μ p (aliasBase al lhs.base)

section Stmts

variable {pol : Policy} {P : Prog} {μ : Forest}

theorem good_of_not_running {L : Nat → Bool} {p : Nat} {s : St} (hl : LiveInv P s)
    (hp : PtrsIn (AddrTaken P) s) (hs : s.status ≠ .running) : Good pol P μ L p s :=
  ⟨hl, hp, fun hr => absurd hr hs⟩

theorem good_execBasic (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ)
    {L : Nat → Bool} {t p1 p2 : Nat} (ht : t < P.code.length) (hp1 : p1 / 2 = t)
    (hp2 : p2 / 2 = t) (hp12 : p1 ≤ p2)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x t = true)
    (ms : MoveSem) (A : Layout) (s : St) (st : Stmt) (h : Good pol P μ L p1 s)
    (hS : ∀ x, (st = .storageLive x ∨ st = .storageDead x) → s.inCall = true)
    (hR : CtxR pol P μ p1 s.alias st) (hW : CtxW pol P μ p2 s.alias st)
    (hT : ∀ b, st.takesAddr b = true → AddrTaken P (aliasBase s.alias b)) :
    Good pol P μ L p2 (execBasic ⟨ms, .atomic⟩ P A s st) := by
  have hpp1 : p1 < 2 * P.code.length + 2 := by omega
  have hpp2 : p2 < 2 * P.code.length + 2 := by omega
  have hL1 : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p1 / 2) = true := by
    rw [hp1]; exact hL
  have hL2 : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x (p2 / 2) = true := by
    rw [hp2]; exact hL
  have hmono : ∀ {s'}, Good pol P μ L p1 s' → Good pol P μ L p2 s' :=
    fun h' => good_mono h' (fun _ hx => hx) hp12
  unfold execBasic
  split
  · exact hmono h
  · cases st with
    | storageLive x =>
      simp only; split
      · exact good_fail h
      · rename_i hc; exact absurd (hS x (Or.inl rfl)) hc
    | storageDead x =>
      simp only; split
      · exact good_fail h
      · rename_i hc; exact absurd (hS x (Or.inr rfl)) hc
    | assign lhs rhs =>
      simp only; split
      · exact good_fail h
      · rename_i hsum
        split
        · exact good_fail h
        · rename_i r hr
          obtain ⟨hlr, hbr, hlenr⟩ := resolvePlace_spec hr
          split
          · rename_i s' vs he
            have h1 := good_evalOps hpol hpc hpp1 hL1 rhs he h hR.1
            obtain ⟨-, hl1, hlen⟩ := liveInv_evalOps rhs he h.live
            have hv := (ptrsIn_evalOps rhs he h.ptrs (fun o ho b hb =>
              hT b (List.any_eq_true.mpr ⟨o, ho, hb⟩))).2 vs rfl
            have hacc : Acc pol P μ p2 r.base := by
              rw [resolvePlace_base hr]; exact hW lhs rhs rfl
            exact good_writeCells hpc hacc hpp2 hL2 vs s' r.off (hmono h1)
              (by rw [hl1]; exact hlr) (by rw [hlen vs rfl]; omega) hv
          · rename_i s' he
            exact hmono (good_evalOps hpol hpc hpp1 hL1 rhs he h hR.1)
    | store q v =>
      have hv : ∀ b, v.takesAddr b = true → AddrTaken P (aliasBase s.alias b) := hT
      simp only; split
      · rename_i r hr
        have hacc : Acc pol P μ p1 r.base := by
          rw [resolvePlace_base hr]; exact hR.2 q v rfl
        split
        · split
          · rename_i s1 l o he1
            have h1 := good_readCells_eq he1 h hacc hpp1
            obtain ⟨-, -, hal1, hvs1⟩ := readCells_eq he1
            have hat : AddrTaken P l := by
              have := hvs1 [.ptr l o] rfl
              simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true,
                Nat.add_zero] at this
              exact h.ptrs r.base r.off l o this.symm
            have hR1 : ∀ b, v.readsName b = true → Acc pol P μ p1 (aliasBase s1.alias b) := by
              rw [hal1]; exact hR.1 v (by simp [Stmt.operands])
            have hv1 : ∀ b, v.takesAddr b = true → AddrTaken P (aliasBase s1.alias b) := by
              rw [hal1]; exact hv
            split
            · rename_i s2 vs he2
              have h2 := good_evalOp hpol hpc hpp1 hL1 he2 h1 hR1
              have hvs := (ptrsIn_evalOp he2 h1.ptrs hv1).2 vs rfl
              split
              · rename_i hc
                exact hmono (good_writeCells hpc (acc_of_addrTaken hpol hat) hpp1 hL1 vs s2 o
                  h2 hc.1 hc.2 hvs)
              · exact good_fail h2
            · rename_i s2 he2
              exact hmono (good_evalOp hpol hpc hpp1 hL1 he2 h1 hR1)
          · rename_i s1 _ _ he1
            exact good_fail (good_readCells_eq he1 h hacc hpp1)
          · rename_i s1 he1
            exact hmono (good_readCells_eq he1 h hacc hpp1)
        · exact good_fail h
      · exact good_fail h
    | ptrEq a b =>
      exact hmono (good_cmpOp hpol hpc hpp1 hL1 ms A s a b _ h
        (hR.1 a (by simp [Stmt.operands])) (hR.1 b (by simp [Stmt.operands])))
    | ptrInRange a b n =>
      exact hmono (good_cmpOp hpol hpc hpp1 hL1 ms A s a b _ h
        (hR.1 a (by simp [Stmt.operands])) (hR.1 b (by simp [Stmt.operands])))
    | out o =>
      simp only; split
      · rename_i s' vs he
        exact hmono (good_emit _ (good_evalOp hpol hpc hpp1 hL1 he h
          (hR.1 o (by simp [Stmt.operands]))))
      · rename_i s' he
        exact hmono (good_evalOp hpol hpc hpp1 hL1 he h (hR.1 o (by simp [Stmt.operands])))
    | call fn a => exact good_fail h
    | nop => exact hmono h

theorem good_execCallee (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ)
    {L : Nat → Bool} {t p : Nat} (ht : t < P.code.length) (hp : p / 2 = t)
    (hL : ∀ x, μ.inClass x = true → L x = true → LexLiveAt P x t = true)
    (ms : MoveSem) (A : Layout) (b : List Stmt) :
    ∀ s, Good pol P μ L p s → s.inCall = true →
      (∀ st ∈ b, CtxR pol P μ p s.alias st ∧ CtxW pol P μ p s.alias st ∧
        ∀ x, st.takesAddr x = true → AddrTaken P (aliasBase s.alias x)) →
      Good pol P μ L p (execCallee ⟨ms, .atomic⟩ P A s b) := by
  induction b with
  | nil => intro s h _ _; exact h
  | cons st b ih =>
    intro s h hc hb
    simp only [execCallee, List.foldl_cons]
    have hst := step_execBasic ⟨ms, .atomic⟩ P A s st
    obtain ⟨h1, h2, h3⟩ := hb st (List.mem_cons_self ..)
    apply ih
    · exact good_execBasic hpol hpc ht hp hp (Nat.le_refl p) hL ms A s st h
        (fun _ _ => hc) h1 h2 h3
    · rw [hst.inCall]; exact hc
    · intro st' hst'
      rw [hst.alias]
      exact hb st' (List.mem_cons_of_mem _ hst')

end Stmts

/-! ## Static facts about the top-level code -/

section Static

variable {pol : Policy} {P : Prog} {μ : Forest}

theorem getD_code (P : Prog) (t : Nat) (ht : t < P.code.length) :
    P.code.getD t .nop = P.code[t] := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem acc_of_accessPt {p x : Nat} (h : AccessPt P x p = true) : Acc pol P μ p x :=
  fun _ _ => h

theorem accessPt_even (P : Prog) (x t : Nat) :
    AccessPt P x (2 * t) = ((P.code.getD t .nop).calleeTouchesByName P x ||
      (P.code.getD t .nop).readsByName P x) := by
  have h1 : 2 * t / 2 = t := by omega
  have h2 : 2 * t % 2 = 0 := by omega
  simp only [AccessPt, h1, h2, ↓reduceIte]

theorem accessPt_odd (P : Prog) (x t : Nat) :
    AccessPt P x (2 * t + 1) = ((P.code.getD t .nop).calleeTouchesByName P x ||
      (P.code.getD t .nop).writesByName P x) := by
  have h1 : (2 * t + 1) / 2 = t := by omega
  have h2 : (2 * t + 1) % 2 = 1 := by omega
  simp only [AccessPt, h1, h2]
  rfl

theorem ctxR_top {t : Nat} {st : Stmt} (hst : P.code.getD t .nop = st) :
    CtxR pol P μ (2 * t) none st := by
  refine ⟨fun o ho b hb => acc_of_accessPt ?_, fun q v hq => acc_of_accessPt ?_⟩
  · show AccessPt P b (2 * t) = true
    rw [accessPt_even, hst]
    have : st.readsByName P b = true := by
      unfold Stmt.readsByName
      simp only [Bool.or_eq_true]
      exact Or.inl (Or.inl (List.any_eq_true.mpr ⟨o, ho, hb⟩))
    simp [this]
  · show AccessPt P q.base (2 * t) = true
    rw [accessPt_even, hst, hq]
    have : (Stmt.store q v).readsByName P q.base = true := by
      unfold Stmt.readsByName; simp
    simp [this]

theorem ctxW_top {t : Nat} {st : Stmt} (hst : P.code.getD t .nop = st) :
    CtxW pol P μ (2 * t + 1) none st := by
  intro lhs rhs hq
  apply acc_of_accessPt
  show AccessPt P lhs.base (2 * t + 1) = true
  rw [accessPt_odd, hst, hq]
  have : (Stmt.assign lhs rhs).writesByName P lhs.base = true := by
    unfold Stmt.writesByName; simp
  simp [this]

theorem accessPt_callee {t fn : Nat} {arg : Operand}
    (hst : P.code.getD t .nop = .call fn arg) {st' : Stmt}
    {b : Nat} (hb : (st'.operands.any (Operand.readsName b) ||
      (match st' with | .store p _ => p.base == b | .assign lhs _ => lhs.base == b | _ => false))
        = true) (hst' : st' ∈ (P.fn fn).body) :
    AccessPt P b (2 * t + 1) = true := by
  rw [accessPt_odd, hst]
  have : (Stmt.call fn arg).calleeTouchesByName P b = true :=
    List.any_eq_true.mpr ⟨st', hst', hb⟩
  simp [this]

theorem acc_alias {t fn : Nat} {arg : Operand} (hst : P.code.getD t .nop = .call fn arg)
    (al : Option (Nat × Place))
    (hal : ∀ prm r, al = some (prm, r) → ∃ q, arg = .move q ∧ r.base = q.base)
    {b : Nat} (hb : AccessPt P b (2 * t + 1) = true) :
    Acc pol P μ (2 * t + 1) (aliasBase al b) := by
  cases al with
  | none => exact acc_of_accessPt hb
  | some pr =>
    obtain ⟨prm, r⟩ := pr
    obtain ⟨q, rfl, hrq⟩ := hal prm r rfl
    simp only [aliasBase]
    split
    · rw [hrq]
      apply acc_of_accessPt
      rw [accessPt_odd, hst]
      have : (Stmt.call fn (.move q)).writesByName P q.base = true := by
        unfold Stmt.writesByName; simp
      simp [this]
    · exact acc_of_accessPt hb

theorem ctx_callee {t fn : Nat} {arg : Operand} (hst : P.code.getD t .nop = .call fn arg)
    (al : Option (Nat × Place))
    (hal : ∀ prm r, al = some (prm, r) → ∃ q, arg = .move q ∧ r.base = q.base)
    {st' : Stmt} (hst' : st' ∈ (P.fn fn).body) :
    CtxR pol P μ (2 * t + 1) al st' ∧ CtxW pol P μ (2 * t + 1) al st' := by
  refine ⟨⟨fun o ho b hb => acc_alias hst al hal (accessPt_callee hst ?_ hst'),
    fun q v hq => acc_alias hst al hal (accessPt_callee hst ?_ hst')⟩,
    fun lhs rhs hq => acc_alias hst al hal (accessPt_callee hst ?_ hst')⟩
  · simp only [Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨o, ho, hb⟩
  · subst hq; simp
  · subst hq; simp

theorem takesAddr_callee {fn : Nat} {arg : Operand} (hmem : Stmt.call fn arg ∈ P.code)
    (al : Option (Nat × Place))
    (hal : ∀ prm r, al = some (prm, r) →
      ∃ q, arg = .move q ∧ r.base = q.base ∧ prm = (P.fn fn).prm)
    {st' : Stmt} (hst' : st' ∈ (P.fn fn).body) :
    ∀ x, st'.takesAddr x = true → AddrTaken P (aliasBase al x) := by
  intro x hx
  cases al with
  | none => exact (addrDisc_addrTaken P).2.1 fn st' hst' x hx
  | some pr =>
    obtain ⟨prm, r⟩ := pr
    obtain ⟨q, rfl, hrq, hprm⟩ := hal prm r rfl
    simp only [aliasBase]
    split
    · rename_i hxp
      rw [hrq]
      subst hxp
      rw [hprm] at hx
      exact (addrDisc_addrTaken P).2.2 fn q hmem (List.any_eq_true.mpr ⟨st', hst', hx⟩)
    · exact (addrDisc_addrTaken P).2.1 fn st' hst' x hx

theorem lexLiveBefore_succ (P : Prog) (x t : Nat) (ht : t < P.code.length) :
    lexLiveBefore P x (t + 1) =
      (match P.code[t] with
       | .storageLive y => if y == x then true else lexLiveBefore P x t
       | .storageDead y => if y == x then false else lexLiveBefore P x t
       | _ => lexLiveBefore P x t) := by
  unfold lexLiveBefore
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append]
  rfl

theorem lexLiveAt_of_succ (P : Prog) (x t : Nat) (ht : t < P.code.length)
    (h : lexLiveBefore P x (t + 1) = true) : LexLiveAt P x t = true := by
  unfold LexLiveAt
  rw [lexLiveBefore_succ P x t ht] at h
  rw [getD_code P t ht]
  revert h
  cases P.code[t] with
  | storageLive y =>
    intro h
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy] at h; simp [h]
  | storageDead y =>
    intro h
    by_cases hy : y = x
    · subst hy; simp at h
    · simp [hy] at h; simp [h]
  | _ => intro h; simp [h]

theorem fn_mem_of_call (hwf : ForestWF P μ) {fn : Nat} {arg : Operand}
    (hmem : Stmt.call fn arg ∈ P.code) : P.fn fn ∈ P.fns := by
  have hcb := hwf.2.2.2.2
  unfold CallsInBounds at hcb
  have := List.all_eq_true.mp hcb _ hmem
  simp only [decide_eq_true_eq] at this
  have hf : P.fn fn = P.fns[fn] := by simp [Prog.fn, List.getD_eq_getElem?_getD, this]
  rw [hf]; exact List.getElem_mem this

end Static

/-! ## Top-level statements and the run -/

section Run

variable {pol : Policy} {P : Prog} {μ : Forest}

theorem good_top_basic (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ)
    (ms : MoveSem) (A : Layout) (t : Nat) (ht : t < P.code.length) (st : Stmt)
    (hg : P.code.getD t .nop = st) (hmem : st ∈ P.code)
    (hS : ∀ x, (st = .storageLive x ∨ st = .storageDead x) → False)
    (hLeq : ∀ x, lexLiveBefore P x (t + 1) = lexLiveBefore P x t)
    (s : St) (ha : s.alias = none)
    (h : Good pol P μ (fun x => lexLiveBefore P x t) (2 * t) s) :
    Good pol P μ (fun x => lexLiveBefore P x (t + 1)) (2 * t + 1)
      (execBasic ⟨ms, .atomic⟩ P A s st) := by
  have hfun : (fun x => lexLiveBefore P x (t + 1)) = fun x => lexLiveBefore P x t :=
    funext hLeq
  rw [hfun]
  refine good_execBasic hpol hpc ht (by omega) (by omega) (by omega) ?_ ms A s st h
    (fun x hx => absurd hx (fun h' => hS x h')) (by rw [ha]; exact ctxR_top hg)
    (by rw [ha]; exact ctxW_top hg)
    (fun b hb => by rw [ha]; exact (addrDisc_addrTaken P).1 _ hmem b hb)
  intro x _ hx
  simp [LexLiveAt, hx]

theorem good_execStmt (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ)
    (hwf : ForestWF P μ) (ms : MoveSem) (A : Layout) (t : Nat) (ht : t < P.code.length)
    (s : St) (hc : s.inCall = false) (ha : s.alias = none)
    (h : Good pol P μ (fun x => lexLiveBefore P x t) (2 * t) s) :
    Good pol P μ (fun x => lexLiveBefore P x (t + 1)) (2 * t + 1)
      (execStmt ⟨ms, .atomic⟩ P A s P.code[t]) := by
  have hg := getD_code P t ht
  have hmem : P.code[t] ∈ P.code := List.getElem_mem ht
  have hsucc := fun x => lexLiveBefore_succ P x t ht
  have hL' : ∀ x, μ.inClass x = true → lexLiveBefore P x (t + 1) = true →
      LexLiveAt P x t = true := fun x _ hx => lexLiveAt_of_succ P x t ht hx
  have hpp : 2 * t + 1 < 2 * P.code.length + 2 := by omega
  have hL2 : ∀ x, μ.inClass x = true → lexLiveBefore P x (t + 1) = true →
      LexLiveAt P x ((2 * t + 1) / 2) = true := by
    have : (2 * t + 1) / 2 = t := by omega
    rw [this]; exact hL'
  generalize P.code[t] = st at hg hmem hsucc ⊢
  unfold execStmt
  split
  · rename_i hns; exact good_of_not_running h.live h.ptrs hns
  · rename_i hrun
    have hrun' : s.status = .running := by
      cases hs : s.status
      · rfl
      · rw [hs] at hrun; exact absurd (by decide) hrun
    cases st with
    | storageLive y =>
      show Good _ _ _ _ _ (execBasic _ P A s (.storageLive y))
      unfold execBasic
      simp only [hrun', hc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true]
      refine good_allocate (good_mono h (fun _ hx => hx) (by omega)) (fun z hz hlz => ?_)
        (fun _ => ?_)
      · rw [hsucc z]; simp [Ne.symm hz, hlz]
      · rw [hsucc y]; simp
    | storageDead y =>
      show Good _ _ _ _ _ (execBasic _ P A s (.storageDead y))
      unfold execBasic
      simp only [hrun', hc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true]
      refine good_deallocate (good_mono h (fun _ hx => hx) (by omega)) (fun z hz hlz => ?_)
      rw [hsucc z]; simp [Ne.symm hz, hlz]
    | call fn arg =>
      have hLeq : ∀ x, lexLiveBefore P x (t + 1) = lexLiveBefore P x t := fun x => hsucc x
      have hLL : ∀ x, lexLiveBefore P x t = true → lexLiveBefore P x (t + 1) = true :=
        fun x hx => by rw [hLeq]; exact hx
      have hfn := fn_mem_of_call hwf hmem
      have hprm : μ.inClass (P.fn fn).prm = false := hwf.2.2.2.1 _ hfn
      have h1 : Good pol P μ (fun x => lexLiveBefore P x (t + 1)) (2 * t + 1) s :=
        good_mono h hLL (by omega)
      simp only
      split
      · next q =>
        split
        · exact good_fail h
        · next r hr =>
          have hrq : r.base = q.base := by rw [resolvePlace_base hr, ha]; rfl
          split
          · exact good_fail h
          · have hs4 : Good pol P μ (fun x => lexLiveBefore P x (t + 1)) (2 * t + 1)
                (execCallee ⟨.inPlaceCall, .atomic⟩ P A
                  { s with alias := some ((P.fn fn).prm, r), inCall := true } (P.fn fn).body) := by
              refine good_execCallee hpol hpc ht (by omega) hL' _ A _ _
                (good_congr h1 rfl rfl rfl rfl) rfl ?_
              intro st' hst'
              have hc := ctx_callee (pol := pol) (μ := μ) hg (some ((P.fn fn).prm, r))
                (fun prm r' he => by
                  simp only [Option.some.injEq, Prod.mk.injEq] at he
                  obtain ⟨-, rfl⟩ := he
                  exact ⟨q, rfl, hrq⟩) hst'
              refine ⟨hc.1, hc.2, takesAddr_callee hmem _ (fun prm r' he => ?_) hst'⟩
              simp only [Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              exact ⟨q, rfl, hrq, rfl⟩
            exact good_congr hs4 rfl rfl rfl rfl
      · split
        · rename_i s1 vs he
          have hR : ∀ b, arg.readsName b = true → Acc pol P μ (2 * t) (aliasBase s.alias b) := by
            rw [ha]; exact (ctxR_top hg).1 arg (by simp [Stmt.operands])
          have hT : ∀ b, arg.takesAddr b = true → AddrTaken P (aliasBase s.alias b) := by
            rw [ha]
            exact fun b hb => (addrDisc_addrTaken P).1 _ hmem b (by simp [Stmt.takesAddr, hb])
          have hL0 : ∀ x, μ.inClass x = true → lexLiveBefore P x t = true →
              LexLiveAt P x (2 * t / 2) = true := by
            have : 2 * t / 2 = t := by omega
            rw [this]; intro x _ hx; simp [LexLiveAt, hx]
          have hs1 := good_evalOp hpol hpc (by omega) hL0 he h hR
          have hvs := (ptrsIn_evalOp he h.ptrs hT).2 vs rfl
          have hal1 : s1.alias = none := (evalOp_alias he).trans ha
          split
          · exact good_fail hs1
          · rename_i hcond
            simp only [ne_eq, not_or, Decidable.not_not, Bool.not_eq_true] at hcond
            have hs1' := good_mono (p' := 2 * t + 1) hs1 hLL (by omega)
            have hs2 := good_allocate (L' := fun x => lexLiveBefore P x (t + 1)) (x := (P.fn fn).prm)
              hs1' (fun _ _ hz => hz) (fun hx => by rw [hprm] at hx; cases hx)
            have hacc : Acc pol P μ (2 * t + 1) (P.fn fn).prm := fun hx => by
              rw [hprm] at hx; cases hx
            have hs3 : Good pol P μ (fun x => lexLiveBefore P x (t + 1)) (2 * t + 1)
                (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs) := by
              rcases allocate_live_or P s1 (P.fn fn).prm with hl | hz
              · exact good_writeCells hpc hacc hpp hL2 vs _ 0 hs2 hl (by omega) hvs
              · have : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst this
                exact hs2
            have hal3 : (writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias =
                none := by
              rw [(step_writeCells _ _ _ _).alias, (step_allocate _ _ _).alias, hal1]
            have hs4 : Good pol P μ (fun x => lexLiveBefore P x (t + 1)) (2 * t + 1)
                (execCallee ⟨ms, .atomic⟩ P A
                  { writeCells (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs with
                    inCall := true } (P.fn fn).body) := by
              refine good_execCallee hpol hpc ht (by omega) hL' ms A _ _
                (good_congr hs3 rfl rfl rfl rfl) rfl ?_
              intro st' hst'
              show CtxR pol P μ (2 * t + 1) (writeCells (allocate P s1 (P.fn fn).prm)
                  (P.fn fn).prm 0 vs).alias st' ∧ CtxW pol P μ (2 * t + 1) (writeCells
                  (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias st' ∧
                  ∀ x, st'.takesAddr x = true → AddrTaken P (aliasBase (writeCells
                  (allocate P s1 (P.fn fn).prm) (P.fn fn).prm 0 vs).alias x)
              rw [hal3]
              have hc := ctx_callee (pol := pol) (μ := μ) hg none
                (fun _ _ he => by cases he) hst'
              exact ⟨hc.1, hc.2, takesAddr_callee hmem none (fun _ _ he => by cases he) hst'⟩
            exact good_deallocate (good_congr hs4 rfl rfl rfl rfl) (fun _ _ hz => hz)
        · rename_i s1 he
          have hR : ∀ b, arg.readsName b = true → Acc pol P μ (2 * t) (aliasBase s.alias b) := by
            rw [ha]; exact (ctxR_top hg).1 arg (by simp [Stmt.operands])
          have hL0 : ∀ x, μ.inClass x = true → lexLiveBefore P x t = true →
              LexLiveAt P x (2 * t / 2) = true := by
            have : 2 * t / 2 = t := by omega
            rw [this]; intro x _ hx; simp [LexLiveAt, hx]
          exact good_mono (good_evalOp hpol hpc (by omega) hL0 he h hR) hLL (by omega)
    | assign lhs rhs =>
      exact good_top_basic hpol hpc ms A t ht _ hg hmem (fun x hx => by rcases hx with hx | hx <;> cases hx)
        (fun x => hsucc x) s ha h
    | store q v =>
      exact good_top_basic hpol hpc ms A t ht _ hg hmem (fun x hx => by rcases hx with hx | hx <;> cases hx)
        (fun x => hsucc x) s ha h
    | ptrEq a b =>
      exact good_top_basic hpol hpc ms A t ht _ hg hmem (fun x hx => by rcases hx with hx | hx <;> cases hx)
        (fun x => hsucc x) s ha h
    | ptrInRange a b n =>
      exact good_top_basic hpol hpc ms A t ht _ hg hmem (fun x hx => by rcases hx with hx | hx <;> cases hx)
        (fun x => hsucc x) s ha h
    | out o =>
      exact good_top_basic hpol hpc ms A t ht _ hg hmem (fun x hx => by rcases hx with hx | hx <;> cases hx)
        (fun x => hsucc x) s ha h
    | nop =>
      exact good_top_basic hpol hpc ms A t ht _ hg hmem (fun x hx => by rcases hx with hx | hx <;> cases hx)
        (fun x => hsucc x) s ha h

theorem good_runAt (hpol : pol true = .lexical) (hpc : PolicyCheck pol P μ)
    (hwf : ForestWF P μ) (ms : MoveSem) (A : Layout) :
    ∀ t, t ≤ P.code.length →
      Good pol P μ (fun x => lexLiveBefore P x t) (2 * t) (runAt ⟨ms, .atomic⟩ P A t) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [runAt_zero]
    refine ⟨liveInv_init P, ptrsIn_init _, fun _ => ⟨rfl, ?_, ?_, ?_⟩⟩
    · intro x _ hx; simp [St.init] at hx
    · intro u o hm; exact absurd rfl hm
    · intro u o c hm; exact absurd rfl hm
  | succ t ih =>
    intro ht
    have ht' : t < P.code.length := by omega
    obtain ⟨-, hc, ha, -⟩ := runAt_frame ⟨ms, .atomic⟩ P A t (by omega)
    rw [runAt_succ _ _ _ _ ht']
    have := good_execStmt hpol hpc hwf ms A t ht' _ hc ha (ih (by omega))
    exact good_mono (good_congr this rfl rfl rfl rfl) (fun _ hx => hx) (by omega)

end Run

theorem classAddrDisjoint_of_policyCheck (pol : Policy) (h : pol true = .lexical) (P : Prog)
    (μ : Forest) (hpc : PolicyCheck pol P μ) : ClassAddrDisjoint P μ := by
  intro u hu v hv hne hsc hwo hau hav
  have := hpc u hu v hv hne hsc hwo
  rw [decide_eq_true hau, decide_eq_true hav, h] at this
  exact this

theorem noValueClobberStmt_of_policyCheck (pol : Policy) (h : pol true = .lexical) (ms : MoveSem)
    (P : Prog) (μ : Forest) (hwf : ForestWF P μ) (hpc : PolicyCheck pol P μ) :
    NoValueClobberStmt ms μ P := by
  intro A hub hbad
  have hg := good_runAt h hpc hwf ms A P.code.length (Nat.le_refl _)
  rw [← run_eq_runAt] at hg
  have hs : (run ⟨ms, .atomic⟩ P A).status = .running := by
    cases hst : (run ⟨ms, .atomic⟩ P A).status with
    | running => rfl
    | ub =>
      exfalso
      unfold outcome at hub hbad
      cases hl : layoutOK P A (run ⟨ms, .atomic⟩ P A).conflicts <;> simp [hl, hst] at hub hbad
  exact (hg.run hs).1

end Pol

open Pol

/-- Sufficiency: a policy that uses lexical intervals for address-taken locals is sound, whatever
it uses for the other locals (in particular precise liveness). -/
theorem policySound_of_lexical_for_addrTaken (pol : Policy) (h : pol true = .lexical) :
    PolicySound pol := by
  intro ms P μ hwf hpc
  exact coalesce_refines_of_noValueClobber_of_classAddrDisjoint ms P μ hwf
    (noValueClobberStmt_of_policyCheck pol h ms P μ hwf hpc)
    (classAddrDisjoint_of_policyCheck pol h P μ hpc)

end Toy.Coalesce
