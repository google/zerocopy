import ToySlotCompact.Basic

/-!
# Lockstep bisimulation for compacted programs
-/

namespace Toy.SlotCompact

variable {N M : Nat}

/-- Rewriting through `π` preserves evaluation when every slot read is kept and the compacted
store holds its value at its new index. -/
theorem eval_compactExpr {p : Prog N} {L : Ann N} (π : Compaction p L M) {σ : Store N}
    {σ' : Store M} (e : Expr N)
    (h : ∀ i, e.reads i = true → ∃ hk : Kept p L i = true, σ' (π ⟨i, hk⟩) = σ i) :
    (compactExpr π e).eval σ' = e.eval σ := by
  induction e with
  | const n => rfl
  | slot j =>
    obtain ⟨hk, hv⟩ := h j (by simp [Expr.reads])
    simp [compactExpr, Expr.subst, Compaction.slotExpr, π.get?_of_kept hk, Expr.eval, hv]
  | add a b iha ihb =>
    show (compactExpr π a).eval σ' + (compactExpr π b).eval σ' = a.eval σ + b.eval σ
    rw [iha (fun i hi => h i (by simp [Expr.reads, hi])),
      ihb (fun i hi => h i (by simp [Expr.reads, hi]))]

/-- Evaluation agreement for an expression read at a point where every slot it reads is live. -/
theorem eval_compactExpr_of_live {p : Prog N} {L : Ann N} (π : Compaction p L M) {pc : Nat}
    {ins : Instr N} (hins : p[pc]? = some ins) {σ : Store N} {σ' : Store M}
    (hst : ∀ (i : Fin N) (h : Kept p L i = true), L pc i = true → σ' (π ⟨i, h⟩) = σ i)
    {e : Expr N} (hlive : ∀ i, e.reads i = true → L pc i = true) :
    (compactExpr π e).eval σ' = e.eval σ :=
  eval_compactExpr π e fun i hi =>
    ⟨kept_of_getElem? hins (hlive i hi), hst i _ (hlive i hi)⟩

/-- Output agreement at a `halt`: if every output slot is kept and the compacted store holds its
value at its new index, the compacted `halt` emits the same output values. -/
theorem map_filterMap_get? {p : Prog N} {L : Ann N} (π : Compaction p L M) {σ : Store N}
    {σ' : Store M} : ∀ (outs : List (Fin N)),
      (∀ i ∈ outs, ∃ hk : Kept p L i = true, σ' (π ⟨i, hk⟩) = σ i) →
      (outs.filterMap π.get?).map σ' = outs.map σ
  | [], _ => rfl
  | i :: rest, h => by
    obtain ⟨hk, hv⟩ := h i (by simp)
    simp [List.filterMap, π.get?_of_kept hk, hv,
      map_filterMap_get? π rest (fun j hj => h j (by simp [hj]))]

/-- Relation after a write: if every kept slot live afterwards is either the written slot (with
the right value) or untouched and live before, the relation is re-established. -/
private theorem rel_after_write {p : Prog N} {L : Ann N} {π : Compaction p L M}
    {pc : Nat} {ins : Instr N} (hins : p[pc]? = some ins) (hT : TransferClosed p L)
    {σ : Store N} {σ' : Store M}
    (hst : ∀ (i : Fin N) (h : Kept p L i = true), L pc i = true → σ' (π ⟨i, h⟩) = σ i)
    (hsucc : pc + 1 ∈ ins.succs pc) (d : Fin N) (hdef : ∀ i, ins.defs i = true ↔ i = d)
    (v : Nat) (σ1' : Store M)
    (hwrite : ∀ (hd : Kept p L d = true), L (pc + 1) d = true → σ1' (π ⟨d, hd⟩) = v)
    (hframe : ∀ (i : Fin N) (hi : Kept p L i = true), i ≠ d → L (pc + 1) i = true →
      σ1' (π ⟨i, hi⟩) = σ' (π ⟨i, hi⟩)) :
    ∀ (i : Fin N) (h : Kept p L i = true), L (pc + 1) i = true → σ1' (π ⟨i, h⟩) = upd σ d v i := by
  intro i hi hl
  by_cases hid : i = d
  · subst hid
    rw [upd_same]
    exact hwrite hi hl
  · rw [upd_other _ _ hid, hframe i hi hid hl]
    apply hst i hi
    apply hT pc ins hins (pc + 1) hsucc i hl
    cases h : ins.defs i
    · rfl
    · exact absurd ((hdef i).mp h) hid

/-- One step of the original and the compacted program from `CompactRel`-related states gives
`CompactRel`-related results, ignoring events. -/
theorem compact_silentBisim_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) :
    SilentBisim p (compact p L π) (CompactRel p L π) := by
  rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨hpc, hst⟩
  simp only at hpc hst
  subst pc'
  cases hins : p[pc]? with
  | none =>
    rw [step_of_getElem?_none (s := ⟨pc, σ⟩) hins,
      step_compact_of_getElem?_none π hins σ']
    trivial
  | some ins =>
    rw [step_of_getElem? (s := ⟨pc, σ⟩) hins,
      step_compact_of_getElem? π hins σ']
    have hlive : ∀ {e : Expr N}, (∀ i, e.reads i = true → ins.uses i = true) →
        (compactExpr π e).eval σ' = e.eval σ := fun hu =>
      eval_compactExpr_of_live π hins hst (fun i hi => hR pc ins hins i (hu i hi))
    have hkeep : ∀ (s : Nat), s ∈ ins.succs pc → (∀ i, ins.defs i = false) →
        ∀ (i : Fin N) (h : Kept p L i = true), L s i = true → σ' (π ⟨i, h⟩) = σ i :=
      fun s hs hnd i h hl => hst i h (hT pc ins hins s hs i hl (hnd i))
    -- a write of value `v` to slot `d` (assignment or marker), given the clobber condition
    have hwrite : ∀ (d : Fin N) (v v' : Nat), (∀ i, ins.defs i = true ↔ i = d) →
        pc + 1 ∈ ins.succs pc → v' = v →
        (∀ (hd : Kept p L d = true) (i : Fin N) (hi : Kept p L i = true), i ≠ d →
          L (pc + 1) i = true → π ⟨i, hi⟩ ≠ π ⟨d, hd⟩) →
        CompactRel p L π ⟨pc + 1, upd σ d v⟩
          ⟨pc + 1, match π.get? d with
            | some k => upd σ' k v'
            | none => σ'⟩ := by
      intro d v v' hdef hsucc hv hcl
      refine ⟨rfl, ?_⟩
      by_cases hd : Kept p L d = true
      · simp only [π.get?_of_kept hd]
        refine rel_after_write hins hT hst hsucc d hdef v _ (fun hd' _ => ?_) (fun i hi hid hl => ?_)
        · simp [hv]
        · exact upd_other _ _ (hcl hd i hi hid hl)
      · simp only [π.get?_of_not_kept hd]
        refine rel_after_write hins hT hst hsucc d hdef v _ (fun hd' _ => absurd hd' hd)
          (fun i hi hid hl => rfl)
    cases ins with
    | assign d e =>
      have h := hwrite d (e.eval σ) ((compactExpr π e).eval σ')
        (fun i => by simp [Instr.defs, eq_comm]) (by simp [Instr.succs])
        (hlive (fun i hi => by simpa [Instr.uses] using hi))
        (fun hd i hi hid hl => hA pc d e hins hd i hi hid hl)
      by_cases hd : Kept p L d = true
      · simp only [π.get?_of_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_kept hd, ResRelS] using h
      · simp only [π.get?_of_not_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_not_kept hd, ResRelS] using h
    | storageLive j =>
      have h := hwrite j 0 0 (fun i => by simp [Instr.defs, eq_comm]) (by simp [Instr.succs]) rfl
        (fun hd i hi hid hl => hM pc j (Or.inl hins) hd i hi hid hl)
      by_cases hd : Kept p L j = true
      · simp only [π.get?_of_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_kept hd, ResRelS] using h
      · simp only [π.get?_of_not_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_not_kept hd, ResRelS] using h
    | storageDead j =>
      have h := hwrite j 0 0 (fun i => by simp [Instr.defs, eq_comm]) (by simp [Instr.succs]) rfl
        (fun hd i hi hid hl => hM pc j (Or.inr hins) hd i hi hid hl)
      by_cases hd : Kept p L j = true
      · simp only [π.get?_of_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_kept hd, ResRelS] using h
      · simp only [π.get?_of_not_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_not_kept hd, ResRelS] using h
    | dbg e =>
      simp only [stepInstr, compactInstr, ResRelS]
      exact ⟨rfl, hkeep (pc + 1) (by simp [Instr.succs]) (fun i => by simp [Instr.defs])⟩
    | nop =>
      simp only [stepInstr, compactInstr, ResRelS]
      exact ⟨rfl, hkeep (pc + 1) (by simp [Instr.succs]) (fun i => by simp [Instr.defs])⟩
    | branch c t f =>
      simp only [stepInstr, compactInstr, ResRelS]
      rw [hlive (fun i hi => by simpa [Instr.uses] using hi)]
      refine ⟨rfl, hkeep _ ?_ (fun i => by simp [Instr.defs])⟩
      split <;> simp [Instr.succs]
    | halt outs =>
      simp only [stepInstr, compactInstr, ResRelS]
      refine ⟨(map_filterMap_get? π outs fun i hi => ?_).symm, rfl, hst⟩
      have hl : L pc i = true := hR pc _ hins i (by simpa [Instr.uses] using hi)
      exact ⟨kept_of_getElem? hins hl, hst i _ hl⟩

/-- The event emitted by a step (only `dbg` emits one). -/
def Res.ev : Res N → Option Nat
  | .running _ e => e
  | _ => none

theorem lockstepBisim_of_silent {p : Prog N} {q : Prog M} {R : State N → State M → Prop}
    (h : SilentBisim p q R) (hev : ∀ s s', R s s' → (step p s).ev = (step q s').ev) :
    LockstepBisim p q R := by
  intro s s' hs
  have h1 := h s s' hs
  have h2 := hev s s' hs
  revert h1 h2
  cases step p s <;> cases step q s' <;> simp_all [ResRel, ResRelS, Res.ev]

/-- Under `DbgReadsLive`, related states emit equal events. -/
theorem compact_ev_eq_of_dbgReadsLive (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hD : DbgReadsLive p L) :
    ∀ s s', CompactRel p L π s s' → (step p s).ev = (step (compact p L π) s').ev := by
  rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨hpc, hst⟩
  simp only at hpc hst
  subst pc'
  cases hins : p[pc]? with
  | none =>
    rw [step_of_getElem?_none (s := ⟨pc, σ⟩) hins,
      step_compact_of_getElem?_none π hins σ']
    rfl
  | some ins =>
    rw [step_of_getElem? (s := ⟨pc, σ⟩) hins,
      step_compact_of_getElem? π hins σ']
    cases ins with
    | dbg e =>
      simp only [stepInstr, compactInstr, Res.ev]
      rw [eval_compactExpr_of_live π hins hst (fun i hi => hD pc e hins i hi)]
    | assign d e =>
      simp only [compactInstr]
      cases π.get? d <;> rfl
    | storageLive j =>
      simp only [compactInstr]
      cases π.get? j <;> rfl
    | storageDead j =>
      simp only [compactInstr]
      cases π.get? j <;> rfl
    | nop => rfl
    | branch c t f => rfl
    | halt outs => rfl

/-- **Lockstep bisimulation under interference freedom (stack-slot sharing).**
If the mask is a liveness certificate (`ReadsLive`, `TransferClosed`), debug reads are of live
slots, and neither assignments nor storage markers clobber a different live slot sharing their
target, then `CompactRel` is a lockstep bisimulation between `p` and its compaction, for
arbitrary control flow (branches and loops). `π` need not be injective. -/
theorem compact_lockstepBisim_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hD : DbgReadsLive p L)
    (hA : NoAssignClobber p L π) (hM : NoMarkerClobber p L π) :
    LockstepBisim p (compact p L π) (CompactRel p L π) :=
  lockstepBisim_of_silent (compact_silentBisim_of_noClobber p L π hR hT hA hM)
    (compact_ev_eq_of_dbgReadsLive p L π hD)

/-- **Lockstep bisimulation for injective compaction**, with the live-slot relation `CompactRel`.
Corollary of `compact_lockstepBisim_of_noClobber`. -/
theorem compact_lockstepBisim_of_injective (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hInj : Function.Injective π) (hR : ReadsLive p L) (hT : TransferClosed p L)
    (hD : DbgReadsLive p L) :
    LockstepBisim p (compact p L π) (CompactRel p L π) :=
  compact_lockstepBisim_of_noClobber p L π hR hT hD
    (noAssignClobber_of_injective hInj) (noMarkerClobber_of_injective hInj)

/-- **Injective compaction with the kept-slot relation.** If `π` is injective and every read
(semantic or debug) is of a kept slot, then the relation tracking *every* kept slot is a lockstep
bisimulation. No per-point condition on the mask (in particular no transfer closure) is assumed. -/
theorem compact_keptRel_lockstepBisim_of_injective (p : Prog N) (L : Ann N)
    (π : Compaction p L M) (hInj : Function.Injective π) (hRK : ReadsKept p L)
    (hDK : DbgReadsKept p L) :
    LockstepBisim p (compact p L π) (KeptRel p L π) := by
  rintro ⟨pc, σ⟩ ⟨pc', σ'⟩ ⟨hpc, hst⟩
  simp only at hpc hst
  subst pc'
  have hev : ∀ {e : Expr N}, (∀ i, e.reads i = true → Kept p L i = true) →
      (compactExpr π e).eval σ' = e.eval σ := fun hk =>
    eval_compactExpr π _ (fun i hi => ⟨hk i hi, hst i _⟩)
  -- after a write of `v` to `d`
  have hw : ∀ (d : Fin N) (v : Nat),
      KeptRel p L π ⟨pc + 1, upd σ d v⟩
        ⟨pc + 1, match π.get? d with
          | some k => upd σ' k v
          | none => σ'⟩ := by
    intro d v
    refine ⟨rfl, fun i hi => ?_⟩
    by_cases hid : i = d
    · subst hid
      simp [π.get?_of_kept hi]
    · dsimp only
      rw [upd_other _ _ hid]
      by_cases hd : Kept p L d = true
      · simp only [π.get?_of_kept hd]
        rw [upd_other _ _ (fun heq => hid (congrArg Subtype.val (hInj heq)))]
        exact hst i hi
      · simp only [π.get?_of_not_kept hd]
        exact hst i hi
  cases hins : p[pc]? with
  | none =>
    rw [step_of_getElem?_none (s := ⟨pc, σ⟩) hins,
      step_compact_of_getElem?_none π hins σ']
    trivial
  | some ins =>
    rw [step_of_getElem? (s := ⟨pc, σ⟩) hins,
      step_compact_of_getElem? π hins σ']
    cases ins with
    | assign d e =>
      have h := hw d (e.eval σ)
      have he := hev (e := e) (fun i hi => hRK pc _ hins i (by simpa [Instr.uses] using hi))
      by_cases hd : Kept p L d = true
      · simp only [π.get?_of_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_kept hd, ResRel, he] using h
      · simp only [π.get?_of_not_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_not_kept hd, ResRel] using h
    | storageLive j =>
      have h := hw j 0
      by_cases hd : Kept p L j = true
      · simp only [π.get?_of_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_kept hd, ResRel] using h
      · simp only [π.get?_of_not_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_not_kept hd, ResRel] using h
    | storageDead j =>
      have h := hw j 0
      by_cases hd : Kept p L j = true
      · simp only [π.get?_of_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_kept hd, ResRel] using h
      · simp only [π.get?_of_not_kept hd] at h
        simpa [stepInstr, compactInstr, π.get?_of_not_kept hd, ResRel] using h
    | dbg e =>
      simp only [stepInstr, compactInstr, ResRel]
      exact ⟨by rw [hev (fun i hi => hDK pc e hins i hi)], rfl, hst⟩
    | nop =>
      simp only [stepInstr, compactInstr, ResRel]
      exact ⟨trivial, rfl, hst⟩
    | branch c t f =>
      simp only [stepInstr, compactInstr, ResRel]
      rw [hev (fun i hi => hRK pc _ hins i (by simpa [Instr.uses] using hi))]
      exact ⟨trivial, rfl, hst⟩
    | halt outs =>
      simp only [stepInstr, compactInstr, ResRel]
      refine ⟨(map_filterMap_get? π outs fun i hi => ?_).symm, rfl, hst⟩
      exact ⟨hRK pc _ hins i (by simpa [Instr.uses] using hi), hst i _⟩

/-! ## Entry adequacy -/

/-- Every compacted store is related to some original store (its pull-back), at every point. -/
theorem compactRel_pullStore {p : Prog N} {L : Ann N} (π : Compaction p L M) (σ' : Store M)
    (pc : Nat) : CompactRel p L π ⟨pc, pullStore π σ'⟩ ⟨pc, σ'⟩ :=
  ⟨rfl, fun _ h _ => (pullStore_kept π σ' h).symm⟩

/-- If `π` is injective on the slots live at `pc`, the push-forward of any original store is a
related compacted store. -/
theorem compactRel_pushStore {p : Prog N} {L : Ann N} {π : Compaction p L M} {pc : Nat}
    (hinj : InjOnLiveAt p L π pc) (σ : Store N) :
    CompactRel p L π ⟨pc, σ⟩ ⟨pc, pushStore π pc σ⟩ :=
  ⟨rfl, fun _ h hl => pushStore_live hinj σ h hl⟩

/-- **Adequacy characterization at a point** (used at the entry point `pc = 0`). Every original
store at `pc` has a related compacted store iff `π` is injective on the kept slots live at `pc`. -/
theorem forall_exists_compactRel_iff_injOnLiveAt {p : Prog N} {L : Ann N}
    (π : Compaction p L M) (pc : Nat) :
    (∀ σ : Store N, ∃ σ' : Store M, CompactRel p L π ⟨pc, σ⟩ ⟨pc, σ'⟩) ↔ InjOnLiveAt p L π pc := by
  constructor
  · intro h i j hi hj hli hlj heq
    apply Classical.byContradiction
    intro hne
    obtain ⟨σ', _, hσ'⟩ := h (fun k => if k = i then 0 else 1)
    have e1 := hσ' i hi hli
    have e2 := hσ' j hj hlj
    rw [heq] at e1
    simp only at e1 e2
    rw [e1] at e2
    simp [Ne.symm hne] at e2
  · intro hinj σ
    exact ⟨_, compactRel_pushStore hinj σ⟩

end Toy.SlotCompact
