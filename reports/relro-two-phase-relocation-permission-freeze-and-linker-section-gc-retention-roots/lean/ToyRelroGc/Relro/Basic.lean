import ToyRelroGc.Relro.Model

/-!
Auxiliary lemmas about the RELRO model's timeline semantics.
-/
namespace Toy.RelroGc

/-- The memory after attempting each relocation in order under a fixed writability map `w`:
relocations whose slot is not writable are skipped (they fault). -/
def tryApplyAll (sa : SymTab) (w : Nat → Bool) (rs : List Reloc) (m : Mem) : Mem :=
  rs.foldl (fun m r => if w r.slot then applyReloc sa m r else m) m

/-- The state after the loading phase of `twoPhase c ops`: relocations attempted under the
map-time permissions, then `protect`. -/
def postLoad (c : Cfg) (sa : SymTab) : St :=
  ⟨tryApplyAll sa (mapWr c.kinds) c.relocs c.init, fun a => mapWr c.kinds a && !c.prot a⟩

theorem stepOp_wr (c : Cfg) (sa : SymTab) (s : St) (o : Op) : (stepOp c sa s o).1.wr = s.wr := by
  cases o with
  | write a v =>
    simp only [stepOp]
    split <;> rfl
  | call x =>
    simp only [stepOp]
    split
    · split <;> rfl
    · rfl

theorem runT_ops_applyOuts (c : Cfg) (sa : SymTab) :
    ∀ (ops : List Op) (s : St), (runT c sa s (ops.map Ev.op)).applyOuts = []
  | [], _ => rfl
  | o :: ops, s => by
    simp only [List.map_cons, runT]
    exact runT_ops_applyOuts c sa ops _

theorem runT_ops_memAtProtect (c : Cfg) (sa : SymTab) :
    ∀ (ops : List Op) (s : St), (runT c sa s (ops.map Ev.op)).memAtProtect = none
  | [], _ => rfl
  | o :: ops, s => by
    simp only [List.map_cons, runT]
    exact runT_ops_memAtProtect c sa ops _

/-- The outcome of a program write depends only on the (unchanging) writability map. -/
theorem runT_ops_write (c : Cfg) (sa : SymTab) :
    ∀ (ops : List Op) (s : St) (j a v : Nat), ops[j]? = some (Op.write a v) →
      (runT c sa s (ops.map Ev.op)).opOuts[j]? = some (if s.wr a then Out.ok else Out.fault)
  | [], _, _, _, _, h => by simp at h
  | o :: ops, s, 0, a, v, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.map_cons, runT, List.getElem?_cons_zero, Option.some.injEq]
    simp only [stepOp]
    split <;> rfl
  | o :: ops, s, j + 1, a, v, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.map_cons, runT, List.getElem?_cons_succ]
    rw [runT_ops_write c sa ops _ j a v h, stepOp_wr]

/-- Running the relocation prefix: permissions do not change, outcomes are determined by the
current writability map, and memory becomes `tryApplyAll`. -/
theorem runT_applies (c : Cfg) (sa : SymTab) :
    ∀ (rs : List Reloc) (s : St) (t : List Ev),
      runT c sa s (rs.map Ev.apply ++ t) =
        { runT c sa ⟨tryApplyAll sa s.wr rs s.mem, s.wr⟩ t with
          applyOuts := rs.map (fun r => if s.wr r.slot then Out.ok else Out.fault) ++
            (runT c sa ⟨tryApplyAll sa s.wr rs s.mem, s.wr⟩ t).applyOuts }
  | [], s, t => by
    simp only [List.map_nil, List.nil_append]
    rfl
  | r :: rs, s, t => by
    simp only [List.map_cons, List.cons_append, runT]
    by_cases h : s.wr r.slot = true
    · have e : stepApply sa s r = (⟨applyReloc sa s.mem r, s.wr⟩, Out.ok) := by
        simp [stepApply, h]
      rw [e]
      simp only
      rw [runT_applies c sa rs ⟨applyReloc sa s.mem r, s.wr⟩ t]
      simp [tryApplyAll, List.foldl_cons, h]
    · have e : stepApply sa s r = (s, Out.fault) := by
        simp [stepApply, h]
      rw [e]
      simp only
      rw [runT_applies c sa rs s t]
      simp [tryApplyAll, List.foldl_cons, h]

theorem trace_twoPhase (c : Cfg) (sa : SymTab) (ops : List Op) :
    trace c sa (twoPhase c ops) =
      { applyOuts := c.relocs.map (fun r => if mapWr c.kinds r.slot then Out.ok else Out.fault)
        opOuts := (runT c sa (postLoad c sa) (ops.map Ev.op)).opOuts
        memAtProtect := some (tryApplyAll sa (mapWr c.kinds) c.relocs c.init) } := by
  simp only [trace, twoPhase]
  rw [runT_applies]
  simp only [Cfg.start, runT, stepProtect, runT_ops_applyOuts, List.append_nil, postLoad]
  rfl

theorem tryApplyAll_eq_applyAll (sa : SymTab) (w : Nat → Bool) :
    ∀ (rs : List Reloc) (m : Mem), (∀ r ∈ rs, w r.slot = true) →
      tryApplyAll sa w rs m = applyAll sa rs m
  | [], _, _ => rfl
  | r :: rs, m, h => by
    have hr : w r.slot = true := h r (List.mem_cons_self ..)
    simp only [tryApplyAll, applyAll, List.foldl_cons, hr, ↓reduceIte]
    exact tryApplyAll_eq_applyAll sa w rs _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))

theorem tryApplyAll_other (sa : SymTab) (w : Nat → Bool) (x : Nat) :
    ∀ (rs : List Reloc) (m : Mem), (∀ r ∈ rs, r.slot ≠ x) → tryApplyAll sa w rs m x = m x
  | [], _, _ => rfl
  | r :: rs, m, h => by
    simp only [tryApplyAll, List.foldl_cons]
    have hr : r.slot ≠ x := h r (List.mem_cons_self ..)
    rw [show List.foldl _ _ rs = tryApplyAll sa w rs _ from rfl,
      tryApplyAll_other sa w x rs _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]
    split
    · simp [applyReloc, upd, Ne.symm hr]
    · rfl

theorem tryApplyAll_bind (sa : SymTab) (w : Nat → Bool) (x : Nat) (t : Sym) (hw : w x = true) :
    ∀ (rs : List Reloc) (m : Mem), (∀ r ∈ rs, r.slot = x → r = bindReloc x t) →
      (m x = sa t ∨ bindReloc x t ∈ rs) → tryApplyAll sa w rs m x = sa t
  | [], m, _, h => by
    rcases h with h | h
    · exact h
    · simp at h
  | r :: rs, m, hall, h => by
    simp only [tryApplyAll, List.foldl_cons]
    rw [show List.foldl _ _ rs = tryApplyAll sa w rs _ from rfl]
    apply tryApplyAll_bind sa w x t hw rs _ (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr'))
    by_cases hs : r.slot = x
    · have hrb : r = bindReloc x t := hall r (List.mem_cons_self ..) hs
      subst hrb
      left
      simp [bindReloc, applyReloc, upd, hw]
    · rcases h with h | h
      · left
        split
        · simp [applyReloc, upd, Ne.symm hs, h]
        · exact h
      · rcases List.mem_cons.mp h with h' | h'
        · exact absurd (show r.slot = x by rw [← h']; rfl) hs
        · right; exact h'

/-- Loading succeeds under the two-phase schedule iff every relocated slot is mapped writable. -/
theorem loadOk_twoPhase_iff (c : Cfg) (sa : SymTab) (ops : List Op) :
    LoadOk (trace c sa (twoPhase c ops)) ↔ RelocSlotsWritable c := by
  rw [trace_twoPhase]
  simp only [LoadOk, List.mem_map, forall_exists_index, and_imp, RelocSlotsWritable]
  constructor
  · intro h r hr
    have := h _ r hr rfl
    revert this
    split <;> simp_all
  · intro h o r hr ho
    subst ho
    simp [h r hr]

/-- Post-entry write protection of `a` holds iff `a` is non-writable after `protect`. -/
theorem writeFaultsAfter_iff (c : Cfg) (sa : SymTab) (a : Nat) :
    WriteFaultsAfter c sa a ↔ (mapWr c.kinds a && !c.prot a) = false := by
  unfold WriteFaultsAfter
  have key : ∀ (ops : List Op) (v : Nat),
      (trace c sa (twoPhase c (ops ++ [Op.write a v]))).opOuts[ops.length]? =
        some (if (mapWr c.kinds a && !c.prot a) then Out.ok else Out.fault) := by
    intro ops v
    rw [trace_twoPhase]
    exact runT_ops_write c sa (ops ++ [Op.write a v]) (postLoad c sa) ops.length a v (by simp)
  simp only [key]
  constructor
  · intro h
    have := h [] 0
    revert this
    split <;> simp_all
  · intro h ops v
    simp [h]

end Toy.RelroGc
