import ToyCFI.Abstract

/-!
# A decidable CFI checker and its soundness

`checkCFI f prog` infers one abstract entry state per block by forward
propagation with join over the CFG, then (i) re-checks that the inferred states
form a sound annotation (entry state and every CFG edge) and (ii) checks, at the
linear address of every PC of every annotated block, that the CFI program's row
is entailed by the abstract state at that PC.
-/

namespace Toy.CFI

/-- A block annotation: a candidate abstract entry state per block index. -/
abbrev Ann := Nat → Option AState

/-- Abstract state at offset `k` of a block entered in state `A`. -/
def absAt (f : Func) (A : AState) (b k : Nat) : AState := absRun A ((f.blockOps b).take k)

/-- Edge check for one block: every successor is annotated and the block's
abstract exit state is at least as precise as the successor's entry state. -/
def edgesOK (f : Func) (ann : Ann) (b : Nat) : Bool :=
  match ann b with
  | none => true
  | some A =>
    (f.succs b).all (fun b' =>
      match ann b' with
      | some B => leqA (absRun A (f.blockOps b)) B
      | none => false)

/-- `annSoundB f ann`: the annotation is sound — block `0` is annotated with a
state implied by `absInit`, and `edgesOK` holds for every block index. -/
def annSoundB (f : Func) (ann : Ann) : Bool :=
  (match ann 0 with
   | some A => leqA absInit A
   | none => false) &&
  (List.range f.blocks.length).all (edgesOK f ann)

/-- Row check for one block: at the linear address of each PC of an annotated
block, the program has a row and the row is entailed by the abstract state. -/
def rowsOK (f : Func) (prog : List CFIInst) (ann : Ann) (b : Nat) : Bool :=
  match ann b with
  | none => true
  | some A =>
    (List.range (f.blockOps b).length).all (fun k =>
      match f.pcOf b k with
      | none => false
      | some pc =>
        match rowAt? prog pc with
        | none => false
        | some R => entails (absAt f A b k) R)

/-- Check a CFI program against a given annotation. -/
def checkWith (f : Func) (prog : List CFIInst) (ann : Ann) : Bool :=
  annSoundB f ann && (List.range f.blocks.length).all (rowsOK f prog ann)

/-! ## Inference of block entry states -/

/-- Join of symbolic values. -/
def joinSym (a b : SymVal) : SymVal := if a = b then a else .unknown

/-- Join of abstract states (keeps the facts common to both). -/
def joinA (A B : AState) : AState :=
  { regs := ⟨joinSym A.regs.sp B.regs.sp, joinSym A.regs.fp B.regs.fp,
      joinSym A.regs.s1 B.regs.s1, joinSym A.regs.t1 B.regs.t1⟩,
    slots := A.slots.filter (fun e => slotAt B.slots e.1 == e.2) }

/-- One propagation pass over all blocks in index order. -/
def propagate (f : Func) (ann : List (Option AState)) : List (Option AState) :=
  (List.range f.blocks.length).foldl (fun acc b =>
    match acc[b]?.join with
    | none => acc
    | some A =>
      let out := absRun A (f.blockOps b)
      (f.succs b).foldl (fun acc' b' =>
        acc'.set b' (some (match acc'[b']?.join with
          | none => out
          | some B => joinA B out))) acc) ann

/-- Iterate `propagate` until it is stable or fuel runs out. -/
def inferLoop (f : Func) : Nat → List (Option AState) → Option (List (Option AState))
  | 0, _ => none
  | n + 1, ann =>
    let ann' := propagate f ann
    if ann' = ann then some ann else inferLoop f n ann'

/-- Inferred block entry states (`none` if propagation did not stabilize within
the fuel bound). -/
def inferEntries (f : Func) : Option (List (Option AState)) :=
  inferLoop f (8 * (f.blocks.length + 1) * (f.blocks.length + 1) + 8)
    ((List.replicate f.blocks.length none).set 0 (some absInit))

/-- The decidable checker. -/
def checkCFI (f : Func) (prog : List CFIInst) : Bool :=
  match inferEntries f with
  | none => false
  | some ann => checkWith f prog (fun b => ann[b]?.join)

/-! ## Soundness -/

theorem blockOps_ne_nil_lt {f : Func} {b : Nat} (h : 0 < (f.blockOps b).length) :
    b < f.blocks.length := by
  unfold Func.blockOps at h
  cases hb : f.blocks[b]? with
  | none => simp [hb] at h
  | some _ => exact (List.getElem?_eq_some_iff.mp hb).1

theorem absRun_take_succ (A : AState) (ops : List Op) {k : Nat} {op : Op}
    (h : ops[k]? = some op) : absRun A (ops.take (k + 1)) = xfer (absRun A (ops.take k)) op := by
  unfold absRun
  rw [List.take_succ, h]
  simp [List.foldl_append]

/-- Under a sound annotation, every reachable state satisfies the abstract state
of its PC.  (The CFI program plays no role here.) -/
theorem reach_inv_of_annSound {f : Func} {ann : Ann} (hs : annSoundB f ann = true)
    {c : Caller} {m : Int → Int} {b k : Nat} {st : MState} (h : Reach f c m b k st) :
    ∃ A, ann b = some A ∧ Inv (absAt f A b k) c st := by
  simp only [annSoundB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨h0, hedges⟩ := hs
  induction h with
  | entry _ =>
    cases h0' : ann 0 with
    | none => simp [h0'] at h0
    | some A =>
      rw [h0'] at h0
      refine ⟨A, rfl, ?_⟩
      simp only [absAt, List.take_zero]
      exact leqA_sound h0 (absInit_sound c m)
  | @next b k st op _ hop _ ih =>
    obtain ⟨A, hA, hinv⟩ := ih
    refine ⟨A, hA, ?_⟩
    simp only [absAt] at hinv ⊢
    rw [absRun_take_succ A _ hop]
    exact xfer_sound op hinv
  | @edge b k b' st op hr hop hlast hsucc _ ih =>
    obtain ⟨A, hA, hinv⟩ := ih
    have hblt : b < f.blocks.length := blockOps_ne_nil_lt (by have := hr.lt_length; omega)
    have he := hedges b hblt
    simp only [edgesOK, hA, List.all_eq_true] at he
    have he' := he b' hsucc
    cases hB : ann b' with
    | none => simp [hB] at he'
    | some B =>
      rw [hB] at he'
      refine ⟨B, rfl, ?_⟩
      have hfull : absRun A (f.blockOps b) = xfer (absAt f A b k) op := by
        simp only [absAt]
        rw [← absRun_take_succ A _ hop, hlast, List.take_length]
      have := xfer_sound op hinv
      rw [← hfull] at this
      simp only [absAt, List.take_zero]
      exact leqA_sound he' this

/-- Soundness of the checker relative to any annotation. -/
theorem checkWith_sound {f : Func} {prog : List CFIInst} {ann : Ann}
    (h : checkWith f prog ann = true) : TableCorrect f prog := by
  simp only [checkWith, Bool.and_eq_true] at h
  obtain ⟨hs, hrows⟩ := h
  intro c m b k st hr
  obtain ⟨A, hA, hinv⟩ := reach_inv_of_annSound hs hr
  have hk := hr.lt_length
  have hblt : b < f.blocks.length := blockOps_ne_nil_lt (by omega)
  simp only [List.all_eq_true, List.mem_range] at hrows
  have hb := hrows b hblt
  simp only [rowsOK, hA, List.all_eq_true, List.mem_range] at hb
  have hbk := hb k hk
  cases hpc : f.pcOf b k with
  | none => simp [hpc] at hbk
  | some pc =>
    cases hR : rowAt? prog pc with
    | none => simp [hpc, hR] at hbk
    | some R =>
      simp only [hpc, hR] at hbk
      exact ⟨pc, R, rfl, hR, entails_sound hbk hinv⟩

/-- **Checker soundness.** If `checkCFI f prog = true` then the CFI program is
correct at every reachable PC of every CFG path, for every caller and memory. -/
theorem checkCFI_sound {f : Func} {prog : List CFIInst} (h : checkCFI f prog = true) :
    TableCorrect f prog := by
  unfold checkCFI at h
  cases hinf : inferEntries f with
  | none => simp [hinf] at h
  | some ann =>
    rw [hinf] at h
    exact checkWith_sound h

end Toy.CFI
