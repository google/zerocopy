import ToyCFI.Checker

/-!
# A CFI generator for linearly laid-out CFGs

Given a block annotation, `genCFI` emits, in layout order, the row derived from
the abstract state at each PC.  Within a block it emits row deltas after each
operation.  At a block boundary where the row inherited from the layout
predecessor differs from the block's entry row it either

* restores a row remembered at the start of the layout predecessor
  (`rememberState` there, `restoreState` here), when the predecessor's entry row
  equals this block's entry row; or
* re-defines the entry row explicitly (`defCfa*`, `offset`, `restore`).

`naiveCFI` emits only the deltas inside each block (as an emitter that attaches
CFI directives to frame-affecting instructions would), never compensating at
block boundaries.
-/

namespace Toy.CFI

/-- Preferred CFA base: the first of `fp, sp, s1, t1` whose symbolic value is
CFA-relative. -/
def cfaChoice (A : AState) : Option (Reg × Int) :=
  [Reg.fp, .sp, .s1, .t1].findSome? (fun r =>
    match A.regs.get r with
    | .cfaRel d => some (r, -d)
    | _ => none)

/-- Rule chosen for register `r`: `same` if `r` still holds the caller's value,
else the offset of the first slot entry whose offset is not shadowed (its
`slotAt` value) and holds the caller's value, else `same` (unrecoverable). -/
def ruleChoice (A : AState) (r : Reg) : RegRule :=
  if A.regs.get r = .callerOf r then .same
  else
    match A.slots.find? (fun e => slotAt A.slots e.1 == .callerOf r) with
    | some e => .offset e.1
    | none => .same

/-- Row derived from an abstract state. -/
def rowOf (A : AState) : Row :=
  let cr := (cfaChoice A).getD (.sp, 0)
  { cfaReg := cr.1, cfaOff := cr.2,
    rules := ⟨ruleChoice A .sp, ruleChoice A .fp, ruleChoice A .s1, ruleChoice A .t1⟩ }

/-- Instructions changing the CFA rule of `R` into that of `R'`. -/
def cfaDelta (R R' : Row) : List CFIInst :=
  if R.cfaReg = R'.cfaReg then
    (if R.cfaOff = R'.cfaOff then [] else [.defCfaOffset R'.cfaOff])
  else if R.cfaOff = R'.cfaOff then [.defCfaRegister R'.cfaReg]
  else [.defCfa R'.cfaReg R'.cfaOff]

/-- Instructions changing the register rules of `R` into those of `R'`. -/
def ruleDelta (R R' : Row) : List CFIInst :=
  Reg.all.filterMap (fun r =>
    if R.rules.get r = R'.rules.get r then none
    else some (match R'.rules.get r with
      | .same => .restore r
      | .offset k => .offset r k))

/-- Instructions turning row `R` into row `R'`. -/
def delta (R R' : Row) : List CFIInst := cfaDelta R R' ++ ruleDelta R R'

/-- Desired rows of block `b` under annotation `ann` (one per PC). -/
def blockRows (f : Func) (ann : Ann) (b : Nat) : Option (List Row) :=
  (ann b).map (fun A => (List.range (f.blockOps b).length).map (fun k => rowOf (absAt f A b k)))

/-- Emit rows for consecutive PCs: before each PC the delta from the previous
row, then `advanceLoc 1`. -/
def emitRows : Row → List Row → List CFIInst
  | _, [] => []
  | cur, R :: Rs => delta cur R ++ [.advanceLoc 1] ++ emitRows R Rs

/-- Entry row of block `b`, if annotated and non-empty. -/
def entryRow (f : Func) (ann : Ann) (b : Nat) : Option Row :=
  (blockRows f ann b).bind List.head?

/-- Emit blocks in layout order. `cur` is the row inherited at the current
location; `pend` records that the previous block remembered a row for us. -/
def genBlocks (f : Func) (ann : Ann) : Row → Bool → List Nat → List CFIInst
  | _, _, [] => []
  | cur, pend, b :: rest =>
    match blockRows f ann b with
    | none => [.advanceLoc (f.blockOps b).length] ++ genBlocks f ann cur false rest
    | some [] => genBlocks f ann cur false rest
    | some (E :: Rs) =>
      let X := ((E :: Rs).getLast?).getD E
      let pre := if pend then [CFIInst.restoreState] else delta cur E
      let rem := decide (rest.head?.bind (entryRow f ann) = some E ∧ X ≠ E)
      pre ++ (if rem then [CFIInst.rememberState] else []) ++ emitRows E (E :: Rs) ++
        genBlocks f ann X rem rest

/-- The generator (with `rememberState`/`restoreState` or explicit re-definition
at block boundaries). -/
def genCFI (f : Func) (ann : Ann) : List CFIInst := genBlocks f ann initRow false f.layout

/-- Naive emitter: per-block deltas only, starting each block from its own entry
row without emitting anything at the boundary. -/
def naiveCFI (f : Func) (ann : Ann) : List CFIInst :=
  f.layout.flatMap (fun b =>
    match blockRows f ann b with
    | none => [.advanceLoc (f.blockOps b).length]
    | some [] => []
    | some (E :: Rs) => emitRows E (E :: Rs))

/-- `stateRecoverableB A`: some register holds a CFA-relative value, and every
callee-saved register either still holds the caller's value or is the
(unshadowed) content of some CFA-relative slot.  This mentions no emitter:
`stateRecoverableB_iff_exists_entails` shows it holds exactly when some row is
entailed by `A`. -/
def stateRecoverableB (A : AState) : Bool :=
  (cfaChoice A).isSome &&
    calleeSaved.all (fun r =>
      (A.regs.get r == .callerOf r) || A.slots.any (fun e => slotAt A.slots e.1 == .callerOf r))

/-- `annRecoverableB f ann`: at every PC of every annotated block the abstract
state is recoverable (`stateRecoverableB`), i.e. some row is entailed by it
(`annRecoverableB_iff`). -/
def annRecoverableB (f : Func) (ann : Ann) : Bool :=
  (List.range f.blocks.length).all (fun b =>
    match ann b with
    | none => true
    | some A => (List.range (f.blockOps b).length).all (fun k =>
        stateRecoverableB (absAt f A b k)))

/-- Every non-empty block appears in the layout. -/
def LayoutCovers (f : Func) : Prop := ∀ b, 0 < (f.blockOps b).length → b ∈ f.layout

/-- Inferred annotation (empty if inference fails). -/
def inferredAnn (f : Func) : Ann := fun b => ((inferEntries f).getD [])[b]?.join

/-! ## Recoverability is emitter-independent, and `rowOf` is complete for it -/

theorem cfaChoice_spec (A : AState) :
    (∀ cr, cfaChoice A = some cr → A.regs.get cr.1 = .cfaRel (-cr.2)) ∧
    ((∃ r d, A.regs.get r = .cfaRel d) → (cfaChoice A).isSome = true) := by
  constructor
  · intro cr h
    unfold cfaChoice at h
    cases hfp : A.regs.fp with
    | cfaRel d =>
      simp [RegFile.get, hfp] at h; rcases h with ⟨rfl, rfl⟩; simp [RegFile.get, hfp]
    | _ =>
      cases hsp : A.regs.sp with
      | cfaRel d =>
        simp [RegFile.get, hfp, hsp] at h; rcases h with ⟨rfl, rfl⟩; simp [RegFile.get, hsp]
      | _ =>
        cases hs1 : A.regs.s1 with
        | cfaRel d =>
          simp [RegFile.get, hfp, hsp, hs1] at h; rcases h with ⟨rfl, rfl⟩
          simp [RegFile.get, hs1]
        | _ =>
          cases ht1 : A.regs.t1 with
          | cfaRel d =>
            simp [RegFile.get, hfp, hsp, hs1, ht1] at h; rcases h with ⟨rfl, rfl⟩
            simp [RegFile.get, ht1]
          | _ => simp [RegFile.get, hfp, hsp, hs1, ht1] at h
  · rintro ⟨r, d, hr⟩
    unfold cfaChoice
    cases hfp : A.regs.fp with
    | cfaRel _ => simp [RegFile.get, hfp]
    | _ =>
      cases hsp : A.regs.sp with
      | cfaRel _ => simp [RegFile.get, hfp, hsp]
      | _ =>
        cases hs1 : A.regs.s1 with
        | cfaRel _ => simp [RegFile.get, hfp, hsp, hs1]
        | _ =>
          cases ht1 : A.regs.t1 with
          | cfaRel _ => simp [RegFile.get, hfp, hsp, hs1, ht1]
          | _ => cases r <;> simp [RegFile.get, hfp, hsp, hs1, ht1] at hr

theorem ruleOK_rowOf {A : AState} {r : Reg}
    (h : ((A.regs.get r == .callerOf r) ||
      A.slots.any (fun e => slotAt A.slots e.1 == .callerOf r)) = true) :
    ruleOK A (rowOf A) r = true := by
  have hget : (rowOf A).rules.get r = ruleChoice A r := by cases r <;> rfl
  unfold ruleOK
  rw [hget]
  unfold ruleChoice
  by_cases hreg : A.regs.get r = .callerOf r
  · simp [hreg]
  · simp only [hreg, ite_false]
    have hregB : (A.regs.get r == .callerOf r) = false := beq_eq_false_iff_ne.mpr hreg
    rw [hregB, Bool.false_or] at h
    obtain ⟨e, heMem, he⟩ := List.any_eq_true.mp h
    cases hfind : A.slots.find? (fun (e : Int × SymVal) => slotAt A.slots e.1 == .callerOf r) with
    | none =>
      have := List.find?_eq_none.mp hfind e heMem
      simp [he] at this
    | some e' =>
      exact List.find?_some (p := fun (e : Int × SymVal) => slotAt A.slots e.1 == .callerOf r) hfind

/-- `rowOf` is complete for recoverability: a recoverable state entails its
derived row. -/
theorem entails_rowOf_of_stateRecoverableB {A : AState} (hs : stateRecoverableB A = true) :
    entails A (rowOf A) = true := by
  simp only [stateRecoverableB, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨hcfa, hcs⟩ := hs
  simp only [entails, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨?_, fun r hr => ruleOK_rowOf (hcs r hr)⟩
  cases hch : cfaChoice A with
  | none => simp [hch] at hcfa
  | some cr =>
    have hspec := (cfaChoice_spec A).1 cr hch
    simpa [rowOf, hch] using hspec

/-- **Recoverability is emitter-independent.** `stateRecoverableB A` holds iff
some row is entailed by `A`. -/
theorem stateRecoverableB_iff_exists_entails (A : AState) :
    stateRecoverableB A = true ↔ ∃ R, entails A R = true := by
  refine ⟨fun hs => ⟨rowOf A, entails_rowOf_of_stateRecoverableB hs⟩, ?_⟩
  rintro ⟨R, hent⟩
  simp only [entails, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hent
  obtain ⟨hcfa, hrules⟩ := hent
  simp only [stateRecoverableB, Bool.and_eq_true, List.all_eq_true]
  refine ⟨(cfaChoice_spec A).2 ⟨R.cfaReg, -R.cfaOff, hcfa⟩, fun r hr => ?_⟩
  have hok := hrules r hr
  unfold ruleOK at hok
  cases hR : R.rules.get r with
  | same =>
    rw [hR] at hok; simp [hok]
  | offset k =>
    rw [hR, beq_iff_eq] at hok
    rcases slotAt_mem_or_unknown A.slots k with hu | hm
    · rw [hok] at hu; cases hu
    · rw [hok] at hm
      apply Bool.or_eq_true_iff.mpr; right
      exact List.any_eq_true.mpr ⟨(k, .callerOf r), hm, by simp [hok]⟩

/-- Unfolded meaning of `annRecoverableB`: at every PC of every annotated
in-range block, some row is entailed by the abstract state there. -/
theorem annRecoverableB_iff (f : Func) (ann : Ann) :
    annRecoverableB f ann = true ↔
      ∀ b < f.blocks.length, ∀ A, ann b = some A → ∀ k < (f.blockOps b).length,
        ∃ R, entails (absAt f A b k) R = true := by
  simp only [annRecoverableB, List.all_eq_true, List.mem_range]
  constructor
  · intro h b hb A hA k hk
    have hb' := h b hb
    rw [hA] at hb'
    simp only [List.all_eq_true, List.mem_range] at hb'
    exact (stateRecoverableB_iff_exists_entails _).1 (hb' k hk)
  · intro h b hb
    cases hA : ann b with
    | none => rfl
    | some A =>
      simp only [List.all_eq_true, List.mem_range]
      exact fun k hk => (stateRecoverableB_iff_exists_entails _).2 (h b hb A hA k hk)

end Toy.CFI
