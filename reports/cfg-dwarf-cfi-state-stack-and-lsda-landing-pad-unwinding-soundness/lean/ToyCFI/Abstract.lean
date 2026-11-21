import ToyCFI.Table

/-!
# Abstract frame states

The abstract interpretation behind the generator and the checker.  An abstract
frame state records, for every register and for finitely many CFA-relative stack
slots, a symbolic value: `cfaRel d` (the CFA plus `d`), `callerOf r` (the
caller's value of `r`), or `unknown`.
-/

namespace Toy.CFI

/-- Symbolic values of the abstract frame state. -/
inductive SymVal
  | cfaRel (d : Int)
  | callerOf (r : Reg)
  | unknown
  deriving DecidableEq, Repr

/-- Abstract frame state: symbolic registers and a list of CFA-relative slots
`(k, v)` meaning "memory at `CFA + k` holds `v`" (first entry for `k` wins). -/
structure AState where
  regs : RegFile SymVal
  slots : List (Int × SymVal)
  deriving DecidableEq, Repr

/-- Symbolic content of slot `k` (`unknown` if absent). -/
def slotAt : List (Int × SymVal) → Int → SymVal
  | [], _ => .unknown
  | (k', v) :: rest, k => if k' = k then v else slotAt rest k

/-- Add a constant to a symbolic value (only CFA-relative values stay known). -/
def symAdd : SymVal → Int → SymVal
  | .cfaRel d, n => .cfaRel (d + n)
  | _, _ => .unknown

/-- Store `v` at symbolic address `addr`: a CFA-relative address updates one slot;
any other address forgets all slots (the write may alias any of them). -/
def storeSlot (sl : List (Int × SymVal)) (addr v : SymVal) : List (Int × SymVal) :=
  match addr with
  | .cfaRel d => (d, v) :: sl.filter (fun e => e.1 != d)
  | _ => []

/-- Load from symbolic address `addr`. -/
def loadSlot (sl : List (Int × SymVal)) : SymVal → SymVal
  | .cfaRel d => slotAt sl d
  | _ => .unknown

/-- Abstract transfer function, mirroring `step`. -/
def xfer (A : AState) : Op → AState
  | .push r =>
    let sp' := symAdd (A.regs.get .sp) (-1)
    { regs := A.regs.set .sp sp', slots := storeSlot A.slots sp' (A.regs.get r) }
  | .pop r =>
    { regs := (A.regs.set .sp (symAdd (A.regs.get .sp) 1)).set r
        (loadSlot A.slots (A.regs.get .sp)),
      slots := A.slots }
  | .subSp n => { A with regs := A.regs.set .sp (symAdd (A.regs.get .sp) (-(n : Int))) }
  | .addSp n => { A with regs := A.regs.set .sp (symAdd (A.regs.get .sp) (n : Int)) }
  | .movReg d s => { A with regs := A.regs.set d (A.regs.get s) }
  | .saveAt r off =>
    { A with slots := storeSlot A.slots (symAdd (A.regs.get .sp) off) (A.regs.get r) }
  | .restore r off =>
    { A with regs := A.regs.set r (loadSlot A.slots (symAdd (A.regs.get .sp) off)) }
  | .call => A
  | .ret => A

/-- Run the abstract transfer over a list of operations. -/
def absRun (A : AState) (ops : List Op) : AState := ops.foldl xfer A

/-- Abstract state on function entry. -/
def absInit : AState :=
  { regs := ⟨.cfaRel 0, .callerOf .fp, .callerOf .s1, .callerOf .t1⟩, slots := [] }

/-- `symLe a b`: `b` is `unknown` or equal to `a` (so `a` is at least as precise). -/
def symLe (a b : SymVal) : Bool := b == .unknown || a == b

/-- `leqA A B`: every fact recorded in `B` is recorded in `A`.  Slots are
compared through `slotAt` on both sides, so a shadowed (later) entry of
`B.slots` for an already-listed offset is ignored, as it is by `Inv`; in
particular `leqA` is reflexive (`leqA_refl`). -/
def leqA (A B : AState) : Bool :=
  Reg.all.all (fun r => symLe (A.regs.get r) (B.regs.get r)) &&
    B.slots.all (fun e => symLe (slotAt A.slots e.1) (slotAt B.slots e.1))

/-- Concretization of a symbolic value relative to caller `c`. -/
def SymHolds (c : Caller) : SymVal → Int → Prop
  | .cfaRel d, x => x = c.cfa + d
  | .callerOf r, x => x = c.regs.get r
  | .unknown, _ => True

/-- `Inv A c st`: concrete state `st` (of a frame called by `c`) satisfies every
fact of the abstract state `A`. -/
def Inv (A : AState) (c : Caller) (st : MState) : Prop :=
  (∀ r, SymHolds c (A.regs.get r) (st.regs.get r)) ∧
    (∀ k, SymHolds c (slotAt A.slots k) (st.mem (c.cfa + k)))

/-- Does abstract state `A` justify rule `R.rules.get r` for register `r`? -/
def ruleOK (A : AState) (R : Row) (r : Reg) : Bool :=
  match R.rules.get r with
  | .same => A.regs.get r == .callerOf r
  | .offset k => slotAt A.slots k == .callerOf r

/-- `entails A R`: in every concrete state satisfying `A`, row `R` recovers the
CFA and the callee-saved registers. -/
def entails (A : AState) (R : Row) : Bool :=
  A.regs.get R.cfaReg == .cfaRel (-R.cfaOff) && calleeSaved.all (ruleOK A R)

/-! ## Soundness lemmas -/

theorem symAdd_holds {c : Caller} {s : SymVal} {x : Int} (n : Int) (h : SymHolds c s x) :
    SymHolds c (symAdd s n) (x + n) := by
  cases s with
  | cfaRel d => simp only [symAdd, SymHolds] at *; omega
  | callerOf r => trivial
  | unknown => trivial

theorem slotAt_filter_ne (sl : List (Int × SymVal)) {d k : Int} (h : k ≠ d) :
    slotAt (sl.filter (fun e => e.1 != d)) k = slotAt sl k := by
  induction sl with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k', v⟩ := e
    by_cases hk : k' = d
    · subst hk
      have : k' ≠ k := fun h' => h h'.symm
      simp [List.filter_cons, slotAt, this, ih]
    · have hb : (k' != d) = true := by simp [hk]
      by_cases hk2 : k' = k
      · subst hk2; simp [List.filter_cons, hb, slotAt]
      · simp [List.filter_cons, hb, slotAt, hk2, ih]

theorem storeSlot_holds {c : Caller} {sl : List (Int × SymVal)} {m : Int → Int}
    {addr v : SymVal} {a x : Int}
    (hsl : ∀ k, SymHolds c (slotAt sl k) (m (c.cfa + k)))
    (ha : SymHolds c addr a) (hv : SymHolds c v x) :
    ∀ k, SymHolds c (slotAt (storeSlot sl addr v) k) (write m a x (c.cfa + k)) := by
  intro k
  cases addr with
  | cfaRel d =>
    simp only [SymHolds] at ha
    subst ha
    simp only [storeSlot, slotAt, write]
    by_cases hk : d = k
    · subst hk; simp [hv]
    · have hne : c.cfa + k ≠ c.cfa + d := by omega
      have hk' : k ≠ d := fun h => hk h.symm
      simp only [hk, if_false, hne]
      rw [slotAt_filter_ne _ hk']
      exact hsl k
  | callerOf r => simp [storeSlot, slotAt, SymHolds]
  | unknown => simp [storeSlot, slotAt, SymHolds]

theorem loadSlot_holds {c : Caller} {sl : List (Int × SymVal)} {m : Int → Int}
    {addr : SymVal} {a : Int}
    (hsl : ∀ k, SymHolds c (slotAt sl k) (m (c.cfa + k))) (ha : SymHolds c addr a) :
    SymHolds c (loadSlot sl addr) (m a) := by
  cases addr with
  | cfaRel d =>
    simp only [SymHolds] at ha
    subst ha
    exact hsl d
  | callerOf r => trivial
  | unknown => trivial

theorem regs_set_holds {c : Caller} {A : RegFile SymVal} {R : RegFile Int}
    (h : ∀ r, SymHolds c (A.get r) (R.get r)) (r0 : Reg) {s : SymVal} {x : Int}
    (hx : SymHolds c s x) : ∀ r, SymHolds c ((A.set r0 s).get r) ((R.set r0 x).get r) := by
  intro r
  by_cases hr : r = r0
  · subst hr; simpa using hx
  · simpa [hr] using h r

/-- The abstract transfer function is sound for the concrete step. -/
theorem xfer_sound {A : AState} {c : Caller} {st : MState} (op : Op) (h : Inv A c st) :
    Inv (xfer A op) c (step st op) := by
  obtain ⟨hr, hs⟩ := h
  cases op with
  | push r =>
    have hsp : SymHolds c (symAdd (A.regs.get .sp) (-1)) (st.regs.get .sp - 1) := by
      have := symAdd_holds (-1) (hr .sp)
      simpa [Int.sub_eq_add_neg] using this
    refine ⟨regs_set_holds hr .sp hsp, ?_⟩
    exact storeSlot_holds hs hsp (hr r)
  | pop r =>
    refine ⟨?_, hs⟩
    exact regs_set_holds (regs_set_holds hr .sp (symAdd_holds 1 (hr .sp))) r
      (loadSlot_holds hs (hr .sp))
  | subSp n =>
    refine ⟨?_, hs⟩
    have := symAdd_holds (-(n : Int)) (hr .sp)
    exact regs_set_holds hr .sp (by simpa [Int.sub_eq_add_neg] using this)
  | addSp n =>
    exact ⟨regs_set_holds hr .sp (symAdd_holds (n : Int) (hr .sp)), hs⟩
  | movReg d s =>
    exact ⟨regs_set_holds hr d (hr s), hs⟩
  | saveAt r off =>
    exact ⟨hr, storeSlot_holds hs (symAdd_holds off (hr .sp)) (hr r)⟩
  | restore r off =>
    exact ⟨regs_set_holds hr r (loadSlot_holds hs (symAdd_holds off (hr .sp))), hs⟩
  | call => exact ⟨hr, hs⟩
  | ret => exact ⟨hr, hs⟩

theorem absRun_sound {c : Caller} : ∀ (ops : List Op) {A : AState} {st : MState},
    Inv A c st → Inv (absRun A ops) c (ops.foldl step st)
  | [], _, _, h => h
  | op :: ops, _, _, h => absRun_sound ops (xfer_sound op h)

theorem absInit_sound (c : Caller) (m : Int → Int) : Inv absInit c (entryState c m) := by
  refine ⟨?_, ?_⟩
  · intro r
    cases r <;> simp [absInit, entryState, RegFile.get, RegFile.set, SymHolds]
  · intro k; simp [absInit, slotAt, SymHolds]

theorem symLe_holds {c : Caller} {a b : SymVal} {x : Int} (hle : symLe a b = true)
    (h : SymHolds c a x) : SymHolds c b x := by
  simp only [symLe, Bool.or_eq_true, beq_iff_eq] at hle
  rcases hle with hb | hab
  · subst hb; trivial
  · subst hab; exact h

theorem slotAt_mem_or_unknown (sl : List (Int × SymVal)) (k : Int) :
    slotAt sl k = .unknown ∨ (k, slotAt sl k) ∈ sl := by
  induction sl with
  | nil => left; rfl
  | cons e rest ih =>
    obtain ⟨k', v⟩ := e
    by_cases hk : k' = k
    · subst hk; right; simp [slotAt]
    · simp only [slotAt, hk, if_false]
      rcases ih with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h

/-- `leqA` is sound: facts of the less precise state follow from the more precise one. -/
theorem leqA_sound {A B : AState} {c : Caller} {st : MState} (hle : leqA A B = true)
    (h : Inv A c st) : Inv B c st := by
  obtain ⟨hr, hs⟩ := h
  simp only [leqA, Bool.and_eq_true, List.all_eq_true] at hle
  obtain ⟨hregs, hslots⟩ := hle
  refine ⟨fun r => symLe_holds (hregs r (Reg.mem_all r)) (hr r), fun k => ?_⟩
  rcases slotAt_mem_or_unknown B.slots k with hu | hm
  · rw [hu]; trivial
  · exact symLe_holds (hslots (k, slotAt B.slots k) hm) (hs k)

/-- `leqA` is reflexive. -/
theorem leqA_refl (A : AState) : leqA A A = true := by
  simp only [leqA, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun r _ => by simp [symLe], fun e _ => by simp [symLe]⟩

/-- `entails` is sound: an entailed row recovers the caller. -/
theorem entails_sound {A : AState} {R : Row} {c : Caller} {st : MState}
    (he : entails A R = true) (h : Inv A c st) : Recovers R c st := by
  obtain ⟨hr, hs⟩ := h
  simp only [entails, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at he
  obtain ⟨hcfa, hrules⟩ := he
  have hc : cfaOf R st = c.cfa := by
    have := hr R.cfaReg
    rw [hcfa] at this
    simp only [SymHolds] at this
    simp only [cfaOf]; omega
  refine ⟨hc, fun r hmem => ?_⟩
  have hok := hrules r hmem
  unfold ruleOK at hok
  unfold ruleVal
  cases hR : R.rules.get r with
  | same =>
    rw [hR] at hok
    simp only [beq_iff_eq] at hok
    have := hr r
    rw [hok] at this
    exact this
  | offset k =>
    rw [hR] at hok
    simp only [beq_iff_eq] at hok
    have := hs k
    rw [hok] at this
    rw [hc]; exact this

end Toy.CFI
