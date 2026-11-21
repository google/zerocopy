import ToyProv.Lemmas

/-!
# R5 — Abstract bytes and provenance

Memory stores abstract bytes `uninit | intFrag n i | ptrFrag p i`; a stored pointer leaves two
`ptrFrag` bytes that each carry the whole pointer, provenance included.

* Loading pointer bytes at integer type yields the address; the integer carries no provenance in
  any model, and the load records the bytes' provenance as exposed. In `strict` that exposure is
  inert (the provenance is simply lost); in `exposed` a later `int2ptr` can pick it up (R5a).
* `memcpy` copies abstract bytes verbatim, so a pointer copied byte-wise keeps its provenance (R5b).
* A value-level integer round trip (load at integer type, store the integer, load at pointer type)
  does not carry provenance in any model: in `strict` the result has none; in `exposed` a
  provenance is re-derived from the exposed set, which may coincide with the original, be absent,
  or be a different allocation (R5c).
-/

namespace Toy.Prov

/-! ### Byte-level codec facts -/

theorem encodeVal_ptr (p : Ptr) : encodeVal (.ptr p) = [.ptrFrag p 0, .ptrFrag p 1] := rfl
theorem encodeVal_int (n : Nat) : encodeVal (.int n) = [.intFrag n 0, .intFrag n 1] := rfl

/-- Integer-typed decoding of a pointer's two bytes: the pointer's address, plus its provenance
as the list of provenances to expose. -/
theorem decodeInt_ptrFrags (p : Ptr) :
    decodeInt (.ptrFrag p 0) (.ptrFrag p 1) = some (p.addr, p.prov.toList) := by
  simp [decodeInt]

/-- Pointer-typed decoding of a pointer's two bytes gives back the same pointer, provenance
included. -/
theorem decodePtr_ptrFrags (p : Ptr) : decodePtr (.ptrFrag p 0) (.ptrFrag p 1) = some (.inl p) := by
  simp [decodePtr]

/-- Pointer-typed decoding of an integer's two bytes gives a bare address, which the load converts
as `int2ptr` would (`castToPtr`). -/
theorem decodePtr_intFrags (n : Nat) : decodePtr (.intFrag n 0) (.intFrag n 1) = some (.inr n) := by
  simp [decodePtr]

/-! ### Memory-level facts -/

theorem writeBytes_lt (mem : Nat → AByte) (a : Nat) (bs : List AByte) (y : Nat) (hy : y < a) :
    writeBytes mem a bs y = mem y := by
  induction bs generalizing mem a with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeBytes]
    rw [ih _ _ (by omega)]
    have : y ≠ a := by omega
    simp [this]

theorem writeBytes_get (mem : Nat → AByte) (a : Nat) (bs : List AByte) (i : Nat)
    (hi : i < bs.length) : writeBytes mem a bs (a + i) = bs[i] := by
  induction bs generalizing mem a i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      simp only [writeBytes]
      rw [writeBytes_lt _ _ _ _ (by omega)]
      simp
    | succ i =>
      simp only [writeBytes]
      rw [show a + (i + 1) = (a + 1) + i by omega, ih _ _ i (by simpa using hi)]
      simp

theorem readBytes_length (mem : Nat → AByte) (a n : Nat) : (readBytes mem a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [readBytes, ih]

theorem readBytes_get (mem : Nat → AByte) (a n i : Nat) (hi : i < n) :
    (readBytes mem a n)[i]'(by rw [readBytes_length]; exact hi) = mem (a + i) := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [readBytes]
    | succ i =>
      simp only [readBytes, List.getElem_cons_succ]
      rw [ih (a + 1) i (by omega)]
      congr 1; omega

/-- **R5b (memory level).** A defined `memcpy d r n` makes the `n` destination bytes equal to the
`n` source bytes of the pre-state, abstract byte for abstract byte (so pointer fragments, with
their provenance, are copied), in every model. -/
theorem memcpy_copies_abstract_bytes (m : Model) (s s' : St) (d r : Reg) (n : Nat) (x y : Ptr)
    (hd : s.regs d = some (.ptr x)) (hr : s.regs r = some (.ptr y))
    (hs : some s' ∈ step m s (.memcpy d r n)) :
    ∀ i < n, s'.mem (x.addr + i) = s.mem (y.addr + i) := by
  intro i hi
  simp only [step, hd, hr] at hs
  split at hs
  · simp only [List.mem_singleton, Option.some.injEq] at hs
    subst hs
    simp only
    rw [writeBytes_get _ _ _ i (by rw [readBytes_length]; exact hi), readBytes_get _ _ _ _ hi]
  · simp at hs

/-- **R5a (step level).** Loading, at integer type, two bytes that hold the fragments of pointer
`p` yields the integer `p.addr` and records `p`'s provenance as exposed; this is the same in every
model, and only `Model.exposed` later consults the exposure. -/
theorem load_int_of_ptrFrags (m : Model) (s : St) (d r : Reg) (x p : Ptr)
    (hr : s.regs r = some (.ptr x)) (hacc : canAccess m s x 2 = true)
    (h0 : s.mem x.addr = .ptrFrag p 0) (h1 : s.mem (x.addr + 1) = .ptrFrag p 1) :
    step m s (.load d .int r) = [some ((s.setReg d (.int p.addr)).expose p.prov.toList)] := by
  simp [step, hr, hacc, h0, h1, decodeInt]

/-- **R5c (step level).** Loading, at pointer type, two bytes that hold the fragments of an
integer `n` converts `n` exactly as `int2ptr` would (`castToPtr`): no provenance in `flat` and
`strict`; an exposed candidate (or none) in `exposed`. The integer bytes carry no provenance of
their own. -/
theorem load_ptr_of_intFrags (m : Model) (s : St) (d r : Reg) (x : Ptr) (n : Nat)
    (hr : s.regs r = some (.ptr x)) (hacc : canAccess m s x 2 = true)
    (h0 : s.mem x.addr = .intFrag n 0) (h1 : s.mem (x.addr + 1) = .intFrag n 1) :
    step m s (.load d .ptr r) = castToPtr m s d n := by
  simp [step, hr, hacc, h0, h1, decodePtr]

theorem writeBytes_ge (mem : Nat → AByte) (a : Nat) (bs : List AByte) (y : Nat)
    (hy : a + bs.length ≤ y) : writeBytes mem a bs y = mem y := by
  induction bs generalizing mem a with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeBytes]
    rw [ih _ _ (by simp at hy; omega)]
    have : y ≠ a := by simp at hy; omega
    simp [this]

/-- **R5b (frame).** A defined `memcpy d r n` leaves every byte outside the destination range
`[x.addr, x.addr + n)` unchanged. -/
theorem memcpy_frame (m : Model) (s s' : St) (d r : Reg) (n : Nat) (x y : Ptr)
    (hd : s.regs d = some (.ptr x)) (hr : s.regs r = some (.ptr y))
    (hs : some s' ∈ step m s (.memcpy d r n)) :
    ∀ z, z < x.addr ∨ x.addr + n ≤ z → s'.mem z = s.mem z := by
  intro z hz
  simp only [step, hd, hr] at hs
  split at hs
  · simp only [List.mem_singleton, Option.some.injEq] at hs
    subst hs
    rcases hz with hz | hz
    · exact writeBytes_lt _ _ _ _ hz
    · exact writeBytes_ge _ _ _ _ (by rw [readBytes_length]; exact hz)
  · simp at hs

/-! ### Witnesses for the step-level statements -/

/-- A, B, C (16, 18, 20); B holds the pointer A. -/
def r5State : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0] init with
  | some s :: _ => s
  | _ => init

/-- **R5a non-vacuity.** In `r5State`, register 1 holds B, B is accessible, and B's bytes are the
two fragments of A. -/
theorem load_int_of_ptrFrags_nonvacuous :
    r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed r5State ⟨some 1, 18⟩ 2 = true ∧
      r5State.mem 18 = .ptrFrag ⟨some 0, 16⟩ 0 ∧ r5State.mem (18 + 1) = .ptrFrag ⟨some 0, 16⟩ 1 := by
  decide

theorem step_ne_of_all_none {l l' : List (Option St)} (h : l.all Option.isNone = true)
    (h' : l'.all Option.isNone = false) : l ≠ l' := by
  intro e; rw [e] at h; rw [h] at h'; exact Bool.noConfusion h'

/-- **R5a, `hr` needed.** Register 9 is unset: the load is UB even though `x` (B) is accessible and
points at A's fragments. -/
theorem load_int_of_ptrFrags_hr_needed :
    canAccess .exposed r5State ⟨some 1, 18⟩ 2 = true ∧ r5State.mem 18 = .ptrFrag ⟨some 0, 16⟩ 0 ∧
      r5State.mem (18 + 1) = .ptrFrag ⟨some 0, 16⟩ 1 ∧
      step .exposed r5State (.load 3 .int 9) ≠
        [some ((r5State.setReg 3 (.int 16)).expose [0])] :=
  ⟨by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- `r5State` with B freed. -/
def r5StateFreed : St := { r5State with blocks := killBlock r5State.blocks 1 }

/-- **R5a, `hacc` needed.** B is freed: the load through B is UB although B's bytes are A's
fragments. -/
theorem load_int_of_ptrFrags_hacc_needed :
    r5StateFreed.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ r5StateFreed.mem 18 = .ptrFrag ⟨some 0, 16⟩ 0 ∧
      r5StateFreed.mem (18 + 1) = .ptrFrag ⟨some 0, 16⟩ 1 ∧
      step .exposed r5StateFreed (.load 3 .int 1) ≠
        [some ((r5StateFreed.setReg 3 (.int 16)).expose [0])] :=
  ⟨by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- C holds `[intFrag 5 0, ptrFrag A 1]` (an integer stored, then B's second byte copied over C's
second byte). -/
def r5StateTorn1 : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0, .const 3 5, .store 2 3,
      .offset 4 2 1, .offset 5 1 1, .memcpy 4 5 1] init with
  | some s :: _ => s
  | _ => init

/-- C holds `[ptrFrag A 0, intFrag 5 1]` (an integer stored, then B's first byte copied over C's
first byte). -/
def r5StateTorn0 : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0, .const 3 5, .store 2 3,
      .memcpy 2 1 1] init with
  | some s :: _ => s
  | _ => init

/-- **R5a, `h0` needed.** C's second byte is A's second fragment but its first byte is an integer
fragment: the integer-typed load is UB. -/
theorem load_int_of_ptrFrags_h0_needed :
    r5StateTorn1.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ canAccess .exposed r5StateTorn1 ⟨some 2, 20⟩ 2 = true ∧
      r5StateTorn1.mem (20 + 1) = .ptrFrag ⟨some 0, 16⟩ 1 ∧ r5StateTorn1.mem 20 ≠ .ptrFrag ⟨some 0, 16⟩ 0 ∧
      step .exposed r5StateTorn1 (.load 6 .int 2) ≠
        [some ((r5StateTorn1.setReg 6 (.int 16)).expose [0])] :=
  ⟨by decide, by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- **R5a, `h1` needed.** Symmetric: C's first byte is A's first fragment, its second byte an
integer fragment. -/
theorem load_int_of_ptrFrags_h1_needed :
    r5StateTorn0.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ canAccess .exposed r5StateTorn0 ⟨some 2, 20⟩ 2 = true ∧
      r5StateTorn0.mem 20 = .ptrFrag ⟨some 0, 16⟩ 0 ∧ r5StateTorn0.mem (20 + 1) ≠ .ptrFrag ⟨some 0, 16⟩ 1 ∧
      step .exposed r5StateTorn0 (.load 6 .int 2) ≠
        [some ((r5StateTorn0.setReg 6 (.int 16)).expose [0])] :=
  ⟨by decide, by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- The successor of `memcpy C B 2` in `r5State`. -/
def r5Succ : St := { r5State with mem := writeBytes r5State.mem 20 (readBytes r5State.mem 18 2) }

theorem r5Succ_mem (m : Model) : some r5Succ ∈ step m r5State (.memcpy 2 1 2) := by
  have hr2 : r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) := by decide
  have hr1 : r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) := by decide
  cases m with
  | flat =>
    have hacc : (canAccess .flat r5State ⟨some 2, 20⟩ 2 && canAccess .flat r5State ⟨some 1, 18⟩ 2) = true := by
      decide
    simp [step, hr2, hr1, hacc, r5Succ]
  | strict =>
    have hacc : (canAccess .strict r5State ⟨some 2, 20⟩ 2 && canAccess .strict r5State ⟨some 1, 18⟩ 2) = true := by
      decide
    simp [step, hr2, hr1, hacc, r5Succ]
  | exposed =>
    have hacc : (canAccess .exposed r5State ⟨some 2, 20⟩ 2 && canAccess .exposed r5State ⟨some 1, 18⟩ 2) = true := by
      decide
    simp [step, hr2, hr1, hacc, r5Succ]

/-- **R5b non-vacuity.** In every model, `memcpy C B 2` from `r5State` has the successor `r5Succ`
(registers 2 and 1 hold C and B). -/
theorem memcpy_copies_abstract_bytes_nonvacuous (m : Model) :
    r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧
      some r5Succ ∈ step m r5State (.memcpy 2 1 2) :=
  ⟨by decide, by decide, r5Succ_mem m⟩

/-- **R5b, `hs` needed.** Without `hs`, `s'` is arbitrary: taking `s' := s` (no copy performed),
C's first byte differs from B's. -/
theorem memcpy_copies_hs_needed :
    r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧
      ¬ (∀ i < 2, r5State.mem (20 + i) = r5State.mem (18 + i)) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 0 (by decide)
  revert this; decide

/-- **R5b, `hd` needed.** If `x` is not the pointer in `d` (here `x` is A while `d` holds C), the
copied bytes are not at `x`. -/
theorem memcpy_copies_hd_needed :
    r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ some r5Succ ∈ step .exposed r5State (.memcpy 2 1 2) ∧
      r5State.regs 2 ≠ some (.ptr ⟨some 0, 16⟩) ∧
      ¬ (∀ i < 2, r5Succ.mem (16 + i) = r5State.mem (18 + i)) := by
  refine ⟨by decide, r5Succ_mem .exposed, by decide, fun h => ?_⟩
  have := h 0 (by decide)
  revert this; decide

/-- **R5b, `hr` needed.** If `y` is not the pointer in `r` (here `y` is A while `r` holds B), the
destination bytes are not `y`'s bytes. -/
theorem memcpy_copies_hr_needed :
    r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ some r5Succ ∈ step .exposed r5State (.memcpy 2 1 2) ∧
      r5State.regs 1 ≠ some (.ptr ⟨some 0, 16⟩) ∧
      ¬ (∀ i < 2, r5Succ.mem (20 + i) = r5State.mem (16 + i)) := by
  refine ⟨by decide, r5Succ_mem .exposed, by decide, fun h => ?_⟩
  have := h 0 (by decide)
  revert this; decide

/-- B holds the integer 16. -/
def r5IntState : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 3 0, .store 1 3] init with
  | some s :: _ => s
  | _ => init

/-- **R5c (step level) non-vacuity.** In `r5IntState`, B is accessible and holds the fragments
of the integer 16; A is exposed, so the pointer-typed load re-derives A's provenance. -/
theorem load_ptr_of_intFrags_nonvacuous :
    r5IntState.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed r5IntState ⟨some 1, 18⟩ 2 = true ∧
      r5IntState.mem 18 = .intFrag 16 0 ∧ r5IntState.mem (18 + 1) = .intFrag 16 1 ∧
      (castToPtr .exposed r5IntState 3 16).length = 1 := by
  decide

/-- **R5c (step level), `hacc` needed.** With B freed, the pointer-typed load through B is UB. -/
theorem load_ptr_of_intFrags_hacc_needed :
    let s : St := { r5IntState with blocks := killBlock r5IntState.blocks 1 }
    s.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ s.mem 18 = .intFrag 16 0 ∧ s.mem (18 + 1) = .intFrag 16 1 ∧
      step .exposed s (.load 3 .ptr 1) ≠ castToPtr .exposed s 3 16 :=
  ⟨by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- **R5c (step level), `hr` needed.** Register 9 is unset. -/
theorem load_ptr_of_intFrags_hr_needed :
    canAccess .exposed r5IntState ⟨some 1, 18⟩ 2 = true ∧ r5IntState.mem 18 = .intFrag 16 0 ∧
      r5IntState.mem (18 + 1) = .intFrag 16 1 ∧
      step .exposed r5IntState (.load 3 .ptr 9) ≠ castToPtr .exposed r5IntState 3 16 :=
  ⟨by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- **R5c (step level), `h0`/`h1` needed.** A's pointer fragments are not integer fragments: the
pointer-typed load of B in `r5State` returns the stored pointer A itself, not `castToPtr`'s
result (B is not exposed there, so `castToPtr` would give no provenance). -/
theorem load_ptr_of_intFrags_h01_needed :
    r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed r5State ⟨some 1, 18⟩ 2 = true ∧
      r5State.mem 18 ≠ .intFrag 16 0 ∧ r5State.mem (18 + 1) ≠ .intFrag 16 1 ∧
      (step .exposed r5State (.load 3 .ptr 1)).map (Option.map (fun t => t.regs 3)) ≠
        (castToPtr .exposed r5State 3 16).map (Option.map (fun t => t.regs 3)) := by
  decide

/-- **R5c (step level), `h0` needed.** Only byte 0 of B differs (it is uninitialised); `hr`,
`hacc` and `h1` hold, and the pointer-typed load is UB rather than `castToPtr`'s result. -/
theorem load_ptr_of_intFrags_h0_needed :
    let s : St := { r5IntState with mem := fun a => if a = 18 then .uninit else r5IntState.mem a }
    s.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed s ⟨some 1, 18⟩ 2 = true ∧
      s.mem 18 ≠ .intFrag 16 0 ∧ s.mem (18 + 1) = .intFrag 16 1 ∧
      step .exposed s (.load 3 .ptr 1) ≠ castToPtr .exposed s 3 16 :=
  ⟨by decide, by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-- **R5c (step level), `h1` needed.** Only byte 1 of B differs (it is uninitialised); `hr`,
`hacc` and `h0` hold, and the pointer-typed load is UB rather than `castToPtr`'s result. -/
theorem load_ptr_of_intFrags_h1_needed :
    let s : St := { r5IntState with mem := fun a => if a = 19 then .uninit else r5IntState.mem a }
    s.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed s ⟨some 1, 18⟩ 2 = true ∧
      s.mem 18 = .intFrag 16 0 ∧ s.mem (18 + 1) ≠ .intFrag 16 1 ∧
      step .exposed s (.load 3 .ptr 1) ≠ castToPtr .exposed s 3 16 :=
  ⟨by decide, by decide, by decide, by decide, step_ne_of_all_none (by decide) (by decide)⟩

/-! ### Program-level examples -/

/-- Store the pointer A into B; load B's bytes at integer type; cast that integer back with
`int2ptr`; store 7 through it; read A. -/
def r5aProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .store 1 0, .load 2 .int 1, .int2ptr 3 2, .const 4 7, .store 3 4,
   .load 5 .int 0, .obs 5]
/-- As `r5aProg` but A's address is guessed as the constant 16 instead of loaded. -/
def r5aGuess : Prog :=
  [.alloc 0 2, .alloc 1 2, .store 1 0, .const 2 16, .int2ptr 3 2, .const 4 7, .store 3 4,
   .load 5 .int 0, .obs 5]
/-- As `r5aGuess` but with an integer-typed load of B's bytes (result unused) before the guess. -/
def r5aGuessAfterLoad : Prog :=
  [.alloc 0 2, .alloc 1 2, .store 1 0, .load 9 .int 1, .const 2 16, .int2ptr 3 2, .const 4 7,
   .store 3 4, .load 5 .int 0, .obs 5]

/-- **R5a.** Transmuting a pointer to an integer by loading its bytes at integer type: in
`strict` the provenance is lost (casting the integer back and storing through it is UB); in
`exposed` the load exposes A, so casting back succeeds, and the exposure is caused by the load
itself (without it the guessed address has no candidate; with an unused load it does). -/
theorem byteLoadAsInt_strict_strips_exposed_exposes :
    beh .strict r5aProg = [.ub] ∧ beh .exposed r5aProg = [.done [7]] ∧
      beh .exposed r5aGuess = [.ub] ∧ beh .exposed r5aGuessAfterLoad = [.done [7]] := by
  decide

/-- Store the pointer A into B; `memcpy` B's two bytes into C; load C at pointer type; store 7
through it; read A. -/
def r5bProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0, .memcpy 2 1 2, .load 3 .ptr 2, .const 4 7,
   .store 3 4, .load 5 .int 0, .obs 5]

/-- **R5b (program level).** A pointer copied byte-wise keeps its provenance: the program is
defined in `strict` and in `exposed`, with no cast anywhere. -/
theorem memcpy_preserves_provenance_example :
    beh .strict r5bProg = [.done [7]] ∧ beh .exposed r5bProg = [.done [7]] := by
  decide

/-- As `r5bProg` but the copy goes through an integer value: load B at integer type, store that
integer into C, load C at pointer type. -/
def r5cProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0, .load 6 .int 1, .store 2 6, .load 3 .ptr 2,
   .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]

/-- **R5c (in range).** A value-level integer round trip of the pointer A: in `strict` the
reloaded pointer has no provenance (UB); in `exposed` the pointer-typed load of integer bytes
re-derives a provenance from the exposed set, and A — exposed by the integer-typed load and the
only candidate — is picked, so the program is defined. -/
theorem intRoundTrip_in_range_example :
    beh .strict r5cProg = [.ub] ∧ beh .exposed r5cProg = [.done [7]] := by
  decide

/-- A pointer 10 bytes past A's start (outside every allocation's closed range) is stored into
B, copied to C (byte-wise with `memcpy`, or through an integer value), reloaded, moved back by
10, and stored through. -/
def r5cOutCopy : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .offset 9 0 10, .store 1 9, .memcpy 2 1 2, .load 3 .ptr 2,
   .offset 3 3 (-10), .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
def r5cOutInt : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .offset 9 0 10, .store 1 9, .load 6 .int 1, .store 2 6,
   .load 3 .ptr 2, .offset 3 3 (-10), .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]

/-- **R5c (out of range).** For a pointer outside its allocation's closed range, the byte-wise
copy keeps A's provenance (defined in both models) while the integer round trip loses it in both
models (no allocation contains the address, so nothing can be re-derived). -/
theorem intRoundTrip_out_of_range_example :
    beh .strict r5cOutCopy = [.done [7]] ∧ beh .exposed r5cOutCopy = [.done [7]] ∧
      beh .strict r5cOutInt = [.ub] ∧ beh .exposed r5cOutInt = [.ub] := by
  decide

/-- The one-past-the-end pointer of A (= B's start, B exposed) is stored into C, copied to D
(by `memcpy` or through an integer value), reloaded, and stored through; then B is read. -/
def r5cBndCopy : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .alloc 3 2, .ptr2int 8 1, .offset 9 0 2, .store 2 9,
   .memcpy 3 2 2, .load 4 .ptr 3, .const 5 7, .store 4 5, .load 6 .int 1, .obs 6]
def r5cBndInt : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .alloc 3 2, .ptr2int 8 1, .offset 9 0 2, .store 2 9,
   .load 7 .int 2, .store 3 7, .load 4 .ptr 3, .const 5 7, .store 4 5, .load 6 .int 1, .obs 6]

/-- **R5c (boundary).** At the one-past-the-end boundary the integer round trip can *change* the
provenance in `exposed`: the byte-wise copy keeps A's provenance (the store is UB), while the
round trip may pick the exposed B (the store is defined). In `strict` both are UB. -/
theorem intRoundTrip_boundary_example :
    beh .exposed r5cBndCopy = [.ub] ∧ beh .exposed r5cBndInt = [.done [7]] ∧
      beh .strict r5cBndCopy = [.ub] ∧ beh .strict r5cBndInt = [.ub] := by
  decide

end Toy.Prov
