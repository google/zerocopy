import ToyReprLower.Uses
import ToyReprLower.Reinterpret

/-!
# Toy unions: whole-value versus projection validity, framing of partial writes, union
registers

A toy union is a list of abstract bytes of the union's size. Whole-value validity of a union is
a parameter (`UnionValidity`): Rust has not decided it for unions without a zero-sized field.
`trivialUnionValidity` (every byte list of the union's size is valid, which Rust guarantees for
unions with a zero-sized field) is one choice. A typed projection (reading field `f`) requires
`f`'s bytes to be valid for `f`.
-/

namespace Toy.ReprLower

/-- A union field: offset, size, and a validity predicate on its bytes. -/
structure UField where
  off : Nat
  size : Nat
  valid : List AByte → Bool

/-- A toy union type: byte size and fields. -/
structure UnionTy where
  size : Nat
  fields : List UField

/-- A whole-value validity policy for unions: which byte lists are valid values of a union
type. -/
abbrev UnionValidity := UnionTy → List AByte → Bool

/-- Trivial whole-value validity: every byte list is valid (the length is checked by
`unionMove`). -/
def trivialUnionValidity : UnionValidity := fun _ _ => true

/-- Empty whole-value validity: no byte list is valid (no value of any union type exists). -/
def emptyUnionValidity : UnionValidity := fun _ _ => false

/-- Moving or copying a union value at union type under the validity policy `wv`: defined iff the
bytes have the union's size and are valid under `wv`, and then returns them unchanged. -/
def unionMove (wv : UnionValidity) (u : UnionTy) (x : List AByte) : Option (List AByte) :=
  if x.length = u.size ∧ wv u x = true then some x else none

/-- Reading field `f` (a typed projection): defined iff `f`'s bytes are valid for `f`, and then
returns those bytes. -/
def readField (f : UField) (x : List AByte) : Option (List AByte) :=
  if f.valid (seg x f.off f.size) = true then some (seg x f.off f.size) else none

/-- Writing the bytes `src` at offset `o` into `x`: positions `[o, o + src.length)` that exist
in `x` take `src`'s bytes; every other position keeps its old byte; the length is unchanged
(bytes past the end of `x` are dropped). -/
def writeBytes (x : List AByte) (o : Nat) (src : List AByte) : List AByte :=
  (List.range x.length).map fun i =>
    if o ≤ i ∧ i < o + src.length then src.getD (i - o) .uninit else x.getD i .uninit

/-- A union move that inherits field `f`'s validity (and hence its niche): defined only if
`f`'s bytes are valid for `f`. This is the semantics that union layouts must not have. -/
def nicheInheritingMove (f : UField) (x : List AByte) : Option (List AByte) :=
  if f.valid (seg x f.off f.size) = true then some x else none

/-- Every field of `u` is uninhabited (no byte list is valid for it). -/
def FieldwiseUninhabited (u : UnionTy) : Prop := ∀ f ∈ u.fields, ∀ bs, f.valid bs = false

/-- A program that, given a union value with bytes `x`, moves it under the validity policy `wv`
and returns a unit-like integer (UB, `none`, iff the move is UB). -/
def moveThenRet (wv : UnionValidity) (u : UnionTy) (x : List AByte) : Option Val :=
  (unionMove wv u x).map fun _ => .int []

/-- An inhabitedness-gated rewrite: if the type is judged uninhabited, the program is replaced
by `Unreachable` (UB, `none`); otherwise it is unchanged. -/
def gatedUnreachable (judgedUninhabited : Bool) (prog : Option Val) : Option Val :=
  if judgedUninhabited then none else prog

/-- The lane mask of a partial write of `len` bytes at offset `o` into a `w`-lane register:
lane `i` is selected iff `o ≤ i < o + len`. -/
def writeMask (w o len : Nat) : List Bool :=
  (List.range w).map fun i => decide (o ≤ i ∧ i < o + len)

/-- The source bytes shifted to register positions: lane `i` holds `src`'s byte `i - o`
(truncated subtraction; lanes outside the write window are never selected). -/
def shiftIn (w o : Nat) (src : List AByte) : List AByte :=
  (List.range w).map fun i => src.getD (i - o) .uninit

/-- Lane-wise select (a blend): lane `i` takes `new`'s byte where the mask is set and `old`'s
byte otherwise; the result is as long as the shortest of the three lists. -/
def laneSelect (mask : List Bool) (old new : List AByte) : List AByte :=
  List.zipWith (fun m (p : AByte × AByte) => if m then p.2 else p.1) mask (List.zip old new)

/-- A register-level partial write into a `union` register: blend the shifted source into the
old register contents under the write mask, lane by lane. Register values other than `raw` are
returned unchanged (partial writes into `initialized` registers are not modelled). -/
def mergeWrite (v : RVal) (o : Nat) (src : List AByte) : RVal :=
  match v with
  | .raw bs => .raw (laneSelect (writeMask bs.length o src.length) bs (shiftIn bs.length o src))
  | v => v

/-- A whole-register write of width `w`: the new register holds `src` at offset `o` and `fill`
(for example `uninit`, standing for poison lanes, or a zero byte) everywhere else. -/
def wholeWrite (w : Nat) (fill : AByte) (o : Nat) (src : List AByte) : RVal :=
  .raw (writeBytes (List.replicate w fill) o src)

/-- Whether a register value has an undefined lane (`poison`, or an `uninit` byte in a `raw`
union register). -/
def hasUndef : RVal → Bool
  | .poison => true
  | .raw bs => bs.any (· == .uninit)
  | _ => false

/-- Passing a register value as a call argument, with or without the `noundef` attribute: with
`noundef`, an argument with an undefined lane is UB (`none`). -/
def passArg (noundef : Bool) (v : RVal) : Option RVal :=
  if noundef && hasUndef v then none else some v

/-! ## Results -/

/-- **Under trivial whole-value validity, moving a union is defined iff the bytes have its size;
reading a field is UB iff the field's bytes are invalid.** For every toy union `u`, field
descriptor `f` and byte list `x`: `unionMove trivialUnionValidity u x = some x` iff
`x.length = u.size`, and `readField f x = none` iff `f.valid` rejects `f`'s bytes. -/
theorem unionMove_trivial_defined_iff_size_and_readField_ub_iff_invalid (u : UnionTy)
    (f : UField) (x : List AByte) :
    (unionMove trivialUnionValidity u x = some x ↔ x.length = u.size) ∧
      (readField f x = none ↔ f.valid (seg x f.off f.size) = false) := by
  refine ⟨?_, ?_⟩
  · unfold unionMove trivialUnionValidity
    by_cases h : x.length = u.size <;> simp [h]
  · unfold readField
    cases f.valid (seg x f.off f.size) <;> simp

/-- **Framing of partial writes.** `writeBytes x o src` has the length of `x`; at every position
`i` of `x` with `o ≤ i < o + src.length` it holds `src`'s byte `i - o`; at every other position
it holds `x`'s old byte. -/
theorem writeBytes_frame (x src : List AByte) (o : Nat) :
    (writeBytes x o src).length = x.length ∧
    (∀ i, i < x.length → o ≤ i → i < o + src.length →
      (writeBytes x o src).getD i .uninit = src.getD (i - o) .uninit) ∧
    (∀ i, ¬ (o ≤ i ∧ i < o + src.length) →
      (writeBytes x o src).getD i .uninit = x.getD i .uninit) := by
  refine ⟨by simp [writeBytes], fun i hi h1 h2 => ?_, fun i hn => ?_⟩
  · simp [writeBytes, List.getD_eq_getElem?_getD, hi, h1, h2]
  · by_cases hi : i < x.length
    · simp [writeBytes, List.getD_eq_getElem?_getD, hi, hn]
    · simp [writeBytes, List.getD_eq_getElem?_getD, hi]

/-- **A wider read after a partial write observes the written bytes plus the old bytes.** For a
read of `k` bytes at `o'` after writing `src` at `o`: byte `j < k` of the read (at a position
`o' + j` inside `x`) is `src`'s byte if `o ≤ o' + j < o + src.length`, and otherwise `x`'s old
byte (which may be `uninit`). -/
theorem readWider_after_partial_write (x src : List AByte) (o o' k j : Nat) (hj : j < k)
    (hin : o' + j < x.length) :
    (seg (writeBytes x o src) o' k).getD j .uninit =
      if o ≤ o' + j ∧ o' + j < o + src.length then src.getD (o' + j - o) .uninit
      else x.getD (o' + j) .uninit := by
  rw [getD_seg, ite_eq_left hj]
  have ⟨_, h1, h2⟩ := writeBytes_frame x src o
  split
  · rename_i h; exact h1 _ hin h.1 h.2
  · rename_i h; exact h2 _ h

/-- The lane blend of `mergeWrite` computes the memory write. -/
theorem laneSelect_writeMask_shiftIn_eq_writeBytes (x src : List AByte) (o : Nat) :
    laneSelect (writeMask x.length o src.length) x (shiftIn x.length o src) =
      writeBytes x o src := by
  apply List.ext_getElem
  · simp [laneSelect, writeMask, shiftIn, writeBytes]
  · intro i h1 h2
    have hi : i < x.length := by simpa [writeBytes] using h2
    simp only [laneSelect, writeMask, shiftIn, writeBytes, List.getElem_zipWith, List.getElem_zip,
      List.getElem_map, List.getElem_range]
    by_cases hw : o ≤ i ∧ i < o + src.length
    · simp [hw]
    · simp [hw, List.getD_eq_getElem?_getD, hi]

/-- **Merging a partial write into a `union` register equals the memory write.** For a `union`
scalar of width at least `n` and a value `x` of length exactly `n`, lowering `x` to the register,
blending `src` in at `o` lane by lane (`mergeWrite`), and raising gives exactly
`writeBytes x o src`. -/
theorem unionRegister_mergeWrite_eq_memoryWrite (p : Prim) (n : Nat) (hn : n ≤ p.size)
    (x src : List AByte) (o : Nat) (hx : x.length = n) :
    raise n (.scalar (.union p)) (.one (mergeWrite (lowerScalar (.union p) (seg x 0 p.size)) o src))
      = writeBytes x o src := by
  have hseg : seg x 0 p.size = x := by
    simp [seg, List.take_of_length_le (by omega : x.length ≤ p.size)]
  have hl : (writeBytes x o src).length = n := by simp [writeBytes, hx]
  simp only [lowerScalar, hseg, mergeWrite, raise, raiseScalar,
    laneSelect_writeMask_shiftIn_eq_writeBytes]
  apply List.ext_getElem (by simp [length_place, hl])
  intro i h1 h2
  have hi : i < n := by simpa [length_place] using h1
  simp [place, chunkAt, hl, hi]

/-- **No constant fill makes a whole-register write refine a partial write.** For every fill byte
`fill`, there is a two-byte union value `x` such that writing one byte `bits 1` at offset `0` and
reading both bytes as an integer is defined, and the same read after a whole-register write of
width `2` that puts `fill` in the untouched lane is not at least as defined (`¬ OutLe`). -/
theorem wholeRegisterWrite_no_constant_fill_refines_partial_write :
    ∀ fill : AByte, ∃ x : List AByte, x.length = 2 ∧
      ¬ OutLe (readInt 0 2 (writeBytes x 0 [.bits 1]))
          (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1]))) := by
  intro fill
  have hrange2 : List.range 2 = [0, 1] := rfl
  cases fill with
  | uninit => exact ⟨[.bits 7, .bits 9], rfl, by decide⟩
  | bits b =>
    by_cases hb : b = 9
    · subst hb; exact ⟨[.bits 7, .bits 8], rfl, by decide⟩
    · refine ⟨[.bits 7, .bits 9], rfl, ?_⟩
      simp [readInt, writeBytes, wholeWrite, raiseScalar, seg, hrange2, allInit, datas, OutLe,
        Val.leb, AByte.isInit, AByte.data]
      exact Ne.symm hb
  | ptrFrag b p i =>
    by_cases hb : b = 9
    · subst hb
      refine ⟨[.bits 7, .bits 8], rfl, ?_⟩
      simp [readInt, writeBytes, wholeWrite, raiseScalar, seg, hrange2, allInit, datas, OutLe,
        Val.leb, AByte.isInit, AByte.data]
    · refine ⟨[.bits 7, .bits 9], rfl, ?_⟩
      simp [readInt, writeBytes, wholeWrite, raiseScalar, seg, hrange2, allInit, datas, OutLe,
        Val.leb, AByte.isInit, AByte.data]
      exact Ne.symm hb

/-- Positive control: if every byte of `x` outside the write window is already `uninit`, the
whole-register write with `uninit` fill equals the partial write. -/
theorem wholeWrite_uninit_eq_writeBytes_of_untouched_uninit (x src : List AByte) (o : Nat)
    (h : ∀ i, i < x.length → ¬ (o ≤ i ∧ i < o + src.length) → x.getD i .uninit = .uninit) :
    raiseScalar (.union (.int x.length)) (wholeWrite x.length .uninit o src) = writeBytes x o src := by
  simp only [wholeWrite, raiseScalar]
  apply List.ext_getElem (by simp [writeBytes])
  intro i h1 h2
  have hi : i < x.length := by simpa [writeBytes] using h2
  simp only [writeBytes, List.getElem_map, List.getElem_range]
  by_cases hw : o ≤ i ∧ i < o + src.length
  · simp [hw]
  · simp only [hw, ite_false]
    rw [h i hi hw]
    simp [List.getD_eq_getElem?_getD, hi]

/-- Positive control: a full-width write (offset `0`, at least as many source bytes as the
register has lanes) as a whole-register write with any fill equals the partial write. -/
theorem wholeWrite_eq_writeBytes_of_full_width (x src : List AByte) (fill : AByte)
    (hsrc : x.length ≤ src.length) :
    raiseScalar (.union (.int x.length)) (wholeWrite x.length fill 0 src) = writeBytes x 0 src := by
  simp only [wholeWrite, raiseScalar]
  apply List.ext_getElem (by simp [writeBytes])
  intro i h1 h2
  have hi : i < x.length := by simpa [writeBytes] using h2
  have hw : i < src.length := by omega
  simp [writeBytes, hw]

/-- The `NonZeroU8` field: one initialized byte with non-zero data. -/
def nonZeroU8Field : UField :=
  ⟨0, 1, fun bs => match bs with | [b] => b.isInit && b.data != 0 | _ => false⟩

/-- The `u8` field: one initialized byte. -/
def u8Field : UField := ⟨0, 1, fun bs => match bs with | [b] => b.isInit | _ => false⟩

/-- The union `{ a: NonZeroU8, b: u8 }`. -/
def nzOrU8 : UnionTy := ⟨1, [nonZeroU8Field, u8Field]⟩

/-- **A union that inherited a field's niche would make a move UB after a valid write.** In
`nzOrU8 = { a: NonZeroU8, b: u8 }`, starting from the bytes of `a = 5` and writing `b = 0`:
reading `b` gives `[bits 0]`, the union move under trivial whole-value validity is defined, and
the niche-inheriting move `nicheInheritingMove nonZeroU8Field` is UB. -/
theorem nicheInheriting_union_move_ub_after_valid_field_write :
    readField u8Field (writeBytes [.bits 5] 0 [.bits 0]) = some [.bits 0] ∧
    unionMove trivialUnionValidity nzOrU8 (writeBytes [.bits 5] 0 [.bits 0]) = some [.bits 0] ∧
    nicheInheritingMove nonZeroU8Field (writeBytes [.bits 5] 0 [.bits 0]) = none := by
  decide

/-- Under trivial whole-value validity every toy union is inhabited: the all-`uninit` byte list
of its size is moved without UB. -/
theorem union_wholeValue_inhabited_of_trivialValidity (u : UnionTy) :
    ∃ x : List AByte, x.length = u.size ∧ unionMove trivialUnionValidity u x = some x :=
  ⟨List.replicate u.size .uninit, by simp, by simp [unionMove, trivialUnionValidity]⟩

/-- The one-byte union whose only field is uninhabited (it has no zero-sized field). -/
def neverUnion : UnionTy := ⟨1, [⟨0, 1, fun _ => false⟩]⟩

/-- **An `Unreachable` rewrite of a union move refines iff whole-value validity admits no value.**
For every whole-value validity policy `wv`, toy union `u` and gate `gate` that fires on `u`
(`gate u = true`), replacing the move-then-return program by UB (`gatedUnreachable`) is at least
as defined as the program on every byte list of `u`'s size iff `wv` rejects every byte list of
`u`'s size. -/
theorem unreachableRewrite_refines_iff_no_wholeValue_valid (wv : UnionValidity) (u : UnionTy)
    (gate : UnionTy → Bool) (hgate : gate u = true) :
    (∀ x : List AByte, x.length = u.size →
      OutLe (moveThenRet wv u x) (gatedUnreachable (gate u) (moveThenRet wv u x))) ↔
    ∀ x : List AByte, x.length = u.size → wv u x = false := by
  simp only [hgate, gatedUnreachable, ite_true]
  constructor
  · intro h x hx
    have := h x hx
    cases hw : wv u x
    · rfl
    · exfalso
      simp [moveThenRet, unionMove, hx, hw, OutLe] at this
  · intro h x hx
    simp [moveThenRet, unionMove, hx, h x hx, OutLe]

/-- **Under trivial whole-value validity, a field-wise uninhabitedness gate is not a
refinement.** For every gate that fires on every `FieldwiseUninhabited` union: `neverUnion` (one
byte, whose only field is uninhabited, no zero-sized field) is `FieldwiseUninhabited`, the
program that moves its value `[uninit]` under `trivialUnionValidity` and returns is defined, and
the gated `Unreachable` rewrite of it is not at least as defined. -/
theorem fieldwiseUninhabited_gate_not_refinement_of_trivialValidity (gate : UnionTy → Bool)
    (hgate : ∀ u, FieldwiseUninhabited u → gate u = true) :
    FieldwiseUninhabited neverUnion ∧
    moveThenRet trivialUnionValidity neverUnion [.uninit] = some (.int []) ∧
    ¬ OutLe (moveThenRet trivialUnionValidity neverUnion [.uninit])
        (gatedUnreachable (gate neverUnion)
          (moveThenRet trivialUnionValidity neverUnion [.uninit])) := by
  have hf : FieldwiseUninhabited neverUnion := by
    intro f hf bs
    simp [neverUnion] at hf
    subst hf
    rfl
  refine ⟨hf, rfl, ?_⟩
  rw [hgate _ hf]
  decide

/-- **`noundef` on a `union` scalar argument introduces UB.** For every primitive `p` of width
at least `1`, the all-`uninit` byte list of width `p.size`, lowered to a `union` scalar register,
is passed without UB when the argument has no `noundef` attribute and is UB with `noundef`. -/
theorem noundef_on_union_scalar_introduces_ub (p : Prim) (hp : 1 ≤ p.size) :
    passArg false (lowerScalar (.union p) (List.replicate p.size .uninit)) =
        some (lowerScalar (.union p) (List.replicate p.size .uninit)) ∧
      passArg true (lowerScalar (.union p) (List.replicate p.size .uninit)) = none := by
  obtain ⟨k, hk⟩ : ∃ k, p.size = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
  refine ⟨rfl, ?_⟩
  simp [passArg, lowerScalar, hasUndef, hk, List.replicate_succ]

/-- Escape hatch for `noundef_on_union_scalar_introduces_ub`: a value lowered to a `union`
register trips `noundef` iff it is not all initialized. -/
theorem passArg_noundef_union_eq_none_iff (p : Prim) (x : List AByte) :
    passArg true (lowerScalar (.union p) x) = none ↔ allInit x = false := by
  simp only [passArg, lowerScalar, hasUndef, Bool.true_and]
  have key : x.any (· == AByte.uninit) = !allInit x := by
    induction x with
    | nil => rfl
    | cons a as ih =>
      simp only [List.any_cons, allInit, List.all_cons] at ih ⊢
      rw [ih]
      cases a <;> simp [AByte.isInit]
  rw [key]
  cases allInit x <;> simp

/-- Positive control: `noundef` never fires on a non-`poison` value lowered to an `initialized`
scalar register. -/
theorem noundef_passes_initialized_nonpoison (q : Prim) (r : List Nat → Bool) (bs : List AByte)
    (h : lowerScalar (.initialized q r) bs ≠ .poison) :
    passArg true (lowerScalar (.initialized q r) bs) = some (lowerScalar (.initialized q r) bs) := by
  have hraw : ∀ cs, lowerScalar (.initialized q r) bs ≠ .raw cs :=
    lowerScalar_initialized_ne_raw q r bs
  unfold passArg
  cases hv : lowerScalar (.initialized q r) bs with
  | poison => exact absurd hv h
  | raw cs => exact absurd hv (hraw cs)
  | int ds => rfl
  | ptr pr ds => rfl

/-- Complement to `wholeRegisterWrite_no_constant_fill_refines_partial_write`, which proves
"not at least as defined" (`¬ OutLe`), not "strictly less defined": for every initialized fill
byte and every byte list `x`, the two-byte integer read after the whole-register write is not
strictly less defined than the read after the partial write (`OutLe` in that direction together
with inequality fails). -/
theorem wholeWrite_init_fill_never_strictly_less_defined (fill : AByte) (hf : fill.isInit = true)
    (x : List AByte) :
    ¬ (OutLe (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1])))
          (readInt 0 2 (writeBytes x 0 [.bits 1])) ∧
        readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1])) ≠
          readInt 0 2 (writeBytes x 0 [.bits 1])) := by
  rintro ⟨hle, hne⟩
  have hwhole : readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1])) =
      some (.int [1, fill.data]) := by
    have hr2 : List.range 2 = [0, 1] := rfl
    match fill with
    | .uninit => simp [AByte.isInit] at hf
    | .bits b =>
      simp [wholeWrite, writeBytes, hr2, raiseScalar, readInt, seg, allInit, datas, AByte.isInit,
        AByte.data]
    | .ptrFrag b p i =>
      simp [wholeWrite, writeBytes, hr2, raiseScalar, readInt, seg, allInit, datas, AByte.isInit,
        AByte.data]
  rw [hwhole] at hle hne
  cases hp : readInt 0 2 (writeBytes x 0 [.bits 1]) with
  | none => rw [hp] at hle; exact hle
  | some v =>
    rw [hp] at hle hne
    cases v with
    | ptr pr ds => simp [OutLe, Val.leb] at hle
    | int ds =>
      simp only [OutLe, Val.leb, beq_iff_eq] at hle
      exact hne (by simp [hle])

/-- Instance: with fill `bits 0` and `x = [bits 7, bits 9]`, the partial-write read
(`[1, 9]`) and the whole-register-write read (`[1, 0]`) are incomparable in `OutLe`. -/
theorem wholeWrite_bits0_incomparable_with_partial :
    ¬ OutLe (readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1]))
        (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1]))) ∧
    ¬ OutLe (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1])))
        (readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1])) := by
  decide

/-- Instance: with fill `uninit`, the whole-register-write read is UB (`none`), which is strictly
less defined than the defined partial-write read on `x = [bits 7, bits 9]`. -/
theorem wholeWrite_uninit_fill_strictly_less_defined_instance :
    OutLe (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1])))
        (readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1])) ∧
    readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1])) ≠
        readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1]) := by
  decide

end Toy.ReprLower
