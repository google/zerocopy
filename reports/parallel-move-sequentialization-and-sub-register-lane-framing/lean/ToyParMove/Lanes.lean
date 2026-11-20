/-!
Sub-register lanes. A register is an `n`-bit word; a lane is a bit range `(off, wid)`. A
`preserveUpper` write (`putLane`) replaces the lane's bits and keeps all others; a `zeroExtend`
write (`writeZext`) replaces the whole word by the zero-extended value.
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

/-! ### Lens laws (local definitions) -/

section LensLaws
variable {S A : Type}

/-- GetPut: writing back what was read changes nothing. -/
def GetPut (get : S → A) (put : A → S → S) : Prop := ∀ s, put (get s) s = s

/-- PutGet: reading after a write returns the written value. -/
def PutGet (get : S → A) (put : A → S → S) : Prop := ∀ a s, get (put a s) = a

/-- PutPut: a second write overrides the first. -/
def PutPut (_get : S → A) (put : A → S → S) : Prop := ∀ a a' s, put a' (put a s) = put a' s

/-- A *very well-behaved* lens: GetPut, PutGet and PutPut. -/
def VeryWellBehaved (get : S → A) (put : A → S → S) : Prop :=
  GetPut get put ∧ PutGet get put ∧ PutPut get put

end LensLaws

/-- Positive example (`VeryWellBehaved`): the first projection of a pair. -/
theorem veryWellBehaved_fst :
    VeryWellBehaved (fun s : Nat × Nat => s.1) (fun a s => (a, s.2)) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Negative example (`VeryWellBehaved`, PutGet fails): a "put" that ignores the value. -/
theorem not_putGet_constant_put :
    ¬ PutGet (fun s : Nat => s) (fun _ _ => 0) := fun h => absurd (h 1 0) (by decide)

/-- Negative example (`VeryWellBehaved`): the same constant "put" is not a very well-behaved
lens. -/
theorem not_veryWellBehaved_constant_put :
    ¬ VeryWellBehaved (fun s : Nat => s) (fun _ _ => 0) := fun h => not_putGet_constant_put h.2.1

/-! ### Lanes -/

/-- A lane: the bit range `[off, off + wid)` of a register word. -/
structure Lane where
  off : Nat
  wid : Nat
deriving DecidableEq, Repr

/-- The lane lies inside an `n`-bit register. -/
def Lane.Fits (L : Lane) (n : Nat) : Prop := L.off + L.wid ≤ n

instance (L : Lane) (n : Nat) : Decidable (L.Fits n) := inferInstanceAs (Decidable (_ ≤ _))

/-- Two lanes occupy disjoint bit ranges: one of them is empty, or one ends before the other
begins. Bit positions beyond the register are counted too (see `Lane.DisjointIn` for the test
restricted to an `n`-bit register, and `Lane.disjoint_iff_bits` for the bitwise meaning). -/
def Lane.Disjoint (L₁ L₂ : Lane) : Prop :=
  L₁.wid = 0 ∨ L₂.wid = 0 ∨ L₁.off + L₁.wid ≤ L₂.off ∨ L₂.off + L₂.wid ≤ L₁.off

instance (L₁ L₂ : Lane) : Decidable (L₁.Disjoint L₂) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- `Lane.Disjoint` is exactly disjointness of the bit sets `[off, off + wid)`. -/
theorem Lane.disjoint_iff_bits (L₁ L₂ : Lane) :
    L₁.Disjoint L₂ ↔
      ∀ i, ¬ (L₁.off ≤ i ∧ i < L₁.off + L₁.wid ∧ L₂.off ≤ i ∧ i < L₂.off + L₂.wid) := by
  unfold Lane.Disjoint
  constructor
  · rintro h i ⟨h1, h2, h3, h4⟩
    omega
  · intro h
    apply Classical.byContradiction
    intro hn
    exact h (max L₁.off L₂.off) ⟨Nat.le_max_left _ _, by omega, Nat.le_max_right _ _, by omega⟩

/-- Two lanes share no bit position *inside an `n`-bit register*. -/
def Lane.DisjointIn (n : Nat) (L₁ L₂ : Lane) : Prop :=
  ∀ i, i < n → ¬ (L₁.off ≤ i ∧ i < L₁.off + L₁.wid ∧ L₂.off ≤ i ∧ i < L₂.off + L₂.wid)

instance (n : Nat) (L₁ L₂ : Lane) : Decidable (L₁.DisjointIn n L₂) :=
  inferInstanceAs (Decidable (∀ i, i < n → _))

/-- The `n`-bit mask with ones exactly on the lane's bits (truncated to the register). -/
def laneMask (n : Nat) (L : Lane) : BitVec n := ((BitVec.allOnes L.wid).setWidth n) <<< L.off

/-- Read a lane: bits `off .. off + wid - 1` of the word (bits beyond the word read as zero). -/
def getLane {n : Nat} (L : Lane) (w : BitVec n) : BitVec L.wid := w.extractLsb' L.off L.wid

/-- **`preserveUpper` write** of the lane value `v`: the lane's bits become `v`, all other bits
of the word are kept. Captures x86-64 8-bit and 16-bit register writes (`al`, `ah`, `ax`). -/
def putLane {n : Nat} (L : Lane) (v : BitVec L.wid) (w : BitVec n) : BitVec n :=
  (w &&& ~~~(laneMask n L)) ||| ((v.setWidth n) <<< L.off)

/-- **`zeroExtend` write** of a `wid`-bit value into an `n`-bit register: the whole word is
replaced by the zero-extended value; the old word is ignored. Captures x86-64 32-bit register
writes and AArch64 `W`-register writes. -/
def writeZext (n : Nat) {wid : Nat} (v : BitVec wid) (_w : BitVec n) : BitVec n := v.setWidth n

section LaneLemmas
variable {n : Nat}

theorem getLsbD_getLane (L : Lane) (w : BitVec n) (j : Nat) :
    (getLane L w).getLsbD j = (decide (j < L.wid) && w.getLsbD (L.off + j)) := by
  simp [getLane, BitVec.getLsbD_extractLsb']

/-- Bitwise description of a `preserveUpper` write. -/
theorem getLsbD_putLane (L : Lane) (v : BitVec L.wid) (w : BitVec n) {i : Nat} (hi : i < n) :
    (putLane L v w).getLsbD i =
      if L.off ≤ i ∧ i < L.off + L.wid then v.getLsbD (i - L.off) else w.getLsbD i := by
  simp only [putLane, laneMask, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hi,
    decide_true, Bool.true_and]
  by_cases h1 : i < L.off
  · have : ¬ (L.off ≤ i ∧ i < L.off + L.wid) := fun h => by omega
    simp [h1, this]
  · by_cases h2 : i - L.off < L.wid
    · have : L.off ≤ i ∧ i < L.off + L.wid := ⟨by omega, by omega⟩
      simp [h1, h2, this, show i - L.off < n by omega]
    · have : ¬ (L.off ≤ i ∧ i < L.off + L.wid) := fun h => by omega
      simp [h1, h2, this, show i - L.off < n by omega,
        BitVec.getLsbD_of_ge v (i - L.off) (by omega)]

/-- GetPut for `preserveUpper` writes (no fit hypothesis needed). -/
theorem putLane_getPut (L : Lane) : GetPut (getLane (n := n) L) (putLane L) := by
  intro w
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_putLane L _ w hi, getLsbD_getLane]
  split
  · next h =>
    have : i - L.off < L.wid := by omega
    simp [this, show L.off + (i - L.off) = i by omega]
  · rfl

/-- PutPut for `preserveUpper` writes (no fit hypothesis needed). -/
theorem putLane_putPut (L : Lane) : PutPut (getLane (n := n) L) (putLane L) := by
  intro v v' w
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_putLane L _ _ hi, getLsbD_putLane L _ _ hi, getLsbD_putLane L _ _ hi]
  split <;> rfl

/-- PutGet for `preserveUpper` writes, for a lane that fits in the register. -/
theorem putLane_putGet_of_fits {L : Lane} (hfit : L.Fits n) : PutGet (getLane (n := n) L) (putLane L) := by
  intro v w
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_getLane, getLsbD_putLane L v w (show L.off + j < n by unfold Lane.Fits at hfit; omega)]
  have : L.off ≤ L.off + j ∧ L.off + j < L.off + L.wid := ⟨by omega, by omega⟩
  simp [hj, this]

/-- **A `preserveUpper` write to a lane that fits is a very well-behaved lens.** -/
theorem putLane_veryWellBehaved_of_fits {L : Lane} (hfit : L.Fits n) :
    VeryWellBehaved (getLane (n := n) L) (putLane L) :=
  ⟨putLane_getPut L, putLane_putGet_of_fits hfit, putLane_putPut L⟩

/-- **Disjoint lanes commute.** -/
theorem putLane_comm_of_disjoint {L₁ L₂ : Lane} (hd : L₁.Disjoint L₂) (v₁ : BitVec L₁.wid)
    (v₂ : BitVec L₂.wid) (w : BitVec n) :
    putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_putLane _ _ _ hi]
  unfold Lane.Disjoint at hd
  by_cases h1 : L₁.off ≤ i ∧ i < L₁.off + L₁.wid
  · have h2 : ¬ (L₂.off ≤ i ∧ i < L₂.off + L₂.wid) := fun h => by omega
    simp [h1, h2]
  · simp [h1]

/-- **Disjoint lanes frame each other:** writing one lane does not change what another,
disjoint lane reads. -/
theorem getLane_putLane_of_disjoint {L₁ L₂ : Lane} (hd : L₁.Disjoint L₂) (v : BitVec L₁.wid)
    (w : BitVec n) : getLane L₂ (putLane L₁ v w) = getLane L₂ w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_getLane, getLsbD_getLane]
  by_cases hn : L₂.off + j < n
  · rw [getLsbD_putLane L₁ v w hn]
    unfold Lane.Disjoint at hd
    have : ¬ (L₁.off ≤ L₂.off + j ∧ L₂.off + j < L₁.off + L₁.wid) := fun h => by omega
    simp [this]
  · simp [BitVec.getLsbD_of_ge _ _ (show n ≤ L₂.off + j by omega)]

/-- **Characterization (in-register).** All pairs of writes to `L₁` and `L₂` commute iff the two
lanes share no bit position inside the `n`-bit register. No hypothesis is needed. -/
theorem putLane_comm_iff_disjointIn (L₁ L₂ : Lane) :
    (∀ (v₁ : BitVec L₁.wid) (v₂ : BitVec L₂.wid) (w : BitVec n),
      putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w)) ↔ L₁.DisjointIn n L₂ := by
  constructor
  · intro h i hin ⟨h1a, h1b, h2a, h2b⟩
    have e := congrArg (fun x => x.getLsbD i) (h (BitVec.allOnes L₁.wid) 0#L₂.wid 0#n)
    simp only [getLsbD_putLane _ _ _ hin, h1a, h1b, h2a, h2b, and_self, ite_true,
      BitVec.getLsbD_allOnes, BitVec.getLsbD_zero] at e
    simp at e
    omega
  · intro hd v₁ v₂ w
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [getLsbD_putLane _ _ _ hi]
    by_cases h1 : L₁.off ≤ i ∧ i < L₁.off + L₁.wid
    · have h2 : ¬ (L₂.off ≤ i ∧ i < L₂.off + L₂.wid) := fun h2 => hd i hi ⟨h1.1, h1.2, h2.1, h2.2⟩
      simp [h1, h2]
    · simp [h1]

/-- **Characterization (bit ranges).** If at least one of the two lanes fits in the register, all
pairs of writes to `L₁` and `L₂` commute iff the lanes are `Disjoint`. -/
theorem putLane_comm_iff_disjoint_of_fits {L₁ L₂ : Lane} (hfit : L₁.Fits n ∨ L₂.Fits n) :
    (∀ (v₁ : BitVec L₁.wid) (v₂ : BitVec L₂.wid) (w : BitVec n),
      putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w)) ↔ L₁.Disjoint L₂ := by
  rw [putLane_comm_iff_disjointIn, Lane.disjoint_iff_bits]
  unfold Lane.DisjointIn Lane.Fits at *
  constructor
  · intro h i hi
    exact h i (by rcases hfit with hf | hf <;> omega) hi
  · intro h i _ hi
    exact h i hi

/-- A `zeroExtend` write equals the full-width `preserveUpper` write of the zero-extended value:
it is a lens on the whole register, viewed as replacing the whole word. -/
theorem writeZext_eq_putLane_full {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    writeZext n v w = putLane ⟨0, n⟩ (v.setWidth n) w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_putLane _ _ _ hi]
  have : (0 : Nat) ≤ i ∧ i < 0 + n := ⟨Nat.zero_le _, by omega⟩
  simp [writeZext, this, show ¬ n ≤ i by omega]

/-- The full-width lane is a very well-behaved lens (instance of `putLane_veryWellBehaved_of_fits`). -/
theorem putLane_full_veryWellBehaved :
    VeryWellBehaved (getLane (n := n) ⟨0, n⟩) (putLane ⟨0, n⟩) :=
  putLane_veryWellBehaved_of_fits (by simp [Lane.Fits])

/-- PutGet for `zeroExtend` writes read through the low lane, when the value fits. -/
theorem writeZext_putGet_of_le {wid : Nat} (h : wid ≤ n) :
    PutGet (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid)) := by
  intro v w
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_getLane]
  simp only [writeZext, BitVec.getLsbD_setWidth]
  have : j < n := by simp at hj; omega
  simp at hj
  simp [hj, this]

/-- PutPut for `zeroExtend` writes (definitional). -/
theorem writeZext_putPut {wid : Nat} :
    PutPut (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid)) := fun _ _ _ => rfl

/-- **Characterization of GetPut for `zeroExtend` writes.** Writing back the low `wid` bits with a
`zeroExtend` write leaves the word unchanged iff all bits at positions `≥ wid` are zero. -/
theorem writeZext_getPut_iff {wid : Nat} (w : BitVec n) :
    writeZext n (getLane ⟨0, wid⟩ w) w = w ↔ ∀ i, wid ≤ i → w.getLsbD i = false := by
  constructor
  · intro h i hi
    have := congrArg (fun x => x.getLsbD i) h
    simp only [writeZext, BitVec.getLsbD_setWidth, getLsbD_getLane] at this
    rw [← this]
    simp [show ¬ i < wid by omega]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [writeZext, BitVec.getLsbD_setWidth, getLsbD_getLane, hi, decide_true,
      Bool.true_and]
    by_cases hw : i < wid
    · simp [hw]
    · simp [hw, h i (by omega)]

/-- **Impossibility: a `zeroExtend` write is not a lens with a narrower view.** If `wid < n`, no
getter `g : BitVec n → BitVec wid` whatsoever makes `writeZext` satisfy GetPut. -/
theorem writeZext_not_getPut_of_lt {wid : Nat} (h : wid < n) :
    ¬ ∃ g : BitVec n → BitVec wid, GetPut g (writeZext n (wid := wid)) := by
  rintro ⟨g, hg⟩
  have := congrArg (fun x => x.getLsbD wid) (hg (BitVec.allOnes n))
  simp only [writeZext, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_of_ge (g (BitVec.allOnes n)) wid (Nat.le_refl _)] at this
  simp [h] at this

/-- Positive control: at full width (`wid = n`) the `zeroExtend` write with the low-lane getter
satisfies GetPut (and, by `writeZext_putGet_of_le`, PutGet). -/
theorem writeZext_getPut_full : GetPut (getLane (n := n) ⟨0, n⟩) (writeZext n (wid := n)) := by
  intro w
  exact (writeZext_getPut_iff w).2 (fun i hi => BitVec.getLsbD_of_ge w i hi)

/-- When the value is at least as wide as the register (`n ≤ wid`), the `zeroExtend` write
(which then truncates) satisfies GetPut with the low-lane getter. -/
theorem writeZext_getPut_of_ge {wid : Nat} (h : n ≤ wid) :
    GetPut (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid)) := by
  intro w
  exact (writeZext_getPut_iff w).2 (fun i hi => BitVec.getLsbD_of_ge w i (Nat.le_trans h hi))

/-- The result of a `zeroExtend` write of a value that fits has zero bits at every position
`≥ wid`: zero-extending writes stay inside the set of words with zero upper bits. -/
theorem writeZext_upper_zero {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    ∀ i, wid ≤ i → (writeZext n v w).getLsbD i = false := by
  intro i hi
  simp [writeZext, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge v i hi]

end LaneLemmas

/-! ### Named lanes of a 64-bit register (used only in examples) -/

/-- Bits 0..7 (x86 `al`). -/
def laneLow8 : Lane := ⟨0, 8⟩
/-- Bits 8..15 (x86 `ah`). -/
def laneHigh8 : Lane := ⟨8, 8⟩
/-- Bits 0..15 (x86 `ax`). -/
def laneLow16 : Lane := ⟨0, 16⟩
/-- Bits 0..31 (x86 `eax`, AArch64 `W` view). -/
def laneLow32 : Lane := ⟨0, 32⟩

/-! ### Definition examples -/

/-- Positive example (`putLane`): an 8-bit write to the low byte keeps the upper 56 bits. -/
theorem putLane_low8_example :
    putLane laneLow8 0xFF#8 (0x1122334455667788#64) = 0x11223344556677FF#64 := by decide

/-- Positive example (`putLane`): a write to bits 8..15 keeps all other bits. -/
theorem putLane_high8_example :
    putLane laneHigh8 0xAB#8 (0x1122334455667788#64) = 0x112233445566AB88#64 := by decide

/-- Negative example (`putLane` is not a zero-extending write): the upper bits survive. -/
theorem putLane_low32_not_zext :
    putLane laneLow32 0xDEADBEEF#32 (0x1122334455667788#64) ≠
      writeZext 64 0xDEADBEEF#32 (0x1122334455667788#64) := by decide

/-- Positive example (`writeZext`): a 32-bit write clears the upper 32 bits. -/
theorem writeZext_example :
    writeZext 64 0xDEADBEEF#32 (0x1122334455667788#64) = 0x00000000DEADBEEF#64 := by decide

/-- Positive / negative examples (`Lane.Disjoint`): `al`/`ah` are disjoint, `al`/`ax` are not, and
an empty lane is disjoint from every lane (it has no bits), even one that surrounds its offset. -/
theorem disjoint_examples :
    laneLow8.Disjoint laneHigh8 ∧ ¬ laneLow8.Disjoint laneLow16 ∧ Lane.Disjoint ⟨4, 0⟩ ⟨0, 8⟩ := by
  decide

/-- Positive / negative examples (`Lane.DisjointIn`): lanes `[6,10)` and `[8,12)` overlap only
beyond bit 7, so they are disjoint inside an 8-bit register but not inside a 16-bit one. -/
theorem disjointIn_examples :
    Lane.DisjointIn 8 ⟨6, 4⟩ ⟨8, 4⟩ ∧ ¬ Lane.DisjointIn 16 ⟨6, 4⟩ ⟨8, 4⟩ := by decide

/-- Positive / negative examples (`getLane`): reading `ah`; bits beyond the word read as zero. -/
theorem getLane_examples :
    getLane (n := 64) ⟨8, 8⟩ (0x1122334455667788#64) = (0x77#8 : BitVec 8) ∧
    getLane (n := 64) ⟨60, 8⟩ (BitVec.allOnes 64) = (0x0F#8 : BitVec 8) := by
  constructor <;> decide

/-- Negative example (`writeZext`): a 32-bit zero-extending write does not keep the upper half. -/
theorem writeZext_not_preserve_upper :
    writeZext 64 0xDEADBEEF#32 (0x1122334455667788#64) ≠ 0x11223344DEADBEEF#64 := by decide

/-- Non-claim witness (`writeZext` truncates a value wider than the register). -/
theorem writeZext_truncates_example : writeZext 8 (0x1234#16) (0#8) = 0x34#8 := by decide

/-- Positive / negative examples (`Lane.Fits`). -/
theorem fits_examples : laneLow32.Fits 64 ∧ ¬ (Lane.Fits ⟨60, 8⟩ 64) := by decide

/-! ### Tightness, counterexamples, non-vacuity for the lane results -/

/-- Counterexample (hypothesis `Fits` of `putLane_putGet_of_fits` and
`putLane_veryWellBehaved_of_fits`): a lane sticking out of an 8-bit register loses its upper
bits, so PutGet (and hence very-well-behavedness) fails. -/
theorem putLane_putGet_needs_fits :
    ¬ (Lane.Fits ⟨4, 8⟩ 8) ∧
    ¬ PutGet (getLane (n := 8) ⟨4, 8⟩) (putLane ⟨4, 8⟩) ∧
    ¬ VeryWellBehaved (getLane (n := 8) ⟨4, 8⟩) (putLane ⟨4, 8⟩) ∧
    getLane (n := 8) ⟨4, 8⟩ (putLane ⟨4, 8⟩ (0xFF#8) (0#8)) ≠ (0xFF#8) := by
  have h : getLane (n := 8) ⟨4, 8⟩ (putLane ⟨4, 8⟩ (0xFF#8) (0#8)) ≠ (0xFF#8) := by decide
  exact ⟨by decide, fun hp => h (hp _ _), fun hv => h (hv.2.1 _ _), h⟩

/-- **Counterexample: overlapping lanes do not commute.** Writing `al` and `ax` of a 16-bit
register in the two orders gives different words. -/
theorem putLane_overlapping_not_comm :
    ¬ laneLow8.Disjoint laneLow16 ∧
    putLane laneLow8 (0xFF#8) (putLane laneLow16 (0x0000#16) (0#16)) ≠
      putLane laneLow16 (0x0000#16) (putLane laneLow8 (0xFF#8) (0#16)) := by decide

/-- Counterexample (hypothesis `Disjoint` of `getLane_putLane_of_disjoint`). -/
theorem getLane_putLane_needs_disjoint :
    ¬ laneLow8.Disjoint laneLow16 ∧
    getLane laneLow16 (putLane laneLow8 (0xFF#8) (0#16)) ≠ getLane laneLow16 (0#16) := by decide

/-- Counterexample (hypothesis "one lane fits" of `putLane_comm_iff_disjoint_of_fits`): in an
8-bit register, the lanes `[6,10)` and `[8,12)` overlap only beyond bit 7; all writes commute,
but the lanes are not `Disjoint`, so the equivalence fails. -/
theorem putLane_comm_iff_needs_fits :
    ¬ (Lane.Fits ⟨6, 4⟩ 8 ∨ Lane.Fits ⟨8, 4⟩ 8) ∧
    (∀ (v₁ : BitVec 4) (v₂ : BitVec 4) (w : BitVec 8),
      putLane ⟨6, 4⟩ v₁ (putLane ⟨8, 4⟩ v₂ w) = putLane ⟨8, 4⟩ v₂ (putLane ⟨6, 4⟩ v₁ w)) ∧
    ¬ Lane.Disjoint ⟨6, 4⟩ ⟨8, 4⟩ ∧
    ¬ ((∀ (v₁ : BitVec 4) (v₂ : BitVec 4) (w : BitVec 8),
      putLane ⟨6, 4⟩ v₁ (putLane ⟨8, 4⟩ v₂ w) = putLane ⟨8, 4⟩ v₂ (putLane ⟨6, 4⟩ v₁ w)) ↔
      Lane.Disjoint ⟨6, 4⟩ ⟨8, 4⟩) := by
  have hc : ∀ (v₁ : BitVec 4) (v₂ : BitVec 4) (w : BitVec 8),
      putLane ⟨6, 4⟩ v₁ (putLane ⟨8, 4⟩ v₂ w) = putLane ⟨8, 4⟩ v₂ (putLane ⟨6, 4⟩ v₁ w) :=
    (putLane_comm_iff_disjointIn (n := 8) ⟨6, 4⟩ ⟨8, 4⟩).2 (by decide)
  have hnd : ¬ Lane.Disjoint ⟨6, 4⟩ ⟨8, 4⟩ := by decide
  exact ⟨by decide, hc, hnd, fun h => hnd (h.1 hc)⟩

/-- Counterexample (hypothesis `wid ≤ n` of `writeZext_putGet_of_le`). -/
theorem writeZext_putGet_needs_fit :
    ¬ (16 ≤ 8) ∧ ¬ PutGet (getLane (n := 8) ⟨0, 16⟩) (writeZext 8 (wid := 16)) ∧
    getLane (n := 8) ⟨0, 16⟩ (writeZext 8 (0xFFFF#16) (0#8)) ≠ (0xFFFF#16) := by
  have h : getLane (n := 8) ⟨0, 16⟩ (writeZext 8 (0xFFFF#16) (0#8)) ≠ (0xFFFF#16) := by decide
  exact ⟨by decide, fun hp => h (hp _ _), h⟩

/-- Counterexample (hypothesis `wid < n` of `writeZext_not_getPut_of_lt`): at full width a getter
exists. -/
theorem writeZext_not_getPut_needs_lt :
    ¬ ((8 : Nat) < 8) ∧ ∃ g : BitVec 8 → BitVec 8, GetPut g (writeZext 8 (wid := 8)) :=
  ⟨by decide, ⟨getLane ⟨0, 8⟩, writeZext_getPut_full⟩⟩

/-- Non-vacuity of `putLane_veryWellBehaved_of_fits` and `putLane_putGet_of_fits`: the `ah` lane
fits in 64 bits. -/
theorem nonvacuity_putLane_veryWellBehaved : laneHigh8.Fits 64 := by decide

/-- Non-vacuity of `putLane_comm_of_disjoint` / `getLane_putLane_of_disjoint`. -/
theorem nonvacuity_putLane_comm : laneLow8.Disjoint laneHigh8 := by decide

/-- Non-vacuity of `putLane_comm_iff_disjoint_of_fits`, on both sides of the equivalence: `al` and
`ah` fit and are disjoint; `al` and `ax` fit and are not disjoint. -/
theorem nonvacuity_putLane_comm_iff :
    (laneLow8.Fits 64 ∨ laneHigh8.Fits 64) ∧ laneLow8.Disjoint laneHigh8 ∧
    (laneLow8.Fits 64 ∨ laneLow16.Fits 64) ∧ ¬ laneLow8.Disjoint laneLow16 := by decide

/-- Instances of `putLane_comm_iff_disjointIn` on both sides: `al`/`ah` (disjoint inside 64 bits)
and `al`/`ax` (not disjoint). -/
theorem nonvacuity_putLane_comm_iff_disjointIn :
    laneLow8.DisjointIn 64 laneHigh8 ∧ ¬ laneLow8.DisjointIn 64 laneLow16 := by decide

/-- Non-vacuity of `writeZext_not_getPut_of_lt` and `writeZext_putGet_of_le`: `32 < 64`. -/
theorem nonvacuity_writeZext : (32 : Nat) < 64 ∧ (32 : Nat) ≤ 64 := by decide

/-- Non-vacuity of `writeZext_getPut_iff` on both sides: a word with zero upper half satisfies
GetPut, a word with a nonzero upper half does not. -/
theorem nonvacuity_writeZext_getPut_iff :
    writeZext 64 (getLane ⟨0, 32⟩ (0x00000000DEADBEEF#64)) (0x00000000DEADBEEF#64) =
      0x00000000DEADBEEF#64 ∧
    writeZext 64 (getLane ⟨0, 32⟩ (0x1122334455667788#64)) (0x1122334455667788#64) ≠
      0x1122334455667788#64 := by decide

end Toy.ParMove
