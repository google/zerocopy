/-!
# Multi-Target `rustc_abi` Layout Calculator, `#[repr]` Algebra, and `x86_win32` Packed-Align Soundness

Self-contained, kernel-checked Lean `v4.34.1` formalization (core `Init` only;
fully constructive, structurally total definitions, axiom-minimal).

Models and proves:
1. `TargetDataLayout` alignment laws (`alignTo`, `maxAlignedFactor`) and nine-target
   primitive/pair layouts (`x86_64`, `i686-linux`, `i686-msvc`, `wasm32`, `s390x`,
   `thumbv7m`, `aarch64-linux`, `aarch64-darwin`, `riscv64gc`).
2. `vectorTypeLayout` (`Fixed` vs. `PackedFixed` power-of-two cliff) and
   `maxAlignedFactor_dvd_size_and_pow2`.
3. `absentVariant` (`uninhabited && all1Zst`) and `#49298` non-1-ZST reservation.
4. Pinned-tail divisibility conservation (`alignTo_add_le_iff_of_dvd`) vs.
   `StructKind::MaybeUnsized` suppression of `NicheBias::End`.
5. Definition-site `checkPackedInner` vs. post-monomorphization `PackedAlignWf`
   and the `x86_win32` ABI invariant `abiAlign ≥ maxReprAlign`
   (`postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign`).
6. Four constructive sharpness counterexamples (`ce1`..`ce4`) plus array/tuple/alias
   `checkPackedInner` corollaries.
-/

namespace RustcAbiLayoutAndReprSoundness

/-! ## Section 1: Pure Constructive Alignment Arithmetic (`alignTo` & `maxAlignedFactor`) -/

/-- Round `offset` up to the next multiple of `align` (for `align > 0`; identity if `align = 0`).
Matches `Size::align_to` in `compiler/rustc_abi/src/lib.rs` for power-of-two alignments. -/
def alignTo (offset align : Nat) : Nat :=
  if align = 0 then offset else ((offset + (align - 1)) / align) * align

/-- Constructive predicate characterizing powers of two (`1, 2, 4, 8, ...`). -/
inductive IsPow2 : Nat → Prop where
  | one : IsPow2 1
  | double {k : Nat} : IsPow2 k → IsPow2 (2 * k)

theorem IsPow2.pos {k : Nat} (h : IsPow2 k) : 0 < k := by
  induction h with
  | one => exact Nat.zero_lt_one
  | double _ ih =>
    have h2 : 0 < 2 := Nat.succ_pos 1
    exact Nat.mul_pos h2 ih

theorem IsPow2.ne_zero {k : Nat} (h : IsPow2 k) : k ≠ 0 :=
  Nat.ne_of_gt h.pos

/-- Structural helper for `maxAlignedFactor`: extracts the largest power of two dividing `n`
within `fuel` halvings (exact whenever `n ≤ fuel`). -/
def maxAlignedFactorAux : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, n =>
    if n = 0 then 1
    else if n % 2 = 0 then 2 * maxAlignedFactorAux fuel (n / 2)
    else 1

/-- Exact power-of-two divisibility: `maxAlignedFactor n` is the largest power of two
dividing `n` (for `n > 0`; returns `1` for `n = 0`), modeling `Align::max_aligned_factor`
in `compiler/rustc_abi/src/lib.rs`. -/
def maxAlignedFactor (n : Nat) : Nat :=
  maxAlignedFactorAux n n

theorem alignTo_eq_mul {offset d : Nat} (hd : 0 < d) :
    alignTo offset d = ((offset + (d - 1)) / d) * d := by
  unfold alignTo
  have hne : d ≠ 0 := Nat.ne_of_gt hd
  simp [hne]

theorem dvd_alignTo (offset d : Nat) (hd : 0 < d) : d ∣ alignTo offset d := by
  rw [alignTo_eq_mul hd]
  exact Nat.dvd_mul_left d _

theorem le_alignTo (offset d : Nat) (hd : 0 < d) : offset ≤ alignTo offset d := by
  rw [alignTo_eq_mul hd]
  let m := offset + (d - 1)
  have hdiv : d * (m / d) + m % d = m := Nat.div_add_mod m d
  have hmod : m % d < d := Nat.mod_lt m hd
  have hmod_le : m % d ≤ d - 1 := Nat.le_sub_one_of_lt hmod
  have hsum : offset + (d - 1) ≤ (m / d) * d + (d - 1) := by
    have hstep : (m / d) * d + m % d ≤ (m / d) * d + (d - 1) :=
      Nat.add_le_add_left hmod_le ((m / d) * d)
    have hEq : (m / d) * d + m % d = offset + (d - 1) := by
      rw [Nat.mul_comm (m / d) d]
      exact hdiv
    rw [hEq] at hstep
    exact hstep
  exact Nat.le_of_add_le_add_right hsum

/-- Galois closure property of `alignTo`: for `d > 0`, `offset ≤ k * d ↔ alignTo offset d ≤ k * d`. -/
theorem alignTo_le_mul_iff {offset k d : Nat} (hd : 0 < d) :
    alignTo offset d ≤ k * d ↔ offset ≤ k * d := by
  constructor
  · intro h
    exact Nat.le_trans (le_alignTo offset d hd) h
  · intro h
    rw [alignTo_eq_mul hd]
    have h1 : offset + (d - 1) ≤ k * d + (d - 1) := Nat.add_le_add_right h (d - 1)
    have h2 : (offset + (d - 1)) / d ≤ (k * d + (d - 1)) / d := Nat.div_le_div_right h1
    have hlt : d - 1 < d := Nat.sub_lt hd Nat.zero_lt_one
    have hkd : (k * d + (d - 1)) / d = k := by
      rw [Nat.mul_comm k d, Nat.mul_add_div hd]
      rw [Nat.div_eq_of_lt hlt, Nat.add_zero]
    rw [hkd] at h2
    exact Nat.mul_le_mul_right d h2

/-- When `d ∣ n` and `0 < d`, `alignTo n d = n`. -/
theorem alignTo_of_dvd {n d : Nat} (hd : 0 < d) (hdvd : d ∣ n) : alignTo n d = n := by
  rcases hdvd with ⟨k, rfl⟩
  rw [Nat.mul_comm d k]
  have hle1 : alignTo (k * d) d ≤ k * d := (alignTo_le_mul_iff hd).mpr (Nat.le_refl (k * d))
  have hle2 : k * d ≤ alignTo (k * d) d := le_alignTo (k * d) d hd
  exact Nat.le_antisymm hle1 hle2

/-- **Theorem 1 (Pinned-Tail Size Conservation Theorem):**
If `d > 0`, `d ∣ sizeT`, and `d ∣ M`, then padding a prefix of size `P` to alignment `d`
before placing a pinned tail of size `sizeT` fits within `M` if and only if the unpadded sum
`P + sizeT` fits within `M`.

This explains why `StructKind::MaybeUnsized` tail pinning alone does not inflate `size_of`
whenever the sorted prefix is padding-free and the tail's size and target budget are multiples
of the tail's alignment `d`. -/
theorem alignTo_add_le_iff_of_dvd
    {P sizeT M d : Nat} (hd : 0 < d) (hT : d ∣ sizeT) (hM : d ∣ M) :
    alignTo P d + sizeT ≤ M ↔ P + sizeT ≤ M := by
  constructor
  · intro h
    exact Nat.le_trans (Nat.add_le_add_right (le_alignTo P d hd) sizeT) h
  · intro h
    rcases hT with ⟨s, hs⟩
    rcases hM with ⟨m, hm⟩
    rw [hs, hm] at h ⊢
    rw [Nat.mul_comm d s, Nat.mul_comm d m] at h ⊢
    have hs_le_m : s * d ≤ m * d := Nat.le_trans (Nat.le_add_left (s * d) P) h
    have hs_m : s ≤ m := Nat.le_of_mul_le_mul_right hs_le_m hd
    have hsplit : m = (m - s) + s := (Nat.sub_add_cancel hs_m).symm
    have hM_split : m * d = (m - s) * d + s * d := by
      calc
        m * d = ((m - s) + s) * d := by rw [← hsplit]
        _ = (m - s) * d + s * d := Nat.add_mul (m - s) s d
    rw [hM_split] at h ⊢
    have hP_le : P ≤ (m - s) * d := Nat.le_of_add_le_add_right h
    have hAlign_le : alignTo P d ≤ (m - s) * d := (alignTo_le_mul_iff hd).mpr hP_le
    exact Nat.add_le_add_right hAlign_le (s * d)

theorem maxAlignedFactorAux_isPow2 : ∀ fuel n : Nat, IsPow2 (maxAlignedFactorAux fuel n)
  | 0, _ => IsPow2.one
  | fuel + 1, n => by
    unfold maxAlignedFactorAux
    by_cases h0 : n = 0
    · simp [h0]
      exact IsPow2.one
    · simp [h0]
      by_cases h2 : n % 2 = 0
      · simp [h2]
        exact IsPow2.double (maxAlignedFactorAux_isPow2 fuel (n / 2))
      · simp [h2]
        exact IsPow2.one

/-- `maxAlignedFactor n` is always a power of two. -/
theorem maxAlignedFactor_isPow2 (n : Nat) : IsPow2 (maxAlignedFactor n) :=
  maxAlignedFactorAux_isPow2 n n

theorem maxAlignedFactorAux_dvd : ∀ fuel n : Nat, maxAlignedFactorAux fuel n ∣ n
  | 0, n => Nat.one_dvd n
  | fuel + 1, n => by
    unfold maxAlignedFactorAux
    by_cases h0 : n = 0
    · simp [h0]
    · simp [h0]
      by_cases h2 : n % 2 = 0
      · simp [h2]
        rcases maxAlignedFactorAux_dvd fuel (n / 2) with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have hdiv : 2 * (n / 2) = n := by
          have hdm := Nat.div_add_mod n 2
          rw [h2, Nat.add_zero] at hdm
          exact hdm
        exact Eq.trans hdiv.symm
          (Eq.trans (congrArg (2 * ·) hq) (Nat.mul_assoc 2 (maxAlignedFactorAux fuel (n / 2)) q).symm)
      · simp [h2]

/-- `maxAlignedFactor n` divides `n` for every `n : Nat`. -/
theorem maxAlignedFactor_dvd (n : Nat) : maxAlignedFactor n ∣ n :=
  maxAlignedFactorAux_dvd n n

theorem pow2_dvd_maxAlignedFactorAux {p : Nat} (hp : IsPow2 p) :
    ∀ {fuel n : Nat}, 0 < n → n ≤ fuel → p ∣ n → p ∣ maxAlignedFactorAux fuel n := by
  induction hp with
  | one =>
    intro fuel n _ _ _
    exact Nat.one_dvd _
  | double hp' ih =>
    rename_i k
    intro fuel n hn hle hdvd
    cases fuel with
    | zero =>
      exact False.elim (Nat.not_lt_zero 0 (Nat.lt_of_lt_of_le hn hle))
    | succ fuel' =>
      have hne : n ≠ 0 := Nat.ne_of_gt hn
      rcases hdvd with ⟨q, hq⟩
      have hn_even : n % 2 = 0 := by
        have h2dvd : 2 ∣ n := ⟨k * q, by rw [hq, Nat.mul_assoc]⟩
        exact Nat.mod_eq_zero_of_dvd h2dvd
      have hhalf_eq : n / 2 = k * q := by
        rw [hq, Nat.mul_assoc]
        exact Nat.mul_div_right (k * q) (Nat.succ_pos 1)
      have hhalf_pos : 0 < n / 2 := by
        by_cases hz : n / 2 = 0
        · have hdm := Nat.div_add_mod n 2
          rw [hz, hn_even, Nat.mul_zero, Nat.add_zero] at hdm
          exact False.elim (hne hdm.symm)
        · exact Nat.pos_of_ne_zero hz
      have hhalf_lt : n / 2 < n := Nat.div_lt_self hn (Nat.le_refl 2)
      have hhalf_le : n / 2 ≤ fuel' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hhalf_lt hle)
      have ih_res : k ∣ maxAlignedFactorAux fuel' (n / 2) :=
        ih hhalf_pos hhalf_le ⟨q, hhalf_eq⟩
      unfold maxAlignedFactorAux
      simp [hne, hn_even]
      rcases ih_res with ⟨r, hr⟩
      exact ⟨r, by rw [hr, Nat.mul_assoc]⟩

/-- Maximality: every power of two dividing a nonzero `n` divides `maxAlignedFactor n`. -/
theorem pow2_dvd_maxAlignedFactor {p n : Nat} (hn : 0 < n) (hp : IsPow2 p) (hdvd : p ∣ n) :
    p ∣ maxAlignedFactor n :=
  pow2_dvd_maxAlignedFactorAux hp hn (Nat.le_refl n) hdvd

/-- **Theorem 3 (`#[repr(simd, packed)]` Alignment Divisor Soundness):**
For any positive raw vector byte size `size > 0`, `maxAlignedFactor size` is a power of two,
divides `size`, dominates every power-of-two divisor of `size`, and preserves `size`
unchanged under `alignTo` (zero tail padding). -/
theorem maxAlignedFactor_dvd_size_and_pow2 {size : Nat} (hpos : 0 < size) :
    IsPow2 (maxAlignedFactor size) ∧
    maxAlignedFactor size ∣ size ∧
    (∀ p, IsPow2 p → p ∣ size → p ∣ maxAlignedFactor size) ∧
    alignTo size (maxAlignedFactor size) = size := by
  have hpow := maxAlignedFactor_isPow2 size
  have hdvd := maxAlignedFactor_dvd size
  refine ⟨hpow, hdvd, ?_, alignTo_of_dvd hpow.pos hdvd⟩
  intro p hp hps
  exact pow2_dvd_maxAlignedFactor hpos hp hps

/-! ## Section 2: Nine-Target `TargetDataLayout` Matrix Model -/

structure TargetDataLayout where
  ptrSize : Nat
  ptrAlign : Nat
  i64Align : Nat
  f64Align : Nat
  i128Align : Nat
  aggregateAlign : Nat
  deriving DecidableEq, Repr

def dlX86_64Linux : TargetDataLayout := ⟨8, 8, 8, 8, 16, 1⟩
def dlI686Linux : TargetDataLayout := ⟨4, 4, 4, 4, 16, 1⟩
def dlI686WinMsvc : TargetDataLayout := ⟨4, 4, 8, 8, 16, 1⟩
def dlWasm32 : TargetDataLayout := ⟨4, 4, 8, 8, 16, 1⟩
def dlS390xLinux : TargetDataLayout := ⟨8, 8, 8, 8, 8, 1⟩
def dlThumbv7m : TargetDataLayout := ⟨4, 4, 8, 8, 8, 1⟩
def dlAarch64Linux : TargetDataLayout := ⟨8, 8, 8, 8, 16, 1⟩
def dlAarch64Darwin : TargetDataLayout := ⟨8, 8, 8, 8, 16, 1⟩
def dlRiscv64gc : TargetDataLayout := ⟨8, 8, 8, 8, 16, 1⟩

structure PairLayout where
  size : Nat
  align : Nat
  secondOffset : Nat
  deriving DecidableEq, Repr

/-- `#[repr(C)]` two-field struct layout `(f0, f1)` preserving declaration order. -/
def reprCPairLayout (s0 a0 s1 a1 : Nat) : PairLayout :=
  let off1 := alignTo s0 a1
  let align := max a0 a1
  let size := alignTo (off1 + s1) align
  ⟨size, align, off1⟩

/-- `#[repr(Rust)]` two-field struct layout placing the higher-aligned field first. -/
def reprRustPairLayout (s0 a0 s1 a1 : Nat) : PairLayout :=
  if a0 ≥ a1 then reprCPairLayout s0 a0 s1 a1
  else reprCPairLayout s1 a1 s0 a0

theorem nine_target_alignment_laws :
    reprCPairLayout 1 1 8 dlI686Linux.i64Align = ⟨12, 4, 4⟩ ∧
    reprRustPairLayout 1 1 8 dlI686Linux.i64Align = ⟨12, 4, 8⟩ ∧
    reprCPairLayout 1 1 8 dlI686WinMsvc.i64Align = ⟨16, 8, 8⟩ ∧
    reprCPairLayout 1 1 8 dlWasm32.i64Align = ⟨16, 8, 8⟩ ∧
    reprCPairLayout 1 1 16 dlS390xLinux.i128Align = ⟨24, 8, 8⟩ ∧
    reprRustPairLayout 1 1 16 dlS390xLinux.i128Align = ⟨24, 8, 16⟩ ∧
    reprCPairLayout 1 1 16 dlThumbv7m.i128Align = ⟨24, 8, 8⟩ ∧
    reprCPairLayout 1 1 16 dlX86_64Linux.i128Align = ⟨32, 16, 16⟩ ∧
    reprCPairLayout 1 1 16 dlAarch64Linux.i128Align = ⟨32, 16, 16⟩ ∧
    reprCPairLayout 1 1 16 dlAarch64Darwin.i128Align = ⟨32, 16, 16⟩ ∧
    reprCPairLayout 1 1 16 dlRiscv64gc.i128Align = ⟨32, 16, 16⟩ := by
  decide

/-! ## Section 3: `#[repr(simd)]` vs. `#[repr(simd, packed)]` Power-of-Two Cliff -/

inductive SimdVectorKind where
  | fixed
  | packedFixed
  deriving DecidableEq, Repr

inductive SimpleBackendRepr where
  | scalar
  | scalarPair
  | simdVector
  | memory
  deriving DecidableEq, Repr

structure SimdLayout where
  size : Nat
  align : Nat
  backendRepr : SimpleBackendRepr
  deriving DecidableEq, Repr

/-- Structural helper for `isPowerOfTwoBool` so `decide` reduces definitionally. -/
def isPowerOfTwoBoolAux : Nat → Nat → Bool
  | 0, n => n == 1
  | fuel + 1, n =>
    if n == 0 then false
    else if n == 1 then true
    else if n % 2 == 0 then isPowerOfTwoBoolAux fuel (n / 2)
    else false

/-- Boolean power-of-two test on `Nat` (positive numbers with no odd factor > 1). -/
def isPowerOfTwoBool (n : Nat) : Bool :=
  isPowerOfTwoBoolAux n n

/-- Smallest power of two `≥ n` (for `n ≥ 1`, returns `1` for `n = 0`). -/
def nextPowerOfTwoAux (fuel cur target : Nat) : Nat :=
  match fuel with
  | 0 => cur
  | fuel' + 1 =>
    if cur ≥ target then cur
    else nextPowerOfTwoAux fuel' (2 * cur) target

def nextPowerOfTwo (n : Nat) : Nat :=
  nextPowerOfTwoAux n 1 n

/-- Models `vector_type_layout` in `compiler/rustc_abi/src/layout.rs:979-1035`
for default `rust_vector_align` (`nextPowerOfTwo size`). -/
def vectorTypeLayout (kind : SimdVectorKind) (elemSize count : Nat) : SimdLayout :=
  let rawSize := elemSize * count
  match kind with
  | .packedFixed =>
    if !isPowerOfTwoBool count then
      let a := maxAlignedFactor rawSize
      ⟨alignTo rawSize a, a, .memory⟩
    else
      let a := nextPowerOfTwo rawSize
      ⟨alignTo rawSize a, a, .simdVector⟩
  | .fixed =>
    let a := nextPowerOfTwo rawSize
    ⟨alignTo rawSize a, a, .simdVector⟩

/-- For non-power-of-two `#[repr(simd, packed)]` vectors of positive byte size,
`vectorTypeLayout` demotes `backendRepr` to `.memory`, assigns `align = maxAlignedFactor rawSize`,
and preserves `size = rawSize` with zero tail padding. -/
theorem vectorTypeLayout_packed_nonpow2_sound
    {elemSize count : Nat}
    (hpos : 0 < elemSize * count)
    (hnp : isPowerOfTwoBool count = false) :
    let ly := vectorTypeLayout .packedFixed elemSize count
    ly.backendRepr = .memory ∧
    ly.align = maxAlignedFactor (elemSize * count) ∧
    IsPow2 ly.align ∧
    ly.align ∣ (elemSize * count) ∧
    ly.size = elemSize * count := by
  have hspec := maxAlignedFactor_dvd_size_and_pow2 hpos
  simp [vectorTypeLayout, hnp, hspec.1, hspec.2.1, hspec.2.2.2]

/-- **Counterexample 2 (`ce2_simd_packed_pow2_ignores_pack_vs_nonpow2_demotes_memory`):**
Power-of-two `SimdPackedF32x4` ignores `packed` completely (`16 B, align 16, SimdVector`),
matching unpacked `SimdF32x4`, whereas non-power-of-two `SimdPackedF32x3`, `SimdPackedF32x6`,
and `SimdPackedU8x3` strip tail padding, align to `maxAlignedFactor(size)`, and demote
to `Memory`. -/
theorem ce2_simd_packed_pow2_ignores_pack_vs_nonpow2_demotes_memory :
    vectorTypeLayout .packedFixed 4 4 = vectorTypeLayout .fixed 4 4 ∧
    vectorTypeLayout .packedFixed 4 4 = ⟨16, 16, .simdVector⟩ ∧
    vectorTypeLayout .fixed 4 3 = ⟨16, 16, .simdVector⟩ ∧
    vectorTypeLayout .packedFixed 4 3 = ⟨12, 4, .memory⟩ ∧
    vectorTypeLayout .fixed 4 6 = ⟨32, 32, .simdVector⟩ ∧
    vectorTypeLayout .packedFixed 4 6 = ⟨24, 8, .memory⟩ ∧
    vectorTypeLayout .packedFixed 1 3 = ⟨3, 1, .memory⟩ := by
  decide

/-! ## Section 4: `StructKind::MaybeUnsized` and `NicheBias::End` Suppression -/

inductive StructKind where
  | alwaysSized
  | maybeUnsized
  deriving DecidableEq, Repr

inductive NicheBias where
  | startBias
  | endBias
  deriving DecidableEq, Repr

structure FieldSpec where
  size : Nat
  align : Nat
  nicheAvail : Nat
  nicheSize : Nat
  deriving DecidableEq, Repr

structure NicheInfo where
  offset : Nat
  size : Nat
  avail : Nat
  deriving DecidableEq, Repr

structure StructLayout where
  size : Nat
  align : Nat
  offsets : List Nat
  niche : Option NicheInfo
  deriving DecidableEq, Repr

/-- Lay out an already-ordered sequence of fields linearly from offset `0`. -/
def layoutOrderedFieldsAux
    (bias : NicheBias) (offset maxAlign : Nat) (bestNiche : Option NicheInfo)
    : List FieldSpec → (Nat × Nat × List Nat × Option NicheInfo)
  | [] => (offset, maxAlign, [], bestNiche)
  | f :: rest =>
    let off := alignTo offset f.align
    let maxAlign' := max maxAlign f.align
    let bestNiche' :=
      if f.nicheAvail > 0 then
        match bestNiche with
        | none => some ⟨off, f.nicheSize, f.nicheAvail⟩
        | some cur =>
          let prefer : Bool :=
            match bias with
            | .startBias => decide (f.nicheAvail > cur.avail)
            | .endBias => decide (f.nicheAvail ≥ cur.avail)
          if prefer then some ⟨off, f.nicheSize, f.nicheAvail⟩ else some cur
      else
        bestNiche
    let (endOff, finalAlign, restOffs, finalNiche) :=
      layoutOrderedFieldsAux bias (off + f.size) maxAlign' bestNiche' rest
    (endOff, finalAlign, off :: restOffs, finalNiche)

/-- Compare two fields for descending-alignment + niche-bias sorting, matching
`layout_of_univariant_biased` in `compiler/rustc_abi/src/layout.rs:693-731`. -/
def fieldBefore (bias : NicheBias) (a b : FieldSpec) : Bool :=
  if a.align != b.align then
    a.align > b.align
  else
    match bias with
    | .startBias => a.nicheAvail > b.nicheAvail
    | .endBias => a.nicheAvail < b.nicheAvail

def insertField (bias : NicheBias) (x : FieldSpec) : List FieldSpec → List FieldSpec
  | [] => [x]
  | y :: ys =>
    if fieldBefore bias x y then x :: y :: ys
    else y :: insertField bias x ys

def sortFields (bias : NicheBias) : List FieldSpec → List FieldSpec
  | [] => []
  | x :: xs => insertField bias x (sortFields bias xs)

def splitInitLast : List FieldSpec → List FieldSpec × Option FieldSpec
  | [] => ([], none)
  | [x] => ([], some x)
  | x :: xs =>
    let (init, last) := splitInitLast xs
    (x :: init, last)

def univariantBiased (fields : List FieldSpec) (kind : StructKind) (bias : NicheBias) :
    StructLayout :=
  let ordered :=
    match kind with
    | .alwaysSized => sortFields bias fields
    | .maybeUnsized =>
      let (prefixFields, lastOpt) := splitInitLast fields
      match lastOpt with
      | none => []
      | some tail => sortFields bias prefixFields ++ [tail]
  let (endOff, maxAlign, offs, niche) := layoutOrderedFieldsAux bias 0 1 none ordered
  ⟨alignTo endOff maxAlign, maxAlign, offs, niche⟩

/-- Models `layout_of_univariant` (`compiler/rustc_abi/src/layout.rs:274-342`):
runs `NicheBias::Start` first, and only retries `NicheBias::End` when
`kind ≠ StructKind::MaybeUnsized` and the niche is strictly interior. -/
def univariantLayout (fields : List FieldSpec) (kind : StructKind) : StructLayout :=
  let startLy := univariantBiased fields kind .startBias
  match kind, startLy.niche with
  | .alwaysSized, some n =>
    let headSpace := n.offset
    let tailSpace := startLy.size - headSpace - n.size
    if fields.length > 1 && headSpace ≠ 0 && tailSpace > 0 then
      let endLy := univariantBiased fields kind .endBias
      match endLy.niche with
      | some altN =>
        let altHead := altN.offset
        if altHead > headSpace && altHead > tailSpace then endLy else startLy
      | none => startLy
    else
      startLy
  | _, _ => startLy

/-- Models `try_fit_variants_around_niche_tag` + tagged fallback in
`compiler/rustc_abi/src/layout/enum_layout.rs:480-520` for a 2-variant enum
`{ A(mainStruct), B(otherSize, otherAlign) }`. -/
def twoVariantEnumSize (main : StructLayout) (otherSize otherAlign : Nat) : Nat :=
  let totalAlign := max main.align otherAlign
  let nichePackedSize := alignTo main.size totalAlign
  let fitsNiche :=
    match main.niche with
    | none => false
    | some n =>
      if otherSize ≤ n.offset then
        true
      else
        let afterOff := alignTo (n.offset + n.size) otherAlign
        afterOff + otherSize ≤ nichePackedSize
  if fitsNiche then
    nichePackedSize
  else
    -- Tagged fallback: 1-byte discriminant + aligned payload
    let aSize := alignTo (alignTo 1 main.align + main.size) totalAlign
    let bSize := alignTo (alignTo 1 otherAlign + otherSize) totalAlign
    max aSize bSize

def fU32 : FieldSpec := ⟨4, 4, 0, 0⟩
def fBool : FieldSpec := ⟨1, 1, 254, 1⟩
def fU8 : FieldSpec := ⟨1, 1, 0, 0⟩
def fUnit : FieldSpec := ⟨0, 1, 0, 0⟩

/-- **Counterexample 3 (`ce3_maybe_unsized_suppresses_niche_bias_end_inflating_enum_8_to_12`):**
On the exact same field list `[u32, bool, u8, ()]`, `StructKind::AlwaysSized` invokes
`NicheBias::End` to move `bool` to offset `5` (allowing `[u8; 5]` to pack into an `8`-byte
enum), whereas `StructKind::MaybeUnsized` suppresses `NicheBias::End` (keeping `bool` at
offset `4`), inflating the outer enum from `8` bytes to `12` bytes even though the tail
`()` is a 0-byte ZST. The same `8 -> 12` inflation holds for `FixedEdge(u32, u8, bool)` vs.
`MaybeDstEdge<u8>(u32, bool, u8)`. -/
theorem ce3_maybe_unsized_suppresses_niche_bias_end_inflating_enum_8_to_12 :
    let sameFields := [fU32, fBool, fU8, fUnit]
    let fixedPure := univariantLayout sameFields .alwaysSized
    let maybePure := univariantLayout sameFields .maybeUnsized
    let fixedEdge := univariantLayout [fU32, fU8, fBool] .alwaysSized
    let maybeEdge := univariantLayout [fU32, fBool, fU8] .maybeUnsized
    fixedPure.size = 8 ∧
    maybePure.size = 8 ∧
    fixedPure.niche = some ⟨5, 1, 254⟩ ∧
    maybePure.niche = some ⟨4, 1, 254⟩ ∧
    twoVariantEnumSize fixedPure 5 1 = 8 ∧
    twoVariantEnumSize maybePure 5 1 = 12 ∧
    twoVariantEnumSize fixedEdge 5 1 = 8 ∧
    twoVariantEnumSize maybeEdge 5 1 = 12 := by
  decide

/-! ## Section 5: Uninhabited Non-1-ZST Variant Reservation (`absent`, `#49298`) -/

structure VariantField where
  size : Nat
  align : Nat
  uninhabited : Bool
  deriving DecidableEq, Repr

def is1Zst (f : VariantField) : Bool :=
  f.size == 0 && f.align == 1

/-- Models `absent` in `compiler/rustc_abi/src/layout.rs:91-102`:
a variant is absent iff it has at least one uninhabited field AND every field is a 1-ZST. -/
def absentVariant (fields : List VariantField) : Bool :=
  fields.any (·.uninhabited) && fields.all is1Zst

def variantSizeAlignAux (offset maxAlign : Nat) : List VariantField → Nat × Nat
  | [] => (alignTo offset maxAlign, maxAlign)
  | f :: rest =>
    let off := alignTo offset f.align
    variantSizeAlignAux (off + f.size) (max maxAlign f.align) rest

def variantSizeAlign (fields : List VariantField) : Nat × Nat :=
  variantSizeAlignAux 0 1 fields

/-- Simplified two-variant enum size & alignment model covering:
- `repr(Rust)` single-present collapse when variant 1 is `absentVariant`,
- `repr(C)` tag-plus-union (`c_int = 4 B`, align `4`) inhibiting `absent`,
- `repr(Rust)` retention of non-absent uninhabited variants (`#49298`) reserving
  payload space and alignment (`align = max a0 a1`, tagged if `v1` is non-absent). -/
def twoVariantAbsentEnumLayout
    (reprC : Bool) (v0 v1 : List VariantField) : Nat × Nat :=
  let (s0, a0) := variantSizeAlign v0
  let (s1, a1) := variantSizeAlign v1
  if reprC then
    let payloadAlign := max a0 a1
    let tagAlign := max 4 payloadAlign
    let payloadSize := max s0 s1
    let total := alignTo (alignTo 4 payloadAlign + payloadSize) tagAlign
    (total, tagAlign)
  else if absentVariant v1 then
    (s0, a0)
  else
    let totalAlign := max a0 a1
    -- For `Live(u8)` + `Dead(Never, payload)`: `v1` is uninhabited so no tag value is
    -- needed to distinguish it from `v0` unless `v0` + `v1` force tagged layout when no
    -- niche exists; `rustc` computes `max(v0_prefixed, v1_prefixed)` aligned to `totalAlign`.
    let v0Pref := alignTo (alignTo 1 a0 + s0) totalAlign
    let v1Pref := alignTo (alignTo 1 a1 + s1) totalAlign
    (max v0Pref v1Pref, totalAlign)

/-- **Counterexample 4 (`ce4_uninhabited_align16_zst_variant_forces_size_16_align_16`):**
1. `Dead1Zst` (`Live(u8), Dead(Never)`): `absentVariant = true`, collapses to `(1, 1)`.
2. `ReprCDead1Zst` (`#[repr(C)] Live(u8), Dead(Never)`): `repr(C)` inhibits `absent`, giving `(8, 4)`.
3. `DeadPayload64` (`Live(u8), Dead(Never, [u8; 64])`): `absentVariant = false`, reserves `(65, 1)`.
4. `DeadAlign16Zst` (`Live(u8), Dead(Never, Align16Zst)`): `Align16Zst` has `align = 16 ≠ 1`,
   so `absentVariant = false`, forcing `(16, 16)`. -/
theorem ce4_uninhabited_align16_zst_variant_forces_size_16_align_16 :
    let fU8v : VariantField := ⟨1, 1, false⟩
    let fNever : VariantField := ⟨0, 1, true⟩
    let fArr64 : VariantField := ⟨64, 1, false⟩
    let fAlign16 : VariantField := ⟨0, 16, false⟩
    absentVariant [fNever] = true ∧
    absentVariant [fNever, fArr64] = false ∧
    absentVariant [fNever, fAlign16] = false ∧
    twoVariantAbsentEnumLayout false [fU8v] [fNever] = (1, 1) ∧
    twoVariantAbsentEnumLayout true [fU8v] [fNever] = (8, 4) ∧
    twoVariantAbsentEnumLayout false [fU8v] [fNever, fArr64] = (65, 1) ∧
    twoVariantAbsentEnumLayout false [fU8v] [fNever, fAlign16] = (16, 16) := by
  decide

/-! ## Section 6: Definition-Site `checkPackedInner` Unsoundness vs. Post-Monomorphization
`PackedAlignWf` and the `x86_win32` ABI Invariant -/

/-- HIR-level (pre-monomorphization) field type syntax capturing the exact gap in
`compiler/rustc_hir_analysis/src/check/check.rs:check_packed_inner`. -/
inductive HirTy where
  | prim (size align : Nat)
  | param
  | alias (target : HirTy)
  | tuple (elems : List HirTy)
  | array (elem : HirTy) (len : Nat)
  | adt (pack : Option Nat) (reprAlign : Option Nat) (fields : List HirTy)
  deriving Repr

/-- Monomorphized type tree (no remaining `param` or unnormalized `alias`). -/
inductive MonoTy where
  | prim (size align : Nat)
  | tuple (elems : List MonoTy)
  | array (elem : MonoTy) (len : Nat)
  | adt (pack : Option Nat) (reprAlign : Option Nat) (fields : List MonoTy)
  deriving Repr

/-- Instantiate `HirTy.param` with `arg` and normalize `HirTy.alias`. -/
def instantiateHir (arg : MonoTy) : HirTy → MonoTy
  | .prim s a => .prim s a
  | .param => arg
  | .alias t => instantiateHir arg t
  | .tuple elems => .tuple (instantiateList arg elems)
  | .array e n => .array (instantiateHir arg e) n
  | .adt p r fields => .adt p r (instantiateList arg fields)
where
  instantiateList (arg : MonoTy) : List HirTy → List MonoTy
    | [] => []
    | x :: xs => instantiateHir arg x :: instantiateList arg xs

/-- Models `check_packed_inner` in `compiler/rustc_hir_analysis/src/check/check.rs:1697-1723`
(and `1756-1782` at HEAD): checks ONLY direct `HirTy.adt` fields at definition time,
failing to recurse into `param`, `alias`, `tuple`, or `array`. Returns `true` iff it detects
a nested `#[repr(align)]` ADT. -/
def checkPackedInnerDef : HirTy → Bool
  | .adt _ reprAlign fields =>
    if reprAlign.isSome then true
    else checkFieldsDef fields
  | _ => false
where
  checkFieldsDef : List HirTy → Bool
    | [] => false
    | f :: rest =>
      (match f with
       | .adt _ _ _ => checkPackedInnerDef f
       | _ => false) || checkFieldsDef rest

/-- Top-level definition-site `check_packed` acceptance predicate (no E0587 and
`checkPackedInnerDef` returns `false`). -/
def checkPackedDefPasses : HirTy → Bool
  | .adt (some _) (some _) _ => false
  | .adt (some _) none fields => !checkPackedInnerDef (.adt (some 1) none fields)
  | _ => true

/-- Optional maximum on `Option Nat`, matching `Option<Align>::max` in `rustc_abi`. -/
def optMax : Option Nat → Option Nat → Option Nat
  | none, y => y
  | x, none => x
  | some a, some b => some (max a b)

/-- Minimal layout summary tracking `abiAlign` and `maxReprAlign`. -/
structure MonoAlignLayout where
  abiAlign : Nat
  maxReprAlign : Option Nat
  deriving DecidableEq, Repr

/-- Models `rustc_abi/src/layout.rs` alignment & `max_repr_align` propagation:
- `layout_of_array_like` (line 200) resets `max_repr_align: None`.
- `layout_of_univariant_biased` (lines 780-784, 811-813) clamps `field_align` by `pack`,
  applies `repr.align`, and unconditionally propagates `max_repr_align = max_repr_align.max(field.max_repr_align)`. -/
def computeMonoLayout : MonoTy → MonoAlignLayout
  | .prim _ a => ⟨a, none⟩
  | .array e _ =>
    let el := computeMonoLayout e
    ⟨el.abiAlign, none⟩
  | .tuple elems =>
    let (a, mra) := foldFields none elems
    ⟨a, mra⟩
  | .adt pack reprAlign fields =>
    let (fieldAbi, fieldMra) := foldFields pack fields
    let abi :=
      match reprAlign with
      | some ra => max fieldAbi ra
      | none => fieldAbi
    ⟨abi, optMax reprAlign fieldMra⟩
where
  foldFields (pack : Option Nat) : List MonoTy → Nat × Option Nat
    | [] => (1, none)
    | f :: rest =>
      let fl := computeMonoLayout f
      let fa := match pack with | some p => min fl.abiAlign p | none => fl.abiAlign
      let (ra, rmra) := foldFields pack rest
      (max fa ra, optMax fl.maxReprAlign rmra)

/-- The exact assertion enforced in `compiler/rustc_target/src/callconv/x86_win32.rs`
(lines 69-73 in `1.98.0-nightly`, 73-77 in `1.99.1`/`1.102.0-nightly`, 82-86 at HEAD):
whenever `max_repr_align = some m` with `m > 4`, `abiAlign ≥ m` must hold. -/
def x86Win32AbiInvariant (ly : MonoAlignLayout) : Prop :=
  ∀ m, ly.maxReprAlign = some m → m > 4 → ly.abiAlign ≥ m

/-- Stronger invariant: `abiAlign` dominates `maxReprAlign` for ALL `m` (not just `m > 4`). -/
def abiAlignDominatesMaxRepr (ly : MonoAlignLayout) : Prop :=
  ∀ m, ly.maxReprAlign = some m → m ≤ ly.abiAlign

/-- Post-monomorphization predicate: `ty` contains no `#[repr(align)]` attribute anywhere
along a `max_repr_align`-propagating path (i.e., outside arrays). -/
def hasNoReprAlign : MonoTy → Prop
  | .prim _ _ => True
  | .array _ _ => True
  | .tuple elems => hasNoReprAlignList elems
  | .adt _ reprAlign fields => reprAlign = none ∧ hasNoReprAlignList fields
where
  hasNoReprAlignList : List MonoTy → Prop
    | [] => True
    | x :: xs => hasNoReprAlign x ∧ hasNoReprAlignList xs

/-- Post-monomorphization well-formedness (`PackedAlignWf`):
every packed ADT has `reprAlign = none` AND every field of a packed ADT satisfies
`hasNoReprAlign`, recursively throughout the monomorphized type tree. -/
def PackedAlignWf : MonoTy → Prop
  | .prim _ _ => True
  | .array e _ => PackedAlignWf e
  | .tuple elems => PackedAlignWfList elems
  | .adt pack reprAlign fields =>
    (pack.isSome → reprAlign = none ∧ hasNoReprAlign.hasNoReprAlignList fields) ∧
    PackedAlignWfList fields
where
  PackedAlignWfList : List MonoTy → Prop
    | [] => True
    | x :: xs => PackedAlignWf x ∧ PackedAlignWfList xs

theorem optMax_none_left (y : Option Nat) : optMax none y = y := by
  cases y <;> rfl

theorem optMax_eq_some_elim {a b : Option Nat} {m : Nat} (h : optMax a b = some m) :
    (a = some m ∧ b = none) ∨
    (a = none ∧ b = some m) ∨
    (∃ x y, a = some x ∧ b = some y ∧ max x y = m) := by
  cases a with
  | none =>
    cases b with
    | none => cases h
    | some y =>
      injection h with hy
      subst hy
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | some x =>
    cases b with
    | none =>
      injection h with hx
      subst hx
      exact Or.inl ⟨rfl, rfl⟩
    | some y =>
      injection h with hxy
      exact Or.inr (Or.inr ⟨x, y, rfl, rfl, hxy⟩)

theorem max_le_of_le_of_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  exact Nat.max_le.mpr ⟨ha, hb⟩

/-- Auxiliary lemma: `hasNoReprAlign ty` implies `(computeMonoLayout ty).maxReprAlign = none`. -/
theorem computeMonoLayout_maxReprAlign_none_of_hasNoReprAlign :
    ∀ ty : MonoTy, hasNoReprAlign ty → (computeMonoLayout ty).maxReprAlign = none
  | .prim _ _, _ => rfl
  | .array _ _, _ => rfl
  | .tuple elems, h => foldFields_mra_none none elems h
  | .adt pack reprAlign fields, ⟨hRa, hFields⟩ => by
    have hfm := foldFields_mra_none pack fields hFields
    simp [computeMonoLayout, hRa, hfm, optMax_none_left]
where
  foldFields_mra_none (pack : Option Nat) :
      ∀ fs : List MonoTy, hasNoReprAlign.hasNoReprAlignList fs →
        (computeMonoLayout.foldFields pack fs).2 = none
    | [], _ => rfl
    | f :: rest, ⟨hf, hrest⟩ => by
      have h1 := computeMonoLayout_maxReprAlign_none_of_hasNoReprAlign f hf
      have h2 := foldFields_mra_none pack rest hrest
      simp [computeMonoLayout.foldFields, h1, h2, optMax_none_left]

/-- Core inductive soundness theorem: under post-monomorphization `PackedAlignWf`,
every monomorphized type satisfies `abiAlignDominatesMaxRepr`. -/
theorem postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign_all :
    ∀ ty : MonoTy, PackedAlignWf ty → abiAlignDominatesMaxRepr (computeMonoLayout ty)
  | .prim _ _, _ => by
    intro m hm
    cases hm
  | .array _ _, _ => by
    intro m hm
    cases hm
  | .tuple elems, hWf => by
    intro m hm
    exact foldFields_none_dominates elems hWf m hm
  | .adt pack reprAlign fields, ⟨hPack, hFieldsWf⟩ => by
    cases pack with
    | some p =>
      have ⟨hRa, hNoAlign⟩ := hPack rfl
      have hfm := computeMonoLayout_maxReprAlign_none_of_hasNoReprAlign.foldFields_mra_none
        (some p) fields hNoAlign
      intro m hm
      simp [computeMonoLayout, hRa, hfm, optMax_none_left] at hm
    | none =>
      intro m hm
      simp only [computeMonoLayout] at hm ⊢
      rcases optMax_eq_some_elim hm with ⟨hRa, _⟩ | ⟨_, hFm⟩ | ⟨ra, fm, hRa, hFm, hEq⟩
      · subst hRa
        exact Nat.le_max_right _ _
      · have hDom := foldFields_none_dominates fields hFieldsWf m hFm
        cases reprAlign with
        | none => exact hDom
        | some ra => exact Nat.le_trans hDom (Nat.le_max_left _ ra)
      · subst hRa
        have hDom := foldFields_none_dominates fields hFieldsWf fm hFm
        rw [← hEq]
        exact max_le_of_le_of_le (Nat.le_max_right _ ra) (Nat.le_trans hDom (Nat.le_max_left _ ra))
where
  foldFields_none_dominates :
      ∀ fs : List MonoTy, PackedAlignWf.PackedAlignWfList fs →
        ∀ m, (computeMonoLayout.foldFields none fs).2 = some m →
          m ≤ (computeMonoLayout.foldFields none fs).1
    | [], _, _, hm => by cases hm
    | f :: rest, ⟨hfWf, hrestWf⟩, m, hm => by
      simp only [computeMonoLayout.foldFields] at hm ⊢
      rcases optMax_eq_some_elim hm with ⟨hF, _⟩ | ⟨_, hR⟩ | ⟨x, y, hF, hR, hEq⟩
      · have h1 := postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign_all f hfWf m hF
        exact Nat.le_trans h1 (Nat.le_max_left _ _)
      · have h2 := foldFields_none_dominates rest hrestWf m hR
        exact Nat.le_trans h2 (Nat.le_max_right _ _)
      · have h1 := postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign_all f hfWf x hF
        have h2 := foldFields_none_dominates rest hrestWf y hR
        rw [← hEq]
        exact max_le_of_le_of_le
          (Nat.le_trans h1 (Nat.le_max_left _ _))
          (Nat.le_trans h2 (Nat.le_max_right _ _))

/-- **Theorem 2 (`postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign`):**
Post-monomorphization `PackedAlignWf` unconditionally guarantees the `x86_win32.rs`
calling-convention assertion (`max_repr_align = some m ∧ m > 4 → abiAlign ≥ m`),
precluding the `rc = 101` ICE. -/
theorem postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign
    {ty : MonoTy} (hWf : PackedAlignWf ty) :
    x86Win32AbiInvariant (computeMonoLayout ty) := by
  intro m hm _hgt4
  exact postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign_all ty hWf m hm

/-! ### Constructive Counterexample 1 & Non-`ty::Adt` Bypass Corollaries -/

def hirInnerAlign8 : HirTy := .adt none (some 8) [.prim 4 4]
def monoInnerAlign8 : MonoTy := .adt none (some 8) [.prim 4 4]

def hirGenericPacked : HirTy := .adt (some 1) none [.param]
def hirTuplePacked : HirTy := .adt (some 1) none [.tuple [hirInnerAlign8]]
def hirAliasPacked : HirTy := .adt (some 1) none [.alias hirInnerAlign8]
def hirArrayPacked : HirTy := .adt (some 1) none [.array hirInnerAlign8 1]
def hirConcretePacked : HirTy := .adt (some 1) none [hirInnerAlign8]

/-- **Counterexample 1 (`ce1_generic_packed_bypasses_def_check_violates_win32_abi_inv`):**
`#[repr(C, packed)] struct GenericPacked<T>(T)` instantiated at
`#[repr(C, align(8))] struct Inner(u32)`:
1. Concrete `ConcretePacked(Inner)` is rejected at definition time (`checkPackedDefPasses = false`).
2. Generic `GenericPacked<T>(T)` PASSES definition-site `checkPackedDefPasses` (`= true`).
3. Instantiated `GenericPacked<Inner>` computes `abiAlign = 1`, `maxReprAlign = some 8`.
4. It VIOLATES `x86Win32AbiInvariant` (`¬ (1 ≥ 8)`), witnessing the live `x86_win32.rs` ICE. -/
theorem ce1_generic_packed_bypasses_def_check_violates_win32_abi_inv :
    checkPackedDefPasses hirConcretePacked = false ∧
    checkPackedDefPasses hirGenericPacked = true ∧
    computeMonoLayout (instantiateHir monoInnerAlign8 hirGenericPacked) = ⟨1, some 8⟩ ∧
    ¬ x86Win32AbiInvariant (computeMonoLayout (instantiateHir monoInnerAlign8 hirGenericPacked)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hInv
  have h1ge8 : 1 ≥ 8 := hInv 8 rfl (by decide)
  exact (by decide : ¬ (1 ≥ 8)) h1ge8

/-- Corollary: even WITHOUT generics, both `TuplePacked((Inner,))` and
`AliasPacked(<() as Assoc>::Out)` bypass definition-site `checkPackedInnerDef` and violate
`x86Win32AbiInvariant`, whereas `ArrayPacked([Inner; 1])` also bypasses `checkPackedInnerDef`
but silently clears `maxReprAlign` to `none` via `layout_of_array_like`. -/
theorem ce1_corollaries_tuple_alias_ice_and_array_mra_drop :
    checkPackedDefPasses hirTuplePacked = true ∧
    computeMonoLayout (instantiateHir monoInnerAlign8 hirTuplePacked) = ⟨1, some 8⟩ ∧
    ¬ x86Win32AbiInvariant (computeMonoLayout (instantiateHir monoInnerAlign8 hirTuplePacked)) ∧
    checkPackedDefPasses hirAliasPacked = true ∧
    computeMonoLayout (instantiateHir monoInnerAlign8 hirAliasPacked) = ⟨1, some 8⟩ ∧
    ¬ x86Win32AbiInvariant (computeMonoLayout (instantiateHir monoInnerAlign8 hirAliasPacked)) ∧
    checkPackedDefPasses hirArrayPacked = true ∧
    computeMonoLayout (instantiateHir monoInnerAlign8 hirArrayPacked) = ⟨1, none⟩ ∧
    x86Win32AbiInvariant (computeMonoLayout (instantiateHir monoInnerAlign8 hirArrayPacked)) := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro hInv
    have h1ge8 : 1 ≥ 8 := hInv 8 rfl (by decide)
    exact (by decide : ¬ (1 ≥ 8)) h1ge8
  · intro hInv
    have h1ge8 : 1 ≥ 8 := hInv 8 rfl (by decide)
    exact (by decide : ¬ (1 ≥ 8)) h1ge8
  · intro m hm _
    cases hm

end RustcAbiLayoutAndReprSoundness

/-! ## Axiom Audit -/
#print axioms RustcAbiLayoutAndReprSoundness.alignTo_add_le_iff_of_dvd
#print axioms RustcAbiLayoutAndReprSoundness.maxAlignedFactor_dvd_size_and_pow2
#print axioms RustcAbiLayoutAndReprSoundness.vectorTypeLayout_packed_nonpow2_sound
#print axioms RustcAbiLayoutAndReprSoundness.postMonoPackedCheck_implies_abiAlign_ge_maxReprAlign
#print axioms RustcAbiLayoutAndReprSoundness.nine_target_alignment_laws
#print axioms RustcAbiLayoutAndReprSoundness.ce1_generic_packed_bypasses_def_check_violates_win32_abi_inv
#print axioms RustcAbiLayoutAndReprSoundness.ce1_corollaries_tuple_alias_ice_and_array_mra_drop
#print axioms RustcAbiLayoutAndReprSoundness.ce2_simd_packed_pow2_ignores_pack_vs_nonpow2_demotes_memory
#print axioms RustcAbiLayoutAndReprSoundness.ce3_maybe_unsized_suppresses_niche_bias_end_inflating_enum_8_to_12
#print axioms RustcAbiLayoutAndReprSoundness.ce4_uninhabited_align16_zst_variant_forces_size_16_align_16
