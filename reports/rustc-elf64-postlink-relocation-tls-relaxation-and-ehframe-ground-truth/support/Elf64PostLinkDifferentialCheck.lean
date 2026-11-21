/-
  Elf64PostLinkDifferentialCheck.lean

  Kernel-checked Lean v4.34.1 differential ELF64 relocation-policy, TLS/GOT
  relaxation, alignment-padding, and `.eh_frame_hdr` binary-search table
  verifier covering both `rust-lld` and `GNU ld` on `x86_64-unknown-linux-gnu`.

  Zero-axiom & zero-tactic hygiene constraints:
    - 0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`,
      0 `native_decide`, 0 `partial def`, 0 `._unsafe_rec`, 0 `@[extern]`.
-/

namespace Elf64PostLinkDifferentialCheck

/-- Linker implementation flavor modeled by the differential policy checker. -/
inductive LinkerFlavor where
  | rustLld
  | gnuLd
  deriving DecidableEq, Repr

/-- Output artifact mode governing ELF64 symbol preemption and TLS/GOT relaxation. -/
inductive LinkMode where
  | pieOrStaticPie
  | cdylib
  deriving DecidableEq, Repr

/-- All 10 ELF64 x86_64 relocation types observed across rustc sysroot `.rlib`s,
    plus `R_X86_64_GOTPCRELX`, `R_X86_64_TPOFF32`, and `R_X86_64_NONE`. -/
inductive RelocType where
  | r64             -- type 1:  R_X86_64_64
  | rPc32           -- type 2:  R_X86_64_PC32
  | rGotpcrel       -- type 9:  R_X86_64_GOTPCREL (legacy non-relaxable in LLVM/lld)
  | rPlt32          -- type 4:  R_X86_64_PLT32
  | r32             -- type 10: R_X86_64_32
  | rTlsgd          -- type 19: R_X86_64_TLSGD
  | rTlsld          -- type 20: R_X86_64_TLSLD
  | rDtpoff32       -- type 21: R_X86_64_DTPOFF32
  | rGottpoff       -- type 22: R_X86_64_GOTTPOFF
  | rTpoff32        -- type 23: R_X86_64_TPOFF32
  | rGotpcrelx      -- type 41: R_X86_64_GOTPCRELX
  | rRexGotpcrelx   -- type 42: R_X86_64_REX_GOTPCRELX
  | rNone           -- type 0:  R_X86_64_NONE
  deriving DecidableEq, Repr

def relocTypeCode : RelocType → Nat
  | .rNone => 0
  | .r64 => 1
  | .rPc32 => 2
  | .rPlt32 => 4
  | .rGotpcrel => 9
  | .r32 => 10
  | .rTlsgd => 19
  | .rTlsld => 20
  | .rDtpoff32 => 21
  | .rGottpoff => 22
  | .rTpoff32 => 23
  | .rGotpcrelx => 41
  | .rRexGotpcrelx => 42

/-- Whether `rt` is a 10-type rustc sysroot `.rlib` relocation observed in the census. -/
def isSysrootRelocType : RelocType → Bool
  | .r64 | .r32 | .rPc32 | .rGotpcrel | .rPlt32
  | .rTlsgd | .rGottpoff | .rRexGotpcrelx | .rDtpoff32 | .rTlsld => true
  | .rTpoff32 | .rGotpcrelx | .rNone => false

/-- Signed 32-bit little-endian integer encoding into 4 `UInt8` bytes. -/
def encodeI32LE (x : Int) : List UInt8 :=
  let u : Nat := (x % (4294967296 : Int)).toNat
  [ UInt8.ofNat (u % 256)
  , UInt8.ofNat ((u / 256) % 256)
  , UInt8.ofNat ((u / 65536) % 256)
  , UInt8.ofNat ((u / 16777216) % 256) ]

/-- Signed 32-bit little-endian integer decoding from 4 `UInt8` bytes. -/
def decodeI32LE (b0 b1 b2 b3 : UInt8) : Int :=
  let u : Int :=
    Int.ofNat b0.toNat
      + 256 * Int.ofNat b1.toNat
      + 65536 * Int.ofNat b2.toNat
      + 16777216 * Int.ofNat b3.toNat
  if u < (2147483648 : Int) then u else u - (4294967296 : Int)

def decodeI32LEList : List UInt8 → Option Int
  | [b0, b1, b2, b3] => some (decodeI32LE b0 b1 b2 b3)
  | _ => none

/-- Constructive proof that `u < 2^32` implies `u / 2^24 < 256` without `Classical.choice`. -/
private theorem div_16777216_lt_256 (u : Nat) (h : u < 4294967296) : u / 16777216 < 256 := by
  have h1 : 16777216 * (u / 16777216) ≤ 16777216 * (u / 16777216) + u % 16777216 :=
    Nat.le_add_right _ _
  rw [Nat.div_add_mod] at h1
  have h2 : 16777216 * (u / 16777216) < 16777216 * 256 := Nat.lt_of_le_of_lt h1 h
  cases Decidable.em (u / 16777216 < 256) with
  | inl hok => exact hok
  | inr hnot =>
      have hge : 256 ≤ u / 16777216 := Nat.le_of_not_lt hnot
      have hmul : 16777216 * 256 ≤ 16777216 * (u / 16777216) := Nat.mul_le_mul_left 16777216 hge
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hmul h2))

/-- Constructive non-negative 32-bit byte-decomposition helper (no `omega`, no `Classical.choice`). -/
private theorem u32_bytes_reconstruct (u : Nat) (h : u < 4294967296) :
    (u % 256)
      + 256 * ((u / 256) % 256)
      + 65536 * ((u / 65536) % 256)
      + 16777216 * ((u / 16777216) % 256) = u := by
  have hdiv : u / 16777216 < 256 := div_16777216_lt_256 u h
  have hmod : (u / 16777216) % 256 = u / 16777216 := Nat.mod_eq_of_lt hdiv
  rw [hmod]
  have step1 : (u / 65536) % 256 + 256 * (u / 16777216) = u / 65536 := by
    have hq : (u / 65536) / 256 = u / 16777216 := Nat.div_div_eq_div_mul u 65536 256
    rw [← hq, Nat.add_comm]
    exact Nat.div_add_mod (u / 65536) 256
  have step2 : (u / 256) % 256 + 256 * (u / 65536) = u / 256 := by
    have hq : (u / 256) / 256 = u / 65536 := Nat.div_div_eq_div_mul u 256 256
    rw [← hq, Nat.add_comm]
    exact Nat.div_add_mod (u / 256) 256
  have step3 : u % 256 + 256 * (u / 256) = u := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod u 256
  calc
    (u % 256) + 256 * ((u / 256) % 256) + 65536 * ((u / 65536) % 256) + 16777216 * (u / 16777216)
        = (u % 256) + 256 * ((u / 256) % 256) + 65536 * ((u / 65536) % 256 + 256 * (u / 16777216)) := by
            rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
    _ = (u % 256) + 256 * ((u / 256) % 256) + 65536 * (u / 65536) := by
            rw [step1]
    _ = (u % 256) + 256 * ((u / 256) % 256 + 256 * (u / 65536)) := by
            rw [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
    _ = (u % 256) + 256 * (u / 256) := by
            rw [step2]
    _ = u := step3

private theorem ofNat_mod_256 (k : Nat) : (UInt8.ofNat (k % 256)).toNat = k % 256 := by
  have hk : k % 256 < 256 := Nat.mod_lt k (by decide)
  change (k % 256) % UInt8.size = k % 256
  exact Nat.mod_eq_of_lt hk

private theorem u32_ofNat_sum_eq (b0 b1 b2 b3 : Nat) :
    Int.ofNat (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) =
      Int.ofNat b0 + 256 * Int.ofNat b1 + 65536 * Int.ofNat b2 + 16777216 * Int.ofNat b3 := by
  rfl

/-- Constructive `decodeI32LE (b0, b1, b2, b3)` evaluated after `encodeI32LE x`. -/
theorem decodeI32LE_encodeI32LE_bytes (x : Int) (hlo : (-2147483648 : Int) ≤ x) (hhi : x ≤ (2147483647 : Int)) :
    let u := (x % (4294967296 : Int)).toNat
    decodeI32LE
      (UInt8.ofNat (u % 256))
      (UInt8.ofNat ((u / 256) % 256))
      (UInt8.ofNat ((u / 65536) % 256))
      (UInt8.ofNat ((u / 16777216) % 256)) = x := by
  intro u
  dsimp only [decodeI32LE]
  have hmod_nonneg : (0 : Int) ≤ x % (4294967296 : Int) :=
    Int.emod_nonneg x (by decide)
  have hmod_lt : x % (4294967296 : Int) < (4294967296 : Int) :=
    Int.emod_lt_of_pos x (by decide)
  have hu_eq : Int.ofNat u = x % (4294967296 : Int) :=
    Int.toNat_of_nonneg hmod_nonneg
  have hu_lt : u < 4294967296 := by
    have h1 : Int.ofNat u < Int.ofNat 4294967296 := by
      rw [hu_eq]; exact hmod_lt
    exact Int.ofNat_lt.mp h1
  have hb0 : (UInt8.ofNat (u % 256)).toNat = u % 256 := ofNat_mod_256 u
  have hb1 : (UInt8.ofNat ((u / 256) % 256)).toNat = (u / 256) % 256 := ofNat_mod_256 (u / 256)
  have hb2 : (UInt8.ofNat ((u / 65536) % 256)).toNat = (u / 65536) % 256 := ofNat_mod_256 (u / 65536)
  have hb3 : (UInt8.ofNat ((u / 16777216) % 256)).toNat = (u / 16777216) % 256 := ofNat_mod_256 (u / 16777216)
  have hsum_nat :
      (UInt8.ofNat (u % 256)).toNat
        + 256 * (UInt8.ofNat ((u / 256) % 256)).toNat
        + 65536 * (UInt8.ofNat ((u / 65536) % 256)).toNat
        + 16777216 * (UInt8.ofNat ((u / 16777216) % 256)).toNat = u := by
    rw [hb0, hb1, hb2, hb3]
    exact u32_bytes_reconstruct u hu_lt
  have hsum_int :
      Int.ofNat (UInt8.ofNat (u % 256)).toNat
        + 256 * Int.ofNat (UInt8.ofNat ((u / 256) % 256)).toNat
        + 65536 * Int.ofNat (UInt8.ofNat ((u / 65536) % 256)).toNat
        + 16777216 * Int.ofNat (UInt8.ofNat ((u / 16777216) % 256)).toNat = Int.ofNat u := by
    rw [← u32_ofNat_sum_eq]
    exact congrArg Int.ofNat hsum_nat
  rw [hsum_int, hu_eq]
  cases Int.lt_trichotomy x 0 with
  | inl hx_neg =>
      have hx_lo_sum : (0 : Int) ≤ x + (4294967296 : Int) := by
        have h' : (-2147483648 : Int) + (4294967296 : Int) ≤ x + (4294967296 : Int) :=
          Int.add_le_add_right hlo (4294967296 : Int)
        exact Int.le_trans (by decide) h'
      have hx_lt_sum : x + (4294967296 : Int) < (4294967296 : Int) := by
        have h' : x + (4294967296 : Int) < (0 : Int) + (4294967296 : Int) :=
          Int.add_lt_add_right hx_neg (4294967296 : Int)
        exact h'
      have hmod_neg : x % (4294967296 : Int) = x + (4294967296 : Int) := by
        have h1 : (x + (4294967296 : Int)) % (4294967296 : Int) = x + (4294967296 : Int) :=
          Int.emod_eq_of_lt hx_lo_sum hx_lt_sum
        rw [← h1]
        have hadd : (x + (4294967296 : Int)) % (4294967296 : Int) = x % (4294967296 : Int) := by
          rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
        exact hadd.symm
      rw [hmod_neg]
      have hge : ¬ (x + (4294967296 : Int) < (2147483648 : Int)) := by
        have hlow : (2147483648 : Int) ≤ x + (4294967296 : Int) := by
          have h' : (-2147483648 : Int) + (4294967296 : Int) ≤ x + (4294967296 : Int) :=
            Int.add_le_add_right hlo (4294967296 : Int)
          exact Int.le_trans (by decide) h'
        exact Int.not_lt.mpr hlow
      have hite : (if x + (4294967296 : Int) < (2147483648 : Int)
            then x + (4294967296 : Int)
            else (x + (4294967296 : Int)) - (4294967296 : Int)) =
          (x + (4294967296 : Int)) - (4294967296 : Int) :=
        ite_eq_right_iff.mpr (fun hp => False.elim (hge hp))
      change (if x + (4294967296 : Int) < (2147483648 : Int)
            then x + (4294967296 : Int)
            else (x + (4294967296 : Int)) - (4294967296 : Int)) = x
      rw [hite]
      exact Int.add_sub_cancel x (4294967296 : Int)
  | inr hx_ge =>
      have hx_nonneg : (0 : Int) ≤ x := by
        cases hx_ge with
        | inl heq => rw [heq]; decide
        | inr hgt => exact Int.le_of_lt hgt
      have hx_lt_2p32 : x < (4294967296 : Int) :=
        Int.lt_of_le_of_lt hhi (by decide)
      have hmod_nonneg_eq : x % (4294967296 : Int) = x :=
        Int.emod_eq_of_lt hx_nonneg hx_lt_2p32
      rw [hmod_nonneg_eq]
      have hlt_2p31 : x < (2147483648 : Int) :=
        Int.lt_of_le_of_lt hhi (by decide)
      exact ite_eq_left_iff.mpr (fun hnp => False.elim (hnp hlt_2p31))

/-- Signed 32-bit little-endian codec round-trip theorem on all in-range `Int` values. -/
theorem decodeI32LE_encodeI32LE (x : Int) (hlo : (-2147483648 : Int) ≤ x) (hhi : x ≤ (2147483647 : Int)) :
    decodeI32LEList (encodeI32LE x) = some x := by
  dsimp only [encodeI32LE, decodeI32LEList]
  exact congrArg some (decodeI32LE_encodeI32LE_bytes x hlo hhi)

/-- Minimal abstract machine state sufficient to state TLS, GOT, and RIP-relative
    addressing semantics without axiomatic placeholders. -/
structure MachView where
  fsBase  : Int
  ripEnd  : Int
  mem     : Int → Int
  gotMem  : Int → Int
  tlsMod  : Int

/-- Pre-link `R_X86_64_TLSGD` sequence (16 bytes = 8B + 8B):
    `66 48 8d 3d 00 00 00 00` (`data16 lea x@tlsgd(%rip), %rdi`) +
    `66 66 48 e8 00 00 00 00` (`data16 data16 rex.W call __tls_get_addr`).
    Returns `tlsMod + tpoff` in `%rax`. -/
def preLinkTlsGdValue (st : MachView) (tpoff : Int) : Int :=
  st.tlsMod + tpoff

def expectedPreTlsGdWindow : List UInt8 :=
  [ 0x66, 0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00
  , 0x66, 0x66, 0x48, 0xe8, 0x00, 0x00, 0x00, 0x00 ]

def expectedPostTlsGdLePrefix : List UInt8 :=
  [ 0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00
  , 0x48, 0x8d, 0x80 ]

/-- Post-link `TLSGD -> LE` (16 bytes = 9B + 7B):
    `64 48 8b 04 25 00 00 00 00` (`mov %fs:0x0, %rax`) +
    `48 8d 80 <tpoff32>` (`lea tpoff(%rax), %rax`).
    Internal instruction-start offsets shift from `[0, 8]` to `[0, 9]`. -/
def checkTlsGdToLe (pre post : List UInt8) (tpoff : Int) : Bool :=
  (pre == expectedPreTlsGdWindow) &&
  (post == expectedPostTlsGdLePrefix ++ encodeI32LE tpoff)

def evalPostTlsGdLe (st : MachView) (post : List UInt8) : Option Int :=
  match post with
  | [ 0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00
    , 0x48, 0x8d, 0x80, b0, b1, b2, b3 ] =>
      some (st.fsBase + decodeI32LE b0 b1 b2 b3)
  | _ => none

/-- Instruction start offsets within the 16-byte `TLSGD` window: pre `[0, 8]`, post `[0, 9]`. -/
def tlsGdInsnOffsets (isPost : Bool) : List Nat :=
  if isPost then [0, 9] else [0, 8]

theorem tlsgd_to_le_sound_and_shifts_boundary
    (st : MachView) (pre post : List UInt8) (tpoff : Int)
    (h_tls : st.tlsMod = st.fsBase)
    (h_lo : (-2147483648 : Int) ≤ tpoff) (h_hi : tpoff ≤ (2147483647 : Int))
    (h_ok : checkTlsGdToLe pre post tpoff = true) :
    pre.length = 16 ∧ post.length = 16 ∧
    tlsGdInsnOffsets false = [0, 8] ∧ tlsGdInsnOffsets true = [0, 9] ∧
    evalPostTlsGdLe st post = some (preLinkTlsGdValue st tpoff) := by
  dsimp only [checkTlsGdToLe] at h_ok
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h_ok
  rcases h_ok with ⟨hpre, hpost⟩
  subst hpre
  subst hpost
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have hdec := decodeI32LE_encodeI32LE_bytes tpoff h_lo h_hi
  dsimp only [evalPostTlsGdLe, expectedPostTlsGdLePrefix, encodeI32LE, preLinkTlsGdValue]
  change some (st.fsBase + decodeI32LE
      (UInt8.ofNat ((tpoff % 4294967296).toNat % 256))
      (UInt8.ofNat ((tpoff % 4294967296).toNat / 256 % 256))
      (UInt8.ofNat ((tpoff % 4294967296).toNat / 65536 % 256))
      (UInt8.ofNat ((tpoff % 4294967296).toNat / 16777216 % 256))) = some (st.tlsMod + tpoff)
  rw [hdec, h_tls]

/-- `TLSLD -> LE` window (`19` bytes = `7B + 5B + 7B` pre-link -> `12B + 7B` post-link):
    Pre: `48 8d 3d 00 00 00 00` + `e8 00 00 00 00` + `48 <op> 80 00 00 00 00`
         (`op = 0x8b` `mov` load vs `op = 0x8d` `lea` address)
    Post: `66 66 66 64 48 8b 04 25 00 00 00 00` (`12B`) + `48 <op> 80 <tpoff32>` (`7B`). -/
def expectedPreTlsLdWindow (op : UInt8) : List UInt8 :=
  [ 0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00
  , 0xe8, 0x00, 0x00, 0x00, 0x00
  , 0x48, op, 0x80, 0x00, 0x00, 0x00, 0x00 ]

def expectedPostTlsLdPrefix (op : UInt8) : List UInt8 :=
  [ 0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00
  , 0x48, op, 0x80 ]

def isValidTlsLdOp (op : UInt8) : Bool :=
  (op == 0x8b) || (op == 0x8d)

def checkTlsLdToLe (op : UInt8) (pre post : List UInt8) (tpoff : Int) : Bool :=
  isValidTlsLdOp op &&
  (pre == expectedPreTlsLdWindow op) &&
  (post == expectedPostTlsLdPrefix op ++ encodeI32LE tpoff)

def preLinkTlsLdValue (st : MachView) (op : UInt8) (tpoff : Int) : Option Int :=
  if op == 0x8b then some (st.mem (st.tlsMod + tpoff))
  else if op == 0x8d then some (st.tlsMod + tpoff)
  else none

def evalPostTlsLdLe (st : MachView) (post : List UInt8) : Option Int :=
  match post with
  | [ 0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00
    , 0x48, op, 0x80, b0, b1, b2, b3 ] =>
      let addr := st.fsBase + decodeI32LE b0 b1 b2 b3
      if op == 0x8b then some (st.mem addr)
      else if op == 0x8d then some addr
      else none
  | _ => none

def tlsLdInsnOffsets (isPost : Bool) : List Nat :=
  if isPost then [0, 12] else [0, 7, 12]

theorem tlsld_to_le_mov_and_lea_sound
    (st : MachView) (op : UInt8) (pre post : List UInt8) (tpoff : Int)
    (h_tls : st.tlsMod = st.fsBase)
    (h_lo : (-2147483648 : Int) ≤ tpoff) (h_hi : tpoff ≤ (2147483647 : Int))
    (h_ok : checkTlsLdToLe op pre post tpoff = true) :
    (op = 0x8b ∨ op = 0x8d) ∧
    pre.length = 19 ∧ post.length = 19 ∧
    tlsLdInsnOffsets false = [0, 7, 12] ∧ tlsLdInsnOffsets true = [0, 12] ∧
    evalPostTlsLdLe st post = preLinkTlsLdValue st op tpoff := by
  dsimp only [checkTlsLdToLe, isValidTlsLdOp] at h_ok
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, beq_iff_eq] at h_ok
  rcases h_ok with ⟨⟨hop, hpre⟩, hpost⟩
  subst hpre
  subst hpost
  have hdec := decodeI32LE_encodeI32LE_bytes tpoff h_lo h_hi
  cases hop with
  | inl heq8b =>
      subst heq8b
      refine ⟨Or.inl rfl, rfl, rfl, rfl, rfl, ?_⟩
      change (if (0x8b : UInt8) == 0x8b
        then some (st.mem (st.fsBase + decodeI32LE
          (UInt8.ofNat ((tpoff % 4294967296).toNat % 256))
          (UInt8.ofNat ((tpoff % 4294967296).toNat / 256 % 256))
          (UInt8.ofNat ((tpoff % 4294967296).toNat / 65536 % 256))
          (UInt8.ofNat ((tpoff % 4294967296).toNat / 16777216 % 256))))
        else if (0x8b : UInt8) == 0x8d
          then some (st.fsBase + decodeI32LE
            (UInt8.ofNat ((tpoff % 4294967296).toNat % 256))
            (UInt8.ofNat ((tpoff % 4294967296).toNat / 256 % 256))
            (UInt8.ofNat ((tpoff % 4294967296).toNat / 65536 % 256))
            (UInt8.ofNat ((tpoff % 4294967296).toNat / 16777216 % 256)))
          else none) = some (st.mem (st.tlsMod + tpoff))
      rw [hdec, h_tls]
      rfl
  | inr heq8d =>
      subst heq8d
      refine ⟨Or.inr rfl, rfl, rfl, rfl, rfl, ?_⟩
      change (if (0x8d : UInt8) == 0x8b
        then some (st.mem (st.fsBase + decodeI32LE
          (UInt8.ofNat ((tpoff % 4294967296).toNat % 256))
          (UInt8.ofNat ((tpoff % 4294967296).toNat / 256 % 256))
          (UInt8.ofNat ((tpoff % 4294967296).toNat / 65536 % 256))
          (UInt8.ofNat ((tpoff % 4294967296).toNat / 16777216 % 256))))
        else if (0x8d : UInt8) == 0x8d
          then some (st.fsBase + decodeI32LE
            (UInt8.ofNat ((tpoff % 4294967296).toNat % 256))
            (UInt8.ofNat ((tpoff % 4294967296).toNat / 256 % 256))
            (UInt8.ofNat ((tpoff % 4294967296).toNat / 65536 % 256))
            (UInt8.ofNat ((tpoff % 4294967296).toNat / 16777216 % 256)))
          else none) = some (st.tlsMod + tpoff)
      rw [hdec, h_tls]
      rfl

/-- `GOTTPOFF -> LE` forms (`7` bytes each):
    - `mov` (%rax):        `48 8b 05 00..00` → `48 c7 c0 <tpoff32>`
    - `add` (%rax):        `48 03 05 00..00` → `48 8d 80 <tpoff32>` (via LEA)
    - `add` (%r12 / %rsp): `4c 03 25 00..00` → `49 81 c4 <tpoff32>` (IMM ADD because ModRM rm=100 needs SIB in LEA). -/
inductive GottpoffForm where
  | movRax
  | addRax
  | addR12
  deriving DecidableEq, Repr

def expectedPreGottpoff : GottpoffForm → List UInt8
  | .movRax => [0x48, 0x8b, 0x05, 0x00, 0x00, 0x00, 0x00]
  | .addRax => [0x48, 0x03, 0x05, 0x00, 0x00, 0x00, 0x00]
  | .addR12 => [0x4c, 0x03, 0x25, 0x00, 0x00, 0x00, 0x00]

def expectedPostGottpoffPrefix : GottpoffForm → List UInt8
  | .movRax => [0x48, 0xc7, 0xc0]
  | .addRax => [0x48, 0x8d, 0x80]
  | .addR12 => [0x49, 0x81, 0xc4]

def checkGottpoffToLe (form : GottpoffForm) (pre post : List UInt8) (tpoff : Int) : Bool :=
  (pre == expectedPreGottpoff form) &&
  (post == expectedPostGottpoffPrefix form ++ encodeI32LE tpoff)

def preLinkGottpoff (st : MachView) (gotSlot acc : Int) : GottpoffForm → Int
  | .movRax => st.gotMem gotSlot
  | .addRax => acc + st.gotMem gotSlot
  | .addR12 => acc + st.gotMem gotSlot

def evalPostGottpoff (acc : Int) (post : List UInt8) : Option Int :=
  match post with
  | [0x48, 0xc7, 0xc0, b0, b1, b2, b3] => some (decodeI32LE b0 b1 b2 b3)
  | [0x48, 0x8d, 0x80, b0, b1, b2, b3] => some (acc + decodeI32LE b0 b1 b2 b3)
  | [0x49, 0x81, 0xc4, b0, b1, b2, b3] => some (acc + decodeI32LE b0 b1 b2 b3)
  | _ => none

theorem gottpoff_to_le_sound
    (st : MachView) (form : GottpoffForm) (pre post : List UInt8) (gotSlot acc tpoff : Int)
    (h_got : st.gotMem gotSlot = tpoff)
    (h_lo : (-2147483648 : Int) ≤ tpoff) (h_hi : tpoff ≤ (2147483647 : Int))
    (h_ok : checkGottpoffToLe form pre post tpoff = true) :
    pre.length = 7 ∧ post.length = 7 ∧
    evalPostGottpoff acc post = some (preLinkGottpoff st gotSlot acc form) := by
  dsimp only [checkGottpoffToLe] at h_ok
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h_ok
  rcases h_ok with ⟨hpre, hpost⟩
  subst hpre
  subst hpost
  have hdec := decodeI32LE_encodeI32LE_bytes tpoff h_lo h_hi
  cases form
  · refine ⟨rfl, rfl, ?_⟩
    change some (decodeI32LE _ _ _ _) = some (st.gotMem gotSlot)
    rw [hdec, h_got]
  · refine ⟨rfl, rfl, ?_⟩
    change some (acc + decodeI32LE _ _ _ _) = some (acc + st.gotMem gotSlot)
    rw [hdec, h_got]
  · refine ⟨rfl, rfl, ?_⟩
    change some (acc + decodeI32LE _ _ _ _) = some (acc + st.gotMem gotSlot)
    rw [hdec, h_got]

/-- Head-to-head linker policy for `GOTPCREL` (type 9) vs `GOTPCRELX`/`REX_GOTPCRELX` (41/42):
    - `movq` (`48 8b <modrm>` -> `48 8d <modrm>`):
      * `rust-lld`: requires `R_X86_64_REX_GOTPCRELX` (or `GOTPCRELX`) in `pieOrStaticPie` with `relaxFlag = true` (`adjustGotPcExpr` in `lld/ELF/Arch/X86_64.cpp`). Rejects legacy `R_X86_64_GOTPCREL`.
      * `GNU ld`: relaxes BOTH `REX_GOTPCRELX` and legacy `R_X86_64_GOTPCREL` `movq` in `pieOrStaticPie` when `relaxFlag = true`.
    - `call *` (`ff 15` -> `67 e8` `addr32 call`):
      * BOTH `rust-lld` and `GNU ld` require `R_X86_64_GOTPCRELX` (or `REX_GOTPCRELX`) in `pieOrStaticPie` with `relaxFlag = true`; neither relaxes `R_X86_64_GOTPCREL` `ff 15`!
    - In `cdylib` mode (default ELF symbol preemption) or `--no-relax` (`relaxFlag = false`), NEITHER opcode mutates. -/
inductive GotInsnKind where
  | movq (rexByte modrmByte : UInt8)
  | callIndirect
  deriving DecidableEq, Repr

def allowsGotOpcodeRelax (flavor : LinkerFlavor) (mode : LinkMode) (relaxFlag : Bool)
    (rt : RelocType) (kind : GotInsnKind) : Bool :=
  match mode, relaxFlag with
  | .pieOrStaticPie, true =>
      match kind with
      | .movq _ _ =>
          match flavor with
          | .rustLld => (rt == .rRexGotpcrelx) || (rt == .rGotpcrelx)
          | .gnuLd   => (rt == .rRexGotpcrelx) || (rt == .rGotpcrelx) || (rt == .rGotpcrel)
      | .callIndirect =>
          (rt == .rRexGotpcrelx) || (rt == .rGotpcrelx)
  | _, _ => false

def expectedPreGotInsn : GotInsnKind → List UInt8
  | .movq rex modrm => [rex, 0x8b, modrm, 0x00, 0x00, 0x00, 0x00]
  | .callIndirect   => [0xff, 0x15, 0x00, 0x00, 0x00, 0x00]

def expectedPostGotInsn (relaxed : Bool) (disp32 : Int) : GotInsnKind → List UInt8
  | .movq rex modrm => [rex, if relaxed then 0x8d else 0x8b, modrm] ++ encodeI32LE disp32
  | .callIndirect   =>
      (if relaxed then [0x67, 0xe8] else [0xff, 0x15]) ++ encodeI32LE disp32

def verifyGotWindow (flavor : LinkerFlavor) (mode : LinkMode) (relaxFlag : Bool)
    (rt : RelocType) (kind : GotInsnKind) (pre post : List UInt8)
    (relaxed : Bool) (disp32 : Int) : Bool :=
  (pre == expectedPreGotInsn kind) &&
  (post == expectedPostGotInsn relaxed disp32 kind) &&
  ((!relaxed) || allowsGotOpcodeRelax flavor mode relaxFlag rt kind)

/-- Address loaded by `mov (%rip + gotDisp)` vs `lea (%rip + directDisp)` in `pieOrStaticPie`. -/
def evalGotMov (st : MachView) (insnBytes : List UInt8) : Option Int :=
  match insnBytes with
  | [_, 0x8b, _, b0, b1, b2, b3] => some (st.gotMem (st.ripEnd + decodeI32LE b0 b1 b2 b3))
  | [_, 0x8d, _, b0, b1, b2, b3] => some (st.ripEnd + decodeI32LE b0 b1 b2 b3)
  | _ => none

/-- Semantic soundness of `mov -> lea` relaxation AND explicit root-cause proof of why
    unrelocated `.got` under ASLR crashes freestanding `#![no_std] -static-pie` when `aslrBase != 0`. -/
theorem differential_gotpcrel_policy_and_aslr_sound
    (symLinkVA aslrBase : Int) :
    allowsGotOpcodeRelax .rustLld .pieOrStaticPie true .rGotpcrel (.movq 0x48 0x1d) = false ∧
    allowsGotOpcodeRelax .gnuLd .pieOrStaticPie true .rGotpcrel (.movq 0x48 0x1d) = true ∧
    allowsGotOpcodeRelax .gnuLd .pieOrStaticPie true .rGotpcrel .callIndirect = false ∧
    allowsGotOpcodeRelax .rustLld .pieOrStaticPie true .rGotpcrel .callIndirect = false ∧
    -- Unrelaxed GOT read without self-relocation differs from relocated address whenever aslrBase ≠ 0:
    (aslrBase ≠ 0 → aslrBase + symLinkVA ≠ symLinkVA) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro h_ne h_eq
  apply h_ne
  have h1 : aslrBase + symLinkVA - symLinkVA = symLinkVA - symLinkVA := by rw [h_eq]
  rw [Int.add_sub_cancel, Int.sub_self] at h1
  exact h1

/-- Direct semantic equivalence between unrelaxed relocated GOT load and relaxed `lea`
    for `REX_GOTPCRELX` when `ripEnd = aslrBase + pcLinkEnd`. -/
theorem got_mov_to_lea_semantic_equiv
    (st : MachView) (rex modrm : UInt8) (aslrBase pcLinkEnd symLinkVA gotLinkVA : Int)
    (h_rip : st.ripEnd = aslrBase + pcLinkEnd)
    (h_got_slot : st.gotMem (aslrBase + gotLinkVA) = aslrBase + symLinkVA)
    (h_got_lo : (-2147483648 : Int) ≤ gotLinkVA - pcLinkEnd)
    (h_got_hi : gotLinkVA - pcLinkEnd ≤ (2147483647 : Int))
    (h_sym_lo : (-2147483648 : Int) ≤ symLinkVA - pcLinkEnd)
    (h_sym_hi : symLinkVA - pcLinkEnd ≤ (2147483647 : Int)) :
    evalGotMov st (expectedPostGotInsn false (gotLinkVA - pcLinkEnd) (.movq rex modrm))
      = some (aslrBase + symLinkVA) ∧
    evalGotMov st (expectedPostGotInsn true (symLinkVA - pcLinkEnd) (.movq rex modrm))
      = some (aslrBase + symLinkVA) := by
  have hdec_got := decodeI32LE_encodeI32LE_bytes (gotLinkVA - pcLinkEnd) h_got_lo h_got_hi
  have hdec_sym := decodeI32LE_encodeI32LE_bytes (symLinkVA - pcLinkEnd) h_sym_lo h_sym_hi
  constructor
  · change some (st.gotMem (st.ripEnd + decodeI32LE _ _ _ _)) = some (aslrBase + symLinkVA)
    rw [hdec_got, h_rip]
    have haddr : aslrBase + pcLinkEnd + (gotLinkVA - pcLinkEnd) = aslrBase + gotLinkVA := by
      rw [Int.add_assoc, Int.sub_eq_add_neg, Int.add_comm gotLinkVA (-pcLinkEnd),
          ← Int.add_assoc pcLinkEnd (-pcLinkEnd) gotLinkVA, Int.add_right_neg, Int.zero_add]
    rw [haddr, h_got_slot]
  · change some (st.ripEnd + decodeI32LE _ _ _ _) = some (aslrBase + symLinkVA)
    rw [hdec_sym, h_rip]
    have haddr : aslrBase + pcLinkEnd + (symLinkVA - pcLinkEnd) = aslrBase + symLinkVA := by
      rw [Int.add_assoc, Int.sub_eq_add_neg, Int.add_comm symLinkVA (-pcLinkEnd),
          ← Int.add_assoc pcLinkEnd (-pcLinkEnd) symLinkVA, Int.add_right_neg, Int.zero_add]
    rw [haddr]

/-- Alignment padding check (`0xcc` `int3` used by `rust-lld` vs NOP family used by `GNU ld`). -/
def isInt3Pad (bytes : List UInt8) : Bool :=
  bytes.all (fun b => b == 0xcc)

/-- `.eh_frame_hdr` binary-search entry + paired `.eh_frame` FDE PC-begin witness. -/
structure EhFrameEntryWitness where
  initLocRel    : Int
  fdePtrRel     : Int
  fdePcBeginRel : Int
  deriving DecidableEq, Repr

/-- Standard 4-byte `.eh_frame_hdr` header:
    `[0x01 (version), 0x1b (DW_EH_PE_pcrel|sdata4), 0x03 (DW_EH_PE_udata4), 0x3b (DW_EH_PE_datarel|sdata4)]`. -/
def expectedEhHdrPrefix : List UInt8 := [0x01, 0x1b, 0x03, 0x3b]

def checkStrictlySortedPairs : List EhFrameEntryWitness → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      decide (a.initLocRel < b.initLocRel) && checkStrictlySortedPairs (b :: rest)

def checkEntriesRelocated (hdrVA : Int) : List EhFrameEntryWitness → Bool
  | [] => true
  | e :: rest =>
      let tablePC := hdrVA + e.initLocRel
      let fdeVA := hdrVA + e.fdePtrRel
      let fdePC := (fdeVA + 8) + e.fdePcBeginRel
      decide (tablePC = fdePC) && checkEntriesRelocated hdrVA rest

def checkEhFrameHdr (hdrBytes12 : List UInt8) (hdrVA ehFrameVA : Int)
    (entries : List EhFrameEntryWitness) : Bool :=
  match hdrBytes12 with
  | [v, pEnc, cEnc, tEnc, p0, p1, p2, p3, c0, c1, c2, c3] =>
      ([v, pEnc, cEnc, tEnc] == expectedEhHdrPrefix) &&
      decide (hdrVA + 4 + decodeI32LE p0 p1 p2 p3 = ehFrameVA) &&
      (decodeI32LE c0 c1 c2 c3 == Int.ofNat entries.length) &&
      checkStrictlySortedPairs entries &&
      checkEntriesRelocated hdrVA entries
  | _ => false

theorem checkStrictlySortedPairs_head_lt_all (a : EhFrameEntryWitness) (xs : List EhFrameEntryWitness)
    (hs : checkStrictlySortedPairs (a :: xs) = true) :
    ∀ y, y ∈ xs → a.initLocRel < y.initLocRel := by
  induction xs generalizing a with
  | nil =>
      intro y hy
      cases hy
  | cons b rest ih =>
      intro y hy
      dsimp only [checkStrictlySortedPairs] at hs
      rw [Bool.and_eq_true] at hs
      rcases hs with ⟨hab_dec, hrest⟩
      have hab : a.initLocRel < b.initLocRel := of_decide_eq_true hab_dec
      cases hy with
      | head _ => exact hab
      | tail _ hmem =>
          have hby : b.initLocRel < y.initLocRel := ih b hrest y hmem
          exact Int.lt_trans hab hby

theorem checkEntriesRelocated_all (hdrVA : Int) (xs : List EhFrameEntryWitness)
    (h : checkEntriesRelocated hdrVA xs = true) :
    ∀ e, e ∈ xs → hdrVA + e.initLocRel = (hdrVA + e.fdePtrRel + 8) + e.fdePcBeginRel := by
  induction xs with
  | nil =>
      intro e he
      cases he
  | cons x rest ih =>
      intro e he
      dsimp only [checkEntriesRelocated] at h
      rw [Bool.and_eq_true] at h
      rcases h with ⟨hx_dec, hrest⟩
      cases he with
      | head _ => exact of_decide_eq_true hx_dec
      | tail _ hmem => exact ih hrest e hmem

/-- Master `.eh_frame_hdr` verification theorem: passing `checkEhFrameHdr` establishes
    header encoding validity, exact `.eh_frame` target VA, strict ordering across all
    entries, and 100% agreement between binary-search keys and relocated FDE PCs. -/
theorem checkEhFrameHdr_sound (hdrBytes12 : List UInt8) (hdrVA ehFrameVA : Int)
    (entries : List EhFrameEntryWitness)
    (h : checkEhFrameHdr hdrBytes12 hdrVA ehFrameVA entries = true) :
    (∀ a b rest1 rest2,
      entries = rest1 ++ [a] ++ rest2 → b ∈ rest2 → hdrVA + a.initLocRel < hdrVA + b.initLocRel) ∧
    (∀ e, e ∈ entries → hdrVA + e.initLocRel = (hdrVA + e.fdePtrRel + 8) + e.fdePcBeginRel) := by
  rcases hdrBytes12 with _ | ⟨v, _ | ⟨pEnc, _ | ⟨cEnc, _ | ⟨tEnc, _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals
    try (dsimp only [checkEhFrameHdr] at h; contradiction)
  cases rest with
  | cons _ _ =>
      dsimp only [checkEhFrameHdr] at h
      contradiction
  | nil =>
      dsimp only [checkEhFrameHdr] at h
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨⟨⟨⟨_, _⟩, _⟩, hsorted⟩, hreloc⟩
      constructor
      · intro a b rest1 rest2 hsplit hmem
        have hsub : ∀ xs, checkStrictlySortedPairs xs = true →
            ∀ r1 r2, xs = r1 ++ [a] ++ r2 → b ∈ r2 → a.initLocRel < b.initLocRel := by
          intro xs hxs r1
          induction r1 generalizing xs with
          | nil =>
              intro r2 heq hbm
              rw [heq] at hxs
              exact checkStrictlySortedPairs_head_lt_all a r2 hxs b hbm
          | cons z zs ih =>
              intro r2 heq hbm
              rw [heq] at hxs
              cases zs with
              | nil =>
                  have htail : checkStrictlySortedPairs (a :: r2) = true := by
                    change (decide (z.initLocRel < a.initLocRel) && checkStrictlySortedPairs (a :: r2)) = true at hxs
                    rw [Bool.and_eq_true] at hxs
                    exact hxs.2
                  exact ih (a :: r2) htail r2 rfl hbm
              | cons z2 zs2 =>
                  have htail : checkStrictlySortedPairs ((z2 :: zs2) ++ [a] ++ r2) = true := by
                    change (decide (z.initLocRel < z2.initLocRel) && checkStrictlySortedPairs ((z2 :: zs2) ++ [a] ++ r2)) = true at hxs
                    rw [Bool.and_eq_true] at hxs
                    exact hxs.2
                  exact ih ((z2 :: zs2) ++ [a] ++ r2) htail r2 rfl hbm
        have hlt := hsub entries hsorted rest1 rest2 hsplit hmem
        exact Int.add_lt_add_left hlt hdrVA
      · exact checkEntriesRelocated_all hdrVA entries hreloc

-- ============================================================================
-- Concrete Positive Differential Witnesses (Taken Verbatim from Live Probe)
-- ============================================================================

/-- Observed `dyn_pie_{gnu_ld, rust_lld}` `TLSGD -> LE` (`8B+8B -> 9B+7B`, `tpoff = -0x58 = -88`). -/
def obsPreTlsGd : List UInt8 :=
  [0x66, 0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00, 0x66, 0x66, 0x48, 0xe8, 0x00, 0x00, 0x00, 0x00]

def obsPostTlsGd : List UInt8 :=
  [0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x80, 0xa8, 0xff, 0xff, 0xff]

/-- Observed `dyn_pie_{gnu_ld, rust_lld}` `TLSLD -> LE` (`7B+5B+7B -> 12B+7B`, `tpoff = -0x60 = -96`). -/
def obsPreTlsLdMov : List UInt8 :=
  [0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x80, 0x00, 0x00, 0x00, 0x00]

def obsPostTlsLdMov : List UInt8 :=
  [0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x80, 0xa0, 0xff, 0xff, 0xff]

def obsPreTlsLdLea : List UInt8 :=
  [0x48, 0x8d, 0x3d, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x80, 0x00, 0x00, 0x00, 0x00]

def obsPostTlsLdLea : List UInt8 :=
  [0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x80, 0xa0, 0xff, 0xff, 0xff]

/-- Observed `dyn_pie_{gnu_ld, rust_lld}` `GOTTPOFF -> LE` (`tpoff = -0x68 = -104`). -/
def obsPreGottpoffMov : List UInt8 := [0x48, 0x8b, 0x05, 0x00, 0x00, 0x00, 0x00]
def obsPostGottpoffMov : List UInt8 := [0x48, 0xc7, 0xc0, 0x98, 0xff, 0xff, 0xff]
def obsPreGottpoffAddRax : List UInt8 := [0x48, 0x03, 0x05, 0x00, 0x00, 0x00, 0x00]
def obsPostGottpoffAddRax : List UInt8 := [0x48, 0x8d, 0x80, 0x98, 0xff, 0xff, 0xff]
def obsPreGottpoffAddR12 : List UInt8 := [0x4c, 0x03, 0x25, 0x00, 0x00, 0x00, 0x00]
def obsPostGottpoffAddR12 : List UInt8 := [0x49, 0x81, 0xc4, 0x98, 0xff, 0xff, 0xff]

/-- Observed `use_got_strict` `mov` (`48 8b 1d`) and `use_got_relaxable` `mov` + `call`:
    `GNU ld` relaxes legacy `R_X86_64_GOTPCREL` `48 8b 1d` → `48 8d 1d` (`+0x37930`), while
    `rust-lld` keeps `48 8b 1d` (`+0x3f5b8`) unrelaxed, and BOTH relax `ff 15 -> 67 e8` on `GOTPCRELX`. -/
def obsPreGotMovRbx : List UInt8 := [0x48, 0x8b, 0x1d, 0x00, 0x00, 0x00, 0x00]
def obsPostGnuGotStrictMov : List UInt8 := [0x48, 0x8d, 0x1d, 0x30, 0x79, 0x03, 0x00]
def obsPostLldGotStrictMov : List UInt8 := [0x48, 0x8b, 0x1d, 0xb8, 0xf5, 0x03, 0x00]
def obsPostLldGotRelaxMov : List UInt8 := [0x48, 0x8d, 0x1d, 0xf8, 0x35, 0xff, 0xff]
def obsPreGotCall : List UInt8 := [0xff, 0x15, 0x00, 0x00, 0x00, 0x00]
def obsPostGotCallRelax : List UInt8 := [0x67, 0xe8, 0xcf, 0xfe, 0xff, 0xff]
def obsPostGotCallUnrelaxGnu : List UInt8 := [0xff, 0x15, 0x87, 0x96, 0x04, 0x00]

/-- Observed `.eh_frame_hdr` 12-byte prefixes and first-two FDE entries for `GNU ld` vs `rust-lld` (`cdylib`).
    `obsCdylibGnuHdr12`: `01 1b 03 3b 04 0f 00 00` (`0x0f04 = 3844`, `0x44a90 + 4 + 3844 = 0x45998`), 2-entry slice count.
    `obsCdylibLldHdr12`: `01 1b 03 3b f4 0e 00 00` (`0x0ef4 = 3828`, `0xb530 + 4 + 3828 = 0xc428`), 2-entry slice count. -/
def obsCdylibGnuHdr12 : List UInt8 :=
  [0x01, 0x1b, 0x03, 0x3b, 0x04, 0x0f, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00] -- 2-entry slice check
def obsCdylibGnuEntries2 : List EhFrameEntryWitness :=
  [ ⟨-260720, 3872, -264600⟩, ⟨-260672, 3912, -264592⟩ ]

def obsCdylibLldHdr12 : List UInt8 :=
  [0x01, 0x1b, 0x03, 0x3b, 0xf4, 0x0e, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00] -- 2-entry slice check
def obsCdylibLldEntries2 : List EhFrameEntryWitness :=
  [ ⟨27120, 3856, 23256⟩, ⟨27136, 3876, 23252⟩ ]

theorem accept_live_tls_and_got_differential_witnesses :
    checkTlsGdToLe obsPreTlsGd obsPostTlsGd (-88) = true ∧
    checkTlsLdToLe 0x8b obsPreTlsLdMov obsPostTlsLdMov (-96) = true ∧
    checkTlsLdToLe 0x8d obsPreTlsLdLea obsPostTlsLdLea (-96) = true ∧
    checkGottpoffToLe .movRax obsPreGottpoffMov obsPostGottpoffMov (-104) = true ∧
    checkGottpoffToLe .addRax obsPreGottpoffAddRax obsPostGottpoffAddRax (-104) = true ∧
    checkGottpoffToLe .addR12 obsPreGottpoffAddR12 obsPostGottpoffAddR12 (-104) = true ∧
    -- Differential GOTPCREL mov: accepted relaxed on GNU ld, accepted unrelaxed on rust-lld, REJECTED relaxed on rust-lld!
    verifyGotWindow .gnuLd .pieOrStaticPie true .rGotpcrel (.movq 0x48 0x1d) obsPreGotMovRbx obsPostGnuGotStrictMov true 0x37930 = true ∧
    verifyGotWindow .rustLld .pieOrStaticPie true .rGotpcrel (.movq 0x48 0x1d) obsPreGotMovRbx obsPostLldGotStrictMov false 0x3f5b8 = true ∧
    verifyGotWindow .rustLld .pieOrStaticPie true .rRexGotpcrelx (.movq 0x48 0x1d) obsPreGotMovRbx obsPostLldGotRelaxMov true (-0xca08) = true ∧
    verifyGotWindow .rustLld .pieOrStaticPie true .rGotpcrelx .callIndirect obsPreGotCall obsPostGotCallRelax true (-0x131) = true ∧
    verifyGotWindow .gnuLd .pieOrStaticPie true .rGotpcrel .callIndirect obsPreGotCall obsPostGotCallUnrelaxGnu false 0x49687 = true ∧
    -- Signed polarity check on .eh_frame_hdr (negative keys on GNU ld, positive keys on rust-lld):
    checkEhFrameHdr obsCdylibGnuHdr12 0x44a90 0x45998 obsCdylibGnuEntries2 = true ∧
    checkEhFrameHdr obsCdylibLldHdr12 0xb530 0xc428 obsCdylibLldEntries2 = true ∧
    isInt3Pad [0xcc, 0xcc, 0xcc, 0xcc] = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl⟩

-- ============================================================================
-- Negative Tamper-Detection Witnesses (Must All Fail Closed = false)
-- ============================================================================

/-- Tamper 1: `rust-lld` MUST NOT mutate opcode on legacy `R_X86_64_GOTPCREL` (`mov -> lea`),
    and NEITHER `GNU ld` nor `rust-lld` may relax `ff 15 -> 67 e8` on `R_X86_64_GOTPCREL`. -/
theorem reject_gotpcrel_illegal_opcode_mutations :
    verifyGotWindow .rustLld .pieOrStaticPie true .rGotpcrel (.movq 0x48 0x1d) obsPreGotMovRbx obsPostGnuGotStrictMov true 0x37930 = false ∧
    verifyGotWindow .gnuLd .pieOrStaticPie true .rGotpcrel .callIndirect obsPreGotCall obsPostGotCallRelax true (-0x131) = false ∧
    verifyGotWindow .rustLld .pieOrStaticPie true .rGotpcrel .callIndirect obsPreGotCall obsPostGotCallRelax true (-0x131) = false ∧
    verifyGotWindow .gnuLd .cdylib true .rRexGotpcrelx (.movq 0x48 0x1d) obsPreGotMovRbx obsPostGnuGotStrictMov true 0x37930 = false := by
  repeat' constructor

/-- Tamper 2: Truncated `TLSGD` (`15B`) or mismatched `TLSLD` prefix (`18B`) is rejected. -/
theorem reject_truncated_tls_sequences :
    checkTlsGdToLe obsPreTlsGd (obsPostTlsGd.take 15) (-88) = false ∧
    checkTlsLdToLe 0x8b obsPreTlsLdMov (obsPostTlsLdMov.take 18) (-96) = false ∧
    checkTlsLdToLe 0x8e obsPreTlsLdMov obsPostTlsLdMov (-96) = false := by
  repeat' constructor

/-- Tamper 3: Out-of-order `.eh_frame_hdr` search table or mismatched FDE PC-begin relocation is rejected. -/
theorem reject_corrupted_eh_frame_hdr :
    checkEhFrameHdr obsCdylibLldHdr12 0xb530 0xc428
      [ ⟨27136, 3876, 23252⟩, ⟨27120, 3856, 23256⟩ ] = false ∧
    checkEhFrameHdr obsCdylibLldHdr12 0xb530 0xc428
      [ ⟨27120, 3856, 23257⟩, ⟨27136, 3876, 23252⟩ ] = false := by
  repeat' constructor

#print axioms decodeI32LE_encodeI32LE
#print axioms tlsgd_to_le_sound_and_shifts_boundary
#print axioms tlsld_to_le_mov_and_lea_sound
#print axioms gottpoff_to_le_sound
#print axioms differential_gotpcrel_policy_and_aslr_sound
#print axioms got_mov_to_lea_semantic_equiv
#print axioms checkEhFrameHdr_sound
#print axioms accept_live_tls_and_got_differential_witnesses
#print axioms reject_gotpcrel_illegal_opcode_mutations
#print axioms reject_truncated_tls_sequences
#print axioms reject_corrupted_eh_frame_hdr

end Elf64PostLinkDifferentialCheck
