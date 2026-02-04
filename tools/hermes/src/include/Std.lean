import Aeneas
open Aeneas Aeneas.Std Result Error

namespace Hermes.Std

class Verifiable (α : Type) where
  is_valid : α -> Prop

attribute [simp] Verifiable.is_valid

instance : Verifiable U8 where is_valid _ := True
instance : Verifiable U16 where is_valid _ := True
instance : Verifiable U32 where is_valid _ := True
instance : Verifiable U64 where is_valid _ := True
instance : Verifiable U128 where is_valid _ := True
instance : Verifiable I8 where is_valid _ := True
instance : Verifiable I16 where is_valid _ := True
instance : Verifiable I32 where is_valid _ := True
instance : Verifiable I64 where is_valid _ := True
instance : Verifiable I128 where is_valid _ := True
instance : Verifiable Usize where is_valid _ := True
instance : Verifiable Isize where is_valid _ := True
instance : Verifiable Bool where is_valid _ := True
instance : Verifiable Unit where is_valid _ := True

instance : OfNat U32 n where ofNat := UScalar.mk (BitVec.ofNat 32 n)
instance : OfNat I32 n where ofNat := IScalar.mk (BitVec.ofNat 32 n)
instance : OfNat Usize n where ofNat := UScalar.mk (BitVec.ofNat System.Platform.numBits n)
instance : OfNat Isize n where ofNat := IScalar.mk (BitVec.ofNat System.Platform.numBits n)

def IsPowerOfTwo (n : Nat) : Prop := ∃ k, n = 2^k

class Alignment (n: Nat) : Prop where
  is_power_of_two : IsPowerOfTwo n
  is_positive : 0 < n

-- TODO: Cite Rust Reference for these invariants.
class Layout (α : Type) where
  size : Nat
  align : Nat
  
  valid_alignment : Alignment align
  size_aligned : size % align = 0

end Hermes.Std

namespace Hermes.Std.Memory

variable {T : Type}

abbrev ConstPtr (T : Type) := ConstRawPtr T

-- Maps a pointer to its address
opaque addr (ptr : ConstPtr T) : Nat

def is_aligned [Layout T] (ptr : ConstPtr T) : Prop :=
  (addr ptr) % (Layout.align T) = 0

opaque is_initialized (ptr : ConstPtr T) : Prop

instance : Verifiable (ConstPtr T) where is_valid _ := True

end Hermes.Std.Memory

namespace Hermes.Std.Platform

-- Target Dependent Definitions
opaque usize_size : Nat

-- TODO(https://github.com/rust-lang/reference/issues/2155): Update signed
-- alignment to be equal to unsigned if this guarantee is added.
opaque usize_align : Nat
opaque isize_align : Nat

opaque u16_align : Nat
opaque i16_align : Nat

opaque u32_align : Nat
opaque i32_align : Nat

opaque u64_align : Nat
opaque i64_align : Nat

opaque u128_align : Nat
opaque i128_align : Nat

-- Alignment Axioms (Power of Two)
axiom usize_align_pow2 : IsPowerOfTwo usize_align
axiom isize_align_pow2 : IsPowerOfTwo isize_align

axiom u16_align_pow2 : IsPowerOfTwo u16_align
axiom i16_align_pow2 : IsPowerOfTwo i16_align

axiom u32_align_pow2 : IsPowerOfTwo u32_align
axiom i32_align_pow2 : IsPowerOfTwo i32_align

axiom u64_align_pow2 : IsPowerOfTwo u64_align
axiom i64_align_pow2 : IsPowerOfTwo i64_align

axiom u128_align_pow2 : IsPowerOfTwo u128_align
axiom i128_align_pow2 : IsPowerOfTwo i128_align

-- Alignment Axioms (Size is Multiple of Alignment)
axiom usize_size_aligned : usize_size % usize_align = 0
axiom isize_size_aligned : usize_size % isize_align = 0

axiom u16_size_aligned : 2 % u16_align = 0
axiom i16_size_aligned : 2 % i16_align = 0

axiom u32_size_aligned : 4 % u32_align = 0
axiom i32_size_aligned : 4 % i32_align = 0

axiom u64_size_aligned : 8 % u64_align = 0
axiom i64_size_aligned : 8 % i64_align = 0

axiom u128_size_aligned : 16 % u128_align = 0
axiom i128_size_aligned : 16 % i128_align = 0

-- Helper for proving positive from power of two
theorem pow2_is_positive (n : Nat) (h : IsPowerOfTwo n) : 0 < n :=
  match h with
  | ⟨k, hk⟩ => by
      rw [hk]
      apply Nat.pow_pos
      decide

-- Layout Helper
def mkLayout {α : Type} (size align : Nat) (h_pow2 : IsPowerOfTwo align) (h_aligned : size % align = 0) : Layout α := {
  size := size
  align := align
  valid_alignment := {
    is_power_of_two := h_pow2
    is_positive := pow2_is_positive _ h_pow2
  }
  size_aligned := h_aligned
}

-- Primitive Layout Instances

-- U8 / I8 (Size 1, Align 1)
instance : Layout U8 := mkLayout 1 1 ⟨0, by decide⟩ (by decide)
instance : Layout I8 := mkLayout 1 1 ⟨0, by decide⟩ (by decide)

-- U16 / I16
instance : Layout U16 := mkLayout 2 u16_align u16_align_pow2 u16_size_aligned
instance : Layout I16 := mkLayout 2 i16_align i16_align_pow2 i16_size_aligned

-- U32 / I32
instance : Layout U32 := mkLayout 4 u32_align u32_align_pow2 u32_size_aligned
instance : Layout I32 := mkLayout 4 i32_align i32_align_pow2 i32_size_aligned

-- U64 / I64
instance : Layout U64 := mkLayout 8 u64_align u64_align_pow2 u64_size_aligned
instance : Layout I64 := mkLayout 8 i64_align i64_align_pow2 i64_size_aligned

-- U128 / I128
instance : Layout U128 := mkLayout 16 u128_align u128_align_pow2 u128_size_aligned
instance : Layout I128 := mkLayout 16 i128_align i128_align_pow2 i128_size_aligned

-- Usize / Isize
instance : Layout Usize := mkLayout usize_size usize_align usize_align_pow2 usize_size_aligned
instance : Layout Isize := mkLayout usize_size isize_align isize_align_pow2 isize_size_aligned

end Hermes.Std.Platform
