-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import BenchmarkSuite.RuleSets
import BenchmarkSuite.KernelBVDecide
import Aesop
import Duper

/-!
# Head-to-Head Tactic Benchmark Suite on Anneal MIR Verification Conditions

Tests `omega`, `grind`, `aesop`, `duper`, `bv_decide_kernel`, and `bv_decide`
across five classes of Anneal verification conditions:
- **Class A (`#71`, `#73`):** Layout & Alignment Arithmetic (`alignUp`,
  power-of-two bitmask alignment `(x + (a - 1)) &&& ~~~(a - 1)`, struct field
  offset non-overlap).
- **Class B (`#72`):** `ByteMemory` / Allocation Frame Disjointness (quantified
  byte-range disjointness and read-over-disjoint-write frame preservation).
- **Class C (`MirLang.SpecOn`):** Coupled Existential Witness Obligations
  (`∃ retVal, eval (x + 1) = some retVal ∧ retVal > x` and `Partial` / `SpecOn`
  coupled refinement obligations).
- **Class D (`#71`):** 64-bit `BitVec` Overflow & Checked Arithmetic (unsigned
  overflow characterization, two's-complement signed addition bounds, and
  32/64-bit bitfield extraction/packing).
- **Class E (`#77`):** First-Order Relational, Set-Inclusion, and Reachability
  Lemmas (Tree Borrows ancestry propagation, Stacked Borrows permission lattice,
  and higher-order tag-footprint set disjointness).
-/

namespace BenchmarkSuite

open KernelBVDecide

-- Ensure `lean-auto` uses pure kernel reduction (`.indirectReduce`) and never
-- invokes external TPTP/SMT subprocesses during `duper` runs.
set_option auto.tptp false
set_option auto.smt false
set_option trace.auto.tptp.result false

/-!
## Class A: Layout & Alignment Arithmetic (`#71`, `#73`)
-/

/-- `#[repr(C)]` struct field byte-offset calculation. -/
@[aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def fieldEnd (off sz pad : Nat) : Nat :=
  off + sz + pad

/-- `alignUp offset align` given `rem = offset % align`. -/
@[aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def alignUpFromRem (offset align rem : Nat) : Nat :=
  if rem = 0 then offset else offset + (align - rem)

-- Problem A1: Struct field offset non-overlap (`#[repr(C)]` 3-field layout)
theorem A1_struct_field_nonoverlap_omega
    (base off0 sz0 pad0 off1 sz1 pad1 off2 sz2 total i j : Nat)
    (h_off1 : off1 = fieldEnd off0 sz0 pad0)
    (h_off2 : off2 = fieldEnd off1 sz1 pad1)
    (h_tot : fieldEnd off2 sz2 0 ≤ total)
    (hi : i < sz0) (hj : j < sz2) :
    base + off0 + i < base + off2 + j ∧ base + off2 + j < base + total := by
  unfold fieldEnd at *
  omega

theorem A1_struct_field_nonoverlap_grind_oob
    (base off0 sz0 pad0 off1 sz1 pad1 off2 sz2 total i j : Nat)
    (h_off1 : off1 = off0 + sz0 + pad0)
    (h_off2 : off2 = off1 + sz1 + pad1)
    (h_tot : off2 + sz2 ≤ total)
    (hi : i < sz0) (hj : j < sz2) :
    base + off0 + i < base + off2 + j ∧ base + off2 + j < base + total := by
  grind

theorem A1_struct_field_nonoverlap_grind_hint
    (base off0 sz0 pad0 off1 sz1 pad1 off2 sz2 total i j : Nat)
    (h_off1 : off1 = fieldEnd off0 sz0 pad0)
    (h_off2 : off2 = fieldEnd off1 sz1 pad1)
    (h_tot : fieldEnd off2 sz2 0 ≤ total)
    (hi : i < sz0) (hj : j < sz2) :
    base + off0 + i < base + off2 + j ∧ base + off2 + j < base + total := by
  grind

-- Problem A2: `alignUp offset align` bounds
-- (`offset ≤ alignUp ∧ alignUp < offset + align`)
theorem A2_alignUp_bounds_omega
    (offset align rem : Nat)
    (_h_align : 0 < align)
    (h_rem : rem < align) :
    offset ≤ alignUpFromRem offset align rem ∧
    alignUpFromRem offset align rem < offset + align := by
  unfold alignUpFromRem
  split <;> omega

theorem A2_alignUp_bounds_grind_oob
    (offset align rem : Nat)
    (h_align : 0 < align)
    (h_rem : rem < align) :
    offset ≤ (if rem == 0 then offset else offset + (align - rem)) ∧
    (if rem == 0 then offset else offset + (align - rem)) < offset + align := by
  grind

theorem A2_alignUp_bounds_grind_hint
    (offset align rem : Nat)
    (h_align : 0 < align)
    (h_rem : rem < align) :
    offset ≤ alignUpFromRem offset align rem ∧
    alignUpFromRem offset align rem < offset + align := by
  grind

-- Problem A3: Power-of-two bitmask alignment `(x + (a - 1)) &&& ~~~(a - 1)`
-- on `BitVec 64`
theorem A3_bitmask_align_bv64_kernel
    (x : BitVec 64) (h : x ≤ 0xffff_ffff_ffff_fff8#64) :
    let aligned := (x + (8#64 - 1#64)) &&& ~~~(8#64 - 1#64)
    aligned ≥ x ∧ (aligned - x < 8#64) ∧ (aligned &&& 7#64 == 0#64) := by
  bv_decide_kernel

theorem A3_bitmask_align_bv64_std
    (x : BitVec 64) (h : x ≤ 0xffff_ffff_ffff_fff8#64) :
    let aligned := (x + (8#64 - 1#64)) &&& ~~~(8#64 - 1#64)
    aligned ≥ x ∧ (aligned - x < 8#64) ∧ (aligned &&& 7#64 == 0#64) := by
  bv_decide

/-!
## Class B: `ByteMemory` / Allocation Frame Disjointness (`#72`)
-/

abbrev ByteMemory := Nat → UInt8

@[grind =]
def ByteMemory.writeByte (mem : ByteMemory) (addr : Nat) (b : UInt8) (a : Nat) : UInt8 :=
  if a == addr then b else mem a

@[aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def ByteMemory.writeWord32 (mem : ByteMemory) (base : Nat) (b0 b1 b2 b3 : UInt8) (a : Nat) : UInt8 :=
  ByteMemory.writeByte
    (ByteMemory.writeByte
      (ByteMemory.writeByte
        (ByteMemory.writeByte mem base b0)
        (base + 1) b1)
      (base + 2) b2)
    (base + 3) b3 a

@[aesop norm (rule_sets := [AnnealBench]), grind =]
theorem ByteMemory.read_writeByte_ne (mem : ByteMemory) (addr a : Nat) (b : UInt8)
    (hne : a ≠ addr) :
    ByteMemory.writeByte mem addr b a = mem a := by
  unfold ByteMemory.writeByte
  have hbeq : (a == addr) = false := beq_false_of_ne hne
  rw [hbeq]
  rfl

-- Problem B1: Quantified byte-range disjointness
-- (`∀ i < n, ∀ j < m, base1 + i ≠ base2 + j`)
theorem B1_byte_range_disjoint_omega
    (base1 n base2 m : Nat) (h_sep : base1 + n ≤ base2) :
    ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j := by
  intro i hi j hj
  omega

theorem B1_byte_range_disjoint_grind_oob
    (base1 n base2 m : Nat) (h_sep : base1 + n ≤ base2) :
    ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j := by
  grind

-- Problem B2: Reading from an updated `ByteMemory` map after a disjoint
-- 4-byte write
theorem B2_byte_memory_disjoint_read_omega
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeWord32 mem base1 b0 b1 b2 b3 (base2 + j) = mem (base2 + j) := by
  unfold ByteMemory.writeWord32 ByteMemory.writeByte
  have h0 : (base2 + j == base1) = false := beq_false_of_ne (by omega)
  have h1 : (base2 + j == base1 + 1) = false := beq_false_of_ne (by omega)
  have h2 : (base2 + j == base1 + 2) = false := beq_false_of_ne (by omega)
  have h3 : (base2 + j == base1 + 3) = false := beq_false_of_ne (by omega)
  rw [h3, h2, h1, h0]
  rfl

theorem B2_byte_memory_disjoint_read_grind_oob
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeByte
      (ByteMemory.writeByte
        (ByteMemory.writeByte
          (ByteMemory.writeByte mem base1 b0)
          (base1 + 1) b1)
        (base1 + 2) b2)
      (base1 + 3) b3 (base2 + j)
      = mem (base2 + j) := by
  grind [ByteMemory.writeByte]

theorem B2_byte_memory_disjoint_read_grind_hint
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeWord32 mem base1 b0 b1 b2 b3 (base2 + j) = mem (base2 + j) := by
  grind

theorem B2_byte_memory_disjoint_read_aesop_hint
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeWord32 mem base1 b0 b1 b2 b3 (base2 + j) = mem (base2 + j) := by
  aesop (rule_sets := [AnnealBench])
    (add safe tactic (by rw [ByteMemory.read_writeByte_ne]), safe tactic (by omega))

-- Problem B3: Quantified allocation-frame preservation over disjoint byte
-- ranges
-- Tests first-order quantifier instantiation across `h_write` and `h_disj`.
theorem B3_quantified_frame_grind_oob
    (mem mem' : ByteMemory) (base1 n base2 m : Nat)
    (h_write : ∀ a, (∀ i, i < n → a ≠ base1 + i) → mem' a = mem a)
    (h_disj : ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j) :
    ∀ j, j < m → mem' (base2 + j) = mem (base2 + j) := by
  grind

theorem B3_quantified_frame_duper_oob
    (mem mem' : ByteMemory) (base1 n base2 m : Nat)
    (h_write : ∀ a, (∀ i, i < n → a ≠ base1 + i) → mem' a = mem a)
    (h_disj : ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j) :
    ∀ j, j < m → mem' (base2 + j) = mem (base2 + j) := by
  duper [*]

theorem B3_quantified_frame_aesop_oob
    (mem mem' : ByteMemory) (base1 n base2 m : Nat)
    (h_write : ∀ a, (∀ i, i < n → a ≠ base1 + i) → mem' a = mem a)
    (h_disj : ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j) :
    ∀ j, j < m → mem' (base2 + j) = mem (base2 + j) := by
  aesop (add unsafe Ne.symm)

/-!
## Class C: Coupled Existential Witness Obligations (`MirLang.SpecOn`)
-/

@[simp, aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def evalInc (z : Int) : Option Int :=
  some z

-- Problem C1: `∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x`
theorem C1_coupled_existential_aesop_omega (x : Int) :
    ∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x := by
  aesop (add safe tactic (by omega))

theorem C1_coupled_existential_aesop_grind (x : Int) :
    ∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x := by
  aesop (add safe tactic (by grind))

theorem C1_coupled_existential_refine_omega (x : Int) :
    ∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x := by
  refine ⟨_, rfl, by omega⟩

theorem C1_coupled_existential_refine_grind (x : Int) :
    ∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x := by
  refine ⟨_, rfl, by grind⟩

-- Problem C2: `MirLang.SpecOn` / `Partial` coupled refinement witness
-- obligation
structure SimplePartial (B : Type) where
  defined : Prop
  val : defined → B

@[simp, aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def SimplePartial.leProp (p1 p2 : SimplePartial (Int → Prop)) : Prop :=
  ∀ h2 : p2.defined, ∃ h1 : p1.defined, ∀ out, p1.val h1 out → p2.val h2 out

@[simp, aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def progSem (x : Int) : SimplePartial (Int → Prop) where
  defined := x ≥ 0
  val _ out := out = x + 1

@[simp, aesop norm unfold (rule_sets := [AnnealBench]), grind =]
def specOnNonneg (x : Int) : SimplePartial (Int → Prop) where
  defined := x ≥ 0
  val _ out := ∃ retVal : Int, some out = some retVal ∧ retVal > x ∧ retVal ≥ 1

theorem C2_spec_on_refinement_aesop_omega (x : Int) :
    SimplePartial.leProp (progSem x) (specOnNonneg x) := by
  aesop (rule_sets := [AnnealBench]) (add safe tactic (by omega))

theorem C2_spec_on_refinement_aesop_grind (x : Int) :
    SimplePartial.leProp (progSem x) (specOnNonneg x) := by
  aesop (rule_sets := [AnnealBench]) (add safe tactic (by grind))

/-!
## Class D: 64-bit `BitVec` Overflow & Checked Arithmetic (`#71`)
-/

-- Problem D1: `BitVec 64` unsigned addition overflow detection
theorem D1_uadd_overflow_iff_bv64_kernel (x y : BitVec 64) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide_kernel

theorem D1_uadd_overflow_iff_bv64_std (x y : BitVec 64) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide

-- Problem D2: `BitVec 64` two's complement signed range bounds & non-overflow
theorem D2_sadd_overflow_signed_bounds_bv64_kernel (x y : BitVec 64)
    (hx0 : BitVec.sle 0#64 x) (hx1 : BitVec.sle x 0x3fff_ffff_ffff_ffff#64)
    (hy0 : BitVec.sle 0#64 y) (hy1 : BitVec.sle y 0x3fff_ffff_ffff_ffff#64) :
    !BitVec.saddOverflow x y ∧ BitVec.sle 0#64 (x + y) := by
  bv_decide_kernel

theorem D2_sadd_overflow_signed_bounds_bv64_std (x y : BitVec 64)
    (hx0 : BitVec.sle 0#64 x) (hx1 : BitVec.sle x 0x3fff_ffff_ffff_ffff#64)
    (hy0 : BitVec.sle 0#64 y) (hy1 : BitVec.sle y 0x3fff_ffff_ffff_ffff#64) :
    !BitVec.saddOverflow x y ∧ BitVec.sle 0#64 (x + y) := by
  bv_decide

-- Problem D3: `BitVec 64` 32-bit bitfield packing & extraction round-trip
theorem D3_bitfield_extract_pack_bv64_kernel (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.zeroExtend 64 <<< 32) ||| lo.zeroExtend 64
    w.extractLsb' 0 32 = lo ∧ w.extractLsb' 32 32 = hi := by
  bv_decide_kernel

theorem D3_bitfield_extract_pack_bv64_std (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.zeroExtend 64 <<< 32) ||| lo.zeroExtend 64
    w.extractLsb' 0 32 = lo ∧ w.extractLsb' 32 32 = hi := by
  bv_decide

theorem D3_bitfield_extract_pack_bv64_grind_oob (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.zeroExtend 64 <<< 32) ||| lo.zeroExtend 64
    w.extractLsb' 0 32 = lo ∧ w.extractLsb' 32 32 = hi := by
  grind

/-!
## Class E: First-Order Relational and Reachability Lemmas (`#77`)
-/

inductive Perm where
  | Disabled
  | Frozen
  | SharedRO
  | SharedRW
  | Unique
  deriving DecidableEq, Repr

inductive PermLe : Perm → Perm → Prop where
  | refl (p : Perm) : PermLe p p
  | trans {p1 p2 p3 : Perm} : PermLe p1 p2 → PermLe p2 p3 → PermLe p1 p3
  | disabled_frozen : PermLe .Disabled .Frozen
  | frozen_sharedRO : PermLe .Frozen .SharedRO
  | sharedRO_sharedRW : PermLe .SharedRO .SharedRW
  | sharedRW_unique : PermLe .SharedRW .Unique

attribute [aesop unsafe 90% apply (rule_sets := [AnnealBench])]
  PermLe.disabled_frozen PermLe.frozen_sharedRO
  PermLe.sharedRO_sharedRW PermLe.sharedRW_unique PermLe.refl
attribute [aesop unsafe 30% apply (rule_sets := [AnnealBench])] PermLe.trans
attribute [grind →] PermLe.trans

theorem permLe_refl (p : Perm) : PermLe p p := PermLe.refl p
theorem permLe_trans {p1 p2 p3 : Perm} : PermLe p1 p2 → PermLe p2 p3 → PermLe p1 p3 := PermLe.trans
theorem permLe_disabled_frozen : PermLe .Disabled .Frozen := PermLe.disabled_frozen
theorem permLe_frozen_sharedRO : PermLe .Frozen .SharedRO := PermLe.frozen_sharedRO
theorem permLe_sharedRO_sharedRW : PermLe .SharedRO .SharedRW := PermLe.sharedRO_sharedRW
theorem permLe_sharedRW_unique : PermLe .SharedRW .Unique := PermLe.sharedRW_unique

-- Problem E1: Tree Borrows transitive tag ancestry & permission propagation
section TreeBorrows

variable (Tag Loc : Type)
variable (Parent : Tag → Tag → Prop)
variable (Ancestor : Tag → Tag → Prop)
variable (HasPerm : Tag → Loc → Perm → Prop)
variable (PreservesValid : Tag → Tag → Loc → Prop)

theorem E1_tree_borrows_ancestry_duper_oob
    (h_refl : ∀ t, Ancestor t t)
    (h_step : ∀ t1 t2 t3, Parent t1 t2 → Ancestor t2 t3 → Ancestor t1 t3)
    (h_prop : ∀ t1 t2 loc, Ancestor t1 t2 → HasPerm t1 loc .Unique →
      HasPerm t2 loc .Frozen → PreservesValid t1 t2 loc)
    (t0 t1 t2 t3 : Tag) (loc : Loc)
    (hp01 : Parent t0 t1) (hp12 : Parent t1 t2) (hp23 : Parent t2 t3)
    (hperm0 : HasPerm t0 loc .Unique) (hperm3 : HasPerm t3 loc .Frozen) :
    PreservesValid t0 t3 loc := by
  duper [*]

theorem E1_tree_borrows_ancestry_aesop_oob
    (h_refl : ∀ t, Ancestor t t)
    (h_step : ∀ t1 t2 t3, Parent t1 t2 → Ancestor t2 t3 → Ancestor t1 t3)
    (h_prop : ∀ t1 t2 loc, Ancestor t1 t2 → HasPerm t1 loc .Unique →
      HasPerm t2 loc .Frozen → PreservesValid t1 t2 loc)
    (t0 t1 t2 t3 : Tag) (loc : Loc)
    (hp01 : Parent t0 t1) (hp12 : Parent t1 t2) (hp23 : Parent t2 t3)
    (hperm0 : HasPerm t0 loc .Unique) (hperm3 : HasPerm t3 loc .Frozen) :
    PreservesValid t0 t3 loc := by
  aesop

-- With a forward-triggerable base step (`Parent t1 t2 → Ancestor t1 t2`),
-- `grind`'s E-matching cascades through the 3-step `Parent` chain.
theorem E1_tree_borrows_ancestry_grind_hint
    (h_refl : ∀ t, Ancestor t t)
    (h_step : ∀ t1 t2 t3, Parent t1 t2 → Ancestor t2 t3 → Ancestor t1 t3)
    (h_prop : ∀ t1 t2 loc, Ancestor t1 t2 → HasPerm t1 loc .Unique →
      HasPerm t2 loc .Frozen → PreservesValid t1 t2 loc)
    (t0 t1 t2 t3 : Tag) (loc : Loc)
    (hp01 : Parent t0 t1) (hp12 : Parent t1 t2) (hp23 : Parent t2 t3)
    (hperm0 : HasPerm t0 loc .Unique) (hperm3 : HasPerm t3 loc .Frozen) :
    PreservesValid t0 t3 loc := by
  have h_base : ∀ a b, Parent a b → Ancestor a b := fun a b hp => h_step a b b hp (h_refl b)
  grind

end TreeBorrows

-- Problem E2: Stacked Borrows permission lattice and stack inclusion
-- compatibility
section StackedBorrows

variable (Tag Stack : Type)
variable (InStack : Tag → Stack → Prop)
variable (TagPerm : Tag → Perm)
variable (ReadAllowed : Tag → Stack → Prop)

theorem E2_stacked_borrows_lattice_grind_hint
    (h_read : ∀ t s, InStack t s → PermLe .SharedRO (TagPerm t) → ReadAllowed t s)
    (s1 s2 : Stack) (t : Tag)
    (h_incl : ∀ x, InStack x s1 → InStack x s2)
    (h_in : InStack t s1)
    (h_perm : TagPerm t = .Unique) :
    ReadAllowed t s2 := by
  have h1 := PermLe.sharedRO_sharedRW
  have h2 := PermLe.sharedRW_unique
  grind

theorem E2_stacked_borrows_lattice_aesop_hint
    (h_read : ∀ t s, InStack t s → PermLe .SharedRO (TagPerm t) → ReadAllowed t s)
    (s1 s2 : Stack) (t : Tag)
    (h_incl : ∀ x, InStack x s1 → InStack x s2)
    (h_in : InStack t s1)
    (h_perm : TagPerm t = .Unique) :
    ReadAllowed t s2 := by
  aesop (rule_sets := [AnnealBench]) (add norm h_perm, safe [h_read, h_incl])

theorem E2_stacked_borrows_lattice_duper_hint
    (h_read : ∀ t s, InStack t s → PermLe .SharedRO (TagPerm t) → ReadAllowed t s)
    (s1 s2 : Stack) (t : Tag)
    (h_incl : ∀ x, InStack x s1 → InStack x s2)
    (h_in : InStack t s1)
    (h_perm : TagPerm t = .Unique) :
    ReadAllowed t s2 := by
  duper [*, permLe_refl, permLe_trans, permLe_sharedRO_sharedRW, permLe_sharedRW_unique]

end StackedBorrows

-- Problem E3: Higher-order set-inclusion & functional image disjointness
-- Tests where superposition (`duper`), rule search (`aesop`), and E-matching
-- (`grind`) differ on higher-order predicates and equality contraposition.
section SetDisjointness

variable (Tag Loc : Type)

theorem E3_higher_order_footprint_disjoint_duper_oob
    (S1 S2 T1 T2 : Loc → Prop)
    (Active1 Active2 : Tag → Prop)
    (proj : Tag → Loc)
    (h_sub1 : ∀ x, S1 x → T1 x)
    (h_sub2 : ∀ x, S2 x → T2 x)
    (h_disj : ∀ x, T1 x → T2 x → False)
    (h_act1 : ∀ t, Active1 t → S1 (proj t))
    (h_act2 : ∀ t, Active2 t → S2 (proj t))
    (t1 t2 : Tag) (ha1 : Active1 t1) (ha2 : Active2 t2) :
    proj t1 ≠ proj t2 := by
  duper [*]

theorem E3_higher_order_footprint_disjoint_grind_oob
    (S1 S2 T1 T2 : Loc → Prop)
    (Active1 Active2 : Tag → Prop)
    (proj : Tag → Loc)
    (h_sub1 : ∀ x, S1 x → T1 x)
    (h_sub2 : ∀ x, S2 x → T2 x)
    (h_disj : ∀ x, T1 x → T2 x → False)
    (h_act1 : ∀ t, Active1 t → S1 (proj t))
    (h_act2 : ∀ t, Active2 t → S2 (proj t))
    (t1 t2 : Tag) (ha1 : Active1 t1) (ha2 : Active2 t2) :
    proj t1 ≠ proj t2 := by
  grind

theorem E3_higher_order_footprint_disjoint_aesop_oob
    (S1 S2 T1 T2 : Loc → Prop)
    (Active1 Active2 : Tag → Prop)
    (proj : Tag → Loc)
    (h_sub1 : ∀ x, S1 x → T1 x)
    (h_sub2 : ∀ x, S2 x → T2 x)
    (h_disj : ∀ x, T1 x → T2 x → False)
    (h_act1 : ∀ t, Active1 t → S1 (proj t))
    (h_act2 : ∀ t, Active2 t → S2 (proj t))
    (t1 t2 : Tag) (ha1 : Active1 t1) (ha2 : Active2 t2) :
    proj t1 ≠ proj t2 := by
  aesop

-- Problem E4: Multi-step relational composition / witness synthesis where
-- `duper` and `grind` chain `h_step` and `h_trans` to synthesize
-- `t2 := step (step t0)` whereas `aesop` cannot decompose
-- `∀ x, Valid x → R x (step x) ∧ Valid (step x)`.
theorem E4_relational_witness_chain_duper_oob
    (R : Tag → Tag → Prop)
    (Valid : Tag → Prop)
    (step : Tag → Tag)
    (h_step : ∀ x, Valid x → R x (step x) ∧ Valid (step x))
    (h_trans : ∀ x y z, R x y → R y z → R x z)
    (t0 : Tag) (hv0 : Valid t0) :
    ∃ t2, R t0 t2 ∧ R (step t0) t2 ∧ Valid t2 := by
  duper [*]

theorem E4_relational_witness_chain_grind_oob
    (R : Tag → Tag → Prop)
    (Valid : Tag → Prop)
    (step : Tag → Tag)
    (h_step : ∀ x, Valid x → R x (step x) ∧ Valid (step x))
    (h_trans : ∀ x y z, R x y → R y z → R x z)
    (t0 : Tag) (hv0 : Valid t0) :
    ∃ t2, R t0 t2 ∧ R (step t0) t2 ∧ Valid t2 := by
  grind

end SetDisjointness

end BenchmarkSuite
