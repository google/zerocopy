module

public import Kraken.ToBytes
public import Std.Data.ExtHashMap

public section

/-!
# Kraken Memory Access

This module provides definitions and basic theorems about individual
memory-accessing operations supported by Kraken semantics. Compound structures
defined for programs, even if common, belong elsewhere. This file does not
depend on separation-logic definitions.
-/

open Std
open Std.ExtHashMap
open List

def List.allSome {α} (l : List (Option α)) : Option (List α) := l.mapM id

abbrev Mem (w) := ExtHashMap (BitVec w) UInt8

def Mem.loadBytes {w} (m : Mem w) (a : BitVec w) (n : Nat) : Option (List UInt8) :=
  ((List.range n).map (fun i => m.get? (a + .ofNat _ i))).allSome

def Mem.loadInt {w} (m : Mem w) (a : BitVec w) (n : Nat) : Option Int :=
  (loadBytes m a n).map Int.ofBytes


-- JP: can't use the Mem abbreviation here because it resolves to List.Mem (the
-- predicate)
def List.At {w} (bs : List UInt8) (a : BitVec w) : ExtHashMap (BitVec w) UInt8 :=
  .ofList (bs.mapIdx (fun i b => (a + .ofNat w i, b)))

def Mem.storeBytes {w} (m : Mem w) (a : BitVec w) (bs : List UInt8) : Mem w :=
  m.union (bs.At a)

def Mem.storeInt {w} (m : Mem w) (a : BitVec w) (n : Nat) (v : Int) : Mem w :=
  storeBytes m a (Int.toBytes n v)


@[expose] def UInt64.At {w} (val : UInt64) (a : BitVec w) : Mem w :=
  val.toBytes.At a

@[expose] def UInt32.At {w} (val : UInt32) (a : BitVec w) : Mem w :=
  val.toBytes.At a

@[expose] def UInt16.At {w} (val : UInt16) (a : BitVec w) : Mem w :=
  val.toBytes.At a

@[expose] def UInt8.At {w} (val : UInt8) (a : BitVec w) : Mem w :=
  val.toBytes.At a


theorem mem_At_iff {w} (bs : List UInt8) (a : BitVec w) (k : BitVec w) :
    k ∈ bs.At a ↔ ∃ i < bs.length, k = a + .ofNat w i := by
  simp only [List.At, mem_ofList, List.elem_iff, mem_map, mem_mapIdx, Prod.mk.injEq, exists_and_right, exists_eq_right, Prod.exists]; grind

theorem get?_At {w} (bs : List UInt8) (a : BitVec w) (p : BitVec w) (hw : bs.length ≤ 2 ^ w) :
    (bs.At a)[p]? = bs[(p - a).toNat]? := by
  if h : (p - a).toNat < bs.length then
    rw [getElem?_eq_getElem h, List.At]
    have h_self : .ofNat w (p - a).toNat = p - a := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt _))
    have hp : p = a + .ofNat w (p - a).toNat := by rw [h_self, BitVec.add_comm, BitVec.sub_add_cancel]
    conv => lhs; rw [hp]
    have h_mem : ⟨a + .ofNat w (p - a).toNat, bs[(p - a).toNat]⟩ ∈ bs.mapIdx (fun i b => (a + .ofNat w i, b)) := by
      rw [mem_mapIdx]; exact ⟨_, h, rfl⟩
    apply getElem?_ofList_of_mem (k_beq := by simp) _ h_mem
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_mapIdx] at hi hj
    have hi_w : i < 2 ^ w := Nat.lt_of_lt_of_le hi hw
    have hj_w : j < 2 ^ w := Nat.lt_of_lt_of_le hj hw
    simp only [List.getElem_mapIdx, beq_eq_false_iff_ne, Ne] at *
    intro h_eq
    have h_cancel := congrArg (fun x => (x - a).toNat) h_eq
    simp [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi_w, Nat.mod_eq_of_lt hj_w] at h_cancel
    omega
  else
    rw [ExtHashMap.getElem?_eq_none, List.getElem?_eq_none (by omega)]; rw [mem_At_iff]; rintro ⟨j, hj, rfl⟩; apply h
    simp (discharger := omega) [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega

theorem get?_At_idx {w} (bs : List UInt8) (a : BitVec w) (i : Nat) (hi : i < 2 ^ w) (hw : bs.length ≤ 2 ^ w) :
    (bs.At a).get? (a + .ofNat w i) = bs[i]? := by
  simpa [get?_eq_getElem?, BitVec.add_comm a, BitVec.add_sub_cancel,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using get?_At bs a (a + .ofNat w i) hw

theorem List.disjoint_At_append {w} (bs1 bs2 : List UInt8) (a : BitVec w)
    (h_len : bs1.length + bs2.length ≤ 2 ^ w) :
    (bs1.At a).inter (bs2.At (a + .ofNat w bs1.length)) = ∅ := by
  rw [eq_empty_iff_forall_not_mem]; intro k
  rw [inter_eq, mem_inter_iff]; rintro ⟨h1, h2⟩
  rw [mem_At_iff] at h1 h2; rcases h1 with ⟨i, hi, rfl⟩; rcases h2 with ⟨j, hj, h_eq2⟩
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h_eq2
  have h_cancel := congrArg (fun x => (x - a).toNat) h_eq2
  rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h_cancel
  omega

theorem List.At_append {w} (bs1 bs2 : List UInt8) (a : BitVec w)
    (h_len : bs1.length + bs2.length ≤ 2 ^ w) :
    (bs1 ++ bs2).At a = (bs1.At a).union (bs2.At (a + .ofNat w bs1.length)) := by
  have := @List.length_append _ bs1 bs2
  apply ExtHashMap.ext_getElem?; intro k
  simp (discharger := omega) only [get?_At, union_eq, getElem?_union, List.getElem?_append]; split
  · next h_lt =>
    have h_not2 : ¬ k ∈ bs2.At (a + .ofNat w bs1.length) := by
      intro h2
      have h_disj := eq_empty_iff_forall_not_mem.mp (List.disjoint_At_append bs1 bs2 a h_len) k
      apply h_disj
      rw [inter_eq, mem_inter_iff, mem_At_iff]
      refine ⟨⟨(k - a).toNat, h_lt, ?_⟩, h2⟩
      have h_self : .ofNat w (k - a).toNat = k - a := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt (BitVec.isLt _))
      rw [h_self, BitVec.add_comm, BitVec.sub_add_cancel]
    have h_none : bs2[(k - (a + .ofNat w bs1.length)).toNat]? = none :=
      (get?_At bs2 _ _ (by omega)).symm.trans (ExtHashMap.getElem?_eq_none h_not2)
    simp only [h_none, Option.none_or]
  · next h_ge =>
    have h_bs1 : bs1[(k - a).toNat]? = none := List.getElem?_eq_none (by omega)
    have h_idx : (k - (a + .ofNat w bs1.length)).toNat = (k - a).toNat - bs1.length := by
      rw [← BitVec.sub_sub]
      have h_le : .ofNat w bs1.length ≤ k - a := by
        rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [BitVec.toNat_sub_of_le h_le]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [h_bs1, Option.or_none, h_idx]
