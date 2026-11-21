import ToyReprLower.Lemmas

/-!
# Typed reads are monotone

`BytesLe` refinement implies refinement for every typed integer or pointer read at every offset
and width (the uses of a byte-level value, including reads of bytes that were moved by a
byte-level transmute, which in this toy are reads of the same bytes at another type).
-/

namespace Toy.ReprLower

theorem bytesLe_length {x y : List AByte} (h : BytesLe x y) : x.length = y.length :=
  ((bytesLeb_iff_getD x y).1 h).1

theorem bytesLe_getD {x y : List AByte} (h : BytesLe x y) (i : Nat) :
    (x.getD i .uninit).leb (y.getD i .uninit) = true := by
  have ⟨hl, hp⟩ := (bytesLeb_iff_getD x y).1 h
  by_cases hi : i < x.length
  · exact hp i hi
  · have h1 : x.getD i .uninit = .uninit := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i)]
    rw [h1]; exact AByte.uninit_leb _

theorem bytesLe_seg {x y : List AByte} (h : BytesLe x y) (o w : Nat) :
    BytesLe (seg x o w) (seg y o w) := by
  unfold BytesLe
  rw [bytesLeb_iff_getD]
  refine ⟨by simp [length_seg, bytesLe_length h], fun k _ => ?_⟩
  rw [getD_seg, getD_seg]
  split
  · exact bytesLe_getD h _
  · rfl

theorem allInit_datas_of_bytesLeb {xs ys : List AByte} (h : bytesLeb xs ys = true)
    (hi : allInit xs = true) : allInit ys = true ∧ datas xs = datas ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [bytesLeb]
  | cons a as ih =>
    cases ys with
    | nil => simp [bytesLeb] at h
    | cons b bs =>
      simp only [bytesLeb, Bool.and_eq_true] at h
      simp only [allInit, List.all_cons, Bool.and_eq_true] at hi
      have ⟨h1, h2⟩ := ih h.2 hi.2
      simp only [allInit, datas, List.all_cons, List.map_cons, Bool.and_eq_true, List.cons.injEq] at h1 h2 ⊢
      refine ⟨⟨?_, h1⟩, ?_, h2⟩ <;>
      cases a <;> cases b <;> simp_all [AByte.leb, AByte.isInit, AByte.data]

theorem eq_of_bytesLeb_of_fragsFrom {xs ys : List AByte} {p k : Nat}
    (h : bytesLeb xs ys = true) (hf : fragsFrom p k xs = true) : xs = ys := by
  induction xs generalizing ys k with
  | nil => cases ys <;> simp_all [bytesLeb]
  | cons a as ih =>
    cases ys with
    | nil => simp [bytesLeb] at h
    | cons b bs =>
      simp only [bytesLeb, Bool.and_eq_true] at h
      cases a with
      | uninit => simp [fragsFrom] at hf
      | bits _ => simp [fragsFrom] at hf
      | ptrFrag d q i =>
        simp only [fragsFrom, Bool.and_eq_true] at hf
        rw [ih h.2 hf.2]
        cases b <;> simp_all [AByte.leb]

theorem ptrProv_of_bytesLeb {xs ys : List AByte} {p : Nat} (h : bytesLeb xs ys = true)
    (hp : ptrProv xs = some p) : ptrProv ys = some p := by
  unfold ptrProv at hp
  split at hp
  · split at hp
    · rename_i hf
      cases hp
      rename_i q hq
      rw [← eq_of_bytesLeb_of_fragsFrom h hf]
      simp [ptrProv, hq, hf]
    · cases hp
  · cases hp

/-- **Typed reads are monotone.** If `y` is at least as defined as `x` (`BytesLe x y`), then for
every offset `off` and width `w`, the typed integer read and the typed pointer read of `y` are
at least as defined as those of `x` (`OutLe`, with UB as the least defined outcome). -/
theorem typedReads_mono_of_bytesLe {x y : List AByte} (h : BytesLe x y) (off w : Nat) :
    OutLe (readInt off w x) (readInt off w y) ∧ OutLe (readPtr off w x) (readPtr off w y) := by
  have hs := bytesLe_seg h off w
  have hl : (seg x off w).length = (seg y off w).length := bytesLe_length hs
  unfold readInt readPtr
  by_cases hc : (seg x off w).length = w ∧ allInit (seg x off w) = true
  · have ⟨hiy, hd⟩ := allInit_datas_of_bytesLeb hs hc.2
    have hcy : (seg y off w).length = w ∧ allInit (seg y off w) = true := ⟨hl ▸ hc.1, hiy⟩
    rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hcy, ite_eq_left hcy, hd]
    refine ⟨by simp [OutLe, Val.leb], ?_⟩
    cases hpx : ptrProv (seg x off w) with
    | none => simp [OutLe, Val.leb]
    | some p => simp [OutLe, Val.leb, ptrProv_of_bytesLeb hs hpx]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact ⟨trivial, trivial⟩

end Toy.ReprLower
