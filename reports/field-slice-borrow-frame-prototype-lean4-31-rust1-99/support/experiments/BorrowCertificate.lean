import Lean
namespace BorrowPrototype
abbrev Byte := Fin 256
def add8 (a b : Byte) : Byte := ⟨(a.val + b.val) % 256, Nat.mod_lt _ (by decide)⟩
structure Pair where
 left : Byte
 right : Byte
 deriving DecidableEq, Repr
inductive Authority where
 | root
 | splitFields
 | sliceCell (index : Fin 2)
 deriving DecidableEq, Repr
structure FieldState where
 pair : Pair
 authority : Authority
 deriving DecidableEq, Repr
inductive FieldOp where
 | split
 | writeLeft (delta : Byte)
 | writeRight (delta : Byte)
 | restore
 deriving DecidableEq, Repr
def fieldStep (s : FieldState) : FieldOp → Option FieldState
 | .split => if s.authority = .root then some {s with authority := .splitFields} else none
 | .writeLeft d => if s.authority = .splitFields then
    some {s with pair := {s.pair with left := add8 s.pair.left d}} else none
 | .writeRight d => if s.authority = .splitFields then
    some {s with pair := {s.pair with right := add8 s.pair.right d}} else none
 | .restore => if s.authority = .splitFields then some {s with authority := .root} else none
def runField : List FieldOp → FieldState → Option FieldState
 | [], s => some s
 | op::ops, s => (fieldStep s op).bind (runField ops)
def capturedField (p : Pair) (d : Byte) : Pair := {p with left := add8 p.left d}
def fieldCertificate (d : Byte) : List FieldOp := [.split, .writeLeft d, .restore]
theorem field_correspondence (p : Pair) (d : Byte) (entry : Authority)
 (entryOwn : entry = .root) :
 runField (fieldCertificate d) ⟨p,entry⟩ = some ⟨capturedField p d,.root⟩ := by
 subst entry
 rfl
theorem field_frame (p : Pair) (d : Byte) : (capturedField p d).right = p.right := rfl
theorem field_permission_restored (p : Pair) (d : Byte) :
 runField (fieldCertificate d) ⟨p,.root⟩ = some ⟨capturedField p d,.root⟩ := rfl

abbrev Slice2 := Fin 2 → Byte
def updateCell (xs : Slice2) (i : Fin 2) (d : Byte) : Slice2 :=
 fun j => if j = i then add8 (xs j) d else xs j
def capturedSlice (xs : Slice2) (index : Nat) (d : Byte) : Option Slice2 :=
 if h : index < 2 then some (updateCell xs ⟨index,h⟩ d) else none
def sliceBorrow (entry : Authority) (index : Fin 2) : Option Authority :=
 if entry = .root then some (.sliceCell index) else none
def sliceWrite (a : Authority) (xs : Slice2) (index : Fin 2) (d : Byte) :
 Option (Slice2 × Authority) :=
 if a = .sliceCell index then some (updateCell xs index d,.root) else none
def transformedSlice (entry : Authority) (xs : Slice2) (index : Nat) (d : Byte) :
 Option (Slice2 × Authority) :=
 if h : index < 2 then (sliceBorrow entry ⟨index,h⟩).bind (fun a => sliceWrite a xs ⟨index,h⟩ d)
 else none
theorem slice_correspondence (xs : Slice2) (index : Nat) (d : Byte) (entry : Authority)
 (entryOwn : entry = .root) :
 transformedSlice entry xs index d = (capturedSlice xs index d).map (fun ys => (ys,.root)) := by
 subst entry
 unfold transformedSlice capturedSlice
 split
 · simp [sliceBorrow, sliceWrite]
 · rfl
theorem slice_frame (xs : Slice2) (i j : Fin 2) (d : Byte) (separate : j ≠ i) :
 updateCell xs i d j = xs j := by simp [updateCell, separate]
theorem slice_oob (xs : Slice2) (index : Nat) (d : Byte) (outside : ¬ index < 2) :
 transformedSlice .root xs index d = none := by simp [transformedSlice, outside]
theorem wrong_authority (xs : Slice2) (i : Fin 2) (d : Byte) :
 sliceWrite .root xs i d = none := rfl
#print axioms field_correspondence
#print axioms field_frame
#print axioms slice_correspondence
#print axioms slice_frame
#print axioms slice_oob
#print axioms wrong_authority
def expectedNativeSourceHash : String := "996f70f543d0bad10d09464b2f4f8df566bc556c8a8f0fdcc8c4b9f796f7797b"
def actualNativeSourceHash : String := "996f70f543d0bad10d09464b2f4f8df566bc556c8a8f0fdcc8c4b9f796f7797b"
theorem fieldConsumerAccepted : expectedNativeSourceHash = actualNativeSourceHash ∧
 (∀ p d entry, entry = Authority.root →
 runField (fieldCertificate d) ⟨p,entry⟩ = some ⟨capturedField p d,.root⟩) :=
 ⟨rfl, field_correspondence⟩
theorem sliceConsumerAccepted : expectedNativeSourceHash = actualNativeSourceHash ∧
 (∀ xs index d entry, entry = Authority.root →
 transformedSlice entry xs index d = (capturedSlice xs index d).map (fun ys => (ys,.root))) :=
 ⟨rfl, slice_correspondence⟩
#print fieldConsumerAccepted
#print sliceConsumerAccepted
#print axioms fieldConsumerAccepted
#print axioms sliceConsumerAccepted
end BorrowPrototype


open BorrowPrototype
-- Literal term emitted from the consumer-checked data-only plan.
def providedPlan (delta : Byte) : List FieldOp := [.split, .writeLeft delta, .restore]
theorem providedCertificate (p : Pair) (delta : Byte) (entry : Authority)
 (entryOwn : entry = .root) :
 runField (providedPlan delta) ⟨p,entry⟩ = some ⟨capturedField p delta,.root⟩ :=
 field_correspondence p delta entry entryOwn
#print axioms providedCertificate
