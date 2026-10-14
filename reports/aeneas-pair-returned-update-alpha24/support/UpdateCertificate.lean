import CapturedFuns
open Aeneas Aeneas.Std Result
namespace ActualBorrowCertificate
abbrev Pair := Std.U8 × Std.U8
abbrev Heap := Nat → Option Pair
def replace (h : Heap) (root : Nat) (p : Pair) : Heap :=
 fun j => if j = root then some p else h j
structure State where
 heap : Heap
 root : Nat
 input : Std.U8
 canWriteRoot : Bool
 returnInitialized : Bool
 temporaryLive : Bool
 temporary : Option Std.U8
 events : List String
def actualLLBCUpdate (s : State) : Option State := do
 if !s.canWriteRoot then none else do
  let pair ← s.heap s.root
  -- Exact selected operation order: unit; live; copy; field write(move); dead; unit; return.
  let s := { s with returnInitialized := true,
                    events := s.events ++ ["unit:0", "live:3", "copy:2:3"] }
  let s := { s with temporaryLive := true, temporary := some s.input }
  let value ← s.temporary
  let s := { s with heap := replace s.heap s.root (pair.1, value), temporary := none,
                    events := s.events ++ ["write:deref-1:field-1:move-3"] }
  pure { s with temporaryLive := false, temporary := none, returnInitialized := true,
                events := s.events ++ ["dead:3", "unit:0", "return:0"] }
def expectedState (s : State) (p : Pair) : State :=
 { s with heap := replace s.heap s.root (p.1, s.input), returnInitialized := true,
          temporaryLive := false, temporary := none,
          events := s.events ++ ["unit:0", "live:3", "copy:2:3", "write:deref-1:field-1:move-3", "dead:3", "unit:0", "return:0"] }
-- Independent selected source-place model: assignment to second field of a valid pair root.
-- The Rust-to-this-model interpretation is assumed, not certified by this definition.
def sourcePlaceUpdate (heap : Heap) (root : Nat) (x : Std.U8) : Option Heap := do
 let old ← heap root
 pure (replace heap root (old.1, x))
theorem source_place_heap (s : State) (p : Pair) (entryRoot : s.heap s.root = some p) :
 sourcePlaceUpdate s.heap s.root s.input = some (expectedState s p).heap := by
 simp [sourcePlaceUpdate, expectedState, entryRoot]
theorem choose_emitted (b : Bool) (x y : Std.U8) :
 CertificateProbe.choose b x y = ok (if b then x else y) := by
 cases b <;> rfl
theorem update_emitted (p : Pair) (x : Std.U8) :
 CertificateProbe.update_second p x = ok (p.1, x) := by
 cases p; rfl
theorem update_state (s : State) (p : Pair)
 (entryRoot : s.heap s.root = some p) (exclusivePermission : s.canWriteRoot = true) :
 actualLLBCUpdate s = some (expectedState s p) := by
 simp [actualLLBCUpdate, expectedState, entryRoot, exclusivePermission, List.append_assoc]
theorem update_root (s : State) (p : Pair) :
 (expectedState s p).heap s.root = some (p.1, s.input) := by
 simp [expectedState, replace]
theorem update_frame (s : State) (p : Pair) (j : Nat) (outside : j ≠ s.root) :
 (expectedState s p).heap j = s.heap j := by
 simp [expectedState, replace, outside]
theorem returned_update_correspondence (s : State) (p : Pair)
 (entryRoot : s.heap s.root = some p) (exclusivePermission : s.canWriteRoot = true) :
 actualLLBCUpdate s = some (expectedState s p) ∧
 CertificateProbe.update_second p s.input = ok (p.1, s.input) ∧
 (expectedState s p).heap s.root = some (p.1, s.input) ∧
 ∀ j, j ≠ s.root → (expectedState s p).heap j = s.heap j :=
 ⟨update_state s p entryRoot exclusivePermission, update_emitted p s.input,
  update_root s p, fun j h => update_frame s p j h⟩
theorem denied (s : State) (h : s.canWriteRoot = false) : actualLLBCUpdate s = none := by
 simp [actualLLBCUpdate, h]
theorem missing_root (s : State) (h : s.heap s.root = none) : actualLLBCUpdate s = none := by
 simp [actualLLBCUpdate, h]
#print axioms choose_emitted
#print axioms update_emitted
#print axioms update_state
#print axioms returned_update_correspondence
#print axioms source_place_heap
#print axioms denied
#print axioms missing_root
end ActualBorrowCertificate
