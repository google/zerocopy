import Lean
set_option linter.unusedSimpArgs false
namespace UnsafeApiCertificate
abbrev Byte := Fin 256
inductive Outcome where
 | ok (value : Option Bool)
 | bad
 deriving DecidableEq, Repr
inductive State where
 | entry (byte : Byte)
 | cast (byte : Byte)
 | done (outcome : Outcome)
 deriving DecidableEq, Repr
-- The transmute validity rule is interpreted from the explicitly pinned Rust contract.
def castResult (byte : Byte) : Outcome :=
 if byte.val=0 then .ok (some false) else if byte.val=1 then .ok (some true) else .bad
def guarded (threshold : Nat) (byte : Byte) : Outcome :=
 if byte.val < threshold then castResult byte else .ok none
inductive Step (threshold : Nat) : State → State → Prop where
 | enterCast (byte : Byte) (h : byte.val < threshold) : Step threshold (.entry byte) (.cast byte)
 | reject (byte : Byte) (h : ¬byte.val < threshold) : Step threshold (.entry byte) (.done (.ok none))
 | cast (byte : Byte) : Step threshold (.cast byte) (.done (castResult byte))
def expected (byte : Byte) : Outcome :=
 if byte.val=0 then .ok (some false) else if byte.val=1 then .ok (some true) else .ok none
theorem all_inputs (byte : Byte) : guarded 2 byte = expected byte := by
 by_cases h0 : byte.val=0
 · simp [guarded, castResult, expected, h0]
 · by_cases h1 : byte.val=1
   · simp [guarded, castResult, expected, h1]
   · have h : ¬byte.val < 2 := by omega
     simp [guarded, castResult, expected, h0, h1, h]
theorem no_bad (byte : Byte) : guarded 2 byte ≠ .bad := by
 rw [all_inputs]
 by_cases h0 : byte.val=0
 · simp [expected, h0]
 · by_cases h1 : byte.val=1
   · simp [expected, h0, h1]
   · simp [expected, h0, h1]
def invariant : State → Prop
 | .entry _ => True
 | .cast byte => byte.val=0 ∨ byte.val=1
 | .done outcome => outcome ≠ .bad
theorem entry_covers_all (byte : Byte) : invariant (.entry byte) := True.intro
theorem step_preserves {s t : State} (h : Step 2 s t) (hs : invariant s) : invariant t := by
 cases h with
 | enterCast byte h => change byte.val=0 ∨ byte.val=1; omega
 | reject byte _ => intro h; cases h
 | cast byte =>
   change byte.val=0 ∨ byte.val=1 at hs
   rcases hs with h0|h1
   · simp [invariant, castResult, h0]
   · simp [invariant, castResult, h1]
-- Removing or widening the guard causes a first bad prefix on an otherwise valid u8.
def two : Byte := ⟨2, by decide⟩
theorem wider_guard_bad : guarded 3 two = .bad := by decide
theorem unguarded_bad : castResult two = .bad := by decide
-- A model restricted to zero/one masks that changed implementation's bad native input.
theorem narrowed_model_hides (x : Fin 2) : guarded 3 ⟨x.val, by omega⟩ = expected ⟨x.val, by omega⟩ := by
 have h : x.val<2 := x.isLt
 by_cases h0 : x.val=0
 · simp [guarded, castResult, expected, h0]
 · have h1 : x.val=1 := by omega
   simp [guarded, castResult, expected, h1]
#print axioms all_inputs
#print axioms no_bad
#print axioms entry_covers_all
#print axioms step_preserves
#print axioms wider_guard_bad
#print axioms narrowed_model_hides
end UnsafeApiCertificate
