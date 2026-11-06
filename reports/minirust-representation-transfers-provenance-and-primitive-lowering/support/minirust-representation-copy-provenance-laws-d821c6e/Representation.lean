import Std

namespace Representation

inductive Byte (P : Type) where
  | uninit
  | init (data : Nat) (provenance : Option P)
  deriving DecidableEq

def Below : Byte P → Byte P → Prop
  | .uninit, _ => True
  | .init d none, .init e _ => d = e
  | .init d (some p), .init e (some q) => d = e ∧ p = q
  | _, _ => False

theorem below_refl (b : Byte P) : Below b b := by
  cases b with
  | uninit => trivial
  | init d p => cases p <;> simp [Below]

def strip : Byte P → Byte P
  | .uninit => .uninit
  | .init d _ => .init d none

theorem strip_below (b : Byte P) : Below (strip b) b := by
  cases b <;> simp [strip, Below]

def mask (keep : Fin n → Bool) (v : Fin n → Byte P) : Fin n → Byte P :=
  fun i => if keep i then v i else .uninit

theorem mask_below (keep : Fin n → Bool) (v : Fin n → Byte P) :
    ∀ i, Below (mask keep v i) (v i) := by
  intro i
  simp only [mask]
  split
  · exact below_refl _
  · trivial

theorem mask_idempotent (keep : Fin n → Bool) (v : Fin n → Byte P) :
    mask keep (mask keep v) = mask keep v := by
  funext i
  simp only [mask]
  split <;> rfl

theorem mask_preserves_kept (keep : Fin n → Bool) (v : Fin n → Byte P)
    (i : Fin n) (h : keep i = true) :
    mask keep v i = v i := by simp [mask, h]

def decodeNat : Byte P → Option Nat
  | .uninit => none
  | .init d _ => some d

def encodeNat (d : Nat) : Byte P := .init d none

theorem scalar_roundtrip (d : Nat) :
    decodeNat (encodeNat d : Byte P) = some d := rfl

theorem scalar_deflation (b : Byte P) (d : Nat)
    (h : decodeNat b = some d) : Below (encodeNat d) b := by
  cases b with
  | uninit => simp [decodeNat] at h
  | init e p =>
    simp [decodeNat] at h
    subst e
    cases p <;> simp [encodeNat, Below]

-- Counterexample: a typed payload observation forgets initialized padding,
-- but an untyped/byte observation can distinguish the storage states.
def original : Fin 2 → Byte Nat := fun i =>
  if i.val = 0 then .init 7 none else .init 99 none
def payloadOnly : Fin 2 → Bool := fun i => i.val == 0

theorem padding_observer_distinguishes :
    decodeNat (original 1) = some 99 ∧
      decodeNat (mask payloadOnly original 1) = none := by decide

#print axioms below_refl
#print axioms strip_below
#print axioms mask_below
#print axioms mask_idempotent
#print axioms mask_preserves_kept
#print axioms scalar_roundtrip
#print axioms scalar_deflation
#print axioms padding_observer_distinguishes

end Representation

