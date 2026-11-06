import Std

namespace Bridge

def BadReflects (lower : S → T) (badS : S → Prop) (badT : T → Prop) : Prop :=
  ∀ s, badS s → badT (lower s)

theorem safety_transfer (lower : S → T) (badS : S → Prop) (badT : T → Prop)
    (reflection : BadReflects lower badS badT) (target_safe : ∀ s, ¬ badT (lower s)) :
    ∀ s, ¬ badS s := by
  intro s hs
  exact target_safe s (reflection s hs)

-- This toy erasure records exactly which distinctions it forgets.
structure Cell where
  value : Nat
  initialized : Bool
  tagLive : Bool
  deriving DecidableEq

def erase (s : Cell) : Nat := s.value
def concreteBad (s : Cell) : Prop :=
  s.initialized = false ∨ s.value > 1 ∨ s.tagLive = false
def abstractBad (_ : Nat) : Prop := False

theorem invalid_bool_erasure :
    ¬ BadReflects erase concreteBad abstractBad := by
  intro h
  have hx := h ⟨2, true, true⟩ (by simp [concreteBad])
  exact hx

theorem invalid_tag_erasure :
    ¬ BadReflects erase concreteBad abstractBad := by
  intro h
  have hx := h ⟨0, true, false⟩ (by simp [concreteBad])
  exact hx

-- An interval split theorem has explicit range and arithmetic hypotheses.
theorem split_disjoint (base count mid i : Nat) (hm : mid ≤ count)
    (hl : base ≤ i ∧ i < base + mid) :
    ¬ (base + mid ≤ i ∧ i < base + count) := by omega

theorem split_cover (base count mid i : Nat) (hm : mid ≤ count) :
    (base ≤ i ∧ i < base + count) ↔
      ((base ≤ i ∧ i < base + mid) ∨
       (base + mid ≤ i ∧ i < base + count)) := by omega

-- This general linking schema assumes, rather than manufactures, the concrete
-- boundary invariant and the behavior relation for every admitted client.
theorem contextual_link
    (Client : Type) (admitted : Client → Prop)
    (concreteBadRun : Client → Prop) (modelBadRun : Client → Prop)
    (functionalResult : Client → Prop)
    (reflects : ∀ c, admitted c → concreteBadRun c → modelBadRun c)
    (modelSafe : ∀ c, admitted c → ¬ modelBadRun c)
    (resultTransport : ∀ c, admitted c → ¬ concreteBadRun c → functionalResult c) :
    ∀ c, admitted c → ¬ concreteBadRun c ∧ functionalResult c := by
  intro c hc
  have hs : ¬ concreteBadRun c := fun hb => modelSafe c hc (reflects c hc hb)
  exact ⟨hs, resultTransport c hc hs⟩

#print axioms safety_transfer
#print axioms invalid_bool_erasure
#print axioms invalid_tag_erasure
#print axioms split_disjoint
#print axioms split_cover
#print axioms contextual_link

end Bridge

