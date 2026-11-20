/-
Toy.Lens.Pair
=============

Properties of *two* lenses on the same state: one-directional
cross-independence, commuting puts, joint extensionality.  Each is a separate
`Prop` with proved positive and negative examples.
-/
import Toy.Lens.Basic

namespace Toy

namespace Lens

universe u v w x

variable {S : Type u} {A : Type v} {B : Type w}

/-! ## Definitions -/

/--
**Cross-independence, one direction.**  `PutIndep l₁ l₂` says: writing through
`l₁` leaves the view of `l₂` unchanged.

Meant to capture the *frame law* "setting field 1 does not change field 2".
It is deliberately **one-directional**: the other direction is
`PutIndep l₂ l₁`, and neither implies the other
(`xorView_fst_putIndep` versus `fst_xorView_not_putIndep`).

Terminology note: this is *not* "lens independence" in the sense of
Foster–Zeyda–Woodcock (2016, Def. 4) and the Isabelle AFP *Optics* entry
(`X ⋈ Y`), which bundles commuting puts with get-invariance in *both*
directions.  Even both directions of `PutIndep` for two very well-behaved
lenses do not give commuting puts (`derived_putComm_tight`, third instance),
so `PutIndep l₁ l₂ ∧ PutIndep l₂ l₁` is strictly weaker than `⋈`.
-/
def PutIndep (l₁ : Lens S A) (l₂ : Lens S B) : Prop :=
  ∀ s a, l₂.get (l₁.put s a) = l₂.get s

/--
**Commuting puts.**  `PutComm l₁ l₂` says: writing through `l₁` and then
through `l₂` gives the same state as writing in the other order.

Meant to capture "the two setters do not interfere with each other's
*effect on the state*", as opposed to `PutIndep`, which only speaks about the
effect on the other *view*.
-/
def PutComm (l₁ : Lens S A) (l₂ : Lens S B) : Prop :=
  ∀ s a b, l₂.put (l₁.put s a) b = l₁.put (l₂.put s b) a

/-- `PutComm` is symmetric in the two lenses. -/
theorem PutComm.symm {l₁ : Lens S A} {l₂ : Lens S B} (h : PutComm l₁ l₂) : PutComm l₂ l₁ :=
  fun s b a => (h s a b).symm

/--
**Joint extensionality.**  `JointExt l₁ l₂` says: the two views together
determine the state — two states with equal `l₁`-views and equal `l₂`-views
are equal.

Meant to capture "the record has no component other than these two fields"
(no hidden "ghost" state).  It is exactly injectivity of the pairing map
`s ↦ (l₁.get s, l₂.get s)`.
-/
def JointExt (l₁ : Lens S A) (l₂ : Lens S B) : Prop :=
  ∀ s t, l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t

/-! ## Example lenses with a hidden component -/

/-- First field of a record that also has an unprojected third ("ghost")
component of type `G`. -/
def ghostFst {G : Type x} : Lens (A × B × G) A where
  get s := s.1
  put s a := (a, s.2.1, s.2.2)

/-- Second field of a record that also has an unprojected third ("ghost")
component of type `G`. -/
def ghostSnd {G : Type x} : Lens (A × B × G) B where
  get s := s.2.1
  put s b := (s.1, b, s.2.2)

/-! ## `PutIndep`: positive and negative examples -/

/-- Positive example for `PutIndep`. -/
theorem fst_snd_putIndep : PutIndep (fst : Lens (A × B) A) (snd : Lens (A × B) B) :=
  fun _ _ => rfl

/-- Positive example for `PutIndep` (the other direction). -/
theorem snd_fst_putIndep : PutIndep (snd : Lens (A × B) B) (fst : Lens (A × B) A) :=
  fun _ _ => rfl

/-- Negative example for `PutIndep`: **aliasing**.  A lens is not independent
of itself (here: `fst` on `Bool × Bool`). -/
theorem fst_fst_not_putIndep :
    ¬ PutIndep (fst : Lens (Bool × Bool) Bool) (fst : Lens (Bool × Bool) Bool) :=
  fun h => absurd (h (false, false) true) (by decide)

/-- Negative example for `PutIndep`: writing through `fst` changes the XOR
view. -/
theorem fst_xorView_not_putIndep :
    ¬ PutIndep (fst : Lens (Bool × Bool) Bool) xorView :=
  fun h => absurd (h (false, false) true) (by decide)

/-- ... while the *other* direction holds: writing the XOR view does not
change `fst`.  So the two directions of cross-independence are genuinely
different conditions. -/
theorem xorView_fst_putIndep :
    PutIndep xorView (fst : Lens (Bool × Bool) Bool) :=
  fun _ _ => rfl

/-- Negative example for `PutIndep`: the state-twisting setter changes the
second field. -/
theorem twist_snd_not_putIndep :
    ¬ PutIndep twist (snd : Lens (Bool × Bool) Bool) :=
  fun h => absurd (h (false, false) true) (by decide)

/-- ... while the other direction holds. -/
theorem snd_twist_putIndep :
    PutIndep (snd : Lens (Bool × Bool) Bool) twist :=
  fun _ _ => rfl

/-! ## `PutComm`: positive and negative examples -/

/-- Positive example for `PutComm`. -/
theorem fst_snd_putComm : PutComm (fst : Lens (A × B) A) (snd : Lens (A × B) B) :=
  fun _ _ _ => rfl

/-- Negative example for `PutComm`: **aliasing**.  Two writes through the same
lens do not commute. -/
theorem fst_fst_not_putComm :
    ¬ PutComm (fst : Lens (Bool × Bool) Bool) (fst : Lens (Bool × Bool) Bool) :=
  fun h => absurd (h (false, false) true false) (by decide)

/-- Negative example for `PutComm`: the state-twisting setter does not commute
with writing the second field. -/
theorem twist_snd_not_putComm :
    ¬ PutComm twist (snd : Lens (Bool × Bool) Bool) :=
  fun h => absurd (h (false, false) true false) (by decide)

/-! ## `JointExt`: positive and negative examples -/

/-- Positive example for `JointExt`. -/
theorem fst_snd_jointExt : JointExt (fst : Lens (A × B) A) (snd : Lens (A × B) B) := by
  intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
  cases h₁
  cases h₂
  rfl

/-- Negative example for `JointExt`: a record with a **ghost** third
component. -/
theorem ghostFst_ghostSnd_not_jointExt :
    ¬ JointExt (ghostFst : Lens (Bool × Bool × Bool) Bool)
        (ghostSnd : Lens (Bool × Bool × Bool) Bool) :=
  fun h => absurd (h (false, false, false) (false, false, true) rfl rfl) (by decide)

/-- Negative example for `JointExt`: **aliasing**.  Two copies of `fst` never
see the second component. -/
theorem fst_fst_not_jointExt :
    ¬ JointExt (fst : Lens (Bool × Bool) Bool) (fst : Lens (Bool × Bool) Bool) :=
  fun h => absurd (h (false, false) (false, true) rfl rfl) (by decide)

end Lens

end Toy
