/-
Probe: how do `axiom`, `opaque`, and explicit parameters differ for an
uninterpreted Sail extern (e.g. `match_reservation`, `load_reservation`) with
respect to `#print axioms`?  Standalone; imports only Init.
Run: <lean-4.34.1>/bin/lean ExternEncodings.lean   (expected: exit 0, no output)
-/

-- A stand-in for a Sail monad: state over a register file.
abbrev M := StateM (Nat → Nat)

-- (1) As in sail-riscv handwritten_support/RiscvExtras.lean: axioms.
axiom match_reservation_ax : UInt64 → Bool
axiom load_reservation_ax : UInt64 → Nat → M Unit

noncomputable def sc_ax (a : UInt64) : M Bool := do
  if match_reservation_ax a then pure true else pure false

theorem sc_ax_total (a : UInt64) (s : Nat → Nat) :
    ((sc_ax a).run s).2 = s := by
  unfold sc_ax; cases match_reservation_ax a <;> rfl

-- (2) Same uninterpreted meaning, but `opaque` (needs Inhabited).
opaque match_reservation_op : UInt64 → Bool
opaque load_reservation_op : UInt64 → Nat → M Unit

def sc_op (a : UInt64) : M Bool := do
  if match_reservation_op a then pure true else pure false

theorem sc_op_total (a : UInt64) (s : Nat → Nat) :
    ((sc_op a).run s).2 = s := by
  unfold sc_op; cases match_reservation_op a <;> rfl

-- An opaque monadic extern is a fixed-but-unknown state transformer: nothing can be
-- proved about its effect on state (same as the axiom version).
-- (3) Explicit parameter (what a backend "extern as parameter/typeclass field" would give):
structure Platform where
  match_reservation : UInt64 → Bool
  load_reservation : UInt64 → Nat → M Unit

def sc_par (P : Platform) (a : UInt64) : M Bool := do
  if P.match_reservation a then pure true else pure false

theorem sc_par_total (P : Platform) (a : UInt64) (s : Nat → Nat) :
    ((sc_par P a).run s).2 = s := by
  unfold sc_par; cases P.match_reservation a <;> rfl

/-- info: 'sc_ax_total' depends on axioms: [match_reservation_ax] -/
#guard_msgs in #print axioms sc_ax_total
/-- info: 'sc_op_total' does not depend on any axioms -/
#guard_msgs in #print axioms sc_op_total
/-- info: 'sc_par_total' does not depend on any axioms -/
#guard_msgs in #print axioms sc_par_total

-- Instantiating the parametric version with a *stateful* reservation is possible only
-- if the platform state lives in M's state; with `opaque`/`axiom` it is impossible to
-- relate load_reservation and match_reservation at all.
