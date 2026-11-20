/-
Probe: single-hart LR/SC across a preemptive context switch.

Normative facts used (riscv-isa-manual @ c05f1725):
 * src/unpriv/zalrsc.adoc L94-97  [norm:sc_success_conditions]: an SC may succeed only if no store
   *from another hart* to the reservation set is observed between LR and SC (a store from the same
   hart is NOT a failure condition).
 * src/unpriv/zalrsc.adoc L23-24 [norm:sc_reservation_invalidate]: executing an SC (success or
   failure) invalidates any reservation held by this hart.
 * src/priv/machine.adoc L2667-2670 [norm:xret_clr_lr_resv]: xRET is allowed to clear an
   outstanding reservation but is not required to.
 * Sail (sail-riscv @ ec5200bd config/config.json.in L566-572) exposes the same freedoms as
   static knobs `invalidate_on_same_hart_store` and `invalidate_on_xret` (both default false).

Scenario: thread A: lr.w x,(p) ... [timer trap -> kernel switches to thread B on the SAME hart ->
B stores to p -> later trap -> kernel switches back] ... A: sc.w (p).  We ask whether the SC is
*permitted* to succeed (which would lose B's update).  Core Lean only; `decide`.
-/

namespace LrScSwitch

structure St where
  resv : Option Nat   -- reserved physical address
  mem  : Nat          -- value at p (p = 0)
deriving DecidableEq

def p : Nat := 0

def lr (s : St) : St × Nat := ({ s with resv := some p }, s.mem)
/-- dummy SC to a kernel scratch word (address 99): always kills the reservation. -/
def dummySc (s : St) : St := { s with resv := none }
/-- xRET (sret) — implementation may or may not clear the reservation. -/
def xret (clears : Bool) (s : St) : St := if clears then { s with resv := none } else s
/-- same-hart store — implementation may or may not invalidate (spec does not require it). -/
def sameHartStore (invalidates : Bool) (v : Nat) (s : St) : St :=
  { mem := v, resv := if invalidates then none else s.resv }
/-- Is the SC *permitted* to succeed? (It is always permitted to fail.) -/
def scMaySucceed (s : St) : Bool := s.resv == some p

/-- Kernel switch path: optional dummy SC, then sret (twice: into B and back into A). -/
def scenario (kernelDummySc xretClears storeInvalidates : Bool) : Bool :=
  let s0 : St := { resv := none, mem := 1 }
  let (s1, _) := lr s0                                     -- A: lr.w
  let s2 := if kernelDummySc then dummySc s1 else s1       -- kernel switch-out
  let s3 := xret xretClears s2                             -- sret into B
  let s4 := sameHartStore storeInvalidates 5 s3            -- B: sw 5,(p)
  let s5 := if kernelDummySc then dummySc s4 else s4       -- kernel switch-back
  let s6 := xret xretClears s5                             -- sret into A
  scMaySucceed s6                                          -- A: sc.w

/-- Without the dummy SC there is a spec-permitted implementation choice under which A's SC may
    succeed after B's intervening store (lost update). -/
theorem lost_update_permitted : scenario false false false = true := by decide

/-- With the dummy SC on every switch, no implementation choice permits the SC to succeed. -/
theorem dummy_sc_sound : ∀ a b : Bool, scenario true a b = false := by decide

/-- QEMU-like choice (xRET/mode change clears, per qemu tcg/cpu_helper.c riscv_cpu_set_mode)
    masks the bug: an emulator test cannot detect a missing dummy SC. -/
theorem qemu_like_masks_bug : scenario false true false = false := by decide

end LrScSwitch
