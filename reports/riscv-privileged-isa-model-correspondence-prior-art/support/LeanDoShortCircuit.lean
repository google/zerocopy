/-
Probe: Lean 4 nested-action lifting `(← e)` inside a
boolean `&&` is hoisted to the enclosing `do` statement and executed BEFORE
the `&&` is evaluated, so an effectful right operand runs even when the left
operand is `false`.  This is the shape the Sail Lean backend emits for
`check_CSR` in both

  Verified-zkEVM/riscv-zkvm@6810fc14  RiscvZkvm/Sail/SysControl.lean:392-394
  opencompl/sail-riscv-lean@51c635c4  LeanRV64D/SysControl.lean:526-528

  def check_CSR csr p access_type : SailM Bool := do
    (pure ((← (check_CSR_priv csr p)) && ((check_CSR_access csr access_type) &&
      ((← (is_CSR_accessible csr p access_type)) && (← (stateen_allows_CSR_access csr p access_type))))))

whereas Sail's `&` short-circuits.  Fixed upstream by rems-project/sail
e55d89e7 ("Lean: support short-circuiting && || with effects", 2026-10-19),
which is NOT contained in the latest Sail release tag 0.20.3.

Init-only; uses `ExceptT String (StateM Nat)` as a stand-in for SailM.
-/

namespace T2ShortCircuit

abbrev M := ExceptT String (StateM Nat)

def privOk : M Bool := pure false                 -- e.g. check_CSR_priv fails
def accessibleThrows : M Bool := throw "assert false (currentlyEnabled Ext_Zkr)"
def accessibleTicks : M Bool := do modify (· + 1); pure true

/-- Backend shape: nested actions hoisted. -/
def checkHoisted (rhs : M Bool) : M Bool := do
  pure ((← privOk) && (← rhs))

/-- Sail semantics: short-circuit. -/
def checkShort (rhs : M Bool) : M Bool := do
  if (← privOk) then rhs else pure false

-- Hoisted form throws although the left operand is false:
example : (checkHoisted accessibleThrows).run.run 0
    = (.error "assert false (currentlyEnabled Ext_Zkr)", 0) := rfl
-- Short-circuit form returns false and does not throw:
example : (checkShort accessibleThrows).run.run 0 = (.ok false, 0) := rfl
-- Hoisted form also performs the right operand's state effect:
example : (checkHoisted accessibleTicks).run.run 0 = (.ok false, 1) := rfl
example : (checkShort accessibleTicks).run.run 0 = (.ok false, 0) := rfl

theorem hoisted_ne_short :
    (checkHoisted accessibleThrows).run.run 0 ≠ (checkShort accessibleThrows).run.run 0 := by
  show ((.error "assert false (currentlyEnabled Ext_Zkr)", 0) : Except String Bool × Nat)
    ≠ (.ok false, 0)
  intro h
  cases h

end T2ShortCircuit

#print axioms T2ShortCircuit.hoisted_ne_short
