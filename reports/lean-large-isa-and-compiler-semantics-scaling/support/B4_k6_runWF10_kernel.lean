/- Probe B4: the exact `runWF10` definition from package
   `lean-large-isa-and-compiler-semantics-scaling` (support/gen_k6_models.py, Axis 3B), whose
   `termination_by limit - st.pc` measure is `Nat`-valued.  Checked here by `decide +kernel`
   (kernel evaluation) instead of `simp [runWF10, step10]`, for the largest trace in that
   benchmark (steps = 1000, i.e. limit 4000, 100 recursive calls) and a 100x longer one. -/
structure MachState where
  pc : Nat
  r0 : Nat
  r1 : Nat

@[inline] def step10 (st : MachState) : MachState :=
  { pc := st.pc + 40, r0 := st.r0 + st.r1 + 10, r1 := (st.r1 + 30) % 256 }

def runWF10 (limit : Nat) (st : MachState) : MachState :=
  if st.pc < limit then
    runWF10 limit (step10 st)
  else
    st
termination_by limit - st.pc
decreasing_by
  simp_wf
  dsimp [step10]
  omega

-- elaborator-level `decide` (expected to fail: WF definitions are irreducible for `Meta.whnf`)
theorem b4_wf_exec_elab : (runWF10 4000 { pc := 0, r0 := 1, r1 := 2 }).pc = 4000 := by decide
-- elaborator-level `rfl` (expected to fail for the same reason)
theorem b4_wf_exec_rfl : (runWF10 4000 { pc := 0, r0 := 1, r1 := 2 }).pc = 4000 := by rfl
-- kernel-only check
theorem b4_wf_exec_ok_1000 : (runWF10 4000 { pc := 0, r0 := 1, r1 := 2 }).pc = 4000 := by decide +kernel
#print axioms b4_wf_exec_ok_1000
theorem b4_wf_exec_ok_100000 : (runWF10 400000 { pc := 0, r0 := 1, r1 := 2 }).pc = 400000 := by decide +kernel
#print axioms b4_wf_exec_ok_100000
-- how the definition is compiled
#print axioms runWF10
-- how the definition is compiled: shows `@[irreducible]` and the `WellFounded.Nat.fix` body
set_option pp.oneline true in
#print runWF10
