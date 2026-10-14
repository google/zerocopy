import Std

abbrev Reg := Fin 3
abbrev RegFile := Reg → Fin 256

def setReg (s : RegFile) (r : Reg) (v : Fin 256) : RegFile :=
  fun q => if q = r then v else s q

def atomicAdd (s : RegFile) (dst lhs rhs : Reg) : RegFile :=
  setReg s dst (s lhs + s rhs)

theorem atomicAdd_all_allocations (s : RegFile) (dst lhs rhs : Reg) :
    atomicAdd s dst lhs rhs dst = s lhs + s rhs := by
  simp [atomicAdd, setReg]

theorem atomicAdd_frame (s : RegFile) (dst lhs rhs q : Reg) (h : q ≠ dst) :
    atomicAdd s dst lhs rhs q = s q := by
  simp [atomicAdd, setReg, h]

def earlyOverwrite (s : RegFile) (dst lhs rhs : Reg) : RegFile :=
  let t := setReg s dst (s lhs)
  setReg t dst (t dst + t rhs)

def allocationWitness : RegFile := fun r => if r = 0 then 1 else 2

theorem illegal_lateout_witness :
    earlyOverwrite allocationWitness 1 0 1 1 ≠ allocationWitness 0 + allocationWitness 1 := by
  decide

structure HeapState where
  bytes : Nat → Nat
  access : List Nat

def temporaryWrite (s : HeapState) (outside : Nat) : HeapState :=
  { bytes := s.bytes, access := s.access ++ [outside] }

theorem final_frame_does_not_imply_trace_safety (s : HeapState) (outside : Nat) :
    (temporaryWrite s outside).bytes = s.bytes ∧ outside ∈ (temporaryWrite s outside).access := by
  simp [temporaryWrite]

def resourceValid (allocationLive aliasAllowed initialized : Bool) : Bool :=
  allocationLive && aliasAllowed && initialized

theorem same_address_is_not_resource_authority :
    resourceValid true true true = true ∧ resourceValid false true true = false ∧
    resourceValid true false true = false ∧ resourceValid true true false = false := by decide

#print axioms atomicAdd_all_allocations
#print axioms atomicAdd_frame
#print axioms illegal_lateout_witness
#print axioms final_frame_does_not_imply_trace_safety
#print axioms same_address_is_not_resource_authority
