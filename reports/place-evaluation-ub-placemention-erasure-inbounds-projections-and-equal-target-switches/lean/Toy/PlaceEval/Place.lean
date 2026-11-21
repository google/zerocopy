import Toy.PlaceEval.Memory

/-!
# Places and place evaluation

A place is a local followed by a list of projections: `field off` (a field at byte
offset `off`, taken as given from a layout computation), `index j sz` (indexing by the
value of local `j`, elements of `sz` bytes) and `deref` (dereferencing the pointer stored
in the current place). Place evaluation computes a pointer; it never loads the final
place. Its only memory reads are the pointer loads of `deref` projections and the reads of
`index` locals.
-/

namespace Toy.PlaceEval

/-- Layout of a local or of a reference's pointee: size and alignment in bytes. -/
structure Layout where
  size : Nat
  align : Nat
deriving DecidableEq, Repr

/-- Projection elements. -/
inductive Proj where
  | field (off : Nat)
  | index (j : Local) (elemSize : Nat)
  | deref
deriving DecidableEq, Repr

/-- A place: a base local and a projection list, applied left to right. -/
structure Place where
  base : Local
  proj : List Proj
deriving DecidableEq, Repr

/-- Machine state: memory and the frame, which maps each local (by index) to the
allocation currently backing it, or `none` if the local is unallocated. Locals beyond the
frame's length are unallocated. -/
structure State where
  mem : Mem
  frame : List (Option AllocId)
deriving DecidableEq, Repr

/-- The allocation backing local `x`, if any. -/
def State.allocOf (st : State) (x : Local) : Option AllocId := st.frame.getD x none

/-- The pointer to local `x`: provenance the backing allocation, address its base.
`none` if `x` is unallocated (or the frame names a missing allocation). -/
def State.basePtr (st : State) (x : Local) : Option Ptr :=
  match st.allocOf x with
  | none => none
  | some k => (st.mem.allocs[k]?).map fun al => ⟨some k, al.base⟩

/-- The type of index locals: a one-byte unsigned integer. -/
def idxTy : Ty := .int 1 1

/-- Read local `j` as a value of type `τ` (a value read: UB if `j` is unallocated or the
load fails). -/
def State.readLocal (st : State) (j : Local) (τ : Ty) : Option Val :=
  (st.basePtr j).bind fun q => st.mem.load q τ

/-- Read the index local `j`. -/
def State.readIndex (st : State) (j : Local) : Option Nat :=
  match st.readLocal j idxTy with
  | some (.int n) => some n
  | _ => none

/-- One projection step from pointer `q`. `deref` loads a pointer through `q`;
`field off` and `index j sz` offset `q` (by `off`, resp. `n * sz` where `n` is the value
of `j`), subject to the in-bounds rule (a zero offset is always permitted). -/
def projStep (st : State) (q : Ptr) : Proj → Option Ptr
  | .deref => st.mem.loadPtr q
  | .field off => if st.mem.offsetInbounds q off then some (q.offset off) else none
  | .index j sz =>
    match st.readIndex j with
    | some n => if st.mem.offsetInbounds q (n * sz) then some (q.offset (n * sz)) else none
    | none => none

/-- Apply a projection list from pointer `q`. -/
def evalProjs (st : State) : Ptr → List Proj → Option Ptr
  | q, [] => some q
  | q, π :: πs => (projStep st q π).bind fun q' => evalProjs st q' πs

/-- **Place evaluation.** The pointer denoted by place `p`, or `none` for UB. The final
place is never accessed: its pointee may be unallocated, freed, misaligned or
uninitialized. -/
def evalPlace (st : State) (p : Place) : Option Ptr :=
  (st.basePtr p.base).bind fun q => evalProjs st q p.proj

/-- Evaluation of the first `i` projections of `p` (all of them if `i` is at least the
length). -/
def evalPrefix (st : State) (p : Place) (i : Nat) : Option Ptr :=
  (st.basePtr p.base).bind fun q => evalProjs st q (p.proj.take i)

end Toy.PlaceEval
