import ToyCFI.Machine

/-!
# Toy call-frame information: rows, CFI programs, table correctness

A CFI program is a linear list of row-modifying instructions interpreted in PC
order with a state stack, in the style of DWARF call-frame instructions
(`DW_CFA_def_cfa`, `DW_CFA_def_cfa_register`, `DW_CFA_def_cfa_offset`,
`DW_CFA_offset`, `DW_CFA_restore`, `DW_CFA_remember_state`,
`DW_CFA_restore_state`, `DW_CFA_advance_loc`).  The row in effect at a PC
recovers the caller's CFA and registers from the current machine state.
-/

namespace Toy.CFI

/-- Per-register recovery rule: `same` (the register still holds the caller's
value) or `offset k` (the caller's value is saved at address `CFA + k`). -/
inductive RegRule
  | same
  | offset (k : Int)
  deriving DecidableEq, Repr

/-- An unwind row: the CFA rule `cfaReg + cfaOff` and a rule per register. -/
structure Row where
  cfaReg : Reg
  cfaOff : Int
  rules : RegFile RegRule
  deriving DecidableEq, Repr

/-- The initial row (the toy counterpart of a CIE's initial instructions):
`CFA = sp + 0`, every register `same`. -/
def initRow : Row := { cfaReg := .sp, cfaOff := 0, rules := RegFile.const .same }

/-- Row-modifying instructions. `advanceLoc d` moves the current location by `d`
address units; `restore r` resets `r` to its rule in `initRow`. -/
inductive CFIInst
  | defCfa (r : Reg) (off : Int)
  | defCfaRegister (r : Reg)
  | defCfaOffset (off : Int)
  | offset (r : Reg) (k : Int)
  | restore (r : Reg)
  | rememberState
  | restoreState
  | advanceLoc (d : Nat)
  deriving DecidableEq, Repr

/-- Interpreter state: current location, current row, and the state stack. -/
structure CFIState where
  loc : Nat
  row : Row
  stack : List Row
  deriving DecidableEq, Repr

/-- Effect of one non-advancing instruction.  `rememberState` pushes the whole
row (CFA rule included); `restoreState` pops it and fails (`none`) on an empty
stack. `advanceLoc` is handled by `rowAtAux` and is a no-op here. -/
def execInst (s : CFIState) : CFIInst → Option CFIState
  | .defCfa r off => some { s with row := { s.row with cfaReg := r, cfaOff := off } }
  | .defCfaRegister r => some { s with row := { s.row with cfaReg := r } }
  | .defCfaOffset off => some { s with row := { s.row with cfaOff := off } }
  | .offset r k => some { s with row := { s.row with rules := s.row.rules.set r (.offset k) } }
  | .restore r =>
    some { s with row := { s.row with rules := s.row.rules.set r (initRow.rules.get r) } }
  | .rememberState => some { s with stack := s.row :: s.stack }
  | .restoreState =>
    match s.stack with
    | [] => none
    | R :: rest => some { s with row := R, stack := rest }
  | .advanceLoc _ => some s

/-- Row in effect at `pc`: interpret instructions in order; an `advanceLoc d`
that would move the location past `pc` ends the interpretation.  Instructions
located at an address `≤ pc` therefore apply at `pc`. -/
def rowAtAux : List CFIInst → CFIState → Nat → Option Row
  | [], s, _ => some s.row
  | i :: rest, s, pc =>
    match i with
    | .advanceLoc d =>
      if pc < s.loc + d then some s.row else rowAtAux rest { s with loc := s.loc + d } pc
    | _ =>
      match execInst s i with
      | none => none
      | some s' => rowAtAux rest s' pc

/-- The row of a CFI program at address `pc` (the program starts at address `0`
with `initRow` and an empty stack); `none` on state-stack underflow. -/
def rowAt? (prog : List CFIInst) (pc : Nat) : Option Row :=
  rowAtAux prog { loc := 0, row := initRow, stack := [] } pc

/-- CFA computed by row `R` from state `st`. -/
def cfaOf (R : Row) (st : MState) : Int := st.regs.get R.cfaReg + R.cfaOff

/-- Value of register `r` in the caller, as recovered by row `R` from `st`. -/
def ruleVal (R : Row) (st : MState) (r : Reg) : Int :=
  match R.rules.get r with
  | .same => st.regs.get r
  | .offset k => st.mem (cfaOf R st + k)

/-- The toy ABI's callee-saved registers. -/
def calleeSaved : List Reg := [.fp, .s1]

/-- Row `R` applied to state `st` recovers caller `c`: the computed CFA is the
caller's CFA and every callee-saved register is recovered. -/
def Recovers (R : Row) (c : Caller) (st : MState) : Prop :=
  cfaOf R st = c.cfa ∧ ∀ r ∈ calleeSaved, ruleVal R st r = c.regs.get r

/-- Per-PC table correctness for a CFG with a linear layout: for every caller,
every initial memory, every reachable `(block, offset)` and every state
reachable there, the PC has a linear address, the CFI program has a row at that
address, and the row recovers the caller. -/
def TableCorrect (f : Func) (prog : List CFIInst) : Prop :=
  ∀ (c : Caller) (m : Int → Int) (b k : Nat) (st : MState), Reach f c m b k st →
    ∃ pc R, f.pcOf b k = some pc ∧ rowAt? prog pc = some R ∧ Recovers R c st

end Toy.CFI
