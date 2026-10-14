import Init

namespace RestrictedWasm
abbrev Word := Fin (2^32)
abbrev Arg := Fin 4
abbrev Small := Fin 64
abbrev Inputs := Arg → Word

def bit (b : Bool) : Nat := if b then 1 else 0

inductive Expr where
  | lt (i : Arg) (c : Small)
  | and (a b : Expr)
deriving DecidableEq, Repr

def eval (xs : Inputs) : Expr → Bool
  | .lt i c => decide ((xs i).val < c.val)
  | .and a b => eval xs a && eval xs b

inductive Instr where
  | get (i : Arg)
  | const (c : Small)
  | ltU
  | and
deriving DecidableEq, Repr

def step (xs : Inputs) : Instr → List Nat → Option (List Nat)
  | .get i, st => some ((xs i).val :: st)
  | .const c, st => some (c.val :: st)
  | .ltU, b::a::st => some (bit (decide (a < b)) :: st)
  | .and, b::a::st => some (Nat.land a b :: st)
  | _, _ => none

def run (xs : Inputs) : List Instr → List Nat → Option (List Nat)
  | [], st => some st
  | i::is, st => (step xs i st).bind (run xs is)

def compile : Expr → List Instr
  | .lt i c => [.get i, .const c, .ltU]
  | .and a b => compile a ++ compile b ++ [.and]

theorem run_append (xs : Inputs) (a b : List Instr) (st : List Nat) :
    run xs (a ++ b) st = (run xs a st).bind (run xs b) := by
  induction a generalizing st with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, run]
    cases h : step xs i st with
    | none => simp
    | some st' => simpa using ih st'

theorem and_bit (a b : Bool) : Nat.land (bit a) (bit b) = bit (a && b) := by
  cases a <;> cases b <;> decide

-- A generic expression compiler theorem, for every stack and every 32-bit input.
theorem compiler_correct (e : Expr) (xs : Inputs) (st : List Nat) :
    run xs (compile e) st = some (bit (eval xs e) :: st) := by
  induction e generalizing st with
  | lt i c => rfl
  | and a b ia ib =>
    simp only [compile, run_append, ia, Option.bind_some, ib, run, step]
    rw [Nat.land_comm, and_bit]
    rfl

def encodeInstr : Instr → List Nat
  | .get i => [32, i.val]
  | .const c => [65, c.val]
  | .ltU => [73]
  | .and => [113]

def encode : List Instr → List Nat
  | [] => []
  | i::is => encodeInstr i ++ encode is

-- Strict, canonical single-byte immediates: local indices <4, signed constants 0..63.
def parseBody : List Nat → Option (List Instr)
  | [11] => some []
  | 32::i::bs => if h : i < 4 then
      (parseBody bs).map (Instr.get ⟨i,h⟩ :: ·) else none
  | 65::c::bs => if h : c < 64 then
      (parseBody bs).map (Instr.const ⟨c,h⟩ :: ·) else none
  | 73::bs => (parseBody bs).map (Instr.ltU :: ·)
  | 113::bs => (parseBody bs).map (Instr.and :: ·)
  | _ => none

theorem body_roundtrip (is : List Instr) :
    parseBody (encode is ++ [11]) = some is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    cases i with
    | get i => simp [encode, encodeInstr, parseBody, i.isLt, ih]
    | const c => simp [encode, encodeInstr, parseBody, c.isLt, ih]
    | ltU => simpa [encode, encodeInstr, parseBody] using congrArg (Option.map (Instr.ltU :: ·)) ih
    | and => simpa [encode, encodeInstr, parseBody] using congrArg (Option.map (Instr.and :: ·)) ih

-- Complete fixed module: type (i32,i32,i32,i32)->i32; one function/export; no imports.
def header : List Nat :=
  [0,97,115,109,1,0,0,0,
   1,9,1,96,4,127,127,127,127,1,127,
   3,2,1,0,
   7,12,1,8,118,97,108,105,100,97,116,101,0,0]

def emitModule (is : List Instr) : List Nat :=
  let bs := encode is
  header ++ [10,bs.length+4,1,bs.length+2,0] ++ bs ++ [11]

def strip : List Nat → List Nat → Option (List Nat)
  | [], bs => some bs
  | a::as, b::bs => if a=b then strip as bs else none
  | _, _ => none

theorem strip_append (a b : List Nat) : strip a (a ++ b) = some b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simpa [strip] using ih

def candidate (bs : List Nat) : Option (List Instr) :=
  (strip header bs).bind fun rest =>
    match rest with
    | 10::sec::1::body::0::code =>
      if sec = code.length+3 ∧ body = code.length+1 ∧ sec < 128 ∧ body < 128
      then parseBody code else none
    | _ => none

-- Re-emission is checked, including section sizes, wrapper, complete body and end marker.
def parseModule (bs : List Nat) : Option (List Instr) :=
  (candidate bs).bind fun is => if bs = emitModule is then some is else none

theorem module_roundtrip (is : List Instr) (small : (encode is).length+4 < 128) :
    parseModule (emitModule is) = some is := by
  have bodySmall : (encode is).length+2 < 128 := by omega
  simp [parseModule, candidate, emitModule, List.append_assoc, strip_append,
    body_roundtrip, small, bodySmall]

theorem accepted_bytes (bs : List Nat) (is : List Instr)
    (accepted : parseModule bs = some is) : bs = emitModule is := by
  unfold parseModule at accepted
  cases hc : candidate bs with
  | none => simp [hc] at accepted
  | some js =>
    simp only [hc, Option.bind_some] at accepted
    split at accepted
    next h =>
      have eq : js = is := by simpa using accepted
      simpa [eq] using h
    next => simp at accepted

-- Binds every accepted literal module for a specified expression to its input semantics.
theorem bound_module_correct (bs : List Nat) (e : Expr) (xs : Inputs)
    (accepted : parseModule bs = some (compile e)) :
    bs = emitModule (compile e) ∧
    run xs (compile e) [] = some [bit (eval xs e)] :=
  ⟨accepted_bytes bs (compile e) accepted, compiler_correct e xs []⟩

def four : Expr := .and (.and (.lt 0 2) (.lt 1 2)) (.and (.lt 2 2) (.lt 3 2))
def validity (xs : Inputs) : Bool :=
  decide ((xs 0).val < 2) && decide ((xs 1).val < 2) &&
  (decide ((xs 2).val < 2) && decide ((xs 3).val < 2))

def moduleBytes := emitModule (compile four)

theorem four_semantics (xs : Inputs) :
    run xs (compile four) [] = some [bit (validity xs)] := by
  exact compiler_correct four xs []

theorem literal_accepted : parseModule moduleBytes = some (compile four) := by
  exact module_roundtrip (compile four) (by decide)

def admitFour (bs : List Nat) : Bool := parseModule bs == some (compile four)

theorem admit_sound (bs : List Nat) (h : admitFour bs = true) (xs : Inputs) :
    bs = moduleBytes ∧ run xs (compile four) [] = some [bit (validity xs)] := by
  have accepted : parseModule bs = some (compile four) := by simpa [admitFour] using h
  exact bound_module_correct bs four xs accepted

-- Changed well-formed predicate is executable, but fails independently selected admission.
def changed : Expr := .and (.and (.lt 0 3) (.lt 1 2)) (.and (.lt 2 2) (.lt 3 2))
theorem changed_predicate_rejected : admitFour (emitModule (compile changed)) = false := by decide
-- Unknown opcode and malformed/incomplete wrapper reject before selected-predicate checking.
theorem unknown_opcode_rejected : parseModule (header ++ [10,5,1,3,0,255,11]) = none := by decide
theorem missing_end_rejected : parseModule (moduleBytes.take (moduleBytes.length-1)) = none := by decide

#print axioms compiler_correct
#print axioms body_roundtrip
#print axioms module_roundtrip
#print axioms accepted_bytes
#print axioms bound_module_correct
#print axioms literal_accepted
#print axioms admit_sound
#print axioms changed_predicate_rejected
#print axioms unknown_opcode_rejected
#print axioms missing_end_rejected
#eval moduleBytes
end RestrictedWasm
