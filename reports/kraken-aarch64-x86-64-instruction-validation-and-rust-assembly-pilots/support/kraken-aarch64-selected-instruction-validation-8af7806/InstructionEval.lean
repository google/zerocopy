module
public import Kraken.AArch64.Semantics
public import Kraken.AArch64.Parser
meta import Kraken.AArch64.Semantics
meta import Kraken.AArch64.Parser

@[expose] public section

open Kraken.AArch64 Kraken.AArch64.Parser

def chosenProgram (op : String) : Except String Program :=
  match op with
  | "adds64" => .ok (parseAArch64("adds x0, x1, x2"))
  | "adcs64" => .ok (parseAArch64("adcs x0, x1, x2"))
  | "add32" => .ok (parseAArch64("add w0, w1, w2"))
  | "lslv64" => .ok (parseAArch64("lslv x0, x1, x2"))
  | "lslv32" => .ok (parseAArch64("lslv w0, w1, w2"))
  | "rev64" => .ok (parseAArch64("rev x0, x1"))
  | "rev32" => .ok (parseAArch64("rev w0, w1"))
  | _ => .error s!"unknown op {op}"

-- Fuel is a diagnostic bound. Any data access or nondeterminism is rejected.
def consume (fuel : Nat) (e : Effects) : Except String (MachineState × Nat) :=
  match fuel with
  | 0 => .error "effect fuel exhausted"
  | n+1 => match e with
    | .done s => .ok (s, 0)
    | .require_exec_access p k => do
      if p.lower != 0 || p.upper != 4 then throw "unexpected execute interval"
      let (s, count) ← consume n (k ())
      pure (s, count+1)
    | .unimplemented msg => .error s!"unimplemented: {msg}"
    | .require_read_access .. => .error "unexpected read"
    | .require_write_access .. => .error "unexpected write"
    | .nonmem_load .. => .error "unexpected nonmemory load"
    | .nonmem_store .. => .error "unexpected nonmemory store"
    | @Effects.undefined _ _ _ => .error "unexpected undefined effect"
    | .unaligned_sp .. => .error "unexpected unaligned SP"

def flags (s : StatusFlags) : Nat :=
  8*s.n.toNat + 4*s.z.toNat + 2*s.c.toNat + s.v.toNat

def runCase (line : String) : Except String String := do
  let fields := line.splitOn "\t"
  let [id, op, astr, bstr, cstr] := fields | throw "expected five TSV fields"
  let some a := astr.toNat? | throw "bad a"
  let some b := bstr.toNat? | throw "bad b"
  let some c := cstr.toNat? | throw "bad carry"
  if a >= 2^64 || b >= 2^64 || c > 1 then throw "input outside chosen domain"
  let prog ← chosenProgram op
  let layout : Kraken.Layout Directive := { start := 0, size := fun _ => 4 }
  let initial : MachineData := {
    regs := { X0 := UInt64.ofNat (2^64-1), X1 := UInt64.ofNat a, X2 := UInt64.ofNat b },
    status := { n := false, z := true, c := if op == "adcs64" then c == 1 else true, v := false } }
  let (final, execCount) ← consume 4 (Executable.straightline (layout prog) ⟨initial, 0⟩ .done)
  if execCount != 1 || final.pc != 4 then throw "wrong execution shape"
  -- Check the concrete whole data frame, not just the scalar observation.
  let expectedFrame := { initial with regs := { initial.regs with X0 := final.data.regs.X0 }, status := final.data.status }
  if final.data != expectedFrame then throw "unexpected data frame change"
  pure s!"{id}\t{final.data.regs.X0.toNat}\t{flags final.data.status}"

def main (args : List String) : IO UInt32 := do
  if args == ["--describe"] then
    for op in ["adds64", "adcs64", "add32", "lslv64", "lslv32", "rev64", "rev32"] do
      match chosenProgram op with
      | .ok prog => IO.println s!"{op}\t{repr prog}"
      | .error msg => IO.eprintln msg; return 1
    return 0
  let [path] := args | IO.eprintln "expected cases.tsv path"; return 2
  let input ← IO.FS.readFile path
  for line in input.splitOn "\n" do
    if line.isEmpty then continue
    match runCase line with
    | .ok result => IO.println result
    | .error msg => IO.eprintln s!"case {line}: {msg}"; return 1
  return 0
