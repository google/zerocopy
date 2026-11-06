/-!
# Kraken AArch64 Parser Opacity and `Effects` Access-Event Probe (Lean 4.34.1)

This standalone Lean 4.34.1 file re-validates two mechanical properties of
`leanprover/kraken@8af78062037bc237b341d20252aafd1797c1bcb7` under
`leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
within the `-j1 -M768` memory ceiling:

1. **Kernel Opacity of Recursive `partial def` Parsers vs. Structural Fuel-Bounded Reduction:**
   In `Kraken/AArch64/Parser/Basic.lean:138-152, 703`, `Kraken.AArch64.Parser.parse`
   calls `parseAddr` -> `parseConstExpr`, where `parseConstExpr` is a recursive
   `partial def`. In Lean 4.34.1 (`Lean/Elab/PreDefinition/Main.lean:299-320`,
   `Lean/Compiler/LCNF/ToDecl.lean:100-117`, `Lean/Meta/Eqns.lean:142-151`),
   recursive `partial def` declarations are added to the kernel environment as
   `ConstantInfo.opaqueInfo` (`Declaration.opaqueDecl`) paired with an `unsafe`
   compiled auxiliary `._unsafe_rec`, and `getEqnsFor?` produces `none`.
   Consequently, `#eval` (compiled `MetaM` evaluation) can execute the parser
   to produce `some 8`, but kernel definitional equality (`rfl`) cannot unfold it.
   By contrast, a fuel-bounded structural parser or a total AST pretty-printer
   elaborates as a safe `ConstantInfo.defnInfo` with kernel unfolding equations
   and reduces by `rfl`.

2. **Permissive Default `Effects.All` vs. Footprint-Enforcing `Effects` Observer:**
   In `Kraken/AArch64/Semantics.lean:171-221, 319-327, 980-993` and
   `Kraken/AArch64/OmniSemantics.lean:13-22`, memory helper functions emit
   `require_read_access`, `require_write_access`, and `require_exec_access`
   events into the `Effects` interaction tree, and `checkSPAlignment` checks
   only `SP`-relative accesses. However, both `Effects.All` and `Executable.eval`
   ignore `require_*_access` events (`require_*_access => Effects.All k`).
   We demonstrate on the 4-instruction `aarch64` leaf
   (`ldr x2, [x0]; str x1, [x0, #imm]; mov x0, x2; ret`) that:
   - Return-value observation (`x0 == a`) cannot distinguish `str x1, [x0]`
     from the wrong-slot store `str x1, [x0, #8]`.
   - When `a == v`, even inspecting the first 64-bit slot (`mem[p] == v`) alongside
     `x0 == a` does not detect the out-of-footprint write to `[p+8, p+16)` unless
     either the witness slot `[p+8, p+16)` is checked or the `Effects` observer
     enforces `require_write_access` against the authorized footprint `[p, p+8)`.
   - Non-`SP` unaligned accesses (`x0 % 8 != 0`) bypass `checkSPAlignment` and
     are accepted by `Effects.All` / `Executable.eval`, whereas a strict
     `Effects` observer rejects them at `require_read_access`.
-/

namespace KrakenBridgeProbe

/-! ## Part 1: Recursive `partial def` Kernel Opacity vs. Fuel-Bounded Structural Reduction -/

/-- Digit value helper for decimal constant expressions. -/
def digitVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else
    none

/-- Consume decimal digits (structural over `List Char`). -/
def parseDigits (cs : List Char) (acc : Nat) : Option (Nat × List Char) :=
  match cs with
  | [] => some (acc, [])
  | c :: rest =>
    match digitVal? c with
    | some d => parseDigits rest (acc * 10 + d)
    | none => some (acc, c :: rest)

/--
Recursive `partial def` constant-expression parser mirroring the recursive
structure of `parseConstExpr` in `Kraken/AArch64/Parser/Basic.lean:138-152`.
-/
partial def parseConstExprPartial (cs : List Char) : Option (Nat × List Char) :=
  match cs with
  | '#' :: rest => parseConstExprPartial rest
  | '(' :: rest =>
    match parseConstExprPartial rest with
    | some (v, ')' :: tail) => some (v, tail)
    | _ => none
  | c :: rest =>
    match digitVal? c with
    | some d =>
      match parseDigits rest d with
      | some (v, '+' :: tail) =>
        match parseConstExprPartial tail with
        | some (rhs, tail') => some (v + rhs, tail')
        | none => none
      | res => res
    | none => none
  | [] => none

def parseImmPartial (cs : List Char) : Option Nat :=
  match parseConstExprPartial cs with
  | some (v, []) => some v
  | _ => none

/--
Fuel-bounded structural constant-expression parser over the same grammar.
-/
def parseConstExprFuel : Nat → List Char → Option (Nat × List Char)
  | 0, _ => none
  | fuel + 1, '#' :: rest => parseConstExprFuel fuel rest
  | fuel + 1, '(' :: rest =>
    match parseConstExprFuel fuel rest with
    | some (v, ')' :: tail) => some (v, tail)
    | _ => none
  | fuel + 1, c :: rest =>
    match digitVal? c with
    | some d =>
      match parseDigits rest d with
      | some (v, '+' :: tail) =>
        match parseConstExprFuel fuel tail with
        | some (rhs, tail') => some (v + rhs, tail')
        | none => none
      | res => res
    | none => none
  | _ + 1, [] => none

def parseImmFuel (fuel : Nat := 16) (cs : List Char) : Option Nat :=
  match parseConstExprFuel fuel cs with
  | some (v, []) => some v
  | _ => none

/-
Compiled `MetaM` evaluation (`#eval`) executes `parseImmPartial` via its
compiled `._unsafe_rec` implementation and produces `some 8`.
-/
/-- info: some 8 -/
#guard_msgs in
#eval parseImmPartial ['#', '8']

/-
However, in the Lean 4.34.1 kernel, `parseConstExprPartial` is an opaque
declaration (`Declaration.opaqueDecl`) with no unfolding equations: attempting
to prove `parseImmPartial ['#', '8'] = some 8` by reflexivity fails in the kernel.
-/
/--
error: Type mismatch
  Eq.refl (parseImmPartial ['#', '8'])
has type
  parseImmPartial ['#', '8'] = parseImmPartial ['#', '8']
but is expected to have type
  parseImmPartial ['#', '8'] = some 8
-/
#guard_msgs in
example : parseImmPartial ['#', '8'] = some 8 := Eq.refl (parseImmPartial ['#', '8'])

/--
By contrast, the fuel-bounded structural parser `parseImmFuel` elaborates as a
total `DefinitionSafety.safe` definition with kernel unfolding equations, so
`rfl` reduces both simple and parenthesized constant expressions directly in the kernel.
-/
theorem parseImmFuel_hash8 : parseImmFuel 16 ['#', '8'] = some 8 := rfl
theorem parseImmFuel_expr8 : parseImmFuel 16 ['#', '(', '4', '+', '4', ')'] = some 8 := rfl
theorem parseImmFuel_hash0 : parseImmFuel 16 ['#', '0'] = some 0 := rfl

/--
Selected 4-instruction AArch64 leaf AST (`ldr`, `str`, `mov`, `ret`)
and structural token parser + canonical token printer round-trip.
-/
inductive Reg64 where
  | x0 | x1 | x2 | sp
  deriving DecidableEq, Repr

inductive LeafInstr where
  | ldrImm64 (rt : Reg64) (rn : Reg64) (immBytes : Nat)
  | strImm64 (rt : Reg64) (rn : Reg64) (immBytes : Nat)
  | movReg64 (rd : Reg64) (rm : Reg64)
  | ret64
  deriving DecidableEq, Repr

inductive AsmToken where
  | ldr | str | mov | ret
  | reg (r : Reg64)
  | bracketOpen | bracketClose | comma
  | immChars (cs : List Char)
  deriving DecidableEq, Repr

def printLeafTokens : LeafInstr → List AsmToken
  | .ldrImm64 rt rn 0 => [.ldr, .reg rt, .comma, .bracketOpen, .reg rn, .bracketClose]
  | .ldrImm64 rt rn _ => [.ldr, .reg rt, .comma, .bracketOpen, .reg rn, .comma, .immChars ['#', '8'], .bracketClose]
  | .strImm64 rt rn 0 => [.str, .reg rt, .comma, .bracketOpen, .reg rn, .bracketClose]
  | .strImm64 rt rn _ => [.str, .reg rt, .comma, .bracketOpen, .reg rn, .comma, .immChars ['#', '8'], .bracketClose]
  | .movReg64 rd rm => [.mov, .reg rd, .comma, .reg rm]
  | .ret64 => [.ret]

def parseLeafTokensFuel (fuel : Nat := 16) : List AsmToken → Option LeafInstr
  | [.ret] => some .ret64
  | [.mov, .reg rd, .comma, .reg rm] => some (.movReg64 rd rm)
  | [.ldr, .reg rt, .comma, .bracketOpen, .reg rn, .bracketClose] =>
    some (.ldrImm64 rt rn 0)
  | [.ldr, .reg rt, .comma, .bracketOpen, .reg rn, .comma, .immChars cs, .bracketClose] =>
    match parseImmFuel fuel cs with
    | some imm => some (.ldrImm64 rt rn imm)
    | none => none
  | [.str, .reg rt, .comma, .bracketOpen, .reg rn, .bracketClose] =>
    some (.strImm64 rt rn 0)
  | [.str, .reg rt, .comma, .bracketOpen, .reg rn, .comma, .immChars cs, .bracketClose] =>
    match parseImmFuel fuel cs with
    | some imm => some (.strImm64 rt rn imm)
    | none => none
  | _ => none

theorem parse_positive_leaf_rfl :
    [ [.ldr, .reg .x2, .comma, .bracketOpen, .reg .x0, .bracketClose]
    , [.str, .reg .x1, .comma, .bracketOpen, .reg .x0, .bracketClose]
    , [.mov, .reg .x0, .comma, .reg .x2]
    , [.ret] ].mapM (parseLeafTokensFuel 16) =
      some [
        .ldrImm64 .x2 .x0 0,
        .strImm64 .x1 .x0 0,
        .movReg64 .x0 .x2,
        .ret64
      ] := rfl

theorem parse_wrong_slot_leaf_rfl :
    [ [.ldr, .reg .x2, .comma, .bracketOpen, .reg .x0, .bracketClose]
    , [.str, .reg .x1, .comma, .bracketOpen, .reg .x0, .comma, .immChars ['#', '8'], .bracketClose]
    , [.mov, .reg .x0, .comma, .reg .x2]
    , [.ret] ].mapM (parseLeafTokensFuel 16) =
      some [
        .ldrImm64 .x2 .x0 0,
        .strImm64 .x1 .x0 8,
        .movReg64 .x0 .x2,
        .ret64
      ] := rfl

theorem print_parse_roundtrip_positive :
    ([LeafInstr.ldrImm64 .x2 .x0 0, .strImm64 .x1 .x0 0, .movReg64 .x0 .x2, .ret64].map printLeafTokens).mapM
      (parseLeafTokensFuel 16) =
      some [.ldrImm64 .x2 .x0 0, .strImm64 .x1 .x0 0, .movReg64 .x0 .x2, .ret64] := rfl

theorem print_parse_roundtrip_wrong_slot :
    ([LeafInstr.ldrImm64 .x2 .x0 0, .strImm64 .x1 .x0 8, .movReg64 .x0 .x2, .ret64].map printLeafTokens).mapM
      (parseLeafTokensFuel 16) =
      some [.ldrImm64 .x2 .x0 0, .strImm64 .x1 .x0 8, .movReg64 .x0 .x2, .ret64] := rfl

/-! ## Part 2: Kraken `Effects` Interaction Tree (`Effects.All` vs. `Effects.StrictObserve`) -/

/--
Machine state for the 2-slot `[u64; 2]` buffer and 4-instruction AArch64 leaf.
Addresses are byte offsets; `slot0` lives at `[baseAddr, baseAddr + 8)` and
`slot1` lives at `[baseAddr + 8, baseAddr + 16)`.
-/
structure MachineState where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  sp : Nat
  pc : Nat
  retAddr : Nat
  baseAddr : Nat
  slot0 : Nat
  slot1 : Nat
  deriving DecidableEq, Repr

def MachineState.getReg (s : MachineState) : Reg64 → Nat
  | .x0 => s.x0
  | .x1 => s.x1
  | .x2 => s.x2
  | .sp => s.sp

def MachineState.setReg (s : MachineState) (r : Reg64) (v : Nat) : MachineState :=
  match r with
  | .x0 => { s with x0 := v }
  | .x1 => { s with x1 := v }
  | .x2 => { s with x2 := v }
  | .sp => { s with sp := v }

def MachineState.read64? (s : MachineState) (addr : Nat) : Option Nat :=
  if addr == s.baseAddr then
    some s.slot0
  else if addr == s.baseAddr + 8 then
    some s.slot1
  else
    none

def MachineState.write64? (s : MachineState) (addr : Nat) (v : Nat) : Option MachineState :=
  if addr == s.baseAddr then
    some { s with slot0 := v }
  else if addr == s.baseAddr + 8 then
    some { s with slot1 := v }
  else
    none

/--
Interaction tree mirroring `Effects` in `Kraken/AArch64/Semantics.lean:171-221`.
-/
inductive Effects where
  | done (s : MachineState)
  | unaligned_sp
  | out_of_bounds_mem
  | require_read_access (addr : Nat) (width : Nat) (k : Effects)
  | require_write_access (addr : Nat) (width : Nat) (k : Effects)
  | require_exec_access (addr : Nat) (width : Nat) (k : Effects)
  deriving DecidableEq, Repr

def Effects.bind : Effects → (MachineState → Effects) → Effects
  | .done s, f => f s
  | .unaligned_sp, _ => .unaligned_sp
  | .out_of_bounds_mem, _ => .out_of_bounds_mem
  | .require_read_access a w k, f => .require_read_access a w (k.bind f)
  | .require_write_access a w k, f => .require_write_access a w (k.bind f)
  | .require_exec_access a w k, f => .require_exec_access a w (k.bind f)

/--
Mirrors `checkSPAlignment` in `Kraken/AArch64/Semantics.lean:319-327`:
only checks alignment when the base register is `SP`.
-/
def checkSPAlignment (rn : Reg64) (s : MachineState) (k : Effects) : Effects :=
  match rn with
  | .sp => if s.sp % 16 == 0 then k else .unaligned_sp
  | _ => k

/--
Single-instruction semantics emitting `require_exec_access`, `require_read_access`,
and `require_write_access` events just like `Kraken/AArch64/Semantics.lean`.
-/
def stepInstr (instr : LeafInstr) (s : MachineState) : Effects :=
  .require_exec_access s.pc 4 <|
    match instr with
    | .ldrImm64 rt rn imm =>
      checkSPAlignment rn s <|
        let addr := s.getReg rn + imm
        .require_read_access addr 8 <|
          match s.read64? addr with
          | some val => .done ({ (s.setReg rt val) with pc := s.pc + 4 })
          | none => .out_of_bounds_mem
    | .strImm64 rt rn imm =>
      checkSPAlignment rn s <|
        let addr := s.getReg rn + imm
        .require_write_access addr 8 <|
          match s.write64? addr (s.getReg rt) with
          | some s' => .done ({ s' with pc := s.pc + 4 })
          | none => .out_of_bounds_mem
    | .movReg64 rd rm =>
      .done ({ (s.setReg rd (s.getReg rm)) with pc := s.pc + 4 })
    | .ret64 =>
      .done ({ s with pc := s.retAddr })

def execLeaf : List LeafInstr → MachineState → Effects
  | [], s => .done s
  | i :: rest, s => (stepInstr i s).bind (execLeaf rest)

def positiveLeafProg : List LeafInstr :=
  [.ldrImm64 .x2 .x0 0, .strImm64 .x1 .x0 0, .movReg64 .x0 .x2, .ret64]

def wrongSlotLeafProg : List LeafInstr :=
  [.ldrImm64 .x2 .x0 0, .strImm64 .x1 .x0 8, .movReg64 .x0 .x2, .ret64]

/--
Permissive `Effects.All` predicate mirroring `Kraken/AArch64/OmniSemantics.lean:13-22`:
ignores `require_read_access`, `require_write_access`, and `require_exec_access`.
-/
def Effects.All (P : MachineState → Bool) : Effects → Bool
  | .done s => P s
  | .unaligned_sp => false
  | .out_of_bounds_mem => false
  | .require_read_access _ _ k => Effects.All P k
  | .require_write_access _ _ k => Effects.All P k
  | .require_exec_access _ _ k => Effects.All P k

/--
Permissive evaluator mirroring `Executable.eval` in `Kraken/AArch64/Semantics.lean:980-993`:
ignores `require_read_access`, `require_write_access`, and `require_exec_access`.
-/
def Executable.eval : Effects → Option MachineState
  | .done s => some s
  | .unaligned_sp => none
  | .out_of_bounds_mem => none
  | .require_read_access _ _ k => Executable.eval k
  | .require_write_access _ _ k => Executable.eval k
  | .require_exec_access _ _ k => Executable.eval k

/--
Explicit permission and alignment policy for a narrow single-slot `&mut u64` call contract:
- Code range: `[codeBase, codeBase + codeLen)` (4-byte aligned fetches)
- Read range: `[readBase, readBase + readLen)` (8-byte aligned loads)
- Write range: `[writeBase, writeBase + writeLen)` (8-byte aligned stores)
-/
structure FootprintPolicy where
  codeBase : Nat
  codeLen : Nat
  readBase : Nat
  readLen : Nat
  writeBase : Nat
  writeLen : Nat
  deriving DecidableEq, Repr

def inRangeAligned (addr width align base len : Nat) : Bool :=
  (addr % align == 0) && (base ≤ addr) && (addr + width ≤ base + len)

/--
Strict `Effects` observer that enforces `require_exec_access`, `require_read_access`,
and `require_write_access` against `FootprintPolicy` and natural alignment.
-/
def Effects.StrictObserve (pol : FootprintPolicy) (P : MachineState → Bool) : Effects → Bool
  | .done s => P s
  | .unaligned_sp => false
  | .out_of_bounds_mem => false
  | .require_read_access addr width k =>
    inRangeAligned addr width 8 pol.readBase pol.readLen && Effects.StrictObserve pol P k
  | .require_write_access addr width k =>
    inRangeAligned addr width 8 pol.writeBase pol.writeLen && Effects.StrictObserve pol P k
  | .require_exec_access addr width k =>
    inRangeAligned addr width 4 pol.codeBase pol.codeLen && Effects.StrictObserve pol P k

def initialState (baseAddr a v b : Nat) : MachineState :=
  { x0 := baseAddr
  , x1 := v
  , x2 := 0
  , sp := 0x8000
  , pc := 0x1000
  , retAddr := 0x2000
  , baseAddr := baseAddr
  , slot0 := a
  , slot1 := b }

def slot0FootprintPolicy (baseAddr : Nat) : FootprintPolicy :=
  { codeBase := 0x1000
  , codeLen := 16
  , readBase := baseAddr
  , readLen := 8
  , writeBase := baseAddr
  , writeLen := 8 }

/--
1. **Return-value-only observation cannot distinguish `str x1, [x0]` from `str x1, [x0, #8]`:**
   Under `Executable.eval`, both programs return `x0 = a` and reach `pc = retAddr`.
-/
theorem return_value_only_cannot_distinguish (baseAddr a v b : Nat) :
    let s0 := initialState baseAddr a v b
    (Executable.eval (execLeaf positiveLeafProg s0)).map (fun s => (s.x0, s.pc)) =
      some (a, 0x2000) ∧
    (Executable.eval (execLeaf wrongSlotLeafProg s0)).map (fun s => (s.x0, s.pc)) =
      some (a, 0x2000) := by
  simp [initialState, positiveLeafProg, wrongSlotLeafProg, execLeaf, stepInstr,
        checkSPAlignment, MachineState.getReg, MachineState.setReg,
        MachineState.read64?, MachineState.write64?, Effects.bind, Executable.eval]

/--
2. **When `a = v`, even checking `s.x0 == a && s.slot0 == v` under `Effects.All`
   fails to reject the wrong-slot leaf `str x1, [x0, #8]`:**
   Because `slot0` already held `a = v` and `Effects.All` ignores
   `require_write_access (baseAddr + 8) 8`, `Effects.All` accepts the wrong-slot leaf!
-/
theorem effects_all_accepts_wrong_slot_when_equal (a b : Nat) :
    let s0 := initialState 0x4000 a a b
    Effects.All (fun s => (s.x0 == a) && (s.slot0 == a) && (s.pc == 0x2000))
      (execLeaf wrongSlotLeafProg s0) = true := by
  simp [initialState, wrongSlotLeafProg, execLeaf, stepInstr, checkSPAlignment,
        MachineState.getReg, MachineState.setReg, MachineState.read64?,
        MachineState.write64?, Effects.bind, Effects.All]

/--
3. **Full two-slot state `(s.x0, s.slot0, s.slot1)` distinguishes the positive leaf
   `(a, v, b)` from the wrong-slot leaf `(a, a, v)` whenever `v ≠ b` or `a ≠ v`:**
-/
theorem two_slot_state_discriminator (baseAddr a v b : Nat) :
    let s0 := initialState baseAddr a v b
    (Executable.eval (execLeaf positiveLeafProg s0)).map (fun s => (s.x0, s.slot0, s.slot1)) =
      some (a, v, b) ∧
    (Executable.eval (execLeaf wrongSlotLeafProg s0)).map (fun s => (s.x0, s.slot0, s.slot1)) =
      some (a, a, v) := by
  simp [initialState, positiveLeafProg, wrongSlotLeafProg, execLeaf, stepInstr,
        checkSPAlignment, MachineState.getReg, MachineState.setReg,
        MachineState.read64?, MachineState.write64?, Effects.bind, Executable.eval]

/--
4. **`Effects.StrictObserve` with the single-slot footprint `[0x4000, 0x4008)`
   accepts the positive leaf AND rejects the wrong-slot leaf even when `a = v = b`:**
   Because `require_write_access 0x4008 8` falls outside `writeBase = 0x4000, writeLen = 8`.
-/
theorem strict_observe_accepts_positive_leaf :
    let s0 := initialState 0x4000 42 99 7
    let pol := slot0FootprintPolicy 0x4000
    Effects.StrictObserve pol
      (fun s => (s.x0 == 42) && (s.slot0 == 99) && (s.slot1 == 7) && (s.pc == 0x2000))
      (execLeaf positiveLeafProg s0) = true := by
  decide

theorem strict_observe_rejects_wrong_slot_even_when_all_values_equal :
    let s0 := initialState 0x4000 42 42 42
    let pol := slot0FootprintPolicy 0x4000
    Effects.StrictObserve pol (fun _ => true)
      (execLeaf wrongSlotLeafProg s0) = false := by
  decide

/--
5. **Non-`SP` unaligned access (`baseAddr = 0x4004`, not 8-byte aligned):**
   Because `checkSPAlignment` only checks `.sp`, `Effects.All` accepts the positive
   leaf on `baseAddr = 0x4004`, whereas `Effects.StrictObserve` rejects it at
   `require_read_access 0x4004 8`.
-/
theorem effects_all_accepts_unaligned_x0_access :
    let s0 := initialState 0x4004 42 99 7
    Effects.All (fun s => (s.x0 == 42) && (s.slot0 == 99))
      (execLeaf positiveLeafProg s0) = true := by
  decide

theorem strict_observe_rejects_unaligned_x0_access :
    let s0 := initialState 0x4004 42 99 7
    let pol := slot0FootprintPolicy 0x4004
    Effects.StrictObserve pol (fun _ => true)
      (execLeaf positiveLeafProg s0) = false := by
  decide

end KrakenBridgeProbe
