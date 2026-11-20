/-
  MirToMiniMachO0Seed.lean

  Self-contained Lean v4.34.1 mechanization of:
  1. `SeedMir`: Stack-local MIR subset modeling `deinitMovedPlace = true`,
     three-state `LocalSlot` (`.dead`, `.live none`, `.live (some v)`),
     inhabited ZST preservation, `StorageLive`/`StorageDead`, and left-to-right
     operand evaluation.
  2. `MiniMachO0`: Non-optimizing stack-slot abstract machine with explicit
     `frameBytes <= 4096` single-page stack-frame bound and deterministic steps.
  3. `compileBody`: Direct non-optimizing `MirToMiniMachO0` compiler with
     `mirToMiniMachO0_forward_sim`, static move/liveness certificate
     checker `checkBodyInvs`, `mirToMiniMachO0_backward_sim`, and negative
     witness `cex_m4_move_then_copy_faults_in_mir_not_mach`.
  4. `two_step_bootstrap_sound`: Two-step verified checker bootstrap theorem
     eliminating unverified compiler TCBs from steady-state certificate
     checking, plus concrete Thompson-trojan rejection witness
     `witness_bootstrap_accepts_valid_and_rejects_thompson_trojan`.
-/

namespace MirToMiniMachO0Seed

/-! ## Section 0: Total List Helpers and Indexing Lemmas -/

def getAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt? xs n

def setAt? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match setAt? xs n v with
    | some xs' => some (x :: xs')
    | none => none

theorem getAt?_lt_length {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      getAt? xs i = some x → i < xs.length
  | [], _, _, h => by simp [getAt?] at h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, i + 1, _, h => by
    simp [getAt?] at h
    exact Nat.succ_lt_succ (getAt?_lt_length h)

theorem exists_getAt?_of_lt {α : Type} :
    ∀ {xs : List α} {i : Nat},
      i < xs.length → ∃ x, getAt? xs i = some x
  | [], i, h => by cases Nat.not_lt_zero i h
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => by
    have hlt : i < xs.length := Nat.lt_of_succ_lt_succ h
    simp [getAt?]
    exact exists_getAt?_of_lt (xs := xs) (i := i) hlt

theorem getAt?_some_of_setAt? {α : Type} :
    ∀ {xs xs' : List α} {i j : Nat} {v : α},
      setAt? xs i v = some xs' →
      (j = i → getAt? xs' j = some v) ∧
      (j ≠ i → getAt? xs' j = getAt? xs j)
  | [], _, _, _, _, h => by simp [setAt?] at h
  | _ :: xs, xs', 0, j, v, h => by
    simp [setAt?] at h
    subst xs'
    constructor
    · intro hj; subst hj; rfl
    · intro hj
      cases j with
      | zero => exact absurd rfl hj
      | succ k => rfl
  | x :: xs, xs', i + 1, j, v, h => by
    simp [setAt?] at h
    cases hs : setAt? xs i v with
    | none => simp [hs] at h
    | some ys =>
      simp [hs] at h
      subst xs'
      have ih := getAt?_some_of_setAt? (xs := xs) (xs' := ys) (i := i) (j := j - 1) (v := v) hs
      constructor
      · intro hj; subst hj; exact ih.1 rfl
      · intro hj
        cases j with
        | zero => rfl
        | succ k =>
          have hk : k ≠ i := fun hEq => hj (congrArg Nat.succ hEq)
          exact ih.2 hk

theorem setAt?_length {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      setAt? xs i v = some xs' → xs'.length = xs.length
  | [], _, _, _, h => by simp [setAt?] at h
  | _ :: xs, xs', 0, v, h => by
    simp [setAt?] at h
    subst xs'
    rfl
  | _ :: xs, xs', i + 1, v, h => by
    simp [setAt?] at h
    cases hs : setAt? xs i v with
    | none => simp [hs] at h
    | some ys =>
      simp [hs] at h
      subst xs'
      simp [setAt?_length hs]

theorem exists_setAt?_of_lt {α : Type} :
    ∀ {xs : List α} {i : Nat} (v : α),
      i < xs.length → ∃ xs', setAt? xs i v = some xs'
  | [], i, _, h => by cases Nat.not_lt_zero i h
  | _ :: xs, 0, v, _ => ⟨v :: xs, rfl⟩
  | x :: xs, i + 1, v, h => by
    have hlt : i < xs.length := Nat.lt_of_succ_lt_succ h
    obtain ⟨ys, hys⟩ := exists_setAt?_of_lt (xs := xs) (i := i) v hlt
    exact ⟨x :: ys, by simp [setAt?, hys]⟩

/-! ## Section 1: `SeedMir` Syntax and Operational Semantics (`deinitMovedPlace = true`) -/

inductive IntWidth where
  | i8 | i16 | i32 | i64 | isize
  deriving DecidableEq, Repr

def IntWidth.mask : IntWidth → BitVec 64
  | .i8 => 0x00000000000000FF#64
  | .i16 => 0x000000000000FFFF#64
  | .i32 => 0x00000000FFFFFFFF#64
  | .i64 | .isize => 0xFFFFFFFFFFFFFFFF#64

def truncWord (w : IntWidth) (x : BitVec 64) : BitVec 64 :=
  x &&& w.mask

theorem truncWord_idem (w : IntWidth) (x : BitVec 64) :
    truncWord w (truncWord w x) = truncWord w x := by
  rw [truncWord, truncWord, BitVec.and_assoc, BitVec.and_self]

theorem truncWord_isize (x : BitVec 64) : truncWord .isize x = x :=
  BitVec.and_allOnes

inductive SeedTy where
  | bool
  | int (w : IntWidth) (signed : Bool)
  | unit
  | zstEnum (discr : BitVec 64)
  deriving DecidableEq, Repr

def isRuntimeStoredTy : SeedTy → Bool
  | .bool | .int _ _ => true
  | .unit | .zstEnum _ => false

def isPrimitiveReadableTy : SeedTy → Bool
  | .bool | .int _ _ => true
  | _ => false

inductive SeedVal where
  | bool (b : Bool)
  | scalar (w : IntWidth) (signed : Bool) (bits : BitVec 64)
  | unit
  | zstEnum (discr : BitVec 64)
  deriving DecidableEq, Repr

def encodeSeedVal : SeedVal → BitVec 64
  | .bool b => if b then 1#64 else 0#64
  | .scalar _ _ bits => bits
  | .unit => 0#64
  | .zstEnum d => d

def valHasTy : SeedVal → SeedTy → Bool
  | .bool _, .bool => true
  | .scalar w s bits, .int w' s' => (w == w') && (s == s') && (truncWord w bits == bits)
  | .unit, .unit => true
  | .zstEnum d, .zstEnum d' => d == d'
  | _, _ => false

inductive FaultKind where
  | undefined
  | unsupported
  deriving DecidableEq, Repr

inductive LocalSlot where
  | dead
  | live (val : Option SeedVal)
  deriving DecidableEq, Repr

/-- Mirrors `Trusted.MirSemantics.liveUninitSlot`: inhabited 0-byte ZSTs
    (`.unit`, 1-variant `.zstEnum`) remain initialized at their unique value
    across `StorageLive` and `Operand.move`, whereas non-ZST locals
    transition to `.live none`. -/
def liveUninitSlot : SeedTy → LocalSlot
  | .unit => .live (some .unit)
  | .zstEnum d => .live (some (.zstEnum d))
  | _ => .live none

inductive Operand where
  | copy (loc : Nat)
  | move (loc : Nat)
  | constVal (ty : SeedTy) (v : SeedVal)
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | bitAnd | bitOr | bitXor | shl | eq | ult | divChecked
  deriving DecidableEq, Repr

inductive UnOp where
  | not | neg
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (op : Operand)
  | binOp (op : BinOp) (lhs rhs : Operand)
  | unOp (op : UnOp) (opnd : Operand)
  | discrZst (loc : Nat)
  deriving DecidableEq, Repr

inductive Stmt where
  | assign (dst : Nat) (rv : Rvalue)
  | storageLive (loc : Nat)
  | storageDead (loc : Nat)
  | nop
  deriving DecidableEq, Repr

inductive Term where
  | goto (target : Nat)
  | switchInt (discr : Operand) (cases : List (BitVec 64 × Nat)) (otherwise : Nat)
  | assertNonZero (cond : Operand) (expected : Bool) (target : Nat)
  | return_
  | unreachable
  deriving DecidableEq, Repr

structure MirBlock where
  stmts : List Stmt
  term : Term
  deriving DecidableEq, Repr

structure MirBody where
  argCount : Nat
  locals : List SeedTy
  hasStorageAnn : List Bool
  blocks : List MirBlock
  deriving DecidableEq, Repr

structure MirState where
  bb : Nat
  slots : List LocalSlot
  deriving DecidableEq, Repr

inductive MirOutcome where
  | running (st : MirState)
  | returned (v : SeedVal)
  | panicked
  | fault (k : FaultKind)
  deriving DecidableEq, Repr

def evalOperandToSlot (bodyLocals : List SeedTy) (slots : List LocalSlot) :
    Operand → Except FaultKind (SeedTy × Option SeedVal × List LocalSlot)
  | .copy loc =>
    match getAt? bodyLocals loc, getAt? slots loc with
    | some ty, some (.live optVal) => .ok (ty, optVal, slots)
    | some _, some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .move loc =>
    match getAt? bodyLocals loc, getAt? slots loc with
    | some ty, some (.live optVal) =>
      match setAt? slots loc (liveUninitSlot ty) with
      | some slots' => .ok (ty, optVal, slots')
      | none => .error .unsupported
    | some _, some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .constVal ty v =>
    if valHasTy v ty then
      .ok (ty, some v, slots)
    else
      .error .unsupported

def evalPrimOperand (bodyLocals : List SeedTy) (slots : List LocalSlot)
    (opnd : Operand) : Except FaultKind (SeedVal × List LocalSlot) :=
  match evalOperandToSlot bodyLocals slots opnd with
  | .error k => .error k
  | .ok (ty, optVal, slots') =>
    if !isPrimitiveReadableTy ty then
      .error .unsupported
    else
      match optVal with
      | some v => .ok (v, slots')
      | none => .error .undefined

def evalBinOp (op : BinOp) (lhs rhs : SeedVal) : Except FaultKind SeedVal :=
  match lhs, rhs with
  | .scalar w s lb, .scalar w' s' rb =>
    if !(w == w' && s == s') then
      .error .unsupported
    else
      match op with
      | .add => .ok (.scalar w s (truncWord w (lb + rb)))
      | .sub => .ok (.scalar w s (truncWord w (lb - rb)))
      | .bitAnd => .ok (.scalar w s (truncWord w (lb &&& rb)))
      | .bitOr => .ok (.scalar w s (truncWord w (lb ||| rb)))
      | .bitXor => .ok (.scalar w s (truncWord w (lb ^^^ rb)))
      | .shl => .ok (.scalar w s (truncWord w (lb <<< (rb &&& 63#64))))
      | .eq => .ok (.bool (lb == rb))
      | .ult => .ok (.bool (lb < rb))
      | .divChecked =>
        if s then
          .error .unsupported
        else if rb == 0#64 then
          .error .undefined
        else
          .ok (.scalar w false (truncWord w (lb / rb)))
  | .bool l, .bool r =>
    match op with
    | .bitAnd => .ok (.bool (l && r))
    | .bitOr => .ok (.bool (l || r))
    | .bitXor => .ok (.bool (l != r))
    | .eq => .ok (.bool (l == r))
    | _ => .error .unsupported
  | _, _ => .error .unsupported

def evalUnOp (op : UnOp) (v : SeedVal) : Except FaultKind SeedVal :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | .not, .scalar w s bits => .ok (.scalar w s (truncWord w (~~~bits)))
  | .neg, .scalar w true bits => .ok (.scalar w true (truncWord w (0#64 - bits)))
  | _, _ => .error .unsupported

def evalRvalue (bodyLocals : List SeedTy) (slots : List LocalSlot)
    (dstTy : SeedTy) : Rvalue → Except FaultKind (SeedVal × List LocalSlot)
  | .use opnd =>
    match evalOperandToSlot bodyLocals slots opnd with
    | .error k => .error k
    | .ok (srcTy, optVal, slots₁) =>
      if !(srcTy == dstTy) then
        .error .unsupported
      else
        match optVal with
        | some v => .ok (v, slots₁)
        | none => .error .undefined
  | .binOp op lhs rhs =>
    match evalPrimOperand bodyLocals slots lhs with
    | .error k => .error k
    | .ok (lv, slots₁) =>
      match evalPrimOperand bodyLocals slots₁ rhs with
      | .error k => .error k
      | .ok (rv, slots₂) =>
        match evalBinOp op lv rv with
        | .error k => .error k
        | .ok res => .ok (res, slots₂)
  | .unOp op opnd =>
    match evalPrimOperand bodyLocals slots opnd with
    | .error k => .error k
    | .ok (v, slots₁) =>
      match evalUnOp op v with
      | .error k => .error k
      | .ok res => .ok (res, slots₁)
  | .discrZst loc =>
    match getAt? bodyLocals loc, getAt? slots loc with
    | some (.zstEnum d), some (.live _) =>
      if dstTy == .int .isize false then
        .ok (.scalar .isize false d, slots)
      else
        .error .unsupported
    | some (.zstEnum _), some .dead => .error .undefined
    | _, _ => .error .unsupported

def writePlace (slots : List LocalSlot) (dst : Nat) (dstTy : SeedTy)
    (v : SeedVal) : Except FaultKind (List LocalSlot) :=
  if !valHasTy v dstTy then
    .error .unsupported
  else
    match getAt? slots dst with
    | none => .error .unsupported
    | some .dead => .error .undefined
    | some (.live _) =>
      match setAt? slots dst (.live (some v)) with
      | some slots' => .ok slots'
      | none => .error .unsupported

def evalStmt (bodyLocals : List SeedTy) (slots : List LocalSlot) :
    Stmt → Except FaultKind (List LocalSlot)
  | .nop => .ok slots
  | .storageLive loc =>
    match getAt? bodyLocals loc with
    | none => .error .unsupported
    | some ty =>
      match setAt? slots loc (liveUninitSlot ty) with
      | some slots' => .ok slots'
      | none => .error .unsupported
  | .storageDead loc =>
    if loc == 0 then
      .error .unsupported
    else
      match setAt? slots loc .dead with
      | some slots' => .ok slots'
      | none => .error .unsupported
  | .assign dst rv =>
    match getAt? bodyLocals dst with
    | none => .error .unsupported
    | some dstTy =>
      match evalRvalue bodyLocals slots dstTy rv with
      | .error k => .error k
      | .ok (v, slots₁) => writePlace slots₁ dst dstTy v

def evalStmts (bodyLocals : List SeedTy) (slots : List LocalSlot) :
    List Stmt → Except FaultKind (List LocalSlot)
  | [] => .ok slots
  | s :: rest =>
    match evalStmt bodyLocals slots s with
    | .error k => .error k
    | .ok slots' => evalStmts bodyLocals slots' rest

def evalSwitchCases (w : IntWidth) (bits : BitVec 64) (otherwise : Nat) :
    List (BitVec 64 × Nat) → Except FaultKind Nat
  | [] => .ok otherwise
  | (c, tgt) :: rest =>
    if truncWord w c != c then
      .error .unsupported
    else if truncWord w bits == truncWord w c then
      .ok tgt
    else
      evalSwitchCases w bits otherwise rest

def evalBoolSwitchCases (b : Bool) (otherwise : Nat) :
    List (BitVec 64 × Nat) → Except FaultKind Nat
  | [] => .ok otherwise
  | (c, tgt) :: rest =>
    if c == 0#64 then
      if !b then .ok tgt else evalBoolSwitchCases b otherwise rest
    else if c == 1#64 then
      if b then .ok tgt else evalBoolSwitchCases b otherwise rest
    else if c.toNat < 256 then
      .error .undefined
    else
      .error .unsupported

def evalTerm (bodyLocals : List SeedTy) (slots : List LocalSlot) :
    Term → MirOutcome
  | .goto tgt => .running { bb := tgt, slots := slots }
  | .unreachable => .fault .undefined
  | .return_ =>
    match getAt? slots 0 with
    | some (.live (some v)) => .returned v
    | some (.live none) | some .dead => .fault .undefined
    | none => .fault .unsupported
  | .switchInt discr cases otherwise =>
    match evalPrimOperand bodyLocals slots discr with
    | .error k => .fault k
    | .ok (v, slots₁) =>
      let res :=
        match v with
        | .scalar w _ bits => evalSwitchCases w bits otherwise cases
        | .bool b => evalBoolSwitchCases b otherwise cases
        | _ => .error .unsupported
      match res with
      | .error k => .fault k
      | .ok tgt => .running { bb := tgt, slots := slots₁ }
  | .assertNonZero cond expected tgt =>
    match evalPrimOperand bodyLocals slots cond with
    | .error k => .fault k
    | .ok (v, slots₁) =>
      let okCond : Except FaultKind Bool :=
        match v with
        | .bool b => .ok (b == expected)
        | .scalar _ _ bits => .ok ((bits != 0#64) == expected)
        | _ => .error .unsupported
      match okCond with
      | .error k => .fault k
      | .ok true => .running { bb := tgt, slots := slots₁ }
      | .ok false => .panicked

def stepMirBlock (body : MirBody) (st : MirState) : MirOutcome :=
  match getAt? body.blocks st.bb with
  | none => .fault .unsupported
  | some blk =>
    match evalStmts body.locals st.slots blk.stmts with
    | .error k => .fault k
    | .ok slots' => evalTerm body.locals slots' blk.term

def runMirBlocks (body : MirBody) : Nat → MirState → MirOutcome
  | 0, st => .running st
  | n + 1, st =>
    match stepMirBlock body st with
    | .running st' => runMirBlocks body n st'
    | out => out

def initMirSlotsAux (argCount : Nat) (args : List SeedVal) (anns : List Bool) :
    Nat → List SeedTy → List LocalSlot
  | _, [] => []
  | idx, ty :: rest =>
    let sl : LocalSlot :=
      if idx == 0 then
        liveUninitSlot ty
      else if idx <= argCount then
        match getAt? args (idx - 1) with
        | some v => .live (some v)
        | none => .dead
      else
        match getAt? anns idx with
        | some true => .dead
        | _ => liveUninitSlot ty
    sl :: initMirSlotsAux argCount args anns (idx + 1) rest

def checkEntryArgsAux (argCount : Nat) (args : List SeedVal) : Nat → List SeedTy → Bool
  | _, [] => args.length == argCount
  | idx, ty :: rest =>
    if idx == 0 then
      checkEntryArgsAux argCount args 1 rest
    else if idx <= argCount then
      match getAt? args (idx - 1) with
      | some v => valHasTy v ty && checkEntryArgsAux argCount args (idx + 1) rest
      | none => false
    else
      args.length == argCount

def initMirState (body : MirBody) (args : List SeedVal) : Option MirState :=
  if 0 < body.locals.length && body.argCount < body.locals.length &&
      checkEntryArgsAux body.argCount args 0 body.locals then
    some { bb := 0, slots := initMirSlotsAux body.argCount args body.hasStorageAnn 0 body.locals }
  else
    none

/-! ## Section 2: `MiniMachO0` Stack-Frame Machine -/

inductive Reg where
  | r0 | r1 | r2
  deriving DecidableEq, Repr

inductive MachInsn where
  | movImm (dst : Reg) (imm : BitVec 64)
  | loadSlot (dst : Reg) (slot : Nat)
  | storeSlot (slot : Nat) (src : Reg)
  | alu2 (dst : Reg) (op : BinOp) (lhs rhs : Reg) (w : Option IntWidth)
  | boolNot (dst : Reg)
  | bitNot (dst : Reg) (w : IntWidth)
  | negW (dst : Reg) (w : IntWidth)
  | trapIfZero (src : Reg)
  deriving DecidableEq, Repr

inductive MachTerm where
  | jmp (target : Nat)
  | brTable (reg : Reg) (cases : List (BitVec 64 × Nat)) (otherwise : Nat)
  | assertMach (reg : Reg) (expected : Bool) (target : Nat)
  | retSlot0 (zstImm? : Option (BitVec 64))
  | ud2Abort
  deriving DecidableEq, Repr

structure MachBlock where
  insns : List MachInsn
  term : MachTerm
  deriving DecidableEq, Repr

structure MachBody where
  frameSlots : Nat
  frameBytes : Nat
  blocks : List MachBlock
  deriving DecidableEq, Repr

structure MachState where
  bb : Nat
  r0 : BitVec 64
  r1 : BitVec 64
  r2 : BitVec 64
  frame : List (BitVec 64)
  deriving DecidableEq, Repr

inductive MachOutcome where
  | running (st : MachState)
  | returned (word : BitVec 64)
  | panicked
  | stuck
  deriving DecidableEq, Repr

def readReg (st : MachState) : Reg → BitVec 64
  | .r0 => st.r0
  | .r1 => st.r1
  | .r2 => st.r2

def writeReg (st : MachState) (v : BitVec 64) : Reg → MachState
  | .r0 => { st with r0 := v }
  | .r1 => { st with r1 := v }
  | .r2 => { st with r2 := v }

@[inline] def evalMachAlu2Raw (op : BinOp) (lv rv : BitVec 64) : BitVec 64 :=
  match op with
  | .add => lv + rv
  | .sub => lv - rv
  | .bitAnd => lv &&& rv
  | .bitOr => lv ||| rv
  | .bitXor => lv ^^^ rv
  | .shl => lv <<< (rv &&& 63#64)
  | .eq => if lv == rv then 1#64 else 0#64
  | .ult => if lv < rv then 1#64 else 0#64
  | .divChecked => if rv == 0#64 then 0#64 else lv / rv

def evalMachAlu2 (op : BinOp) (lv rv : BitVec 64) : Option IntWidth → BitVec 64
  | none => evalMachAlu2Raw op lv rv
  | some iw =>
    match op with
    | .eq | .ult => evalMachAlu2Raw op lv rv
    | _ => truncWord iw (evalMachAlu2Raw op lv rv)

def execMachInsn (st : MachState) : MachInsn → Option MachState
  | .movImm dst imm => some (writeReg st imm dst)
  | .loadSlot dst slot =>
    match getAt? st.frame slot with
    | some w => some (writeReg st w dst)
    | none => none
  | .storeSlot slot src =>
    match setAt? st.frame slot (readReg st src) with
    | some fr' => some { st with frame := fr' }
    | none => none
  | .alu2 dst op lhs rhs w =>
    let res := evalMachAlu2 op (readReg st lhs) (readReg st rhs) w
    some (writeReg st res dst)
  | .boolNot dst =>
    some (writeReg st (1#64 ^^^ readReg st dst) dst)
  | .bitNot dst w =>
    some (writeReg st (truncWord w (~~~readReg st dst)) dst)
  | .negW dst w =>
    some (writeReg st (truncWord w (0#64 - readReg st dst)) dst)
  | .trapIfZero src =>
    if readReg st src == 0#64 then none else some st

def execMachInsns (st : MachState) : List MachInsn → Option MachState
  | [] => some st
  | ins :: rest =>
    match execMachInsn st ins with
    | some st' => execMachInsns st' rest
    | none => none

def execBrTable (v : BitVec 64) (otherwise : Nat) : List (BitVec 64 × Nat) → Nat
  | [] => otherwise
  | (c, tgt) :: rest => if v == c then tgt else execBrTable v otherwise rest

def execMachTerm (st : MachState) : MachTerm → MachOutcome
  | .jmp tgt => .running { st with bb := tgt }
  | .ud2Abort => .stuck
  | .retSlot0 zstImm? =>
    match zstImm? with
    | some imm => .returned imm
    | none =>
      match getAt? st.frame 0 with
      | some w => .returned w
      | none => .stuck
  | .brTable reg cases otherwise =>
    let tgt := execBrTable (readReg st reg) otherwise cases
    .running { st with bb := tgt }
  | .assertMach reg expected target =>
    if ((readReg st reg != 0#64) == expected) then
      .running { st with bb := target }
    else
      .panicked

def stepMachBlock (body : MachBody) (st : MachState) : MachOutcome :=
  match getAt? body.blocks st.bb with
  | none => .stuck
  | some blk =>
    match execMachInsns st blk.insns with
    | none => .stuck
    | some st' => execMachTerm st' blk.term

def runMachBlocks (body : MachBody) : Nat → MachState → MachOutcome
  | 0, st => .running st
  | n + 1, st =>
    match stepMachBlock body st with
    | .running st' => runMachBlocks body n st'
    | out => out

def initMachFrameAux (argCount : Nat) (args : List SeedVal) :
    Nat → List SeedTy → List (BitVec 64)
  | _, [] => []
  | idx, _ :: rest =>
    let w : BitVec 64 :=
      if idx == 0 then 0#64
      else if idx <= argCount then
        match getAt? args (idx - 1) with
        | some v => encodeSeedVal v
        | none => 0#64
      else 0#64
    w :: initMachFrameAux argCount args (idx + 1) rest

def initMachState (body : MirBody) (args : List SeedVal) : MachState :=
  { bb := 0, r0 := 0#64, r1 := 0#64, r2 := 0#64,
    frame := initMachFrameAux body.argCount args 0 body.locals }

/-! ## Section 3: Direct Non-Optimizing `MirToMiniMachO0` Compiler & Simulation -/

def checkOperandTy (locals : List SeedTy) : Operand → Option SeedTy
  | .copy loc | .move loc => getAt? locals loc
  | .constVal ty v => if valHasTy v ty then some ty else none

def compileOperand (dst : Reg) : Operand → List MachInsn
  | .copy loc | .move loc => [.loadSlot dst loc]
  | .constVal _ v => [.movImm dst (encodeSeedVal v)]

def binOpResultTy (op : BinOp) (lty rty : SeedTy) : Option (SeedTy × Option IntWidth) :=
  match lty, rty with
  | .int w s, .int w' s' =>
    if !(w == w' && s == s') then
      none
    else
      match op with
      | .eq | .ult => some (.bool, some w)
      | .divChecked => if s then none else some (.int w false, some w)
      | _ => some (.int w s, some w)
  | .bool, .bool =>
    match op with
    | .bitAnd | .bitOr | .bitXor | .eq => some (.bool, none)
    | _ => none
  | _, _ => none

def unOpResultTy (op : UnOp) (ty : SeedTy) : Option SeedTy :=
  match op, ty with
  | .not, .bool => some .bool
  | .not, .int w s => some (.int w s)
  | .neg, .int w true => some (.int w true)
  | _, _ => none

def compileRvalue (locals : List SeedTy) (dstTy : SeedTy) :
    Rvalue → Option (List MachInsn)
  | .use opnd =>
    match checkOperandTy locals opnd with
    | none => none
    | some srcTy =>
      if srcTy == dstTy then
        if isRuntimeStoredTy dstTy then some (compileOperand .r0 opnd) else some []
      else none
  | .binOp op lhs rhs =>
    match checkOperandTy locals lhs, checkOperandTy locals rhs with
    | some lty, some rty =>
      match binOpResultTy op lty rty with
      | some (resTy, wOpt) =>
        if resTy == dstTy then
          let guard := match op with | .divChecked => [.trapIfZero .r1] | _ => []
          some (compileOperand .r0 lhs ++ compileOperand .r1 rhs ++ guard ++
                [.alu2 .r0 op .r0 .r1 wOpt])
        else none
      | none => none
    | _, _ => none
  | .unOp op opnd =>
    match checkOperandTy locals opnd with
    | some ty =>
      match unOpResultTy op ty with
      | some resTy =>
        if resTy == dstTy then
          let opInsn :=
            match op, ty with
            | .not, .bool => [.boolNot .r0]
            | .not, .int w _ => [.bitNot .r0 w]
            | .neg, .int w true => [.negW .r0 w]
            | _, _ => []
          some (compileOperand .r0 opnd ++ opInsn)
        else none
      | none => none
    | none => none
  | .discrZst loc =>
    match getAt? locals loc with
    | some (.zstEnum d) =>
      if dstTy == .int .isize false then some [.movImm .r0 d] else none
    | _ => none

def compileStmt (locals : List SeedTy) : Stmt → Option (List MachInsn)
  | .nop => some []
  | .storageLive loc =>
    match getAt? locals loc with
    | some _ => some []
    | none => none
  | .storageDead loc =>
    if loc == 0 then none
    else
      match getAt? locals loc with
      | some _ => some []
      | none => none
  | .assign dst rv =>
    match getAt? locals dst with
    | none => none
    | some dstTy =>
      match compileRvalue locals dstTy rv with
      | none => none
      | some code =>
        if isRuntimeStoredTy dstTy then
          some (code ++ [.storeSlot dst .r0])
        else
          some code

def compileStmts (locals : List SeedTy) : List Stmt → Option (List MachInsn)
  | [] => some []
  | s :: rest =>
    match compileStmt locals s, compileStmts locals rest with
    | some c₁, some c₂ => some (c₁ ++ c₂)
    | _, _ => none

def validSwitchCases (numBlocks : Nat) (ty : SeedTy) :
    List (BitVec 64 × Nat) → Bool
  | [] => true
  | (c, tgt) :: rest =>
    let okC :=
      match ty with
      | .int w _ => truncWord w c == c
      | .bool => (c == 0#64) || (c == 1#64)
      | _ => false
    okC && (tgt < numBlocks) && validSwitchCases numBlocks ty rest

def compileTerm (locals : List SeedTy) (numBlocks : Nat) :
    Term → Option (List MachInsn × MachTerm)
  | .goto tgt =>
    if tgt < numBlocks then some ([], .jmp tgt) else none
  | .unreachable => some ([], .ud2Abort)
  | .return_ =>
    match getAt? locals 0 with
    | some .unit => some ([], .retSlot0 (some 0#64))
    | some (.zstEnum d) => some ([], .retSlot0 (some d))
    | some _ => some ([], .retSlot0 none)
    | none => none
  | .switchInt discr cases otherwise =>
    match checkOperandTy locals discr with
    | some ty =>
      if isPrimitiveReadableTy ty && (otherwise < numBlocks) &&
          validSwitchCases numBlocks ty cases then
        some (compileOperand .r0 discr, .brTable .r0 cases otherwise)
      else none
    | none => none
  | .assertNonZero cond expected tgt =>
    match checkOperandTy locals cond with
    | some ty =>
      if isPrimitiveReadableTy ty && (tgt < numBlocks) then
        some (compileOperand .r0 cond, .assertMach .r0 expected tgt)
      else none
    | none => none

def compileBlock (locals : List SeedTy) (numBlocks : Nat) (blk : MirBlock) :
    Option MachBlock :=
  match compileStmts locals blk.stmts, compileTerm locals numBlocks blk.term with
  | some insns1, some (insns2, term') =>
    some { insns := insns1 ++ insns2, term := term' }
  | _, _ => none

def compileBlocks (locals : List SeedTy) (numBlocks : Nat) :
    List MirBlock → Option (List MachBlock)
  | [] => some []
  | b :: rest =>
    match compileBlock locals numBlocks b, compileBlocks locals numBlocks rest with
    | some mb, some mrest => some (mb :: mrest)
    | _, _ => none

/-- Direct non-optimizing stack-slot compiler `compileBody`.
    Enforces single-page guard-page bound `locals.length * 8 <= 4096`. -/
def compileBody (body : MirBody) : Option MachBody :=
  let frameBytes := body.locals.length * 8
  if !(0 < body.locals.length && body.argCount < body.locals.length &&
      0 < body.blocks.length && frameBytes <= 4096) then
    none
  else
    match compileBlocks body.locals body.blocks.length body.blocks with
    | none => none
    | some mblks =>
      some { frameSlots := body.locals.length, frameBytes := frameBytes, blocks := mblks }

/-! ### Simulation Invariant (`MatchSlot`, `MatchStateInv`) -/

def MatchSlot (ty : SeedTy) (sl : LocalSlot) (w : BitVec 64) : Prop :=
  match sl with
  | .dead => True
  | .live none => True
  | .live (some v) =>
    valHasTy v ty = true ∧ (isRuntimeStoredTy ty = true → w = encodeSeedVal v)

structure MatchStateInv (tys : List SeedTy) (slots : List LocalSlot)
    (frame : List (BitVec 64)) : Prop where
  len_slots : slots.length = tys.length
  len_frame : frame.length = tys.length
  slot_ok : ∀ i ty, getAt? tys i = some ty →
    ∃ sl w, getAt? slots i = some sl ∧ getAt? frame i = some w ∧ MatchSlot ty sl w

theorem execMachInsns_append (st : MachState) (c₁ c₂ : List MachInsn) :
    execMachInsns st (c₁ ++ c₂) =
      match execMachInsns st c₁ with
      | some st' => execMachInsns st' c₂
      | none => none := by
  induction c₁ generalizing st with
  | nil => rfl
  | cons i rest ih =>
    simp [execMachInsns]
    cases hi : execMachInsn st i with
    | none => simp
    | some st₁ => simp [ih st₁]

theorem compileBlocks_getAt? (locals : List SeedTy) (numBlocks : Nat) :
    ∀ {blks : List MirBlock} {mblks : List MachBlock} {i : Nat} {blk : MirBlock},
      compileBlocks locals numBlocks blks = some mblks →
      getAt? blks i = some blk →
      ∃ mblk, getAt? mblks i = some mblk ∧ compileBlock locals numBlocks blk = some mblk
  | [], _, _, _, _, hg => by simp [getAt?] at hg
  | b :: rest, mblks, 0, blk, hcb, hg => by
    simp [getAt?] at hg
    subst blk
    simp [compileBlocks] at hcb
    cases hb : compileBlock locals numBlocks b <;> cases hr : compileBlocks locals numBlocks rest <;>
      simp [hb, hr] at hcb
    subst mblks
    exact ⟨_, rfl, rfl⟩
  | b :: rest, mblks, i + 1, blk, hcb, hg => by
    simp [getAt?] at hg
    simp [compileBlocks] at hcb
    cases hb : compileBlock locals numBlocks b <;> cases hr : compileBlocks locals numBlocks rest <;>
      simp [hb, hr] at hcb
    subst mblks
    simp [getAt?]
    exact compileBlocks_getAt? locals numBlocks hr hg

theorem move_deinit_preserves_inv {tys : List SeedTy} {slots slots' : List LocalSlot}
    {frame : List (BitVec 64)} {loc : Nat} {ty : SeedTy}
    (hInv : MatchStateInv tys slots frame)
    (hTy : getAt? tys loc = some ty)
    (hSet : setAt? slots loc (liveUninitSlot ty) = some slots') :
    MatchStateInv tys slots' frame := by
  constructor
  · rw [setAt?_length hSet, hInv.len_slots]
  · exact hInv.len_frame
  · intro i tyi hTyi
    obtain ⟨sl, w, hSl, hW, hMatch⟩ := hInv.slot_ok i tyi hTyi
    have hGet := getAt?_some_of_setAt? (j := i) hSet
    by_cases hij : i = loc
    · subst hij
      rw [hTy] at hTyi
      cases hTyi
      refine ⟨liveUninitSlot ty, w, hGet.1 rfl, hW, ?_⟩
      cases ty with
      | unit => simp [liveUninitSlot, MatchSlot, valHasTy, isRuntimeStoredTy]
      | zstEnum d => simp [liveUninitSlot, MatchSlot, valHasTy, isRuntimeStoredTy]
      | bool => simp [liveUninitSlot, MatchSlot]
      | int _ _ => simp [liveUninitSlot, MatchSlot]
    · exact ⟨sl, w, by rw [hGet.2 hij]; exact hSl, hW, hMatch⟩

theorem storageDead_preserves_inv {tys : List SeedTy} {slots slots' : List LocalSlot}
    {frame : List (BitVec 64)} {loc : Nat}
    (hInv : MatchStateInv tys slots frame)
    (hSet : setAt? slots loc .dead = some slots') :
    MatchStateInv tys slots' frame := by
  constructor
  · rw [setAt?_length hSet, hInv.len_slots]
  · exact hInv.len_frame
  · intro i tyi hTyi
    obtain ⟨sl, w, hSl, hW, hMatch⟩ := hInv.slot_ok i tyi hTyi
    have hGet := getAt?_some_of_setAt? (j := i) hSet
    by_cases hij : i = loc
    · refine ⟨.dead, w, hGet.1 hij, hW, trivial⟩
    · exact ⟨sl, w, by rw [hGet.2 hij]; exact hSl, hW, hMatch⟩

theorem assign_write_preserves_inv {tys : List SeedTy} {slots slots' : List LocalSlot}
    {frame frame' : List (BitVec 64)} {dst : Nat} {dstTy : SeedTy} {v : SeedVal}
    (hInv : MatchStateInv tys slots frame)
    (hTy : getAt? tys dst = some dstTy)
    (hValTy : valHasTy v dstTy = true)
    (hSetS : setAt? slots dst (.live (some v)) = some slots')
    (hSetF : isRuntimeStoredTy dstTy = true →
      setAt? frame dst (encodeSeedVal v) = some frame')
    (hUnchangedF : isRuntimeStoredTy dstTy = false → frame' = frame) :
    MatchStateInv tys slots' frame' := by
  constructor
  · rw [setAt?_length hSetS, hInv.len_slots]
  · cases hSt : isRuntimeStoredTy dstTy with
    | false => rw [hUnchangedF hSt, hInv.len_frame]
    | true => rw [setAt?_length (hSetF hSt), hInv.len_frame]
  · intro i tyi hTyi
    obtain ⟨sl, w, hSl, hW, hMatch⟩ := hInv.slot_ok i tyi hTyi
    have hGetS := getAt?_some_of_setAt? (j := i) hSetS
    cases hSt : isRuntimeStoredTy dstTy with
    | false =>
      have hFr : frame' = frame := hUnchangedF hSt
      subst frame'
      by_cases hij : i = dst
      · subst hij
        rw [hTy] at hTyi
        cases hTyi
        exact ⟨.live (some v), w, hGetS.1 rfl, hW, hValTy, fun h => by simp [hSt] at h⟩
      · exact ⟨sl, w, by rw [hGetS.2 hij]; exact hSl, hW, hMatch⟩
    | true =>
      have hSf := hSetF hSt
      have hGetF := getAt?_some_of_setAt? (j := i) hSf
      by_cases hij : i = dst
      · subst hij
        rw [hTy] at hTyi
        cases hTyi
        exact ⟨.live (some v), encodeSeedVal v, hGetS.1 rfl, hGetF.1 rfl,
          hValTy, fun _ => rfl⟩
      · exact ⟨sl, w, by rw [hGetS.2 hij]; exact hSl,
          by rw [hGetF.2 hij]; exact hW, hMatch⟩

theorem compileOperand_sim {tys : List SeedTy} {slots slots' : List LocalSlot}
    {st : MachState} {opnd : Operand} {reg : Reg} {ty : SeedTy} {v : SeedVal}
    (hInv : MatchStateInv tys slots st.frame)
    (hEval : evalOperandToSlot tys slots opnd = .ok (ty, some v, slots')) :
    MatchStateInv tys slots' st.frame ∧
    (isRuntimeStoredTy ty = true →
      execMachInsns st (compileOperand reg opnd) = some (writeReg st (encodeSeedVal v) reg)) := by
  cases opnd with
  | copy loc =>
    simp [evalOperandToSlot] at hEval
    cases hTy : getAt? tys loc with
    | none => simp [hTy] at hEval
    | some ty0 =>
      cases hSl : getAt? slots loc with
      | none => simp [hTy, hSl] at hEval
      | some sl0 =>
        cases sl0 with
        | dead => simp [hTy, hSl] at hEval
        | live optV =>
          simp [hTy, hSl] at hEval
          rcases hEval with ⟨rfl, rfl, rfl⟩
          refine ⟨hInv, ?_⟩
          intro hStored
          obtain ⟨sl1, w1, hSl1, hW1, hMatch⟩ := hInv.slot_ok loc ty0 hTy
          rw [hSl] at hSl1
          cases hSl1
          have hEqW : w1 = encodeSeedVal v := hMatch.2 hStored
          simp [compileOperand, execMachInsns, execMachInsn, hW1, hEqW]
  | move loc =>
    simp [evalOperandToSlot] at hEval
    cases hTy : getAt? tys loc with
    | none => simp [hTy] at hEval
    | some ty0 =>
      cases hSl : getAt? slots loc with
      | none => simp [hTy, hSl] at hEval
      | some sl0 =>
        cases sl0 with
        | dead => simp [hTy, hSl] at hEval
        | live optV =>
          cases hSet : setAt? slots loc (liveUninitSlot ty0) with
          | none => simp [hTy, hSl, hSet] at hEval
          | some sls' =>
            simp [hTy, hSl, hSet] at hEval
            rcases hEval with ⟨rfl, rfl, rfl⟩
            refine ⟨move_deinit_preserves_inv hInv hTy hSet, ?_⟩
            intro hStored
            obtain ⟨sl1, w1, hSl1, hW1, hMatch⟩ := hInv.slot_ok loc ty0 hTy
            rw [hSl] at hSl1
            cases hSl1
            have hEqW : w1 = encodeSeedVal v := hMatch.2 hStored
            simp [compileOperand, execMachInsns, execMachInsn, hW1, hEqW]
  | constVal cty cv =>
    simp [evalOperandToSlot] at hEval
    cases hV : valHasTy cv cty with
    | false => simp [hV] at hEval
    | true =>
      simp [hV] at hEval
      rcases hEval with ⟨rfl, rfl, rfl⟩
      refine ⟨hInv, fun _ => ?_⟩
      simp [compileOperand, execMachInsns, execMachInsn]

theorem evalPrimOperand_sim {tys : List SeedTy} {slots slots' : List LocalSlot}
    {st : MachState} {opnd : Operand} {reg : Reg} {v : SeedVal}
    (hInv : MatchStateInv tys slots st.frame)
    (hEval : evalPrimOperand tys slots opnd = .ok (v, slots')) :
    ∃ ty, checkOperandTy tys opnd = some ty ∧ isPrimitiveReadableTy ty = true ∧
      valHasTy v ty = true ∧ MatchStateInv tys slots' st.frame ∧
      execMachInsns st (compileOperand reg opnd) = some (writeReg st (encodeSeedVal v) reg) := by
  unfold evalPrimOperand at hEval
  cases hOp : evalOperandToSlot tys slots opnd with
  | error k => simp [hOp] at hEval
  | ok res =>
    rcases res with ⟨ty, optV, sls'⟩
    simp [hOp] at hEval
    cases hPrim : isPrimitiveReadableTy ty with
    | false => simp [hPrim] at hEval
    | true =>
      simp [hPrim] at hEval
      cases optV with
      | none => simp at hEval
      | some v0 =>
        simp at hEval
        rcases hEval with ⟨rfl, rfl⟩
        have ⟨hInv', hMach⟩ := compileOperand_sim (reg := reg) hInv hOp
        have hStored : isRuntimeStoredTy ty = true := by
          cases ty <;> simp [isPrimitiveReadableTy] at hPrim <;> rfl
        have hMach' := hMach hStored
        have hCk : checkOperandTy tys opnd = some ty ∧ valHasTy v0 ty = true := by
          cases opnd with
          | copy loc =>
            simp [evalOperandToSlot] at hOp
            cases hT : getAt? tys loc <;> simp [hT] at hOp
            cases hS : getAt? slots loc <;> simp [hS] at hOp
            rename_i sl; cases sl <;> simp at hOp
            rcases hOp with ⟨rfl, rfl, rfl⟩
            obtain ⟨sl1, _, hSl1, _, hMatch⟩ := hInv.slot_ok loc _ hT
            rw [hS] at hSl1; cases hSl1
            exact ⟨by simp [checkOperandTy, hT], hMatch.1⟩
          | move loc =>
            simp [evalOperandToSlot] at hOp
            cases hT : getAt? tys loc <;> simp [hT] at hOp
            rename_i ty0
            cases hS : getAt? slots loc <;> simp [hS] at hOp
            rename_i sl; cases sl <;> simp at hOp
            cases hSet : setAt? slots loc (liveUninitSlot ty0) <;> simp [hSet] at hOp
            rcases hOp with ⟨rfl, rfl, rfl⟩
            obtain ⟨sl1, _, hSl1, _, hMatch⟩ := hInv.slot_ok loc _ hT
            rw [hS] at hSl1; cases hSl1
            exact ⟨by simp [checkOperandTy, hT], hMatch.1⟩
          | constVal cty cv =>
            simp [evalOperandToSlot] at hOp
            cases hV : valHasTy cv cty <;> simp [hV] at hOp
            rcases hOp with ⟨rfl, rfl, rfl⟩
            exact ⟨by simp [checkOperandTy, hV], hV⟩
        exact ⟨ty, hCk.1, hPrim, hCk.2, hInv', hMach'⟩

theorem evalBinOp_sim (op : BinOp) (lv rv res : SeedVal) (lty rty resTy : SeedTy)
    (wOpt : Option IntWidth)
    (hlTy : valHasTy lv lty = true) (hrTy : valHasTy rv rty = true)
    (hTy : binOpResultTy op lty rty = some (resTy, wOpt))
    (hEval : evalBinOp op lv rv = .ok res) :
    valHasTy res resTy = true ∧
    evalMachAlu2 op (encodeSeedVal lv) (encodeSeedVal rv) wOpt = encodeSeedVal res := by
  cases lv <;> cases rv <;> cases lty <;> cases rty <;>
    simp [valHasTy] at hlTy hrTy <;>
    simp [evalBinOp, binOpResultTy] at hTy hEval ⊢
  case scalar.scalar.int.int w1 s1 b1 w2 s2 b2 iw1 sg1 iw2 sg2 =>
    rcases hlTy with ⟨⟨rfl, rfl⟩, _⟩
    rcases hrTy with ⟨⟨rfl, rfl⟩, _⟩
    rcases hTy with ⟨⟨rfl, rfl⟩, hTyRes⟩
    cases op with
    | divChecked =>
      cases s1 with
      | true => simp at hTyRes
      | false =>
        simp at hTyRes hEval
        rcases hTyRes with ⟨rfl, rfl⟩
        by_cases hZero : b2 = 0#64
        · simp [hZero] at hEval
        · simp [hZero] at hEval
          subst res
          refine ⟨by simp [valHasTy, truncWord_idem], ?_⟩
          have hZb : (b2 == 0#64) = false := beq_false_of_ne hZero
          unfold evalMachAlu2 evalMachAlu2Raw
          simp [encodeSeedVal, hZb]
    | eq =>
      simp at hTyRes hEval
      rcases hTyRes with ⟨rfl, rfl⟩
      subst res
      refine ⟨by simp [valHasTy], ?_⟩
      unfold evalMachAlu2 evalMachAlu2Raw
      simp [encodeSeedVal]
    | ult =>
      simp at hTyRes hEval
      rcases hTyRes with ⟨rfl, rfl⟩
      subst res
      refine ⟨by simp [valHasTy], ?_⟩
      unfold evalMachAlu2 evalMachAlu2Raw
      simp [encodeSeedVal]
      by_cases hb : b1 < b2 <;> simp [hb]
    | add | sub | bitAnd | bitOr | bitXor | shl =>
      simp at hTyRes hEval
      rcases hTyRes with ⟨rfl, rfl⟩
      subst res
      refine ⟨by simp [valHasTy, truncWord_idem], ?_⟩
      unfold evalMachAlu2 evalMachAlu2Raw
      rfl
  case bool.bool.bool.bool lb rb =>
    cases op <;> simp at hTy hEval
    all_goals
      rcases hTy with ⟨rfl, rfl⟩
      subst res
      refine ⟨rfl, ?_⟩
      unfold evalMachAlu2 evalMachAlu2Raw
      cases lb <;> cases rb <;> rfl

theorem evalUnOp_sim (op : UnOp) (v res : SeedVal) (ty resTy : SeedTy)
    (hvTy : valHasTy v ty = true)
    (hTy : unOpResultTy op ty = some resTy)
    (hEval : evalUnOp op v = .ok res) :
    valHasTy res resTy = true ∧
    match op, ty with
    | .not, .bool => (1#64 ^^^ encodeSeedVal v) = encodeSeedVal res
    | .not, .int w _ => truncWord w (~~~encodeSeedVal v) = encodeSeedVal res
    | .neg, .int w true => truncWord w (0#64 - encodeSeedVal v) = encodeSeedVal res
    | _, _ => False := by
  cases v <;> cases ty <;> simp [valHasTy] at hvTy <;>
    simp [evalUnOp, unOpResultTy] at hTy hEval
  case bool.bool b =>
    cases op <;> simp at hTy hEval
    subst resTy; subst res
    refine ⟨rfl, ?_⟩
    dsimp
    clear hvTy hTy hEval
    decide +revert
  case scalar.int =>
    rcases hvTy with ⟨⟨rfl, rfl⟩, _⟩
    cases op with
    | not =>
      simp at hTy hEval
      subst resTy; subst res
      exact ⟨by simp [valHasTy, truncWord_idem], rfl⟩
    | neg =>
      cases ‹Bool› <;> simp at hTy hEval
      subst resTy; subst res
      exact ⟨by simp [valHasTy, truncWord_idem], rfl⟩

theorem compileRvalue_sim {tys : List SeedTy} {slots slots' : List LocalSlot}
    {st : MachState} {dstTy : SeedTy} {rv : Rvalue} {v : SeedVal}
    {insns : List MachInsn}
    (hInv : MatchStateInv tys slots st.frame)
    (hComp : compileRvalue tys dstTy rv = some insns)
    (hEval : evalRvalue tys slots dstTy rv = .ok (v, slots')) :
    MatchStateInv tys slots' st.frame ∧
    valHasTy v dstTy = true ∧
    (isRuntimeStoredTy dstTy = true →
      ∃ st', execMachInsns st insns = some st' ∧
        st'.frame = st.frame ∧ st'.bb = st.bb ∧ st'.r0 = encodeSeedVal v) := by
  cases rv with
  | use opnd =>
    simp [evalRvalue] at hEval
    cases hOp : evalOperandToSlot tys slots opnd with
    | error k => simp [hOp] at hEval
    | ok res =>
      rcases res with ⟨srcTy, optV, sls₁⟩
      simp [hOp] at hEval
      by_cases hEq : srcTy = dstTy
      · subst hEq
        simp at hEval
        cases optV with
        | none => simp at hEval
        | some v0 =>
          simp at hEval
          rcases hEval with ⟨rfl, rfl⟩
          have ⟨hInv', hMach⟩ := compileOperand_sim (reg := .r0) hInv hOp
          have hValTy : valHasTy v0 srcTy = true := by
            cases opnd with
            | copy loc =>
              simp [evalOperandToSlot] at hOp
              cases hT : getAt? tys loc <;> simp [hT] at hOp
              cases hS : getAt? slots loc <;> simp [hS] at hOp
              rename_i sl; cases sl <;> simp at hOp
              rcases hOp with ⟨rfl, rfl, rfl⟩
              obtain ⟨sl1, _, hSl1, _, hMatch⟩ := hInv.slot_ok loc _ hT
              rw [hS] at hSl1; cases hSl1
              exact hMatch.1
            | move loc =>
              simp [evalOperandToSlot] at hOp
              cases hT : getAt? tys loc <;> simp [hT] at hOp
              rename_i ty0
              cases hS : getAt? slots loc <;> simp [hS] at hOp
              rename_i sl; cases sl <;> simp at hOp
              cases hSet : setAt? slots loc (liveUninitSlot ty0) <;> simp [hSet] at hOp
              rcases hOp with ⟨rfl, rfl, rfl⟩
              obtain ⟨sl1, _, hSl1, _, hMatch⟩ := hInv.slot_ok loc _ hT
              rw [hS] at hSl1; cases hSl1
              exact hMatch.1
            | constVal cty cv =>
              simp [evalOperandToSlot] at hOp
              cases hV : valHasTy cv cty <;> simp [hV] at hOp
              rcases hOp with ⟨rfl, rfl, rfl⟩; exact hV
          refine ⟨hInv', hValTy, ?_⟩
          intro hStored
          simp [compileRvalue] at hComp
          cases hCk : checkOperandTy tys opnd with
          | none => simp [hCk] at hComp
          | some ckTy =>
            simp [hCk] at hComp
            have hCkEq : ckTy = srcTy := by
              cases opnd with
              | copy loc =>
                simp [evalOperandToSlot] at hOp
                cases hT : getAt? tys loc <;> simp [hT] at hOp
                cases hS : getAt? slots loc <;> simp [hS] at hOp
                rename_i sl; cases sl <;> simp at hOp
                simp [checkOperandTy, hT] at hCk; rw [← hCk]; exact hOp.1
              | move loc =>
                simp [evalOperandToSlot] at hOp
                cases hT : getAt? tys loc <;> simp [hT] at hOp
                rename_i ty0
                cases hS : getAt? slots loc <;> simp [hS] at hOp
                rename_i sl; cases sl <;> simp at hOp
                cases hSet : setAt? slots loc (liveUninitSlot ty0) <;> simp [hSet] at hOp
                simp [checkOperandTy, hT] at hCk; rw [← hCk]; exact hOp.1
              | constVal cty cv =>
                simp [evalOperandToSlot] at hOp
                cases hV : valHasTy cv cty <;> simp [hV] at hOp
                simp [checkOperandTy, hV] at hCk; rw [← hCk]; exact hOp.1
            subst hCkEq
            simp [hStored] at hComp
            subst insns
            exact ⟨writeReg st (encodeSeedVal v0) .r0, hMach hStored, rfl, rfl, rfl⟩
      · simp [hEq] at hEval
  | binOp op lhs rhs =>
    simp [evalRvalue] at hEval
    cases hL : evalPrimOperand tys slots lhs with
    | error k => simp [hL] at hEval
    | ok resL =>
      rcases resL with ⟨lv, sls₁⟩
      simp [hL] at hEval
      cases hR : evalPrimOperand tys sls₁ rhs with
      | error k => simp [hR] at hEval
      | ok resR =>
        rcases resR with ⟨rv', sls₂⟩
        simp [hR] at hEval
        cases hB : evalBinOp op lv rv' with
        | error k => simp [hB] at hEval
        | ok resV =>
          simp [hB] at hEval
          rcases hEval with ⟨rfl, rfl⟩
          obtain ⟨lty, hCkL, _, hlValTy, hInv₁, hMachL⟩ := evalPrimOperand_sim (reg := .r0) hInv hL
          have hInv₁' : MatchStateInv tys sls₁ (writeReg st (encodeSeedVal lv) .r0).frame := by
            simpa [writeReg] using hInv₁
          obtain ⟨rty, hCkR, _, hrValTy, hInv₂, hMachR⟩ :=
            evalPrimOperand_sim (reg := .r1) hInv₁' hR
          simp [compileRvalue, hCkL, hCkR] at hComp
          cases hResTy : binOpResultTy op lty rty with
          | none => simp [hResTy] at hComp
          | some p =>
            rcases p with ⟨resTy, wOpt⟩
            simp [hResTy] at hComp
            by_cases hEqTy : resTy = dstTy
            · subst hEqTy
              simp at hComp
              obtain ⟨hResValTy, hAlu⟩ := evalBinOp_sim op lv rv' resV lty rty resTy wOpt hlValTy hrValTy hResTy hB
              refine ⟨by simpa [writeReg] using hInv₂, hResValTy, fun _ => ?_⟩
              subst insns
              rw [execMachInsns_append, hMachL]; dsimp
              rw [execMachInsns_append, hMachR]; dsimp
              rw [execMachInsns_append]
              cases op with
              | divChecked =>
                cases lv <;> cases rv' <;> simp [evalBinOp] at hB
                rename_i w1 s1 b1 w2 s2 b2
                by_cases hZero : b2 = 0#64
                · split at hB
                  · simp at hB
                  · cases s1 <;> simp at hB
                · have hZb : (b2 == 0#64) = false := beq_false_of_ne hZero
                  simp [execMachInsns, execMachInsn, readReg, writeReg, encodeSeedVal, hZb]
                  simpa [encodeSeedVal] using hAlu
              | add | sub | bitAnd | bitOr | bitXor | shl | eq | ult =>
                simp [execMachInsns, execMachInsn, readReg, writeReg, hAlu]
            · simp [hEqTy] at hComp
  | unOp op opnd =>
    simp [evalRvalue] at hEval
    cases hO : evalPrimOperand tys slots opnd with
    | error k => simp [hO] at hEval
    | ok resO =>
      rcases resO with ⟨v0, sls₁⟩
      simp [hO] at hEval
      cases hU : evalUnOp op v0 with
      | error k => simp [hU] at hEval
      | ok resV =>
        simp [hU] at hEval
        rcases hEval with ⟨rfl, rfl⟩
        obtain ⟨ty0, hCkO, _, hvValTy, hInv₁, hMachO⟩ := evalPrimOperand_sim (reg := .r0) hInv hO
        simp [compileRvalue, hCkO] at hComp
        cases hResTy : unOpResultTy op ty0 with
        | none => simp [hResTy] at hComp
        | some resTy =>
          simp [hResTy] at hComp
          by_cases hEqTy : resTy = dstTy
          · subst hEqTy
            simp at hComp
            obtain ⟨hResValTy, hUn⟩ := evalUnOp_sim op v0 resV ty0 resTy hvValTy hResTy hU
            refine ⟨by simpa [writeReg] using hInv₁, hResValTy, fun _ => ?_⟩
            subst insns
            rw [execMachInsns_append, hMachO]
            cases op <;> cases ty0 <;> simp [unOpResultTy] at hResTy
            · simp [execMachInsns, execMachInsn, readReg, writeReg]
              exact hUn
            · simp [execMachInsns, execMachInsn, readReg, writeReg]
              exact hUn
            · cases ‹Bool› <;> simp at hResTy
              simp [execMachInsns, execMachInsn, readReg, writeReg]
              exact hUn
          · simp [hEqTy] at hComp
  | discrZst loc =>
    simp [evalRvalue] at hEval
    cases hT : getAt? tys loc with
    | none => simp [hT] at hEval
    | some ty0 =>
      cases ty0 with
      | zstEnum d =>
        cases hS : getAt? slots loc with
        | none => simp [hT, hS] at hEval
        | some sl0 =>
          cases sl0 with
          | dead => simp [hT, hS] at hEval
          | live _ =>
            simp [hT, hS] at hEval
            by_cases hDt : dstTy = .int .isize false
            · subst hDt
              simp at hEval
              rcases hEval with ⟨rfl, rfl⟩
              simp [compileRvalue, hT] at hComp
              subst insns
              refine ⟨hInv, ?_, fun _ => ?_⟩
              · simp [valHasTy, truncWord_isize]
              · exact ⟨writeReg st d .r0, by simp [execMachInsns, execMachInsn], rfl, rfl, rfl⟩
            · simp [hDt] at hEval
      | bool | int _ _ | unit => simp [hT] at hEval

theorem binOpResultTy_runtimeStored {op : BinOp} {lty rty resTy : SeedTy} {w : Option IntWidth}
    (h : binOpResultTy op lty rty = some (resTy, w)) : isRuntimeStoredTy resTy = true := by
  cases lty <;> cases rty <;> simp [binOpResultTy] at h
  · cases op <;> simp at h <;> rcases h with ⟨rfl, _⟩ <;> rfl
  · rcases h with ⟨_, hM⟩
    cases op <;> simp at hM
    all_goals
      try (rcases hM with ⟨rfl, _⟩; rfl)
    rcases hM with ⟨_, rfl, _⟩; rfl

theorem unOpResultTy_runtimeStored {op : UnOp} {ty resTy : SeedTy}
    (h : unOpResultTy op ty = some resTy) : isRuntimeStoredTy resTy = true := by
  cases op <;> cases ty <;> simp [unOpResultTy] at h
  · subst h; rfl
  · subst h; rfl
  · cases ‹Bool› <;> simp at h
    subst h; rfl

theorem compileStmt_sim {tys : List SeedTy} {slots slots' : List LocalSlot}
    {st : MachState} {s : Stmt} {insns : List MachInsn}
    (hInv : MatchStateInv tys slots st.frame)
    (hComp : compileStmt tys s = some insns)
    (hEval : evalStmt tys slots s = .ok slots') :
    ∃ st', execMachInsns st insns = some st' ∧ st'.bb = st.bb ∧
      MatchStateInv tys slots' st'.frame := by
  cases s with
  | nop =>
    simp [compileStmt] at hComp; simp [evalStmt] at hEval
    subst insns; subst slots'
    exact ⟨st, rfl, rfl, hInv⟩
  | storageLive loc =>
    simp [compileStmt] at hComp; simp [evalStmt] at hEval
    cases hTy : getAt? tys loc with
    | none => simp [hTy] at hComp
    | some ty0 =>
      simp [hTy] at hComp hEval
      cases hSet : setAt? slots loc (liveUninitSlot ty0) with
      | none => simp [hSet] at hEval
      | some sls' =>
        simp [hSet] at hEval
        subst insns; subst slots'
        exact ⟨st, rfl, rfl, move_deinit_preserves_inv hInv hTy hSet⟩
  | storageDead loc =>
    simp [compileStmt] at hComp; simp [evalStmt] at hEval
    by_cases hZ : loc = 0
    · subst hZ; simp at hComp
    · simp [hZ] at hComp hEval
      cases hTy : getAt? tys loc with
      | none => simp [hTy] at hComp
      | some _ =>
        simp [hTy] at hComp
        cases hSet : setAt? slots loc .dead with
        | none => simp [hSet] at hEval
        | some sls' =>
          simp [hSet] at hEval
          subst insns; subst slots'
          exact ⟨st, rfl, rfl, storageDead_preserves_inv hInv hSet⟩
  | assign dst rv =>
    simp [compileStmt] at hComp; simp [evalStmt] at hEval
    cases hTy : getAt? tys dst with
    | none => simp [hTy] at hComp
    | some dstTy =>
      simp [hTy] at hComp hEval
      cases hCRv : compileRvalue tys dstTy rv with
      | none => simp [hCRv] at hComp
      | some code =>
        simp [hCRv] at hComp
        cases hERv : evalRvalue tys slots dstTy rv with
        | error k => simp [hERv] at hEval
        | ok res =>
          rcases res with ⟨v, sls₁⟩
          simp [hERv] at hEval
          obtain ⟨hInv₁, hValTy, hExecRv⟩ := compileRvalue_sim hInv hCRv hERv
          unfold writePlace at hEval
          simp [hValTy] at hEval
          cases hSlDst : getAt? sls₁ dst with
          | none => simp [hSlDst] at hEval
          | some slDst =>
            cases slDst with
            | dead => simp [hSlDst] at hEval
            | live _ =>
              simp [hSlDst] at hEval
              cases hSetS : setAt? sls₁ dst (.live (some v)) with
              | none => simp [hSetS] at hEval
              | some sls₂ =>
                simp [hSetS] at hEval
                subst slots'
                cases hStored : isRuntimeStoredTy dstTy with
                | false =>
                  simp [hStored] at hComp
                  subst insns
                  have hCodeExec : ∃ st', execMachInsns st code = some st' ∧
                      st'.bb = st.bb ∧ st'.frame = st.frame := by
                    cases rv with
                    | use opnd =>
                      simp [compileRvalue] at hCRv
                      cases hCk : checkOperandTy tys opnd <;> simp [hCk, hStored] at hCRv
                      rcases hCRv with ⟨_, rfl⟩
                      exact ⟨st, rfl, rfl, rfl⟩
                    | binOp op lhs rhs =>
                      simp [compileRvalue] at hCRv
                      cases hCkL : checkOperandTy tys lhs <;>
                        cases hCkR : checkOperandTy tys rhs <;> simp [hCkL, hCkR] at hCRv
                      rename_i lty rty
                      cases hBt : binOpResultTy op lty rty with
                      | none => simp [hBt] at hCRv
                      | some p =>
                        rcases p with ⟨rTy, wOpt⟩
                        simp [hBt] at hCRv
                        have hEq : rTy = dstTy := hCRv.1
                        have hSt := binOpResultTy_runtimeStored hBt
                        rw [hEq, hStored] at hSt
                        cases hSt
                    | unOp op opnd =>
                      simp [compileRvalue] at hCRv
                      cases hCk : checkOperandTy tys opnd <;> simp [hCk] at hCRv
                      rename_i ty0
                      cases hUt : unOpResultTy op ty0 <;> simp [hUt] at hCRv
                      rcases hCRv with ⟨hEq, _⟩
                      have hSt := unOpResultTy_runtimeStored hUt
                      rw [hEq, hStored] at hSt
                      cases hSt
                    | discrZst loc =>
                      simp [compileRvalue] at hCRv
                      cases hT : getAt? tys loc <;> simp [hT] at hCRv
                      rename_i zty
                      cases zty with
                      | bool | int _ _ | unit => simp at hCRv
                      | zstEnum d =>
                        simp at hCRv
                        rcases hCRv with ⟨hEq, _⟩
                        rw [hEq] at hStored
                        cases hStored
                  obtain ⟨st₁, hExec₁, hBb₁, hFr₁⟩ := hCodeExec
                  refine ⟨st₁, hExec₁, hBb₁, ?_⟩
                  rw [hFr₁]
                  exact assign_write_preserves_inv hInv₁ hTy hValTy hSetS
                    (fun h => by simp [hStored] at h) (fun _ => rfl)
                | true =>
                  simp [hStored] at hComp
                  subst insns
                  obtain ⟨st₁, hExec₁, hFr₁, hBb₁, hR0₁⟩ := hExecRv hStored
                  have hLtDst : dst < st₁.frame.length := by
                    rw [hFr₁, hInv₁.len_frame]; exact getAt?_lt_length hTy
                  obtain ⟨fr₂, hSetF⟩ := exists_setAt?_of_lt (encodeSeedVal v) hLtDst
                  refine ⟨{ st₁ with frame := fr₂ }, ?_, hBb₁, ?_⟩
                  · rw [execMachInsns_append, hExec₁]
                    simp [execMachInsns, execMachInsn, readReg, hR0₁, hSetF]
                  · exact assign_write_preserves_inv hInv₁ hTy hValTy hSetS
                      (fun _ => by rw [← hFr₁]; exact hSetF)
                      (fun h => by simp [hStored] at h)

theorem compileStmts_sim {tys : List SeedTy} {slots slots' : List LocalSlot}
    {st : MachState} {stmts : List Stmt} {insns : List MachInsn}
    (hInv : MatchStateInv tys slots st.frame)
    (hComp : compileStmts tys stmts = some insns)
    (hEval : evalStmts tys slots stmts = .ok slots') :
    ∃ st', execMachInsns st insns = some st' ∧ st'.bb = st.bb ∧
      MatchStateInv tys slots' st'.frame := by
  induction stmts generalizing slots st insns with
  | nil =>
    simp [compileStmts] at hComp; simp [evalStmts] at hEval
    subst insns; subst slots'
    exact ⟨st, rfl, rfl, hInv⟩
  | cons s rest ih =>
    simp [compileStmts] at hComp; simp [evalStmts] at hEval
    cases hCs : compileStmt tys s <;> cases hCr : compileStmts tys rest <;>
      simp [hCs, hCr] at hComp
    cases hEs : evalStmt tys slots s with
    | error k => simp [hEs] at hEval
    | ok sls₁ =>
      simp [hEs] at hEval
      subst insns
      obtain ⟨st₁, hExec₁, hBb₁, hInv₁⟩ := compileStmt_sim hInv hCs hEs
      obtain ⟨st₂, hExec₂, hBb₂, hInv₂⟩ := ih hInv₁ hCr hEval
      refine ⟨st₂, ?_, hBb₂.trans hBb₁, hInv₂⟩
      rw [execMachInsns_append, hExec₁]
      simp [hExec₂]

theorem switchCases_sim (w : IntWidth) (bits : BitVec 64) (otherwise tgt : Nat)
    (cases : List (BitVec 64 × Nat))
    (hW : truncWord w bits = bits)
    (hEval : evalSwitchCases w bits otherwise cases = .ok tgt) :
    execBrTable bits otherwise cases = tgt := by
  induction cases with
  | nil =>
    simp [evalSwitchCases] at hEval
    simp [execBrTable, hEval]
  | cons hd rest ih =>
    rcases hd with ⟨c, cTgt⟩
    simp [evalSwitchCases] at hEval
    by_cases hTrunc : truncWord w c = c
    · simp [hTrunc, hW] at hEval
      by_cases hb : bits = c
      · simp [hb] at hEval
        have hB1 : (bits == c) = true := beq_iff_eq.mpr hb
        simp [execBrTable, hB1, hEval]
      · have hB0 : (bits == c) = false := beq_false_of_ne hb
        simp [hb] at hEval
        simp [execBrTable, hB0]
        exact ih hEval
    · simp [hTrunc] at hEval

theorem boolSwitchCases_sim (b : Bool) (otherwise tgt : Nat)
    (cases : List (BitVec 64 × Nat))
    (hEval : evalBoolSwitchCases b otherwise cases = .ok tgt) :
    execBrTable (if b then 1#64 else 0#64) otherwise cases = tgt := by
  induction cases with
  | nil =>
    simp [evalBoolSwitchCases] at hEval
    simp [execBrTable, hEval]
  | cons hd rest ih =>
    rcases hd with ⟨c, cTgt⟩
    simp [evalBoolSwitchCases] at hEval
    by_cases hc0 : c = 0#64
    · subst hc0
      cases b with
      | false =>
        simp at hEval
        simp [execBrTable, hEval]
      | true =>
        simp at hEval
        simp [execBrTable]
        exact ih hEval
    · simp [hc0] at hEval
      by_cases hc1 : c = 1#64
      · subst hc1
        cases b with
        | false =>
          simp at hEval
          simp [execBrTable]
          exact ih hEval
        | true =>
          simp at hEval
          simp [execBrTable, hEval]
      · simp [hc1] at hEval
        split at hEval <;> simp at hEval

theorem block_step_forward_sim {body : MirBody} {mbody : MachBody}
    {mirSt : MirState} {machSt : MachState}
    (hComp : compileBody body = some mbody)
    (hBb : machSt.bb = mirSt.bb)
    (hInv : MatchStateInv body.locals mirSt.slots machSt.frame)
    (hNoFault : ∀ k, stepMirBlock body mirSt ≠ .fault k) :
    match stepMirBlock body mirSt, stepMachBlock mbody machSt with
    | .running mirSt', .running machSt' =>
      machSt'.bb = mirSt'.bb ∧ MatchStateInv body.locals mirSt'.slots machSt'.frame
    | .returned v, .returned w => w = encodeSeedVal v
    | .panicked, .panicked => True
    | _, _ => False := by
  dsimp [compileBody] at hComp
  cases hCBlks : compileBlocks body.locals body.blocks.length body.blocks with
  | none => simp [hCBlks] at hComp
  | some mblks =>
    simp [hCBlks] at hComp
    rcases hComp with ⟨_, rfl⟩
    unfold stepMirBlock stepMachBlock
    ·
      cases hGetBlk : getAt? body.blocks mirSt.bb with
      | none =>
        have hF : stepMirBlock body mirSt = .fault .unsupported := by
          simp [stepMirBlock, hGetBlk]
        exact absurd hF (hNoFault .unsupported)
      | some blk =>
        obtain ⟨mblk, hGetMBlk, hCBlk⟩ := compileBlocks_getAt? body.locals body.blocks.length hCBlks hGetBlk
        rw [hBb, hGetMBlk]
        simp [compileBlock] at hCBlk
        cases hCS : compileStmts body.locals blk.stmts <;>
          cases hCT : compileTerm body.locals body.blocks.length blk.term <;>
          simp [hCS, hCT] at hCBlk
        rename_i insns1 p; rcases p with ⟨insns2, mterm⟩
        subst mblk
        cases hES : evalStmts body.locals mirSt.slots blk.stmts with
        | error k =>
          have hF : stepMirBlock body mirSt = .fault k := by
            simp [stepMirBlock, hGetBlk, hES]
          exact absurd hF (hNoFault k)
        | ok sls₁ =>
          obtain ⟨st₁, hExec₁, _, hInv₁⟩ := compileStmts_sim hInv hCS hES
          dsimp; rw [hES]; dsimp
          rw [execMachInsns_append, hExec₁]; dsimp
          cases hTerm : blk.term with
          | goto tgt =>
            simp [compileTerm, hTerm] at hCT
            rcases hCT with ⟨_, rfl, rfl⟩
            simp [evalTerm, execMachInsns, execMachTerm]
            exact hInv₁
          | unreachable =>
            have hF : stepMirBlock body mirSt = .fault .undefined := by
              simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm]
            exact absurd hF (hNoFault .undefined)
          | return_ =>
            simp [compileTerm, hTerm] at hCT
            cases hT0 : getAt? body.locals 0 with
            | none => simp [hT0] at hCT
            | some retTy =>
              simp [hT0] at hCT
              simp [evalTerm]
              obtain ⟨sl0, w0, hSl0, hW0, hMatch0⟩ := hInv₁.slot_ok 0 retTy hT0
              rw [hSl0]
              cases sl0 with
              | dead =>
                have hF : stepMirBlock body mirSt = .fault .undefined := by
                  simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hSl0]
                exact absurd hF (hNoFault .undefined)
              | live optV =>
                cases optV with
                | none =>
                  have hF : stepMirBlock body mirSt = .fault .undefined := by
                    simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hSl0]
                  exact absurd hF (hNoFault .undefined)
                | some retV =>
                  cases retTy with
                  | unit =>
                    simp at hCT
                    rcases hCT with ⟨rfl, rfl⟩
                    cases retV <;> simp [MatchSlot, valHasTy] at hMatch0
                    simp [execMachInsns, execMachTerm, encodeSeedVal]
                  | zstEnum d =>
                    simp at hCT
                    rcases hCT with ⟨rfl, rfl⟩
                    cases retV <;> simp [MatchSlot, valHasTy] at hMatch0
                    simp [execMachInsns, execMachTerm, encodeSeedVal, hMatch0.1]
                  | bool | int _ _ =>
                    simp at hCT
                    rcases hCT with ⟨rfl, rfl⟩
                    simp [execMachInsns, execMachTerm, hW0]
                    exact hMatch0.2 rfl
          | switchInt discr cases otherwise =>
            simp [compileTerm, hTerm] at hCT
            cases hCkD : checkOperandTy body.locals discr with
            | none => simp [hCkD] at hCT
            | some dTy =>
              simp [hCkD] at hCT
              rcases hCT with ⟨_, rfl, rfl⟩
              simp [evalTerm]
              cases hEvD : evalPrimOperand body.locals sls₁ discr with
              | error k =>
                have hF : stepMirBlock body mirSt = .fault k := by
                  simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hEvD]
                exact absurd hF (hNoFault k)
              | ok resD =>
                rcases resD with ⟨dVal, sls₂⟩
                obtain ⟨dTy', hCkD', hPrim', hValTy', hInv₂, hExecD⟩ :=
                  evalPrimOperand_sim (reg := .r0) hInv₁ hEvD
                rw [hExecD]; dsimp
                cases dVal with
                | unit | zstEnum _ =>
                  have hF : stepMirBlock body mirSt = .fault .unsupported := by
                    simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hEvD]
                  exact absurd hF (hNoFault .unsupported)
                | scalar w s bits =>
                  simp
                  cases hSw : evalSwitchCases w bits otherwise cases with
                  | error k =>
                    have hF : stepMirBlock body mirSt = .fault k := by
                      simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hEvD, hSw]
                    exact absurd hF (hNoFault k)
                  | ok tgt =>
                    have hWb : truncWord w bits = bits := by
                      rw [hCkD] at hCkD'; cases dTy' <;> simp [valHasTy] at hValTy'
                      exact hValTy'.2
                    have hBr := switchCases_sim w bits otherwise tgt cases hWb hSw
                    simp [execMachTerm, readReg, writeReg, encodeSeedVal, hBr]
                    simpa [writeReg] using hInv₂
                | bool b =>
                  simp
                  cases hSw : evalBoolSwitchCases b otherwise cases with
                  | error k =>
                    have hF : stepMirBlock body mirSt = .fault k := by
                      simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hEvD, hSw]
                    exact absurd hF (hNoFault k)
                  | ok tgt =>
                    have hBr := boolSwitchCases_sim b otherwise tgt cases hSw
                    simp [execMachTerm, readReg, writeReg, encodeSeedVal, hBr]
                    simpa [writeReg] using hInv₂
          | assertNonZero cond expected tgt =>
            simp [compileTerm, hTerm] at hCT
            cases hCkC : checkOperandTy body.locals cond with
            | none => simp [hCkC] at hCT
            | some cTy =>
              simp [hCkC] at hCT
              rcases hCT with ⟨_, rfl, rfl⟩
              simp [evalTerm]
              cases hEvC : evalPrimOperand body.locals sls₁ cond with
              | error k =>
                have hF : stepMirBlock body mirSt = .fault k := by
                  simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hEvC]
                exact absurd hF (hNoFault k)
              | ok resC =>
                rcases resC with ⟨cVal, sls₂⟩
                obtain ⟨_, _, _, _, hInv₂, hExecC⟩ :=
                  evalPrimOperand_sim (reg := .r0) hInv₁ hEvC
                rw [hExecC]; dsimp
                cases cVal with
                | unit | zstEnum _ =>
                  have hF : stepMirBlock body mirSt = .fault .unsupported := by
                    simp [stepMirBlock, hGetBlk, hES, evalTerm, hTerm, hEvC]
                  exact absurd hF (hNoFault .unsupported)
                | bool b =>
                  cases b <;> cases expected <;>
                    simp [execMachTerm, readReg, writeReg, encodeSeedVal]
                  · exact hInv₂
                  · exact hInv₂
                | scalar w s bits =>
                  by_cases hb : bits = 0#64
                  · subst hb; cases expected <;>
                      simp [execMachTerm, readReg, writeReg, encodeSeedVal]
                    exact hInv₂
                  · have hNz : (bits != 0#64) = true := by
                      cases hEq : (bits == 0#64)
                      · simp [bne, hEq]
                      · exact absurd (eq_of_beq hEq) hb
                    cases expected <;>
                      simp [execMachTerm, readReg, writeReg, encodeSeedVal, hNz]
                    exact hInv₂

theorem checkEntryArgsAux_gt (argCount : Nat) (args : List SeedVal) :
    ∀ (j : Nat) (tys : List SeedTy), argCount < j →
      checkEntryArgsAux argCount args j tys = (args.length == argCount)
  | _, [], _ => rfl
  | j, _ :: rest, hj => by
    have h0 : j ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le argCount) hj)
    have hle : ¬ j ≤ argCount := Nat.not_le_of_gt hj
    simp [checkEntryArgsAux, h0, hle]

theorem initMirSlots_match (argCount : Nat) (args : List SeedVal) (anns : List Bool)
    (idx : Nat) (tys : List SeedTy)
    (hArgs : checkEntryArgsAux argCount args idx tys = true) :
    ∀ k ty, getAt? tys k = some ty →
      ∃ sl w, getAt? (initMirSlotsAux argCount args anns idx tys) k = some sl ∧
        getAt? (initMachFrameAux argCount args idx tys) k = some w ∧
        MatchSlot ty sl w := by
  induction tys generalizing idx with
  | nil =>
    intro k ty hG; simp [getAt?] at hG
  | cons t rest ih =>
    intro k ty hG
    cases k with
    | zero =>
      simp [getAt?] at hG
      subst t
      simp [initMirSlotsAux, initMachFrameAux, getAt?]
      by_cases h0 : idx = 0
      · subst h0
        simp
        cases ty <;> simp [liveUninitSlot, MatchSlot, valHasTy, isRuntimeStoredTy]
      · simp [h0]
        by_cases hLe : idx <= argCount
        · simp [hLe]
          simp [checkEntryArgsAux, h0, hLe] at hArgs
          cases hArg : getAt? args (idx - 1) with
          | none => simp [hArg] at hArgs
          | some v =>
            simp [hArg] at hArgs
            exact ⟨hArgs.1, fun _ => rfl⟩
        · simp [hLe]
          split
          · exact trivial
          · cases ty <;> simp [liveUninitSlot, MatchSlot, valHasTy, isRuntimeStoredTy]
    | succ k' =>
      simp [getAt?] at hG
      dsimp [initMirSlotsAux, initMachFrameAux, getAt?]
      simp [checkEntryArgsAux] at hArgs
      have hRestArgs : checkEntryArgsAux argCount args (idx + 1) rest = true := by
        by_cases h0 : idx = 0
        · subst h0; exact hArgs
        · simp [h0] at hArgs
          by_cases hLe : idx ≤ argCount
          · simp [hLe] at hArgs
            cases hA : getAt? args (idx - 1) with
            | none => simp [hA] at hArgs
            | some v => simp [hA] at hArgs; exact hArgs.2
          · simp [hLe] at hArgs
            have hGt : argCount < idx + 1 := Nat.lt_of_lt_of_le (Nat.lt_of_not_le hLe) (Nat.le_succ _)
            rw [checkEntryArgsAux_gt argCount args (idx + 1) rest hGt]
            simp [hArgs]
      exact ih (idx + 1) hRestArgs k' ty hG

theorem initMirSlots_len (argCount : Nat) (args : List SeedVal) (anns : List Bool)
    (idx : Nat) (tys : List SeedTy) :
    (initMirSlotsAux argCount args anns idx tys).length = tys.length := by
  induction tys generalizing idx with
  | nil => rfl
  | cons _ _ ih => simp [initMirSlotsAux, ih]

theorem initMachFrame_len (argCount : Nat) (args : List SeedVal) (idx : Nat) (tys : List SeedTy) :
    (initMachFrameAux argCount args idx tys).length = tys.length := by
  induction tys generalizing idx with
  | nil => rfl
  | cons _ _ ih => simp [initMachFrameAux, ih]

theorem init_matchStateInv {body : MirBody} {args : List SeedVal} {mirSt0 : MirState}
    (hInit : initMirState body args = some mirSt0) :
    mirSt0.bb = 0 ∧ MatchStateInv body.locals mirSt0.slots (initMachState body args).frame := by
  unfold initMirState at hInit
  split at hInit
  · rename_i hCond
    simp at hCond
    cases hInit
    refine ⟨rfl, ?_⟩
    exact {
      len_slots := initMirSlots_len _ _ _ _ _
      len_frame := initMachFrame_len _ _ _ _
      slot_ok := initMirSlots_match body.argCount args body.hasStorageAnn 0 body.locals hCond.2
    }
  · contradiction

/-- End-to-end forward simulation from `SeedMir` (`deinitMovedPlace = true`)
    to `MiniMachO0` over arbitrary multi-block CFG fuel `n`. -/
theorem mirToMiniMachO0_forward_sim_from_state {body : MirBody} {mbody : MachBody}
    (hComp : compileBody body = some mbody) :
    ∀ n mirSt machSt,
      machSt.bb = mirSt.bb →
      MatchStateInv body.locals mirSt.slots machSt.frame →
      (∀ m st', m <= n → runMirBlocks body m mirSt = .running st' →
        ∀ k, stepMirBlock body st' ≠ .fault k) →
      (∀ k, runMirBlocks body n mirSt ≠ .fault k) →
      match runMirBlocks body n mirSt, runMachBlocks mbody n machSt with
      | .running mirSt', .running machSt' =>
        machSt'.bb = mirSt'.bb ∧ MatchStateInv body.locals mirSt'.slots machSt'.frame
      | .returned v, .returned w => w = encodeSeedVal v
      | .panicked, .panicked => True
      | _, _ => False
  | 0, mirSt, machSt, hBb, hInv, _, _ => ⟨hBb, hInv⟩
  | n + 1, mirSt, machSt, hBb, hInv, hAllNoFault, hNoFault => by
    have hStepNF : ∀ k, stepMirBlock body mirSt ≠ .fault k :=
      hAllNoFault 0 mirSt (Nat.zero_le _) rfl
    have hBlk := block_step_forward_sim hComp hBb hInv hStepNF
    simp [runMirBlocks, runMachBlocks]
    cases hM : stepMirBlock body mirSt <;> simp [hM] at hBlk
    · rename_i mirSt₁
      cases hC : stepMachBlock mbody machSt <;> simp [hC] at hBlk
      rename_i machSt₁
      have hSubAll : ∀ m st', m <= n → runMirBlocks body m mirSt₁ = .running st' →
          ∀ k, stepMirBlock body st' ≠ .fault k := by
        intro m st' hm hRun
        apply hAllNoFault (m + 1) st' (Nat.succ_le_succ hm)
        simp [runMirBlocks, hM, hRun]
      have hSubNF : ∀ k, runMirBlocks body n mirSt₁ ≠ .fault k := by
        intro k hk
        apply hNoFault k
        simp [runMirBlocks, hM, hk]
      exact mirToMiniMachO0_forward_sim_from_state hComp n mirSt₁ machSt₁ hBlk.1 hBlk.2 hSubAll hSubNF
    · cases hC : stepMachBlock mbody machSt <;> simp [hC] at hBlk
      exact hBlk
    · cases hC : stepMachBlock mbody machSt <;> simp [hC] at hBlk
      trivial

theorem mirToMiniMachO0_forward_sim {body : MirBody} {mbody : MachBody}
    {args : List SeedVal} {mirSt0 : MirState}
    (hComp : compileBody body = some mbody)
    (hInit : initMirState body args = some mirSt0)
    (n : Nat)
    (hAllNoFault : ∀ m st', m <= n → runMirBlocks body m mirSt0 = .running st' →
      ∀ k, stepMirBlock body st' ≠ .fault k)
    (hNoFault : ∀ k, runMirBlocks body n mirSt0 ≠ .fault k) :
    match runMirBlocks body n mirSt0, runMachBlocks mbody n (initMachState body args) with
    | .running mirSt', .running machSt' =>
      machSt'.bb = mirSt'.bb ∧ MatchStateInv body.locals mirSt'.slots machSt'.frame
    | .returned v, .returned w => w = encodeSeedVal v
    | .panicked, .panicked => True
    | _, _ => False := by
  obtain ⟨hBb, hInv⟩ := init_matchStateInv hInit
  exact mirToMiniMachO0_forward_sim_from_state hComp n mirSt0 (initMachState body args)
    hBb.symm hInv hAllNoFault hNoFault

/-! ### Static Move/Init/Liveness Certificate Checker & Backward Simulation -/

inductive AbsSlot where
  | dead | uninit | init
  deriving DecidableEq, Repr

def absSubsumes : AbsSlot → AbsSlot → Bool
  | .init, _ => true
  | .uninit, .uninit => true
  | .uninit, .dead => true
  | .dead, .dead => true
  | _, _ => false

def envSubsumes : List AbsSlot → List AbsSlot → Bool
  | [], [] => true
  | a :: as, b :: bs => absSubsumes a b && envSubsumes as bs
  | _, _ => false

def CompatSlot (ty : SeedTy) (sl : LocalSlot) (a : AbsSlot) : Prop :=
  match a with
  | .dead => True
  | .uninit => ∃ optV, sl = .live optV
  | .init => ∃ v, sl = .live (some v) ∧ valHasTy v ty = true

def CompatEnv (tys : List SeedTy) (slots : List LocalSlot) (env : List AbsSlot) : Prop :=
  slots.length = tys.length ∧ env.length = tys.length ∧
  ∀ i ty, getAt? tys i = some ty →
    ∃ sl a, getAt? slots i = some sl ∧ getAt? env i = some a ∧ CompatSlot ty sl a

theorem absSubsumes_compat {ty : SeedTy} {sl : LocalSlot} {a b : AbsSlot}
    (hSub : absSubsumes a b = true) (hC : CompatSlot ty sl a) :
    CompatSlot ty sl b := by
  cases a <;> cases b <;> simp [absSubsumes] at hSub
  · trivial
  · trivial
  · exact hC
  · trivial
  · rcases hC with ⟨v, hSl, _⟩; exact ⟨some v, hSl⟩
  · exact hC

theorem envSubsumes_length : ∀ {e1 e2 : List AbsSlot}, envSubsumes e1 e2 = true → e1.length = e2.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp [envSubsumes] at h
    exact congrArg Nat.succ (envSubsumes_length h.2)
  | [], _ :: _, h => by simp [envSubsumes] at h
  | _ :: _, [], h => by simp [envSubsumes] at h

theorem envSubsumes_compat {tys : List SeedTy} {slots : List LocalSlot} {e1 e2 : List AbsSlot}
    (hSub : envSubsumes e1 e2 = true) (hC : CompatEnv tys slots e1) :
    CompatEnv tys slots e2 := by
  have hLens : e1.length = e2.length := envSubsumes_length hSub
  rcases hC with ⟨hLenS, hLenE1, hSlot⟩
  refine ⟨hLenS, hLens.symm.trans hLenE1, ?_⟩
  intro i ty hTy
  obtain ⟨sl, a, hSl, hA, hComp⟩ := hSlot i ty hTy
  have hAt : ∀ {xs ys : List AbsSlot} {k : Nat} {x : AbsSlot},
      envSubsumes xs ys = true → getAt? xs k = some x →
      ∃ y, getAt? ys k = some y ∧ absSubsumes x y = true := by
    intro xs ys k x hS hGx
    induction xs generalizing ys k with
    | nil => simp [getAt?] at hGx
    | cons u us ih =>
      cases ys with
      | nil => simp [envSubsumes] at hS
      | cons w ws =>
        simp [envSubsumes] at hS
        cases k with
        | zero => simp [getAt?] at hGx; subst u; exact ⟨w, rfl, hS.1⟩
        | succ k' => simp [getAt?] at hGx ⊢; exact ih hS.2 hGx
  obtain ⟨b, hB, hSubAB⟩ := hAt hSub hA
  exact ⟨sl, b, hSl, hB, absSubsumes_compat hSubAB hComp⟩

def absEvalOperand (tys : List SeedTy) (env : List AbsSlot) :
    Operand → Option (SeedTy × List AbsSlot)
  | .copy loc =>
    match getAt? tys loc, getAt? env loc with
    | some ty, some .init => some (ty, env)
    | _, _ => none
  | .move loc =>
    match getAt? tys loc, getAt? env loc with
    | some ty, some .init =>
      let post := if isRuntimeStoredTy ty then .uninit else .init
      match setAt? env loc post with
      | some env' => some (ty, env')
      | none => none
    | _, _ => none
  | .constVal ty v =>
    if valHasTy v ty then some (ty, env) else none

def absEvalPrimOperand (tys : List SeedTy) (env : List AbsSlot) (opnd : Operand) :
    Option (SeedTy × List AbsSlot) :=
  match absEvalOperand tys env opnd with
  | some (ty, env') => if isPrimitiveReadableTy ty then some (ty, env') else none
  | none => none

def isNonZeroUnsignedConst : Operand → Bool
  | .constVal (.int _ false) (.scalar _ false bits) => bits != 0#64
  | _ => false

def absEvalRvalue (tys : List SeedTy) (env : List AbsSlot) (dstTy : SeedTy) :
    Rvalue → Option (List AbsSlot)
  | .use opnd =>
    match absEvalOperand tys env opnd with
    | some (srcTy, env') => if srcTy == dstTy then some env' else none
    | none => none
  | .binOp op lhs rhs =>
    match absEvalPrimOperand tys env lhs with
    | some (lty, env₁) =>
      match absEvalPrimOperand tys env₁ rhs with
      | some (rty, env₂) =>
        match binOpResultTy op lty rty with
        | some (resTy, _) =>
          let divOk := match op with | .divChecked => isNonZeroUnsignedConst rhs | _ => true
          if (resTy == dstTy) && divOk then some env₂ else none
        | none => none
      | none => none
    | none => none
  | .unOp op opnd =>
    match absEvalPrimOperand tys env opnd with
    | some (ty, env₁) =>
      match unOpResultTy op ty with
      | some resTy => if resTy == dstTy then some env₁ else none
      | none => none
    | none => none
  | .discrZst loc =>
    match getAt? tys loc, getAt? env loc with
    | some (.zstEnum _), some .uninit
    | some (.zstEnum _), some .init =>
      if dstTy == .int .isize false then some env else none
    | _, _ => none

def absEvalStmt (tys : List SeedTy) (env : List AbsSlot) :
    Stmt → Option (List AbsSlot)
  | .nop => some env
  | .storageLive loc =>
    match getAt? tys loc with
    | none => none
    | some ty => setAt? env loc (if isRuntimeStoredTy ty then .uninit else .init)
  | .storageDead loc =>
    if loc == 0 then none
    else
      match getAt? tys loc with
      | some _ => setAt? env loc .dead
      | none => none
  | .assign dst rv =>
    match getAt? tys dst with
    | none => none
    | some dstTy =>
      match absEvalRvalue tys env dstTy rv with
      | none => none
      | some env₁ =>
        match getAt? env₁ dst with
        | some .dead | none => none
        | some .uninit | some .init => setAt? env₁ dst .init

def absEvalStmts (tys : List SeedTy) (env : List AbsSlot) :
    List Stmt → Option (List AbsSlot)
  | [] => some env
  | s :: rest =>
    match absEvalStmt tys env s with
    | some env' => absEvalStmts tys env' rest
    | none => none

def checkCasesInvs (invs : List (List AbsSlot)) (envOut : List AbsSlot) (ty : SeedTy) :
    List (BitVec 64 × Nat) → Bool
  | [] => true
  | (c, tgt) :: rest =>
    let okC :=
      match ty with
      | .int w _ => truncWord w c == c
      | .bool => (c == 0#64) || (c == 1#64)
      | _ => false
    let okEdge :=
      match getAt? invs tgt with
      | some tgtInv => envSubsumes envOut tgtInv
      | none => false
    okC && okEdge && checkCasesInvs invs envOut ty rest

def checkTermInv (tys : List SeedTy) (invs : List (List AbsSlot)) (env : List AbsSlot) :
    Term → Bool
  | .unreachable => false
  | .return_ => getAt? env 0 == some .init
  | .goto tgt =>
    match getAt? invs tgt with
    | some tgtInv => envSubsumes env tgtInv
    | none => false
  | .switchInt discr cases otherwise =>
    match absEvalPrimOperand tys env discr with
    | none => false
    | some (ty, env') =>
      let okDef :=
        match getAt? invs otherwise with
        | some tgtInv => envSubsumes env' tgtInv
        | none => false
      okDef && checkCasesInvs invs env' ty cases
  | .assertNonZero cond _ tgt =>
    match absEvalPrimOperand tys env cond with
    | none => false
    | some (_, env') =>
      match getAt? invs tgt with
      | some tgtInv => envSubsumes env' tgtInv
      | none => false

def checkAllBlocksInvs (tys : List SeedTy) (allInvs : List (List AbsSlot)) :
    List MirBlock → List (List AbsSlot) → Bool
  | [], [] => true
  | b :: bs, inv :: rest =>
    match absEvalStmts tys inv b.stmts with
    | some envOut => checkTermInv tys allInvs envOut b.term && checkAllBlocksInvs tys allInvs bs rest
    | none => false
  | _, _ => false

def initAbsSlotsAux (argCount : Nat) (anns : List Bool) :
    Nat → List SeedTy → List AbsSlot
  | _, [] => []
  | idx, ty :: rest =>
    let a : AbsSlot :=
      if idx == 0 then
        if isRuntimeStoredTy ty then .uninit else .init
      else if idx <= argCount then
        .init
      else
        match getAt? anns idx with
        | some true => .dead
        | _ => if isRuntimeStoredTy ty then .uninit else .init
    a :: initAbsSlotsAux argCount anns (idx + 1) rest

def checkBodyInvs (body : MirBody) (invs : List (List AbsSlot)) : Bool :=
  match getAt? invs 0 with
  | none => false
  | some inv0 =>
    envSubsumes (initAbsSlotsAux body.argCount body.hasStorageAnn 0 body.locals) inv0 &&
    checkAllBlocksInvs body.locals invs body.blocks invs

theorem absEvalOperand_sound {tys : List SeedTy} {slots : List LocalSlot}
    {env env' : List AbsSlot} {opnd : Operand} {ty : SeedTy}
    (hComp : CompatEnv tys slots env)
    (hAbs : absEvalOperand tys env opnd = some (ty, env')) :
    ∃ v slots', evalOperandToSlot tys slots opnd = .ok (ty, some v, slots') ∧
      valHasTy v ty = true ∧ CompatEnv tys slots' env' := by
  cases opnd with
  | copy loc =>
    simp [absEvalOperand] at hAbs
    cases hT : getAt? tys loc <;> cases hE : getAt? env loc <;> simp [hT, hE] at hAbs
    rename_i ty0 a0; cases a0 <;> simp at hAbs
    rcases hAbs with ⟨rfl, rfl⟩
    obtain ⟨sl, a, hSl, hA, hC⟩ := hComp.2.2 loc ty0 hT
    rw [hE] at hA; cases hA
    rcases hC with ⟨v, hSlEq, hValTy⟩
    rw [hSlEq] at hSl
    exact ⟨v, slots, by simp [evalOperandToSlot, hT, hSl], hValTy, hComp⟩
  | move loc =>
    simp [absEvalOperand] at hAbs
    cases hT : getAt? tys loc <;> cases hE : getAt? env loc <;> simp [hT, hE] at hAbs
    rename_i ty0 a0; cases a0 <;> simp at hAbs
    cases hSE : setAt? env loc (if isRuntimeStoredTy ty0 then .uninit else .init) <;>
      simp [hSE] at hAbs
    rcases hAbs with ⟨rfl, rfl⟩
    obtain ⟨sl, a, hSl, hA, hC⟩ := hComp.2.2 loc ty0 hT
    rw [hE] at hA; cases hA
    rcases hC with ⟨v, hSlEq, hValTy⟩
    rw [hSlEq] at hSl
    have hLt : loc < slots.length := by rw [hComp.1]; exact getAt?_lt_length hT
    obtain ⟨sls', hSetS⟩ := exists_setAt?_of_lt (liveUninitSlot ty0) hLt
    refine ⟨v, sls', by simp [evalOperandToSlot, hT, hSl, hSetS], hValTy, ?_⟩
    refine ⟨by rw [setAt?_length hSetS, hComp.1], by rw [setAt?_length hSE, hComp.2.1], ?_⟩
    intro i tyi hTyi
    have hGS := getAt?_some_of_setAt? (j := i) hSetS
    have hGE := getAt?_some_of_setAt? (j := i) hSE
    by_cases hij : i = loc
    · subst hij; rw [hT] at hTyi; cases hTyi
      refine ⟨liveUninitSlot ty0, if isRuntimeStoredTy ty0 then .uninit else .init,
        hGS.1 rfl, hGE.1 rfl, ?_⟩
      cases ty0 <;> simp [liveUninitSlot, isRuntimeStoredTy, CompatSlot, valHasTy]
    · obtain ⟨sli, ai, hSli, hAi, hCi⟩ := hComp.2.2 i tyi hTyi
      exact ⟨sli, ai, by rw [hGS.2 hij]; exact hSli, by rw [hGE.2 hij]; exact hAi, hCi⟩
  | constVal cty cv =>
    simp [absEvalOperand] at hAbs
    rcases hAbs with ⟨hV, rfl, rfl⟩
    exact ⟨cv, slots, by simp [evalOperandToSlot, hV], hV, hComp⟩

theorem absEvalPrimOperand_sound {tys : List SeedTy} {slots : List LocalSlot}
    {env env' : List AbsSlot} {opnd : Operand} {ty : SeedTy}
    (hComp : CompatEnv tys slots env)
    (hAbs : absEvalPrimOperand tys env opnd = some (ty, env')) :
    ∃ v slots', evalPrimOperand tys slots opnd = .ok (v, slots') ∧
      isPrimitiveReadableTy ty = true ∧ valHasTy v ty = true ∧ CompatEnv tys slots' env' := by
  simp [absEvalPrimOperand] at hAbs
  cases hOp : absEvalOperand tys env opnd with
  | none => simp [hOp] at hAbs
  | some p =>
    rcases p with ⟨ty0, e1⟩
    simp [hOp] at hAbs
    rcases hAbs with ⟨hPrim, rfl, rfl⟩
    obtain ⟨v, sls', hEv, hValTy, hComp'⟩ := absEvalOperand_sound hComp hOp
    exact ⟨v, sls', by simp [evalPrimOperand, hEv, hPrim], hPrim, hValTy, hComp'⟩

theorem absEvalRvalue_sound {tys : List SeedTy} {slots : List LocalSlot}
    {env env' : List AbsSlot} {dstTy : SeedTy} {rv : Rvalue}
    (hComp : CompatEnv tys slots env)
    (hAbs : absEvalRvalue tys env dstTy rv = some env') :
    ∃ v slots', evalRvalue tys slots dstTy rv = .ok (v, slots') ∧
      valHasTy v dstTy = true ∧ CompatEnv tys slots' env' := by
  cases rv with
  | use opnd =>
    simp [absEvalRvalue] at hAbs
    cases hOp : absEvalOperand tys env opnd with
    | none => simp [hOp] at hAbs
    | some p =>
      rcases p with ⟨srcTy, e1⟩
      simp [hOp] at hAbs
      rcases hAbs with ⟨hEq, rfl⟩
      subst hEq
      obtain ⟨v, sls', hEv, hValTy, hComp'⟩ := absEvalOperand_sound hComp hOp
      exact ⟨v, sls', by simp [evalRvalue, hEv], hValTy, hComp'⟩
  | binOp op lhs rhs =>
    simp [absEvalRvalue] at hAbs
    cases hL : absEvalPrimOperand tys env lhs with
    | none => simp [hL] at hAbs
    | some pL =>
      rcases pL with ⟨lty, e1⟩
      simp [hL] at hAbs
      cases hR : absEvalPrimOperand tys e1 rhs with
      | none => simp [hR] at hAbs
      | some pR =>
        rcases pR with ⟨rty, e2⟩
        simp [hR] at hAbs
        cases hB : binOpResultTy op lty rty with
        | none => simp [hB] at hAbs
        | some pB =>
          rcases pB with ⟨resTy, _⟩
          simp [hB] at hAbs
          rcases hAbs with ⟨⟨hEq, hDivOk⟩, rfl⟩
          subst hEq
          obtain ⟨lv, sls₁, hEvL, _, hlTy, hC1⟩ := absEvalPrimOperand_sound hComp hL
          obtain ⟨rv', sls₂, hEvR, _, hrTy, hC2⟩ := absEvalPrimOperand_sound hC1 hR
          have hEvalB : ∃ res, evalBinOp op lv rv' = .ok res ∧ valHasTy res resTy = true := by
            cases lv <;> cases rv' <;> cases lty <;> cases rty <;>
              simp [valHasTy] at hlTy hrTy <;> simp [binOpResultTy] at hB
            case scalar.scalar.int.int w1 s1 b1 w2 s2 b2 iw1 sg1 iw2 sg2 =>
              rcases hlTy with ⟨⟨rfl, rfl⟩, _⟩
              rcases hrTy with ⟨⟨rfl, rfl⟩, _⟩
              rcases hB with ⟨⟨rfl, rfl⟩, hBt⟩
              cases op with
              | divChecked =>
                dsimp at hBt
                split at hBt
                · simp at hBt
                · simp at hBt; cases hBt.1
                  have hNz : isNonZeroUnsignedConst rhs = true := hDivOk
                  cases rhs <;> simp [isNonZeroUnsignedConst] at hNz
                  rename_i cty cv
                  cases cty with
                  | bool | unit | zstEnum _ => simp at hNz
                  | int w_c sg_c =>
                    cases sg_c with
                    | true => simp at hNz
                    | false =>
                      cases cv with
                      | bool _ | unit | zstEnum _ => simp at hNz
                      | scalar w_v sg_v b_v =>
                        cases sg_v with
                        | true => simp at hNz
                        | false =>
                          simp at hNz
                          simp [evalPrimOperand, evalOperandToSlot] at hEvR
                          cases hV : valHasTy (SeedVal.scalar w_v false b_v) (SeedTy.int w_c false) with
                          | false => simp [hV] at hEvR
                          | true =>
                            simp [hV, isPrimitiveReadableTy] at hEvR
                            rcases hEvR with ⟨⟨rfl, hSgF, rfl⟩, _⟩
                            have hNeZ : (b_v == 0#64) = false := by
                              cases hZ : (b_v == 0#64)
                              · rfl
                              · have : b_v = 0#64 := eq_of_beq hZ; subst this; simp at hNz
                            simp [evalBinOp, hSgF, hNeZ, valHasTy, truncWord_idem]
              | eq =>
                simp at hBt; cases hBt.1
                exact ⟨_, by simp [evalBinOp]; rfl, rfl⟩
              | ult =>
                simp at hBt; cases hBt.1
                exact ⟨_, by simp [evalBinOp]; rfl, rfl⟩
              | add | sub | bitAnd | bitOr | bitXor | shl =>
                simp at hBt; cases hBt.1
                exact ⟨_, by simp [evalBinOp]; rfl, by simp [valHasTy, truncWord_idem]⟩
            case bool.bool.bool.bool lb rb =>
              cases op <;> simp at hB <;> cases hB.1 <;>
                exact ⟨_, by simp [evalBinOp]; rfl, rfl⟩
          obtain ⟨res, hOkB, hResTy⟩ := hEvalB
          exact ⟨res, sls₂, by simp [evalRvalue, hEvL, hEvR, hOkB], hResTy, hC2⟩
  | unOp op opnd =>
    simp [absEvalRvalue] at hAbs
    cases hO : absEvalPrimOperand tys env opnd with
    | none => simp [hO] at hAbs
    | some p =>
      rcases p with ⟨ty0, e1⟩
      simp [hO] at hAbs
      cases hU : unOpResultTy op ty0 with
      | none => simp [hU] at hAbs
      | some resTy =>
        simp [hU] at hAbs
        rcases hAbs with ⟨hEq, rfl⟩
        subst hEq
        obtain ⟨v0, sls₁, hEvO, _, hvTy, hC1⟩ := absEvalPrimOperand_sound hComp hO
        have hEvalU : ∃ res, evalUnOp op v0 = .ok res ∧ valHasTy res resTy = true := by
          cases v0 <;> cases ty0 <;> simp [valHasTy] at hvTy <;> simp [unOpResultTy] at hU
          · cases op <;> simp at hU; subst resTy; exact ⟨_, rfl, rfl⟩
          · rcases hvTy with ⟨⟨rfl, rfl⟩, _⟩
            cases op with
            | not => simp at hU; subst resTy; exact ⟨_, rfl, by simp [valHasTy, truncWord_idem]⟩
            | neg =>
              cases ‹Bool› <;> simp at hU
              subst resTy; exact ⟨_, rfl, by simp [valHasTy, truncWord_idem]⟩
        obtain ⟨res, hOkU, hResTy⟩ := hEvalU
        exact ⟨res, sls₁, by simp [evalRvalue, hEvO, hOkU], hResTy, hC1⟩
  | discrZst loc =>
    simp [absEvalRvalue] at hAbs
    cases hT : getAt? tys loc <;> simp [hT] at hAbs
    rename_i zty
    cases zty with
    | bool | int _ _ | unit => simp at hAbs
    | zstEnum d =>
      cases hE : getAt? env loc with
      | none => simp [hE] at hAbs
      | some a =>
        cases a with
        | dead => simp [hE] at hAbs
        | uninit =>
          simp [hE] at hAbs
          rcases hAbs with ⟨hEq, rfl⟩
          subst hEq
          obtain ⟨sl, a', hSl, hA, hC⟩ := hComp.2.2 loc _ hT
          rw [hE] at hA; cases hA
          rcases hC with ⟨optV, hSlEq⟩
          rw [hSlEq] at hSl
          exact ⟨.scalar .isize false d, slots, by simp [evalRvalue, hT, hSl],
            by simp [valHasTy, truncWord_isize], hComp⟩
        | init =>
          simp [hE] at hAbs
          rcases hAbs with ⟨hEq, rfl⟩
          subst hEq
          obtain ⟨sl, a', hSl, hA, hC⟩ := hComp.2.2 loc _ hT
          rw [hE] at hA; cases hA
          rcases hC with ⟨v0, hSlEq, _⟩
          rw [hSlEq] at hSl
          exact ⟨.scalar .isize false d, slots, by simp [evalRvalue, hT, hSl],
            by simp [valHasTy, truncWord_isize], hComp⟩

theorem absEvalStmt_sound {tys : List SeedTy} {slots : List LocalSlot}
    {env env' : List AbsSlot} {s : Stmt}
    (hComp : CompatEnv tys slots env)
    (hAbs : absEvalStmt tys env s = some env') :
    ∃ slots', evalStmt tys slots s = .ok slots' ∧ CompatEnv tys slots' env' := by
  cases s with
  | nop => simp [absEvalStmt] at hAbs; cases hAbs; exact ⟨slots, rfl, hComp⟩
  | storageLive loc =>
    simp [absEvalStmt] at hAbs
    cases hT : getAt? tys loc <;> simp [hT] at hAbs
    rename_i ty
    have hLt : loc < slots.length := by rw [hComp.1]; exact getAt?_lt_length hT
    obtain ⟨sls', hSetS⟩ := exists_setAt?_of_lt (liveUninitSlot ty) hLt
    refine ⟨sls', by simp [evalStmt, hT, hSetS], ?_⟩
    refine ⟨by rw [setAt?_length hSetS, hComp.1], by rw [setAt?_length hAbs, hComp.2.1], ?_⟩
    intro i tyi hTyi
    have hGS := getAt?_some_of_setAt? (j := i) hSetS
    have hGE := getAt?_some_of_setAt? (j := i) hAbs
    by_cases hij : i = loc
    · subst hij; rw [hT] at hTyi; cases hTyi
      refine ⟨liveUninitSlot ty, if isRuntimeStoredTy ty then .uninit else .init,
        hGS.1 rfl, hGE.1 rfl, ?_⟩
      cases ty <;> simp [liveUninitSlot, isRuntimeStoredTy, CompatSlot, valHasTy]
    · obtain ⟨sli, ai, hSli, hAi, hCi⟩ := hComp.2.2 i tyi hTyi
      exact ⟨sli, ai, by rw [hGS.2 hij]; exact hSli, by rw [hGE.2 hij]; exact hAi, hCi⟩
  | storageDead loc =>
    simp [absEvalStmt] at hAbs
    by_cases hZ : loc = 0
    · subst hZ; simp at hAbs
    · simp [hZ] at hAbs
      cases hT : getAt? tys loc <;> simp [hT] at hAbs
      have hLt : loc < slots.length := by rw [hComp.1]; exact getAt?_lt_length hT
      obtain ⟨sls', hSetS⟩ := exists_setAt?_of_lt .dead hLt
      refine ⟨sls', by simp [evalStmt, hZ, hSetS], ?_⟩
      refine ⟨by rw [setAt?_length hSetS, hComp.1], by rw [setAt?_length hAbs, hComp.2.1], ?_⟩
      intro i tyi hTyi
      have hGS := getAt?_some_of_setAt? (j := i) hSetS
      have hGE := getAt?_some_of_setAt? (j := i) hAbs
      by_cases hij : i = loc
      · exact ⟨.dead, .dead, hGS.1 hij, hGE.1 hij, trivial⟩
      · obtain ⟨sli, ai, hSli, hAi, hCi⟩ := hComp.2.2 i tyi hTyi
        exact ⟨sli, ai, by rw [hGS.2 hij]; exact hSli, by rw [hGE.2 hij]; exact hAi, hCi⟩
  | assign dst rv =>
    simp [absEvalStmt] at hAbs
    cases hT : getAt? tys dst <;> simp [hT] at hAbs
    rename_i dstTy
    cases hRv : absEvalRvalue tys env dstTy rv <;> simp [hRv] at hAbs
    rename_i e1
    obtain ⟨v, sls₁, hEvRv, hValTy, hC1⟩ := absEvalRvalue_sound hComp hRv
    cases hE1 : getAt? e1 dst <;> simp [hE1] at hAbs
    rename_i a1
    cases a1 with
    | dead => simp at hAbs
    | uninit | init =>
      obtain ⟨slD, aD, hSlD, hAD, hCD⟩ := hC1.2.2 dst dstTy hT
      rw [hE1] at hAD; cases hAD
      have hNotDead : ∃ optV, slD = .live optV := by
        first | exact hCD | (rcases hCD with ⟨vd, hSlEq, _⟩; exact ⟨some vd, hSlEq⟩)
      rcases hNotDead with ⟨optV, hSlEq⟩
      rw [hSlEq] at hSlD
      have hLt : dst < sls₁.length := by rw [hC1.1]; exact getAt?_lt_length hT
      obtain ⟨sls₂, hSetS⟩ := exists_setAt?_of_lt (.live (some v)) hLt
      refine ⟨sls₂, by simp [evalStmt, hT, hEvRv, writePlace, hValTy, hSlD, hSetS], ?_⟩
      refine ⟨by rw [setAt?_length hSetS, hC1.1], by rw [setAt?_length hAbs, hC1.2.1], ?_⟩
      intro i tyi hTyi
      have hGS := getAt?_some_of_setAt? (j := i) hSetS
      have hGE := getAt?_some_of_setAt? (j := i) hAbs
      by_cases hij : i = dst
      · subst hij; rw [hT] at hTyi; cases hTyi
        exact ⟨.live (some v), .init, hGS.1 rfl, hGE.1 rfl, ⟨v, rfl, hValTy⟩⟩
      · obtain ⟨sli, ai, hSli, hAi, hCi⟩ := hC1.2.2 i tyi hTyi
        exact ⟨sli, ai, by rw [hGS.2 hij]; exact hSli, by rw [hGE.2 hij]; exact hAi, hCi⟩

theorem absEvalStmts_sound {tys : List SeedTy} {slots : List LocalSlot}
    {env env' : List AbsSlot} {stmts : List Stmt}
    (hComp : CompatEnv tys slots env)
    (hAbs : absEvalStmts tys env stmts = some env') :
    ∃ slots', evalStmts tys slots stmts = .ok slots' ∧ CompatEnv tys slots' env' := by
  induction stmts generalizing slots env with
  | nil => simp [absEvalStmts] at hAbs; cases hAbs; exact ⟨slots, rfl, hComp⟩
  | cons s rest ih =>
    simp [absEvalStmts] at hAbs
    cases hS : absEvalStmt tys env s with
    | none => simp [hS] at hAbs
    | some e1 =>
      simp [hS] at hAbs
      obtain ⟨sls₁, hEvS, hC1⟩ := absEvalStmt_sound hComp hS
      obtain ⟨sls₂, hEvRest, hC2⟩ := ih hC1 hAbs
      exact ⟨sls₂, by simp [evalStmts, hEvS, hEvRest], hC2⟩

theorem switchCases_no_fault_and_inv {invs : List (List AbsSlot)} {env : List AbsSlot}
    {w : IntWidth} {s : Bool} {bits : BitVec 64} {otherwise : Nat}
    {cases : List (BitVec 64 × Nat)} {tgtInv : List AbsSlot}
    (hDef : getAt? invs otherwise = some tgtInv)
    (hSubDef : envSubsumes env tgtInv = true)
    (hCk : checkCasesInvs invs env (.int w s) cases = true) :
    ∃ tgt tgtInv', evalSwitchCases w bits otherwise cases = .ok tgt ∧
      getAt? invs tgt = some tgtInv' ∧ envSubsumes env tgtInv' = true := by
  induction cases with
  | nil => exact ⟨otherwise, tgtInv, rfl, hDef, hSubDef⟩
  | cons hd rest ih =>
    rcases hd with ⟨c, cTgt⟩
    simp [checkCasesInvs] at hCk
    rcases hCk with ⟨⟨hTrunc, hEdge⟩, hRest⟩
    cases hGI : getAt? invs cTgt with
    | none => simp [hGI] at hEdge
    | some cInv =>
      simp [hGI] at hEdge
      by_cases hb : truncWord w bits = c
      · exact ⟨cTgt, cInv, by simp [evalSwitchCases, hTrunc, hb], hGI, hEdge⟩
      · have hEvStep : evalSwitchCases w bits otherwise ((c, cTgt) :: rest) =
            evalSwitchCases w bits otherwise rest := by
          simp [evalSwitchCases, hTrunc, hb]
        rw [hEvStep]
        exact ih hRest

theorem boolSwitchCases_no_fault_and_inv {invs : List (List AbsSlot)} {env : List AbsSlot}
    {b : Bool} {otherwise : Nat} {cases : List (BitVec 64 × Nat)}
    {tgtInv : List AbsSlot}
    (hDef : getAt? invs otherwise = some tgtInv)
    (hSubDef : envSubsumes env tgtInv = true)
    (hCk : checkCasesInvs invs env .bool cases = true) :
    ∃ tgt tgtInv', evalBoolSwitchCases b otherwise cases = .ok tgt ∧
      getAt? invs tgt = some tgtInv' ∧ envSubsumes env tgtInv' = true := by
  induction cases with
  | nil => exact ⟨otherwise, tgtInv, rfl, hDef, hSubDef⟩
  | cons hd rest ih =>
    rcases hd with ⟨c, cTgt⟩
    simp [checkCasesInvs] at hCk
    rcases hCk with ⟨⟨hC, hEdge⟩, hRest⟩
    cases hGI : getAt? invs cTgt with
    | none => simp [hGI] at hEdge
    | some cInv =>
      simp [hGI] at hEdge
      rcases hC with h0 | h1
      · subst h0
        cases b with
        | false => exact ⟨cTgt, cInv, by simp [evalBoolSwitchCases], hGI, hEdge⟩
        | true =>
          have hStep : evalBoolSwitchCases true otherwise ((0#64, cTgt) :: rest) =
              evalBoolSwitchCases true otherwise rest := by simp [evalBoolSwitchCases]
          rw [hStep]
          exact ih hRest
      · subst h1
        cases b with
        | false =>
          have hStep : evalBoolSwitchCases false otherwise ((1#64, cTgt) :: rest) =
              evalBoolSwitchCases false otherwise rest := by simp [evalBoolSwitchCases]
          rw [hStep]
          exact ih hRest
        | true => exact ⟨cTgt, cInv, by simp [evalBoolSwitchCases], hGI, hEdge⟩

theorem checkBodyInvs_lookup {body : MirBody} {invs : List (List AbsSlot)}
    {k : Nat} {i0 : List AbsSlot}
    (hBody : checkBodyInvs body invs = true)
    (hGetInv : getAt? invs k = some i0) :
    ∃ blk envOut, getAt? body.blocks k = some blk ∧
      absEvalStmts body.locals i0 blk.stmts = some envOut ∧
      checkTermInv body.locals invs envOut blk.term = true := by
  have hAll : checkAllBlocksInvs body.locals invs body.blocks invs = true := by
    unfold checkBodyInvs at hBody
    cases h0 : getAt? invs 0 <;> simp [h0] at hBody
    exact hBody.2
  have hPair : ∀ {blks : List MirBlock} {is : List (List AbsSlot)} {k : Nat}
      {i0 : List AbsSlot},
      checkAllBlocksInvs body.locals invs blks is = true →
      getAt? is k = some i0 →
      ∃ b' envOut, getAt? blks k = some b' ∧
        absEvalStmts body.locals i0 b'.stmts = some envOut ∧
        checkTermInv body.locals invs envOut b'.term = true := by
    intro blks is k' i0' hCA hGI
    induction blks generalizing is k' with
    | nil => cases is <;> simp [checkAllBlocksInvs] at hCA; simp [getAt?] at hGI
    | cons bk bks ih =>
      cases is with
      | nil => simp [checkAllBlocksInvs] at hCA
      | cons iHd iTl =>
        simp [checkAllBlocksInvs] at hCA
        cases hAE : absEvalStmts body.locals iHd bk.stmts with
        | none => simp [hAE] at hCA
        | some eOut =>
          simp [hAE] at hCA
          cases k' with
          | zero =>
            simp [getAt?] at hGI; subst i0'
            exact ⟨bk, eOut, rfl, hAE, hCA.1⟩
          | succ k'' =>
            simp [getAt?] at hGI
            exact ih hCA.2 hGI
  exact hPair hAll hGetInv

theorem checkBodyInvs_step {body : MirBody} {invs : List (List AbsSlot)}
    {mirSt : MirState} {inv : List AbsSlot}
    (hBody : checkBodyInvs body invs = true)
    (hGetInv : getAt? invs mirSt.bb = some inv)
    (hComp : CompatEnv body.locals mirSt.slots inv) :
    (∀ k, stepMirBlock body mirSt ≠ .fault k) ∧
    (∀ mirSt', stepMirBlock body mirSt = .running mirSt' →
      ∃ inv', getAt? invs mirSt'.bb = some inv' ∧ CompatEnv body.locals mirSt'.slots inv') := by
  obtain ⟨blk, envOut, hGetBlk, hAE, hTermCk⟩ := checkBodyInvs_lookup hBody hGetInv
  obtain ⟨sls₁, hEvStmts, hComp₁⟩ := absEvalStmts_sound hComp hAE
  have hStepEq : stepMirBlock body mirSt = evalTerm body.locals sls₁ blk.term := by
    simp [stepMirBlock, hGetBlk, hEvStmts]
  rw [hStepEq]
  cases hT : blk.term with
  | unreachable => simp [checkTermInv, hT] at hTermCk
  | goto tgt =>
    simp [checkTermInv, hT] at hTermCk
    cases hGI : getAt? invs tgt <;> simp [hGI] at hTermCk
    rename_i tgtInv
    simp [evalTerm]
    exact ⟨tgtInv, hGI, envSubsumes_compat hTermCk hComp₁⟩
  | return_ =>
    simp [checkTermInv, hT] at hTermCk
    cases hLoc0 : getAt? body.locals 0 with
    | none =>
      have hLen : inv.length = body.locals.length := hComp.2.1
      have hEnvLen : envOut.length = body.locals.length := hComp₁.2.1
      have hLt0 : 0 < envOut.length := getAt?_lt_length hTermCk
      rw [hEnvLen] at hLt0
      obtain ⟨_, hSome⟩ := exists_getAt?_of_lt hLt0
      rw [hSome] at hLoc0; cases hLoc0
    | some ty0 =>
      obtain ⟨sl0, a0, hSl0, hA0, hC0⟩ := hComp₁.2.2 0 ty0 hLoc0
      rw [hTermCk] at hA0; cases hA0
      rcases hC0 with ⟨v0, hSlEq, _⟩
      simp [evalTerm, hSl0, hSlEq]
  | switchInt discr cases otherwise =>
    simp [checkTermInv, hT] at hTermCk
    cases hAD : absEvalPrimOperand body.locals envOut discr with
    | none => simp [hAD] at hTermCk
    | some pD =>
      rcases pD with ⟨dTy, env₂⟩
      simp [hAD] at hTermCk
      cases hGI : getAt? invs otherwise <;> simp [hGI] at hTermCk
      rename_i defInv
      obtain ⟨dVal, sls₂, hEvD, hPrim, hDValTy, hComp₂⟩ := absEvalPrimOperand_sound hComp₁ hAD
      simp [evalTerm, hEvD]
      cases dVal with
      | unit | zstEnum _ =>
        cases dTy <;> simp [valHasTy] at hDValTy
        all_goals simp [isPrimitiveReadableTy] at hPrim
      | scalar w s bits =>
        have hDTyEq : ∃ w0 s0, dTy = .int w0 s0 := by
          cases dTy <;> simp [valHasTy] at hDValTy; exact ⟨_, _, rfl⟩
        rcases hDTyEq with ⟨w0, s0, rfl⟩
        simp [valHasTy] at hDValTy
        rcases hDValTy with ⟨⟨rfl, rfl⟩, _⟩
        obtain ⟨tgt, tgtInv, hSw, hGITgt, hSubTgt⟩ :=
          switchCases_no_fault_and_inv (bits := bits) hGI hTermCk.1 hTermCk.2
        simp [hSw]
        exact ⟨tgtInv, hGITgt, envSubsumes_compat hSubTgt hComp₂⟩
      | bool b =>
        have hDTyEq : dTy = .bool := by
          cases dTy <;> simp [valHasTy] at hDValTy; rfl
        subst hDTyEq
        obtain ⟨tgt, tgtInv, hSw, hGITgt, hSubTgt⟩ :=
          boolSwitchCases_no_fault_and_inv (b := b) hGI hTermCk.1 hTermCk.2
        simp [hSw]
        exact ⟨tgtInv, hGITgt, envSubsumes_compat hSubTgt hComp₂⟩
  | assertNonZero cond expected tgt =>
    simp [checkTermInv, hT] at hTermCk
    cases hAC : absEvalPrimOperand body.locals envOut cond with
    | none => simp [hAC] at hTermCk
    | some pC =>
      rcases pC with ⟨cTy, env₂⟩
      simp [hAC] at hTermCk
      cases hGI : getAt? invs tgt <;> simp [hGI] at hTermCk
      rename_i tgtInv
      obtain ⟨cVal, sls₂, hEvC, hPrim, hCVTy, hComp₂⟩ := absEvalPrimOperand_sound hComp₁ hAC
      simp [evalTerm, hEvC]
      cases cVal with
      | unit | zstEnum _ =>
        cases cTy <;> simp [valHasTy] at hCVTy <;> simp [isPrimitiveReadableTy] at hPrim
      | bool b =>
        cases hB : (b == expected) <;> simp [hB]
        exact ⟨tgtInv, hGI, envSubsumes_compat hTermCk hComp₂⟩
      | scalar w s bits =>
        cases hB : ((bits != 0#64) == expected) <;> simp [hB]
        exact ⟨tgtInv, hGI, envSubsumes_compat hTermCk hComp₂⟩

theorem init_compatEnv {body : MirBody} {invs : List (List AbsSlot)}
    {args : List SeedVal} {mirSt0 : MirState}
    (hBody : checkBodyInvs body invs = true)
    (hInit : initMirState body args = some mirSt0) :
    ∃ inv0, getAt? invs mirSt0.bb = some inv0 ∧ CompatEnv body.locals mirSt0.slots inv0 := by
  unfold checkBodyInvs at hBody
  cases h0 : getAt? invs 0 <;> simp [h0] at hBody
  rename_i inv0
  unfold initMirState at hInit
  split at hInit <;> try contradiction
  rename_i hCond; simp at hCond
  cases hInit
  have hCompatInit : CompatEnv body.locals
      (initMirSlotsAux body.argCount args body.hasStorageAnn 0 body.locals)
      (initAbsSlotsAux body.argCount body.hasStorageAnn 0 body.locals) := by
    have hLenAbs : (initAbsSlotsAux body.argCount body.hasStorageAnn 0 body.locals).length =
        body.locals.length := by
      have : ∀ idx tys, (initAbsSlotsAux body.argCount body.hasStorageAnn idx tys).length = tys.length := by
        intro idx tys; induction tys generalizing idx with
        | nil => rfl
        | cons _ _ ih => simp [initAbsSlotsAux, ih]
      exact this 0 body.locals
    refine ⟨initMirSlots_len _ _ _ _ _, hLenAbs, ?_⟩
    have hAux : ∀ idx tys, checkEntryArgsAux body.argCount args idx tys = true →
        ∀ k ty, getAt? tys k = some ty →
          ∃ sl a, getAt? (initMirSlotsAux body.argCount args body.hasStorageAnn idx tys) k = some sl ∧
            getAt? (initAbsSlotsAux body.argCount body.hasStorageAnn idx tys) k = some a ∧
            CompatSlot ty sl a := by
      intro idx tys hAr k ty hG
      induction tys generalizing idx k with
      | nil => simp [getAt?] at hG
      | cons t rest ih =>
        cases k with
        | zero =>
          simp [getAt?] at hG; subst t
          simp [initMirSlotsAux, initAbsSlotsAux, getAt?]
          by_cases hZ : idx = 0
          · subst hZ; simp
            cases ty <;> simp [liveUninitSlot, isRuntimeStoredTy, CompatSlot, valHasTy]
          · simp [hZ]
            by_cases hLe : idx <= body.argCount
            · simp [hLe]
              simp [checkEntryArgsAux, hZ, hLe] at hAr
              cases hA : getAt? args (idx - 1) with
              | none => simp [hA] at hAr
              | some v => simp [hA] at hAr; exact ⟨v, rfl, hAr.1⟩
            · simp [hLe]
              split
              · exact trivial
              · cases ty <;> simp [liveUninitSlot, isRuntimeStoredTy, CompatSlot, valHasTy]
        | succ k' =>
          simp [getAt?] at hG
          dsimp [initMirSlotsAux, initAbsSlotsAux, getAt?]
          simp [checkEntryArgsAux] at hAr
          have hRest : checkEntryArgsAux body.argCount args (idx + 1) rest = true := by
            by_cases hZ : idx = 0
            · subst hZ; exact hAr
            · simp [hZ] at hAr
              by_cases hLe : idx ≤ body.argCount
              · simp [hLe] at hAr
                cases hA : getAt? args (idx - 1) with
                | none => simp [hA] at hAr
                | some _ => simp [hA] at hAr; exact hAr.2
              · simp [hLe] at hAr
                have hGt : body.argCount < idx + 1 := Nat.lt_of_lt_of_le (Nat.lt_of_not_le hLe) (Nat.le_succ _)
                rw [checkEntryArgsAux_gt body.argCount args (idx + 1) rest hGt]
                simp [hAr]
          exact ih (idx + 1) hRest k' hG
    exact hAux 0 body.locals hCond.2
  exact ⟨inv0, h0, envSubsumes_compat hBody.1 hCompatInit⟩

theorem checkBodyInvs_no_fault_from_state {body : MirBody} {invs : List (List AbsSlot)}
    (hBody : checkBodyInvs body invs = true) :
    ∀ n mirSt inv,
      getAt? invs mirSt.bb = some inv →
      CompatEnv body.locals mirSt.slots inv →
      (∀ m st', m <= n → runMirBlocks body m mirSt = .running st' →
        ∀ k, stepMirBlock body st' ≠ .fault k) ∧
      (∀ k, runMirBlocks body n mirSt ≠ .fault k)
  | 0, mirSt, inv, hGet, hComp => by
    obtain ⟨hNF, _⟩ := checkBodyInvs_step hBody hGet hComp
    constructor
    · intro m st' hm hRun
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0; simp [runMirBlocks] at hRun; subst hRun; exact hNF
    · intro k; simp [runMirBlocks]
  | n + 1, mirSt, inv, hGet, hComp => by
    obtain ⟨hNF, hPres⟩ := checkBodyInvs_step hBody hGet hComp
    cases hSt : stepMirBlock body mirSt with
    | fault k => exact absurd hSt (hNF k)
    | returned v =>
      constructor
      · intro m st' hm hRun
        cases m with
        | zero => simp [runMirBlocks] at hRun; subst hRun; exact hNF
        | succ m' => simp [runMirBlocks, hSt] at hRun
      · intro k; simp [runMirBlocks, hSt]
    | panicked =>
      constructor
      · intro m st' hm hRun
        cases m with
        | zero => simp [runMirBlocks] at hRun; subst hRun; exact hNF
        | succ m' => simp [runMirBlocks, hSt] at hRun
      · intro k; simp [runMirBlocks, hSt]
    | running mirSt₁ =>
      obtain ⟨inv₁, hGet₁, hComp₁⟩ := hPres mirSt₁ hSt
      have ih := checkBodyInvs_no_fault_from_state hBody n mirSt₁ inv₁ hGet₁ hComp₁
      constructor
      · intro m st' hm hRun
        cases m with
        | zero => simp [runMirBlocks] at hRun; subst hRun; exact hNF
        | succ m' =>
          simp [runMirBlocks, hSt] at hRun
          exact ih.1 m' st' (Nat.le_of_succ_le_succ hm) hRun
      · intro k; simp [runMirBlocks, hSt]; exact ih.2 k

/-- Backward simulation from `MiniMachO0` to `SeedMir` (`deinitMovedPlace = true`)
    for any body certified by `checkBodyInvs` (supports arbitrary loops and branches). -/
theorem mirToMiniMachO0_backward_sim {body : MirBody} {mbody : MachBody}
    {invs : List (List AbsSlot)} {args : List SeedVal} {mirSt0 : MirState}
    (hComp : compileBody body = some mbody)
    (hBody : checkBodyInvs body invs = true)
    (hInit : initMirState body args = some mirSt0)
    (n : Nat) :
    (∀ outW, runMachBlocks mbody n (initMachState body args) = .returned outW →
      ∃ v, runMirBlocks body n mirSt0 = .returned v ∧ encodeSeedVal v = outW) ∧
    (runMachBlocks mbody n (initMachState body args) = .panicked →
      runMirBlocks body n mirSt0 = .panicked) := by
  obtain ⟨inv0, hGet0, hCompat0⟩ := init_compatEnv hBody hInit
  obtain ⟨hAllNF, hNF⟩ := checkBodyInvs_no_fault_from_state hBody n mirSt0 inv0 hGet0 hCompat0
  have hFwd := mirToMiniMachO0_forward_sim hComp hInit n hAllNF hNF
  constructor
  · intro outW hMachRet
    rw [hMachRet] at hFwd
    cases hMir : runMirBlocks body n mirSt0 with
    | running _ => simp [hMir] at hFwd
    | panicked => simp [hMir] at hFwd
    | fault k => exact absurd hMir (hNF k)
    | returned v =>
      simp [hMir] at hFwd
      exact ⟨v, rfl, hFwd.symm⟩
  · intro hMachPan
    rw [hMachPan] at hFwd
    cases hMir : runMirBlocks body n mirSt0 with
    | running _ => simp [hMir] at hFwd
    | returned _ => simp [hMir] at hFwd
    | fault k => exact absurd hMir (hNF k)
    | panicked => rfl

/-! ### Negative Counterexample: `m4_same_stmt_move_alias` (`Add(move _1, copy _1)`) -/

def m4MoveAliasBody : MirBody :=
  { argCount := 1
    locals := [.int .i64 false, .int .i64 false]
    hasStorageAnn := [false, false]
    blocks := [{
      stmts := [.assign 0 (.binOp .add (.move 1) (.copy 1))]
      term := .return_
    }] }

def m4MoveAliasInv : List (List AbsSlot) := [[.uninit, .init]]

theorem cex_m4_move_then_copy_faults_in_mir_not_mach :
    ∃ mirSt0 mbody,
      initMirState m4MoveAliasBody [.scalar .i64 false 21#64] = some mirSt0 ∧
      compileBody m4MoveAliasBody = some mbody ∧
      checkBodyInvs m4MoveAliasBody m4MoveAliasInv = false ∧
      runMirBlocks m4MoveAliasBody 2 mirSt0 = .fault .undefined ∧
      runMachBlocks mbody 2 (initMachState m4MoveAliasBody [.scalar .i64 false 21#64]) =
        .returned 42#64 := by
  refine ⟨{ bb := 0, slots := [.live none, .live (some (.scalar .i64 false 21#64))] },
    { frameSlots := 2, frameBytes := 16, blocks := [{
        insns := [.loadSlot .r0 1, .loadSlot .r1 1,
                  .alu2 .r0 .add .r0 .r1 (some .i64), .storeSlot 0 .r0],
        term := .retSlot0 none }] },
    rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 4: Two-Step Verified Checker Bootstrap Soundness & Thompson Attack Rejection -/

def SemRefines {Prog Obs : Type} (sem : Prog → Obs → Prop) (src tgt : Prog) : Prop :=
  ∀ o, sem tgt o → sem src o

def SpecCheckerSound {Prog Cert Obs : Type} (sem : Prog → Obs → Prop)
    (specCheck : Prog → Prog → Cert → Bool) : Prop :=
  ∀ src tgt cert, specCheck src tgt cert = true → SemRefines sem src tgt

/-- Soundness of a compiled checker in `MiniMachO0` using encoded `(src, tgt, cert)` words. -/
def MachCheckerSound {Prog Cert : Type} (mbody : MachBody) (fuel : Nat)
    (enc : Prog → Prog → Cert → List SeedVal)
    (specCheck : Prog → Prog → Cert → Bool) : Prop :=
  ∀ src tgt cert,
    runMachBlocks mbody fuel (initMachState
      { argCount := (enc src tgt cert).length, locals := [], hasStorageAnn := [], blocks := [] }
      (enc src tgt cert)) = .returned 1#64 →
    specCheck src tgt cert = true

theorem checkBodyInvs_step_returned_ty {body : MirBody} {invs : List (List AbsSlot)}
    {mirSt : MirState} {inv : List AbsSlot} {ty0 : SeedTy} {v : SeedVal}
    (hBody : checkBodyInvs body invs = true)
    (hGetInv : getAt? invs mirSt.bb = some inv)
    (hComp : CompatEnv body.locals mirSt.slots inv)
    (hTy0 : getAt? body.locals 0 = some ty0)
    (hRet : stepMirBlock body mirSt = .returned v) :
    valHasTy v ty0 = true := by
  obtain ⟨blk, envOut, hGetBlk, hAE, hTermCk⟩ := checkBodyInvs_lookup hBody hGetInv
  obtain ⟨sls₁, hEvStmts, hComp₁⟩ := absEvalStmts_sound hComp hAE
  have hStepEq : stepMirBlock body mirSt = evalTerm body.locals sls₁ blk.term := by
    simp [stepMirBlock, hGetBlk, hEvStmts]
  rw [hStepEq] at hRet
  cases hT : blk.term with
  | unreachable => simp [checkTermInv, hT] at hTermCk
  | goto tgt => simp [hT, evalTerm] at hRet
  | switchInt discr cases otherwise =>
    simp [checkTermInv, hT] at hTermCk
    cases hAD : absEvalPrimOperand body.locals envOut discr with
    | none => simp [hAD] at hTermCk
    | some pD =>
      rcases pD with ⟨dTy, env₂⟩
      obtain ⟨dVal, sls₂, hEvD, hPrim, hDValTy, _⟩ := absEvalPrimOperand_sound hComp₁ hAD
      simp [hT, evalTerm, hEvD] at hRet
      cases dVal with
      | unit | zstEnum _ =>
        cases dTy <;> simp [valHasTy] at hDValTy <;> simp [isPrimitiveReadableTy] at hPrim
      | scalar w _ bits =>
        cases hSw : evalSwitchCases w bits otherwise cases <;> simp [hSw] at hRet
      | bool b =>
        cases hSw : evalBoolSwitchCases b otherwise cases <;> simp [hSw] at hRet
  | assertNonZero cond expected tgt =>
    simp [checkTermInv, hT] at hTermCk
    cases hAC : absEvalPrimOperand body.locals envOut cond with
    | none => simp [hAC] at hTermCk
    | some pC =>
      rcases pC with ⟨cTy, env₂⟩
      obtain ⟨cVal, sls₂, hEvC, hPrim, hCVTy, _⟩ := absEvalPrimOperand_sound hComp₁ hAC
      simp [hT, evalTerm, hEvC] at hRet
      cases cVal with
      | unit | zstEnum _ =>
        cases cTy <;> simp [valHasTy] at hCVTy <;> simp [isPrimitiveReadableTy] at hPrim
      | bool b => cases hCnd : (b == expected) <;> simp [hCnd] at hRet
      | scalar _ _ bits => cases hCnd : ((bits != 0#64) == expected) <;> simp [hCnd] at hRet
  | return_ =>
    simp [checkTermInv, hT] at hTermCk
    simp [hT, evalTerm] at hRet
    obtain ⟨sl0, a0, hSl0, hA0, hC0⟩ := hComp₁.2.2 0 ty0 hTy0
    rw [hTermCk] at hA0; cases hA0
    rcases hC0 with ⟨v0, hSlEq, hValTy⟩
    rw [hSlEq] at hSl0
    simp [hSl0] at hRet
    subst hRet
    exact hValTy

theorem checkBodyInvs_run_returned_ty {body : MirBody} {invs : List (List AbsSlot)}
    {ty0 : SeedTy} {v : SeedVal}
    (hBody : checkBodyInvs body invs = true)
    (hTy0 : getAt? body.locals 0 = some ty0) :
    ∀ n mirSt inv,
      getAt? invs mirSt.bb = some inv →
      CompatEnv body.locals mirSt.slots inv →
      runMirBlocks body n mirSt = .returned v →
      valHasTy v ty0 = true
  | 0, mirSt, inv, _, _, hRun => by simp [runMirBlocks] at hRun
  | n + 1, mirSt, inv, hGet, hComp, hRun => by
    obtain ⟨hNF, hPres⟩ := checkBodyInvs_step hBody hGet hComp
    simp [runMirBlocks] at hRun
    cases hStep : stepMirBlock body mirSt with
    | fault k => exact absurd hStep (hNF k)
    | panicked => simp [hStep] at hRun
    | returned v' =>
      simp [hStep] at hRun; subst v'
      exact checkBodyInvs_step_returned_ty hBody hGet hComp hTy0 hStep
    | running mirSt₁ =>
      simp [hStep] at hRun
      obtain ⟨inv₁, hGet₁, hComp₁⟩ := hPres mirSt₁ hStep
      exact checkBodyInvs_run_returned_ty hBody hTy0 n mirSt₁ inv₁ hGet₁ hComp₁ hRun

/-- Step-1 + Step-2 Verified Checker Bootstrap Soundness Theorem.
    Once the checker MIR `certCheckMir` has `.bool` return type (`h_ret_bool`),
    is verified against `SeedMir` (`h_mir_verif`), passes static move/liveness
    checking (`h_invs`), and compiles cleanly via `compileBody` (`h_seed_compile`),
    any fast `-O3` checker binary accepted by `seedCheckerMach` soundly implies
    `SemRefines sem userSrc userTgtO3` — completely eliminating `lean -c`, `clang`,
    and the unverified `-O3` compiler from the steady-state TCB. -/
theorem two_step_bootstrap_sound
    {Prog Cert Obs : Type}
    (sem : Prog → Obs → Prop)
    (specCheck : Prog → Prog → Cert → Bool)
    (certCheckMir : MirBody)
    (certInvs : List (List AbsSlot))
    (seedCheckerMach : MachBody)
    (fuel : Nat)
    (enc : Prog → Prog → Cert → List SeedVal)
    (fastCheckerO3 : Prog)
    (bootCert : Cert)
    (certCheckAsProg : Prog)
    (runFastO3 : Prog → Prog → Prog → Cert → Bool)
    (userSrc userTgtO3 : Prog)
    (userCert : Cert)
    (h_ret_bool : getAt? certCheckMir.locals 0 = some .bool)
    (h_spec : SpecCheckerSound sem specCheck)
    (h_seed_compile : compileBody certCheckMir = some seedCheckerMach)
    (h_invs : checkBodyInvs certCheckMir certInvs = true)
    (h_mir_verif : ∀ p1 p2 c mirSt0,
      initMirState certCheckMir (enc p1 p2 c) = some mirSt0 →
      runMirBlocks certCheckMir fuel mirSt0 = .returned (.bool true) →
      specCheck p1 p2 c = true)
    (h_init_boot : ∃ mirSt0, initMirState certCheckMir (enc certCheckAsProg fastCheckerO3 bootCert) = some mirSt0)
    (h_step1_boot : runMachBlocks seedCheckerMach fuel
      (initMachState certCheckMir (enc certCheckAsProg fastCheckerO3 bootCert)) = .returned 1#64)
    (h_fast_semantic_link : SemRefines sem certCheckAsProg fastCheckerO3 →
      runFastO3 fastCheckerO3 userSrc userTgtO3 userCert = true →
      SemRefines sem userSrc userTgtO3)
    (h_step2_user : runFastO3 fastCheckerO3 userSrc userTgtO3 userCert = true) :
    SemRefines sem userSrc userTgtO3 := by
  obtain ⟨mirSt0, hInit⟩ := h_init_boot
  have hBack := (mirToMiniMachO0_backward_sim h_seed_compile h_invs hInit fuel).1 1#64 h_step1_boot
  rcases hBack with ⟨v, hMirRet, hEnc⟩
  obtain ⟨inv0, hGet0, hComp0⟩ := init_compatEnv h_invs hInit
  have hValBool : valHasTy v .bool = true :=
    checkBodyInvs_run_returned_ty h_invs h_ret_bool fuel mirSt0 inv0 hGet0 hComp0 hMirRet
  have hBoolTrue : v = .bool true := by
    cases v with
    | bool b =>
      cases b with
      | true => rfl
      | false => simp [encodeSeedVal] at hEnc
    | scalar _ _ _ | unit | zstEnum _ => simp [valHasTy] at hValBool
  exact h_fast_semantic_link (h_spec _ _ _ (h_mir_verif _ _ _ mirSt0 hInit (by rw [hMirRet, hBoolTrue]))) h_step2_user

/-- Concrete Step-1 checker MIR checking equality of an expected semantic digest tag
    against a candidate binary's certified digest tag across a 3-block CFG using
    `Operand.move` (`deinitMovedPlace = true`) and `switchInt`. -/
def seedCheckerMir : MirBody :=
  { argCount := 2
    locals := [.bool, .int .i64 false, .int .i64 false, .bool]
    hasStorageAnn := [false, false, false, false]
    blocks :=
      [ { stmts := [.assign 3 (.binOp .eq (.move 1) (.move 2))]
          term := .switchInt (.move 3) [(1#64, 1)] 2 }
      , { stmts := [.assign 0 (.use (.constVal .bool (.bool true)))]
          term := .return_ }
      , { stmts := [.assign 0 (.use (.constVal .bool (.bool false)))]
          term := .return_ } ] }

def seedCheckerInvs : List (List AbsSlot) :=
  [ [.uninit, .init, .init, .uninit]
  , [.uninit, .uninit, .uninit, .uninit]
  , [.uninit, .uninit, .uninit, .uninit] ]

theorem witness_bootstrap_accepts_valid_and_rejects_thompson_trojan :
    ∃ mbody mirStValid mirStTrojan,
      compileBody seedCheckerMir = some mbody ∧
      checkBodyInvs seedCheckerMir seedCheckerInvs = true ∧
      getAt? seedCheckerMir.locals 0 = some .bool ∧
      initMirState seedCheckerMir [.scalar .i64 false 42#64, .scalar .i64 false 42#64] = some mirStValid ∧
      initMirState seedCheckerMir [.scalar .i64 false 42#64, .scalar .i64 false 99#64] = some mirStTrojan ∧
      runMachBlocks mbody 2 (initMachState seedCheckerMir [.scalar .i64 false 42#64, .scalar .i64 false 42#64]) = .returned 1#64 ∧
      runMirBlocks seedCheckerMir 2 mirStValid = .returned (.bool true) ∧
      runMachBlocks mbody 2 (initMachState seedCheckerMir [.scalar .i64 false 42#64, .scalar .i64 false 99#64]) = .returned 0#64 ∧
      runMirBlocks seedCheckerMir 2 mirStTrojan = .returned (.bool false) := by
  refine ⟨
    { frameSlots := 4
      frameBytes := 32
      blocks :=
        [ { insns := [.loadSlot .r0 1, .loadSlot .r1 2, .alu2 .r0 .eq .r0 .r1 (some .i64),
                      .storeSlot 3 .r0, .loadSlot .r0 3]
            term := .brTable .r0 [(1#64, 1)] 2 }
        , { insns := [.movImm .r0 1#64, .storeSlot 0 .r0]
            term := .retSlot0 none }
        , { insns := [.movImm .r0 0#64, .storeSlot 0 .r0]
            term := .retSlot0 none } ] },
    { bb := 0
      slots := [.live none, .live (some (.scalar .i64 false 42#64)),
                .live (some (.scalar .i64 false 42#64)), .live none] },
    { bb := 0
      slots := [.live none, .live (some (.scalar .i64 false 42#64)),
                .live (some (.scalar .i64 false 99#64)), .live none] },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MirToMiniMachO0Seed

#print axioms MirToMiniMachO0Seed.mirToMiniMachO0_forward_sim
#print axioms MirToMiniMachO0Seed.mirToMiniMachO0_backward_sim
#print axioms MirToMiniMachO0Seed.cex_m4_move_then_copy_faults_in_mir_not_mach
#print axioms MirToMiniMachO0Seed.two_step_bootstrap_sound
#print axioms MirToMiniMachO0Seed.witness_bootstrap_accepts_valid_and_rejects_thompson_trojan
