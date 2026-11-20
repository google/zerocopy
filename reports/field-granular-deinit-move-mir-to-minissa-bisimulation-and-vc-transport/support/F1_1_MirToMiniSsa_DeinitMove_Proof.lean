/-
  F1-1 Statement-First Compiler Formalization (Stage 2 Revised Draft — Post Blind Review)
  Target Theorem: `MirToMiniSsa_DeinitMove_Bisim`

  Anchored in live `joshlf/anneal@c131b320e` (`trusted/lean/Trusted/MirSemantics.lean:949-1019, 1391-1393`,
  `deinitMovedPlace = true`, `StorageDead 0 -> .unsupported`) and `E1-1`/`E1-2d` real `rustc 1.99.1`
  (`58cf8f9c3`) empirical findings:
    - M3 (real `zerocopy::TryFromBytes::try_read_from_prefix` in `Runtime(PostCleanup)`,
      `zerocopy::padding_needed_for`, `libcore::slice_get_unchecked_mut_range`):
      sibling partial-field moves `move (_2.0); move (_2.1)` / `move (_4.0); copy (_4.1)` require
      field-granular move deinitialization rather than local-granular deinitialization.
    - M4 (real `libcore::parse_decimal_seq`, `dec2flt`, `round_up`):
      `slice_index_fail(const 8, copy _104, move _104)` requires strict left-to-right
      operand evaluation threading `locals` state from operand 1 to operand 2.
    - ZST exception (`Trusted.MirSemantics.liveUninitSlot`):
      moving an inhabited zero-sized `.unit` local leaves its slot inhabited (`.live .zst`),
      never uninitialized.

  Scope boundary vs. full `Trusted.MirSemantics.lean`:
    - Models `.u64`, `.unit`, and `.pairU64` (2-field struct extending `MirSemantics` to field
      projections); does NOT yet model `.bool`, multi-width signed/unsigned ints, fieldless
      enums, UB-bearing arithmetic (`.div`/`.rem`/unchecked overflow), or `cleanup`/calls.
    - Enforces `StorageDead 0 -> .error .unsupported` (matching `MirSemantics.lean:1391-1393`).
    - Uses `namespace VrustcFormal.F1_1` (NEVER shadows `namespace Trusted`).
    - Zero `bv_decide`, zero `native_decide`, zero `partial`, zero `@[extern]`.
-/

namespace VrustcFormal.F1_1

/-- Fault kinds mirroring `Trusted.MirSemantics.FaultKind`. -/
inductive FaultKind where
  | undefined   -- UB: reading dead or uninitialized (including moved-out non-ZST) place
  | unsupported -- out-of-bounds local / `StorageDead 0` / type mismatch / malformed CFG target
  deriving DecidableEq, Repr

/-- MIR local types: non-ZST `u64` scalar, inhabited ZST `unit`, and 2-field struct `(u64, u64)`
(modeling `zerocopy::TrailingSliceLayout`, `Range<usize>`, and `(MaybeUninit<Self>, &[u8])`). -/
inductive MirTy where
  | u64
  | unit
  | pairU64
  deriving DecidableEq, Repr

/-- Field selector for `MirTy.pairU64`. -/
inductive FieldIdx where
  | fst
  | snd
  deriving DecidableEq, Repr

/-- MIR place: either an unprojected local `_k` or a single-field projection `(_k.0)` / `(_k.1)`. -/
inductive Place where
  | local (id : Nat)
  | field (id : Nat) (f : FieldIdx)
  deriving DecidableEq, Repr

/-- Runtime scalar/ZST/pair values. -/
inductive Val where
  | u64 (n : UInt64)
  | unit
  | pair (a b : UInt64)
  deriving DecidableEq, Repr

/-- Live slot payload supporting field-granular initialization (independent init state per field). -/
inductive LivePayload where
  | scalar (v : Option UInt64)
  | zst
  | pair (v0 v1 : Option UInt64)
  deriving DecidableEq, Repr

/-- Local storage slot mirroring `Trusted.MirSemantics.LocalSlot` (`dead` vs `live`). -/
inductive LocalSlot where
  | dead
  | live (p : LivePayload)
  deriving DecidableEq, Repr

/-- `liveUninitSlot` matching `Trusted.MirSemantics.lean:942-947`:
ZST `.unit` locals stay inhabited (`.live .zst`); non-ZST locals become uninitialized. -/
def liveUninitSlot : MirTy → LocalSlot
  | .u64     => .live (.scalar none)
  | .unit    => .live .zst
  | .pairU64 => .live (.pair none none)

def getAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt? xs n

def setAt? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (setAt? xs n v).map (x :: ·)

/-- Granularity switch enabling formal comparison of `.fieldGranular` vs naive `.localGranular` deinit. -/
inductive DeinitMode where
  | fieldGranular
  | localGranular
  deriving DecidableEq, Repr

inductive Operand where
  | copy (p : Place)
  | move (p : Place)
  | constU64 (k : UInt64)
  | constUnit
  deriving DecidableEq, Repr

/-- Read a place value and deinitialize moved non-ZST places under `deinitMovedPlace = true`. -/
def evalOperand (mode : DeinitMode) (tys : List MirTy) (locals : List LocalSlot) :
    Operand → Except FaultKind (Val × List LocalSlot)
  | .constU64 k => .ok (.u64 k, locals)
  | .constUnit => .ok (.unit, locals)
  | .copy (.local id) =>
    match getAt? tys id, getAt? locals id with
    | some .u64, some (.live (.scalar (some v))) => .ok (.u64 v, locals)
    | some .u64, some (.live (.scalar none)) => .error .undefined
    | some .unit, some (.live .zst) => .ok (.unit, locals)
    | some .pairU64, some (.live (.pair (some a) (some b))) => .ok (.pair a b, locals)
    | some .pairU64, some (.live (.pair _ _)) => .error .undefined
    | some _, some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .move (.local id) =>
    match getAt? tys id, getAt? locals id with
    | some ty, some (.live payload) =>
      let readRes : Except FaultKind Val := match ty, payload with
        | .u64, .scalar (some v) => .ok (.u64 v)
        | .u64, .scalar none => .error .undefined
        | .unit, .zst => .ok .unit
        | .pairU64, .pair (some a) (some b) => .ok (.pair a b)
        | .pairU64, .pair _ _ => .error .undefined
        | _, _ => .error .unsupported
      match readRes with
      | .error e => .error e
      | .ok v =>
        match setAt? locals id (liveUninitSlot ty) with
        | some locals' => .ok (v, locals')
        | none => .error .unsupported
    | some _, some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .copy (.field id f) =>
    match getAt? tys id, getAt? locals id with
    | some .pairU64, some (.live (.pair v0 v1)) =>
      match f with
      | .fst => match v0 with | some v => .ok (.u64 v, locals) | none => .error .undefined
      | .snd => match v1 with | some v => .ok (.u64 v, locals) | none => .error .undefined
    | some .pairU64, some .dead => .error .undefined
    | _, _ => .error .unsupported
  | .move (.field id f) =>
    match getAt? tys id, getAt? locals id with
    | some .pairU64, some (.live (.pair v0 v1)) =>
      let readRes : Except FaultKind UInt64 := match f with
        | .fst => match v0 with | some v => .ok v | none => .error .undefined
        | .snd => match v1 with | some v => .ok v | none => .error .undefined
      match readRes with
      | .error e => .error e
      | .ok v =>
        let newSlot : LocalSlot := match mode with
          | .localGranular => .live (.pair none none)
          | .fieldGranular =>
            match f with
            | .fst => .live (.pair none v1)
            | .snd => .live (.pair v0 none)
        match setAt? locals id newSlot with
        | some locals' => .ok (.u64 v, locals')
        | none => .error .unsupported
    | some .pairU64, some .dead => .error .undefined
    | _, _ => .error .unsupported

inductive BinOp where
  | add | sub | xor | bitAnd
  deriving DecidableEq, Repr

def evalBinOp (op : BinOp) (a b : UInt64) : UInt64 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .xor => a ^^^ b
  | .bitAnd => a &&& b

inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs rhs : Operand)
  | mkPair (op0 op1 : Operand)
  deriving DecidableEq, Repr

/-- Strictly left-to-right rvalue evaluation (threading `locals1` from `lhs` to `rhs`). -/
def evalRvalue (mode : DeinitMode) (tys : List MirTy) (locals : List LocalSlot) :
    Rvalue → Except FaultKind (Val × List LocalSlot)
  | .use op => evalOperand mode tys locals op
  | .binaryOp op lhs rhs =>
    match evalOperand mode tys locals lhs with
    | .error e => .error e
    | .ok (.u64 a, locals1) =>
      match evalOperand mode tys locals1 rhs with
      | .error e => .error e
      | .ok (.u64 b, locals2) => .ok (.u64 (evalBinOp op a b), locals2)
      | .ok (_, _) => .error .unsupported
    | .ok (_, _) => .error .unsupported
  | .mkPair op0 op1 =>
    match evalOperand mode tys locals op0 with
    | .error e => .error e
    | .ok (.u64 a, locals1) =>
      match evalOperand mode tys locals1 op1 with
      | .error e => .error e
      | .ok (.u64 b, locals2) => .ok (.pair a b, locals2)
      | .ok (_, _) => .error .unsupported
    | .ok (_, _) => .error .unsupported

/-- Write value into a live MIR place (checks type compatibility before `.dead`). -/
def writePlace (tys : List MirTy) (locals : List LocalSlot) (p : Place) (v : Val) :
    Except FaultKind (List LocalSlot) :=
  match p with
  | .local id =>
    match getAt? tys id, getAt? locals id, v with
    | some .u64, some (.live _), .u64 n =>
      match setAt? locals id (.live (.scalar (some n))) with
      | some l' => .ok l' | none => .error .unsupported
    | some .unit, some (.live _), .unit =>
      match setAt? locals id (.live .zst) with
      | some l' => .ok l' | none => .error .unsupported
    | some .pairU64, some (.live _), .pair a b =>
      match setAt? locals id (.live (.pair (some a) (some b))) with
      | some l' => .ok l' | none => .error .unsupported
    | some .u64, some .dead, .u64 _ => .error .undefined
    | some .unit, some .dead, .unit => .error .undefined
    | some .pairU64, some .dead, .pair _ _ => .error .undefined
    | _, _, _ => .error .unsupported
  | .field id f =>
    match getAt? tys id, getAt? locals id, v with
    | some .pairU64, some (.live (.pair v0 v1)), .u64 n =>
      let next := match f with | .fst => LocalSlot.live (.pair (some n) v1) | .snd => LocalSlot.live (.pair v0 (some n))
      match setAt? locals id next with
      | some l' => .ok l' | none => .error .unsupported
    | some .pairU64, some .dead, .u64 _ => .error .undefined
    | _, _, _ => .error .unsupported

inductive MirStmt where
  | storageLive (id : Nat)
  | storageDead (id : Nat)
  | assign (dst : Place) (rv : Rvalue)
  deriving DecidableEq, Repr

inductive MirTerm where
  | goto (target : Nat)
  | switchZero (discr : Operand) (zeroTarget nonZeroTarget : Nat)
  | ret
  deriving DecidableEq, Repr

structure MirBlock where
  stmts : List MirStmt
  term  : MirTerm
  deriving DecidableEq, Repr

structure MirBody where
  localTys : List MirTy   -- _0 is return place (u64), _1.._k are args/locals
  blocks   : List MirBlock
  deriving DecidableEq, Repr

inductive ExecOutcome where
  | ret (v : UInt64)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Step one MIR statement (enforcing `StorageDead 0 -> .error .unsupported` per
`Trusted/MirSemantics.lean:1391-1393`, `StackError.cannotMakeReturnPlaceDead`). -/
def stepMirStmt (mode : DeinitMode) (tys : List MirTy) (locals : List LocalSlot) :
    MirStmt → Except FaultKind (List LocalSlot)
  | .storageLive id =>
    match getAt? tys id with
    | some ty =>
      match setAt? locals id (liveUninitSlot ty) with
      | some l' => .ok l' | none => .error .unsupported
    | none => .error .unsupported
  | .storageDead id =>
    if id == 0 then
      .error .unsupported
    else
      match getAt? tys id with
      | some _ =>
        match setAt? locals id .dead with
        | some l' => .ok l' | none => .error .unsupported
      | none => .error .unsupported
  | .assign dst rv =>
    match evalRvalue mode tys locals rv with
    | .error e => .error e
    | .ok (v, locals1) => writePlace tys locals1 dst v

def stepMirStmts (mode : DeinitMode) (tys : List MirTy) (locals : List LocalSlot) :
    List MirStmt → Except FaultKind (List LocalSlot)
  | [] => .ok locals
  | s :: rest =>
    match stepMirStmt mode tys locals s with
    | .error e => .error e
    | .ok l' => stepMirStmts mode tys l' rest

/-- Genuine fuel-indexed operational CFG execution (NO closed-form loop shortcuts). -/
def execMirLoop (mode : DeinitMode) (body : MirBody) :
    Nat → Nat → List LocalSlot → Except FaultKind ExecOutcome
  | 0, _, _ => .ok .outOfFuel
  | fuel + 1, pc, locals =>
    match getAt? body.blocks pc with
    | none => .error .unsupported
    | some blk =>
      match stepMirStmts mode body.localTys locals blk.stmts with
      | .error e => .error e
      | .ok l1 =>
        match blk.term with
        | .goto tgt => execMirLoop mode body fuel tgt l1
        | .switchZero discr zTgt nzTgt =>
          match evalOperand mode body.localTys l1 discr with
          | .error e => .error e
          | .ok (.u64 n, l2) =>
            if n == 0 then execMirLoop mode body fuel zTgt l2
            else execMirLoop mode body fuel nzTgt l2
          | .ok (_, _) => .error .unsupported
        | .ret =>
          match getAt? body.localTys 0, getAt? l1 0 with
          | some .u64, some (.live (.scalar (some v))) => .ok (.ret v)
          | some .u64, some (.live (.scalar none)) => .error .undefined
          | some .u64, some .dead => .error .undefined
          | _, _ => .error .unsupported

/-! ### Target `MiniSSA` IR (Immutable SSA Registers + Block-Parameter Phis, Zero Move Mutation) -/

inductive SsaArg where
  | reg (r : Nat)
  | constU64 (k : UInt64)
  deriving DecidableEq, Repr

inductive SsaStmt where
  | copy (dst : Nat) (src : SsaArg)
  | binOp (dst : Nat) (op : BinOp) (lhs rhs : SsaArg)
  deriving DecidableEq, Repr

inductive SsaTerm where
  | goto (target : Nat) (phiArgs : List SsaArg)
  | switchZero (discr : SsaArg)
      (zTarget : Nat) (zPhiArgs : List SsaArg)
      (nzTarget : Nat) (nzPhiArgs : List SsaArg)
  | ret (v : SsaArg)
  deriving DecidableEq, Repr

structure SsaBlock where
  params : List Nat       -- block-parameter SSA registers bound in parallel on entry
  stmts  : List SsaStmt
  term   : SsaTerm
  deriving DecidableEq, Repr

structure SsaBody where
  blocks : List SsaBlock
  deriving DecidableEq, Repr

abbrev SsaEnv := Nat → Option UInt64

def evalSsaArg (env : SsaEnv) : SsaArg → Option UInt64
  | .reg r => env r
  | .constU64 k => some k

def bindSsa (env : SsaEnv) (r : Nat) (v : UInt64) : SsaEnv :=
  fun x => if x == r then some v else env x

/-- Parallel phi-parameter rebinding (`evalEnv` stays fixed while updating `baseEnv`). -/
def bindSsaParams (baseEnv : SsaEnv) (evalEnv : SsaEnv) :
    List Nat → List SsaArg → Option SsaEnv
  | [], [] => some baseEnv
  | r :: rs, a :: as =>
    match evalSsaArg evalEnv a with
    | none => none
    | some v => bindSsaParams (bindSsa baseEnv r v) evalEnv rs as
  | _, _ => none

def stepSsaStmts (env : SsaEnv) : List SsaStmt → Option SsaEnv
  | [] => some env
  | .copy dst a :: rest =>
    match evalSsaArg env a with
    | none => none
    | some v => stepSsaStmts (bindSsa env dst v) rest
  | .binOp dst op a b :: rest =>
    match evalSsaArg env a, evalSsaArg env b with
    | some va, some vb => stepSsaStmts (bindSsa env dst (evalBinOp op va vb)) rest
    | _, _ => none

def execSsaLoop (body : SsaBody) : Nat → Nat → SsaEnv → Option ExecOutcome
  | 0, _, _ => some .outOfFuel
  | fuel + 1, pc, env =>
    match getAt? body.blocks pc with
    | none => none
    | some blk =>
      match stepSsaStmts env blk.stmts with
      | none => none
      | some env1 =>
        match blk.term with
        | .goto tgt args =>
          match getAt? body.blocks tgt with
          | none => none
          | some tblk =>
            match bindSsaParams env1 env1 tblk.params args with
            | none => none
            | some env2 => execSsaLoop body fuel tgt env2
        | .switchZero discr zTgt zArgs nzTgt nzArgs =>
          match evalSsaArg env1 discr with
          | none => none
          | some n =>
            let (tgt, args) := if n == 0 then (zTgt, zArgs) else (nzTgt, nzArgs)
            match getAt? body.blocks tgt with
            | none => none
            | some tblk =>
              match bindSsaParams env1 env1 tblk.params args with
              | none => none
              | some env2 => execSsaLoop body fuel tgt env2
        | .ret a =>
          match evalSsaArg env1 a with
          | none => none
          | some v => some (.ret v)

/-! ### Single-Pass Decidable `deinitMovedPlace`-Aware Certificate & Checker -/

/-- Abstract per-local liveness + field-granular initialization + SSA register mapping. -/
inductive AbsSlot where
  | dead
  | liveScalar (ssaReg : Option Nat)       -- `some r` iff provably initialized & equal to SSA reg `r`
  | liveZst                                -- inhabited `.unit` ZST (valid even after `move`)
  | livePair (ssaReg0 ssaReg1 : Option Nat) -- field-granular SSA register mapping
  deriving DecidableEq, Repr

structure SsaCert where
  blockEntryAbs : List (List AbsSlot)
  deriving DecidableEq, Repr

/-- Exact refinement relation between concrete MIR `LocalSlot`s, `MirTy`s, `SsaEnv`, and `AbsSlot`s. -/
def slotMatches (env : SsaEnv) : MirTy → LocalSlot → AbsSlot → Prop
  | _, .dead, .dead => True
  | .u64, .live (.scalar (some v)), .liveScalar (some r) => env r = some v
  | .u64, .live (.scalar _), .liveScalar none => True
  | .unit, .live .zst, .liveZst => True
  | .pairU64, .live (.pair v0 v1), .livePair r0 r1 =>
      (∀ reg, r0 = some reg → ∃ x, v0 = some x ∧ env reg = some x) ∧
      (∀ reg, r1 = some reg → ∃ y, v1 = some y ∧ env reg = some y)
  | _, _, _ => False

def stateMatches (env : SsaEnv) (tys : List MirTy) (locals : List LocalSlot) (abs : List AbsSlot) : Prop :=
  tys.length = locals.length ∧ locals.length = abs.length ∧
  ∀ i ty sl ab, getAt? tys i = some ty → getAt? locals i = some sl → getAt? abs i = some ab →
    slotMatches env ty sl ab

/-- True iff SSA register `r` is not currently referenced by any slot in `abs`. -/
def regNotInAbs (r : Nat) (abs : List AbsSlot) : Bool :=
  abs.all fun
    | .dead => true
    | .liveZst => true
    | .liveScalar (some x) => x != r
    | .liveScalar none => true
    | .livePair a b => (a != some r) && (b != some r)

/-- Decidable abstract operand check under field-granular `deinitMovedPlace = true`:
verifies live+initialized, yields corresponding `SsaArg`, and clears ONLY the moved local/field. -/
def checkAbsOperand (tys : List MirTy) (abs : List AbsSlot) :
    Operand → Option (Option SsaArg × List AbsSlot)
  | .constU64 k => some (some (.constU64 k), abs)
  | .constUnit => some (none, abs)
  | .copy (.local id) =>
    match getAt? tys id, getAt? abs id with
    | some .u64, some (.liveScalar (some r)) => some (some (.reg r), abs)
    | some .unit, some .liveZst => some (none, abs)
    | _, _ => none
  | .move (.local id) =>
    match getAt? tys id, getAt? abs id with
    | some .u64, some (.liveScalar (some r)) =>
      (setAt? abs id (.liveScalar none)).map fun abs' => (some (.reg r), abs')
    | some .unit, some .liveZst => some (none, abs)
    | _, _ => none
  | .copy (.field id f) =>
    match getAt? tys id, getAt? abs id with
    | some .pairU64, some (.livePair r0 r1) =>
      match f with
      | .fst => r0.map fun r => (some (.reg r), abs)
      | .snd => r1.map fun r => (some (.reg r), abs)
    | _, _ => none
  | .move (.field id f) =>
    match getAt? tys id, getAt? abs id with
    | some .pairU64, some (.livePair r0 r1) =>
      match f with
      | .fst => r0.bind fun r => (setAt? abs id (.livePair none r1)).map fun abs' => (some (.reg r), abs')
      | .snd => r1.bind fun r => (setAt? abs id (.livePair r0 none)).map fun abs' => (some (.reg r), abs')
    | _, _ => none

/-- Single-pass lockstep MIR-to-MiniSSA statement checker (merges freshness checks inline,
fixes B1 `a1' != .reg r0` sequential clobber, and fixes B3 `StorageDead 0` rejection). -/
def checkBlockStmts (tys : List MirTy) :
    List AbsSlot → List MirStmt → List SsaStmt → Option (List AbsSlot)
  | abs, [], [] => some abs
  | abs, .storageLive id :: mrest, sstmts =>
    match getAt? tys id with
    | some .u64     => (setAt? abs id (.liveScalar none)).bind fun a' => checkBlockStmts tys a' mrest sstmts
    | some .unit    => (setAt? abs id .liveZst).bind fun a' => checkBlockStmts tys a' mrest sstmts
    | some .pairU64 => (setAt? abs id (.livePair none none)).bind fun a' => checkBlockStmts tys a' mrest sstmts
    | none => none
  | abs, .storageDead id :: mrest, sstmts =>
    if id == 0 then none
    else
      match getAt? tys id with
      | some _ => (setAt? abs id .dead).bind fun a' => checkBlockStmts tys a' mrest sstmts
      | none => none
  | abs, .assign (.local id) (.use op) :: mrest, sstmts =>
    match getAt? tys id, getAt? abs id with
    | some .unit, some .liveZst =>
      match checkAbsOperand tys abs op with
      | some (none, abs1) => checkBlockStmts tys abs1 mrest sstmts
      | _ => none
    | some .u64, some (.liveScalar _) =>
      match checkAbsOperand tys abs op, sstmts with
      | some (some sArg, abs1), .copy dstReg sArg' :: srest =>
        if sArg == sArg' then
          (setAt? abs1 id (.liveScalar none)).bind fun aCleared =>
            if regNotInAbs dstReg aCleared then
              (setAt? aCleared id (.liveScalar (some dstReg))).bind fun abs2 =>
                checkBlockStmts tys abs2 mrest srest
            else none
        else none
      | _, _ => none
    | _, _ => none
  | abs, .assign (.local id) (.binaryOp bop lhs rhs) :: mrest, .binOp dstReg bop' sL sR :: srest =>
    if bop != bop' then none else
    match getAt? tys id, getAt? abs id with
    | some .u64, some (.liveScalar _) =>
      match checkAbsOperand tys abs lhs with
      | some (some aL, abs1) =>
        match checkAbsOperand tys abs1 rhs with
        | some (some aR, abs2) =>
          if aL == sL && aR == sR then
            (setAt? abs2 id (.liveScalar none)).bind fun aCleared =>
              if regNotInAbs dstReg aCleared then
                (setAt? aCleared id (.liveScalar (some dstReg))).bind fun abs3 =>
                  checkBlockStmts tys abs3 mrest srest
              else none
          else none
        | _ => none
      | _ => none
    | _, _ => none
  | abs, .assign (.local id) (.mkPair op0 op1) :: mrest, .copy r0 a0' :: .copy r1 a1' :: srest =>
    match getAt? tys id, getAt? abs id with
    | some .pairU64, some (.livePair _ _) =>
      match checkAbsOperand tys abs op0 with
      | some (some a0, abs1) =>
        match checkAbsOperand tys abs1 op1 with
        | some (some a1, abs2) =>
          -- B1 fix: `a1' != .reg r0` guarantees `.copy r0 a0'` cannot clobber `a1'` before `.copy r1 a1'`!
          if a0 == a0' && a1 == a1' && r0 != r1 && a1' != .reg r0 then
            (setAt? abs2 id (.livePair none none)).bind fun aCleared =>
              if regNotInAbs r0 aCleared && regNotInAbs r1 aCleared then
                (setAt? aCleared id (.livePair (some r0) (some r1))).bind fun abs3 =>
                  checkBlockStmts tys abs3 mrest srest
              else none
          else none
        | _ => none
      | _ => none
    | _, _ => none
  | abs, .assign (.field id f) (.use op) :: mrest, .copy dstReg sArg' :: srest =>
    match getAt? tys id, getAt? abs id with
    | some .pairU64, some (.livePair _ _) =>
      match checkAbsOperand tys abs op with
      | some (some sArg, abs1) =>
        if sArg == sArg' then
          match getAt? abs1 id with
          | some (.livePair r0' r1') =>
            let cleared := match f with | .fst => AbsSlot.livePair none r1' | .snd => AbsSlot.livePair r0' none
            (setAt? abs1 id cleared).bind fun aCleared =>
              if regNotInAbs dstReg aCleared then
                let next := match f with | .fst => AbsSlot.livePair (some dstReg) r1' | .snd => AbsSlot.livePair r0' (some dstReg)
                (setAt? aCleared id next).bind fun abs2 => checkBlockStmts tys abs2 mrest srest
              else none
          | _ => none
        else none
      | _ => none
    | _, _ => none
  | _, _, _ => none

/-- Check CFG edge phi rebinding (B2 fix: requires EVERY `.reg rs` in `edgeArgs` to be live in
`absEnd` so `bindSsaParams` can never fail with `none` on an unused/dead phi parameter!). -/
def checkEdge (absEnd : List AbsSlot) (tgtAbs : List AbsSlot)
    (tgtParams : List Nat) (edgeArgs : List SsaArg) : Bool :=
  tgtParams.length == edgeArgs.length &&
  absEnd.length == tgtAbs.length &&
  (tgtParams.eraseDups.length == tgtParams.length) &&
  (edgeArgs.all fun
    | .constU64 _ => true
    | .reg rs => !regNotInAbs rs absEnd) &&
  let pairs := tgtParams.zip edgeArgs
  (absEnd.zip tgtAbs).all fun (srcSl, dstSl) =>
    let regOk (srcOpt dstOpt : Option Nat) : Bool :=
      match dstOpt with
      | none => true
      | some rd =>
        match pairs.find? (fun p => p.1 == rd) with
        | some (_, .reg rs) => srcOpt == some rs
        | some (_, .constU64 _) => false
        | none => (srcOpt == some rd) && !(tgtParams.contains rd)
    match srcSl, dstSl with
    | .dead, .dead => true
    | .liveZst, .liveZst => true
    | .liveScalar rs, .liveScalar rd => regOk rs rd
    | .livePair s0 s1, .livePair d0 d1 => regOk s0 d0 && regOk s1 d1
    | _, _ => false

def checkOneBlock (mir : MirBody) (ssa : SsaBody) (cert : SsaCert) (pc : Nat) : Bool :=
  match getAt? mir.blocks pc, getAt? ssa.blocks pc, getAt? cert.blockEntryAbs pc with
  | some mblk, some sblk, some entryAbs =>
    (entryAbs.length == mir.localTys.length) &&
    match checkBlockStmts mir.localTys entryAbs mblk.stmts sblk.stmts with
    | none => false
    | some absEnd =>
      match mblk.term, sblk.term with
      | .goto tgt, .goto sTgt sArgs =>
        (tgt == sTgt) &&
        match getAt? ssa.blocks tgt, getAt? cert.blockEntryAbs tgt with
        | some tblk, some tAbs => checkEdge absEnd tAbs tblk.params sArgs
        | _, _ => false
      | .switchZero discr zTgt nzTgt, .switchZero sDiscr szTgt szArgs snzTgt snzArgs =>
        (zTgt == szTgt) && (nzTgt == snzTgt) &&
        match checkAbsOperand mir.localTys absEnd discr with
        | some (some aDiscr, absAfter) =>
          (aDiscr == sDiscr) &&
          match getAt? ssa.blocks zTgt, getAt? cert.blockEntryAbs zTgt,
                getAt? ssa.blocks nzTgt, getAt? cert.blockEntryAbs nzTgt with
          | some zBlk, some zAbs, some nzBlk, some nzAbs =>
            checkEdge absAfter zAbs zBlk.params szArgs &&
            checkEdge absAfter nzAbs nzBlk.params snzArgs
          | _, _, _, _ => false
        | _ => false
      | .ret, .ret sRetArg =>
        match getAt? mir.localTys 0, getAt? absEnd 0 with
        | some .u64, some (.liveScalar (some r0)) => sRetArg == .reg r0
        | _, _ => false
      | _, _ => false
  | _, _, _ => false

def checkMirToMiniSsaCert (mir : MirBody) (ssa : SsaBody) (cert : SsaCert) : Bool :=
  (mir.blocks.length == ssa.blocks.length) &&
  (mir.blocks.length == cert.blockEntryAbs.length) &&
  (List.range mir.blocks.length).all (checkOneBlock mir ssa cert)

/-! ### Private Proof Helpers -/

private theorem getAt?_lt_length {α : Type} :
    ∀ (l : List α) (i : Nat) (x : α), getAt? l i = some x → i < l.length
  | [], _, _, h => by simp [getAt?] at h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, n + 1, x, h => Nat.succ_lt_succ (getAt?_lt_length xs n x h)

private theorem getAt?_some_of_lt {α : Type} :
    ∀ (l : List α) (i : Nat), i < l.length → ∃ x, getAt? l i = some x
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, n + 1, h => getAt?_some_of_lt xs n (Nat.lt_of_succ_lt_succ h)

private theorem setAt?_some_of_lt {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α), i < l.length → ∃ l', setAt? l i v = some l'
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: xs, 0, v, _ => ⟨v :: xs, rfl⟩
  | x :: xs, n + 1, v, h =>
    let ⟨l', hl'⟩ := setAt?_some_of_lt xs n v (Nat.lt_of_succ_lt_succ h)
    ⟨x :: l', by simp [setAt?, hl']⟩

private theorem setAt?_length {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α) (l' : List α), setAt? l i v = some l' → l'.length = l.length
  | [], _, _, _, h => by simp [setAt?] at h
  | _ :: _, 0, _, _, h => by simp [setAt?] at h; subst h; rfl
  | x :: xs, n + 1, v, l', h => by
    simp [setAt?] at h
    rcases h with ⟨l1, hl1, rfl⟩
    simp [setAt?_length xs n v l1 hl1]

private theorem getAt?_setAt?_eq {α : Type} :
    ∀ (l : List α) (i : Nat) (v : α) (l' : List α), setAt? l i v = some l' → getAt? l' i = some v
  | [], _, _, _, h => by simp [setAt?] at h
  | _ :: _, 0, _, _, h => by simp [setAt?] at h; subst h; rfl
  | _ :: xs, n + 1, v, l', h => by
    simp [setAt?] at h
    rcases h with ⟨l1, hl1, rfl⟩
    exact getAt?_setAt?_eq xs n v l1 hl1

private theorem getAt?_setAt?_ne {α : Type} :
    ∀ (l : List α) (i j : Nat) (v : α) (l' : List α),
      setAt? l i v = some l' → j ≠ i → getAt? l' j = getAt? l j
  | [], _, _, _, _, h, _ => by simp [setAt?] at h
  | _ :: _, 0, 0, _, _, _, hne => absurd rfl hne
  | _ :: xs, 0, j + 1, _, _, h, _ => by simp [setAt?] at h; subst h; rfl
  | _ :: xs, n + 1, 0, v, l', h, _ => by
    simp [setAt?] at h; rcases h with ⟨l1, _, rfl⟩; rfl
  | _ :: xs, n + 1, j + 1, v, l', h, hne => by
    simp [setAt?] at h
    rcases h with ⟨l1, hl1, rfl⟩
    exact getAt?_setAt?_ne xs n j v l1 hl1 (fun heq => hne (congrArg Nat.succ heq))

private theorem getAt?_mem {α : Type} :
    ∀ (l : List α) (i : Nat) (x : α), getAt? l i = some x → x ∈ l
  | [], _, _, h => by simp [getAt?] at h
  | _ :: _, 0, _, h => by simp [getAt?] at h; subst h; exact List.Mem.head _
  | _ :: xs, n + 1, y, h => List.Mem.tail _ (getAt?_mem xs n y h)

private theorem mem_to_getAt? {α : Type} :
    ∀ (l : List α) (x : α), x ∈ l → ∃ i, getAt? l i = some x
  | [], _, h => nomatch h
  | _ :: ys, x, h => by
    cases h with
    | head => exact ⟨0, rfl⟩
    | tail _ htail =>
      let ⟨i, hi⟩ := mem_to_getAt? ys x htail
      exact ⟨i + 1, hi⟩

private theorem getAt?_zip_mem {α β : Type} :
    ∀ (xs : List α) (ys : List β) (i : Nat) (a : α) (b : β),
      getAt? xs i = some a → getAt? ys i = some b → (a, b) ∈ xs.zip ys
  | [], _, _, _, _, hx, _ => by simp [getAt?] at hx
  | _, [], _, _, _, _, hy => by simp [getAt?] at hy
  | _ :: _, _ :: _, 0, _, _, hx, hy => by
    simp [getAt?] at hx hy
    subst hx; subst hy
    exact List.Mem.head _
  | _ :: xs, _ :: ys, n + 1, a, b, hx, hy =>
    List.Mem.tail _ (getAt?_zip_mem xs ys n a b hx hy)

private theorem exists_of_all_eq_false {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.all p = false → ∃ x, x ∈ l ∧ p x = false
  | [], h => by simp at h
  | x :: xs, h => by
    cases hpx : p x with
    | false => exact ⟨x, List.Mem.head _, hpx⟩
    | true =>
      have hxs : xs.all p = false := by
        rw [List.all_cons, hpx, Bool.true_and] at h
        exact h
      let ⟨y, hy, hpy⟩ := exists_of_all_eq_false p xs hxs
      exact ⟨y, List.Mem.tail _ hy, hpy⟩

private theorem eraseDupsBy_loop_length_le {α : Type} (r : α → α → Bool) :
    ∀ (as bs : List α), (List.eraseDupsBy.loop r as bs).length ≤ as.length + bs.length
  | [], bs => by simp [List.eraseDupsBy.loop]
  | a :: as, bs => by
    simp only [List.eraseDupsBy.loop]
    cases bs.any (r a)
    · have ih := eraseDupsBy_loop_length_le r as (a :: bs)
      simp only [List.length_cons] at ih ⊢
      omega
    · have ih := eraseDupsBy_loop_length_le r as bs
      simp only [List.length_cons]
      omega

private theorem eraseDupsBy_loop_eq_nodup :
    ∀ (as bs : List Nat),
      (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) as bs).length = as.length + bs.length →
      as.Nodup ∧ ∀ x, x ∈ as → x ∉ bs
  | [], _, _ => ⟨List.Pairwise.nil, fun _ h => nomatch h⟩
  | a :: as, bs, hlen => by
    simp only [List.eraseDupsBy.loop] at hlen
    cases h : bs.any (fun x2 => a == x2) with
    | true =>
      rw [h] at hlen
      have hle := eraseDupsBy_loop_length_le (fun x1 x2 => x1 == x2) as bs
      simp only [List.length_cons] at hlen
      omega
    | false =>
      rw [h] at hlen
      have hlen' : (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) as (a :: bs)).length =
          as.length + (a :: bs).length := by
        simp only [List.length_cons] at hlen ⊢
        omega
      have ⟨hnodup, hnotmem⟩ := eraseDupsBy_loop_eq_nodup as (a :: bs) hlen'
      have ha_not_as : a ∉ as := fun ha => hnotmem a ha (List.Mem.head _)
      have ha_not_bs : a ∉ bs := by
        intro habs
        have htrue : bs.any (fun x2 => a == x2) = true :=
          List.any_eq_true.mpr ⟨a, habs, beq_iff_eq.mpr rfl⟩
        rw [htrue] at h
        cases h
      refine ⟨List.nodup_cons.mpr ⟨ha_not_as, hnodup⟩, ?_⟩
      intro x hx
      cases hx with
      | head => exact ha_not_bs
      | tail _ hxt =>
        intro hxbs
        exact hnotmem x hxt (List.Mem.tail _ hxbs)

private theorem nodup_of_eraseDups_length (l : List Nat)
    (h : l.eraseDups.length = l.length) : l.Nodup := by
  have h' : (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l []).length =
      l.length + ([] : List Nat).length := by
    simpa [List.eraseDups, List.eraseDupsBy] using h
  exact (eraseDupsBy_loop_eq_nodup l [] h').1

private theorem bindSsa_eq (env : SsaEnv) (r : Nat) (v : UInt64) :
    bindSsa env r v r = some v := by
  unfold bindSsa
  have hr : (r == r) = true := beq_iff_eq.mpr rfl
  rw [hr]
  rfl

private theorem bindSsa_ne (env : SsaEnv) (r x : Nat) (v : UInt64) (hne : x ≠ r) :
    bindSsa env r v x = env x := by
  simp [bindSsa, hne]

private def absSlotNotMention (r : Nat) : AbsSlot → Bool
  | .dead => true
  | .liveZst => true
  | .liveScalar (some x) => x != r
  | .liveScalar none => true
  | .livePair a b => (a != some r) && (b != some r)

private theorem regNotInAbs_eq_all (r : Nat) (abs : List AbsSlot) :
    regNotInAbs r abs = abs.all (absSlotNotMention r) := rfl

private theorem slotMatches_bindSsa_of_notMention
    (env : SsaEnv) (ty : MirTy) (sl : LocalSlot) (ab : AbsSlot)
    (r : Nat) (v : UInt64)
    (hm : slotMatches env ty sl ab)
    (hnm : absSlotNotMention r ab = true) :
    slotMatches (bindSsa env r v) ty sl ab := by
  cases ab with
  | dead =>
    cases sl with
    | dead => trivial
    | live p => cases ty <;> cases p <;> simp [slotMatches] at hm
  | liveZst =>
    cases ty <;> cases sl <;> try (simp [slotMatches] at hm)
    case unit.live p =>
      cases p <;> simp [slotMatches] at hm ⊢
  | liveScalar opt =>
    cases opt with
    | none =>
      cases ty <;> cases sl <;> try (simp [slotMatches] at hm)
      case u64.live p =>
        cases p <;> simp [slotMatches] at hm ⊢
    | some x =>
      have hne : x ≠ r := by simpa [absSlotNotMention] using hnm
      cases ty <;> cases sl <;> try (simp [slotMatches] at hm)
      case u64.live p =>
        cases p with
        | scalar ov =>
          cases ov with
          | none => simp at hm
          | some val =>
            simp only [slotMatches] at hm ⊢
            rw [bindSsa_ne env r x v hne]
            exact hm
        | zst => simp at hm
        | pair _ _ => simp at hm
  | livePair r0 r1 =>
    simp only [absSlotNotMention, Bool.and_eq_true, bne_iff_ne] at hnm
    cases ty <;> cases sl <;> try (simp [slotMatches] at hm)
    case pairU64.live p =>
      cases p with
      | pair v0 v1 =>
        simp only [slotMatches] at hm ⊢
        refine ⟨?_, ?_⟩
        · intro reg hreg
          have hne : reg ≠ r := fun heq => hnm.1 (heq ▸ hreg)
          have ⟨x, hx0, hxr⟩ := hm.1 reg hreg
          exact ⟨x, hx0, by rw [bindSsa_ne env r reg v hne]; exact hxr⟩
        · intro reg hreg
          have hne : reg ≠ r := fun heq => hnm.2 (heq ▸ hreg)
          have ⟨y, hy1, hyr⟩ := hm.2 reg hreg
          exact ⟨y, hy1, by rw [bindSsa_ne env r reg v hne]; exact hyr⟩
      | scalar _ => simp at hm
      | zst => simp at hm

private theorem exists_val_of_not_regNotInAbs
    (env : SsaEnv) (tys : List MirTy) (locals : List LocalSlot) (abs : List AbsSlot)
    (rs : Nat)
    (hm : stateMatches env tys locals abs)
    (h : (!regNotInAbs rs abs) = true) :
    ∃ v, env rs = some v := by
  have hfalse : abs.all (absSlotNotMention rs) = false := by
    rw [← regNotInAbs_eq_all]
    cases hr : regNotInAbs rs abs <;> simp [hr] at h ⊢
  obtain ⟨ab, habMem, habFalse⟩ := exists_of_all_eq_false (absSlotNotMention rs) abs hfalse
  obtain ⟨i, hiAbs⟩ := mem_to_getAt? abs ab habMem
  have hiLt : i < abs.length := getAt?_lt_length abs i ab hiAbs
  have ⟨htl, hla, hslots⟩ := hm
  obtain ⟨sl, hiLoc⟩ := getAt?_some_of_lt locals i (hla.symm ▸ hiLt)
  obtain ⟨ty, hiTy⟩ := getAt?_some_of_lt tys i (htl.symm ▸ hla.symm ▸ hiLt)
  have hsm := hslots i ty sl ab hiTy hiLoc hiAbs
  cases ab with
  | dead => simp [absSlotNotMention] at habFalse
  | liveZst => simp [absSlotNotMention] at habFalse
  | liveScalar opt =>
    cases opt with
    | none => simp [absSlotNotMention] at habFalse
    | some x =>
      have hxrs : x = rs := by simpa [absSlotNotMention] using habFalse
      subst hxrs
      cases ty <;> cases sl <;> try (simp [slotMatches] at hsm)
      case u64.live p =>
        cases p with
        | scalar ov =>
          cases ov with
          | none => simp at hsm
          | some v => exact ⟨v, hsm⟩
        | zst => simp at hsm
        | pair _ _ => simp at hsm
  | livePair r0 r1 =>
    cases ty <;> cases sl <;> try (simp [slotMatches] at hsm)
    case pairU64.live p =>
      cases p with
      | pair v0 v1 =>
        simp only [absSlotNotMention] at habFalse
        cases h0 : (r0 != some rs) with
        | false =>
          have hr0 : r0 = some rs := by simpa using h0
          obtain ⟨x, _, hxr⟩ := hsm.1 rs hr0
          exact ⟨x, hxr⟩
        | true =>
          have h1 : (r1 != some rs) = false := by simpa [h0] using habFalse
          have hr1 : r1 = some rs := by simpa using h1
          obtain ⟨y, _, hyr⟩ := hsm.2 rs hr1
          exact ⟨y, hyr⟩
      | scalar _ => simp at hsm
      | zst => simp at hsm

private theorem evalOperand_preserves_live
    (mode : DeinitMode) (tys : List MirTy) (locals locals' : List LocalSlot)
    (op : Operand) (v : Val) (id : Nat) (p : LivePayload)
    (heval : evalOperand mode tys locals op = .ok (v, locals'))
    (hlive : getAt? locals id = some (.live p)) :
    ∃ p', getAt? locals' id = some (.live p') := by
  cases op with
  | constU64 k =>
    simp [evalOperand] at heval
    rcases heval with ⟨_, rfl⟩
    exact ⟨p, hlive⟩
  | constUnit =>
    simp [evalOperand] at heval
    rcases heval with ⟨_, rfl⟩
    exact ⟨p, hlive⟩
  | copy pl =>
    cases pl with
    | «local» id' =>
      simp only [evalOperand] at heval
      cases hty : getAt? tys id' with
      | none => simp [hty] at heval
      | some ty =>
        cases hsl : getAt? locals id' with
        | none => simp [hty, hsl] at heval
        | some sl =>
          cases ty <;> cases sl <;> simp [hty, hsl] at heval
          · case u64.live q =>
            cases q with
            | scalar ov =>
              cases ov <;> simp at heval
              rcases heval with ⟨_, rfl⟩
              exact ⟨p, hlive⟩
            | zst => simp at heval
            | pair _ _ => simp at heval
          · case unit.live q =>
            cases q <;> simp at heval
            rcases heval with ⟨_, rfl⟩
            exact ⟨p, hlive⟩
          · case pairU64.live q =>
            cases q with
            | pair v0 v1 =>
              cases v0 <;> cases v1 <;> simp at heval
              rcases heval with ⟨_, rfl⟩
              exact ⟨p, hlive⟩
            | scalar _ => simp at heval
            | zst => simp at heval
    | field id' f =>
      simp only [evalOperand] at heval
      cases hty : getAt? tys id' with
      | none => simp [hty] at heval
      | some ty =>
        cases hsl : getAt? locals id' with
        | none => simp [hty, hsl] at heval
        | some sl =>
          cases ty <;> cases sl <;> simp [hty, hsl] at heval
          case pairU64.live q =>
            cases q <;> simp at heval
            case pair v0 v1 =>
              cases f with
              | fst =>
                cases v0 <;> simp at heval
                rcases heval with ⟨_, rfl⟩
                exact ⟨p, hlive⟩
              | snd =>
                cases v1 <;> simp at heval
                rcases heval with ⟨_, rfl⟩
                exact ⟨p, hlive⟩
  | move pl =>
    cases pl with
    | «local» id' =>
      simp only [evalOperand] at heval
      cases hty : getAt? tys id' with
      | none => simp [hty] at heval
      | some ty =>
        cases hsl : getAt? locals id' with
        | none => simp [hty, hsl] at heval
        | some sl =>
          cases sl with
          | dead => simp [hty, hsl] at heval
          | live payload =>
            simp only [hty, hsl] at heval
            split at heval
            · simp at heval
            · split at heval
              · case h_1 l1 hset =>
                simp at heval
                rcases heval with ⟨_, rfl⟩
                by_cases hEq : id = id'
                · subst hEq
                  rw [getAt?_setAt?_eq locals id (liveUninitSlot ty) l1 hset]
                  cases ty with
                  | u64 => exact ⟨.scalar none, rfl⟩
                  | unit => exact ⟨.zst, rfl⟩
                  | pairU64 => exact ⟨.pair none none, rfl⟩
                · rw [getAt?_setAt?_ne locals id' id (liveUninitSlot ty) l1 hset hEq]
                  exact ⟨p, hlive⟩
              · simp at heval
    | field id' f =>
      simp only [evalOperand] at heval
      cases hty : getAt? tys id' with
      | none => simp [hty] at heval
      | some ty =>
        cases hsl : getAt? locals id' with
        | none => simp [hty, hsl] at heval
        | some sl =>
          cases ty <;> cases sl <;> simp [hty, hsl] at heval
          case pairU64.live q =>
            cases q <;> simp at heval
            case pair v0 v1 =>
              split at heval
              · simp at heval
              · split at heval
                · case h_1 l1 hset =>
                  simp at heval
                  rcases heval with ⟨_, rfl⟩
                  by_cases hEq : id = id'
                  · subst hEq
                    rw [getAt?_setAt?_eq locals id _ l1 hset]
                    cases mode with
                    | localGranular => exact ⟨.pair none none, rfl⟩
                    | fieldGranular =>
                      cases f with
                      | fst => exact ⟨.pair none v1, rfl⟩
                      | snd => exact ⟨.pair v0 none, rfl⟩
                  · rw [getAt?_setAt?_ne locals id' id _ l1 hset hEq]
                    exact ⟨p, hlive⟩
                · simp at heval

private theorem stateMatches_update_at
    (env : SsaEnv) (tys : List MirTy)
    (locals locals' : List LocalSlot) (abs abs' : List AbsSlot)
    (id : Nat) (slNew : LocalSlot) (abNew : AbsSlot)
    (hm : stateMatches env tys locals abs)
    (hsetL : setAt? locals id slNew = some locals')
    (hsetA : setAt? abs id abNew = some abs')
    (hslotNew : ∀ ty, getAt? tys id = some ty → slotMatches env ty slNew abNew) :
    stateMatches env tys locals' abs' := by
  rcases hm with ⟨htl, hla, hslots⟩
  have hlenL := setAt?_length locals id slNew locals' hsetL
  have hlenA := setAt?_length abs id abNew abs' hsetA
  refine ⟨by omega, by omega, ?_⟩
  intro i ty sl ab hiTy hiLoc hiAbs
  by_cases hEq : i = id
  · subst hEq
    rw [getAt?_setAt?_eq locals i slNew locals' hsetL] at hiLoc
    rw [getAt?_setAt?_eq abs i abNew abs' hsetA] at hiAbs
    cases hiLoc; cases hiAbs
    exact hslotNew ty hiTy
  · rw [getAt?_setAt?_ne locals id i slNew locals' hsetL hEq] at hiLoc
    rw [getAt?_setAt?_ne abs id i abNew abs' hsetA hEq] at hiAbs
    exact hslots i ty sl ab hiTy hiLoc hiAbs

private theorem checkAbsOperand_some
    (env : SsaEnv) (tys : List MirTy) (locals : List LocalSlot) (abs abs' : List AbsSlot)
    (op : Operand) (sArg : SsaArg)
    (hm : stateMatches env tys locals abs)
    (hchk : checkAbsOperand tys abs op = some (some sArg, abs')) :
    ∃ v locals',
      evalOperand .fieldGranular tys locals op = .ok (.u64 v, locals') ∧
      evalSsaArg env sArg = some v ∧
      stateMatches env tys locals' abs' := by
  rcases hm with ⟨htl, hla, hslots⟩
  cases op with
  | constU64 k =>
    simp [checkAbsOperand] at hchk
    rcases hchk with ⟨rfl, rfl⟩
    exact ⟨k, locals, rfl, rfl, ⟨htl, hla, hslots⟩⟩
  | constUnit =>
    simp [checkAbsOperand] at hchk
  | copy pl =>
    cases pl with
    | «local» id =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          case u64.liveScalar opt =>
            cases opt with
            | none => simp at hchk
            | some r =>
              simp at hchk
              rcases hchk with ⟨rfl, rfl⟩
              have hiLt : id < locals.length := htl ▸ getAt?_lt_length tys id .u64 hty
              obtain ⟨sl, hsl⟩ := getAt?_some_of_lt locals id hiLt
              have hsm := hslots id .u64 sl (.liveScalar (some r)) hty hsl hab
              cases sl with
              | dead => exact False.elim hsm
              | live p =>
                cases p with
                | scalar ov =>
                  cases ov with
                  | none => exact False.elim hsm
                  | some v =>
                    exact ⟨v, locals, by simp [evalOperand, hty, hsl], hsm, ⟨htl, hla, hslots⟩⟩
                | zst => exact False.elim hsm
                | pair _ _ => exact False.elim hsm
    | field id f =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          case pairU64.livePair r0 r1 =>
            have hiLt : id < locals.length := htl ▸ getAt?_lt_length tys id .pairU64 hty
            obtain ⟨sl, hsl⟩ := getAt?_some_of_lt locals id hiLt
            have hsm := hslots id .pairU64 sl (.livePair r0 r1) hty hsl hab
            cases sl with
            | dead => exact False.elim hsm
            | live p =>
              cases p with
              | pair v0 v1 =>
                simp only [slotMatches] at hsm
                cases f with
                | fst =>
                  cases r0 with
                  | none => simp at hchk
                  | some r =>
                    simp at hchk
                    rcases hchk with ⟨rfl, rfl⟩
                    obtain ⟨x, hx0, hxr⟩ := hsm.1 r rfl
                    subst hx0
                    exact ⟨x, locals, by simp [evalOperand, hty, hsl], hxr, ⟨htl, hla, hslots⟩⟩
                | snd =>
                  cases r1 with
                  | none => simp at hchk
                  | some r =>
                    simp at hchk
                    rcases hchk with ⟨rfl, rfl⟩
                    obtain ⟨y, hy1, hyr⟩ := hsm.2 r rfl
                    subst hy1
                    exact ⟨y, locals, by simp [evalOperand, hty, hsl], hyr, ⟨htl, hla, hslots⟩⟩
              | scalar _ => simp [slotMatches] at hsm
              | zst => simp [slotMatches] at hsm
  | move pl =>
    cases pl with
    | «local» id =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          case u64.liveScalar opt =>
            cases opt with
            | none => simp at hchk
            | some r =>
              simp at hchk
              rcases hchk with ⟨hsetA, rfl⟩
              have hiLt : id < locals.length := htl ▸ getAt?_lt_length tys id .u64 hty
              obtain ⟨sl, hsl⟩ := getAt?_some_of_lt locals id hiLt
              have hsm := hslots id .u64 sl (.liveScalar (some r)) hty hsl hab
              cases sl with
              | dead => simp [slotMatches] at hsm
              | live p =>
                cases p with
                | scalar ov =>
                  cases ov with
                  | none => simp [slotMatches] at hsm
                  | some v =>
                    obtain ⟨locals', hsetL⟩ := setAt?_some_of_lt locals id (liveUninitSlot .u64) hiLt
                    refine ⟨v, locals', ?_, hsm, ?_⟩
                    · simp [evalOperand, hty, hsl, hsetL]
                    · exact stateMatches_update_at env tys locals locals' abs abs' id
                        (liveUninitSlot .u64) (.liveScalar none) ⟨htl, hla, hslots⟩ hsetL hsetA
                        (fun ty' hty' => by rw [hty] at hty'; cases hty'; trivial)
                | zst => simp [slotMatches] at hsm
                | pair _ _ => simp [slotMatches] at hsm
    | field id f =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          case pairU64.livePair r0 r1 =>
            have hiLt : id < locals.length := htl ▸ getAt?_lt_length tys id .pairU64 hty
            obtain ⟨sl, hsl⟩ := getAt?_some_of_lt locals id hiLt
            have hsm := hslots id .pairU64 sl (.livePair r0 r1) hty hsl hab
            cases sl with
            | dead => simp [slotMatches] at hsm
            | live p =>
              cases p with
              | pair v0 v1 =>
                simp only [slotMatches] at hsm
                cases f with
                | fst =>
                  cases r0 with
                  | none => simp at hchk
                  | some r =>
                    simp at hchk
                    rcases hchk with ⟨hsetA, rfl⟩
                    obtain ⟨x, hx0, hxr⟩ := hsm.1 r rfl
                    subst hx0
                    obtain ⟨locals', hsetL⟩ := setAt?_some_of_lt locals id (.live (.pair none v1)) hiLt
                    refine ⟨x, locals', ?_, hxr, ?_⟩
                    · simp [evalOperand, hty, hsl, hsetL]
                    · exact stateMatches_update_at env tys locals locals' abs abs' id
                        (.live (.pair none v1)) (.livePair none r1) ⟨htl, hla, hslots⟩ hsetL hsetA
                        (fun ty' hty' => by
                          rw [hty] at hty'; cases hty'
                          simp only [slotMatches]
                          exact ⟨(fun _ h => nomatch h), hsm.2⟩)
                | snd =>
                  cases r1 with
                  | none => simp at hchk
                  | some r =>
                    simp at hchk
                    rcases hchk with ⟨hsetA, rfl⟩
                    obtain ⟨y, hy1, hyr⟩ := hsm.2 r rfl
                    subst hy1
                    obtain ⟨locals', hsetL⟩ := setAt?_some_of_lt locals id (.live (.pair v0 none)) hiLt
                    refine ⟨y, locals', ?_, hyr, ?_⟩
                    · simp [evalOperand, hty, hsl, hsetL]
                    · exact stateMatches_update_at env tys locals locals' abs abs' id
                        (.live (.pair v0 none)) (.livePair r0 none) ⟨htl, hla, hslots⟩ hsetL hsetA
                        (fun ty' hty' => by
                          rw [hty] at hty'; cases hty'
                          simp only [slotMatches]
                          exact ⟨hsm.1, (fun _ h => nomatch h)⟩)
              | scalar _ => simp [slotMatches] at hsm
              | zst => simp [slotMatches] at hsm

private theorem checkAbsOperand_none
    (env : SsaEnv) (tys : List MirTy) (locals : List LocalSlot) (abs abs' : List AbsSlot)
    (op : Operand)
    (hm : stateMatches env tys locals abs)
    (hchk : checkAbsOperand tys abs op = some (none, abs')) :
    ∃ locals',
      evalOperand .fieldGranular tys locals op = .ok (.unit, locals') ∧
      stateMatches env tys locals' abs' := by
  rcases hm with ⟨htl, hla, hslots⟩
  cases op with
  | constU64 _ => simp [checkAbsOperand] at hchk
  | constUnit =>
    simp [checkAbsOperand] at hchk
    subst hchk
    exact ⟨locals, rfl, ⟨htl, hla, hslots⟩⟩
  | copy pl =>
    cases pl with
    | «local» id =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          · case u64.liveScalar opt => cases opt <;> simp at hchk
          · case unit.liveZst =>
            subst hchk
            have hiLt : id < locals.length := htl ▸ getAt?_lt_length tys id .unit hty
            obtain ⟨sl, hsl⟩ := getAt?_some_of_lt locals id hiLt
            have hsm := hslots id .unit sl .liveZst hty hsl hab
            cases sl with
            | dead => simp [slotMatches] at hsm
            | live p =>
              cases p with
              | zst => exact ⟨locals, by simp [evalOperand, hty, hsl], ⟨htl, hla, hslots⟩⟩
              | scalar _ => simp [slotMatches] at hsm
              | pair _ _ => simp [slotMatches] at hsm
    | field id f =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          case pairU64.livePair r0 r1 =>
            cases f <;> simp at hchk
  | move pl =>
    cases pl with
    | «local» id =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          · case u64.liveScalar opt =>
            cases opt <;> simp at hchk
          · case unit.liveZst =>
            subst hchk
            have hiLt : id < locals.length := htl ▸ getAt?_lt_length tys id .unit hty
            obtain ⟨sl, hsl⟩ := getAt?_some_of_lt locals id hiLt
            have hsm := hslots id .unit sl .liveZst hty hsl hab
            cases sl with
            | dead => simp [slotMatches] at hsm
            | live p =>
              cases p with
              | zst =>
                obtain ⟨locals', hsetL⟩ := setAt?_some_of_lt locals id (liveUninitSlot .unit) hiLt
                refine ⟨locals', by simp [evalOperand, hty, hsl, hsetL], ?_⟩
                have hlenL := setAt?_length locals id (liveUninitSlot .unit) locals' hsetL
                refine ⟨by omega, by omega, ?_⟩
                intro i ty' sl' ab' hiTy hiLoc hiAbs
                by_cases hEq : i = id
                · subst hEq
                  rw [hty] at hiTy; cases hiTy
                  rw [hab] at hiAbs; cases hiAbs
                  rw [getAt?_setAt?_eq locals i (liveUninitSlot .unit) locals' hsetL] at hiLoc
                  cases hiLoc
                  trivial
                · rw [getAt?_setAt?_ne locals id i (liveUninitSlot .unit) locals' hsetL hEq] at hiLoc
                  exact hslots i ty' sl' ab' hiTy hiLoc hiAbs
              | scalar _ => simp [slotMatches] at hsm
              | pair _ _ => simp [slotMatches] at hsm
    | field id f =>
      simp only [checkAbsOperand] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        cases hab : getAt? abs id with
        | none => simp [hty, hab] at hchk
        | some ab =>
          cases ty <;> cases ab <;> simp [hty, hab] at hchk
          case pairU64.livePair r0 r1 =>
            cases f with
            | fst => cases r0 <;> simp at hchk
            | snd => cases r1 <;> simp at hchk

private theorem checkBlockStmts_sound
    (tys : List MirTy) :
    ∀ (mstmts : List MirStmt) (sstmts : List SsaStmt)
      (abs absEnd : List AbsSlot) (locals : List LocalSlot) (env : SsaEnv),
      stateMatches env tys locals abs →
      checkBlockStmts tys abs mstmts sstmts = some absEnd →
      ∃ locals' env',
        stepMirStmts .fieldGranular tys locals mstmts = .ok locals' ∧
        stepSsaStmts env sstmts = some env' ∧
        stateMatches env' tys locals' absEnd := by
  intro mstmts
  induction mstmts with
  | nil =>
    intro sstmts abs absEnd locals env hm hchk
    cases sstmts with
    | nil =>
      simp [checkBlockStmts] at hchk
      subst hchk
      exact ⟨locals, env, rfl, rfl, hm⟩
    | cons _ _ =>
      simp [checkBlockStmts] at hchk
  | cons ms mrest ih =>
    intro sstmts abs absEnd locals env hm hchk
    cases ms with
    | storageLive id =>
      simp only [checkBlockStmts] at hchk
      cases hty : getAt? tys id with
      | none => simp [hty] at hchk
      | some ty =>
        have hiLt : id < locals.length := hm.1 ▸ getAt?_lt_length tys id ty hty
        obtain ⟨l1, hsetL⟩ := setAt?_some_of_lt locals id (liveUninitSlot ty) hiLt
        cases ty with
        | u64 =>
          simp only [hty, Option.bind_eq_some_iff] at hchk
          rcases hchk with ⟨a1, hsetA, hrest⟩
          have hm1 : stateMatches env tys l1 a1 :=
            stateMatches_update_at env tys locals l1 abs a1 id
              (liveUninitSlot .u64) (.liveScalar none) hm hsetL hsetA
              (fun ty' hty' => by rw [hty] at hty'; cases hty'; trivial)
          obtain ⟨l', env', hml', hse', hm'⟩ := ih sstmts a1 absEnd l1 env hm1 hrest
          exact ⟨l', env', by simp [stepMirStmts, stepMirStmt, hty, hsetL, hml'], hse', hm'⟩
        | unit =>
          simp only [hty, Option.bind_eq_some_iff] at hchk
          rcases hchk with ⟨a1, hsetA, hrest⟩
          have hm1 : stateMatches env tys l1 a1 :=
            stateMatches_update_at env tys locals l1 abs a1 id
              (liveUninitSlot .unit) .liveZst hm hsetL hsetA
              (fun ty' hty' => by rw [hty] at hty'; cases hty'; trivial)
          obtain ⟨l', env', hml', hse', hm'⟩ := ih sstmts a1 absEnd l1 env hm1 hrest
          exact ⟨l', env', by simp [stepMirStmts, stepMirStmt, hty, hsetL, hml'], hse', hm'⟩
        | pairU64 =>
          simp only [hty, Option.bind_eq_some_iff] at hchk
          rcases hchk with ⟨a1, hsetA, hrest⟩
          have hm1 : stateMatches env tys l1 a1 :=
            stateMatches_update_at env tys locals l1 abs a1 id
              (liveUninitSlot .pairU64) (.livePair none none) hm hsetL hsetA
              (fun ty' hty' => by
                rw [hty] at hty'; cases hty'
                simp only [liveUninitSlot, slotMatches]
                exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩)
          obtain ⟨l', env', hml', hse', hm'⟩ := ih sstmts a1 absEnd l1 env hm1 hrest
          exact ⟨l', env', by simp [stepMirStmts, stepMirStmt, hty, hsetL, hml'], hse', hm'⟩
    | storageDead id =>
      simp only [checkBlockStmts] at hchk
      cases hid0 : (id == 0) with
      | true => simp [hid0] at hchk
      | false =>
        simp only [hid0, Bool.false_eq_true, ↓reduceIte] at hchk
        cases hty : getAt? tys id with
        | none => simp [hty] at hchk
        | some ty =>
          simp only [hty, Option.bind_eq_some_iff] at hchk
          rcases hchk with ⟨a1, hsetA, hrest⟩
          have hiLt : id < locals.length := hm.1 ▸ getAt?_lt_length tys id ty hty
          obtain ⟨l1, hsetL⟩ := setAt?_some_of_lt locals id .dead hiLt
          have hm1 : stateMatches env tys l1 a1 :=
            stateMatches_update_at env tys locals l1 abs a1 id .dead .dead hm hsetL hsetA
              (fun _ _ => trivial)
          obtain ⟨l', env', hml', hse', hm'⟩ := ih sstmts a1 absEnd l1 env hm1 hrest
          exact ⟨l', env', by simp [stepMirStmts, stepMirStmt, hid0, hty, hsetL, hml'], hse', hm'⟩
    | assign dst rv =>
      cases dst with
      | «local» id =>
        cases rv with
        | use op =>
          simp only [checkBlockStmts] at hchk
          cases hty : getAt? tys id with
          | none => simp [hty] at hchk
          | some ty =>
            cases hab : getAt? abs id with
            | none => simp [hty, hab] at hchk
            | some ab =>
              cases ty <;> cases ab <;> simp [hty, hab] at hchk
              · case u64.liveScalar opt =>
                have hiLt0 : id < locals.length := hm.1 ▸ getAt?_lt_length tys id .u64 hty
                obtain ⟨sl0, hsl0⟩ := getAt?_some_of_lt locals id hiLt0
                have hsm0 := hm.2.2 id .u64 sl0 (.liveScalar opt) hty hsl0 hab
                have ⟨p0, hp0⟩ : ∃ p0, sl0 = .live p0 := by
                  cases sl0 with
                  | dead => cases opt <;> exact False.elim hsm0
                  | live p0 => exact ⟨p0, rfl⟩
                subst hp0
                cases hop : checkAbsOperand tys abs op with
                | none => simp [hop] at hchk
                | some res =>
                  rcases res with ⟨optArg, abs1⟩
                  cases optArg with
                  | none => simp [hop] at hchk
                  | some sArg =>
                    cases sstmts with
                    | nil => simp [hop] at hchk
                    | cons ss srest =>
                      cases ss with
                      | binOp _ _ _ _ => simp [hop] at hchk
                      | copy dstReg sArg' =>
                        simp only [hop] at hchk
                        split at hchk
                        · rename_i hargEq
                          subst hargEq
                          simp only [Option.bind_eq_some_iff] at hchk
                          rcases hchk with ⟨aCleared, hsetClr, hchk2⟩
                          cases hfresh : regNotInAbs dstReg aCleared with
                          | false => simp [hfresh] at hchk2
                          | true =>
                            simp only [hfresh, ↓reduceIte, Option.bind_eq_some_iff] at hchk2
                            rcases hchk2 with ⟨abs2, hsetAbs2, hrest⟩
                            obtain ⟨v, locals1, hevalOp, hevalArg, hm1⟩ :=
                              checkAbsOperand_some env tys locals abs abs1 op sArg hm hop
                            obtain ⟨p1, hp1⟩ :=
                              evalOperand_preserves_live .fieldGranular tys locals locals1 op (.u64 v) id p0 hevalOp hsl0
                            have hiLt1 : id < locals1.length := hm1.1 ▸ getAt?_lt_length tys id .u64 hty
                            obtain ⟨locals2, hsetL2⟩ := setAt?_some_of_lt locals1 id (.live (.scalar (some v))) hiLt1
                            have hlenL2 := setAt?_length locals1 id (.live (.scalar (some v))) locals2 hsetL2
                            have hlenClr := setAt?_length abs1 id (.liveScalar none) aCleared hsetClr
                            have hlenAbs2 := setAt?_length aCleared id (.liveScalar (some dstReg)) abs2 hsetAbs2
                            have hm2 : stateMatches (bindSsa env dstReg v) tys locals2 abs2 := by
                              refine ⟨by have := hm1.1; omega, by have := hm1.2.1; omega, ?_⟩
                              intro i ty' sl' ab' hiTy hiLoc hiAbs
                              by_cases hEq : i = id
                              · subst hEq
                                rw [hty] at hiTy; cases hiTy
                                rw [getAt?_setAt?_eq locals1 i (.live (.scalar (some v))) locals2 hsetL2] at hiLoc
                                rw [getAt?_setAt?_eq aCleared i (.liveScalar (some dstReg)) abs2 hsetAbs2] at hiAbs
                                cases hiLoc; cases hiAbs
                                exact bindSsa_eq env dstReg v
                              · rw [getAt?_setAt?_ne locals1 id i (.live (.scalar (some v))) locals2 hsetL2 hEq] at hiLoc
                                rw [getAt?_setAt?_ne aCleared id i (.liveScalar (some dstReg)) abs2 hsetAbs2 hEq] at hiAbs
                                have hiClr : getAt? aCleared i = some ab' := hiAbs
                                rw [getAt?_setAt?_ne abs1 id i (.liveScalar none) aCleared hsetClr hEq] at hiAbs
                                have hsmOld := hm1.2.2 i ty' sl' ab' hiTy hiLoc hiAbs
                                have hnm : absSlotNotMention dstReg ab' = true :=
                                  (List.all_eq_true.mp hfresh) ab' (getAt?_mem aCleared i ab' hiClr)
                                exact slotMatches_bindSsa_of_notMention env ty' sl' ab' dstReg v hsmOld hnm
                            obtain ⟨l', env', hml', hse', hm'⟩ := ih srest abs2 absEnd locals2 (bindSsa env dstReg v) hm2 hrest
                            refine ⟨l', env', ?_, ?_, hm'⟩
                            · simp [stepMirStmts, stepMirStmt, evalRvalue, hevalOp, writePlace, hty, hp1, hsetL2, hml']
                            · simp [stepSsaStmts, hevalArg, hse']
                        · simp at hchk
              · case unit.liveZst =>
                have hiLt0 : id < locals.length := hm.1 ▸ getAt?_lt_length tys id .unit hty
                obtain ⟨sl0, hsl0⟩ := getAt?_some_of_lt locals id hiLt0
                have hsm0 := hm.2.2 id .unit sl0 .liveZst hty hsl0 hab
                have ⟨p0, hp0⟩ : ∃ p0, sl0 = .live p0 := by
                  cases sl0 with
                  | dead => exact False.elim hsm0
                  | live p0 => exact ⟨p0, rfl⟩
                subst hp0
                cases hop : checkAbsOperand tys abs op with
                | none => simp [hop] at hchk
                | some res =>
                  rcases res with ⟨optArg, abs1⟩
                  cases optArg with
                  | some _ => simp [hop] at hchk
                  | none =>
                    simp only [hop] at hchk
                    obtain ⟨locals1, hevalOp, hm1⟩ := checkAbsOperand_none env tys locals abs abs1 op hm hop
                    obtain ⟨p1, hp1⟩ :=
                      evalOperand_preserves_live .fieldGranular tys locals locals1 op .unit id p0 hevalOp hsl0
                    have hiLt1 : id < locals1.length := hm1.1 ▸ getAt?_lt_length tys id .unit hty
                    obtain ⟨locals2, hsetL2⟩ := setAt?_some_of_lt locals1 id (.live .zst) hiLt1
                    have hlenL2 := setAt?_length locals1 id (.live .zst) locals2 hsetL2
                    have hm2 : stateMatches env tys locals2 abs1 := by
                      refine ⟨by have := hm1.1; omega, by have := hm1.2.1; omega, ?_⟩
                      intro i ty' sl' ab' hiTy hiLoc hiAbs
                      by_cases hEq : i = id
                      · subst hEq
                        rw [hty] at hiTy; cases hiTy
                        rw [getAt?_setAt?_eq locals1 i (.live .zst) locals2 hsetL2] at hiLoc
                        cases hiLoc
                        have hsm1 := hm1.2.2 i .unit (.live p1) ab' hty hp1 hiAbs
                        cases ab' with
                        | liveZst => trivial
                        | dead => cases p1 <;> simp [slotMatches] at hsm1
                        | liveScalar _ => cases p1 <;> simp [slotMatches] at hsm1
                        | livePair _ _ => cases p1 <;> simp [slotMatches] at hsm1
                      · rw [getAt?_setAt?_ne locals1 id i (.live .zst) locals2 hsetL2 hEq] at hiLoc
                        exact hm1.2.2 i ty' sl' ab' hiTy hiLoc hiAbs
                    obtain ⟨l', env', hml', hse', hm'⟩ := ih sstmts abs1 absEnd locals2 env hm2 hchk
                    refine ⟨l', env', ?_, hse', hm'⟩
                    simp [stepMirStmts, stepMirStmt, evalRvalue, hevalOp, writePlace, hty, hp1, hsetL2, hml']
        | binaryOp bop lhs rhs =>
          cases sstmts with
          | nil => simp [checkBlockStmts] at hchk
          | cons ss srest =>
            cases ss with
            | copy _ _ => simp [checkBlockStmts] at hchk
            | binOp dstReg bop' sL sR =>
              simp only [checkBlockStmts] at hchk
              cases hbopEq : (bop != bop') with
              | true => simp [hbopEq] at hchk
              | false =>
                have hbop : bop = bop' := by simpa using hbopEq
                subst hbop
                simp only [hbopEq, Bool.false_eq_true, ↓reduceIte] at hchk
                cases hty : getAt? tys id with
                | none => simp [hty] at hchk
                | some ty =>
                  cases hab : getAt? abs id with
                  | none => simp [hty, hab] at hchk
                  | some ab =>
                    cases ty <;> cases ab <;> simp [hty, hab] at hchk
                    case u64.liveScalar opt =>
                      have hiLt0 : id < locals.length := hm.1 ▸ getAt?_lt_length tys id .u64 hty
                      obtain ⟨sl0, hsl0⟩ := getAt?_some_of_lt locals id hiLt0
                      have hsm0 := hm.2.2 id .u64 sl0 (.liveScalar opt) hty hsl0 hab
                      have ⟨p0, hp0⟩ : ∃ p0, sl0 = .live p0 := by
                        cases sl0 with
                        | dead => cases opt <;> exact False.elim hsm0
                        | live p0 => exact ⟨p0, rfl⟩
                      subst hp0
                      cases hopL : checkAbsOperand tys abs lhs with
                      | none => simp [hopL] at hchk
                      | some resL =>
                        rcases resL with ⟨optL, abs1⟩
                        cases optL with
                        | none => simp [hopL] at hchk
                        | some aL =>
                          simp only [hopL] at hchk
                          cases hopR : checkAbsOperand tys abs1 rhs with
                          | none => simp [hopR] at hchk
                          | some resR =>
                            rcases resR with ⟨optR, abs2⟩
                            cases optR with
                            | none => simp [hopR] at hchk
                            | some aR =>
                              simp only [hopR] at hchk
                              split at hchk
                              · rename_i hcond
                                rcases hcond with ⟨rfl, rfl⟩
                                simp only [Option.bind_eq_some_iff] at hchk
                                rcases hchk with ⟨aCleared, hsetClr, hchk2⟩
                                cases hfresh : regNotInAbs dstReg aCleared with
                                | false => simp [hfresh] at hchk2
                                | true =>
                                  simp only [hfresh, ↓reduceIte, Option.bind_eq_some_iff] at hchk2
                                  rcases hchk2 with ⟨abs3, hsetAbs3, hrest⟩
                                  obtain ⟨vL, locals1, hevalL, hargL, hm1⟩ :=
                                    checkAbsOperand_some env tys locals abs abs1 lhs aL hm hopL
                                  obtain ⟨vR, locals2, hevalR, hargR, hm2⟩ :=
                                    checkAbsOperand_some env tys locals1 abs1 abs2 rhs aR hm1 hopR
                                  obtain ⟨p1, hp1⟩ :=
                                    evalOperand_preserves_live .fieldGranular tys locals locals1 lhs (.u64 vL) id p0 hevalL hsl0
                                  obtain ⟨p2, hp2⟩ :=
                                    evalOperand_preserves_live .fieldGranular tys locals1 locals2 rhs (.u64 vR) id p1 hevalR hp1
                                  have hiLt2 : id < locals2.length := hm2.1 ▸ getAt?_lt_length tys id .u64 hty
                                  let vRes := evalBinOp bop vL vR
                                  obtain ⟨locals3, hsetL3⟩ := setAt?_some_of_lt locals2 id (.live (.scalar (some vRes))) hiLt2
                                  have hlenL3 := setAt?_length locals2 id (.live (.scalar (some vRes))) locals3 hsetL3
                                  have hlenClr := setAt?_length abs2 id (.liveScalar none) aCleared hsetClr
                                  have hlenAbs3 := setAt?_length aCleared id (.liveScalar (some dstReg)) abs3 hsetAbs3
                                  have hm3 : stateMatches (bindSsa env dstReg vRes) tys locals3 abs3 := by
                                    refine ⟨by have := hm2.1; omega, by have := hm2.2.1; omega, ?_⟩
                                    intro i ty' sl' ab' hiTy hiLoc hiAbs
                                    by_cases hEq : i = id
                                    · subst hEq
                                      rw [hty] at hiTy; cases hiTy
                                      rw [getAt?_setAt?_eq locals2 i (.live (.scalar (some vRes))) locals3 hsetL3] at hiLoc
                                      rw [getAt?_setAt?_eq aCleared i (.liveScalar (some dstReg)) abs3 hsetAbs3] at hiAbs
                                      cases hiLoc; cases hiAbs
                                      exact bindSsa_eq env dstReg vRes
                                    · rw [getAt?_setAt?_ne locals2 id i (.live (.scalar (some vRes))) locals3 hsetL3 hEq] at hiLoc
                                      rw [getAt?_setAt?_ne aCleared id i (.liveScalar (some dstReg)) abs3 hsetAbs3 hEq] at hiAbs
                                      have hiClr : getAt? aCleared i = some ab' := hiAbs
                                      rw [getAt?_setAt?_ne abs2 id i (.liveScalar none) aCleared hsetClr hEq] at hiAbs
                                      have hsmOld := hm2.2.2 i ty' sl' ab' hiTy hiLoc hiAbs
                                      have hnm : absSlotNotMention dstReg ab' = true :=
                                        (List.all_eq_true.mp hfresh) ab' (getAt?_mem aCleared i ab' hiClr)
                                      exact slotMatches_bindSsa_of_notMention env ty' sl' ab' dstReg vRes hsmOld hnm
                                  obtain ⟨l', env', hml', hse', hm'⟩ := ih srest abs3 absEnd locals3 (bindSsa env dstReg vRes) hm3 hrest
                                  refine ⟨l', env', ?_, ?_, hm'⟩
                                  · simp [stepMirStmts, stepMirStmt, evalRvalue, hevalL, hevalR, writePlace, hty, hp2, hsetL3, hml', vRes]
                                  · simp [stepSsaStmts, hargL, hargR, hse', vRes]
                              · simp at hchk
        | mkPair op0 op1 =>
          cases sstmts with
          | nil => simp [checkBlockStmts] at hchk
          | cons ss0 srest0 =>
            cases ss0 with
            | binOp _ _ _ _ => simp [checkBlockStmts] at hchk
            | copy r0 a0' =>
              cases srest0 with
              | nil => simp [checkBlockStmts] at hchk
              | cons ss1 srest =>
                cases ss1 with
                | binOp _ _ _ _ => simp [checkBlockStmts] at hchk
                | copy r1 a1' =>
                  simp only [checkBlockStmts] at hchk
                  cases hty : getAt? tys id with
                  | none => simp [hty] at hchk
                  | some ty =>
                    cases hab : getAt? abs id with
                    | none => simp [hty, hab] at hchk
                    | some ab =>
                      cases ty <;> cases ab <;> simp [hty, hab] at hchk
                      case pairU64.livePair sr0 sr1 =>
                        have hiLt0 : id < locals.length := hm.1 ▸ getAt?_lt_length tys id .pairU64 hty
                        obtain ⟨sl0, hsl0⟩ := getAt?_some_of_lt locals id hiLt0
                        have hsm0 := hm.2.2 id .pairU64 sl0 (.livePair sr0 sr1) hty hsl0 hab
                        have ⟨p0, hp0⟩ : ∃ p0, sl0 = .live p0 := by
                          cases sl0 with
                          | dead => exact False.elim hsm0
                          | live p0 => exact ⟨p0, rfl⟩
                        subst hp0
                        cases hop0 : checkAbsOperand tys abs op0 with
                        | none => simp [hop0] at hchk
                        | some res0 =>
                          rcases res0 with ⟨opt0, abs1⟩
                          cases opt0 with
                          | none => simp [hop0] at hchk
                          | some a0 =>
                            simp only [hop0] at hchk
                            cases hop1 : checkAbsOperand tys abs1 op1 with
                            | none => simp [hop1] at hchk
                            | some res1 =>
                              rcases res1 with ⟨opt1, abs2⟩
                              cases opt1 with
                              | none => simp [hop1] at hchk
                              | some a1 =>
                                simp only [hop1] at hchk
                                split at hchk
                                · rename_i hcond
                                  rcases hcond with ⟨⟨⟨rfl, rfl⟩, hr01⟩, ha1ne⟩
                                  simp only [Option.bind_eq_some_iff] at hchk
                                  rcases hchk with ⟨aCleared, hsetClr, hchk2⟩
                                  split at hchk2
                                  · rename_i hfresh
                                    rcases hfresh with ⟨hfresh0, hfresh1⟩
                                    simp only [Option.bind_eq_some_iff] at hchk2
                                    rcases hchk2 with ⟨abs3, hsetAbs3, hrest⟩
                                    obtain ⟨v0, locals1, heval0, harg0, hm1⟩ :=
                                      checkAbsOperand_some env tys locals abs abs1 op0 a0 hm hop0
                                    obtain ⟨v1, locals2, heval1, harg1, hm2⟩ :=
                                      checkAbsOperand_some env tys locals1 abs1 abs2 op1 a1 hm1 hop1
                                    obtain ⟨p1, hp1⟩ :=
                                      evalOperand_preserves_live .fieldGranular tys locals locals1 op0 (.u64 v0) id p0 heval0 hsl0
                                    obtain ⟨p2, hp2⟩ :=
                                      evalOperand_preserves_live .fieldGranular tys locals1 locals2 op1 (.u64 v1) id p1 heval1 hp1
                                    have hiLt2 : id < locals2.length := hm2.1 ▸ getAt?_lt_length tys id .pairU64 hty
                                    obtain ⟨locals3, hsetL3⟩ :=
                                      setAt?_some_of_lt locals2 id (.live (.pair (some v0) (some v1))) hiLt2
                                    have hlenL3 := setAt?_length locals2 id (.live (.pair (some v0) (some v1))) locals3 hsetL3
                                    have hlenClr := setAt?_length abs2 id (.livePair none none) aCleared hsetClr
                                    have hlenAbs3 := setAt?_length aCleared id (.livePair (some r0) (some r1)) abs3 hsetAbs3
                                    let env1 := bindSsa env r0 v0
                                    let env2 := bindSsa env1 r1 v1
                                    have harg1' : evalSsaArg env1 a1 = some v1 := by
                                      cases a1 with
                                      | constU64 k => exact harg1
                                      | reg rx =>
                                        have hrx : rx ≠ r0 := fun heq => ha1ne (congrArg SsaArg.reg heq)
                                        simp only [evalSsaArg, env1] at harg1 ⊢
                                        rw [bindSsa_ne env r0 rx v0 hrx]
                                        exact harg1
                                    have hm3 : stateMatches env2 tys locals3 abs3 := by
                                      refine ⟨by have := hm2.1; omega, by have := hm2.2.1; omega, ?_⟩
                                      intro i ty' sl' ab' hiTy hiLoc hiAbs
                                      by_cases hEq : i = id
                                      · subst hEq
                                        rw [hty] at hiTy; cases hiTy
                                        rw [getAt?_setAt?_eq locals2 i (.live (.pair (some v0) (some v1))) locals3 hsetL3] at hiLoc
                                        rw [getAt?_setAt?_eq aCleared i (.livePair (some r0) (some r1)) abs3 hsetAbs3] at hiAbs
                                        cases hiLoc; cases hiAbs
                                        simp only [slotMatches]
                                        refine ⟨?_, ?_⟩
                                        · intro reg hreg
                                          cases hreg
                                          refine ⟨v0, rfl, ?_⟩
                                          simp only [env2, env1]
                                          rw [bindSsa_ne _ r1 r0 v1 hr01, bindSsa_eq]
                                        · intro reg hreg
                                          cases hreg
                                          exact ⟨v1, rfl, bindSsa_eq env1 r1 v1⟩
                                      · rw [getAt?_setAt?_ne locals2 id i (.live (.pair (some v0) (some v1))) locals3 hsetL3 hEq] at hiLoc
                                        rw [getAt?_setAt?_ne aCleared id i (.livePair (some r0) (some r1)) abs3 hsetAbs3 hEq] at hiAbs
                                        have hiClr : getAt? aCleared i = some ab' := hiAbs
                                        rw [getAt?_setAt?_ne abs2 id i (.livePair none none) aCleared hsetClr hEq] at hiAbs
                                        have hsmOld := hm2.2.2 i ty' sl' ab' hiTy hiLoc hiAbs
                                        have hnm0 : absSlotNotMention r0 ab' = true :=
                                          (List.all_eq_true.mp hfresh0) ab' (getAt?_mem aCleared i ab' hiClr)
                                        have hnm1 : absSlotNotMention r1 ab' = true :=
                                          (List.all_eq_true.mp hfresh1) ab' (getAt?_mem aCleared i ab' hiClr)
                                        have hsmMid := slotMatches_bindSsa_of_notMention env ty' sl' ab' r0 v0 hsmOld hnm0
                                        exact slotMatches_bindSsa_of_notMention env1 ty' sl' ab' r1 v1 hsmMid hnm1
                                    obtain ⟨l', env', hml', hse', hm'⟩ := ih srest abs3 absEnd locals3 env2 hm3 hrest
                                    refine ⟨l', env', ?_, ?_, hm'⟩
                                    · simp [stepMirStmts, stepMirStmt, evalRvalue, heval0, heval1, writePlace, hty, hp2, hsetL3, hml']
                                    · simp [stepSsaStmts, harg0, harg1', env1, env2, hse']
                                  · simp at hchk2
                                · simp at hchk
      | field id f =>
        cases rv with
        | binaryOp _ _ _ => simp [checkBlockStmts] at hchk
        | mkPair _ _ => simp [checkBlockStmts] at hchk
        | use op =>
          cases sstmts with
          | nil => simp [checkBlockStmts] at hchk
          | cons ss srest =>
            cases ss with
            | binOp _ _ _ _ => simp [checkBlockStmts] at hchk
            | copy dstReg sArg' =>
              simp only [checkBlockStmts] at hchk
              cases hty : getAt? tys id with
              | none => simp [hty] at hchk
              | some ty =>
                cases hab : getAt? abs id with
                | none => simp [hty, hab] at hchk
                | some ab =>
                  cases ty <;> cases ab <;> simp [hty, hab] at hchk
                  case pairU64.livePair sr0 sr1 =>
                    cases hop : checkAbsOperand tys abs op with
                    | none => simp [hop] at hchk
                    | some res =>
                      rcases res with ⟨optArg, abs1⟩
                      cases optArg with
                      | none => simp [hop] at hchk
                      | some sArg =>
                        simp only [hop] at hchk
                        split at hchk
                        · rename_i hargEq
                          subst hargEq
                          cases hab1 : getAt? abs1 id with
                          | none => simp [hab1] at hchk
                          | some ab1 =>
                            cases ab1 <;> simp [hab1] at hchk
                            case livePair r0' r1' =>
                              cases f with
                              | fst =>
                                simp only [Option.bind_eq_some_iff] at hchk
                                rcases hchk with ⟨aCleared, hsetClr, hchk2⟩
                                cases hfresh : regNotInAbs dstReg aCleared with
                                | false => simp [hfresh] at hchk2
                                | true =>
                                  simp only [hfresh, ↓reduceIte, Option.bind_eq_some_iff] at hchk2
                                  rcases hchk2 with ⟨abs2, hsetAbs2, hrest⟩
                                  obtain ⟨v, locals1, hevalOp, hevalArg, hm1⟩ :=
                                    checkAbsOperand_some env tys locals abs abs1 op sArg hm hop
                                  have hiLt1 : id < locals1.length := hm1.1 ▸ getAt?_lt_length tys id .pairU64 hty
                                  obtain ⟨sl1, hsl1⟩ := getAt?_some_of_lt locals1 id hiLt1
                                  have hsm1 := hm1.2.2 id .pairU64 sl1 (.livePair r0' r1') hty hsl1 hab1
                                  cases sl1 with
                                  | dead => simp [slotMatches] at hsm1
                                  | live p1 =>
                                    cases p1 with
                                    | scalar _ => simp [slotMatches] at hsm1
                                    | zst => simp [slotMatches] at hsm1
                                    | pair v0 v1 =>
                                      simp only [slotMatches] at hsm1
                                      obtain ⟨locals2, hsetL2⟩ := setAt?_some_of_lt locals1 id (.live (.pair (some v) v1)) hiLt1
                                      have hlenL2 := setAt?_length locals1 id (.live (.pair (some v) v1)) locals2 hsetL2
                                      have hlenClr := setAt?_length abs1 id (.livePair none r1') aCleared hsetClr
                                      have hlenAbs2 := setAt?_length aCleared id (.livePair (some dstReg) r1') abs2 hsetAbs2
                                      have hnmClr : absSlotNotMention dstReg (.livePair none r1') = true :=
                                        (List.all_eq_true.mp hfresh) _
                                          (getAt?_mem aCleared id _ (getAt?_setAt?_eq abs1 id _ aCleared hsetClr))
                                      have hm2 : stateMatches (bindSsa env dstReg v) tys locals2 abs2 := by
                                        refine ⟨by have := hm1.1; omega, by have := hm1.2.1; omega, ?_⟩
                                        intro i ty' sl' ab' hiTy hiLoc hiAbs
                                        by_cases hEq : i = id
                                        · subst hEq
                                          rw [hty] at hiTy; cases hiTy
                                          rw [getAt?_setAt?_eq locals1 i _ locals2 hsetL2] at hiLoc
                                          rw [getAt?_setAt?_eq aCleared i _ abs2 hsetAbs2] at hiAbs
                                          cases hiLoc; cases hiAbs
                                          simp only [slotMatches]
                                          simp only [absSlotNotMention, Bool.and_eq_true, bne_iff_ne] at hnmClr
                                          refine ⟨?_, ?_⟩
                                          · intro reg hreg; cases hreg; exact ⟨v, rfl, bindSsa_eq env dstReg v⟩
                                          · intro reg hreg
                                            have hne : reg ≠ dstReg := fun heq => hnmClr.2 (heq ▸ hreg)
                                            obtain ⟨y, hy1, hyr⟩ := hsm1.2 reg hreg
                                            exact ⟨y, hy1, by rw [bindSsa_ne env dstReg reg v hne]; exact hyr⟩
                                        · rw [getAt?_setAt?_ne locals1 id i _ locals2 hsetL2 hEq] at hiLoc
                                          rw [getAt?_setAt?_ne aCleared id i _ abs2 hsetAbs2 hEq] at hiAbs
                                          have hiClr : getAt? aCleared i = some ab' := hiAbs
                                          rw [getAt?_setAt?_ne abs1 id i _ aCleared hsetClr hEq] at hiAbs
                                          have hsmOld := hm1.2.2 i ty' sl' ab' hiTy hiLoc hiAbs
                                          have hnm : absSlotNotMention dstReg ab' = true :=
                                            (List.all_eq_true.mp hfresh) ab' (getAt?_mem aCleared i ab' hiClr)
                                          exact slotMatches_bindSsa_of_notMention env ty' sl' ab' dstReg v hsmOld hnm
                                      obtain ⟨l', env', hml', hse', hm'⟩ := ih srest abs2 absEnd locals2 (bindSsa env dstReg v) hm2 hrest
                                      refine ⟨l', env', ?_, ?_, hm'⟩
                                      · simp [stepMirStmts, stepMirStmt, evalRvalue, hevalOp, writePlace, hty, hsl1, hsetL2, hml']
                                      · simp [stepSsaStmts, hevalArg, hse']
                              | snd =>
                                simp only [Option.bind_eq_some_iff] at hchk
                                rcases hchk with ⟨aCleared, hsetClr, hchk2⟩
                                cases hfresh : regNotInAbs dstReg aCleared with
                                | false => simp [hfresh] at hchk2
                                | true =>
                                  simp only [hfresh, ↓reduceIte, Option.bind_eq_some_iff] at hchk2
                                  rcases hchk2 with ⟨abs2, hsetAbs2, hrest⟩
                                  obtain ⟨v, locals1, hevalOp, hevalArg, hm1⟩ :=
                                    checkAbsOperand_some env tys locals abs abs1 op sArg hm hop
                                  have hiLt1 : id < locals1.length := hm1.1 ▸ getAt?_lt_length tys id .pairU64 hty
                                  obtain ⟨sl1, hsl1⟩ := getAt?_some_of_lt locals1 id hiLt1
                                  have hsm1 := hm1.2.2 id .pairU64 sl1 (.livePair r0' r1') hty hsl1 hab1
                                  cases sl1 with
                                  | dead => simp [slotMatches] at hsm1
                                  | live p1 =>
                                    cases p1 with
                                    | scalar _ => simp [slotMatches] at hsm1
                                    | zst => simp [slotMatches] at hsm1
                                    | pair v0 v1 =>
                                      simp only [slotMatches] at hsm1
                                      obtain ⟨locals2, hsetL2⟩ := setAt?_some_of_lt locals1 id (.live (.pair v0 (some v))) hiLt1
                                      have hlenL2 := setAt?_length locals1 id (.live (.pair v0 (some v))) locals2 hsetL2
                                      have hlenClr := setAt?_length abs1 id (.livePair r0' none) aCleared hsetClr
                                      have hlenAbs2 := setAt?_length aCleared id (.livePair r0' (some dstReg)) abs2 hsetAbs2
                                      have hnmClr : absSlotNotMention dstReg (.livePair r0' none) = true :=
                                        (List.all_eq_true.mp hfresh) _
                                          (getAt?_mem aCleared id _ (getAt?_setAt?_eq abs1 id _ aCleared hsetClr))
                                      have hm2 : stateMatches (bindSsa env dstReg v) tys locals2 abs2 := by
                                        refine ⟨by have := hm1.1; omega, by have := hm1.2.1; omega, ?_⟩
                                        intro i ty' sl' ab' hiTy hiLoc hiAbs
                                        by_cases hEq : i = id
                                        · subst hEq
                                          rw [hty] at hiTy; cases hiTy
                                          rw [getAt?_setAt?_eq locals1 i _ locals2 hsetL2] at hiLoc
                                          rw [getAt?_setAt?_eq aCleared i _ abs2 hsetAbs2] at hiAbs
                                          cases hiLoc; cases hiAbs
                                          simp only [slotMatches]
                                          simp only [absSlotNotMention, Bool.and_eq_true, bne_iff_ne] at hnmClr
                                          refine ⟨?_, ?_⟩
                                          · intro reg hreg
                                            have hne : reg ≠ dstReg := fun heq => hnmClr.1 (heq ▸ hreg)
                                            obtain ⟨x, hx0, hxr⟩ := hsm1.1 reg hreg
                                            exact ⟨x, hx0, by rw [bindSsa_ne env dstReg reg v hne]; exact hxr⟩
                                          · intro reg hreg; cases hreg; exact ⟨v, rfl, bindSsa_eq env dstReg v⟩
                                        · rw [getAt?_setAt?_ne locals1 id i _ locals2 hsetL2 hEq] at hiLoc
                                          rw [getAt?_setAt?_ne aCleared id i _ abs2 hsetAbs2 hEq] at hiAbs
                                          have hiClr : getAt? aCleared i = some ab' := hiAbs
                                          rw [getAt?_setAt?_ne abs1 id i _ aCleared hsetClr hEq] at hiAbs
                                          have hsmOld := hm1.2.2 i ty' sl' ab' hiTy hiLoc hiAbs
                                          have hnm : absSlotNotMention dstReg ab' = true :=
                                            (List.all_eq_true.mp hfresh) ab' (getAt?_mem aCleared i ab' hiClr)
                                          exact slotMatches_bindSsa_of_notMention env ty' sl' ab' dstReg v hsmOld hnm
                                      obtain ⟨l', env', hml', hse', hm'⟩ := ih srest abs2 absEnd locals2 (bindSsa env dstReg v) hm2 hrest
                                      refine ⟨l', env', ?_, ?_, hm'⟩
                                      · simp [stepMirStmts, stepMirStmt, evalRvalue, hevalOp, writePlace, hty, hsl1, hsetL2, hml']
                                      · simp [stepSsaStmts, hevalArg, hse']
                        · simp at hchk

private theorem bindSsaParams_exists (evalEnv : SsaEnv) :
    ∀ (params : List Nat) (args : List SsaArg) (baseEnv : SsaEnv),
      params.length = args.length →
      (∀ a, a ∈ args → ∃ v, evalSsaArg evalEnv a = some v) →
      ∃ env', bindSsaParams baseEnv evalEnv params args = some env'
  | [], [], baseEnv, _, _ => ⟨baseEnv, rfl⟩
  | _ :: _, [], _, hlen, _ => nomatch hlen
  | [], _ :: _, _, hlen, _ => nomatch hlen
  | r :: rs, a :: as, baseEnv, hlen, hargs => by
    obtain ⟨v, hv⟩ := hargs a (List.Mem.head _)
    have hlen' : rs.length = as.length := Nat.succ.inj hlen
    have hargs' : ∀ a', a' ∈ as → ∃ v', evalSsaArg evalEnv a' = some v' :=
      fun a' ha' => hargs a' (List.Mem.tail _ ha')
    obtain ⟨env', henv'⟩ := bindSsaParams_exists evalEnv rs as (bindSsa baseEnv r v) hlen' hargs'
    exact ⟨env', by simp [bindSsaParams, hv, henv']⟩

private theorem bindSsaParams_not_mem (evalEnv : SsaEnv) (rd : Nat) :
    ∀ (params : List Nat) (args : List SsaArg) (baseEnv env' : SsaEnv),
      bindSsaParams baseEnv evalEnv params args = some env' →
      rd ∉ params →
      env' rd = baseEnv rd
  | [], [], baseEnv, env', hbind, _ => by
    simp [bindSsaParams] at hbind
    subst hbind; rfl
  | _ :: _, [], _, _, hbind, _ => by simp [bindSsaParams] at hbind
  | [], _ :: _, _, _, hbind, _ => by simp [bindSsaParams] at hbind
  | r :: rs, a :: as, baseEnv, env', hbind, hnotmem => by
    simp only [bindSsaParams] at hbind
    cases hv : evalSsaArg evalEnv a with
    | none => simp [hv] at hbind
    | some v =>
      simp only [hv] at hbind
      have hne : rd ≠ r := fun heq => hnotmem (heq ▸ List.Mem.head _)
      have hnotrs : rd ∉ rs := fun hmem => hnotmem (List.Mem.tail _ hmem)
      rw [bindSsaParams_not_mem evalEnv rd rs as (bindSsa baseEnv r v) env' hbind hnotrs]
      exact bindSsa_ne baseEnv r rd v hne

private theorem bindSsaParams_find?_some (evalEnv : SsaEnv) (rd : Nat) :
    ∀ (params : List Nat) (args : List SsaArg) (baseEnv env' : SsaEnv) (rd' : Nat) (arg : SsaArg),
      bindSsaParams baseEnv evalEnv params args = some env' →
      params.Nodup →
      (params.zip args).find? (fun p => p.1 == rd) = some (rd', arg) →
      env' rd = evalSsaArg evalEnv arg
  | [], _, _, _, _, _, _, _, hfind => by simp at hfind
  | _, [], _, _, _, _, _, _, hfind => by simp at hfind
  | r :: rs, a :: as, baseEnv, env', rd', arg, hbind, hnodup, hfind => by
    simp only [bindSsaParams] at hbind
    cases hv : evalSsaArg evalEnv a with
    | none => simp [hv] at hbind
    | some v =>
      simp only [hv] at hbind
      have ⟨hr_not_rs, hnodup_rs⟩ := List.nodup_cons.mp hnodup
      simp only [List.zip_cons_cons, List.find?_cons] at hfind
      cases heq : (r == rd) with
      | true =>
        have hrrd : r = rd := eq_of_beq heq
        subst hrrd
        simp only [heq] at hfind
        cases hfind
        rw [bindSsaParams_not_mem evalEnv r rs as (bindSsa baseEnv r v) env' hbind hr_not_rs]
        rw [bindSsa_eq, hv]
      | false =>
        simp only [heq] at hfind
        exact bindSsaParams_find?_some evalEnv rd rs as (bindSsa baseEnv r v) env' rd' arg hbind hnodup_rs hfind

private theorem checkEdge_regOk_sound
    (env1 env2 : SsaEnv) (tgtParams : List Nat) (edgeArgs : List SsaArg)
    (hbind : bindSsaParams env1 env1 tgtParams edgeArgs = some env2)
    (hnodup : tgtParams.Nodup)
    (srcOpt : Option Nat) (rd : Nat) (valOpt : Option UInt64)
    (hsrc : ∀ r, srcOpt = some r → ∃ x, valOpt = some x ∧ env1 r = some x)
    (hregOk :
      (match (tgtParams.zip edgeArgs).find? (fun p => p.1 == rd) with
       | some (_, .reg rs) => srcOpt == some rs
       | some (_, .constU64 _) => false
       | none => (srcOpt == some rd) && !(tgtParams.contains rd)) = true) :
    ∃ x, valOpt = some x ∧ env2 rd = some x := by
  cases hfind : (tgtParams.zip edgeArgs).find? (fun p => p.1 == rd) with
  | none =>
    simp only [hfind, Bool.and_eq_true, beq_iff_eq] at hregOk
    rcases hregOk with ⟨hsrcEq, hnotCont⟩
    have hnotMem : rd ∉ tgtParams := by simpa using hnotCont
    obtain ⟨x, hxVal, hxEnv1⟩ := hsrc rd hsrcEq
    exact ⟨x, hxVal, by rw [bindSsaParams_not_mem env1 rd tgtParams edgeArgs env1 env2 hbind hnotMem]; exact hxEnv1⟩
  | some p =>
    rcases p with ⟨rd', arg⟩
    cases arg with
    | constU64 _ =>
      simp [hfind] at hregOk
    | reg rs =>
      simp only [hfind, beq_iff_eq] at hregOk
      obtain ⟨x, hxVal, hxEnv1⟩ := hsrc rs hregOk
      have henv2 : env2 rd = evalSsaArg env1 (.reg rs) :=
        bindSsaParams_find?_some env1 rd tgtParams edgeArgs env1 env2 rd' (.reg rs) hbind hnodup hfind
      exact ⟨x, hxVal, by rw [henv2]; exact hxEnv1⟩

private theorem checkEdge_sound
    (env1 : SsaEnv) (tys : List MirTy) (locals : List LocalSlot)
    (absEnd tgtAbs : List AbsSlot) (tgtParams : List Nat) (edgeArgs : List SsaArg)
    (hm : stateMatches env1 tys locals absEnd)
    (hedge : checkEdge absEnd tgtAbs tgtParams edgeArgs = true) :
    ∃ env2, bindSsaParams env1 env1 tgtParams edgeArgs = some env2 ∧
            stateMatches env2 tys locals tgtAbs := by
  simp only [checkEdge, Bool.and_eq_true, beq_iff_eq] at hedge
  rcases hedge with ⟨⟨⟨⟨hPLen, hAbsLen⟩, hEraseLen⟩, hArgsLive⟩, hSlotsOk⟩
  have hnodup : tgtParams.Nodup := nodup_of_eraseDups_length tgtParams hEraseLen
  have hArgsEval : ∀ a, a ∈ edgeArgs → ∃ v, evalSsaArg env1 a = some v := by
    intro a ha
    have haOk := (List.all_eq_true.mp hArgsLive) a ha
    cases a with
    | constU64 k => exact ⟨k, rfl⟩
    | reg rs => exact exists_val_of_not_regNotInAbs env1 tys locals absEnd rs hm haOk
  obtain ⟨env2, hbind⟩ := bindSsaParams_exists env1 tgtParams edgeArgs env1 hPLen hArgsEval
  refine ⟨env2, hbind, ?_⟩
  rcases hm with ⟨htl, hla, hslots⟩
  refine ⟨htl, by omega, ?_⟩
  intro i ty sl dstSl hiTy hiLoc hiDst
  have hiLt : i < absEnd.length := hAbsLen ▸ getAt?_lt_length tgtAbs i dstSl hiDst
  obtain ⟨srcSl, hiSrc⟩ := getAt?_some_of_lt absEnd i hiLt
  have hsm := hslots i ty sl srcSl hiTy hiLoc hiSrc
  have hpairOk := (List.all_eq_true.mp hSlotsOk) (srcSl, dstSl) (getAt?_zip_mem absEnd tgtAbs i srcSl dstSl hiSrc hiDst)
  cases srcSl <;> cases dstSl <;> simp only at hpairOk
  · -- dead, dead
    cases sl with
    | dead => trivial
    | live p => cases ty <;> cases p <;> simp [slotMatches] at hsm
  · cases hpairOk
  · cases hpairOk
  · cases hpairOk
  · cases hpairOk
  · -- liveScalar rs, liveScalar rd
    case liveScalar.liveScalar rs rd =>
    cases ty with
    | unit => cases sl <;> simp [slotMatches] at hsm
    | pairU64 => cases sl <;> simp [slotMatches] at hsm
    | u64 =>
      cases sl with
      | dead => cases rs <;> simp [slotMatches] at hsm
      | live p =>
        cases p with
        | zst => cases rs <;> simp [slotMatches] at hsm
        | pair _ _ => cases rs <;> simp [slotMatches] at hsm
        | scalar ov =>
          cases rd with
          | none => simp [slotMatches]
          | some rd' =>
            have hsrc : ∀ r, rs = some r → ∃ x, ov = some x ∧ env1 r = some x := by
              intro r hr
              subst hr
              cases ov with
              | none => simp [slotMatches] at hsm
              | some x => exact ⟨x, rfl, hsm⟩
            obtain ⟨x, hxOv, hxEnv2⟩ :=
              checkEdge_regOk_sound env1 env2 tgtParams edgeArgs hbind hnodup rs rd' ov hsrc hpairOk
            subst hxOv
            exact hxEnv2
  · cases hpairOk
  · cases hpairOk
  · cases hpairOk
  · cases hpairOk
  · -- liveZst, liveZst
    cases ty <;> cases sl <;> try (simp [slotMatches] at hsm)
    case unit.live p => cases p <;> simp [slotMatches] at hsm ⊢
  · cases hpairOk
  · cases hpairOk
  · cases hpairOk
  · cases hpairOk
  · -- livePair s0 s1, livePair d0 d1
    case livePair.livePair s0 s1 d0 d1 =>
    simp only [Bool.and_eq_true] at hpairOk
    cases ty <;> cases sl <;> try (simp [slotMatches] at hsm)
    case pairU64.live p =>
      cases p with
      | scalar _ => simp at hsm
      | zst => simp at hsm
      | pair v0 v1 =>
        simp only [slotMatches] at hsm ⊢
        refine ⟨?_, ?_⟩
        · intro reg hreg
          subst hreg
          exact checkEdge_regOk_sound env1 env2 tgtParams edgeArgs hbind hnodup s0 reg v0 hsm.1 hpairOk.1
        · intro reg hreg
          subst hreg
          exact checkEdge_regOk_sound env1 env2 tgtParams edgeArgs hbind hnodup s1 reg v1 hsm.2 hpairOk.2

/-! ### Core Theorems (Revised Pre-Freeze Statement Surface) -/

/-- **Theorem 1 (`mir_to_minissa_forward_bisim`):**
If `checkMirToMiniSsaCert mir ssa cert = true`, then starting from any matching initial state
at block `pc` (including arbitrary loops over arbitrary `fuel`), operational field-granular
`deinitMovedPlace = true` MIR execution produces the EXACT same `ExecOutcome` as immutable
`MiniSSA` execution (both return values and out-of-fuel divergence agree, with zero faults). -/
theorem mir_to_minissa_forward_bisim
    (mir : MirBody) (ssa : SsaBody) (cert : SsaCert)
    (hcert : checkMirToMiniSsaCert mir ssa cert = true)
    (fuel pc : Nat) (locals : List LocalSlot) (env : SsaEnv) (entryAbs : List AbsSlot)
    (habs : getAt? cert.blockEntryAbs pc = some entryAbs)
    (hmatch : stateMatches env mir.localTys locals entryAbs) :
    ∃ out, execMirLoop .fieldGranular mir fuel pc locals = .ok out ∧
           execSsaLoop ssa fuel pc env = some out := by
  induction fuel generalizing pc locals env entryAbs with
  | zero =>
    exact ⟨.outOfFuel, rfl, rfl⟩
  | succ fuel' ih =>
    have hcert' := hcert
    simp only [checkMirToMiniSsaCert, Bool.and_eq_true, beq_iff_eq] at hcert'
    rcases hcert' with ⟨⟨hLenSsa, hLenCert⟩, hAllBlks⟩
    have hpcLt : pc < mir.blocks.length := hLenCert ▸ getAt?_lt_length cert.blockEntryAbs pc entryAbs habs
    have hblkOk : checkOneBlock mir ssa cert pc = true :=
      (List.all_eq_true.mp hAllBlks) pc (List.mem_range.mpr hpcLt)
    simp only [checkOneBlock] at hblkOk
    cases hmblk : getAt? mir.blocks pc with
    | none => simp [hmblk] at hblkOk
    | some mblk =>
      cases hsblk : getAt? ssa.blocks pc with
      | none => simp [hmblk, hsblk] at hblkOk
      | some sblk =>
        simp only [hmblk, hsblk, habs, Bool.and_eq_true, beq_iff_eq] at hblkOk
        rcases hblkOk with ⟨_, hBodyOk⟩
        cases hstmts : checkBlockStmts mir.localTys entryAbs mblk.stmts sblk.stmts with
        | none => simp [hstmts] at hBodyOk
        | some absEnd =>
          simp only [hstmts] at hBodyOk
          obtain ⟨l1, env1, hMirStmts, hSsaStmts, hm1⟩ :=
            checkBlockStmts_sound mir.localTys mblk.stmts sblk.stmts entryAbs absEnd locals env hmatch hstmts
          cases hmt : mblk.term <;> cases hst : sblk.term <;> simp only [hmt, hst] at hBodyOk
          · -- goto / goto
            case goto.goto tgt sTgt sArgs =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hBodyOk
            rcases hBodyOk with ⟨rfl, hTargetOk⟩
            cases htblk : getAt? ssa.blocks tgt with
            | none => simp [htblk] at hTargetOk
            | some tblk =>
              cases htAbs : getAt? cert.blockEntryAbs tgt with
              | none => simp [htblk, htAbs] at hTargetOk
              | some tAbs =>
                simp only [htblk, htAbs] at hTargetOk
                obtain ⟨env2, hbind, hm2⟩ :=
                  checkEdge_sound env1 mir.localTys l1 absEnd tAbs tblk.params sArgs hm1 hTargetOk
                obtain ⟨out, hmirOut, hssaOut⟩ := ih tgt l1 env2 tAbs htAbs hm2
                refine ⟨out, ?_, ?_⟩
                · simp [execMirLoop, hmblk, hMirStmts, hmt, hmirOut]
                · simp [execSsaLoop, hsblk, hSsaStmts, hst, htblk, hbind, hssaOut]
          · cases hBodyOk
          · cases hBodyOk
          · cases hBodyOk
          · -- switchZero / switchZero
            case switchZero.switchZero discr zTgt nzTgt sDiscr szTgt szArgs snzTgt snzArgs =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hBodyOk
            rcases hBodyOk with ⟨⟨rfl, rfl⟩, hSwOk⟩
            cases hdisc : checkAbsOperand mir.localTys absEnd discr with
            | none => simp [hdisc] at hSwOk
            | some res =>
              rcases res with ⟨optArg, absAfter⟩
              cases optArg with
              | none => simp [hdisc] at hSwOk
              | some aDiscr =>
                simp only [hdisc, Bool.and_eq_true, beq_iff_eq] at hSwOk
                rcases hSwOk with ⟨rfl, hEdgesOk⟩
                cases hzBlk : getAt? ssa.blocks zTgt with
                | none => simp [hzBlk] at hEdgesOk
                | some zBlk =>
                  cases hzAbs : getAt? cert.blockEntryAbs zTgt with
                  | none => simp [hzBlk, hzAbs] at hEdgesOk
                  | some zAbs =>
                    cases hnzBlk : getAt? ssa.blocks nzTgt with
                    | none => simp [hzBlk, hzAbs, hnzBlk] at hEdgesOk
                    | some nzBlk =>
                      cases hnzAbs : getAt? cert.blockEntryAbs nzTgt with
                      | none => simp [hzBlk, hzAbs, hnzBlk, hnzAbs] at hEdgesOk
                      | some nzAbs =>
                        simp only [hzBlk, hzAbs, hnzBlk, hnzAbs, Bool.and_eq_true] at hEdgesOk
                        rcases hEdgesOk with ⟨hzEdge, hnzEdge⟩
                        obtain ⟨n, l2, hevalDisc, hargDisc, hm2⟩ :=
                          checkAbsOperand_some env1 mir.localTys l1 absEnd absAfter discr aDiscr hm1 hdisc
                        cases hn0 : (n == 0) with
                        | true =>
                          obtain ⟨env2, hbind, hm3⟩ :=
                            checkEdge_sound env1 mir.localTys l2 absAfter zAbs zBlk.params szArgs hm2 hzEdge
                          obtain ⟨out, hmirOut, hssaOut⟩ := ih zTgt l2 env2 zAbs hzAbs hm3
                          refine ⟨out, ?_, ?_⟩
                          · simp [execMirLoop, hmblk, hMirStmts, hmt, hevalDisc, hn0, hmirOut]
                          · simp [execSsaLoop, hsblk, hSsaStmts, hst, hargDisc, hn0, hzBlk, hbind, hssaOut]
                        | false =>
                          obtain ⟨env2, hbind, hm3⟩ :=
                            checkEdge_sound env1 mir.localTys l2 absAfter nzAbs nzBlk.params snzArgs hm2 hnzEdge
                          obtain ⟨out, hmirOut, hssaOut⟩ := ih nzTgt l2 env2 nzAbs hnzAbs hm3
                          refine ⟨out, ?_, ?_⟩
                          · simp [execMirLoop, hmblk, hMirStmts, hmt, hevalDisc, hn0, hmirOut]
                          · simp [execSsaLoop, hsblk, hSsaStmts, hst, hargDisc, hn0, hnzBlk, hbind, hssaOut]
          · cases hBodyOk
          · cases hBodyOk
          · cases hBodyOk
          · -- ret / ret
            case ret.ret sRetArg =>
            cases hty0 : getAt? mir.localTys 0 with
            | none => simp [hty0] at hBodyOk
            | some ty0 =>
              cases hab0 : getAt? absEnd 0 with
              | none => simp [hty0, hab0] at hBodyOk
              | some ab0 =>
                cases ty0 <;> cases ab0 <;> simp [hty0, hab0] at hBodyOk
                case u64.liveScalar opt =>
                  cases opt with
                  | none => simp at hBodyOk
                  | some r0 =>
                    simp only [beq_iff_eq] at hBodyOk
                    subst hBodyOk
                    have h0Lt : 0 < l1.length := hm1.1 ▸ getAt?_lt_length mir.localTys 0 .u64 hty0
                    obtain ⟨sl0, hsl0⟩ := getAt?_some_of_lt l1 0 h0Lt
                    have hsm0 := hm1.2.2 0 .u64 sl0 (.liveScalar (some r0)) hty0 hsl0 hab0
                    cases sl0 with
                    | dead => exact False.elim hsm0
                    | live p0 =>
                      cases p0 with
                      | zst => exact False.elim hsm0
                      | pair _ _ => exact False.elim hsm0
                      | scalar ov =>
                        cases ov with
                        | none => exact False.elim hsm0
                        | some v =>
                          simp only [slotMatches] at hsm0
                          refine ⟨.ret v, ?_, ?_⟩
                          · simp [execMirLoop, hmblk, hMirStmts, hmt, hty0, hsl0]
                          · simp [execSsaLoop, hsblk, hSsaStmts, hst, evalSsaArg, hsm0]

/-- **Theorem 2 (`mir_to_minissa_vc_transport` — Strengthened per B4):**
Any postcondition `P : UInt64 → Prop` proved over `MiniSSA` transports soundly to MIR,
MIR and MiniSSA agree bidirectionally on return outcomes, AND MIR is completely fault-free
(`∀ fuel k, ... ≠ .error k`, matching `Trusted.MirSemantics.WellFormed`). -/
theorem mir_to_minissa_vc_transport
    (mir : MirBody) (ssa : SsaBody) (cert : SsaCert)
    (hcert : checkMirToMiniSsaCert mir ssa cert = true)
    (locals : List LocalSlot) (env : SsaEnv) (entryAbs : List AbsSlot)
    (habs : getAt? cert.blockEntryAbs 0 = some entryAbs)
    (hmatch : stateMatches env mir.localTys locals entryAbs)
    (P : UInt64 → Prop)
    (hssa : ∀ fuel v, execSsaLoop ssa fuel 0 env = some (.ret v) → P v) :
    (∀ fuel v, execMirLoop .fieldGranular mir fuel 0 locals = .ok (.ret v) → P v) ∧
    (∀ fuel v, execMirLoop .fieldGranular mir fuel 0 locals = .ok (.ret v) ↔
               execSsaLoop ssa fuel 0 env = some (.ret v)) ∧
    (∀ fuel k, execMirLoop .fieldGranular mir fuel 0 locals ≠ .error k) := by
  have hbisim : ∀ fuel, ∃ out,
      execMirLoop .fieldGranular mir fuel 0 locals = .ok out ∧
      execSsaLoop ssa fuel 0 env = some out :=
    fun fuel => mir_to_minissa_forward_bisim mir ssa cert hcert fuel 0 locals env entryAbs habs hmatch
  refine ⟨?_, ?_, ?_⟩
  · intro fuel v hmir
    obtain ⟨out, hm, hs⟩ := hbisim fuel
    rw [hm] at hmir
    cases hmir
    exact hssa fuel v hs
  · intro fuel v
    obtain ⟨out, hm, hs⟩ := hbisim fuel
    rw [hm, hs]
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  · intro fuel k hmir
    obtain ⟨out, hm, _⟩ := hbisim fuel
    rw [hm] at hmir
    cases hmir

/-! ### Positive Non-Vacuity Canaries & Tightness Counterexamples -/

/-- **Positive Non-Vacuity Canary (`canary_counted_loop_cert_accepted`):**
A real 4-block counted summation loop `sum(n)` with phi-parameter back-edges passes
`checkMirToMiniSsaCert = true` and evaluates identically (`sum(5) = 15`) in both MIR and MiniSSA. -/
def sumLoopMir : MirBody :=
  { localTys := [.u64, .u64, .u64] -- _0=ret, _1=n, _2=acc
  , blocks := [
      { stmts := [.assign (.local 2) (.use (.constU64 0))], term := .goto 1 },
      { stmts := [], term := .switchZero (.copy (.local 1)) 3 2 },
      { stmts := [
          .assign (.local 2) (.binaryOp .add (.move (.local 2)) (.copy (.local 1))),
          .assign (.local 1) (.binaryOp .sub (.move (.local 1)) (.constU64 1))
        ], term := .goto 1 },
      { stmts := [.assign (.local 0) (.use (.move (.local 2)))], term := .ret }
    ] }

def sumLoopSsa : SsaBody :=
  { blocks := [
      { params := [], stmts := [.copy 2 (.constU64 0)], term := .goto 1 [.reg 1, .reg 2] },
      { params := [3, 4], stmts := [], term := .switchZero (.reg 3) 3 [] 2 [] },
      { params := [], stmts := [
          .binOp 5 .add (.reg 4) (.reg 3),
          .binOp 6 .sub (.reg 3) (.constU64 1)
        ], term := .goto 1 [.reg 6, .reg 5] },
      { params := [], stmts := [.copy 7 (.reg 4)], term := .ret (.reg 7) }
    ] }

def sumLoopCert : SsaCert :=
  { blockEntryAbs := [
      [.liveScalar none, .liveScalar (some 1), .liveScalar none],
      [.liveScalar none, .liveScalar (some 3), .liveScalar (some 4)],
      [.liveScalar none, .liveScalar (some 3), .liveScalar (some 4)],
      [.liveScalar none, .liveScalar (some 3), .liveScalar (some 4)]
    ] }

theorem canary_counted_loop_cert_accepted :
    checkMirToMiniSsaCert sumLoopMir sumLoopSsa sumLoopCert = true ∧
    execMirLoop .fieldGranular sumLoopMir 20 0
      [.live (.scalar none), .live (.scalar (some 5)), .live (.scalar none)] = .ok (.ret 15) ∧
    execSsaLoop sumLoopSsa 20 0 (fun r => if r == 1 then some 5 else none) = some (.ret 15) :=
  ⟨rfl, rfl, rfl⟩

/-- **Counterexample 1 (`ce_operand_order_matters` — Real `libcore` M4 pattern):**
`copy _0 + move _0` SUCCEEDS (`42 + 42 = 84`), while `move _0 + copy _0` FAULTS `.undefined`. -/
theorem ce_operand_order_matters :
    evalRvalue .fieldGranular [.u64] [.live (.scalar (some 42))]
      (.binaryOp .add (.copy (.local 0)) (.move (.local 0))) =
      .ok (.u64 84, [.live (.scalar none)]) ∧
    evalRvalue .fieldGranular [.u64] [.live (.scalar (some 42))]
      (.binaryOp .add (.move (.local 0)) (.copy (.local 0))) =
      .error .undefined :=
  ⟨rfl, rfl⟩

/-- **Counterexample 2 (`ce_local_granular_breaks_sibling_field_move` — Real `zerocopy`/`libcore` M3 pattern):**
Moving `(_0.0)` then `(_0.1)` SUCCEEDS under `.fieldGranular` and FAULTS `.undefined` under `.localGranular`. -/
theorem ce_local_granular_breaks_sibling_field_move :
    evalRvalue .fieldGranular [.pairU64] [.live (.pair (some 10) (some 20))]
      (.binaryOp .add (.move (.field 0 .fst)) (.move (.field 0 .snd))) =
      .ok (.u64 30, [.live (.pair none none)]) ∧
    evalRvalue .localGranular [.pairU64] [.live (.pair (some 10) (some 20))]
      (.binaryOp .add (.move (.field 0 .fst)) (.move (.field 0 .snd))) =
      .error .undefined :=
  ⟨rfl, rfl⟩

/-- **Counterexample 3 (`ce_zst_move_remains_inhabited` — `Trusted.MirSemantics.liveUninitSlot`):**
Moving a `.unit` local followed by copying it SUCCEEDS, whereas doing so on `.u64` FAULTS `.undefined`. -/
theorem ce_zst_move_remains_inhabited :
    (match evalOperand .fieldGranular [.unit] [.live .zst] (.move (.local 0)) with
     | .ok (.unit, l1) => evalOperand .fieldGranular [.unit] l1 (.copy (.local 0))
     | other => other) = .ok (.unit, [.live .zst]) ∧
    (match evalOperand .fieldGranular [.u64] [.live (.scalar (some 7))] (.move (.local 0)) with
     | .ok (_, l1) => evalOperand .fieldGranular [.u64] l1 (.copy (.local 0))
     | other => other) = .error .undefined :=
  ⟨rfl, rfl⟩

/-- **Counterexample 4 (`ce_loop_backedge_use_after_move` — Strengthened unconditionally per B4):**
A 1-block self-loop that moves `_1` without re-initializing it before the back-edge succeeds on
iteration 1 (`fuel = 1` -> `.outOfFuel`) and FAULTS `.undefined` on iteration 2 (`fuel = 2`),
and `checkMirToMiniSsaCert` rejects EVERY `(ssa, cert)` unconditionally. -/
def loopUseAfterMoveMir : MirBody :=
  { localTys := [.u64, .u64]
  , blocks := [
      { stmts := [.assign (.local 0) (.use (.move (.local 1)))]
      , term  := .goto 0 }
    ] }

theorem ce_loop_backedge_use_after_move :
    execMirLoop .fieldGranular loopUseAfterMoveMir 1 0 [.live (.scalar none), .live (.scalar (some 9))] =
      .ok .outOfFuel ∧
    execMirLoop .fieldGranular loopUseAfterMoveMir 2 0 [.live (.scalar none), .live (.scalar (some 9))] =
      .error .undefined ∧
    (∀ ssa cert, checkMirToMiniSsaCert loopUseAfterMoveMir ssa cert = false) := by
  refine ⟨rfl, rfl, ?_⟩
  intro ssa cert
  cases h : checkMirToMiniSsaCert loopUseAfterMoveMir ssa cert with
  | false => rfl
  | true =>
    exfalso
    simp only [checkMirToMiniSsaCert, loopUseAfterMoveMir, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hLenSsa, hLenCert⟩, hAll⟩
    have hblk : checkOneBlock loopUseAfterMoveMir ssa cert 0 = true :=
      (List.all_eq_true.mp hAll) 0 (List.mem_range.mpr (Nat.zero_lt_succ 0))
    simp only [checkOneBlock, loopUseAfterMoveMir, getAt?] at hblk
    cases hsblk : getAt? ssa.blocks 0 with
    | none => simp [hsblk] at hblk
    | some sblk =>
      cases habs : getAt? cert.blockEntryAbs 0 with
      | none => simp [hsblk, habs] at hblk
      | some entryAbs =>
        simp only [hsblk, habs, Bool.and_eq_true, beq_iff_eq] at hblk
        rcases hblk with ⟨hEntryLen, hBody⟩
        cases entryAbs with
        | nil => simp at hEntryLen
        | cons a0 rest0 =>
          cases rest0 with
          | nil => simp at hEntryLen
          | cons a1 rest1 =>
            cases rest1 with
            | cons _ _ => simp at hEntryLen
            | nil =>
              cases hstmts : checkBlockStmts [.u64, .u64] [a0, a1] [.assign (.local 0) (.use (.move (.local 1)))] sblk.stmts with
              | none => simp [hstmts] at hBody
              | some absEnd =>
                simp only [hstmts] at hBody
                cases a0 <;> simp [checkBlockStmts, getAt?] at hstmts
                case liveScalar opt0 =>
                  cases a1 <;> simp [checkAbsOperand, getAt?] at hstmts
                  case liveScalar opt1 =>
                    cases opt1 with
                    | none => simp at hstmts
                    | some r1 =>
                      cases hss : sblk.stmts with
                      | nil => simp [hss] at hstmts
                      | cons ss0 srest =>
                        cases ss0 with
                        | binOp _ _ _ _ => simp [hss] at hstmts
                        | copy dstReg sArg' =>
                          simp only [hss, setAt?, Option.map_some, Option.bind_some] at hstmts
                          split at hstmts
                          · simp only [regNotInAbs, List.all_cons, List.all_nil, Bool.and_self, ↓reduceIte] at hstmts
                            cases srest with
                            | cons _ _ => simp [checkBlockStmts] at hstmts
                            | nil =>
                              simp only [checkBlockStmts, Option.some.injEq] at hstmts
                              subst hstmts
                              cases hterm : sblk.term with
                              | switchZero _ _ _ _ _ => simp [hterm] at hBody
                              | ret _ => simp [hterm] at hBody
                              | goto sTgt sArgs =>
                                simp only [hterm, Bool.and_eq_true, beq_iff_eq] at hBody
                                rcases hBody with ⟨hTgt0, hEdge⟩
                                subst hTgt0
                                simp only [hsblk, habs] at hEdge
                                simp only [checkEdge, Bool.and_eq_true] at hEdge
                                rcases hEdge with ⟨_, hSlots⟩
                                have hSlot1 := (List.all_eq_true.mp hSlots)
                                  (.liveScalar none, .liveScalar (some r1))
                                  (List.Mem.tail _ (List.Mem.head _))
                                simp only at hSlot1
                                cases hfind : (sblk.params.zip sArgs).find? (fun p => p.1 == r1) with
                                | none => simp [hfind] at hSlot1
                                | some p =>
                                  rcases p with ⟨_, arg⟩
                                  cases arg <;> simp [hfind] at hSlot1
                          · simp at hstmts

end VrustcFormal.F1_1

#print axioms VrustcFormal.F1_1.mir_to_minissa_forward_bisim
#print axioms VrustcFormal.F1_1.mir_to_minissa_vc_transport
#print axioms VrustcFormal.F1_1.ce_loop_backedge_use_after_move
