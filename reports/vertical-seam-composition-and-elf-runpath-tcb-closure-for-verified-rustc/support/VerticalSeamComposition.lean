/-!
Kernel-Checked Lean v4.34.1 Vertical Composition & Adversarial Counterexample Suite
for `r3_b3_seam_crucible_4`:
- Seam V1: `F1-1b` `MoveToCopy` / `RemoveStorageMarkers` (`deinitMovedPlace = true`)
           × `E2-4` `Const::Unevaluated` dependency cone
           × `E2-9` `WithRetag` (`no_retag copy`) & `F1-2` Tree Borrows retagging
- Seam V2: `F1-2` Tree Borrows Partial SROA
           × `E2-6` Multi-Target `FnAbi` release/target drift (`55/833` binary breaks)
           × `E2-9` `Atomic<T>` / `UnsafeCell` indirect stack copy & `readonly` UB
- Seam V3: `E2-7` AVX-512 `prefer-256-bit` vs `ZMM512` spill cliff (`> 4096 B`)
           × `r2` `vzeroupper` / `16-B` outlined thunks / FDE CFA
           × `E2-9` `x86_64` `fence(SeqCst)` red-zone `lock orl $0, -64(%rsp)` vs `(%rsp)`
- Seam V4: `7176fdd92a` `libleanshared.so` + `$ORIGIN/../lib` `DT_RUNPATH` precedence closure
           × `E2-2` `nanoda_bin 0.4.19` dual-kernel checking & choice-axiom gate
           × `ktrust` (`Toy.KernelTrust`) `pinned` statement-hash binding
- Seam V5: Unified end-to-end vertical composition theorem, non-vacuity witness,
           and cross-seam ablation counterexample.

Kernel & TCB Discipline:
- Zero unproved placeholders or incomplete proofs
- Zero choice axiom; constructive `[propext, Quot.sound]` / empty-axiom proofs only
- Zero decision-procedure black boxes or native boolean reflection
- Zero recursive compiler shims (`noncomputable def` on all recursive/value defs)
- Zero external calls or separate trusted namespace declarations.
-/

namespace VrustcProbe.VerticalSeamComposition

/-! ## Section 1: Seam V1 (`F1-1b` × `E2-4` `Const::Unevaluated` Cone × `E2-9` `WithRetag` / Tree Borrows) -/

inductive RustcRelease where
  | r1_96_0
  | r1_99_1
  | r1_100_0
  | r1_102_nightly
  deriving DecidableEq

inductive WithRetagMode where
  | noRetag
  | retagChild
  deriving DecidableEq

noncomputable def defaultCopyRetag : RustcRelease → WithRetagMode
  | .r1_96_0 => .noRetag
  | .r1_99_1 => .retagChild
  | .r1_100_0 => .retagChild
  | .r1_102_nightly => .retagChild

inductive TbPerm where
  | cell
  | reserved (conflicted : Bool)
  | active
  | frozen
  | disabled
  deriving DecidableEq

structure BorrowCell where
  val : BitVec 64
  isUnsafeCell : Bool
  nextTag : Nat
  permOf : Nat → TbPerm

noncomputable def tbStepTag (c : BorrowCell) (accessorTag : Nat) (isWrite : Bool) (newVal : BitVec 64) :
    Option BorrowCell :=
  match c.permOf accessorTag with
  | .disabled => none
  | .frozen => if isWrite then none else some c
  | .cell =>
      some { c with val := if isWrite then newVal else c.val }
  | .reserved _ =>
      if isWrite then
        some { c with
          val := newVal
          permOf := fun t =>
            if Nat.beq t accessorTag then .active
            else if Nat.beq t 1 && Nat.beq accessorTag 0 then .disabled
            else c.permOf t }
      else some c
  | .active =>
      if isWrite then
        some { c with
          val := newVal
          permOf := fun t =>
            if Nat.beq t accessorTag then .active
            else if Nat.beq t 1 && Nat.beq accessorTag 0 then .disabled
            else c.permOf t }
      else some c

inductive LocalSlot where
  | dead
  | liveUninit
  | liveScalar (v : BitVec 64)
  | livePtr (tag : Nat)
  deriving DecidableEq

inductive MirOp where
  | lit (v : BitVec 64)
  | unevalConst (cid : Nat)
  | copy (loc : Nat)
  | move (loc : Nat)
  deriving DecidableEq

inductive MirStmt where
  | storageLive (loc : Nat)
  | storageDead (loc : Nat)
  | nop
  | assignOp (dst : Nat) (op : MirOp)
  | bitAndOp (dst : Nat) (lhs rhs : MirOp)
  | checkedLutLoad (dst idxLoc : Nat) (lutLen : BitVec 64)
  | useRefAssign (dst srcPtrLoc : Nat) (isMove explicitNoRetag : Bool)
  | ptrWrite (ptrLoc : Nat) (v : BitVec 64)
  | ptrRead (dst ptrLoc : Nat)
  deriving DecidableEq

inductive V1Fault where
  | useAfterMoveUb
  | deadSlotUb
  | oobPanic
  | tbUb
  | storageDeadRetUb
  | typeMismatchUb
  deriving DecidableEq

inductive V1Outcome (α : Type) where
  | ok (val : α)
  | error (f : V1Fault)
  deriving DecidableEq

structure MirBody where
  numLocals : Nat
  stmts : List MirStmt
  constConeIds : List Nat
  specHash : BitVec 64

structure MirV1State where
  slots : Nat → LocalSlot
  mem : BorrowCell

noncomputable def setSlot (slots : Nat → LocalSlot) (loc : Nat) (s : LocalSlot) : Nat → LocalSlot :=
  fun k => if Nat.beq k loc then s else slots k

abbrev ConstEnv := Nat → BitVec 64

noncomputable def evalMirOp (cenv : ConstEnv) (slots : Nat → LocalSlot) :
    MirOp → V1Outcome (BitVec 64 × (Nat → LocalSlot))
  | .lit v => .ok (v, slots)
  | .unevalConst cid => .ok (cenv cid, slots)
  | .copy loc =>
      match slots loc with
      | .dead => .error .deadSlotUb
      | .liveUninit => .error .useAfterMoveUb
      | .liveScalar v => .ok (v, slots)
      | .livePtr _ => .error .typeMismatchUb
  | .move loc =>
      match slots loc with
      | .dead => .error .deadSlotUb
      | .liveUninit => .error .useAfterMoveUb
      | .liveScalar v => .ok (v, setSlot slots loc .liveUninit)
      | .livePtr _ => .error .typeMismatchUb

noncomputable def evalMirStmt (cenv : ConstEnv) (rel : RustcRelease)
    (st : MirV1State) : MirStmt → V1Outcome MirV1State
  | .nop => .ok st
  | .storageLive loc =>
      .ok { st with slots := setSlot st.slots loc .liveUninit }
  | .storageDead loc =>
      if Nat.beq loc 0 then .error .storageDeadRetUb
      else .ok { st with slots := setSlot st.slots loc .dead }
  | .assignOp dst op =>
      match evalMirOp cenv st.slots op with
      | .error e => .error e
      | .ok (v, slots1) =>
          match slots1 dst with
          | .dead => .error .deadSlotUb
          | _ => .ok { st with slots := setSlot slots1 dst (.liveScalar v) }
  | .bitAndOp dst lhs rhs =>
      match evalMirOp cenv st.slots lhs with
      | .error e => .error e
      | .ok (vl, slots1) =>
          match evalMirOp cenv slots1 rhs with
          | .error e => .error e
          | .ok (vr, slots2) =>
              match slots2 dst with
              | .dead => .error .deadSlotUb
              | _ => .ok { st with slots := setSlot slots2 dst (.liveScalar (vl &&& vr)) }
  | .checkedLutLoad dst idxLoc lutLen =>
      match st.slots idxLoc with
      | .dead => .error .deadSlotUb
      | .liveUninit => .error .useAfterMoveUb
      | .liveScalar idx =>
          if idx < lutLen then
            match st.slots dst with
            | .dead => .error .deadSlotUb
            | _ => .ok { st with slots := setSlot st.slots dst (.liveScalar idx) }
          else .error .oobPanic
      | .livePtr _ => .error .typeMismatchUb
  | .useRefAssign dst srcPtrLoc isMove explicitNoRetag =>
      match st.slots srcPtrLoc with
      | .dead => .error .deadSlotUb
      | .liveUninit => .error .useAfterMoveUb
      | .liveScalar _ => .error .typeMismatchUb
      | .livePtr srcTag =>
          match st.mem.permOf srcTag with
          | .disabled => .error .tbUb
          | _ =>
              let mode := if explicitNoRetag then .noRetag else defaultCopyRetag rel
              let slots1 := if isMove then setSlot st.slots srcPtrLoc .liveUninit else st.slots
              match slots1 dst with
              | .dead => .error .deadSlotUb
              | _ =>
                  match mode with
                  | .noRetag =>
                      .ok { st with slots := setSlot slots1 dst (.livePtr srcTag) }
                  | .retagChild =>
                      let childTag := st.mem.nextTag
                      let mem1 : BorrowCell :=
                        { st.mem with
                          nextTag := childTag + 1
                          permOf := fun t =>
                            if Nat.beq t childTag then
                              (if st.mem.isUnsafeCell then .cell else .active)
                            else st.mem.permOf t }
                      .ok { slots := setSlot slots1 dst (.livePtr childTag), mem := mem1 }
  | .ptrWrite ptrLoc v =>
      match st.slots ptrLoc with
      | .dead => .error .deadSlotUb
      | .liveUninit => .error .useAfterMoveUb
      | .liveScalar _ => .error .typeMismatchUb
      | .livePtr tag =>
          match tbStepTag st.mem tag true v with
          | none => .error .tbUb
          | some mem1 => .ok { st with mem := mem1 }
  | .ptrRead dst ptrLoc =>
      match st.slots ptrLoc with
      | .dead => .error .deadSlotUb
      | .liveUninit => .error .useAfterMoveUb
      | .liveScalar _ => .error .typeMismatchUb
      | .livePtr tag =>
          match tbStepTag st.mem tag false 0#64 with
          | none => .error .tbUb
          | some mem1 =>
              match st.slots dst with
              | .dead => .error .deadSlotUb
              | _ => .ok { slots := setSlot st.slots dst (.liveScalar mem1.val), mem := mem1 }

noncomputable def evalMirStmts (cenv : ConstEnv) (rel : RustcRelease)
    (st : MirV1State) : List MirStmt → V1Outcome MirV1State
  | [] => .ok st
  | s :: rest =>
      match evalMirStmt cenv rel st s with
      | .error e => .error e
      | .ok st1 => evalMirStmts cenv rel st1 rest

noncomputable def hasStorageMarker (loc : Nat) : List MirStmt → Bool
  | [] => false
  | .storageLive k :: rest => if Nat.beq loc k then true else hasStorageMarker loc rest
  | .storageDead k :: rest => if Nat.beq loc k then true else hasStorageMarker loc rest
  | _ :: rest => hasStorageMarker loc rest

noncomputable def initV1Slots (stmts : List MirStmt) (arg1 : BitVec 64) : Nat → LocalSlot :=
  fun k =>
    if Nat.beq k 0 then .liveUninit
    else if Nat.beq k 1 then .liveScalar arg1
    else if hasStorageMarker k stmts then .dead
    else .liveUninit

noncomputable def initV1State (stmts : List MirStmt) (arg1 : BitVec 64) : MirV1State :=
  { slots := initV1Slots stmts arg1
    mem := { val := 0#64, isUnsafeCell := false, nextTag := 1, permOf := fun _ => .active } }

noncomputable def initV1RefState (stmts : List MirStmt) (seed : BitVec 64) : MirV1State :=
  { slots := fun k =>
      if Nat.beq k 0 then .liveUninit
      else if Nat.beq k 1 then .livePtr 0
      else if hasStorageMarker k stmts then .dead
      else .liveUninit
    mem := { val := seed, isUnsafeCell := false, nextTag := 1, permOf := fun _ => .active } }

noncomputable def evalMirBody (cenv : ConstEnv) (rel : RustcRelease)
    (body : MirBody) (arg1 : BitVec 64) : V1Outcome (BitVec 64) :=
  match evalMirStmts cenv rel (initV1State body.stmts arg1) body.stmts with
  | .error e => .error e
  | .ok stF =>
      match stF.slots 0 with
      | .liveScalar v => .ok v
      | .liveUninit => .error .useAfterMoveUb
      | .dead => .error .deadSlotUb
      | .livePtr _ => .error .typeMismatchUb

noncomputable def evalMirRefBody (cenv : ConstEnv) (rel : RustcRelease)
    (body : MirBody) (seed : BitVec 64) : V1Outcome (BitVec 64) :=
  match evalMirStmts cenv rel (initV1RefState body.stmts seed) body.stmts with
  | .error e => .error e
  | .ok stF =>
      match stF.slots 0 with
      | .liveScalar v => .ok v
      | .liveUninit => .error .useAfterMoveUb
      | .dead => .error .deadSlotUb
      | .livePtr _ => .error .typeMismatchUb

-- F1-1b pre-normalization passes over MirBody: MoveToCopy and all-in-bounds RemoveStorageMarkers.
noncomputable def demoteMoveOp : MirOp → MirOp
  | .move loc => .copy loc
  | op => op

noncomputable def applyMoveToCopyStmt : MirStmt → MirStmt
  | .assignOp dst op => .assignOp dst (demoteMoveOp op)
  | .bitAndOp dst lhs rhs => .bitAndOp dst (demoteMoveOp lhs) (demoteMoveOp rhs)
  | .useRefAssign dst src _ noRet => .useRefAssign dst src false noRet
  | s => s

noncomputable def applyRemoveStorageStmt : MirStmt → MirStmt
  | .storageLive _ => .nop
  | .storageDead loc => if Nat.beq loc 0 then .storageDead 0 else .nop
  | s => s

noncomputable def applyMoveToCopyProg : List MirStmt → List MirStmt
  | [] => []
  | s :: rest => applyMoveToCopyStmt s :: applyMoveToCopyProg rest

noncomputable def applyRemoveStorageProg : List MirStmt → List MirStmt
  | [] => []
  | s :: rest => applyRemoveStorageStmt s :: applyRemoveStorageProg rest

noncomputable def normalizeF11b (body : MirBody) : MirBody :=
  { body with stmts := applyRemoveStorageProg (applyMoveToCopyProg body.stmts) }

-- Three-state abstract interpretation certificate modeled after F1-1b (`AbsSlot`).
inductive AbsSlot where
  | absInit
  | absUninit
  | absDead
  deriving DecidableEq

noncomputable def setAbs (env : Nat → AbsSlot) (loc : Nat) (s : AbsSlot) : Nat → AbsSlot :=
  fun k => if Nat.beq k loc then s else env k

noncomputable def checkAbsOp (env : Nat → AbsSlot) : MirOp → Option (Nat → AbsSlot)
  | .lit _ => some env
  | .unevalConst _ => some env
  | .copy loc =>
      match env loc with
      | .absInit => some env
      | _ => none
  | .move loc =>
      match env loc with
      | .absInit => some (setAbs env loc .absUninit)
      | _ => none

noncomputable def checkAbsStmt (env : Nat → AbsSlot) : MirStmt → Option (Nat → AbsSlot)
  | .nop => some env
  | .storageLive loc => some (setAbs env loc .absUninit)
  | .storageDead loc =>
      if Nat.beq loc 0 then none else some (setAbs env loc .absDead)
  | .assignOp dst op =>
      match checkAbsOp env op with
      | none => none
      | some env1 =>
          match env1 dst with
          | .absDead => none
          | _ => some (setAbs env1 dst .absInit)
  | .bitAndOp dst lhs rhs =>
      match checkAbsOp env lhs with
      | none => none
      | some env1 =>
          match checkAbsOp env1 rhs with
          | none => none
          | some env2 =>
              match env2 dst with
              | .absDead => none
              | _ => some (setAbs env2 dst .absInit)
  | .checkedLutLoad dst idxLoc _ =>
      match env idxLoc with
      | .absInit =>
          match env dst with
          | .absDead => none
          | _ => some (setAbs env dst .absInit)
      | _ => none
  | .useRefAssign dst src isMove _ =>
      match env src with
      | .absInit =>
          let env1 := if isMove then setAbs env src .absUninit else env
          match env1 dst with
          | .absDead => none
          | _ => some (setAbs env1 dst .absInit)
      | _ => none
  | .ptrWrite ptrLoc _ =>
      match env ptrLoc with
      | .absInit => some env
      | _ => none
  | .ptrRead dst ptrLoc =>
      match env ptrLoc with
      | .absInit =>
          match env dst with
          | .absDead => none
          | _ => some (setAbs env dst .absInit)
      | _ => none

noncomputable def checkAbsStmts (env : Nat → AbsSlot) : List MirStmt → Bool
  | [] => match env 0 with | .absInit => true | _ => false
  | s :: rest =>
      match checkAbsStmt env s with
      | none => false
      | some env1 => checkAbsStmts env1 rest

noncomputable def initAbsEnv (stmts : List MirStmt) : Nat → AbsSlot :=
  fun k =>
    if Nat.beq k 0 then .absUninit
    else if Nat.beq k 1 then .absInit
    else if hasStorageMarker k stmts then .absDead
    else .absUninit

noncomputable def checkMirV1Cert (body : MirBody) : Bool :=
  checkAbsStmts (initAbsEnv body.stmts) body.stmts

-- Naive incremental cache key omits Const::Unevaluated cone values & compiler release.
structure NaiveBodyKey where
  stmts : List MirStmt
  specHash : BitVec 64
  deriving DecidableEq

-- Sound incremental cache key binds body AST, evaluated transitive Const::Unevaluated cone, and release.
structure SoundV1CacheKey where
  stmts : List MirStmt
  constConeVals : List (Nat × BitVec 64)
  rel : RustcRelease
  specHash : BitVec 64
  deriving DecidableEq

noncomputable def evalConstCone (cenv : ConstEnv) : List Nat → List (Nat × BitVec 64)
  | [] => []
  | cid :: rest => (cid, cenv cid) :: evalConstCone cenv rest

noncomputable def naiveBodyOnlyKey (body : MirBody) : NaiveBodyKey :=
  { stmts := body.stmts, specHash := body.specHash }

noncomputable def soundV1CacheKey (cenv : ConstEnv) (rel : RustcRelease) (body : MirBody) : SoundV1CacheKey :=
  { stmts := body.stmts
    constConeVals := evalConstCone cenv body.constConeIds
    rel := rel
    specHash := body.specHash }

noncomputable def opInCone (cone : List Nat) : MirOp → Prop
  | .unevalConst cid => cid ∈ cone
  | _ => True

noncomputable def stmtInCone (cone : List Nat) : MirStmt → Prop
  | .assignOp _ op => opInCone cone op
  | .bitAndOp _ lhs rhs => opInCone cone lhs ∧ opInCone cone rhs
  | _ => True

noncomputable def stmtsInCone (cone : List Nat) : List MirStmt → Prop
  | [] => True
  | s :: rest => stmtInCone cone s ∧ stmtsInCone cone rest

private theorem evalConstCone_eq_implies_mem_eq :
    ∀ (cone : List Nat) (cenv0 cenv1 : ConstEnv),
      evalConstCone cenv0 cone = evalConstCone cenv1 cone →
      ∀ cid, cid ∈ cone → cenv0 cid = cenv1 cid
  | [], _, _, _, cid, hmem => by cases hmem
  | c :: cs, cenv0, cenv1, heq, cid, hmem => by
      dsimp [evalConstCone] at heq
      have hhd : (c, cenv0 c) = (c, cenv1 c) := List.head_eq_of_cons_eq heq
      have htl : evalConstCone cenv0 cs = evalConstCone cenv1 cs := List.tail_eq_of_cons_eq heq
      cases hmem with
      | head => exact congrArg Prod.snd hhd
      | tail _ hmem' => exact evalConstCone_eq_implies_mem_eq cs cenv0 cenv1 htl cid hmem'

private theorem evalMirOp_eq_of_cone_agree
    (cenv0 cenv1 : ConstEnv) (cone : List Nat)
    (hc : ∀ cid, cid ∈ cone → cenv0 cid = cenv1 cid)
    (slots : Nat → LocalSlot) (op : MirOp) (hin : opInCone cone op) :
    evalMirOp cenv1 slots op = evalMirOp cenv0 slots op := by
  cases op with
  | lit _ => rfl
  | unevalConst cid =>
      dsimp [opInCone] at hin
      dsimp [evalMirOp]
      rw [hc cid hin]
  | copy _ => rfl
  | move _ => rfl

private theorem evalMirStmts_eq_of_cone_agree
    (cenv0 cenv1 : ConstEnv) (rel : RustcRelease) (cone : List Nat)
    (hc : ∀ cid, cid ∈ cone → cenv0 cid = cenv1 cid) :
    ∀ (stmts : List MirStmt) (st : MirV1State),
      stmtsInCone cone stmts →
      evalMirStmts cenv1 rel st stmts = evalMirStmts cenv0 rel st stmts
  | [], _, _ => rfl
  | s :: rest, st, h => by
      have hs : stmtInCone cone s := h.1
      have hrest : stmtsInCone cone rest := h.2
      have hstep : evalMirStmt cenv1 rel st s = evalMirStmt cenv0 rel st s := by
        cases s with
        | nop => rfl
        | storageLive _ => rfl
        | storageDead _ => rfl
        | assignOp dst op =>
            dsimp [stmtInCone] at hs
            dsimp [evalMirStmt]
            rw [evalMirOp_eq_of_cone_agree cenv0 cenv1 cone hc st.slots op hs]
        | bitAndOp dst lhs rhs =>
            dsimp [stmtInCone] at hs
            dsimp [evalMirStmt]
            rw [evalMirOp_eq_of_cone_agree cenv0 cenv1 cone hc st.slots lhs hs.1]
            cases evalMirOp cenv0 st.slots lhs with
            | error e => rfl
            | ok p =>
                dsimp
                rw [evalMirOp_eq_of_cone_agree cenv0 cenv1 cone hc p.2 rhs hs.2]
        | checkedLutLoad _ _ _ => rfl
        | useRefAssign _ _ _ _ => rfl
        | ptrWrite _ _ => rfl
        | ptrRead _ _ => rfl
      dsimp [evalMirStmts]
      rw [hstep]
      cases evalMirStmt cenv0 rel st s with
      | error _ => rfl
      | ok st1 => exact evalMirStmts_eq_of_cone_agree cenv0 cenv1 rel cone hc rest st1 hrest

theorem v1_const_cone_and_profile_cache_preserves_semantics
    (cenv0 cenv1 : ConstEnv) (rel0 rel1 : RustcRelease) (body : MirBody)
    (hcone : stmtsInCone body.constConeIds body.stmts)
    (hkey : soundV1CacheKey cenv0 rel0 body = soundV1CacheKey cenv1 rel1 body)
    (arg1 : BitVec 64) :
    evalMirBody cenv1 rel1 body arg1 = evalMirBody cenv0 rel0 body arg1 := by
  have hrel : rel0 = rel1 := congrArg SoundV1CacheKey.rel hkey
  have hvals : evalConstCone cenv0 body.constConeIds = evalConstCone cenv1 body.constConeIds :=
    congrArg SoundV1CacheKey.constConeVals hkey
  have hc : ∀ cid, cid ∈ body.constConeIds → cenv0 cid = cenv1 cid :=
    evalConstCone_eq_implies_mem_eq body.constConeIds cenv0 cenv1 hvals
  subst hrel
  dsimp [evalMirBody]
  rw [evalMirStmts_eq_of_cone_agree cenv0 cenv1 rel0 body.constConeIds hc body.stmts
    (initV1State body.stmts arg1) hcone]

-- F1-1b certified scalar refinement over MoveToCopy + RemoveStorageMarkers.
noncomputable def isScalarPureStmt : MirStmt → Prop
  | .nop => True
  | .storageLive _ => True
  | .storageDead _ => True
  | .assignOp _ _ => True
  | .bitAndOp _ _ _ => True
  | .checkedLutLoad _ _ _ => True
  | .useRefAssign _ _ _ _ => False
  | .ptrWrite _ _ => False
  | .ptrRead _ _ => False

noncomputable def isScalarPureStmts : List MirStmt → Prop
  | [] => True
  | s :: rest => isScalarPureStmt s ∧ isScalarPureStmts rest

def SlotScalarAgree (sSrc sTgt : LocalSlot) (a : AbsSlot) : Prop :=
  match a with
  | .absInit => ∃ v : BitVec 64, sSrc = .liveScalar v ∧ sTgt = .liveScalar v
  | .absUninit => sSrc = .liveUninit ∧ (sTgt = .liveUninit ∨ ∃ v : BitVec 64, sTgt = .liveScalar v)
  | .absDead => sSrc = .dead ∧ (sTgt = .liveUninit ∨ ∃ v : BitVec 64, sTgt = .liveScalar v)

def EnvScalarAgree (stSrc stTgt : MirV1State) (absEnv : Nat → AbsSlot) : Prop :=
  ∀ k : Nat, SlotScalarAgree (stSrc.slots k) (stTgt.slots k) (absEnv k)

private theorem hasStorageMarker_norm_eq_false (k : Nat) (hk0 : Nat.beq k 0 = false) :
    ∀ stmts : List MirStmt,
      hasStorageMarker k (applyRemoveStorageProg (applyMoveToCopyProg stmts)) = false
  | [] => rfl
  | s :: rest => by
      have hrest := hasStorageMarker_norm_eq_false k hk0 rest
      cases s with
      | nop => exact hrest
      | storageLive loc => exact hrest
      | storageDead loc =>
          dsimp [applyMoveToCopyProg, applyMoveToCopyStmt, applyRemoveStorageProg, applyRemoveStorageStmt]
          cases hloc : Nat.beq loc 0 with
          | true =>
              dsimp [hasStorageMarker]
              rw [hk0]
              exact hrest
          | false => exact hrest
      | assignOp _ _ => exact hrest
      | bitAndOp _ _ _ => exact hrest
      | checkedLutLoad _ _ _ => exact hrest
      | useRefAssign _ _ _ _ => exact hrest
      | ptrWrite _ _ => exact hrest
      | ptrRead _ _ => exact hrest

private theorem envScalarAgree_checkAbsOp
    (cenv : ConstEnv) (stSrc stTgt : MirV1State) (absEnv absEnv1 : Nat → AbsSlot)
    (hagree : EnvScalarAgree stSrc stTgt absEnv)
    (op : MirOp) (hcheck : checkAbsOp absEnv op = some absEnv1) :
    ∃ v : BitVec 64, ∃ slotsSrc1 slotsTgt1 : Nat → LocalSlot,
      evalMirOp cenv stSrc.slots op = .ok (v, slotsSrc1) ∧
      evalMirOp cenv stTgt.slots (demoteMoveOp op) = .ok (v, slotsTgt1) ∧
      EnvScalarAgree { stSrc with slots := slotsSrc1 } { stTgt with slots := slotsTgt1 } absEnv1 := by
  cases op with
  | lit v =>
      dsimp [checkAbsOp] at hcheck
      cases hcheck
      exact ⟨v, stSrc.slots, stTgt.slots, rfl, rfl, hagree⟩
  | unevalConst cid =>
      dsimp [checkAbsOp] at hcheck
      cases hcheck
      exact ⟨cenv cid, stSrc.slots, stTgt.slots, rfl, rfl, hagree⟩
  | copy loc =>
      dsimp [checkAbsOp] at hcheck
      have hk := hagree loc
      cases ha : absEnv loc with
      | absInit =>
          rw [ha] at hcheck hk
          cases hcheck
          rcases hk with ⟨v, hv1, hv2⟩
          dsimp [evalMirOp, demoteMoveOp]
          rw [hv1, hv2]
          exact ⟨v, stSrc.slots, stTgt.slots, rfl, rfl, hagree⟩
      | absUninit => rw [ha] at hcheck; cases hcheck
      | absDead => rw [ha] at hcheck; cases hcheck
  | move loc =>
      dsimp [checkAbsOp] at hcheck
      have hk := hagree loc
      cases ha : absEnv loc with
      | absInit =>
          rw [ha] at hcheck hk
          cases hcheck
          rcases hk with ⟨v, hv1, hv2⟩
          dsimp [evalMirOp, demoteMoveOp]
          rw [hv1, hv2]
          refine ⟨v, setSlot stSrc.slots loc .liveUninit, stTgt.slots, rfl, rfl, ?_⟩
          intro k
          dsimp [setSlot, setAbs]
          cases hkbeq : Nat.beq k loc with
          | false => exact hagree k
          | true =>
              have hkl : k = loc := Nat.eq_of_beq_eq_true hkbeq
              subst hkl
              exact ⟨rfl, Or.inr ⟨v, hv2⟩⟩
      | absUninit => rw [ha] at hcheck; cases hcheck
      | absDead => rw [ha] at hcheck; cases hcheck

private theorem slotScalarAgree_nonDead_tgt
    (sSrc sTgt : LocalSlot) (a : AbsSlot) (hs : SlotScalarAgree sSrc sTgt a)
    (ha : a ≠ .absDead) :
    sSrc ≠ .dead ∧ sTgt ≠ .dead := by
  cases a with
  | absInit =>
      rcases hs with ⟨v, h1, h2⟩
      rw [h1, h2]
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | absUninit =>
      rcases hs with ⟨h1, h2⟩
      rw [h1]
      refine ⟨(fun h => by cases h), ?_⟩
      rcases h2 with h2 | ⟨v, h2⟩
      · rw [h2]; intro h; cases h
      · rw [h2]; intro h; cases h
  | absDead => exact False.elim (ha rfl)

private theorem assign_preserves_envScalarAgree
    (stSrc stTgt : MirV1State) (absEnv : Nat → AbsSlot)
    (hagree : EnvScalarAgree stSrc stTgt absEnv)
    (dst : Nat) (v : BitVec 64) (hne : absEnv dst ≠ .absDead) :
    (match stSrc.slots dst with
     | .dead => V1Outcome.error V1Fault.deadSlotUb
     | _ => V1Outcome.ok { stSrc with slots := setSlot stSrc.slots dst (.liveScalar v) }) =
      V1Outcome.ok { stSrc with slots := setSlot stSrc.slots dst (.liveScalar v) } ∧
    (match stTgt.slots dst with
     | .dead => V1Outcome.error V1Fault.deadSlotUb
     | _ => V1Outcome.ok { stTgt with slots := setSlot stTgt.slots dst (.liveScalar v) }) =
      V1Outcome.ok { stTgt with slots := setSlot stTgt.slots dst (.liveScalar v) } ∧
    EnvScalarAgree
      { stSrc with slots := setSlot stSrc.slots dst (.liveScalar v) }
      { stTgt with slots := setSlot stTgt.slots dst (.liveScalar v) }
      (setAbs absEnv dst .absInit) := by
  have hnd := slotScalarAgree_nonDead_tgt (stSrc.slots dst) (stTgt.slots dst) (absEnv dst) (hagree dst) hne
  refine ⟨?_, ?_, ?_⟩
  · cases h : stSrc.slots dst with
    | dead => exact False.elim (hnd.1 h)
    | liveUninit => rfl
    | liveScalar _ => rfl
    | livePtr _ => rfl
  · cases h : stTgt.slots dst with
    | dead => exact False.elim (hnd.2 h)
    | liveUninit => rfl
    | liveScalar _ => rfl
    | livePtr _ => rfl
  · intro k
    dsimp [setSlot, setAbs]
    cases Nat.beq k dst with
    | true => exact ⟨v, rfl, rfl⟩
    | false => exact hagree k

private def ScalarOutcomeMatch : V1Outcome MirV1State → V1Outcome MirV1State → Prop
  | .ok stSrcF, .ok stTgtF =>
      ∃ v : BitVec 64, stSrcF.slots 0 = .liveScalar v ∧ stTgtF.slots 0 = .liveScalar v
  | .error f1, .error f2 => f1 = f2
  | _, _ => False

private theorem evalMirStmts_scalar_norm_preserves_clean
    (cenv : ConstEnv) (rel : RustcRelease) :
    ∀ (stmts : List MirStmt) (stSrc stTgt : MirV1State) (absEnv : Nat → AbsSlot),
      isScalarPureStmts stmts →
      checkAbsStmts absEnv stmts = true →
      EnvScalarAgree stSrc stTgt absEnv →
      ScalarOutcomeMatch (evalMirStmts cenv rel stSrc stmts)
        (evalMirStmts cenv rel stTgt (applyRemoveStorageProg (applyMoveToCopyProg stmts)))
  | [], stSrc, stTgt, absEnv, _, hcert, hagree => by
      dsimp [checkAbsStmts] at hcert
      have h0 := hagree 0
      cases ha0 : absEnv 0 with
      | absInit =>
          rw [ha0] at h0
          rcases h0 with ⟨v, hv1, hv2⟩
          dsimp [applyMoveToCopyProg, applyRemoveStorageProg, evalMirStmts, ScalarOutcomeMatch]
          exact ⟨v, hv1, hv2⟩
      | absUninit => rw [ha0] at hcert; cases hcert
      | absDead => rw [ha0] at hcert; cases hcert
  | s :: rest, stSrc, stTgt, absEnv, hpure, hcert, hagree => by
      dsimp [checkAbsStmts] at hcert
      have hsPure : isScalarPureStmt s := hpure.1
      have hrestPure : isScalarPureStmts rest := hpure.2
      cases hs : checkAbsStmt absEnv s with
      | none => rw [hs] at hcert; cases hcert
      | some absEnv1 =>
          rw [hs] at hcert
          cases s with
          | nop =>
              dsimp [checkAbsStmt] at hs
              cases hs
              dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
              exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest stSrc stTgt absEnv hrestPure hcert hagree
          | storageLive loc =>
              dsimp [checkAbsStmt] at hs
              cases hs
              dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
              have hagree1 : EnvScalarAgree { stSrc with slots := setSlot stSrc.slots loc .liveUninit }
                  stTgt (setAbs absEnv loc .absUninit) := by
                intro k
                dsimp [setSlot, setAbs]
                cases hkbeq : Nat.beq k loc with
                | false => exact hagree k
                | true =>
                    have hkl : k = loc := Nat.eq_of_beq_eq_true hkbeq
                    subst hkl
                    have hprev := hagree k
                    cases ha : absEnv k with
                    | absInit =>
                        rw [ha] at hprev
                        rcases hprev with ⟨v, _, hv2⟩
                        exact ⟨rfl, Or.inr ⟨v, hv2⟩⟩
                    | absUninit =>
                        rw [ha] at hprev
                        exact ⟨rfl, hprev.2⟩
                    | absDead =>
                        rw [ha] at hprev
                        exact ⟨rfl, hprev.2⟩
              exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ stTgt _ hrestPure hcert hagree1
          | storageDead loc =>
              dsimp [checkAbsStmt] at hs
              cases h0 : Nat.beq loc 0 with
              | true => rw [h0] at hs; cases hs
              | false =>
                  rw [h0] at hs
                  cases hs
                  dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                    applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
                  rw [h0]
                  dsimp
                  have hagree1 : EnvScalarAgree { stSrc with slots := setSlot stSrc.slots loc .dead }
                      stTgt (setAbs absEnv loc .absDead) := by
                    intro k
                    dsimp [setSlot, setAbs]
                    cases hkbeq : Nat.beq k loc with
                    | false => exact hagree k
                    | true =>
                        have hkl : k = loc := Nat.eq_of_beq_eq_true hkbeq
                        subst hkl
                        have hprev := hagree k
                        cases ha : absEnv k with
                        | absInit =>
                            rw [ha] at hprev
                            rcases hprev with ⟨v, _, hv2⟩
                            exact ⟨rfl, Or.inr ⟨v, hv2⟩⟩
                        | absUninit =>
                            rw [ha] at hprev
                            exact ⟨rfl, hprev.2⟩
                        | absDead =>
                            rw [ha] at hprev
                            exact ⟨rfl, hprev.2⟩
                  exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ stTgt _ hrestPure hcert hagree1
          | assignOp dst op =>
              dsimp [checkAbsStmt] at hs
              cases hop : checkAbsOp absEnv op with
              | none => rw [hop] at hs; cases hs
              | some envMid =>
                  rw [hop] at hs
                  dsimp at hs
                  cases hdst : envMid dst with
                  | absDead => rw [hdst] at hs; cases hs
                  | absInit =>
                      rw [hdst] at hs; cases hs
                      rcases envScalarAgree_checkAbsOp cenv stSrc stTgt absEnv envMid hagree op hop with
                        ⟨v, slotsSrc1, slotsTgt1, hev1, hev2, hagreeMid⟩
                      have hne : envMid dst ≠ .absDead := by rw [hdst]; intro h; cases h
                      have hass := assign_preserves_envScalarAgree
                        { stSrc with slots := slotsSrc1 } { stTgt with slots := slotsTgt1 }
                        envMid hagreeMid dst v hne
                      dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                        applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
                      rw [hev1, hev2]
                      dsimp
                      rw [hass.1, hass.2.1]
                      exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ _ _ hrestPure hcert hass.2.2
                  | absUninit =>
                      rw [hdst] at hs; cases hs
                      rcases envScalarAgree_checkAbsOp cenv stSrc stTgt absEnv envMid hagree op hop with
                        ⟨v, slotsSrc1, slotsTgt1, hev1, hev2, hagreeMid⟩
                      have hne : envMid dst ≠ .absDead := by rw [hdst]; intro h; cases h
                      have hass := assign_preserves_envScalarAgree
                        { stSrc with slots := slotsSrc1 } { stTgt with slots := slotsTgt1 }
                        envMid hagreeMid dst v hne
                      dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                        applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
                      rw [hev1, hev2]
                      dsimp
                      rw [hass.1, hass.2.1]
                      exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ _ _ hrestPure hcert hass.2.2
          | bitAndOp dst lhs rhs =>
              dsimp [checkAbsStmt] at hs
              cases hl : checkAbsOp absEnv lhs with
              | none => rw [hl] at hs; cases hs
              | some envMid1 =>
                  rw [hl] at hs
                  dsimp at hs
                  cases hr : checkAbsOp envMid1 rhs with
                  | none => rw [hr] at hs; cases hs
                  | some envMid2 =>
                      rw [hr] at hs
                      dsimp at hs
                      rcases envScalarAgree_checkAbsOp cenv stSrc stTgt absEnv envMid1 hagree lhs hl with
                        ⟨vl, slotsSrc1, slotsTgt1, hevL1, hevL2, hagree1⟩
                      rcases envScalarAgree_checkAbsOp cenv { stSrc with slots := slotsSrc1 }
                        { stTgt with slots := slotsTgt1 } envMid1 envMid2 hagree1 rhs hr with
                        ⟨vr, slotsSrc2, slotsTgt2, hevR1, hevR2, hagree2⟩
                      cases hdst : envMid2 dst with
                      | absDead => rw [hdst] at hs; cases hs
                      | absInit =>
                          rw [hdst] at hs; cases hs
                          have hne : envMid2 dst ≠ .absDead := by rw [hdst]; intro h; cases h
                          have hass := assign_preserves_envScalarAgree
                            { stSrc with slots := slotsSrc2 } { stTgt with slots := slotsTgt2 }
                            envMid2 hagree2 dst (vl &&& vr) hne
                          dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                            applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
                          rw [hevL1, hevL2]
                          dsimp
                          rw [hevR1, hevR2]
                          dsimp
                          rw [hass.1, hass.2.1]
                          exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ _ _ hrestPure hcert hass.2.2
                      | absUninit =>
                          rw [hdst] at hs; cases hs
                          have hne : envMid2 dst ≠ .absDead := by rw [hdst]; intro h; cases h
                          have hass := assign_preserves_envScalarAgree
                            { stSrc with slots := slotsSrc2 } { stTgt with slots := slotsTgt2 }
                            envMid2 hagree2 dst (vl &&& vr) hne
                          dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                            applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
                          rw [hevL1, hevL2]
                          dsimp
                          rw [hevR1, hevR2]
                          dsimp
                          rw [hass.1, hass.2.1]
                          exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ _ _ hrestPure hcert hass.2.2
          | checkedLutLoad dst idxLoc lutLen =>
              dsimp [checkAbsStmt] at hs
              have hidx := hagree idxLoc
              cases haIdx : absEnv idxLoc with
              | absUninit => rw [haIdx] at hs; cases hs
              | absDead => rw [haIdx] at hs; cases hs
              | absInit =>
                  rw [haIdx] at hs hidx
                  dsimp at hs
                  rcases hidx with ⟨idxVal, hidx1, hidx2⟩
                  dsimp [applyMoveToCopyProg, applyRemoveStorageProg, applyMoveToCopyStmt,
                    applyRemoveStorageStmt, evalMirStmts, evalMirStmt]
                  rw [hidx1, hidx2]
                  dsimp
                  cases hcmp : decide (idxVal < lutLen) with
                  | false =>
                      have hnlt : ¬ (idxVal < lutLen) := of_decide_eq_false hcmp
                      simp only [hnlt, ↓reduceIte]
                      exact rfl
                  | true =>
                      have hlt : idxVal < lutLen := of_decide_eq_true hcmp
                      simp only [hlt, ↓reduceIte]
                      cases hdst : absEnv dst with
                      | absDead => rw [hdst] at hs; cases hs
                      | absInit =>
                          rw [hdst] at hs; cases hs
                          have hne : absEnv dst ≠ .absDead := by rw [hdst]; intro h; cases h
                          have hass := assign_preserves_envScalarAgree stSrc stTgt absEnv hagree dst idxVal hne
                          rw [hass.1, hass.2.1]
                          exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ _ _ hrestPure hcert hass.2.2
                      | absUninit =>
                          rw [hdst] at hs; cases hs
                          have hne : absEnv dst ≠ .absDead := by rw [hdst]; intro h; cases h
                          have hass := assign_preserves_envScalarAgree stSrc stTgt absEnv hagree dst idxVal hne
                          rw [hass.1, hass.2.1]
                          exact evalMirStmts_scalar_norm_preserves_clean cenv rel rest _ _ _ hrestPure hcert hass.2.2
          | useRefAssign _ _ _ _ => exact False.elim hsPure
          | ptrWrite _ _ => exact False.elim hsPure
          | ptrRead _ _ => exact False.elim hsPure

theorem v1_certified_f11b_norm_preserves_eval
    (cenv : ConstEnv) (rel : RustcRelease) (body : MirBody)
    (hpure : isScalarPureStmts body.stmts)
    (hcert : checkMirV1Cert body = true)
    (arg1 : BitVec 64) :
    evalMirBody cenv rel (normalizeF11b body) arg1 = evalMirBody cenv rel body arg1 := by
  have hinitAgree : EnvScalarAgree (initV1State body.stmts arg1)
      (initV1State (applyRemoveStorageProg (applyMoveToCopyProg body.stmts)) arg1)
      (initAbsEnv body.stmts) := by
    intro k
    dsimp [initV1State, initV1Slots, initAbsEnv]
    cases hk0 : Nat.beq k 0 with
    | true => exact ⟨rfl, Or.inl rfl⟩
    | false =>
        cases hk1 : Nat.beq k 1 with
        | true => exact ⟨arg1, rfl, rfl⟩
        | false =>
            have hnorm := hasStorageMarker_norm_eq_false k hk0 body.stmts
            rw [hnorm]
            dsimp
            cases hasStorageMarker k body.stmts with
            | true => exact ⟨rfl, Or.inl rfl⟩
            | false => exact ⟨rfl, Or.inl rfl⟩
  have hmatch := evalMirStmts_scalar_norm_preserves_clean cenv rel body.stmts
    (initV1State body.stmts arg1)
    (initV1State (applyRemoveStorageProg (applyMoveToCopyProg body.stmts)) arg1)
    (initAbsEnv body.stmts) hpure hcert hinitAgree
  dsimp [evalMirBody, normalizeF11b]
  cases h1 : evalMirStmts cenv rel (initV1State body.stmts arg1) body.stmts with
  | error f1 =>
      rw [h1] at hmatch
      cases h2 : evalMirStmts cenv rel
        (initV1State (applyRemoveStorageProg (applyMoveToCopyProg body.stmts)) arg1)
        (applyRemoveStorageProg (applyMoveToCopyProg body.stmts)) with
      | ok _ => rw [h2] at hmatch; exact False.elim hmatch
      | error f2 =>
          rw [h2] at hmatch
          dsimp [ScalarOutcomeMatch] at hmatch
          rw [hmatch]
  | ok st1 =>
      rw [h1] at hmatch
      cases h2 : evalMirStmts cenv rel
        (initV1State (applyRemoveStorageProg (applyMoveToCopyProg body.stmts)) arg1)
        (applyRemoveStorageProg (applyMoveToCopyProg body.stmts)) with
      | error _ => rw [h2] at hmatch; exact False.elim hmatch
      | ok st2 =>
          rw [h2] at hmatch
          dsimp [ScalarOutcomeMatch] at hmatch
          rcases hmatch with ⟨v, hv1, hv2⟩
          dsimp
          rw [hv1, hv2]

-- Adversarial Counterexample #1 (Seam V1a):
-- E4_internal_const (miniz_oxide BASE_EXTRA_MASK: 15 -> 31, CID = 7) changes semantics
-- while leaving MIR body text and `naiveBodyOnlyKey` identical!
noncomputable def bodyMinizMaskProbe : MirBody :=
  { numLocals := 3
    stmts :=
      [ .storageLive 2
      , .bitAndOp 2 (.move 1) (.unevalConst 7)
      , .checkedLutLoad 0 2 16#64
      , .storageDead 2
      ]
    constConeIds := [7]
    specHash := 0x1111_2222_3333_4444#64 }

noncomputable def cenvMask15 : ConstEnv := fun cid => if Nat.beq cid 7 then 15#64 else 0#64
noncomputable def cenvMask31 : ConstEnv := fun cid => if Nat.beq cid 7 then 31#64 else 0#64

theorem cex_v1a_unevaluated_const_change_breaks_uncached_cone :
    naiveBodyOnlyKey bodyMinizMaskProbe = naiveBodyOnlyKey bodyMinizMaskProbe ∧
    checkMirV1Cert bodyMinizMaskProbe = true ∧
    evalMirBody cenvMask15 .r1_99_1 bodyMinizMaskProbe 16#64 = .ok 0#64 ∧
    evalMirBody cenvMask15 .r1_99_1 (normalizeF11b bodyMinizMaskProbe) 16#64 = .ok 0#64 ∧
    evalMirBody cenvMask31 .r1_99_1 bodyMinizMaskProbe 16#64 = .error .oobPanic ∧
    soundV1CacheKey cenvMask15 .r1_99_1 bodyMinizMaskProbe ≠
      soundV1CacheKey cenvMask31 .r1_99_1 bodyMinizMaskProbe := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have h15 : (7, 15#64) = (7, 31#64) := by
    injection h with _ hc
    exact List.head_eq_of_cons_eq hc
  have hval : (15#64 : BitVec 64) = 31#64 := congrArg Prod.snd h15
  cases hval

-- Adversarial Counterexample #2 (Seam V1b):
-- Upgrading rustc 1.96.0 -> 1.99.1 turns implicit `copy (*_1).0` (without `no_retag copy`)
-- into `WithRetag::Yes`, creating a child tag disabled by a parent write -> `.tbUb`!
-- Meanwhile, uncertified MoveToCopy (`_2 = move _1; _3 = copy _1`) masks `.useAfterMoveUb`.
noncomputable def bodyRefProjWithoutNoRetag : MirBody :=
  { numLocals := 3
    stmts :=
      [ .storageLive 2
      , .useRefAssign 2 1 false false
      , .ptrWrite 1 77#64
      , .ptrRead 0 2
      , .storageDead 2
      ]
    constConeIds := []
    specHash := 0x2222_3333_4444_5555#64 }

noncomputable def bodyRefProjWithNoRetag : MirBody :=
  { numLocals := 3
    stmts :=
      [ .storageLive 2
      , .useRefAssign 2 1 false true
      , .ptrWrite 1 77#64
      , .ptrRead 0 2
      , .storageDead 2
      ]
    constConeIds := []
    specHash := 0x2222_3333_4444_5555#64 }

noncomputable def bodyScalarUseAfterMove : MirBody :=
  { numLocals := 3
    stmts :=
      [ .storageLive 2
      , .assignOp 2 (.move 1)
      , .assignOp 0 (.copy 1)
      , .storageDead 2
      ]
    constConeIds := []
    specHash := 0x3333_4444_5555_6666#64 }

theorem cex_v1b_rustc_196_to_199_retag_drift_and_movetocopy_ub :
    evalMirRefBody cenvMask15 .r1_96_0 bodyRefProjWithoutNoRetag 10#64 = .ok 77#64 ∧
    evalMirRefBody cenvMask15 .r1_99_1 bodyRefProjWithoutNoRetag 10#64 = .error .tbUb ∧
    evalMirRefBody cenvMask15 .r1_99_1 bodyRefProjWithNoRetag 10#64 = .ok 77#64 ∧
    soundV1CacheKey cenvMask15 .r1_96_0 bodyRefProjWithoutNoRetag ≠
      soundV1CacheKey cenvMask15 .r1_99_1 bodyRefProjWithoutNoRetag ∧
    checkMirV1Cert bodyScalarUseAfterMove = false ∧
    evalMirBody cenvMask15 .r1_99_1 bodyScalarUseAfterMove 9#64 = .error .useAfterMoveUb ∧
    evalMirBody cenvMask15 .r1_99_1 (normalizeF11b bodyScalarUseAfterMove) 9#64 = .ok 9#64 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro h
  cases h


/-! ## Section 2: Seam V2 (`F1-2` Tree Borrows Partial SROA × `E2-6` Multi-Target `FnAbi` Drift × `E2-9` Atomic Lowering) -/

inductive TargetTriple where
  | x86_64_linux
  | x86_64_win_msvc
  | aarch64_linux
  | i686_win_msvc
  deriving DecidableEq

inductive CallConv where
  | rustCc
  | cCc
  | vectorcallCc
  deriving DecidableEq

inductive AbiSigKind where
  | simdF32x4
  | nonReprCZstThenMutRef
  | vecHfa4
  | hybridPairStruct (hasUnsafeCell : Bool)
  deriving DecidableEq

inductive PassMode where
  | ignoreZst
  | directVecReg
  | pairScalarRegs
  | indirectHiddenPtr (llvmReadonly : Bool)
  deriving DecidableEq

structure AbiDescriptor where
  passMode : PassMode
  symDecorationBytes : Option Nat
  deriving DecidableEq

noncomputable def classifyFnAbi (rel : RustcRelease) (tgt : TargetTriple)
    (cc : CallConv) (sig : AbiSigKind) : AbiDescriptor :=
  match sig with
  | .simdF32x4 =>
      match tgt, rel with
      | .x86_64_linux, .r1_96_0 => ⟨.indirectHiddenPtr false, none⟩
      | .x86_64_linux, .r1_99_1 => ⟨.indirectHiddenPtr false, none⟩
      | .x86_64_linux, .r1_100_0 => ⟨.directVecReg, none⟩
      | .x86_64_linux, .r1_102_nightly => ⟨.directVecReg, none⟩
      | .x86_64_win_msvc, .r1_96_0 => ⟨.indirectHiddenPtr false, none⟩
      | .x86_64_win_msvc, .r1_99_1 => ⟨.indirectHiddenPtr false, none⟩
      | .x86_64_win_msvc, .r1_100_0 => ⟨.directVecReg, none⟩
      | .x86_64_win_msvc, .r1_102_nightly => ⟨.directVecReg, none⟩
      | .i686_win_msvc, .r1_96_0 => ⟨.indirectHiddenPtr false, none⟩
      | .i686_win_msvc, .r1_99_1 => ⟨.indirectHiddenPtr false, none⟩
      | .i686_win_msvc, .r1_100_0 => ⟨.directVecReg, none⟩
      | .i686_win_msvc, .r1_102_nightly => ⟨.directVecReg, none⟩
      | .aarch64_linux, .r1_102_nightly => ⟨.directVecReg, none⟩
      | .aarch64_linux, _ => ⟨.indirectHiddenPtr false, none⟩
  | .nonReprCZstThenMutRef =>
      match tgt, cc, rel with
      | .x86_64_win_msvc, .cCc, .r1_102_nightly => ⟨.ignoreZst, none⟩
      | .x86_64_win_msvc, .cCc, _ => ⟨.indirectHiddenPtr false, none⟩
      | _, _, _ => ⟨.ignoreZst, none⟩
  | .vecHfa4 =>
      match tgt, cc, rel with
      | .x86_64_linux, .vectorcallCc, .r1_102_nightly => ⟨.indirectHiddenPtr false, some 24⟩
      | .x86_64_linux, .vectorcallCc, _ => ⟨.indirectHiddenPtr false, some 16⟩
      | .x86_64_win_msvc, .vectorcallCc, .r1_102_nightly => ⟨.indirectHiddenPtr false, some 24⟩
      | .x86_64_win_msvc, .vectorcallCc, _ => ⟨.indirectHiddenPtr false, some 16⟩
      | _, _, _ => ⟨.indirectHiddenPtr false, none⟩
  | .hybridPairStruct hasUnsafeCell =>
      ⟨.indirectHiddenPtr (!hasUnsafeCell), none⟩

noncomputable def isIndirectReadonly : PassMode → Bool
  | .indirectHiddenPtr ro => ro
  | _ => false

noncomputable def checkAbiLinkCompat
    (callerRel calleeRel : RustcRelease)
    (callerTgt calleeTgt : TargetTriple)
    (callerCc calleeCc : CallConv)
    (sig : AbiSigKind)
    (callerDesc calleeDesc : AbiDescriptor)
    (hasUnsafeCell : Bool)
    (calleePerformsAtomicWrite : Bool)
    (sroaWriteThrough : Bool) : Bool :=
  decide (callerRel = calleeRel) &&
  decide (callerTgt = calleeTgt) &&
  decide (callerCc = calleeCc) &&
  decide (callerDesc = classifyFnAbi callerRel callerTgt callerCc sig) &&
  decide (calleeDesc = classifyFnAbi calleeRel calleeTgt calleeCc sig) &&
  decide (callerDesc = calleeDesc) &&
  !(calleePerformsAtomicWrite && !hasUnsafeCell) &&
  !(calleePerformsAtomicWrite && isIndirectReadonly callerDesc.passMode) &&
  !(calleePerformsAtomicWrite && isIndirectReadonly calleeDesc.passMode) &&
  (match callerDesc.passMode with
   | .indirectHiddenPtr _ => sroaWriteThrough
   | _ => true)

inductive V2Fault where
  | abiMismatchFault
  | linkerSymbolMismatch
  | badAbiPtrDeref
  | llvmReadonlyUb
  | staleSroaCopy
  deriving DecidableEq

inductive V2Outcome (α : Type) where
  | ok (val : α)
  | error (f : V2Fault)
  deriving DecidableEq

noncomputable def evalCrossUnitAbiCall
    (callerDesc calleeDesc : AbiDescriptor)
    (sig : AbiSigKind)
    (callerArgVal : BitVec 64)
    (calleePerformsAtomicWrite : Bool)
    (sroaWriteThrough : Bool) : V2Outcome (BitVec 64) :=
  if callerDesc.symDecorationBytes ≠ calleeDesc.symDecorationBytes then
    .error .linkerSymbolMismatch
  else
    match sig, callerDesc.passMode, calleeDesc.passMode with
    | .nonReprCZstThenMutRef, .indirectHiddenPtr _, .ignoreZst =>
        -- Caller placed synthetic ZST ptr in %rcx and &mut u64 in %rdx; callee reads %rcx as ptr!
        .error .badAbiPtrDeref
    | .nonReprCZstThenMutRef, .ignoreZst, .indirectHiddenPtr _ =>
        .error .badAbiPtrDeref
    | .hybridPairStruct _, .indirectHiddenPtr roCaller, .indirectHiddenPtr roCallee =>
        if !sroaWriteThrough then
          .error .staleSroaCopy
        else if calleePerformsAtomicWrite && (roCaller || roCallee) then
          .error .llvmReadonlyUb
        else
          .ok callerArgVal
    | _, m1, m2 =>
        if m1 = m2 then .ok callerArgVal else .error .abiMismatchFault

theorem v2_epoch_pinned_freeze_aware_abi_call_sound
    (callerRel calleeRel : RustcRelease)
    (callerTgt calleeTgt : TargetTriple)
    (callerCc calleeCc : CallConv)
    (sig : AbiSigKind)
    (callerDesc calleeDesc : AbiDescriptor)
    (hasUnsafeCell calleePerformsAtomicWrite sroaWriteThrough : Bool)
    (hSigFreeze : match sig with
      | .hybridPairStruct uc => uc = hasUnsafeCell
      | _ => True)
    (hCompat : checkAbiLinkCompat callerRel calleeRel callerTgt calleeTgt
      callerCc calleeCc sig callerDesc calleeDesc hasUnsafeCell
      calleePerformsAtomicWrite sroaWriteThrough = true)
    (argVal : BitVec 64) :
    evalCrossUnitAbiCall callerDesc calleeDesc sig argVal
      calleePerformsAtomicWrite sroaWriteThrough = .ok argVal := by
  dsimp [checkAbiLinkCompat] at hCompat
  cases hrel : decide (callerRel = calleeRel) <;> rw [hrel] at hCompat
  · cases hCompat
  cases htgt : decide (callerTgt = calleeTgt) <;> rw [htgt] at hCompat
  · cases hCompat
  cases hcc : decide (callerCc = calleeCc) <;> rw [hcc] at hCompat
  · cases hCompat
  cases hcd : decide (callerDesc = classifyFnAbi callerRel callerTgt callerCc sig) <;> rw [hcd] at hCompat
  · cases hCompat
  cases hkd : decide (calleeDesc = classifyFnAbi calleeRel calleeTgt calleeCc sig) <;> rw [hkd] at hCompat
  · cases hCompat
  cases heq : decide (callerDesc = calleeDesc) <;> rw [heq] at hCompat
  · cases hCompat
  have heqDesc : callerDesc = calleeDesc := of_decide_eq_true heq
  have hrelEq : callerRel = calleeRel := of_decide_eq_true hrel
  have htgtEq : callerTgt = calleeTgt := of_decide_eq_true htgt
  have hccEq : callerCc = calleeCc := of_decide_eq_true hcc
  have hcallerClass : callerDesc = classifyFnAbi callerRel callerTgt callerCc sig :=
    of_decide_eq_true hcd
  subst heqDesc hrelEq htgtEq hccEq
  dsimp [evalCrossUnitAbiCall]
  simp only [not_true_eq_false, ↓reduceIte]
  cases sig with
  | simdF32x4 =>
      dsimp
      simp only [↓reduceIte]
  | nonReprCZstThenMutRef =>
      cases callerDesc.passMode with
      | ignoreZst => rfl
      | directVecReg => rfl
      | pairScalarRegs => rfl
      | indirectHiddenPtr _ => dsimp; simp only [↓reduceIte]
  | vecHfa4 =>
      dsimp
      simp only [↓reduceIte]
  | hybridPairStruct uc =>
      dsimp at hSigFreeze
      rw [hSigFreeze] at hcallerClass ⊢
      rw [hcallerClass] at hCompat ⊢
      dsimp [classifyFnAbi, isIndirectReadonly] at hCompat ⊢
      cases hasUnsafeCell <;> cases calleePerformsAtomicWrite <;> cases sroaWriteThrough <;>
        simp at hCompat ⊢

-- Adversarial Counterexample #3 (Seam V2a): All 4 E2-6 cross-release / cross-target ABI breaks.
theorem cex_v2a_cross_release_and_cross_target_fnabi_breaks :
    -- (1) x86_64_linux simdF32x4 1.99.1 -> 1.100.0 (sret -> direct xmm0)
    evalCrossUnitAbiCall
      (classifyFnAbi .r1_99_1 .x86_64_linux .rustCc .simdF32x4)
      (classifyFnAbi .r1_100_0 .x86_64_linux .rustCc .simdF32x4)
      .simdF32x4 42#64 false true = .error .abiMismatchFault ∧
    -- (2) 1.100.0 staggered x86_64 vs aarch64 divergence
    classifyFnAbi .r1_100_0 .x86_64_linux .rustCc .simdF32x4 ≠
      classifyFnAbi .r1_100_0 .aarch64_linux .rustCc .simdF32x4 ∧
    -- (3) Win64 extern "C" non-#[repr(C)] ZST 1.100.0 -> 1.102_nightly (%rcx/%rdx shift)
    evalCrossUnitAbiCall
      (classifyFnAbi .r1_100_0 .x86_64_win_msvc .cCc .nonReprCZstThenMutRef)
      (classifyFnAbi .r1_102_nightly .x86_64_win_msvc .cCc .nonReprCZstThenMutRef)
      .nonReprCZstThenMutRef 42#64 false true = .error .badAbiPtrDeref ∧
    -- (4) x86_64 vectorcall abi_vec_hfa4@@16 -> @@24 linker break
    evalCrossUnitAbiCall
      (classifyFnAbi .r1_100_0 .x86_64_linux .vectorcallCc .vecHfa4)
      (classifyFnAbi .r1_102_nightly .x86_64_linux .vectorcallCc .vecHfa4)
      .vecHfa4 42#64 false true = .error .linkerSymbolMismatch := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro h
  cases h

-- Adversarial Counterexample #4 (Seam V2b):
-- (a) Marking indirect copy of hybrid struct containing Atomic/UnsafeCell `readonly` causes llvmReadonlyUb;
-- (b) Unflushed PartialSROA register before indirectHiddenPtr call causes staleSroaCopy.
theorem cex_v2b_indirect_copy_readonly_on_atomic_and_unflushed_sroa_unsound :
    let descWrongRo : AbiDescriptor := ⟨.indirectHiddenPtr true, none⟩
    let descSound   : AbiDescriptor := classifyFnAbi .r1_99_1 .x86_64_linux .rustCc (.hybridPairStruct true)
    evalCrossUnitAbiCall descWrongRo descWrongRo (.hybridPairStruct true) 99#64 true true =
      .error .llvmReadonlyUb ∧
    evalCrossUnitAbiCall descSound descSound (.hybridPairStruct true) 99#64 true false =
      .error .staleSroaCopy ∧
    checkAbiLinkCompat .r1_99_1 .r1_99_1 .x86_64_linux .x86_64_linux .rustCc .rustCc
      (.hybridPairStruct true) descSound descSound true true false = false ∧
    evalCrossUnitAbiCall descSound descSound (.hybridPairStruct true) 99#64 true true =
      .ok 99#64 := by
  exact ⟨rfl, rfl, rfl, rfl⟩


/-! ## Section 3: Seam V3 (`E2-7` ZMM512 Spill Cliff × `r2` `vzeroupper` + Probes × `E2-9` Red-Zone `SeqCst`) -/

inductive SimdWidthPolicy where
  | prefer256
  | fullZmm512
  deriving DecidableEq

inductive RedZoneMode where
  | redZoneAllowed
  | noRedZone
  deriving DecidableEq

inductive FenceDisp where
  | dispNeg64
  | dispZeroRsp
  deriving DecidableEq

inductive ProbeStep where
  | subRsp (bytes : Nat)
  | touchRsp
  deriving DecidableEq

structure BackendBlockSpec where
  widthPol : SimdWidthPolicy
  spilledSimdRegs : Nat
  calleeLocalBytes : Nat
  probeProg : List ProbeStep
  usesZmm0To15Upper : Bool
  emitsPreCallVZeroUpper : Bool
  callsLegacyOrUnwind : Bool
  hasOutlinedThunkCall : Bool
  outlinedThunkShift : Nat
  usesRedZoneSpill : Bool
  seqCstFence : Option FenceDisp
  retAddrSlotVal : BitVec 64

noncomputable def spillBytesPerReg : SimdWidthPolicy → Nat
  | .prefer256 => 32
  | .fullZmm512 => 64

noncomputable def totalSpillFrameBytes (pol : SimdWidthPolicy) (spilledRegs localBytes : Nat) : Nat :=
  spilledRegs * spillBytesPerReg pol + localBytes

noncomputable def sumSubRsp : List ProbeStep → Nat
  | [] => 0
  | .subRsp k :: rest => k + sumSubRsp rest
  | .touchRsp :: rest => sumSubRsp rest

noncomputable def checkProbeStepsAux (pending4k : Bool) : List ProbeStep → Bool
  | [] => !pending4k
  | .touchRsp :: rest => checkProbeStepsAux false rest
  | .subRsp k :: rest =>
      if pending4k then false
      else if decide (k ≤ 4096) then
        let needTouch := decide (k = 4096) && !(rest.isEmpty)
        checkProbeStepsAux needTouch rest
      else false

noncomputable def checkProbeProg (prog : List ProbeStep) (frameBytes : Nat) : Bool :=
  checkProbeStepsAux false prog && decide (sumSubRsp prog = frameBytes)

noncomputable def checkRedZoneFence (rzMode : RedZoneMode) (hasThunk : Bool) :
    Option FenceDisp → Bool
  | none => true
  | some .dispZeroRsp => true
  | some .dispNeg64 =>
      match rzMode with
      | .noRedZone => false
      | .redZoneAllowed => !hasThunk

noncomputable def checkBackendV3 (rzMode : RedZoneMode) (spec : BackendBlockSpec) : Bool :=
  let fbytes := totalSpillFrameBytes spec.widthPol spec.spilledSimdRegs spec.calleeLocalBytes
  checkProbeProg spec.probeProg fbytes &&
  (!(spec.usesZmm0To15Upper && spec.callsLegacyOrUnwind) || spec.emitsPreCallVZeroUpper) &&
  (!spec.hasOutlinedThunkCall || (Nat.beq spec.outlinedThunkShift 16 && !spec.usesRedZoneSpill)) &&
  checkRedZoneFence rzMode spec.hasOutlinedThunkCall spec.seqCstFence

inductive V3Fault where
  | guardPageSkipped
  | probeMissingTouch
  | frameSizeMismatch
  | dirtyAvxUpperAtBoundary
  | misalignedThunkRsp
  | redZoneClobberedByThunk
  | noRedZoneViolation
  deriving DecidableEq

inductive V3Outcome (α : Type) where
  | ok (val : α)
  | error (f : V3Fault)
  deriving DecidableEq

noncomputable def runProbes (pending4k : Bool) (accSp : Nat) :
    List ProbeStep → V3Outcome Nat
  | [] =>
      if pending4k then .error .probeMissingTouch else .ok accSp
  | .touchRsp :: rest =>
      runProbes false accSp rest
  | .subRsp k :: rest =>
      if pending4k then .error .probeMissingTouch
      else if decide (k ≤ 4096) then
        let needTouch := decide (k = 4096) && !(rest.isEmpty)
        runProbes needTouch (accSp + k) rest
      else .error .guardPageSkipped

noncomputable def evalBackendV3 (rzMode : RedZoneMode) (spec : BackendBlockSpec) :
    V3Outcome (BitVec 64 × Nat) :=
  let fbytes := totalSpillFrameBytes spec.widthPol spec.spilledSimdRegs spec.calleeLocalBytes
  match runProbes false 0 spec.probeProg with
  | .error e => .error e
  | .ok probedBytes =>
      if !decide (probedBytes = fbytes) then
        .error .frameSizeMismatch
      else if spec.usesZmm0To15Upper && spec.callsLegacyOrUnwind && !spec.emitsPreCallVZeroUpper then
        .error .dirtyAvxUpperAtBoundary
      else if spec.hasOutlinedThunkCall && !Nat.beq spec.outlinedThunkShift 16 then
        .error .misalignedThunkRsp
      else if spec.hasOutlinedThunkCall && spec.usesRedZoneSpill then
        .error .redZoneClobberedByThunk
      else
        match spec.seqCstFence with
        | none => .ok (spec.retAddrSlotVal, probedBytes)
        | some .dispZeroRsp =>
            -- `lock orl $0, (%rsp)` reads/writes top-of-stack without changing value (`x ||| 0 = x`).
            .ok (spec.retAddrSlotVal ||| 0#64, probedBytes)
        | some .dispNeg64 =>
            match rzMode with
            | .noRedZone => .error .noRedZoneViolation
            | .redZoneAllowed =>
                if spec.hasOutlinedThunkCall then .error .redZoneClobberedByThunk
                else .ok (spec.retAddrSlotVal ||| 0#64, probedBytes)

private theorem runProbes_of_checkAux :
    ∀ (prog : List ProbeStep) (pending : Bool) (acc : Nat),
      checkProbeStepsAux pending prog = true →
      runProbes pending acc prog = .ok (acc + sumSubRsp prog)
  | [], false, acc, _ => rfl
  | [], true, acc, h => by dsimp [checkProbeStepsAux] at h; cases h
  | .touchRsp :: rest, _, acc, h => by
      dsimp [checkProbeStepsAux] at h
      dsimp [runProbes, sumSubRsp]
      exact runProbes_of_checkAux rest false acc h
  | .subRsp k :: rest, true, acc, h => by
      dsimp [checkProbeStepsAux] at h
      cases h
  | .subRsp k :: rest, false, acc, h => by
      dsimp [checkProbeStepsAux] at h
      cases hle : decide (k ≤ 4096) with
      | false => rw [hle] at h; cases h
      | true =>
          rw [hle] at h
          dsimp [runProbes, sumSubRsp]
          rw [hle]
          dsimp
          have ih := runProbes_of_checkAux rest (decide (k = 4096) && !(rest.isEmpty)) (acc + k) h
          rw [ih, Nat.add_assoc]

theorem v3_backend_zmm512_probe_vzeroupper_redzone_sound
    (rzMode : RedZoneMode) (spec : BackendBlockSpec)
    (hcheck : checkBackendV3 rzMode spec = true) :
    evalBackendV3 rzMode spec =
      .ok (spec.retAddrSlotVal, totalSpillFrameBytes spec.widthPol spec.spilledSimdRegs spec.calleeLocalBytes) := by
  dsimp [checkBackendV3, checkProbeProg] at hcheck
  cases hpr : checkProbeStepsAux false spec.probeProg with
  | false => rw [hpr] at hcheck; cases hcheck
  | true =>
      rw [hpr] at hcheck
      cases hsum : decide (sumSubRsp spec.probeProg =
        totalSpillFrameBytes spec.widthPol spec.spilledSimdRegs spec.calleeLocalBytes) with
      | false => rw [hsum] at hcheck; cases hcheck
      | true =>
          rw [hsum] at hcheck
          have hrun := runProbes_of_checkAux spec.probeProg false 0 hpr
          rw [Nat.zero_add] at hrun
          have hsumEq : sumSubRsp spec.probeProg =
              totalSpillFrameBytes spec.widthPol spec.spilledSimdRegs spec.calleeLocalBytes :=
            of_decide_eq_true hsum
          dsimp [evalBackendV3]
          rw [hrun]
          dsimp
          rw [hsumEq]
          simp only [decide_true, Bool.not_true]
          have hvzu : (spec.usesZmm0To15Upper && spec.callsLegacyOrUnwind && !spec.emitsPreCallVZeroUpper) = false := by
            cases hu : spec.usesZmm0To15Upper <;> cases hc : spec.callsLegacyOrUnwind <;>
              cases hv : spec.emitsPreCallVZeroUpper <;>
              first | rfl | (rw [hu, hc, hv] at hcheck; simp at hcheck)
          rw [hvzu]
          dsimp
          have hthunk1 : (spec.hasOutlinedThunkCall && !Nat.beq spec.outlinedThunkShift 16) = false := by
            cases ht : spec.hasOutlinedThunkCall <;> cases hs : Nat.beq spec.outlinedThunkShift 16 <;>
              first | rfl | (rw [ht, hs] at hcheck; simp at hcheck)
          rw [hthunk1]
          dsimp
          have hthunk2 : (spec.hasOutlinedThunkCall && spec.usesRedZoneSpill) = false := by
            cases ht : spec.hasOutlinedThunkCall <;> cases hur : spec.usesRedZoneSpill <;>
              first | rfl | (rw [ht, hur] at hcheck; simp at hcheck)
          rw [hthunk2]
          dsimp
          cases hfence : spec.seqCstFence with
          | none => rfl
          | some d =>
              cases d with
              | dispZeroRsp =>
                  dsimp
                  rw [BitVec.or_zero]
              | dispNeg64 =>
                  cases hrz : rzMode with
                  | noRedZone =>
                      rw [hfence, hrz] at hcheck
                      simp [checkRedZoneFence] at hcheck
                  | redZoneAllowed =>
                      cases ht : spec.hasOutlinedThunkCall with
                      | true =>
                          rw [hfence, hrz, ht] at hcheck
                          simp [checkRedZoneFence] at hcheck
                      | false =>
                          dsimp
                          rw [BitVec.or_zero]

noncomputable def validZmm512NoRedZoneSpec (retVal : BitVec 64) : BackendBlockSpec :=
  { widthPol := .fullZmm512
    spilledSimdRegs := 32
    calleeLocalBytes := 2112
    probeProg := [.subRsp 4096, .touchRsp, .subRsp 64]
    usesZmm0To15Upper := true
    emitsPreCallVZeroUpper := true
    callsLegacyOrUnwind := true
    hasOutlinedThunkCall := true
    outlinedThunkShift := 16
    usesRedZoneSpill := false
    seqCstFence := some .dispZeroRsp
    retAddrSlotVal := retVal }

theorem v3_noredzone_rejects_neg64_and_admits_zeroRsp (retVal : BitVec 64) :
    checkBackendV3 .noRedZone { validZmm512NoRedZoneSpec retVal with seqCstFence := some .dispNeg64 } = false ∧
    checkBackendV3 .noRedZone (validZmm512NoRedZoneSpec retVal) = true := by
  dsimp [checkBackendV3, checkProbeProg, totalSpillFrameBytes, spillBytesPerReg,
    validZmm512NoRedZoneSpec, checkProbeStepsAux, sumSubRsp, checkRedZoneFence]
  exact ⟨rfl, rfl⟩

-- Adversarial Counterexample #5 (Seam V3a):
-- 32 spilled SIMD regs + 2,112 B locals = 3,136 B under prefer-256-bit (fits < 4096 B),
-- but expands to 4,160 B under fullZmm512 -> unsplit prologue skips guard page!
-- Also omitting vzeroupper on ZMM512 leaks upper bits -> dirtyAvxUpperAtBoundary.
theorem cex_v3a_zmm512_spill_crosses_4096_cliff_and_leaks_zmmHi :
    let specPref256 : BackendBlockSpec :=
      { validZmm512NoRedZoneSpec 99#64 with
        widthPol := .prefer256, probeProg := [.subRsp 3136] }
    let specZmmUnsplit : BackendBlockSpec :=
      { validZmm512NoRedZoneSpec 99#64 with
        widthPol := .fullZmm512, probeProg := [.subRsp 4160] }
    let specZmmNoVzu : BackendBlockSpec :=
      { validZmm512NoRedZoneSpec 99#64 with
        emitsPreCallVZeroUpper := false }
    checkBackendV3 .noRedZone specPref256 = true ∧
    totalSpillFrameBytes .prefer256 32 2112 = 3136 ∧
    totalSpillFrameBytes .fullZmm512 32 2112 = 4160 ∧
    checkBackendV3 .noRedZone specZmmUnsplit = false ∧
    evalBackendV3 .noRedZone specZmmUnsplit = .error .guardPageSkipped ∧
    checkBackendV3 .noRedZone specZmmNoVzu = false ∧
    evalBackendV3 .noRedZone specZmmNoVzu = .error .dirtyAvxUpperAtBoundary := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Adversarial Counterexample #6 (Seam V3b):
-- (1) `lock orl $0, -64(%rsp)` fails under `-C no-redzone=yes`, whereas `lock orl $0, (%rsp)` succeeds;
-- (2) Using the red zone in a function that outlines a throwing cold thunk corrupts red-zone slots.
theorem cex_v3b_redzone_fence_corrupts_noredzone_and_outlined_leaf :
    let specNeg64 := { validZmm512NoRedZoneSpec 0xABCD#64 with
      hasOutlinedThunkCall := false, seqCstFence := some .dispNeg64 }
    let specZeroRsp := { validZmm512NoRedZoneSpec 0xABCD#64 with
      hasOutlinedThunkCall := false, seqCstFence := some .dispZeroRsp }
    let specRzOutlined := { validZmm512NoRedZoneSpec 0xABCD#64 with
      usesRedZoneSpill := true, seqCstFence := some .dispNeg64 }
    evalBackendV3 .noRedZone specNeg64 = .error .noRedZoneViolation ∧
    evalBackendV3 .noRedZone specZeroRsp = .ok (0xABCD#64, 4160) ∧
    checkBackendV3 .redZoneAllowed specRzOutlined = false ∧
    evalBackendV3 .redZoneAllowed specRzOutlined = .error .redZoneClobberedByThunk := by
  exact ⟨rfl, rfl, rfl, rfl⟩


/-! ## Section 4: Seam V4 (`7176fdd92a` `libleanshared.so` + `$ORIGIN/../lib` `DT_RUNPATH` × `E2-2` `nanoda_bin` × `ktrust`) -/

inductive ElfDep where
  | libInitShared
  | libLeanShared1
  | libLeanShared2
  | libLeanSharedMain
  | libcSo6
  deriving DecidableEq

inductive SearchDir where
  | originParentLib
  | originParentLibLean
  | systemLib
  deriving DecidableEq

structure ToolchainFs where
  launcherDigest : BitVec 64
  oleanManifestDigest : BitVec 64
  lookupSo : SearchDir → ElfDep → Option (BitVec 64)

noncomputable def resolveElfDep (fs : ToolchainFs) (dep : ElfDep) : Option (BitVec 64) :=
  match fs.lookupSo .originParentLib dep with
  | some d => some d
  | none =>
      match dep with
      | .libcSo6 => fs.lookupSo .systemLib .libcSo6
      | _ =>
          match fs.lookupSo .originParentLibLean dep with
          | some d => some d
          | none => fs.lookupSo .systemLib dep

structure TcbLock where
  launcherDigest : BitVec 64
  oleanManifestDigest : BitVec 64
  expectedDepDigest : ElfDep → BitVec 64
  nanodaStaticDigest : BitVec 64
  pinnedTargetStmtHash : BitVec 64
  allowClassicalChoice : Bool

structure ExportArtifact where
  exporterSoDigest : BitVec 64
  exportedStmtHash : BitVec 64
  usesChoiceAxiom : Bool
  nanodaBinaryDigest : BitVec 64
  nanodaAccepted : Bool

-- Current `joshlf/anneal@c131b320e` `trusted/audit/` check: launcher + `.olean` manifest only.
noncomputable def auditCurrentAnnealLauncherOnly (lock : TcbLock) (fs : ToolchainFs) : Bool :=
  decide (fs.launcherDigest = lock.launcherDigest) &&
  decide (fs.oleanManifestDigest = lock.oleanManifestDigest)

-- Naive fixed-path patch: checks `lib/lean/libleanshared.so` only, ignoring `$ORIGIN/../lib` shadowing.
noncomputable def auditNaiveFixedPathLibLean (lock : TcbLock) (fs : ToolchainFs) : Bool :=
  auditCurrentAnnealLauncherOnly lock fs &&
  decide (fs.lookupSo .originParentLibLean .libLeanSharedMain = some (lock.expectedDepDigest .libLeanSharedMain))

noncomputable def checkOneElfDep (lock : TcbLock) (fs : ToolchainFs) (dep : ElfDep) : Bool :=
  match fs.lookupSo .originParentLib dep with
  | some _ => false
  | none => decide (resolveElfDep fs dep = some (lock.expectedDepDigest dep))

noncomputable def allElfDeps : List ElfDep :=
  [.libInitShared, .libLeanShared1, .libLeanShared2, .libLeanSharedMain, .libcSo6]

noncomputable def checkElfDepList (lock : TcbLock) (fs : ToolchainFs) : List ElfDep → Bool
  | [] => true
  | d :: rest => checkOneElfDep lock fs d && checkElfDepList lock fs rest

noncomputable def checkPrimaryElfClosure (lock : TcbLock) (fs : ToolchainFs) : Bool :=
  auditCurrentAnnealLauncherOnly lock fs &&
  checkElfDepList lock fs allElfDeps

noncomputable def checkDualKernelClosure (lock : TcbLock) (exp : ExportArtifact) : Bool :=
  decide (exp.nanodaBinaryDigest = lock.nanodaStaticDigest) &&
  exp.nanodaAccepted &&
  !(exp.usesChoiceAxiom && !lock.allowClassicalChoice) &&
  decide (exp.exportedStmtHash = lock.pinnedTargetStmtHash)

noncomputable def auditDefenseInDepthTcb (lock : TcbLock) (fs : ToolchainFs) (exp : ExportArtifact) : Bool :=
  checkPrimaryElfClosure lock fs &&
  checkDualKernelClosure lock exp

private theorem checkElfDepList_mem (lock : TcbLock) (fs : ToolchainFs) :
    ∀ (deps : List ElfDep),
      checkElfDepList lock fs deps = true →
      ∀ d, d ∈ deps → resolveElfDep fs d = some (lock.expectedDepDigest d)
  | [], _, d, hmem => by cases hmem
  | x :: xs, h, d, hmem => by
      dsimp [checkElfDepList] at h
      cases hx : checkOneElfDep lock fs x with
      | false => rw [hx] at h; cases h
      | true =>
          rw [hx] at h
          cases hmem with
          | head =>
              dsimp [checkOneElfDep] at hx
              cases hsh : fs.lookupSo .originParentLib x with
              | some _ => rw [hsh] at hx; cases hx
              | none =>
                  rw [hsh] at hx
                  exact of_decide_eq_true hx
          | tail _ hmem' => exact checkElfDepList_mem lock fs xs h d hmem'

theorem v4_closed_tcb_and_pinned_dual_kernel_sound
    (SemanticallyValid : BitVec 64 → Prop)
    (PrimaryGenuineFaithful : ToolchainFs → BitVec 64 → Prop)
    (NanodaGenuineFaithful : ExportArtifact → Prop)
    (lock : TcbLock) (fs : ToolchainFs) (exp : ExportArtifact)
    (hPrimaryFaith :
      (resolveElfDep fs .libLeanSharedMain = some (lock.expectedDepDigest .libLeanSharedMain) ∧
       resolveElfDep fs .libInitShared = some (lock.expectedDepDigest .libInitShared) ∧
       resolveElfDep fs .libLeanShared1 = some (lock.expectedDepDigest .libLeanShared1) ∧
       resolveElfDep fs .libLeanShared2 = some (lock.expectedDepDigest .libLeanShared2) ∧
       resolveElfDep fs .libcSo6 = some (lock.expectedDepDigest .libcSo6) ∧
       fs.launcherDigest = lock.launcherDigest ∧
       fs.oleanManifestDigest = lock.oleanManifestDigest) →
      PrimaryGenuineFaithful fs lock.pinnedTargetStmtHash)
    (hPrimarySound : PrimaryGenuineFaithful fs lock.pinnedTargetStmtHash →
      SemanticallyValid lock.pinnedTargetStmtHash)
    (hNanodaFaith :
      exp.nanodaBinaryDigest = lock.nanodaStaticDigest →
      (!(exp.usesChoiceAxiom && !lock.allowClassicalChoice)) = true →
      NanodaGenuineFaithful exp)
    (hNanodaSound : NanodaGenuineFaithful exp → exp.nanodaAccepted = true →
      SemanticallyValid exp.exportedStmtHash)
    (haudit : auditDefenseInDepthTcb lock fs exp = true) :
    SemanticallyValid lock.pinnedTargetStmtHash ∧
    PrimaryGenuineFaithful fs lock.pinnedTargetStmtHash ∧
    NanodaGenuineFaithful exp := by
  dsimp [auditDefenseInDepthTcb, checkPrimaryElfClosure, checkDualKernelClosure] at haudit
  cases hbase : auditCurrentAnnealLauncherOnly lock fs with
  | false => rw [hbase] at haudit; cases haudit
  | true =>
      rw [hbase] at haudit
      cases hdeps : checkElfDepList lock fs allElfDeps with
      | false => rw [hdeps] at haudit; cases haudit
      | true =>
          rw [hdeps] at haudit
          cases hnb : decide (exp.nanodaBinaryDigest = lock.nanodaStaticDigest) with
          | false => rw [hnb] at haudit; cases haudit
          | true =>
              rw [hnb] at haudit
              cases hna : exp.nanodaAccepted with
              | false => rw [hna] at haudit; cases haudit
              | true =>
                  rw [hna] at haudit
                  cases hch : !(exp.usesChoiceAxiom && !lock.allowClassicalChoice) with
                  | false => rw [hch] at haudit; cases haudit
                  | true =>
                      rw [hch] at haudit
                      have hstmtEq : exp.exportedStmtHash = lock.pinnedTargetStmtHash :=
                        of_decide_eq_true haudit
                      have hm := checkElfDepList_mem lock fs allElfDeps hdeps
                      dsimp [auditCurrentAnnealLauncherOnly] at hbase
                      cases hl1 : decide (fs.launcherDigest = lock.launcherDigest) with
                      | false => rw [hl1] at hbase; cases hbase
                      | true =>
                          rw [hl1] at hbase
                          have hla : fs.launcherDigest = lock.launcherDigest := of_decide_eq_true hl1
                          have hol : fs.oleanManifestDigest = lock.oleanManifestDigest := of_decide_eq_true hbase
                          have hpf : PrimaryGenuineFaithful fs lock.pinnedTargetStmtHash :=
                            hPrimaryFaith
                              ⟨ hm .libLeanSharedMain (by decide)
                              , hm .libInitShared (by decide)
                              , hm .libLeanShared1 (by decide)
                              , hm .libLeanShared2 (by decide)
                              , hm .libcSo6 (by decide)
                              , hla, hol ⟩
                          have hnf : NanodaGenuineFaithful exp :=
                            hNanodaFaith (of_decide_eq_true hnb) hch
                          have hval : SemanticallyValid lock.pinnedTargetStmtHash :=
                            hPrimarySound hpf
                          have hvalDual : SemanticallyValid lock.pinnedTargetStmtHash :=
                            hstmtEq ▸ hNanodaSound hnf hna
                          exact ⟨hval, hpf, hnf⟩

-- Concrete digest constants matching host SHA-256 prefixes (for readable finite verification).
noncomputable def digestLauncher      : BitVec 64 := 0xe8ba_aa71_855a_616d#64
noncomputable def digestOleanMan      : BitVec 64 := 0x2fa0_ec69_2ae7_4051#64
noncomputable def digestInitSo        : BitVec 64 := 0x07f8_c115_6271_ab6e#64
noncomputable def digestLeanShared1   : BitVec 64 := 0x69e9_00c0_25f4_0bf0#64
noncomputable def digestLeanShared2   : BitVec 64 := 0x38d0_a037_50b2_e8d5#64
noncomputable def digestLeanShared    : BitVec 64 := 0x6b30_cc96_3d06_5fc9#64
noncomputable def digestLibc          : BitVec 64 := 0x551b_d390_f2c4_9d09#64
noncomputable def digestTrojanKernel  : BitVec 64 := 0xdead_beef_baad_f00d#64
noncomputable def digestStaticNanoda  : BitVec 64 := 0x0da9_f98f_eadd_0419#64
noncomputable def hashTargetStmt      : BitVec 64 := 0x1234_5678_9abc_def0#64
noncomputable def hashTrivialStmt     : BitVec 64 := 0x0000_0000_0000_0001#64

noncomputable def defaultLock : TcbLock :=
  { launcherDigest := digestLauncher
    oleanManifestDigest := digestOleanMan
    expectedDepDigest := fun d => match d with
      | .libInitShared => digestInitSo
      | .libLeanShared1 => digestLeanShared1
      | .libLeanShared2 => digestLeanShared2
      | .libLeanSharedMain => digestLeanShared
      | .libcSo6 => digestLibc
    nanodaStaticDigest := digestStaticNanoda
    pinnedTargetStmtHash := hashTargetStmt
    allowClassicalChoice := false }

noncomputable def fsGenuine : ToolchainFs :=
  { launcherDigest := digestLauncher
    oleanManifestDigest := digestOleanMan
    lookupSo := fun dir dep => match dir, dep with
      | .originParentLibLean, .libInitShared => some digestInitSo
      | .originParentLibLean, .libLeanShared1 => some digestLeanShared1
      | .originParentLibLean, .libLeanShared2 => some digestLeanShared2
      | .originParentLibLean, .libLeanSharedMain => some digestLeanShared
      | .systemLib, .libcSo6 => some digestLibc
      | _, _ => none }

noncomputable def fsTrojanLibLean : ToolchainFs :=
  { fsGenuine with
    lookupSo := fun dir dep => match dir, dep with
      | .originParentLibLean, .libLeanSharedMain => some digestTrojanKernel
      | _, _ => fsGenuine.lookupSo dir dep }

noncomputable def fsRunpathShadowed : ToolchainFs :=
  { fsGenuine with
    lookupSo := fun dir dep => match dir, dep with
      | .originParentLib, .libLeanSharedMain => some digestTrojanKernel
      | _, _ => fsGenuine.lookupSo dir dep }

-- Adversarial Counterexample #7 (Seam V4a):
-- Launcher-only audit passes when `libleanshared.so` is trojanized;
-- Naive fixed-path `lib/lean/libleanshared.so` check ALSO passes when `$ORIGIN/../lib` shadows it!
theorem cex_v4a_launcher_only_and_runpath_shadow_accept_trojan_kernel :
    auditCurrentAnnealLauncherOnly defaultLock fsTrojanLibLean = true ∧
    resolveElfDep fsTrojanLibLean .libLeanSharedMain = some digestTrojanKernel ∧
    checkPrimaryElfClosure defaultLock fsTrojanLibLean = false ∧
    auditNaiveFixedPathLibLean defaultLock fsRunpathShadowed = true ∧
    resolveElfDep fsRunpathShadowed .libLeanSharedMain = some digestTrojanKernel ∧
    checkPrimaryElfClosure defaultLock fsRunpathShadowed = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Adversarial Counterexample #8 (Seam V4b):
-- (1) Even with genuine static `nanoda_bin`, an unpinned `lean4export` renaming the theorem to a
--     trivial statement succeeds while `checkDualKernelClosure` catches it;
-- (2) Transitive `Classical.choice` (`usesChoiceAxiom = true`) is rejected fail-closed (`E2-2` rc=101).
theorem cex_v4b_unpinned_lean4export_or_unpermitted_choice_breaks_dual_kernel :
    let expRenamed : ExportArtifact :=
      { exporterSoDigest := digestLeanShared
        exportedStmtHash := hashTrivialStmt
        usesChoiceAxiom := false
        nanodaBinaryDigest := digestStaticNanoda
        nanodaAccepted := true }
    let expWithChoice : ExportArtifact :=
      { exporterSoDigest := digestLeanShared
        exportedStmtHash := hashTargetStmt
        usesChoiceAxiom := true
        nanodaBinaryDigest := digestStaticNanoda
        nanodaAccepted := true }
    expRenamed.nanodaAccepted = true ∧
    expRenamed.exportedStmtHash ≠ defaultLock.pinnedTargetStmtHash ∧
    checkDualKernelClosure defaultLock expRenamed = false ∧
    checkDualKernelClosure defaultLock expWithChoice = false := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro h
  cases h


/-! ## Section 5: Seam V5 (Unified End-to-End Vertical Composition, Witness, & Cross-Seam Ablation) -/

structure VerticalCompilationBundle where
  -- Stage 1 (MIR & Incremental Cache)
  mirBody : MirBody
  cenvCached : ConstEnv
  cenvLive : ConstEnv
  relCached : RustcRelease
  relLive : RustcRelease
  argVal : BitVec 64
  -- Stage 2 (FnAbi & Partial SROA / Freeze)
  callerTgt : TargetTriple
  calleeTgt : TargetTriple
  callerCc : CallConv
  calleeCc : CallConv
  abiSig : AbiSigKind
  callerDesc : AbiDescriptor
  calleeDesc : AbiDescriptor
  hasUnsafeCell : Bool
  calleeAtomicWrite : Bool
  sroaWriteThrough : Bool
  -- Stage 3 (Backend ZMM512 / Probes / vzeroupper / RedZone)
  rzMode : RedZoneMode
  backend : BackendBlockSpec
  -- Stage 4 (Dual-Kernel + Transitive ELF TCB)
  tcbLock : TcbLock
  toolchainFs : ToolchainFs
  exportArt : ExportArtifact

noncomputable def targetAllowsRedZone : TargetTriple → Bool
  | .x86_64_linux => true
  | .x86_64_win_msvc => false
  | .aarch64_linux => true
  | .i686_win_msvc => false

noncomputable def checkVerticalPipeline (b : VerticalCompilationBundle) : Bool :=
  -- V1: Incremental cache key binds Const::Unevaluated cone + release + F1-1b cert
  decide (soundV1CacheKey b.cenvCached b.relCached b.mirBody =
          soundV1CacheKey b.cenvLive b.relLive b.mirBody) &&
  checkMirV1Cert b.mirBody &&
  -- V2: ABI epoch pinned to Stage 1's live release + Freeze/UnsafeCell & write-through SROA guard
  checkAbiLinkCompat b.relLive b.relLive b.callerTgt b.calleeTgt b.callerCc b.calleeCc
    b.abiSig b.callerDesc b.calleeDesc b.hasUnsafeCell b.calleeAtomicWrite b.sroaWriteThrough &&
  -- V3: Target red-zone compatibility + ZMM512 spill probe + vzeroupper + 16-B thunk + SeqCst fence
  (!(b.rzMode == .redZoneAllowed) || targetAllowsRedZone b.callerTgt) &&
  checkBackendV3 b.rzMode b.backend &&
  -- V4: Transitive ELF closure + pinned statement hash + external static nanoda gate
  decide (b.mirBody.specHash = b.tcbLock.pinnedTargetStmtHash) &&
  auditDefenseInDepthTcb b.tcbLock b.toolchainFs b.exportArt

inductive VerticalFault where
  | v1Fault (f : V1Fault)
  | v2Fault (f : V2Fault)
  | v3Fault (f : V3Fault)
  | v4UntrustedTcb
  deriving DecidableEq

inductive VerticalOutcome (α : Type) where
  | ok (val : α)
  | error (f : VerticalFault)
  deriving DecidableEq

noncomputable def execVerticalPipeline (b : VerticalCompilationBundle) :
    VerticalOutcome (BitVec 64 × Nat) :=
  match evalMirBody b.cenvLive b.relLive (normalizeF11b b.mirBody) b.argVal with
  | .error f1 => .error (.v1Fault f1)
  | .ok v1 =>
      match evalCrossUnitAbiCall b.callerDesc b.calleeDesc b.abiSig v1
          b.calleeAtomicWrite b.sroaWriteThrough with
      | .error f2 => .error (.v2Fault f2)
      | .ok v2 =>
          match evalBackendV3 b.rzMode { b.backend with retAddrSlotVal := v2 } with
          | .error f3 => .error (.v3Fault f3)
          | .ok res3 =>
              if auditDefenseInDepthTcb b.tcbLock b.toolchainFs b.exportArt then
                .ok res3
              else
                .error .v4UntrustedTcb

-- Master End-to-End Vertical Composition Theorem (Seam V5).
theorem v5_unified_vertical_seam_composition_sound
    (SemanticallyValid : BitVec 64 → Prop)
    (PrimaryGenuineFaithful : ToolchainFs → BitVec 64 → Prop)
    (NanodaGenuineFaithful : ExportArtifact → Prop)
    (b : VerticalCompilationBundle)
    (hScalarPure : isScalarPureStmts b.mirBody.stmts)
    (hCone : stmtsInCone b.mirBody.constConeIds b.mirBody.stmts)
    (hSigFreeze : match b.abiSig with
      | .hybridPairStruct uc => uc = b.hasUnsafeCell
      | _ => True)
    (hPrimaryFaith :
      (resolveElfDep b.toolchainFs .libLeanSharedMain = some (b.tcbLock.expectedDepDigest .libLeanSharedMain) ∧
       resolveElfDep b.toolchainFs .libInitShared = some (b.tcbLock.expectedDepDigest .libInitShared) ∧
       resolveElfDep b.toolchainFs .libLeanShared1 = some (b.tcbLock.expectedDepDigest .libLeanShared1) ∧
       resolveElfDep b.toolchainFs .libLeanShared2 = some (b.tcbLock.expectedDepDigest .libLeanShared2) ∧
       resolveElfDep b.toolchainFs .libcSo6 = some (b.tcbLock.expectedDepDigest .libcSo6) ∧
       b.toolchainFs.launcherDigest = b.tcbLock.launcherDigest ∧
       b.toolchainFs.oleanManifestDigest = b.tcbLock.oleanManifestDigest) →
      PrimaryGenuineFaithful b.toolchainFs b.tcbLock.pinnedTargetStmtHash)
    (hPrimarySound : PrimaryGenuineFaithful b.toolchainFs b.tcbLock.pinnedTargetStmtHash →
      SemanticallyValid b.tcbLock.pinnedTargetStmtHash)
    (hNanodaFaith :
      b.exportArt.nanodaBinaryDigest = b.tcbLock.nanodaStaticDigest →
      (!(b.exportArt.usesChoiceAxiom && !b.tcbLock.allowClassicalChoice)) = true →
      NanodaGenuineFaithful b.exportArt)
    (hNanodaSound : NanodaGenuineFaithful b.exportArt → b.exportArt.nanodaAccepted = true →
      SemanticallyValid b.exportArt.exportedStmtHash)
    (hCheck : checkVerticalPipeline b = true)
    (vSrc : BitVec 64)
    (hSrcOk : evalMirBody b.cenvCached b.relCached b.mirBody b.argVal = .ok vSrc) :
    execVerticalPipeline b =
      .ok (vSrc, totalSpillFrameBytes b.backend.widthPol b.backend.spilledSimdRegs b.backend.calleeLocalBytes) ∧
    SemanticallyValid b.mirBody.specHash := by
  dsimp [checkVerticalPipeline] at hCheck
  cases hkey : decide (soundV1CacheKey b.cenvCached b.relCached b.mirBody =
      soundV1CacheKey b.cenvLive b.relLive b.mirBody) with
  | false => rw [hkey] at hCheck; cases hCheck
  | true =>
      rw [hkey] at hCheck
      cases hv1c : checkMirV1Cert b.mirBody with
      | false => rw [hv1c] at hCheck; cases hCheck
      | true =>
          rw [hv1c] at hCheck
          cases habi : checkAbiLinkCompat b.relLive b.relLive b.callerTgt b.calleeTgt
              b.callerCc b.calleeCc b.abiSig b.callerDesc b.calleeDesc
              b.hasUnsafeCell b.calleeAtomicWrite b.sroaWriteThrough with
          | false => rw [habi] at hCheck; cases hCheck
          | true =>
              rw [habi] at hCheck
              cases hrz : (!(b.rzMode == .redZoneAllowed) || targetAllowsRedZone b.callerTgt) with
              | false => rw [hrz] at hCheck; cases hCheck
              | true =>
                  rw [hrz] at hCheck
                  cases hbk : checkBackendV3 b.rzMode b.backend with
                  | false => rw [hbk] at hCheck; cases hCheck
                  | true =>
                      rw [hbk] at hCheck
                      cases hsp : decide (b.mirBody.specHash = b.tcbLock.pinnedTargetStmtHash) with
                      | false => rw [hsp] at hCheck; cases hCheck
                      | true =>
                          rw [hsp] at hCheck
                          simp only [Bool.true_and] at hCheck
                          have hV1Norm := v1_certified_f11b_norm_preserves_eval
                            b.cenvLive b.relLive b.mirBody hScalarPure hv1c b.argVal
                          have hV1Cache := v1_const_cone_and_profile_cache_preserves_semantics
                            b.cenvCached b.cenvLive b.relCached b.relLive b.mirBody
                            hCone (of_decide_eq_true hkey) b.argVal
                          have hV1Res : evalMirBody b.cenvLive b.relLive (normalizeF11b b.mirBody) b.argVal = .ok vSrc := by
                            rw [hV1Norm, hV1Cache, hSrcOk]
                          have hV2Res := v2_epoch_pinned_freeze_aware_abi_call_sound
                            b.relLive b.relLive b.callerTgt b.calleeTgt b.callerCc b.calleeCc
                            b.abiSig b.callerDesc b.calleeDesc b.hasUnsafeCell
                            b.calleeAtomicWrite b.sroaWriteThrough hSigFreeze habi vSrc
                          have hBkSpec : checkBackendV3 b.rzMode { b.backend with retAddrSlotVal := vSrc } = true :=
                            hbk
                          have hV3Res := v3_backend_zmm512_probe_vzeroupper_redzone_sound
                            b.rzMode { b.backend with retAddrSlotVal := vSrc } hBkSpec
                          have hV4 := v4_closed_tcb_and_pinned_dual_kernel_sound
                            SemanticallyValid PrimaryGenuineFaithful NanodaGenuineFaithful
                            b.tcbLock b.toolchainFs b.exportArt
                            hPrimaryFaith hPrimarySound hNanodaFaith hNanodaSound hCheck
                          have hspecEq : b.mirBody.specHash = b.tcbLock.pinnedTargetStmtHash :=
                            of_decide_eq_true hsp
                          refine ⟨?_, ?_⟩
                          · dsimp [execVerticalPipeline]
                            rw [hV1Res]
                            dsimp
                            rw [hV2Res]
                            dsimp
                            rw [hV3Res]
                            dsimp
                            rw [hCheck]
                            rfl
                          · rw [hspecEq]
                            exact hV4.1

-- Non-Vacuity End-to-End Witness (Seam V5):
-- Concrete verified bundle with `const MASK = 15`, input `29` -> `13`, `r1_99_1`,
-- `hybridPairStruct true`, `fullZmm512` `4,160 B` probed frame, `noRedZone` + `dispZeroRsp`,
-- and full shadow-free ELF + pinned static `nanoda_bin`.
noncomputable def witnessLock : TcbLock :=
  { defaultLock with pinnedTargetStmtHash := bodyMinizMaskProbe.specHash }

noncomputable def witnessExport : ExportArtifact :=
  { exporterSoDigest := digestLeanShared
    exportedStmtHash := bodyMinizMaskProbe.specHash
    usesChoiceAxiom := false
    nanodaBinaryDigest := digestStaticNanoda
    nanodaAccepted := true }

noncomputable def witnessValidBundle : VerticalCompilationBundle :=
  { mirBody := bodyMinizMaskProbe
    cenvCached := cenvMask15
    cenvLive := cenvMask15
    relCached := .r1_99_1
    relLive := .r1_99_1
    argVal := 29#64
    callerTgt := .x86_64_linux
    calleeTgt := .x86_64_linux
    callerCc := .rustCc
    calleeCc := .rustCc
    abiSig := .hybridPairStruct true
    callerDesc := classifyFnAbi .r1_99_1 .x86_64_linux .rustCc (.hybridPairStruct true)
    calleeDesc := classifyFnAbi .r1_99_1 .x86_64_linux .rustCc (.hybridPairStruct true)
    hasUnsafeCell := true
    calleeAtomicWrite := true
    sroaWriteThrough := true
    rzMode := .noRedZone
    backend := validZmm512NoRedZoneSpec 0#64
    tcbLock := witnessLock
    toolchainFs := fsGenuine
    exportArt := witnessExport }

theorem witness_v5_end_to_end_zmm512_noredzone_dual_kernel_verified :
    checkVerticalPipeline witnessValidBundle = true ∧
    evalMirBody cenvMask15 .r1_99_1 bodyMinizMaskProbe 29#64 = .ok 13#64 ∧
    execVerticalPipeline witnessValidBundle = .ok (13#64, 4160) := by
  exact ⟨rfl, rfl, rfl⟩

-- Adversarial Counterexample #9 (Seam V5 Cross-Seam Ablation):
-- Every stage's *local/legacy* check passes in isolation:
-- - Stage 1 MIR body alone passes `checkMirV1Cert` (under stale cache `cenvMask15`, fails under `cenvMask31`),
-- - Stage 2 caller (1.99.1) & callee (1.100.0) are each valid ABIs for their own release,
-- - Stage 3 passes userspace `checkBackendV3 .redZoneAllowed` (yet fails on `.noRedZone` / Win64),
-- - Stage 4 passes `auditCurrentAnnealLauncherOnly` (yet runs trojan `libleanshared.so`)!
-- Composed together without seam guards, execution crashes AND `checkVerticalPipeline` rejects it.
noncomputable def adversarialBrokenCompositionBundle : VerticalCompilationBundle :=
  { mirBody := bodyMinizMaskProbe
    cenvCached := cenvMask15
    cenvLive := cenvMask31
    relCached := .r1_99_1
    relLive := .r1_100_0
    argVal := 16#64
    callerTgt := .x86_64_linux
    calleeTgt := .x86_64_linux
    callerCc := .rustCc
    calleeCc := .rustCc
    abiSig := .simdF32x4
    callerDesc := classifyFnAbi .r1_99_1 .x86_64_linux .rustCc .simdF32x4
    calleeDesc := classifyFnAbi .r1_100_0 .x86_64_linux .rustCc .simdF32x4
    hasUnsafeCell := false
    calleeAtomicWrite := false
    sroaWriteThrough := true
    rzMode := .noRedZone
    backend := { validZmm512NoRedZoneSpec 0#64 with
      hasOutlinedThunkCall := false, seqCstFence := some .dispNeg64 }
    tcbLock := witnessLock
    toolchainFs := fsRunpathShadowed
    exportArt := { witnessExport with exportedStmtHash := hashTrivialStmt } }

theorem cex_v5_locally_valid_stages_fail_when_composed_without_seam_couplings :
    -- Locally valid pieces in isolation:
    checkMirV1Cert adversarialBrokenCompositionBundle.mirBody = true ∧
    evalMirBody cenvMask15 .r1_99_1 adversarialBrokenCompositionBundle.mirBody 16#64 = .ok 0#64 ∧
    checkBackendV3 .redZoneAllowed adversarialBrokenCompositionBundle.backend = true ∧
    auditCurrentAnnealLauncherOnly witnessLock fsRunpathShadowed = true ∧
    -- Yet composed pipeline fails BOTH under live execution AND under unified gate:
    evalMirBody cenvMask31 .r1_100_0 adversarialBrokenCompositionBundle.mirBody 16#64 = .error .oobPanic ∧
    execVerticalPipeline adversarialBrokenCompositionBundle = .error (.v1Fault .oobPanic) ∧
    checkVerticalPipeline adversarialBrokenCompositionBundle = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end VrustcProbe.VerticalSeamComposition

-- Kernel `#print axioms` audit across every public theorem in this module:
#print axioms VrustcProbe.VerticalSeamComposition.v1_const_cone_and_profile_cache_preserves_semantics
#print axioms VrustcProbe.VerticalSeamComposition.v1_certified_f11b_norm_preserves_eval
#print axioms VrustcProbe.VerticalSeamComposition.cex_v1a_unevaluated_const_change_breaks_uncached_cone
#print axioms VrustcProbe.VerticalSeamComposition.cex_v1b_rustc_196_to_199_retag_drift_and_movetocopy_ub
#print axioms VrustcProbe.VerticalSeamComposition.v2_epoch_pinned_freeze_aware_abi_call_sound
#print axioms VrustcProbe.VerticalSeamComposition.cex_v2a_cross_release_and_cross_target_fnabi_breaks
#print axioms VrustcProbe.VerticalSeamComposition.cex_v2b_indirect_copy_readonly_on_atomic_and_unflushed_sroa_unsound
#print axioms VrustcProbe.VerticalSeamComposition.v3_backend_zmm512_probe_vzeroupper_redzone_sound
#print axioms VrustcProbe.VerticalSeamComposition.v3_noredzone_rejects_neg64_and_admits_zeroRsp
#print axioms VrustcProbe.VerticalSeamComposition.cex_v3a_zmm512_spill_crosses_4096_cliff_and_leaks_zmmHi
#print axioms VrustcProbe.VerticalSeamComposition.cex_v3b_redzone_fence_corrupts_noredzone_and_outlined_leaf
#print axioms VrustcProbe.VerticalSeamComposition.v4_closed_tcb_and_pinned_dual_kernel_sound
#print axioms VrustcProbe.VerticalSeamComposition.cex_v4a_launcher_only_and_runpath_shadow_accept_trojan_kernel
#print axioms VrustcProbe.VerticalSeamComposition.cex_v4b_unpinned_lean4export_or_unpermitted_choice_breaks_dual_kernel
#print axioms VrustcProbe.VerticalSeamComposition.v5_unified_vertical_seam_composition_sound
#print axioms VrustcProbe.VerticalSeamComposition.witness_v5_end_to_end_zmm512_noredzone_dual_kernel_verified
#print axioms VrustcProbe.VerticalSeamComposition.cex_v5_locally_valid_stages_fail_when_composed_without_seam_couplings
