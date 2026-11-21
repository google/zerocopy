/-
  MirInliningAndCleanupSplicing.lean
  Standalone Lean v4.34.1 mechanization of `rustc` MIR call-site inlining
  (`compiler/rustc_mir_transform/src/inline.rs`), disjoint local/block/unwind
  splicing (`Integrator`), LIFO cleanup-pad drop ordering, intra-procedural
  verification reduction for fail-closed single-frame MIR semantics
  (`Anneal` `Trusted.MirSemantics`), and sharpness counterexamples.

  Constructive kernel-checked mechanization:
  - Purely structural recursion and constructive decidability (`[propext, Quot.sound]` only)
  - Checked with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`
-/

namespace MirInliningAndCleanupSplicing

/-! ## Section 1: Identifiers, Values, Move-Deinitializing Local Slots, and Outcomes -/

abbrev DefId := Nat
abbrev BlockId := Nat
abbrev LocalId := Nat
abbrev FeatureId := Nat
abbrev DropTag := Nat

inductive Val where
  | int (n : Nat)
  | bool (b : Bool)
  deriving DecidableEq, Repr

inductive LocalSlot where
  | dead
  | liveUninit
  | liveVal (v : Val)
  deriving DecidableEq, Repr

inductive Fault where
  | undefined          -- DeadLocal, uninitialized read, unreachable reached, uninhabited ref
  | illegalInstruction -- Target-feature violation (#UD / SIGILL)
  | unsupported        -- Unmodeled / fail-closed construct (e.g. Call in Intra semantics)
  deriving DecidableEq, Repr

inductive Outcome where
  | returned (val : Val) (drops : List DropTag)
  | unwound (drops : List DropTag)
  | aborted (drops : List DropTag)
  | fault (kind : Fault)
  deriving DecidableEq, Repr

/-! ## Section 2: Constructive List & Nat Helpers (Constructive Structural Induction) -/

def getAt : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => getAt xs i

def setAt : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
    match setAt xs i v with
    | some xs' => some (x :: xs')
    | none => none

def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if Nat.beq x y then true else memNat x ys

def eqNatList : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && eqNatList xs ys
  | _, _ => false

theorem eqNatList_eq {xs ys : List Nat} (h : eqNatList xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      simp only [eqNatList, Bool.and_eq_true] at h
      have hxy : x = y := Nat.eq_of_beq_eq_true h.1
      have hxs : xs = ys := ih h.2
      subst hxy; subst hxs; rfl

theorem setAt_length :
    ∀ {xs xs' : List α} {i : Nat} {v : α}, setAt xs i v = some xs' → xs'.length = xs.length
  | [], _, _, _, h => nomatch h
  | _ :: _, _, 0, _, h => by cases h; rfl
  | _ :: xs, _, i + 1, v, h => by
    simp only [setAt] at h
    cases hset : setAt xs i v with
    | none => rw [hset] at h; cases h
    | some ys =>
      rw [hset] at h; cases h
      simp [setAt_length hset]

theorem getAt_lt_some {xs : List α} {i : Nat} (h : i < xs.length) :
    ∃ v, getAt xs i = some v := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨x, rfl⟩
    | succ i => exact ih (Nat.lt_of_succ_lt_succ h)

theorem getAt_some_lt {xs : List α} {i : Nat} {v : α} (h : getAt xs i = some v) :
    i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons _ xs ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ xs.length
    | succ i => exact Nat.succ_lt_succ (ih h)

theorem getAt_none_of_le {xs : List α} {i : Nat} (h : xs.length ≤ i) :
    getAt xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => cases h
    | succ i => exact ih (Nat.le_of_succ_le_succ h)

theorem getAt_setAt_same {xs : List α} :
    ∀ {xs' : List α} {i : Nat} {v : α}, setAt xs i v = some xs' → getAt xs' i = some v := by
  induction xs with
  | nil => intro _ _ _ h; cases h
  | cons _ xs ih =>
    intro xs' i v h
    cases i with
    | zero => cases h; rfl
    | succ i =>
      simp only [setAt] at h
      cases hs : setAt xs i v with
      | none => rw [hs] at h; cases h
      | some ys => rw [hs] at h; cases h; exact @ih ys i v hs

theorem getAt_setAt_ne {xs xs' : List α} {i j : Nat} {v : α}
    (h : setAt xs i v = some xs') (hne : j ≠ i) : getAt xs' j = getAt xs j := by
  induction xs generalizing xs' i j with
  | nil => cases h
  | cons _ xs ih =>
    cases i with
    | zero =>
      cases h
      cases j with
      | zero => exact absurd rfl hne
      | succ _ => rfl
    | succ i =>
      simp only [setAt] at h
      cases hs : setAt xs i v with
      | none => rw [hs] at h; cases h
      | some _ =>
        rw [hs] at h; cases h
        cases j with
        | zero => rfl
        | succ j => exact ih hs (fun heq => hne (congrArg Nat.succ heq))

theorem getAt_append_left {xs ys : List α} {i : Nat} (hi : i < xs.length) :
    getAt (xs ++ ys) i = getAt xs i := by
  induction xs generalizing i with
  | nil => cases hi
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (Nat.lt_of_succ_lt_succ hi)

theorem getAt_append_right :
    ∀ (xs ys : List α) (j : Nat), getAt (xs ++ ys) (xs.length + j) = getAt ys j
  | [], _, _ => by simp
  | _ :: xs, ys, j => by
    have hadd : (xs.length + 1) + j = (xs.length + j) + 1 := Nat.succ_add xs.length j
    simp only [List.cons_append, List.length_cons, hadd, getAt]
    exact getAt_append_right xs ys j

theorem setAt_append_left :
    ∀ {xs ys : List α} {i : Nat} {v : α},
      i < xs.length → setAt (xs ++ ys) i v = (setAt xs i v).map (fun xs' => xs' ++ ys)
  | [], _, _, _, hi => nomatch hi
  | _ :: _, _, 0, _, _ => rfl
  | _ :: xs, _, i + 1, v, hi => by
    simp only [List.cons_append, setAt, setAt_append_left (Nat.lt_of_succ_lt_succ hi)]
    cases setAt xs i v <;> rfl

theorem setAt_append_right :
    ∀ (xs ys : List α) (j : Nat) (v : α),
      setAt (xs ++ ys) (xs.length + j) v = (setAt ys j v).map (fun ys' => xs ++ ys')
  | [], ys, j, v => by
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    cases setAt ys j v <;> rfl
  | _ :: xs, ys, j, v => by
    have hadd : (xs.length + 1) + j = (xs.length + j) + 1 := Nat.succ_add xs.length j
    simp only [List.cons_append, List.length_cons, hadd, setAt, setAt_append_right xs ys j v]
    cases setAt ys j v <;> rfl

theorem getAt_map (f : α → β) :
    ∀ (xs : List α) (i : Nat), getAt (xs.map f) i = (getAt xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => getAt_map f xs i

/-! ## Section 3: Core MIR AST and Operational Primitives -/

inductive Operand where
  | copy (loc : LocalId)
  | move (loc : LocalId)
  | constVal (v : Val)
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (op : Operand)
  | addNat (lhs rhs : Operand)
  | eqNat (lhs rhs : Operand)
  | featureAdd (reqFeat : FeatureId) (lhs rhs : Operand)
  deriving DecidableEq, Repr

inductive Stmt where
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | assign (dst : LocalId) (rv : Rvalue)
  | dropGuard (loc : LocalId) (tag : DropTag)
  | validateDestRef (inhabited : Bool)
  deriving DecidableEq, Repr

inductive UnwindAction where
  | cleanup (bb : BlockId)
  | continue_
  | terminate
  | unreachable
  deriving DecidableEq, Repr

inductive Terminator where
  | goto (target : BlockId)
  | switchBool (cond : Operand) (tTarget fTarget : BlockId)
  | return_
  | unwindStart (unwind : UnwindAction)
  | unwindResume
  | unwindTerminate
  | unreachable
  | call (callee : DefId) (args : List Operand) (dst : LocalId)
         (target : Option BlockId) (unwind : UnwindAction)
  deriving DecidableEq, Repr

structure BasicBlock where
  isCleanup : Bool
  stmts : List Stmt
  term : Terminator
  deriving DecidableEq, Repr

structure Body where
  numLocals : Nat
  argCount : Nat
  features : List FeatureId
  blocks : List BasicBlock
  deriving DecidableEq, Repr

abbrev Program := List Body

/-- Evaluate an `Operand` with `deinitMovedPlace = true` (`Operand.move` mutates
    the moved slot to `.liveUninit`, matching `Anneal` `Trusted.MirSemantics`). -/
def evalOperand (locals : List LocalSlot) : Operand → Except Fault (Val × List LocalSlot)
  | .constVal v => .ok (v, locals)
  | .copy loc =>
    match getAt locals loc with
    | some (.liveVal v) => .ok (v, locals)
    | some .liveUninit | some .dead => .error .undefined
    | none => .error .unsupported
  | .move loc =>
    match getAt locals loc with
    | some (.liveVal v) =>
      match setAt locals loc .liveUninit with
      | some locals' => .ok (v, locals')
      | none => .error .unsupported
    | some .liveUninit | some .dead => .error .undefined
    | none => .error .unsupported

def evalArgs (locals : List LocalSlot) : List Operand → Except Fault (List Val × List LocalSlot)
  | [] => .ok ([], locals)
  | op :: rest =>
    match evalOperand locals op with
    | .error f => .error f
    | .ok (v, locals₁) =>
      match evalArgs locals₁ rest with
      | .error f => .error f
      | .ok (vs, locals₂) => .ok (v :: vs, locals₂)

def evalRvalue (bodyFeats cpuFeats : List FeatureId) (locals : List LocalSlot) :
    Rvalue → Except Fault (Val × List LocalSlot)
  | .use op => evalOperand locals op
  | .addNat lhs rhs =>
    match evalOperand locals lhs with
    | .error f => .error f
    | .ok (v1, locals₁) =>
      match evalOperand locals₁ rhs with
      | .error f => .error f
      | .ok (v2, locals₂) =>
        match v1, v2 with
        | .int a, .int b => .ok (.int (a + b), locals₂)
        | _, _ => .error .unsupported
  | .eqNat lhs rhs =>
    match evalOperand locals lhs with
    | .error f => .error f
    | .ok (v1, locals₁) =>
      match evalOperand locals₁ rhs with
      | .error f => .error f
      | .ok (v2, locals₂) =>
        match v1, v2 with
        | .int a, .int b => .ok (.bool (Nat.beq a b), locals₂)
        | _, _ => .error .unsupported
  | .featureAdd req lhs rhs =>
    if !(memNat req bodyFeats && memNat req cpuFeats) then
      .error .illegalInstruction
    else
      match evalOperand locals lhs with
      | .error f => .error f
      | .ok (v1, locals₁) =>
        match evalOperand locals₁ rhs with
        | .error f => .error f
        | .ok (v2, locals₂) =>
          match v1, v2 with
          | .int a, .int b => .ok (.int (a + b), locals₂)
          | _, _ => .error .unsupported

def writeLocal (locals : List LocalSlot) (dst : LocalId) (v : Val) :
    Except Fault (List LocalSlot) :=
  match getAt locals dst with
  | none => .error .unsupported
  | some .dead => .error .undefined
  | some .liveUninit | some (.liveVal _) =>
    match setAt locals dst (.liveVal v) with
    | some locals' => .ok locals'
    | none => .error .unsupported

def evalStmt (bodyFeats cpuFeats : List FeatureId)
    (locals : List LocalSlot) (drops : List DropTag) :
    Stmt → Except Fault (List LocalSlot × List DropTag)
  | .storageLive loc =>
    match setAt locals loc .liveUninit with
    | some locals' => .ok (locals', drops)
    | none => .error .unsupported
  | .storageDead loc =>
    if Nat.beq loc 0 then
      .error .unsupported
    else
      match setAt locals loc .dead with
      | some locals' => .ok (locals', drops)
      | none => .error .unsupported
  | .assign dst rv =>
    match evalRvalue bodyFeats cpuFeats locals rv with
    | .error f => .error f
    | .ok (v, locals₁) =>
      match writeLocal locals₁ dst v with
      | .error f => .error f
      | .ok locals₂ => .ok (locals₂, drops)
  | .dropGuard loc tag =>
    match getAt locals loc with
    | some (.liveVal _) =>
      match setAt locals loc .liveUninit with
      | some locals' => .ok (locals', drops ++ [tag])
      | none => .error .unsupported
    | some .liveUninit | some .dead => .error .undefined
    | none => .error .unsupported
  | .validateDestRef inhabited =>
    if inhabited then .ok (locals, drops) else .error .undefined

def evalStmts (bodyFeats cpuFeats : List FeatureId)
    (locals : List LocalSlot) (drops : List DropTag) :
    List Stmt → Except Fault (List LocalSlot × List DropTag)
  | [] => .ok (locals, drops)
  | s :: rest =>
    match evalStmt bodyFeats cpuFeats locals drops s with
    | .error f => .error f
    | .ok (locals₁, drops₁) => evalStmts bodyFeats cpuFeats locals₁ drops₁ rest

def replicateSlot : Nat → LocalSlot → List LocalSlot
  | 0, _ => []
  | n + 1, s => s :: replicateSlot n s

theorem replicateSlot_length (n : Nat) (s : LocalSlot) :
    (replicateSlot n s).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicateSlot, ih]

def initFrameLocals (body : Body) (args : List Val) : Option (List LocalSlot) :=
  if Nat.beq args.length body.argCount && decide (1 + body.argCount ≤ body.numLocals) then
    some ([LocalSlot.liveUninit] ++ args.map LocalSlot.liveVal ++
      replicateSlot (body.numLocals - (1 + body.argCount)) LocalSlot.dead)
  else
    none

theorem initFrameLocals_length {body : Body} {args : List Val} {locals : List LocalSlot}
    (h : initFrameLocals body args = some locals) :
    locals.length = body.numLocals := by
  unfold initFrameLocals at h
  split at h
  · next hcond =>
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hlen : args.length = body.argCount := Nat.eq_of_beq_eq_true hcond.1
    have hle : 1 + body.argCount ≤ body.numLocals := hcond.2
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
      replicateSlot_length, hlen, Nat.zero_add]
    exact Nat.add_sub_of_le hle
  · cases h

def allFeaturesPresent (req cpu : List FeatureId) : Bool :=
  match req with
  | [] => true
  | f :: fs => memNat f cpu && allFeaturesPresent fs cpu

/-! ## Section 4: Interprocedural Stack Semantics vs. Intra-Procedural Semantics -/

/-- Computable fuel-bounded intra-procedural single-frame evaluator matching
    `Anneal` `Trusted.MirSemantics`: every `Terminator.call` fails closed with
    `Outcome.fault .unsupported`. -/
def evalBlockIntra (body : Body) (cpu : List FeatureId) :
    Nat → BlockId → List LocalSlot → List DropTag → Outcome
  | 0, _, _, _ => .fault .unsupported
  | fuel + 1, bbIdx, locals, drops =>
    match getAt body.blocks bbIdx with
    | none => .fault .unsupported
    | some bb =>
      match evalStmts body.features cpu locals drops bb.stmts with
      | .error f => .fault f
      | .ok (locals₁, drops₁) =>
        match bb.term with
        | .goto t => evalBlockIntra body cpu fuel t locals₁ drops₁
        | .switchBool cond tTarget fTarget =>
          match evalOperand locals₁ cond with
          | .error f => .fault f
          | .ok (.bool true, locals₂) => evalBlockIntra body cpu fuel tTarget locals₂ drops₁
          | .ok (.bool false, locals₂) => evalBlockIntra body cpu fuel fTarget locals₂ drops₁
          | .ok (.int _, _) => .fault .unsupported
        | .return_ =>
          if bb.isCleanup then .fault .unsupported
          else
            match getAt locals₁ 0 with
            | some (.liveVal v) => .returned v drops₁
            | some .liveUninit | some .dead => .fault .undefined
            | none => .fault .unsupported
        | .unreachable => .fault .undefined
        | .unwindTerminate => .aborted drops₁
        | .unwindResume =>
          if bb.isCleanup then .unwound drops₁ else .fault .unsupported
        | .unwindStart u =>
          match u with
          | .cleanup cbb => evalBlockIntra body cpu fuel cbb locals₁ drops₁
          | .continue_ => .unwound drops₁
          | .terminate => .aborted drops₁
          | .unreachable => .fault .undefined
        | .call _ _ _ _ _ => .fault .unsupported

def evalBodyIntra (body : Body) (cpu : List FeatureId) (fuel : Nat) (args : List Val) : Outcome :=
  if !allFeaturesPresent body.features cpu then
    .fault .illegalInstruction
  else
    match initFrameLocals body args with
    | none => .fault .unsupported
    | some locals₀ => evalBlockIntra body cpu fuel 0 locals₀ []

/-- Computable fuel-bounded interprocedural multi-frame evaluator. -/
def evalBlockInterproc (prog : Program) (cpu : List FeatureId) :
    Nat → Body → BlockId → List LocalSlot → List DropTag → Outcome
  | 0, _, _, _, _ => .fault .unsupported
  | fuel + 1, body, bbIdx, locals, drops =>
    match getAt body.blocks bbIdx with
    | none => .fault .unsupported
    | some bb =>
      match evalStmts body.features cpu locals drops bb.stmts with
      | .error f => .fault f
      | .ok (locals₁, drops₁) =>
        match bb.term with
        | .goto t => evalBlockInterproc prog cpu fuel body t locals₁ drops₁
        | .switchBool cond tTarget fTarget =>
          match evalOperand locals₁ cond with
          | .error f => .fault f
          | .ok (.bool true, locals₂) => evalBlockInterproc prog cpu fuel body tTarget locals₂ drops₁
          | .ok (.bool false, locals₂) => evalBlockInterproc prog cpu fuel body fTarget locals₂ drops₁
          | .ok (.int _, _) => .fault .unsupported
        | .return_ =>
          if bb.isCleanup then .fault .unsupported
          else
            match getAt locals₁ 0 with
            | some (.liveVal v) => .returned v drops₁
            | some .liveUninit | some .dead => .fault .undefined
            | none => .fault .unsupported
        | .unreachable => .fault .undefined
        | .unwindTerminate => .aborted drops₁
        | .unwindResume =>
          if bb.isCleanup then .unwound drops₁ else .fault .unsupported
        | .unwindStart u =>
          match u with
          | .cleanup cbb => evalBlockInterproc prog cpu fuel body cbb locals₁ drops₁
          | .continue_ => .unwound drops₁
          | .terminate => .aborted drops₁
          | .unreachable => .fault .undefined
        | .call calleeId argOps dst target unwind =>
          if bb.isCleanup then
            .fault .unsupported
          else
            match getAt prog calleeId with
            | none => .fault .unsupported
            | some callee =>
              if !allFeaturesPresent callee.features cpu then
                .fault .illegalInstruction
              else
                match evalArgs locals₁ argOps with
                | .error f => .fault f
                | .ok (argVals, locals₂) =>
                  match initFrameLocals callee argVals with
                  | none => .fault .unsupported
                  | some calleeLocals₀ =>
                    match evalBlockInterproc prog cpu fuel callee 0 calleeLocals₀ drops₁ with
                    | .returned retVal drops₂ =>
                      match target with
                      | none => .fault .undefined
                      | some retBb =>
                        match writeLocal locals₂ dst retVal with
                        | .error f => .fault f
                        | .ok locals₃ =>
                          evalBlockInterproc prog cpu fuel body retBb locals₃ drops₂
                    | .unwound drops₂ =>
                      match unwind with
                      | .cleanup cbb =>
                        evalBlockInterproc prog cpu fuel body cbb locals₂ drops₂
                      | .continue_ => .unwound drops₂
                      | .terminate => .aborted drops₂
                      | .unreachable => .fault .undefined
                    | .aborted drops₂ => .aborted drops₂
                    | .fault f => .fault f

def evalBodyInterproc (prog : Program) (body : Body) (cpu : List FeatureId)
    (fuel : Nat) (args : List Val) : Outcome :=
  if !allFeaturesPresent body.features cpu then
    .fault .illegalInstruction
  else
    match initFrameLocals body args with
    | none => .fault .unsupported
    | some locals₀ => evalBlockInterproc prog cpu fuel body 0 locals₀ []

/-- Fuel-independent inductive operational semantics `ExecBlock`. -/
inductive ExecBlock (prog : Program) (cpu : List FeatureId) :
    Body → BlockId → List LocalSlot → List DropTag → Outcome → Prop where
  | oobBlock {body bbIdx locals drops} :
      getAt body.blocks bbIdx = none →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | stmtFault {body bbIdx bb locals drops f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .error f →
      ExecBlock prog cpu body bbIdx locals drops (.fault f)
  | goto {body bbIdx bb locals drops locals₁ drops₁ target out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .goto target →
      ExecBlock prog cpu body target locals₁ drops₁ out →
      ExecBlock prog cpu body bbIdx locals drops out
  | switchFault {body bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .error f →
      ExecBlock prog cpu body bbIdx locals drops (.fault f)
  | switchNonBool {body bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget n locals₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .ok (.int n, locals₂) →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | switchTrue {body bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget locals₂ out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .ok (.bool true, locals₂) →
      ExecBlock prog cpu body tTarget locals₂ drops₁ out →
      ExecBlock prog cpu body bbIdx locals drops out
  | switchFalse {body bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget locals₂ out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .ok (.bool false, locals₂) →
      ExecBlock prog cpu body fTarget locals₂ drops₁ out →
      ExecBlock prog cpu body bbIdx locals drops out
  | returnCleanupFault {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = true →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | returnOk {body bbIdx bb locals drops locals₁ drops₁ v} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = false →
      getAt locals₁ 0 = some (.liveVal v) →
      ExecBlock prog cpu body bbIdx locals drops (.returned v drops₁)
  | returnUninitOrDead {body bbIdx bb locals drops locals₁ drops₁ s} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = false →
      getAt locals₁ 0 = some s →
      (s = .liveUninit ∨ s = .dead) →
      ExecBlock prog cpu body bbIdx locals drops (.fault .undefined)
  | returnNoSlot {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = false →
      getAt locals₁ 0 = none →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | unreachable {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unreachable →
      ExecBlock prog cpu body bbIdx locals drops (.fault .undefined)
  | unwindTerminate {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindTerminate →
      ExecBlock prog cpu body bbIdx locals drops (.aborted drops₁)
  | unwindResumeOk {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindResume →
      bb.isCleanup = true →
      ExecBlock prog cpu body bbIdx locals drops (.unwound drops₁)
  | unwindResumeFault {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindResume →
      bb.isCleanup = false →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | unwindStartCleanup {body bbIdx bb locals drops locals₁ drops₁ cbb out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart (.cleanup cbb) →
      ExecBlock prog cpu body cbb locals₁ drops₁ out →
      ExecBlock prog cpu body bbIdx locals drops out
  | unwindStartContinue {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart .continue_ →
      ExecBlock prog cpu body bbIdx locals drops (.unwound drops₁)
  | unwindStartTerminate {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart .terminate →
      ExecBlock prog cpu body bbIdx locals drops (.aborted drops₁)
  | unwindStartUnreachable {body bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart .unreachable →
      ExecBlock prog cpu body bbIdx locals drops (.fault .undefined)
  | callInCleanupFault {body bbIdx bb locals drops locals₁ drops₁ calleeId argOps dst target unwind} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = true →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | callMissingCallee {body bbIdx bb locals drops locals₁ drops₁ calleeId argOps dst target unwind} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = false →
      getAt prog calleeId = none →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | callFeatureFault {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target unwind} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = false →
      ExecBlock prog cpu body bbIdx locals drops (.fault .illegalInstruction)
  | callArgFault {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target unwind f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .error f →
      ExecBlock prog cpu body bbIdx locals drops (.fault f)
  | callInitFault {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target unwind argVals locals₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = none →
      ExecBlock prog cpu body bbIdx locals drops (.fault .unsupported)
  | callReturnOk {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst retBb unwind
        argVals locals₂ calleeLocals₀ retVal drops₂ locals₃ out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst (some retBb) unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.returned retVal drops₂) →
      writeLocal locals₂ dst retVal = .ok locals₃ →
      ExecBlock prog cpu body retBb locals₃ drops₂ out →
      ExecBlock prog cpu body bbIdx locals drops out
  | callReturnWriteFault {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst retBb unwind
        argVals locals₂ calleeLocals₀ retVal drops₂ f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst (some retBb) unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.returned retVal drops₂) →
      writeLocal locals₂ dst retVal = .error f →
      ExecBlock prog cpu body bbIdx locals drops (.fault f)
  | callReturnDiverging {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst unwind
        argVals locals₂ calleeLocals₀ retVal drops₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst none unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.returned retVal drops₂) →
      ExecBlock prog cpu body bbIdx locals drops (.fault .undefined)
  | callUnwindCleanup {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target cbb
        argVals locals₂ calleeLocals₀ drops₂ out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target (.cleanup cbb) →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.unwound drops₂) →
      ExecBlock prog cpu body cbb locals₂ drops₂ out →
      ExecBlock prog cpu body bbIdx locals drops out
  | callUnwindContinue {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target
        argVals locals₂ calleeLocals₀ drops₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target .continue_ →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.unwound drops₂) →
      ExecBlock prog cpu body bbIdx locals drops (.unwound drops₂)
  | callUnwindTerminate {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target
        argVals locals₂ calleeLocals₀ drops₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target .terminate →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.unwound drops₂) →
      ExecBlock prog cpu body bbIdx locals drops (.aborted drops₂)
  | callUnwindUnreachable {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target
        argVals locals₂ calleeLocals₀ drops₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target .unreachable →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.unwound drops₂) →
      ExecBlock prog cpu body bbIdx locals drops (.fault .undefined)
  | callPropagateAbort {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target unwind
        argVals locals₂ calleeLocals₀ drops₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.aborted drops₂) →
      ExecBlock prog cpu body bbIdx locals drops (.aborted drops₂)
  | callPropagateFault {body bbIdx bb locals drops locals₁ drops₁ calleeId callee argOps dst target unwind
        argVals locals₂ calleeLocals₀ f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      bb.isCleanup = false →
      getAt prog calleeId = some callee →
      allFeaturesPresent callee.features cpu = true →
      evalArgs locals₁ argOps = .ok (argVals, locals₂) →
      initFrameLocals callee argVals = some calleeLocals₀ →
      ExecBlock prog cpu callee 0 calleeLocals₀ drops₁ (.fault f) →
      ExecBlock prog cpu body bbIdx locals drops (.fault f)

def ExecBody (prog : Program) (body : Body) (cpu : List FeatureId)
    (args : List Val) (out : Outcome) : Prop :=
  if !allFeaturesPresent body.features cpu then
    out = .fault .illegalInstruction
  else
    match initFrameLocals body args with
    | none => out = .fault .unsupported
    | some locals₀ => ExecBlock prog cpu body 0 locals₀ [] out

/-- Inductive intra-procedural semantics (`body` is a fixed parameter):
    every `Terminator.call` fails closed with `.fault .unsupported`. -/
inductive ExecBlockIntra (cpu : List FeatureId) (body : Body) :
    BlockId → List LocalSlot → List DropTag → Outcome → Prop where
  | oobBlock {bbIdx locals drops} :
      getAt body.blocks bbIdx = none →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .unsupported)
  | stmtFault {bbIdx bb locals drops f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .error f →
      ExecBlockIntra cpu body bbIdx locals drops (.fault f)
  | goto {bbIdx bb locals drops locals₁ drops₁ target out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .goto target →
      ExecBlockIntra cpu body target locals₁ drops₁ out →
      ExecBlockIntra cpu body bbIdx locals drops out
  | switchFault {bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget f} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .error f →
      ExecBlockIntra cpu body bbIdx locals drops (.fault f)
  | switchNonBool {bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget n locals₂} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .ok (.int n, locals₂) →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .unsupported)
  | switchTrue {bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget locals₂ out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .ok (.bool true, locals₂) →
      ExecBlockIntra cpu body tTarget locals₂ drops₁ out →
      ExecBlockIntra cpu body bbIdx locals drops out
  | switchFalse {bbIdx bb locals drops locals₁ drops₁ cond tTarget fTarget locals₂ out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .switchBool cond tTarget fTarget →
      evalOperand locals₁ cond = .ok (.bool false, locals₂) →
      ExecBlockIntra cpu body fTarget locals₂ drops₁ out →
      ExecBlockIntra cpu body bbIdx locals drops out
  | returnCleanupFault {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = true →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .unsupported)
  | returnOk {bbIdx bb locals drops locals₁ drops₁ v} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = false →
      getAt locals₁ 0 = some (.liveVal v) →
      ExecBlockIntra cpu body bbIdx locals drops (.returned v drops₁)
  | returnUninitOrDead {bbIdx bb locals drops locals₁ drops₁ s} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = false →
      getAt locals₁ 0 = some s →
      (s = .liveUninit ∨ s = .dead) →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .undefined)
  | returnNoSlot {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .return_ →
      bb.isCleanup = false →
      getAt locals₁ 0 = none →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .unsupported)
  | unreachable {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unreachable →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .undefined)
  | unwindTerminate {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindTerminate →
      ExecBlockIntra cpu body bbIdx locals drops (.aborted drops₁)
  | unwindResumeOk {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindResume →
      bb.isCleanup = true →
      ExecBlockIntra cpu body bbIdx locals drops (.unwound drops₁)
  | unwindResumeFault {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindResume →
      bb.isCleanup = false →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .unsupported)
  | unwindStartCleanup {bbIdx bb locals drops locals₁ drops₁ cbb out} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart (.cleanup cbb) →
      ExecBlockIntra cpu body cbb locals₁ drops₁ out →
      ExecBlockIntra cpu body bbIdx locals drops out
  | unwindStartContinue {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart .continue_ →
      ExecBlockIntra cpu body bbIdx locals drops (.unwound drops₁)
  | unwindStartTerminate {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart .terminate →
      ExecBlockIntra cpu body bbIdx locals drops (.aborted drops₁)
  | unwindStartUnreachable {bbIdx bb locals drops locals₁ drops₁} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .unwindStart .unreachable →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .undefined)
  | callFailClosed {bbIdx bb locals drops locals₁ drops₁ calleeId argOps dst target unwind} :
      getAt body.blocks bbIdx = some bb →
      evalStmts body.features cpu locals drops bb.stmts = .ok (locals₁, drops₁) →
      bb.term = .call calleeId argOps dst target unwind →
      ExecBlockIntra cpu body bbIdx locals drops (.fault .unsupported)

def ExecBodyIntra (body : Body) (cpu : List FeatureId)
    (args : List Val) (out : Outcome) : Prop :=
  if !allFeaturesPresent body.features cpu then
    out = .fault .illegalInstruction
  else
    match initFrameLocals body args with
    | none => out = .fault .unsupported
    | some locals₀ => ExecBlockIntra cpu body 0 locals₀ [] out

/-! ## Section 5: The `inlineCallSite` CFG Splicer (`Integrator` Formalization) -/

def shiftOperand (off : Nat) : Operand → Operand
  | .copy loc => .copy (off + loc)
  | .move loc => .move (off + loc)
  | .constVal v => .constVal v

def shiftRvalue (off : Nat) : Rvalue → Rvalue
  | .use op => .use (shiftOperand off op)
  | .addNat lhs rhs => .addNat (shiftOperand off lhs) (shiftOperand off rhs)
  | .eqNat lhs rhs => .eqNat (shiftOperand off lhs) (shiftOperand off rhs)
  | .featureAdd req lhs rhs =>
    .featureAdd req (shiftOperand off lhs) (shiftOperand off rhs)

def shiftStmt (off : Nat) : Stmt → Stmt
  | .storageLive loc => .storageLive (off + loc)
  | .storageDead loc => .storageDead (off + loc)
  | .assign dst rv => .assign (off + dst) (shiftRvalue off rv)
  | .dropGuard loc tag => .dropGuard (off + loc) tag
  | .validateDestRef inhabited => .validateDestRef inhabited

def mapUnwind (blockOff : Nat) (callerUnwind : UnwindAction) : UnwindAction → UnwindAction
  | .cleanup target => .cleanup (blockOff + target)
  | .continue_ => callerUnwind
  | .terminate => .terminate
  | .unreachable => .unreachable

def integrateTerm (localOff blockOff retTrampoline : Nat)
    (callerTarget : Option BlockId) (callerUnwind : UnwindAction)
    (inCleanup : Bool) : Terminator → Terminator
  | .goto target => .goto (blockOff + target)
  | .switchBool cond tTarget fTarget =>
    .switchBool (shiftOperand localOff cond) (blockOff + tTarget) (blockOff + fTarget)
  | .return_ =>
    if inCleanup then
      .return_
    else
      match callerTarget with
      | some _ => .goto retTrampoline
      | none => .unreachable
  | .unwindStart u => .unwindStart (mapUnwind blockOff callerUnwind u)
  | .unwindResume =>
    if !inCleanup then
      .unwindResume
    else
      match callerUnwind with
      | .cleanup cbb => .goto cbb
      | .continue_ => .unwindResume
      | .terminate => .unwindTerminate
      | .unreachable => .unreachable
  | .unwindTerminate => .unwindTerminate
  | .unreachable => .unreachable
  | .call calleeId argOps dst target unwind =>
    .call calleeId (argOps.map (shiftOperand localOff)) (localOff + dst)
      (target.map (blockOff + ·)) (mapUnwind blockOff callerUnwind unwind)

def integrateBlock (localOff blockOff retTrampoline : Nat)
    (callerTarget : Option BlockId) (callerUnwind : UnwindAction)
    (bb : BasicBlock) : BasicBlock :=
  { isCleanup := bb.isCleanup
    stmts := bb.stmts.map (shiftStmt localOff)
    term := integrateTerm localOff blockOff retTrampoline callerTarget callerUnwind bb.isCleanup bb.term }

def buildArgBindings (paramStart : Nat) : List Operand → List Stmt
  | [] => []
  | op :: rest =>
    Stmt.storageLive paramStart ::
    Stmt.assign paramStart (.use op) ::
    buildArgBindings (paramStart + 1) rest

def resetDeadRange : Nat → Nat → List Stmt
  | _, 0 => []
  | startIdx, count + 1 =>
    Stmt.storageDead startIdx :: resetDeadRange (startIdx + 1) count

def buildCallPrelude (localOff argCount calleeLocals : Nat) (argOps : List Operand) : List Stmt :=
  Stmt.storageLive localOff ::
  (buildArgBindings (localOff + 1) argOps ++
   resetDeadRange (localOff + 1 + argCount) (calleeLocals - (1 + argCount)))

def stmtValidForCallee : Stmt → Bool
  | .storageDead loc => !Nat.beq loc 0
  | _ => true

def stmtsValidForCallee : List Stmt → Bool
  | [] => true
  | s :: ss => stmtValidForCallee s && stmtsValidForCallee ss

def operandBounded (limit : Nat) : Operand → Bool
  | .copy loc | .move loc => decide (loc < limit)
  | .constVal _ => true

def operandListBounded (limit : Nat) : List Operand → Bool
  | [] => true
  | op :: ops => operandBounded limit op && operandListBounded limit ops

def rvalueBounded (limit : Nat) : Rvalue → Bool
  | .use op => operandBounded limit op
  | .addNat lhs rhs | .eqNat lhs rhs | .featureAdd _ lhs rhs =>
    operandBounded limit lhs && operandBounded limit rhs

def stmtBounded (limit : Nat) : Stmt → Bool
  | .storageLive loc | .storageDead loc | .dropGuard loc _ => decide (loc < limit)
  | .assign dst rv => decide (dst < limit) && rvalueBounded limit rv
  | .validateDestRef _ => true

def stmtsBounded (limit : Nat) : List Stmt → Bool
  | [] => true
  | s :: ss => stmtBounded limit s && stmtsBounded limit ss

def unwindBounded (blockLimit : Nat) : UnwindAction → Bool
  | .cleanup bb => decide (bb < blockLimit)
  | .continue_ | .terminate | .unreachable => true

def optBlockBounded (blockLimit : Nat) : Option BlockId → Bool
  | none => true
  | some bb => decide (bb < blockLimit)

def termBounded (localLimit blockLimit : Nat) : Terminator → Bool
  | .goto t => decide (t < blockLimit)
  | .switchBool cond t f =>
    operandBounded localLimit cond && decide (t < blockLimit) && decide (f < blockLimit)
  | .return_ | .unwindResume | .unwindTerminate | .unreachable => true
  | .unwindStart u => unwindBounded blockLimit u
  | .call _ argOps dst target unwind =>
    operandListBounded localLimit argOps && decide (dst < localLimit) &&
    optBlockBounded blockLimit target && unwindBounded blockLimit unwind

def blocksWellFormed (localLimit blockLimit : Nat) (checkNonZeroDead : Bool) :
    List BasicBlock → Bool
  | [] => true
  | bb :: bbs =>
    stmtsBounded localLimit bb.stmts &&
    (!checkNonZeroDead || stmtsValidForCallee bb.stmts) &&
    termBounded localLimit blockLimit bb.term &&
    blocksWellFormed localLimit blockLimit checkNonZeroDead bbs

def isCallFreeBlocks : List BasicBlock → Bool
  | [] => true
  | bb :: bbs =>
    match bb.term with
    | .call _ _ _ _ _ => false
    | _ => isCallFreeBlocks bbs

def isCallFree (b : Body) : Bool :=
  isCallFreeBlocks b.blocks

def bodyWellFormed (b : Body) (checkNonZeroDead : Bool) : Bool :=
  decide (1 + b.argCount ≤ b.numLocals) &&
  decide (1 ≤ b.blocks.length) &&
  blocksWellFormed b.numLocals b.blocks.length checkNonZeroDead b.blocks

def mkReturnTrampoline (N : Nat) (dst : LocalId) : Option BlockId → List BasicBlock
  | none => []
  | some retBb =>
    [{ isCleanup := false
       stmts := [Stmt.assign dst (.use (.move N))]
       term := .goto retBb }]

def inlineCallSite (prog : Program) (caller : Body) (callBb : BlockId) : Option Body :=
  if !bodyWellFormed caller false then
    none
  else
    match getAt caller.blocks callBb with
    | none => none
    | some bb =>
      if bb.isCleanup then
        none
      else
        match bb.term with
        | .call calleeId argOps dst target unwind =>
          match getAt prog calleeId with
          | none => none
          | some callee =>
            if !bodyWellFormed callee true then
              none
            else if !isCallFree callee then
              none
            else if !eqNatList callee.features caller.features then
              none
            else if !Nat.beq argOps.length callee.argCount then
              none
            else
              let N := caller.numLocals
              let B := caller.blocks.length
              let C := callee.blocks.length
              let retTrampoline := B + C
              let patchedCallBb : BasicBlock := {
                isCleanup := false
                stmts := bb.stmts ++ buildCallPrelude N callee.argCount callee.numLocals argOps
                term := .goto B
              }
              match setAt caller.blocks callBb patchedCallBb with
              | none => none
              | some callerBlocksPatched =>
                let integratedCallee :=
                  callee.blocks.map (integrateBlock N B retTrampoline target unwind)
                let extraRetBlocks : List BasicBlock := mkReturnTrampoline N dst target
                some {
                  numLocals := N + callee.numLocals
                  argCount := caller.argCount
                  features := caller.features
                  blocks := callerBlocksPatched ++ integratedCallee ++ extraRetBlocks
                }
        | _ => none

/-! ## Section 6: Frame-Split & Local-Shift Equivariance Lemmas -/

theorem evalOperand_prefix {xs extra : List LocalSlot} {op : Operand}
    (hb : operandBounded xs.length op = true) :
    evalOperand (xs ++ extra) op =
      (evalOperand xs op).map (fun (v, xs') => (v, xs' ++ extra)) := by
  cases op with
  | constVal _ => rfl
  | copy loc =>
    simp only [operandBounded, decide_eq_true_eq] at hb
    simp only [evalOperand, getAt_append_left hb]
    cases getAt xs loc with
    | none => rfl
    | some slot => cases slot <;> rfl
  | move loc =>
    simp only [operandBounded, decide_eq_true_eq] at hb
    simp only [evalOperand, getAt_append_left hb]
    cases getAt xs loc with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | liveUninit => rfl
      | liveVal _ =>
        simp only [setAt_append_left hb]
        cases setAt xs loc .liveUninit <;> rfl

theorem evalOperand_preserves_length {xs xs' : List LocalSlot} {op : Operand} {v : Val}
    (h : evalOperand xs op = .ok (v, xs')) : xs'.length = xs.length := by
  cases op with
  | constVal _ => cases h; rfl
  | copy loc =>
    simp only [evalOperand] at h
    cases hget : getAt xs loc with
    | none => rw [hget] at h; cases h
    | some slot =>
      rw [hget] at h
      cases slot with
      | dead => cases h
      | liveUninit => cases h
      | liveVal _ => cases h; rfl
  | move loc =>
    simp only [evalOperand] at h
    cases hget : getAt xs loc with
    | none => rw [hget] at h; cases h
    | some slot =>
      rw [hget] at h
      cases slot with
      | dead => cases h
      | liveUninit => cases h
      | liveVal _ =>
        simp only [] at h
        cases hset : setAt xs loc .liveUninit with
        | none => rw [hset] at h; cases h
        | some _ => rw [hset] at h; cases h; exact setAt_length hset

theorem evalArgs_prefix {ops : List Operand} :
    ∀ {xs extra : List LocalSlot},
      operandListBounded xs.length ops = true →
      evalArgs (xs ++ extra) ops =
        (evalArgs xs ops).map (fun (vs, xs') => (vs, xs' ++ extra)) := by
  induction ops with
  | nil => intros; rfl
  | cons op rest ih =>
    intro xs extra hb
    simp only [operandListBounded, Bool.and_eq_true] at hb
    simp only [evalArgs, evalOperand_prefix hb.1]
    cases hop : evalOperand xs op with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨_, xs₁⟩
      have hlen : xs₁.length = xs.length := evalOperand_preserves_length hop
      have hb2 : operandListBounded xs₁.length rest = true := by rw [hlen]; exact hb.2
      simp only [Except.map, ih hb2]
      cases evalArgs xs₁ rest <;> rfl

theorem evalArgs_preserves_length {ops : List Operand} :
    ∀ {xs xs' : List LocalSlot} {vs : List Val},
      evalArgs xs ops = .ok (vs, xs') → xs'.length = xs.length := by
  induction ops with
  | nil => intro _ _ _ h; cases h; rfl
  | cons op rest ih =>
    intro xs xs' vs h
    simp only [evalArgs] at h
    cases hop : evalOperand xs op with
    | error _ => rw [hop] at h; cases h
    | ok pair =>
      rcases pair with ⟨_, xs₁⟩
      rw [hop] at h; simp only [] at h
      cases hrest : evalArgs xs₁ rest with
      | error _ => rw [hrest] at h; cases h
      | ok _ =>
        rw [hrest] at h; cases h
        exact (ih hrest).trans (evalOperand_preserves_length hop)

theorem evalArgs_out_length {ops : List Operand} :
    ∀ {xs xs' : List LocalSlot} {vs : List Val},
      evalArgs xs ops = .ok (vs, xs') → vs.length = ops.length := by
  induction ops with
  | nil => intro _ _ _ h; cases h; rfl
  | cons op rest ih =>
    intro xs xs' vs h
    simp only [evalArgs] at h
    cases hop : evalOperand xs op with
    | error _ => rw [hop] at h; cases h
    | ok pair =>
      rcases pair with ⟨_, xs₁⟩
      rw [hop] at h; simp only [] at h
      cases hrest : evalArgs xs₁ rest with
      | error _ => rw [hrest] at h; cases h
      | ok _ =>
        rw [hrest] at h; cases h
        simp [ih hrest]

theorem evalRvalue_prefix {bodyFeats cpu : List FeatureId} {xs extra : List LocalSlot} {rv : Rvalue}
    (hb : rvalueBounded xs.length rv = true) :
    evalRvalue bodyFeats cpu (xs ++ extra) rv =
      (evalRvalue bodyFeats cpu xs rv).map (fun (v, xs') => (v, xs' ++ extra)) := by
  cases rv with
  | use op => exact evalOperand_prefix hb
  | addNat lhs rhs =>
    simp only [rvalueBounded, Bool.and_eq_true] at hb
    simp only [evalRvalue, evalOperand_prefix hb.1]
    cases hl : evalOperand xs lhs with
    | error _ => rfl
    | ok p1 =>
      rcases p1 with ⟨v1, xs₁⟩
      have hlen := evalOperand_preserves_length hl
      have hr_b : operandBounded xs₁.length rhs = true := by rw [hlen]; exact hb.2
      simp only [Except.map, evalOperand_prefix hr_b]
      cases evalOperand xs₁ rhs with
      | error _ => rfl
      | ok p2 =>
        rcases p2 with ⟨v2, _⟩
        cases v1 <;> cases v2 <;> rfl
  | eqNat lhs rhs =>
    simp only [rvalueBounded, Bool.and_eq_true] at hb
    simp only [evalRvalue, evalOperand_prefix hb.1]
    cases hl : evalOperand xs lhs with
    | error _ => rfl
    | ok p1 =>
      rcases p1 with ⟨v1, xs₁⟩
      have hlen := evalOperand_preserves_length hl
      have hr_b : operandBounded xs₁.length rhs = true := by rw [hlen]; exact hb.2
      simp only [Except.map, evalOperand_prefix hr_b]
      cases evalOperand xs₁ rhs with
      | error _ => rfl
      | ok p2 =>
        rcases p2 with ⟨v2, _⟩
        cases v1 <;> cases v2 <;> rfl
  | featureAdd _ lhs rhs =>
    simp only [rvalueBounded, Bool.and_eq_true] at hb
    simp only [evalRvalue]
    split
    · rfl
    · simp only [evalOperand_prefix hb.1]
      cases hl : evalOperand xs lhs with
      | error _ => rfl
      | ok p1 =>
        rcases p1 with ⟨v1, xs₁⟩
        have hlen := evalOperand_preserves_length hl
        have hr_b : operandBounded xs₁.length rhs = true := by rw [hlen]; exact hb.2
        simp only [Except.map, evalOperand_prefix hr_b]
        cases evalOperand xs₁ rhs with
        | error _ => rfl
        | ok p2 =>
          rcases p2 with ⟨v2, _⟩
          cases v1 <;> cases v2 <;> rfl

theorem evalRvalue_preserves_length {bodyFeats cpu : List FeatureId} {xs xs' : List LocalSlot}
    {rv : Rvalue} {v : Val}
    (h : evalRvalue bodyFeats cpu xs rv = .ok (v, xs')) : xs'.length = xs.length := by
  cases rv with
  | use op => exact evalOperand_preserves_length h
  | addNat lhs rhs =>
    simp only [evalRvalue] at h
    cases hl : evalOperand xs lhs with
    | error _ => rw [hl] at h; cases h
    | ok p1 =>
      rcases p1 with ⟨v1, xs₁⟩
      rw [hl] at h; simp only [] at h
      cases hr : evalOperand xs₁ rhs with
      | error _ => rw [hr] at h; cases h
      | ok p2 =>
        rcases p2 with ⟨v2, _⟩
        rw [hr] at h; simp only [] at h
        cases v1 <;> cases v2 <;> cases h
        exact (evalOperand_preserves_length hr).trans (evalOperand_preserves_length hl)
  | eqNat lhs rhs =>
    simp only [evalRvalue] at h
    cases hl : evalOperand xs lhs with
    | error _ => rw [hl] at h; cases h
    | ok p1 =>
      rcases p1 with ⟨v1, xs₁⟩
      rw [hl] at h; simp only [] at h
      cases hr : evalOperand xs₁ rhs with
      | error _ => rw [hr] at h; cases h
      | ok p2 =>
        rcases p2 with ⟨v2, _⟩
        rw [hr] at h; simp only [] at h
        cases v1 <;> cases v2 <;> cases h
        exact (evalOperand_preserves_length hr).trans (evalOperand_preserves_length hl)
  | featureAdd _ lhs rhs =>
    simp only [evalRvalue] at h
    split at h
    · cases h
    · cases hl : evalOperand xs lhs with
      | error _ => rw [hl] at h; cases h
      | ok p1 =>
        rcases p1 with ⟨v1, xs₁⟩
        rw [hl] at h; simp only [] at h
        cases hr : evalOperand xs₁ rhs with
        | error _ => rw [hr] at h; cases h
        | ok p2 =>
          rcases p2 with ⟨v2, _⟩
          rw [hr] at h; simp only [] at h
          cases v1 <;> cases v2 <;> cases h
          exact (evalOperand_preserves_length hr).trans (evalOperand_preserves_length hl)

theorem writeLocal_prefix {xs extra : List LocalSlot} {dst : LocalId} {v : Val}
    (hdst : dst < xs.length) :
    writeLocal (xs ++ extra) dst v =
      (writeLocal xs dst v).map (fun xs' => xs' ++ extra) := by
  simp only [writeLocal, getAt_append_left hdst]
  cases getAt xs dst with
  | none => rfl
  | some slot =>
    cases slot with
    | dead => rfl
    | liveUninit =>
      simp only [setAt_append_left hdst]
      cases setAt xs dst (.liveVal v) <;> rfl
    | liveVal _ =>
      simp only [setAt_append_left hdst]
      cases setAt xs dst (.liveVal v) <;> rfl

theorem writeLocal_preserves_length {xs xs' : List LocalSlot} {dst : LocalId} {v : Val}
    (h : writeLocal xs dst v = .ok xs') : xs'.length = xs.length := by
  simp only [writeLocal] at h
  cases hg : getAt xs dst with
  | none => rw [hg] at h; cases h
  | some slot =>
    rw [hg] at h
    cases slot with
    | dead => cases h
    | liveUninit =>
      simp only [] at h
      cases hs : setAt xs dst (.liveVal v) with
      | none => rw [hs] at h; cases h
      | some _ => rw [hs] at h; cases h; exact setAt_length hs
    | liveVal _ =>
      simp only [] at h
      cases hs : setAt xs dst (.liveVal v) with
      | none => rw [hs] at h; cases h
      | some _ => rw [hs] at h; cases h; exact setAt_length hs

theorem evalStmt_prefix {bodyFeats cpu : List FeatureId} {xs extra : List LocalSlot}
    {drops : List DropTag} {s : Stmt} (hb : stmtBounded xs.length s = true) :
    evalStmt bodyFeats cpu (xs ++ extra) drops s =
      (evalStmt bodyFeats cpu xs drops s).map (fun (xs', d') => (xs' ++ extra, d')) := by
  cases s with
  | storageLive loc =>
    simp only [stmtBounded, decide_eq_true_eq] at hb
    simp only [evalStmt, setAt_append_left hb]
    cases setAt xs loc .liveUninit <;> rfl
  | storageDead loc =>
    simp only [stmtBounded, decide_eq_true_eq] at hb
    simp only [evalStmt]
    split
    · rfl
    · simp only [setAt_append_left hb]
      cases setAt xs loc .dead <;> rfl
  | assign dst rv =>
    simp only [stmtBounded, Bool.and_eq_true, decide_eq_true_eq] at hb
    simp only [evalStmt, evalRvalue_prefix hb.2]
    cases hrv : evalRvalue bodyFeats cpu xs rv with
    | error _ => rfl
    | ok p =>
      rcases p with ⟨v, xs₁⟩
      have hlen := evalRvalue_preserves_length hrv
      have hdst : dst < xs₁.length := by rw [hlen]; exact hb.1
      simp only [Except.map, writeLocal_prefix hdst]
      cases writeLocal xs₁ dst v <;> rfl
  | dropGuard loc _ =>
    simp only [stmtBounded, decide_eq_true_eq] at hb
    simp only [evalStmt, getAt_append_left hb]
    cases getAt xs loc with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | liveUninit => rfl
      | liveVal _ =>
        simp only [setAt_append_left hb]
        cases setAt xs loc .liveUninit <;> rfl
  | validateDestRef inh =>
    cases inh <;> rfl

theorem evalStmt_preserves_length {bodyFeats cpu : List FeatureId}
    {xs xs' : List LocalSlot} {drops drops' : List DropTag} {s : Stmt}
    (h : evalStmt bodyFeats cpu xs drops s = .ok (xs', drops')) :
    xs'.length = xs.length := by
  cases s with
  | storageLive loc =>
    simp only [evalStmt] at h
    cases hs : setAt xs loc .liveUninit with
    | none => rw [hs] at h; cases h
    | some _ => rw [hs] at h; cases h; exact setAt_length hs
  | storageDead loc =>
    simp only [evalStmt] at h
    split at h
    · cases h
    · cases hs : setAt xs loc .dead with
      | none => rw [hs] at h; cases h
      | some _ => rw [hs] at h; cases h; exact setAt_length hs
  | assign dst rv =>
    simp only [evalStmt] at h
    cases hrv : evalRvalue bodyFeats cpu xs rv with
    | error _ => rw [hrv] at h; cases h
    | ok p =>
      rcases p with ⟨v, xs₁⟩
      rw [hrv] at h; simp only [] at h
      cases hw : writeLocal xs₁ dst v with
      | error _ => rw [hw] at h; cases h
      | ok _ =>
        rw [hw] at h; cases h
        exact (writeLocal_preserves_length hw).trans (evalRvalue_preserves_length hrv)
  | dropGuard loc _ =>
    simp only [evalStmt] at h
    cases hg : getAt xs loc with
    | none => rw [hg] at h; cases h
    | some slot =>
      rw [hg] at h
      cases slot with
      | dead => cases h
      | liveUninit => cases h
      | liveVal _ =>
        simp only [] at h
        cases hs : setAt xs loc .liveUninit with
        | none => rw [hs] at h; cases h
        | some _ => rw [hs] at h; cases h; exact setAt_length hs
  | validateDestRef inh =>
    cases inh <;> simp [evalStmt] at h
    exact h.1 ▸ rfl

theorem evalStmts_prefix {bodyFeats cpu : List FeatureId} {ss : List Stmt} :
    ∀ {xs extra : List LocalSlot} {drops : List DropTag},
      stmtsBounded xs.length ss = true →
      evalStmts bodyFeats cpu (xs ++ extra) drops ss =
        (evalStmts bodyFeats cpu xs drops ss).map (fun (xs', d') => (xs' ++ extra, d')) := by
  induction ss with
  | nil => intros; rfl
  | cons s rest ih =>
    intro xs extra drops hb
    simp only [stmtsBounded, Bool.and_eq_true] at hb
    simp only [evalStmts, evalStmt_prefix hb.1]
    cases hs : evalStmt bodyFeats cpu xs drops s with
    | error _ => rfl
    | ok p =>
      rcases p with ⟨xs₁, _⟩
      have hlen := evalStmt_preserves_length hs
      have hb2 : stmtsBounded xs₁.length rest = true := by rw [hlen]; exact hb.2
      simp only [Except.map]
      exact ih hb2

theorem evalStmts_preserves_length {bodyFeats cpu : List FeatureId} {ss : List Stmt} :
    ∀ {xs xs' : List LocalSlot} {drops drops' : List DropTag},
      evalStmts bodyFeats cpu xs drops ss = .ok (xs', drops') →
      xs'.length = xs.length := by
  induction ss with
  | nil => intro _ _ _ _ h; cases h; rfl
  | cons s rest ih =>
    intro xs xs' drops drops' h
    simp only [evalStmts] at h
    cases hs : evalStmt bodyFeats cpu xs drops s with
    | error _ => rw [hs] at h; cases h
    | ok _ =>
      rw [hs] at h; simp only [] at h
      exact (ih h).trans (evalStmt_preserves_length hs)

theorem evalStmts_append {bodyFeats cpu : List FeatureId} (s1 s2 : List Stmt) :
    ∀ (xs : List LocalSlot) (drops : List DropTag),
      evalStmts bodyFeats cpu xs drops (s1 ++ s2) =
        match evalStmts bodyFeats cpu xs drops s1 with
        | .error f => .error f
        | .ok (xs₁, drops₁) => evalStmts bodyFeats cpu xs₁ drops₁ s2 := by
  induction s1 with
  | nil => intros; rfl
  | cons s rest ih =>
    intro xs drops
    simp only [List.cons_append, evalStmts]
    cases evalStmt bodyFeats cpu xs drops s with
    | error _ => rfl
    | ok p => exact ih p.1 p.2

theorem evalOperand_shift (xs ys : List LocalSlot) (op : Operand) :
    evalOperand (xs ++ ys) (shiftOperand xs.length op) =
      (evalOperand ys op).map (fun (v, ys') => (v, xs ++ ys')) := by
  cases op with
  | constVal _ => rfl
  | copy loc =>
    simp only [shiftOperand, evalOperand, getAt_append_right]
    cases getAt ys loc with
    | none => rfl
    | some slot => cases slot <;> rfl
  | move loc =>
    simp only [shiftOperand, evalOperand, getAt_append_right]
    cases getAt ys loc with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | liveUninit => rfl
      | liveVal _ =>
        simp only [setAt_append_right]
        cases setAt ys loc .liveUninit <;> rfl

theorem evalRvalue_shift (bodyFeats cpu : List FeatureId) (xs ys : List LocalSlot) (rv : Rvalue) :
    evalRvalue bodyFeats cpu (xs ++ ys) (shiftRvalue xs.length rv) =
      (evalRvalue bodyFeats cpu ys rv).map (fun (v, ys') => (v, xs ++ ys')) := by
  cases rv with
  | use op => exact evalOperand_shift xs ys op
  | addNat lhs rhs =>
    simp only [shiftRvalue, evalRvalue, evalOperand_shift]
    cases evalOperand ys lhs with
    | error _ => rfl
    | ok p1 =>
      rcases p1 with ⟨v1, ys₁⟩
      simp only [Except.map, evalOperand_shift]
      cases evalOperand ys₁ rhs with
      | error _ => rfl
      | ok p2 =>
        rcases p2 with ⟨v2, _⟩
        cases v1 <;> cases v2 <;> rfl
  | eqNat lhs rhs =>
    simp only [shiftRvalue, evalRvalue, evalOperand_shift]
    cases evalOperand ys lhs with
    | error _ => rfl
    | ok p1 =>
      rcases p1 with ⟨v1, ys₁⟩
      simp only [Except.map, evalOperand_shift]
      cases evalOperand ys₁ rhs with
      | error _ => rfl
      | ok p2 =>
        rcases p2 with ⟨v2, _⟩
        cases v1 <;> cases v2 <;> rfl
  | featureAdd _ lhs rhs =>
    simp only [shiftRvalue, evalRvalue]
    split
    · rfl
    · simp only [evalOperand_shift]
      cases evalOperand ys lhs with
      | error _ => rfl
      | ok p1 =>
        rcases p1 with ⟨v1, ys₁⟩
        simp only [Except.map, evalOperand_shift]
        cases evalOperand ys₁ rhs with
        | error _ => rfl
        | ok p2 =>
          rcases p2 with ⟨v2, _⟩
          cases v1 <;> cases v2 <;> rfl

theorem writeLocal_shift (xs ys : List LocalSlot) (dst : LocalId) (v : Val) :
    writeLocal (xs ++ ys) (xs.length + dst) v =
      (writeLocal ys dst v).map (fun ys' => xs ++ ys') := by
  simp only [writeLocal, getAt_append_right]
  cases getAt ys dst with
  | none => rfl
  | some slot =>
    cases slot with
    | dead => rfl
    | liveUninit =>
      simp only [setAt_append_right]
      cases setAt ys dst (.liveVal v) <;> rfl
    | liveVal _ =>
      simp only [setAt_append_right]
      cases setAt ys dst (.liveVal v) <;> rfl

theorem evalStmt_shift {bodyFeats cpu : List FeatureId} (xs ys : List LocalSlot)
    (drops : List DropTag) (s : Stmt) (hv : stmtValidForCallee s = true) :
    evalStmt bodyFeats cpu (xs ++ ys) drops (shiftStmt xs.length s) =
      (evalStmt bodyFeats cpu ys drops s).map (fun (ys', d') => (xs ++ ys', d')) := by
  cases s with
  | storageLive loc =>
    simp only [shiftStmt, evalStmt, setAt_append_right]
    cases setAt ys loc .liveUninit <;> rfl
  | storageDead loc =>
    simp only [stmtValidForCallee, Bool.not_eq_true'] at hv
    cases loc with
    | zero => cases hv
    | succ k =>
      have hne1 : Nat.beq (xs.length + (k + 1)) 0 = false := by
        rw [Nat.add_succ]; rfl
      have hne2 : Nat.beq (k + 1) 0 = false := rfl
      simp only [shiftStmt, evalStmt, hne1, hne2, setAt_append_right]
      cases setAt ys (k + 1) .dead <;> rfl
  | assign dst rv =>
    simp only [shiftStmt, evalStmt, evalRvalue_shift]
    cases evalRvalue bodyFeats cpu ys rv with
    | error _ => rfl
    | ok p =>
      rcases p with ⟨v, ys₁⟩
      simp only [Except.map, writeLocal_shift]
      cases writeLocal ys₁ dst v <;> rfl
  | dropGuard loc _ =>
    simp only [shiftStmt, evalStmt, getAt_append_right]
    cases getAt ys loc with
    | none => rfl
    | some slot =>
      cases slot with
      | dead => rfl
      | liveUninit => rfl
      | liveVal _ =>
        simp only [setAt_append_right]
        cases setAt ys loc .liveUninit <;> rfl
  | validateDestRef inh =>
    cases inh <;> rfl

theorem evalStmts_shift {bodyFeats cpu : List FeatureId} (xs : List LocalSlot) (ss : List Stmt) :
    ∀ (ys : List LocalSlot) (drops : List DropTag),
      stmtsValidForCallee ss = true →
      evalStmts bodyFeats cpu (xs ++ ys) drops (ss.map (shiftStmt xs.length)) =
        (evalStmts bodyFeats cpu ys drops ss).map (fun (ys', d') => (xs ++ ys', d')) := by
  induction ss with
  | nil => intros; rfl
  | cons s rest ih =>
    intro ys drops hv
    simp only [stmtsValidForCallee, Bool.and_eq_true] at hv
    simp only [List.map_cons, evalStmts, evalStmt_shift xs ys drops s hv.1]
    cases evalStmt bodyFeats cpu ys drops s with
    | error _ => rfl
    | ok p =>
      simp only [Except.map]
      exact ih p.1 p.2 hv.2

theorem evalStmts_shift_ok {sFeats cFeats cpu : List FeatureId}
    {xs ys ys₁ : List LocalSlot} {drops drops₁ : List DropTag} {N : Nat} {ss : List Stmt}
    (hlen : xs.length = N) (hf : sFeats = cFeats)
    (hv : stmtsValidForCallee ss = true)
    (hs : evalStmts cFeats cpu ys drops ss = .ok (ys₁, drops₁)) :
    evalStmts sFeats cpu (xs ++ ys) drops (ss.map (shiftStmt N)) =
      .ok (xs ++ ys₁, drops₁) := by
  rw [← hlen, hf, evalStmts_shift xs ss ys drops hv, hs]
  rfl

theorem evalStmts_shift_err {sFeats cFeats cpu : List FeatureId}
    {xs ys : List LocalSlot} {drops : List DropTag} {N : Nat} {ss : List Stmt} {err : Fault}
    (hlen : xs.length = N) (hf : sFeats = cFeats)
    (hv : stmtsValidForCallee ss = true)
    (hs : evalStmts cFeats cpu ys drops ss = .error err) :
    evalStmts sFeats cpu (xs ++ ys) drops (ss.map (shiftStmt N)) = .error err := by
  rw [← hlen, hf, evalStmts_shift xs ss ys drops hv, hs]
  rfl

theorem evalOperand_shift_ok {xs ys ys₁ : List LocalSlot} {N : Nat} {op : Operand} {v : Val}
    (hlen : xs.length = N) (hc : evalOperand ys op = .ok (v, ys₁)) :
    evalOperand (xs ++ ys) (shiftOperand N op) = .ok (v, xs ++ ys₁) := by
  rw [← hlen, evalOperand_shift xs ys op, hc]
  rfl

theorem evalOperand_shift_err {xs ys : List LocalSlot} {N : Nat} {op : Operand} {err : Fault}
    (hlen : xs.length = N) (hc : evalOperand ys op = .error err) :
    evalOperand (xs ++ ys) (shiftOperand N op) = .error err := by
  rw [← hlen, evalOperand_shift xs ys op, hc]
  rfl

/-! ## Section 7: Call Prelude Exact Frame-Construction Lemma -/

theorem resetDeadRange_correct (bodyFeats cpu : List FeatureId) (tailSlots : List LocalSlot) :
    ∀ (prefixSlots : List LocalSlot) (drops : List DropTag),
      1 ≤ prefixSlots.length →
      evalStmts bodyFeats cpu (prefixSlots ++ tailSlots) drops
        (resetDeadRange prefixSlots.length tailSlots.length) =
        .ok (prefixSlots ++ replicateSlot tailSlots.length LocalSlot.dead, drops) := by
  induction tailSlots with
  | nil => intros; rfl
  | cons slot rest ih =>
    intro prefixSlots drops hpos
    have hne0 : Nat.beq prefixSlots.length 0 = false := by
      cases hlen : prefixSlots.length with
      | zero => rw [hlen] at hpos; cases hpos
      | succ _ => rfl
    have hset : setAt (prefixSlots ++ (slot :: rest)) prefixSlots.length LocalSlot.dead =
        some (prefixSlots ++ (LocalSlot.dead :: rest)) := by
      have h0 := setAt_append_right prefixSlots (slot :: rest) 0 LocalSlot.dead
      rw [Nat.add_zero] at h0
      exact h0
    simp only [List.length_cons, resetDeadRange, evalStmts, evalStmt, hne0, hset,
      Bool.false_eq_true, ↓reduceIte]
    have hassoc : prefixSlots ++ (LocalSlot.dead :: rest) = (prefixSlots ++ [LocalSlot.dead]) ++ rest := by
      simp [List.append_assoc]
    have hlen2 : (prefixSlots ++ [LocalSlot.dead]).length = prefixSlots.length + 1 := by simp
    have hpos2 : 1 ≤ (prefixSlots ++ [LocalSlot.dead]).length := by
      rw [hlen2]; exact Nat.le_trans hpos (Nat.le_succ _)
    rw [hassoc, ← hlen2, ih (prefixSlots ++ [LocalSlot.dead]) drops hpos2]
    simp [List.append_assoc, replicateSlot]

theorem buildArgBindings_correct (bodyFeats cpu : List FeatureId) (argOps : List Operand) :
    ∀ (callerSlots accParams remSlots : List LocalSlot) (drops : List DropTag),
      operandListBounded callerSlots.length argOps = true →
      argOps.length ≤ remSlots.length →
      evalStmts bodyFeats cpu (callerSlots ++ accParams ++ remSlots) drops
        (buildArgBindings (callerSlots.length + accParams.length) argOps) =
        match evalArgs callerSlots argOps with
        | .error f => .error f
        | .ok (vals, callerSlots') =>
          .ok (callerSlots' ++ accParams ++ vals.map LocalSlot.liveVal ++
               remSlots.drop argOps.length, drops) := by
  induction argOps with
  | nil =>
    intros
    simp [buildArgBindings, evalStmts, evalArgs]
  | cons op rest ih =>
    intro callerSlots accParams remSlots drops hb hrem
    cases remSlots with
    | nil => cases hrem
    | cons r0 rRest =>
      simp only [operandListBounded, Bool.and_eq_true] at hb
      have hprefix_op : operandBounded (callerSlots ++ accParams).length op = true := by
        cases op with
        | constVal _ => rfl
        | copy loc | move loc =>
          simp only [operandBounded, decide_eq_true_eq, List.length_append] at hb ⊢
          exact Nat.lt_of_lt_of_le hb.1 (Nat.le_add_right _ _)
      have hset_live :
          setAt ((callerSlots ++ accParams) ++ (r0 :: rRest))
            (callerSlots.length + accParams.length) LocalSlot.liveUninit =
          some ((callerSlots ++ accParams) ++ (LocalSlot.liveUninit :: rRest)) := by
        have hlen_app : (callerSlots ++ accParams).length = callerSlots.length + accParams.length :=
          List.length_append
        rw [← hlen_app]
        have h0 := setAt_append_right (callerSlots ++ accParams) (r0 :: rRest) 0 LocalSlot.liveUninit
        rw [Nat.add_zero] at h0
        exact h0
      simp only [buildArgBindings, evalStmts, evalStmt, hset_live]
      have hop_ext :
          evalOperand ((callerSlots ++ accParams) ++ (LocalSlot.liveUninit :: rRest)) op =
          (evalOperand callerSlots op).map
            (fun (v, cs') => (v, (cs' ++ accParams) ++ (LocalSlot.liveUninit :: rRest))) := by
        have h1 := evalOperand_prefix hprefix_op (extra := LocalSlot.liveUninit :: rRest)
        have h2 := evalOperand_prefix hb.1 (extra := accParams)
        rw [h1, h2]
        cases evalOperand callerSlots op <;> rfl
      simp only [evalRvalue, hop_ext, evalArgs]
      cases hop : evalOperand callerSlots op with
      | error _ => rfl
      | ok p =>
        rcases p with ⟨v, cs₁⟩
        have hcs_len : cs₁.length = callerSlots.length := evalOperand_preserves_length hop
        have hwrite :
            writeLocal ((cs₁ ++ accParams) ++ (LocalSlot.liveUninit :: rRest))
              (callerSlots.length + accParams.length) v =
            .ok ((cs₁ ++ accParams) ++ (LocalSlot.liveVal v :: rRest)) := by
          have hlen_app : (cs₁ ++ accParams).length = callerSlots.length + accParams.length := by
            simp [hcs_len]
          rw [← hlen_app]
          have hw := writeLocal_shift (cs₁ ++ accParams) (LocalSlot.liveUninit :: rRest) 0 v
          rw [Nat.add_zero] at hw
          exact hw
        simp only [Except.map, hwrite]
        have hreassoc :
            (cs₁ ++ accParams) ++ (LocalSlot.liveVal v :: rRest) =
            (cs₁ ++ (accParams ++ [LocalSlot.liveVal v])) ++ rRest := by
          simp [List.append_assoc]
        have hidx :
            callerSlots.length + accParams.length + 1 =
            cs₁.length + (accParams ++ [LocalSlot.liveVal v]).length := by
          simp [hcs_len, Nat.add_assoc]
        have hb_rest : operandListBounded cs₁.length rest = true := by
          rw [hcs_len]; exact hb.2
        have hrem_rest : rest.length ≤ rRest.length :=
          Nat.le_of_succ_le_succ hrem
        rw [hreassoc, hidx, ih cs₁ (accParams ++ [LocalSlot.liveVal v]) rRest drops hb_rest hrem_rest]
        cases evalArgs cs₁ rest with
        | error _ => rfl
        | ok _ => simp [List.append_assoc]

theorem buildCallPrelude_correct (bodyFeats cpu : List FeatureId)
    (callerSlots extraSlots : List LocalSlot) (drops : List DropTag)
    (callee : Body) (argOps : List Operand)
    (hpos : 1 ≤ callerSlots.length)
    (hcallee_wf : 1 + callee.argCount ≤ callee.numLocals)
    (hextra_len : extraSlots.length = callee.numLocals)
    (harg_len : argOps.length = callee.argCount)
    (hb : operandListBounded callerSlots.length argOps = true) :
    evalStmts bodyFeats cpu (callerSlots ++ extraSlots) drops
      (buildCallPrelude callerSlots.length callee.argCount callee.numLocals argOps) =
      match evalArgs callerSlots argOps with
      | .error f => .error f
      | .ok (argVals, callerSlots') =>
        match initFrameLocals callee argVals with
        | none => .error .unsupported
        | some calleeLocals₀ => .ok (callerSlots' ++ calleeLocals₀, drops) := by
  cases extraSlots with
  | nil =>
    exfalso
    have h0 : 1 + callee.argCount ≤ 0 := by
      rw [List.length_nil] at hextra_len
      rw [← hextra_len] at hcallee_wf
      exact hcallee_wf
    have hpos_c : 1 ≤ 1 + callee.argCount := Nat.le_add_right 1 _
    exact absurd (Nat.le_trans hpos_c h0) (by decide)
  | cons e0 eRest =>
    have hset0 :
        setAt (callerSlots ++ (e0 :: eRest)) callerSlots.length LocalSlot.liveUninit =
        some (callerSlots ++ (LocalSlot.liveUninit :: eRest)) := by
      have h0 := setAt_append_right callerSlots (e0 :: eRest) 0 LocalSlot.liveUninit
      rw [Nat.add_zero] at h0
      exact h0
    simp only [buildCallPrelude, evalStmts, evalStmt, hset0, evalStmts_append]
    have hsplit :
        callerSlots ++ (LocalSlot.liveUninit :: eRest) =
        callerSlots ++ [LocalSlot.liveUninit] ++ eRest := by
      simp [List.append_assoc]
    have hrem : argOps.length ≤ eRest.length := by
      simp only [List.length_cons] at hextra_len
      rw [harg_len]
      have hbound : 1 + callee.argCount ≤ 1 + eRest.length := by
        rw [Nat.add_comm 1 eRest.length, hextra_len]
        exact hcallee_wf
      exact Nat.le_of_add_le_add_left hbound
    have hbind := buildArgBindings_correct bodyFeats cpu argOps callerSlots [LocalSlot.liveUninit] eRest drops hb hrem
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at hbind
    rw [hsplit, hbind]
    cases hargs : evalArgs callerSlots argOps with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨vals, cs'⟩
      simp only []
      have hvals_len : vals.length = callee.argCount :=
        (evalArgs_out_length hargs).trans harg_len
      have hcs'_len : cs'.length = callerSlots.length :=
        evalArgs_preserves_length hargs
      have hdrop_len : (eRest.drop argOps.length).length = callee.numLocals - (1 + callee.argCount) := by
        simp only [List.length_cons] at hextra_len
        rw [List.length_drop, harg_len]
        have heRest : eRest.length = callee.numLocals - 1 := by
          rw [← hextra_len]; rfl
        rw [heRest, Nat.sub_sub, Nat.add_comm 1 callee.argCount]
      let pref := cs' ++ [LocalSlot.liveUninit] ++ vals.map LocalSlot.liveVal
      have hpref_len : pref.length = callerSlots.length + 1 + callee.argCount := by
        simp only [pref, List.length_append, List.length_cons, List.length_nil,
          List.length_map, hcs'_len, hvals_len, Nat.zero_add, Nat.add_assoc]
      have hpref_pos : 1 ≤ pref.length := by
        rw [hpref_len]
        exact Nat.le_trans hpos (Nat.le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ _))
      have hreset := resetDeadRange_correct bodyFeats cpu (eRest.drop argOps.length) pref drops hpref_pos
      rw [hpref_len, hdrop_len] at hreset
      have hinit : initFrameLocals callee vals =
          some ([LocalSlot.liveUninit] ++ vals.map LocalSlot.liveVal ++
                replicateSlot (callee.numLocals - (1 + callee.argCount)) LocalSlot.dead) := by
        simp [initFrameLocals, hvals_len, Nat.beq_refl, hcallee_wf]
      rw [hinit]
      have hassoc :
          cs' ++ [LocalSlot.liveUninit] ++ vals.map LocalSlot.liveVal ++ eRest.drop argOps.length =
          pref ++ eRest.drop argOps.length := rfl
      rw [hassoc, hreset]
      simp [pref, List.append_assoc]

/-! ## Section 8: Intra-Procedural Equivalence for Call-Free Bodies (`Anneal` Bridge) -/

theorem getAt_callFree_not_call {bbs : List BasicBlock} :
    ∀ {idx : Nat} {bb : BasicBlock},
      isCallFreeBlocks bbs = true →
      getAt bbs idx = some bb →
      ∀ c a d t u, bb.term ≠ .call c a d t u := by
  induction bbs with
  | nil => intro _ _ _ hget; cases hget
  | cons b rest ih =>
    intro idx bb hcf hget
    simp only [isCallFreeBlocks] at hcf
    cases idx with
    | zero =>
      cases hget
      intro c a d t u hterm
      rw [hterm] at hcf
      cases hcf
    | succ _ =>
      cases hb : b.term <;> rw [hb] at hcf
      case call => cases hcf
      all_goals exact ih hcf hget

theorem callFree_evalBlock_eq (prog : Program) (body : Body) (cpu : List FeatureId)
    (hcf : isCallFree body = true) :
    ∀ fuel bbIdx locals drops,
      evalBlockInterproc prog cpu fuel body bbIdx locals drops =
      evalBlockIntra body cpu fuel bbIdx locals drops := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro bbIdx locals drops
    simp only [evalBlockInterproc, evalBlockIntra]
    cases hget : getAt body.blocks bbIdx with
    | none => rfl
    | some bb =>
      simp only []
      cases evalStmts body.features cpu locals drops bb.stmts with
      | error _ => rfl
      | ok p =>
        rcases p with ⟨locals₁, drops₁⟩
        simp only []
        cases hterm : bb.term with
        | goto t => exact ih t locals₁ drops₁
        | switchBool cond _ _ =>
          simp only []
          cases evalOperand locals₁ cond with
          | error _ => rfl
          | ok p2 =>
            rcases p2 with ⟨v, locals₂⟩
            cases v with
            | int _ => rfl
            | bool b => cases b <;> exact ih _ locals₂ drops₁
        | return_ | unreachable | unwindTerminate | unwindResume => rfl
        | unwindStart u =>
          cases u with
          | cleanup cbb => exact ih cbb locals₁ drops₁
          | continue_ | terminate | unreachable => rfl
        | call c a d t u =>
          exfalso
          exact getAt_callFree_not_call hcf hget c a d t u hterm

theorem callFree_evalBody_eq (prog : Program) (body : Body) (cpu : List FeatureId)
    (hcf : isCallFree body = true) (fuel : Nat) (args : List Val) :
    evalBodyInterproc prog body cpu fuel args = evalBodyIntra body cpu fuel args := by
  simp only [evalBodyInterproc, evalBodyIntra]
  split
  · rfl
  · cases initFrameLocals body args with
    | none => rfl
    | some locals₀ => exact callFree_evalBlock_eq prog body cpu hcf fuel 0 locals₀ []

theorem callFree_execBlock_iff (prog : Program) (body : Body) (cpu : List FeatureId)
    (hcf : isCallFree body = true) :
    ∀ bbIdx locals drops out,
      ExecBlock prog cpu body bbIdx locals drops out ↔
      ExecBlockIntra cpu body bbIdx locals drops out := by
  intro bbIdx locals drops out
  constructor
  · intro h
    generalize hb : body = b₀ at h
    induction h with
    | oobBlock hg => subst hb; exact .oobBlock hg
    | stmtFault hg hs => subst hb; exact .stmtFault hg hs
    | goto hg hs ht _ ih => subst hb; exact .goto hg hs ht (ih rfl)
    | switchFault hg hs ht hc => subst hb; exact .switchFault hg hs ht hc
    | switchNonBool hg hs ht hc => subst hb; exact .switchNonBool hg hs ht hc
    | switchTrue hg hs ht hc _ ih => subst hb; exact .switchTrue hg hs ht hc (ih rfl)
    | switchFalse hg hs ht hc _ ih => subst hb; exact .switchFalse hg hs ht hc (ih rfl)
    | returnCleanupFault hg hs ht hcl => subst hb; exact .returnCleanupFault hg hs ht hcl
    | returnOk hg hs ht hcl h0 => subst hb; exact .returnOk hg hs ht hcl h0
    | returnUninitOrDead hg hs ht hcl h0 hor => subst hb; exact .returnUninitOrDead hg hs ht hcl h0 hor
    | returnNoSlot hg hs ht hcl h0 => subst hb; exact .returnNoSlot hg hs ht hcl h0
    | unreachable hg hs ht => subst hb; exact .unreachable hg hs ht
    | unwindTerminate hg hs ht => subst hb; exact .unwindTerminate hg hs ht
    | unwindResumeOk hg hs ht hcl => subst hb; exact .unwindResumeOk hg hs ht hcl
    | unwindResumeFault hg hs ht hcl => subst hb; exact .unwindResumeFault hg hs ht hcl
    | unwindStartCleanup hg hs ht _ ih => subst hb; exact .unwindStartCleanup hg hs ht (ih rfl)
    | unwindStartContinue hg hs ht => subst hb; exact .unwindStartContinue hg hs ht
    | unwindStartTerminate hg hs ht => subst hb; exact .unwindStartTerminate hg hs ht
    | unwindStartUnreachable hg hs ht => subst hb; exact .unwindStartUnreachable hg hs ht
    | callInCleanupFault hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callMissingCallee hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callFeatureFault hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callArgFault hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callInitFault hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callReturnOk hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callReturnWriteFault hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callReturnDiverging hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callUnwindCleanup hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callUnwindContinue hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callUnwindTerminate hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callUnwindUnreachable hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callPropagateAbort hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
    | callPropagateFault hg _ ht => subst hb; exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht
  · intro h
    induction h with
    | oobBlock hg => exact .oobBlock hg
    | stmtFault hg hs => exact .stmtFault hg hs
    | goto hg hs ht _ ih => exact .goto hg hs ht ih
    | switchFault hg hs ht hc => exact .switchFault hg hs ht hc
    | switchNonBool hg hs ht hc => exact .switchNonBool hg hs ht hc
    | switchTrue hg hs ht hc _ ih => exact .switchTrue hg hs ht hc ih
    | switchFalse hg hs ht hc _ ih => exact .switchFalse hg hs ht hc ih
    | returnCleanupFault hg hs ht hcl => exact .returnCleanupFault hg hs ht hcl
    | returnOk hg hs ht hcl h0 => exact .returnOk hg hs ht hcl h0
    | returnUninitOrDead hg hs ht hcl h0 hor => exact .returnUninitOrDead hg hs ht hcl h0 hor
    | returnNoSlot hg hs ht hcl h0 => exact .returnNoSlot hg hs ht hcl h0
    | unreachable hg hs ht => exact .unreachable hg hs ht
    | unwindTerminate hg hs ht => exact .unwindTerminate hg hs ht
    | unwindResumeOk hg hs ht hcl => exact .unwindResumeOk hg hs ht hcl
    | unwindResumeFault hg hs ht hcl => exact .unwindResumeFault hg hs ht hcl
    | unwindStartCleanup hg hs ht _ ih => exact .unwindStartCleanup hg hs ht ih
    | unwindStartContinue hg hs ht => exact .unwindStartContinue hg hs ht
    | unwindStartTerminate hg hs ht => exact .unwindStartTerminate hg hs ht
    | unwindStartUnreachable hg hs ht => exact .unwindStartUnreachable hg hs ht
    | callFailClosed hg _ ht => exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht

theorem callFree_execBody_iff (prog : Program) (body : Body) (cpu : List FeatureId)
    (hcf : isCallFree body = true) (args : List Val) (out : Outcome) :
    ExecBody prog body cpu args out ↔ ExecBodyIntra body cpu args out := by
  simp only [ExecBody, ExecBodyIntra]
  split
  · exact Iff.rfl
  · cases initFrameLocals body args with
    | none => exact Iff.rfl
    | some locals₀ => exact callFree_execBlock_iff prog body cpu hcf 0 locals₀ [] out

/-! ## Section 9: Main Bisimulation Theorem (`inlineCallSite_bisimulation`) -/

theorem blocksWellFormed_getAt {localLimit blockLimit : Nat} {chk : Bool} {bbs : List BasicBlock} :
    ∀ {idx : Nat} {bb : BasicBlock},
      blocksWellFormed localLimit blockLimit chk bbs = true →
      getAt bbs idx = some bb →
      stmtsBounded localLimit bb.stmts = true ∧
      (chk = true → stmtsValidForCallee bb.stmts = true) ∧
      termBounded localLimit blockLimit bb.term = true := by
  induction bbs with
  | nil => intro _ _ _ hget; cases hget
  | cons _ _ ih =>
    intro idx bb hwf hget
    simp only [blocksWellFormed, Bool.and_eq_true] at hwf
    cases idx with
    | zero =>
      cases hget
      refine ⟨hwf.1.1.1, ?_, hwf.1.2⟩
      intro hchk
      rw [hchk] at hwf
      exact hwf.1.1.2
    | succ _ =>
      exact ih hwf.2 hget

def CalleePostSpliced (prog : Program) (cpu : List FeatureId)
    (spliced : Body) (calleeNumLocals : Nat)
    (callerLocals₂ : List LocalSlot) (dst : LocalId)
    (target : Option BlockId) (unwind : UnwindAction)
    (outC outFinal : Outcome) : Prop :=
  match outC with
  | .returned retVal drops₂ =>
    match target with
    | none => outFinal = .fault .undefined
    | some retBb =>
      match writeLocal callerLocals₂ dst retVal with
      | .error f => outFinal = .fault f
      | .ok callerLocals₃ =>
        ∀ extra, extra.length = calleeNumLocals →
          ExecBlock prog cpu spliced retBb (callerLocals₃ ++ extra) drops₂ outFinal
  | .unwound drops₂ =>
    match unwind with
    | .cleanup cbb =>
      ∀ extra, extra.length = calleeNumLocals →
        ExecBlock prog cpu spliced cbb (callerLocals₂ ++ extra) drops₂ outFinal
    | .continue_ => outFinal = .unwound drops₂
    | .terminate => outFinal = .aborted drops₂
    | .unreachable => outFinal = .fault .undefined
  | .aborted drops₂ => outFinal = .aborted drops₂
  | .fault f => outFinal = .fault f

def CalleePostCaller (prog : Program) (cpu : List FeatureId)
    (caller : Body) (callerLocals₂ : List LocalSlot) (dst : LocalId)
    (target : Option BlockId) (unwind : UnwindAction)
    (outC outFinal : Outcome) : Prop :=
  match outC with
  | .returned retVal drops₂ =>
    match target with
    | none => outFinal = .fault .undefined
    | some retBb =>
      match writeLocal callerLocals₂ dst retVal with
      | .error f => outFinal = .fault f
      | .ok callerLocals₃ =>
        ExecBlock prog cpu caller retBb callerLocals₃ drops₂ outFinal
  | .unwound drops₂ =>
    match unwind with
    | .cleanup cbb => ExecBlock prog cpu caller cbb callerLocals₂ drops₂ outFinal
    | .continue_ => outFinal = .unwound drops₂
    | .terminate => outFinal = .aborted drops₂
    | .unreachable => outFinal = .fault .undefined
  | .aborted drops₂ => outFinal = .aborted drops₂
  | .fault f => outFinal = .fault f

theorem integrateBlock_switchBool {N B tr : Nat} {tgt : Option BlockId} {u : UnwindAction}
    {bb : BasicBlock} {cond : Operand} {tT fT : BlockId}
    (ht : bb.term = .switchBool cond tT fT) :
    (integrateBlock N B tr tgt u bb).term =
      .switchBool (shiftOperand N cond) (B + tT) (B + fT) := by
  simp [integrateBlock, ht, integrateTerm]

/-- Forward embedding of `callee` (`ExecBlockIntra`) into `spliced` blocks `B + cb`. -/
theorem callee_exec_forward
    {prog : Program} {cpu : List FeatureId}
    {caller callee spliced : Body}
    {patchedBlocks : List BasicBlock}
    {dst : LocalId} {target : Option BlockId} {unwind : UnwindAction}
    (hcallee_wf : bodyWellFormed callee true = true)
    (hcf : isCallFree callee = true)
    (hfeats : callee.features = caller.features)
    (hdst : dst < caller.numLocals)
    (hpatched_len : patchedBlocks.length = caller.blocks.length)
    (hspliced : spliced = {
      numLocals := caller.numLocals + callee.numLocals
      argCount := caller.argCount
      features := caller.features
      blocks := patchedBlocks ++
        callee.blocks.map (integrateBlock caller.numLocals caller.blocks.length
          (caller.blocks.length + callee.blocks.length) target unwind) ++
        mkReturnTrampoline caller.numLocals dst target
    })
    {cb : BlockId} {calleeLocals : List LocalSlot}
    {drops : List DropTag} {outC : Outcome}
    (hexec : ExecBlockIntra cpu callee cb calleeLocals drops outC) :
    cb < callee.blocks.length →
    calleeLocals.length = callee.numLocals →
    ∀ (callerLocals₂ : List LocalSlot) (outFinal : Outcome),
      callerLocals₂.length = caller.numLocals →
      CalleePostSpliced prog cpu spliced callee.numLocals
        callerLocals₂ dst target unwind outC outFinal →
      ExecBlock prog cpu spliced (caller.blocks.length + cb)
        (callerLocals₂ ++ calleeLocals) drops outFinal := by
  simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcallee_wf
  have hget_spliced_cb : ∀ idx bb,
      getAt callee.blocks idx = some bb →
      getAt spliced.blocks (caller.blocks.length + idx) =
        some (integrateBlock caller.numLocals caller.blocks.length
          (caller.blocks.length + callee.blocks.length) target unwind bb) := by
    intro idx bb hg
    have hlt : idx < callee.blocks.length := getAt_some_lt hg
    have hidx_eq : caller.blocks.length + idx = patchedBlocks.length + idx := by
      rw [hpatched_len]
    have hlt_map : idx < (callee.blocks.map (integrateBlock caller.numLocals caller.blocks.length
        (caller.blocks.length + callee.blocks.length) target unwind)).length := by
      simp [hlt]
    rw [hspliced]
    simp only [List.append_assoc]
    rw [hidx_eq, getAt_append_right patchedBlocks _ idx, getAt_append_left hlt_map, getAt_map, hg]
    rfl
  have hspliced_feats : spliced.features = callee.features := by
    rw [hspliced]; exact hfeats.symm
  induction hexec with
  | oobBlock hg =>
    intro hcb
    rcases getAt_lt_some hcb with ⟨_, hsome⟩
    rw [hg] at hsome; cases hsome
  | stmtFault hg hs =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .stmtFault (hget_spliced_cb _ _ hg)
      (evalStmts_shift_err hcs_len hspliced_feats (hvalid rfl) hs)
  | goto hg hs ht _ ih =>
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, htb⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    rw [ht] at htb
    simp only [termBounded, decide_eq_true_eq] at htb
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    exact .goto (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm])
      (ih htb hcl₁_len callerLocals₂ outFinal hcs_len hpost)
  | switchFault hg hs ht hc =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .switchFault
      (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (integrateBlock_switchBool ht)
      (evalOperand_shift_err hcs_len hc)
  | switchNonBool hg hs ht hc =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .switchNonBool
      (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (integrateBlock_switchBool ht)
      (evalOperand_shift_ok hcs_len hc)
  | switchTrue hg hs ht hc _ ih =>
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, htb⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    have hcl₂_len := (evalOperand_preserves_length hc).trans hcl₁_len
    exact .switchTrue
      (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (integrateBlock_switchBool ht)
      (evalOperand_shift_ok hcs_len hc)
      (ih htb.1.2 hcl₂_len callerLocals₂ outFinal hcs_len hpost)
  | switchFalse hg hs ht hc _ ih =>
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, htb⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    have hcl₂_len := (evalOperand_preserves_length hc).trans hcl₁_len
    exact .switchFalse
      (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (integrateBlock_switchBool ht)
      (evalOperand_shift_ok hcs_len hc)
      (ih htb.2 hcl₂_len callerLocals₂ outFinal hcs_len hpost)
  | returnCleanupFault hg hs ht hcl =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .returnCleanupFault (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm, hcl])
      hcl
  | returnOk hg hs ht hcl h0 =>
    rename_i curIdx curBb curLocals curDrops locals₁ drops₁ retVal
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    have hshift := evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs
    cases target with
    | none =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unreachable (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl])
    | some retBb =>
      simp only [CalleePostSpliced] at hpost
      have hget_tramp :
          getAt spliced.blocks (caller.blocks.length + callee.blocks.length) =
          some { isCleanup := false
                 stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
                 term := .goto retBb } := by
        let preList := patchedBlocks ++ callee.blocks.map
          (integrateBlock caller.numLocals caller.blocks.length
            (caller.blocks.length + callee.blocks.length) (some retBb) unwind)
        have hpre_len : preList.length = caller.blocks.length + callee.blocks.length := by
          simp [preList, hpatched_len]
        have h0_tr := getAt_append_right preList
          [{ isCleanup := false
             stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
             term := .goto retBb }] 0
        rw [Nat.add_zero, hpre_len] at h0_tr
        rw [hspliced]
        exact h0_tr
      cases locals₁ with
      | nil => cases h0
      | cons s0 lTail =>
        simp only [getAt] at h0; cases h0
        have hmove_N :
            evalOperand (callerLocals₂ ++ (LocalSlot.liveVal retVal :: lTail)) (.move caller.numLocals) =
            .ok (retVal, callerLocals₂ ++ (LocalSlot.liveUninit :: lTail)) :=
          evalOperand_shift_ok hcs_len (op := .move 0) rfl
        have hdst_lt : dst < callerLocals₂.length := by rw [hcs_len]; exact hdst
        have hw_pref := writeLocal_prefix (extra := LocalSlot.liveUninit :: lTail) (v := retVal) hdst_lt
        cases hw : writeLocal callerLocals₂ dst retVal with
        | error f =>
          rw [hw] at hpost hw_pref; subst hpost
          have htr_err :
              evalStmts spliced.features cpu (callerLocals₂ ++ (LocalSlot.liveVal retVal :: lTail)) drops₁
                [Stmt.assign dst (.use (.move caller.numLocals))] = .error f := by
            simp only [evalStmts, evalStmt, evalRvalue, hmove_N, hw_pref, Except.map]
          exact .goto (hget_spliced_cb _ _ hg) hshift
            (by simp [integrateBlock, ht, integrateTerm, hcl])
            (.stmtFault hget_tramp htr_err)
        | ok callerLocals₃ =>
          rw [hw] at hpost hw_pref
          have htr_ok :
              evalStmts spliced.features cpu (callerLocals₂ ++ (LocalSlot.liveVal retVal :: lTail)) drops₁
                [Stmt.assign dst (.use (.move caller.numLocals))] =
              .ok (callerLocals₃ ++ (LocalSlot.liveUninit :: lTail), drops₁) := by
            simp only [evalStmts, evalStmt, evalRvalue, hmove_N, hw_pref, Except.map]
          have htail_len : (LocalSlot.liveUninit :: lTail).length = callee.numLocals := by
            simpa using hcl₁_len
          exact .goto (hget_spliced_cb _ _ hg) hshift
            (by simp [integrateBlock, ht, integrateTerm, hcl])
            (.goto hget_tramp htr_ok rfl (hpost _ htail_len))
  | returnUninitOrDead hg hs ht hcl h0 hor =>
    rename_i curIdx curBb curLocals curDrops locals₁ drops₁ slot0
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    have hshift := evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs
    cases target with
    | none =>
      exact .unreachable (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl])
    | some retBb =>
      have hget_tramp :
          getAt spliced.blocks (caller.blocks.length + callee.blocks.length) =
          some { isCleanup := false
                 stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
                 term := .goto retBb } := by
        let preList := patchedBlocks ++ callee.blocks.map
          (integrateBlock caller.numLocals caller.blocks.length
            (caller.blocks.length + callee.blocks.length) (some retBb) unwind)
        have hpre_len : preList.length = caller.blocks.length + callee.blocks.length := by
          simp [preList, hpatched_len]
        have h0_tr := getAt_append_right preList
          [{ isCleanup := false
             stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
             term := .goto retBb }] 0
        rw [Nat.add_zero, hpre_len] at h0_tr
        rw [hspliced]
        exact h0_tr
      have h0_err : evalOperand locals₁ (.move 0) = .error .undefined := by
        rcases hor with rfl | rfl <;> simp [evalOperand, h0]
      have hmove_err :
          evalOperand (callerLocals₂ ++ locals₁) (.move caller.numLocals) = .error .undefined :=
        evalOperand_shift_err hcs_len (op := .move 0) h0_err
      have htr_err :
          evalStmts spliced.features cpu (callerLocals₂ ++ locals₁) drops₁
            [Stmt.assign dst (.use (.move caller.numLocals))] = .error .undefined := by
        simp only [evalStmts, evalStmt, evalRvalue, hmove_err]
      exact .goto (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl])
        (.stmtFault hget_tramp htr_err)
  | returnNoSlot _ hs _ _ h0 =>
    intro _ hcl_len _ _ _ _
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    have hpos : 0 < callee.numLocals :=
      Nat.lt_of_lt_of_le (Nat.zero_lt_succ _)
        (Nat.le_trans (Nat.le_add_right 1 _) hcallee_wf.1.1)
    rw [← hcl₁_len] at hpos
    rcases getAt_lt_some hpos with ⟨_, hs0⟩
    rw [h0] at hs0; cases hs0
  | unreachable hg hs ht =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .unreachable (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm])
  | unwindTerminate hg hs ht =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .unwindTerminate (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm])
  | unwindResumeOk hg hs ht hcl =>
    rename_i _ _ _ _ locals₁ drops₁
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    have hshift := evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs
    cases unwind with
    | cleanup cbb =>
      simp only [CalleePostSpliced] at hpost
      exact .goto (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl])
        (hpost locals₁ hcl₁_len)
    | continue_ =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unwindResumeOk (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl]) hcl
    | terminate =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unwindTerminate (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl])
    | unreachable =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unreachable (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, hcl])
  | unwindResumeFault hg hs ht hcl =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .unwindResumeFault (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm, hcl]) hcl
  | unwindStartCleanup hg hs ht _ ih =>
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, htb⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    rw [ht] at htb
    simp only [termBounded, unwindBounded, decide_eq_true_eq] at htb
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    exact .unwindStartCleanup (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
      (ih htb hcl₁_len callerLocals₂ outFinal hcs_len hpost)
  | unwindStartContinue hg hs ht =>
    rename_i _ _ _ _ locals₁ _
    intro _ hcl_len callerLocals₂ outFinal hcs_len hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    have hcl₁_len := (evalStmts_preserves_length hs).trans hcl_len
    have hshift := evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs
    cases unwind with
    | cleanup cbb =>
      simp only [CalleePostSpliced] at hpost
      exact .unwindStartCleanup (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
        (hpost locals₁ hcl₁_len)
    | continue_ =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unwindStartContinue (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
    | terminate =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unwindStartTerminate (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
    | unreachable =>
      simp only [CalleePostSpliced] at hpost; subst hpost
      exact .unwindStartUnreachable (hget_spliced_cb _ _ hg) hshift
        (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
  | unwindStartTerminate hg hs ht =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .unwindStartTerminate (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
  | unwindStartUnreachable hg hs ht =>
    intro _ _ callerLocals₂ outFinal hcs_len hpost
    simp only [CalleePostSpliced] at hpost; subst hpost
    have ⟨_, hvalid, _⟩ := blocksWellFormed_getAt hcallee_wf.2 hg
    exact .unwindStartUnreachable (hget_spliced_cb _ _ hg)
      (evalStmts_shift_ok hcs_len hspliced_feats (hvalid rfl) hs)
      (by simp [integrateBlock, ht, integrateTerm, mapUnwind])
  | callFailClosed hg _ ht =>
    exfalso; exact getAt_callFree_not_call hcf hg _ _ _ _ _ ht


/-! ## Section 10: Prefix Helper Wrappers & Forward Caller Simulation (`inlineCallSite_sound`) -/

theorem evalStmts_prefix_ok {feats cpu : List FeatureId}
    {xs extra xs₁ : List LocalSlot} {drops drops₁ : List DropTag} {ss : List Stmt}
    (hb : stmtsBounded xs.length ss = true)
    (hs : evalStmts feats cpu xs drops ss = .ok (xs₁, drops₁)) :
    evalStmts feats cpu (xs ++ extra) drops ss = .ok (xs₁ ++ extra, drops₁) := by
  rw [evalStmts_prefix hb, hs]
  rfl

theorem evalStmts_prefix_err {feats cpu : List FeatureId}
    {xs extra : List LocalSlot} {drops : List DropTag} {ss : List Stmt} {err : Fault}
    (hb : stmtsBounded xs.length ss = true)
    (hs : evalStmts feats cpu xs drops ss = .error err) :
    evalStmts feats cpu (xs ++ extra) drops ss = .error err := by
  rw [evalStmts_prefix hb, hs]
  rfl

theorem evalOperand_prefix_ok {xs extra xs₁ : List LocalSlot} {op : Operand} {v : Val}
    (hb : operandBounded xs.length op = true)
    (hc : evalOperand xs op = .ok (v, xs₁)) :
    evalOperand (xs ++ extra) op = .ok (v, xs₁ ++ extra) := by
  rw [evalOperand_prefix hb, hc]
  rfl

theorem evalOperand_prefix_err {xs extra : List LocalSlot} {op : Operand} {err : Fault}
    (hb : operandBounded xs.length op = true)
    (hc : evalOperand xs op = .error err) :
    evalOperand (xs ++ extra) op = .error err := by
  rw [evalOperand_prefix hb, hc]
  rfl

theorem evalArgs_prefix_ok {xs extra xs₁ : List LocalSlot} {ops : List Operand} {vs : List Val}
    (hb : operandListBounded xs.length ops = true)
    (ha : evalArgs xs ops = .ok (vs, xs₁)) :
    evalArgs (xs ++ extra) ops = .ok (vs, xs₁ ++ extra) := by
  rw [evalArgs_prefix hb, ha]
  rfl

theorem evalArgs_prefix_err {xs extra : List LocalSlot} {ops : List Operand} {err : Fault}
    (hb : operandListBounded xs.length ops = true)
    (ha : evalArgs xs ops = .error err) :
    evalArgs (xs ++ extra) ops = .error err := by
  rw [evalArgs_prefix hb, ha]
  rfl

theorem writeLocal_prefix_ok {xs extra xs₁ : List LocalSlot} {dst : LocalId} {v : Val}
    (hdst : dst < xs.length)
    (hw : writeLocal xs dst v = .ok xs₁) :
    writeLocal (xs ++ extra) dst v = .ok (xs₁ ++ extra) := by
  rw [writeLocal_prefix hdst, hw]
  rfl

theorem writeLocal_prefix_err {xs extra : List LocalSlot} {dst : LocalId} {v : Val} {err : Fault}
    (hdst : dst < xs.length)
    (hw : writeLocal xs dst v = .error err) :
    writeLocal (xs ++ extra) dst v = .error err := by
  rw [writeLocal_prefix hdst, hw]
  rfl

theorem dec_block_eq {b n : Nat} (_ : b < n) (callBb : BlockId) :
    b = callBb ∨ b ≠ callBb :=
  match Nat.decEq b callBb with
  | isTrue h => Or.inl h
  | isFalse h => Or.inr h

theorem add_sub_left_of_le {a b c : Nat} (h : c ≤ a) :
    (a + b) - c = (a - c) + b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have hle : c ≤ a + b := Nat.le_trans h (Nat.le_add_right a b)
    rw [Nat.add_succ, Nat.succ_sub hle, ih, Nat.add_succ]

theorem replicateSlot_add (m n : Nat) (s : LocalSlot) :
    replicateSlot (m + n) s = replicateSlot m s ++ replicateSlot n s := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add]
    simp [replicateSlot, ih]

theorem evalStmts_with_prelude
    {sFeats cFeats cpu : List FeatureId}
    {xs extra xs₁ : List LocalSlot} {drops drops₁ : List DropTag}
    {ss : List Stmt} {callee : Body} {argOps : List Operand} {N : Nat}
    (hs_feats : sFeats = cFeats)
    (hN : xs₁.length = N)
    (hsb : stmtsBounded xs.length ss = true)
    (hs : evalStmts cFeats cpu xs drops ss = .ok (xs₁, drops₁))
    (hpos : 1 ≤ xs₁.length)
    (hcallee_wf : 1 + callee.argCount ≤ callee.numLocals)
    (hextra_len : extra.length = callee.numLocals)
    (harg_len : argOps.length = callee.argCount)
    (hab : operandListBounded xs₁.length argOps = true) :
    evalStmts sFeats cpu (xs ++ extra) drops
      (ss ++ buildCallPrelude N callee.argCount callee.numLocals argOps) =
      match evalArgs xs₁ argOps with
      | .error f => .error f
      | .ok (argVals, callerSlots') =>
        match initFrameLocals callee argVals with
        | none => .error .unsupported
        | some calleeLocals₀ => .ok (callerSlots' ++ calleeLocals₀, drops₁) := by
  rw [← hN, hs_feats, evalStmts_append, evalStmts_prefix_ok hsb hs]
  exact buildCallPrelude_correct cFeats cpu xs₁ extra drops₁ callee argOps
    hpos hcallee_wf hextra_len harg_len hab

theorem callee_exec_forward_at_zero
    {prog : Program} {cpu : List FeatureId}
    {caller callee spliced : Body}
    {patchedBlocks : List BasicBlock}
    {dst : LocalId} {target : Option BlockId} {unwind : UnwindAction}
    {calleeLocals callerLocals₂ : List LocalSlot}
    {drops : List DropTag} {outC : Outcome}
    (hcallee_wf : bodyWellFormed callee true = true)
    (hcf : isCallFree callee = true)
    (hfeats : callee.features = caller.features)
    (hdst : dst < caller.numLocals)
    (hpatched_len : patchedBlocks.length = caller.blocks.length)
    (hspliced : spliced = {
      numLocals := caller.numLocals + callee.numLocals
      argCount := caller.argCount
      features := caller.features
      blocks := patchedBlocks ++
        callee.blocks.map (integrateBlock caller.numLocals caller.blocks.length
          (caller.blocks.length + callee.blocks.length) target unwind) ++
        mkReturnTrampoline caller.numLocals dst target
    })
    (hexec : ExecBlockIntra cpu callee 0 calleeLocals drops outC)
    (hc0 : 0 < callee.blocks.length)
    (hcl_len : calleeLocals.length = callee.numLocals)
    (outFinal : Outcome)
    (hcs_len : callerLocals₂.length = caller.numLocals)
    (hpost : CalleePostSpliced prog cpu spliced callee.numLocals
      callerLocals₂ dst target unwind outC outFinal) :
    ExecBlock prog cpu spliced caller.blocks.length
      (callerLocals₂ ++ calleeLocals) drops outFinal := by
  have h := callee_exec_forward hcallee_wf hcf hfeats hdst hpatched_len hspliced
    hexec hc0 hcl_len callerLocals₂ outFinal hcs_len hpost
  rw [Nat.add_zero] at h
  exact h

theorem caller_exec_forward
    {prog : Program} {cpu : List FeatureId}
    {caller bbCallOwner : Body}
    {callBb : BlockId} {bbCall : BasicBlock}
    {calleeId : DefId} {callee spliced : Body}
    {argOps : List Operand} {dst : LocalId}
    {target : Option BlockId} {unwind : UnwindAction}
    {patchedBlocks : List BasicBlock}
    (hcaller_wf : bodyWellFormed caller false = true)
    (hcpu_ok : allFeaturesPresent caller.features cpu = true)
    (hcall_get : getAt caller.blocks callBb = some bbCall)
    (hcall_ncl : bbCall.isCleanup = false)
    (hcall_term : bbCall.term = .call calleeId argOps dst target unwind)
    (hcallee_get : getAt prog calleeId = some callee)
    (hcallee_wf : bodyWellFormed callee true = true)
    (hcallee_cf : isCallFree callee = true)
    (hfeats : callee.features = caller.features)
    (harg_len : argOps.length = callee.argCount)
    (hset_patched : setAt caller.blocks callBb
      { isCleanup := false
        stmts := bbCall.stmts ++ buildCallPrelude caller.numLocals callee.argCount callee.numLocals argOps
        term := .goto caller.blocks.length } = some patchedBlocks)
    (hspliced : spliced = {
      numLocals := caller.numLocals + callee.numLocals
      argCount := caller.argCount
      features := caller.features
      blocks := patchedBlocks ++
        callee.blocks.map (integrateBlock caller.numLocals caller.blocks.length
          (caller.blocks.length + callee.blocks.length) target unwind) ++
        mkReturnTrampoline caller.numLocals dst target
    })
    {idx : BlockId} {locals : List LocalSlot} {drops : List DropTag} {out : Outcome}
    (hexec : ExecBlock prog cpu bbCallOwner idx locals drops out) :
    bbCallOwner = caller →
    idx < caller.blocks.length →
    locals.length = caller.numLocals →
    ∀ extra, extra.length = callee.numLocals →
      ExecBlock prog cpu spliced idx (locals ++ extra) drops out := by
  have hpatched_len : patchedBlocks.length = caller.blocks.length := setAt_length hset_patched
  have hspliced_feats : spliced.features = caller.features := by rw [hspliced]
  have hcaller_wf_unp := hcaller_wf
  simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcaller_wf_unp
  have hcallee_wf_unp := hcallee_wf
  simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcallee_wf_unp
  have hget_non_call : ∀ j bb,
      j < caller.blocks.length → j ≠ callBb →
      getAt caller.blocks j = some bb →
      getAt spliced.blocks j = some bb := by
    intro j bb hj hne hg
    rw [hspliced]
    simp only [List.append_assoc]
    have hj_p : j < patchedBlocks.length := by rw [hpatched_len]; exact hj
    rw [getAt_append_left hj_p, getAt_setAt_ne hset_patched hne]
    exact hg
  have hget_at_call :
      getAt spliced.blocks callBb = some {
        isCleanup := false
        stmts := bbCall.stmts ++ buildCallPrelude caller.numLocals callee.argCount callee.numLocals argOps
        term := .goto caller.blocks.length
      } := by
    have hlt_call : callBb < patchedBlocks.length := by
      rw [hpatched_len]; exact getAt_some_lt hcall_get
    rw [hspliced]
    simp only [List.append_assoc]
    rw [getAt_append_left hlt_call]
    exact getAt_setAt_same hset_patched
  induction hexec with
  | oobBlock hg =>
    intro hb hlt
    rw [hb] at hg
    rcases getAt_lt_some hlt with ⟨_, hs0⟩
    rw [hg] at hs0; cases hs0
  | stmtFault hg hs =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [← hlen] at hsb
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg
      injection hg with hbb
      rw [← hbb] at hs hsb
      rw [heq]
      exact .stmtFault hget_at_call (by
        rw [hspliced_feats, evalStmts_append, evalStmts_prefix_err hsb hs])
    · exact .stmtFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_err hsb hs)
  | goto hg hs ht _ ih =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [ht] at htb; simp only [termBounded, decide_eq_true_eq] at htb
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      rw [← hlen] at hsb
      exact .goto (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
        (ih hb htb hlen₁ extra hextra)
  | switchFault hg hs ht hc =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [ht] at htb; simp only [termBounded, Bool.and_eq_true] at htb
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      rw [← hlen] at hsb
      have hcb := htb.1.1; rw [← hlen₁] at hcb
      exact .switchFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
        (evalOperand_prefix_err hcb hc)
  | switchNonBool hg hs ht hc =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [ht] at htb; simp only [termBounded, Bool.and_eq_true] at htb
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      rw [← hlen] at hsb
      have hcb := htb.1.1; rw [← hlen₁] at hcb
      exact .switchNonBool (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
        (evalOperand_prefix_ok hcb hc)
  | switchTrue hg hs ht hc _ ih =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [ht] at htb; simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      have hlen₂ := (evalOperand_preserves_length hc).trans hlen₁
      rw [← hlen] at hsb
      have hcb := htb.1.1; rw [← hlen₁] at hcb
      exact .switchTrue (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
        (evalOperand_prefix_ok hcb hc)
        (ih hb htb.1.2 hlen₂ extra hextra)
  | switchFalse hg hs ht hc _ ih =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [ht] at htb; simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      have hlen₂ := (evalOperand_preserves_length hc).trans hlen₁
      rw [← hlen] at hsb
      have hcb := htb.1.1; rw [← hlen₁] at hcb
      exact .switchFalse (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
        (evalOperand_prefix_ok hcb hc)
        (ih hb htb.2 hlen₂ extra hextra)
  | returnCleanupFault hg hs ht hcl =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .returnCleanupFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl
  | returnOk hg hs ht hcl h0 =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      have hpos : 0 < caller.numLocals :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _)
          (Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1)
      rw [← hlen₁] at hpos
      rw [← hlen] at hsb
      exact .returnOk (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl
        (by rw [getAt_append_left hpos]; exact h0)
  | returnUninitOrDead hg hs ht hcl h0 hor =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      have hpos : 0 < caller.numLocals :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _)
          (Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1)
      rw [← hlen₁] at hpos
      rw [← hlen] at hsb
      exact .returnUninitOrDead (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl
        (by rw [getAt_append_left hpos]; exact h0) hor
  | returnNoSlot _ hs _ _ h0 =>
    intro hb _ hlen _ _
    rw [hb] at hs
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hpos : 0 < caller.numLocals :=
      Nat.lt_of_lt_of_le (Nat.zero_lt_succ _)
        (Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1)
    rw [← hlen₁] at hpos
    rcases getAt_lt_some hpos with ⟨_, hs0⟩
    rw [h0] at hs0; cases hs0
  | unreachable hg hs ht =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unreachable (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
  | unwindTerminate hg hs ht =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unwindTerminate (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
  | unwindResumeOk hg hs ht hcl =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unwindResumeOk (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl
  | unwindResumeFault hg hs ht hcl =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unwindResumeFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl
  | unwindStartCleanup hg hs ht _ ih =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [ht] at htb; simp only [termBounded, unwindBounded, decide_eq_true_eq] at htb
      have hlen₁ := (evalStmts_preserves_length hs).trans hlen
      rw [← hlen] at hsb
      exact .unwindStartCleanup (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
        (ih hb htb hlen₁ extra hextra)
  | unwindStartContinue hg hs ht =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unwindStartContinue (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
  | unwindStartTerminate hg hs ht =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unwindStartTerminate (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
  | unwindStartUnreachable hg hs ht =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht; cases ht
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .unwindStartUnreachable (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht
  | callInCleanupFault hg hs ht hcl =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_ncl] at hcl; cases hcl
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .callInCleanupFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl
  | callMissingCallee hg hs ht hcl hmiss =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht
      injection ht with hc1 _ _ _ _
      rw [← hc1, hcallee_get] at hmiss; cases hmiss
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .callMissingCallee (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hmiss
  | callFeatureFault hg hs ht hcl hcg hff =>
    intro hb hlt hlen extra _
    rw [hb] at hg hs
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb; rw [← hbb, hcall_term] at ht
      injection ht with hc1 _ _ _ _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce, hfeats, hcpu_ok] at hff; cases hff
    · have ⟨hsb, _, _⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
      rw [← hlen] at hsb
      exact .callFeatureFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hff
  | callArgFault hg hs ht hcl hcg hcf_ok ha_err =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb; simp only [termBounded, Bool.and_eq_true] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 _ _ _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hc2] at ha_err hab
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      rw [ha_err] at hfull
      rw [heq]
      exact .stmtFault hget_at_call hfull
    · exact .callArgFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_err hab ha_err)
  | callInitFault hg hs ht hcl hcg hcf_ok ha_ok hinit_none =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb; simp only [termBounded, Bool.and_eq_true] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 _ _ _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_none
      rw [← hc2] at ha_ok hab
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_none] at hfull
      rw [heq]
      exact .stmtFault hget_at_call hfull
    · exact .callInitFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_none
  | callReturnOk hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c hw_ok _ _ ih_cont =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, optBlockBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    have hlen₃ := (writeLocal_preserves_length hw_ok).trans hlen₂
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    have hdst_b := htb.1.1.2; rw [← hlen₂] at hdst_b
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 hc4 _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at hw_ok htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc4]
          simp only [CalleePostSpliced, hw_ok]
          intro extra' hextra'
          exact ih_cont hb htb.1.2 hlen₃ extra' hextra'))
    · exact .callReturnOk (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
        (writeLocal_prefix_ok hdst_b hw_ok)
        (ih_cont hb htb.1.2 hlen₃ extra hextra)
  | callReturnWriteFault hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c hw_err =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    have hdst_b := htb.1.1.2; rw [← hlen₂] at hdst_b
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 hc4 _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at hw_err htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc4]
          simp only [CalleePostSpliced, hw_err]))
    · exact .callReturnWriteFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
        (writeLocal_prefix_err hdst_b hw_err)
  | callReturnDiverging hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 hc4 _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc4]; rfl))
    · exact .callReturnDiverging (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
  | callUnwindCleanup hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c _ _ ih_cont =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, unwindBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 _ hc5
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc5]
          intro extra' hextra'
          exact ih_cont hb htb.2 hlen₂ extra' hextra'))
    · exact .callUnwindCleanup (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
        (ih_cont hb htb.2 hlen₂ extra hextra)
  | callUnwindContinue hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 _ hc5
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc5]; rfl))
    · exact .callUnwindContinue (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
  | callUnwindTerminate hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 _ hc5
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc5]; rfl))
    · exact .callUnwindTerminate (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
  | callUnwindUnreachable hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 _ hc5
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ (by
          rw [hc5]; rfl))
    · exact .callUnwindUnreachable (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
  | callPropagateAbort hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 _ _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ rfl)
    · exact .callPropagateAbort (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c
  | callPropagateFault hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb hlt hlen extra hextra
    rw [hb] at hg hs
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg
    rw [ht] at htb
    simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
    have hlen₁ := (evalStmts_preserves_length hs).trans hlen
    have hlen₂ := (evalArgs_preserves_length ha_ok).trans hlen₁
    rw [← hlen] at hsb
    have hab := htb.1.1.1; rw [← hlen₁] at hab
    rcases dec_block_eq hlt callBb with heq | heq
    · rw [heq, hcall_get] at hg; injection hg with hbb
      rw [← hbb] at hs ht hsb
      rw [hcall_term] at ht; injection ht with hc1 hc2 hc3 _ _
      rw [← hc1, hcallee_get] at hcg; injection hcg with hce
      rw [← hce] at hinit_some hexec_c
      rw [← hc2] at ha_ok hab
      rw [← hc3] at htb
      have hpos₁ : 1 ≤ caller.numLocals :=
        Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      rw [← hlen₁] at hpos₁
      have hfull := evalStmts_with_prelude hspliced_feats hlen₁ hsb hs
        hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab
      simp only [ha_ok, hinit_some] at hfull
      have hexec_intra := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 _ _ _).mp hexec_c
      have hc0_lt : 0 < callee.blocks.length :=
        Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
      have hcl₀_len := initFrameLocals_length hinit_some
      rw [heq]
      exact .goto hget_at_call hfull rfl
        (callee_exec_forward_at_zero hcallee_wf hcallee_cf hfeats htb.1.1.2
          hpatched_len hspliced hexec_intra hc0_lt hcl₀_len _ hlen₂ rfl)
    · exact .callPropagateFault (hget_non_call _ _ hlt heq hg)
        (hspliced_feats ▸ evalStmts_prefix_ok hsb hs) ht hcl hcg hcf_ok
        (evalArgs_prefix_ok hab ha_ok) hinit_some hexec_c

theorem initFrameLocals_spliced {caller callee spliced : Body} {args : List Val}
    (hcaller_le : 1 + caller.argCount ≤ caller.numLocals)
    (hs_num : spliced.numLocals = caller.numLocals + callee.numLocals)
    (hs_arg : spliced.argCount = caller.argCount) :
    initFrameLocals spliced args =
      (initFrameLocals caller args).map (· ++ replicateSlot callee.numLocals .dead) := by
  unfold initFrameLocals
  rw [hs_num, hs_arg]
  cases hbeq : Nat.beq args.length caller.argCount with
  | false => simp
  | true =>
    have hs_le : 1 + caller.argCount ≤ caller.numLocals + callee.numLocals :=
      Nat.le_trans hcaller_le (Nat.le_add_right _ _)
    simp only [Bool.true_and, decide_eq_true hcaller_le, decide_eq_true hs_le, ↓reduceIte, Option.map]
    rw [add_sub_left_of_le hcaller_le, replicateSlot_add]
    simp [List.append_assoc]

/-- Forward soundness of `inlineCallSite`: every interprocedural execution outcome of
    `caller` is preserved by `spliced`. -/
theorem inlineCallSite_sound
    {prog : Program} {caller spliced : Body} {callBb : BlockId}
    {cpu : List FeatureId} {args : List Val} {out : Outcome}
    (hinline : inlineCallSite prog caller callBb = some spliced)
    (hexec : ExecBody prog caller cpu args out) :
    ExecBody prog spliced cpu args out := by
  unfold inlineCallSite at hinline
  cases hwf_c : bodyWellFormed caller false with
  | false => simp [hwf_c] at hinline
  | true =>
    simp only [hwf_c, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
    cases hget_bb : getAt caller.blocks callBb with
    | none => simp [hget_bb] at hinline
    | some bbCall =>
      rcases bbCall with ⟨isCl, bbStmts, bbTerm⟩
      simp only [hget_bb] at hinline
      cases isCl with
      | true => simp at hinline
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hinline
        cases bbTerm with
        | goto _ | switchBool _ _ _ | return_ | unreachable | unwindTerminate
        | unwindResume | unwindStart _ => simp at hinline
        | call calleeId argOps dst target unwind =>
          simp only [] at hinline
          cases hget_ce : getAt prog calleeId with
          | none => simp [hget_ce] at hinline
          | some callee =>
            simp only [hget_ce] at hinline
            cases hwf_ce : bodyWellFormed callee true with
            | false => simp [hwf_ce] at hinline
            | true =>
              simp only [hwf_ce, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
              cases hcf_ce : isCallFree callee with
              | false => simp [hcf_ce] at hinline
              | true =>
                simp only [hcf_ce, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
                cases hfeq : eqNatList callee.features caller.features with
                | false => simp [hfeq] at hinline
                | true =>
                  simp only [hfeq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
                  cases hargb : Nat.beq argOps.length callee.argCount with
                  | false => simp [hargb] at hinline
                  | true =>
                    simp only [hargb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
                    cases hsetp : setAt caller.blocks callBb
                      { isCleanup := false
                        stmts := bbStmts ++ buildCallPrelude caller.numLocals callee.argCount callee.numLocals argOps
                        term := .goto caller.blocks.length } with
                    | none => simp [hsetp] at hinline
                    | some patchedBlocks =>
                      simp only [hsetp, Option.some.injEq] at hinline
                      have hspliced := hinline.symm
                      have hfeats : callee.features = caller.features := eqNatList_eq hfeq
                      have harg_len : argOps.length = callee.argCount := Nat.eq_of_beq_eq_true hargb
                      have hs_feats : spliced.features = caller.features := by rw [hspliced]
                      have hcaller_wf_unp := hwf_c
                      simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcaller_wf_unp
                      have hinit_eq := initFrameLocals_spliced
                        (caller := caller) (callee := callee) (spliced := spliced) (args := args)
                        hcaller_wf_unp.1.1 (by rw [hspliced]) (by rw [hspliced])
                      unfold ExecBody at hexec ⊢
                      rw [hs_feats]
                      cases hcpu : allFeaturesPresent caller.features cpu with
                      | false =>
                        simp [hcpu] at hexec ⊢
                        exact hexec
                      | true =>
                        simp only [hcpu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hexec ⊢
                        rw [hinit_eq]
                        cases hinit_c : initFrameLocals caller args with
                        | none =>
                          simp [hinit_c] at hexec ⊢
                          exact hexec
                        | some locals₀ =>
                          simp only [hinit_c, Option.map] at hexec ⊢
                          have hb0 : 0 < caller.blocks.length :=
                            Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcaller_wf_unp.1.2
                          have hl0 : locals₀.length = caller.numLocals :=
                            initFrameLocals_length hinit_c
                          exact caller_exec_forward hwf_c hcpu hget_bb rfl rfl
                            hget_ce hwf_ce hcf_ce hfeats harg_len hsetp hspliced hexec
                            rfl hb0 hl0 (replicateSlot callee.numLocals .dead)
                            (replicateSlot_length _ _)

/-! ## Section 11: Backward Completeness & Exact Call-Site Bisimulation (`inlineCallSite_bisimulation`) -/

def CallContStep (R : BlockId → List LocalSlot → List DropTag → Outcome → Prop)
    (extLocals₂ : List LocalSlot) (cDst : LocalId)
    (cTarget : Option BlockId) (cUnwind : UnwindAction)
    (outC out : Outcome) : Prop :=
  match outC with
  | .returned retVal drops₂ =>
    match cTarget with
    | none => out = .fault .undefined
    | some retBb =>
      match writeLocal extLocals₂ cDst retVal with
      | .error f => out = .fault f
      | .ok extLocals₃ => R retBb extLocals₃ drops₂ out
  | .unwound drops₂ =>
    match cUnwind with
    | .cleanup cbb => R cbb extLocals₂ drops₂ out
    | .continue_ => out = .unwound drops₂
    | .terminate => out = .aborted drops₂
    | .unreachable => out = .fault .undefined
  | .aborted drops₂ => out = .aborted drops₂
  | .fault f => out = .fault f

def TermStepSpliced (prog : Program) (cpu : List FeatureId)
    (R : BlockId → List LocalSlot → List DropTag → Outcome → Prop)
    (bb : BasicBlock) (extLocals₁ : List LocalSlot) (drops₁ : List DropTag)
    (out : Outcome) : Prop :=
  match bb.term with
  | .goto t => R t extLocals₁ drops₁ out
  | .switchBool cond tT fT =>
    match evalOperand extLocals₁ cond with
    | .error f => out = .fault f
    | .ok (.int _, _) => out = .fault .unsupported
    | .ok (.bool true, l₂) => R tT l₂ drops₁ out
    | .ok (.bool false, l₂) => R fT l₂ drops₁ out
  | .return_ =>
    if bb.isCleanup then out = .fault .unsupported
    else
      match getAt extLocals₁ 0 with
      | some (.liveVal v) => out = .returned v drops₁
      | some .liveUninit | some .dead => out = .fault .undefined
      | none => out = .fault .unsupported
  | .unreachable => out = .fault .undefined
  | .unwindTerminate => out = .aborted drops₁
  | .unwindResume =>
    if bb.isCleanup then out = .unwound drops₁ else out = .fault .unsupported
  | .unwindStart u =>
    match u with
    | .cleanup cbb => R cbb extLocals₁ drops₁ out
    | .continue_ => out = .unwound drops₁
    | .terminate => out = .aborted drops₁
    | .unreachable => out = .fault .undefined
  | .call calleeId argOps cDst cTarget cUnwind =>
    if bb.isCleanup then out = .fault .unsupported
    else
      match getAt prog calleeId with
      | none => out = .fault .unsupported
      | some cBody =>
        if !allFeaturesPresent cBody.features cpu then
          out = .fault .illegalInstruction
        else
          match evalArgs extLocals₁ argOps with
          | .error f => out = .fault f
          | .ok (argVals, extLocals₂) =>
            match initFrameLocals cBody argVals with
            | none => out = .fault .unsupported
            | some cl₀ =>
              ∃ outC,
                ExecBlock prog cpu cBody 0 cl₀ drops₁ outC ∧
                CallContStep R extLocals₂ cDst cTarget cUnwind outC out

def BlockStepSpliced (prog : Program) (cpu : List FeatureId) (spliced : Body)
    (R : BlockId → List LocalSlot → List DropTag → Outcome → Prop)
    (idx : BlockId) (extLocals : List LocalSlot) (drops : List DropTag)
    (out : Outcome) : Prop :=
  match getAt spliced.blocks idx with
  | none => out = .fault .unsupported
  | some bb =>
    match evalStmts spliced.features cpu extLocals drops bb.stmts with
    | .error f => out = .fault f
    | .ok (extLocals₁, drops₁) =>
      TermStepSpliced prog cpu R bb extLocals₁ drops₁ out

theorem execBlock_induct_spliced
    {prog : Program} {cpu : List FeatureId} {spliced owner : Body}
    (R : BlockId → List LocalSlot → List DropTag → Outcome → Prop)
    (hclosed : ∀ idx extLocals drops out,
      BlockStepSpliced prog cpu spliced R idx extLocals drops out →
      R idx extLocals drops out)
    {idx : BlockId} {extLocals : List LocalSlot} {drops : List DropTag} {out : Outcome}
    (hexec : ExecBlock prog cpu owner idx extLocals drops out) :
    owner = spliced → R idx extLocals drops out := by
  induction hexec with
  | oobBlock hg =>
    intro hb; rw [hb] at hg
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, hg])
  | stmtFault hg hs =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, hg, hs])
  | goto hg hs ht _ ih =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]; exact ih hb)
  | switchFault hg hs ht hc =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc])
  | switchNonBool hg hs ht hc =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc])
  | switchTrue hg hs ht hc _ ih =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc]; exact ih hb)
  | switchFalse hg hs ht hc _ ih =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc]; exact ih hb)
  | returnCleanupFault hg hs ht hcl =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl])
  | returnOk hg hs ht hcl h0 =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, h0])
  | returnUninitOrDead hg hs ht hcl h0 hor =>
    intro hb; rw [hb] at hg hs
    rcases hor with rfl | rfl <;>
      exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, h0])
  | returnNoSlot hg hs ht hcl h0 =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, h0])
  | unreachable hg hs ht =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht])
  | unwindTerminate hg hs ht =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht])
  | unwindResumeOk hg hs ht hcl =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl])
  | unwindResumeFault hg hs ht hcl =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl])
  | unwindStartCleanup hg hs ht _ ih =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]; exact ih hb)
  | unwindStartContinue hg hs ht =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht])
  | unwindStartTerminate hg hs ht =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht])
  | unwindStartUnreachable hg hs ht =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht])
  | callInCleanupFault hg hs ht hcl =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl])
  | callMissingCallee hg hs ht hcl hmiss =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hmiss])
  | callFeatureFault hg hs ht hcl hcg hff =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hcg, hff])
  | callArgFault hg hs ht hcl hcg hcf_ok ha_err =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hcg, hcf_ok, ha_err])
  | callInitFault hg hs ht hcl hcg hcf_ok ha_ok hinit_none =>
    intro hb; rw [hb] at hg hs
    exact hclosed _ _ _ _ (by simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hcg, hcf_ok, ha_ok, hinit_none])
  | callReturnOk hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c hw_ok _ _ ih_cont =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, by simp [CallContStep, hw_ok]; exact ih_cont hb⟩
  | callReturnWriteFault hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c hw_err =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, by simp [CallContStep, hw_err]⟩
  | callReturnDiverging hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, rfl⟩
  | callUnwindCleanup hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c _ _ ih_cont =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, ih_cont hb⟩
  | callUnwindContinue hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, rfl⟩
  | callUnwindTerminate hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, rfl⟩
  | callUnwindUnreachable hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, rfl⟩
  | callPropagateAbort hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, rfl⟩
  | callPropagateFault hg hs ht hcl hcg hcf_ok ha_ok hinit_some hexec_c =>
    intro hb; rw [hb] at hg hs
    refine hclosed _ _ _ _ ?_
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf_ok, Bool.not_true, ha_ok, hinit_some]
    exact ⟨_, hexec_c, rfl⟩

def TrampPost (prog : Program) (cpu : List FeatureId) (caller : Body)
    (cs₂ : List LocalSlot) (dst : LocalId) (retBb : BlockId)
    (s0 : LocalSlot) (drops : List DropTag) (out : Outcome) : Prop :=
  match s0 with
  | .liveVal retVal =>
    match writeLocal cs₂ dst retVal with
    | .error f => out = .fault f
    | .ok cs₃ => ExecBlock prog cpu caller retBb cs₃ drops out
  | .liveUninit | .dead => out = .fault .undefined

structure SplicedInv (prog : Program) (cpu : List FeatureId)
    (caller callee : Body) (dst : LocalId)
    (target : Option BlockId) (unwind : UnwindAction)
    (idx : BlockId) (extLocals : List LocalSlot) (drops : List DropTag)
    (out : Outcome) : Prop where
  onCaller :
    idx < caller.blocks.length →
    ∀ locals extra,
      extLocals = locals ++ extra →
      locals.length = caller.numLocals →
      extra.length = callee.numLocals →
      ExecBlock prog cpu caller idx locals drops out
  onCallee :
    ∀ cb,
      idx = caller.blocks.length + cb →
      cb < callee.blocks.length →
      ∀ cs₂ cls,
        extLocals = cs₂ ++ cls →
        cs₂.length = caller.numLocals →
        cls.length = callee.numLocals →
        ∃ outC,
          ExecBlockIntra cpu callee cb cls drops outC ∧
          CalleePostCaller prog cpu caller cs₂ dst target unwind outC out
  onTramp :
    ∀ retBb,
      target = some retBb →
      idx = caller.blocks.length + callee.blocks.length →
      ∀ cs₂ s0 lTail,
        extLocals = cs₂ ++ (s0 :: lTail) →
        cs₂.length = caller.numLocals →
        (s0 :: lTail).length = callee.numLocals →
        TrampPost prog cpu caller cs₂ dst retBb s0 drops out

theorem splicedInv_step_tramp
    {prog : Program} {cpu : List FeatureId}
    {caller callee spliced : Body}
    {dst : LocalId} {target : Option BlockId} {unwind : UnwindAction}
    {retBb : BlockId}
    (hdst : dst < caller.numLocals)
    (hret_lt : retBb < caller.blocks.length)
    (hget_tramp : getAt spliced.blocks (caller.blocks.length + callee.blocks.length) =
      some { isCleanup := false
             stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
             term := .goto retBb })
    {idx : BlockId} {extLocals : List LocalSlot} {drops : List DropTag} {out : Outcome}
    (hstep : BlockStepSpliced prog cpu spliced
      (SplicedInv prog cpu caller callee dst target unwind) idx extLocals drops out)
    (hidx : idx = caller.blocks.length + callee.blocks.length)
    {cs₂ : List LocalSlot} {s0 : LocalSlot} {lTail : List LocalSlot}
    (hext : extLocals = cs₂ ++ (s0 :: lTail))
    (hcs₂_len : cs₂.length = caller.numLocals)
    (hcl_len : (s0 :: lTail).length = callee.numLocals) :
    TrampPost prog cpu caller cs₂ dst retBb s0 drops out := by
  rw [hidx, hext] at hstep
  simp only [BlockStepSpliced, hget_tramp, evalStmts, evalStmt, evalRvalue] at hstep
  cases s0 with
  | liveUninit =>
    have hmv : evalOperand (cs₂ ++ (.liveUninit :: lTail)) (.move caller.numLocals) = .error .undefined :=
      evalOperand_shift_err hcs₂_len (op := .move 0) rfl
    simp only [hmv, TrampPost] at hstep ⊢
    exact hstep
  | dead =>
    have hmv : evalOperand (cs₂ ++ (.dead :: lTail)) (.move caller.numLocals) = .error .undefined :=
      evalOperand_shift_err hcs₂_len (op := .move 0) rfl
    simp only [hmv, TrampPost] at hstep ⊢
    exact hstep
  | liveVal retVal =>
    have hmv : evalOperand (cs₂ ++ (.liveVal retVal :: lTail)) (.move caller.numLocals) =
        .ok (retVal, cs₂ ++ (.liveUninit :: lTail)) :=
      evalOperand_shift_ok hcs₂_len (op := .move 0) rfl
    have hdst_c : dst < cs₂.length := by rw [hcs₂_len]; exact hdst
    have hwp := writeLocal_prefix (extra := .liveUninit :: lTail) (v := retVal) hdst_c
    simp only [hmv, Except.map, hwp, TrampPost] at hstep ⊢
    cases hw : writeLocal cs₂ dst retVal with
    | error f =>
      simp only [hw] at hstep ⊢
      exact hstep
    | ok cs₃ =>
      simp only [hw, TermStepSpliced] at hstep ⊢
      have hcs₃_len : cs₃.length = caller.numLocals :=
        (writeLocal_preserves_length hw).trans hcs₂_len
      exact hstep.onCaller hret_lt cs₃ (.liveUninit :: lTail) rfl hcs₃_len hcl_len

theorem splicedInv_step_callee
    {prog : Program} {cpu : List FeatureId}
    {caller callee spliced : Body}
    {dst : LocalId} {target : Option BlockId} {unwind : UnwindAction}
    (hcallee_wf : bodyWellFormed callee true = true)
    (hcf : isCallFree callee = true)
    (hspliced_feats : spliced.features = callee.features)
    (hu_bound : unwindBounded caller.blocks.length unwind = true)
    (hget_spliced_cb : ∀ j bb,
      getAt callee.blocks j = some bb →
      getAt spliced.blocks (caller.blocks.length + j) =
        some (integrateBlock caller.numLocals caller.blocks.length
          (caller.blocks.length + callee.blocks.length) target unwind bb))
    {idx : BlockId} {extLocals : List LocalSlot} {drops : List DropTag} {out : Outcome}
    (hstep : BlockStepSpliced prog cpu spliced
      (SplicedInv prog cpu caller callee dst target unwind) idx extLocals drops out)
    {cb : BlockId} (hidx : idx = caller.blocks.length + cb)
    (hcb : cb < callee.blocks.length)
    {cs₂ cls : List LocalSlot}
    (hext : extLocals = cs₂ ++ cls)
    (hcs₂_len : cs₂.length = caller.numLocals)
    (hcls_len : cls.length = callee.numLocals) :
    ∃ outC,
      ExecBlockIntra cpu callee cb cls drops outC ∧
      CalleePostCaller prog cpu caller cs₂ dst target unwind outC out := by
  have hcallee_wf_unp := hcallee_wf
  simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcallee_wf_unp
  rcases getAt_lt_some hcb with ⟨origBb, hg_cb⟩
  have ⟨_, hvalid, htb⟩ := blocksWellFormed_getAt hcallee_wf_unp.2 hg_cb
  have hvalid' := hvalid rfl
  have hg_sp := hget_spliced_cb cb origBb hg_cb
  rw [hidx, hext] at hstep
  simp only [BlockStepSpliced, hg_sp] at hstep
  have hsh :
      evalStmts spliced.features cpu (cs₂ ++ cls) drops (origBb.stmts.map (shiftStmt caller.numLocals)) =
      (evalStmts callee.features cpu cls drops origBb.stmts).map (fun (cl', d') => (cs₂ ++ cl', d')) := by
    rw [← hcs₂_len, hspliced_feats]
    exact evalStmts_shift cs₂ origBb.stmts cls drops hvalid'
  simp only [integrateBlock, hsh] at hstep
  cases hs_c : evalStmts callee.features cpu cls drops origBb.stmts with
  | error f =>
    simp only [hs_c, Except.map] at hstep
    exact ⟨.fault f, .stmtFault hg_cb hs_c, hstep⟩
  | ok pair =>
    rcases pair with ⟨cls₁, drops₁⟩
    have hcls₁_len : cls₁.length = callee.numLocals :=
      (evalStmts_preserves_length hs_c).trans hcls_len
    simp only [hs_c, Except.map, TermStepSpliced] at hstep
    cases ht_c : origBb.term with
    | goto t =>
      rw [ht_c] at htb; simp only [termBounded, decide_eq_true_eq] at htb
      simp only [ht_c, integrateTerm] at hstep
      rcases hstep.onCallee t rfl htb cs₂ cls₁ rfl hcs₂_len hcls₁_len with ⟨outC, hex, hpost⟩
      exact ⟨outC, .goto hg_cb hs_c ht_c hex, hpost⟩
    | switchBool cond tT fT =>
      rw [ht_c] at htb; simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
      have hop_sh : evalOperand (cs₂ ++ cls₁) (shiftOperand caller.numLocals cond) =
          (evalOperand cls₁ cond).map (fun (v, cl') => (v, cs₂ ++ cl')) := by
        rw [← hcs₂_len]; exact evalOperand_shift cs₂ cls₁ cond
      simp only [ht_c, integrateTerm, hop_sh] at hstep
      cases hc_c : evalOperand cls₁ cond with
      | error f =>
        simp only [hc_c, Except.map] at hstep
        exact ⟨.fault f, .switchFault hg_cb hs_c ht_c hc_c, hstep⟩
      | ok p2 =>
        rcases p2 with ⟨v, cls₂⟩
        have hcls₂_len : cls₂.length = callee.numLocals :=
          (evalOperand_preserves_length hc_c).trans hcls₁_len
        cases v with
        | int n =>
          simp only [hc_c, Except.map] at hstep
          exact ⟨.fault .unsupported, .switchNonBool hg_cb hs_c ht_c hc_c, hstep⟩
        | bool b =>
          cases b with
          | true =>
            simp only [hc_c, Except.map] at hstep
            rcases hstep.onCallee tT rfl htb.1.2 cs₂ cls₂ rfl hcs₂_len hcls₂_len with ⟨outC, hex, hpost⟩
            exact ⟨outC, .switchTrue hg_cb hs_c ht_c hc_c hex, hpost⟩
          | false =>
            simp only [hc_c, Except.map] at hstep
            rcases hstep.onCallee fT rfl htb.2 cs₂ cls₂ rfl hcs₂_len hcls₂_len with ⟨outC, hex, hpost⟩
            exact ⟨outC, .switchFalse hg_cb hs_c ht_c hc_c hex, hpost⟩
    | return_ =>
      cases hcl : origBb.isCleanup with
      | true =>
        simp only [ht_c, integrateTerm, hcl, ↓reduceIte] at hstep
        exact ⟨.fault .unsupported, .returnCleanupFault hg_cb hs_c ht_c hcl, hstep⟩
      | false =>
        cases cls₁ with
        | nil =>
          exfalso
          have hpos : 1 ≤ callee.numLocals :=
            Nat.le_trans (Nat.le_add_right 1 _) hcallee_wf_unp.1.1
          rw [← hcls₁_len, List.length_nil] at hpos
          exact absurd hpos (by decide)
        | cons s0 lTail =>
          cases htarget : target with
          | none =>
            simp only [ht_c, integrateTerm, hcl, Bool.false_eq_true, ↓reduceIte, htarget] at hstep
            cases s0 with
            | liveVal v =>
              exact ⟨.returned v drops₁, .returnOk hg_cb hs_c ht_c hcl rfl,
                by simp [CalleePostCaller, hstep]⟩
            | liveUninit =>
              exact ⟨.fault .undefined,
                .returnUninitOrDead hg_cb hs_c ht_c hcl rfl (Or.inl rfl), hstep⟩
            | dead =>
              exact ⟨.fault .undefined,
                .returnUninitOrDead hg_cb hs_c ht_c hcl rfl (Or.inr rfl), hstep⟩
          | some retBb =>
            simp only [ht_c, integrateTerm, hcl, Bool.false_eq_true, ↓reduceIte, htarget] at hstep
            have htr := hstep.onTramp retBb rfl rfl cs₂ s0 lTail rfl hcs₂_len hcls₁_len
            cases s0 with
            | liveVal v =>
              exact ⟨.returned v drops₁, .returnOk hg_cb hs_c ht_c hcl rfl,
                by simp [CalleePostCaller]; exact htr⟩
            | liveUninit =>
              exact ⟨.fault .undefined,
                .returnUninitOrDead hg_cb hs_c ht_c hcl rfl (Or.inl rfl), htr⟩
            | dead =>
              exact ⟨.fault .undefined,
                .returnUninitOrDead hg_cb hs_c ht_c hcl rfl (Or.inr rfl), htr⟩
    | unreachable =>
      simp only [ht_c, integrateTerm] at hstep
      exact ⟨.fault .undefined, .unreachable hg_cb hs_c ht_c, hstep⟩
    | unwindTerminate =>
      simp only [ht_c, integrateTerm] at hstep
      exact ⟨.aborted drops₁, .unwindTerminate hg_cb hs_c ht_c, hstep⟩
    | unwindResume =>
      cases hcl : origBb.isCleanup with
      | false =>
        simp only [ht_c, integrateTerm, hcl, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at hstep
        exact ⟨.fault .unsupported, .unwindResumeFault hg_cb hs_c ht_c hcl, hstep⟩
      | true =>
        cases hunw : unwind with
        | cleanup callerCbb =>
          rw [hunw] at hu_bound
          simp only [unwindBounded, decide_eq_true_eq] at hu_bound
          simp only [ht_c, integrateTerm, hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hunw] at hstep
          have hc := hstep.onCaller hu_bound cs₂ cls₁ rfl hcs₂_len hcls₁_len
          exact ⟨.unwound drops₁, .unwindResumeOk hg_cb hs_c ht_c hcl,
            by simp [CalleePostCaller]; exact hc⟩
        | continue_ =>
          simp only [ht_c, integrateTerm, hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hunw] at hstep
          exact ⟨.unwound drops₁, .unwindResumeOk hg_cb hs_c ht_c hcl,
            by simp [CalleePostCaller, hstep]⟩
        | terminate =>
          simp only [ht_c, integrateTerm, hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hunw] at hstep
          exact ⟨.unwound drops₁, .unwindResumeOk hg_cb hs_c ht_c hcl,
            by simp [CalleePostCaller, hstep]⟩
        | unreachable =>
          simp only [ht_c, integrateTerm, hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hunw] at hstep
          exact ⟨.unwound drops₁, .unwindResumeOk hg_cb hs_c ht_c hcl,
            by simp [CalleePostCaller, hstep]⟩
    | unwindStart u =>
      cases u with
      | cleanup cbb =>
        rw [ht_c] at htb; simp only [termBounded, unwindBounded, decide_eq_true_eq] at htb
        simp only [ht_c, integrateTerm, mapUnwind] at hstep
        rcases hstep.onCallee cbb rfl htb cs₂ cls₁ rfl hcs₂_len hcls₁_len with ⟨outC, hex, hpost⟩
        exact ⟨outC, .unwindStartCleanup hg_cb hs_c ht_c hex, hpost⟩
      | continue_ =>
        cases hunw : unwind with
        | cleanup callerCbb =>
          rw [hunw] at hu_bound
          simp only [unwindBounded, decide_eq_true_eq] at hu_bound
          simp only [ht_c, integrateTerm, mapUnwind, hunw] at hstep
          have hc := hstep.onCaller hu_bound cs₂ cls₁ rfl hcs₂_len hcls₁_len
          exact ⟨.unwound drops₁, .unwindStartContinue hg_cb hs_c ht_c,
            by simp [CalleePostCaller]; exact hc⟩
        | continue_ =>
          simp only [ht_c, integrateTerm, mapUnwind, hunw] at hstep
          exact ⟨.unwound drops₁, .unwindStartContinue hg_cb hs_c ht_c,
            by simp [CalleePostCaller, hstep]⟩
        | terminate =>
          simp only [ht_c, integrateTerm, mapUnwind, hunw] at hstep
          exact ⟨.unwound drops₁, .unwindStartContinue hg_cb hs_c ht_c,
            by simp [CalleePostCaller, hstep]⟩
        | unreachable =>
          simp only [ht_c, integrateTerm, mapUnwind, hunw] at hstep
          exact ⟨.unwound drops₁, .unwindStartContinue hg_cb hs_c ht_c,
            by simp [CalleePostCaller, hstep]⟩
      | terminate =>
        simp only [ht_c, integrateTerm, mapUnwind] at hstep
        exact ⟨.aborted drops₁, .unwindStartTerminate hg_cb hs_c ht_c, hstep⟩
      | unreachable =>
        simp only [ht_c, integrateTerm, mapUnwind] at hstep
        exact ⟨.fault .undefined, .unwindStartUnreachable hg_cb hs_c ht_c, hstep⟩
    | call c a d t u =>
      exfalso
      exact getAt_callFree_not_call hcf hg_cb c a d t u ht_c

theorem splicedInv_step_caller
    {prog : Program} {cpu : List FeatureId}
    {caller callee spliced : Body}
    {callBb : BlockId} {bbCall : BasicBlock}
    {calleeId : DefId} {argOps : List Operand} {dst : LocalId}
    {target : Option BlockId} {unwind : UnwindAction}
    (hcaller_wf : bodyWellFormed caller false = true)
    (hcpu_ok : allFeaturesPresent caller.features cpu = true)
    (hcall_get : getAt caller.blocks callBb = some bbCall)
    (hcall_ncl : bbCall.isCleanup = false)
    (hcall_term : bbCall.term = .call calleeId argOps dst target unwind)
    (hcallee_get : getAt prog calleeId = some callee)
    (hcallee_wf : bodyWellFormed callee true = true)
    (hcallee_cf : isCallFree callee = true)
    (hfeats : callee.features = caller.features)
    (harg_len : argOps.length = callee.argCount)
    (hspliced_feats : spliced.features = caller.features)
    (hget_non_call : ∀ j bb,
      j < caller.blocks.length → j ≠ callBb →
      getAt caller.blocks j = some bb →
      getAt spliced.blocks j = some bb)
    (hget_at_call : getAt spliced.blocks callBb = some {
      isCleanup := false
      stmts := bbCall.stmts ++ buildCallPrelude caller.numLocals callee.argCount callee.numLocals argOps
      term := .goto caller.blocks.length
    })
    {idx : BlockId} {extLocals : List LocalSlot} {drops : List DropTag} {out : Outcome}
    (hstep : BlockStepSpliced prog cpu spliced
      (SplicedInv prog cpu caller callee dst target unwind) idx extLocals drops out)
    (hlt : idx < caller.blocks.length)
    {locals extra : List LocalSlot}
    (hext : extLocals = locals ++ extra)
    (hlen : locals.length = caller.numLocals)
    (hextra : extra.length = callee.numLocals) :
    ExecBlock prog cpu caller idx locals drops out := by
  have hcaller_wf_unp := hcaller_wf
  simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcaller_wf_unp
  have hcallee_wf_unp := hcallee_wf
  simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcallee_wf_unp
  rcases dec_block_eq hlt callBb with heq | heq
  · -- idx = callBb
    rw [heq] at hstep ⊢
    rw [hext] at hstep
    simp only [BlockStepSpliced, hget_at_call] at hstep
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hcall_get
    rw [← hlen] at hsb
    rw [hcall_term] at htb
    simp only [termBounded, Bool.and_eq_true] at htb
    rw [hspliced_feats, evalStmts_append, evalStmts_prefix hsb] at hstep
    cases hs_c : evalStmts caller.features cpu locals drops bbCall.stmts with
    | error f =>
      simp only [hs_c, Except.map] at hstep
      rw [hstep]
      exact .stmtFault hcall_get hs_c
    | ok pair =>
      rcases pair with ⟨locals₁, drops₁⟩
      have hlen₁ : locals₁.length = caller.numLocals :=
        (evalStmts_preserves_length hs_c).trans hlen
      have hpos₁ : 1 ≤ locals₁.length := by
        rw [hlen₁]; exact Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1
      have hab : operandListBounded locals₁.length argOps = true := by
        rw [hlen₁]; exact htb.1.1.1
      have hcpu_ce : allFeaturesPresent callee.features cpu = true := by
        rw [hfeats]; exact hcpu_ok
      simp only [hs_c, Except.map] at hstep
      rw [← hlen₁, buildCallPrelude_correct caller.features cpu locals₁ extra drops₁ callee argOps
            hpos₁ hcallee_wf_unp.1.1 hextra harg_len hab] at hstep
      cases ha_c : evalArgs locals₁ argOps with
      | error f =>
        simp only [ha_c] at hstep
        rw [hstep]
        exact .callArgFault hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c
      | ok p2 =>
        rcases p2 with ⟨argVals, locals₂⟩
        have hlen₂ : locals₂.length = caller.numLocals :=
          (evalArgs_preserves_length ha_c).trans hlen₁
        simp only [ha_c] at hstep
        cases hinit_ce : initFrameLocals callee argVals with
        | none =>
          simp only [hinit_ce] at hstep
          rw [hstep]
          exact .callInitFault hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce
        | some cl₀ =>
          simp only [hinit_ce, TermStepSpliced] at hstep
          have hc0_lt : 0 < callee.blocks.length :=
            Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcallee_wf_unp.1.2
          have hcl₀_len : cl₀.length = callee.numLocals :=
            initFrameLocals_length hinit_ce
          rcases hstep.onCallee 0 (Nat.add_zero _).symm hc0_lt locals₂ cl₀ rfl hlen₂ hcl₀_len with
            ⟨outC, hexec_intra, hpost⟩
          have hexec_c := (callFree_execBlock_iff prog callee cpu hcallee_cf 0 cl₀ drops₁ outC).mpr hexec_intra
          cases outC with
          | returned retVal drops₂ =>
            cases htarget : target with
            | none =>
              rw [htarget] at hcall_term hpost
              simp only [CalleePostCaller] at hpost
              rw [hpost]
              exact .callReturnDiverging hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c
            | some retBb =>
              rw [htarget] at hcall_term hpost
              simp only [CalleePostCaller] at hpost
              cases hw : writeLocal locals₂ dst retVal with
              | error f =>
                rw [hw] at hpost
                rw [hpost]
                exact .callReturnWriteFault hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c hw
              | ok locals₃ =>
                rw [hw] at hpost
                exact .callReturnOk hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c hw hpost
          | unwound drops₂ =>
            cases hunw : unwind with
            | cleanup cbb =>
              rw [hunw] at hcall_term hpost
              simp only [CalleePostCaller] at hpost
              exact .callUnwindCleanup hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c hpost
            | continue_ =>
              rw [hunw] at hcall_term hpost
              simp only [CalleePostCaller] at hpost
              rw [hpost]
              exact .callUnwindContinue hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c
            | terminate =>
              rw [hunw] at hcall_term hpost
              simp only [CalleePostCaller] at hpost
              rw [hpost]
              exact .callUnwindTerminate hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c
            | unreachable =>
              rw [hunw] at hcall_term hpost
              simp only [CalleePostCaller] at hpost
              rw [hpost]
              exact .callUnwindUnreachable hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c
          | aborted drops₂ =>
            simp only [CalleePostCaller] at hpost
            rw [hpost]
            exact .callPropagateAbort hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c
          | fault f =>
            simp only [CalleePostCaller] at hpost
            rw [hpost]
            exact .callPropagateFault hcall_get hs_c hcall_term hcall_ncl hcallee_get hcpu_ce ha_c hinit_ce hexec_c
  · -- idx ≠ callBb
    rcases getAt_lt_some hlt with ⟨bb, hg_c⟩
    have hg_sp := hget_non_call idx bb hlt heq hg_c
    have ⟨hsb, _, htb⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hg_c
    rw [← hlen] at hsb
    rw [hext] at hstep
    simp only [BlockStepSpliced, hg_sp] at hstep
    rw [hspliced_feats, evalStmts_prefix hsb] at hstep
    cases hs_c : evalStmts caller.features cpu locals drops bb.stmts with
    | error f =>
      simp only [hs_c, Except.map] at hstep
      rw [hstep]
      exact .stmtFault hg_c hs_c
    | ok pair =>
      rcases pair with ⟨locals₁, drops₁⟩
      have hlen₁ : locals₁.length = caller.numLocals :=
        (evalStmts_preserves_length hs_c).trans hlen
      simp only [hs_c, Except.map, TermStepSpliced] at hstep
      cases ht_c : bb.term with
      | goto t =>
        rw [ht_c] at htb; simp only [termBounded, decide_eq_true_eq] at htb
        simp only [ht_c] at hstep
        exact .goto hg_c hs_c ht_c (hstep.onCaller htb locals₁ extra rfl hlen₁ hextra)
      | switchBool cond tT fT =>
        rw [ht_c] at htb; simp only [termBounded, Bool.and_eq_true, decide_eq_true_eq] at htb
        have hcb_op : operandBounded locals₁.length cond = true := by rw [hlen₁]; exact htb.1.1
        simp only [ht_c, evalOperand_prefix hcb_op] at hstep
        cases hc_c : evalOperand locals₁ cond with
        | error f =>
          simp only [hc_c, Except.map] at hstep; rw [hstep]
          exact .switchFault hg_c hs_c ht_c hc_c
        | ok p2 =>
          rcases p2 with ⟨v, locals₂⟩
          have hlen₂ : locals₂.length = caller.numLocals :=
            (evalOperand_preserves_length hc_c).trans hlen₁
          cases v with
          | int n =>
            simp only [hc_c, Except.map] at hstep; rw [hstep]
            exact .switchNonBool hg_c hs_c ht_c hc_c
          | bool b =>
            cases b with
            | true =>
              simp only [hc_c, Except.map] at hstep
              exact .switchTrue hg_c hs_c ht_c hc_c
                (hstep.onCaller htb.1.2 locals₂ extra rfl hlen₂ hextra)
            | false =>
              simp only [hc_c, Except.map] at hstep
              exact .switchFalse hg_c hs_c ht_c hc_c
                (hstep.onCaller htb.2 locals₂ extra rfl hlen₂ hextra)
      | return_ =>
        simp only [ht_c] at hstep
        cases hcl : bb.isCleanup with
        | true =>
          simp only [hcl, ↓reduceIte] at hstep; rw [hstep]
          exact .returnCleanupFault hg_c hs_c ht_c hcl
        | false =>
          have hpos : 0 < locals₁.length := by
            rw [hlen₁]
            exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ _)
              (Nat.le_trans (Nat.le_add_right 1 _) hcaller_wf_unp.1.1)
          simp only [hcl, Bool.false_eq_true, ↓reduceIte, getAt_append_left hpos] at hstep
          rcases getAt_lt_some hpos with ⟨s0, hs0⟩
          rw [hs0] at hstep
          cases s0 with
          | liveVal v =>
            simp only [] at hstep; rw [hstep]
            exact .returnOk hg_c hs_c ht_c hcl hs0
          | liveUninit =>
            simp only [] at hstep; rw [hstep]
            exact .returnUninitOrDead hg_c hs_c ht_c hcl hs0 (Or.inl rfl)
          | dead =>
            simp only [] at hstep; rw [hstep]
            exact .returnUninitOrDead hg_c hs_c ht_c hcl hs0 (Or.inr rfl)
      | unreachable =>
        simp only [ht_c] at hstep; rw [hstep]
        exact .unreachable hg_c hs_c ht_c
      | unwindTerminate =>
        simp only [ht_c] at hstep; rw [hstep]
        exact .unwindTerminate hg_c hs_c ht_c
      | unwindResume =>
        simp only [ht_c] at hstep
        cases hcl : bb.isCleanup with
        | true =>
          simp only [hcl, ↓reduceIte] at hstep; rw [hstep]
          exact .unwindResumeOk hg_c hs_c ht_c hcl
        | false =>
          simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hstep; rw [hstep]
          exact .unwindResumeFault hg_c hs_c ht_c hcl
      | unwindStart u =>
        simp only [ht_c] at hstep
        cases u with
        | cleanup cbb =>
          rw [ht_c] at htb; simp only [termBounded, unwindBounded, decide_eq_true_eq] at htb
          exact .unwindStartCleanup hg_c hs_c ht_c
            (hstep.onCaller htb locals₁ extra rfl hlen₁ hextra)
        | continue_ =>
          rw [hstep]; exact .unwindStartContinue hg_c hs_c ht_c
        | terminate =>
          rw [hstep]; exact .unwindStartTerminate hg_c hs_c ht_c
        | unreachable =>
          rw [hstep]; exact .unwindStartUnreachable hg_c hs_c ht_c
      | call cId cArgs cDst cTarget cUnwind =>
        rw [ht_c] at htb
        simp only [termBounded, Bool.and_eq_true] at htb
        simp only [ht_c] at hstep
        cases hcl : bb.isCleanup with
        | true =>
          simp only [hcl, ↓reduceIte] at hstep; rw [hstep]
          exact .callInCleanupFault hg_c hs_c ht_c hcl
        | false =>
          simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hstep
          cases hcg : getAt prog cId with
          | none =>
            simp only [hcg] at hstep; rw [hstep]
            exact .callMissingCallee hg_c hs_c ht_c hcl hcg
          | some cBody =>
            simp only [hcg] at hstep
            cases hcfeat : allFeaturesPresent cBody.features cpu with
            | false =>
              simp only [hcfeat, Bool.not_false, ↓reduceIte] at hstep; rw [hstep]
              exact .callFeatureFault hg_c hs_c ht_c hcl hcg hcfeat
            | true =>
              have hab : operandListBounded locals₁.length cArgs = true := by
                rw [hlen₁]; exact htb.1.1.1
              simp only [hcfeat, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                evalArgs_prefix hab] at hstep
              cases ha_c : evalArgs locals₁ cArgs with
              | error f =>
                simp only [ha_c, Except.map] at hstep; rw [hstep]
                exact .callArgFault hg_c hs_c ht_c hcl hcg hcfeat ha_c
              | ok p2 =>
                rcases p2 with ⟨argVals, locals₂⟩
                have hlen₂ : locals₂.length = caller.numLocals :=
                  (evalArgs_preserves_length ha_c).trans hlen₁
                simp only [ha_c, Except.map] at hstep
                cases hinit_o : initFrameLocals cBody argVals with
                | none =>
                  simp only [hinit_o] at hstep; rw [hstep]
                  exact .callInitFault hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o
                | some cl₀ =>
                  simp only [hinit_o] at hstep
                  rcases hstep with ⟨outC, hexec_c, hcont⟩
                  cases outC with
                  | returned retVal drops₂ =>
                    cases hct : cTarget with
                    | none =>
                      rw [hct] at ht_c hcont
                      simp only [CallContStep] at hcont; rw [hcont]
                      exact .callReturnDiverging hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c
                    | some retBb =>
                      rw [hct] at ht_c htb hcont
                      simp only [optBlockBounded, decide_eq_true_eq] at htb
                      have hdst_c : cDst < locals₂.length := by
                        rw [hlen₂]; exact htb.1.1.2
                      simp only [CallContStep, writeLocal_prefix hdst_c] at hcont
                      cases hw : writeLocal locals₂ cDst retVal with
                      | error f =>
                        simp only [hw, Except.map] at hcont; rw [hcont]
                        exact .callReturnWriteFault hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c hw
                      | ok locals₃ =>
                        simp only [hw, Except.map] at hcont
                        have hlen₃ : locals₃.length = caller.numLocals :=
                          (writeLocal_preserves_length hw).trans hlen₂
                        exact .callReturnOk hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c hw
                          (hcont.onCaller htb.1.2 locals₃ extra rfl hlen₃ hextra)
                  | unwound drops₂ =>
                    cases hcu : cUnwind with
                    | cleanup cbb =>
                      rw [hcu] at ht_c htb hcont
                      simp only [unwindBounded, decide_eq_true_eq] at htb
                      simp only [CallContStep] at hcont
                      exact .callUnwindCleanup hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c
                        (hcont.onCaller htb.2 locals₂ extra rfl hlen₂ hextra)
                    | continue_ =>
                      rw [hcu] at ht_c hcont; simp only [CallContStep] at hcont; rw [hcont]
                      exact .callUnwindContinue hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c
                    | terminate =>
                      rw [hcu] at ht_c hcont; simp only [CallContStep] at hcont; rw [hcont]
                      exact .callUnwindTerminate hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c
                    | unreachable =>
                      rw [hcu] at ht_c hcont; simp only [CallContStep] at hcont; rw [hcont]
                      exact .callUnwindUnreachable hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c
                  | aborted drops₂ =>
                    simp only [CallContStep] at hcont; rw [hcont]
                    exact .callPropagateAbort hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c
                  | fault f =>
                    simp only [CallContStep] at hcont; rw [hcont]
                    exact .callPropagateFault hg_c hs_c ht_c hcl hcg hcfeat ha_c hinit_o hexec_c

/-- Backward completeness of `inlineCallSite`: every execution outcome of `spliced`
    was already a valid interprocedural execution outcome of `caller`. -/
theorem inlineCallSite_complete
    {prog : Program} {caller spliced : Body} {callBb : BlockId}
    {cpu : List FeatureId} {args : List Val} {out : Outcome}
    (hinline : inlineCallSite prog caller callBb = some spliced)
    (hexec : ExecBody prog spliced cpu args out) :
    ExecBody prog caller cpu args out := by
  unfold inlineCallSite at hinline
  cases hwf_c : bodyWellFormed caller false with
  | false => simp [hwf_c] at hinline
  | true =>
    simp only [hwf_c, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
    cases hget_bb : getAt caller.blocks callBb with
    | none => simp [hget_bb] at hinline
    | some bbCall =>
      rcases bbCall with ⟨isCl, bbStmts, bbTerm⟩
      simp only [hget_bb] at hinline
      cases isCl with
      | true => simp at hinline
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hinline
        cases bbTerm with
        | goto _ | switchBool _ _ _ | return_ | unreachable | unwindTerminate
        | unwindResume | unwindStart _ => simp at hinline
        | call calleeId argOps dst target unwind =>
          simp only [] at hinline
          cases hget_ce : getAt prog calleeId with
          | none => simp [hget_ce] at hinline
          | some callee =>
            simp only [hget_ce] at hinline
            cases hwf_ce : bodyWellFormed callee true with
            | false => simp [hwf_ce] at hinline
            | true =>
              simp only [hwf_ce, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
              cases hcf_ce : isCallFree callee with
              | false => simp [hcf_ce] at hinline
              | true =>
                simp only [hcf_ce, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
                cases hfeq : eqNatList callee.features caller.features with
                | false => simp [hfeq] at hinline
                | true =>
                  simp only [hfeq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
                  cases hargb : Nat.beq argOps.length callee.argCount with
                  | false => simp [hargb] at hinline
                  | true =>
                    simp only [hargb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hinline
                    cases hsetp : setAt caller.blocks callBb
                      { isCleanup := false
                        stmts := bbStmts ++ buildCallPrelude caller.numLocals callee.argCount callee.numLocals argOps
                        term := .goto caller.blocks.length } with
                    | none => simp [hsetp] at hinline
                    | some patchedBlocks =>
                      simp only [hsetp, Option.some.injEq] at hinline
                      have hspliced := hinline.symm
                      have hpatched_len : patchedBlocks.length = caller.blocks.length := setAt_length hsetp
                      have hfeats : callee.features = caller.features := eqNatList_eq hfeq
                      have harg_len : argOps.length = callee.argCount := Nat.eq_of_beq_eq_true hargb
                      have hs_feats : spliced.features = caller.features := by rw [hspliced]
                      have hs_feats_ce : spliced.features = callee.features := by rw [hspliced, hfeats]
                      have hcaller_wf_unp := hwf_c
                      simp only [bodyWellFormed, Bool.and_eq_true, decide_eq_true_eq] at hcaller_wf_unp
                      have ⟨_, _, htb_call⟩ := blocksWellFormed_getAt hcaller_wf_unp.2 hget_bb
                      simp only [termBounded, Bool.and_eq_true] at htb_call
                      have hdst_lt : dst < caller.numLocals := decide_eq_true_eq.mp htb_call.1.1.2
                      have hu_bound : unwindBounded caller.blocks.length unwind = true := htb_call.2
                      have hget_non_call : ∀ j bb,
                          j < caller.blocks.length → j ≠ callBb →
                          getAt caller.blocks j = some bb →
                          getAt spliced.blocks j = some bb := by
                        intro j bb hj hne hg
                        rw [hspliced]; simp only [List.append_assoc]
                        have hj_p : j < patchedBlocks.length := by rw [hpatched_len]; exact hj
                        rw [getAt_append_left hj_p, getAt_setAt_ne hsetp hne]
                        exact hg
                      have hget_at_call :
                          getAt spliced.blocks callBb = some {
                            isCleanup := false
                            stmts := bbStmts ++ buildCallPrelude caller.numLocals callee.argCount callee.numLocals argOps
                            term := .goto caller.blocks.length
                          } := by
                        have hlt_call : callBb < patchedBlocks.length := by
                          rw [hpatched_len]; exact getAt_some_lt hget_bb
                        rw [hspliced]; simp only [List.append_assoc]
                        rw [getAt_append_left hlt_call]
                        exact getAt_setAt_same hsetp
                      have hget_spliced_cb : ∀ j bb,
                          getAt callee.blocks j = some bb →
                          getAt spliced.blocks (caller.blocks.length + j) =
                            some (integrateBlock caller.numLocals caller.blocks.length
                              (caller.blocks.length + callee.blocks.length) target unwind bb) := by
                        intro j bb hg
                        have hlt_j : j < callee.blocks.length := getAt_some_lt hg
                        have hidx_eq : caller.blocks.length + j = patchedBlocks.length + j := by
                          rw [hpatched_len]
                        have hlt_map : j < (callee.blocks.map (integrateBlock caller.numLocals caller.blocks.length
                            (caller.blocks.length + callee.blocks.length) target unwind)).length := by
                          simp [hlt_j]
                        rw [hspliced]; simp only [List.append_assoc]
                        rw [hidx_eq, getAt_append_right patchedBlocks _ j, getAt_append_left hlt_map, getAt_map, hg]
                        rfl
                      have hinit_eq := initFrameLocals_spliced
                        (caller := caller) (callee := callee) (spliced := spliced) (args := args)
                        hcaller_wf_unp.1.1 (by rw [hspliced]) (by rw [hspliced])
                      unfold ExecBody at hexec ⊢
                      rw [hs_feats] at hexec
                      cases hcpu : allFeaturesPresent caller.features cpu with
                      | false =>
                        simp [hcpu] at hexec ⊢
                        exact hexec
                      | true =>
                        simp only [hcpu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hexec ⊢
                        rw [hinit_eq] at hexec
                        cases hinit_c : initFrameLocals caller args with
                        | none =>
                          simp [hinit_c] at hexec ⊢
                          exact hexec
                        | some locals₀ =>
                          simp only [hinit_c, Option.map] at hexec ⊢
                          have hb0 : 0 < caller.blocks.length :=
                            Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hcaller_wf_unp.1.2
                          have hl0 : locals₀.length = caller.numLocals :=
                            initFrameLocals_length hinit_c
                          have hinv := execBlock_induct_spliced
                            (SplicedInv prog cpu caller callee dst target unwind)
                            (fun idx extLocals drops out hstep => {
                              onCaller := fun hlt locals extra hext hlen hextra =>
                                splicedInv_step_caller hwf_c hcpu hget_bb rfl rfl
                                  hget_ce hwf_ce hcf_ce hfeats harg_len hs_feats
                                  hget_non_call hget_at_call hstep hlt hext hlen hextra
                              onCallee := fun cb hidx hcb cs₂ cls hext hcs₂_len hcls_len =>
                                splicedInv_step_callee hwf_ce hcf_ce hs_feats_ce hu_bound
                                  hget_spliced_cb hstep hidx hcb hext hcs₂_len hcls_len
                              onTramp := fun retBb htarget hidx cs₂ s0 lTail hext hcs₂_len hcl_len => by
                                have hret_lt : retBb < caller.blocks.length := by
                                  have hopt := htb_call.1.2
                                  rw [htarget] at hopt
                                  exact decide_eq_true_eq.mp hopt
                                have hget_tr : getAt spliced.blocks (caller.blocks.length + callee.blocks.length) =
                                    some { isCleanup := false
                                           stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
                                           term := .goto retBb } := by
                                  let preList := patchedBlocks ++ callee.blocks.map
                                    (integrateBlock caller.numLocals caller.blocks.length
                                      (caller.blocks.length + callee.blocks.length) (some retBb) unwind)
                                  have hpre_len : preList.length = caller.blocks.length + callee.blocks.length := by
                                    simp [preList, hpatched_len]
                                  have h0_tr := getAt_append_right preList
                                    [{ isCleanup := false
                                       stmts := [Stmt.assign dst (.use (.move caller.numLocals))]
                                       term := .goto retBb }] 0
                                  rw [Nat.add_zero, hpre_len] at h0_tr
                                  rw [hspliced, htarget]
                                  exact h0_tr
                                exact splicedInv_step_tramp hdst_lt hret_lt hget_tr hstep
                                  hidx hext hcs₂_len hcl_len
                            })
                            hexec rfl
                          exact hinv.onCaller hb0 locals₀ (replicateSlot callee.numLocals .dead)
                            rfl hl0 (replicateSlot_length _ _)

/-- **Theorem 1 (`inlineCallSite_bisimulation`)**:
    Whenever `inlineCallSite prog caller callBb = some spliced`, the spliced body is
    in **exact trace & LIFO cleanup-drop bisimulation** with the interprocedural
    multi-frame execution of `caller` across all normal returns, unwinding cleanups,
    aborts, and faults. -/
theorem inlineCallSite_bisimulation
    {prog : Program} {caller spliced : Body} {callBb : BlockId}
    (hinline : inlineCallSite prog caller callBb = some spliced)
    (cpu : List FeatureId) (args : List Val) (out : Outcome) :
    ExecBody prog caller cpu args out ↔ ExecBody prog spliced cpu args out :=
  ⟨inlineCallSite_sound hinline, inlineCallSite_complete hinline⟩


/-! ## Section 12: Intra-Procedural Reduction Theorem & 3-Frame LIFO Cleanup Witness -/

/-- Transitive chain of valid `inlineCallSite` transformations across an acyclic call graph. -/
inductive ValidInlineChain (prog : Program) : Body → Body → Prop where
  | refl (b : Body) : ValidInlineChain prog b b
  | step {b₀ b₁ b₂ : Body} (callBb : BlockId) :
      inlineCallSite prog b₀ callBb = some b₁ →
      ValidInlineChain prog b₁ b₂ →
      ValidInlineChain prog b₀ b₂

theorem validInlineChain_bisimulation
    {prog : Program} {entry finalBody : Body}
    (hchain : ValidInlineChain prog entry finalBody)
    (cpu : List FeatureId) (args : List Val) (out : Outcome) :
    ExecBody prog entry cpu args out ↔ ExecBody prog finalBody cpu args out := by
  induction hchain with
  | refl _ => exact Iff.rfl
  | step _ hstep _ ih =>
    exact (inlineCallSite_bisimulation hstep cpu args out).trans ih

/-- **Theorem 2 (`inlineChain_intra_reduction` — Intra-Procedural Verification Unlocking)**:
    Once every `Terminator.call` reachable from `entry` in an acyclic call hierarchy is
    spliced via `ValidInlineChain prog entry finalBody` into a call-free body
    (`isCallFree finalBody = true`), multi-frame interprocedural semantics (`ExecBody`)
    coincides (`↔`) with purely intra-procedural single-frame semantics (`ExecBodyIntra`)
    where `Terminator.call` fails closed with `.fault .unsupported` (matching `Anneal`
    `Trusted/MirSemantics.lean`). -/
theorem inlineChain_intra_reduction
    {prog : Program} {entry finalBody : Body}
    (hchain : ValidInlineChain prog entry finalBody)
    (hcf : isCallFree finalBody = true)
    (cpu : List FeatureId) (args : List Val) (out : Outcome) :
    ExecBody prog entry cpu args out ↔ ExecBodyIntra finalBody cpu args out :=
  (validInlineChain_bisimulation hchain cpu args out).trans
    (callFree_execBody_iff prog finalBody cpu hcf args out)

/-- Concrete 3-frame LIFO cleanup-pad hierarchy (`outerCaller -> middleCallee -> innerCallee`)
    matching the empirical `Guard(1)` / `Guard(2)` / `Guard(3)` Miri + native probe. -/
def lifoInnerCallee : Body := {
  -- _0: ret, _1: shouldPanic (Bool), _2: x (Int), _3: Guard(3)
  numLocals := 4
  argCount := 2
  features := []
  blocks := [
    -- bb0: init Guard(3), branch on shouldPanic
    { isCleanup := false
      stmts := [.storageLive 3, .assign 3 (.use (.constVal (.int 0)))]
      term := .switchBool (.copy 1) 2 1 },
    -- bb1: normal return: _0 = _2 + 2; drop Guard(3); return
    { isCleanup := false
      stmts := [.assign 0 (.addNat (.copy 2) (.constVal (.int 2))),
                .dropGuard 3 3, .storageDead 3]
      term := .return_ },
    -- bb2: panic start -> cleanup bb3
    { isCleanup := false
      stmts := []
      term := .unwindStart (.cleanup 3) },
    -- bb3 (cleanup): drop Guard(3); unwindResume
    { isCleanup := true
      stmts := [.dropGuard 3 3, .storageDead 3]
      term := .unwindResume }
  ]
}

def lifoMiddleCallee : Body := {
  -- _0: ret, _1: shouldPanic (Bool), _2: x (Int), _3: Guard(2), _4: innerRet
  numLocals := 5
  argCount := 2
  features := []
  blocks := [
    -- bb0: init Guard(2), call innerCallee(0)
    { isCleanup := false
      stmts := [.storageLive 3, .assign 3 (.use (.constVal (.int 0))), .storageLive 4]
      term := .call 0 [.copy 1, .copy 2] 4 (some 1) (.cleanup 2) },
    -- bb1: normal return: _0 = _4 + 40; drop Guard(2); return
    { isCleanup := false
      stmts := [.assign 0 (.addNat (.move 4) (.constVal (.int 40))),
                .storageDead 4, .dropGuard 3 2, .storageDead 3]
      term := .return_ },
    -- bb2 (cleanup): drop Guard(2); unwindResume
    { isCleanup := true
      stmts := [.storageDead 4, .dropGuard 3 2, .storageDead 3]
      term := .unwindResume }
  ]
}

def lifoOuterCaller : Body := {
  -- _0: ret, _1: shouldPanic (Bool), _2: Guard(1), _3: midRet
  numLocals := 4
  argCount := 1
  features := []
  blocks := [
    -- bb0: init Guard(1), call middleCallee(1) with (shouldPanic, 0)
    { isCleanup := false
      stmts := [.storageLive 2, .assign 2 (.use (.constVal (.int 0))), .storageLive 3]
      term := .call 1 [.copy 1, .constVal (.int 0)] 3 (some 1) (.cleanup 2) },
    -- bb1: normal return: _0 = move _3; drop Guard(1); return
    { isCleanup := false
      stmts := [.assign 0 (.use (.move 3)), .storageDead 3, .dropGuard 2 1, .storageDead 2]
      term := .return_ },
    -- bb2 (cleanup): drop Guard(1); unwindResume
    { isCleanup := true
      stmts := [.storageDead 3, .dropGuard 2 1, .storageDead 2]
      term := .unwindResume }
  ]
}

def lifoProg : Program :=
  match inlineCallSite [lifoInnerCallee] lifoMiddleCallee 0 with
  | none => [lifoInnerCallee, lifoMiddleCallee]
  | some midSpliced => [lifoInnerCallee, midSpliced]

theorem three_frame_lifo_cleanup_verified :
    ∃ midSpliced outerSpliced,
      inlineCallSite [lifoInnerCallee, lifoMiddleCallee] lifoMiddleCallee 0 = some midSpliced ∧
      inlineCallSite [lifoInnerCallee, midSpliced] lifoOuterCaller 0 = some outerSpliced ∧
      isCallFree outerSpliced = true ∧
      evalBodyInterproc [lifoInnerCallee, lifoMiddleCallee] lifoOuterCaller [] 30 [.bool false] =
        .returned (.int 42) [3, 2, 1] ∧
      evalBodyIntra outerSpliced [] 30 [.bool false] =
        .returned (.int 42) [3, 2, 1] ∧
      evalBodyInterproc [lifoInnerCallee, lifoMiddleCallee] lifoOuterCaller [] 30 [.bool true] =
        .unwound [3, 2, 1] ∧
      evalBodyIntra outerSpliced [] 30 [.bool true] =
        .unwound [3, 2, 1] := by
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Section 13: Sharpness Counterexamples (`ce1`, `ce2`, `ce3`) -/

/-- Single-step inversion helper for concrete counterexample bodies. -/
theorem execBlock_step_once
    {prog : Program} {cpu : List FeatureId} {body : Body}
    {idx : BlockId} {locals : List LocalSlot} {drops : List DropTag} {out : Outcome}
    (h : ExecBlock prog cpu body idx locals drops out) :
    BlockStepSpliced prog cpu body (ExecBlock prog cpu body) idx locals drops out := by
  cases h with
  | oobBlock hg => simp [BlockStepSpliced, hg]
  | stmtFault hg hs => simp [BlockStepSpliced, hg, hs]
  | goto hg hs ht hsub => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hsub]
  | switchFault hg hs ht hc => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc]
  | switchNonBool hg hs ht hc => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc]
  | switchTrue hg hs ht hc hsub => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc, hsub]
  | switchFalse hg hs ht hc hsub => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hc, hsub]
  | returnCleanupFault hg hs ht hcl => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl]
  | returnOk hg hs ht hcl h0 => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, h0]
  | returnUninitOrDead hg hs ht hcl h0 hor =>
    rcases hor with rfl | rfl <;> simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, h0]
  | returnNoSlot hg hs ht hcl h0 => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, h0]
  | unreachable hg hs ht => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]
  | unwindTerminate hg hs ht => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]
  | unwindResumeOk hg hs ht hcl => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl]
  | unwindResumeFault hg hs ht hcl => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl]
  | unwindStartCleanup hg hs ht hsub => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hsub]
  | unwindStartContinue hg hs ht => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]
  | unwindStartTerminate hg hs ht => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]
  | unwindStartUnreachable hg hs ht => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht]
  | callInCleanupFault hg hs ht hcl => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl]
  | callMissingCallee hg hs ht hcl hmiss => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hmiss]
  | callFeatureFault hg hs ht hcl hcg hff => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hcg, hff]
  | callArgFault hg hs ht hcl hcg hcf ha => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hcg, hcf, ha]
  | callInitFault hg hs ht hcl hcg hcf ha hi => simp [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, hcg, hcf, ha, hi]
  | callReturnOk hg hs ht hcl hcg hcf ha hi hc hw hcont =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, by simp [CallContStep, hw, hcont]⟩
  | callReturnWriteFault hg hs ht hcl hcg hcf ha hi hc hw =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, by simp [CallContStep, hw]⟩
  | callReturnDiverging hg hs ht hcl hcg hcf ha hi hc =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, rfl⟩
  | callUnwindCleanup hg hs ht hcl hcg hcf ha hi hc hcont =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, hcont⟩
  | callUnwindContinue hg hs ht hcl hcg hcf ha hi hc =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, rfl⟩
  | callUnwindTerminate hg hs ht hcl hcg hcf ha hi hc =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, rfl⟩
  | callUnwindUnreachable hg hs ht hcl hcg hcf ha hi hc =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, rfl⟩
  | callPropagateAbort hg hs ht hcl hcg hcf ha hi hc =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, rfl⟩
  | callPropagateFault hg hs ht hcl hcg hcf ha hi hc =>
    simp only [BlockStepSpliced, TermStepSpliced, hg, hs, ht, hcl, Bool.false_eq_true, ↓reduceIte,
      hcg, hcf, Bool.not_true, ha, hi]
    exact ⟨_, hc, rfl⟩

/-! ### Counterexample 1: Unshifted Callee Locals Corrupt the Caller Frame -/

/-- Buggy splicer omitting the `+ caller.numLocals` local offset (`localOff = 0`). -/
def buggyInlineUnshiftedLocals (prog : Program) (caller : Body) (callBb : BlockId) : Option Body :=
  match getAt caller.blocks callBb with
  | none => none
  | some bb =>
    match bb.term with
    | .call calleeId argOps dst target unwind =>
      match getAt prog calleeId with
      | none => none
      | some callee =>
        let B := caller.blocks.length
        let C := callee.blocks.length
        let patchedCallBb : BasicBlock := {
          isCleanup := false
          stmts := bb.stmts ++ buildCallPrelude 0 callee.argCount callee.numLocals argOps
          term := .goto B
        }
        match setAt caller.blocks callBb patchedCallBb with
        | none => none
        | some callerBlocksPatched =>
          some {
            numLocals := caller.numLocals + callee.numLocals
            argCount := caller.argCount
            features := caller.features
            blocks := callerBlocksPatched ++
              callee.blocks.map (integrateBlock 0 B (B + C) target unwind) ++
              mkReturnTrampoline 0 dst target
          }
    | _ => none

def ce1Callee : Body := {
  -- _0: ret, _1: scratch temp (writes 99, returns 7)
  numLocals := 2
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1, .assign 1 (.use (.constVal (.int 99))),
                .assign 0 (.use (.constVal (.int 7)))]
      term := .return_ }
  ]
}

def ce1Caller : Body := {
  -- _0: ret, _1: live caller local (= 100), _2: call dest -> returns _1 + _2 = 107
  numLocals := 3
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1, .assign 1 (.use (.constVal (.int 100))), .storageLive 2]
      term := .call 0 [] 2 (some 1) .continue_ },
    { isCleanup := false
      stmts := [.assign 0 (.addNat (.copy 1) (.copy 2))]
      term := .return_ }
  ]
}

/-- **Sharpness Counterexample 1 (`ce1_unshifted_local_collision_corrupts_caller_frame`)**:
    Without shifting callee locals by `+ caller.numLocals`, callee scratch local `_1`
    collides with caller local `_1 = 100`, overwriting it with `99` and corrupting the
    caller's return value from `107` to `106` (whereas `inlineCallSite` preserves `107`). -/
theorem ce1_unshifted_local_collision_corrupts_caller_frame :
    ∃ goodSpliced buggySpliced,
      inlineCallSite [ce1Callee] ce1Caller 0 = some goodSpliced ∧
      buggyInlineUnshiftedLocals [ce1Callee] ce1Caller 0 = some buggySpliced ∧
      ExecBody [ce1Callee] ce1Caller [] [] (.returned (.int 107) []) ∧
      ExecBody [ce1Callee] goodSpliced [] [] (.returned (.int 107) []) ∧
      ExecBody [ce1Callee] buggySpliced [] [] (.returned (.int 106) []) ∧
      ¬ ExecBody [ce1Callee] buggySpliced [] [] (.returned (.int 107) []) := by
  refine ⟨_, _, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- ExecBody ce1Caller = .returned 107 []
    have hce : ExecBlock [ce1Callee] [] ce1Callee 0 [.liveUninit, .dead] [] (.returned (.int 7) []) :=
      .returnOk rfl rfl rfl rfl rfl
    exact .callReturnOk rfl rfl rfl rfl rfl rfl rfl rfl hce rfl
      (.returnOk rfl rfl rfl rfl rfl)
  · -- ExecBody goodSpliced = .returned 107 []
    exact .goto rfl rfl rfl
      (.goto rfl rfl rfl
        (.goto rfl rfl rfl
          (.returnOk rfl rfl rfl rfl rfl)))
  · -- ExecBody buggySpliced = .returned 106 []
    exact .goto rfl rfl rfl
      (.goto rfl rfl rfl
        (.goto rfl rfl rfl
          (.returnOk rfl rfl rfl rfl rfl)))
  · -- ¬ ExecBody buggySpliced (.returned 107 [])
    intro h0
    unfold ExecBody at h0
    dsimp [allFeaturesPresent, initFrameLocals, replicateSlot] at h0
    have h1 := execBlock_step_once h0
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, buildCallPrelude, buildArgBindings,
      resetDeadRange, integrateBlock, integrateTerm, mkReturnTrampoline] at h1
    have h2 := execBlock_step_once h1
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, shiftStmt, shiftRvalue, shiftOperand,
      integrateBlock, integrateTerm, mkReturnTrampoline] at h2
    have h3 := execBlock_step_once h2
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, integrateBlock, integrateTerm, mkReturnTrampoline] at h3
    have h4 := execBlock_step_once h3
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, integrateBlock, integrateTerm, mkReturnTrampoline] at h4
    cases h4


/-! ### Counterexample 2: Omitting `UnwindResume -> Goto(callerCleanup)` Skips Caller Drops -/

def buggyIntegrateTermNoUnwindSplice (localOff blockOff retTrampoline : Nat)
    (callerTarget : Option BlockId) (callerUnwind : UnwindAction)
    (inCleanup : Bool) : Terminator → Terminator
  | .goto target => .goto (blockOff + target)
  | .switchBool cond tT fT => .switchBool (shiftOperand localOff cond) (blockOff + tT) (blockOff + fT)
  | .return_ =>
    if inCleanup then .return_
    else match callerTarget with | some _ => .goto retTrampoline | none => .unreachable
  | .unwindStart u => .unwindStart (mapUnwind blockOff callerUnwind u)
  | .unwindResume => .unwindResume   -- BUG: fails to rewrite `.cleanup cbb => .goto cbb`!
  | .unwindTerminate => .unwindTerminate
  | .unreachable => .unreachable
  | .call c a d t u =>
    .call c (a.map (shiftOperand localOff)) (localOff + d)
      (t.map (blockOff + ·)) (mapUnwind blockOff callerUnwind u)

def buggyInlineNoUnwindSplice (prog : Program) (caller : Body) (callBb : BlockId) : Option Body :=
  match getAt caller.blocks callBb with
  | none => none
  | some bb =>
    match bb.term with
    | .call calleeId argOps dst target unwind =>
      match getAt prog calleeId with
      | none => none
      | some callee =>
        let N := caller.numLocals
        let B := caller.blocks.length
        let C := callee.blocks.length
        let patchedCallBb : BasicBlock := {
          isCleanup := false
          stmts := bb.stmts ++ buildCallPrelude N callee.argCount callee.numLocals argOps
          term := .goto B
        }
        match setAt caller.blocks callBb patchedCallBb with
        | none => none
        | some callerBlocksPatched =>
          some {
            numLocals := N + callee.numLocals
            argCount := caller.argCount
            features := caller.features
            blocks := callerBlocksPatched ++
              callee.blocks.map (fun cbb => {
                isCleanup := cbb.isCleanup
                stmts := cbb.stmts.map (shiftStmt N)
                term := buggyIntegrateTermNoUnwindSplice N B (B + C) target unwind cbb.isCleanup cbb.term
              }) ++
              mkReturnTrampoline N dst target
          }
    | _ => none

def ce2PanickingCallee : Body := {
  -- _0: ret, _1: Guard(20); panics and drops Guard(20) in cleanup bb1
  numLocals := 2
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1, .assign 1 (.use (.constVal (.int 0)))]
      term := .unwindStart (.cleanup 1) },
    { isCleanup := true
      stmts := [.dropGuard 1 20, .storageDead 1]
      term := .unwindResume }
  ]
}

def ce2CallerWithGuard : Body := {
  -- _0: ret, _1: Guard(10), _2: call dest; cleanup bb2 drops Guard(10)
  numLocals := 3
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1, .assign 1 (.use (.constVal (.int 0))), .storageLive 2]
      term := .call 0 [] 2 (some 1) (.cleanup 2) },
    { isCleanup := false
      stmts := [.assign 0 (.use (.constVal (.int 0))), .dropGuard 1 10, .storageDead 1]
      term := .return_ },
    { isCleanup := true
      stmts := [.dropGuard 1 10, .storageDead 1]
      term := .unwindResume }
  ]
}

/-- **Sharpness Counterexample 2 (`ce2_missing_unwind_resume_to_cleanup_splice_skips_caller_drop`)**:
    When a panicking callee's cleanup `UnwindResume` is NOT spliced to `Goto(callerCleanup)`,
    unwinding exits the entire outer function directly from the callee's cleanup block with
    drop trace `[20]`, skipping the caller's live `Guard(10)` destructor (`[20, 10]`). -/
theorem ce2_missing_unwind_resume_to_cleanup_splice_skips_caller_drop :
    ∃ goodSpliced buggySpliced,
      inlineCallSite [ce2PanickingCallee] ce2CallerWithGuard 0 = some goodSpliced ∧
      buggyInlineNoUnwindSplice [ce2PanickingCallee] ce2CallerWithGuard 0 = some buggySpliced ∧
      ExecBody [ce2PanickingCallee] ce2CallerWithGuard [] [] (.unwound [20, 10]) ∧
      ExecBody [ce2PanickingCallee] goodSpliced [] [] (.unwound [20, 10]) ∧
      ExecBody [ce2PanickingCallee] buggySpliced [] [] (.unwound [20]) ∧
      ¬ ExecBody [ce2PanickingCallee] buggySpliced [] [] (.unwound [20, 10]) := by
  refine ⟨_, _, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- ExecBody ce2CallerWithGuard = .unwound [20, 10]
    have hce : ExecBlock [ce2PanickingCallee] [] ce2PanickingCallee 0 [.liveUninit, .dead] [] (.unwound [20]) :=
      .unwindStartCleanup rfl rfl rfl (.unwindResumeOk rfl rfl rfl rfl)
    exact .callUnwindCleanup rfl rfl rfl rfl rfl rfl rfl rfl hce
      (.unwindResumeOk rfl rfl rfl rfl)
  · -- ExecBody goodSpliced = .unwound [20, 10]
    exact .goto rfl rfl rfl
      (.unwindStartCleanup rfl rfl rfl
        (.goto rfl rfl rfl
          (.unwindResumeOk rfl rfl rfl rfl)))
  · -- ExecBody buggySpliced = .unwound [20]
    exact .goto rfl rfl rfl
      (.unwindStartCleanup rfl rfl rfl
        (.unwindResumeOk rfl rfl rfl rfl))
  · -- ¬ ExecBody buggySpliced (.unwound [20, 10])
    intro h0
    unfold ExecBody at h0
    dsimp [allFeaturesPresent, initFrameLocals, replicateSlot] at h0
    have h1 := execBlock_step_once h0
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, buildCallPrelude, buildArgBindings,
      resetDeadRange, buggyIntegrateTermNoUnwindSplice, mkReturnTrampoline] at h1
    have h2 := execBlock_step_once h1
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, shiftStmt, shiftRvalue, shiftOperand,
      mapUnwind, buggyIntegrateTermNoUnwindSplice, mkReturnTrampoline] at h2
    have h3 := execBlock_step_once h2
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, shiftStmt, shiftRvalue, shiftOperand,
      buggyIntegrateTermNoUnwindSplice, mkReturnTrampoline] at h3
    cases h3


/-! ### Counterexample 3: Cross-Feature MIR Inlining Violates Target-Feature Gating -/

/-- Buggy splicer omitting the `eqNatList callee.features caller.features` guard. -/
def buggyInlineIgnoreFeatures (prog : Program) (caller : Body) (callBb : BlockId) : Option Body :=
  match getAt caller.blocks callBb with
  | none => none
  | some bb =>
    match bb.term with
    | .call calleeId argOps dst target unwind =>
      match getAt prog calleeId with
      | none => none
      | some callee =>
        let N := caller.numLocals
        let B := caller.blocks.length
        let C := callee.blocks.length
        let patchedCallBb : BasicBlock := {
          isCleanup := false
          stmts := bb.stmts ++ buildCallPrelude N callee.argCount callee.numLocals argOps
          term := .goto B
        }
        match setAt caller.blocks callBb patchedCallBb with
        | none => none
        | some callerBlocksPatched =>
          some {
            numLocals := N + callee.numLocals
            argCount := caller.argCount
            features := caller.features
            blocks := callerBlocksPatched ++
              callee.blocks.map (integrateBlock N B (B + C) target unwind) ++
              mkReturnTrampoline N dst target
          }
    | _ => none

/-- Callee compiled with `#[target_feature(enable = "avx2")]` (`FeatureId = 1`). -/
def ce3Avx2Callee : Body := {
  numLocals := 1
  argCount := 0
  features := [1]
  blocks := [
    { isCleanup := false
      stmts := [.assign 0 (.featureAdd 1 (.constVal (.int 20)) (.constVal (.int 22)))]
      term := .return_ }
  ]
}

/-- Baseline caller (`features = []`) that calls `ce3Avx2Callee` on a runtime CPU `[1]`. -/
def ce3BaselineCaller : Body := {
  numLocals := 2
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1]
      term := .call 0 [] 1 (some 1) .continue_ },
    { isCleanup := false
      stmts := [.assign 0 (.use (.move 1))]
      term := .return_ }
  ]
}

/-- **Sharpness Counterexample 3 (`ce3_cross_feature_mir_inline_violates_feature_gate`)**:
    Calling an `#[target_feature]` callee (`features = [1]`) from a baseline caller
    (`features = []`) on a CPU supporting `[1]` succeeds interprocedurally (`.returned 42 []`),
    and `inlineCallSite` rightly rejects the cross-feature splice (`= none`).
    Forcing the MIR splice without `callee.features == caller.features` places the
    feature-gated operation inside a caller body with `features = []`, triggering
    `.fault .illegalInstruction` (`¬ ExecBody ... (.returned 42 [])`). -/
theorem ce3_cross_feature_mir_inline_violates_feature_gate :
    inlineCallSite [ce3Avx2Callee] ce3BaselineCaller 0 = none ∧
    ∃ buggySpliced,
      buggyInlineIgnoreFeatures [ce3Avx2Callee] ce3BaselineCaller 0 = some buggySpliced ∧
      ExecBody [ce3Avx2Callee] ce3BaselineCaller [1] [] (.returned (.int 42) []) ∧
      ExecBody [ce3Avx2Callee] buggySpliced [1] [] (.fault .illegalInstruction) ∧
      ¬ ExecBody [ce3Avx2Callee] buggySpliced [1] [] (.returned (.int 42) []) := by
  refine ⟨rfl, _, rfl, ?_, ?_, ?_⟩
  · -- Interprocedural call succeeds on CPU `[1]`
    have hce : ExecBlock [ce3Avx2Callee] [1] ce3Avx2Callee 0 [.liveUninit] [] (.returned (.int 42) []) :=
      .returnOk rfl rfl rfl rfl rfl
    exact .callReturnOk rfl rfl rfl rfl rfl rfl rfl rfl hce rfl
      (.returnOk rfl rfl rfl rfl rfl)
  · -- Buggy cross-feature splice faults with `.illegalInstruction`
    exact .goto rfl rfl rfl
      (.stmtFault rfl rfl)
  · -- ¬ ExecBody buggySpliced (.returned 42 [])
    intro h0
    unfold ExecBody at h0
    dsimp [allFeaturesPresent, initFrameLocals, replicateSlot] at h0
    have h1 := execBlock_step_once h0
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, writeLocal, buildCallPrelude, buildArgBindings,
      resetDeadRange, integrateBlock, integrateTerm, mkReturnTrampoline] at h1
    have h2 := execBlock_step_once h1
    dsimp [BlockStepSpliced, TermStepSpliced, getAt, evalStmts, evalStmt, setAt,
      evalRvalue, evalOperand, memNat, writeLocal, shiftStmt, shiftRvalue, shiftOperand,
      integrateBlock, integrateTerm, mkReturnTrampoline] at h2
    cases h2


/-! ### Counterexample 4: Pre-Call `Rvalue::Ref` on Uninhabited `!is_stable_offset()` Return Place -/

/-- Diverging callee (`fn diverge_unwind() -> Infallible { panic!() }`): unwinds without returning. -/
def ce4DivergeUnwindCallee : Body := {
  numLocals := 1
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := []
      term := .unwindStart .continue_ }
  ]
}

/-- Caller invoking `*dangling_infallible_ptr = diverge_unwind()` with `unwind = .cleanup 1`:
    before inlining, the return place is never materialized because `diverge_unwind` unwinds. -/
def ce4UninhabitedDestCaller : Body := {
  numLocals := 3
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1, .assign 1 (.use (.constVal (.int 0))), .storageLive 2]
      term := .call 0 [] 2 none (.cleanup 1) },
    { isCleanup := true
      stmts := [.dropGuard 1 77, .storageDead 1]
      term := .unwindResume }
  ]
}

/-- `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) `!destination.is_stable_offset()`
    lowering (`_tmp = &mut (*_1)` where `*_1 : Infallible` is uninhabited), which executes
    `Stmt.validateDestRef false` *before* entering the callee and triggers immediate UB
    (`constructing invalid value of type &mut core::convert::Infallible`), whereas upstream `main`
    (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) lowers `Rvalue::RawPtr(RawPtrKind::Mut, destination)`
    (modeled by `inlineCallSite`, no eager reference validity assertion). -/
def ce4BuggyEagerMutRefSpliced : Body := {
  numLocals := 4
  argCount := 0
  features := []
  blocks := [
    { isCleanup := false
      stmts := [.storageLive 1, .assign 1 (.use (.constVal (.int 0))), .storageLive 2,
                .validateDestRef false, .storageLive 3]
      term := .goto 2 },
    { isCleanup := true
      stmts := [.dropGuard 1 77, .storageDead 1]
      term := .unwindResume },
    { isCleanup := false
      stmts := []
      term := .unwindStart (.cleanup 1) }
  ]
}

theorem ce4_unstable_offset_dest_ref_ub_vs_rawptr_sound :
    ∃ rawPtrSpliced,
      inlineCallSite [ce4DivergeUnwindCallee] ce4UninhabitedDestCaller 0 = some rawPtrSpliced ∧
      ExecBody [ce4DivergeUnwindCallee] ce4UninhabitedDestCaller [] [] (.unwound [77]) ∧
      ExecBody [ce4DivergeUnwindCallee] rawPtrSpliced [] [] (.unwound [77]) ∧
      ExecBody [ce4DivergeUnwindCallee] ce4BuggyEagerMutRefSpliced [] [] (.fault .undefined) ∧
      ¬ ExecBody [ce4DivergeUnwindCallee] ce4BuggyEagerMutRefSpliced [] [] (.unwound [77]) := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · have hce : ExecBlock [ce4DivergeUnwindCallee] [] ce4DivergeUnwindCallee 0 [.liveUninit] [] (.unwound []) :=
      .unwindStartContinue rfl rfl rfl
    exact .callUnwindCleanup rfl rfl rfl rfl rfl rfl rfl rfl hce
      (.unwindResumeOk rfl rfl rfl rfl)
  · exact .goto rfl rfl rfl
      (.unwindStartCleanup rfl rfl rfl
        (.unwindResumeOk rfl rfl rfl rfl))
  · exact .stmtFault rfl rfl
  · intro h0
    unfold ExecBody at h0
    dsimp [allFeaturesPresent, initFrameLocals, replicateSlot] at h0
    have h1 := execBlock_step_once h0
    dsimp [BlockStepSpliced, getAt, evalStmts, evalStmt, setAt, evalRvalue,
      evalOperand, writeLocal, ce4BuggyEagerMutRefSpliced] at h1
    cases h1

end MirInliningAndCleanupSplicing

#print axioms MirInliningAndCleanupSplicing.inlineCallSite_bisimulation
#print axioms MirInliningAndCleanupSplicing.inlineChain_intra_reduction
#print axioms MirInliningAndCleanupSplicing.three_frame_lifo_cleanup_verified
#print axioms MirInliningAndCleanupSplicing.ce1_unshifted_local_collision_corrupts_caller_frame
#print axioms MirInliningAndCleanupSplicing.ce2_missing_unwind_resume_to_cleanup_splice_skips_caller_drop
#print axioms MirInliningAndCleanupSplicing.ce3_cross_feature_mir_inline_violates_feature_gate
#print axioms MirInliningAndCleanupSplicing.ce4_unstable_offset_dest_ref_ub_vs_rawptr_sound
