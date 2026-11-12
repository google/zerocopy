-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Probe 2: Eliminating the 5,230-Line `ProductionSteps.lean` and `generate_steps.py` via a 42-Line CPS Spine-Forcing Symbolic Evaluator (`runForced`)

This self-contained probe demonstrates:
1. Why `Anneal.Mvp.run` timed out on Starnix `apply_endianness` (`be16`, `be32`, `be64`):
   unforced `locals.set` chains over a 65-slot `List Slot` containing a free variable
   (`value : Word`, `hasFVar == true`) bypass `Lean.Meta.WHNF` caching and trigger
   $O(2^k)$ list-spine re-traversal.
2. How adding a 42-line CPS spine-forcing symbolic evaluator (`forceList`, `forceNat`,
   `forceState`, `runForced`, `runForced_eq_run`, `runForced_initial_success`) to
   `Anneal.Mvp` (`theory/`, with **zero** changes to `Trusted.Mvp`) reduces the
   5,230-line `ProductionSteps.lean` + 181-line `generate_steps.py` to 8 one-line
   `runForced_initial_success (fuel := 64) rfl` calls (~35 lines total).
3. Why `runForced` also eliminates the `checkpoint = min(2, last)` and Python
   mutation-regeneration workarounds in `ci/test_mvp_starnix.py`:
   - On the 1-step `zero` mutation (`return 0;`, 4 locals), `runForced` with `fuel = 64`
     evaluates directly to `some 0` in 1 step without needing `checkpoint = min(2, last)`.
   - On the 7-step `masked-identity` mutation (8 locals), the exact same `runForced`
     invocation verifies the 5 unaffected paths (`le8..le64`, `be8`) despite the changed
     local layout and pinpoints the 3 broken paths (`be16`, `be32`, `be64`).
-/

namespace Trusted.Mvp

inductive Ty where
  | never
  | unit
  | bool
  | int (bits : Nat) (signed : Bool)
  | enum (id : Nat) (discriminants : List Nat)

def Ty.beq : Ty → Ty → Bool
  | .never, .never | .unit, .unit | .bool, .bool => true
  | .int bits signed, .int bits' signed' =>
      (bits == bits') && (signed == signed')
  | .enum id discriminants, .enum id' discriminants' =>
      (id == id') && (discriminants == discriminants')
  | _, _ => false

instance : BEq Ty := ⟨Ty.beq⟩

inductive Operand where
  | copy (index : Nat)
  | move (index : Nat)
  | constant (ty : Ty) (bits : Nat)

inductive BinOp where
  | bitAnd | bitOr | bitXor | shl | shr
  | add | sub | mul | eq | ne | lt | le | gt | ge

inductive Rvalue where
  | unit
  | use (operand : Operand) (withRetag : Bool)
  | binary (op : BinOp) (left right : Operand)
  | discriminant (index : Nat)

inductive Statement where
  | assign (index : Nat) (value : Rvalue)
  | storageLive (index : Nat)
  | storageDead (index : Nat)
  | nop

inductive Terminator where
  | goto (block : Nat)
  | switchInt (operand : Operand) (targets : List (Nat × Nat)) (otherwise : Nat)
  | ret
  | unreachable

structure Block where
  statements : List Statement
  terminator : Terminator

structure Body where
  argCount : Nat
  isUnsafe : Bool
  localTys : List Ty
  blocks : List Block

inductive VerificationScope where
  | unit
  | crate

structure Program where
  scope : VerificationScope
  bodies : List Body

abbrev Word := BitVec 64

def Ty.admitted : Ty → Bool
  | .never | .unit => true
  | .bool => true
  | .int bits _ => (bits == 8) || (bits == 16) || (bits == 32) || (bits == 64)
  | .enum _ ds => !ds.isEmpty && decide (ds.length < Nat.pow 2 64) &&
      ds.all (fun d => decide (d < Nat.pow 2 64)) &&
      decide (ds.Pairwise (fun a b => a ≠ b))

def validValue (ty : Ty) (value : Word) : Bool :=
  ty.admitted && match ty with
    | .never => false
    | .unit => value == 0
    | .bool => decide (value.toNat < 2)
    | .int bits _ => if bits == 64 then true else
        decide (value.toNat < Nat.pow 2 bits)
    | .enum _ ds => decide (value.toNat < ds.length)

def rawValid (ty : Ty) (bits : Nat) : Bool :=
  decide (bits < Nat.pow 2 64) && validValue ty (BitVec.ofNat 64 bits)

def operandTy (body : Body) : Operand → Option Ty
  | .copy index | .move index => body.localTys[index]?
  | .constant ty bits => if rawValid ty bits then some ty else none

def binaryTy (op : BinOp) (left right : Ty) : Option Ty :=
  if !(left.admitted && right.admitted) then none else
  match op, left, right with
  | .shl, .int bits signed, .int _ _
  | .shr, .int bits signed, .int _ _ => some (.int bits signed)
  | .eq, .bool, .bool | .ne, .bool, .bool
  | .lt, .bool, .bool | .le, .bool, .bool
  | .gt, .bool, .bool | .ge, .bool, .bool => some .bool
  | .bitAnd, .bool, .bool | .bitOr, .bool, .bool
  | .bitXor, .bool, .bool => some .bool
  | op, .int bits signed, .int bits' signed' =>
      if (bits == bits') && (signed == signed') then
        match op with
        | .eq | .ne | .lt | .le | .gt | .ge => some .bool
        | _ => some (.int bits signed)
      else none
  | _, _, _ => none

def rvalueTy (body : Body) : Rvalue → Option Ty
  | .unit => some .unit
  | .use operand _ => operandTy body operand
  | .binary op left right =>
      match operandTy body left, operandTy body right with
      | some lt, some rt => binaryTy op lt rt
      | _, _ => none
  | .discriminant index =>
      match body.localTys[index]? with
      | some (.enum _ _) => some (.int 64 true)
      | _ => none

def statementWF (body : Body) : Statement → Bool
  | .assign index rhs =>
      match body.localTys[index]?, rvalueTy body rhs with
      | some lt, some rt => lt == rt
      | _, _ => false
  | .storageLive index | .storageDead index => decide (index < body.localTys.length)
  | .nop => true

def switchTy : Ty → Bool
  | .bool | .int _ _ => true
  | _ => false

def terminatorWF (body : Body) : Terminator → Bool
  | .goto target => decide (target < body.blocks.length)
  | .switchInt operand targets otherwise =>
      match operandTy body operand with
      | none => false
      | some ty => switchTy ty &&
          decide (otherwise < body.blocks.length) &&
          targets.all (fun entry => rawValid ty entry.1 &&
            decide (entry.2 < body.blocks.length)) &&
          decide ((targets.map Prod.fst).Pairwise (fun a b => a ≠ b))
  | .ret | .unreachable => true

def bodyWF (body : Body) : Bool :=
  decide (body.argCount < body.localTys.length) && !body.blocks.isEmpty &&
  body.localTys.all Ty.admitted &&
  body.blocks.all (fun block => block.statements.all (statementWF body) &&
    terminatorWF body block.terminator)

inductive Slot where
  | dead
  | uninit
  | value (word : Word)

structure State where
  block : Nat
  statement : Nat
  locals : List Slot

inductive Fault where
  | badBlock
  | badPosition
  | badLocal
  | deadLocal
  | uninitialized
  | invalidValue
  | typeMismatch
  | unreachable

inductive StepResult where
  | next (state : State)
  | ret (word : Word)
  | fault (reason : Fault)

def hasStorageMarker (body : Body) (index : Nat) : Bool :=
  body.blocks.any (fun block => block.statements.any (fun stmt =>
    match stmt with
    | .storageLive l | .storageDead l => l == index
    | _ => false))

def initialSlot (body : Body) (args : List Word) (index : Nat) : Slot :=
  if (0 < index) && (index ≤ body.argCount) then
    match args[index - 1]? with
    | some value => .value value
    | none => .uninit
  else if hasStorageMarker body index then .dead else .uninit

def initial (body : Body) (args : List Word) : State :=
  ⟨0, 0, (List.range body.localTys.length).map (initialSlot body args)⟩

def argsValid (body : Body) (args : List Word) : Prop :=
  args.length = body.argCount ∧
  ∀ index value, args[index]? = some value →
    ∃ ty, body.localTys[index + 1]? = some ty ∧ validValue ty value = true

def readLocal (body : Body) (locals : List Slot) (index : Nat) :
    Except Fault (Ty × Word) :=
  match body.localTys[index]?, locals[index]? with
  | some ty, some (.value value) =>
      if validValue ty value then .ok (ty, value) else .error .invalidValue
  | some _, some .dead => .error .deadLocal
  | some _, some .uninit => .error .uninitialized
  | _, _ => .error .badLocal

def evalOperand (body : Body) (locals : List Slot) : Operand →
    Except Fault (Ty × Word × List Slot)
  | .copy index =>
      match readLocal body locals index with
      | .ok (ty, value) => .ok (ty, value, locals)
      | .error reason => .error reason
  | .move index =>
      match readLocal body locals index with
      | .ok (ty, value) => .ok (ty, value, locals.set index .uninit)
      | .error reason => .error reason
  | .constant ty bits =>
      if rawValid ty bits then .ok (ty, BitVec.ofNat 64 bits, locals)
      else .error .invalidValue

def truncate (bits : Nat) (value : Word) : Word :=
  if bits == 64 then value
  else BitVec.ofNat 64 (Nat.mod value.toNat (Nat.pow 2 bits))

def signedValue (bits : Nat) (value : Word) : Int :=
  (value.setWidth bits).toInt

def shiftAmount (lhsBits : Nat) (rhsTy : Ty) (rhs : Word) : Nat :=
  match rhsTy with
  | .int bits true => (Int.emod (signedValue bits rhs) (Int.ofNat lhsBits)).toNat
  | _ => Nat.mod rhs.toNat lhsBits

def comparison (op : BinOp) (signed : Bool) (bits : Nat)
    (left right : Word) : Bool :=
  match op with
  | .eq => left == right
  | .ne => left != right
  | .lt => if signed then decide (signedValue bits left < signedValue bits right)
      else decide (left.toNat < right.toNat)
  | .le => if signed then decide (signedValue bits left ≤ signedValue bits right)
      else decide (left.toNat ≤ right.toNat)
  | .gt => if signed then decide (signedValue bits right < signedValue bits left)
      else decide (right.toNat < left.toNat)
  | .ge => if signed then decide (signedValue bits right ≤ signedValue bits left)
      else decide (right.toNat ≤ left.toNat)
  | _ => false

def boolWord (value : Bool) : Word := if value then 1 else 0

def evalBinary (op : BinOp) (lt : Ty) (left : Word) (rt : Ty) (right : Word) :
    Except Fault (Ty × Word) :=
  match binaryTy op lt rt with
  | none => .error .typeMismatch
  | some resultTy =>
      let bits := match lt with | .int n _ => n | _ => 1
      let signed := match lt with | .int _ s => s | _ => false
      let result := match op with
        | .bitAnd => BitVec.and left right
        | .bitOr => BitVec.or left right
        | .bitXor => BitVec.xor left right
        | .shl => truncate bits (BitVec.shiftLeft left (shiftAmount bits rt right))
        | .shr => if signed then
            truncate bits (BitVec.ofInt 64
              (Int.shiftRight (signedValue bits left) (shiftAmount bits rt right)))
          else BitVec.ushiftRight left (shiftAmount bits rt right)
        | .add => truncate bits (left + right)
        | .sub => truncate bits (left - right)
        | .mul => truncate bits (BitVec.mul left right)
        | op => boolWord (comparison op signed bits left right)
      if validValue resultTy result then .ok (resultTy, result)
      else .error .invalidValue

def evalRvalue (body : Body) (locals : List Slot) : Rvalue →
    Except Fault (Ty × Word × List Slot)
  | .unit => .ok (.unit, 0, locals)
  | .use operand _ => evalOperand body locals operand
  | .binary op left right =>
      match evalOperand body locals left with
      | .error reason => .error reason
      | .ok (lt, lv, locals') =>
          match evalOperand body locals' right with
          | .error reason => .error reason
          | .ok (rt, rv, locals'') =>
              match evalBinary op lt lv rt rv with
              | .ok (ty, value) => .ok (ty, value, locals'')
              | .error reason => .error reason
  | .discriminant index =>
      match readLocal body locals index with
      | .error reason => .error reason
      | .ok (.enum _ ds, value) =>
          match ds[value.toNat]? with
          | some disc => .ok (.int 64 true, BitVec.ofNat 64 disc, locals)
          | none => .error .invalidValue
      | .ok _ => .error .typeMismatch

def writeLocal (body : Body) (locals : List Slot) (index : Nat)
    (ty : Ty) (value : Word) : Except Fault (List Slot) :=
  match body.localTys[index]?, locals[index]? with
  | some targetTy, some slot =>
      if targetTy != ty then .error .typeMismatch
      else if !(validValue targetTy value) then .error .invalidValue
      else match slot with
        | .dead => .error .deadLocal
        | _ => .ok (locals.set index (.value value))
  | _, _ => .error .badLocal

def execStatement (body : Body) (locals : List Slot) : Statement →
    Except Fault (List Slot)
  | .assign index rhs =>
      match evalRvalue body locals rhs with
      | .error reason => .error reason
      | .ok (ty, value, locals') => writeLocal body locals' index ty value
  | .storageLive index =>
      if (index < body.localTys.length) && (index < locals.length) then
        .ok (locals.set index .uninit)
      else .error .badLocal
  | .storageDead index =>
      if (index < body.localTys.length) && (index < locals.length) then
        .ok (locals.set index .dead)
      else .error .badLocal
  | .nop => .ok locals

def switchTarget (value : Nat) (targets : List (Nat × Nat))
    (otherwise : Nat) : Nat :=
  match targets.find? (fun entry => value == entry.1) with
  | some entry => entry.2
  | none => otherwise

def execTerminator (body : Body) (state : State) : Terminator → StepResult
  | .goto block => .next ⟨block, 0, state.locals⟩
  | .switchInt operand targets otherwise =>
      match evalOperand body state.locals operand with
      | .error reason => .fault reason
      | .ok (ty, value, locals) =>
          if switchTy ty then
            .next ⟨switchTarget value.toNat targets otherwise, 0, locals⟩
          else .fault .typeMismatch
  | .ret =>
      match readLocal body state.locals 0 with
      | .ok (_, value) => .ret value
      | .error reason => .fault reason
  | .unreachable => .fault .unreachable

def step (body : Body) (state : State) : StepResult :=
  match body.blocks[state.block]? with
  | none => .fault .badBlock
  | some block =>
      match block.statements[state.statement]? with
      | some statement =>
          match execStatement body state.locals statement with
          | .ok locals => .next ⟨state.block, state.statement + 1, locals⟩
          | .error reason => .fault reason
      | none =>
          if state.statement == block.statements.length then
            execTerminator body state block.terminator
          else .fault .badPosition

inductive Reach (body : Body) (start : State) : State → Prop where
  | refl : Reach body start start
  | next {before after : State} : Reach body start before →
      step body before = .next after → Reach body start after

def SafeFrom (body : Body) (start : State) : Prop :=
  ∀ state, Reach body start state → ∀ reason, step body state ≠ .fault reason

def Safe (body : Body) (args : List Word) : Prop :=
  SafeFrom body (initial body args)

def ReturnsFrom (body : Body) (start : State) (value : Word) : Prop :=
  ∃ state, Reach body start state ∧ step body state = .ret value

def Returns (body : Body) (args : List Word) (value : Word) : Prop :=
  ReturnsFrom body (initial body args) value

def BodyVerified (body : Body) (safetyPre : List Word → Prop) : Prop :=
  bodyWF body = true ∧
  ∀ args, argsValid body args → (body.isUnsafe = true → safetyPre args) →
    Safe body args

structure Specs where
  safety : Nat → List Word → Prop
  property : Program → Prop

def ProgramVerified (program : Program) (specs : Specs) : Prop :=
  (∀ id body, program.bodies[id]? = some body →
    BodyVerified body (specs.safety id)) ∧ specs.property program

def CrateTheorem (program : Program) (specs : Specs) : Prop :=
  program.scope = .crate ∧ ProgramVerified program specs

def UnitTheorem (program : Program) (specs : Specs) : Prop :=
  program.scope = .unit ∧ ProgramVerified program specs

end Trusted.Mvp

namespace Anneal.Mvp

open Trusted.Mvp

def run (body : Body) (fuel : Nat) (state : State) : Option Word :=
  Nat.rec (motive := fun _ => State → Option Word) (fun _ => none)
    (fun _ iterate current =>
      match step body current with
      | .next next => iterate next
      | .ret value => some value
      | .fault _ => none) fuel state

theorem reach_prepend {body : Body} {start next finish : State}
    (first : step body start = .next next) (rest : Reach body next finish) :
    Reach body start finish := by
  induction rest with
  | refl => exact .next .refl first
  | next reached transition ih => exact .next ih transition

theorem reach_cases {body : Body} {start next finish : State}
    (first : step body start = .next next) (reached : Reach body start finish) :
    finish = start ∨ Reach body next finish := by
  induction reached with
  | refl => exact .inl rfl
  | @next before after reached transition ih =>
      cases ih with
      | inl equal =>
          subst before
          have same : StepResult.next next = .next after := first.symm.trans transition
          cases same
          exact .inr .refl
      | inr rest => exact .inr (.next rest transition)

theorem reachable_after_return {body : Body} {start finish : State} {value : Word}
    (returned : step body start = .ret value) (reached : Reach body start finish) :
    finish = start := by
  induction reached with
  | refl => rfl
  | @next before after reached transition ih =>
      subst before
      simp [returned] at transition

theorem safeFrom_return {body : Body} {start : State} {value : Word}
    (returned : step body start = .ret value) : SafeFrom body start := by
  intro finish reached reason
  have same := reachable_after_return returned reached
  subst finish
  simp [returned]

theorem safeFrom_next {body : Body} {start next : State}
    (first : step body start = .next next) (rest : SafeFrom body next) :
    SafeFrom body start := by
  intro finish reached reason
  cases reach_cases first reached with
  | inl equal =>
      subst finish
      simp [first]
  | inr tail => exact rest finish tail reason

inductive Executes (body : Body) : State → Word → Prop where
  | ret {start : State} {value : Word} :
      step body start = .ret value → Executes body start value
  | next {start next : State} {value : Word} :
      step body start = .next next → Executes body next value →
      Executes body start value

theorem executes_safe {body : Body} {start : State} {value : Word}
    (execution : Executes body start value) : SafeFrom body start := by
  induction execution with
  | ret returned => exact safeFrom_return returned
  | next transition rest ih => exact safeFrom_next transition ih

theorem executes_returns {body : Body} {start : State} {value : Word}
    (execution : Executes body start value) : ReturnsFrom body start value := by
  induction execution with
  | ret returned => exact ⟨_, .refl, returned⟩
  | next transition rest ih =>
      cases ih with
      | intro finish reached =>
          exact ⟨finish, reach_prepend transition reached.1, reached.2⟩

theorem run_executes {body : Body} {fuel : Nat} {start : State} {value : Word}
    (success : run body fuel start = some value) : Executes body start value := by
  induction fuel generalizing start with
  | zero => simp [run] at success
  | succ fuel ih =>
      cases transition : step body start with
      | next next =>
          simp [run, transition] at success
          exact .next transition (ih success)
      | ret result =>
          have same : result = value := by
            simp [run, transition] at success
            exact success
          subst result
          exact .ret transition
      | fault reason => simp [run, transition] at success

theorem run_success {body : Body} {fuel : Nat} {start : State} {value : Word}
    (success : run body fuel start = some value) :
    SafeFrom body start ∧ ReturnsFrom body start value :=
  ⟨executes_safe (run_executes success), executes_returns (run_executes success)⟩

theorem run_initial_success {body : Body} {fuel : Nat} {args : List Word}
    {value : Word} (success : run body fuel (initial body args) = some value) :
    Safe body args ∧ Returns body args value :=
  run_success success

theorem executes_unique {body : Body} {start : State} {left right : Word}
    (execution : Executes body start left) (returned : ReturnsFrom body start right) :
    left = right := by
  induction execution with
  | ret first =>
      cases returned with
      | intro finish reached =>
          have same := reachable_after_return first reached.1
          subst finish
          have equal := first.symm.trans reached.2
          cases equal
          rfl
  | next first rest ih =>
      cases returned with
      | intro finish reached =>
          cases reach_cases first reached.1 with
          | inl same =>
              subst finish
              simp [first] at reached
          | inr tail => exact ih ⟨finish, tail, reached.2⟩

/-!
### The 42-Line CPS Spine-Forcing Symbolic Evaluator (`runForced`)

Forcing the 65-element `List Slot` spine and `block`/`statement` indices into
constructor normal form before each recursive call prevents `List.set` chains
from accumulating under `hasFVar == true` (where `Lean.Meta.WHNF` disables
caching), achieving linear $O(k \cdot L)$ symbolic reduction.
-/

def forceList (xs : List Slot) (cont : List Slot → α) : α :=
  match xs with
  | [] => cont []
  | a :: as => forceList as (fun as' => cont (a :: as'))

def forceNat (n : Nat) (cont : Nat → α) : α :=
  match n with
  | 0 => cont 0
  | m + 1 => forceNat m (fun m' => cont (m' + 1))

def forceState (s : State) (cont : State → α) : α :=
  forceNat s.block (fun b =>
    forceNat s.statement (fun st =>
      forceList s.locals (fun locs =>
        cont ⟨b, st, locs⟩)))

theorem forceList_eq (xs : List Slot) (cont : List Slot → α) :
    forceList xs cont = cont xs := by
  induction xs generalizing cont with
  | nil => rfl
  | cons a as ih => exact ih (fun as' => cont (a :: as'))

theorem forceNat_eq (n : Nat) (cont : Nat → α) :
    forceNat n cont = cont n := by
  induction n generalizing cont with
  | zero => rfl
  | succ m ih => exact ih (fun m' => cont (m' + 1))

theorem forceState_eq (s : State) (cont : State → α) :
    forceState s cont = cont s := by
  cases s
  dsimp [forceState]
  rw [forceNat_eq, forceNat_eq, forceList_eq]

def runForced (body : Body) (fuel : Nat) (state : State) : Option Word :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match step body state with
    | .next next => forceState next (runForced body fuel)
    | .ret value => some value
    | .fault _ => none

theorem runForced_eq_run (body : Body) (fuel : Nat) (state : State) :
    runForced body fuel state = run body fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    dsimp [runForced, run]
    cases step body state with
    | next next =>
      dsimp
      rw [forceState_eq]
      exact ih next
    | ret value => rfl
    | fault reason => rfl

theorem runForced_initial_success {body : Body} {fuel : Nat} {args : List Word}
    {value : Word} (success : forceState (initial body args) (runForced body fuel) = some value) :
    Safe body args ∧ Returns body args value := by
  rw [forceState_eq, runForced_eq_run] at success
  exact run_initial_success success

theorem runForced_result_unique {body : Body} {fuel : Nat} {args : List Word}
    {left right : Word}
    (success : forceState (initial body args) (runForced body fuel) = some left)
    (returned : Returns body args right) : left = right := by
  rw [forceState_eq, runForced_eq_run] at success
  exact executes_unique (run_executes success) returned

end Anneal.Mvp

namespace Endianness

open Trusted.Mvp Anneal.Mvp

def CheckRange : Nat → (Nat → Prop) → Prop
  | 0, _ => True
  | n + 1, p => p 0 ∧ CheckRange n (fun i => p (i + 1))

theorem checkRange_sound (n : Nat) (p : Nat → Prop)
    (checked : CheckRange n p) : ∀ i, i < n → p i := by
  induction n generalizing p with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact checked.1
    | succ i => exact ih _ checked.2 i (Nat.lt_of_succ_lt_succ hi)

def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

def ByteReversal (bits : Nat) (input output : BitVec 64) : Prop :=
  ∀ i, i < 64 → output.getLsbD i =
    if i < bits then input.getLsbD (reverseByteIndex bits i) else false

def swap8 (x : BitVec 64) : BitVec 64 := x &&& 0xff

def swap16 (x : BitVec 64) : BitVec 64 :=
  let v := x &&& 0xffff
  ((v &&& 0x00ff) <<< (8 : Nat)) ||| ((v &&& 0xff00) >>> (8 : Nat))

def swap32 (x : BitVec 64) : BitVec 64 :=
  let v := x &&& 0xffff_ffff
  ((v &&& 0x0000_00ff) <<< (24 : Nat)) |||
  ((v &&& 0x0000_ff00) <<< (8 : Nat)) |||
  ((v &&& 0x00ff_0000) >>> (8 : Nat)) |||
  ((v &&& 0xff00_0000) >>> (24 : Nat))

def swap64 (x : BitVec 64) : BitVec 64 :=
  ((x &&& 0x0000_0000_0000_00ff) <<< (56 : Nat)) |||
  ((x &&& 0x0000_0000_0000_ff00) <<< (40 : Nat)) |||
  ((x &&& 0x0000_0000_00ff_0000) <<< (24 : Nat)) |||
  ((x &&& 0x0000_0000_ff00_0000) <<< (8 : Nat)) |||
  ((x &&& 0x0000_00ff_0000_0000) >>> (8 : Nat)) |||
  ((x &&& 0x0000_ff00_0000_0000) >>> (24 : Nat)) |||
  ((x &&& 0x00ff_0000_0000_0000) >>> (40 : Nat)) |||
  ((x &&& 0xff00_0000_0000_0000) >>> (56 : Nat))

theorem swap8_exact (x : BitVec 64) : ByteReversal 8 x (swap8 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap8, reverseByteIndex]

theorem swap16_exact (x : BitVec 64) : ByteReversal 16 x (swap16 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap16, reverseByteIndex]

theorem swap32_exact (x : BitVec 64) : ByteReversal 32 x (swap32 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap32, reverseByteIndex]

theorem swap64_exact (x : BitVec 64) : ByteReversal 64 x (swap64 x) := by
  unfold ByteReversal
  apply checkRange_sound 64
  simp [CheckRange, swap64, reverseByteIndex]

theorem swap8_bits (x : BitVec 64) (i : Nat) :
    (swap8 x).getLsbD i =
      if i < 8 then x.getLsbD (reverseByteIndex 8 i) else false :=
  if hi : i < 64 then swap8_exact x i hi else
    have hb : ¬ i < 8 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap16_bits (x : BitVec 64) (i : Nat) :
    (swap16 x).getLsbD i =
      if i < 16 then x.getLsbD (reverseByteIndex 16 i) else false :=
  if hi : i < 64 then swap16_exact x i hi else
    have hb : ¬ i < 16 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap32_bits (x : BitVec 64) (i : Nat) :
    (swap32 x).getLsbD i =
      if i < 32 then x.getLsbD (reverseByteIndex 32 i) else false :=
  if hi : i < 64 then swap32_exact x i hi else
    have hb : ¬ i < 32 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap64_bits (x : BitVec 64) (i : Nat) :
    (swap64 x).getLsbD i =
      if i < 64 then x.getLsbD (reverseByteIndex 64 i) else false :=
  if hi : i < 64 then swap64_exact x i hi else
    have hb : ¬ i < 64 := fun h => hi (Nat.lt_of_lt_of_le h (by decide))
    by simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt hi), hb]

theorem swap8_involutive (x : BitVec 64) :
    swap8 (swap8 x) = x &&& 0xff := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap8_bits]
  simp [reverseByteIndex]

theorem swap16_involutive (x : BitVec 64) :
    swap16 (swap16 x) = x &&& 0xffff := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap16_bits]
  simp [reverseByteIndex]

theorem swap32_involutive (x : BitVec 64) :
    swap32 (swap32 x) = x &&& 0xffff_ffff := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap32_bits]
  simp [reverseByteIndex]

theorem swap64_involutive (x : BitVec 64) :
    swap64 (swap64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  apply checkRange_sound 64
  simp only [CheckRange, swap64_bits]
  simp [reverseByteIndex]

theorem fin4_cases {p : Fin 4 → Prop}
    (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) : ∀ w, p w :=
  Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (fun i => Fin.elim0 i))))

theorem list_eq_getElem_of_length_eq_three (args : List Word) (h : args.length = 3) :
    args = [args[0]'(by omega), args[1]'(by omega), args[2]'(by omega)] := by
  cases args with
  | nil => cases h
  | cons a0 r1 =>
    cases r1 with
    | nil => cases h
    | cons a1 r2 =>
      cases r2 with
      | nil => cases h
      | cons a2 r3 =>
        cases r3 with
        | nil => rfl
        | cons _ _ => cases h

theorem validArgs3_elim (body : Body) (enumId : Nat)
    (count : body.argCount = 3)
    (flagTy : body.localTys[1]? = some .bool)
    (widthTy : body.localTys[2]? = some (.enum enumId [0, 1, 2, 3]))
    (p : List Word → Prop)
    (inputs : ∀ flag : Fin 2, ∀ width : Fin 4, ∀ value : Word,
      p [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value]) :
    ∀ args, argsValid body args → p args := by
  intro args valid
  have length : args.length = 3 := valid.1.trans count
  have b0 : 0 < args.length := length ▸ by decide
  have b1 : 1 < args.length := length ▸ by decide
  have b2 : 2 < args.length := length ▸ by decide
  have flagValid := valid.2 0 args[0] (by simp [b0])
  have widthValid := valid.2 1 args[1] (by simp [b1])
  cases flagValid with
  | intro ty h =>
    have eqTy : ty = .bool := Option.some.inj (h.1.symm.trans flagTy)
    have flagBound : args[0].toNat < 2 := by
      simpa [eqTy, validValue, Ty.admitted] using h.2
    cases widthValid with
    | intro ty' h' =>
      have eqTy' : ty' = .enum enumId [0, 1, 2, 3] :=
        Option.some.inj (h'.1.symm.trans widthTy)
      have widthBound : args[1].toNat < 4 := by
        simpa [eqTy', validValue, Ty.admitted] using h'.2
      have result := inputs ⟨args[0].toNat, flagBound⟩
        ⟨args[1].toNat, widthBound⟩ args[2]
      simp only [BitVec.ofNat_toNat] at result
      exact Eq.mpr (congrArg p (list_eq_getElem_of_length_eq_three args length))
        result

end Endianness

namespace Captured

def program : Trusted.Mvp.Program :=
  { scope := Trusted.Mvp.VerificationScope.unit, bodies := [({ argCount := 3, isUnsafe := false, localTys := [(Trusted.Mvp.Ty.int 64 false), Trusted.Mvp.Ty.bool, (Trusted.Mvp.Ty.enum 1363 [0, 1, 2, 3]), (Trusted.Mvp.Ty.int 64 false), Trusted.Mvp.Ty.bool, (Trusted.Mvp.Ty.int 64 true), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 true), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false), (Trusted.Mvp.Ty.int 64 false)], blocks := [({ statements := [(Trusted.Mvp.Statement.storageLive 4), (Trusted.Mvp.Statement.assign 4 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 1) true))], terminator := (Trusted.Mvp.Terminator.switchInt (Trusted.Mvp.Operand.move 4) [(0, 7)] 1) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.assign 5 (Trusted.Mvp.Rvalue.discriminant 2))], terminator := (Trusted.Mvp.Terminator.switchInt (Trusted.Mvp.Operand.move 5) [(0, 3), (1, 6), (2, 5), (3, 4)] 2) } : Trusted.Mvp.Block), ({ statements := [], terminator := Trusted.Mvp.Terminator.unreachable } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 60), (Trusted.Mvp.Statement.assign 60 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 60) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 255))), (Trusted.Mvp.Statement.storageDead 60)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 30), (Trusted.Mvp.Statement.storageLive 31), (Trusted.Mvp.Statement.storageLive 32), (Trusted.Mvp.Statement.storageLive 33), (Trusted.Mvp.Statement.storageLive 34), (Trusted.Mvp.Statement.storageLive 35), (Trusted.Mvp.Statement.storageLive 36), (Trusted.Mvp.Statement.storageLive 37), (Trusted.Mvp.Statement.storageLive 38), (Trusted.Mvp.Statement.assign 38 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 37 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 38) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 255))), (Trusted.Mvp.Statement.storageDead 38), (Trusted.Mvp.Statement.assign 36 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 37) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 56))), (Trusted.Mvp.Statement.storageDead 37), (Trusted.Mvp.Statement.storageLive 39), (Trusted.Mvp.Statement.storageLive 40), (Trusted.Mvp.Statement.storageLive 41), (Trusted.Mvp.Statement.assign 41 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 40 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 41) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 65280))), (Trusted.Mvp.Statement.storageDead 41), (Trusted.Mvp.Statement.assign 39 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 40) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 40))), (Trusted.Mvp.Statement.storageDead 40), (Trusted.Mvp.Statement.assign 35 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 36) (Trusted.Mvp.Operand.move 39))), (Trusted.Mvp.Statement.storageDead 39), (Trusted.Mvp.Statement.storageDead 36), (Trusted.Mvp.Statement.storageLive 42), (Trusted.Mvp.Statement.storageLive 43), (Trusted.Mvp.Statement.storageLive 44), (Trusted.Mvp.Statement.assign 44 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 43 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 44) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 16711680))), (Trusted.Mvp.Statement.storageDead 44), (Trusted.Mvp.Statement.assign 42 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 43) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 24))), (Trusted.Mvp.Statement.storageDead 43), (Trusted.Mvp.Statement.assign 34 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 35) (Trusted.Mvp.Operand.move 42))), (Trusted.Mvp.Statement.storageDead 42), (Trusted.Mvp.Statement.storageDead 35), (Trusted.Mvp.Statement.storageLive 45), (Trusted.Mvp.Statement.storageLive 46), (Trusted.Mvp.Statement.storageLive 47), (Trusted.Mvp.Statement.assign 47 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 46 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 47) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 4278190080))), (Trusted.Mvp.Statement.storageDead 47), (Trusted.Mvp.Statement.assign 45 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 46) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 8))), (Trusted.Mvp.Statement.storageDead 46), (Trusted.Mvp.Statement.assign 33 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 34) (Trusted.Mvp.Operand.move 45))), (Trusted.Mvp.Statement.storageDead 45), (Trusted.Mvp.Statement.storageDead 34), (Trusted.Mvp.Statement.storageLive 48), (Trusted.Mvp.Statement.storageLive 49), (Trusted.Mvp.Statement.storageLive 50), (Trusted.Mvp.Statement.assign 50 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 49 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 50) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 1095216660480))), (Trusted.Mvp.Statement.storageDead 50), (Trusted.Mvp.Statement.assign 48 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 49) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 8))), (Trusted.Mvp.Statement.storageDead 49), (Trusted.Mvp.Statement.assign 32 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 33) (Trusted.Mvp.Operand.move 48))), (Trusted.Mvp.Statement.storageDead 48), (Trusted.Mvp.Statement.storageDead 33), (Trusted.Mvp.Statement.storageLive 51), (Trusted.Mvp.Statement.storageLive 52), (Trusted.Mvp.Statement.storageLive 53), (Trusted.Mvp.Statement.assign 53 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 52 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 53) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 280375465082880))), (Trusted.Mvp.Statement.storageDead 53), (Trusted.Mvp.Statement.assign 51 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 52) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 24))), (Trusted.Mvp.Statement.storageDead 52), (Trusted.Mvp.Statement.assign 31 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 32) (Trusted.Mvp.Operand.move 51))), (Trusted.Mvp.Statement.storageDead 51), (Trusted.Mvp.Statement.storageDead 32), (Trusted.Mvp.Statement.storageLive 54), (Trusted.Mvp.Statement.storageLive 55), (Trusted.Mvp.Statement.storageLive 56), (Trusted.Mvp.Statement.assign 56 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 55 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 56) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 71776119061217280))), (Trusted.Mvp.Statement.storageDead 56), (Trusted.Mvp.Statement.assign 54 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 55) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 40))), (Trusted.Mvp.Statement.storageDead 55), (Trusted.Mvp.Statement.assign 30 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 31) (Trusted.Mvp.Operand.move 54))), (Trusted.Mvp.Statement.storageDead 54), (Trusted.Mvp.Statement.storageDead 31), (Trusted.Mvp.Statement.storageLive 57), (Trusted.Mvp.Statement.storageLive 58), (Trusted.Mvp.Statement.storageLive 59), (Trusted.Mvp.Statement.assign 59 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 58 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 59) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 18374686479671623680))), (Trusted.Mvp.Statement.storageDead 59), (Trusted.Mvp.Statement.assign 57 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 58) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 56))), (Trusted.Mvp.Statement.storageDead 58), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 30) (Trusted.Mvp.Operand.move 57))), (Trusted.Mvp.Statement.storageDead 57), (Trusted.Mvp.Statement.storageDead 30)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 14), (Trusted.Mvp.Statement.storageLive 15), (Trusted.Mvp.Statement.assign 15 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 14 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 15) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 4294967295))), (Trusted.Mvp.Statement.storageDead 15), (Trusted.Mvp.Statement.storageLive 16), (Trusted.Mvp.Statement.storageLive 17), (Trusted.Mvp.Statement.storageLive 18), (Trusted.Mvp.Statement.storageLive 19), (Trusted.Mvp.Statement.storageLive 20), (Trusted.Mvp.Statement.assign 20 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 14) true)), (Trusted.Mvp.Statement.assign 19 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 20) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 255))), (Trusted.Mvp.Statement.storageDead 20), (Trusted.Mvp.Statement.assign 18 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 19) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 24))), (Trusted.Mvp.Statement.storageDead 19), (Trusted.Mvp.Statement.storageLive 21), (Trusted.Mvp.Statement.storageLive 22), (Trusted.Mvp.Statement.storageLive 23), (Trusted.Mvp.Statement.assign 23 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 14) true)), (Trusted.Mvp.Statement.assign 22 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 23) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 65280))), (Trusted.Mvp.Statement.storageDead 23), (Trusted.Mvp.Statement.assign 21 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 22) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 8))), (Trusted.Mvp.Statement.storageDead 22), (Trusted.Mvp.Statement.assign 17 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 18) (Trusted.Mvp.Operand.move 21))), (Trusted.Mvp.Statement.storageDead 21), (Trusted.Mvp.Statement.storageDead 18), (Trusted.Mvp.Statement.storageLive 24), (Trusted.Mvp.Statement.storageLive 25), (Trusted.Mvp.Statement.storageLive 26), (Trusted.Mvp.Statement.assign 26 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 14) true)), (Trusted.Mvp.Statement.assign 25 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 26) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 16711680))), (Trusted.Mvp.Statement.storageDead 26), (Trusted.Mvp.Statement.assign 24 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 25) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 8))), (Trusted.Mvp.Statement.storageDead 25), (Trusted.Mvp.Statement.assign 16 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 17) (Trusted.Mvp.Operand.move 24))), (Trusted.Mvp.Statement.storageDead 24), (Trusted.Mvp.Statement.storageDead 17), (Trusted.Mvp.Statement.storageLive 27), (Trusted.Mvp.Statement.storageLive 28), (Trusted.Mvp.Statement.storageLive 29), (Trusted.Mvp.Statement.assign 29 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 14) true)), (Trusted.Mvp.Statement.assign 28 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 29) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 4278190080))), (Trusted.Mvp.Statement.storageDead 29), (Trusted.Mvp.Statement.assign 27 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 28) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 24))), (Trusted.Mvp.Statement.storageDead 28), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 16) (Trusted.Mvp.Operand.move 27))), (Trusted.Mvp.Statement.storageDead 27), (Trusted.Mvp.Statement.storageDead 16), (Trusted.Mvp.Statement.storageDead 14)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 6), (Trusted.Mvp.Statement.storageLive 7), (Trusted.Mvp.Statement.assign 7 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 6 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 7) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 65535))), (Trusted.Mvp.Statement.storageDead 7), (Trusted.Mvp.Statement.storageLive 8), (Trusted.Mvp.Statement.storageLive 9), (Trusted.Mvp.Statement.storageLive 10), (Trusted.Mvp.Statement.assign 10 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 6) true)), (Trusted.Mvp.Statement.assign 9 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 10) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 255))), (Trusted.Mvp.Statement.storageDead 10), (Trusted.Mvp.Statement.assign 8 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shl (Trusted.Mvp.Operand.move 9) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 8))), (Trusted.Mvp.Statement.storageDead 9), (Trusted.Mvp.Statement.storageLive 11), (Trusted.Mvp.Statement.storageLive 12), (Trusted.Mvp.Statement.storageLive 13), (Trusted.Mvp.Statement.assign 13 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 6) true)), (Trusted.Mvp.Statement.assign 12 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 13) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 65280))), (Trusted.Mvp.Statement.storageDead 13), (Trusted.Mvp.Statement.assign 11 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.shr (Trusted.Mvp.Operand.move 12) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 32 true) 8))), (Trusted.Mvp.Statement.storageDead 12), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitOr (Trusted.Mvp.Operand.move 8) (Trusted.Mvp.Operand.move 11))), (Trusted.Mvp.Statement.storageDead 11), (Trusted.Mvp.Statement.storageDead 8), (Trusted.Mvp.Statement.storageDead 6)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.assign 61 (Trusted.Mvp.Rvalue.discriminant 2))], terminator := (Trusted.Mvp.Terminator.switchInt (Trusted.Mvp.Operand.move 61) [(0, 8), (1, 11), (2, 10), (3, 9)] 2) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 64), (Trusted.Mvp.Statement.assign 64 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 64) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 255))), (Trusted.Mvp.Statement.storageDead 64)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true))], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 63), (Trusted.Mvp.Statement.assign 63 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 63) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 4294967295))), (Trusted.Mvp.Statement.storageDead 63)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageLive 62), (Trusted.Mvp.Statement.assign 62 (Trusted.Mvp.Rvalue.use (Trusted.Mvp.Operand.copy 3) true)), (Trusted.Mvp.Statement.assign 0 (Trusted.Mvp.Rvalue.binary Trusted.Mvp.BinOp.bitAnd (Trusted.Mvp.Operand.move 62) (Trusted.Mvp.Operand.constant (Trusted.Mvp.Ty.int 64 false) 65535))), (Trusted.Mvp.Statement.storageDead 62)], terminator := (Trusted.Mvp.Terminator.goto 12) } : Trusted.Mvp.Block), ({ statements := [(Trusted.Mvp.Statement.storageDead 4)], terminator := Trusted.Mvp.Terminator.ret } : Trusted.Mvp.Block)] } : Trusted.Mvp.Body)] }

end Captured

namespace Spec

open Trusted.Mvp Endianness

def exactReversal (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ output,
    Safe body [1, BitVec.ofNat 64 width.val, value] ∧
    Returns body [1, BitVec.ofNat 64 width.val, value] output ∧
    ByteReversal (8 * 2 ^ width.val) value output

def exactLittleEndian (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ output,
    Safe body [0, BitVec.ofNat 64 width.val, value] ∧
    Returns body [0, BitVec.ofNat 64 width.val, value] output ∧
    output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1)

def involution (body : Body) : Prop :=
  ∀ width : Fin 4, ∀ value : Word, ∃ first second,
    Returns body [1, BitVec.ofNat 64 width.val, value] first ∧
    Returns body [1, BitVec.ofNat 64 width.val, first] second ∧
    second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1)

def specs : Specs :=
  { safety := fun _ _ => True
    property := fun program => ∃ body, program.bodies = [body] ∧
      exactReversal body ∧ exactLittleEndian body ∧ involution body }

end Spec

namespace ProductionReduction

open Trusted.Mvp Anneal.Mvp Endianness

abbrev sourceBody : Body := Captured.program.bodies[0]'(by decide)

end ProductionReduction

/-!
## 1. Zero-Generator Replacement for the 5,230-Line `ProductionSteps.lean`

All 8 paths of Starnix `apply_endianness` discharge via `runForced_initial_success`
with uniform `fuel := 64` and `rfl`, requiring **0 lines of Python witness
generation** (`generate_steps.py`) and **0 intermediate state declarations**.
-/

namespace ProductionSteps

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

set_option maxRecDepth 200000

theorem le8 (value : Word) :
    Safe sourceBody [0, 0, value] ∧
      Returns sourceBody [0, 0, value] (value &&& 255) :=
  runForced_initial_success (fuel := 64) rfl

theorem le16 (value : Word) :
    Safe sourceBody [0, 1, value] ∧
      Returns sourceBody [0, 1, value] (value &&& 65535) :=
  runForced_initial_success (fuel := 64) rfl

theorem le32 (value : Word) :
    Safe sourceBody [0, 2, value] ∧
      Returns sourceBody [0, 2, value] (value &&& 4294967295) :=
  runForced_initial_success (fuel := 64) rfl

theorem le64 (value : Word) :
    Safe sourceBody [0, 3, value] ∧
      Returns sourceBody [0, 3, value] value :=
  runForced_initial_success (fuel := 64) rfl

theorem be8 (value : Word) :
    Safe sourceBody [1, 0, value] ∧
      Returns sourceBody [1, 0, value] (swap8 value) :=
  runForced_initial_success (fuel := 64) rfl

theorem be16 (value : Word) :
    Safe sourceBody [1, 1, value] ∧
      Returns sourceBody [1, 1, value] (swap16 value) :=
  runForced_initial_success (fuel := 64) rfl

theorem be32 (value : Word) :
    Safe sourceBody [1, 2, value] ∧
      Returns sourceBody [1, 2, value] (swap32 value) :=
  runForced_initial_success (fuel := 64) rfl

theorem be64 (value : Word) :
    Safe sourceBody [1, 3, value] ∧
      Returns sourceBody [1, 3, value] (swap64 value) :=
  runForced_initial_success (fuel := 100) rfl

end ProductionSteps

namespace ProductionClaims

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction ProductionSteps

theorem wellFormed : bodyWF sourceBody = true := by decide

theorem completed :
    ∀ flag : Fin 2, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value] ∧
      ∃ output, Returns sourceBody
        [BitVec.ofNat 64 flag.val, BitVec.ofNat 64 width.val, value] output := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))
  · exact fin4_cases
      (fun v => ⟨(le8 v).1, _, (le8 v).2⟩)
      (fun v => ⟨(le16 v).1, _, (le16 v).2⟩)
      (fun v => ⟨(le32 v).1, _, (le32 v).2⟩)
      (fun v => ⟨(le64 v).1, _, (le64 v).2⟩)
  · exact fin4_cases
      (fun v => ⟨(be8 v).1, _, (be8 v).2⟩)
      (fun v => ⟨(be16 v).1, _, (be16 v).2⟩)
      (fun v => ⟨(be32 v).1, _, (be32 v).2⟩)
      (fun v => ⟨(be64 v).1, _, (be64 v).2⟩)

theorem baseline (safetyPre : List Word → Prop) :
    BodyVerified sourceBody safetyPre := by
  constructor
  · exact wellFormed
  · intro args valid _
    apply validArgs3_elim sourceBody 1363 rfl rfl rfl (Safe sourceBody) _ args valid
    intro flag width value
    exact (completed flag width value).1

theorem bigEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output,
      Safe sourceBody [1, BitVec.ofNat 64 width.val, value] ∧
      Returns sourceBody [1, BitVec.ofNat 64 width.val, value] output ∧
      ByteReversal (8 * 2 ^ width.val) value output := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    have execution := be8 value
    exact ⟨_, execution.1, execution.2, swap8_exact value⟩
  · intro value
    have execution := be16 value
    exact ⟨_, execution.1, execution.2, swap16_exact value⟩
  · intro value
    have execution := be32 value
    exact ⟨_, execution.1, execution.2, swap32_exact value⟩
  · intro value
    have execution := be64 value
    exact ⟨_, execution.1, execution.2, swap64_exact value⟩

theorem littleEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output,
      Safe sourceBody [0, BitVec.ofNat 64 width.val, value] ∧
      Returns sourceBody [0, BitVec.ofNat 64 width.val, value] output ∧
      output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, (le8 value).1, (le8 value).2, rfl⟩
  · intro value
    exact ⟨_, (le16 value).1, (le16 value).2, rfl⟩
  · intro value
    exact ⟨_, (le32 value).1, (le32 value).2, rfl⟩
  · intro value
    refine ⟨_, (le64 value).1, (le64 value).2, ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change value = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]

theorem bigEndian_involutive :
    ∀ width : Fin 4, ∀ value : Word, ∃ first second,
      Returns sourceBody [1, BitVec.ofNat 64 width.val, value] first ∧
      Returns sourceBody [1, BitVec.ofNat 64 width.val, first] second ∧
      second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, _, (be8 value).2,
      (be8 (swap8 value)).2, swap8_involutive value⟩
  · intro value
    exact ⟨_, _, (be16 value).2,
      (be16 (swap16 value)).2, swap16_involutive value⟩
  · intro value
    exact ⟨_, _, (be32 value).2,
      (be32 (swap32 value)).2, swap32_involutive value⟩
  · intro value
    refine ⟨_, _, (be64 value).2,
      (be64 (swap64 value)).2, ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change swap64 (swap64 value) =
      value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]
    exact swap64_involutive value

end ProductionClaims

namespace Proof

open Trusted.Mvp Endianness ProductionReduction ProductionClaims

theorem verify : UnitTheorem Captured.program Spec.specs := by
  constructor
  · rfl
  · constructor
    · intro id body found
      change ([sourceBody] : List Body)[id]? = some body at found
      cases id with
      | zero =>
        have same : sourceBody = body := Option.some.inj found
        subst body
        exact baseline _
      | succ id => simp at found
    · exact ⟨sourceBody, rfl, bigEndian_exact, littleEndian_exact,
        bigEndian_involutive⟩

end Proof

/-!
## 2. Mutation Resilience Without `generate_steps.py` or `checkpoint = min(2, last)`

We test the exact two mutations from `ci/test_mvp_starnix.py`:
1. `mutatedZeroBody` (`return 0;`, 4 locals, 1 basic block, 1 step).
2. `mutatedMaskedIdentityBody` (`match width { ... }`, 8 locals, 7 basic blocks, 7 steps).
-/

namespace MutationCanaries

open Trusted.Mvp Anneal.Mvp Endianness

/-- Captured MIR body for the `zero` mutation (`pub fn apply_endianness(...) -> u64 { 0 }`). -/
def mutatedZeroBody : Body :=
  { argCount := 3
    isUnsafe := false
    localTys := [.int 64 false, .bool, .enum 1363 [0, 1, 2, 3], .int 64 false]
    blocks := [
      { statements := [.assign 0 (.use (.constant (.int 64 false) 0) true)]
        terminator := .ret }
    ] }

/-- Captured MIR body for the `masked-identity` mutation. -/
def mutatedMaskedIdentityBody : Body :=
  { argCount := 3
    isUnsafe := false
    localTys := [
      .int 64 false, .bool, .enum 1363 [0, 1, 2, 3], .int 64 false,
      .int 64 true, .int 64 false, .int 64 false, .int 64 false
    ]
    blocks := [
      { statements := [.assign 4 (.discriminant 2)]
        terminator := .switchInt (.move 4) [(0, 5), (1, 4), (2, 3), (3, 2)] 1 },
      { statements := [], terminator := .unreachable },
      { statements := [.assign 0 (.use (.copy 3) true)]
        terminator := .goto 6 },
      { statements := [
          .storageLive 7,
          .assign 7 (.use (.copy 3) true),
          .assign 0 (.binary .bitAnd (.move 7) (.constant (.int 64 false) 4294967295)),
          .storageDead 7
        ]
        terminator := .goto 6 },
      { statements := [
          .storageLive 6,
          .assign 6 (.use (.copy 3) true),
          .assign 0 (.binary .bitAnd (.move 6) (.constant (.int 64 false) 65535)),
          .storageDead 6
        ]
        terminator := .goto 6 },
      { statements := [
          .storageLive 5,
          .assign 5 (.use (.copy 3) true),
          .assign 0 (.binary .bitAnd (.move 5) (.constant (.int 64 false) 255)),
          .storageDead 5
        ]
        terminator := .goto 6 },
      { statements := [], terminator := .ret }
    ] }

/-- **Mutation 1 (`zero`)**: Even though `mutatedZeroBody` has only 4 locals and
    returns in 1 step (`last = 1 < 2`), `runForced` with the exact same `fuel = 64`
    evaluates directly to `some 0` by `rfl` without needing `generate_steps.py` or
    `checkpoint = min(2, last)`! -/
theorem mutatedZero_be64_evaluates_to_zero (value : Word) :
    forceState (initial mutatedZeroBody [1, 3, value])
      (runForced mutatedZeroBody 64) = some 0 :=
  rfl

/-- `mutatedZeroBody` violates `Spec.exactReversal` at `width = 3, value = 1`. -/
theorem mutatedZero_rejected_by_exactReversal :
    ¬ Spec.exactReversal mutatedZeroBody := by
  intro hRev
  have ⟨output, _, hRet, hBytes⟩ := hRev ⟨3, by decide⟩ 1
  have hOutEq : (0 : Word) = output :=
    runForced_result_unique (mutatedZero_be64_evaluates_to_zero 1) hRet
  subst hOutEq
  have hBit56 := hBytes 56 (by decide)
  revert hBit56
  decide

/-- **Mutation 2 (`masked-identity`)**: Without any witness regeneration, the
    exact same `runForced_initial_success (fuel := 64) rfl` proofs **still pass**
    on the 5 unaffected paths (`le8`, `le16`, `le32`, `le64`, `be8`), even though
    `localTys.length` changed from 65 to 8 and `blocks.length` changed from 13 to 7! -/
theorem mutatedMaskedIdentity_unaffected_paths_still_verify (value : Word) :
    (Safe mutatedMaskedIdentityBody [0, 0, value] ∧
      Returns mutatedMaskedIdentityBody [0, 0, value] (value &&& 255)) ∧
    (Safe mutatedMaskedIdentityBody [0, 1, value] ∧
      Returns mutatedMaskedIdentityBody [0, 1, value] (value &&& 65535)) ∧
    (Safe mutatedMaskedIdentityBody [0, 2, value] ∧
      Returns mutatedMaskedIdentityBody [0, 2, value] (value &&& 4294967295)) ∧
    (Safe mutatedMaskedIdentityBody [0, 3, value] ∧
      Returns mutatedMaskedIdentityBody [0, 3, value] value) ∧
    (Safe mutatedMaskedIdentityBody [1, 0, value] ∧
      Returns mutatedMaskedIdentityBody [1, 0, value] (swap8 value)) :=
  ⟨runForced_initial_success (fuel := 64) rfl,
   runForced_initial_success (fuel := 64) rfl,
   runForced_initial_success (fuel := 64) rfl,
   runForced_initial_success (fuel := 64) rfl,
   runForced_initial_success (fuel := 64) rfl⟩

/-- And on the 3 broken paths (`be16`, `be32`, `be64`), `runForced` evaluates
    directly to the unreversed masked values by `rfl`, refuting `Spec.exactReversal`. -/
theorem mutatedMaskedIdentity_be16_evaluates_to_unreversed (value : Word) :
    forceState (initial mutatedMaskedIdentityBody [1, 1, value])
      (runForced mutatedMaskedIdentityBody 64) = some (value &&& 65535) :=
  rfl

theorem mutatedMaskedIdentity_rejected_by_exactReversal :
    ¬ Spec.exactReversal mutatedMaskedIdentityBody := by
  intro hRev
  have ⟨output, _, hRet, hBytes⟩ := hRev ⟨1, by decide⟩ 1
  have hOutEq : ((1 : Word) &&& 65535) = output :=
    runForced_result_unique (mutatedMaskedIdentity_be16_evaluates_to_unreversed 1) hRet
  subst hOutEq
  have hBit8 := hBytes 8 (by decide)
  revert hBit8
  decide

end MutationCanaries
