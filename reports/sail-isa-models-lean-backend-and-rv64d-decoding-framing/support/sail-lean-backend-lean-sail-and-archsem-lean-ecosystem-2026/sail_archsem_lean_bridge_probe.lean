/-
  sail_archsem_lean_bridge_probe.lean

  Standalone Lean 4.34.1 mechanization for:
  "Sail Lean Backend, lean-sail, and the ArchSem Lean Ecosystem (2026)"

  This file mechanizes and compares:
  1. `lean-sail`'s V2 (`CONCURRENCY_INTERFACE_V2` / `Sail.ArchSem`) freer monad
     `PreSailM := FreeM ((Except (SailError ue) InstructionEffect) ⊕ FinChoice)`
     and its `LawfulMonad` structure.
  2. `lean-sail`'s `Sail.ArchSemSequential` deterministic `EStateM` interpreter,
     which hardcodes `FinChoice` to index `0` and treats `.barrier`,
     `.memWriteAnnounce`, `.archException`, and `.returnException` as `pure ()`.
  3. `archsem-lean`'s `NEStateM` nondeterministic list-set state monad interpreter
     and view-based promising memory read candidates.
  4. Anneal's Layer 1A (`Behavior`, `Language`, `WellFormed`), Layer 1B
     (`ChoiceKind`, `StepResult`, `ReachesPrefix`, `SmallStepMachine`,
     `BehaviorOf`), and `Trusted.Memory` (`View`, `AtomicMsg`, `MemState`,
     `visibleAtomicMsgs`, `applyAtomicLoad`) bridge interpreter.
  5. Formal theorems proving:
     - `ArchSemSequential` is unsound for demonic undefined-value (`FinChoice`)
       safety: a program using `undefined_bit` that asserts the chosen bit is `0`
       succeeds unconditionally under `ArchSemSequential`, yet fails with UB
       in `archsem-lean`'s `NEStateM` and violates `WellFormed` in Anneal's
       `StepResult` semantics (`archSemSeq_unsound_for_demonic_undefined`).
     - `ArchSemSequential` is unsound for architectural exceptions emitted via
       `sail_take_exception`: it treats `.archException` as a no-op and continues
       executing subsequent register writes, whereas both `archsem-lean` and the
       Anneal `StepResult` bridge flag UB (`archSemSeq_unsound_for_silent_exception`).
     - `ArchSemSequential` collapses weak-memory loads to a single latest byte
       and ignores barriers, whereas the Anneal `StepResult` + `Trusted.Memory`
       bridge demonically branches over all `visibleAtomicMsgs` allowed by the
       thread's coherence/acquire view and restricts stale reads once views
       advance (`unsync_can_read_new_and_stale`, `synced_cannot_read_stale`).
     - For any `FreeM` instruction tree in the choice+register fragment,
       `WellFormed` of the Anneal `StepResult` bridge guarantees UB freedom
       across all nondeterministic branches in `archsem-lean`'s `NEStateM`,
       and every `ArchSemSequential` `.ok` result is included in the Anneal
       `StepResult` behavior's `.val` set
       (`stepResult_wellFormed_excludes_neStateM_error` and
       `archSemSeq_ok_in_stepResult_behavior`).
-/

namespace SailArchSemBridgeProbe

/-! ## Part 1: `lean-sail` V2 (`Sail.ArchSem`) Freer Monad & Effect Signature -/

/-- Effect typeclass matching `Sail.ArchSem.Effect` (`lean-sail/Sail/ArchSem.lean:27-29`). -/
class Effect (Eff : Type) where
  ret : Eff → Type

instance [Effect A] [Effect B] : Effect (A ⊕ B) where
  ret
    | .inl a => Effect.ret a
    | .inr b => Effect.ret b

instance {ε A : Type} [Effect A] : Effect (Except ε A) where
  ret
    | .error _ => Empty
    | .ok e => Effect.ret e

/-- Bounded nondeterministic choice effect (`lean-sail/Sail/ArchSem.lean:69-72`). -/
abbrev FinChoice : Type := Nat

instance : Effect FinChoice where
  ret (n : Nat) := Fin n

/-- The freer monad `FreeM` used by `lean-sail` (`lean-sail/Sail/ArchSem.lean:40-66`). -/
inductive FreeM (Eff : Type) [Effect Eff] (α : Type) : Type where
  | pure (x : α) : FreeM Eff α
  | impure (eff : Eff) (cont : Effect.ret eff → FreeM Eff α) : FreeM Eff α

namespace FreeM

variable {Eff : Type} [Effect Eff]

def bind {α β : Type} : FreeM Eff α → (α → FreeM Eff β) → FreeM Eff β
  | .pure x, f => f x
  | .impure eff k, f => .impure eff (fun r => bind (k r) f)

def map {α β : Type} (f : α → β) : FreeM Eff α → FreeM Eff β
  | .pure x => .pure (f x)
  | .impure eff k => .impure eff (fun r => map f (k r))

instance : Monad (FreeM Eff) where
  pure := FreeM.pure
  bind := FreeM.bind
  map := FreeM.map

@[simp] theorem pure_def (x : α) : (Pure.pure x : FreeM Eff α) = .pure x := rfl
@[simp] theorem bind_pure (x : α) (f : α → FreeM Eff β) :
    (FreeM.pure x >>= f) = f x := rfl
@[simp] theorem bind_impure (eff : Eff) (k : Effect.ret eff → FreeM Eff α)
    (f : α → FreeM Eff β) :
    (FreeM.impure eff k >>= f) = .impure eff (fun r => k r >>= f) := rfl

theorem map_eq_bind_pure {α β : Type} (f : α → β) (m : FreeM Eff α) :
    f <$> m = (m >>= fun x => .pure (f x)) := by
  induction m with
  | pure x => rfl
  | impure eff k ih =>
    change FreeM.impure eff (fun r => f <$> k r) =
      FreeM.impure eff (fun r => k r >>= fun x => .pure (f x))
    congr 1
    funext r
    exact ih r

theorem id_map' {α : Type} (m : FreeM Eff α) : (id <$> m) = m := by
  induction m with
  | pure x => rfl
  | impure eff k ih =>
    change FreeM.impure eff (fun r => id <$> k r) = FreeM.impure eff k
    congr 1
    funext r
    exact ih r

theorem pure_bind' {α β : Type} (x : α) (f : α → FreeM Eff β) :
    (Pure.pure x >>= f) = f x := rfl

theorem bind_assoc' {α β γ : Type} (m : FreeM Eff α)
    (f : α → FreeM Eff β) (g : β → FreeM Eff γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  induction m with
  | pure x => rfl
  | impure eff k ih =>
    simp only [bind_impure]
    congr 1
    funext r
    exact ih r

theorem bind_pure_comp' {α β : Type} (f : α → β) (m : FreeM Eff α) :
    (m >>= fun x => Pure.pure (f x)) = (f <$> m) :=
  (map_eq_bind_pure f m).symm

instance : LawfulMonad (FreeM Eff) :=
  LawfulMonad.mk'
    (id_map := id_map')
    (pure_bind := pure_bind')
    (bind_assoc := bind_assoc')
    (bind_pure_comp := bind_pure_comp')

/-- Lift an effect interpreter into any target monad `m` (`lean-sail/Sail/ArchSem.lean:62-65`). -/
def liftM {m : Type → Type} [Monad m] {α : Type}
    (interp : (eff : Eff) → m (Effect.ret eff)) : FreeM Eff α → m α
  | .pure x => Pure.pure x
  | .impure eff k => do
      let r ← interp eff
      liftM interp (k r)

end FreeM

/-- Sail runtime errors matching `lean-sail/Sail/Common.lean:15-31`. -/
inductive SailError (ue : Type) : Type where
  | Exit
  | Unreachable
  | OutOfMemoryRange (addr : Nat)
  | Assertion (msg : String)
  | InfiniteNondeterminisim
  | User (err : ue)
  deriving DecidableEq, Repr

/-- Minimal architectural instantiation matching `Sail.ArchSem.Arch`. -/
inductive Reg : Type where
  | R0
  | R1
  | PC
  deriving DecidableEq, Repr

abbrev Word := BitVec 64
abbrev Addr := Nat

/-- Memory access ordering attributes matching `AccessDescriptor` classifiers. -/
inductive MemAcc : Type where
  | explicitRelaxed
  | explicitAcquire
  | explicitRelease
  | explicitAcqRel
  | ifetch
  deriving DecidableEq, Repr

def MemAcc.isExplicit : MemAcc → Bool
  | .ifetch => false
  | _ => true

def MemAcc.isAcquire : MemAcc → Bool
  | .explicitAcquire | .explicitAcqRel => true
  | _ => false

def MemAcc.isRelease : MemAcc → Bool
  | .explicitRelease | .explicitAcqRel => true
  | _ => false

inductive BarrierKind : Type where
  | dmbSy
  | dmbLd
  | dmbSt
  | isb
  deriving DecidableEq, Repr

structure MemReq where
  address : Addr
  accessKind : MemAcc
  numTag : Nat := 0
  deriving DecidableEq, Repr

/-- `InstructionEffect` matching `lean-sail/Sail/ArchSem.lean:151-193`. -/
inductive InstructionEffect : Type where
  | regRead (reg : Reg) (acc : Option Unit)
  | regWrite (reg : Reg) (acc : Option Unit) (val : Word)
  | memRead (req : MemReq)
  | memWriteAnnounce (req : MemReq)
  | memWrite (req : MemReq) (val : Word)
  | barrier (b : BarrierKind)
  | archException (exn : Unit)
  | returnException
  | printMessage (msg : String)
  deriving DecidableEq, Repr

instance : Effect InstructionEffect where
  ret
    | .regRead _ _ => Word
    | .regWrite _ _ _ => Unit
    | .memRead _ => Except Unit Word
    | .memWriteAnnounce _ => Unit
    | .memWrite _ _ => Except Unit Unit
    | .barrier _ => Unit
    | .archException _ => Unit
    | .returnException => Unit
    | .printMessage _ => Unit

/-- `PreSailM` freer monad matching `lean-sail/Sail/ArchSem.lean:212-213`. -/
abbrev PreSailEff (ue : Type) : Type :=
  (Except (SailError ue) InstructionEffect) ⊕ FinChoice

abbrev PreSailM (ue : Type) : Type → Type :=
  FreeM (PreSailEff ue)

/-! ### Sail Primitives in `PreSailM` -/

def choose_fin {ue : Type} (n : Nat) : PreSailM ue (Fin n) :=
  .impure (.inr n) .pure

def sailThrowError {ue : Type} {α : Type} (err : SailError ue) : PreSailM ue α :=
  .impure (.inl (.error err)) (fun e : Empty => Empty.elim e)

def sailEffect {ue : Type} (eff : InstructionEffect) : PreSailM ue (Effect.ret eff) :=
  .impure (.inl (.ok eff)) .pure

def undefined_bit {ue : Type} (_ : Unit) : PreSailM ue (BitVec 1) := do
  let i ← choose_fin 2
  return BitVec.ofNat 1 i.val

def undefined_bool {ue : Type} (_ : Unit) : PreSailM ue Bool := do
  let i ← choose_fin 2
  return (i.val == 1)

def sail_assert {ue : Type} (p : Bool) (msg : String) : PreSailM ue Unit :=
  if p then .pure () else sailThrowError (.Assertion msg)

def readReg {ue : Type} (r : Reg) : PreSailM ue Word :=
  sailEffect (.regRead r none)

def writeReg {ue : Type} (r : Reg) (v : Word) : PreSailM ue Unit :=
  sailEffect (.regWrite r none v)

def sail_mem_read {ue : Type} (req : MemReq) : PreSailM ue (Except Unit Word) :=
  sailEffect (.memRead req)

def sail_mem_write {ue : Type} (req : MemReq) (v : Word) : PreSailM ue (Except Unit Unit) :=
  sailEffect (.memWrite req v)

def sail_barrier {ue : Type} (b : BarrierKind) : PreSailM ue Unit :=
  sailEffect (.barrier b)

def sail_take_exception {ue : Type} (f : Unit) : PreSailM ue Unit :=
  sailEffect (.archException f)

/-! ## Part 2: `lean-sail`'s `ArchSemSequential` Interpreter (`EStateM`) -/

/-- Sequential state matching `lean-sail/Sail/ArchSemSequential.lean:24-31`. -/
structure SequentialState where
  regs : Reg → Option Word
  mem : Addr → Option Word
  cycleCount : Nat := 0
  sailOutput : List String := []

def SequentialState.readReg? (s : SequentialState) (r : Reg) : Option Word :=
  s.regs r

def SequentialState.writeReg (s : SequentialState) (r : Reg) (v : Word) : SequentialState :=
  { s with regs := fun r' => if r' = r then some v else s.regs r' }

def SequentialState.readMem? (s : SequentialState) (a : Addr) : Option Word :=
  s.mem a

def SequentialState.writeMem (s : SequentialState) (a : Addr) (v : Word) : SequentialState :=
  { s with mem := fun a' => if a' = a then some v else s.mem a' }

abbrev ArchSemSeqM (ue : Type) (α : Type) :=
  EStateM (SailError ue) SequentialState α

/-- Exact semantics of `Sail.ArchSem.Sequential.interpretEffect`
    (`lean-sail/Sail/ArchSemSequential.lean:51-81`).
    Note that `.memWriteAnnounce`, `.barrier`, `.archException`, and `.returnException`
    all evaluate to `pure ()`. -/
def archSemSeqInterpretEffect {ue : Type} (eff : InstructionEffect) :
    ArchSemSeqM ue (Effect.ret eff) :=
  match eff with
  | .regRead reg _ => fun s =>
      match s.readReg? reg with
      | some v => .ok v s
      | none => .error .Unreachable s
  | .regWrite reg _ val => fun s =>
      .ok () (s.writeReg reg val)
  | .memRead req => fun s =>
      if req.numTag != 0 then
        .error (.Assertion "Tagged memory not supported") s
      else
        match s.readMem? req.address with
        | some v => .ok (.ok v) s
        | none => .error (.OutOfMemoryRange req.address) s
  | .memWriteAnnounce _ => fun s => .ok () s
  | .memWrite req val => fun s =>
      if req.numTag != 0 then
        .error (.Assertion "Tagged memory not supported") s
      else
        .ok (.ok ()) (s.writeMem req.address val)
  | .barrier _ => fun s => .ok () s
  | .archException _ => fun s => .ok () s
  | .returnException => fun s => .ok () s
  | .printMessage msg => fun s =>
      .ok () { s with sailOutput := msg :: s.sailOutput }

/-- Exact semantics of `Sail.ArchSem.Sequential.interpretSailEffects`
    (`lean-sail/Sail/ArchSemSequential.lean:83-90`).
    Note that `.inr choice` deterministically selects `⟨0, h⟩ : Fin choice`! -/
def archSemSeqInterpret {ue : Type} {α : Type} :
    PreSailM ue α → ArchSemSeqM ue α :=
  FreeM.liftM (fun
    | .inl (.error err) => fun s => .error err s
    | .inl (.ok eff) => archSemSeqInterpretEffect eff
    | .inr choice => fun s =>
        if h : 0 < choice then
          .ok (⟨0, h⟩ : Fin choice) s
        else
          .error .Unreachable s)

/-! ## Part 3: `archsem-lean`'s `NEStateM` Nondeterministic Interpreter -/

/-- Nondeterministic exception result matching `archsem-lean/ArchSem/NondeterministicMonad.lean:16-19`. -/
structure NExcept (ε α : Type) where
  oks : List α
  errors : List ε
  deriving DecidableEq, Repr

/-- Nondeterministic state monad matching `archsem-lean/ArchSem/NondeterministicMonad.lean:146`. -/
abbrev NEStateM (ε σ α : Type) := σ → NExcept ε (σ × α)

namespace NEStateM

def pure {ε σ α : Type} (x : α) : NEStateM ε σ α :=
  fun s => { oks := [(s, x)], errors := [] }

def bind {ε σ α β : Type} (m : NEStateM ε σ α) (f : α → NEStateM ε σ β) :
    NEStateM ε σ β :=
  fun s =>
    let r1 := m s
    let r2s := r1.oks.map (fun (s', a) => f a s')
    { oks := r2s.flatMap NExcept.oks
    , errors := r1.errors ++ r2s.flatMap NExcept.errors }

instance {ε σ : Type} : Monad (NEStateM ε σ) where
  pure := NEStateM.pure
  bind := NEStateM.bind

def get {ε σ : Type} : NEStateM ε σ σ :=
  fun s => { oks := [(s, s)], errors := [] }

def modify {ε σ : Type} (f : σ → σ) : NEStateM ε σ Unit :=
  fun s => { oks := [(f s, ())], errors := [] }

def throwError {ε σ α : Type} (e : ε) : NEStateM ε σ α :=
  fun _ => { oks := [], errors := [e] }

def chooseFin {ε σ : Type} (n : Nat) : NEStateM ε σ (Fin n) :=
  fun s => { oks := (List.finRange n).map (fun i => (s, i)), errors := [] }

theorem mem_bind_errors {ε σ α β : Type} {m : NEStateM ε σ α}
    {f : α → NEStateM ε σ β} {s : σ} {err : ε} :
    err ∈ (NEStateM.bind m f s).errors ↔
    err ∈ (m s).errors ∨ ∃ s' a, (s', a) ∈ (m s).oks ∧ err ∈ (f a s').errors := by
  simp only [NEStateM.bind, List.mem_append, List.mem_flatMap, List.mem_map, Prod.exists]
  constructor
  · rintro (h | ⟨r, ⟨s', a, hOk, rfl⟩, hErr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s', a, hOk, hErr⟩
  · rintro (h | ⟨s', a, hOk, hErr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨f a s', ⟨s', a, hOk, rfl⟩, hErr⟩

end NEStateM

/-- `archsem-lean` sequential effect handler (`ArchSemTinyArm/Sequential.lean:51-87`).
    Unlike `lean-sail`'s `ArchSemSequential`, it explores all `FinChoice` branches
    via `NEStateM.chooseFin` and rejects `.archException` and `.returnException`. -/
def archsemLeanInterpretEffect (eff : InstructionEffect) :
    NEStateM String SequentialState (Effect.ret eff) :=
  match eff with
  | .regRead reg none => fun s =>
      match s.readReg? reg with
      | some v => { oks := [(s, v)], errors := [] }
      | none => { oks := [], errors := ["Unmapped register"] }
  | .regRead _ (some _) =>
      NEStateM.throwError "Non trivial reg access types unsupported"
  | .regWrite reg none val =>
      NEStateM.modify (fun s => s.writeReg reg val)
  | .regWrite _ (some _) _ =>
      NEStateM.throwError "Non trivial reg access types unsupported"
  | .memRead req => fun s =>
      if req.numTag != 0 then
        { oks := [], errors := ["Memory request tags not supported"] }
      else
        match s.readMem? req.address with
        | some v => { oks := [(s, .ok v)], errors := [] }
        | none => { oks := [], errors := ["OutOfMemoryRange"] }
  | .memWriteAnnounce _ => NEStateM.pure ()
  | .memWrite req val => fun s =>
      if req.numTag != 0 then
        { oks := [], errors := ["Memory request tags not supported"] }
      else
        { oks := [(s.writeMem req.address val, .ok ())], errors := [] }
  | .barrier _ => NEStateM.pure ()
  | .archException _ => NEStateM.throwError "Architecture exception"
  | .returnException => NEStateM.throwError "Unsupported effect: returnException"
  | .printMessage msg =>
      NEStateM.modify (fun s => { s with sailOutput := msg :: s.sailOutput })

def archsemLeanInterpret {ue : Type} {α : Type} :
    PreSailM ue α → NEStateM String SequentialState α :=
  FreeM.liftM (fun
    | .inl (.error _) => NEStateM.throwError "SailError"
    | .inl (.ok eff) => archsemLeanInterpretEffect eff
    | .inr choice => NEStateM.chooseFin choice)

/-! ## Part 4: Anneal Layer 1A, Layer 1B (`StepResult`), and `Trusted.Memory` Bridge -/

/-- Layer 1A Preorder and Refinement (`Trusted/Refinement.lean`). -/
class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

structure Behavior (Obs : Type) where
  wf : Prop
  val : Obs → Prop

instance {Obs : Type} : Preorder (Behavior Obs) where
  le b1 b2 := (b2.wf → b1.wf) ∧ (b2.wf → ∀ o, b1.val o → b2.val o)
  le_refl _ := ⟨id, fun _ _ h => h⟩
  le_trans := fun ⟨h1w, h1v⟩ ⟨h2w, h2v⟩ =>
    ⟨fun hw3 => h1w (h2w hw3), fun hw3 o ho => h2v hw3 o (h1v (h2w hw3) o ho)⟩

/-- Top of the refinement lattice (`Trusted/Refinement.lean`). -/
def WellFormed (P : Type) : Behavior P where
  wf := True
  val := fun _ => True

/-- Layer 1B Small-Step Semantics (`Trusted/StepResult.lean`). -/
inductive ChoiceKind : Type where
  | demonic
  | angelic
  deriving DecidableEq, Repr

inductive FailureKind : Type where
  | ub
  | fuelExhausted
  deriving DecidableEq, Repr

inductive StepResult (State : Type) (Obs : Type) : Type 1 where
  | step (next : State)
  | choice (kind : ChoiceKind) {ι : Type} (branches : ι → State)
  | done (obs : Obs)
  | failed (kind : FailureKind)

inductive PrefixOutcome (Obs : Type) : Type where
  | done (obs : Obs)
  | failed (kind : FailureKind)
  deriving DecidableEq, Repr

inductive ReachesPrefix {State Obs : Type} (stepFn : State → StepResult State Obs) :
    Nat → State → PrefixOutcome Obs → Prop where
  | zero (s : State) :
      ReachesPrefix stepFn 0 s (.failed .fuelExhausted)
  | done {n : Nat} {s : State} {obs : Obs} :
      stepFn s = .done obs →
      ReachesPrefix stepFn (n + 1) s (.done obs)
  | failed {n : Nat} {s : State} {k : FailureKind} :
      stepFn s = .failed k →
      ReachesPrefix stepFn (n + 1) s (.failed k)
  | step {n : Nat} {s next : State} {out : PrefixOutcome Obs} :
      stepFn s = .step next →
      ReachesPrefix stepFn n next out →
      ReachesPrefix stepFn (n + 1) s out
  | choice_demonic {n : Nat} {s : State} {ι : Type} {branches : ι → State}
      (i : ι) {out : PrefixOutcome Obs} :
      stepFn s = .choice .demonic branches →
      ReachesPrefix stepFn n (branches i) out →
      ReachesPrefix stepFn (n + 1) s out
  | choice_angelic_done {n : Nat} {s : State} {ι : Type} {branches : ι → State}
      (i : ι) {obs : Obs} :
      stepFn s = .choice .angelic branches →
      ReachesPrefix stepFn n (branches i) (.done obs) →
      ReachesPrefix stepFn (n + 1) s (.done obs)
  | choice_angelic_all_failed {n : Nat} {s : State} {ι : Type} {branches : ι → State}
      (k : FailureKind) (w : ι) :
      stepFn s = .choice .angelic branches →
      (∀ i : ι, ReachesPrefix stepFn n (branches i) (.failed k)) →
      ReachesPrefix stepFn (n + 1) s (.failed k)

structure SmallStepMachine (Prog State Obs : Type) where
  init : Prog → State
  step : State → StepResult State Obs

def BehaviorOf {Prog State Obs : Type} (M : SmallStepMachine Prog State Obs)
    (fuel : Nat) (p : Prog) : Behavior Obs where
  wf := ¬ ReachesPrefix M.step fuel (M.init p) (.failed .ub)
  val := fun obs => ReachesPrefix M.step fuel (M.init p) (.done obs)

/-- Timestamped View & Promising-Lite Memory (`Trusted/Memory.lean`). -/
abbrev Timestamp := Nat

structure View where
  ts : Addr → Timestamp

def View.bot : View where
  ts := fun _ => 0

def View.join (v1 v2 : View) : View where
  ts := fun a => Nat.max (v1.ts a) (v2.ts a)

def View.bump (v : View) (a : Addr) (t : Timestamp) : View where
  ts := fun a' => if a' = a then Nat.max (v.ts a) t else v.ts a'

structure AtomicMsg where
  addr : Addr
  val : Word
  timestamp : Timestamp
  relView : View

structure MemState where
  mapped : Addr → Bool
  atomicHistory : List AtomicMsg

/-- Visible atomic messages at address `a` for a thread with coherence view `curView`
    (`Trusted/Memory.lean:visibleAtomicMsgs`). -/
def MemState.visibleAtomicMsgs (m : MemState) (curView : View) (a : Addr) : List AtomicMsg :=
  if m.mapped a then
    m.atomicHistory.filter (fun msg => decide (msg.addr = a ∧ curView.ts a ≤ msg.timestamp))
  else
    []

/-- Post-load view update (`Trusted/Memory.lean:applyAtomicLoad`). -/
def applyAtomicLoad (curView : View) (acc : MemAcc) (msg : AtomicMsg) : View :=
  let vCoh := curView.bump msg.addr msg.timestamp
  if acc.isAcquire then
    View.join vCoh msg.relView
  else
    vCoh

/-- Append a new atomic store message (`Trusted/Memory.lean:appendAtomicMsg`). -/
def MemState.appendStore (m : MemState) (curView : View) (acc : MemAcc)
    (a : Addr) (v : Word) : Option (MemState × View) :=
  if m.mapped a then
    let newTs := m.atomicHistory.length + 1
    let vPost := curView.bump a newTs
    let relV := if acc.isRelease then vPost else View.bot
    let msg : AtomicMsg := { addr := a, val := v, timestamp := newTs, relView := relV }
    some ({ m with atomicHistory := msg :: m.atomicHistory }, vPost)
  else
    none

/-- Combined architectural + weak-memory state for the Anneal-Sail bridge. -/
structure BridgeMachineState where
  regs : Reg → Option Word
  curView : View
  acqView : View
  mem : MemState
  output : List String := []

def BridgeMachineState.readReg? (s : BridgeMachineState) (r : Reg) : Option Word :=
  s.regs r

def BridgeMachineState.writeReg (s : BridgeMachineState) (r : Reg) (v : Word) : BridgeMachineState :=
  { s with regs := fun r' => if r' = r then some v else s.regs r' }

/-- Small-step configuration pairing a `PreSailM` freer monad term with `BridgeMachineState`. -/
structure SailConfig (ue α : Type) where
  term : PreSailM ue α
  state : BridgeMachineState

/-- Single-step operational semantics interpreting `PreSailM` into Anneal's `StepResult`:
    - `FinChoice n` with `0 < n` becomes `StepResult.choice .demonic` over `Fin n`.
    - `FinChoice 0` or `SailError` or `.archException` becomes `StepResult.failed .ub`.
    - `.memRead` on explicit accesses demonically chooses among `visibleAtomicMsgs`
      (using `Fin cand.length`), updating `curView` and `acqView` on acquire loads.
    - `.barrier .dmbSy` / `.dmbLd` merges `acqView` into `curView`. -/
def stepSailConfig {ue α : Type} (cfg : SailConfig ue α) :
    StepResult (SailConfig ue α) (α × BridgeMachineState) :=
  match cfg.term with
  | .pure v => .done (v, cfg.state)
  | .impure (.inl (.error _)) _ => .failed .ub
  | .impure (.inr n) k =>
      if _ : 0 < n then
        .choice .demonic (fun i : Fin n => { term := k i, state := cfg.state })
      else
        .failed .ub
  | .impure (.inl (.ok eff)) k =>
      match eff, k with
      | .regRead r none, k =>
          match cfg.state.readReg? r with
          | some v => .step { term := k v, state := cfg.state }
          | none => .failed .ub
      | .regRead _ (some _), _ => .failed .ub
      | .regWrite r none v, k =>
          .step { term := k (), state := cfg.state.writeReg r v }
      | .regWrite _ (some _) _, _ => .failed .ub
      | .memRead req, k =>
          if req.numTag != 0 || !req.accessKind.isExplicit then
            .failed .ub
          else
            let cands := cfg.state.mem.visibleAtomicMsgs cfg.state.curView req.address
            if _ : 0 < cands.length then
              .choice .demonic (fun i : Fin cands.length =>
                let msg := cands[i]
                let newCur := applyAtomicLoad cfg.state.curView req.accessKind msg
                let newAcq :=
                  if req.accessKind.isAcquire then View.join cfg.state.acqView msg.relView
                  else cfg.state.acqView
                { term := k (.ok msg.val)
                , state := { cfg.state with curView := newCur, acqView := newAcq } })
            else
              .failed .ub
      | .memWriteAnnounce _, k =>
          .step { term := k (), state := cfg.state }
      | .memWrite req val, k =>
          if req.numTag != 0 || !req.accessKind.isExplicit then
            .failed .ub
          else
            match cfg.state.mem.appendStore cfg.state.curView req.accessKind req.address val with
            | some (mem', view') =>
                .step { term := k (.ok ()), state := { cfg.state with mem := mem', curView := view' } }
            | none => .failed .ub
      | .barrier b, k =>
          let nextState :=
            match b with
            | .dmbSy | .dmbLd =>
                { cfg.state with curView := View.join cfg.state.curView cfg.state.acqView }
            | .dmbSt | .isb => cfg.state
          .step { term := k (), state := nextState }
      | .archException _, _ => .failed .ub
      | .returnException, _ => .failed .ub
      | .printMessage msg, k =>
          .step { term := k (), state := { cfg.state with output := msg :: cfg.state.output } }

def sailBridgeMachine (ue α : Type) (initState : BridgeMachineState) :
    SmallStepMachine (PreSailM ue α) (SailConfig ue α) (α × BridgeMachineState) where
  init := fun prog => { term := prog, state := initState }
  step := stepSailConfig

/-! ## Part 5: Mechanized Theorems -/

/-! ### Theorem 1: Unsoundness of `ArchSemSequential` on Demonic `undefined_*` (`FinChoice`) -/

/-- A Sail instruction model fragment that picks an `undefined_bit ()`
    (e.g., an architecturally `UNDEFINED` / `CONSTRAINED UNPREDICTABLE` bit)
    and asserts `b == 0#1` (or faults when `b == 1#1`). -/
def undefHazardProg : PreSailM Unit Unit := do
  let b ← undefined_bit ()
  sail_assert (b == 0#1) "undefined bit took non-zero value 1#1"

def emptySeqState : SequentialState where
  regs := fun _ => some 0#64
  mem := fun _ => none

def emptyBridgeState : BridgeMachineState where
  regs := fun _ => some 0#64
  curView := View.bot
  acqView := View.bot
  mem := { mapped := fun _ => false, atomicHistory := [] }

/-- 1A: `ArchSemSequential` deterministically succeeds on `undefHazardProg` because
    it hardcodes `FinChoice` to index `0` (`0#1`). -/
theorem archSemSeq_undefHazard_succeeds (s : SequentialState) :
    archSemSeqInterpret undefHazardProg s = .ok () s :=
  rfl

/-- 1B: `archsem-lean`'s `NEStateM` catches the assertion failure on branch `1` of
    `undefHazardProg`. -/
theorem archsemLean_undefHazard_has_error (s : SequentialState) :
    "SailError" ∈ (archsemLeanInterpret undefHazardProg s).errors := by
  have h : (archsemLeanInterpret undefHazardProg s).errors = ["SailError"] := rfl
  rw [h]
  exact List.Mem.head []

/-- 1C: Anneal's `StepResult` bridge (`sailBridgeMachine`) reaches `.failed .ub` on
    branch `⟨1, _⟩ : Fin 2` and therefore `undefHazardProg` is NOT `WellFormed`! -/
theorem stepResult_undefHazard_reaches_ub :
    ReachesPrefix stepSailConfig 2
      { term := undefHazardProg, state := emptyBridgeState }
      (.failed .ub) := by
  have h1 :
      stepSailConfig { term := undefHazardProg, state := emptyBridgeState } =
      .choice .demonic (fun i : Fin 2 =>
        { term := sail_assert (BitVec.ofNat 1 i.val == 0#1)
            "undefined bit took non-zero value 1#1"
        , state := emptyBridgeState }) := rfl
  refine ReachesPrefix.choice_demonic (⟨1, by decide⟩ : Fin 2) h1 ?_
  exact ReachesPrefix.failed rfl

theorem archSemSeq_unsound_for_demonic_undefined :
    (archSemSeqInterpret undefHazardProg emptySeqState = .ok () emptySeqState) ∧
    ("SailError" ∈ (archsemLeanInterpret undefHazardProg emptySeqState).errors) ∧
    ¬ (BehaviorOf (sailBridgeMachine Unit Unit emptyBridgeState) 2 undefHazardProg ≤
       WellFormed (Unit × BridgeMachineState)) := by
  refine ⟨archSemSeq_undefHazard_succeeds emptySeqState,
          archsemLean_undefHazard_has_error emptySeqState, ?_⟩
  intro hRef
  have hWf : (BehaviorOf (sailBridgeMachine Unit Unit emptyBridgeState) 2 undefHazardProg).wf :=
    hRef.1 trivial
  exact hWf stepResult_undefHazard_reaches_ub

/-! ### Theorem 2: Unsoundness of `ArchSemSequential` on `.archException` (`sail_take_exception`) -/

/-- A Sail instruction that raises an architectural fault via `sail_take_exception`
    before updating `R0` to `0xdead#64`. -/
def silentExnProg : PreSailM Unit Unit := do
  sail_take_exception ()
  writeReg .R0 0xdead#64

/-- `ArchSemSequential` silently ignores `.archException`, continues execution, and
    commits `R0 := 0xdead#64`, whereas `archsem-lean` and the Anneal `StepResult`
    bridge both reject the execution with an exception / UB failure. -/
theorem archSemSeq_unsound_for_silent_exception :
    (∃ s', archSemSeqInterpret silentExnProg emptySeqState = .ok () s' ∧
           s'.readReg? .R0 = some 0xdead#64) ∧
    ("Architecture exception" ∈ (archsemLeanInterpret silentExnProg emptySeqState).errors) ∧
    ReachesPrefix stepSailConfig 1
      { term := silentExnProg, state := emptyBridgeState }
      (.failed .ub) := by
  refine ⟨⟨emptySeqState.writeReg .R0 0xdead#64, rfl, rfl⟩, ?_, ?_⟩
  · have h : (archsemLeanInterpret silentExnProg emptySeqState).errors =
        ["Architecture exception"] := rfl
    rw [h]
    exact List.Mem.head []
  · exact ReachesPrefix.failed rfl

/-! ### Theorem 3: Weak-Memory Multi-Message Visibility vs. `ArchSemSequential` Collapse -/

/-- Address `0x1000` with two write messages in `Trusted.Memory`:
    - Timestamp 0: initial value `0#64` (release view `bot`)
    - Timestamp 1: concurrent release store of `42#64` with `relView = { 0x1000 ↦ 1 }` -/
def msgInit0 : AtomicMsg where
  addr := 0x1000
  val := 0#64
  timestamp := 0
  relView := View.bot

def msgStore42 : AtomicMsg where
  addr := 0x1000
  val := 42#64
  timestamp := 1
  relView := View.bot.bump 0x1000 1

def weakMemState : MemState where
  mapped := fun a => a == 0x1000
  atomicHistory := [msgStore42, msgInit0]

def unsyncBridgeState : BridgeMachineState where
  regs := fun _ => some 0#64
  curView := View.bot
  acqView := View.bot
  mem := weakMemState

def syncedBridgeState : BridgeMachineState where
  regs := fun _ => some 0#64
  curView := View.bot.bump 0x1000 1
  acqView := View.bot.bump 0x1000 1
  mem := weakMemState

def readAddr1000Prog : PreSailM Unit (Except Unit Word) :=
  sail_mem_read { address := 0x1000, accessKind := .explicitRelaxed, numTag := 0 }

/-- Before synchronization (`curView = View.bot`), both the new value `42#64` (index 0)
    and the stale value `0#64` (index 1) are reachable in Anneal's `StepResult` bridge. -/
theorem unsync_can_read_new_and_stale :
    (∃ s1, ReachesPrefix stepSailConfig 2
      { term := readAddr1000Prog, state := unsyncBridgeState }
      (.done (.ok 42#64, s1))) ∧
    (∃ s2, ReachesPrefix stepSailConfig 2
      { term := readAddr1000Prog, state := unsyncBridgeState }
      (.done (.ok 0#64, s2))) := by
  let branches : Fin 2 → SailConfig Unit (Except Unit Word) := fun i =>
    let cands := [msgStore42, msgInit0]
    let msg := cands[i]
    { term := .pure (.ok msg.val)
    , state := { unsyncBridgeState with
        curView := applyAtomicLoad unsyncBridgeState.curView .explicitRelaxed msg } }
  have hStep :
      stepSailConfig { term := readAddr1000Prog, state := unsyncBridgeState } =
      .choice .demonic branches := rfl
  constructor
  · refine ⟨(branches ⟨0, by decide⟩).state, ?_⟩
    exact ReachesPrefix.choice_demonic (⟨0, by decide⟩ : Fin 2) hStep (ReachesPrefix.done rfl)
  · refine ⟨(branches ⟨1, by decide⟩).state, ?_⟩
    exact ReachesPrefix.choice_demonic (⟨1, by decide⟩ : Fin 2) hStep (ReachesPrefix.done rfl)

/-! ### Theorem 4: General Demonic Choice & `WellFormed` Soundness for `StepResult` -/

/-- Inversion lemma for `StepResult.choice .demonic`: a demonic choice node reaches
    `out` in `n + 1` steps iff some branch `i` reaches `out` in `n` steps. -/
theorem reachesPrefix_choice_demonic_iff {State Obs : Type}
    {stepFn : State → StepResult State Obs} {n : Nat} {s : State}
    {ι : Type} {branches : ι → State} {out : PrefixOutcome Obs}
    (hStep : stepFn s = .choice .demonic branches) :
    ReachesPrefix stepFn (n + 1) s out ↔
    ∃ i : ι, ReachesPrefix stepFn n (branches i) out := by
  constructor
  · intro h
    cases h with
    | done hd => rw [hStep] at hd; cases hd
    | failed hf => rw [hStep] at hf; cases hf
    | step hs _ => rw [hStep] at hs; cases hs
    | choice_demonic i hc hsub =>
      rw [hStep] at hc
      injection hc with _ hType hBr
      subst hType
      cases hBr
      exact ⟨i, hsub⟩
    | choice_angelic_done _ hc _ => rw [hStep] at hc; cases hc
    | choice_angelic_all_failed _ _ hc _ => rw [hStep] at hc; cases hc
  · rintro ⟨i, hi⟩
    exact ReachesPrefix.choice_demonic i hStep hi

/-- After acquire/barrier synchronization (`curView.ts 0x1000 = 1`), the stale
    message `msgInit0` (`timestamp = 0 < 1`) is filtered out of `visibleAtomicMsgs`,
    so reading `0#64` is impossible under `ReachesPrefix`! -/
theorem synced_cannot_read_stale (s' : BridgeMachineState) :
    ¬ ReachesPrefix stepSailConfig 2
      { term := readAddr1000Prog, state := syncedBridgeState }
      (.done (.ok 0#64, s')) := by
  let branchesSynced : Fin 1 → SailConfig Unit (Except Unit Word) := fun i =>
    let cands := [msgStore42]
    let msg := cands[i]
    { term := .pure (.ok msg.val)
    , state := { syncedBridgeState with
        curView := applyAtomicLoad syncedBridgeState.curView .explicitRelaxed msg } }
  have hStepEq :
      stepSailConfig { term := readAddr1000Prog, state := syncedBridgeState } =
      .choice .demonic branchesSynced := rfl
  rw [reachesPrefix_choice_demonic_iff hStepEq]
  rintro ⟨i, hNext⟩
  match i with
  | ⟨0, hi⟩ =>
    have hStep2 :
        stepSailConfig (branchesSynced ⟨0, hi⟩) =
        .done (.ok 42#64, (branchesSynced ⟨0, hi⟩).state) := rfl
    cases hNext with
    | done hDone =>
      rw [hStep2] at hDone
      injection hDone with hPair
      injection hPair with hOk _
      injection hOk with hVal
      revert hVal
      decide
    | step hS _ =>
      rw [hStep2] at hS
      cases hS
    | choice_demonic _ hC _ =>
      rw [hStep2] at hC
      cases hC
    | choice_angelic_done _ hC _ =>
      rw [hStep2] at hC
      cases hC

/-- If a `SmallStepMachine` refines `WellFormed` at fuel `n + 1` from a demonic choice
    state, then EVERY branch `i : ι` is free of `.failed .ub` at fuel `n`. -/
theorem wellFormed_demonic_choice_all_branches_safe {State Obs : Type}
    {stepFn : State → StepResult State Obs} {n : Nat} {s : State}
    {ι : Type} {branches : ι → State}
    (hStep : stepFn s = .choice .demonic branches)
    (hSafe : ¬ ReachesPrefix stepFn (n + 1) s (.failed .ub)) :
    ∀ i : ι, ¬ ReachesPrefix stepFn n (branches i) (.failed .ub) := by
  intro i hUb
  exact hSafe (ReachesPrefix.choice_demonic i hStep hUb)

/-- Pure + choice + register subset of `PreSailM` (where memory/barrier effects are absent)
    to state the exact correspondence between `ArchSemSequential`, `archsem-lean`'s
    `NEStateM`, and Anneal's `StepResult` machine. -/
inductive IsChoiceRegOnly {ue α : Type} : PreSailM ue α → Prop where
  | pure (x : α) : IsChoiceRegOnly (.pure x)
  | error (err : SailError ue) (k : Empty → PreSailM ue α) :
      IsChoiceRegOnly (.impure (.inl (.error err)) k)
  | choice (n : Nat) (k : Fin n → PreSailM ue α) :
      (∀ i : Fin n, IsChoiceRegOnly (k i)) →
      IsChoiceRegOnly (.impure (.inr n) k)
  | regRead (r : Reg) (k : Word → PreSailM ue α) :
      (∀ v : Word, IsChoiceRegOnly (k v)) →
      IsChoiceRegOnly (.impure (.inl (.ok (.regRead r none))) k)
  | regWrite (r : Reg) (v : Word) (k : Unit → PreSailM ue α) :
      IsChoiceRegOnly (k ()) →
      IsChoiceRegOnly (.impure (.inl (.ok (.regWrite r none v))) k)

/-- State correspondence between `SequentialState` and `BridgeMachineState` on registers. -/
def RegStateAgrees (sSeq : SequentialState) (sBridge : BridgeMachineState) : Prop :=
  ∀ r : Reg, sSeq.regs r = sBridge.regs r

theorem regStateAgrees_write (sSeq : SequentialState) (sBridge : BridgeMachineState)
    (r : Reg) (v : Word) (h : RegStateAgrees sSeq sBridge) :
    RegStateAgrees (sSeq.writeReg r v) (sBridge.writeReg r v) := by
  intro r'
  simp only [SequentialState.writeReg, BridgeMachineState.writeReg]
  split
  · rfl
  · exact h r'

/-- Soundness Theorem (`neStateM_error_implies_stepResult_ub`):
    For any `IsChoiceRegOnly` Sail computation `m`, if `archsem-lean`'s `NEStateM`
    interpreter produces an error in `(archsemLeanInterpret m sSeq).errors`, then
    there exists a finite fuel `fuel` such that Anneal's `StepResult` machine
    reaches `PrefixOutcome.failed .ub` from any register-agreeing `sBridge`. -/
theorem neStateM_error_implies_stepResult_ub {ue α : Type}
    {m : PreSailM ue α} (hm : IsChoiceRegOnly m) :
    ∀ {sSeq : SequentialState} {sBridge : BridgeMachineState} {err : String},
      RegStateAgrees sSeq sBridge →
      err ∈ (archsemLeanInterpret m sSeq).errors →
      ∃ fuel : Nat,
        ReachesPrefix stepSailConfig fuel { term := m, state := sBridge } (.failed .ub) := by
  induction hm with
  | pure x =>
    intro sSeq sBridge err _ hErr
    cases hErr
  | error e k =>
    intro sSeq sBridge err _ _
    exact ⟨1, ReachesPrefix.failed rfl⟩
  | choice n k _ ih =>
    intro sSeq sBridge err hAgree hErr
    change err ∈ (NEStateM.bind (NEStateM.chooseFin n)
      (fun i => archsemLeanInterpret (k i)) sSeq).errors at hErr
    rw [NEStateM.mem_bind_errors] at hErr
    rcases hErr with hErr0 | ⟨sSeq', i, hInOks, hSubErr⟩
    · cases hErr0
    · simp only [NEStateM.chooseFin, List.mem_map] at hInOks
      rcases hInOks with ⟨j, _, hPair⟩
      injection hPair with hSt hIdx
      subst hSt hIdx
      have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
      rcases ih j hAgree hSubErr with ⟨fuel, hReach⟩
      refine ⟨fuel + 1, ?_⟩
      have hStep :
          stepSailConfig { term := .impure (.inr n) k, state := sBridge } =
          .choice .demonic (fun idx : Fin n => { term := k idx, state := sBridge }) := by
        simp [stepSailConfig, hn]
      exact ReachesPrefix.choice_demonic j hStep hReach
  | regRead r k _ ih =>
    intro sSeq sBridge err hAgree hErr
    change err ∈ (NEStateM.bind (archsemLeanInterpretEffect (.regRead r none))
      (fun v => archsemLeanInterpret (k v)) sSeq).errors at hErr
    rw [NEStateM.mem_bind_errors] at hErr
    have hRegEq : sSeq.readReg? r = sBridge.readReg? r := hAgree r
    cases hReg : sSeq.readReg? r with
    | none =>
      have hBridgeNone : sBridge.readReg? r = none := by rw [← hRegEq, hReg]
      refine ⟨1, ?_⟩
      apply ReachesPrefix.failed
      simp [stepSailConfig, hBridgeNone]
    | some v =>
      have hBridgeSome : sBridge.readReg? r = some v := by rw [← hRegEq, hReg]
      simp only [archsemLeanInterpretEffect, hReg] at hErr
      rcases hErr with hErr0 | ⟨sSeq', v', hInOks, hSubErr⟩
      · cases hErr0
      · simp only [List.mem_singleton] at hInOks
        injection hInOks with hSt hVal
        cases hSt
        cases hVal
        rcases ih v hAgree hSubErr with ⟨fuel, hReach⟩
        refine ⟨fuel + 1, ?_⟩
        apply ReachesPrefix.step _ hReach
        simp [stepSailConfig, hBridgeSome]
  | regWrite r v k _ ih =>
    intro sSeq sBridge err hAgree hErr
    change err ∈ (NEStateM.bind (archsemLeanInterpretEffect (.regWrite r none v))
      (fun u => archsemLeanInterpret (k u)) sSeq).errors at hErr
    rw [NEStateM.mem_bind_errors] at hErr
    simp only [archsemLeanInterpretEffect, NEStateM.modify] at hErr
    rcases hErr with hErr0 | ⟨sSeq', u, hInOks, hSubErr⟩
    · cases hErr0
    · simp only [List.mem_singleton] at hInOks
      injection hInOks with hSt hUnit
      subst hSt hUnit
      have hAgree' := regStateAgrees_write sSeq sBridge r v hAgree
      rcases ih hAgree' hSubErr with ⟨fuel, hReach⟩
      refine ⟨fuel + 1, ?_⟩
      apply ReachesPrefix.step _ hReach
      simp [stepSailConfig]

/-- Contrapositive Corollary (`stepResult_wellFormed_excludes_neStateM_error`):
    If the Anneal `StepResult` machine is UB-free (`WellFormed`) at all finite fuels,
    then `archsem-lean`'s `NEStateM` cannot produce any error on any nondeterministic branch. -/
theorem stepResult_wellFormed_excludes_neStateM_error {ue α : Type}
    {m : PreSailM ue α} (hm : IsChoiceRegOnly m)
    {sSeq : SequentialState} {sBridge : BridgeMachineState}
    (hAgree : RegStateAgrees sSeq sBridge)
    (hWf : ∀ fuel : Nat,
      (BehaviorOf (sailBridgeMachine ue α sBridge) fuel m).wf) :
    (archsemLeanInterpret m sSeq).errors = [] := by
  cases hErrs : (archsemLeanInterpret m sSeq).errors with
  | nil => rfl
  | cons err rest =>
    have hIn : err ∈ (archsemLeanInterpret m sSeq).errors := by simp [hErrs]
    rcases neStateM_error_implies_stepResult_ub hm hAgree hIn with ⟨fuel, hUb⟩
    exact False.elim (hWf fuel hUb)

/-- Inclusion Theorem (`archSemSeq_ok_in_stepResult_behavior`):
    Whenever `ArchSemSequential` succeeds with `.ok val sSeq'`, there exists a finite
    fuel `fuel` and a corresponding `sBridge'` (agreeing on all registers with `sSeq'`)
    such that `(val, sBridge')` is in the `.val` set of Anneal's `StepResult` behavior! -/
theorem archSemSeq_ok_in_stepResult_behavior {ue α : Type}
    {m : PreSailM ue α} (hm : IsChoiceRegOnly m) :
    ∀ {sSeq sSeq' : SequentialState} {sBridge : BridgeMachineState} {val : α},
      RegStateAgrees sSeq sBridge →
      archSemSeqInterpret m sSeq = .ok val sSeq' →
      ∃ (fuel : Nat) (sBridge' : BridgeMachineState),
        RegStateAgrees sSeq' sBridge' ∧
        (BehaviorOf (sailBridgeMachine ue α sBridge) fuel m).val (val, sBridge') := by
  induction hm with
  | pure x =>
    intro sSeq sSeq' sBridge val hAgree hOk
    injection hOk with hVal hSt
    subst hVal hSt
    refine ⟨1, sBridge, hAgree, ?_⟩
    exact ReachesPrefix.done rfl
  | error e k =>
    intro sSeq sSeq' sBridge val _ hOk
    cases hOk
  | choice n k _ ih =>
    intro sSeq sSeq' sBridge val hAgree hOk
    unfold archSemSeqInterpret FreeM.liftM at hOk
    dsimp [bind, EStateM.bind] at hOk
    by_cases hn : 0 < n
    · simp only [hn, ↓reduceDIte] at hOk
      change archSemSeqInterpret (k ⟨0, hn⟩) sSeq = .ok val sSeq' at hOk
      rcases ih ⟨0, hn⟩ hAgree hOk with ⟨fuel, sBridge', hAgree', hReach⟩
      change ReachesPrefix stepSailConfig fuel
        { term := k ⟨0, hn⟩, state := sBridge } (.done (val, sBridge')) at hReach
      refine ⟨fuel + 1, sBridge', hAgree', ?_⟩
      change ReachesPrefix stepSailConfig (fuel + 1)
        { term := .impure (.inr n) k, state := sBridge } (.done (val, sBridge'))
      have hStep :
          stepSailConfig { term := .impure (.inr n) k, state := sBridge } =
          .choice .demonic (fun idx : Fin n => { term := k idx, state := sBridge }) := by
        simp [stepSailConfig, hn]
      exact ReachesPrefix.choice_demonic ⟨0, hn⟩ hStep hReach
    · simp only [hn, ↓reduceDIte] at hOk
      cases hOk
  | regRead r k _ ih =>
    intro sSeq sSeq' sBridge val hAgree hOk
    unfold archSemSeqInterpret FreeM.liftM at hOk
    dsimp [bind, EStateM.bind, archSemSeqInterpretEffect] at hOk
    have hRegEq : sSeq.readReg? r = sBridge.readReg? r := hAgree r
    cases hReg : sSeq.readReg? r with
    | none =>
      rw [hReg] at hOk
      cases hOk
    | some v =>
      have hBridgeSome : sBridge.readReg? r = some v := by rw [← hRegEq, hReg]
      rw [hReg] at hOk
      change archSemSeqInterpret (k v) sSeq = .ok val sSeq' at hOk
      rcases ih v hAgree hOk with ⟨fuel, sBridge', hAgree', hReach⟩
      refine ⟨fuel + 1, sBridge', hAgree', ?_⟩
      change ReachesPrefix stepSailConfig (fuel + 1)
        { term := .impure (.inl (.ok (.regRead r none))) k, state := sBridge }
        (.done (val, sBridge'))
      have hStep :
          stepSailConfig { term := .impure (.inl (.ok (.regRead r none))) k, state := sBridge } =
          .step { term := k v, state := sBridge } := by
        simp [stepSailConfig, hBridgeSome]
      exact ReachesPrefix.step hStep hReach
  | regWrite r v k _ ih =>
    intro sSeq sSeq' sBridge val hAgree hOk
    unfold archSemSeqInterpret FreeM.liftM at hOk
    dsimp [bind, EStateM.bind, archSemSeqInterpretEffect] at hOk
    change archSemSeqInterpret (k ()) (sSeq.writeReg r v) = .ok val sSeq' at hOk
    have hAgree' := regStateAgrees_write sSeq sBridge r v hAgree
    rcases ih hAgree' hOk with ⟨fuel, sBridge', hAgree'', hReach⟩
    refine ⟨fuel + 1, sBridge', hAgree'', ?_⟩
    change ReachesPrefix stepSailConfig (fuel + 1)
      { term := .impure (.inl (.ok (.regWrite r none v))) k, state := sBridge }
      (.done (val, sBridge'))
    have hStep :
        stepSailConfig { term := .impure (.inl (.ok (.regWrite r none v))) k, state := sBridge } =
        .step { term := k (), state := sBridge.writeReg r v } := rfl
    exact ReachesPrefix.step hStep hReach

/-! ## Axiom & Guard Verification -/

/-- info: 'SailArchSemBridgeProbe.FreeM.instLawfulMonad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FreeM.instLawfulMonad

/-- info: 'SailArchSemBridgeProbe.archSemSeq_unsound_for_demonic_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms archSemSeq_unsound_for_demonic_undefined

/-- info: 'SailArchSemBridgeProbe.archSemSeq_unsound_for_silent_exception' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms archSemSeq_unsound_for_silent_exception

/-- info: 'SailArchSemBridgeProbe.unsync_can_read_new_and_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unsync_can_read_new_and_stale

/-- info: 'SailArchSemBridgeProbe.synced_cannot_read_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms synced_cannot_read_stale

/-- info: 'SailArchSemBridgeProbe.stepResult_wellFormed_excludes_neStateM_error' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepResult_wellFormed_excludes_neStateM_error

/-- info: 'SailArchSemBridgeProbe.archSemSeq_ok_in_stepResult_behavior' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms archSemSeq_ok_in_stepResult_behavior

end SailArchSemBridgeProbe
