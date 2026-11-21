import ToyTailCall.Machine

/-!
# Stack borrows at tail calls: the dynamic hypothesis and a static escape check
-/

namespace Toy.TailCall

/-- A bounded walk over a run checking `pred` on every running state; `false` if the fuel
runs out before the run halts. -/
def allRunning (pred : State → Bool) (sem : Sem) (D : Option Nat) (p : Prog) :
    Nat → Conf → Bool
  | _, .halted _ => true
  | 0, .running _ => false
  | n + 1, .running st => pred st && allRunning pred sem D p n (step sem D p st)

/-- Soundness of the bounded checker: a `true` verdict covers every running state of the run,
at every step count. -/
theorem allRunning_sound (pred : State → Bool) (sem : Sem) (D : Option Nat) (p : Prog) :
    ∀ (N : Nat) (c : Conf), allRunning pred sem D p N c = true →
      ∀ n st, run sem D p n c = .running st → pred st = true := by
  intro N
  induction N with
  | zero =>
    intro c h n st hrun
    cases c with
    | halted r => rw [run_halted] at hrun; cases hrun
    | running s => simp [allRunning] at h
  | succ N ih =>
    intro c h n st hrun
    cases c with
    | halted r => rw [run_halted] at hrun; cases hrun
    | running s =>
      simp only [allRunning, Bool.and_eq_true] at h
      cases n with
      | zero => simp only [run, Conf.running.injEq] at hrun; subst hrun; exact h.1
      | succ m => exact ih _ h.2 m st hrun

/-- `v` is a pointer into the frame with identity `fid`. -/
def Val.pointsInto (fid : Nat) : Val → Bool
  | .ptr f _ => f == fid
  | _ => false

/-- The running state is about to execute a `tailCall` one of whose evaluated arguments is a
pointer into the current frame. -/
def tailCallBorrowsFrame (p : Prog) (st : State) : Bool :=
  match st.stack with
  | [] => false
  | fr :: rest =>
    if st.unwinding || fr.pendingRet.isSome then false else
    match p.fns[fr.fn]? with
    | none => false
    | some fn =>
      match fn.code[fr.pc]? with
      | some (.tailCall _ args) =>
        match evalOps rest fr args with
        | some (vs, _) => vs.any (Val.pointsInto fr.fid)
        | none => false
      | _ => false

/-- **H-noStackBorrow** (dynamic). In the unbounded `preJump` run of `p`, no executed
`tailCall` passes an argument that points into the current frame.

The toy has no heap and no store through pointers, so the callee can reach the current
frame only through its argument values: every other value a callee can load lies in a frame
below the current one, and such frames receive values from the current frame only when it
returns (not proved here). The predicate therefore inspects argument values only. -/
def NoStackBorrow (p : Prog) : Prop :=
  ∀ n st, run .preJump none p n (start none p) = .running st → tailCallBorrowsFrame p st = false

/-- A finite certificate for `NoStackBorrow`: the `preJump` run halts within `N` steps and no
running state on the way borrows the frame at a tail call. -/
theorem noStackBorrow_of_allRunning (p : Prog) (N : Nat)
    (h : allRunning (fun st => !tailCallBorrowsFrame p st) .preJump none p N (start none p) = true) :
    NoStackBorrow p := by
  intro n st hrun
  have := allRunning_sound _ _ _ _ N _ h n st hrun
  simpa using this

/-! ### A static escape check -/

/-- An operand is tainted (may yield a pointer into the current frame) if it takes an address
or reads a tainted slot. -/
def opTainted (T : List Bool) : Operand → Bool
  | .const _ => false
  | .addrOf _ => true
  | .copy s => T.getD s false
  | .move s => T.getD s false
  | .deref s => T.getD s false
  | .succ s => T.getD s false

/-- One round of flow-insensitive taint propagation: a slot becomes tainted when some
`assign` writes a tainted operand into it, or some `call` with a tainted argument stores its
result into it. The check is intra-procedural: a `call` taints its destination slot and
nothing else. That is adequate in this toy, which has no stores through pointers (so no
out-parameters), no heap or global state and no compound values; it is not offered as an
analysis for languages that have them. -/
def taintStep (fn : Fn) (T : List Bool) : List Bool :=
  (List.range fn.nSlots).map fun d =>
    T.getD d false || fn.code.any fun i =>
      match i with
      | .assign d' op _ => d' == d && opTainted T op
      | .call _ args d' _ => d' == d && args.any (opTainted T)
      | _ => false

/-- Tainted slots of `fn`: `nSlots + 1` rounds of `taintStep` from "nothing tainted"
(parameters start untainted: they are written by the caller before the frame exists). -/
def taint (fn : Fn) : List Bool :=
  Nat.repeat (taintStep fn) (fn.nSlots + 1) (List.replicate fn.nSlots false)

/-- The escape check for one function: no `tailCall` argument is tainted. -/
def EscapeCheckFn (fn : Fn) : Bool :=
  fn.code.all fun i =>
    match i with
    | .tailCall _ args => !(args.any (opTainted (taint fn)))
    | _ => true

/-- The escape check accepts `p` (a static verdict; compare the semantic `NoStackBorrow`). -/
def EscapeCheckAccepts (p : Prog) : Bool := p.fns.all EscapeCheckFn

end Toy.TailCall
