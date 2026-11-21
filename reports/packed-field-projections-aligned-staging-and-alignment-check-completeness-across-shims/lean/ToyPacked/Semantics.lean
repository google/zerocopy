import ToyPacked.Basic

/-!
# Toy programs, synthesized shims, staging, instrumentation, and the two semantics

* A program has one source body (a straight-line list of operations) over typed locals placed at
  given base addresses. Synthesized shims are generated from the type environment: for every type
  id `t`, a drop-glue shim and a clone shim, and for every owning-pointer (`box`) type a box-free
  shim, each taking a raw pointer (`shimExists`). Calling a shim that does not exist is a no-op.
* In this toy, reference creation is the alignment-relevant operation: it occurs at op `0` of
  every existing shim (`&mut *self` / `&*self` from the incoming raw pointer) and at user-written
  `rawRef` source ops. Loads and stores through raw pointers are not modelled (`readUnaligned` and
  `moveOut` are no-ops).
* Compiler-generated reference-taking operations (`comp`: drop of a place, freeing a box through
  a reference to the box field, cloning a place) call the shim of their kind on the place's
  address; with *aligned staging* they first move/copy the place to a temporary and call the
  shim on the temporary instead.
* *Ideal* semantics: alignment-oblivious, every reference creation succeeds.
  *Reference* semantics: a reference created at a misaligned address is a UB event, unless an
  inserted dynamic check traps first. Both events end the run.
-/

namespace Toy.Packed

/-- A place: a base local plus a projection path of field indices. -/
structure Place where
  root : Nat
  path : List Nat
  deriving DecidableEq, Repr

/-- Kinds of synthesized shims (and of the compiler operations that call them). -/
inductive ShimKind where
  | dropGlue
  | boxFree
  | clone
  deriving DecidableEq, Repr

/-- Bodies: the source body, or the shim of a given kind for a given type id. -/
inductive BodyId where
  | src
  | shim (k : ShimKind) (t : Nat)
  deriving DecidableEq, Repr

/-- Source operations.
* `comp k p`: compiler-generated reference-taking operation on place `p` (`dropGlue`: drop `p`;
  `boxFree`: free the box at `p` after its pointee was moved out; `clone`: clone `p`).
* `moveOut p`: deref-move out of the box at `p` (a by-value access; creates no reference).
* `readUnaligned t a`: an unaligned read through a raw pointer (no alignment requirement).
* `rawRef t a`: user-written `&*ptr` for a raw pointer with address `a` and pointee type `t`.
* `rawCall k t a`: unsafe client code calls shim `k` for type `t` with a raw pointer `a`. -/
inductive Op where
  | comp (k : ShimKind) (p : Place)
  | moveOut (p : Place)
  | readUnaligned (t a : Nat)
  | rawRef (t a : Nat)
  | rawCall (k : ShimKind) (t a : Nat)
  deriving DecidableEq, Repr

/-- A toy program: environment, layout, local types, local base addresses, source body. -/
structure Prog where
  env : Env
  layout : Layout
  locals : List Nat
  frame : List Nat
  src : List Op

/-- Where a value name comes from: a local, or the raw pointer passed by source op `i`. -/
inductive Origin where
  | loc (x : Nat)
  | raw (i : Nat)
  deriving DecidableEq, Repr

/-- Address-independent names of values (origin plus path; a box pointee extends the box's
path with `0`). Destructor events carry names, so they identify values, not addresses. -/
structure VName where
  origin : Origin
  path : List Nat
  deriving DecidableEq, Repr

/-- The name of sub-value `j`. -/
def VName.child (n : VName) (j : Nat) : VName := ⟨n.origin, n.path ++ [j]⟩

/-- Trace events. `dtor`, `addrObs`, `free`, `cloned` are observable effects; `copy` is the cost
of a staging move/copy (not observable); `stuck`, `ub`, `trap`, `outOfFuel` end a run. -/
inductive Ev where
  | dtor (n : VName)
  | addrObs (n : VName) (a : Nat)
  | free (n : VName)
  | cloned (n : VName)
  | copy (n : VName)
  | stuck (b : BodyId) (i : Nat)
  | ub (b : BodyId) (i : Nat)
  | trap (b : BodyId) (i : Nat)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Is this a UB event? -/
def Ev.isUB : Ev → Bool
  | .ub _ _ => true
  | _ => false

/-- Is this a UB event inside a shim? -/
def Ev.isShimUB : Ev → Bool
  | .ub (.shim _ _) _ => true
  | _ => false

/-- The observable projection of a trace: drop the staging-cost events. -/
def obs (evs : List Ev) : List Ev :=
  evs.filter fun e => match e with
    | .copy _ => false
    | _ => true

/-- Number of staging moves/copies in a trace. -/
def copies (evs : List Ev) : Nat :=
  (evs.filter fun e => match e with
    | .copy _ => true
    | _ => false).length

/-- A staging criterion: given the operation kind, the base alignment, the base type and the
projection path of the operated place, decide whether to stage. -/
abbrev Crit := ShimKind → Nat → Nat → List Nat → Bool

/-- Configuration: staging criterion, temporary addresses per (body, op), and the
instrumentation policy (the set of (body, op) pairs at which an alignment check is inserted). -/
structure Cfg where
  crit : Crit
  tmp : BodyId → Nat → Nat
  instr : BodyId → Nat → Bool

/-- The two semantics. -/
inductive Mode where
  | ideal
  | ref
  deriving DecidableEq, Repr

/-- A (partial) run outcome: the events so far, and whether execution continues. -/
structure Out where
  evs : List Ev
  ok : Bool
  deriving DecidableEq, Repr

/-- Sequencing: run the continuation only if execution continues. -/
def Out.andThen (o : Out) (f : Unit → Out) : Out :=
  if o.ok then
    let o' := f ()
    { evs := o.evs ++ o'.evs, ok := o'.ok }
  else o

/-- Does a value of type `t` need drop glue (a destructor or a box somewhere inside)? Beyond the
fuel bound (reachable only in cyclic environments) the answer is `false`, so the answer is
monotone in the fuel. -/
def needsDrop (env : Env) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, t =>
    match (env.ty t).kind with
    | .scalar => false
    | .res _ => true
    | .box _ => true
    | .agg _ fs => fs.any fun f => needsDrop env fuel f

/-- No address-observing destructor is reachable in the drop glue of `t` through inline
sub-values, that is, sub-values that move with `t` when `t` is moved. A box's pointee does not
move with the box (it stays at its heap address), so `box` is address-blind whatever its pointee
is. -/
def AddrBlind (env : Env) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, t =>
    match (env.ty t).kind with
    | .scalar => true
    | .res obs => !obs
    | .box _ => true
    | .agg _ fs => fs.all fun f => AddrBlind env fuel f

/-- The heap address of a box pointee of type `p` (aligned for `p`). -/
def heapAddr (env : Env) (p : Nat) : Nat := env.align p

/-- One reference creation with required alignment `n` at address `a`, at op `i` of body `b`.
A check inserted by the policy traps iff the address is misaligned. -/
def refStep (m : Mode) (cfg : Cfg) (b : BodyId) (i n a : Nat) : Out :=
  match m with
  | .ideal => ⟨[], true⟩
  | .ref =>
    if n ∣ a then ⟨[], true⟩
    else if cfg.instr b i then ⟨[.trap b i], false⟩ else ⟨[.ub b i], false⟩

/-- Does shim `k` exist for type id `t`? Drop glue and clone shims exist for every type id; a
box-free shim exists for owning-pointer types only. -/
def shimExists (env : Env) : ShimKind → Nat → Bool
  | .boxFree, t => env.isBox t
  | _, _ => true

/-- Does a compiler-generated operation of kind `k` on a value of type `u` call a shim? A drop of
a type without drop glue and a free of a non-box type call none (they are no-ops). -/
def callsShim (env : Env) (fuel : Nat) : ShimKind → Nat → Bool
  | .dropGlue, u => needsDrop env fuel u
  | k, u => shimExists env k u

/-- A compiler-generated operation of kind `k` at op `i` of body `b` on a place with base
alignment `A`, base type `t0`, path `path`, type `u`, address `a` and value name `n`; `call`
runs the callee shim. Operations that call no shim (`callsShim`) are no-ops. If the criterion
stages the place, the value is moved (copied, for `clone`) to the temporary `cfg.tmp b i` and the
shim runs there, with no write-back to the place; an unsized value cannot be moved to a temporary
of statically known size, which the toy records as the run-ending event `stuck` (a compile-time
rejection, not UB). -/
def compStep (call : Nat → Nat → VName → Out) (env : Env) (fuel : Nat) (cfg : Cfg)
    (k : ShimKind) (b : BodyId) (i A t0 : Nat) (path : List Nat) (u a : Nat) (n : VName) : Out :=
  if callsShim env fuel k u then
    if cfg.crit k A t0 path then
      if (env.ty u).sized then (Out.mk [.copy n] true).andThen fun _ => call u (cfg.tmp b i) n
      else ⟨[.stuck b i], false⟩
    else call u a n
  else ⟨[], true⟩

/-- Run a sequence of field operations, stopping at the first event that ends the run. -/
def seqFields (fs : List Nat) (step : Nat → Nat → Out) : Out :=
  fs.zipIdx.foldl (fun acc p => acc.andThen fun _ => step p.1 p.2) ⟨[], true⟩

/-- Run shim `k` for type `t` on a raw pointer with address `a` (value name `n`); a no-op if the
shim does not exist. Op `0` creates `&mut *self` (`&*self` for `clone`); op `j + 1` of an
aggregate's drop glue (clone shim) is the compiler-generated drop (clone) of field `j`. A box's
pointee is dropped at its heap address `heapAddr env p`, whatever the box's own address. -/
def runShim (m : Mode) (cfg : Cfg) (env : Env) (L : Layout) :
    Nat → ShimKind → Nat → Nat → VName → Out
  | 0, _, _, _, _ => ⟨[.outOfFuel], false⟩
  | fuel + 1, k, t, a, n =>
    if shimExists env k t then
    (refStep m cfg (.shim k t) 0 (env.align t) a).andThen fun _ =>
    match k, (env.ty t).kind with
    | .dropGlue, .scalar => ⟨[], true⟩
    | .dropGlue, .res obs => ⟨(if obs then [.addrObs n a] else []) ++ [.dtor n], true⟩
    | .dropGlue, .box p =>
      (if needsDrop env fuel p then
        runShim m cfg env L fuel .dropGlue p (heapAddr env p) (n.child 0)
      else ⟨[], true⟩).andThen fun _ => ⟨[.free n], true⟩
    | .dropGlue, .agg _ fs =>
      seqFields fs fun f j =>
        compStep (fun u a' n' => runShim m cfg env L fuel .dropGlue u a' n') env fuel cfg
          .dropGlue (.shim .dropGlue t) (j + 1) (env.align t) t [j] f (a + L t j) (n.child j)
    | .boxFree, _ => ⟨[.free n], true⟩
    | .clone, .agg _ fs =>
      seqFields fs fun f j =>
        compStep (fun u a' n' => runShim m cfg env L fuel .clone u a' n') env fuel cfg
          .clone (.shim .clone t) (j + 1) (env.align t) t [j] f (a + L t j) (n.child j)
    | .clone, _ => ⟨[.cloned n], true⟩
    else ⟨[], true⟩

/-- Fuel for shim nesting: enough for acyclic environments. -/
def Prog.fuel (P : Prog) : Nat := P.env.length + 1

/-- Resolve a source place: (base alignment, base type, place type, address). `none` if the
root is not a local or the path does not follow the types. A local without a `frame` entry is
placed at address `0` (aligned for every alignment, including `0`). -/
def Prog.place (P : Prog) (p : Place) : Option (Nat × Nat × Nat × Nat) :=
  if p.root < P.locals.length then
    let t0 := P.locals.getD p.root 0
    match resolve P.env P.layout t0 p.path with
    | some (u, o) => some (P.env.align t0, t0, u, P.frame.getD p.root 0 + o)
    | none => none
  else none

/-- Run source op `i`. Ill-formed places are skipped. `moveOut` and `readUnaligned` are no-ops
(the toy tracks neither ownership nor memory contents), and a `rawCall` site has no check of its
own: `cfg.instr .src i` is consulted at `rawRef` only. -/
def srcStep (m : Mode) (cfg : Cfg) (P : Prog) (i : Nat) : Op → Out
  | .comp k p =>
    match P.place p with
    | some (A, t0, u, a) =>
      compStep (fun u' a' n' => runShim m cfg P.env P.layout P.fuel k u' a' n') P.env P.fuel cfg
        k .src i A t0 p.path u a ⟨.loc p.root, p.path⟩
    | none => ⟨[], true⟩
  | .moveOut _ => ⟨[], true⟩
  | .readUnaligned _ _ => ⟨[], true⟩
  | .rawRef t a => refStep m cfg .src i (P.env.align t) a
  | .rawCall k t a => runShim m cfg P.env P.layout P.fuel k t a ⟨.raw i, []⟩

/-- The run of a program (the toy semantics is deterministic: one run per program). -/
def run (m : Mode) (cfg : Cfg) (P : Prog) : Out :=
  P.src.zipIdx.foldl (fun acc p => acc.andThen fun _ => srcStep m cfg P p.2 p.1) ⟨[], true⟩

/-- No UB event occurs in the run. Among the runs satisfying it are runs with no misaligned
reference creation and runs that end with `trap`, `stuck` or `outOfFuel` before any UB event. -/
def NoUB (o : Out) : Prop := ∀ e, e ∈ o.evs → e.isUB = false

instance (o : Out) : Decidable (NoUB o) := by unfold NoUB; infer_instance

/-- No UB event occurs inside a shim. -/
def NoShimUB (o : Out) : Prop := ∀ e, e ∈ o.evs → e.isShimUB = false

instance (o : Out) : Decidable (NoShimUB o) := by unfold NoShimUB; infer_instance

/-- Is this a `stuck` event (an unsized value was to be staged)? -/
def Ev.isStuck : Ev → Bool
  | .stuck _ _ => true
  | _ => false

/-- No `stuck` event occurs in the run. -/
def NoStuck (o : Out) : Prop := ∀ e, e ∈ o.evs → e.isStuck = false

instance (o : Out) : Decidable (NoStuck o) := by unfold NoStuck; infer_instance

end Toy.Packed
