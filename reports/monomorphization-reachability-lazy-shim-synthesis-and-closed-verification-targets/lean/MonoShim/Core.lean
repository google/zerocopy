/-!
# Toy monomorphization model: syntax and the shared interpreter

Everything in this package is a toy model of a Rust-style compiler pipeline. Types, programs and
statements are deliberately small; see the doc comment of each definition for the real notion it
is meant to capture.
-/

namespace Toy.MonoShim

/-- Toy types: `base n` is a nominal leaf type (it may carry a user `Drop` or `Clone` impl),
`box τ` an owning pointer, `pair a b` a two-field tuple, `dyn tr` a trait object type,
`fnPtr` a function-pointer type, `param i` the `i`-th type parameter of a generic function,
and `proj tr τ` the associated-type projection `<τ as tr>::Out`. -/
inductive Ty where
  | base : Nat → Ty
  | box : Ty → Ty
  | pair : Ty → Ty → Ty
  | dyn : Nat → Ty
  | fnPtr : Ty
  | param : Nat → Ty
  | proj : Nat → Ty → Ty
  deriving DecidableEq, Repr

/-- Symbol keys of the monomorphic program (the analogue of mono items / instances).
`inst f τs` is the instance `f::<τs>`; `meth tr m τ` is `<τ as tr>::m`; `userDrop n` and
`userClone n` are the user `Drop::drop` / `Clone::clone` bodies of `base n`; `dropGlue τ`,
`cloneShim τ` and `reifyShim f τs` are compiler-synthesized shims (drop glue, the builtin
tuple-like `Clone`, and the function-pointer shim of a `trackCaller` function). -/
inductive Key where
  | inst : Nat → List Ty → Key
  | meth : Nat → Nat → Ty → Key
  | userDrop : Nat → Key
  | userClone : Nat → Key
  | dropGlue : Ty → Key
  | cloneShim : Ty → Key
  | reifyShim : Nat → List Ty → Key
  deriving DecidableEq, Repr

/-- Shim keys are the keys whose bodies come from the synthesizer, not from source text. -/
def Key.isShim : Key → Bool
  | .dropGlue _ => true
  | .cloneShim _ => true
  | .reifyShim _ _ => true
  | _ => false

/-- Statements. Calls carry no value arguments; frames hold the function pointers and trait
objects created by `reify` and `unsize`. `onUnwind s c` runs `s` and, if `s` unwinds, runs the
cleanup `c` (a panic inside the cleanup aborts). `cloneAgg ts` is the source-level aggregate
"clone every field left to right" (the tuple expression `(x.0.clone(), x.1.clone(), …)`).
`guard s` runs `s` when the global counter is nonzero (decrementing it first) and skips otherwise: it is the
value guard used to make polymorphic recursion terminate at run time. `invoke k` calls a key
directly (synthesized shims use it, e.g. drop glue calling a user `Drop::drop`). -/
inductive Stmt where
  | skip : Stmt
  | seq : Stmt → Stmt → Stmt
  | emit : Nat → Stmt
  | panic : Stmt
  | call : Nat → List Ty → Stmt
  | invoke : Key → Stmt
  | mcall : Nat → Nat → Ty → Stmt
  | drop : Ty → Stmt
  | clone : Ty → Stmt
  | reify : Nat → Nat → List Ty → Stmt
  | callPtr : Nat → Stmt
  | unsize : Nat → Ty → Nat → Stmt
  | callDyn : Nat → Nat → Stmt
  | dropDyn : Nat → Stmt
  | onUnwind : Stmt → Stmt → Stmt
  | cloneAgg : List Ty → Stmt
  | guard : Stmt → Stmt
  deriving DecidableEq, Repr

/-- A generic function definition: body over `param i`, plus the `trackCaller` flag. -/
structure FnDef where
  trackCaller : Bool
  body : Stmt
  deriving Repr

/-- One impl-table entry `impl tr for ty { fn m() { body } }`, for a concrete `ty`. -/
structure ImplEntry where
  tr : Nat
  m : Nat
  ty : Ty
  body : Stmt
  deriving Repr

/-- A toy program: function `f` is `fns[f]`; `methods` lists the (dyn-compatible) methods of each
trait; `impls` is the impl table; `dropImpls`/`cloneImpls` give user `Drop`/`Clone` bodies of
base types; `assoc` gives associated types `<ty as tr>::Out = out` as `(tr, ty, out)`. -/
structure Program where
  fns : List FnDef
  methods : List (Nat × List Nat)
  impls : List ImplEntry
  dropImpls : List (Nat × Stmt)
  cloneImpls : List (Nat × Stmt)
  assoc : List (Nat × Ty × Ty)

/-- The static signature both semantics share: `trackCaller` flags and trait method lists. -/
structure Sig where
  tc : Nat → Bool
  methods : Nat → List Nat

def Program.sig (P : Program) : Sig where
  tc f := ((P.fns[f]?).map FnDef.trackCaller).getD false
  methods tr := (P.methods.lookup tr).getD []

/-! ## Substitution and normalization -/

def Ty.subst (σ : List Ty) : Ty → Ty
  | .param i => σ.getD i (.param i)
  | .box t => .box (t.subst σ)
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .proj tr t => .proj tr (t.subst σ)
  | t => t

def Key.subst (σ : List Ty) : Key → Key
  | .inst f τs => .inst f (τs.map (Ty.subst σ))
  | .meth tr m t => .meth tr m (t.subst σ)
  | .dropGlue t => .dropGlue (t.subst σ)
  | .cloneShim t => .cloneShim (t.subst σ)
  | .reifyShim f τs => .reifyShim f (τs.map (Ty.subst σ))
  | k => k

def Stmt.subst (σ : List Ty) : Stmt → Stmt
  | .seq a b => .seq (a.subst σ) (b.subst σ)
  | .call f τs => .call f (τs.map (Ty.subst σ))
  | .invoke k => .invoke (k.subst σ)
  | .mcall tr m t => .mcall tr m (t.subst σ)
  | .drop t => .drop (t.subst σ)
  | .clone t => .clone (t.subst σ)
  | .reify j f τs => .reify j f (τs.map (Ty.subst σ))
  | .unsize j t tr => .unsize j (t.subst σ) tr
  | .onUnwind a b => .onUnwind (a.subst σ) (b.subst σ)
  | .cloneAgg ts => .cloneAgg (ts.map (Ty.subst σ))
  | .guard s => .guard (s.subst σ)
  | s => s

def assocLookup (A : List (Nat × Ty × Ty)) (tr : Nat) (t : Ty) : Option Ty :=
  (A.find? (fun e => decide (e.1 = tr ∧ e.2.1 = t))).map (fun e => e.2.2)

/-- Normalization of associated-type projections (the toy analogue of normalizing types before
keying an instance). A projection with no `assoc` entry is left in place. This is a single
bottom-up pass: the right-hand side found in `A` is returned as is, not normalized again, so on a
table whose outputs contain reducible projections `Ty.norm` is not idempotent (see
`assocNormal` and `ty_norm_idem_of_assocNormal`). -/
def Ty.norm (A : List (Nat × Ty × Ty)) : Ty → Ty
  | .box t => .box (t.norm A)
  | .pair a b => .pair (a.norm A) (b.norm A)
  | .proj tr t => (assocLookup A tr (t.norm A)).getD (.proj tr (t.norm A))
  | t => t

def Key.norm (P : Program) : Key → Key
  | .inst f τs => .inst f (τs.map (Ty.norm P.assoc))
  | .meth tr m t => .meth tr m (t.norm P.assoc)
  | .dropGlue t => .dropGlue (t.norm P.assoc)
  | .cloneShim t => .cloneShim (t.norm P.assoc)
  | .reifyShim f τs => .reifyShim f (τs.map (Ty.norm P.assoc))
  | k => k

/-- Normalization of every type and key a statement mentions (one `Ty.norm` pass each). Source
bodies are instantiated by substitution followed by this normalization. -/
def Stmt.norm (P : Program) : Stmt → Stmt
  | .seq a b => .seq (a.norm P) (b.norm P)
  | .call f τs => .call f (τs.map (Ty.norm P.assoc))
  | .invoke k => .invoke (k.norm P)
  | .mcall tr m t => .mcall tr m (t.norm P.assoc)
  | .drop t => .drop (t.norm P.assoc)
  | .clone t => .clone (t.norm P.assoc)
  | .reify j f τs => .reify j f (τs.map (Ty.norm P.assoc))
  | .unsize j t tr => .unsize j (t.norm P.assoc) tr
  | .onUnwind a b => .onUnwind (a.norm P) (b.norm P)
  | .cloneAgg ts => .cloneAgg (ts.map (Ty.norm P.assoc))
  | .guard s => .guard (s.norm P)
  | s => s

/-! ## Keys requested by statements -/

/-- The key a `clone` of `τ` requests: user `Clone` for base types, the builtin shim otherwise. -/
def cloneKey : Ty → Key
  | .base n => .userClone n
  | t => .cloneShim t

/-- The key a function pointer to `f::<τs>` designates: the reify shim when `f` is
`trackCaller`, the instance itself otherwise. -/
def reifyKey (sig : Sig) (f : Nat) (τs : List Ty) : Key :=
  if sig.tc f then .reifyShim f τs else .inst f τs

/-- Vtable entries created by unsizing `τ` to `dyn tr`: every method of `tr` at `τ`. -/
def vtEntries (sig : Sig) (t : Ty) (tr : Nat) : List (Nat × Key) :=
  (sig.methods tr).map fun m => (m, .meth tr m t)

/-- Runtime references of a statement: every key the interpreter may request while running it,
or store into a frame slot (and later request through a function pointer or a vtable). Covers
calls, operand-position reifications, unsizing (all trait methods plus the drop glue), drops on
normal and cleanup paths, and clones. -/
def refs (sig : Sig) : Stmt → List Key
  | .skip => []
  | .seq a b => refs sig a ++ refs sig b
  | .emit _ => []
  | .panic => []
  | .call f τs => [.inst f τs]
  | .invoke k => [k]
  | .mcall tr m t => [.meth tr m t]
  | .drop t => [.dropGlue t]
  | .clone t => [cloneKey t]
  | .reify _ f τs => [reifyKey sig f τs]
  | .callPtr _ => []
  | .unsize _ t tr => (vtEntries sig t tr).map Prod.snd ++ [.dropGlue t]
  | .callDyn _ _ => []
  | .dropDyn _ => []
  | .onUnwind a b => refs sig a ++ refs sig b
  | .cloneAgg ts => ts.map cloneKey ++ ts.map Key.dropGlue
  | .guard s => refs sig s

/-! ## The shared interpreter -/

/-- Contents of a frame slot: a function pointer, or a trait object's vtable
(method entries and the drop entry). -/
inductive SlotVal where
  | fn : Key → SlotVal
  | vt : List (Nat × Key) → Key → SlotVal
  deriving DecidableEq, Repr

abbrev Frame := List (Nat × SlotVal)

/-- Global state: the observable event trace (in order) and the guard counter. -/
structure St where
  evs : List Nat
  ctr : Nat
  deriving DecidableEq, Repr

/-- Outcomes: normal completion, unwinding, abort (a panic during cleanup), a call to an undefined
symbol (`link k`), an ill-formed frame access, and fuel exhaustion. -/
inductive Res where
  | ok : Res
  | unwind : Res
  | abort : Res
  | link : Key → Res
  | stuck : Res
  | outOfFuel : Res
  deriving DecidableEq, Repr

/-- A call oracle: how a key behaves when called from state `st`. -/
abbrev Call := Key → St → Res × St

/-- Cleanup of already-cloned fields (most recent first); a panic inside cleanup aborts. -/
def cleanupDrops (c : Call) : List Ty → St → Res × St
  | [], st => (.unwind, st)
  | t :: ts, st =>
    match c (.dropGlue t) st with
    | (.ok, st') => cleanupDrops c ts st'
    | (.unwind, st') => (.abort, st')
    | r => r

/-- Source-level aggregate clone: clone fields left to right; if cloning a field unwinds, drop
the clones made so far in reverse order of creation, then keep unwinding. -/
def aggClone (c : Call) : List Ty → List Ty → St → Res × St
  | _, [], st => (.ok, st)
  | done, t :: ts, st =>
    match c (cloneKey t) st with
    | (.ok, st') => aggClone c (t :: done) ts st'
    | (.unwind, st') => cleanupDrops c done st'
    | r => r

/-- One body execution, parametric in the call oracle `c` (structural on the statement). -/
def execS (sig : Sig) (c : Call) : Stmt → Frame → St → Res × Frame × St
  | .skip, fr, st => (.ok, fr, st)
  | .seq a b, fr, st =>
    match execS sig c a fr st with
    | (.ok, fr', st') => execS sig c b fr' st'
    | r => r
  | .emit e, fr, st => (.ok, fr, { st with evs := st.evs ++ [e] })
  | .panic, fr, st => (.unwind, fr, st)
  | .call f τs, fr, st => ((c (.inst f τs) st).1, fr, (c (.inst f τs) st).2)
  | .invoke k, fr, st => ((c k st).1, fr, (c k st).2)
  | .mcall tr m t, fr, st => ((c (.meth tr m t) st).1, fr, (c (.meth tr m t) st).2)
  | .drop t, fr, st => ((c (.dropGlue t) st).1, fr, (c (.dropGlue t) st).2)
  | .clone t, fr, st => ((c (cloneKey t) st).1, fr, (c (cloneKey t) st).2)
  | .reify j f τs, fr, st => (.ok, (j, .fn (reifyKey sig f τs)) :: fr, st)
  | .callPtr j, fr, st =>
    match fr.lookup j with
    | some (.fn k) => ((c k st).1, fr, (c k st).2)
    | _ => (.stuck, fr, st)
  | .unsize j t tr, fr, st => (.ok, (j, .vt (vtEntries sig t tr) (.dropGlue t)) :: fr, st)
  | .callDyn j m, fr, st =>
    match fr.lookup j with
    | some (.vt es _) =>
      match es.lookup m with
      | some k => ((c k st).1, fr, (c k st).2)
      | none => (.stuck, fr, st)
    | _ => (.stuck, fr, st)
  | .dropDyn j, fr, st =>
    match fr.lookup j with
    | some (.vt _ d) => ((c d st).1, fr, (c d st).2)
    | _ => (.stuck, fr, st)
  | .onUnwind a b, fr, st =>
    match execS sig c a fr st with
    | (.unwind, fr', st') =>
      match execS sig c b fr' st' with
      | (.ok, fr'', st'') => (.unwind, fr'', st'')
      | (.unwind, fr'', st'') => (.abort, fr'', st'')
      | r => r
    | r => r
  | .cloneAgg ts, fr, st => ((aggClone c [] ts st).1, fr, (aggClone c [] ts st).2)
  | .guard s, fr, st =>
    if st.ctr = 0 then (.ok, fr, st) else execS sig c s fr { st with ctr := st.ctr - 1 }

/-- Running a key with fuel: look the key up in a resolver `R` (a symbol table), run its body in
a fresh frame, and answer nested calls by running with one less unit of fuel. Fuel bounds the
call depth. An undefined key gives `link k`. -/
def runKey (sig : Sig) (R : Key → Option Stmt) : Nat → Key → St → Res × St
  | 0, _, st => (.outOfFuel, st)
  | n + 1, k, st =>
    match R k with
    | none => (.link k, st)
    | some b => ((execS sig (runKey sig R n) b [] st).1, (execS sig (runKey sig R n) b [] st).2.2)

end Toy.MonoShim
