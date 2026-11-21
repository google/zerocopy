/-!
# Tricolor marking: a finite toy model

This module defines a toy model of incremental tracing (mark) garbage collection over a
finite heap whose objects are `Fin n`.

* The heap is a Boolean adjacency matrix `edge`: `edge x y = true` means some field of `x`
  points to `y`. Fields are not individually modeled, so an overwrite `x.f := y` replacing a
  pointer to `z` is modeled as an `erase x z` followed by a `store x y`. Two fields of `x`
  that both point to `z` are one edge, so one `erase x z` removes both.
* The root set `root` abstracts the mutator's registers and stack slots. Root writes
  (`load`, `drop`, `alloc`) do not run the heap write barrier.
* Every object carries a `Color`. White objects that remain at the end of marking are the
  ones a sweep would free (sweeping itself is not modeled).

The collector step `scan s g` greys the white successors of `g` and blackens `g`. Mutator
steps are `store`, `erase`, `load`, `drop` and `alloc`. A `Barrier` is a hook on the heap
writes `store` and `erase`.

Mutator discipline (`Op.Enabled`): a heap store writes a pointer the mutator currently holds
in its roots (it must have been loaded or allocated first); a root load takes any object that
is currently reachable from the roots (abstracting a chain of field loads); erases and drops
are always enabled. The object whose field is written (`x` in `store x y` and `erase x z`) is
not constrained, which only enlarges the step relation (every preservation theorem then
covers more steps). A pointer-chasing overwrite `x.f := x.f.next` whose new target is
reachable only through the old one must load the new target into the roots before the
`erase`, since after the erase the target may no longer be reachable.
-/

namespace Toy.Tricolor

/-- Object colors in tricolor marking. White: not yet reached by the collector (freed if still
white when marking ends). Grey: reached, successors not yet scanned. Black: reached and scanned. -/
inductive Color where
  | white
  | grey
  | black
  deriving DecidableEq, Repr

/-- A heap state over objects `Fin n`: pointer graph, root set and object colors. -/
structure St (n : Nat) where
  /-- `edge x y = true` iff some field of object `x` points to object `y`. -/
  edge : Fin n → Fin n → Bool
  /-- `root r = true` iff `r` is held by the mutator's roots (registers, stack slots). -/
  root : Fin n → Bool
  /-- The current color of each object. -/
  color : Fin n → Color

variable {n : Nat}

theorem St.ext' {s t : St n} (he : s.edge = t.edge) (hr : s.root = t.root)
    (hc : s.color = t.color) : s = t := by
  cases s; cases t; simp_all

/-! ## Reachability and invariants -/

/-- `Live s y`: object `y` is reachable from the root set along heap edges (a root itself is
live). These are the objects a correct collector must not free. -/
inductive Live (s : St n) : Fin n → Prop where
  | root {r : Fin n} : s.root r = true → Live s r
  | step {x y : Fin n} : Live s x → s.edge x y = true → Live s y

/-- `NoGrey s`: no grey object remains; this is the termination test of the mark phase. -/
def NoGrey (s : St n) : Prop := ∀ x, s.color x ≠ .grey

/-- The strong tricolor invariant: no edge from a black object to a white object. -/
def Strong (s : St n) : Prop :=
  ∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white

/-- `GreyProtected s y`: `y` is white and is reachable from some grey object along a path of
length at least one all of whose objects after the grey start (including `y`) are white. -/
inductive GreyProtected (s : St n) : Fin n → Prop where
  | direct {g y : Fin n} :
      s.color g = .grey → s.edge g y = true → s.color y = .white → GreyProtected s y
  | chain {w y : Fin n} :
      GreyProtected s w → s.edge w y = true → s.color y = .white → GreyProtected s y

/-- The weak tricolor invariant: every white object pointed to by a black object is grey
protected. -/
def Weak (s : St n) : Prop :=
  ∀ x y, s.edge x y = true → s.color x = .black → s.color y = .white → GreyProtected s y

/-- Every root is non-white. -/
def RootsNonWhite (s : St n) : Prop := ∀ r, s.root r = true → s.color r ≠ .white

/-- Every white root is grey protected. This is the root clause of the weak invariant for a
mutator whose roots are not rescanned (the roots are treated like a black object). -/
def RootsProtected (s : St n) : Prop :=
  ∀ r, s.root r = true → s.color r = .white → GreyProtected s r

/-- Marking safety: every live object is black (so freeing the white objects frees no live
object). -/
def AllLiveBlack (s : St n) : Prop := ∀ y, Live s y → s.color y = .black

/-- `Isolated s a`: no edge leaves or enters `a` (a cell with null fields that no object points
to). Allocation requires it: a freshly allocated object has zeroed pointer fields, which the
mutator fills later with ordinary (barriered) stores. -/
def Isolated (s : St n) (a : Fin n) : Prop := ∀ v, s.edge a v = false ∧ s.edge v a = false

instance (s : St n) : Decidable (NoGrey s) :=
  inferInstanceAs (Decidable (∀ x, s.color x ≠ .grey))
instance (s : St n) : Decidable (Strong s) :=
  inferInstanceAs (Decidable (∀ x y, s.edge x y = true → s.color x = .black → s.color y ≠ .white))
instance (s : St n) : Decidable (RootsNonWhite s) :=
  inferInstanceAs (Decidable (∀ r, s.root r = true → s.color r ≠ .white))
instance (s : St n) (a : Fin n) : Decidable (Isolated s a) :=
  inferInstanceAs (Decidable (∀ v, s.edge a v = false ∧ s.edge v a = false))

/-! ## Operations -/

/-- Shade `y`: grey it if it is white, otherwise leave it unchanged. -/
def shade (c : Fin n → Color) (y : Fin n) : Fin n → Color :=
  fun v => if v = y ∧ c v = .white then .grey else c v

/-- Add the edge `x → y`. -/
def addEdge (e : Fin n → Fin n → Bool) (x y : Fin n) : Fin n → Fin n → Bool :=
  fun u v => if u = x ∧ v = y then true else e u v

/-- Remove the edge `x → z`. -/
def delEdge (e : Fin n → Fin n → Bool) (x z : Fin n) : Fin n → Fin n → Bool :=
  fun u v => if u = x ∧ v = z then false else e u v

/-- Collector step: grey the white successors of `g` and blacken `g`. As a step of the
system (`Op.Enabled`) it requires `g` to be grey. -/
def scan (s : St n) (g : Fin n) : St n :=
  { s with color := fun v =>
      if v = g then .black
      else if s.edge g v = true ∧ s.color v = .white then .grey else s.color v }

/-- Heap write barriers. `none`: no barrier. `dijkstra`: insertion barrier, shades the new
target of a store. `yuasa`: deletion (snapshot-at-the-beginning) barrier, shades the old target
of an erased pointer. -/
inductive Barrier where
  | none
  | dijkstra
  | yuasa
  deriving DecidableEq, Repr

/-- Mutator store `x.f := y` into a previously null field: add `x → y`; the Dijkstra barrier
shades `y`. -/
def store (b : Barrier) (s : St n) (x y : Fin n) : St n :=
  { s with edge := addEdge s.edge x y,
           color := if b = .dijkstra then shade s.color y else s.color }

/-- Mutator erase of the pointer `x → z` (the deletion half of an overwrite, or a store of
null): remove `x → z`; the Yuasa barrier shades the old target `z` if the edge existed. -/
def erase (b : Barrier) (s : St n) (x z : Fin n) : St n :=
  { s with edge := delEdge s.edge x z,
           color := if b = .yuasa ∧ s.edge x z = true then shade s.color z else s.color }

/-- Mutator root load: `y` becomes a root. Root writes run no heap barrier; with
`shadeLoads = true` the loaded object is shaded (a load barrier, the load-side discipline
that keeps the mutator black). -/
def load (shadeLoads : Bool) (s : St n) (y : Fin n) : St n :=
  { s with root := fun v => if v = y then true else s.root v,
           color := if shadeLoads then shade s.color y else s.color }

/-- Mutator root drop: `r` stops being a root. -/
def drop (s : St n) (r : Fin n) : St n :=
  { s with root := fun v => if v = r then false else s.root v }

/-- Allocation of object `a` with color `c` into the roots. As a step (`Op.Enabled`) it
requires `a` to be an isolated non-root object of any current color. An allocation of a cell
that is white in the current state models taking a free cell; an allocation of a cell that is
already grey or black in the current marking cycle re-colors it (no sweep runs in between),
which stands in for a fresh cell beyond the `n` initial ones and is what lets allocation add
collector work (see the termination module). -/
def alloc (s : St n) (a : Fin n) (c : Color) : St n :=
  { s with root := fun v => if v = a then true else s.root v,
           color := fun v => if v = a then c else s.color v }

/-- Start of a marking cycle: grey every root, whiten everything else. This is one atomic step
that shades every root-referenced object at once, modeling a stop-the-world root snapshot (the
mutator is black from the start of the cycle); it does not model thread stacks that stay grey
and are scanned concurrently with the heap. -/
def initMark (s : St n) : St n :=
  { s with color := fun v => if s.root v = true then .grey else .white }

/-- Root rescan: grey every white root. -/
def rescan (s : St n) : St n :=
  { s with color := fun v => if s.root v = true ∧ s.color v = .white then .grey else s.color v }

/-- A collector configuration: heap barrier, whether root loads are shaded, and which
allocation colors the allocator may use. -/
structure Config where
  barrier : Barrier
  shadeLoads : Bool
  allocOk : Color → Bool

/-- Steps of the system (collector `scan`, mutator operations). -/
inductive Op (n : Nat) where
  | scan (g : Fin n)
  | store (x y : Fin n)
  | erase (x z : Fin n)
  | load (y : Fin n)
  | drop (r : Fin n)
  | alloc (a : Fin n) (c : Color)
  deriving DecidableEq, Repr

/-- The effect of a step. -/
def Op.apply (cfg : Config) : Op n → St n → St n
  | .scan g, s => Tricolor.scan s g
  | .store x y, s => Tricolor.store cfg.barrier s x y
  | .erase x z, s => Tricolor.erase cfg.barrier s x z
  | .load y, s => Tricolor.load cfg.shadeLoads s y
  | .drop r, s => Tricolor.drop s r
  | .alloc a c, s => Tricolor.alloc s a c

/-- When a step may fire. The collector scans only grey objects. The mutator may store into a
heap field only a pointer it holds in its roots (`s.root y = true`), and may load into its roots
only an object it can reach (`Live s y`). Allocation takes an isolated non-root object and an
allowed color. -/
def Op.Enabled (cfg : Config) : Op n → St n → Prop
  | .scan g, s => s.color g = .grey
  | .store _ y, s => s.root y = true
  | .erase _ _, _ => True
  | .load y, s => Live s y
  | .drop _, _ => True
  | .alloc a c, s => cfg.allocOk c = true ∧ s.root a = false ∧ Isolated s a

/-- `Run cfg s ops s'`: executing the enabled steps `ops` from `s` reaches `s'`. -/
inductive Run (cfg : Config) : St n → List (Op n) → St n → Prop where
  | nil (s : St n) : Run cfg s [] s
  | cons {s s' : St n} {op : Op n} {ops : List (Op n)} :
      op.Enabled cfg s → Run cfg (op.apply cfg s) ops s' → Run cfg s (op :: ops) s'

/-- One enabled step. -/
def Step (cfg : Config) (s s' : St n) : Prop :=
  ∃ op : Op n, op.Enabled cfg s ∧ s' = op.apply cfg s

/-- The final state of executing `ops` (ignoring enabledness). -/
def runOps (cfg : Config) (ops : List (Op n)) (s : St n) : St n :=
  ops.foldl (fun t op => op.apply cfg t) s

/-- Whether a step is a collector scan. -/
def Op.isScan : Op n → Bool
  | .scan _ => true
  | _ => false

/-! ## Basic lemmas -/

theorem GreyProtected.white {s : St n} {y : Fin n} (h : GreyProtected s y) :
    s.color y = .white := by
  cases h <;> assumption

/-- Induction-free closure principle: any predicate containing the direct grey-successor
whites and closed under white successors contains every grey-protected object. -/
theorem GreyProtected.subset {s : St n} (S : Fin n → Prop)
    (h1 : ∀ g y, s.color g = .grey → s.edge g y = true → s.color y = .white → S y)
    (h2 : ∀ w y, S w → s.edge w y = true → s.color y = .white → S y) :
    ∀ {y}, GreyProtected s y → S y := by
  intro y h
  induction h with
  | direct hg he hy => exact h1 _ _ hg he hy
  | chain _ he hy ih => exact h2 _ _ ih he hy

/-- Any predicate containing the roots and closed under edges contains every live object. -/
theorem Live.subset {s : St n} (S : Fin n → Prop)
    (h1 : ∀ r, s.root r = true → S r) (h2 : ∀ x y, S x → s.edge x y = true → S y) :
    ∀ {y}, Live s y → S y := by
  intro y h
  induction h with
  | root hr => exact h1 _ hr
  | step _ he ih => exact h2 _ _ ih he

theorem not_greyProtected_of_noGrey {s : St n} (hng : NoGrey s) {y : Fin n} :
    ¬ GreyProtected s y := by
  intro h
  have := GreyProtected.subset (s := s) (fun _ => False)
    (fun g _ hg _ _ => hng g hg) (fun _ _ h _ _ => h) h
  exact this

theorem Run.eq_runOps {cfg : Config} {s s' : St n} {ops : List (Op n)}
    (h : Run cfg s ops s') : s' = runOps cfg ops s := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa [runOps] using ih

theorem Run.append {cfg : Config} {s s' s'' : St n} {ops ops' : List (Op n)}
    (h : Run cfg s ops s') (h' : Run cfg s' ops' s'') : Run cfg s (ops ++ ops') s'' := by
  induction h with
  | nil => simpa using h'
  | cons he _ ih => exact Run.cons he (ih h')

/-- Run-level invariance: a property preserved by every enabled step holds after every run. -/
theorem Run.invariant {cfg : Config} (P : St n → Prop)
    (hP : ∀ s s', P s → Step cfg s s' → P s') {s s' : St n} {ops : List (Op n)}
    (h : Run cfg s ops s') (h0 : P s) : P s' := by
  induction h with
  | nil => exact h0
  | cons he _ ih => exact ih (hP _ _ h0 ⟨_, he, rfl⟩)

end Toy.Tricolor
