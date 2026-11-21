/-!
# Toy drop checking: syntax and runtime semantics

A deliberately small model of one block scope at the moment it exits.

* Locals `0, 1, …, n-1` are declared in that order and each holds a value. A value may
  contain references to any local (earlier or later), which models late initialization such as
  `let mut v = Vec::new(); let x = 0; v.push(&x);`.
* At scope exit the locals are dropped one at a time in a *drop order* `ord : List Nat`
  (for Rust's rule, reverse declaration order). A local counts as *dead* from the moment its own
  drop begins: while its value is being dropped, observing the local through a reference is
  already undefined behaviour, and afterwards its storage has ended.
* Containers are values `obj c elems`, an instance of the generic type constructor `c` (think
  `Vec<T>` or `Box<T>`) holding element values of type `T`. Every type constructor has exactly
  one type parameter and no lifetime parameters. Each type constructor has a `DropImpl`: runtime
  behaviour (`DropBehavior`) plus the facts the drop checker is told (`DropDecl`).
* Undefined behaviour is modelled by `false`: a destructor *uses* its elements by observing them,
  and observing a reference to a dead or nonexistent local is undefined behaviour.
-/

namespace Toy.Dropck

/-- Types. `int` is plain data without drop glue; `ref j` is a shared reference whose lifetime is
the storage of local `j` (the toy identifies a lifetime with the referent local, and the type
records that local and not the type of the referent); `app c t` is the generic container type
constructor `c` applied to the element type `t`. -/
inductive Ty where
  | int : Ty
  | ref (j : Nat) : Ty
  | app (c : Nat) (t : Ty) : Ty
  deriving DecidableEq, Repr

/-- Values. `ref j` points at local `j`; `obj c elems` is an instance of container `c` owning (or
holding) the element values `elems`. -/
inductive Val where
  | int (n : Nat) : Val
  | ref (j : Nat) : Val
  | obj (c : Nat) (elems : List Val) : Val

/-- Runtime behaviour of dropping an instance of a container type constructor.
* `hasDrop`: the type constructor has a user `Drop` impl (a destructor);
* `usesT`: that destructor uses its `T` elements (reads, writes or calls methods on them); it has
  no effect when `hasDrop = false`;
* `dropsElems`: dropping the container drops its `T` elements (through the destructor, as `Vec`
  does with `drop_in_place`, or through compiler drop glue for by-value fields). -/
structure DropBehavior where
  hasDrop : Bool
  usesT : Bool
  dropsElems : Bool
  deriving DecidableEq, Repr

/-- What the drop checker is told about a container type constructor, beyond whether it has a
`Drop` impl.
* `mayDangle`: the `Drop` impl carries `#[may_dangle]` on its type parameter `T` (an unchecked
  promise by the impl's author);
* `ownsT`: the type declares, in a way the drop checker can see, that it owns values of type `T`
  (a by-value field of type `T`, or a `PhantomData<T>` marker). -/
structure DropDecl where
  mayDangle : Bool
  ownsT : Bool
  deriving DecidableEq, Repr

/-- The drop-relevant description of one container type constructor. -/
structure DropImpl where
  beh : DropBehavior
  decl : DropDecl
  deriving DecidableEq, Repr

/-- Container type constructors are named by natural numbers. -/
abbrev ImplTable := Nat → DropImpl

/-- The runtime part of an implementation table. -/
def behOf (impls : ImplTable) : Nat → DropBehavior := fun c => (impls c).beh

mutual
/-- `observe L v`: using the value `v` (for instance printing it through a trait method). It
recurses through container values to every reference inside `v` and, for a reference `ref j`,
checks that local `j` is live according to `L`; it does not read local `j`'s own value (there is
no second dereference). It is defined (`true`) iff every local so referenced is live. -/
def observe (L : Nat → Bool) : Val → Bool
  | .int _ => true
  | .ref j => L j
  | .obj _ vs => observeAll L vs
/-- `observe` on every element of a list. -/
def observeAll (L : Nat → Bool) : List Val → Bool
  | [] => true
  | v :: vs => observe L v && observeAll L vs
end

mutual
/-- `dropVal beh L v`: running the drop of value `v` while the live locals are `L` is defined
(`true`) or reaches undefined behaviour (`false`). References and integers have no drop glue. For
`obj c vs`: first the destructor of `c` runs, observing the elements if it uses them; then, if `c`
drops its elements, each element is dropped in turn. The live set `L` does not change during one
value's drop. -/
def dropVal (beh : Nat → DropBehavior) (L : Nat → Bool) : Val → Bool
  | .int _ => true
  | .ref _ => true
  | .obj c vs =>
    (!((beh c).hasDrop && (beh c).usesT) || observeAll L vs) &&
    (!(beh c).dropsElems || dropAll beh L vs)
/-- `dropVal` on every element of a list, in list order. -/
def dropAll (beh : Nat → DropBehavior) (L : Nat → Bool) : List Val → Bool
  | [] => true
  | v :: vs => dropVal beh L v && dropAll beh L vs
end

/-- A block scope at the moment it exits: local `i` has declared type `(locals[i]).1` and holds the
value `(locals[i]).2`. -/
structure Prog where
  locals : List (Ty × Val)

/-- `live n dead j`: local `j` exists (`j < n`) and is not in `dead`. -/
def live (n : Nat) (dead : List Nat) (j : Nat) : Bool :=
  decide (j < n) && !dead.contains j

/-- The scope-exit drop loop. `runDrops beh p ord dead` processes `ord` left to right; `dead`
lists the locals already dropped. An index that is already dead or that names no local is
skipped; otherwise local `k` becomes dead and its value is dropped with `k` itself counted as dead
(a value whose drop has begun must not be observed through references). The result is `false` iff
some drop reaches undefined behaviour. -/
def runDrops (beh : Nat → DropBehavior) (p : Prog) : List Nat → List Nat → Bool
  | [], _ => true
  | k :: ks, dead =>
    if dead.contains k then runDrops beh p ks dead
    else
      match p.locals[k]? with
      | none => runDrops beh p ks dead
      | some (_, v) =>
        dropVal beh (live p.locals.length (k :: dead)) v && runDrops beh p ks (k :: dead)

/-- The semantic property: dropping the locals of `p` in the order `ord` never lets a destructor
(or drop glue) observe a dead or nonexistent local, where a local counts as dead from the moment
its own drop begins. Undefined behaviour in the toy arises from such an observation and from
nothing else. Locals that `ord` never names are never dropped. -/
def DropSafe (impls : ImplTable) (ord : List Nat) (p : Prog) : Prop :=
  runDrops (behOf impls) p ord [] = true

instance (impls : ImplTable) (ord : List Nat) (p : Prog) : Decidable (DropSafe impls ord p) :=
  inferInstanceAs (Decidable (_ = true))

/-- Rust's scope-exit order for `n` locals: reverse declaration order `[n-1, …, 1, 0]`. -/
def revDeclOrder (n : Nat) : List Nat := (List.range n).reverse

/-- Declaration order `[0, 1, …, n-1]` (the order Rust does *not* use for locals). -/
def declOrder (n : Nat) : List Nat := List.range n

/-! ## Honesty conditions relating declarations to behaviour -/

/-- `#[may_dangle]` is truthful: a `Drop` impl that claims `may_dangle` on `T` does not use its `T`
elements (it may still drop them). -/
def MayDangleHonest (d : DropImpl) : Prop :=
  d.beh.hasDrop = true → d.decl.mayDangle = true → d.beh.usesT = false

/-- The ownership (`PhantomData<T>`) condition for `may_dangle` impls: a `Drop` impl that claims
`may_dangle` on `T` and drops its `T` elements declares that it owns `T`. -/
def OwnsDeclared (d : DropImpl) : Prop :=
  d.beh.hasDrop = true → d.decl.mayDangle = true → d.beh.dropsElems = true → d.decl.ownsT = true

/-- Drop glue of a type without a `Drop` impl is visible to the checker: if such a type drops its
`T` elements it declares that it owns `T`. The toy states this as a separate condition on the
table; whether Rust's drop glue satisfies an analogue of it is a modeling question outside the
toy. -/
def GlueVisible (d : DropImpl) : Prop :=
  d.beh.hasDrop = false → d.beh.dropsElems = true → d.decl.ownsT = true

/-- A `Drop` impl that claims `may_dangle` on `T` does not drop its `T` elements (for example a
handle that frees a buffer without running the elements' destructors). -/
def MayDangleDropsNothing (d : DropImpl) : Prop :=
  d.beh.hasDrop = true → d.decl.mayDangle = true → d.beh.dropsElems = false

instance (d : DropImpl) : Decidable (MayDangleHonest d) :=
  inferInstanceAs (Decidable (_ → _ → _))
instance (d : DropImpl) : Decidable (OwnsDeclared d) :=
  inferInstanceAs (Decidable (_ → _ → _ → _))
instance (d : DropImpl) : Decidable (GlueVisible d) :=
  inferInstanceAs (Decidable (_ → _ → _))
instance (d : DropImpl) : Decidable (MayDangleDropsNothing d) :=
  inferInstanceAs (Decidable (_ → _ → _))

end Toy.Dropck
