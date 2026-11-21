import ToyDropck.Basic

/-!
# Toy drop checking: typing and the decidable drop checker

The checker is type-based: it inspects the declared type of each local, never its value. For a
local `i` that the drop order `ord` drops, it requires `dropckP … (outlives ord i) t` of the
local's type `t`, where `outlives ord i j` says that local `j` is not `i` itself and is not dropped
before `i` (so `j` *strictly* outlives the drop of `i`).
-/

namespace Toy.Dropck

/-- The lifetimes (referent locals) occurring anywhere in a type. -/
def lifetimes : Ty → List Nat
  | .int => []
  | .ref j => [j]
  | .app _ t => lifetimes t

mutual
/-- `hasTy v t`: value `v` has type `t`. A reference `ref j` has exactly the type `ref j`; a
container value `obj c vs` has type `app c t` iff every element has type `t`. -/
def hasTy : Val → Ty → Bool
  | .int _, .int => true
  | .ref j, .ref k => j == k
  | .obj c vs, .app d t => c == d && hasTyAll vs t
  | _, _ => false
/-- `hasTy` for every element of a list. -/
def hasTyAll : List Val → Ty → Bool
  | [], _ => true
  | v :: vs, t => hasTy v t && hasTyAll vs t
end

/-- Every local's value has the local's declared type. -/
def ValuesHaveTypes (p : Prog) : Prop :=
  p.locals.all (fun e => hasTy e.2 e.1) = true

/-- Every lifetime occurring in a declared type names an existing local (`j < n` for a scope with
`n` locals). -/
def LifetimesInScope (p : Prog) : Prop :=
  p.locals.all (fun e => (lifetimes e.1).all (fun j => decide (j < p.locals.length))) = true

instance (p : Prog) : Decidable (ValuesHaveTypes p) := inferInstanceAs (Decidable (_ = true))
instance (p : Prog) : Decidable (LifetimesInScope p) := inferInstanceAs (Decidable (_ = true))

/-- `outlives ord i j`: `j` is not `i`, and `j` does not occur in `ord` before the first occurrence
of `i`. For a local `i` that occurs in `ord` (the case in which the checker consults it) and
an existing local `j`, this says that `j` strictly outlives the drop of `i`. When `i` does not
occur in `ord` the whole of `ord` is scanned; the function does not know the number of locals. -/
def outlives (ord : List Nat) (i j : Nat) : Bool :=
  j != i && !(ord.takeWhile (· != i)).contains j

/-- How the checker treats the type parameter `T` of a `Drop` impl that carries
`#[may_dangle]`. The policies differ in when `T`'s lifetimes are exempt from the outlives
requirement and in what they demand instead.
* `ownsRecurse` (RFC 1327's `#[may_dangle]` combined with the ownership recursion of RFC 769,
  where `PhantomData<T>` counts as owning `T`): `T`'s lifetimes are exempt; if the type declares
  that it owns `T`, the drop of `T` itself is checked recursively;
* `noUseSuffices` (relaxation): `T` is exempt and nothing further is demanded;
* `headNoDrop` (relaxation, "`T: !Drop`" checked shallowly): `T` is exempt when the outermost
  type constructor of `T` has no `Drop` impl; otherwise `T`'s lifetimes must outlive the drop;
* `deepNoDrop` ("`T: !Drop`" checked deeply): `T` is exempt when no type constructor occurring in
  `T` has a `Drop` impl; otherwise `T`'s lifetimes must outlive the drop. -/
inductive DanglePolicy where
  | ownsRecurse
  | noUseSuffices
  | headNoDrop
  | deepNoDrop
  deriving DecidableEq, Repr

/-- The outermost type constructor of `t` has no `Drop` impl (integers and references have none). -/
def headHasNoDrop (impls : ImplTable) : Ty → Bool
  | .app c _ => !(impls c).beh.hasDrop
  | _ => true

/-- No type constructor occurring in `t` has a `Drop` impl (whether or not it owns its parameter). -/
def deepHasNoDrop (impls : ImplTable) : Ty → Bool
  | .app c t => !(impls c).beh.hasDrop && deepHasNoDrop impls t
  | _ => true

/-- `dropckP pol impls ok t`: the drop-check judgment for dropping a value of type `t` at a point
where exactly the lifetimes `j` with `ok j = true` strictly outlive the drop.
For `app c t`:
* if `c` has a `Drop` impl with `#[may_dangle]` on `T`: whatever `pol` demands;
* otherwise: if `c` has a `Drop` impl, every lifetime in `t` must satisfy `ok` (the strict
  "parameters strictly outlive" rule), and if `c` declares that it owns `T`, `t` is checked
  recursively. -/
def dropckP (pol : DanglePolicy) (impls : ImplTable) (ok : Nat → Bool) : Ty → Bool
  | .int => true
  | .ref _ => true
  | .app c t =>
    if (impls c).beh.hasDrop && (impls c).decl.mayDangle then
      match pol with
      | .ownsRecurse => !(impls c).decl.ownsT || dropckP pol impls ok t
      | .noUseSuffices => true
      | .headNoDrop => headHasNoDrop impls t || (lifetimes t).all ok
      | .deepNoDrop => deepHasNoDrop impls t || (lifetimes t).all ok
    else
      (!(impls c).beh.hasDrop || (lifetimes t).all ok) &&
      (!(impls c).decl.ownsT || dropckP pol impls ok t)

/-- The checker over a list of locals, starting at index `i`. -/
def acceptsFrom (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat) :
    Nat → List (Ty × Val) → Bool
  | _, [] => true
  | i, (t, _) :: rest =>
    (!ord.contains i || dropckP pol impls (outlives ord i) t) && acceptsFrom pol impls ord (i + 1) rest

/-- The checker verdict under policy `pol`: every local `i` that `ord` drops passes
`dropckP pol impls (outlives ord i)` on its declared type. Locals that `ord` never drops are not
constrained. -/
def acceptsP (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat) (p : Prog) : Bool :=
  acceptsFrom pol impls ord 0 p.locals

/-- The `may_dangle` checker (policy `ownsRecurse`). -/
def accepts (impls : ImplTable) (ord : List Nat) (p : Prog) : Bool :=
  acceptsP .ownsRecurse impls ord p

/-- Erase every `#[may_dangle]` annotation, keeping behaviour and ownership declarations. -/
def stripDangle (impls : ImplTable) : ImplTable :=
  fun c => ⟨(impls c).beh, ⟨false, (impls c).decl.ownsT⟩⟩

/-- The strict checker (no `may_dangle`): every type parameter of every `Drop` impl must strictly
outlive the value being dropped. -/
def acceptsStrict (impls : ImplTable) (ord : List Nat) (p : Prog) : Bool :=
  accepts (stripDangle impls) ord p

end Toy.Dropck
