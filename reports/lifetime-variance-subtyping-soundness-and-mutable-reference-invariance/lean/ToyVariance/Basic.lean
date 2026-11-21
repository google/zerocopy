/-!
# Lifetimes, variances, variance tables, types, generated subtyping, variance inference

Toy model of lifetime subtyping lifted through type constructors by a variance table.
Everything here is a small, Mathlib-free model; it is not rustc's implementation.
-/

namespace Toy.Variance

/-! ## Lifetimes -/

/-- A lifetime (region name). `static` never ends. `till n` is live at times `0, …, n` and
dead from time `n + 1` on. Ending region `till n` is modelled by advancing the clock to
`n + 1`, which also ends every `till m` with `m ≤ n`; so the outlives order of this model is
total (a simplification of Rust's region preorder). -/
inductive Lft where
  | static
  | till (n : Nat)
  deriving DecidableEq, Repr

namespace Lft

/-- Is the region live at time `t`? -/
def live (t : Nat) : Lft → Bool
  | static => true
  | till n => decide (t ≤ n)

/-- `a.outlives b` is Rust's `'a : 'b`: `a` is live whenever `b` is. -/
def outlives : Lft → Lft → Bool
  | static, _ => true
  | till _, static => false
  | till n, till m => decide (m ≤ n)

end Lft

/-! ## Variances -/

/-- A variance of one constructor position. `bi` imposes no constraint, `co` requires the
argument relation forwards, `contra` backwards, `inv` both ways. -/
inductive Variance where
  | bi
  | co
  | contra
  | inv
  deriving DecidableEq, Repr

namespace Variance

/-- Does the variance require the forward relation (`A ≤ B` to relate `C A ≤ C B`)? -/
def fwd : Variance → Bool
  | co => true
  | inv => true
  | _ => false

/-- Does the variance require the backward relation (`B ≤ A` to relate `C A ≤ C B`)? -/
def bwd : Variance → Bool
  | contra => true
  | inv => true
  | _ => false

/-- The variance requiring exactly the given directions. -/
def ofDirs : Bool → Bool → Variance
  | false, false => bi
  | true, false => co
  | false, true => contra
  | true, true => inv

/-- `v.le w`: `v` is at most as permissive as `w`, i.e. `v` requires every direction that
`w` requires. `inv` is least permissive and `bi` most permissive; `co` and `contra` are
incomparable. -/
def le (v w : Variance) : Bool := (!w.fwd || v.fwd) && (!w.bwd || v.bwd)

/-- Greatest lower bound in the permissiveness order: require the union of directions. -/
def meet (v w : Variance) : Variance := ofDirs (v.fwd || w.fwd) (v.bwd || w.bwd)

/-- Composition: the variance of an occurrence at inner variance `w` inside an outer
position of variance `v` (`co ∘ w = w`, `contra` flips, `inv ∘ w = inv` unless `w = bi`,
`bi ∘ w = bi`). An inner `bi` means "no constraint from inside", so it stays `bi`. -/
def comp (v w : Variance) : Variance :=
  ofDirs ((v.fwd && w.fwd) || (v.bwd && w.bwd)) ((v.fwd && w.bwd) || (v.bwd && w.fwd))

/-- The relation lifted along a variance: `Rel v R a b` holds iff `R a b` whenever `v`
requires the forward direction and `R b a` whenever it requires the backward one. -/
def Rel {α : Type} (v : Variance) (R : α → α → Prop) (a b : α) : Prop :=
  (v.fwd = true → R a b) ∧ (v.bwd = true → R b a)

end Variance

/-- The lifetime relation of a lifetime position with variance `v`. -/
def LRel (v : Variance) (a b : Lft) : Prop :=
  Variance.Rel v (fun x y => x.outlives y = true) a b

/-! ## Variance tables -/

/-- The variance-carrying positions of the built-in type constructors. -/
inductive Pos where
  | refLft
  | refTy
  | refMutLft
  | refMutTy
  | cell
  | fnArg
  | fnRes
  | prodL
  | prodR
  | phantom
  deriving DecidableEq, Repr

/-- A variance table assigns a variance to every position. -/
abbrev Table := Pos → Variance

/-- The table modelled on Rust's: `&'a T` covariant in `'a` and `T`; `&'a mut T` covariant
in `'a`, invariant in `T`; `Cell<T>` invariant; `fn(T) -> U` contravariant in `T`,
covariant in `U`; tuples covariant; `PhantomData<T>` covariant. -/
def rustTable : Table
  | .refLft => .co
  | .refTy => .co
  | .refMutLft => .co
  | .refMutTy => .inv
  | .cell => .inv
  | .fnArg => .contra
  | .fnRes => .co
  | .prodL => .co
  | .prodR => .co
  | .phantom => .co

/-- Replace the variance of one position. -/
def Table.set (tbl : Table) (p : Pos) (v : Variance) : Table :=
  fun q => if q = p then v else tbl q

/-- Pointwise permissiveness order on tables. -/
def Table.le (t₁ t₂ : Table) : Prop := ∀ p, (t₁ p).le (t₂ p) = true

/-- `rustTable` with the `PhantomData` position made bivariant. -/
def safeTable : Table := rustTable.set .phantom .bi

/-! ## Types -/

/-- Toy types. `param` is the single type parameter of a struct body (see `inferVar`);
programs only use closed types (no `param`). `phantom T` is `PhantomData<T>` (no data).
`cell T` is `Cell<T>`: `newCell` creates a `ref ℓ (cell T)`, and `cellGet`/`cellSet` require a
shared reference `ref ℓ (cell T)`. A bare value of type `cell T` can also exist: `read` copies
the contents out of a `ref ℓ (cell T)` at type `cell T` (unlike Rust, where `Cell<T>` is not
`Copy`), and such a value can be paired, projected, copied, and boxed again with `alloc`. A bare
`cell T` value is an immutable copy; mutation always goes through a reference. -/
inductive Ty where
  | unit
  | nat
  | ref (l : Lft) (T : Ty)
  | refMut (l : Lft) (T : Ty)
  | cell (T : Ty)
  | fn (T U : Ty)
  | prod (T U : Ty)
  | phantom (T : Ty)
  | param
  deriving DecidableEq, Repr

namespace Ty

/-- `F.subst A` substitutes `A` for the parameter in `F`. -/
def subst : Ty → Ty → Ty
  | unit, _ => unit
  | nat, _ => nat
  | ref l T, A => ref l (subst T A)
  | refMut l T, A => refMut l (subst T A)
  | cell T, A => cell (subst T A)
  | fn T U, A => fn (subst T A) (subst U A)
  | prod T U, A => prod (subst T A) (subst U A)
  | phantom T, A => phantom (subst T A)
  | param, A => A

/-- No occurrence of `param`. -/
def closed : Ty → Bool
  | unit => true
  | nat => true
  | ref _ T => closed T
  | refMut _ T => closed T
  | cell T => closed T
  | fn T U => closed T && closed U
  | prod T U => closed T && closed U
  | phantom T => closed T
  | param => false

/-- Every lifetime occurring in the type satisfies `lv`. -/
def liveIn (lv : Lft → Bool) : Ty → Bool
  | unit => true
  | nat => true
  | ref l T => lv l && liveIn lv T
  | refMut l T => lv l && liveIn lv T
  | cell T => liveIn lv T
  | fn T U => liveIn lv T && liveIn lv U
  | prod T U => liveIn lv T && liveIn lv U
  | phantom T => liveIn lv T
  | param => true

/-- Every lifetime occurring in the type is `static` (the analogue of `T: 'static`). -/
def allStatic (T : Ty) : Bool := liveIn (fun l => l == Lft.static) T

/-- No `phantom` constructor occurs. -/
def phantomFree : Ty → Bool
  | unit => true
  | nat => true
  | ref _ T => phantomFree T
  | refMut _ T => phantomFree T
  | cell T => phantomFree T
  | fn T U => phantomFree T && phantomFree U
  | prod T U => phantomFree T && phantomFree U
  | phantom _ => false
  | param => true

end Ty

/-! ## Subtyping generated by a table -/

/-- The subtyping relation generated by reflexivity, transitivity, the extra generators
`ax`, and one congruence rule per constructor whose premises are read off the table. -/
inductive SubGen (tbl : Table) (ax : Ty → Ty → Prop) : Ty → Ty → Prop where
  | refl (T : Ty) : SubGen tbl ax T T
  | trans {S T U : Ty} : SubGen tbl ax S T → SubGen tbl ax T U → SubGen tbl ax S U
  | base {S T : Ty} : ax S T → SubGen tbl ax S T
  | ref {a b : Lft} {S T : Ty} : LRel (tbl .refLft) a b →
      ((tbl .refTy).fwd = true → SubGen tbl ax S T) →
      ((tbl .refTy).bwd = true → SubGen tbl ax T S) →
      SubGen tbl ax (.ref a S) (.ref b T)
  | refMut {a b : Lft} {S T : Ty} : LRel (tbl .refMutLft) a b →
      ((tbl .refMutTy).fwd = true → SubGen tbl ax S T) →
      ((tbl .refMutTy).bwd = true → SubGen tbl ax T S) →
      SubGen tbl ax (.refMut a S) (.refMut b T)
  | cell {S T : Ty} :
      ((tbl .cell).fwd = true → SubGen tbl ax S T) →
      ((tbl .cell).bwd = true → SubGen tbl ax T S) →
      SubGen tbl ax (.cell S) (.cell T)
  | fn {S S' U U' : Ty} :
      ((tbl .fnArg).fwd = true → SubGen tbl ax S S') →
      ((tbl .fnArg).bwd = true → SubGen tbl ax S' S) →
      ((tbl .fnRes).fwd = true → SubGen tbl ax U U') →
      ((tbl .fnRes).bwd = true → SubGen tbl ax U' U) →
      SubGen tbl ax (.fn S U) (.fn S' U')
  | prod {S S' U U' : Ty} :
      ((tbl .prodL).fwd = true → SubGen tbl ax S S') →
      ((tbl .prodL).bwd = true → SubGen tbl ax S' S) →
      ((tbl .prodR).fwd = true → SubGen tbl ax U U') →
      ((tbl .prodR).bwd = true → SubGen tbl ax U' U) →
      SubGen tbl ax (.prod S U) (.prod S' U')
  | phantom {S T : Ty} :
      ((tbl .phantom).fwd = true → SubGen tbl ax S T) →
      ((tbl .phantom).bwd = true → SubGen tbl ax T S) →
      SubGen tbl ax (.phantom S) (.phantom T)

/-- No extra generators. -/
def NoAx : Ty → Ty → Prop := fun _ _ => False

/-! ## Variance inference for struct bodies -/

/-- Inferred variance of the parameter in a struct body `F`: the greatest lower bound, over
all occurrences of `param`, of the composition of the table variances along the path to the
occurrence (`bi` if there is none). A struct with fields `F₁, …, Fₖ` is the body
`prod F₁ (prod F₂ … unit)`; `phantom param` is `PhantomData<T>`. -/
def inferVar (tbl : Table) : Ty → Variance
  | .unit => .bi
  | .nat => .bi
  | .ref _ T => (tbl .refTy).comp (inferVar tbl T)
  | .refMut _ T => (tbl .refMutTy).comp (inferVar tbl T)
  | .cell T => (tbl .cell).comp (inferVar tbl T)
  | .fn T U => ((tbl .fnArg).comp (inferVar tbl T)).meet ((tbl .fnRes).comp (inferVar tbl U))
  | .prod T U => ((tbl .prodL).comp (inferVar tbl T)).meet ((tbl .prodR).comp (inferVar tbl U))
  | .phantom T => (tbl .phantom).comp (inferVar tbl T)
  | .param => .co

/-- The schematic body rule for a body `F` at declared variance `v`, as extra generators of
the subtyping relation: `F[A] ≤ F[B]` for closed `A`, `B` related along `v` by the Rust-table
subtyping. The toy has no nominal struct types: `BodyAx F v` relates the unfolded body types
`F.subst A` and `F.subst B` themselves, so a declared variance stricter than `inferVar` cannot
suppress the built-in structural coercions between them (`bodyAx_inv_still_covariant`), and a
declared variance more permissive than `inferVar` adds coercions between ordinary built-in types
(`bodyAx_param_contra_coerces_bare_refs`). It models "what if the compiler accepted the
declaration `struct S<T>(F)` at variance `v`", with the struct unfolded to its body. -/
def BodyAx (F : Ty) (v : Variance) (S T : Ty) : Prop :=
  ∃ A B : Ty, A.closed = true ∧ B.closed = true ∧ S = F.subst A ∧ T = F.subst B ∧
    Variance.Rel v (SubGen rustTable NoAx) A B

/-- `T.dataBodyAt underRef`: `T` is built from `unit`, `nat`, `param`, tuples, `ref`, `refMut`,
and `cell`, where every `cell` sits directly under a `ref` (`underRef` records whether `T`
itself sits directly under a `ref`). -/
def Ty.dataBodyAt : Bool → Ty → Bool
  | _, .unit => true
  | _, .nat => true
  | _, .param => true
  | _, .prod A B => A.dataBodyAt false && B.dataBodyAt false
  | _, .ref _ T => T.dataBodyAt true
  | _, .refMut _ T => T.dataBodyAt false
  | underRef, .cell T => underRef && T.dataBodyAt false
  | _, .fn _ _ => false
  | _, .phantom _ => false

/-- First-order data bodies: built from `unit`, `nat`, `param`, tuples, `ref`, `refMut`, and
`Cell` directly under a shared reference (`ref ℓ (cell T)`). Excluded: function types, bare
`cell` (not directly under `ref`, e.g. a tuple field or `refMut ℓ (cell T)`), and `PhantomData`. -/
def Ty.dataBody (F : Ty) : Bool := F.dataBodyAt false

end Toy.Variance
