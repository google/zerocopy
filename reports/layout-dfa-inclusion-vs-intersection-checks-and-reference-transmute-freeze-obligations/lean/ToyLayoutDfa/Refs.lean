import ToyLayoutDfa.Basic

/-!
# A toy reference model: bit validity, `Freeze`, and the `frozen` / `unique` assertions

A reference cast reinterprets one region of memory, the *referent*, at a second type. The
model has two *views* of the region: the source view (typed at the source referent `S`,
reached through the original reference) and the destination view (typed at the
destination referent `D`, reached through the cast reference). The two referents cover
the same region; sizes are not modelled separately (a referent type is its validity
predicate on the region's whole contents).

* A referent type (`RefTy`) is a bit-validity predicate on byte strings plus one flag,
  `freeze`, for the *whole* region: `true` means the type has no interior mutability
  (Rust's `Freeze`); `false` means that a shared view may overwrite the whole region with
  any byte string valid at its type (uniform, unrestricted `Cell`-like interior
  mutability). Per-byte placement of interior mutability, restricted-write APIs and
  synchronisation are not expressible.
* `Mode` is the kind of a reference: `shared` (`&T`) or `mutable` (`&mut T`). A cast is given
  by the mode of the source reference `ms` and of the destination reference `md`.
* While the cast reference is live, each view may perform the operations its capability
  allows (`Permitted`): the destination view may read; it may write any `D`-valid value
  if it is a `&mut` or if `D` is not `Freeze`. The source view is active during the cast
  if and only if the source reference is shared (a shared reference stays usable after it is
  copied); it may then read, and write any `S`-valid value if `S` is not `Freeze`. A
  source `&mut` is treated as reborrowed and inactive while the cast reference is live
  (pointer provenance and aliasing tags of a bit-level transmute are not modelled).
* After the cast reference dies, the source side reads the region at `S` (the owner of a
  `&mut` resumes; the original `&` keeps being used).
* Each live view also relies on an assertion (`OpOK`): every read through a view sees
  bytes valid at the view's type (bit validity); while a live shared reference to a
  `Freeze` referent exists, nothing writes the region (the `frozen` assertion); while a
  live `&mut` destination exists, the source view does not access the region (the
  `unique` assertion).
* `Sound ms md S D`: from every `S`-valid initial contents, every finite sequence of
  permitted operations satisfies every assertion (`RunOK`). Because every write replaces
  the whole region and the final check reads at `S`, this is equivalent to a one-operation
  condition (`sound_iff_soundOneStep`).

Aliasing models beyond these two assertions (Stacked Borrows, Tree Borrows), lifetimes,
per-byte placement of interior mutability, alignment, sizes, concurrency, destructors and
library safety invariants are not modelled.
-/

namespace Toy.LayoutDfa

/-- A referent type: a bit-validity predicate on byte strings (`valid`) and a `Freeze`
flag for the whole region (`freeze = true`: no interior mutability; `freeze = false`:
shared views may overwrite the whole region with any valid byte string). Meant to capture
the two facts about a referent that the reference cells of the obligation matrix consult.
Two referent types may have the same validity and differ in `freeze` (as `u8` and
`Cell<u8>` do). -/
structure RefTy where
  valid : List Sym → Prop
  freeze : Bool

/-- The referent type with the language of layout `A` as its validity and `freeze` flag
`fz`. -/
def RefTy.ofLayout (A : Layout) (fz : Bool) : RefTy := ⟨A.Lang, fz⟩

/-- Validity inclusion: every `S`-valid byte string is `D`-valid. -/
def Includes (S D : RefTy) : Prop := ∀ m, S.valid m → D.valid m

/-- Some byte string is valid at `S` (the referent type is inhabited at the byte level). -/
def Satisfiable (S : RefTy) : Prop := ∃ m, S.valid m

/-- The kind of a reference: shared (`&T`) or mutable (`&mut T`). -/
inductive Mode where
  | shared
  | mutable
  deriving DecidableEq, Repr

/-- The two views of the region: through the source reference or through the cast
(destination) reference. -/
inductive View where
  | src
  | dst
  deriving DecidableEq, Repr

/-- An operation on the region during the cast: a read through a view, or a write of a
whole byte string through a view. -/
inductive Op where
  | read (v : View)
  | write (v : View) (bytes : List Sym)

/-- The referent type a view is typed at. -/
def viewTy (S D : RefTy) : View → RefTy
  | .src => S
  | .dst => D

/-- The capability of each view while the cast reference is live (see the module
comment): which operations code holding the references may perform. -/
def Permitted (ms md : Mode) (S D : RefTy) : Op → Prop
  | .read .src => ms = .shared
  | .read .dst => True
  | .write .src b => ms = .shared ∧ S.freeze = false ∧ S.valid b
  | .write .dst b => (md = .mutable ∨ D.freeze = false) ∧ D.valid b

/-- Some view that is live during the cast is a shared reference to a `Freeze` referent,
so the `frozen` assertion is in force: the region must not be written. -/
def FrozenDuring (ms md : Mode) (S D : RefTy) : Prop :=
  (ms = .shared ∧ S.freeze = true) ∨ (md = .shared ∧ D.freeze = true)

/-- The assertions one operation must satisfy at current contents `m`: a read sees bytes
valid at the reading view's type; a write requires that no `frozen` assertion is in
force; and while a `&mut` destination is live, the source view performs no operation
(the `unique` assertion). -/
def OpOK (ms md : Mode) (S D : RefTy) (m : List Sym) : Op → Prop
  | .read v => (viewTy S D v).valid m ∧ ¬ (md = .mutable ∧ v = .src)
  | .write v _ => ¬ FrozenDuring ms md S D ∧ ¬ (md = .mutable ∧ v = .src)

/-- The contents after an operation. -/
def Op.next (m : List Sym) : Op → List Sym
  | .read _ => m
  | .write _ b => b

/-- `RunOK ms md S D m ops`: performing `ops` during the cast from contents `m` satisfies
every assertion, and afterwards the source side reads bytes valid at `S`. -/
def RunOK (ms md : Mode) (S D : RefTy) : List Sym → List Op → Prop
  | m, [] => S.valid m
  | m, op :: ops => OpOK ms md S D m op ∧ RunOK ms md S D (op.next m) ops

/-- Soundness of an unchecked reference cast from a `ms`-reference to `S` to an
`md`-reference to `D`: from every `S`-valid initial contents, every finite sequence of
permitted operations satisfies every assertion. -/
def Sound (ms md : Mode) (S D : RefTy) : Prop :=
  ∀ m, S.valid m → ∀ ops : List Op, (∀ op ∈ ops, Permitted ms md S D op) → RunOK ms md S D m ops

/-- The reference obligation matrix as a rule on the four mode pairs (equal-size
referents assumed by the model):
* `& → &`: `S ⊆ D`, `D: Freeze` and `S: Freeze`;
* `&mut → &`: `S ⊆ D` and `D: Freeze`;
* `&mut → &mut`: `S ⊆ D` and `D ⊆ S`;
* `& → &mut`: rejected. -/
def MatrixOK : Mode → Mode → RefTy → RefTy → Prop
  | .shared, .shared, S, D => Includes S D ∧ D.freeze = true ∧ S.freeze = true
  | .mutable, .shared, S, D => Includes S D ∧ D.freeze = true
  | .mutable, .mutable, S, D => Includes S D ∧ Includes D S
  | .shared, .mutable, _, _ => False

/-- The obligation matrix with the source-side `Freeze` obligation removed from the
`& → &` cell (all other cells as in `MatrixOK`). -/
def MatrixOKNoSrcFreeze : Mode → Mode → RefTy → RefTy → Prop
  | .shared, .shared, S, D => Includes S D ∧ D.freeze = true
  | .mutable, .shared, S, D => Includes S D ∧ D.freeze = true
  | .mutable, .mutable, S, D => Includes S D ∧ Includes D S
  | .shared, .mutable, _, _ => False

/-- A Boolean reference checker on layouts: the obligation matrix with every validity
inclusion decided by `forallCheck` and the `Freeze` flags supplied by the caller (they
are trusted inputs, not computed from the layouts, which cannot distinguish `u8` from
`Cell<u8>`). -/
def refCheck : Mode → Mode → Layout → Bool → Layout → Bool → Bool
  | .shared, .shared, S, fzS, D, fzD => forallCheck S D && fzD && fzS
  | .mutable, .shared, S, _, D, fzD => forallCheck S D && fzD
  | .mutable, .mutable, S, _, D, _ => forallCheck S D && forallCheck D S
  | .shared, .mutable, _, _, _, _ => false

end Toy.LayoutDfa
