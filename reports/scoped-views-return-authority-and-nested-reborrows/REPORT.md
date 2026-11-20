# Scoped views over raw-pointer-owned memory: return authority, nested reborrows, and closed views (Lean toy model)

## Summary

This package is a Lean 4 formalization of a toy memory model in which *views* lend exclusive
(`&mut`-like) and shared (`&`-like) access to raw-pointer-owned memory, nested to any depth, and in
which ending a view hands its cells back to its parent. Every result below is a kernel-checked
theorem about that toy model (no `sorry`; axioms at most `propext`, `Classical.choice`,
`Quot.sound`). Card identifiers are labels only and are not contiguous: there are no cards R3b,
R3e, or R4b–R4f, and no result of this package is missing at those labels. One sentence per
result, with its key hypotheses:

- **R1a** (impossibility). Under the *naive end rule* ("an active parent that holds a child's cells
  as outstanding loans may end that child", which inspects neither the child's own cells nor its
  descendants), a nested exclusive reborrow (root `A` lends cell 0 to `B`, `B` relends it to `C`)
  leads from states satisfying all seven loan-tree laws and write exclusivity to a state in which
  both `A` and `C` can write cell 0 and `A` regained access while its active descendant `C` still
  covers the cell, for every byte handed back; without the nested reborrow the same end is safe
  (positive control).
- **R1b** (impossibility). The same for a nested shared reborrow: after the naive end of `B` in the
  state where `A` shares cell 0 with `B` and `B` re-shares it with `C`, `A` is writable again while
  `C` still reads cell 0; without nesting the end is safe (positive control).
- **R2a**. If a state satisfies the five tree-local laws (`ParentCoversActive`, `ExclChildLoaned`,
  `SharedChildBelowOwn`, `SharedChildrenShared`, `DepthCounts`) and view `c` has *return authority*
  (no active proper descendant of `c` covers a cell of `c`), then every successful raw end of `c`
  preserves the five local laws and gives no view access to a cell that an active proper descendant
  of it still covers; because every raw end preserves the two global laws `ParentLt` and
  `RootsDisjoint`, the full seven-law invariant is preserved too. Each of the six law/authority
  hypotheses is necessary.
- **R2b**. The seven loan-tree laws imply write exclusivity (a view that can write a cell excludes
  every other active reader or writer of it); each of the seven laws is necessary.
- **R2c** (corollary of R2a, R2b). Under the seven laws and return authority of `c`, a successful raw
  end of `c` leaves a write-exclusive state; each law and return authority is necessary, even from
  write-exclusive pre-states.
- **R2d**. Under `ParentCoversActive`, `ExclChildLoaned` and `DepthCounts`, a view that holds every
  cell it covers as an `own` cell at its own mode baseline depth (the *local return check*: it has
  lent nothing onward) has return authority; if moreover `SharedChildBelowOwn` and
  `SharedChildrenShared` hold, a successful raw end of such a view preserves the five local laws and
  resurrects nothing. Each of the five laws and the check is necessary.
- **R3a**. `ClosedViews` (old views keep parent link, activity flag and covered addresses; views
  created later are inactive) is reflexive and transitive.
- **R3c**. If view `v` has return authority in `s₀` and `ClosedViews s₀ s₁`, then `v` has return
  authority in `s₁`, provided every parent link of `s₀` points to an existing view (first form) or
  `ParentCoversActive s₁` holds (second form); the conclusion has operational content only for views
  that already exist in `s₀`. Each hypothesis is necessary.
- **R3d**. A single scope is closed: an opening step that keeps every existing view's parent link,
  activity flag and domain and adds exactly one view (`borrow` and `share` are such steps), followed
  by a closed inner computation and the raw end of exactly that fresh view, yields a state closed
  relative to the state before the scope. Each hypothesis is necessary.
- **R3f**. A successful write yields a state closed relative to the state before it.
- **R3g** (corollary of R3c, R2a). If `c` had return authority in `s₀`, `ClosedViews s₀ s₁`, and the
  five local laws hold in `s₁` (they are not carried over by `ClosedViews`), then a successful raw end
  of `c` in `s₁` preserves the five local laws and resurrects nothing. Each of the authority,
  closed-views and law hypotheses is necessary.
- **R3h**. Every *scoped run* (writes and well-bracketed `borrow`/`share` scopes that end exactly the
  view they opened, nested and sequenced to any depth) is closed; hence return authority survives
  any scoped run, provided `ParentCoversActive` holds afterwards.
- **R4a** (counterexamples). Each of the four `ClosedViews` conditions is necessary: dropping any one
  admits states in which a view with return authority before loses it after (with the full loan-tree
  invariant holding after), and ending it then breaks the local laws.
- **R4g** (counterexample). `ClosedViews` is sufficient but not necessary for keeping return
  authority: retiring an unrelated root violates it while return authority is kept.
- **R5a**. Under `DepthCounts`, an active view that holds a cell as an `own` cell can write it if and
  only if the view is exclusive-mode and none of its active shared children covers the cell; each
  hypothesis is necessary.
- **R5b** (counterexample). Exact per-view depth counters alone do not prevent the nested shared
  failure of R1b: after the naive end, `DepthCounts` still holds while `ParentCoversActive` and write
  exclusivity fail.

What these results do **not** show is listed first under **Boundaries** (per result); read a
result's non-claims before relying on it. In particular, nothing here is proved about Rust, Aeneas,
or any real memory model: the connection to real systems is a separately labelled modeling bridge.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: this is a toy model.** All definitions live in the Lean namespace `Toy.Views`
(concrete states and witnesses in `Toy.Views.Ex`) and are self-contained; none is a production
definition, and no production system is formalized or checked here.

*What the definitions are meant to capture.* A memory model that lends safe references out of
raw-pointer-owned memory, as needed by verification tools that translate Rust programs mixing raw
pointers with safe borrows: a *root view* stands for memory owned through a raw pointer; a *child
view* stands for a reference lent out of a parent view, exclusive or shared, nested to any depth.
Each view records its parent, its mode, an activity flag, and per-address cells `own d b` (accessible
byte `b`; writable iff the sharing depth `d` is `0`) or `loaned c` (exclusively lent to child `c`).
The design question the package informs is when ending a borrow (handing the child's cells back to
its parent) is authorized: is the naive parent-side rule sound once reborrows nest; what exactly is
needed for soundness, and can it be checked locally; and is a transitive *closed views* relation
between the states before and after a scope the right invariant for keeping outer return authority
across nested, completed scopes. The relation to one concrete prototype memory model is described
under *Modeling bridge* in **Findings**, labelled `derived (modeling bridge)`; it is motivation, not
a subject of this report.

*Known gaps between the toy and real systems* (each also recorded under **Boundaries**):

- no allocation or deallocation of roots, and no allocation lifetime separate from view activity;
- no addresses or layout beyond natural-number cell indices, no typed values, no pointer provenance;
- only permissions are tracked: bytes that different views hold for one address need not agree;
- no implicit heap of unmodelled safe loans: every reborrow is an explicit child view;
- no global compatibility check on steps: the raw end `endRaw` checks only the parent's
  placeholder cells (the *naive* rule), deliberately weaker than a real evaluator may be;
- the end operation merges "retire the child" and "restore the parent";
- one step relation only for `borrow`, `share`, `write`, `endRaw`; no concurrency, no function
  calls, no protectors, no dynamic invalidation of descendants;
- preservation of the loan-tree laws by `borrow`, `share` and `write` is not stated by any theorem.

*Scope of the formal results.* Each theorem states exactly what its Lean statement says over these
definitions; the plain-language claims in **Findings** are restatements of those Lean statements.
Quantifiers over view ids are bounded by `s.size` and over addresses by `s.width` (the longest cell
list); lemmas `State.isActive_lt_size` and `State.covers_lt_width` show these bounds are exact for
active views and covered addresses. Results R1a, R1b, R4a, R4g and R5b (like every counterexample, non-vacuity witness and positive control) are statements about specific
concrete states; R2, R3 and R5a are universally quantified over all states.

*Toolchain.* Lean `leanprover/lean4:v4.34.1`, core library and `Std` only: no Mathlib and no other
Lake dependency (`lean/lakefile.toml` declares one `[[lean_lib]]`, `ToyViews`, and no `[[require]]`).

*Subjects and their relationship.* `REPORT.json` lists the Lean 4 toolchain release, which is the
checker of every theorem, and the primary papers cited as prior art. The papers are not formalized
here; they are cited for the folklore or known results that individual cards restate, contrast, or
make precise in this toy vocabulary (see each card's prior art). An unmerged pull request to the
Aeneas repository is cited only as motivation and is deliberately not a subject.

## Findings

### Definitions (quoted verbatim from the Lean sources)

Every definition below is copied from the package's Lean sources, docstrings included; the results' statement and definition-closure hashes under **Evidence** fix them exactly.

#### State model and operations (`lean/ToyViews/Basic.lean`)

```lean
namespace Toy.Views

/-- View identifiers: positions in `State.views`. -/
abbrev ViewId := Nat
/-- Cell addresses: positions in `View.cells`. -/
abbrev Addr := Nat
/-- Byte contents (uninterpreted). -/
abbrev Byte := Nat

/-- How a view obtained its cells: exclusively (`excl`, read/write while no child holds them) or
shared (`shared`, read-only). Root views use the mode to say whether the raw memory they expose is
writable (`excl`) or read-only (`shared`). -/
inductive Mode where
  | excl
  | shared
  deriving DecidableEq, Repr

/-- A per-view cell: `own depth byte` (accessible; writable iff `depth = 0`) or `loaned child`
(exclusively lent to `child`; inaccessible here). -/
inductive Cell where
  | own (depth : Nat) (byte : Byte)
  | loaned (child : ViewId)
  deriving DecidableEq, Repr

/-- A view: parent link (`none` for a root), mode, activity flag, and address-indexed cells
(`none` = address not covered by this view). -/
structure View where
  parent : Option ViewId
  mode : Mode
  active : Bool
  cells : List (Option Cell)
  deriving DecidableEq, Repr

/-- A state: the list of all views ever created; the view with id `v` is `views[v]`. -/
structure State where
  views : List View
  deriving DecidableEq, Repr

/-- The depth of a cell, if it is accessible (`own`). -/
def Cell.depth? : Cell → Option Nat
  | .own d _ => some d
  | .loaned _ => none

/-- The mode baseline depth: `0` for exclusive views, `1` for shared views. -/
def Mode.baseline : Mode → Nat
  | .excl => 0
  | .shared => 1

/-- The cell of a view at address `a`, if covered. -/
def View.cell? (vw : View) (a : Addr) : Option Cell := vw.cells.getD a none

/-- The addresses a view covers, in increasing order. -/
def View.domain (vw : View) : List Addr :=
  (List.range vw.cells.length).filter (fun a => (vw.cell? a).isSome)

namespace State

/-- Number of views ever created (= the next fresh id). -/
def size (s : State) : Nat := s.views.length

/-- An upper bound on all covered addresses: the longest cell list. -/
def width (s : State) : Nat := s.views.foldr (fun vw m => max vw.cells.length m) 0

/-- The view with id `v`, if it exists. -/
def view? (s : State) (v : ViewId) : Option View := s.views[v]?

/-- The cell of view `v` at address `a`, if `v` exists and covers `a`. -/
def cell? (s : State) (v : ViewId) (a : Addr) : Option Cell := (s.view? v).bind (·.cell? a)

/-- The depth of view `v`'s cell at `a`, if that cell exists and is accessible. -/
def depth? (s : State) (v : ViewId) (a : Addr) : Option Nat := (s.cell? v a).bind Cell.depth?

/-- The parent of view `v` (`none` if `v` is a root or does not exist). -/
def parentOf (s : State) (v : ViewId) : Option ViewId := (s.view? v).bind View.parent

/-- The mode of view `v`, if it exists. -/
def modeOf (s : State) (v : ViewId) : Option Mode := (s.view? v).map View.mode

/-- Whether view `v` exists and is active. -/
def isActive (s : State) (v : ViewId) : Bool := ((s.view? v).map View.active).getD false

/-- Whether view `v` exists and covers address `a`. -/
def covers (s : State) (v : ViewId) (a : Addr) : Bool := (s.cell? v a).isSome

/-- The mode baseline of view `v` (`0` if `v` does not exist). -/
def baselineOf (s : State) (v : ViewId) : Nat := ((s.modeOf v).map Mode.baseline).getD 0

/-- Read access: `v` is active and holds `a` as an `own` cell (any depth). Access through an
inactive view is impossible by construction. -/
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome

/-- Write access: `v` is active and holds `a` as an `own` cell of depth `0`. -/
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0

/-- Access level of `v` at `a`: `2` write, `1` read-only, `0` none. -/
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0

/-- Number of active shared-mode children of `v` that cover `a` (the readers `v` has lent `a`
to). -/
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length

/-- Replace view `v` (no effect if `v` does not exist). -/
def setView (s : State) (v : ViewId) (vw : View) : State := ⟨s.views.set v vw⟩

end State

/-! ## Operations -/

/-- Rewrite every cell of a view through `f` (applied to all addresses below `n`). -/
def View.mapCells (vw : View) (n : Nat) (f : Addr → Option Cell → Option Cell) : View :=
  { vw with cells := (List.range n).map (fun a => f a (vw.cell? a)) }

/-- Is `x` an `own` cell of depth `0`? -/
def Cell.isWritable : Option Cell → Bool
  | some (.own 0 _) => true
  | _ => false

/-- Is `x` an `own` cell (any depth)? -/
def Cell.isOwn : Option Cell → Bool
  | some (.own _ _) => true
  | _ => false

/-- The byte of an `own` cell (`0` otherwise; only used on `own` cells). -/
def Cell.byteOf : Option Cell → Byte
  | some (.own _ b) => b
  | _ => 0

/-- Create an exclusive child of active exclusive-mode view `p` covering addresses `A` (all of
which `p` must hold writable). The parent's cells become `loaned c` for the fresh id `c`; the child
holds them at depth `0` with the same bytes. -/
def borrow (s : State) (p : ViewId) (A : List Addr) : Option State :=
  match s.view? p with
  | none => none
  | some vp =>
    if vp.active && vp.mode == .excl && A.all (fun a => Cell.isWritable (vp.cell? a)) then
      let c := s.size
      let n := vp.cells.length
      let vp' := vp.mapCells n (fun a x => if A.contains a then some (.loaned c) else x)
      let vc : View :=
        { parent := some p, mode := .excl, active := true,
          cells := (List.range n).map (fun a =>
            if A.contains a then some (.own 0 (Cell.byteOf (vp.cell? a))) else none) }
      some ⟨(s.views.set p vp') ++ [vc]⟩
    else none

/-- Create a shared child of active view `p` covering addresses `A` (all of which `p` must hold as
`own` cells). The parent's depth at each address goes up by one; the child holds the cells at its
baseline depth `1` with the same bytes. -/
def share (s : State) (p : ViewId) (A : List Addr) : Option State :=
  match s.view? p with
  | none => none
  | some vp =>
    if vp.active && A.all (fun a => Cell.isOwn (vp.cell? a)) then
      let n := vp.cells.length
      let vp' := vp.mapCells n (fun a x =>
        if A.contains a then
          match x with
          | some (.own d b) => some (.own (d + 1) b)
          | y => y
        else x)
      let vc : View :=
        { parent := some p, mode := .shared, active := true,
          cells := (List.range n).map (fun a =>
            if A.contains a then some (.own 1 (Cell.byteOf (vp.cell? a))) else none) }
      some ⟨(s.views.set p vp') ++ [vc]⟩
    else none

/-- Write byte `b` at `a` through `v`; enabled iff `v` can write `a`. -/
def write (s : State) (v : ViewId) (a : Addr) (b : Byte) : Option State :=
  match s.view? v with
  | none => none
  | some vw =>
    if s.canWrite v a then
      some (s.setView v (vw.mapCells vw.cells.length (fun a' x => if a' = a then some (.own 0 b) else x)))
    else none

/-- Read the byte at `a` through `v`; enabled iff `v` can read `a`. -/
def read (s : State) (v : ViewId) (a : Addr) : Option Byte :=
  if s.canRead v a then some (Cell.byteOf (s.cell? v a)) else none

/-- Is parent view `vp` active, and does it hold every cell covered by child view `vc` (with id
`c`) as an *outstanding loan* — `loaned c` if `vc` is exclusive, and an `own` cell whose depth is
strictly above `vp`'s own mode baseline (so at least one shared loan is outstanding) if `vc` is
shared? This is the only check the raw end operation performs: the parent that is active and holds
the child's cells in loaned-out form may take them back. Nothing about the child's own cells or
descendants is inspected. -/
def returnable (vc vp : View) (c : ViewId) : Bool :=
  vp.active && (List.range vc.cells.length).all fun a =>
    match vc.cell? a with
    | none => true
    | some _ =>
      match vc.mode, vp.cell? a with
      | .excl, some (.loaned c') => c' == c
      | .shared, some (.own d _) => decide (vp.mode.baseline < d)
      | _, _ => false

/-- The parent's cells after child `vc` returns: each cell covered by an exclusive child becomes
writable again with the supplied byte `r a` (the value handed back by the borrow's continuation);
each cell covered by a shared child has its depth decremented. -/
def restoreCells (vc vp : View) (r : Addr → Byte) : View :=
  vp.mapCells (max vp.cells.length vc.cells.length) fun a x =>
    match vc.cell? a with
    | none => x
    | some _ =>
      match vc.mode, x with
      | .excl, _ => some (.own 0 (r a))
      | .shared, some (.own (d + 1) b) => some (.own d b)
      | .shared, y => y

/-- Raw end of view `c`: retire `c` and give its cells back to its parent. Enabled iff `c` is
active, has an existing parent, and that parent is active and holds all of `c`'s cells as
outstanding loans (`returnable`). Nothing about `c`'s own cells or descendants is checked: this is
the *naive* rule "the parent holding the loaned-out cells may end the borrow". Root views (no
parent) can never be ended by this operation. Sound uses must additionally establish
`ReturnAuthority`. -/
def endRaw (s : State) (c : ViewId) (r : Addr → Byte) : Option State :=
  match s.view? c with
  | none => none
  | some vc =>
    match vc.parent with
    | none => none
    | some p =>
      match s.view? p with
      | none => none
      | some vp =>
        if vc.active && returnable vc vp c then
          let s₁ := s.setView p (restoreCells vc vp r)
          match s₁.view? c with
          | none => none
          | some vc₁ => some (s₁.setView c { vc₁ with active := false })
        else none

end Toy.Views
```

*Meaning.* A view is a handle on raw-pointer-owned memory (a root) or a reference lent out of
another view (a child): exclusive (`&mut`-like) or shared (`&`-like), nested to any depth. A
per-view cell `own d b` says the view can access byte `b`, read/write iff `d = 0`; `loaned c`
says the cell is lent exclusively to child `c`. Depth is a counter: mode baseline (`0` for
exclusive views, `1` for shared views) plus the number of active shared children reading the
cell (enforced by the law `DepthCounts`, not by the type). Ids are never reused. Only permissions
are tracked: the bytes that different views hold for one address need not agree.

*Operations* (all `Option`-valued; `none` = not enabled):

* `borrow s p A` — enabled iff `p` exists, is active, is exclusive-mode, and holds every
  `a ∈ A` as `own 0 _`. Effect: `p`'s cells at `A` become `loaned c` (`c = s.size`); a new view
  `c` is appended with parent `p`, mode `excl`, active, cells `own 0 b` at `A` (same bytes). `A`
  may be empty (the new view then covers nothing).
* `share s p A` — enabled iff `p` exists, is active, and holds every `a ∈ A` as `own _ _`.
  Effect: `p`'s depth at each `a ∈ A` goes up by one; new view `c` (parent `p`, mode `shared`,
  active) holds `own 1 b` at `A`.
* `write s v a b` — enabled iff `s.canWrite v a`; sets the cell to `own 0 b`.
* `read s v a` — enabled iff `s.canRead v a`; returns the byte.
* `endRaw s c r` — **the naive end**. Enabled iff `c` exists and is active, has a parent `p`
  that exists, and `returnable vc vp c` holds (quoted above): the parent is active and holds
  each cell covered by `c` as `loaned c` (exclusive child) or as `own d _` with `d` strictly
  above the parent's own mode baseline (shared child).
  Effect: every cell `a` covered by `c` becomes, in the parent, `own 0 (r a)` if `c` is
  exclusive (`r` is the value handed back by the borrow's continuation) or `own d b` (depth
  decremented) if `c` is shared; then `c.active := false`. Nothing about `c`'s own cells or
  descendants is checked. Root views (no parent) can never be ended.

*Proved adequacy lemmas:* `endRaw_isSome_iff : (endRaw s c r).isSome ↔ NaiveAuthority s c`;
`endRaw_eq_none_of_parentOf_eq_none` (roots); `read_isSome_imp_isActive`,
`write_isSome_imp_isActive` (access requires activity — the first clause of the safety property
holds by construction); `isActive_lt_size`, `covers_lt_width` (bounded quantifiers below are
exact); `writeExclusive_iff_unbounded : WriteExclusive s ↔ ∀ v w a, v ≠ w → s.canWrite v a = true →
s.canRead w a = false` (the bounded definition of `WriteExclusive`, quoted below, is equivalent to
its unbounded form).

*Operation examples* (`Authority.lean`): `borrow_s0`, `borrow_s1` (succeed), `borrow_s1_A_none`
(loaned cell), `borrow_t1_B_none` (shared view cannot lend exclusively), `share_s0`,
`share_t1`, `share_s1_A_none`, `endRaw_s1_B`, `endRaw_s2_B`, `endRaw_s2_C`, `endRaw_t1_B`,
`endRaw_t2_B`, `endRaw_u2_B`, `endRaw_s2_A_none` (root), `not_naiveAuthority_s3_B` (retired),
`read_s1_B`, `read_s1_A_none`, `read_s1e_B_none`, `write_t1_A_none`. Two further example theorems
evaluate the access, level, counting and domain functions on the named states:

```lean
theorem access_examples :
    s1.canWrite 1 0 = true ∧ s1.canRead 0 0 = false ∧ t1.canRead 0 0 = true ∧
    t1.canWrite 0 0 = false ∧ t1.canRead 1 0 = true ∧ t1.canWrite 1 0 = false ∧
    (s1e 0).canRead 1 0 = false ∧ s1.level 1 0 = 2 ∧ t1.level 0 0 = 1 ∧ s1.level 0 0 = 0
theorem count_domain_examples :
    u2.activeSharedChildren 0 0 = 2 ∧ u2e.activeSharedChildren 0 0 = 1 ∧
    t2.activeSharedChildren 0 0 = 1 ∧ (w2.view? 1).map View.domain = some [0] ∧
    (w2.view? 2).map View.domain = some [1] ∧ (w2.view? 0).map View.domain = some [0, 1]
```

#### Structural laws of the loan tree and write exclusivity (`lean/ToyViews/Laws.lean`)

```lean
/-- Every parent link points to an existing view. -/
def ParentsExist (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < s.size

/-- Parents are created before their children: every parent link points to a smaller id. (Implies
`ParentsExist` and acyclicity of the parent relation.) -/
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v

/-- An active view's cells are covered by its parent, and that parent is active: a reborrow never
outlives, or reaches beyond, the view it was taken from. -/
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true

/-- Every cell covered by an active exclusive child is recorded in its parent as loaned to that
child. -/
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)

/-- Every cell covered by an active shared child is held by its parent as an `own` cell of
positive depth (the parent is read-only there while the child reads). -/
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)

/-- Active children of shared views are shared: a read-only view cannot lend exclusively. -/
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared

/-- Depth is a counter: the depth of an active view's accessible cell equals the view's mode
baseline plus the number of active shared children reading that cell. -/
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a

/-- Distinct active root views cover disjoint addresses (each raw-pointer-owned cell has one
owner). -/
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false

/-- The loan-tree invariant: all seven structural laws. -/
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s

/-- The five *tree-local* laws: the laws that relate a view only to its parent and its direct
children (`ParentCoversActive`, `ExclChildLoaned`, `SharedChildBelowOwn`, `SharedChildrenShared`,
`DepthCounts`). The remaining two laws of `LoanTreeInv` are global: `ParentLt` (well-founded parent
links) and `RootsDisjoint` (one active root per cell). Ending a view never touches parent links,
domains or roots, so the two global laws are preserved by every raw end
(`endRaw_preserves_parentLt`, `endRaw_preserves_rootsDisjoint`); the five local laws are the ones
whose preservation needs return authority. -/
structure LocalLoanLaws (s : State) : Prop where
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s

/-- Write exclusivity: a view that can write a cell is the only active view that can access it
(no two writers, and no reader beside a writer). -/
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false
```

The five *local* laws relate a view only to its parent and direct children; the two *global* laws
are `ParentLt` (well-founded parent links) and `RootsDisjoint` (one active root per cell). Every raw
end preserves the global laws unconditionally (frame lemmas `endRaw_preserves_parentLt`, `endRaw_preserves_rootsDisjoint`).

| law | captures | positive example | negative example |
|---|---|---|---|
| `ParentsExist` | parent links resolve | `laws_hold_on_intended_states` (`s2`) | `parentsExist_example_neg`, `eS0` |
| `ParentLt` | parents created before children (acyclic) | `laws_hold_on_intended_states` | `cxParentLt`, `weParentLt` (self-parent) |
| `ParentCoversActive` | a reborrow neither outlives nor exceeds its parent | same | `cxParentCoversActive`, `weParentCoversActive` |
| `ExclChildLoaned` | parent records exclusive loans | same | `cxExclChildLoaned`, `weExclChildLoaned` |
| `SharedChildBelowOwn` | parent of a reader is read-only there | same | `cxSharedChildBelowOwn`, `weSharedChildBelowOwn` |
| `SharedChildrenShared` | read-only views do not lend exclusively | same | `cxSharedChildrenShared`, `weSharedChildrenShared` |
| `DepthCounts` | depth is a reader counter | same | `cxDepthCounts`, `weDepthCounts` |
| `RootsDisjoint` | one raw owner per cell | same | `cxRootsDisjoint`, `weRootsDisjoint` |
| `LocalLoanLaws` | the five local laws | `localLoanLaws_examples` (`s2`, and `cxParentLt`, which violates `ParentLt`) | `localLoanLaws_examples` (`cxDepthCounts`) |

(`laws_hold_on_intended_states` proves `LoanTreeInv` for `s0 s1 s2 t1 t2 u2 w2`; each negative
example violates exactly the named law, proved inside the counterexample theorems listed in the result cards.)

#### Descendants, authority, the naive rule, the local check, no-resurrection (`lean/ToyViews/Authority.lean`)

```lean
/-- `ProperDesc s d c`: `d` is a proper descendant of `c`, i.e. following parent links from `d`
(through existing views) reaches `c` in one or more steps. Retired views still count: being
inactive does not cut a view out of the tree. -/
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c

/-- **Return authority** for ending view `c`: no active proper descendant of `c` covers any cell
that `c` covers. -/
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false

/-- **The naive rule**: "the parent holding the loaned-out cells may end the borrow". View `c`
exists and is active, has an existing parent, and that parent is active and holds every cell `c`
covers as an outstanding loan (`loaned c` for an exclusive child; an `own` cell at a depth strictly
above the parent's own mode baseline for a shared child). Here "the parent owns the loaned-out
cells" refers to the *parent's* placeholder cells, not to the child's cells. Nothing is required of
`c`'s own cells or of `c`'s descendants. -/
def NaiveAuthority (s : State) (c : ViewId) : Prop :=
  ∃ vc p vp, s.view? c = some vc ∧ vc.active = true ∧ vc.parent = some p ∧
    s.view? p = some vp ∧ returnable vc vp c = true

/-- **Local return check** on view `c`: every cell `c` covers is held by `c` itself as an `own`
cell at exactly `c`'s mode baseline depth (`0` for an exclusive view, `1` for a shared view), i.e.
`c` has lent none of its cells onward, exclusively or shared. Unlike `ReturnAuthority`, it inspects
only `c`'s own cells, not `c`'s descendants. -/
def LocalReturnCheck (s : State) (c : ViewId) : Prop :=
  ∀ a < s.width, s.covers c a = true → s.depth? c a = some (s.baselineOf c)

/-- **No resurrection** across a step `s → s'`: whenever some view `u` gains access to a cell
(its access level goes up), no active proper descendant of `u` still covers that cell in `s'`. -/
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false
```

"Owning the loaned-out cells" in the naive rule refers to the *parent's* placeholder cells
(`loaned c`, or a depth above the parent's baseline), not to the child's cells. Retired views stay
in the tree (a retired child does not cut off an active grandchild). `ReturnAuthority` is
cell-wise: an active descendant covering no cell does not block it.

Examples: `properDesc_s2_C_A` / `not_properDesc_s2_A_C`; `returnAuthority_s2_C`,
`returnAuthority_s1_B`, `returnAuthority_t2_C` / `not_returnAuthority_s2_B`,
`not_returnAuthority_t2_B`; `naiveAuthority_s2_B`, `naiveAuthority_t2_B` (hold although unsafe) /
`not_naiveAuthority_s2_A` (root), `not_naiveAuthority_weExclChildLoaned_B` (loan not recorded),
`not_naiveAuthority_t2flat_C` (shared parent at its own baseline), `not_naiveAuthority_s3_C`
(retired parent), `not_naiveAuthority_aS0_C` (retired child), `not_naiveAuthority_s3_B`;
`localReturnCheck_examples_pos` (`s1`/`t1` view `B`, `s2` view `C`) /
`localReturnCheck_examples_neg` (`s2` and `t2` view `B` — the ends R1 exploits). Helper lemmas
(proved), used to decide `ReturnAuthority` and `NoResurrection` on concrete states: each replaces
the inductive relation `ProperDesc` by an explicit list `S` of views that contains every child of
the ended view (resp. of `u`) and every child of a member of `S`:

```lean
theorem ProperDesc.mem_of_closed {s : State} {c : ViewId} {S : List ViewId}
    (h : ∀ d < s.size, ∀ p, s.parentOf d = some p → (p = c ∨ p ∈ S) → d ∈ S) :
    ∀ {d}, ProperDesc s d c → d ∈ S
theorem returnAuthority_of_closed {s : State} {c : ViewId} (S : List ViewId)
    (hS : ∀ d < s.size, ∀ p, s.parentOf d = some p → (p = c ∨ p ∈ S) → d ∈ S)
    (hA : ∀ d ∈ S, s.isActive d = true → ∀ a < s.width, s.covers c a = true →
      s.covers d a = false) :
    ReturnAuthority s c
theorem noResurrection_of_closed {s s' : State} (S : ViewId → List ViewId)
    (hS : ∀ u < s'.size, ∀ d < s'.size, ∀ p, s'.parentOf d = some p → (p = u ∨ p ∈ S u) →
      d ∈ S u)
    (hA : ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
      ∀ d ∈ S u, s'.isActive d = true → s'.covers d a = false) :
    NoResurrection s s'
```

*The safety property.*

1. *No access through an inactive view*: by construction (`canRead`/`canWrite` require
   `isActive`; lemmas `read_isSome_imp_isActive`, `write_isSome_imp_isActive`).
2. *Write exclusivity* (state property `WriteExclusive`, quoted above): a writer excludes every other reader or writer; nothing is said about bytes
   (`loanTreeInv_allows_reader_byte_disagreement`). Examples: `writeExclusive_examples`
   (`s2`, `t2` hold; `t3` fails).
3. *No resurrection* (step property `NoResurrection`, quoted above): whenever a view's access level to a cell goes up, no active proper descendant of it still
   covers that cell. (Interpretation of "ending a view never resurrects access for a view whose
   child is still active", with *descendant* in place of *child*: in the nested trace of R1a the
   resurrected view's direct child is retired and its grandchild is active.) The level is coarse
   (none / read / write): a step that lowers a depth from 2 to 1 is not an increase, so a single
   unsound step can satisfy both `WriteExclusive` and `NoResurrection`
   (`naive_shared_end_hidden_by_sibling_reader`); the inductive safety criterion is the
   invariant `LoanTreeInv`. Examples: `noResurrection_s1_end_B` (holds),
   `not_noResurrection_s2_end_B` (fails).

#### Frame lemmas (`lean/ToyViews/Frame.lean`)

`returnable_spec` (what `returnable` guarantees per covered address), `returnable_parent_active`,
`restoreCells_domain` (ending a child keeps the parent's domain), `endRaw_unpack`, `endRaw_size`,
`endRaw_parentOf`, `endRaw_covers`, `endRaw_isActive` (only the ended view changes activity, to
`false`), `endRaw_modeOf`, `endRaw_baselineOf`, and the two global-law frame lemmas

```lean
theorem endRaw_preserves_parentLt {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hlt : ParentLt s) (hend : endRaw s c r = some s') : ParentLt s'
theorem endRaw_preserves_rootsDisjoint {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hrd : RootsDisjoint s) (hend : endRaw s c r = some s') : RootsDisjoint s'
```

together with `borrow_size`, `share_size` (one new view) and `write_size`.

#### Closed views, opening steps, scoped runs (`lean/ToyViews/Closed.lean`)

```lean
/-- Views existing in `s₀` still exist in `s₁` with the same parent link. -/
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent

/-- Views existing in `s₀` still exist in `s₁` with the same activity flag. -/
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active

/-- Views existing in `s₀` still exist in `s₁` and cover the same addresses. -/
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain

/-- Every view created after `s₀` is inactive in `s₁`. -/
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false

/-- **Closed views**: the four conditions above. -/
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁

/-- The *opening step* of a scope: views of `s` keep their parent link, activity flag and domain in
`s₁`, and exactly one view (the fresh id `s.size`) is added. Both `borrow` and `share` produce
such a step (`openScopeShape_of_borrow`, `openScopeShape_of_share`); cell contents and permission
forms of old views (in particular the parent's loaned cells) may change. -/
structure OpenScopeShape (s s₁ : State) : Prop where
  parents : ParentsStable s s₁
  activity : ActivityStable s s₁
  domains : DomainsStable s s₁
  size_eq : s₁.size = s.size + 1

/-- **Scoped runs**: the well-bracketed computations built from writes and from scopes that open a
fresh view by `borrow` or `share`, run a scoped inner computation, and then end exactly that fresh
view, composed sequentially. This is the syntax of "any number of nested, completed scopes". -/
inductive ScopedRun : State → State → Prop
  | refl (s : State) : ScopedRun s s
  | write {s s' : State} {v : ViewId} {a : Addr} {b : Byte} :
      write s v a b = some s' → ScopedRun s s'
  | borrowScope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr} {r : Addr → Byte} :
      borrow s p A = some s₁ → ScopedRun s₁ s₂ → endRaw s₂ s.size r = some s₃ → ScopedRun s s₃
  | shareScope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr} {r : Addr → Byte} :
      share s p A = some s₁ → ScopedRun s₁ s₂ → endRaw s₂ s.size r = some s₃ → ScopedRun s s₃
  | seq {s₀ s₁ s₂ : State} : ScopedRun s₀ s₁ → ScopedRun s₁ s₂ → ScopedRun s₀ s₂
```

Old views (ids below `s₀.size`) keep their *return shape* — parent, activity flag, covered
addresses — and still exist (the `Option.map` equalities force `some = some`); views created
after `s₀` are inactive in `s₁`. Everything else about old views is unconstrained: bytes, cell
permission forms (depths, loans), and also the view **mode** (`closedViews_ignores_modes`:
`ClosedViews t1 s1` with `B` changing from shared to exclusive, `LoanTreeInv` on both sides).
`ClosedViews` preserves neither `LoanTreeInv` (`closedViews_does_not_preserve_loanTreeInv`) nor
the parent cells an outer end needs (`closedViews_does_not_preserve_end_enabledness`), and the
model has no allocation lifetime. Fresh-id monotonicity is derivable here (`ParentsStable.size_le`); the
prototype discussed under *Modeling bridge* states it as a separate conjunct of its own `ClosedViews`
(derived (modeling bridge)). Examples:
`closedViews_example_pos` (`s1` → `s2e b`) / `closedViews_example_neg` (`s1` → `s2`, open scope);
`parentsStable_examples`, `activityStable_examples`, `domainsStable_examples`,
`newViewsInactive_examples`, `openScopeShape_examples` (each: positive and negative);
`scopedRun_example_pos` (`s0` → `runEnd`, two nested scopes and a write) /
`scopedRun_example_neg` (the open borrow `s1` → `s2` and the end of the old view `B` in `s2` are
genuine steps but not scoped runs, by `ScopedRun.isActive_eq`; and `s2` cannot reach `s1`, by
`ScopedRun.size_le`). Proved helpers: `openScopeShape_of_borrow`, `openScopeShape_of_share`,
`OpenScopeShape.isActive_old`, `write_isActive`, `ScopedRun.size_le`,
`ScopedRun.isActive_eq : ScopedRun s s' → s'.isActive u = if u < s.size then s.isActive u else false`
(a scoped run keeps every old view's activity and leaves every new view inactive; proved directly
by induction, independently of R3),
`parentsExist_of_parentLt_of_parentsStable`, `returnAuthority_vacuous_of_ge_size`,
`endRaw_eq_none_of_closedViews_of_ge_size`.

#### Named concrete states (`lean/ToyViews/States.lean`, `Naive.lean`, `EndSafe.lean`, `Closed.lean`)

Single address `0` unless stated; `A`,`B`,`C`,`D` = ids `0`,`1`,`2`,`3`; `x`/`s` = mode.

| state | views |
|---|---|
| `s0` | `A` root x active `own 0 0` |
| `s1` | `A` `loaned 1`; `B` (parent A, x, active) `own 0 0` |
| `s2` | `A` `loaned 1`; `B` `loaned 2`; `C` (parent B, x, active) `own 0 0` — nested exclusive reborrow |
| `s3 b` | naive end of `B` in `s2`: `A` `own 0 b`; `B` retired `loaned 2`; `C` active `own 0 0` |
| `s1e b`, `s2e b`, `s2ee b` | end of `B` in `s1`; end of `C` in `s2`; then end of `B` |
| `t1`, `t2` | `A` shares to `B` (`A` depth 1, `B` shared depth 1); `B` re-shares to `C` (`B` depth 2) |
| `t3` | naive end of `B` in `t2`: `A` `own 0 0` (writable), `C` still reads under retired `B` |
| `t1e`, `t2e`, `t2ee` | end of `B` in `t1`; end of `C` in `t2`; then end of `B` |
| `u2`, `u2e` | `A` depth 2 with shared children `B`, `C`; after ending `B`: `A` depth 1 |
| `w2` | two addresses: `A` lends `0` exclusively to `B` and shares `1` with `C` |
| `weExclChildLoaned` | `A` `own 0 0`; `B` (A, x, active) `own 0 0` (loan not recorded) |
| `t2flat` | as `t2` but `B` at depth `1` (its own baseline) with active shared child `C` |
| `aS0` | `A` `loaned 1`; `B` `loaned 2`; `C` (B, x, **retired**) `own 0 0` |
| `v2`, `v2e1`, `v2e2` | `A` depth 2, shared children `B₁`, `B₂`; `B₁` (depth 2) re-shared to `C`; naive end of `B₁`; then end of `B₂` |
| `e2`, `e3 b` | `s1` plus an active exclusive child `C` of `B` covering nothing (`borrow s1 1 []`); end of `B` |
| `byteIncoherent` | `A` x `own 1 42`; `B` (A, s) `own 1 99` |
| `rdParentCoversActive` | `A` `loaned 1`; `B` `own 0 0`; `C` (B, retired) `loaned 3`; `D` (C, active) `own 0 0` |
| `rdExclChildLoaned` | `A` `loaned 1`; `B` (A, x) `own 0 0`; `C` (B, x, active) `own 0 0` (loan not recorded) |
| `rdDepthCounts` | `A` x `own 1 0`; `B` (A, s) `own 1 0`; `C` (B, s, active) `own 1 0` (`B` at its baseline despite reader `C`) |
| `s2w`, `runMid`, `runEnd` | `C` writes `5` in `s2`; end of `C` (byte 7); end of `B` (byte 9) |
| `eS0`, `eS0open`, `eS1` | `A` `loaned 1`; `B` `loaned 3`; `C` (parent **3**, dangling, active) `own 0 0`; then `B` borrows the empty list (new view `3`); then view `3` ends |
| `g1`, `g1r` | two addresses: `A` lends `0` to `B`; unrelated root `R` owns `1`; then `R` retired |
| `s2open`, `t2open` | `s2` (resp. `t2`) plus an active child of `C` covering nothing |

Negative examples for the laws in R2b (`EndSafe.lean`; single address `0`; all views active unless
stated). Each violates exactly the named law, satisfies the other six of the seven laws, and is not
write-exclusive (proved in `Toy.Views.Ex.writeExclusive_needs_*`); `weExclChildLoaned` is listed
above:

| state | views |
|---|---|
| `weParentLt` | `A` root x `own 0 0`; `B` (parent **B**, s) `own 2 0` — a self-parented reader beside a writer root |
| `weParentCoversActive` | `A` root x `own 0 0`; `B` (A, x, **retired**) `loaned 2`; `C` (B, x) `own 0 0` — an active writer below a retired view, beside a writer root |
| `weSharedChildBelowOwn` | `A` root x `loaned 1`; `B` (A, x) `own 0 0`; `C` (A, s) `own 1 0` — a reader on a cell that `A` lent exclusively to `B` |
| `weSharedChildrenShared` | `A` root x `own 1 0`; `B` (A, s) `loaned 2`; `C` (B, x) `own 0 0` — a shared view that lent exclusively: `C` writes while `A` reads |
| `weDepthCounts` | `A` root x `own 1 0`; `B` (A, s) `own 0 0` — a shared child at depth `0` (below its baseline, so it writes) beside its reading parent |
| `weRootsDisjoint` | `A` root x `own 0 0`; `B` root x `own 0 0` — two active exclusive roots on the same cell |

Counterexample states for the hypotheses of R2a and R2c (single address `0`; the ended view in the last column):

| witness | views | end |
|---|---|---|
| `cxParentLt` | `A` x `own 1`; `B` (A, s) `own 1`; `C` (parent **C**, s) `own 2` | `B` |
| `cxParentCoversActive` | `A` `loaned 1`; `B` (A) `loaned 2`; `2` (B, retired) `own 0`; `X`=3 (A, retired) `loaned 4`; `Y`=4 (X, active) `own 0` | `B` |
| `cxExclChildLoaned` | `A` `loaned 1`; `B` (A) `loaned 2`; `2` (B, retired) `own 0`; `D`=3 (A, x, active) `own 0` | `B` |
| `cxSharedChildBelowOwn` | as above but `D` shared `own 1` | `B` |
| `cxSharedChildrenShared` | `A` `own 1`; `B` (A, s) `loaned 2`; `C` (B, **x**) `loaned 3`; `3` (C, retired) `own 0` | `C` |
| `cxDepthCounts` | `A` `own 1`; `B`, `C` (A, s) `own 1` each | `B` |
| `cxRootsDisjoint` | `A` root x `own 1`; `R` root s `own 1`; `B` (A, s) `own 1` | `B` |

### Result cards

Common design question (all cards except R5a and R5b): A memory model that lends safe references (exclusive and shared, possibly nested) out of raw-pointer-owned memory must decide when ending a borrow is authorized. Is 'the parent holding the loaned-out cells may end the borrow' sound once reborrows nest; what exactly is needed for soundness, and can it be checked locally; and is a transitive 'closed views' relation between the states before and after a scope the right invariant for keeping outer return authority across any number of nested, completed scopes?

### R1a — naive end unsound nested exclusive

- **Card id:** `R1a-naive-end-unsound-nested-exclusive`; **kind:** impossibility; **tier:** T1; **depth:** `definitional`; **proof status:** proved (Lean kernel check).
- **Plain claim:** Under the naive rule 'an active parent that holds a child's cells as outstanding loans may end that child' (which inspects neither the child's own cells nor its descendants), a nested exclusive reborrow (root A lends cell 0 to B, B relends it to C) reaches, from states that satisfy all seven loan-tree laws and write exclusivity, a state with two active writers of cell 0 (A and C) in which A regained access while its descendant C still covers the cell, whatever byte the borrow's continuation hands back.
- **Tier justification:** Folklore: a borrow must not end while a reborrow derived from it is live (RustBelt's LftL-reborrow returns the outer borrow only after the inner lifetime has ended; the Aeneas semantics' End-Mut refuses to end a borrow whose value is itself loaned out). Made precise and mechanized here for a concrete toy model. The Aeneas memory-model prototype's raw evaluator does not accept the analogue of this trace (its commit-time compatibility check rejects two active explicit writers). [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.Ex.naive_end_breaks_safety_of_nested_exclusive_reborrow   (ToyViews/Naive.lean:22)
theorem naive_end_breaks_safety_of_nested_exclusive_reborrow (r : Addr → Byte) :
    borrow s0 0 [0] = some s1 ∧ borrow s1 1 [0] = some s2 ∧
    LoanTreeInv s0 ∧ LoanTreeInv s1 ∧ LoanTreeInv s2 ∧
    WriteExclusive s0 ∧ WriteExclusive s1 ∧ WriteExclusive s2 ∧
    NaiveAuthority s2 1 ∧ ¬ ReturnAuthority s2 1 ∧
    endRaw s2 1 r = some (s3 (r 0)) ∧
    (s3 (r 0)).canWrite 0 0 = true ∧ (s3 (r 0)).canWrite 2 0 = true ∧
    ¬ WriteExclusive (s3 (r 0)) ∧ ¬ NoResurrection s2 (s3 (r 0))
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def returnable (vc vp : View) (c : ViewId) : Bool :=
  vp.active && (List.range vc.cells.length).all fun a =>
    match vc.cell? a with
    | none => true
    | some _ =>
      match vc.mode, vp.cell? a with
      | .excl, some (.loaned c') => c' == c
      | .shared, some (.own d _) => decide (vp.mode.baseline < d)
      | _, _ => false
def NaiveAuthority (s : State) (c : ViewId) : Prop :=
  ∃ vc p vp, s.view? c = some vc ∧ vc.active = true ∧ vc.parent = some p ∧
    s.view? p = some vp ∧ returnable vc vp c = true
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false
```

**Hypothesis ledger:** none (a closed statement about concrete states).

- **Non-vacuity witness:** Closed statement: the concrete trace s0 -> s1 -> s2 (two borrows) and the naive end of B in s2 are exhibited, for every restored-byte function r. Lean: `Toy.Views.Ex.naive_end_breaks_safety_of_nested_exclusive_reborrow`.
- **Positive control:** `Toy.Views.Ex.naive_end_safe_without_nested_reborrow` (a nearby setting in which the negative conclusion fails; Lean statement quoted just below).

**Positive control** (Lean statement):

```lean
-- Toy.Views.Ex.naive_end_safe_without_nested_reborrow   (ToyViews/Naive.lean:41)
theorem naive_end_safe_without_nested_reborrow (r : Addr → Byte) :
    LoanTreeInv s1 ∧ NaiveAuthority s1 1 ∧ ReturnAuthority s1 1 ∧
    endRaw s1 1 r = some (s1e (r 0)) ∧ LoanTreeInv (s1e (r 0)) ∧
    WriteExclusive (s1e (r 0)) ∧ NoResurrection s1 (s1e (r 0))
```

- **Non-claims:** listed under **Boundaries**, card R1a.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154. Section 5.1 and Fig. 4 (p. 66:23), whose rules are Iris updates (view shifts), not implications: LftL-borrow turns ▷P into a full borrow &κ_full P together with an inheritance [†κ] ⇛ ▷P that gives ▷P back once κ has ended; LftL-reborrow turns κ' ⊑ κ and &κ_full P into &κ'_full P together with [†κ'] ⇛ &κ_full P, so the outer borrow is regained only after the inner lifetime has ended; the paper notes that each inheritance 'may only be used once'. Ending κ gives up the full token [κ]_1 ('ensuring that all borrows are closed again') in exchange for the dead token [†κ]; Section 5.2 treats lifetime inclusion. The lifetime logic is mechanized in the Rocq/Coq development https://gitlab.mpi-sws.org/iris/lambda-rust (directory lifetime/, observed 2026-11-20). Conceptual analogue only: no formal correspondence between the lifetime logic and this toy model is claimed.
- Ho, S. & Protzenko, J., 'Aeneas: Rust Verification by Functional Translation', Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022, doi:10.1145/3547647 (text checked in the extended version arXiv:2206.07185v2). Section 3.4 ('Reorganizing Environments and Terminating Borrows', Fig. 9): rule End-Mut ends a mutable borrow only if the borrowed value contains no loans or reserved borrows and the borrow does not sit inside another borrowed value ('we can only terminate borrows for values that are not themselves borrowed'; 'we enforce that we own the value we are about to return (i.e. not loaned)'); ending a shared borrow removes its identifier from the shared loan's identifier set (End-Shared-Or-Reserved-1/2). Section 6, paragraph 'Precise Reborrows (Discussion)': 'our semantics does not track the hierarchy between borrows and their subsequent reborrows' -- a shared reborrow is attached to the original shared loan, so ending the intermediate borrow does not end the reborrow. Contrast: the termination check there inspects only the value being returned (a local check, cf. R2d), and shared loans are flat identifier sets on the owner rather than per-view counters.
- Jung, R., Dang, H.-H., Kang, J. & Dreyer, D., 'Stacked Borrows: An Aliasing Model for Rust', Proc. ACM Program. Lang. 4(POPL), Article 41, 2020, doi:10.1145/3371109. Section 3.1: after a reference is used, 'all references above it get popped, which permanently invalidates them'; Section 4.1 (Protectors): 'popping an active protector is undefined behavior'. Contrast: Stacked Borrows resolves an access through a parent by invalidating derived references (or declaring undefined behaviour when they are protected), whereas this toy model returns access to a parent only through an explicit end operation.
- Villani, N., Hostert, J., Dreyer, D. & Jung, R., 'Tree Borrows', Proc. ACM Program. Lang. 9(PLDI), Article 188, pp. 1019-1042, 2025, doi:10.1145/3735592 (volume, issue and pages via Crossref; the article number via web search results citing the authors' institution; the ACM page was not accessed). The abstract (on the authors' institution's page) states that Tree Borrows 'is defined by replacing the stack at the heart of Stacked Borrows with a tree'; the same page links a Rocq mechanization in the simuliris development (https://gitlab.mpi-sws.org/iris/simuliris, directory theories/tree_borrows). R. Jung's blog post 'From Stacks to Trees: A new aliasing model for Rust' (2023-06-02, https://ralfj.de/blog/2023/06/02/tree-borrows.html) says Tree Borrows keeps 'protectors' to enforce that certain references remain valid for the duration of an entire function call. The paper body was not inspected; no claim is made about its transition rules beyond these sources. Contrast: an access-based aliasing model over a tree of derived references, not a model with an explicit borrow-ending operation.
- Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69 (open and unmerged when observed on 2026-11-20; a non-durable prototype, cited as motivation only). Files named below are under backends/lean/Aeneas/Std/Heap/ unless a full path is given. Model.lean stores views as blocks (base pointer, root id, cell list, and separate 'owned', 'active' (view activity) and 'alive' (allocation lifetime) flags; no parent link). Cells are 'shared depth byte' (depth 0 = exclusive write permission) or 'borrowed' (lent to the unmodelled implicit safe heap). Repr.lean defines Cell.compatible: a 'borrowed' cell is compatible with anything, and two 'shared' cells are compatible only if both depths are positive and their bytes agree; every raw operation, including endBorrow and endShare, succeeds only if afterwards all pairs of active blocks are compatible at every common address (Heap.check, via commit). endExposureAt retires a non-owning view only if all its cells are at the given baseline depth (0; or 1 for endSharedExposure). README.md: raw restoration 'checks borrowed cells and heap compatibility, not a dynamic loan tree. It can restore a parent while a child view is itself borrowed'; the corresponding test in backends/lean/Aeneas/Std/HeapTests.lean restores a parent while the child view's cells are 'borrowed' into the implicit safe heap (there is no explicit grandchild view), and the nested-shared test 'sharedAliases' checks that restoring the root's write access while explicit shared views remain active is rejected. So the prototype's raw evaluator does not accept the analogue of the toy traces s2 -> s3 or t2 -> t3. Commit authors recorded for the 54 commits of the pull request up to that head (GitHub API, observed 2026-11-20): fournet, Cezar Andrici, Son Ho.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R1b — naive end unsound nested shared

- **Card id:** `R1b-naive-end-unsound-nested-shared`; **kind:** impossibility; **tier:** T1; **depth:** `definitional`; **proof status:** proved (Lean kernel check).
- **Plain claim:** Under the naive rule for shared children ('an active parent that holds the child's cells at a depth above its own baseline may end the child and decrement'), a nested shared reborrow (A shares cell 0 with B, B re-shares it with C) reaches, from states satisfying all seven loan-tree laws and write exclusivity, a state in which A is back at depth 0 (writable) while C still reads cell 0.
- **Tier justification:** Same folklore as R1a, for shared reborrows tracked by per-view depth counters. The Aeneas prototype's raw evaluator rejects the analogue of this step (its compatibility check forbids a writer beside an active reader), and the Aeneas semantics records a shared reborrow on the original loan with no link to the intermediate borrow, so this nesting is not represented there. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.Ex.naive_end_breaks_safety_of_nested_shared_reborrow   (ToyViews/Naive.lean:55)
theorem naive_end_breaks_safety_of_nested_shared_reborrow (r : Addr → Byte) :
    share s0 0 [0] = some t1 ∧ share t1 1 [0] = some t2 ∧
    LoanTreeInv t1 ∧ LoanTreeInv t2 ∧ WriteExclusive t1 ∧ WriteExclusive t2 ∧
    NaiveAuthority t2 1 ∧ ¬ ReturnAuthority t2 1 ∧
    endRaw t2 1 r = some t3 ∧ t3.canWrite 0 0 = true ∧ t3.canRead 2 0 = true ∧
    ¬ WriteExclusive t3 ∧ ¬ NoResurrection t2 t3
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def returnable (vc vp : View) (c : ViewId) : Bool :=
  vp.active && (List.range vc.cells.length).all fun a =>
    match vc.cell? a with
    | none => true
    | some _ =>
      match vc.mode, vp.cell? a with
      | .excl, some (.loaned c') => c' == c
      | .shared, some (.own d _) => decide (vp.mode.baseline < d)
      | _, _ => false
def NaiveAuthority (s : State) (c : ViewId) : Prop :=
  ∃ vc p vp, s.view? c = some vc ∧ vc.active = true ∧ vc.parent = some p ∧
    s.view? p = some vp ∧ returnable vc vp c = true
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false
```

**Hypothesis ledger:** none (a closed statement about concrete states).

- **Non-vacuity witness:** Closed statement: concrete trace s0 -> t1 -> t2 (two shares) and the naive end of B in t2. Lean: `Toy.Views.Ex.naive_end_breaks_safety_of_nested_shared_reborrow`.
- **Positive control:** `Toy.Views.Ex.naive_end_safe_without_nested_shared_reborrow` (a nearby setting in which the negative conclusion fails; Lean statement quoted just below).

**Positive control** (Lean statement):

```lean
-- Toy.Views.Ex.naive_end_safe_without_nested_shared_reborrow   (ToyViews/Naive.lean:70)
theorem naive_end_safe_without_nested_shared_reborrow (r : Addr → Byte) :
    LoanTreeInv t1 ∧ NaiveAuthority t1 1 ∧ ReturnAuthority t1 1 ∧
    endRaw t1 1 r = some t1e ∧ LoanTreeInv t1e ∧ WriteExclusive t1e ∧ NoResurrection t1 t1e
```

- **Non-claims:** listed under **Boundaries**, card R1b.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Bornat, R., Calcagno, C., O'Hearn, P. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327. Section 6 (counting permissions): a source permission is annotated with the number of read permissions split off from it; 'the split-off read permissions can't be split further; only a source with no split-off children gives total read/write/dispose ownership'; Section 10.2 gives the integer model of counting permissions. Section 10.4 ('Combined Model', over the rationals) makes read permissions divisible: 'By making read permissions divisible, it's possible to combine the properties of fractional and counting permissions', and notes that in the combined model it is 'impossible ... to set up a logic in which read permissions cannot be split once issued'.
- Same entry as under R1a (full text there): Ho, S. & Protzenko, J., 'Aeneas: Rust Verification by Functional Translation', Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022, doi:10.1145/3547647.
- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.
- Same entry as under R1a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R2a — end under return authority preserves invariant

- **Card id:** `R2a-end-under-return-authority-preserves-invariant`; **kind:** theorem; **tier:** T1; **depth:** `substantive`; **proof status:** proved (Lean kernel check).
- **Plain claim:** If a state satisfies the five tree-local loan laws (ParentCoversActive, ExclChildLoaned, SharedChildBelowOwn, SharedChildrenShared, DepthCounts) and view c has return authority (no active proper descendant of c covers any cell of c), then ending c with the raw end operation, for any returned bytes, yields a state that again satisfies the five local laws, and in that step no view gains access to a cell that an active proper descendant of it still covers. ParentLt and RootsDisjoint are not needed; since every raw end preserves them, the full seven-law invariant LoanTreeInv is preserved as a corollary.
- **Tier justification:** Folklore stack/lifetime discipline (a borrow ends only after everything derived from it has ended; cf. RustBelt LftL-reborrow), made precise for an operational loan tree with exclusive and depth-counted shared loans, with every hypothesis shown necessary. The second Lean name is the full-invariant corollary (seven laws), obtained with the two frame lemmas.

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority   (ToyViews/EndSafe.lean:20)
theorem endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hauth : ReturnAuthority s c) (hend : endRaw s c r = some s') :
    LocalLoanLaws s' ∧ NoResurrection s s'

-- Toy.Views.endRaw_preserves_loanTreeInv_and_noResurrection_of_returnAuthority   (ToyViews/EndSafe.lean:32)
theorem endRaw_preserves_loanTreeInv_and_noResurrection_of_returnAuthority
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hinv : LoanTreeInv s) (hauth : ReturnAuthority s c) (hend : endRaw s c r = some s') :
    LoanTreeInv s' ∧ NoResurrection s s'
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s
structure LocalLoanLaws (s : State) : Prop where
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hpc : ParentCoversActive s` | both forms (in the full-invariant form as a field of hinv : LoanTreeInv s): an active view's cells are covered by its parent, which is active; in the counterexample the step breaks NoResurrection (not only the dropped law fails afterwards) | `tight` | `Toy.Views.Ex.endRaw_inv_needs_parentCoversActive` |
| `hecl : ExclChildLoaned s` | both forms (in the full-invariant form as a field of hinv : LoanTreeInv s): cells of an active exclusive child are recorded in the parent as loaned to it; in the counterexample the step breaks NoResurrection (not only the dropped law fails afterwards) | `tight` | `Toy.Views.Ex.endRaw_inv_needs_exclChildLoaned` |
| `hscb : SharedChildBelowOwn s` | both forms (in the full-invariant form as a field of hinv : LoanTreeInv s): cells of an active shared child are held by the parent at positive depth; in the counterexample the step also breaks DepthCounts (not only the dropped law fails afterwards) | `tight` | `Toy.Views.Ex.endRaw_inv_needs_sharedChildBelowOwn` |
| `hscs : SharedChildrenShared s` | both forms (in the full-invariant form as a field of hinv : LoanTreeInv s): active children of shared views are shared (read-only views do not lend exclusively); in the counterexample the step breaks DepthCounts (not only the dropped law fails afterwards) | `tight` | `Toy.Views.Ex.endRaw_inv_needs_sharedChildrenShared` |
| `hdc : DepthCounts s` | both forms (in the full-invariant form as a field of hinv : LoanTreeInv s): depth = mode baseline + number of active shared children on the cell; in the counterexample the step also breaks SharedChildBelowOwn (not only the dropped law fails afterwards) | `tight` | `Toy.Views.Ex.endRaw_inv_needs_depthCounts` |
| `hinv.parentLt : ParentLt s (full-invariant form only)` | full-invariant form only, as a field of hinv : LoanTreeInv s; the main form does not assume it, and endRaw preserves it unconditionally (endRaw_preserves_parentLt), so it is assumed here only because it is part of the conclusion LoanTreeInv s'. In the counterexample the other six laws and return authority hold and the end succeeds; the step keeps the five local laws and NoResurrection, but the post-state is not write-exclusive, so LoanTreeInv s' fails (by R2b, writeExclusive_of_loanTree_laws). Since RootsDisjoint is preserved (endRaw_preserves_rootsDisjoint), the law that fails afterwards is ParentLt itself: the dropped law persists through the step rather than being broken by it. This last inference combines the counterexample, R2b and the frame lemma; it is not stated as a single Lean theorem | `tight` | `Toy.Views.Ex.endRaw_writeExclusive_needs_parentLt` |
| `hinv.rootsDisjoint : RootsDisjoint s (full-invariant form only)` | full-invariant form only, as a field of hinv : LoanTreeInv s; the main form does not assume it, and endRaw preserves it unconditionally (endRaw_preserves_rootsDisjoint), so it is assumed here only because it is part of the conclusion LoanTreeInv s'. In the counterexample the other six laws and return authority hold and the end succeeds; the step keeps the five local laws and NoResurrection, but the post-state is not write-exclusive, so LoanTreeInv s' fails (by R2b, writeExclusive_of_loanTree_laws). Since ParentLt is preserved (endRaw_preserves_parentLt), the law that fails afterwards is RootsDisjoint itself: the dropped law persists through the step rather than being broken by it. This last inference combines the counterexample, R2b and the frame lemma; it is not stated as a single Lean theorem | `tight` | `Toy.Views.Ex.endRaw_writeExclusive_needs_rootsDisjoint` |
| `hauth : ReturnAuthority s c` | both forms: no active proper descendant of c covers a cell of c; the authority whose absence makes R1 possible | `tight` | `Toy.Views.Ex.endRaw_inv_needs_returnAuthority` |
| `hend : endRaw s c r = some s'` | both forms: names the post-state of the step under analysis (c and its parent active, the parent holds c's cells as outstanding loans) | `harmless` | — |

- **Non-vacuity witness:** Nested state s2 (A lends to B, B to C): all laws hold, C has return authority, and ending C succeeds; also u2 (A with two shared children): ending B succeeds and A stays read-only. Lean: `Toy.Views.Ex.endRaw_inv_nonvacuous_nested`, `Toy.Views.Ex.endRaw_inv_nonvacuous_shared`.
- **Non-claims:** listed under **Boundaries**, card R2a.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.
- Same entry as under R1a (full text there): Ho, S. & Protzenko, J., 'Aeneas: Rust Verification by Functional Translation', Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022, doi:10.1145/3547647.
- Ho, S., Fromherz, A. & Protzenko, J., 'Sound Borrow-Checking for Rust via Symbolic Semantics', Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024, doi:10.1145/3674640 (abstract checked via Crossref and arXiv:2404.02680): proves that LLBC, the borrow-centric semantics of Aeneas, is a correct view over a low-level pointer-based language a la CompCert, and that its symbolic semantics act as a borrow checker (symbolically checked programs do not get stuck on a heap-and-addresses model). Related aim (justifying borrow termination against a low-level heap); no correspondence with this toy model is claimed.
- Matsushita, Y., Denis, X., Jourdan, J.-H. & Dreyer, D., 'RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code', PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704. Abstract: a machine-checked soundness proof for RustHorn-style verification, which describes mutable borrows with prophecies, extending RustBelt's semantic model with 'parametric prophecies'. Related to the value handed back when an exclusive borrow ends (the arbitrary function r of endRaw); this package tracks permissions only and models no prophecies.
- Gäher, L., Sammler, M., Jung, R., Krebbers, R. & Dreyer, D., 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', Proc. ACM Program. Lang. 8(PLDI), pp. 1115-1139, 2024, doi:10.1145/3656422. Abstract: a refinement type system, proven sound in Coq, for semi-automated functional verification of both safe and unsafe Rust. Related foundational work on borrows in unsafe code; no correspondence with this toy model is claimed.
- Same entry as under R1a (full text there): Villani, N., Hostert, J., Dreyer, D. & Jung, R., 'Tree Borrows', Proc. ACM Program. Lang. 9(PLDI), Article 188, pp. 1019-1042, 2025, doi:10.1145/3735592.
- Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69 (open and unmerged when observed on 2026-11-20; a non-durable prototype, cited as motivation only). Files named below are under backends/lean/Aeneas/Std/Heap/ unless a full path is given. Model.lean stores views as blocks (base pointer, root id, cell list, and separate 'owned', 'active' (view activity) and 'alive' (allocation lifetime) flags; no parent link). Cells are 'shared depth byte' (depth 0 = exclusive write permission) or 'borrowed' (lent to the unmodelled implicit safe heap). Allocation.lean defines RootReturn s base: the view covers its whole root allocation, and no other active view of the same root exists; RootReturn.modify proves that it is preserved by every operation implemented through Heap.modify (writes and the raw borrow, share and end operations on cells). ScopedView.lean defines ClosedViews s0 s1 (the fresh-id counter does not decrease; ids below s0.next keep their return shape: base pointer, root, length, active flag; ids at or above s0.next are inactive) and proves ClosedViews.trans and RootReturn.after_closed_views (assuming also the heap invariant of s0 and base < s0.next). Commit authors recorded for the 54 commits of the pull request up to that head (GitHub API, observed 2026-11-20): fournet, Cezar Andrici, Son Ho.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R2b — loan tree laws imply write exclusivity

- **Card id:** `R2b-loan-tree-laws-imply-write-exclusivity`; **kind:** theorem; **tier:** T1; **depth:** `substantive`; **proof status:** proved (Lean kernel check).
- **Plain claim:** The seven loan-tree laws together imply write exclusivity: whenever an active view can write a cell, no other active view can read or write it.
- **Tier justification:** Folklore (a well-formed loan structure gives aliasing-xor-mutability; source-level analogues in Oxide and in Pearce's calculus), made precise for this model with each law shown necessary.

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.writeExclusive_of_loanTree_laws   (ToyViews/EndSafe.lean:45)
theorem writeExclusive_of_loanTree_laws {s : State}
    (hlt : ParentLt s) (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hrd : RootsDisjoint s) :
    WriteExclusive s
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hlt : ParentLt s` | parent links point to smaller ids (parents are created first; excludes cycles) | `tight` | `Toy.Views.Ex.writeExclusive_needs_parentLt` |
| `hpc : ParentCoversActive s` | an active view's cells are covered by its parent, which is active | `tight` | `Toy.Views.Ex.writeExclusive_needs_parentCoversActive` |
| `hecl : ExclChildLoaned s` | cells of an active exclusive child are recorded in the parent as loaned to it | `tight` | `Toy.Views.Ex.writeExclusive_needs_exclChildLoaned` |
| `hscb : SharedChildBelowOwn s` | cells of an active shared child are held by the parent at positive depth | `tight` | `Toy.Views.Ex.writeExclusive_needs_sharedChildBelowOwn` |
| `hscs : SharedChildrenShared s` | active children of shared views are shared (read-only views do not lend exclusively) | `tight` | `Toy.Views.Ex.writeExclusive_needs_sharedChildrenShared` |
| `hdc : DepthCounts s` | depth = mode baseline + number of active shared children on the cell | `tight` | `Toy.Views.Ex.writeExclusive_needs_depthCounts` |
| `hrd : RootsDisjoint s` | distinct active roots cover disjoint cells | `tight` | `Toy.Views.Ex.writeExclusive_needs_rootsDisjoint` |

- **Non-vacuity witness:** w2: two addresses, one exclusive and one shared loan, all seven laws hold. Lean: `Toy.Views.Ex.loanTree_laws_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R2b.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Pearce, D. J., 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust', ACM Trans. Program. Lang. Syst. 43(1), pp. 1-73, 2021, doi:10.1145/3443420. Abstract: a flow-sensitive calculus enforcing 'type and borrow safety', covering mutable borrowing, reborrowing and lifetimes. A source-level analogue of a well-formed loan structure guaranteeing safe access; no toy-model correspondence claimed.
- Weiss, A., Gierczak, O., Patterson, D. & Ahmed, A., 'Oxide: The Essence of Rust', arXiv:1903.00982 (v4): a formalized source-level calculus capturing Rust's ownership and borrowing, reading lifetimes as approximations of reference provenances. Source-level analogue only.
- Same entry as under R1a (full text there): Jung, R., Dang, H.-H., Kang, J. & Dreyer, D., 'Stacked Borrows: An Aliasing Model for Rust', Proc. ACM Program. Lang. 4(POPL), Article 41, 2020, doi:10.1145/3371109.
- Same entry as under R1a (full text there): Villani, N., Hostert, J., Dreyer, D. & Jung, R., 'Tree Borrows', Proc. ACM Program. Lang. 9(PLDI), Article 188, pp. 1019-1042, 2025, doi:10.1145/3735592.
- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

### R2c — end under return authority write exclusive

- **Card id:** `R2c-end-under-return-authority-write-exclusive`; **kind:** theorem; **tier:** T1; **depth:** `shallow`; **proof status:** proved (Lean kernel check); derived from R2a and R2b.
- **Plain claim:** Corollary (soundness of ending under return authority): if a state satisfies all seven loan-tree laws and view c has return authority, then the raw end of c, for any returned bytes, yields a write-exclusive state. Each of the seven laws is needed, even when the pre-state is write-exclusive.
- **Tier justification:** Immediate corollary of R2a, the two frame lemmas and R2b; kept as a separate card because it is the soundness statement of the package and its hypothesis ledger differs from R2a's (all seven laws are needed here).

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.endRaw_writeExclusive_of_loanTree_laws_of_returnAuthority   (ToyViews/EndSafe.lean:56)
theorem endRaw_writeExclusive_of_loanTree_laws_of_returnAuthority
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hlt : ParentLt s) (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hrd : RootsDisjoint s)
    (hauth : ReturnAuthority s c) (hend : endRaw s c r = some s') :
    WriteExclusive s'
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hlt : ParentLt s` | parent links point to smaller ids (parents are created first; excludes cycles); the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_writeExclusive_needs_parentLt` |
| `hpc : ParentCoversActive s` | an active view's cells are covered by its parent, which is active; the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_inv_needs_parentCoversActive` |
| `hecl : ExclChildLoaned s` | cells of an active exclusive child are recorded in the parent as loaned to it; the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_inv_needs_exclChildLoaned` |
| `hscb : SharedChildBelowOwn s` | cells of an active shared child are held by the parent at positive depth; the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_inv_needs_sharedChildBelowOwn` |
| `hscs : SharedChildrenShared s` | active children of shared views are shared (read-only views do not lend exclusively); the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_inv_needs_sharedChildrenShared` |
| `hdc : DepthCounts s` | depth = mode baseline + number of active shared children on the cell; the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_inv_needs_depthCounts` |
| `hrd : RootsDisjoint s` | distinct active roots cover disjoint cells; the counterexample starts from a write-exclusive state | `tight` | `Toy.Views.Ex.endRaw_writeExclusive_needs_rootsDisjoint` |
| `hauth : ReturnAuthority s c` | the authority whose absence makes R1 possible | `tight` | `Toy.Views.Ex.endRaw_inv_needs_returnAuthority` |
| `hend : endRaw s c r = some s'` | names the post-state of the step under analysis | `harmless` | — |

- **Non-vacuity witness:** As for R2a: s2 with C ending, and u2 with B ending. Lean: `Toy.Views.Ex.endRaw_inv_nonvacuous_nested`, `Toy.Views.Ex.endRaw_inv_nonvacuous_shared`.
- **Non-claims:** listed under **Boundaries**, card R2c.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.
- Same entry as under R2a (full text there): Ho, S., Fromherz, A. & Protzenko, J., 'Sound Borrow-Checking for Rust via Symbolic Semantics', Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024, doi:10.1145/3674640.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

### R2d — local baseline check implies return authority

- **Card id:** `R2d-local-baseline-check-implies-return-authority`; **kind:** theorem; **tier:** T1; **depth:** `shallow`; **proof status:** proved (Lean kernel check); the second statement is derived from the first and R2a.
- **Plain claim:** Under the three tree-local laws ParentCoversActive, ExclChildLoaned and DepthCounts, if view c holds every cell it covers as an own cell at its own mode baseline depth (0 for an exclusive view, 1 for a shared view; i.e. it has lent nothing onward), then c has return authority. The check inspects only c's own cells, not its descendants, and it does not suffice without the three laws. End form (with R2a): if moreover the other two tree-local laws, SharedChildBelowOwn and SharedChildrenShared, hold and the raw end of c succeeds (for any returned bytes), then the resulting state satisfies all five tree-local laws and the step resurrects nothing. The end form needs both extra laws, although return authority itself does not.
- **Tier justification:** Folklore made precise: the Aeneas semantics decides borrow termination from the value being returned (it must not be loaned out), and the Aeneas memory-model prototype retires a child view only if all its cells are at baseline depth; that such a local check implies the descendant-based authority under the tree laws is made precise and mechanized here. The second Lean name (the end form) is the corollary obtained with R2a; it needs all five tree-local laws. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.returnAuthority_of_localReturnCheck_of_parentCoversActive_exclChildLoaned_depthCounts   (ToyViews/EndSafe.lean:76)
theorem returnAuthority_of_localReturnCheck_of_parentCoversActive_exclChildLoaned_depthCounts
    {s : State} {c : ViewId}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s) (hdc : DepthCounts s)
    (hloc : LocalReturnCheck s c) : ReturnAuthority s c

-- Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_localReturnCheck   (ToyViews/EndSafe.lean:87)
theorem endRaw_preserves_localLoanLaws_and_noResurrection_of_localReturnCheck
    {s s' : State} {c : ViewId} {r : Addr → Byte}
    (hpc : ParentCoversActive s) (hecl : ExclChildLoaned s)
    (hscb : SharedChildBelowOwn s) (hscs : SharedChildrenShared s) (hdc : DepthCounts s)
    (hloc : LocalReturnCheck s c) (hend : endRaw s c r = some s') :
    LocalLoanLaws s' ∧ NoResurrection s s'
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
structure LocalLoanLaws (s : State) : Prop where
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def LocalReturnCheck (s : State) (c : ViewId) : Prop :=
  ∀ a < s.width, s.covers c a = true → s.depth? c a = some (s.baselineOf c)
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hpc : ParentCoversActive s` | both statements: lets an active descendant on c's cell be traced up to an active direct child of c on that cell; in the counterexample c passes the check, has no return authority, and its end succeeds and breaks NoResurrection | `tight` | `Toy.Views.Ex.localCheck_needs_parentCoversActive` |
| `hecl : ExclChildLoaned s` | both statements: an active exclusive child on the cell forces c's cell to be loaned, which the check excludes; in the counterexample c passes the check, has no return authority, and its end succeeds and breaks NoResurrection | `tight` | `Toy.Views.Ex.localCheck_needs_exclChildLoaned` |
| `hscb : SharedChildBelowOwn s (end form only)` | not needed for return authority; without it a shared sibling of c can read a cell that c's parent lent exclusively to c, so ending c makes the parent writable at depth 0 under an active reader; in the counterexample c passes the check and has return authority, and the end step breaks DepthCounts | `tight` | `Toy.Views.Ex.localCheck_end_needs_sharedChildBelowOwn` |
| `hscs : SharedChildrenShared s (end form only)` | not needed for return authority; without it an exclusive child c of a shared view hands back a depth-0 cell to its read-only parent; in the counterexample c passes the check and has return authority, and the end step breaks DepthCounts | `tight` | `Toy.Views.Ex.localCheck_end_needs_sharedChildrenShared` |
| `hdc : DepthCounts s` | both statements: an active shared child on the cell forces c's depth above its baseline, which the check excludes; in the counterexample c passes the check, has no return authority, and its end succeeds and breaks NoResurrection | `tight` | `Toy.Views.Ex.localCheck_needs_depthCounts` |
| `hloc : LocalReturnCheck s c` | both statements: the local check itself; in the counterexample (state s2 of R1a, all five local laws hold) c fails the check, has no return authority, and its end succeeds and breaks the local laws and NoResurrection | `tight` | `Toy.Views.Ex.localCheck_needs_localReturnCheck` |
| `hend : endRaw s c r = some s' (end form only)` | names the post-state of the step under analysis (c and its parent active, the parent holds c's cells as outstanding loans) | `harmless` | — |

- **Non-vacuity witness:** s1 (exclusive child B) and t1 (shared child B): all five tree-local laws hold, B passes the check, and the raw end of B succeeds (covers both statements). Lean: `Toy.Views.Ex.localCheck_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R2d.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R1a (full text there): Ho, S. & Protzenko, J., 'Aeneas: Rust Verification by Functional Translation', Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022, doi:10.1145/3547647.
- Same entry as under R1a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R3a — closed views preorder

- **Card id:** `R3a-closed-views-preorder`; **kind:** theorem; **tier:** T0; **depth:** `shallow`; **proof status:** proved (Lean kernel check).
- **Plain claim:** ClosedViews is a preorder: every state is closed relative to itself, and if s₁ is closed relative to s₀ and s₂ is closed relative to s₁, then s₂ is closed relative to s₀ (consecutive completed scopes compose).
- **Tier justification:** The Aeneas prototype proves ClosedViews.trans for its analogous relation; reflexivity is immediate (included as a reference point). [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.closedViews_refl   (ToyViews/Closed.lean:99)
theorem closedViews_refl (s : State) : ClosedViews s s

-- Toy.Views.closedViews_trans   (ToyViews/Closed.lean:104)
theorem closedViews_trans {s₀ s₁ s₂ : State} (h₁ : ClosedViews s₀ s₁) (h₂ : ClosedViews s₁ s₂) :
    ClosedViews s₀ s₂
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `h₁ : ClosedViews s₀ s₁ (transitivity)` | first scope | `tight` | `Toy.Views.Ex.closedViews_trans_needs_both` |
| `h₂ : ClosedViews s₁ s₂ (transitivity)` | second scope | `tight` | `Toy.Views.Ex.closedViews_trans_needs_both` |

- **Non-vacuity witness:** Two consecutive closed steps from s1: a write, then a completed nested scope. Reflexivity has no hypotheses. Lean: `Toy.Views.Ex.closedViews_trans_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R3a.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69 (open and unmerged when observed on 2026-11-20; a non-durable prototype, cited as motivation only). Files named below are under backends/lean/Aeneas/Std/Heap/ unless a full path is given. Allocation.lean defines RootReturn s base: the view covers its whole root allocation, and no other active view of the same root exists; RootReturn.modify proves that it is preserved by every operation implemented through Heap.modify (writes and the raw borrow, share and end operations on cells). ScopedView.lean defines ClosedViews s0 s1 (the fresh-id counter does not decrease; ids below s0.next keep their return shape: base pointer, root, length, active flag; ids at or above s0.next are inactive) and proves ClosedViews.trans and RootReturn.after_closed_views (assuming also the heap invariant of s0 and base < s0.next). Commit authors recorded for the 54 commits of the pull request up to that head (GitHub API, observed 2026-11-20): fournet, Cezar Andrici, Son Ho.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R3c — closed views preserve return authority

- **Card id:** `R3c-closed-views-preserve-return-authority`; **kind:** theorem; **tier:** T0; **depth:** `shallow`; **proof status:** proved (Lean kernel check).
- **Plain claim:** If view v has return authority in s₀ and s₁ is closed relative to s₀ (old views keep parent, activity and domain; views created after s₀ are inactive in s₁), then v has return authority in s₁, provided either every parent link of s₀ points to an existing view (first form) or ParentCoversActive holds in s₁ (second form). The conclusion has operational content only for views that already exist in s₀.
- **Tier justification:** Analogue of the Aeneas prototype's RootReturn.after_closed_views, restated for a descendant-based authority over parent-linked views. The second form (structural hypothesis on the post-state instead of the pre-state) has no counterpart in the prototype. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.returnAuthority_of_closedViews_of_parentsExist   (ToyViews/Closed.lean:126)
theorem returnAuthority_of_closedViews_of_parentsExist {s₀ s₁ : State} {v : ViewId}
    (hpe : ParentsExist s₀) (hauth : ReturnAuthority s₀ v) (hcv : ClosedViews s₀ s₁) :
    ReturnAuthority s₁ v

-- Toy.Views.returnAuthority_of_closedViews_of_parentCoversActive   (ToyViews/Closed.lean:197)
theorem returnAuthority_of_closedViews_of_parentCoversActive {s₀ s₁ : State} {v : ViewId}
    (hpc : ParentCoversActive s₁) (hauth : ReturnAuthority s₀ v) (hcv : ClosedViews s₀ s₁) :
    ReturnAuthority s₁ v
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def ParentsExist (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < s.size
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hpe : ParentsExist s₀ (first form)` | dangling parent links in s₀ could be resolved by views created later, making an old active view a new descendant of v | `tight` | `Toy.Views.Ex.returnAuthority_lost_without_parentsExist` |
| `hpc : ParentCoversActive s₁ (second form)` | an active descendant on v's cell then has an active (hence old) parent chain up to v | `tight` | `Toy.Views.Ex.returnAuthority_lost_without_parentsExist` |
| `hauth : ReturnAuthority s₀ v` | the authority being preserved | `tight` | `Toy.Views.Ex.returnAuthority_needed_before_scope` |
| `hcv : ClosedViews s₀ s₁` | s₁ is closed relative to s₀: ParentsStable, ActivityStable, DomainsStable and NewViewsInactive (one Lean parameter, a structure with these four fields); each field is necessary, with one witness per field in the counterexample list, in the order NewViewsInactive, ParentsStable, ActivityStable, DomainsStable | `tight` | `Toy.Views.Ex.returnAuthority_lost_without_newViewsInactive`, `Toy.Views.Ex.returnAuthority_lost_without_parentsStable`, `Toy.Views.Ex.returnAuthority_lost_without_activityStable`, `Toy.Views.Ex.returnAuthority_lost_without_domainsStable` |

- **Non-vacuity witness:** B has authority in s1; the closed nested scope s1 -> s2e 0; parent links of s1 exist and ParentCoversActive holds in s2e 0. Lean: `Toy.Views.Ex.returnAuthority_closedViews_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R3c.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R3a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.
- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R3d — fresh scope is closed

- **Card id:** `R3d-fresh-scope-is-closed`; **kind:** theorem; **tier:** T1; **depth:** `shallow`; **proof status:** proved (Lean kernel check).
- **Plain claim:** A single scope is closed: if an opening step keeps the parent links, activity flags and domains of all existing views and adds exactly one view c = s.size (OpenScopeShape; borrow and share are such steps), the inner computation is closed (ClosedViews s₁ s₂), and the scope ends with the raw end of c, then the result is closed relative to the state before the opening step. Exclusive versus shared loans play no role.
- **Tier justification:** The Aeneas prototype proves a special case in a different form, RootReturn.after_scoped_view: one fresh view, NewView s0 s1 (every other allocation literally unchanged), no inner scope, and a conclusion about root authority rather than a closed-views relation. This theorem allows an opening step that changes the parent's cells (borrow, share), an arbitrary closed inner computation, and the end of the fresh view; the borrow and share forms are corollaries via the proved lemmas openScopeShape_of_borrow and openScopeShape_of_share. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.closedViews_of_fresh_scope   (ToyViews/Closed.lean:283)
theorem closedViews_of_fresh_scope {s s₁ s₂ s₃ : State} {r : Addr → Byte}
    (hop : OpenScopeShape s s₁) (hin : ClosedViews s₁ s₂)
    (he : endRaw s₂ s.size r = some s₃) : ClosedViews s s₃

-- Toy.Views.closedViews_of_borrow_scope   (ToyViews/Closed.lean:479)
theorem closedViews_of_borrow_scope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr}
    {r : Addr → Byte} (hb : borrow s p A = some s₁) (hin : ClosedViews s₁ s₂)
    (he : endRaw s₂ s.size r = some s₃) : ClosedViews s s₃

-- Toy.Views.closedViews_of_share_scope   (ToyViews/Closed.lean:485)
theorem closedViews_of_share_scope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr}
    {r : Addr → Byte} (hb : share s p A = some s₁) (hin : ClosedViews s₁ s₂)
    (he : endRaw s₂ s.size r = some s₃) : ClosedViews s s₃
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
structure OpenScopeShape (s s₁ : State) : Prop where
  parents : ParentsStable s s₁
  activity : ActivityStable s s₁
  domains : DomainsStable s s₁
  size_eq : s₁.size = s.size + 1
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hop : OpenScopeShape s s₁ (hb : borrow s p A = some s₁, resp. share, in the corollaries)` | relates the state before the scope to the state after opening it; without it the outer state is unrelated | `tight` | `Toy.Views.Ex.fresh_scope_needs_open_step` |
| `hin : ClosedViews s₁ s₂` | the inner computation leaves no new view active and keeps old views' shapes | `tight` | `Toy.Views.Ex.closedViews_of_borrow_scope_needs_inner_closed`, `Toy.Views.Ex.closedViews_of_share_scope_needs_inner_closed` |
| `he : endRaw s₂ s.size r = some s₃` | the scope ends exactly the fresh view s.size; dropping it (s₃ := s₂) or ending another view fails | `tight` | `Toy.Views.Ex.fresh_scope_needs_end_of_fresh_view` |

- **Non-vacuity witness:** Borrow (resp. share) A -> B from s0, an inner closed scope that itself contains a completed nested scope B -> C (so it allocates a view, s₁.size < s₂.size), then the end of B. Lean: `Toy.Views.Ex.borrow_scope_nonvacuous`, `Toy.Views.Ex.share_scope_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R3d.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69 (open and unmerged when observed on 2026-11-20; a non-durable prototype, cited as motivation only). Files named below are under backends/lean/Aeneas/Std/Heap/ unless a full path is given. Allocation.lean defines RootReturn s base: the view covers its whole root allocation, and no other active view of the same root exists; RootReturn.modify proves that it is preserved by every operation implemented through Heap.modify (writes and the raw borrow, share and end operations on cells). ScopedView.lean defines ClosedViews s0 s1 (the fresh-id counter does not decrease; ids below s0.next keep their return shape: base pointer, root, length, active flag; ids at or above s0.next are inactive) and proves ClosedViews.trans and RootReturn.after_closed_views (assuming also the heap invariant of s0 and base < s0.next). ScopedView.lean also defines NewView s0 s1 := s1.next = s0.next + 1 and every allocation other than the fresh id s0.next is literally unchanged, and proves RootReturn.after_scoped_view from NewView s0 s1 and inactivity of the fresh id in s1: a single fresh view, no change to any old view, and no inner scope. Commit authors recorded for the 54 commits of the pull request up to that head (GitHub API, observed 2026-11-20): fournet, Cezar Andrici, Son Ho.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R3f — write is closed

- **Card id:** `R3f-write-is-closed`; **kind:** theorem; **tier:** T0; **depth:** `shallow`; **proof status:** proved (Lean kernel check).
- **Plain claim:** A successful write (which changes one byte of a cell the writer holds at depth 0) yields a state closed relative to the state before it.
- **Tier justification:** A trivial frame fact; the Aeneas prototype proves the analogous preservation of root authority by writes and other cell updates (RootReturn.modify). [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.closedViews_of_write   (ToyViews/Closed.lean:491)
theorem closedViews_of_write {s s' : State} {v : ViewId} {a : Addr} {b : Byte}
    (hw : write s v a b = some s') : ClosedViews s s'
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hw : write s v a b = some s'` | names the post-state of the write | `harmless` | — |

- **Non-vacuity witness:** B writes byte 5 in s1. Lean: `Toy.Views.Ex.write_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R3f.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R3a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R3g — scoped end preserves invariant

- **Card id:** `R3g-scoped-end-preserves-invariant`; **kind:** theorem; **tier:** T1; **depth:** `shallow`; **proof status:** proved (Lean kernel check); derived from R3c and R2a.
- **Plain claim:** If view c had return authority in s₀, s₁ is closed relative to s₀, and the five tree-local laws hold in s₁, then the raw end of c in s₁ (for any returned bytes) preserves the five local laws and resurrects nothing. The laws must hold in s₁ itself (ClosedViews does not carry them over from s₀); no hypothesis about parent links (ParentLt, ParentsExist) is needed.
- **Tier justification:** Corollary of R3c (second form) and R2a; folklore that authority established before a completed scope remains valid after it (cf. RustBelt's lifetime inclusion).

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority_before_closedViews   (ToyViews/Closed.lean:548)
theorem endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority_before_closedViews
    {s₀ s₁ s₂ : State} {c : ViewId} {r : Addr → Byte}
    (hauth : ReturnAuthority s₀ c) (hcv : ClosedViews s₀ s₁)
    (hpc : ParentCoversActive s₁) (hecl : ExclChildLoaned s₁) (hscb : SharedChildBelowOwn s₁)
    (hscs : SharedChildrenShared s₁) (hdc : DepthCounts s₁)
    (hend : endRaw s₁ c r = some s₂) : LocalLoanLaws s₂ ∧ NoResurrection s₁ s₂
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def level (s : State) (v : ViewId) (a : Addr) : Nat :=
  if s.canWrite v a then 2 else if s.canRead v a then 1 else 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
structure LocalLoanLaws (s : State) : Prop where
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def NoResurrection (s s' : State) : Prop :=
  ∀ u < s'.size, ∀ a < s'.width, s.level u a < s'.level u a →
    ∀ d, ProperDesc s' d u → s'.isActive d = true → s'.covers d a = false
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hauth : ReturnAuthority s₀ c` | authority established before the scope | `tight` | `Toy.Views.Ex.returnAuthority_needed_before_scope` |
| `hcv : ClosedViews s₀ s₁` | s₁ is closed relative to s₀: ParentsStable, ActivityStable, DomainsStable and NewViewsInactive (one Lean parameter, a structure with these four fields); each field is necessary, with one witness per field in the counterexample list, in the order NewViewsInactive, ParentsStable, ActivityStable, DomainsStable | `tight` | `Toy.Views.Ex.returnAuthority_lost_without_newViewsInactive`, `Toy.Views.Ex.returnAuthority_lost_without_parentsStable`, `Toy.Views.Ex.returnAuthority_lost_without_activityStable`, `Toy.Views.Ex.returnAuthority_lost_without_domainsStable` |
| `hpc : ParentCoversActive s₁` | an active view's cells are covered by its parent, which is active (in the state after the scope) | `tight` | `Toy.Views.Ex.scoped_end_needs_local_laws` |
| `hecl : ExclChildLoaned s₁` | cells of an active exclusive child are recorded in the parent as loaned to it (in the state after the scope) | `tight` | `Toy.Views.Ex.scoped_end_needs_local_laws` |
| `hscb : SharedChildBelowOwn s₁` | cells of an active shared child are held by the parent at positive depth (in the state after the scope) | `tight` | `Toy.Views.Ex.scoped_end_needs_local_laws` |
| `hscs : SharedChildrenShared s₁` | active children of shared views are shared (read-only views do not lend exclusively) (in the state after the scope) | `tight` | `Toy.Views.Ex.scoped_end_needs_local_laws` |
| `hdc : DepthCounts s₁` | depth = mode baseline + number of active shared children on the cell (in the state after the scope) | `tight` | `Toy.Views.Ex.scoped_end_needs_local_laws` |
| `hend : endRaw s₁ c r = some s₂` | names the post-state of the end | `harmless` | — |

- **Non-vacuity witness:** B had authority in s1; after the closed nested scope to s2e 0 the five local laws hold and ending B succeeds. Lean: `Toy.Views.Ex.scoped_end_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R3g.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.
- Same entry as under R3a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R3h — scoped runs are closed

- **Card id:** `R3h-scoped-runs-are-closed`; **kind:** theorem; **tier:** T1; **depth:** `shallow`; **proof status:** proved (Lean kernel check).
- **Plain claim:** Every scoped run (a computation built from writes and from scopes that open a fresh view by borrow or share, run a scoped inner computation, and end exactly that fresh view, composed sequentially and nested to any depth) is closed; hence a view's return authority survives any scoped run, provided ParentCoversActive holds afterwards.
- **Tier justification:** Folklore (well-nested scopes compose; cf. RustBelt's nested lifetimes) made precise as an induction over an explicit syntax of scoped runs, from R3a, R3d and R3f (and R3c for the authority form).

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.closedViews_of_scopedRun   (ToyViews/Closed.lean:571)
theorem closedViews_of_scopedRun {s s' : State} (h : ScopedRun s s') : ClosedViews s s'

-- Toy.Views.returnAuthority_of_scopedRun_of_parentCoversActive   (ToyViews/Closed.lean:581)
theorem returnAuthority_of_scopedRun_of_parentCoversActive {s₀ s₁ : State} {v : ViewId}
    (hpc : ParentCoversActive s₁) (hauth : ReturnAuthority s₀ v) (hrun : ScopedRun s₀ s₁) :
    ReturnAuthority s₁ v
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
inductive ScopedRun : State → State → Prop
  | refl (s : State) : ScopedRun s s
  | write {s s' : State} {v : ViewId} {a : Addr} {b : Byte} :
      write s v a b = some s' → ScopedRun s s'
  | borrowScope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr} {r : Addr → Byte} :
      borrow s p A = some s₁ → ScopedRun s₁ s₂ → endRaw s₂ s.size r = some s₃ → ScopedRun s s₃
  | shareScope {s s₁ s₂ s₃ : State} {p : ViewId} {A : List Addr} {r : Addr → Byte} :
      share s p A = some s₁ → ScopedRun s₁ s₂ → endRaw s₂ s.size r = some s₃ → ScopedRun s s₃
  | seq {s₀ s₁ s₂ : State} : ScopedRun s₀ s₁ → ScopedRun s₁ s₂ → ScopedRun s₀ s₂
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `h : ScopedRun s s' (hrun in the authority form)` | the computation is a well-bracketed scoped run; in both witnesses the open borrow s1 -> s2 is a genuine borrow step, is proved not to be a scoped run (ScopedRun.isActive_eq), and the conclusion fails | `tight` | `Toy.Views.Ex.closedViews_of_scopedRun_needs_scopedRun`, `Toy.Views.Ex.scopedRun_authority_tightness` |
| `hpc : ParentCoversActive s₁ (authority form)` | as in R3c's second form | `tight` | `Toy.Views.Ex.scopedRun_authority_tightness` |
| `hauth : ReturnAuthority s₀ v (authority form)` | the authority being preserved | `tight` | `Toy.Views.Ex.scopedRun_authority_tightness` |

- **Non-vacuity witness:** From s0: borrow A -> B; inside, borrow B -> C, write through C, end C; then end B. A has authority in s0 and ParentCoversActive holds at the end. Lean: `Toy.Views.Ex.scopedRun_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R3h.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R1a (full text there): Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), Article 66, 2018, doi:10.1145/3158154.
- Same entry as under R3d (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R4a — closed views conditions each necessary

- **Card id:** `R4a-closed-views-conditions-each-necessary`; **kind:** counterexample; **tier:** T1; **depth:** `definitional`; **proof status:** proved (Lean kernel check).
- **Plain claim:** Each of the four closed-views conditions is necessary: for each of NewViewsInactive, ParentsStable, ActivityStable and DomainsStable there are states s₀, s₁ in which view B has return authority in s₀, every parent link of s₀ exists, s₁ satisfies the full loan-tree invariant and the other three conditions, yet B has no return authority in s₁ and ending B there breaks the local laws.
- **Tier justification:** Tightness witnesses for the four conditions of ClosedViews in R3c (both forms) and R3g, gathered as one reference card; folklore made precise.

**Lean statements** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.Ex.returnAuthority_lost_without_newViewsInactive   (ToyViews/Closed.lean:906)
theorem returnAuthority_lost_without_newViewsInactive (r : Addr → Byte) :
    ParentsExist s1 ∧ ReturnAuthority s1 1 ∧
    ParentsStable s1 s2 ∧ ActivityStable s1 s2 ∧ DomainsStable s1 s2 ∧
    ¬ NewViewsInactive s1 s2 ∧ ¬ ReturnAuthority s2 1 ∧
    LoanTreeInv s2 ∧ endRaw s2 1 r = some (s3 (r 0)) ∧ ¬ LocalLoanLaws (s3 (r 0)) ∧
    ¬ LoanTreeInv (s3 (r 0))

-- Toy.Views.Ex.returnAuthority_lost_without_parentsStable   (ToyViews/Closed.lean:917)
theorem returnAuthority_lost_without_parentsStable :
    ParentsExist u2 ∧ ReturnAuthority u2 1 ∧
    ¬ ParentsStable u2 t2 ∧ ActivityStable u2 t2 ∧ DomainsStable u2 t2 ∧
    NewViewsInactive u2 t2 ∧ ¬ ReturnAuthority t2 1 ∧
    LoanTreeInv u2 ∧ LoanTreeInv t2 ∧ endRaw t2 1 (fun _ => 0) = some t3 ∧
    ¬ LocalLoanLaws t3 ∧ ¬ LoanTreeInv t3

-- Toy.Views.Ex.returnAuthority_lost_without_activityStable   (ToyViews/Closed.lean:928)
theorem returnAuthority_lost_without_activityStable (r : Addr → Byte) :
    ParentsExist aS0 ∧ ReturnAuthority aS0 1 ∧
    ParentsStable aS0 s2 ∧ ¬ ActivityStable aS0 s2 ∧ DomainsStable aS0 s2 ∧
    NewViewsInactive aS0 s2 ∧ ¬ ReturnAuthority s2 1 ∧
    LoanTreeInv s2 ∧ endRaw s2 1 r = some (s3 (r 0)) ∧ ¬ LocalLoanLaws (s3 (r 0)) ∧
    ¬ LoanTreeInv (s3 (r 0))

-- Toy.Views.Ex.returnAuthority_lost_without_domainsStable   (ToyViews/Closed.lean:940)
theorem returnAuthority_lost_without_domainsStable (r : Addr → Byte) :
    ParentsExist e2 ∧ ReturnAuthority e2 1 ∧
    ParentsStable e2 s2 ∧ ActivityStable e2 s2 ∧ ¬ DomainsStable e2 s2 ∧
    NewViewsInactive e2 s2 ∧ ¬ ReturnAuthority s2 1 ∧
    LoanTreeInv e2 ∧ LoanTreeInv s2 ∧ endRaw s2 1 r = some (s3 (r 0)) ∧
    ¬ LocalLoanLaws (s3 (r 0)) ∧ ¬ LoanTreeInv (s3 (r 0))
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentsExist (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < s.size
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s
structure LocalLoanLaws (s : State) : Prop where
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
```

**Hypothesis ledger:** none (a closed statement about concrete states).

- **Non-vacuity witness:** Closed statements: each theorem exhibits its states. Lean: `Toy.Views.Ex.returnAuthority_lost_without_newViewsInactive`, `Toy.Views.Ex.returnAuthority_lost_without_parentsStable`, `Toy.Views.Ex.returnAuthority_lost_without_activityStable`, `Toy.Views.Ex.returnAuthority_lost_without_domainsStable`.
- **Non-claims:** listed under **Boundaries**, card R4a.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R3a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R4g — closed views sufficient not necessary

- **Card id:** `R4g-closed-views-sufficient-not-necessary`; **kind:** counterexample; **tier:** T1; **depth:** `definitional`; **proof status:** proved (Lean kernel check).
- **Plain claim:** ClosedViews is sufficient but not necessary for preserving return authority: retiring an unrelated root violates ActivityStable, yet view B keeps its return authority, with the full loan-tree invariant on both sides.
- **Tier justification:** Shows the closed-views relation is stronger than needed; folklore made precise.

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.Ex.closedViews_not_necessary_for_returnAuthority   (ToyViews/Closed.lean:1019)
theorem closedViews_not_necessary_for_returnAuthority :
    LoanTreeInv g1 ∧ LoanTreeInv g1r ∧ ReturnAuthority g1 1 ∧ ReturnAuthority g1r 1 ∧
    ¬ ClosedViews g1 g1r
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s
inductive ProperDesc (s : State) : ViewId → ViewId → Prop
  | child {d c : ViewId} : s.parentOf d = some c → ProperDesc s d c
  | step {d x c : ViewId} : s.parentOf d = some x → ProperDesc s x c → ProperDesc s d c
def ReturnAuthority (s : State) (c : ViewId) : Prop :=
  ∀ d, ProperDesc s d c → s.isActive d = true → ∀ a, s.covers c a = true → s.covers d a = false
def ParentsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.parent = (s₀.view? v).map View.parent
def ActivityStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.active = (s₀.view? v).map View.active
def DomainsStable (s₀ s₁ : State) : Prop :=
  ∀ v < s₀.size, (s₁.view? v).map View.domain = (s₀.view? v).map View.domain
def NewViewsInactive (s₀ s₁ : State) : Prop :=
  ∀ v < s₁.size, s₀.size ≤ v → s₁.isActive v = false
structure ClosedViews (s₀ s₁ : State) : Prop where
  parents : ParentsStable s₀ s₁
  activity : ActivityStable s₀ s₁
  domains : DomainsStable s₀ s₁
  fresh : NewViewsInactive s₀ s₁
```

**Hypothesis ledger:** none (a closed statement about concrete states).

- **Non-vacuity witness:** Closed statement: states g1 and g1r. Lean: `Toy.Views.Ex.closedViews_not_necessary_for_returnAuthority`.
- **Non-claims:** listed under **Boundaries**, card R4g.
- **Design question:** the common design question stated at the start of *Result cards*.

**Prior art:**

- Same entry as under R3a (full text there): Basis: derived (modeling bridge); motivation only, not a subject of this report. AeneasVerif/aeneas pull request #1497 ('Fournet/wip memory model'), branch fournet/wip-memory-model, head commit d17ca83fc07d712d1785f650840cb2073c259e69.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

Basis: derived (modeling bridge) — every statement in this card about the Aeneas memory-model prototype (pull request #1497) is a reading of that prototype's source at head commit `d17ca83fc07d712d1785f650840cb2073c259e69` (see *Modeling bridge*), not a kernel-checked fact; the toy definitions are not proved to correspond to it.

### R5a — depth as counting permission writability

- **Card id:** `R5a-depth-as-counting-permission-writability`; **kind:** characterization; **tier:** T0; **depth:** `shallow`; **proof status:** proved (Lean kernel check).
- **Plain claim:** Under DepthCounts, an active view that holds a cell as an own cell can write it if and only if the view is exclusive-mode and none of its active shared children covers that cell.
- **Tier justification:** A re-derivation of the counting-permission rule (Bornat et al. 2005, Section 6: only a source with no split-off read permissions has total ownership) for depth-annotated cells; under DepthCounts it reduces to 0 + n = 0 iff n = 0, and 1 + n ≠ 0.

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.canWrite_iff_excl_and_no_active_shared_children_of_depthCounts   (ToyViews/Counting.lean:19)
theorem canWrite_iff_excl_and_no_active_shared_children_of_depthCounts
    {s : State} {v : ViewId} {a : Addr} (hdc : DepthCounts s)
    (hact : s.isActive v = true) (hown : (s.depth? v a).isSome = true) :
    s.canWrite v a = true ↔ (s.modeOf v = some .excl ∧ s.activeSharedChildren v a = 0)
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
```

**Hypothesis ledger:**

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
|---|---|---|---|
| `hdc : DepthCounts s` | depth is baseline plus active shared children | `tight` | `Toy.Views.Ex.canWrite_iff_needs_depthCounts` |
| `hact : s.isActive v = true` | inactive views cannot write regardless of depth | `tight` | `Toy.Views.Ex.canWrite_iff_needs_isActive` |
| `hown : (s.depth? v a).isSome = true` | loaned or uncovered cells cannot be written | `tight` | `Toy.Views.Ex.canWrite_iff_needs_own` |

- **Non-vacuity witness:** Both polarities: A in t1 (one reader; both sides false), B in w2 (exclusive, no readers; both sides true), B in t1 (shared-mode; both sides false). Lean: `Toy.Views.Ex.canWrite_iff_nonvacuous`.
- **Non-claims:** listed under **Boundaries**, card R5a.
- **Design question:** How should a sharing-depth annotation on cells be read as permission accounting, and what can a view decide locally from its own depth when it or one of its children ends?

**Prior art:**

- Same entry as under R1b (full text there): Bornat, R., Calcagno, C., O'Hearn, P. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327.
- Boyland, J., 'Checking Interference with Fractional Permissions', Static Analysis (SAS 2003), LNCS 2694, pp. 55-72, Springer, 2003, doi:10.1007/3-540-44898-5_4 (bibliographic data via Crossref): fractional permissions, the standard alternative to counting permissions.
- Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, Springer, doi:10.1007/978-3-642-10672-9_13 (authors' copy checked): share accounting for concurrent-read/exclusive-write resources, with a share model built from binary trees and a reusable Coq development.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

### R5b — depth counts survives naive shared end

- **Card id:** `R5b-depth-counts-survives-naive-shared-end`; **kind:** counterexample; **tier:** T1; **depth:** `definitional`; **proof status:** proved (Lean kernel check).
- **Plain claim:** Exact per-view depth counters do not by themselves prevent the nested shared failure: in t2 (all seven laws hold) the parent A counts its one direct shared child B and B counts its one shared child C, so B fails the local return check; the naive end of B, which consults only A's cell, brings A's counter to zero and lets A write while C still reads, yet DepthCounts still holds in the result t3. What breaks is ParentCoversActive (C is active under the retired B), and with it write exclusivity.
- **Tier justification:** Folklore that a per-node counter sees only direct children (cf. counting permissions), made precise as a mechanized example in which all counters are exact before and after an unsound step.

**Lean statement** (namespace `Toy.Views`; `Ex.` names are in `Toy.Views.Ex`):

```lean
-- Toy.Views.Ex.depthCounts_survives_naive_shared_end_while_writeExclusive_fails   (ToyViews/Counting.lean:97)
theorem depthCounts_survives_naive_shared_end_while_writeExclusive_fails (r : Addr → Byte) :
    LoanTreeInv t2 ∧ t2.activeSharedChildren 0 0 = 1 ∧ t2.activeSharedChildren 1 0 = 1 ∧
    ¬ LocalReturnCheck t2 1 ∧ NaiveAuthority t2 1 ∧
    endRaw t2 1 r = some t3 ∧ t3.activeSharedChildren 0 0 = 0 ∧ DepthCounts t3 ∧
    ¬ ParentCoversActive t3 ∧ t3.canWrite 0 0 = true ∧ t3.canRead 2 0 = true ∧
    ¬ WriteExclusive t3
```

**Key definitions, unfolded** (verbatim, docstrings omitted; operations such as `endRaw`, `borrow`, `share`, `write` and the named states are quoted under *Definitions*):

```lean
def canRead (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && (s.depth? v a).isSome
def canWrite (s : State) (v : ViewId) (a : Addr) : Bool := s.isActive v && s.depth? v a == some 0
def activeSharedChildren (s : State) (v : ViewId) (a : Addr) : Nat :=
  ((List.range s.size).filter (fun c =>
    s.parentOf c == some v && s.isActive c && s.modeOf c == some .shared && s.covers c a)).length
def ParentLt (s : State) : Prop :=
  ∀ v < s.size, ∀ p, s.parentOf v = some p → p < v
def ParentCoversActive (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ p, s.parentOf v = some p →
    s.isActive v = true → s.covers v a = true → s.isActive p = true ∧ s.covers p a = true
def ExclChildLoaned (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .excl → s.covers c a = true →
      s.cell? p a = some (.loaned c)
def SharedChildBelowOwn (s : State) : Prop :=
  ∀ c < s.size, ∀ a < s.width, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf c = some .shared → s.covers c a = true →
      ∃ d, s.depth? p a = some (d + 1)
def SharedChildrenShared (s : State) : Prop :=
  ∀ c < s.size, ∀ p, s.parentOf c = some p →
    s.isActive c = true → s.modeOf p = some .shared → s.modeOf c = some .shared
def DepthCounts (s : State) : Prop :=
  ∀ v < s.size, ∀ a < s.width, ∀ d, s.depth? v a = some d →
    s.isActive v = true → d = s.baselineOf v + s.activeSharedChildren v a
def RootsDisjoint (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.isActive v = true → s.isActive w = true → s.parentOf v = none → s.parentOf w = none →
      s.covers v a = true → s.covers w a = false
structure LoanTreeInv (s : State) : Prop where
  parentLt : ParentLt s
  parentCoversActive : ParentCoversActive s
  exclChildLoaned : ExclChildLoaned s
  sharedChildBelowOwn : SharedChildBelowOwn s
  sharedChildrenShared : SharedChildrenShared s
  depthCounts : DepthCounts s
  rootsDisjoint : RootsDisjoint s
def WriteExclusive (s : State) : Prop :=
  ∀ v < s.size, ∀ w < s.size, ∀ a < s.width, v ≠ w →
    s.canWrite v a = true → s.canRead w a = false
def returnable (vc vp : View) (c : ViewId) : Bool :=
  vp.active && (List.range vc.cells.length).all fun a =>
    match vc.cell? a with
    | none => true
    | some _ =>
      match vc.mode, vp.cell? a with
      | .excl, some (.loaned c') => c' == c
      | .shared, some (.own d _) => decide (vp.mode.baseline < d)
      | _, _ => false
def NaiveAuthority (s : State) (c : ViewId) : Prop :=
  ∃ vc p vp, s.view? c = some vc ∧ vc.active = true ∧ vc.parent = some p ∧
    s.view? p = some vp ∧ returnable vc vp c = true
def LocalReturnCheck (s : State) (c : ViewId) : Prop :=
  ∀ a < s.width, s.covers c a = true → s.depth? c a = some (s.baselineOf c)
```

**Hypothesis ledger:** none (a closed statement about concrete states).

- **Non-vacuity witness:** Closed statement: the states t2 and t3. Lean: `Toy.Views.Ex.depthCounts_survives_naive_shared_end_while_writeExclusive_fails`.
- **Positive control:** `Toy.Views.Ex.parent_counter_zero_means_no_reader_without_nesting` (a nearby setting in which the negative conclusion fails; Lean statement quoted just below).

**Positive control** (Lean statement):

```lean
-- Toy.Views.Ex.parent_counter_zero_means_no_reader_without_nesting   (ToyViews/Counting.lean:108)
theorem parent_counter_zero_means_no_reader_without_nesting (r : Addr → Byte) :
    endRaw t1 1 r = some t1e ∧ t1e.activeSharedChildren 0 0 = 0 ∧ t1e.canWrite 0 0 = true ∧
      LoanTreeInv t1e ∧ WriteExclusive t1e
```

- **Non-claims:** listed under **Boundaries**, card R5b.
- **Design question:** How should a sharing-depth annotation on cells be read as permission accounting, and what can a view decide locally from its own depth when it or one of its children ends?

**Prior art:**

- Same entry as under R1b (full text there): Bornat, R., Calcagno, C., O'Hearn, P. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327.
- Same entry as under R1a (full text there): Ho, S. & Protzenko, J., 'Aeneas: Rust Verification by Functional Translation', Proc. ACM Program. Lang. 6(ICFP), pp. 711-741, 2022, doi:10.1145/3547647.
- Same entry as under R5a (full text there): Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, Springer, doi:10.1007/978-3-642-10672-9_13.

Basis: execution (Lean kernel check) — every Lean name of this card, with the axioms and hashes recorded under **Evidence**.

### Modeling bridge: relation to the Aeneas memory-model prototype

Basis: derived (modeling bridge). Nothing in this subsection is kernel-checked; it records how the
toy definitions were chosen relative to one prototype, read from that prototype's source.

*The prototype.* AeneasVerif/aeneas pull request #1497 (title "Fournet/wip memory model", head
branch `fournet/wip-memory-model`, head commit `d17ca83fc07d712d1785f650840cb2073c259e69`). The
GitHub API, queried on 2026-11-20, reports the pull request open and unmerged and records 54 commits
up to that head, by the commit authors fournet, Cezar Andrici and Son Ho. An unmerged pull request is
not a durable subject, so it is not listed in `REPORT.json`; it motivates the design question and
is described here only as its source files state at that head. Paths below are relative to
`backends/lean/Aeneas/Std/Heap/` unless given in full.

- *State.* `Model.lean` stores each view as a block: base pointer, root allocation id, a list of
  cells, and separate `owned`, `active` (view activity) and `alive` (allocation lifetime) flags.
  Blocks record their root, not their parent. A cell is `shared depth byte` (depth `0` is exclusive
  write permission, positive depths are read-only) or `borrowed` (lent to the unmodelled implicit
  safe heap).
- *Raw evaluator.* `Cell.compatible` (`Repr.lean`): a `borrowed` cell is compatible with anything;
  two `shared` cells are compatible only if both depths are positive and the bytes agree. Raw
  operations built on `Heap.modify` (among them `endBorrow` and `endShare`) and `endExposureAt`
  commit through `commit` (`Model.lean`), which succeeds only if `Heap.check` holds, i.e. all pairs
  of active blocks are compatible at every common address. `endExposureAt` (`Model.lean`) retires a non-owning
  view only if all its cells are at the given baseline depth (`0`; `1` for `endSharedExposure`).
  `README.md` states that raw restoration "checks borrowed cells and heap compatibility, not a
  dynamic loan tree. It can restore a parent while a child view is itself borrowed". In
  `backends/lean/Aeneas/Std/HeapTests.lean`, an example documented as "Raw restoration can succeed
  with a suspended child" restores a parent while the child view's cells are borrowed into the
  implicit heap (there is no explicit grandchild view), and the test `sharedAliases` requires that
  ending the root's share while explicit shared views are active fails. The analogues of the toy
  traces `s2 → s3` and `t2 → t3` (two active explicit writers; a writer beside an active reader)
  are therefore rejected by the prototype's compatibility check. The toy has no implicit heap and no
  global compatibility check; its naive end is a deliberately weaker rule.
- *Authority.* `RootReturn s base` (`Allocation.lean`): the view covers its whole root allocation
  and no other active view of the same root exists (`noAliases`); `RootReturn.modify` shows it is
  preserved by every operation implemented through `Heap.modify`.
- *Closed views.* `ClosedViews s₀ s₁` (`ScopedView.lean`): the fresh-id counter does not decrease;
  ids below `s₀.next` keep their return shape (base pointer, root, length, active flag); ids at or
  above `s₀.next` are inactive. Proved there: `ClosedViews.trans`, and
  `RootReturn.after_closed_views` (assuming also the heap invariant of `s₀` and `base < s₀.next`).
  `NewView s₀ s₁` requires `s₁.next = s₀.next + 1` and every other allocation literally unchanged;
  `RootReturn.after_scoped_view` derives `RootReturn s₁ base` from `NewView s₀ s₁` and inactivity of
  the fresh id.

*Correspondence used in this package* (each item is a modeling choice, not a theorem):

- toy `View.active` ↔ prototype `active`; the prototype's `alive` has no counterpart here;
- toy `Cell.own d b` ↔ prototype `shared d byte`; toy `loaned c` ↔ prototype `borrowed`, except that
  the toy cell names the explicit child it is lent to (the toy has no implicit heap);
- toy `endRaw` ↔ the prototype's raw restoration of a parent's cells combined with retirement of the
  child, *without* the prototype's global compatibility check;
- toy `LocalReturnCheck` ↔ the prototype's baseline-depth check in `endExposureAt`;
- toy `ReturnAuthority` (no active *descendant* on the cells; needs parent links) is *finer* than
  `RootReturn` (no other active view of the *root* at all, plus whole-root coverage); no theorem
  relating the two is proved here;
- toy `ClosedViews` return shape (parent, activity, domain) ↔ prototype return shape (base pointer,
  root, length, active); the counter-monotonicity conjunct is derivable in the toy; the toy needs no
  `v < s₀.size` bound because its authority asserts no positive coverage fact;
- toy `OpenScopeShape` generalizes `NewView` (old views keep their return shape but may change
  cells); toy R3d and R3h have no counterpart in the prototype.

*What follows for the prototype.* Nothing is proved about it. The derived reading is: (1) its raw
evaluator does not exhibit the R1 traces, because of its global compatibility check, not because of
a descendant-based authority check; (2) R2d suggests that a baseline-depth check on the ending view,
like `endExposureAt`'s, suffices for descendant-based authority *when every reborrow is an explicit
view and the tree laws hold*, which the prototype's implicit heap does not guarantee; (3) R3 suggests
that a closed-views relation keeps an outer authority across nested completed scopes, in the toy's
descendant-based form. Checking any of these against the prototype requires a formal relation
between the two models, which this package does not provide.

### Supporting bounded search (not a proof)

Basis: execution of `support/finite_search/reach.py` (Python 3 standard library; a Python
re-implementation of the toy definitions in `support/finite_search/model.py`), run on 2026-11-20.
Label: `[bounded search]`. It explores, breadth-first up to 6 steps from the empty state, all states
with at most 4 views over addresses `{0, 1}` reachable by allocating roots, `borrow`, `share`, and
`endRaw` restricted to ends authorized by return authority, by the local return check, or (up to 4
steps) by the naive rule alone, and reports reachable states that violate a loan-tree law, write
exclusivity, or (for end steps) no-resurrection:

```text
authority: reachable 26033 bad 0
local check: reachable 26033 bad 0
naive: reachable 7514 bad 28
```

This is consistent with R1 (the naive rule reaches bad states) and with R2/R2d, and it is the only
evidence in this package that `borrow` and `share` preserve the loan-tree laws along reachable
traces (no theorem states it; `write` steps are not explored by this script). The other scripts in
`support/finite_search/` (described in its `README.md`) are earlier exhaustive searches over small
state universes; they were not re-run for this report. A passing bounded search shows nothing about
larger states, and the Python model is not proved to agree with the Lean definitions.

## Boundaries

### Non-claims (per result)

Each list states what the result does *not* show. These come first because the results are easy to over-read.

#### R1a (`R1a-naive-end-unsound-nested-exclusive`)

- Does not show that every naive end is unsafe: without a nested reborrow the same naive end is safe (positive control naive_end_safe_without_nested_reborrow).
- Does not show that detecting an active exclusive reborrow requires nonlocal traversal of descendants: in this explicit-tree model (under LoanTreeInv, in fact under ParentCoversActive, ExclChildLoaned and DepthCounts alone), checking locally that the ending child view itself holds every covered cell as own at its baseline depth (not loaned to a grandchild) already implies ReturnAuthority and blocks this trace (R2d, localReturnCheck_examples_neg); nonlocal authority may become necessary when child borrows can reside in an unmodelled implicit context or when parent restoration is decoupled from child retirement (not analysed here).
- Does not reproduce a trace accepted by the raw evaluator of the Aeneas memory-model prototype (pull request #1497): that evaluator checks pairwise cell compatibility across all explicit active views on every commit, which rejects two explicit active writers as in s3; it restores a parent prematurely only when the child view's cells are marked borrowed into the unmodelled implicit safe heap. No claim that Aeneas or the prototype is unsound. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]
- Does not rule out alternative sound semantics for parent reactivation, such as dynamically invalidating (disabling) all active descendants when an ancestor regains access, as in Stacked Borrows and Tree Borrows.
- A global post-step check that rejects any end whose result is not write-exclusive would refuse this particular step (s3 is not write-exclusive), but single-step write exclusivity and no-resurrection are not an inductive criterion on their own (naive_shared_end_hidden_by_sibling_reader).
- The naive rule tested is the strictest parent-side rule considered: the child and its parent must be active and the parent must hold each of the child's cells as an outstanding loan; any more permissive parent-side rule admits the same trace.
- The toy end operation merges 'retire the child' and 'restore the parent'; models that separate them may fail differently (e.g. restoring the parent while the child stays active) but are not analysed.
- Only the safety property defined here (write exclusivity, no resurrection) is violated; no claim about undefined behaviour in Rust or any particular aliasing model.
- Models neither physical allocation lifetime ('alive') nor deallocation.

#### R1b (`R1b-naive-end-unsound-nested-shared`)

- Does not show that decrementing a sharing depth is unsound in general: with no nested reader (t1) the naive end is safe (positive control).
- Does not show that per-view sharing-depth counters cannot locally block premature ending of a re-shared borrow: in t2 the ending view B itself has depth 2 (above its shared baseline 1), and requiring a retiring view's own cells to sit at its baseline depth (the local return check; the Aeneas prototype's endSharedExposure checks depth 1) rejects this step locally (localReturnCheck_examples_neg, R2d). [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]
- Applies to hierarchical per-view share counting; in a flat design where a shared reborrow is recorded on the original owner's loan (as in the Aeneas semantics' shared-loan identifier sets), ending an intermediate shared borrow while a derived reader remains active leaves the owner's loan in place, so this failure does not arise there (reasoned from the cited source, not analysed here).
- Does not reproduce a trace accepted by the raw evaluator of the Aeneas prototype, whose commit check rejects restoring a writer while another explicit active view holds positive sharing depth on the same address. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]
- The counters in t2 are exact (DepthCounts holds before the step, and still holds after it, R5b); the failure is not a counting error but the rule's consultation of the parent's cell only.
- No claim about Rust shared references as such: shared references are freely copyable in Rust; this toy models a design in which read-only views re-share explicitly.
- Models neither physical allocation lifetime ('alive') nor deallocation.

#### R2a (`R2a-end-under-return-authority-preserves-invariant`)

- Only one step is covered; preservation of the laws by borrow, share and write is not stated (it was checked only by a bounded finite search over small states, support/finite_search; that search is not a proof).
- Return authority is a precondition the caller must establish; the raw end operation does not check it. A sufficient local check is given in R2d.
- Each of the five local laws is necessary, and in each counterexample the step itself breaks NoResurrection or a law that held before; the set is not claimed to be the unique minimal one.
- ParentLt and RootsDisjoint are not used by the main form: endRaw preserves them unconditionally (endRaw_preserves_parentLt, endRaw_preserves_rootsDisjoint), and the full-invariant form assumes them only as fields of LoanTreeInv s. They are needed for write exclusivity (R2b, R2c), not for this preservation step; in particular the local laws and NoResurrection are preserved even in cyclic or multi-root states.
- Applies only to child views (views with a parent): endRaw always returns none on root views (endRaw_eq_none_of_parentOf_eq_none), so this theorem says nothing about reclaiming, returning, or deallocating root allocations.
- ReturnAuthority is cell-wise: ending view c is permitted even when c has an active descendant with empty domain (covering no cells), leaving that empty descendant active under a retired parent (returnAuthority_ignores_active_empty_descendants).
- NoResurrection compares coarse three-valued access levels (0 none, 1 read at any positive depth, 2 write at depth 0): an unauthorized end of a shared view that decrements its parent from depth 2 to depth 1 satisfies both WriteExclusive and NoResurrection in that single step while breaking LoanTreeInv, so single-step WriteExclusive and NoResurrection without LoanTreeInv is not an inductive safety criterion (naive_shared_end_hidden_by_sibling_reader).
- LoanTreeInv constrains permissions only, not byte values: two concurrent active readers of the same address may hold distinct bytes in their cells (loanTreeInv_allows_reader_byte_disagreement), and ending a shared view leaves the parent's stored byte unchanged.
- The returned bytes r are arbitrary: no claim about functional correctness of the values handed back (only permissions are tracked).
- Toy model: no allocation, deallocation, allocation lifetime ('alive'), addresses, layout or typed values.

#### R2b (`R2b-loan-tree-laws-imply-write-exclusivity`)

- Establishes mutual exclusion between writers and other active readers or writers, not value coherence: LoanTreeInv permits two active readers of the same cell to hold different byte values (loanTreeInv_allows_reader_byte_disagreement).
- The converse fails: write exclusivity does not imply the laws; no characterization is claimed.
- No theorem in this package assumes write exclusivity separately: it is derivable from the laws.

#### R2c (`R2c-end-under-return-authority-write-exclusive`)

- A reference point combining R2a and R2b; it adds no hypothesis or argument beyond them.
- Neither return authority alone nor write exclusivity of the pre-state together with return authority suffices: every counterexample starts from a write-exclusive state in which the ended view has return authority.
- Applies only to child views (views with a parent): endRaw always returns none on root views (endRaw_eq_none_of_parentOf_eq_none), so this theorem says nothing about reclaiming, returning, or deallocating root allocations.
- ReturnAuthority is cell-wise: ending view c is permitted even when c has an active descendant with empty domain (covering no cells), leaving that empty descendant active under a retired parent (returnAuthority_ignores_active_empty_descendants).
- Write exclusivity is mutual exclusion of permissions, not value coherence (loanTreeInv_allows_reader_byte_disagreement).
- Toy model: no allocation, deallocation, allocation lifetime ('alive'), addresses, layout or typed values.

#### R2d (`R2d-local-baseline-check-implies-return-authority`)

- The local check alone does not imply return authority or a safe end: each of ParentCoversActive, ExclChildLoaned and DepthCounts is needed, and in each counterexample the view passes the check, has no return authority, and its raw end succeeds and breaks NoResurrection (localCheck_needs_parentCoversActive, localCheck_needs_exclChildLoaned, localCheck_needs_depthCounts).
- Return authority (the first statement) does not need SharedChildBelowOwn or SharedChildrenShared, but a safe end does: with either law dropped, a view that passes the check and has return authority can be ended so that DepthCounts breaks (localCheck_end_needs_sharedChildBelowOwn, localCheck_end_needs_sharedChildrenShared). The end form therefore assumes all five tree-local laws; like R2a it does not need ParentLt or RootsDisjoint.
- The check does not make the end enabled: it holds for retired and nonexistent views, whose raw end fails (localReturnCheck_does_not_enable_end); the end form says nothing about views whose raw end fails (root views, retired views, or views whose parent does not hold their cells as outstanding loans).
- The local check is sufficient, not necessary: it refuses ends that return authority permits, e.g. when the view still records a loan to an already retired child (localReturnCheck_strictly_stronger_than_returnAuthority).
- Relies on every reborrow being an explicit view whose loan is recorded exactly in its parent (ParentCoversActive, ExclChildLoaned, DepthCounts); where a view's cells can be lent to an unmodelled context, or loan records are inexact, a local check need not imply authority (not analysed).
- Like ReturnAuthority, the check is cell-wise: an active child covering no cells does not make it fail (returnAuthority_ignores_active_empty_descendants).
- No claim about the cost of maintaining the laws that make the check sound, nor about reachability of states satisfying them.

#### R3a (`R3a-closed-views-preorder`)

- ClosedViews leaves View.mode of pre-existing views unconstrained (an exclusive view in s₀ may become shared in s₁ or vice versa while ClosedViews and LoanTreeInv hold on both sides, closedViews_ignores_modes), and imposes no frame condition on bytes or permission forms of any cell, including unborrowed cells and unrelated roots.
- ClosedViews is only the return-authority half of a nested-scope specification: it preserves neither LoanTreeInv (closedViews_does_not_preserve_loanTreeInv) nor the parent cells that ending an outer view needs (closedViews_does_not_preserve_end_enabledness).
- Models no physical deallocation or separate allocation-lifetime flag ('alive'); in a model with deallocation, preserving return shape alone does not prevent a scope from deallocating an allocation.

#### R3c (`R3c-closed-views-preserve-return-authority`)

- For view ids v >= s₀.size (views not yet created in s₀), ReturnAuthority s₀ v holds vacuously because v covers no cells in s₀ (returnAuthority_vacuous_of_ge_size), and NewViewsInactive forces v to be inactive or absent in s₁, so endRaw s₁ v r is always none (endRaw_eq_none_of_closedViews_of_ge_size); the conclusion grants endable authority only to views that already existed in s₀.
- ClosedViews is sufficient, not necessary: retiring an unrelated old view violates ActivityStable but preserves authority (R4g).
- ClosedViews leaves View.mode of pre-existing views unconstrained (an exclusive view in s₀ may become shared in s₁ or vice versa while ClosedViews and LoanTreeInv hold on both sides, closedViews_ignores_modes), and imposes no frame condition on bytes or permission forms of any cell, including unborrowed cells and unrelated roots.
- ClosedViews is only the return-authority half of a nested-scope specification: it preserves neither LoanTreeInv (closedViews_does_not_preserve_loanTreeInv) nor the parent cells that ending an outer view needs (closedViews_does_not_preserve_end_enabledness).
- Authority here is descendant-based and requires parent links; it is not the Aeneas prototype's root-wide alias check, and no theorem relates the two. Unlike RootReturn.after_closed_views, no bound on v is needed, because this authority asserts no positive coverage fact. [Statements about the prototype: derived (modeling bridge) from its source at head commit d17ca83fc07d712d1785f650840cb2073c259e69; not kernel-checked.]
- Models no physical deallocation or separate allocation-lifetime flag ('alive'); in a model with deallocation, preserving return shape alone does not prevent a scope from deallocating an allocation.

#### R3d (`R3d-fresh-scope-is-closed`)

- ClosedViews is only the return-authority half of a nested-scope specification: closedViews_of_fresh_scope and its borrow/share corollaries establish neither LoanTreeInv nor outer endRaw enabledness after the scope, so chaining them into R3g requires separate invariant-preservation and parent-cell framing arguments (closedViews_does_not_preserve_loanTreeInv, closedViews_does_not_preserve_end_enabledness).
- Covers one scope; arbitrarily nested and sequenced scopes are covered by R3h (an induction using R3a, R3f and this theorem).
- The byte-restoration argument r of endRaw is unused when ending a shared view (the parent keeps its own byte with decremented depth).
- ClosedViews leaves View.mode of pre-existing views unconstrained (an exclusive view in s₀ may become shared in s₁ or vice versa while ClosedViews and LoanTreeInv hold on both sides, closedViews_ignores_modes), and imposes no frame condition on bytes or permission forms of any cell, including unborrowed cells and unrelated roots.
- Models no physical deallocation or separate allocation-lifetime flag ('alive'); in a model with deallocation, preserving return shape alone does not prevent a scope from deallocating an allocation.

#### R3f (`R3f-write-is-closed`)

- Says nothing about which writes are permitted beyond the operation's own check.
- LoanTreeInv of the result is not asserted (preservation of the laws by write is not stated).

#### R3g (`R3g-scoped-end-preserves-invariant`)

- ClosedViews s₀ s₁ does not preserve LoanTreeInv (closedViews_does_not_preserve_loanTreeInv): the local laws must be established for s₁ separately, and this theorem does not say how.
- R3d and R3h produce ClosedViews, but neither the laws of s₁ nor enabledness of the end (hend); combining them requires invariant-preservation results not stated here.
- Full LoanTreeInv of s₂ follows if ParentLt and RootsDisjoint also hold in s₁ (frame lemmas); write exclusivity of s₂ then follows by R2b.
- ClosedViews leaves View.mode of pre-existing views unconstrained (an exclusive view in s₀ may become shared in s₁ or vice versa while ClosedViews and LoanTreeInv hold on both sides, closedViews_ignores_modes), and imposes no frame condition on bytes or permission forms of any cell, including unborrowed cells and unrelated roots.
- Applies only to child views (views with a parent): endRaw always returns none on root views (endRaw_eq_none_of_parentOf_eq_none), so this theorem says nothing about reclaiming, returning, or deallocating root allocations.
- ReturnAuthority is cell-wise: ending view c is permitted even when c has an active descendant with empty domain (covering no cells), leaving that empty descendant active under a retired parent (returnAuthority_ignores_active_empty_descendants).
- NoResurrection compares coarse three-valued access levels (0 none, 1 read at any positive depth, 2 write at depth 0): an unauthorized end of a shared view that decrements its parent from depth 2 to depth 1 satisfies both WriteExclusive and NoResurrection in that single step while breaking LoanTreeInv, so single-step WriteExclusive and NoResurrection without LoanTreeInv is not an inductive safety criterion (naive_shared_end_hidden_by_sibling_reader).
- LoanTreeInv constrains permissions only, not byte values: two concurrent active readers of the same address may hold distinct bytes in their cells (loanTreeInv_allows_reader_byte_disagreement), and ending a shared view leaves the parent's stored byte unchanged.
- Models no physical deallocation or separate allocation-lifetime flag ('alive'); in a model with deallocation, preserving return shape alone does not prevent a scope from deallocating an allocation.

#### R3h (`R3h-scoped-runs-are-closed`)

- ScopedRun covers only writes and well-bracketed borrow/share scopes that end exactly their own fresh view; interleaved (non-nested) borrow lifetimes, two-phase borrows, and scopes closed by ending any other view are not covered.
- Closedness says nothing about LoanTreeInv or enabledness of ends after the run (see R3d); the authority form needs ParentCoversActive of the final state as a separate hypothesis.
- Models no physical deallocation or separate allocation-lifetime flag ('alive'); in a model with deallocation, preserving return shape alone does not prevent a scope from deallocating an allocation.

#### R4a (`R4a-closed-views-conditions-each-necessary`)

- Shows only that NewViewsInactive cannot be dropped outright from ClosedViews in R3c/R3g; a weaker condition requiring inactivity only of newly created views that cover (or lie on a parent chain to) cells of the outer view is not ruled out.
- The ParentsStable witness re-parents an active shared reader C from A to its sibling B (u2 -> t2), with LoanTreeInv on both sides; a weaker condition forbidding only re-parenting into the outer view's subtree is not ruled out.
- In the ActivityStable witness the pre-scope state aS0 has B holding cell 0 as loaned 2 to an already retired child C; LoanTreeInv aS0 holds because the structural child laws quantify over active children only, though aS0 is not reachable from s0 by the operations of this model (and no operation re-activates a retired view). Only re-activation threatens authority, not retirement (R4g).
- DomainsStable is required only because ReturnAuthority is cell-wise (the active empty-domain child of e2 later acquires address 0); under a stricter authority forbidding active descendants regardless of domain, domain stability of old views would not be needed for this purpose.
- The post-scope states are not produced from the pre-scope states by operations of this model; the witnesses show necessity for the stated theorems, not that a real scope could violate the conditions.

#### R4g (`R4g-closed-views-sufficient-not-necessary`)

- Does not characterize the weakest relation preserving authority; a relation that lets old views be retired but not re-activated (with the other three conditions) is suggested, but neither its transitivity nor its preservation of authority is stated.
- Retiring an ancestor of the outer view while the outer view stays active breaks ParentCoversActive; such states are not considered here.

#### R5a (`R5a-depth-as-counting-permission-writability`)

- Each view's counter counts only its direct shared children; a reader further down is recorded in the intermediate view's own counter, not in this view's (R5b).
- Shared-mode views re-sharing (depth above 1) have no counterpart in Bornat et al.'s pure integer counting algebra (Section 6 and Section 10.2), where split-off read permissions cannot be split further; Bornat et al.'s combined rational model (Section 10.4) instead supports sub-splitting read permissions by making them divisible (fractional) rather than by per-view integer counters.
- Algebraic comparison among fractional permissions, integer counting permissions, tree shares, and per-cell sharing depths as abstract permission models is outside the scope of this package.
- While a parent's own depth counts only its direct active shared children, checking locally on a retiring child view that its covered cells are own at its mode baseline (depth 0 for exclusive, depth 1 for shared) suffices under LoanTreeInv to exclude active nested readers as well (R2d).

#### R5b (`R5b-depth-counts-survives-naive-shared-end`)

- Only the parent A's counter is blind to C: in t2 the intermediate view B has local depth 2 (activeSharedChildren 1 0 = 1), so requiring a retiring shared view's own depth to equal its baseline 1 prevents premature write recovery without traversing descendants (R2d); recording shared loans on the original owner, as in the Aeneas semantics, would also avoid it (reasoned from the cited source, not analysed here).
- Applies to hierarchical integer counters, not to Bornat et al.'s pure integer counting model (Sections 6 and 10.2, where read permissions cannot be re-split) or combined rational model (Section 10.4, where read permissions are divisible).
- Does not show that DepthCounts is useless: it is needed for R2a, R2b and R2d; it is just not sufficient without ParentCoversActive.

### Escape hatches

For the impossibility results (R1a, R1b) and the counterexample results (R4a, R4g, R5b), these are
the assumptions whose change defeats the negative conclusion:

- **R1a, R1b — the end rule.** The traces need the naive rule, which inspects only the parent's
  placeholder cells. Requiring return authority (R2a, R2c) or the local return check under the tree
  laws (R2d) rules out both traces (`localReturnCheck_examples_neg`: the ended view `B` fails the
  check in `s2` and `t2`).
- **R1a, R1b — nesting.** Without the nested reborrow the same naive end is safe (positive controls
  `naive_end_safe_without_nested_reborrow`, `naive_end_safe_without_nested_shared_reborrow`).
- **R1a, R1b — a global post-step check.** A step relation that rejects any end whose result is not
  write-exclusive would refuse these particular steps; but single-step write exclusivity and
  no-resurrection are not an inductive criterion (`naive_shared_end_hidden_by_sibling_reader`), so
  such a check alone does not restore soundness in this model.
- **R1a, R1b — dynamic invalidation.** A semantics that disables all active descendants when an
  ancestor regains access (as aliasing models with per-location stacks or trees of derived
  references do) is not modelled; the traces say nothing about it.
- **R1a, R1b — implicit loans.** The toy has no implicit heap of unmodelled safe loans; where child
  borrows can reside outside the explicit view tree, whether the local check of R2d still implies
  authority is not analysed.
- **R5b — counters versus tree shape.** Exact depth counters survive the naive shared end, but the
  local return check on the ending view (`B` has depth 2 above its baseline 1 in `t2`) or the law
  `ParentCoversActive` in the post-state detects the problem.
- **R4a — which relaxation.** Each counterexample drops one closed-views condition in one specific
  way; weaker conditions than `ClosedViews` can still preserve authority in particular cases (R4g),
  and no minimal sufficient condition is identified.

### Attractive stronger conclusions that are not established

- That any of these results holds for Rust, for the Aeneas semantics, for the prototype described
  under *Modeling bridge*, or for any production memory model. Only the toy model is formalized.
- That the loan-tree invariant is an invariant of the whole toy step relation: preservation is
  proved only for `endRaw` under return authority (R2a); for `borrow`, `share` and `write` it is
  supported only by the bounded search above. Consequently there is no theorem that every state
  reachable with authority-checked ends is write-exclusive.
- That return authority can always be checked locally: R2d needs the tree laws and explicit
  reborrows; in models with implicit loans or with parent restoration decoupled from child
  retirement this is not analysed.
- That `ClosedViews` carries the loan-tree invariant or end-enabledness across a scope: it does not
  (`closedViews_does_not_preserve_loanTreeInv`, `closedViews_does_not_preserve_end_enabledness`);
  the five local laws must be re-established after a scope (R3g).
- That `ClosedViews` is necessary for keeping return authority: it is not (R4g).
- That bytes are coherent across views, that allocation lifetime or deallocation is handled, or that
  anything holds under concurrency: none of these is modelled.

### Not examined

- Allocation and deallocation of roots, allocation lifetime distinct from view activity, pointer
  provenance, layout, and typed values.
- Implicit (unmodelled) safe loans, function calls and protectors, two-phase borrows, interior
  mutability, and prophecy-style values returned at the end of an exclusive borrow beyond an
  arbitrary function `r`.
- Any formal relation between the toy model and the prototype or Aeneas.

### Hypotheses of unknown tightness

None: every hypothesis of every card is labelled `tight` (with a proved counterexample named in the ledger) or `harmless` (it only names the post-state of the step under analysis).

### Disproved or dropped statements

None. No statement of this package was found false, weakened, or dropped: every result listed above
is proved in Lean with the exact statement recorded under **Evidence**. The gaps in the card
numbering (no R3b, R3e, or R4b–R4f) do not correspond to any dropped statement.

## Evidence

All evidence was acquired on 2026-11-20.

*Toolchain.* Lean `leanprover/lean4:v4.34.1` (pinned in `lean/lean-toolchain`); the release tag
`v4.34.1` points to commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub API, tag ref of
`leanprover/lean4`), and the binary used reports `Lean (version 4.34.1, x86_64-unknown-linux-gnu,
commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` and `Lake version 5.0.0-src+5045d00`.
Core library and `Std` only; no Mathlib, no Lake dependencies.

*Build.* `lake build` in `lean/` builds the library `ToyViews` (modules `Basic`, `Laws`, `States`,
`Authority`, `Naive`, `Frame`, `EndSafeLemmas`, `EndSafe`, `Closed`, `Counting`) without errors or
`sorry` warnings. The Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`,
`implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. `ToyViews/EndSafeLemmas.lean`
(namespace `Toy.Views.ProofLemmas`) and the lemma `Toy.Views.ProofLemmas.old_of_active_of_closedViews`
in `ToyViews/Closed.lean` hold auxiliary lemmas used only inside proofs; they introduce no
definitions. `lean/RevalidationAudit.lean` is not part of the library target.

*What is hashed.* For each Lean name referenced by `results.json`, `audit/statements.json` records
SHA-256 of (a) the statement: the Lean `repr` of the declaration's type, and (b) the definition
closure: the sorted list of lines `name : repr(type)` (followed by ` := repr(value)` for
non-theorems) for every constant of the `ToyViews` library reachable from the statement through
types and definition values, with theorem bodies excluded; so the closure fixes every definition the
statement depends on, but no proof. `audit/axioms.json` records `Lean.collectAxioms` for every
library declaration. Both files are regenerated and compared by `support/revalidate.py`
(see **Revalidation**).

### Kernel-check record per card-referenced declaration

Axioms are those reported by `Lean.collectAxioms` for the declaration (none of them is `sorryAx`); hashes are SHA-256 of the statement text and of the definition-closure text, as recorded in `audit/statements.json` (closure size in parentheses).

| declaration | role(s) | axioms | statement SHA-256 | closure SHA-256 (size) |
|---|---|---|---|---|
| `Toy.Views.Ex.borrow_scope_nonvacuous` | R3d non-vacuity | propext | `a49ac7ebcf0f96f038c0674b508304425f375411b6c0e83ffa15d88141383c60` | `ae30e6b509835e9016b9d07b082d3be9be917fd0ae7aad2f7556ce20213ee3da` (65) |
| `Toy.Views.Ex.canWrite_iff_needs_depthCounts` | R5a counterexample | propext | `61499f53a383d8a70d4eed00a742ab882b32f70f553496cf86fc8331585451ac` | `2690632a160c4966d0ee4f4dff226736923d1a79d688ef5250784c2d56395728` (45) |
| `Toy.Views.Ex.canWrite_iff_needs_isActive` | R5a counterexample | propext | `2be7db9bb900bdb5d9936c163151c786063e7d36b2a52c89d9f36432ece7a834` | `f4b052411ee1c923eba3522ffa72fbc13e5dbe89c3bac500b8bf92b81d4be429` (45) |
| `Toy.Views.Ex.canWrite_iff_needs_own` | R5a counterexample | propext | `17a003ca58a2579c4caf1e5b44211d4ff5c99fd0aa8c9a8cbf27203c39194a3d` | `332c6955b3be34104c508c706a1da45ebaf2bb3125a9b11ed22d246763791cf7` (45) |
| `Toy.Views.Ex.canWrite_iff_nonvacuous` | R5a non-vacuity | propext | `b4199754839f8f9467b579f4390186c6b0db3492d4bcb5934ddf82842714f305` | `f22a221e7352c0ed25192aa2326344cd045963dd6b586fe9ae35eb1e3d48d368` (46) |
| `Toy.Views.Ex.closedViews_not_necessary_for_returnAuthority` | R4g result, R4g non-vacuity | Classical.choice, Quot.sound, propext | `4027bfffe79db56076821fa76f3db146979e9bf7bccc6d092109ab675973eaf5` | `5a6b01ad5735bda3c5160d1ecd620aa1423b882c0cf6b1fdd4a684732e0b3ce2` (64) |
| `Toy.Views.Ex.closedViews_of_borrow_scope_needs_inner_closed` | R3d counterexample | propext | `151b1aab5cd1171072871cf9a08b840b91cf7705ad8813b2af492d665ad4c6ad` | `4edfb11722855f4db554cf18c35300a87b6316032ee973ad3816a8fd710cd008` (64) |
| `Toy.Views.Ex.closedViews_of_scopedRun_needs_scopedRun` | R3h counterexample | Quot.sound, propext | `e1ee1535496a89e913a092d3e4efe731fc6c9060b1a5e4946864162f707e4269` | `ee72d04fb22face972fec622e02bbd9a1b8b009e81e9ff8256a279271e0171ec` (75) |
| `Toy.Views.Ex.closedViews_of_share_scope_needs_inner_closed` | R3d counterexample | propext | `78eb617c30a521a36d52bd7b846458652b2f5adbc2eb7fd88ca3dbe588544939` | `103e95dbc0f5fa78ebc01849f2b368ff4f41faf8cb4dbdda710d49ebc5a472e7` (59) |
| `Toy.Views.Ex.closedViews_trans_needs_both` | R3a counterexample | propext | `5d1a14782f6977368dc08955b2ff869c519904938f97f71bdfc6a6377c997725` | `c9dc57195371c5b579e6a94f69a594e8c91e4784f4b978a68c085f17aca0a472` (30) |
| `Toy.Views.Ex.closedViews_trans_nonvacuous` | R3a non-vacuity | propext | `3b75457e5c5868118790019d39522ccb34b76ac9589f6bb0be5e5e88ebf57458` | `e928e75a29640d2a1f8020806f8c38c475e7e1133fafeeae6e3a0888febda7c3` (30) |
| `Toy.Views.Ex.depthCounts_survives_naive_shared_end_while_writeExclusive_fails` | R5b result, R5b non-vacuity | Classical.choice, Quot.sound, propext | `8919e0e5fec8888a626ebd16ac56d164ddfa7c55818fc26ebe439ed4233f4500` | `9d2f78a0287627dd4401d2c23ef798caea61ed9a36976bcc6790043293d0261f` (73) |
| `Toy.Views.Ex.endRaw_inv_needs_depthCounts` | R2a counterexample, R2c counterexample | Classical.choice, Quot.sound, propext | `543baf8dd6a63ac2ce2a1086a21a04e49686d666854bed781283cc30a73707df` | `23d68b326e6cbc6ba96ecc4a1f7d21dea8a469c27bb15159a13f9ed89a9ab738` (74) |
| `Toy.Views.Ex.endRaw_inv_needs_exclChildLoaned` | R2a counterexample, R2c counterexample | Classical.choice, Quot.sound, propext | `ecd5bdda0b9ae9c1fef446e189fade106c0a79939748b0e038057ac633097870` | `b149ff6324b836b48f52b79060225ad169fab39f1ce8d9d2fbd8d628a9743469` (76) |
| `Toy.Views.Ex.endRaw_inv_needs_parentCoversActive` | R2a counterexample, R2c counterexample | Classical.choice, Quot.sound, propext | `e4797fa8eef373102c23f6d5ad143742d9e28751de4b0c55db0bcb6b834bd9b4` | `63cd69cc128982a8e02cef173b48589f4dddfc0ca0ff1eba4d56794086360f1b` (76) |
| `Toy.Views.Ex.endRaw_inv_needs_returnAuthority` | R2a counterexample, R2c counterexample | Classical.choice, Quot.sound, propext | `af42df8d3f5999cce6c189dd1a1db9fc92c7e53abf69fd81dfe254e7e622ac3c` | `a16e9eb320a0bd538d6699e3334dcee7354c6dc080b485dc4634c4c065308dcf` (78) |
| `Toy.Views.Ex.endRaw_inv_needs_sharedChildBelowOwn` | R2a counterexample, R2c counterexample | Classical.choice, Quot.sound, propext | `08520fa735372aa997e8785a796c8b212c369b9a1bce6912a8f56e63e6495cb3` | `2238b7998719684e503e3b6267ce1e4dd02a5e4b3bb152d888a1c045e3f52cf9` (74) |
| `Toy.Views.Ex.endRaw_inv_needs_sharedChildrenShared` | R2a counterexample, R2c counterexample | Classical.choice, Quot.sound, propext | `60d0f82f0da7d3d107ccf677d25703b089b1b3d25b3716648890757dc6096039` | `902c37fecf3334f84b39771f78d1a32b730fc99526b3a3ac8be10e769c2d9764` (74) |
| `Toy.Views.Ex.endRaw_inv_nonvacuous_nested` | R2a non-vacuity, R2c non-vacuity | Classical.choice, Quot.sound, propext | `7a6b6eceb141de7929c79b90eb9e8d27fa5095490990913ef84c1eaf8d111b26` | `0c4b53168c1ab8844c51776ec6c1f68aa6dc28e6f4cc7aa5cc6727e3ed8f23d9` (72) |
| `Toy.Views.Ex.endRaw_inv_nonvacuous_shared` | R2a non-vacuity, R2c non-vacuity | Classical.choice, Quot.sound, propext | `c03c60d6f1a432b99f13d7315f66996acfcdd26bc3bea99354fc4bb6ec1f19dd` | `9730e01769dbcceb09aa6f5f761db949ca6e985b23ae23e78d71a21804b87ec7` (73) |
| `Toy.Views.Ex.endRaw_writeExclusive_needs_parentLt` | R2c counterexample | Classical.choice, Quot.sound, propext | `5588ca6b6305abdaa7be4a6db6d40fbf905907ee84a89e3ca5db67a322b345cb` | `28f9f0cea24def4931eb5ccbba79eeb635462dc5dc5240d630e23793561414ad` (76) |
| `Toy.Views.Ex.endRaw_writeExclusive_needs_rootsDisjoint` | R2c counterexample | Classical.choice, Quot.sound, propext | `ac061e600de8a1d6bd36c62808a75f62a949d9dc8cf91c2fdd00f0e5d630c04c` | `f5758e0a49fa7ab79769b4ec3fc178b13fe8cf9748244b43cd110348dcfe4ca3` (76) |
| `Toy.Views.Ex.fresh_scope_needs_end_of_fresh_view` | R3d counterexample | propext | `1b8d4293a9dd75f9af2a35348d7fe8a2115f84017dd85e8fedab166ce4f8c9d1` | `aebf7748f6cf9555dd5ab697a9bd0b7e4c9da9edd3f2d1fa537b5fbe80077edf` (55) |
| `Toy.Views.Ex.fresh_scope_needs_open_step` | R3d counterexample | propext | `873cb10be6c6e08e020e70db4f3da47854e8f6319cf414f79fa6594a2e0dcf2c` | `026c12c2f718a12667305c0aef714b5d4d20438ccbe25ff1a146fca090997edb` (55) |
| `Toy.Views.Ex.loanTree_laws_nonvacuous` | R2b non-vacuity | Classical.choice, Quot.sound, propext | `243f81f296157e9722237bbc8cf88b59641c05e9ddb84aad285991c5d7ae4907` | `04f7647585204ce234cd78cfa07f13939767e1e538c4edc7d180336894cc1375` (55) |
| `Toy.Views.Ex.localCheck_end_needs_sharedChildBelowOwn` | R2d counterexample | Classical.choice, Quot.sound, propext | `c85a9c95d22364acd229e1ab0dcce89cc7d285904cd43403f3d55959b38164ee` | `87c01127af823bd37a0309c5e1b799c29229db7e637c8705021fa9020b5b4516` (74) |
| `Toy.Views.Ex.localCheck_end_needs_sharedChildrenShared` | R2d counterexample | Classical.choice, Quot.sound, propext | `7baaafceba8cf1d8e5ba87e0e3ceadc8efb7d157ec1df22427b44b5d8fdec533` | `1d47509c9ee68d09d69af52cbc3c912b2ebcb5b29b00f73678bc0c1f2faf4af9` (74) |
| `Toy.Views.Ex.localCheck_needs_depthCounts` | R2d counterexample | Classical.choice, Quot.sound, propext | `09669529244c3a2d990161ae3ba70dbff23f1068c834001d612ebbf2c4b49816` | `b7ac5882bb238b4704a9740925b2491701c1e7f486f15a9fa62426b32bea4747` (74) |
| `Toy.Views.Ex.localCheck_needs_exclChildLoaned` | R2d counterexample | Classical.choice, Quot.sound, propext | `01a2c564e8c0ae8a669a563aee19b863900dda121656646060ec459c2f92e4ee` | `8059892a445c6eeab3b7a6cda75a8dedd578beaecb23d9987fe513c3f38000a7` (74) |
| `Toy.Views.Ex.localCheck_needs_localReturnCheck` | R2d counterexample | Classical.choice, Quot.sound, propext | `b2365bbcf2599f891c619b6c9bcccce6198d5acf7e8256853cf8f7e4959b4c58` | `50ffeff9be44cfcb07adbc73e78f739c866098b686718cc137071ee0a06d9307` (74) |
| `Toy.Views.Ex.localCheck_needs_parentCoversActive` | R2d counterexample | Classical.choice, Quot.sound, propext | `619a67f5114ac2c42f25dbdcc45e4c13f825cec6e7bd94da3f9a73690bf14a2c` | `9cce547197dc8892e198a27e4ffa9955369f233435607eb9939d1bcbd0263de5` (74) |
| `Toy.Views.Ex.localCheck_nonvacuous` | R2d non-vacuity | Classical.choice, Quot.sound, propext | `12246af5aada8815873f2aeebd642c2a4010cc7fbb8ed4362cfd4376f11cdc35` | `57c4a42dc8bfc4d90f698126c19cba356f4e304178f1562176e91c78d0378aed` (65) |
| `Toy.Views.Ex.naive_end_breaks_safety_of_nested_exclusive_reborrow` | R1a result, R1a non-vacuity | Classical.choice, Quot.sound, propext | `3eb4530cf98efdb466f0fc8509bebb01ee4760687c64d51bf343d261ae0294c5` | `146edacd2b46a4b31858abcc1fd5cfbe901cee0450262d2e95666ab760f414b2` (85) |
| `Toy.Views.Ex.naive_end_breaks_safety_of_nested_shared_reborrow` | R1b result, R1b non-vacuity | Classical.choice, Quot.sound, propext | `26f24bf3cc90698c9337f4bcceb24018008d97635df0e9db2b2deb00e0478ef9` | `bc2d4f963187e5cacaf7f9262a499dd6b134fdb678bcc14624d229c3ae464499` (84) |
| `Toy.Views.Ex.naive_end_safe_without_nested_reborrow` | R1a positive control | Classical.choice, Quot.sound, propext | `25bcd87ee2b28f3176d5490a63a56cb5c983c4b3897f754ea3b21a592e95ffea` | `467fd5172e726c1b545d29fb4bf58c3927371185c3f51930eea1dc20ed9bcc63` (78) |
| `Toy.Views.Ex.naive_end_safe_without_nested_shared_reborrow` | R1b positive control | Classical.choice, Quot.sound, propext | `5995bfdf46aac46d65649f0e9d855bb4d66a452a865f4dceb4f87c25ead5025e` | `a51614c72d7f1a5c9ccb13f0da1d65eaf52ee1047af024f53b7f277956555547` (78) |
| `Toy.Views.Ex.parent_counter_zero_means_no_reader_without_nesting` | R5b positive control | Classical.choice, Quot.sound, propext | `6ebc6deae2bfdb138177eebf511448d13bec26b5540a9c259fb81802af3184fe` | `627a40247cbc5df231a58fd29a6236630ec6a07af267f27e0b0caf98ad7ef9da` (71) |
| `Toy.Views.Ex.returnAuthority_closedViews_nonvacuous` | R3c non-vacuity | Quot.sound, propext | `2be29ec351bca054e5ab982274f88308b1e52cd153035da1310617b0f364c6dd` | `51cf3a30dd47d56a89a8c0777da06345ee2e6a9550be352bc14d38e376ea7b27` (40) |
| `Toy.Views.Ex.returnAuthority_lost_without_activityStable` | R3c counterexample, R3g counterexample, R4a result, R4a non-vacuity | Classical.choice, Quot.sound, propext | `91a0860b22a9ac761be743abf50968d7e925879968823045f505cf9eca5931d4` | `50656b55930f4b3b2ed028acc7bfd2ffa6b93b269239db9854bd0d62990569ec` (81) |
| `Toy.Views.Ex.returnAuthority_lost_without_domainsStable` | R3c counterexample, R3g counterexample, R4a result, R4a non-vacuity | Classical.choice, Quot.sound, propext | `97ab070ddf176b90fd2fd2dc3af7328a82ce0331dfc5b85f708aecd93915e6db` | `25676fb4687258fe5d3df104a8cfe248e975b21557ad7cfe53d198f3d60d61c7` (81) |
| `Toy.Views.Ex.returnAuthority_lost_without_newViewsInactive` | R3c counterexample, R3g counterexample, R4a result, R4a non-vacuity | Classical.choice, Quot.sound, propext | `a9a5e567a22f2a5ed6a52c3d97f2d3425b96e169f9cf1a385d711c8bf3f0ccdc` | `d1685c985bfa6a9c21e135ddcc30f3aaeb8e737c0546da79c134769afadfea7e` (81) |
| `Toy.Views.Ex.returnAuthority_lost_without_parentsExist` | R3c counterexample | Quot.sound, propext | `d6aea2bb42ec15bbbdce81fe5d4e0d2a041a932e6a8741a2e5ac364ad4d83402` | `8f847a662c07960520e13bbb1db9467c4902df227d28c4be1c992dd0fbb39e0d` (40) |
| `Toy.Views.Ex.returnAuthority_lost_without_parentsStable` | R3c counterexample, R3g counterexample, R4a result, R4a non-vacuity | Classical.choice, Quot.sound, propext | `c73a3cbcd88a23f13e02e28438a06eae5bdc35f606699341a16bf744bbdc3e9d` | `5585560a61ce9d5fdb28c58980506584c9141654638419fe414d722f83ebe749` (81) |
| `Toy.Views.Ex.returnAuthority_needed_before_scope` | R3c counterexample, R3g counterexample | Classical.choice, Quot.sound, propext | `e8bc15f71cf811031dc0822214fdf4a05d4aff38e78601b9099685051e1c6539` | `0f8fbe3dd8f2010bae140399827c775482c3a5423c7d3d3d3a0dc4baefd401c4` (77) |
| `Toy.Views.Ex.scopedRun_authority_tightness` | R3h counterexample | Quot.sound, propext | `0e9fa38f11d5dcbe8a92274ea56c86801cd32c1d556107871d2720dc48d339df` | `fbcfe10ae2d70751f0931057cc10c01459d356332b53e14fc99fb1af022be52a` (78) |
| `Toy.Views.Ex.scopedRun_nonvacuous` | R3h non-vacuity | Quot.sound, propext | `6e8bbc35de5570acd7fc0982f00e79f13177de00d3e7d05b9811f45f16397e6a` | `266c275513057f8bc6695377c94ea4e19730b62170b5072ea5ea6f0aef4869d4` (76) |
| `Toy.Views.Ex.scoped_end_needs_local_laws` | R3g counterexample | Classical.choice, Quot.sound, propext | `efade7339a01f22a85de7b02b54e0cf3772e7b1d566dea9f9d99e22115513d25` | `e49fdbf649b71cc5ab6059a36c61ed0d23b012ec9d7c8345eec25279d004dd59` (84) |
| `Toy.Views.Ex.scoped_end_nonvacuous` | R3g non-vacuity | Classical.choice, Quot.sound, propext | `20df5f63f48f8421d257c16341c56a52abbbb821b6807898ffb8cf38c0909148` | `d0625710a9e534eff9990931e51ee1fcc6703426c1c1cdb2367714a0e085dd6f` (78) |
| `Toy.Views.Ex.share_scope_nonvacuous` | R3d non-vacuity | propext | `c1b9b0ebd966c7aa978d58135bb76905980a2bd032e0bfde3192702294ef4e9f` | `5acd8f76e8169ce0d1ccbadc9c59d07a4ff967668ba1afe49067901507a7d7da` (60) |
| `Toy.Views.Ex.writeExclusive_needs_depthCounts` | R2b counterexample | Classical.choice, Quot.sound, propext | `46d8b1a2f120e8da0e9f28eb3fbdad9e004a356c515bbc1ae6061abef137a69d` | `61ff5b10b7fc034a092b3c8e615c61e8362bad590c7b9478d43a8edc341900fc` (53) |
| `Toy.Views.Ex.writeExclusive_needs_exclChildLoaned` | R2b counterexample | Classical.choice, Quot.sound, propext | `d524bf5881d082d623591d801126ee68c1e0659f279e21fe063ea89a19d7f2dc` | `b26c0dee7ee2f0e70e7a12848d78e86ef8217f632f8d68f60d5fe5f93f100e45` (53) |
| `Toy.Views.Ex.writeExclusive_needs_parentCoversActive` | R2b counterexample | Classical.choice, Quot.sound, propext | `fefe6e8941066be05cf1614976a7dd96f960de57fb2f2fee86b7c2349747bf3d` | `8149510d45118f6d6085f1e77199d28bc387ece32cfb3e18a7e583fe7bd538b2` (53) |
| `Toy.Views.Ex.writeExclusive_needs_parentLt` | R2b counterexample | Classical.choice, Quot.sound, propext | `30dc651815811231d572648f0106ddd706500bf8bdba6c8b0592f89de5cf1a59` | `3a65fe8fc94620d91bcc7efb9ad2b350bf0c30da03f5ecfae1218588babb99da` (53) |
| `Toy.Views.Ex.writeExclusive_needs_rootsDisjoint` | R2b counterexample | Classical.choice, Quot.sound, propext | `8b5234db88e71da4bef571ef6aed6af478f127d184bbf975a061318344407a74` | `7f43a0636afbe8b6017ab957ac12183b59317a3013a71f1ca2336ed21305c566` (53) |
| `Toy.Views.Ex.writeExclusive_needs_sharedChildBelowOwn` | R2b counterexample | Classical.choice, Quot.sound, propext | `086fd1f805df1ec06f483bf475d33c0328dc936b33975d1bb51c3766593622af` | `f4004e4eb1ca96a2df4b867a6f65217e21d1d9eee9fe3535fe6c34d75d78966c` (53) |
| `Toy.Views.Ex.writeExclusive_needs_sharedChildrenShared` | R2b counterexample | Classical.choice, Quot.sound, propext | `7b029cd991d3a6fdfe5da32a4ed0a534933b4a2ae5cc96a849c67ad4b888adc5` | `a9b01b161d8e9088d652d51e39b60228907546555de559f86c38e19c6ff12974` (53) |
| `Toy.Views.Ex.write_nonvacuous` | R3f non-vacuity | propext | `5e6aefd0d3db9bd01b7d01d0e971a2af02a5367350efdcca8f1e06713772a1a7` | `e00b6d4d4ac8b2480f27f0961b3d978c8b3a817c83756eadada14d4e0f9cb635` (34) |
| `Toy.Views.canWrite_iff_excl_and_no_active_shared_children_of_depthCounts` | R5a result | Quot.sound, propext | `b315edc13d144f74a912e272efa9e09a7aec10fe4664e71856a8edfbaa990ba0` | `8b27cdae1019f50f9604ca0105184c7abfbb6e273d96ddc796e18f5d8041967f` (44) |
| `Toy.Views.closedViews_of_borrow_scope` | R3d result | Quot.sound, propext | `f2f68de035f3e185d5ae9088cd6544e5a21e19729022f3212ec57b066bde7037` | `d68ae6a856801cf8282a081dbc444e8449e6076c9de4b547db1e2a3475e99807` (59) |
| `Toy.Views.closedViews_of_fresh_scope` | R3d result | Quot.sound, propext | `c642374b93826dd4938f7bb5a06d67c938da3ce22855b6170d7e32f842adbf5f` | `8ef557a8c3b7abed112770e3ec134861ba8ace374b8d15d7a6c001dba4156036` (52) |
| `Toy.Views.closedViews_of_scopedRun` | R3h result | Quot.sound, propext | `dd5e11d8e0d6f0a11b346f175e646ad32a5303c6cea0e922ade83cdedee7cdbb` | `7a220c5bc36aca06eb93c428282f0052d74e8f72f29bc4f6ebcfe98efa42432d` (73) |
| `Toy.Views.closedViews_of_share_scope` | R3d result | Quot.sound, propext | `8bf9bdec184b6b71b82eeb18ac25d3bf376f4aa097e26a6bbe60a5563f1d94e3` | `1bf3854825aa9be4a4a2e727613a9da43351b30694dc1c505a1813a8da5e60e3` (54) |
| `Toy.Views.closedViews_of_write` | R3f result | Quot.sound, propext | `126602f61f85cfbc870ccdf90d19125d0bdbf170ae552da446adb3a45bc414b5` | `d139bd068d36449d831752a850ee6bfb520d16ab57e8a623e26398c016e17610` (40) |
| `Toy.Views.closedViews_refl` | R3a result | propext | `408f44cf505592cd064b6d61b9ccb5a1287ca1cf9e6264f1fe3f954df2c2fced` | `28f47ae075c2aff9be92ae43d5ad69a8f8bb930285c4435d3251f7a70fea6e7a` (28) |
| `Toy.Views.closedViews_trans` | R3a result | Quot.sound, propext | `2f453cda8d871cfef147ff46e7fc304c4b264fa9831b8b3931ef6690a71a3656` | `28f47ae075c2aff9be92ae43d5ad69a8f8bb930285c4435d3251f7a70fea6e7a` (28) |
| `Toy.Views.endRaw_preserves_loanTreeInv_and_noResurrection_of_returnAuthority` | R2a result | Classical.choice, Quot.sound, propext | `9c37f5b244a1c3536f04d7133e2e3a2eb0df20071773b81fa5a2f900650976be` | `141bfab02672757ce6848f549008437a72d209652f259d45afd8e4b5b9956028` (74) |
| `Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_localReturnCheck` | R2d result | Classical.choice, Quot.sound, propext | `b5e427105ff55f857d1d734fd34c6041483aa26bafe5f3ce6111d6f05e6bed00` | `bf018f4c3c772ba689946865aed5e9ab164bce3939dff2e09f3d9e0c9cb99af3` (72) |
| `Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority` | R2a result | Classical.choice, Quot.sound, propext | `833e47ce352e5a497915b820ebcce32014b7983144fb8fb2d4ff96e5c305a4ef` | `248541f0894c65d3854152c1b2700c8d95b12ec3026105c4c9a51589e493a512` (72) |
| `Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority_before_closedViews` | R3g result | Classical.choice, Quot.sound, propext | `ce2ae3088d43c55736f4eec508d102cb052858a6a4370e1ceb68aa0e55c08dc9` | `ee1e3e6f8a36e5ede235ba61731692fd287d508ca7ccb51fd5ae6e0d624c5704` (79) |
| `Toy.Views.endRaw_writeExclusive_of_loanTree_laws_of_returnAuthority` | R2c result | Classical.choice, Quot.sound, propext | `365e87388ca8f4994705e7116666f81a3994ff50c284645f0c8e790c274aec16` | `0ccd20bff9c99ee3371103ee1b9a6ccc84dd37508a51e6e4db1139f828e69d76` (71) |
| `Toy.Views.returnAuthority_of_closedViews_of_parentCoversActive` | R3c result | Quot.sound, propext | `932b5bd1cc921907a8a692cffa11e05a31b6658b269b5d1d14ba9df6113eb6fc` | `bbc96c93b71104a016d82c167458d03abf6a6e0a68a6b7f82a08b96f749b67f6` (37) |
| `Toy.Views.returnAuthority_of_closedViews_of_parentsExist` | R3c result | Quot.sound, propext | `2625e3c06c482b7440d326f7d572cfce0bbbbfe370310885f6e6cd7608b9898b` | `68b6a84076528e2968686de39798d1e736f32c84c5ec4b7f87ef72074be91fc8` (36) |
| `Toy.Views.returnAuthority_of_localReturnCheck_of_parentCoversActive_exclChildLoaned_depthCounts` | R2d result | Classical.choice, Quot.sound, propext | `256c3aa97c9254113cb2b2e947c9933b260bf9e199eff44030678da153ded21f` | `e8eff113f1c71758c0954778d100958cc05ebf164bfbe772b21cb660269e3e31` (50) |
| `Toy.Views.returnAuthority_of_scopedRun_of_parentCoversActive` | R3h result | Quot.sound, propext | `d9f1e4580aa5dc3a2d8300ffad10d20d1b4a0a09ba6f0c6428371fc3bf860978` | `41c9eb38216f62cfe1316d52fc3d9fc2a288aa438b83647d60e9a1099f09f2e7` (74) |
| `Toy.Views.writeExclusive_of_loanTree_laws` | R2b result | Classical.choice, Quot.sound, propext | `bd1582367dfae0053c2cba4f556acaced58568dbc673e0d1d0c21239d5a9fe8b` | `0e79d7d67638b4085f3944bb0d39415f7ee97ea09e9e7a955cb531ea86f080bc` (52) |

All 528 declarations of the `ToyViews` library (recorded in `audit/axioms.json`) depend on at most: Classical.choice, Quot.sound, propext.

### Primary sources

Bibliographic identity (title, authors, venue, volume/issue, pages, year) of every DOI below was
re-verified against Crossref, and of every arXiv identifier against arXiv, on 2026-11-20. Section,
figure and page characterizations quoted in the cards were checked against open-access copies of
the papers on 2026-11-20; where a card says a paper body or artifact was not inspected, that
limitation stands.

- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer. *RustBelt: Securing the Foundations of the Rust
  Programming Language.* Proc. ACM Program. Lang. 2(POPL), Article 66, 34 pp., 2018.
  doi:10.1145/3158154. (Mechanization cited in cards: https://gitlab.mpi-sws.org/iris/lambda-rust,
  directory `lifetime/`.)
- R. Jung, H.-H. Dang, J. Kang, D. Dreyer. *Stacked Borrows: An Aliasing Model for Rust.* Proc. ACM
  Program. Lang. 4(POPL), 32 pp., 2020. doi:10.1145/3371109.
- N. Villani, J. Hostert, D. Dreyer, R. Jung. *Tree Borrows.* Proc. ACM Program. Lang. 9(PLDI),
  pp. 1019–1042, 2025. doi:10.1145/3735592. (Related sources cited in cards: the Rocq development
  https://gitlab.mpi-sws.org/iris/simuliris, directory `theories/tree_borrows`; R. Jung, "From
  Stacks to Trees: A new aliasing model for Rust", https://ralfj.de/blog/2023/06/02/tree-borrows.html.)
- S. Ho, J. Protzenko. *Aeneas: Rust Verification by Functional Translation.* Proc. ACM Program.
  Lang. 6(ICFP), pp. 711–741, 2022. doi:10.1145/3547647; arXiv:2206.07185.
- S. Ho, A. Fromherz, J. Protzenko. *Sound Borrow-Checking for Rust via Symbolic Semantics.* Proc.
  ACM Program. Lang. 8(ICFP), pp. 426–454, 2024. doi:10.1145/3674640; arXiv:2404.02680 (long
  version).
- Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer. *RustHornBelt: A Semantic Foundation for
  Functional Verification of Rust Programs with Unsafe Code.* PLDI 2022, pp. 841–856.
  doi:10.1145/3519939.3523704.
- L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer. *RefinedRust: A Type System for
  High-Assurance Verification of Rust Programs.* Proc. ACM Program. Lang. 8(PLDI), pp. 1115–1139,
  2024. doi:10.1145/3656422.
- D. J. Pearce. *A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust.* ACM Trans.
  Program. Lang. Syst. 43(1), 73 pp., 2021. doi:10.1145/3443420.
- A. Weiss, O. Gierczak, D. Patterson, A. Ahmed. *Oxide: The Essence of Rust.* arXiv:1903.00982
  (v4, 2021).
- R. Bornat, C. Calcagno, P. O'Hearn, M. Parkinson. *Permission Accounting in Separation Logic.*
  POPL 2005, pp. 259–270. doi:10.1145/1040305.1040327.
- J. Boyland. *Checking Interference with Fractional Permissions.* Static Analysis (SAS 2003),
  LNCS, pp. 55–72. doi:10.1007/3-540-44898-5_4.
- R. Dockins, A. Hobor, A. W. Appel. *A Fresh Look at Separation Algebras and Share Accounting.*
  APLAS 2009, LNCS, pp. 161–177. doi:10.1007/978-3-642-10672-9_13.

Motivation only, not a subject (unmerged): AeneasVerif/aeneas pull request #1497, head commit
`d17ca83fc07d712d1785f650840cb2073c259e69`, commit authors fournet, Cezar Andrici, Son Ho (GitHub
API, 2026-11-20); files read at that commit: `backends/lean/Aeneas/Std/Heap/{Model,Repr,Allocation,ScopedView}.lean`,
`backends/lean/Aeneas/Std/Heap/README.md`, `backends/lean/Aeneas/Std/HeapTests.lean`. See
*Modeling bridge*.

## Revalidation

Requirements: `elan` (so that `lake` and `lean` resolve to the toolchain pinned in
`lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3` (standard library only). Nothing
else is needed: the Lean project has no dependencies.

**Primary check (one command, from the package directory):**

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, scans
every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations, runs an audit
program that computes `Lean.collectAxioms` for every declaration of the `ToyViews` library and the
statement and definition-closure texts of every Lean name referenced by `results.json`, and
compares their SHA-256 hashes with `audit/statements.json` (exactly what is hashed is described
under **Evidence**, *What is hashed*, and in the script's docstring). It prints `REVALIDATED` and
exits with status 0 iff the build succeeds, no banned token occurs, every declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`, and every recorded hash matches.

**The same check by hand** (from the package directory; uses the package-included audit program
`lean/RevalidationAudit.lean`, which is outside the library target):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/scoped-views-audit.out
cd ..
python3 - /tmp/scoped-views-audit.out <<'EOF'
import hashlib, json, re, sys
out = open(sys.argv[1]).read()
audit = json.loads(re.search(r"AUDIT_JSON (\{.*\})", out).group(1))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = [d["name"] for d in audit["decls"] if set(d["axioms"]) - allowed]
recorded = json.load(open("audit/statements.json"))["statements"]
mismatch = []
for s in audit["stmts"]:
    got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
           "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
           "closure_size": len(s["closure"])}
    if s.get("missing") or recorded.get(s["name"]) != got:
        mismatch.append(s["name"])
print(len(audit["decls"]), "declarations; non-standard axioms:", bad or "none")
print(len(audit["stmts"]), "statements; hash mismatches:", mismatch or "none")
EOF
```

Expected output on this package: `528 declarations; non-standard axioms: none` and
`75 statements; hash mismatches: none`. To inspect the axioms of a single theorem interactively,
add for example `#print axioms Toy.Views.writeExclusive_of_loanTree_laws` to a file that does
`import ToyViews` and run it with `lake env lean` from `lean/`.

**What revalidation does and does not establish.** A passing run re-establishes that every theorem
listed under **Evidence** is kernel-checked with standard axioms, and that the statements and the
definitions they depend on are byte-for-byte the recorded ones. It does not re-check the modeling
bridge, the prior-art characterizations, or the bounded search; to re-run the latter, use
`python3 support/finite_search/reach.py` (a few seconds) and compare with the output recorded under
*Supporting bounded search*. After a change to a definition, the closure hash of every statement
that depends on it changes, and the affected cards must be re-examined.
