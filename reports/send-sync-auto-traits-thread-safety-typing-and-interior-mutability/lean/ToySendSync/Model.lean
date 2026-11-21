/-!
# A toy capability model of `Send` and `Sync`

This file defines a small, Mathlib-free model of thread-safety typing with
shared references and interior mutability.

* A value of a type `T` is described by three finite lists of *capability events*
  (`Fp`): what an owner of a `T` can do (`own`), what a holder of a shared
  reference `&T` can do (`shr`), and what *another* party may still be able to do
  concurrently over locations reachable from the value (`alias`): clones of a
  shared allocation, the lender of a borrow, other lockers of a borrowed mutex.
* Locations are paths in the type tree of the value under consideration.
* Two threads are modelled: the origin thread (`Tid.origin`), which created the
  value, and another thread (`Tid.other`).
* A data race (`Race`) is a pair of conflicting memory accesses (same location,
  at least one write, not both atomic), one per thread, that are simultaneously
  enabled in some synchronization snapshot (`Snap`): a lock is held by at most
  one holder, and a uniquely held counted allocation has no handle on the other
  thread.
* `SemSend T` : transferring a `T` to the other thread cannot produce a data race
  with what the origin thread retains, and does not make the other thread release
  a lock acquisition that it did not make (`NoForeignRelease`).
* `SemSync T` : sharing `&T` with the other thread cannot produce a data race, and
  does not let the other thread release a lock acquisition that it did not make.
* `autoCheck` : a structural checker in the style of auto traits, parameterized
  by an impl table for the library primitives.

These are definitions of a toy model; they are not definitions of Rust's traits.
-/

namespace Toy.SendSync

/-- Locations and lock/allocation identities are paths in the type tree. -/
abbrev Path := List Nat

/-- The two threads of the model: the thread that created the value under
consideration, and another thread that receives it or a shared reference to it. -/
inductive Tid where
  | origin
  | other
  deriving DecidableEq, Repr

/-- The other thread of the two. -/
def Tid.flip : Tid → Tid
  | .origin => .other
  | .other => .origin

/-- Lock acquisitions: `fresh` is an acquisition made by the executing thread itself
(locking a mutex through a shared reference, or registering a mutable borrow in the
borrow flag of a `refCell`); `guard g` is the acquisition owned by the guard value at
path `g`, which was made by the thread that created that guard. -/
inductive Acq where
  | fresh
  | guard (g : Path)
  deriving DecidableEq, Repr

/-- Preconditions under which an event can execute.
* `held lk a` : the lock at path `lk` is held by acquisition `a`.
* `via p` : the executing thread holds a handle to the counted allocation at `p`.
* `uniq p` : the executing thread holds a handle to the counted allocation at `p`
  and the other thread holds none. -/
inductive Claim where
  | held (lk : Path) (a : Acq)
  | via (alloc : Path)
  | uniq (alloc : Path)
  deriving DecidableEq, Repr

/-- The path a claim constrains. -/
def Claim.path : Claim → Path
  | .held p _ => p
  | .via p => p
  | .uniq p => p

/-- Event kinds: non-atomic read, non-atomic write, atomic read-modify-write, and
release of a lock acquisition (not a memory access). -/
inductive Kind where
  | rd
  | wr
  | atomic
  | rel
  deriving DecidableEq, Repr

/-- Memory accesses are all kinds except `rel`. -/
def Kind.isAccess : Kind → Bool
  | .rel => false
  | _ => true

/-- Writes: non-atomic writes and atomic read-modify-writes. -/
def Kind.isWrite : Kind → Bool
  | .wr => true
  | .atomic => true
  | _ => false

/-- Atomic accesses. -/
def Kind.isAtomic : Kind → Bool
  | .atomic => true
  | _ => false

/-- Non-atomic reads (the only kind a read-only view exposes). -/
def Kind.isRead : Kind → Bool
  | .rd => true
  | _ => false

/-- A capability event: an access (or a release) at a location, with the claims
that must hold when it executes. -/
structure Ev where
  kind : Kind
  loc : Path
  claims : List Claim
  deriving DecidableEq, Repr

/-- A claim that a lock is held by an acquisition the executing thread made itself. -/
def Claim.isFresh : Claim → Bool
  | .held _ .fresh => true
  | _ => false

/-- The event runs under a lock acquisition made by the executing thread itself (it has a
`held _ .fresh` claim). Making that acquisition writes lock state: locking a mutex, or
registering a mutable borrow in a `refCell`'s borrow flag. -/
def Ev.acquires (e : Ev) : Bool := e.claims.any Claim.isFresh

/-- Lock holders in a snapshot. -/
inductive Holder where
  | thread (t : Tid)
  | guard (g : Path)
  deriving DecidableEq, Repr

/-- A synchronization snapshot: the holder of each lock (at most one, since `lock`
is a function) and, for each counted allocation, which threads hold a handle to it.
Every snapshot is treated as reachable. The package has no execution semantics, so
no relation between snapshots and the states of real executions is established. -/
structure Snap where
  lock : Path → Option Holder
  holds : Path → Tid → Bool

/-- The holder that an acquisition denotes when used by thread `t`. -/
def Acq.holder (t : Tid) : Acq → Holder
  | .fresh => .thread t
  | .guard g => .guard g

/-- Satisfaction of a claim by thread `t` in snapshot `σ`. -/
def Sat (σ : Snap) (t : Tid) : Claim → Prop
  | .held p a => σ.lock p = some (a.holder t)
  | .via p => σ.holds p t = true
  | .uniq p => σ.holds p t = true ∧ σ.holds p t.flip = false

/-- All claims of a list are satisfied by thread `t` in `σ`. -/
def SatAll (σ : Snap) (t : Tid) (cs : List Claim) : Prop := ∀ c ∈ cs, Sat σ t c

/-- Claims `cs₁` (of the other thread) and `cs₂` (of the origin thread) can hold
in one snapshot. -/
def Compatible (cs₁ cs₂ : List Claim) : Prop :=
  ∃ σ : Snap, SatAll σ .other cs₁ ∧ SatAll σ .origin cs₂

/-- Event `e₁` of the other thread and event `e₂` of the origin thread can be
enabled at the same time. -/
def Concurrent (e₁ e₂ : Ev) : Prop := Compatible e₁.claims e₂.claims

/-- Two events conflict: same location, both memory accesses, at least one write,
not both atomic. -/
def Conflicting (e₁ e₂ : Ev) : Prop :=
  e₁.loc = e₂.loc ∧ e₁.kind.isAccess = true ∧ e₂.kind.isAccess = true ∧
    (e₁.kind.isWrite = true ∨ e₂.kind.isWrite = true) ∧
    ¬ (e₁.kind.isAtomic = true ∧ e₂.kind.isAtomic = true)

instance (e₁ e₂ : Ev) : Decidable (Conflicting e₁ e₂) := by
  unfold Conflicting; infer_instance

/-- A data race between capability list `B` (executed by the other thread) and
capability list `A` (executed by the origin thread): a conflicting pair that is
simultaneously enabled in some snapshot. -/
def Race (B A : List Ev) : Prop :=
  ∃ e₁ ∈ B, ∃ e₂ ∈ A, Conflicting e₁ e₂ ∧ Concurrent e₁ e₂

/-- The thread that made an acquisition, seen from the executing thread `t`: a
`fresh` acquisition was made by `t` itself; the acquisition owned by a guard was made
by the thread that created the guard, which in both transfer scenarios (the value and
everything reachable from it were created by the origin thread) is `Tid.origin`. -/
def Acq.maker (t : Tid) : Acq → Tid
  | .fresh => t
  | .guard _ => .origin

/-- Release affinity: every release event of the list, executed by thread `t`,
releases only acquisitions that `t` made. A release event at location `l` releases
the acquisition `a` named by its claim `held l a` (the lock at the event's own
location); other claims of the event are preconditions. -/
def NoForeignRelease (t : Tid) (es : List Ev) : Prop :=
  ∀ e ∈ es, ∀ a : Acq, e.kind = .rel → Claim.held e.loc a ∈ e.claims → a.maker t = t

/-- Every release event of the list names the acquisition it releases: it carries a claim
`held l a` on its own location `l`. `NoForeignRelease` constrains only the acquisitions so
named, so it accepts a release event without such a claim. -/
def RelNamesAcq (es : List Ev) : Prop :=
  ∀ e ∈ es, e.kind = .rel → ∃ a : Acq, Claim.held e.loc a ∈ e.claims

/-! ## Relocation into a child position -/

/-- Relocate a lock holder into child `i`. -/
def Holder.reloc (i : Nat) : Holder → Holder
  | .thread t => .thread t
  | .guard g => .guard (i :: g)

/-- Relocate an acquisition into child `i`. -/
def Acq.reloc (i : Nat) : Acq → Acq
  | .fresh => .fresh
  | .guard g => .guard (i :: g)

/-- Relocate a claim into child `i`. -/
def Claim.reloc (i : Nat) : Claim → Claim
  | .held p a => .held (i :: p) (a.reloc i)
  | .via p => .via (i :: p)
  | .uniq p => .uniq (i :: p)

/-- Place an event of a child at position `i` of its parent, adding the parent's
root claims `r`. -/
def Ev.place (r : List Claim) (i : Nat) (e : Ev) : Ev :=
  { kind := e.kind, loc := i :: e.loc, claims := r ++ e.claims.map (Claim.reloc i) }

/-- Place a list of child events at position `i`, adding root claims `r`. -/
def place (r : List Claim) (i : Nat) (es : List Ev) : List Ev := es.map (Ev.place r i)

/-- An event at the root location of a node. -/
def rootEv (k : Kind) (cs : List Claim := []) : Ev := ⟨k, [], cs⟩

/-! ## Types and their capability footprints -/

/-- What a user wrapper exposes through a shared reference: the whole shared
capability of its field, its non-atomic reads, or nothing. The view filters the
field's shared capability list event by event: `readOnly` exposes exactly the `rd`
events that do not run under a lock acquisition made by the executing thread
(`Ev.acquires`); it exposes no write, atomic read-modify-write or release, and no access
that first requires locking a mutex or registering a mutable borrow in a `refCell`'s
borrow flag, since both write lock state. It models an API whose every operation
performs reads only; an API operation that reads data but also writes metadata (such
as `RefCell::borrow`, which updates the borrow flag) is not a read-only operation in
this sense. -/
inductive View where
  | full
  | readOnly
  | none
  deriving DecidableEq, Repr

/-- The events a view exposes. -/
def View.expose : View → List Ev → List Ev
  | .full, es => es
  | .readOnly, es => es.filter (fun e => e.kind.isRead && !e.acquires)
  | .none, _ => []

/-- Toy types. `plain`: owned plain data (an integer). `cell`, `refCell`: non-atomic
interior mutability. `rc`: non-atomically counted shared allocation. `arc`:
atomically counted shared allocation. `mutex`: a lock owning its content. `guard`:
a held lock acquisition borrowing a mutex. `box`, `ref`, `refMut`, `prod`, `sum`:
structural constructors. `wrap f v u`: a user type with one field `f` whose shared
API exposes `v`, with `u = true` when its author wrote an unsafe `Sync` impl. -/
inductive Ty where
  | plain
  | cell (t : Ty)
  | refCell (t : Ty)
  | rc (t : Ty)
  | arc (t : Ty)
  | mutex (t : Ty)
  | guard (t : Ty)
  | box (t : Ty)
  | ref (t : Ty)
  | refMut (t : Ty)
  | prod (a b : Ty)
  | sum (a b : Ty)
  | wrap (f : Ty) (v : View) (unsafeSync : Bool)
  deriving DecidableEq, Repr

/-- A capability footprint: owner capabilities, shared-reference capabilities, and
the capabilities another party may retain concurrently over reachable locations. -/
structure Fp where
  own : List Ev
  shr : List Ev
  alias : List Ev
  deriving Repr

/-- The capability footprint of a type, with locations relative to the value.
Child positions: content of `cell`/`refCell`/`rc`/`arc`/`mutex`/`guard` at `0`;
components of `prod`/`sum` at `0` and `1`. The root location `[]` is the cell's
storage, the `refCell` borrow flag, the `rc`/`arc` count, or the lock (`mutex`, and the
borrowed mutex of a `guard`). `box`, `ref`, `refMut`, `wrap` add no location.
A shared reference to a `cell` reaches the owner capabilities of its content
(`Cell::get` copies the content out, `Cell::replace`/`set`/`take` move it out or drop
it). A shared reference to a `refCell` reads and writes the borrow flag, reaches the
shared capabilities of its content through a shared borrow (`RefCell::borrow`, or the
unsafe `RefCell::try_borrow_unguarded`, which reads the flag without updating it), and
reaches the owner capabilities of its content under a mutable borrow registered in the
flag (claim `held [] .fresh`: `RefCell::borrow_mut`, and `replace`, `replace_with`,
`swap`, `take`, which borrow mutably); the owner of a `refCell` also reaches the owner
capabilities of its content without the flag (`RefCell::get_mut`, `into_inner`). A
thread that locks a `mutex` through a shared reference also releases that acquisition
(`rel` with a `fresh` claim). -/
def fp : Ty → Fp
  | .plain => ⟨[rootEv .rd, rootEv .wr], [rootEv .rd], []⟩
  | .cell t =>
    let c := fp t
    let s := [rootEv .rd, rootEv .wr] ++ place [] 0 c.own
    ⟨s, s, place [] 0 c.alias⟩
  | .refCell t =>
    let c := fp t
    let s := [rootEv .rd, rootEv .wr] ++ place [] 0 c.shr ++ place [.held [] .fresh] 0 c.own
    ⟨place [] 0 c.own ++ s, s, place [] 0 c.alias⟩
  | .rc t =>
    let c := fp t
    let h := [rootEv .rd [.via []], rootEv .wr [.via []]] ++ place [.via []] 0 c.shr ++
      place [.uniq []] 0 c.own
    ⟨h, h, h ++ place [] 0 c.alias⟩
  | .arc t =>
    let c := fp t
    let h := [rootEv .atomic [.via []]] ++ place [.via []] 0 c.shr ++ place [.uniq []] 0 c.own
    ⟨h, h, h ++ place [] 0 c.alias⟩
  | .mutex t =>
    let c := fp t
    let s := place [.held [] .fresh] 0 c.own ++ [rootEv .rel [.held [] .fresh]]
    ⟨place [] 0 c.own ++ s, s, place [] 0 c.alias⟩
  | .guard t =>
    let c := fp t
    ⟨place [.held [] (.guard [])] 0 c.own ++ [rootEv .rel [.held [] (.guard [])]],
      place [.held [] (.guard [])] 0 c.shr,
      place [.held [] .fresh] 0 c.own ++ place [] 0 c.alias⟩
  | .box t => fp t
  | .ref t =>
    let c := fp t
    ⟨c.shr, c.shr, c.shr ++ c.alias⟩
  | .refMut t => fp t
  | .prod a b =>
    let x := fp a
    let y := fp b
    ⟨place [] 0 x.own ++ place [] 1 y.own, place [] 0 x.shr ++ place [] 1 y.shr,
      place [] 0 x.alias ++ place [] 1 y.alias⟩
  | .sum a b =>
    let x := fp a
    let y := fp b
    ⟨place [] 0 x.own ++ place [] 1 y.own, place [] 0 x.shr ++ place [] 1 y.shr,
      place [] 0 x.alias ++ place [] 1 y.alias⟩
  | .wrap f v _ =>
    let c := fp f
    ⟨c.own, v.expose c.shr, c.alias⟩

/-! ## Semantic predicates -/

/-- Semantic `Send`: transferring a `T` from the origin thread to the other thread,
while the origin thread keeps the alias capabilities, admits no data race, and no
capability of the transferred value makes the other thread release an acquisition it
did not make. -/
def SemSend (T : Ty) : Prop :=
  ¬ Race (fp T).own (fp T).alias ∧ NoForeignRelease .other (fp T).own

/-- Semantic `Sync`: giving the other thread a shared reference to a `T`, while the
origin thread keeps shared capabilities and alias capabilities, admits no data race,
and no shared capability makes the other thread release an acquisition it did not
make. -/
def SemSync (T : Ty) : Prop :=
  ¬ Race (fp T).shr ((fp T).shr ++ (fp T).alias) ∧ NoForeignRelease .other (fp T).shr

/-! ## The auto-trait checker -/

/-- Library primitives whose `Send`/`Sync` come from an impl table. -/
inductive Prim where
  | cell
  | refCell
  | rc
  | arc
  | mutex
  | guard
  deriving DecidableEq, Repr

/-- The type built by a primitive from its argument. -/
def Prim.apply : Prim → Ty → Ty
  | .cell, t => .cell t
  | .refCell, t => .refCell t
  | .rc, t => .rc t
  | .arc, t => .arc t
  | .mutex, t => .mutex t
  | .guard, t => .guard t

/-- An impl-table rule: `allowed = false` is a negative impl; otherwise the impl
holds when the argument has the required traits. -/
structure Rule where
  allowed : Bool
  needSend : Bool
  needSync : Bool
  deriving DecidableEq, Repr

/-- Evaluate a rule on the argument's checker verdicts. -/
def Rule.eval (r : Rule) (s y : Bool) : Bool :=
  r.allowed && (!r.needSend || s) && (!r.needSync || y)

/-- A rule's condition on propositions about the argument. -/
def Rule.Holds (r : Rule) (s y : Prop) : Prop :=
  r.allowed = true ∧ (r.needSend = true → s) ∧ (r.needSync = true → y)

/-- An impl table for the primitives. -/
structure Table where
  send : Prim → Rule
  sync : Prim → Rule

/-- The table mirroring the standard library's impls (as documented):
`Cell`/`RefCell`: `Send` if `T: Send`, never `Sync`; `Rc`: neither;
`Arc`: both if `T: Send + Sync`; `Mutex`: both if `T: Send`;
`MutexGuard`: never `Send`, `Sync` if `T: Sync`. -/
def stdTable : Table where
  send
    | .cell => ⟨true, true, false⟩
    | .refCell => ⟨true, true, false⟩
    | .rc => ⟨false, false, false⟩
    | .arc => ⟨true, true, true⟩
    | .mutex => ⟨true, true, false⟩
    | .guard => ⟨false, false, false⟩
  sync
    | .cell => ⟨false, false, false⟩
    | .refCell => ⟨false, false, false⟩
    | .rc => ⟨false, false, false⟩
    | .arc => ⟨true, true, true⟩
    | .mutex => ⟨true, true, false⟩
    | .guard => ⟨true, false, true⟩

/-- The checker verdicts `(send, sync)`: fixed rules for `plain`, `&T` and `&mut T`,
the table for primitives, conjunction over components for `box`/`prod`/`sum`, and for
a wrapper the field's verdicts, with `sync` forced by an unsafe impl. -/
def autoCheck (tb : Table) : Ty → Bool × Bool
  | .plain => (true, true)
  | .cell t =>
    let r := autoCheck tb t
    ((tb.send .cell).eval r.1 r.2, (tb.sync .cell).eval r.1 r.2)
  | .refCell t =>
    let r := autoCheck tb t
    ((tb.send .refCell).eval r.1 r.2, (tb.sync .refCell).eval r.1 r.2)
  | .rc t =>
    let r := autoCheck tb t
    ((tb.send .rc).eval r.1 r.2, (tb.sync .rc).eval r.1 r.2)
  | .arc t =>
    let r := autoCheck tb t
    ((tb.send .arc).eval r.1 r.2, (tb.sync .arc).eval r.1 r.2)
  | .mutex t =>
    let r := autoCheck tb t
    ((tb.send .mutex).eval r.1 r.2, (tb.sync .mutex).eval r.1 r.2)
  | .guard t =>
    let r := autoCheck tb t
    ((tb.send .guard).eval r.1 r.2, (tb.sync .guard).eval r.1 r.2)
  | .box t => autoCheck tb t
  | .ref t => ((autoCheck tb t).2, (autoCheck tb t).2)
  | .refMut t => autoCheck tb t
  | .prod a b =>
    ((autoCheck tb a).1 && (autoCheck tb b).1, (autoCheck tb a).2 && (autoCheck tb b).2)
  | .sum a b =>
    ((autoCheck tb a).1 && (autoCheck tb b).1, (autoCheck tb a).2 && (autoCheck tb b).2)
  | .wrap f _ u => ((autoCheck tb f).1, u || (autoCheck tb f).2)

/-- Soundness of an impl table relative to the semantics: whenever a rule's
condition holds of the argument's semantic properties, the primitive type has the
semantic property. -/
def TableSound (tb : Table) : Prop :=
  ∀ (p : Prim) (U : Ty),
    ((tb.send p).Holds (SemSend U) (SemSync U) → SemSend (p.apply U)) ∧
    ((tb.sync p).Holds (SemSend U) (SemSync U) → SemSync (p.apply U))

/-- Every unsafe `Sync` impl on a wrapper node inside `T` is semantically justified. -/
def ImplsSound : Ty → Prop
  | .plain => True
  | .cell t => ImplsSound t
  | .refCell t => ImplsSound t
  | .rc t => ImplsSound t
  | .arc t => ImplsSound t
  | .mutex t => ImplsSound t
  | .guard t => ImplsSound t
  | .box t => ImplsSound t
  | .ref t => ImplsSound t
  | .refMut t => ImplsSound t
  | .prod a b => ImplsSound a ∧ ImplsSound b
  | .sum a b => ImplsSound a ∧ ImplsSound b
  | .wrap f v u => (u = true → SemSync (.wrap f v u)) ∧ ImplsSound f

/-- `T` contains no user wrapper. -/
def WrapFree : Ty → Prop
  | .plain => True
  | .cell t => WrapFree t
  | .refCell t => WrapFree t
  | .rc t => WrapFree t
  | .arc t => WrapFree t
  | .mutex t => WrapFree t
  | .guard t => WrapFree t
  | .box t => WrapFree t
  | .ref t => WrapFree t
  | .refMut t => WrapFree t
  | .prod a b => WrapFree a ∧ WrapFree b
  | .sum a b => WrapFree a ∧ WrapFree b
  | .wrap _ _ _ => False

/-- The proof obligation of an unsafe `Sync` impl on `wrap f v u`, as an explicit
invariant: every conflicting pair formed by an exposed shared capability (other
thread) and an exposed shared capability or an alias capability of the field (origin
thread) is never simultaneously enabled, and no exposed capability makes the other
thread release an acquisition it did not make. -/
def SyncObligation (f : Ty) (v : View) : Prop :=
  (∀ e₁ ∈ v.expose (fp f).shr, ∀ e₂ ∈ v.expose (fp f).shr ++ (fp f).alias,
      Conflicting e₁ e₂ → ¬ Concurrent e₁ e₂) ∧
    NoForeignRelease .other (v.expose (fp f).shr)

/-- Reads through the owner capabilities of `U` that a read-only view keeps (`rd` events
that need no acquisition by the executing thread), executed by the other thread, race
with no alias capability of `U` (executed by the origin thread). This is the condition
on the content of a `Cell<U>` under a read-only wrapper: a shared reference to the cell
reaches the owner capabilities of the content. -/
def OwnReadsRaceFree (U : Ty) : Prop :=
  ¬ Race (View.expose .readOnly (fp U).own) (fp U).alias

/-- Reads through the shared capabilities of `U` that a read-only view keeps, executed by
the other thread, race with no alias capability of `U` (executed by the origin thread).
This is the condition on the content of a `RefCell<U>` under a read-only wrapper: without
writing the borrow flag, a shared reference to the `refCell` reaches the shared
capabilities of the content (as `RefCell::try_borrow_unguarded` does). -/
def ShrReadsRaceFree (U : Ty) : Prop :=
  ¬ Race (View.expose .readOnly (fp U).shr) (fp U).alias

end Toy.SendSync
