/-!
# Double fetches against a concurrent writer: the toy model

A parser reads a shared byte region while an arbitrary concurrent writer may change it.

* `Region n` is the shared region: `n` bytes.
* `Adversary n` is the writer, given as the region state at each time step. The parser's `k`-th
  memory access (counting from `0`) observes the state `adv k`.
* `Prog n α` is a parser: a finite decision tree whose internal nodes either read one byte
  (`read`), possibly at an address computed from earlier reads, or copy the whole region in one
  atomic step (`snap`). Leaves return a value of type `α`.
* `Prog.exec` runs a parser against a writer; `Prog.eval` runs it on a region that nobody else
  writes (private memory); `Prog.obs` records every memory access as an observable event.
* Byte reads and snapshots are atomic, and the clock advances by one per access. Copying a region
  one byte at a time (`byteCopy`) is therefore not atomic; `snap` is an idealized atomic copy.

Robustness notions, each quantified over every adversary:

* `RSafe safe p`: every result satisfies the safety predicate `safe`.
* `RValid spec p`: every result equals `spec s'` for some byte vector `s'`.
* `RState spec p`: every result equals `spec (adv t)` for some time `t`, i.e. for a region state the
  writer actually produced.

All definitions are in the namespace `Toy.DoubleFetch`. They model the shape of the problem and are
not a model of any real memory system, compiler, or language.
-/

namespace Toy.DoubleFetch

/-- A byte: one of 256 values. -/
abbrev Byte := Fin 256

/-- The shared region: `n` addressable bytes. -/
abbrev Region (n : Nat) := Fin n → Byte

/-- A concurrent writer, given by the region state at each time step: the parser's `k`-th memory
access (counting from `0`) observes `adv k`. No constraint is placed on how the states change. -/
abbrev Adversary (n : Nat) := Nat → Region n

/-- The writer that never writes: the region stays `s` forever. -/
def Adversary.const {n : Nat} (s : Region n) : Adversary n := fun _ => s

/-- A parser over an `n`-byte region with results in `α`: a finite decision tree.

* `ret a` returns `a`.
* `read i k` reads the byte at address `i` (one memory access) and continues with `k b`, where `b`
  is the byte read. The continuation may choose later addresses from earlier bytes.
* `snap k` copies all `n` bytes in one atomic memory access and continues with `k s`, where `s` is
  the copied region. -/
inductive Prog (n : Nat) (α : Type) : Type where
  | ret : α → Prog n α
  | read : Fin n → (Byte → Prog n α) → Prog n α
  | snap : (Region n → Prog n α) → Prog n α

namespace Prog

variable {n : Nat} {α : Type}

/-- Run `p` against the writer `adv`, starting at time `t`: each memory access observes the state
at the current time, and the clock advances by one after every access. -/
def execFrom : Prog n α → Adversary n → Nat → α
  | ret a, _, _ => a
  | read i k, adv, t => (k (adv t i)).execFrom adv (t + 1)
  | snap k, adv, t => (k (adv t)).execFrom adv (t + 1)

/-- Run `p` against the writer `adv`, starting at time `0`. -/
def exec (p : Prog n α) (adv : Adversary n) : α := p.execFrom adv 0

/-- Private-memory semantics: run `p` on the region `s`, which nobody else writes. -/
def eval : Prog n α → Region n → α
  | ret a, _ => a
  | read i k, s => (k (s i)).eval s
  | snap k, s => (k s).eval s

end Prog

/-- An observable memory event: a one-byte read (address and byte) or an atomic snapshot. -/
inductive Event (n : Nat) : Type where
  | rd : Fin n → Byte → Event n
  | sn : Region n → Event n

namespace Prog

variable {n : Nat} {α : Type}

/-- Observable-read semantics, starting at time `t`: the list of memory events (every read is an
event, as for volatile or atomic accesses) together with the result. -/
def obsFrom : Prog n α → Adversary n → Nat → List (Event n) × α
  | ret a, _, _ => ([], a)
  | read i k, adv, t =>
      let r := (k (adv t i)).obsFrom adv (t + 1)
      (Event.rd i (adv t i) :: r.1, r.2)
  | snap k, adv, t =>
      let r := (k (adv t)).obsFrom adv (t + 1)
      (Event.sn (adv t) :: r.1, r.2)

/-- Observable-read semantics from time `0`. -/
def obs (p : Prog n α) (adv : Adversary n) : List (Event n) × α := p.obsFrom adv 0

/-- `p.SingleReadFrom vis`: on every root-to-leaf path, `p` reads each address at most once,
given that the addresses marked `true` in `vis` were already read. A `snap` reads every address,
so on a nonempty region (`0 < n`) it requires that nothing has been read yet, and nothing may be
read after it. On the empty region (`n = 0`) a `snap` reads no address, so repeated snapshots are
allowed (`singleRead_zero_double_snap`). -/
def SingleReadFrom : Prog n α → (Fin n → Bool) → Prop
  | ret _, _ => True
  | read i k, vis =>
      vis i = false ∧ ∀ b, (k b).SingleReadFrom (fun j => if j = i then true else vis j)
  | snap k, vis => (∀ j, vis j = false) ∧ ∀ s, (k s).SingleReadFrom (fun _ => true)

/-- `p.NoSnap`: `p` uses one-byte reads and no atomic snapshot. -/
def NoSnap : Prog n α → Prop
  | ret _ => True
  | read _ k => ∀ b, (k b).NoSnap
  | snap _ => False

/-- The vector assembled from a run of `p` against `adv` from time `t`: every address read during
the run holds the byte the run observed there, and every other address holds the filler `d`
(after a `snap`, the snapshot itself). -/
def assembleFrom : Prog n α → Adversary n → Nat → Region n → Region n
  | ret _, _, _, d => d
  | read i k, adv, t, d =>
      fun j => if j = i then adv t i else (k (adv t i)).assembleFrom adv (t + 1) d j
  | snap _, adv, t, _ => adv t

/-- `assembleFrom` from time `0`. -/
def assemble (p : Prog n α) (adv : Adversary n) (d : Region n) : Region n := p.assembleFrom adv 0 d

end Prog

section Notions

variable {n : Nat} {α : Type}

/-- Single-read discipline: every root-to-leaf path reads each address at most once. -/
def SingleRead (p : Prog n α) : Prop := p.SingleReadFrom (fun _ => false)

/-- R-safe: against every writer, the result satisfies `safe` (e.g. "no action is out of
bounds"). -/
def RSafe (safe : α → Prop) (p : Prog n α) : Prop := ∀ adv : Adversary n, safe (p.exec adv)

/-- R-valid: against every writer, the result is `spec s'` for some byte vector `s'` (which need not
be any state the writer produced). -/
def RValid (spec : Region n → α) (p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ s' : Region n, p.exec adv = spec s'

/-- R-state: against every writer, the result is `spec (adv t)` for some time `t`, i.e. the spec
applied to a region state the writer actually produced. The time `t` ranges over all of `Nat`
(including times outside the parser's own access window); this is the weakest form, and the
positive results below name a witness time inside the window. -/
def RState (spec : Region n → α) (p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ t : Nat, p.exec adv = spec (adv t)

/-- R-state restricted to the writers satisfying `W`. -/
def RStateUnder (W : Adversary n → Prop) (spec : Region n → α) (p : Prog n α) : Prop :=
  ∀ adv : Adversary n, W adv → ∃ t : Nat, p.exec adv = spec (adv t)

/-- `p` implements `spec` in private memory: on every region nobody else writes, `p` returns
`spec` of that region. -/
def Implements (p : Prog n α) (spec : Region n → α) : Prop := ∀ s : Region n, p.eval s = spec s

/-- Refinement in the private-memory semantics (programs are deterministic, so refinement is
equality of results on every region). -/
def PrivRefines (q p : Prog n α) : Prop := ∀ s : Region n, q.eval s = p.eval s

/-- Refinement in the observable-access semantics: every (event list, result) behaviour of `q`
under some writer is a behaviour of `p` under some (possibly different) writer. Because every
memory access is an observable event and parsers are deterministic, this relation is equality of
parsers (`obsRefines_iff_eq`). -/
def ObsRefines (q p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ adv' : Adversary n, q.obs adv = p.obs adv'

/-- Robust result refinement: every result that `q` returns against some writer, `p` returns
against some (possibly different) writer. Only results are compared; the memory accesses and the
writer's states are not. -/
def RobustRefines (q p : Prog n α) : Prop :=
  ∀ adv : Adversary n, ∃ adv' : Adversary n, q.exec adv = p.exec adv'

end Notions

/-- A two-byte region literal. -/
def reg2 (a b : Byte) : Region 2 := fun i => if i.val = 0 then a else b

/-- A three-byte region literal. -/
def reg3 (a b c : Byte) : Region 3 := fun i => if i.val = 0 then a else if i.val = 1 then b else c

end Toy.DoubleFetch
