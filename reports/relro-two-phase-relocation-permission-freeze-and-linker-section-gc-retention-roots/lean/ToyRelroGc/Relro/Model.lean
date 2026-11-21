/-
Toy model of load-time relocation followed by a permission freeze (RELRO).

The model is deliberately small:
* an image is a list of byte kinds (`code`, `ro`, `relro`, `mutable`) plus initial contents;
* a relocation is a slot plus a value function of the symbol table and the current memory;
* the loader applies relocations, runs one `protect` event, and then the program runs;
* a write to a non-writable address faults, and a fault leaves the state unchanged.

It is a toy: it neither establishes nor refutes claims about any real loader or linker.
-/
namespace Toy.RelroGc

/-- Memory contents: one natural-number value per address (a slot is one address). -/
abbrev Mem := Nat → Nat
/-- Symbols are numbered. -/
abbrev Sym := Nat
/-- A symbol table: the address of every symbol (load-time addresses for the loader). -/
abbrev SymTab := Sym → Nat

/-- Point update of a memory. -/
def upd (m : Mem) (a v : Nat) : Mem := fun b => if b = a then v else m b

/-- The kind of an image byte, standing for the input section it came from:
`code` (`.text`), `ro` (`.rodata`), `relro` (`.data.rel.ro`, GOT entries placed inside the
`PT_GNU_RELRO` range), `mutable` (`.data`/`.bss`, writable for the whole run). -/
inductive Kind where
  | code
  | ro
  | relro
  | mutable
  deriving DecidableEq, Repr

/-- A relocation: the slot it writes and the value it computes from the symbol table and the
current memory. An ordinary relocation ignores the memory (see `Reloc.AddressOnly`); a resolver
relocation (an IFUNC-like resolver run by the loader) may read it. -/
structure Reloc where
  slot : Nat
  val : SymTab → Mem → Nat

/-- The relocation's value depends on symbol addresses alone, not on memory contents. -/
def Reloc.AddressOnly (r : Reloc) : Prop :=
  ∀ (sa : SymTab) (m m' : Mem), r.val sa m = r.val sa m'

/-- The relocation's value depends on memory only through the addresses satisfying `S`. -/
def Reloc.ReadsOnly (r : Reloc) (S : Nat → Prop) : Prop :=
  ∀ (sa : SymTab) (m m' : Mem), (∀ a, S a → m a = m' a) → r.val sa m = r.val sa m'

/-- Apply one relocation, ignoring permissions. -/
def applyReloc (sa : SymTab) (m : Mem) (r : Reloc) : Mem := upd m r.slot (r.val sa m)

/-- Apply a list of relocations in list order, ignoring permissions: the fully relocated image. -/
def applyAll (sa : SymTab) (rs : List Reloc) (m : Mem) : Mem := rs.foldl (applyReloc sa) m

/-- A loader input. `kinds[a]` is the kind of byte `a` (addresses at or past `kinds.length` are
unmapped). `relocs` are the dynamic relocations, applied in list order. `prot` is the set of
addresses that `protect` makes read-only. `lazy` lists lazily bound slots with their target
symbols; an unbound lazy slot holds `stub` (the address of the lazy-binding resolver). -/
structure Cfg where
  kinds : List Kind
  init : Mem
  relocs : List Reloc
  prot : Nat → Bool
  lazy : List (Nat × Sym)
  stub : Nat

/-- Map-time writability: exactly the `relro` and `mutable` bytes are mapped writable.
Unmapped addresses are not writable. The model tracks write permission alone: read and execute
permissions are not modeled. -/
def mapWr (L : List Kind) (a : Nat) : Bool :=
  match L[a]? with
  | some .relro => true
  | some .mutable => true
  | _ => false

/-- Loader/program state: memory and the current writability of every address. -/
structure St where
  mem : Mem
  wr : Nat → Bool

/-- The state right after mapping. -/
def Cfg.start (c : Cfg) : St := ⟨c.init, mapWr c.kinds⟩

/-- Program operations after entry: a store, or an indirect call through a binding slot. -/
inductive Op where
  | write (a v : Nat)
  | call (x : Nat)

/-- Timeline events: the loader applies a relocation, the loader runs `protect`, or the
program performs an operation. -/
inductive Ev where
  | apply (r : Reloc)
  | protect
  | op (o : Op)

/-- Outcome of one event: success, a permission fault, or an indirect call to address `d`. -/
inductive Out where
  | ok
  | fault
  | jump (d : Nat)
  deriving DecidableEq, Repr

/-- The loader applies one relocation; it faults if the slot is not currently writable. -/
def stepApply (sa : SymTab) (s : St) (r : Reloc) : St × Out :=
  if s.wr r.slot then ({ s with mem := applyReloc sa s.mem r }, .ok) else (s, .fault)

/-- `protect`: every address in `c.prot` becomes non-writable; nothing becomes writable. -/
def stepProtect (c : Cfg) (s : St) : St := { s with wr := fun a => s.wr a && !c.prot a }

/-- One program operation. A write faults on a non-writable address. A call through `x` jumps
to the address stored in `x`, except that if `x` is a lazy slot still holding `stub`, the lazy
resolver first writes the target's address into `x` (faulting if `x` is not writable). -/
def stepOp (c : Cfg) (sa : SymTab) (s : St) : Op → St × Out
  | .write a v => if s.wr a then ({ s with mem := upd s.mem a v }, .ok) else (s, .fault)
  | .call x =>
    match (if s.mem x = c.stub then c.lazy.lookup x else none) with
    | some t => if s.wr x then ({ s with mem := upd s.mem x (sa t) }, .jump (sa t)) else (s, .fault)
    | none => (s, .jump (s.mem x))

/-- What a timeline produced: the outcomes of the `apply` events and of the program operations
(each in order), and the memory at the first `protect` event. -/
structure Trace where
  applyOuts : List Out
  opOuts : List Out
  memAtProtect : Option Mem

/-- Run a timeline from a state. -/
def runT (c : Cfg) (sa : SymTab) : St → List Ev → Trace
  | _, [] => ⟨[], [], none⟩
  | s, .apply r :: t =>
    let p := stepApply sa s r
    let tr := runT c sa p.1 t
    { tr with applyOuts := p.2 :: tr.applyOuts }
  | s, .protect :: t =>
    let tr := runT c sa (stepProtect c s) t
    { tr with memAtProtect := some s.mem }
  | s, .op o :: t =>
    let p := stepOp c sa s o
    let tr := runT c sa p.1 t
    { tr with opOuts := p.2 :: tr.opOuts }

/-- Run a timeline from the mapped image. -/
def trace (c : Cfg) (sa : SymTab) (t : List Ev) : Trace := runT c sa c.start t

/-- Insert `x` at position `k` of `l` (at the end if `k ≥ l.length`). -/
def insertAt {α : Type} (k : Nat) (x : α) (l : List α) : List α := l.take k ++ x :: l.drop k

/-- The timeline generator: the relocations of `c` in list order, then the program operations
`ops`, with the single `protect` event inserted at position `k`. -/
def timeline (c : Cfg) (ops : List Op) (k : Nat) : List Ev :=
  insertAt k .protect (c.relocs.map .apply ++ ops.map .op)

/-- The standard two-phase timeline: all relocations, then `protect`, then the program. -/
def twoPhase (c : Cfg) (ops : List Op) : List Ev :=
  c.relocs.map .apply ++ .protect :: ops.map .op

/-- No relocation faulted. -/
def LoadOk (tr : Trace) : Prop := ∀ o ∈ tr.applyOuts, o = .ok

instance (tr : Trace) : Decidable (LoadOk tr) :=
  inferInstanceAs (Decidable (∀ o ∈ tr.applyOuts, o = .ok))

/-! ### Hypotheses of the two-phase schedule (each a separate `Prop`) -/

/-- (H1) Every dynamically relocated slot is mapped writable. -/
def RelocSlotsWritable (c : Cfg) : Prop := ∀ r ∈ c.relocs, mapWr c.kinds r.slot = true

/-- A mask covers every RELRO byte of the layout. -/
def CoversRelro (L : List Kind) (m : Nat → Bool) : Prop :=
  ∀ a < L.length, L[a]? = some .relro → m a = true

/-- A mask contains no mutable byte of the layout. -/
def AvoidsMut (L : List Kind) (m : Nat → Bool) : Prop :=
  ∀ a < L.length, L[a]? = some .mutable → m a = false

instance (L : List Kind) (m : Nat → Bool) : Decidable (CoversRelro L m) :=
  inferInstanceAs (Decidable (∀ a < L.length, L[a]? = some .relro → m a = true))

instance (L : List Kind) (m : Nat → Bool) : Decidable (AvoidsMut L m) :=
  inferInstanceAs (Decidable (∀ a < L.length, L[a]? = some .mutable → m a = false))

/-- (H3) `protect` covers every RELRO byte. -/
def ProtCoversRelro (c : Cfg) : Prop := CoversRelro c.kinds c.prot

/-- (H4) `protect` covers no mutable byte. -/
def ProtAvoidsMut (c : Cfg) : Prop := AvoidsMut c.kinds c.prot

instance (c : Cfg) : Decidable (RelocSlotsWritable c) :=
  inferInstanceAs (Decidable (∀ r ∈ c.relocs, mapWr c.kinds r.slot = true))

instance (c : Cfg) : Decidable (ProtCoversRelro c) :=
  inferInstanceAs (Decidable (CoversRelro c.kinds c.prot))

instance (c : Cfg) : Decidable (ProtAvoidsMut c) :=
  inferInstanceAs (Decidable (AvoidsMut c.kinds c.prot))

/-- The guarantees of a timeline position `k` for program `ops`:
(a) no relocation faulted; (b) the memory at `protect` is the fully relocated image;
(c) every program write to a RELRO byte faults; (d) every program write to a mutable byte
succeeds. -/
def TwoPhaseGuarantees (c : Cfg) (sa : SymTab) (ops : List Op) (k : Nat) : Prop :=
  let tr := trace c sa (timeline c ops k)
  LoadOk tr ∧ tr.memAtProtect = some (applyAll sa c.relocs c.init) ∧
  (∀ j a v : Nat, ops[j]? = some (Op.write a v) → c.kinds[a]? = some Kind.relro →
    tr.opOuts[j]? = some Out.fault) ∧
  (∀ j a v : Nat, ops[j]? = some (Op.write a v) → c.kinds[a]? = some Kind.mutable →
    tr.opOuts[j]? = some Out.ok)

/-! ### Post-entry integrity and binding -/

/-- Post-entry write protection of address `a` under the two-phase loader: after any program
prefix `ops`, a further write of any value to `a` faults. -/
def WriteFaultsAfter (c : Cfg) (sa : SymTab) (a : Nat) : Prop :=
  ∀ (ops : List Op) (v : Nat),
    (trace c sa (twoPhase c (ops ++ [.write a v]))).opOuts[ops.length]? = some .fault

/-- Link-time resolution under the link-time symbol table `saL`: the linker applies the
relocations to the file image (`init := applyAll saL c.relocs c.init`) and emits no dynamic
relocations. The model does not relate `saL` to the addresses at which the image is later
loaded: once `relocs = []`, loading never reads the load-time symbol table. -/
def linkResolve (saL : SymTab) (c : Cfg) : Cfg :=
  { c with init := applyAll saL c.relocs c.init, relocs := [] }

/-- The relocation an eager binding of slot `x` to symbol `t` contributes. -/
def bindReloc (x : Nat) (t : Sym) : Reloc := ⟨x, fun sa _ => sa t⟩

/-- Slot `x` is eagerly bound to `t`: the loader writes `t`'s address into `x` via the
dynamic relocation `bindReloc x t`, no other dynamic relocation writes `x`, and `x` is not a
lazy slot. -/
def EagerBound (c : Cfg) (x : Nat) (t : Sym) : Prop :=
  bindReloc x t ∈ c.relocs ∧ (∀ r ∈ c.relocs, r.slot = x → r = bindReloc x t) ∧
  c.lazy.lookup x = none

/-- Slot `x` is lazily bound to `t`: it is listed as lazy with target `t`, it initially holds
`stub`, and no dynamic relocation writes it. -/
def LazyBound (c : Cfg) (x : Nat) (t : Sym) : Prop :=
  c.lazy.lookup x = some t ∧ c.init x = c.stub ∧ ∀ r ∈ c.relocs, r.slot ≠ x

/-- A call through slot `x`, executed as the sole program operation immediately after entry
(the one-operation program `[.call x]`, with no preceding program operation), loads without
fault and jumps to the address of `t`. Programs with earlier operations are not covered: an
earlier write to a writable lazy slot can redirect even the first call through it
(`partial_relro_lazy_slot_write_redirects_call`). -/
def CallWorks (c : Cfg) (sa : SymTab) (x : Nat) (t : Sym) : Prop :=
  let tr := trace c sa (twoPhase c [.call x])
  LoadOk tr ∧ tr.opOuts = [.jump (sa t)]

/-! ### Page rounding of the protected range -/

/-- Round down to a multiple of `P` (floor division; `alignDown 0 a = 0`). -/
def alignDown (P a : Nat) : Nat := a / P * P

/-- Round up to a multiple of `P` (floor division; `alignUp 0 a = 0`). -/
def alignUp (P a : Nat) : Nat := (a + P - 1) / P * P

/-- Rounding policies for the RELRO range `[rs, re)`: round both ends down, round the start
down and the end up, or protect the exact byte range (not realizable with page-granular
protection unless both ends are aligned). -/
inductive Rounding where
  | downDown
  | downUp
  | exact
  deriving DecidableEq, Repr

/-- The half-open range `[lo, hi)` as a mask. -/
def rangeMask (lo hi : Nat) : Nat → Bool := fun a => decide (lo ≤ a ∧ a < hi)

/-- The mask protected under a rounding policy, page size `P`, and RELRO range `[rs, re)`.
Degenerate edges: for `P = 0`, `alignDown 0 a = alignUp 0 a = 0` (floor division by `0` is `0`),
so every policy except `exact` protects nothing. An empty or inverted range (`re ≤ rs`)
protects nothing under every policy (`roundedMask_eq_false_of_le`): `downDown` and `exact` give
an empty interval by themselves, and `downUp` is guarded explicitly, because rounding an empty
range `[rs, rs)` with `rs % P ≠ 0` outwards would otherwise protect the whole page of `rs`. -/
def roundedMask (pol : Rounding) (P rs re : Nat) : Nat → Bool :=
  match pol with
  | .downDown => rangeMask (alignDown P rs) (alignDown P re)
  | .downUp => if rs < re then rangeMask (alignDown P rs) (alignUp P re) else fun _ => false
  | .exact => rangeMask rs re

/-- The RELRO bytes of the layout are exactly the contiguous range `[rs, re)`, inside the image. -/
def RelroIs (L : List Kind) (rs re : Nat) : Prop :=
  rs ≤ re ∧ re ≤ L.length ∧ ∀ a < L.length, (L[a]? = some .relro ↔ (rs ≤ a ∧ a < re))

instance (L : List Kind) (rs re : Nat) : Decidable (RelroIs L rs re) :=
  inferInstanceAs (Decidable (rs ≤ re ∧ re ≤ L.length ∧
    ∀ a < L.length, (L[a]? = some .relro ↔ (rs ≤ a ∧ a < re))))

/-- No mutable byte lies in `[lo, hi)`. -/
def NoMutIn (L : List Kind) (lo hi : Nat) : Prop := ∀ a < hi, lo ≤ a → L[a]? ≠ some .mutable

instance (L : List Kind) (lo hi : Nat) : Decidable (NoMutIn L lo hi) :=
  inferInstanceAs (Decidable (∀ a < hi, lo ≤ a → L[a]? ≠ some .mutable))

/-- A mask is page-granular for page size `P`: addresses on the same page (same floor
quotient by `P`) get the same value. -/
def PageGranular (P : Nat) (m : Nat → Bool) : Prop := ∀ a b, a / P = b / P → m a = m b

/-- No page holds both a RELRO byte and a mutable byte. -/
def NoSharedPage (P : Nat) (L : List Kind) : Prop :=
  ∀ a < L.length, ∀ b < L.length, a / P = b / P → L[a]? = some .relro → L[b]? ≠ some .mutable

/-- `NoSharedPage` for a concrete layout reduces to a bounded check. -/
instance (P : Nat) (L : List Kind) : Decidable (NoSharedPage P L) :=
  inferInstanceAs (Decidable (∀ a < L.length, ∀ b < L.length, a / P = b / P →
    L[a]? = some .relro → L[b]? ≠ some .mutable))

end Toy.RelroGc
