/-!
# Toy pointer-provenance models: syntax and semantics

A deliberately small, fully executable model of a byte-addressed heap with three treatments of
pointer provenance:

* `Model.flat`    — pointers are plain addresses; any access that lands inside some live
                    allocation is allowed, whatever pointer was used.
* `Model.strict`  — every pointer carries the allocation it was derived from (or no provenance);
                    an access is allowed only if it lies inside the pointer's own live allocation.
                    Integer-to-pointer casts produce pointers *without* provenance.
* `Model.exposed` — as `strict`, but an integer-to-pointer cast
                    nondeterministically picks the provenance of some *exposed*, live allocation
                    whose closed range `[base, base + size]` contains the address (no provenance if
                    there is none). An allocation becomes exposed when a pointer to it is cast to an
                    integer, or when bytes of a stored pointer to it are loaded at integer type; a
                    pointer-typed load of bytes that were stored as an integer converts the integer
                    exactly like an integer-to-pointer cast.
                    Nondeterminism is resolved angelically at the level of whole-program behaviour
                    (`beh`).

Stored values occupy two abstract bytes; pointer bytes carry the whole pointer, provenance
included. Decoding two pointer bytes never depends on their provenances agreeing: at integer type
it yields the common address (exposing every provenance carried), at pointer type a pointer with
the common provenance, or with no provenance if the bytes disagree (as in MiniRust's pointer
decoding). Consequently adding provenance to a value never introduces UB (`ToyProv.Monotone`).

The program language is straight-line: allocation, deallocation, loads and stores of two-byte
values, a byte-wise copy, pointer↔integer casts, pointer and integer equality, wrapping pointer
offset, constants, register copy, and an observation instruction that appends a number to the
output trace.

Everything here is computable, so concrete programs can be evaluated by `decide`.
-/

namespace Toy.Prov

/-- Allocation identifiers: index of the allocation in `St.blocks` (allocation order). -/
abbrev AllocId := Nat
/-- Byte addresses. -/
abbrev Addr := Nat
/-- Register names. -/
abbrev Reg := Nat

/-- One allocation: its base address, its size in bytes, and whether it is still live.
Blocks are never removed; `free` only clears `live`. -/
structure Block where
  base : Addr
  size : Nat
  live : Bool
deriving DecidableEq, Repr

/-- A pointer value: an optional provenance (the allocation it may access) and an address.
In `Model.flat` every pointer that a program can produce has `prov = none`. -/
structure Ptr where
  prov : Option AllocId
  addr : Addr
deriving DecidableEq, Repr

/-- Register values: unbounded naturals ("integers") or pointers. -/
inductive Val where
  | int (n : Nat)
  | ptr (p : Ptr)
deriving DecidableEq, Repr

/-- Abstract bytes. A stored value occupies two bytes; each byte remembers which value it is a
fragment of and its index within that value. `ptrFrag` bytes therefore carry the full pointer,
including its provenance (as in byte-level semantics with provenance-carrying bytes);
`intFrag` bytes carry no provenance. Integers are fragmented symbolically, not as base-256
digits, so no arithmetic bounds are involved. -/
inductive AByte where
  | uninit
  | intFrag (n : Nat) (idx : Nat)
  | ptrFrag (p : Ptr) (idx : Nat)
deriving DecidableEq, Repr

/-- The type at which a load reads its two bytes. -/
inductive Ty where
  | int
  | ptr
deriving DecidableEq, Repr

/-- The three provenance models. -/
inductive Model where
  | flat
  | strict
  | exposed
deriving DecidableEq, Repr

/-- Straight-line instructions. `dst` registers are written; all other register arguments are
read. -/
inductive Instr where
  /-- `dst := alloc n`: fresh block of `n ≥ 1` bytes at the current top of the heap
  (bump allocation, so consecutive allocations are adjacent); `n = 0` is UB. -/
  | alloc (dst : Reg) (n : Nat)
  /-- `free p`: `p` must denote the base of a live block (by provenance in `strict`/`exposed`,
  by address in `flat`). -/
  | free (p : Reg)
  /-- `dst := load ty p`: read the two bytes at `p` and decode them at type `ty`. -/
  | load (dst : Reg) (ty : Ty) (p : Reg)
  /-- `store p src`: write the two-byte encoding of `src` at `p`. -/
  | store (p : Reg) (src : Reg)
  /-- `memcpy dst src n`: byte-wise copy of `n` abstract bytes (provenance included). -/
  | memcpy (dst src : Reg) (n : Nat)
  /-- `dst := ptr2int p`: the address; records `p`'s provenance as exposed. -/
  | ptr2int (dst : Reg) (p : Reg)
  /-- `dst := int2ptr i`. -/
  | int2ptr (dst : Reg) (i : Reg)
  /-- `dst := (p == q)` comparing addresses only; result `1` or `0`. -/
  | ptrEq (dst : Reg) (p q : Reg)
  /-- `dst := (i == j)` on integers; result `1` or `0`. -/
  | intEq (dst : Reg) (i j : Reg)
  /-- `dst := p.wrapping_offset k`: keeps provenance, never checks bounds; UB only if the
  address would become negative. -/
  | offset (dst : Reg) (p : Reg) (k : Int)
  /-- `dst := n`. -/
  | const (dst : Reg) (n : Nat)
  /-- `dst := src` (the value, provenance included). -/
  | copy (dst : Reg) (src : Reg)
  /-- Append the register's integer value (or a pointer's address) to the output trace. -/
  | obs (r : Reg)
deriving DecidableEq, Repr

/-- Programs are instruction lists. -/
abbrev Prog := List Instr

/-- Machine state. -/
structure St where
  blocks : List Block
  mem : Addr → AByte
  regs : Reg → Option Val
  exposed : List AllocId
  top : Addr
  out : List Nat

/-- Total list lookup (kept local and structural so that `decide` evaluates it). -/
def lookup {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => lookup xs n

/-- Clear the `live` flag of block `id`. -/
def killBlock : List Block → Nat → List Block
  | [], _ => []
  | b :: bs, 0 => { b with live := false } :: bs
  | b :: bs, n + 1 => b :: killBlock bs n

/-- Index of the first live block whose base is `a`. -/
def findLiveBase (a : Addr) : List Block → Nat → Option AllocId
  | [], _ => none
  | b :: bs, i => if b.live && b.base == a then some i else findLiveBase a bs (i + 1)

/-- Bytes `[a, a + n)` lie inside the live block `b`. -/
def inBlock (b : Block) (a n : Nat) : Bool :=
  b.live && decide (b.base ≤ a) && decide (a + n ≤ b.base + b.size)

/-- Is an `n`-byte access through pointer `p` allowed? -/
def canAccess (m : Model) (s : St) (p : Ptr) (n : Nat) : Bool :=
  match m with
  | .flat => s.blocks.any (fun b => inBlock b p.addr n)
  | .strict | .exposed =>
    match p.prov with
    | none => false
    | some id =>
      match lookup s.blocks id with
      | none => false
      | some b => inBlock b p.addr n

/-- The block that `free p` deallocates, if the free is allowed. -/
def freeTarget (m : Model) (s : St) (p : Ptr) : Option AllocId :=
  match m with
  | .flat => findLiveBase p.addr s.blocks 0
  | .strict | .exposed =>
    match p.prov with
    | none => none
    | some id =>
      match lookup s.blocks id with
      | none => none
      | some b => if b.live && b.base == p.addr then some id else none

/-- Allocations an integer-to-pointer cast of address `a` may pick in `Model.exposed`: exposed,
live, and with `base ≤ a ≤ base + size` (one-past-the-end included). -/
def candidates (s : St) (a : Addr) : List AllocId :=
  (List.range s.blocks.length).filter (fun id =>
    s.exposed.contains id &&
      match lookup s.blocks id with
      | none => false
      | some b => b.live && decide (b.base ≤ a) && decide (a ≤ b.base + b.size))

/-- Two-byte encoding of a value. -/
def encodeVal : Val → List AByte
  | .int n => [.intFrag n 0, .intFrag n 1]
  | .ptr p => [.ptrFrag p 0, .ptrFrag p 1]

/-- Provenance of a pointer reassembled from two pointer fragments with provenances `a` and `b`:
the common provenance if they agree, no provenance otherwise (the rule MiniRust's pointer
decoding uses for bytes with mixed provenance). -/
def mergeProv (a b : Option AllocId) : Option AllocId := if a = b then a else none

/-- Provenances carried by two pointer fragments with provenances `a` and `b` (each listed once
when they agree). An integer-typed read of the fragments exposes all of them. -/
def provsOf (a b : Option AllocId) : List AllocId := if a = b then a.toList else a.toList ++ b.toList

@[simp] theorem mergeProv_self (a : Option AllocId) : mergeProv a a = a := by simp [mergeProv]
@[simp] theorem provsOf_self (a : Option AllocId) : provsOf a a = a.toList := by simp [provsOf]

/-- Decode two bytes at integer type. Two pointer fragments (index 0 then 1) whose pointers have
the same address decode to that address, whatever their provenances; the second component lists
every provenance the bytes carry, which the load adds to the exposed set. The integer itself
never carries provenance; whether the exposure matters depends on the model (only
`Model.exposed` consults it). Fragments with different addresses or out-of-order indices, a mix
of integer and pointer fragments, and uninitialized bytes are UB (`none`).

Provenance never decides definedness here: replacing the provenance of a fragment by another one
(in particular `none` by `some id`) leaves the result defined with the same address. -/
def decodeInt : AByte → AByte → Option (Nat × List AllocId)
  | .intFrag n 0, .intFrag n' 1 => if n = n' then some (n, []) else none
  | .ptrFrag p 0, .ptrFrag p' 1 =>
    if p.addr = p'.addr then some (p.addr, provsOf p.prov p'.prov) else none
  | _, _ => none

/-- Decode two bytes at pointer type: `some (.inl q)` for two pointer fragments (index 0 then 1)
with the same address, where `q` has that address and the merged provenance (`mergeProv`: the
common provenance, or none if the fragments disagree); `some (.inr n)` for the two fragments of
one stored integer (a bare address, which the load then converts exactly as `int2ptr` would: no
provenance in `flat`/`strict`, an exposed candidate in `exposed`); `none` otherwise (UB).

Mixed provenance yields a pointer without provenance rather than UB, so that adding provenance to
a fragment never introduces UB (provenance monotonicity; see `ToyProv.Monotone`). -/
def decodePtr : AByte → AByte → Option (Ptr ⊕ Nat)
  | .ptrFrag p 0, .ptrFrag p' 1 =>
    if p.addr = p'.addr then some (.inl ⟨mergeProv p.prov p'.prov, p.addr⟩) else none
  | .intFrag n 0, .intFrag n' 1 => if n = n' then some (.inr n) else none
  | _, _ => none

/-- Write a byte list starting at address `a`. -/
def writeBytes (mem : Addr → AByte) (a : Addr) : List AByte → (Addr → AByte)
  | [] => mem
  | b :: bs => writeBytes (fun x => if x = a then b else mem x) (a + 1) bs

/-- Read `n` bytes starting at address `a`. -/
def readBytes (mem : Addr → AByte) (a : Addr) : Nat → List AByte
  | 0 => []
  | n + 1 => mem a :: readBytes mem (a + 1) n

/-- Register update. -/
def St.setReg (s : St) (r : Reg) (v : Val) : St :=
  { s with regs := fun x => if x = r then some v else s.regs x }

/-- Add provenances to the exposed set. Exposure is recorded in every model, but only the
`int2ptr` of `Model.exposed` consults it; in `flat` and `strict` it is inert bookkeeping. -/
def St.expose (s : St) (ps : List AllocId) : St :=
  { s with exposed := s.exposed ++ ps }

/-- Successors of converting address `a` to a pointer stored in register `d` (shared by `int2ptr`
and by pointer-typed loads of integer bytes): no provenance in `flat` and `strict`; in `exposed`
one successor per candidate allocation, or no provenance if there is no candidate. -/
def castToPtr (m : Model) (s : St) (d : Reg) (a : Addr) : List (Option St) :=
  match m with
  | .exposed =>
    match candidates s a with
    | [] => [some (s.setReg d (.ptr ⟨none, a⟩))]
    | c :: cs => (c :: cs).map (fun id => some (s.setReg d (.ptr ⟨some id, a⟩)))
  | .flat | .strict => [some (s.setReg d (.ptr ⟨none, a⟩))]

/-- Wrapping offset on addresses; `none` if the result would be negative. -/
def offsetAddr (a : Addr) : Int → Option Addr
  | .ofNat n => some (a + n)
  | .negSucc n => if n + 1 ≤ a then some (a - (n + 1)) else none

/-- One step. The result lists every possible successor; `none` is undefined behaviour. Only
`castToPtr` in `Model.exposed` (an `int2ptr`, or a pointer-typed load of integer bytes) can have
more than one successor. -/
def step (m : Model) (s : St) : Instr → List (Option St)
  | .alloc d n =>
    if n = 0 then [none] else
      let prov : Option AllocId := match m with
        | .flat => none
        | .strict | .exposed => some s.blocks.length
      [some { (s.setReg d (.ptr ⟨prov, s.top⟩)) with
                blocks := s.blocks ++ [⟨s.top, n, true⟩], top := s.top + n }]
  | .free p =>
    match s.regs p with
    | some (.ptr x) =>
      match freeTarget m s x with
      | some id => [some { s with blocks := killBlock s.blocks id }]
      | none => [none]
    | _ => [none]
  | .load d ty p =>
    match s.regs p with
    | some (.ptr x) =>
      if canAccess m s x 2 then
        match ty with
        | .int =>
          match decodeInt (s.mem x.addr) (s.mem (x.addr + 1)) with
          | some (n, ps) => [some ((s.setReg d (.int n)).expose ps)]
          | none => [none]
        | .ptr =>
          match decodePtr (s.mem x.addr) (s.mem (x.addr + 1)) with
          | some (.inl q) => [some (s.setReg d (.ptr q))]
          | some (.inr n) => castToPtr m s d n
          | none => [none]
      else [none]
    | _ => [none]
  | .store p r =>
    match s.regs p, s.regs r with
    | some (.ptr x), some v =>
      if canAccess m s x 2 then [some { s with mem := writeBytes s.mem x.addr (encodeVal v) }]
      else [none]
    | _, _ => [none]
  | .memcpy d r n =>
    match s.regs d, s.regs r with
    | some (.ptr x), some (.ptr y) =>
      if canAccess m s x n && canAccess m s y n then
        [some { s with mem := writeBytes s.mem x.addr (readBytes s.mem y.addr n) }]
      else [none]
    | _, _ => [none]
  | .ptr2int d p =>
    match s.regs p with
    | some (.ptr x) => [some ((s.setReg d (.int x.addr)).expose x.prov.toList)]
    | _ => [none]
  | .int2ptr d i =>
    match s.regs i with
    | some (.int a) => castToPtr m s d a
    | _ => [none]
  | .ptrEq d p q =>
    match s.regs p, s.regs q with
    | some (.ptr x), some (.ptr y) => [some (s.setReg d (.int (if x.addr = y.addr then 1 else 0)))]
    | _, _ => [none]
  | .intEq d i j =>
    match s.regs i, s.regs j with
    | some (.int a), some (.int b) => [some (s.setReg d (.int (if a = b then 1 else 0)))]
    | _, _ => [none]
  | .offset d p k =>
    match s.regs p with
    | some (.ptr x) =>
      match offsetAddr x.addr k with
      | some a => [some (s.setReg d (.ptr ⟨x.prov, a⟩))]
      | none => [none]
    | _ => [none]
  | .const d n => [some (s.setReg d (.int n))]
  | .copy d r =>
    match s.regs r with
    | some v => [some (s.setReg d v)]
    | none => [none]
  | .obs r =>
    match s.regs r with
    | some (.int n) => [some { s with out := s.out ++ [n] }]
    | some (.ptr x) => [some { s with out := s.out ++ [x.addr] }]
    | none => [none]

/-- All executions of a program from a state (`none` = the execution reached UB). -/
def exec (m : Model) : Prog → St → List (Option St)
  | [], s => [some s]
  | i :: is, s =>
    (step m s i).flatMap (fun o =>
      match o with
      | none => [none]
      | some s' => exec m is s')

/-- Initial state: empty heap starting at address 16, no registers, nothing exposed. -/
def init : St where
  blocks := []
  mem := fun _ => .uninit
  regs := fun _ => none
  exposed := []
  top := 16
  out := []

/-- Whole-program outcomes. -/
inductive Outcome where
  | ub
  | done (out : List Nat)
deriving DecidableEq, Repr

/-- Outcome of every execution (demonic collection, before angelic resolution). -/
def runs (m : Model) (P : Prog) : List Outcome :=
  (exec m P init).map (fun o => match o with
    | none => .ub
    | some s => .done s.out)

/-- Behaviour with angelic resolution of nondeterminism: if every execution is UB the behaviour
is `[ub]`; otherwise it is the list of outcomes of the UB-free executions. In `flat` and
`strict` there is exactly one execution. -/
def beh (m : Model) (P : Prog) : List Outcome :=
  let r := runs m P
  if r.all (fun o => decide (o = .ub)) then [.ub] else r.filter (fun o => decide (o ≠ .ub))

/-- Refinement: `tgt` refines `src` in model `m` if `src` has UB (every resolution is UB), or
every behaviour of `tgt` is a behaviour of `src`. -/
def Refines (m : Model) (tgt src : Prog) : Prop :=
  Outcome.ub ∈ beh m src ∨ ∀ o ∈ beh m tgt, o ∈ beh m src

instance (m : Model) (tgt src : Prog) : Decidable (Refines m tgt src) := by
  unfold Refines; infer_instance

end Toy.Prov
