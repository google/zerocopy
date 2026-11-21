# Pointer provenance models and integer–pointer cast optimizations: a kernel-checked toy semantics

## Summary

This package is a small, fully executable Lean 4 semantics of a byte-addressed heap with three treatments of pointer provenance: **flat** (pointers are plain addresses), **strict** (every pointer carries the allocation it was derived from; an integer-to-pointer cast yields a pointer without provenance), and **exposed** (as strict, but an integer-to-pointer cast angelically picks the provenance of an *exposed*, live allocation whose closed range `[base, base + size]` contains the address). Over this semantics it states and kernel-checks 26 results about which integer/pointer optimizations are refinements in which model. Model–system relation: none proved (the refinements and the monotone simulation proved here relate programs and provenance models of this package to one another, not the model to a real language or compiler). Every result is a statement about this toy model; these theorems neither establish nor refute the corresponding claims about C, LLVM IR, Rust, MiniRust, or a particular compiler, and any connection to them is a separate, explicitly labeled modeling-bridge argument (see **Applicability** and the `Basis: derived (modeling bridge)` lines under **Findings**).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (identifiers are the result ids used throughout; `AllAfter m pre c` means "the state predicate `c` holds in every UB-free state reachable after the code `pre` before the rewrite point"):

- **R1a.** In every model, for all allocation sizes `n₁ ≠ 0` and `n₂ ≠ 0` (both tight), the pointer one past the end of an `n₁`-byte allocation compares equal by address to the start of the `n₂`-byte allocation that the toy's bump allocator places immediately after it (the program outputs `[1]`).
- **R1b.** In strict and exposed, replacing reads of `q` by reads of `p` in one instruction because the two registers hold pointers with equal addresses in every reachable state (`SubstAddrEq`) is not sound: on a concrete program with `p` one past allocation A and `q` the start of the adjacent B, the target is UB while the source outputs `[1, 7]`; in flat the same rewrite is a refinement.
- **R1c.** In every model, that substitution is a refinement when, in every reachable state, the addresses are equal (`addrEqC p q`) and both pointers are in bounds of a live allocation (`inBoundsC m p`, `inBoundsC m q`: `base ≤ address < base + size` for a live allocation, which in strict/exposed must be the pointer's own provenance; an allocation's start address is in bounds, its one-past-the-end address is not); each of the three conjuncts is tight.
- **R2a.** In strict and exposed, the substitution stays unsound even when both pointers' provenances are additionally in the exposed set (`SubstIntEq`), because the substituted pointer keeps its own provenance; in flat the same rewrite is a refinement.
- **R2b.** In exposed, folding `d := int2ptr k` into `d := p` is a refinement provided that in every reachable state `k` holds `p`'s address (`hk`) and every allocation `int2ptr` could pick for that address is `p`'s own provenance, or there is none (`hc`); both tight.
- **R2c.** In every model, replacing reads of `q` by reads of `p` in one instruction gives *equal* behaviour when the two registers hold identical values (for pointers: same address and same provenance) in every reachable state (`h`, tight); in particular integer substitution after `(int)p == (int)q` is sound even in exposed at the one-past-the-end boundary.
- **R3a.** In exposed, `d := int2ptr k` and `d := p` have equal behaviour when in every reachable state `k` holds `p`'s address (`hk`) and the `int2ptr` candidates for that address are exactly `p`'s own provenance (`hc`); both tight.
- **R3b.** In exposed, folding `int2ptr((int)p)` into `p` is not a refinement even though `p`'s allocation is live, exposed, and contains `p`'s address in its closed range: proved on a concrete program with `p` one past A's end and the adjacent B exposed, and on one with `p` = B's start (in bounds of B: `base ≤ address < base + size` holds with `address = base`) and A exposed.
- **R3c.** In strict, introducing the round trip (`d := p` ⟶ `d := int2ptr k` with `k = (int)p` computed earlier) turns a program that outputs `[7]` into a UB program, so `CopyToInt2ptr` is unsound in strict; in exposed the same pair has equal behaviour.
- **R4a.** Store-to-load forwarding across a store through a freshly cast pointer `r := int2ptr k` (`ForwardAcrossCast`) is not a refinement in exposed (source `[9]`, target `[5]`) nor in flat; its soundness in strict holds only vacuously, because every matching strict source is UB (proved for all matching pairs, `h` tight; matching pairs exist).
- **R4b.** Dead-store elimination across a load through `r := int2ptr k` (`DSEAcrossCast`) is not a refinement in exposed (source `[5]`, target `[1]`) nor in flat; its soundness in strict holds only vacuously, because every matching strict source is UB (proved for all matching pairs, `h` tight; matching pairs exist).
- **R4c.** In exposed, replacing `x := load int a` by `x := v` in the window `store a v; store r w; load` is a refinement when, in every reachable state before the window, `r` and `a` hold pointers of different provenance (`hne`) and `v` holds an integer (`hv`); `r` may come from an `int2ptr`; both tight.
- **R4d.** In exposed, deleting `store a v` before `x := load ty r; store a w` is a refinement when `r` and `a` hold pointers of different provenance in every reachable state before the window (`hne`) and `x ≠ a` (`hx`); both tight.
- **R4e.** If register `k` holds an integer `n` (`hk`), every result of an exposed-model `int2ptr` is a pointer with address `n` whose provenance, if any, is an exposed live candidate, and the strict-model result has no provenance; consequently, under `hk`, `ha` (register `a` holds pointer `y`), `hA` (`y.prov = some A`), `hnot` (`A` not exposed) and `hda` (`d ≠ a`), each tight, every successor of `d := int2ptr k` satisfies `provNeC d a`, the side condition of R4c/R4d.
- **R5a.** In every model, an integer-typed load of the two fragments of a stored pointer (`hr`, `hacc`, `h0`, `h1`, each tight) yields the pointer's address as a provenance-free integer and adds the pointer's provenance to the exposed set; only exposed-model `int2ptr` consults that set, so in strict casting the integer back gives an unusable pointer while in exposed it can recover the allocation.
- **R5b.** In every model, a defined `memcpy d r n` (`hd`, `hr`, `hs`; each tight for the copy statement, while for the frame statement `hd` and `hs` are tight and `hr` is harmless) makes each destination byte equal to the corresponding source byte of the pre-state, abstract byte for abstract byte (pointer fragments keep their provenance), and leaves every other byte unchanged.
- **R5c.** In every model, a pointer-typed load of the two fragments of a stored integer `n` (`hr`, `hacc`, `h0`, `h1`, each tight) behaves exactly like `int2ptr` of `n`; hence copying a pointer through an integer value does not carry its provenance (strict: none; exposed: re-derived from the exposed set, which on three proved programs gives the same allocation, none, or a different allocation).
- **R6a.** For every program, the exposed model's behaviour refines the strict model's (no hypotheses).
- **R6b.** For every program, the flat model's behaviour refines the exposed model's (no hypotheses).
- **R6c.** For every program, all elements of the exposed model's behaviour list are equal: angelic resolution never yields two different defined outcomes (no hypotheses).
- **R6d.** Both orderings are strict: one concrete program is defined in exposed and UB in strict, and another is defined in flat and UB in exposed.
- **R6e.** A refinement in strict is a refinement in exposed when every strict behaviour of the source is an exposed behaviour of it (`hsrc`), and a refinement in exposed is a refinement in strict when every strict behaviour of the target is an exposed behaviour of it (`htgt`); both tight.
- **R6f.** In exposed, replacing `d := p` by `d := int2ptr k` is a refinement when in every reachable state `k` holds `p`'s address (`hk`) and `p`'s allocation is an `int2ptr` candidate for it (`hc`: exposed, live, address in its closed range); uniqueness is not needed in this direction; both tight.
- **R6g.** For ten transformations in the three models every soundness entry is a Lean theorem: 17 ✓ and 13 ✗ entries; **14 ✓ entries are non-vacuous** (each inhabited by a pair whose source is defined), while **3 ✓ entries are vacuous** (every matching source is UB: `CopyToInt2ptrIfCand` in flat, `ForwardAcrossCast` and `DSEAcrossCast` in strict) and are not evidence of soundness; soundness transfers neither from strict to exposed nor from exposed to strict.
- **R7a.** Under an alternative decoder that accepts two pointer fragments only if both carry the identical pointer (provenance included), adding provenance can introduce UB: exposed no longer refines strict, the strict cast fold and the no-candidate case of R2b fail, and both R6e transfer principles fail (concrete programs).
- **R7b.** This package's decoders are provenance-monotone: if each byte of one pair is below the corresponding byte of another pair (`h₀`, `h₁`; identical except that a pointer fragment may gain provenance), a defined decoding of the first pair (`h`, for the integer decoder) stays defined on the second with the same address or integer and at least as much provenance.

**The decoder design is load-bearing.** Two pointer fragments decode only if their *addresses* agree; the decoded pointer carries the common provenance if the fragments' provenances agree and *no provenance* otherwise (as MiniRust does for pointer bytes with mixed provenance), and an integer-typed read yields the common address and exposes every provenance carried. R6a, the strict cast fold in R6g, and the no-candidate case of R2b depend on this choice; with the alternative identical-pointer decoder they are false (R7a).

What these results do **not** show is listed first under **Boundaries** (per-result non-claims), followed by attractive stronger conclusions that are false or not established.

## Applicability

### What the results are about

All 26 results are theorems about one Lean 4 definition of a toy language and its three semantics (`Toy.Prov.step`/`exec`/`beh` with `Model.flat`, `Model.strict`, `Model.exposed`), in the Lake project under `lean/` (library `ToyProv`, namespace `Toy.Prov`). **This is a toy model.** It is designed to make the provenance questions behind integer–pointer casts small enough to decide by evaluation and to prove in general; it is not a model of C, LLVM IR, Rust, or MiniRust, and none of the definitions mirrors a production definition.

The three models are meant to capture three familiar design points:

- `flat` — pointers are plain addresses (every pointer a program can produce has `prov = none`); an access is allowed if it lies inside *some* live allocation, whatever pointer was used. This is the shape of a fully concrete memory model.
- `strict` — every pointer carries the allocation it was derived from (or none); an access is allowed only inside the pointer's own live allocation; `int2ptr` produces a pointer without provenance. Exposure is recorded but never consulted.
- `exposed` — as `strict`, but `int2ptr` of address `a` has one successor per *candidate*: an allocation that is exposed, live, and satisfies `base ≤ a ≤ base + size` (one-past-the-end included); with no candidate the result has no provenance. An allocation becomes exposed when a pointer to it is cast to an integer (`ptr2int`) or when bytes of a stored pointer to it are loaded at integer type. A pointer-typed load of bytes stored as an integer converts the integer exactly like `int2ptr`. Nondeterminism is resolved angelically at the level of whole-program behaviour: `beh` is `[ub]` only if every resolution is UB, and otherwise lists the outcomes of the UB-free resolutions. This is the shape of an exposure-based ("PNVI-ae-udi-like") semantics.

Known gaps between the toy and any real language or IR (each one can change an answer):

- Programs are straight-line instruction lists: no control flow, loops, functions, concurrency, or I/O beyond an `obs` instruction that appends a register's integer (or a pointer's address) to an output trace. `obs` never reveals provenance.
- Values are unbounded naturals or pointers; every stored value occupies exactly two *symbolic* abstract bytes (`intFrag n i`, `ptrFrag p i`, `uninit`), not `u8` bytes. A load is defined only on fragments 0 and 1 of one integer, or on two pointer fragments 0 and 1 with a common address; partial, misaligned, and mixed integer/pointer reads are UB. There is no alignment, no effective-type or strict-aliasing rule, and no padding.
- The allocator is deterministic bump allocation starting at address 16: consecutive allocations are adjacent, addresses are never reused, `alloc 0` is UB, and there is no out-of-memory. Allocation-address nondeterminism (which makes guessing an address UB in PNVI-ae-udi and in twin-allocation models) is absent.
- Pointer equality `ptrEq` compares addresses only and is deterministic. `offset` is a wrapping offset that keeps provenance and never checks bounds (UB only below address 0); forming an out-of-bounds pointer is therefore defined, unlike ISO C.
- `int2ptr` candidates are restricted by address (closed range, so a one-past address can have two candidates). Angelic choice is made per whole execution, not by PNVI-ae-udi's delayed "user disambiguation". MiniRust's `int2ptr` instead may pick any exposed provenance regardless of the address.
- `memcpy d r n` checks `canAccess` for both pointers even when `n = 0`; zero-sized accesses through provenance-less pointers, which Rust allows, are not modeled.
- `free p` must name the base of a live block (by provenance in strict/exposed, by address in flat); freed blocks stay in the block list with `live = false`.

### Definitions (quoted from `lean/ToyProv/Basic.lean` and `lean/ToyProv/Transform.lean`)

`lean/ToyProv/Basic.lean` (namespace `Toy.Prov`):

```lean
-- lean/ToyProv/Basic.lean:38-395
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
```

`lean/ToyProv/Transform.lean` (namespace `Toy.Prov`):

```lean
-- lean/ToyProv/Transform.lean:15-233
/-- UB-free states reachable by running `pre` from `init` (all resolutions of nondeterminism). -/
def after (m : Model) (pre : Prog) : List St :=
  (exec m pre init).filterMap id

/-- The state predicate `c` holds in every UB-free state reachable after `pre`. This is how a
transformation's run-time side condition at the point between `pre` and the rewritten
instruction is expressed. -/
def AllAfter (m : Model) (pre : Prog) (c : St → Bool) : Prop :=
  ∀ s ∈ after m pre, c s = true

instance (m : Model) (pre : Prog) (c : St → Bool) : Decidable (AllAfter m pre c) := by
  unfold AllAfter; infer_instance

/-! ## State predicates used as side conditions -/

/-- Registers `p` and `q` both hold pointers with the same address (what `ptrEq` tests). -/
def addrEqC (p q : Reg) (s : St) : Bool :=
  match s.regs p, s.regs q with
  | some (.ptr x), some (.ptr y) => x.addr == y.addr
  | _, _ => false

/-- Registers `p` and `q` both hold pointers whose provenances (if any) are in the exposed
set. -/
def bothExposedC (p q : Reg) (s : St) : Bool :=
  match s.regs p, s.regs q with
  | some (.ptr x), some (.ptr y) =>
    x.prov.toList.all (s.exposed.contains ·) && y.prov.toList.all (s.exposed.contains ·)
  | _, _ => false

/-- Registers `p` and `q` hold identical values (same kind, same address, same provenance). -/
def sameValC (p q : Reg) (s : St) : Bool :=
  match s.regs p, s.regs q with
  | some v, some w => decide (v = w)
  | _, _ => false

/-- Register `k` holds the integer equal to the address of the pointer in register `p`
(what `intEq k (ptr2int p)` would test). -/
def intIsAddrOfC (k p : Reg) (s : St) : Bool :=
  match s.regs k, s.regs p with
  | some (.int a), some (.ptr x) => a == x.addr
  | _, _ => false

/-- The `int2ptr` candidates for `p`'s address are exactly `p`'s own provenance: either `[A]`
when `p` has provenance `A`, or `[]` when `p` has none. -/
def candEqProvC (p : Reg) (s : St) : Bool :=
  match s.regs p with
  | some (.ptr x) => decide (candidates s x.addr = x.prov.toList)
  | _ => false

/-- Every `int2ptr` candidate for `p`'s address is `p`'s own provenance (there may be none). -/
def candSubProvC (p : Reg) (s : St) : Bool :=
  match s.regs p with
  | some (.ptr x) => (candidates s x.addr).all (fun c => decide (some c = x.prov))
  | _ => false

/-- `p` has a provenance that is itself an `int2ptr` candidate for `p`'s address (exposed, live,
address in its closed range). -/
def provIsCandC (p : Reg) (s : St) : Bool :=
  match s.regs p with
  | some (.ptr x) =>
    match x.prov with
    | some A => (candidates s x.addr).contains A
    | none => false
  | _ => false

/-- Register `r` holds a pointer. -/
def isPtrC (r : Reg) (s : St) : Bool :=
  match s.regs r with
  | some (.ptr _) => true
  | _ => false

/-- Register `r` holds an integer. -/
def isIntC (r : Reg) (s : St) : Bool :=
  match s.regs r with
  | some (.int _) => true
  | _ => false

/-- Registers `r` and `a` hold pointers with different provenance (`none` counts as a
provenance value, so two provenance-less pointers do *not* satisfy this). This is the
judgement of a provenance-based alias analysis: accesses through pointers of different
provenance cannot touch the same byte unless one of them is UB. -/
def provNeC (r a : Reg) (s : St) : Bool :=
  match s.regs r, s.regs a with
  | some (.ptr x), some (.ptr y) => decide (x.prov ≠ y.prov)
  | _, _ => false

/-- Register `r` holds a pointer through which a one-byte access is allowed in model `m`: in
`strict`/`exposed` its provenance is a live allocation with `base ≤ address < base + size` (the
start is included, one-past-the-end excluded); in `flat`, some live allocation meets those bounds. -/
def inBoundsC (m : Model) (r : Reg) (s : St) : Bool :=
  match s.regs r with
  | some (.ptr x) => canAccess m s x 1
  | _ => false

/-! ## Syntactic operations on instructions -/

/-- Register renaming used by `Instr.substUse`. -/
def subReg (q p r : Reg) : Reg := if r = q then p else r

/-- Replace every *read* of register `q` by a read of `p`; destination registers are unchanged. -/
def Instr.substUse (q p : Reg) : Instr → Instr
  | .alloc d n => .alloc d n
  | .free r => .free (subReg q p r)
  | .load d ty r => .load d ty (subReg q p r)
  | .store r v => .store (subReg q p r) (subReg q p v)
  | .memcpy d r n => .memcpy (subReg q p d) (subReg q p r) n
  | .ptr2int d r => .ptr2int d (subReg q p r)
  | .int2ptr d r => .int2ptr d (subReg q p r)
  | .ptrEq d r t => .ptrEq d (subReg q p r) (subReg q p t)
  | .intEq d r t => .intEq d (subReg q p r) (subReg q p t)
  | .offset d r k => .offset d (subReg q p r) k
  | .const d n => .const d n
  | .copy d r => .copy d (subReg q p r)
  | .obs r => .obs (subReg q p r)

/-- Does the instruction read register `x`? -/
def Instr.reads (x : Reg) : Instr → Bool
  | .alloc _ _ => false
  | .free r => r == x
  | .load _ _ r => r == x
  | .store r v => r == x || v == x
  | .memcpy d r _ => d == x || r == x
  | .ptr2int _ r => r == x
  | .int2ptr _ r => r == x
  | .ptrEq _ r t => r == x || t == x
  | .intEq _ r t => r == x || t == x
  | .offset _ r _ => r == x
  | .const _ _ => false
  | .copy _ r => r == x
  | .obs r => r == x

/-! ## Transformations

Each is stated with an explicit split `src = pre ++ i :: post` of the source program; `pre` is
the code before the rewrite point and the side condition is checked on every state reachable
after `pre`. -/

/-- Soundness of a transformation in a model: every rewrite it allows is a refinement. -/
def Sound (m : Model) (T : Model → Prog → Prog → Prop) : Prop :=
  ∀ src tgt, T m src tgt → Refines m tgt src

/-- **Address-equality substitution** (GVN on pointers justified by `p == q`): replace the reads
of `q` in one instruction by reads of `p`, when `p` and `q` hold pointers with equal addresses in
every reachable state at that point. -/
def SubstAddrEq (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (addrEqC p q)

/-- **Integer-equality substitution of pointers**: as `SubstAddrEq`, but additionally both
pointers' provenances are exposed at that point, as they are after the program has cast both
to integers and found the integers equal (`(int)p == (int)q`). -/
def SubstIntEq (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (fun s => addrEqC p q s && bothExposedC p q s)

/-- **Identical-value substitution**: replace reads of `q` by reads of `p` when the two
registers hold identical values (for integers this is integer GVN; for pointers it requires
equal provenance as well as equal address). -/
def SubstSameVal (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (sameValC p q)

/-- **In-bounds address-equality substitution**: as `SubstAddrEq`, but additionally both
pointers are in bounds of a live allocation (`inBoundsC`: `base ≤ address < base + size`) in
every reachable state at that point. -/
def SubstAddrEqInBounds (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (fun s => addrEqC p q s && inBoundsC m p s && inBoundsC m q s)

/-- **Cast folding** `d := int2ptr k` ⟶ `d := p`, justified by `k == (int)p` at that point
(this covers the round-trip fold `int2ptr(ptr2int p) ⟶ p`). -/
def Int2ptrToCopy (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d k p, src = pre ++ .int2ptr d k :: post ∧ tgt = pre ++ .copy d p :: post ∧
    AllAfter m pre (intIsAddrOfC k p)

/-- **Cast introduction** `d := p` ⟶ `d := int2ptr k`, justified by `k == (int)p` (the reverse
of `Int2ptrToCopy`: replacing a pointer by the round trip through an equal integer). -/
def CopyToInt2ptr (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d k p, src = pre ++ .copy d p :: post ∧ tgt = pre ++ .int2ptr d k :: post ∧
    AllAfter m pre (intIsAddrOfC k p)

/-- **Cast introduction with a candidate** `d := p` ⟶ `d := int2ptr k`: as `CopyToInt2ptr`, but
additionally `p`'s provenance is an `int2ptr` candidate for its address (`provIsCandC`: exposed,
live, address in its closed range) in every reachable state at that point. -/
def CopyToInt2ptrIfCand (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d k p, src = pre ++ .copy d p :: post ∧ tgt = pre ++ .int2ptr d k :: post ∧
    AllAfter m pre (intIsAddrOfC k p) ∧ AllAfter m pre (provIsCandC p)

/-- **Dead-cast elimination**: delete `d := ptr2int p` when `p` holds a pointer at that point
(so the cast itself is not UB) and no later instruction reads `d`. -/
def DropUnusedPtr2int (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d p, src = pre ++ .ptr2int d p :: post ∧ tgt = pre ++ post ∧
    (∀ i ∈ post, i.reads d = false) ∧ AllAfter m pre (isPtrC p)

/-- **Store-to-load forwarding across a store through a freshly cast pointer**:
`r := int2ptr k; store a v; store r w; x := load int a` ⟶ the same with the load replaced by
`x := v`, when `v` holds an integer. The optimizer's assumption is that a pointer obtained from
an integer does not alias `a`. -/
def ForwardAcrossCast (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post r k a v w x, r ≠ a ∧ r ≠ v ∧
    src = pre ++ [.int2ptr r k, .store a v, .store r w, .load x .int a] ++ post ∧
    tgt = pre ++ [.int2ptr r k, .store a v, .store r w, .copy x v] ++ post ∧
    AllAfter m pre (isIntC v)

/-- **Dead-store elimination across a load through a freshly cast pointer**:
`r := int2ptr k; store a v; x := load ty r; store a w` ⟶ the same without `store a v`. The
optimizer's assumption is that the load through `r` cannot observe the first store. -/
def DSEAcrossCast (_m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post r k a v x ty w, r ≠ a ∧ r ≠ v ∧ x ≠ a ∧
    src = pre ++ [.int2ptr r k, .store a v, .load x ty r, .store a w] ++ post ∧
    tgt = pre ++ [.int2ptr r k, .load x ty r, .store a w] ++ post

/-- Semantic ordering of models on one program: `m₁`'s behaviour of `P` refines `m₂`'s (either
`P` has UB in `m₂`, or every `m₁` behaviour is an `m₂` behaviour). "`m₂` has more UB." -/
def SemRefines (m₁ m₂ : Model) (P : Prog) : Prop :=
  Outcome.ub ∈ beh m₂ P ∨ ∀ o ∈ beh m₁ P, o ∈ beh m₂ P

instance (m₁ m₂ : Model) (P : Prog) : Decidable (SemRefines m₁ m₂ P) := by
  unfold SemRefines; infer_instance
```

`lean/ToyProv/Examples.lean` proves intended positive and negative examples for the following definitions (all quoted above). **Operational definitions:** `alloc` (consecutive allocations are adjacent; `alloc 0` is UB in every model); `canAccess` (in strict, an access needs the pointer's own live allocation, and a pointer without provenance or with another allocation's provenance is rejected; in flat, any live allocation containing the bytes suffices); `candidates` (address 18 has the two candidates A and B when both are exposed, none when neither is exposed, and none for an address outside every closed range); `mergeProv` and `provsOf`; `decodeInt` and `decodePtr` (matching fragments, mixed provenance, mismatched addresses, misordered fragments, an uninitialised byte, and integer/pointer mixtures); `castToPtr` (two results in exposed, one in strict); `runs` and `beh` (a program with one UB and one defined resolution, whose angelic behaviour is the defined one, and which is UB in strict); `Refines`; `Instr.substUse` and `Instr.reads`; and `SemRefines`. **State predicates** (via `AllAfter`): positive and negative examples for 8 of the 11 predicates: `addrEqC`, `sameValC`, `intIsAddrOfC`, `bothExposedC`, `candEqProvC`, `candSubProvC`, `provIsCandC`, `provNeC`. **Transformation relations:** a positive and a negative instance for 8 of the 10 relations: `SubstAddrEq`, `SubstSameVal`, `SubstIntEq`, `Int2ptrToCopy`, `CopyToInt2ptr`, `DropUnusedPtr2int`, `ForwardAcrossCast`, `DSEAcrossCast`. `Examples.lean` has no example for the predicates `inBoundsC`, `isPtrC`, `isIntC` or for the relations `SubstAddrEqInBounds`, `CopyToInt2ptrIfCand`. Elsewhere in the package: `inBoundsC` has positive and negative instances as conjuncts of the R1c tightness witnesses (`substAddrEqInBounds_p_needed`, `substAddrEqInBounds_q_needed`, `substAddrEqInBounds_addrEq_needed`, in `ToyProv/OnePast.lean`); `isIntC` has positive instances as conjuncts of R4c statements (`forwardLoad_provNe_needed`, `forwardLoad_nonvacuous`, in `ToyProv/Forwarding.lean`), while its failure in the initial state is used inside the proof of the negative `ForwardAcrossCast` example and is not stated separately; `SubstAddrEqInBounds` has positive instances (R1c's non-vacuity witness and the R6g table witnesses) but no stated negative instance; `CopyToInt2ptrIfCand` has a positive instance in strict (R6g) and a negative one in flat (`not_copyToInt2ptrIfCand_flat_r3`, quoted under R6g); `isPtrC` has no stated positive or negative example of its own: it is a conjunct of `DropUnusedPtr2int`, whose positive instances evaluate it to true. **Proof method:** the examples about operational definitions and state predicates, and the `SemRefines` examples, are closed evaluations (`decide`). Each positive transformation instance names the decomposition into prefix, window and suffix explicitly and checks the side condition by `decide`. Each negative transformation instance is proved by case analysis on how the program can be decomposed (with a lemma that a one-instruction program splits only with an empty prefix, with a length argument, or by cases on the prefix), followed by evaluating the side condition in the initial state or by contradicting the relation's register or read conditions; these are not closed evaluations.

### Toolchain and dependencies

Lean 4 `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), pinned in `lean/lean-toolchain`. The project uses core Lean only: no Mathlib and no other `[[require]]` dependency. `lean/lakefile.toml` declares the single library `ToyProv`.

### How the subjects relate

`REPORT.json` lists the Lean toolchain release that kernel-checks every theorem, the primary papers whose results or examples are re-derived or compared in this toy (Memarian et al. 2019; Lee et al. 2018; Kang et al. 2015; Lepigre et al. 2022), and the MiniRust specification at one pinned commit, whose pointer-byte decoding and `int2ptr` rule are compared with this toy's. The report does not examine any of these systems by execution; the papers and the specification are the reference points for the tier and prior-art statements and for the modeling-bridge arguments. The ISO/IEC TS 6010:2025 provenance model is referred to through its public draft text (WG21 P2318R0 / WG14 N2577); the normative TS text was not examined. Rust's standard-library documentation (version 1.84.0) is quoted for the meaning of `with_exposed_provenance` and `without_provenance`.

### Modeling bridges (not kernel-checked)

The following correspondences are arguments, not theorems; each finding repeats the one it relies on as a separate `Basis: derived (modeling bridge)` line.

- **Exposed ↔ PNVI-ae-udi.** P2318R0 defines exposure by pointer-to-integer conversion, by a non-pointer-type read of a pointer's representation, or by `%p` output; PNVI-ae-udi "is designed to permit a cast of a one-past pointer to integer and back to recover the original provenance", leaving an ambiguous provenance unknown until the first disambiguating operation and "allowing one or the other (but not both) to be used, so long as that is done consistently". The toy's exposure rule (minus `%p`, which it does not have) and its closed-range candidate set follow this; the delayed, consistent disambiguation is approximated by whole-execution angelic choice among the candidates.
- **Strict ↔ Rust strict-provenance APIs.** Strict `int2ptr` behaves like Rust's `std::ptr::without_provenance(addr)` ("Creates a pointer with the given address and no provenance"), not like an `as` cast: the Rust 1.84.0 documentation says `with_exposed_provenance` "is fully equivalent to `addr as *const T`" and does not specify which exposed provenance is picked. The angelic choice in `exposed` is MiniRust's and PNVI-ae-udi's reading, not a guarantee of the Rust documentation.
- **Decoder ↔ MiniRust.** MiniRust (commit `063d784186d3252bee242217f218223205c0b568`, `spec/lang/representation.md`) decodes pointer bytes "not all having the same provenance" to "a pointer without provenance", and requires decoding to be monotone ("If `bytes1 <= bytes2`, then `ty.decode(bytes1) <= ty.decode(bytes2)`"). This toy's `decodePtr`/`mergeProv` makes the same choice for mixed provenance and proves the analogous monotonicity for its two-byte decoders (R7b). It differs from MiniRust at integer type: MiniRust's integer decoding "entirely ignores provenance" (a pointer-to-integer transmutation strips provenance *without* exposing it, marked as an open question there), whereas the toy's integer-typed load exposes the provenances it reads, following PNVI-ae.
- **Exposed `int2ptr` ↔ MiniRust `int2ptr`.** MiniRust (`spec/mem/intptrcast.md`, same commit) predicts a provenance that "must be either `None` or already exposed", with no address-range check, "maximally in the programmer's favor". The toy adds the address-range restriction, so address-local side conditions (`candSubProvC`, `candEqProvC`, `provIsCandC`) do not carry over to MiniRust when another allocation is exposed.
- **Transformations ↔ compiler passes.** `SubstAddrEq`, `SubstIntEq`, `Int2ptrToCopy`, `ForwardAcrossCast`, `DSEAcrossCast` and the others are this package's relations (fixed windows, semantic side conditions over reachable states). They are shaped after GVN on pointers, cast folding, store-to-load forwarding and dead-store elimination as discussed by Lee et al. (2018) and Jung (2020, 2022), but they are not any compiler's passes.

## Findings

Every result below is a Lean theorem in `lean/ToyProv/`, kernel-checked under Lean 4 `v4.34.1` with no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (per-theorem record under **Evidence**). Lean statements are quoted verbatim from the source; the definitions they use are quoted under **Applicability** (semantics and transformations) or next to the statement (concrete programs and states). Register numbers in concrete programs are arbitrary; allocation A is the first allocation (address 16) and B the second (address 18) unless stated otherwise.

| id | kind | tier | depth | main Lean name(s) |
| --- | --- | --- | --- | --- |
| R1a | theorem | T0 | definitional | `onePast_ptrEq_adjacent_start` |
| R1b | counterexample | T0 | definitional | `substAddrEq_counterexample_strict`, `substAddrEq_counterexample_exposed`, `substAddrEq_not_sound_strict` (+1 more) |
| R1c | theorem | T0 | substantive | `substAddrEqInBounds_sound` |
| R2a | counterexample | T0 | definitional | `substIntEq_counterexample_strict`, `substIntEq_counterexample_exposed`, `substIntEq_not_sound_strict` (+1 more) |
| R2b | theorem | T1 | substantive | `int2ptrToCopy_refines_exposed_of_intIsAddrOf_of_candSubProv` |
| R2c | theorem | T0 | shallow | `substSameVal_beh_eq`, `substSameVal_sound` |
| R3a | theorem | T1 | shallow | `int2ptrToCopy_beh_eq_exposed_of_intIsAddrOf_of_candEqProv` |
| R3b | counterexample | T1 | definitional | `roundTrip_fold_counterexample_exposed_boundary`, `int2ptrToCopy_not_sound_exposed`, `roundTrip_fold_counterexample_exposed_base_pointer` |
| R3c | counterexample | T0 | definitional | `roundTrip_counterexample_strict`, `copyToInt2ptr_not_sound_strict` |
| R4a | counterexample | T1 | shallow | `forwardAcrossCast_counterexample`, `forwardAcrossCast_not_sound_exposed`, `forwardAcrossCast_not_sound_flat` (+2 more) |
| R4b | counterexample | T1 | shallow | `dseAcrossCast_counterexample`, `dseAcrossCast_not_sound_exposed`, `dseAcrossCast_not_sound_flat` (+1 more) |
| R4c | theorem | T1 | substantive | `forwardLoad_refines_exposed_of_provNe_of_isInt` |
| R4d | theorem | T1 | substantive | `dse_refines_exposed_of_provNe_of_ne` |
| R4e | theorem | T0 | definitional | `int2ptr_exposed_result`, `int2ptr_strict_result`, `int2ptr_result_provNe_of_not_exposed` |
| R5a | theorem | T1 | definitional | `load_int_of_ptrFrags`, `decodeInt_ptrFrags`, `byteLoadAsInt_strict_strips_exposed_exposes` |
| R5b | theorem | T0 | shallow | `memcpy_copies_abstract_bytes`, `memcpy_frame`, `memcpy_preserves_provenance_example` (+1 more) |
| R5c | theorem | T1 | definitional | `load_ptr_of_intFrags`, `decodePtr_intFrags`, `intRoundTrip_in_range_example` (+2 more) |
| R6a | theorem | T1 | substantive | `exposed_semRefines_strict` |
| R6b | theorem | T1 | substantive | `flat_semRefines_exposed` |
| R6c | theorem | T1 | substantive | `exposed_beh_elements_equal` |
| R6d | theorem | T0 | definitional | `model_orderings_strict` |
| R6e | theorem | T0 | shallow | `refines_exposed_of_refines_strict_of_src_semRefines`, `refines_strict_of_refines_exposed_of_tgt_semRefines`, `refines_exposed_of_refines_strict_core` (+1 more) |
| R6f | theorem | T1 | substantive | `copyToInt2ptr_refines_exposed_of_intIsAddrOf_of_provIsCand` |
| R6g | characterization | T1 | substantive | `substAddrEq_sound_flat`, `substAddrEq_not_sound_strict`, `substAddrEq_not_sound_exposed` (+26 more) |
| R7a | counterexample | T1 | definitional | `EqProvDecode.decodeEq_not_monotone`, `EqProvDecode.eqProvDecode_exposed_not_semRefines_strict`, `EqProvDecode.eqProvDecode_fold_not_refinement` (+2 more) |
| R7b | theorem | T1 | shallow | `decodeInt_mono`, `decodePtr_mono` |

Tiers: T0 = known result restated in this vocabulary; T1 = folklore or informal knowledge made precise and mechanized here. No result claims novelty (T3). Depth: `definitional` = closed evaluation or a direct unfolding; `shallow` = a short argument over the definitions; `substantive` = needs a whole-semantics invariant or simulation (in `FlatInv`, `Disjoint`, `DeadCast`, `Erasure`, `MonoSim`).

### R1a: one past end compares equal to adjacent start

- **Kind / tier / depth:** theorem · T0 · definitional. Tier rationale: The adjacency fact is the situation addressed by ISO C18 6.5.9p6 and used in every cited provenance paper; here it is a closed evaluation in the toy, quantified over allocation sizes.
- **Plain claim:** In each of the three models (flat, strict, exposed), for all allocation sizes n1, n2 >= 1, with the toy's bump allocator placing a second allocation B of n2 bytes immediately after an allocation A of n1 bytes, the pointer A + n1 (one past A's end) compares equal by address to the pointer to B's start (the program outputs [1]).

Lean statement (`R1a`):

```lean
-- lean/ToyProv/OnePast.lean:23-24
-- onePast_ptrEq_adjacent_start  (ToyProv/OnePast.lean:23)
theorem onePast_ptrEq_adjacent_start (m : Model) (n₁ n₂ : Nat) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) :
    beh m (onePastProgN n₁ n₂) = [.done [1]]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/OnePast.lean
/-- Allocate A (`n₁` bytes) and B (`n₂` bytes), form `A + n₁` (one past A's end), compare it with
B's start by `ptrEq`, and observe the result. -/
def onePastProgN (n₁ n₂ : Nat) : Prog :=
  [.alloc 0 n₁, .alloc 1 n₂, .offset 2 0 (n₁ : Int), .ptrEq 3 2 1, .obs 3]
-- ToyProv/OnePast.lean
/-- Allocate A (2 bytes) and B (2 bytes), form `A + 2` (one past A's end), compare it with B's
start by `ptrEq`, and observe the result. -/
def onePastProg : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptrEq 3 2 1, .obs 3]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h₁ : n₁ ≠ 0` | A zero-size allocation is UB in the toy. | tight | `onePast_size₁_needed` (ToyProv/OnePast.lean:28) |
| `h₂ : n₂ ≠ 0` | A zero-size allocation is UB in the toy. | tight | `onePast_size₂_needed` (ToyProv/OnePast.lean:33) |

- **Non-vacuity witness:** The two-byte instance onePastProg (n1 = n2 = 2), used again by R1b. Lean: `onePast_ptrEq_adjacent_start_all_models`.

```lean
-- lean/ToyProv/OnePast.lean:38-39
-- onePast_ptrEq_adjacent_start_all_models  (ToyProv/OnePast.lean:38)
theorem onePast_ptrEq_adjacent_start_all_models (m : Model) :
    (2 : Nat) ≠ 0 ∧ (2 : Nat) ≠ 0 ∧ beh m onePastProg = [.done [1]]
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), on ISO C18 6.5.9p6: the text 'requires such pointers [one past the end of one array object and the start of an immediately following one] to compare equal'.
  - [Memarian et al. 2019] (full entry under **Evidence**)
  - [Jung 2020] (full entry under **Evidence**)
- **Design question:** Which pointer-substitution optimizations (GVN on pointers after p == q or (int)p == (int)q) a compiler may perform under each provenance model. (Reference point: the boundary situation behind R1b-R3b.)
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — ISO C18 6.5.9p6, as quoted in P2318R0, "requires such pointers [one past the end of one array object and the start of an immediately following one] to compare equal"; the toy's address-only `ptrEq` and adjacent bump allocation make this situation occur deterministically. Real allocators need not place allocations adjacently, and semantics in which such pointers may compare unequal or nondeterministically are not covered. This is a correspondence argument, not a kernel-checked claim.

### R1b: address equality substitution unsound strict exposed

- **Kind / tier / depth:** counterexample · T0 · definitional. Tier rationale: The one-past-the-end pointer-substitution miscompilation is a published example (Memarian et al. 2019; Lee et al. 2018; Jung 2020); restated as a decidable counterexample over an explicit transformation relation.
- **Plain claim:** In the strict and the exposed model, the transformation SubstAddrEq (replace the reads of register q in one instruction by reads of p, when p and q hold pointers with equal addresses in every reachable state at that point) is not sound: with p one past A's end and q B's start, replacing the pointer operand of a store gives a target that is UB while the source outputs [1, 7]. In the flat model the same rewrite is a refinement (both output [1, 7]).

Lean statements (`R1b`):

```lean
-- lean/ToyProv/OnePast.lean:60-62
-- substAddrEq_counterexample_strict  (ToyProv/OnePast.lean:60)
theorem substAddrEq_counterexample_strict :
    SubstAddrEq .strict r1Src r1Tgt ∧ ¬ Refines .strict r1Tgt r1Src ∧
      beh .strict r1Src = [.done [1, 7]] ∧ beh .strict r1Tgt = [.ub]

-- lean/ToyProv/OnePast.lean:66-68
-- substAddrEq_counterexample_exposed  (ToyProv/OnePast.lean:66)
theorem substAddrEq_counterexample_exposed :
    SubstAddrEq .exposed r1Src r1Tgt ∧ ¬ Refines .exposed r1Tgt r1Src ∧
      beh .exposed r1Src = [.done [1, 7]] ∧ beh .exposed r1Tgt = [.ub]

-- lean/ToyProv/OnePast.lean:71
-- substAddrEq_not_sound_strict  (ToyProv/OnePast.lean:71)
theorem substAddrEq_not_sound_strict : ¬ Sound .strict SubstAddrEq

-- lean/ToyProv/OnePast.lean:74
-- substAddrEq_not_sound_exposed  (ToyProv/OnePast.lean:74)
theorem substAddrEq_not_sound_exposed : ¬ Sound .exposed SubstAddrEq
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/OnePast.lean
/-- Source: store through `q` (register 1, B's start). -/
def r1Src : Prog := r1Pre ++ .store 1 4 :: r1Post
-- ToyProv/OnePast.lean
/-- Target: the store's pointer operand `q` replaced by the address-equal `p` (register 2,
one past A's end). -/
def r1Tgt : Prog := r1Pre ++ (Instr.store 1 4).substUse 1 2 :: r1Post
-- ToyProv/OnePast.lean
/-- Code before the rewrite point: A, B, `p := A + 2`, observe `p == q` (it is `1`), `t := 7`. -/
def r1Pre : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptrEq 3 2 1, .obs 3, .const 4 7]
-- ToyProv/OnePast.lean
/-- Code after the rewrite point: read B back and observe it. -/
def r1Post : Prog := [.load 5 .int 1, .obs 5]
```

Hypothesis ledger: none — the statement is a closed, fully evaluated instance.

- **Non-vacuity witness:** r1Src / r1Tgt satisfy SubstAddrEq in all three models. Lean: `substAddrEq_example_refines_flat`.
- **Positive control** (a nearby setting where the negative conclusion fails): `substAddrEq_example_refines_flat`.

```lean
-- lean/ToyProv/OnePast.lean:79-81
-- substAddrEq_example_refines_flat  (ToyProv/OnePast.lean:79)
theorem substAddrEq_example_refines_flat :
    SubstAddrEq .flat r1Src r1Tgt ∧ Refines .flat r1Tgt r1Src ∧ beh .flat r1Tgt = beh .flat r1Src ∧
      beh .flat r1Src = [.done [1, 7]]
```

- **Prior art:**
  - [Memarian et al. 2019] (full entry under **Evidence**)
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Jung 2020] (full entry under **Evidence**)
- **Design question:** Which pointer-substitution optimizations (GVN on pointers after p == q or (int)p == (int)q) a compiler may perform under each provenance model.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — This is the one-past-the-end pointer-substitution example discussed by Memarian et al. (2019), Lee et al. (2018) and Jung (2020), reproduced in the toy; whether a given compiler performs this rewrite is not examined. This is a correspondence argument, not a kernel-checked claim.

### R1c: in bounds address equality substitution sound

- **Kind / tier / depth:** theorem · T0 · substantive. Tier rationale: Analogue, for these three models, of the in-bounds condition of Lee et al.'s Coq-proved Theorem C.5 (twin-allocation model); restated over this semantics.
- **Plain claim:** In every model, replacing the reads of q by reads of p in one instruction is a refinement when, in every reachable state at that point, p and q hold pointers with equal addresses and both are in bounds of a live allocation (inBoundsC: a one-byte access through each is allowed, i.e. base ≤ address < base + size for a live allocation, which in strict/exposed must be the pointer's own provenance; the start address is included, one past the end is excluded). In strict/exposed, disjointness of live allocations forces equal provenance, so the two registers hold the same value.

Lean statement (`R1c`):

```lean
-- lean/ToyProv/OnePast.lean:91
-- substAddrEqInBounds_sound  (ToyProv/OnePast.lean:91)
theorem substAddrEqInBounds_sound (m : Model) : Sound m SubstAddrEqInBounds
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/OnePast.lean
/-- Code before the rewrite point: A; `q := A`; `p := (A + 1) - 1`. -/
def r1cPreNV : Prog := [.alloc 0 2, .copy 1 0, .offset 2 0 1, .offset 2 2 (-1), .const 3 7]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `SubstAddrEqInBounds side condition, conjunct addrEqC p q` | Without it, p and q may be two different in-bounds pointers (to different allocations), and reading through p instead of q reads a different allocation. | tight | `substAddrEqInBounds_addrEq_needed` (ToyProv/OnePast.lean:179) |
| `SubstAddrEqInBounds side condition, conjunct inBoundsC m p` | Without it, p may be a one-past-the-end pointer with another allocation's provenance (R1b's pair). | tight | `substAddrEqInBounds_p_needed` (ToyProv/OnePast.lean:152) |
| `SubstAddrEqInBounds side condition, conjunct inBoundsC m q` | Without it, q may be a one-past-the-end pointer that the source moves back into its own allocation, which p cannot do. | tight | `substAddrEqInBounds_q_needed` (ToyProv/OnePast.lean:165) |

- **Non-vacuity witness:** q := A and p := (A + 1) - 1: equal addresses, both in bounds, in strict and exposed. Lean: `substAddrEqInBounds_nonvacuous`.

```lean
-- lean/ToyProv/OnePast.lean:193-198
-- substAddrEqInBounds_nonvacuous  (ToyProv/OnePast.lean:193)
theorem substAddrEqInBounds_nonvacuous :
    SubstAddrEqInBounds .strict (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4])
      (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) ∧
      SubstAddrEqInBounds .exposed (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4])
        (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) ∧
      beh .strict (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) = [.done [7]]
```

- **Prior art:**
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Memarian et al. 2019] (full entry under **Evidence**)
- **Design question:** Which pointer-substitution optimizations (GVN on pointers after p == q or (int)p == (int)q) a compiler may perform under each provenance model.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — The side condition plays the role of the in-bounds (dereferenceable) condition under which Lee et al. (2018, Theorem C.5, Coq) prove GVN on pointers sound in their twin-allocation model; the toy's result is the analogue for its own three models, relying on disjoint live allocations. This is a correspondence argument, not a kernel-checked claim.

### R2a: integer equality pointer substitution unsound even when exposed

- **Kind / tier / depth:** counterexample · T0 · definitional. Tier rationale: The (int)p == (int)q pointer-substitution examples are published (Memarian et al. 2019; Jung 2020); here with exposure made explicit in the side condition.
- **Plain claim:** In the strict and the exposed model, the transformation SubstIntEq (as SubstAddrEq, with the additional side condition that the provenances of both pointers are in the exposed set in every reachable state at that point) is not sound: on a program that also casts both pointers to integers and observes them equal, replacing q (B's start) by p (one past A's end) in a store gives a UB target while the source outputs [1, 7]. Exposure does not rescue pointer substitution because the substituted pointer keeps its own provenance. In the flat model the same rewrite is a refinement.

Lean statements (`R2a`):

```lean
-- lean/ToyProv/IntEq.lean:36-38
-- substIntEq_counterexample_strict  (ToyProv/IntEq.lean:36)
theorem substIntEq_counterexample_strict :
    SubstIntEq .strict r2Src r2Tgt ∧ ¬ Refines .strict r2Tgt r2Src ∧
      beh .strict r2Src = [.done [1, 7]] ∧ beh .strict r2Tgt = [.ub]

-- lean/ToyProv/IntEq.lean:43-45
-- substIntEq_counterexample_exposed  (ToyProv/IntEq.lean:43)
theorem substIntEq_counterexample_exposed :
    SubstIntEq .exposed r2Src r2Tgt ∧ ¬ Refines .exposed r2Tgt r2Src ∧
      beh .exposed r2Src = [.done [1, 7]] ∧ beh .exposed r2Tgt = [.ub]

-- lean/ToyProv/IntEq.lean:48
-- substIntEq_not_sound_strict  (ToyProv/IntEq.lean:48)
theorem substIntEq_not_sound_strict : ¬ Sound .strict SubstIntEq

-- lean/ToyProv/IntEq.lean:51
-- substIntEq_not_sound_exposed  (ToyProv/IntEq.lean:51)
theorem substIntEq_not_sound_exposed : ¬ Sound .exposed SubstIntEq
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/IntEq.lean
/-- Source: store through `q` (B's start). -/
def r2Src : Prog := r2Pre ++ .store 1 6 :: r2Post
-- ToyProv/IntEq.lean
/-- Target: `q` replaced by `p` (one past A's end), justified by `(int)p == (int)q`. -/
def r2Tgt : Prog := r2Pre ++ (Instr.store 1 6).substUse 1 2 :: r2Post
-- ToyProv/IntEq.lean
/-- A, B, `p := A + 2`, cast both to integers, observe that the integers are equal, `t := 7`. -/
def r2Pre : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptr2int 3 2, .ptr2int 4 1, .intEq 5 3 4, .obs 5, .const 6 7]
-- ToyProv/IntEq.lean
def r2Post : Prog := [.load 7 .int 1, .obs 7]
```

Hypothesis ledger: none — the statement is a closed, fully evaluated instance.

- **Non-vacuity witness:** r2Src / r2Tgt satisfy SubstIntEq (including bothExposedC) in all models. Lean: `substIntEq_example_refines_flat`.
- **Positive control** (a nearby setting where the negative conclusion fails): `substIntEq_example_refines_flat`.

```lean
-- lean/ToyProv/IntEq.lean:55-57
-- substIntEq_example_refines_flat  (ToyProv/IntEq.lean:55)
theorem substIntEq_example_refines_flat :
    SubstIntEq .flat r2Src r2Tgt ∧ Refines .flat r2Tgt r2Src ∧
      beh .flat r2Src = [.done [1, 7]] ∧ beh .flat r2Tgt = [.done [1, 7]]
```

- **Prior art:**
  - [Memarian et al. 2019] (full entry under **Evidence**)
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), definition of PNVI-ae: 'A storage instance is deemed exposed by a conversion of a pointer to it to an integer type, by a read (at non-pointer type) of the representation of the pointer, or by an output of the pointer using "%p".'
  - [Jung 2020] (full entry under **Evidence**)
- **Design question:** Which pointer-substitution optimizations (GVN on pointers after p == q or (int)p == (int)q) a compiler may perform under each provenance model.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — The `(int)p == (int)q` substitution examples are published (Memarian et al. 2019; Jung 2020); the side condition `bothExposedC` models PNVI-ae's exposure by pointer-to-integer conversion. The toy shows only that exposure does not rescue substituting already-formed pointers in this semantics. This is a correspondence argument, not a kernel-checked claim.

### R2b: int2ptr fold refines exposed if no other candidate

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: The PNVI-ae-udi literature discusses when the round-trip fold is valid informally, and VIP (Coq) verifies programs that state the intended provenance explicitly; no mechanized statement of this fold condition for an angelic exposed-provenance semantics was found.
- **Plain claim:** In the exposed model, replacing d := int2ptr k by d := p is a refinement provided that, in every reachable state at that point, k holds p's address as an integer (hk) and every allocation that int2ptr could pick for that address (exposed, live, address within [base, base + size]) is p's own provenance (hc) - either p's allocation is the unique such candidate, or there is no candidate at all, in which case the source pointer has no provenance and the target pointer has p's.

Lean statement (`R2b`):

```lean
-- lean/ToyProv/IntEq.lean:101-105
-- int2ptrToCopy_refines_exposed_of_intIsAddrOf_of_candSubProv  (ToyProv/IntEq.lean:101)
theorem int2ptrToCopy_refines_exposed_of_intIsAddrOf_of_candSubProv
    (pre post : Prog) (d k p : Reg)
    (hk : AllAfter .exposed pre (intIsAddrOfC k p))
    (hc : AllAfter .exposed pre (candSubProvC p)) :
    Refines .exposed (pre ++ .copy d p :: post) (pre ++ .int2ptr d k :: post)
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/IntEq.lean
def r2bPreNV : Prog := [.alloc 0 2, .ptr2int 1 0]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hk : AllAfter .exposed pre (intIsAddrOfC k p)` | The integer must equal p's address; otherwise the cast may pick an unrelated allocation. | tight | `int2ptrToCopy_intIsAddrOf_needed` (ToyProv/IntEq.lean:188) |
| `hc : AllAfter .exposed pre (candSubProvC p)` | If another exposed live allocation contains the address (one-past-the-end of A = start of B), the source's cast can angelically pick it while the target keeps p's provenance; p's allocation being live, exposed and in range is not enough. | tight | `int2ptrToCopy_candSubProv_needed` (ToyProv/IntEq.lean:200) |

- **Non-vacuity witness:** After k := ptr2int A, A is the only candidate for its own address and the fold preserves the output [5]. The case with no candidate (A not exposed, so `candidates` is empty) is witnessed by `int2ptrToCopy_refines_exposed_no_candidate_example`, quoted below with its programs. Lean: `int2ptrToCopy_refines_exposed_nonvacuous`, `int2ptrToCopy_refines_exposed_no_candidate_example`.

```lean
-- lean/ToyProv/IntEq.lean:209-214
-- int2ptrToCopy_refines_exposed_nonvacuous  (ToyProv/IntEq.lean:209)
theorem int2ptrToCopy_refines_exposed_nonvacuous :
    AllAfter .exposed r2bPreNV (intIsAddrOfC 1 0) ∧ AllAfter .exposed r2bPreNV (candSubProvC 0) ∧
      Refines .exposed (r2bPreNV ++ .copy 2 0 :: [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4])
        (r2bPreNV ++ .int2ptr 2 1 :: [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4]) ∧
      beh .exposed (r2bPreNV ++ .int2ptr 2 1 :: [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4]) =
        [.done [5]]
```

```lean
-- lean/ToyProv/IntEq.lean:217-219
/-- A (unexposed, at 16), B, C; `k := 16`; `q := int2ptr k` (no candidate, so no provenance) is
stored into B. -/
def r2bPreTorn : Prog := [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3, .store 1 4]
-- lean/ToyProv/IntEq.lean:220-221
/-- Store `d` into C, copy B's first byte over C's first byte, load C at integer type. -/
def r2bPostTorn : Prog := [.store 2 5, .memcpy 2 1 1, .load 6 .int 2, .obs 6]

-- lean/ToyProv/IntEq.lean:227-232
-- int2ptrToCopy_refines_exposed_no_candidate_example  (ToyProv/IntEq.lean:227)
theorem int2ptrToCopy_refines_exposed_no_candidate_example :
    AllAfter .exposed r2bPreTorn (intIsAddrOfC 3 0) ∧ AllAfter .exposed r2bPreTorn (candSubProvC 0) ∧
      AllAfter .exposed r2bPreTorn (fun s => (candidates s 16).isEmpty) ∧
      Refines .exposed (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) ∧
      beh .exposed (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) = [.done [16]] ∧
      beh .exposed (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) = [.done [16]]
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), on one-past integer-to-pointer casts: 'for PNVI-plain and PNVI-ae we follow the stricter semantics. PNVI-ae-udi, however, is designed to permit a cast of a one-past pointer to integer and back to recover the original provenance'; ambiguous cases are resolved by leaving 'the provenance of pointer values resulting from such casts unknown until the first operation (e.g. an access, pointer arithmetic, or pointer relational comparison) that disambiguates them', 'allowing one or the other (but not both) to be used, so long as that is done consistently'.
  - [Jung 2020] (full entry under **Evidence**)
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Lepigre et al. 2022] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
- **Design question:** When an optimizer may fold or introduce integer-pointer round trips (inttoptr(ptrtoint p) vs p) under strict and exposed provenance.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — In PNVI-ae-udi (P2318R0) a round trip through an integer can recover the original provenance and ambiguity arises only at an address shared by two allocations; `candSubProvC` is the toy's way of excluding that ambiguity. MiniRust's `int2ptr` has no address check, so this side condition does not transfer to MiniRust. This is a correspondence argument, not a kernel-checked claim.

### R2c: identical value substitution sound all models

- **Kind / tier / depth:** theorem · T0 · shallow. Tier rationale: That GVN on values with no hidden state is behaviour-preserving is standard (Lee et al. 2018 make integers provenance-free so that 'GVN for integers becomes sound'); restated over this semantics.
- **Plain claim:** In every model, replacing the reads of register q by reads of p in one instruction preserves behaviour (equality of behaviour, not merely refinement) whenever q and p hold identical values in every reachable state at that point; in particular substituting one integer for an equal integer (integer GVN after (int)p == (int)q) is sound even in the exposed model at the one-past-the-end boundary.

Lean statements (`R2c`):

```lean
-- lean/ToyProv/IntEq.lean:67-69
-- substSameVal_beh_eq  (ToyProv/IntEq.lean:67)
theorem substSameVal_beh_eq (m : Model) (pre post : Prog) (i : Instr) (q p : Reg)
    (h : AllAfter m pre (sameValC p q)) :
    beh m (pre ++ i.substUse q p :: post) = beh m (pre ++ i :: post)

-- lean/ToyProv/IntEq.lean:77
-- substSameVal_sound  (ToyProv/IntEq.lean:77)
theorem substSameVal_sound (m : Model) : Sound m SubstSameVal
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/IntEq.lean
/-- **R2c non-vacuity, at the one-past-the-end boundary.** After `ip := (int)(A + 2)` and
`iq := (int)B`, replacing `iq` by `ip` as the operand of `int2ptr` is an instance of
`SubstSameVal` in the exposed model, and behaviour is unchanged (both output `[7]`). -/
def r2cPre : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptr2int 3 2, .ptr2int 4 1]
-- ToyProv/IntEq.lean
def r2cPost : Prog := [.const 6 7, .store 5 6, .load 7 .int 1, .obs 7]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h : AllAfter m pre (sameValC p q)` | Identical values (for pointers: equal provenance as well as address). Weakening it to equal addresses gives SubstAddrEq, which is unsound in strict/exposed. | tight | `substAddrEq_counterexample_strict` (ToyProv/OnePast.lean:60) |

- **Non-vacuity witness:** Integer substitution iq -> ip after ip := (int)(A+2), iq := (int)B in the exposed model. Lean: `substSameVal_int_boundary_example`.

```lean
-- lean/ToyProv/IntEq.lean:86-89
-- substSameVal_int_boundary_example  (ToyProv/IntEq.lean:86)
theorem substSameVal_int_boundary_example :
    SubstSameVal .exposed (r2cPre ++ .int2ptr 5 4 :: r2cPost) (r2cPre ++ (Instr.int2ptr 5 4).substUse 4 3 :: r2cPost) ∧
      beh .exposed (r2cPre ++ (Instr.int2ptr 5 4).substUse 4 3 :: r2cPost) = [.done [7]] ∧
      beh .exposed (r2cPre ++ .int2ptr 5 4 :: r2cPost) = [.done [7]]
```

- **Prior art:**
  - [Jung 2020] (full entry under **Evidence**)
  - [Lee et al. 2018] (full entry under **Evidence**)
- **Design question:** Which pointer-substitution optimizations (GVN on pointers after p == q or (int)p == (int)q) a compiler may perform under each provenance model.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Lee et al. (2018) make integers provenance-free so that GVN for integers becomes sound; the toy's integers carry no provenance by construction, so the result says nothing about semantics in which integers carry provenance. This is a correspondence argument, not a kernel-checked claim.

### R3a: roundtrip interchangeable exposed if unique candidate

- **Kind / tier / depth:** theorem · T1 · shallow. Tier rationale: The PNVI-ae-udi literature treats the unambiguous case informally; stated and proved here for one semantics.
- **Plain claim:** In the exposed model, d := int2ptr k and d := p are interchangeable (equal behaviour) when, in every reachable state at that point, k holds p's address (hk) and the int2ptr candidates for that address are exactly p's own provenance (hc: p's allocation is live, exposed, contains the address in its closed range and is the only such allocation, or p has no provenance and there is no candidate).

Lean statement (`R3a`):

```lean
-- lean/ToyProv/RoundTrip.lean:23-27
-- int2ptrToCopy_beh_eq_exposed_of_intIsAddrOf_of_candEqProv  (ToyProv/RoundTrip.lean:23)
theorem int2ptrToCopy_beh_eq_exposed_of_intIsAddrOf_of_candEqProv
    (pre post : Prog) (d k p : Reg)
    (hk : AllAfter .exposed pre (intIsAddrOfC k p))
    (hc : AllAfter .exposed pre (candEqProvC p)) :
    beh .exposed (pre ++ .copy d p :: post) = beh .exposed (pre ++ .int2ptr d k :: post)
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/IntEq.lean
def r2bPreNV : Prog := [.alloc 0 2, .ptr2int 1 0]
-- ToyProv/RoundTrip.lean
/-- **R3a non-vacuity.** After `k := (int)A` (A alone exposed), the hypotheses hold and both
programs output `[5]`. -/
def r3PostNV : Prog := [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hk : AllAfter .exposed pre (intIsAddrOfC k p)` | Ties the integer to p's address. | tight | `int2ptrToCopy_beh_eq_intIsAddrOf_needed` (ToyProv/RoundTrip.lean:46) |
| `hc : AllAfter .exposed pre (candEqProvC p)` | Uniqueness: at the one-past-the-end boundary with the next allocation exposed, the round trip and p behave differently. | tight | `roundTrip_fold_counterexample_exposed_boundary` (ToyProv/RoundTrip.lean:56) |

- **Non-vacuity witness:** After k := ptr2int A with only A exposed; both programs output [5]. Lean: `int2ptrToCopy_beh_eq_nonvacuous`.

```lean
-- lean/ToyProv/RoundTrip.lean:100-102
-- int2ptrToCopy_beh_eq_nonvacuous  (ToyProv/RoundTrip.lean:100)
theorem int2ptrToCopy_beh_eq_nonvacuous :
    AllAfter .exposed r2bPreNV (intIsAddrOfC 1 0) ∧ AllAfter .exposed r2bPreNV (candEqProvC 0) ∧
      beh .exposed (r2bPreNV ++ .copy 2 0 :: r3PostNV) = [.done [5]]
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), on one-past integer-to-pointer casts: 'for PNVI-plain and PNVI-ae we follow the stricter semantics. PNVI-ae-udi, however, is designed to permit a cast of a one-past pointer to integer and back to recover the original provenance'; ambiguous cases are resolved by leaving 'the provenance of pointer values resulting from such casts unknown until the first operation (e.g. an access, pointer arithmetic, or pointer relational comparison) that disambiguates them', 'allowing one or the other (but not both) to be used, so long as that is done consistently'.
  - [Jung 2020] (full entry under **Evidence**)
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Lepigre et al. 2022] (full entry under **Evidence**)
- **Design question:** When an optimizer may fold or introduce integer-pointer round trips (inttoptr(ptrtoint p) vs p) under strict and exposed provenance.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Corresponds to the unambiguous case of PNVI-ae-udi's one-past round trip (P2318R0); MiniRust's address-unrestricted `int2ptr` does not satisfy the toy's candidate restriction, so `candEqProvC` does not transfer to MiniRust. This is a correspondence argument, not a kernel-checked claim.

### R3b: roundtrip fold unsound exposed at one past boundary

- **Kind / tier / depth:** counterexample · T1 · definitional. Tier rationale: Matches the round-trip-removal step identified as incorrect in Jung (2020) and the user-disambiguation case of PNVI-ae-udi; here decidable instances, including one with an in-bounds base pointer.
- **Plain claim:** In the exposed model, folding int2ptr((int)p) into p is not a refinement even though p's allocation A is live, exposed by the cast, and contains p's address in its closed range: with p one past A's end and the adjacent B exposed, the source's cast can pick B and outputs [7] while the target's store through p is UB. The same happens for p = B's start (in bounds of B: base ≤ address < base + size holds with address = base) when A is exposed and later code moves the pointer back into A.

Lean statements (`R3b`):

```lean
-- lean/ToyProv/RoundTrip.lean:56-61
-- roundTrip_fold_counterexample_exposed_boundary  (ToyProv/RoundTrip.lean:56)
theorem roundTrip_fold_counterexample_exposed_boundary :
    Int2ptrToCopy .exposed (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) (r2bPreRT ++ .copy 4 2 :: r2bPostRT) ∧
      AllAfter .exposed r2bPreRT (provIsCandC 2) ∧
      ¬ Refines .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) ∧
      beh .exposed (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) = [.done [7]] ∧
      beh .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT) = [.ub]

-- lean/ToyProv/RoundTrip.lean:64
-- int2ptrToCopy_not_sound_exposed  (ToyProv/RoundTrip.lean:64)
theorem int2ptrToCopy_not_sound_exposed : ¬ Sound .exposed Int2ptrToCopy

-- lean/ToyProv/RoundTrip.lean:87-93
-- roundTrip_fold_counterexample_exposed_base_pointer  (ToyProv/RoundTrip.lean:87)
theorem roundTrip_fold_counterexample_exposed_base_pointer :
    Int2ptrToCopy .exposed (r3PreBase ++ .int2ptr 4 3 :: r3PostBase) (r3PreBase ++ .copy 4 1 :: r3PostBase) ∧
      AllAfter .exposed r3PreBase (fun s => match s.regs 1 with
        | some (.ptr x) => canAccess .exposed s x 1 | _ => false) ∧
      AllAfter .exposed r3PreBase (provIsCandC 1) ∧ ¬ AllAfter .exposed r3PreBase (candSubProvC 1) ∧
      beh .exposed (r3PreBase ++ .int2ptr 4 3 :: r3PostBase) = [.done [7]] ∧
      beh .exposed (r3PreBase ++ .copy 4 1 :: r3PostBase) = [.ub]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/IntEq.lean
/-- A and B adjacent; B exposed; `p := A + 2` and `k := (int)p` (which exposes A). -/
def r2bPreRT : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 9 1, .offset 2 0 2, .ptr2int 3 2]
-- ToyProv/IntEq.lean
def r2bPostRT : Prog := [.const 5 7, .store 4 5, .load 6 .int 1, .obs 6]
-- ToyProv/RoundTrip.lean
/-- A (16..18) exposed, B (18..20); `k := (int)B` (exposes B). `p` is B's *start*, in bounds
of B (`base ≤ address < base + size` holds with `address = base`). -/
def r3PreBase : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 9 0, .ptr2int 3 1]
-- ToyProv/RoundTrip.lean
/-- Move the cast pointer back by 2 (into A) and store through it; read A. -/
def r3PostBase : Prog := [.offset 5 4 (-2), .const 6 7, .store 5 6, .load 7 .int 0, .obs 7]
```

Hypothesis ledger: none — the statement is a closed, fully evaluated instance.

- **Non-vacuity witness:** The r2bPreRT program pair satisfies Int2ptrToCopy and provIsCandC. Lean: `roundTrip_fold_counterexample_exposed_boundary`.
- **Positive control** (a nearby setting where the negative conclusion fails): `roundTrip_fold_boundary_flat_strict`.

```lean
-- lean/ToyProv/RoundTrip.lean:70-74
-- roundTrip_fold_boundary_flat_strict  (ToyProv/RoundTrip.lean:70)
theorem roundTrip_fold_boundary_flat_strict :
    Int2ptrToCopy .flat (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) (r2bPreRT ++ .copy 4 2 :: r2bPostRT) ∧
      Refines .flat (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) ∧
      beh .flat (r2bPreRT ++ .copy 4 2 :: r2bPostRT) = [.done [7]] ∧
      beh .strict (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) = [.ub]
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), on one-past integer-to-pointer casts: 'for PNVI-plain and PNVI-ae we follow the stricter semantics. PNVI-ae-udi, however, is designed to permit a cast of a one-past pointer to integer and back to recover the original provenance'; ambiguous cases are resolved by leaving 'the provenance of pointer values resulting from such casts unknown until the first operation (e.g. an access, pointer arithmetic, or pointer relational comparison) that disambiguates them', 'allowing one or the other (but not both) to be used, so long as that is done consistently'.
  - [Jung 2020] (full entry under **Evidence**)
- **Design question:** When an optimizer may fold or introduce integer-pointer round trips (inttoptr(ptrtoint p) vs p) under strict and exposed provenance.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Matches the round-trip-removal step that Jung (2020) identifies as the incorrect one in his three-step miscompilation chain, and PNVI-ae-udi's ambiguous one-past case (P2318R0). The source's success depends on angelic resolution, which the toy uses as its stand-in for PNVI-ae-udi's delayed disambiguation. This is a correspondence argument, not a kernel-checked claim.

### R3c: roundtrip not equivalent strict

- **Kind / tier / depth:** counterexample · T0 · definitional. Tier rationale: Immediate from strict provenance (int2ptr yields no provenance); restated as a concrete program.
- **Plain claim:** In the strict model int2ptr(ptr2int p) is not interchangeable with p: introducing the round trip (the single-instruction rewrite d := p -> d := int2ptr k with k := (int)p computed earlier) turns a program that outputs [7] into a UB program, so CopyToInt2ptr is unsound in strict; in the exposed model the same pair has equal behaviour.

Lean statements (`R3c`):

```lean
-- lean/ToyProv/RoundTrip.lean:114-118
-- roundTrip_counterexample_strict  (ToyProv/RoundTrip.lean:114)
theorem roundTrip_counterexample_strict :
    CopyToInt2ptr .strict (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      ¬ Refines .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) ∧
      beh .strict (r3Pre ++ .copy 2 0 :: r3Post) = [.done [7]] ∧
      beh .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) = [.ub]

-- lean/ToyProv/RoundTrip.lean:121
-- copyToInt2ptr_not_sound_strict  (ToyProv/RoundTrip.lean:121)
theorem copyToInt2ptr_not_sound_strict : ¬ Sound .strict CopyToInt2ptr
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/RoundTrip.lean
def r3Pre : Prog := [.alloc 0 2, .ptr2int 1 0]
-- ToyProv/RoundTrip.lean
def r3Post : Prog := [.const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
```

Hypothesis ledger: none — the statement is a closed, fully evaluated instance.

- **Non-vacuity witness:** r3Pre program pair. Lean: `roundTrip_counterexample_strict`.
- **Positive control** (a nearby setting where the negative conclusion fails): `roundTrip_example_exposed`.

```lean
-- lean/ToyProv/RoundTrip.lean:126-127
-- roundTrip_example_exposed  (ToyProv/RoundTrip.lean:126)
theorem roundTrip_example_exposed :
    beh .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) = beh .exposed (r3Pre ++ .copy 2 0 :: r3Post)
```

- **Prior art:**
  - [Rust 1.84.0 documentation] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
  - [Lepigre et al. 2022] (full entry under **Evidence**)
- **Design question:** When an optimizer may fold or introduce integer-pointer round trips (inttoptr(ptrtoint p) vs p) under strict and exposed provenance.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — The strict model's `int2ptr` corresponds to Rust's `std::ptr::without_provenance(addr)` (no provenance; non-zero-sized accesses through it are UB), not to Rust's `as` casts, which the Rust 1.84.0 documentation equates with `with_exposed_provenance`. This is a correspondence argument, not a kernel-checked claim.

### R4a: forwarding across cast store unsound exposed flat

- **Kind / tier / depth:** counterexample · T1 · shallow. Tier rationale: Folklore about inttoptr and alias analysis (Lee et al. 2018; Jung 2022); stated as a decidable counterexample, with the strict model's vacuity made explicit. Depth: the four closed statements are evaluations (`decide`), but `forwardAcrossCast_strict_src_ub` quantifies over all program pairs and needs a short argument over an arbitrary prefix (single-step and prefix execution lemmas), so the card as a whole is `shallow`.
- **Plain claim:** Store-to-load forwarding across a store through r := int2ptr k (ForwardAcrossCast: the optimizer's heuristic that a freshly cast pointer r, as a register distinct from a, does not alias a) is not a refinement in the exposed model: with k := (int)A the cast picks A, the source outputs [9] and the target [5]; the same happens in the flat model. In the strict model, for every pair of programs src, tgt matching ForwardAcrossCast (hypothesis h of forwardAcrossCast_strict_src_ub), both src and tgt are UB; such pairs exist (r4Src / r4Tgt, forwardAcrossCast_example_refines_strict). Hence the strict-model soundness of this forwarding is vacuous: it holds only because every matching source is UB, and it says nothing about defined programs.

Lean statements (`R4a`):

```lean
-- lean/ToyProv/Forwarding.lean:27-31
-- forwardAcrossCast_counterexample  (ToyProv/Forwarding.lean:27)
theorem forwardAcrossCast_counterexample :
    ForwardAcrossCast .exposed r4Src r4Tgt ∧ ¬ Refines .exposed r4Tgt r4Src ∧
      beh .exposed r4Src = [.done [9]] ∧ beh .exposed r4Tgt = [.done [5]] ∧
      ForwardAcrossCast .flat r4Src r4Tgt ∧ ¬ Refines .flat r4Tgt r4Src ∧
      beh .flat r4Src = [.done [9]] ∧ beh .flat r4Tgt = [.done [5]]

-- lean/ToyProv/Forwarding.lean:37
-- forwardAcrossCast_not_sound_exposed  (ToyProv/Forwarding.lean:37)
theorem forwardAcrossCast_not_sound_exposed : ¬ Sound .exposed ForwardAcrossCast

-- lean/ToyProv/Forwarding.lean:40
-- forwardAcrossCast_not_sound_flat  (ToyProv/Forwarding.lean:40)
theorem forwardAcrossCast_not_sound_flat : ¬ Sound .flat ForwardAcrossCast

-- lean/ToyProv/Forwarding.lean:50-54
-- forwardAcrossCast_counterexample_guessed_address  (ToyProv/Forwarding.lean:50)
theorem forwardAcrossCast_counterexample_guessed_address :
    ForwardAcrossCast .exposed (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6])
      (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]) ∧
      ¬ Refines .exposed (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6])
        (r4PreGuess ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6])

-- lean/ToyProv/Forwarding.lean:160-161
-- forwardAcrossCast_strict_src_ub  (ToyProv/Forwarding.lean:160)
theorem forwardAcrossCast_strict_src_ub (src tgt : Prog) (h : ForwardAcrossCast .strict src tgt) :
    beh .strict src = [.ub] ∧ beh .strict tgt = [.ub]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Forwarding.lean
def r4Src : Prog := r4Pre ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]
-- ToyProv/Forwarding.lean
def r4Tgt : Prog := r4Pre ++ [.int2ptr 5 2, .store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]
-- ToyProv/Forwarding.lean
/-- As `r4Pre`, but `(int)A` is discarded and the cast's operand is the constant 16 (A's address
under the toy's deterministic allocator). -/
def r4PreGuess : Prog := [.alloc 0 2, .ptr2int 1 0, .const 2 16, .const 3 5, .const 4 9]
-- ToyProv/Forwarding.lean
/-- A (never exposed), B (exposed), `r := int2ptr (int)B`, `v := 5`, `w := 9`. -/
def r4cPreNV : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 2 1, .int2ptr 5 2, .const 3 5, .const 4 9]
-- ToyProv/Forwarding.lean
/-- A at 16; `k := (int)A` (this exposes A); `v := 5`, `w := 9`. -/
def r4Pre : Prog := [.alloc 0 2, .ptr2int 2 0, .const 3 5, .const 4 9]
```

Hypothesis ledger (per statement):

- `forwardAcrossCast_counterexample`, `forwardAcrossCast_not_sound_exposed`, `forwardAcrossCast_not_sound_flat`, `forwardAcrossCast_counterexample_guessed_address`: none — each is a closed, fully evaluated statement.
- `forwardAcrossCast_strict_src_ub`: universally quantified over programs `src` and `tgt`, with exactly one hypothesis:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h : ForwardAcrossCast .strict src tgt (forwardAcrossCast_strict_src_ub)` | Restricts `src`, `tgt` to pairs that match the cast window in the strict model; without it the programs are arbitrary. | tight | `forwardAcrossCast_strict_src_ub_h_needed` (ToyProv/LedgerWitnesses.lean:32). Witness class: a closed two-instruction program without casts, `src = tgt = constObsProg`, which is defined in strict (outputs `[1]`) and does not match the window. |

```lean
-- lean/ToyProv/LedgerWitnesses.lean:21-23
/-- A two-instruction program: write the integer 1 into register 0 and output it. It contains no
cast, so it matches neither `ForwardAcrossCast` nor `DSEAcrossCast`. -/
def constObsProg : Prog := [.const 0 1, .obs 0]

-- lean/ToyProv/LedgerWitnesses.lean:32-34
-- forwardAcrossCast_strict_src_ub_h_needed  (ToyProv/LedgerWitnesses.lean:32)
theorem forwardAcrossCast_strict_src_ub_h_needed :
    ¬ ForwardAcrossCast .strict constObsProg constObsProg ∧
      ¬ (beh .strict constObsProg = [.ub] ∧ beh .strict constObsProg = [.ub])
```

What is vacuous: the hypothesis `h` is satisfiable (the non-vacuity witness below), but the theorem's conclusion is that every pair satisfying it is UB on both sides. Consequently the strict-model soundness of forwarding (`forwardAcrossCast_sound_strict`, R6g) is a **vacuous** ✓. The closed statements of this card are not vacuous: their exposed and flat sources are defined.

- **Non-vacuity witness:** For the closed statements: r4Src / r4Tgt satisfy ForwardAcrossCast in the exposed and flat models, where both sources are defined (`forwardAcrossCast_counterexample`). For `forwardAcrossCast_strict_src_ub`: the same pair satisfies its hypothesis `h` (`ForwardAcrossCast .strict r4Src r4Tgt`), and both sides are UB in strict, as the theorem says (`forwardAcrossCast_example_refines_strict`). Lean: `forwardAcrossCast_counterexample`, `forwardAcrossCast_example_refines_strict`.

```lean
-- lean/ToyProv/Forwarding.lean:60-62
-- forwardAcrossCast_example_refines_strict  (ToyProv/Forwarding.lean:60)
theorem forwardAcrossCast_example_refines_strict :
    ForwardAcrossCast .strict r4Src r4Tgt ∧ Refines .strict r4Tgt r4Src ∧
      beh .strict r4Src = [.ub] ∧ beh .strict r4Tgt = [.ub]
```

- **Positive control** (a nearby setting where the negative conclusion fails): `forwardLoad_nonvacuous`.

```lean
-- lean/ToyProv/Forwarding.lean:379-382
-- forwardLoad_nonvacuous  (ToyProv/Forwarding.lean:379)
theorem forwardLoad_nonvacuous :
    AllAfter .exposed r4cPreNV (provNeC 5 0) ∧ AllAfter .exposed r4cPreNV (isIntC 3) ∧
      beh .exposed (r4cPreNV ++ [.store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]) = [.done [5]] ∧
      beh .exposed (r4cPreNV ++ [.store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]) = [.done [5]]
```

- **Prior art:**
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Jung 2022] (full entry under **Evidence**)
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), discussion of pointer_from_integer_1ie.c: casting a guessed constant address is UB even after the storage instance is exposed - 'if j is exposed, as in the example on the right, these models still make it UB, now for the same reason as PNVI-plain' (allocation addresses are chosen nondeterministically).
- **Design question:** Whether provenance-based alias analysis may treat pointers obtained from integers as non-aliasing, and what exposure information it needs.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — The optimizer heuristic modeled here (a freshly cast pointer does not alias an unrelated pointer) is the alias-analysis assumption discussed by Lee et al. (2018) and Jung (2022) for `inttoptr`. The primary counterexample casts `(int)A`, which is a legitimate exposure-based round trip in PNVI-ae-udi; the guessed-address variant does not transfer, because casting a guessed address is UB in PNVI-ae-udi (P2318R0, `pointer_from_integer_1ie.c`) and in twin allocation. This is a correspondence argument, not a kernel-checked claim.

### R4b: dse across cast load unsound exposed flat

- **Kind / tier / depth:** counterexample · T1 · shallow. Tier rationale: As R4a, for dead-store elimination. Depth: the three closed statements are evaluations (`decide`), but `dseAcrossCast_strict_src_ub` quantifies over all program pairs and needs a short argument over an arbitrary prefix, so the card as a whole is `shallow`.
- **Plain claim:** Deleting store a v before x := load r; store a w, where r := int2ptr k (DSEAcrossCast), is not a refinement in the exposed model (with k := (int)A the load reads A; the source outputs [5], the target [1]) nor in the flat model. In the strict model, for every pair of programs src, tgt matching DSEAcrossCast (hypothesis h of dseAcrossCast_strict_src_ub), both src and tgt are UB; such pairs exist (r4dSrc / r4dTgt, dseAcrossCast_example_refines_strict). Hence the strict-model soundness of this dead-store elimination is vacuous: it holds only because every matching source is UB, and it says nothing about defined programs.

Lean statements (`R4b`):

```lean
-- lean/ToyProv/Forwarding.lean:76-80
-- dseAcrossCast_counterexample  (ToyProv/Forwarding.lean:76)
theorem dseAcrossCast_counterexample :
    DSEAcrossCast .exposed r4dSrc r4dTgt ∧ ¬ Refines .exposed r4dTgt r4dSrc ∧
      beh .exposed r4dSrc = [.done [5]] ∧ beh .exposed r4dTgt = [.done [1]] ∧
      DSEAcrossCast .flat r4dSrc r4dTgt ∧ ¬ Refines .flat r4dTgt r4dSrc ∧
      beh .flat r4dSrc = [.done [5]] ∧ beh .flat r4dTgt = [.done [1]]

-- lean/ToyProv/Forwarding.lean:86
-- dseAcrossCast_not_sound_exposed  (ToyProv/Forwarding.lean:86)
theorem dseAcrossCast_not_sound_exposed : ¬ Sound .exposed DSEAcrossCast

-- lean/ToyProv/Forwarding.lean:89
-- dseAcrossCast_not_sound_flat  (ToyProv/Forwarding.lean:89)
theorem dseAcrossCast_not_sound_flat : ¬ Sound .flat DSEAcrossCast

-- lean/ToyProv/Forwarding.lean:181-182
-- dseAcrossCast_strict_src_ub  (ToyProv/Forwarding.lean:181)
theorem dseAcrossCast_strict_src_ub (src tgt : Prog) (h : DSEAcrossCast .strict src tgt) :
    beh .strict src = [.ub] ∧ beh .strict tgt = [.ub]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Forwarding.lean
def r4dSrc : Prog := r4dPre ++ [.int2ptr 5 2, .store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]
-- ToyProv/Forwarding.lean
def r4dTgt : Prog := r4dPre ++ [.int2ptr 5 2, .load 6 .int 5, .store 0 4] ++ [.obs 6]
-- ToyProv/Forwarding.lean
/-- A (never exposed), B (exposed, initialised to 1), `r := int2ptr (int)B`, `v := 5`, `w := 6`. -/
def r4dPreNV : Prog :=
  [.alloc 0 2, .alloc 1 2, .const 9 1, .store 1 9, .ptr2int 2 1, .int2ptr 5 2, .const 3 5, .const 4 6]
-- ToyProv/Forwarding.lean
/-- A at 16 initialised to 1; `k := (int)A` (exposes A); `v := 5`, `w := 6`. -/
def r4dPre : Prog := [.alloc 0 2, .const 1 1, .store 0 1, .ptr2int 2 0, .const 3 5, .const 4 6]
```

Hypothesis ledger (per statement):

- `dseAcrossCast_counterexample`, `dseAcrossCast_not_sound_exposed`, `dseAcrossCast_not_sound_flat`: none — each is a closed, fully evaluated statement.
- `dseAcrossCast_strict_src_ub`: universally quantified over programs `src` and `tgt`, with exactly one hypothesis:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h : DSEAcrossCast .strict src tgt (dseAcrossCast_strict_src_ub)` | Restricts `src`, `tgt` to pairs that match the cast window in the strict model; without it the programs are arbitrary. | tight | `dseAcrossCast_strict_src_ub_h_needed` (ToyProv/LedgerWitnesses.lean:46). Witness class: a closed two-instruction program without casts, `src = tgt = constObsProg` (quoted under R4a), which is defined in strict (outputs `[1]`) and does not match the window. |

```lean
-- lean/ToyProv/LedgerWitnesses.lean:46-48
-- dseAcrossCast_strict_src_ub_h_needed  (ToyProv/LedgerWitnesses.lean:46)
theorem dseAcrossCast_strict_src_ub_h_needed :
    ¬ DSEAcrossCast .strict constObsProg constObsProg ∧
      ¬ (beh .strict constObsProg = [.ub] ∧ beh .strict constObsProg = [.ub])
```

What is vacuous: the hypothesis `h` is satisfiable (the non-vacuity witness below), but the theorem's conclusion is that every pair satisfying it is UB on both sides. Consequently the strict-model soundness of this dead-store elimination (`dseAcrossCast_sound_strict`, R6g) is a **vacuous** ✓. The closed statements of this card are not vacuous: their exposed and flat sources are defined.

- **Non-vacuity witness:** For the closed statements: r4dSrc / r4dTgt satisfy DSEAcrossCast in the exposed and flat models, where both sources are defined (`dseAcrossCast_counterexample`). For `dseAcrossCast_strict_src_ub`: the same pair satisfies its hypothesis `h` (`DSEAcrossCast .strict r4dSrc r4dTgt`), and both sides are UB in strict, as the theorem says (`dseAcrossCast_example_refines_strict`). Lean: `dseAcrossCast_counterexample`, `dseAcrossCast_example_refines_strict`.

```lean
-- lean/ToyProv/Forwarding.lean:95-97
-- dseAcrossCast_example_refines_strict  (ToyProv/Forwarding.lean:95)
theorem dseAcrossCast_example_refines_strict :
    DSEAcrossCast .strict r4dSrc r4dTgt ∧ Refines .strict r4dTgt r4dSrc ∧
      beh .strict r4dSrc = [.ub] ∧ beh .strict r4dTgt = [.ub]
```

- **Positive control** (a nearby setting where the negative conclusion fails): `dse_nonvacuous`.

```lean
-- lean/ToyProv/Forwarding.lean:762-765
-- dse_nonvacuous  (ToyProv/Forwarding.lean:762)
theorem dse_nonvacuous :
    AllAfter .exposed r4dPreNV (provNeC 5 0) ∧ (6 : Reg) ≠ 0 ∧
      beh .exposed (r4dPreNV ++ [.store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [1]] ∧
      beh .exposed (r4dPreNV ++ [.load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [1]]
```

- **Prior art:**
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Jung 2022] (full entry under **Evidence**)
- **Design question:** Whether provenance-based alias analysis may treat pointers obtained from integers as non-aliasing, and what exposure information it needs.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — As for R4a, for dead-store elimination: the modeled assumption is that a load through a pointer obtained from an integer cannot observe an earlier store; the counterexample uses an exposure-based round trip. This is a correspondence argument, not a kernel-checked claim.

### R4c: forwarding refines exposed if provenances differ

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: Provenance-based alias analysis is standard and Coq-verified for block-based models without integer-to-pointer provenance recovery (CompCert); not found mechanized for an angelic exposed-provenance semantics where r may come from an int2ptr.
- **Plain claim:** In the exposed model, replacing x := load int a by x := v in the window store a v; store r w; load is a refinement provided that, in every reachable state before the window, r and a hold pointers of different provenance (hne) and v holds an integer (hv); r may come from an int2ptr.

Lean statement (`R4c`):

```lean
-- lean/ToyProv/Forwarding.lean:236-241
-- forwardLoad_refines_exposed_of_provNe_of_isInt  (ToyProv/Forwarding.lean:236)
theorem forwardLoad_refines_exposed_of_provNe_of_isInt
    (pre post : Prog) (a v r w x : Reg)
    (hne : AllAfter .exposed pre (provNeC r a))
    (hv : AllAfter .exposed pre (isIntC v)) :
    Refines .exposed (pre ++ [.store a v, .store r w, .copy x v] ++ post)
      (pre ++ [.store a v, .store r w, .load x .int a] ++ post)
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Forwarding.lean
/-- A (never exposed), B (exposed), `r := int2ptr (int)B`, `v := 5`, `w := 9`. -/
def r4cPreNV : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 2 1, .int2ptr 5 2, .const 3 5, .const 4 9]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hne : AllAfter .exposed pre (provNeC r a)` | Provenance-based non-aliasing; without it the cast pointer may carry a's provenance. | tight | `forwardLoad_provNe_needed` (ToyProv/Forwarding.lean:351) |
| `hv : AllAfter .exposed pre (isIntC v)` | The forwarded load is integer-typed: loading a stored pointer at integer type returns its address (and exposes it), not the pointer itself. | tight | `forwardLoad_isInt_needed` (ToyProv/Forwarding.lean:362) |

- **Non-vacuity witness:** r := int2ptr (int)B with A never exposed; both programs output [5]. Lean: `forwardLoad_nonvacuous`.

```lean
-- lean/ToyProv/Forwarding.lean:379-382
-- forwardLoad_nonvacuous  (ToyProv/Forwarding.lean:379)
theorem forwardLoad_nonvacuous :
    AllAfter .exposed r4cPreNV (provNeC 5 0) ∧ AllAfter .exposed r4cPreNV (isIntC 3) ∧
      beh .exposed (r4cPreNV ++ [.store 0 3, .store 5 4, .load 6 .int 0] ++ [.obs 6]) = [.done [5]] ∧
      beh .exposed (r4cPreNV ++ [.store 0 3, .store 5 4, .copy 6 3] ++ [.obs 6]) = [.done [5]]
```

- **Prior art:**
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [Leroy and Blazy 2008] (full entry under **Evidence**)
- **Design question:** Whether provenance-based alias analysis may treat pointers obtained from integers as non-aliasing, and what exposure information it needs.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — `provNeC` is the judgement of a provenance-based alias analysis (as in block-based models such as CompCert's; Leroy and Blazy 2008); the toy shows the judgement stays sound when one pointer comes from an exposed-model `int2ptr`. How a compiler establishes it is not modeled (R4e gives one sufficient criterion). This is a correspondence argument, not a kernel-checked claim.

### R4d: dse refines exposed if provenances differ

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: As R4c, for dead-store elimination.
- **Plain claim:** In the exposed model, deleting store a v before x := load ty r; store a w is a refinement provided that, in every reachable state before the window, r and a hold pointers of different provenance (hne) and the load does not overwrite register a (hx).

Lean statement (`R4d`):

```lean
-- lean/ToyProv/Forwarding.lean:506-511
-- dse_refines_exposed_of_provNe_of_ne  (ToyProv/Forwarding.lean:506)
theorem dse_refines_exposed_of_provNe_of_ne
    (pre post : Prog) (a v r x w : Reg) (ty : Ty)
    (hne : AllAfter .exposed pre (provNeC r a))
    (hx : x ≠ a) :
    Refines .exposed (pre ++ [.load x ty r, .store a w] ++ post)
      (pre ++ [.store a v, .load x ty r, .store a w] ++ post)
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Forwarding.lean
/-- A (never exposed), B (exposed, initialised to 1), `r := int2ptr (int)B`, `v := 5`, `w := 6`. -/
def r4dPreNV : Prog :=
  [.alloc 0 2, .alloc 1 2, .const 9 1, .store 1 9, .ptr2int 2 1, .int2ptr 5 2, .const 3 5, .const 4 6]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hne : AllAfter .exposed pre (provNeC r a)` | Otherwise the load may read the deleted store. | tight | `dse_provNe_needed` (ToyProv/Forwarding.lean:739) |
| `hx : x ≠ a` | If the load overwrites a, the second store goes elsewhere and the first is not dead. | tight | `dse_ne_needed` (ToyProv/Forwarding.lean:751) |

- **Non-vacuity witness:** r := int2ptr (int)B, A never exposed, B initialised; both programs output [1]. Lean: `dse_nonvacuous`.

```lean
-- lean/ToyProv/Forwarding.lean:762-765
-- dse_nonvacuous  (ToyProv/Forwarding.lean:762)
theorem dse_nonvacuous :
    AllAfter .exposed r4dPreNV (provNeC 5 0) ∧ (6 : Reg) ≠ 0 ∧
      beh .exposed (r4dPreNV ++ [.store 0 3, .load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [1]] ∧
      beh .exposed (r4dPreNV ++ [.load 6 .int 5, .store 0 4] ++ [.obs 6]) = [.done [1]]
```

- **Prior art:**
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [Leroy and Blazy 2008] (full entry under **Evidence**)
- **Design question:** Whether provenance-based alias analysis may treat pointers obtained from integers as non-aliasing, and what exposure information it needs.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — As for R4c, for dead-store elimination. This is a correspondence argument, not a kernel-checked claim.

### R4e: int2ptr picks only exposed candidates

- **Kind / tier / depth:** theorem · T0 · definitional. Tier rationale: Restates the definition of the exposed-model cast and the strict cast, plus the one-step consequence used as the side condition of R4c/R4d.
- **Plain claim:** When register k holds an integer n, every result of d := int2ptr k in the exposed model is a pointer with address n whose provenance, if any, is a candidate (exposed, live, n within its closed range [base, base + size]); in the strict model the only result is the pointer with address n and no provenance. Consequently, if a register a different from the destination (d ≠ a) holds a pointer y whose allocation A is not exposed at the cast, every successor of d := int2ptr k in the exposed model satisfies provNeC d a (the side condition of R4c/R4d).

Lean statements (`R4e`):

```lean
-- lean/ToyProv/Forwarding.lean:774-776
-- int2ptr_exposed_result  (ToyProv/Forwarding.lean:774)
theorem int2ptr_exposed_result (s : St) (d k : Reg) (a : Nat) (hk : s.regs k = some (.int a)) :
    ∀ o ∈ step .exposed s (.int2ptr d k), ∃ x, o = some (s.setReg d (.ptr x)) ∧ x.addr = a ∧
      ∀ A, x.prov = some A → A ∈ candidates s a ∧ A ∈ s.exposed

-- lean/ToyProv/Forwarding.lean:804-805
-- int2ptr_strict_result  (ToyProv/Forwarding.lean:804)
theorem int2ptr_strict_result (s : St) (d k : Reg) (a : Nat) (hk : s.regs k = some (.int a)) :
    step .strict s (.int2ptr d k) = [some (s.setReg d (.ptr ⟨none, a⟩))]

-- lean/ToyProv/Forwarding.lean:830-833
-- int2ptr_result_provNe_of_not_exposed  (ToyProv/Forwarding.lean:830)
theorem int2ptr_result_provNe_of_not_exposed (s : St) (d k a : Reg) (n : Nat) (y : Ptr) (A : AllocId)
    (hk : s.regs k = some (.int n)) (ha : s.regs a = some (.ptr y)) (hA : y.prov = some A)
    (hnot : A ∉ s.exposed) (hda : d ≠ a) :
    ∀ o ∈ step .exposed s (.int2ptr d k), ∃ s', o = some s' ∧ provNeC d a s' = true
```

Naming: in `int2ptr_exposed_result` and `int2ptr_strict_result` the integer is called `a : Nat`; in `int2ptr_result_provNe_of_not_exposed` the integer is `n : Nat` and `a : Reg` is a register. The plain claim calls the integer n throughout and uses a only for the register.

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Forwarding.lean
/-- **R4e non-vacuity.** After `k := (int)A` with A and B adjacent and both exposed, register 3
holds the integer 18 (A's one-past address = B's start), and the exposed-model cast has two
successors (A and B) while the strict-model cast has one. -/
def r4eState : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1] init with
  | some s :: _ => s
  | _ => init
-- ToyProv/Forwarding.lean
/-- State after `alloc A; alloc B; k := (int)B` in the exposed model. -/
def r4cState : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 2 1] init with
  | some s :: _ => s
  | _ => init
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hk : s.regs k = some (.int a) (int2ptr_exposed_result, int2ptr_strict_result)` | Otherwise the cast is UB. | tight | `int2ptr_exposed_result_hk_needed` (ToyProv/Forwarding.lean:798); `int2ptr_strict_result_hk_needed` (ToyProv/Forwarding.lean:809) |
| `hk : s.regs k = some (.int n) (int2ptr_result_provNe_of_not_exposed)` | Otherwise the cast is UB and its only successor is none, which is not a state satisfying provNeC. | tight | `int2ptr_result_provNe_hk_needed` (ToyProv/Forwarding.lean:856) |
| `ha : s.regs a = some (.ptr y) (int2ptr_result_provNe_of_not_exposed)` | provNeC d a requires register a to hold a pointer; ha also ties y (the pointer named in hA) to register a. | tight | `int2ptr_result_provNe_ha_needed` (ToyProv/Forwarding.lean:866) |
| `hA : y.prov = some A (int2ptr_result_provNe_of_not_exposed)` | Ties the unexposed allocation A of hnot to a's pointer; if a's pointer has another (exposed) provenance, the cast may pick that provenance. | tight | `int2ptr_result_provNe_hA_needed` (ToyProv/Forwarding.lean:875) |
| `hnot : A ∉ s.exposed (int2ptr_result_provNe_of_not_exposed)` | If a's allocation is exposed (and contains the address), the cast may pick it. | tight | `int2ptr_result_provNe_hnot_needed` (ToyProv/Forwarding.lean:884) |
| `hda : d ≠ a (int2ptr_result_provNe_of_not_exposed)` | If the cast writes register a itself, provNeC a a compares a register with itself and is false. | tight | `int2ptr_result_provNe_hda_needed` (ToyProv/Forwarding.lean:893) |

- **Non-vacuity witness:** After A, B adjacent and both exposed, register 3 holds 18 and the exposed cast has two successors; for the consequence, in the state after alloc A; alloc B; k := (int)B (A never exposed), all five hypotheses hold for d = 5, k = 2, a = 0, y = A's pointer, and every successor of the cast satisfies provNeC 5 0. Lean: `int2ptr_result_nonvacuous`, `int2ptr_result_provNe_nonvacuous`.

```lean
-- lean/ToyProv/Forwarding.lean:821-823
-- int2ptr_result_nonvacuous  (ToyProv/Forwarding.lean:821)
theorem int2ptr_result_nonvacuous :
    r4eState.regs 3 = some (.int 18) ∧ (step .exposed r4eState (.int2ptr 5 3)).length = 2 ∧
      (step .strict r4eState (.int2ptr 5 3)).length = 1

-- lean/ToyProv/Forwarding.lean:845-848
-- int2ptr_result_provNe_nonvacuous  (ToyProv/Forwarding.lean:845)
theorem int2ptr_result_provNe_nonvacuous :
    r4cState.regs 2 = some (.int 18) ∧ r4cState.regs 0 = some (.ptr ⟨some 0, 16⟩) ∧
      (⟨some 0, 16⟩ : Ptr).prov = some 0 ∧ (0 : AllocId) ∉ r4cState.exposed ∧ (5 : Reg) ≠ 0 ∧
      ∀ o ∈ step .exposed r4cState (.int2ptr 5 2), ∃ s', o = some s' ∧ provNeC 5 0 s' = true
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [Rust 1.84.0 documentation] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
- **Design question:** Whether provenance-based alias analysis may treat pointers obtained from integers as non-aliasing, and what exposure information it needs.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — PNVI-ae-udi and MiniRust both restrict `int2ptr` to exposed provenance (or none); MiniRust does not additionally restrict by address. Whether the step-level consequence holds for MiniRust's rule is not examined here. This is a correspondence argument, not a kernel-checked claim.

### R5a: integer load of pointer bytes strips or exposes

- **Kind / tier / depth:** theorem · T1 · definitional. Tier rationale: PNVI-ae's 'read (at non-pointer type) of the representation' exposure rule and MiniRust's stripping integer decode, made precise in one toy.
- **Plain claim:** Loading a stored pointer's two bytes at integer type yields the pointer's address as a provenance-free integer and records its provenance as exposed, in every model; in strict that exposure is inert, so casting the integer back gives a pointer that cannot be used (UB), while in exposed the load is what lets a later int2ptr (even of a guessed constant) pick the allocation again.

Lean statements (`R5a`):

```lean
-- lean/ToyProv/Bytes.lean:105-108
-- load_int_of_ptrFrags  (ToyProv/Bytes.lean:105)
theorem load_int_of_ptrFrags (m : Model) (s : St) (d r : Reg) (x p : Ptr)
    (hr : s.regs r = some (.ptr x)) (hacc : canAccess m s x 2 = true)
    (h0 : s.mem x.addr = .ptrFrag p 0) (h1 : s.mem (x.addr + 1) = .ptrFrag p 1) :
    step m s (.load d .int r) = [some ((s.setReg d (.int p.addr)).expose p.prov.toList)]

-- lean/ToyProv/Bytes.lean:28-29
-- decodeInt_ptrFrags  (ToyProv/Bytes.lean:28)
theorem decodeInt_ptrFrags (p : Ptr) :
    decodeInt (.ptrFrag p 0) (.ptrFrag p 1) = some (p.addr, p.prov.toList)

-- lean/ToyProv/Bytes.lean:353-355
-- byteLoadAsInt_strict_strips_exposed_exposes  (ToyProv/Bytes.lean:353)
theorem byteLoadAsInt_strict_strips_exposed_exposes :
    beh .strict r5aProg = [.ub] ∧ beh .exposed r5aProg = [.done [7]] ∧
      beh .exposed r5aGuess = [.ub] ∧ beh .exposed r5aGuessAfterLoad = [.done [7]]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Bytes.lean
/-- Store the pointer A into B; load B's bytes at integer type; cast that integer back with
`int2ptr`; store 7 through it; read A. -/
def r5aProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .store 1 0, .load 2 .int 1, .int2ptr 3 2, .const 4 7, .store 3 4,
   .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- As `r5aProg` but A's address is guessed as the constant 16 instead of loaded. -/
def r5aGuess : Prog :=
  [.alloc 0 2, .alloc 1 2, .store 1 0, .const 2 16, .int2ptr 3 2, .const 4 7, .store 3 4,
   .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- As `r5aGuess` but with an integer-typed load of B's bytes (result unused) before the guess. -/
def r5aGuessAfterLoad : Prog :=
  [.alloc 0 2, .alloc 1 2, .store 1 0, .load 9 .int 1, .const 2 16, .int2ptr 3 2, .const 4 7,
   .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- A, B, C (16, 18, 20); B holds the pointer A. -/
def r5State : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0] init with
  | some s :: _ => s
  | _ => init
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hr : s.regs r = some (.ptr x)` | The load's address register must hold a pointer. | tight | `load_int_of_ptrFrags_hr_needed` (ToyProv/Bytes.lean:168) |
| `hacc : canAccess m s x 2 = true` | The access must be allowed (live allocation, in bounds, provenance in strict/exposed). | tight | `load_int_of_ptrFrags_hacc_needed` (ToyProv/Bytes.lean:180) |
| `h0 : s.mem x.addr = .ptrFrag p 0` | The first byte must be fragment 0 of a pointer. | tight | `load_int_of_ptrFrags_h0_needed` (ToyProv/Bytes.lean:205) |
| `h1 : s.mem (x.addr + 1) = .ptrFrag p 1` | The second byte must be fragment 1 of a pointer. | tight | `load_int_of_ptrFrags_h1_needed` (ToyProv/Bytes.lean:214) |

- **Non-vacuity witness:** r5State: B holds the pointer A and is accessible; program-level: r5aProg, r5aGuess, r5aGuessAfterLoad. Lean: `load_int_of_ptrFrags_nonvacuous`.

```lean
-- lean/ToyProv/Bytes.lean:157-159
-- load_int_of_ptrFrags_nonvacuous  (ToyProv/Bytes.lean:157)
theorem load_int_of_ptrFrags_nonvacuous :
    r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed r5State ⟨some 1, 18⟩ 2 = true ∧
      r5State.mem 18 = .ptrFrag ⟨some 0, 16⟩ 0 ∧ r5State.mem (18 + 1) = .ptrFrag ⟨some 0, 16⟩ 1
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - P2318R0 (as above), definition of PNVI-ae: 'A storage instance is deemed exposed by a conversion of a pointer to it to an integer type, by a read (at non-pointer type) of the representation of the pointer, or by an output of the pointer using "%p".'
  - [Jung 2022] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
  - [Jung 2018] (full entry under **Evidence**)
  - [Besson et al. 2019] (full entry under **Evidence**)
- **Design question:** What a byte-level memory must record so that transmute-style pointer/integer reinterpretation (as performed by zerocopy-like byte casts) has a defined meaning under each provenance model.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — PNVI-ae exposes a storage instance on a non-pointer-type read of a pointer's representation (P2318R0), which the exposed model follows. MiniRust's integer decoding instead strips provenance without exposing (an open question there), which corresponds to the strict column; Rust therefore does not behave like the exposed model here. This is a correspondence argument, not a kernel-checked claim.

### R5b: memcpy copies abstract bytes and provenance

- **Kind / tier / depth:** theorem · T0 · shallow. Tier rationale: Byte copies preserving pointer fragments is the standard design (MiniRust, PNVI's memcpy rule, CompCert's pointer fragments); restated.
- **Plain claim:** In every model, a defined memcpy d r n makes each of the n destination bytes equal to the corresponding source byte of the pre-state, abstract byte for abstract byte (so pointer fragments and their provenance are copied), and leaves every byte outside the destination range unchanged; a pointer copied this way is usable with no cast, even when it points outside its allocation's range and is moved back with wrapping offsets.

Lean statements (`R5b`):

```lean
-- lean/ToyProv/Bytes.lean:89-92
-- memcpy_copies_abstract_bytes  (ToyProv/Bytes.lean:89)
theorem memcpy_copies_abstract_bytes (m : Model) (s s' : St) (d r : Reg) (n : Nat) (x y : Ptr)
    (hd : s.regs d = some (.ptr x)) (hr : s.regs r = some (.ptr y))
    (hs : some s' ∈ step m s (.memcpy d r n)) :
    ∀ i < n, s'.mem (x.addr + i) = s.mem (y.addr + i)

-- lean/ToyProv/Bytes.lean:133-136
-- memcpy_frame  (ToyProv/Bytes.lean:133)
theorem memcpy_frame (m : Model) (s s' : St) (d r : Reg) (n : Nat) (x y : Ptr)
    (hd : s.regs d = some (.ptr x)) (hr : s.regs r = some (.ptr y))
    (hs : some s' ∈ step m s (.memcpy d r n)) :
    ∀ z, z < x.addr ∨ x.addr + n ≤ z → s'.mem z = s.mem z

-- lean/ToyProv/Bytes.lean:366-367
-- memcpy_preserves_provenance_example  (ToyProv/Bytes.lean:366)
theorem memcpy_preserves_provenance_example :
    beh .strict r5bProg = [.done [7]] ∧ beh .exposed r5bProg = [.done [7]]

-- lean/ToyProv/Bytes.lean:397-399
-- intRoundTrip_out_of_range_example  (ToyProv/Bytes.lean:397)
theorem intRoundTrip_out_of_range_example :
    beh .strict r5cOutCopy = [.done [7]] ∧ beh .exposed r5cOutCopy = [.done [7]] ∧
      beh .strict r5cOutInt = [.ub] ∧ beh .exposed r5cOutInt = [.ub]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Bytes.lean
/-- Store the pointer A into B; `memcpy` B's two bytes into C; load C at pointer type; store 7
through it; read A. -/
def r5bProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0, .memcpy 2 1 2, .load 3 .ptr 2, .const 4 7,
   .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- A pointer 10 bytes past A's start (outside every allocation's closed range) is stored into
B, copied to C (byte-wise with `memcpy`, or through an integer value), reloaded, moved back by
10, and stored through. -/
def r5cOutCopy : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .offset 9 0 10, .store 1 9, .memcpy 2 1 2, .load 3 .ptr 2,
   .offset 3 3 (-10), .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
def r5cOutInt : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .offset 9 0 10, .store 1 9, .load 6 .int 1, .store 2 6,
   .load 3 .ptr 2, .offset 3 3 (-10), .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- A, B, C (16, 18, 20); B holds the pointer A. -/
def r5State : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0] init with
  | some s :: _ => s
  | _ => init
-- ToyProv/Bytes.lean
/-- The successor of `memcpy C B 2` in `r5State`. -/
def r5Succ : St := { r5State with mem := writeBytes r5State.mem 20 (readBytes r5State.mem 18 2) }
```

Hypothesis ledger (per statement; `memcpy_preserves_provenance_example` and `intRoundTrip_out_of_range_example` are closed evaluations with no hypotheses):

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hd : s.regs d = some (.ptr x) (memcpy_copies_abstract_bytes)` | Names the destination pointer; with a different x the bytes at x are not the copy. | tight | `memcpy_copies_hd_needed` (ToyProv/Bytes.lean:259). Witness class: the concrete state `r5State` (allocations A, B, C), exposed model, `s' := r5Succ`, `x` = A while `d` holds C. |
| `hr : s.regs r = some (.ptr y) (memcpy_copies_abstract_bytes)` | Names the source pointer; with a different y the copied bytes are not y's. | tight | `memcpy_copies_hr_needed` (ToyProv/Bytes.lean:269). Witness class: `r5State`, exposed model, `s' := r5Succ`, `y` = A while `r` holds B. |
| `hs : some s' ∈ step m s (.memcpy d r n) (memcpy_copies_abstract_bytes)` | s' must be the successor of the memcpy; an arbitrary s' (e.g. s itself) does not contain the copy. | tight | `memcpy_copies_hs_needed` (ToyProv/Bytes.lean:250). Witness class: `r5State` with `s' := r5State` (no copy performed). |
| `hd : s.regs d = some (.ptr x) (memcpy_frame)` | Names the destination pointer; the frame is stated relative to x. | tight | `memcpy_frame_hd_needed` (ToyProv/LedgerWitnesses.lean:61). Witness class: `r5State`, exposed model, `s' := r5Succ`, `x` = A (at 16) while `d` holds C (at 20); C's changed byte at 20 lies outside `[16, 18)`. |
| `hr : s.regs r = some (.ptr y) (memcpy_frame)` | Not needed: the conclusion does not mention y, and a defined memcpy already forces register r to hold some pointer. | harmless | — (`memcpy_frame_of_hd_hs` proves the same conclusion from `hd` and `hs` alone) |
| `hs : some s' ∈ step m s (.memcpy d r n) (memcpy_frame)` | s' must be the successor of the memcpy; an arbitrary s' may differ from s outside the destination range. | tight | `memcpy_frame_hs_needed` (ToyProv/LedgerWitnesses.lean:78). Witness class: `r5State`, `x` = C, `y` = B, `s' := r5WrongDst` (B's bytes written over A instead of C), which differs from `r5State` at 16, outside `[20, 22)`. |

The three `memcpy_copies_*_needed` witnesses establish tightness for `memcpy_copies_abstract_bytes` only; `memcpy_copies_hr_needed` and `memcpy_copies_hs_needed` satisfy `memcpy_frame`'s conclusion, so they say nothing about `memcpy_frame`, whose ledger rows cite their own witnesses.

```lean
-- lean/ToyProv/LedgerWitnesses.lean:70-72
/-- `r5State` with B's two bytes written over A (at 16) instead of C: not the successor of
`memcpy C B 2`. -/
def r5WrongDst : St := { r5State with mem := writeBytes r5State.mem 16 (readBytes r5State.mem 18 2) }

-- lean/ToyProv/LedgerWitnesses.lean:61-65
-- memcpy_frame_hd_needed  (ToyProv/LedgerWitnesses.lean:61)
theorem memcpy_frame_hd_needed :
    r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ some r5Succ ∈ step .exposed r5State (.memcpy 2 1 2) ∧
      r5State.regs 2 ≠ some (.ptr ⟨some 0, 16⟩) ∧
      ¬ (∀ z, z < (⟨some 0, 16⟩ : Ptr).addr ∨ (⟨some 0, 16⟩ : Ptr).addr + 2 ≤ z →
          r5Succ.mem z = r5State.mem z)

-- lean/ToyProv/LedgerWitnesses.lean:78-81
-- memcpy_frame_hs_needed  (ToyProv/LedgerWitnesses.lean:78)
theorem memcpy_frame_hs_needed :
    r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧
      ¬ (∀ z, z < (⟨some 2, 20⟩ : Ptr).addr ∨ (⟨some 2, 20⟩ : Ptr).addr + 2 ≤ z →
          r5WrongDst.mem z = r5State.mem z)

-- lean/ToyProv/LedgerWitnesses.lean:89-91
-- memcpy_frame_of_hd_hs  (ToyProv/LedgerWitnesses.lean:89)
theorem memcpy_frame_of_hd_hs (m : Model) (s s' : St) (d r : Reg) (n : Nat) (x : Ptr)
    (hd : s.regs d = some (.ptr x)) (hs : some s' ∈ step m s (.memcpy d r n)) :
    ∀ z, z < x.addr ∨ x.addr + n ≤ z → s'.mem z = s.mem z
```

- **Non-vacuity witness:** r5State: memcpy C B 2 has the successor r5Succ in every model; program level: r5bProg defined in strict and exposed. Lean: `memcpy_copies_abstract_bytes_nonvacuous`.

```lean
-- lean/ToyProv/Bytes.lean:243-245
-- memcpy_copies_abstract_bytes_nonvacuous  (ToyProv/Bytes.lean:243)
theorem memcpy_copies_abstract_bytes_nonvacuous (m : Model) :
    r5State.regs 2 = some (.ptr ⟨some 2, 20⟩) ∧ r5State.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧
      some r5Succ ∈ step m r5State (.memcpy 2 1 2)
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
  - [Jung 2018] (full entry under **Evidence**)
  - [Leroy and Blazy 2008] (full entry under **Evidence**)
  - [Rust 1.84.0 documentation] (full entry under **Evidence**)
- **Design question:** What a byte-level memory must record so that transmute-style pointer/integer reinterpretation (as performed by zerocopy-like byte casts) has a defined meaning under each provenance model.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Byte copies that preserve pointer fragments and their provenance are the design of MiniRust's abstract bytes, PNVI's `memcpy` rule and CompCert's pointer fragments; the toy's `memcpy` has memmove semantics and requires provenance even for `n = 0`, unlike Rust. This is a correspondence argument, not a kernel-checked claim.

### R5c: integer value roundtrip does not carry provenance

- **Kind / tier / depth:** theorem · T1 · definitional. Tier rationale: Contrasts the PNVI-style re-derivation with strict loss of provenance in one toy; the boundary case is not found stated elsewhere as a program.
- **Plain claim:** Loading, at pointer type, the two fragments of a stored integer n converts n exactly as int2ptr would (load_ptr_of_intFrags). Hence copying a pointer through an integer value (load at integer type, store the integer, load at pointer type) does not carry its provenance: in strict the reloaded pointer has none; in exposed a provenance is re-derived from the exposed set, which on the three proved example programs coincides with the original (in-range pointer, unique candidate), is absent (pointer outside every allocation's range), or is a different allocation (one-past-the-end boundary).

Lean statements (`R5c`):

```lean
-- lean/ToyProv/Bytes.lean:115-118
-- load_ptr_of_intFrags  (ToyProv/Bytes.lean:115)
theorem load_ptr_of_intFrags (m : Model) (s : St) (d r : Reg) (x : Ptr) (n : Nat)
    (hr : s.regs r = some (.ptr x)) (hacc : canAccess m s x 2 = true)
    (h0 : s.mem x.addr = .intFrag n 0) (h1 : s.mem (x.addr + 1) = .intFrag n 1) :
    step m s (.load d .ptr r) = castToPtr m s d n

-- lean/ToyProv/Bytes.lean:39
-- decodePtr_intFrags  (ToyProv/Bytes.lean:39)
theorem decodePtr_intFrags (n : Nat) : decodePtr (.intFrag n 0) (.intFrag n 1) = some (.inr n)

-- lean/ToyProv/Bytes.lean:380-381
-- intRoundTrip_in_range_example  (ToyProv/Bytes.lean:380)
theorem intRoundTrip_in_range_example :
    beh .strict r5cProg = [.ub] ∧ beh .exposed r5cProg = [.done [7]]

-- lean/ToyProv/Bytes.lean:397-399
-- intRoundTrip_out_of_range_example  (ToyProv/Bytes.lean:397)
theorem intRoundTrip_out_of_range_example :
    beh .strict r5cOutCopy = [.done [7]] ∧ beh .exposed r5cOutCopy = [.done [7]] ∧
      beh .strict r5cOutInt = [.ub] ∧ beh .exposed r5cOutInt = [.ub]

-- lean/ToyProv/Bytes.lean:414-416
-- intRoundTrip_boundary_example  (ToyProv/Bytes.lean:414)
theorem intRoundTrip_boundary_example :
    beh .exposed r5cBndCopy = [.ub] ∧ beh .exposed r5cBndInt = [.done [7]] ∧
      beh .strict r5cBndCopy = [.ub] ∧ beh .strict r5cBndInt = [.ub]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Bytes.lean
/-- As `r5bProg` but the copy goes through an integer value: load B at integer type, store that
integer into C, load C at pointer type. -/
def r5cProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .store 1 0, .load 6 .int 1, .store 2 6, .load 3 .ptr 2,
   .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- A pointer 10 bytes past A's start (outside every allocation's closed range) is stored into
B, copied to C (byte-wise with `memcpy`, or through an integer value), reloaded, moved back by
10, and stored through. -/
def r5cOutCopy : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .offset 9 0 10, .store 1 9, .memcpy 2 1 2, .load 3 .ptr 2,
   .offset 3 3 (-10), .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
def r5cOutInt : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .offset 9 0 10, .store 1 9, .load 6 .int 1, .store 2 6,
   .load 3 .ptr 2, .offset 3 3 (-10), .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/Bytes.lean
/-- The one-past-the-end pointer of A (= B's start, B exposed) is stored into C, copied to D
(by `memcpy` or through an integer value), reloaded, and stored through; then B is read. -/
def r5cBndCopy : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .alloc 3 2, .ptr2int 8 1, .offset 9 0 2, .store 2 9,
   .memcpy 3 2 2, .load 4 .ptr 3, .const 5 7, .store 4 5, .load 6 .int 1, .obs 6]
-- ToyProv/Bytes.lean
def r5cBndInt : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .alloc 3 2, .ptr2int 8 1, .offset 9 0 2, .store 2 9,
   .load 7 .int 2, .store 3 7, .load 4 .ptr 3, .const 5 7, .store 4 5, .load 6 .int 1, .obs 6]
-- ToyProv/Bytes.lean
/-- B holds the integer 16. -/
def r5IntState : St :=
  match exec .exposed [.alloc 0 2, .alloc 1 2, .ptr2int 3 0, .store 1 3] init with
  | some s :: _ => s
  | _ => init
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hr : s.regs r = some (.ptr x)` | The load's address register must hold a pointer. | tight | `load_ptr_of_intFrags_hr_needed` (ToyProv/Bytes.lean:299) |
| `hacc : canAccess m s x 2 = true` | The access must be allowed. | tight | `load_ptr_of_intFrags_hacc_needed` (ToyProv/Bytes.lean:292) |
| `h0 : s.mem x.addr = .intFrag n 0` | Byte 0 must be fragment 0 of the integer n; otherwise (here an uninitialised byte) the pointer-typed load is UB, not castToPtr's result. | tight | `load_ptr_of_intFrags_h0_needed` (ToyProv/Bytes.lean:317) |
| `h1 : s.mem (x.addr + 1) = .intFrag n 1` | As h0, for byte 1. | tight | `load_ptr_of_intFrags_h1_needed` (ToyProv/Bytes.lean:326) |

- **Non-vacuity witness:** r5IntState: B holds the integer 16 (A's exposed address); program level: r5cProg, r5cOutInt, r5cBndInt. Lean: `load_ptr_of_intFrags_nonvacuous`.

```lean
-- lean/ToyProv/Bytes.lean:285-288
-- load_ptr_of_intFrags_nonvacuous  (ToyProv/Bytes.lean:285)
theorem load_ptr_of_intFrags_nonvacuous :
    r5IntState.regs 1 = some (.ptr ⟨some 1, 18⟩) ∧ canAccess .exposed r5IntState ⟨some 1, 18⟩ 2 = true ∧
      r5IntState.mem 18 = .intFrag 16 0 ∧ r5IntState.mem (18 + 1) = .intFrag 16 1 ∧
      (castToPtr .exposed r5IntState 3 16).length = 1
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
  - [Besson et al. 2019] (full entry under **Evidence**)
- **Design question:** What a byte-level memory must record so that transmute-style pointer/integer reinterpretation (as performed by zerocopy-like byte casts) has a defined meaning under each provenance model.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — In the exposed model a pointer-typed load of integer bytes acts as `int2ptr` (a PNVI-ae-udi reading); in Rust/MiniRust such a load yields a pointer without provenance, which corresponds to the strict column. This is a correspondence argument, not a kernel-checked claim.

### R6a: exposed refines strict

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: Informally known that exposed provenance only adds definedness over strict (VIP proves a related compatibility result for PNVI-ae-udi on paper and verifies RefinedC-VIP in Coq); not found mechanized for this pair of models.
- **Plain claim:** For every program, the exposed model's behaviour refines the strict model's: either the program has UB in strict, or every exposed behaviour is a strict behaviour (strict has more UB).

Lean statement (`R6a`):

```lean
-- lean/ToyProv/Ordering.lean:53
-- exposed_semRefines_strict  (ToyProv/Ordering.lean:53)
theorem exposed_semRefines_strict (P : Prog) : SemRefines .exposed .strict P
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Ordering.lean
/-- Round trip of A's address, store 7 through it, read A back. -/
def r6StrictUB : Prog :=
  [.alloc 0 2, .ptr2int 1 0, .int2ptr 2 1, .const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
-- ToyProv/Ordering.lean
/-- Store 7 through the one-past-the-end pointer of A, read B back. -/
def r6ExposedUB : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .const 3 7, .store 2 3, .load 4 .int 1, .obs 4]
```

Hypothesis ledger: none — the statement is universally quantified with no side hypotheses.

- **Non-vacuity witness:** No hypotheses; the ordering is strict (R6d). Lean: `model_orderings_strict`.

```lean
-- lean/ToyProv/Ordering.lean:131-135
-- model_orderings_strict  (ToyProv/Ordering.lean:131)
theorem model_orderings_strict :
    beh .exposed r6StrictUB = [.done [7]] ∧ beh .strict r6StrictUB = [.ub] ∧
      ¬ SemRefines .strict .exposed r6StrictUB ∧
      beh .flat r6ExposedUB = [.done [7]] ∧ beh .exposed r6ExposedUB = [.ub] ∧
      ¬ SemRefines .exposed .flat r6ExposedUB
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [Rust 1.84.0 documentation] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
  - [Lepigre et al. 2022] (full entry under **Evidence**)
- **Design question:** Whether choosing a stricter or more permissive provenance model lets optimization soundness results be reused.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Informally, exposed provenance only adds definedness over strict provenance; Lepigre et al. (2022) prove a related compatibility result between VIP and PNVI-ae-udi. The toy theorem depends on its monotone decoder (R7b) and on `int2ptr` with no candidate yielding a provenance-less pointer whose *use* is UB, as with Rust's `without_provenance`. This is a correspondence argument, not a kernel-checked claim.

### R6b: flat refines exposed

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: Kang et al. (2015) verify in Coq a compiler from their quasi-concrete model to a concrete model that eliminates dead casts; not found mechanized for this exposed model.
- **Plain claim:** For every program, the flat model's behaviour refines the exposed model's: either the program has UB in exposed, or every flat behaviour is an exposed behaviour.

Lean statement (`R6b`):

```lean
-- lean/ToyProv/Ordering.lean:83
-- flat_semRefines_exposed  (ToyProv/Ordering.lean:83)
theorem flat_semRefines_exposed (P : Prog) : SemRefines .flat .exposed P
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Ordering.lean
/-- Round trip of A's address, store 7 through it, read A back. -/
def r6StrictUB : Prog :=
  [.alloc 0 2, .ptr2int 1 0, .int2ptr 2 1, .const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
-- ToyProv/Ordering.lean
/-- Store 7 through the one-past-the-end pointer of A, read B back. -/
def r6ExposedUB : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .const 3 7, .store 2 3, .load 4 .int 1, .obs 4]
```

Hypothesis ledger: none — the statement is universally quantified with no side hypotheses.

- **Non-vacuity witness:** No hypotheses; the ordering is strict (R6d). Lean: `model_orderings_strict`.

```lean
-- lean/ToyProv/Ordering.lean:131-135
-- model_orderings_strict  (ToyProv/Ordering.lean:131)
theorem model_orderings_strict :
    beh .exposed r6StrictUB = [.done [7]] ∧ beh .strict r6StrictUB = [.ub] ∧
      ¬ SemRefines .strict .exposed r6StrictUB ∧
      beh .flat r6ExposedUB = [.done [7]] ∧ beh .exposed r6ExposedUB = [.ub] ∧
      ¬ SemRefines .exposed .flat r6ExposedUB
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [Kang et al. 2015] (full entry under **Evidence**)
  - [Beck et al. 2024] (full entry under **Evidence**)
- **Design question:** Whether choosing a stricter or more permissive provenance model lets optimization soundness results be reused.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Kang et al. (2015) verify in Coq a compiler from their quasi-concrete model to a concrete model; the toy result is the analogous containment for its own flat and exposed models and depends on strictly positive, disjoint, deterministic allocation without out-of-memory. This is a correspondence argument, not a kernel-checked claim.

### R6c: exposed defined behaviours coincide

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: A consequence of angelic resolution and provenance-insensitive observation in this toy; not found stated.
- **Plain claim:** In the exposed model, angelic resolution never yields two different defined behaviours: for every program P, all elements of beh .exposed P are equal (at most one distinct outcome; the list may repeat it once per resolution).

Lean statement (`R6c`):

```lean
-- lean/ToyProv/Erasure.lean:504-505
-- exposed_beh_elements_equal  (ToyProv/Erasure.lean:504)
theorem exposed_beh_elements_equal (P : Prog) :
    ∀ o₁ ∈ beh .exposed P, ∀ o₂ ∈ beh .exposed P, o₁ = o₂
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Ordering.lean
/-- A and B adjacent and both exposed; `int2ptr` of B's start has two resolutions with the same
output. -/
def dupBehProg : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1, .int2ptr 4 3, .obs 4]
```

Hypothesis ledger: none — the statement is universally quantified with no side hypotheses.

- **Non-vacuity witness:** angelicProg (quoted below) has two executions, one UB and one outputting [7] (`ex_runs_two_resolutions`), and the single behaviour [7] (`ex_beh_angelic_pos`); dupBehProg has two equal behaviours (`exposed_beh_may_repeat`). Lean: `exposed_beh_may_repeat`, `ex_runs_two_resolutions`, `ex_beh_angelic_pos`.

```lean
-- lean/ToyProv/Ordering.lean:118-119
-- exposed_beh_may_repeat  (ToyProv/Ordering.lean:118)
theorem exposed_beh_may_repeat :
    beh .exposed dupBehProg = [.done [18], .done [18]] ∧ beh .strict dupBehProg = [.done [18]]
```

```lean
-- lean/ToyProv/Examples.lean:86-89
/-- In `exposed`, `int2ptr 18` with both A and B exposed has two resolutions: storing through
the A-resolution (one past A's end) is UB, through the B-resolution it is defined. -/
def angelicProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .ptr2int 2 0, .ptr2int 3 1, .int2ptr 4 3, .const 5 7, .store 4 5, .obs 5]

-- lean/ToyProv/Examples.lean:90
-- ex_runs_two_resolutions  (ToyProv/Examples.lean:90)
theorem ex_runs_two_resolutions : runs .exposed angelicProg = [.ub, .done [7]]

-- lean/ToyProv/Examples.lean:92
-- ex_beh_angelic_pos  (ToyProv/Examples.lean:92)
theorem ex_beh_angelic_pos : beh .exposed angelicProg = [.done [7]]
```

- **Prior art:**
  - [MiniRust] (full entry under **Evidence**)
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
- **Design question:** Whether choosing a stricter or more permissive provenance model lets optimization soundness results be reused.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Holds because the toy has no allocation-address nondeterminism, deterministic address-only pointer equality, and no way to observe provenance without UB; a language with any of these features is not covered. This is a correspondence argument, not a kernel-checked claim.

### R6d: orderings are strict

- **Kind / tier / depth:** theorem · T0 · definitional. Tier rationale: Concrete evaluations.
- **Plain claim:** A round trip of A's address followed by a store is defined in exposed and UB in strict, and a store through A's one-past-the-end pointer into B is defined in flat and UB in exposed; neither reverse ordering holds. Together with R6a and R6b, flat is strictly more defined than exposed, which is strictly more defined than strict.

Lean statement (`R6d`):

```lean
-- lean/ToyProv/Ordering.lean:131-135
-- model_orderings_strict  (ToyProv/Ordering.lean:131)
theorem model_orderings_strict :
    beh .exposed r6StrictUB = [.done [7]] ∧ beh .strict r6StrictUB = [.ub] ∧
      ¬ SemRefines .strict .exposed r6StrictUB ∧
      beh .flat r6ExposedUB = [.done [7]] ∧ beh .exposed r6ExposedUB = [.ub] ∧
      ¬ SemRefines .exposed .flat r6ExposedUB
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Ordering.lean
/-- Round trip of A's address, store 7 through it, read A back. -/
def r6StrictUB : Prog :=
  [.alloc 0 2, .ptr2int 1 0, .int2ptr 2 1, .const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
-- ToyProv/Ordering.lean
/-- Store 7 through the one-past-the-end pointer of A, read B back. -/
def r6ExposedUB : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .const 3 7, .store 2 3, .load 4 .int 1, .obs 4]
```

Hypothesis ledger: none — the statement has no hypotheses.

- **Non-vacuity witness:** r6StrictUB, r6ExposedUB. Lean: `model_orderings_strict`.

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
- **Design question:** Whether choosing a stricter or more permissive provenance model lets optimization soundness results be reused.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.

### R6e: refinement transfer principles

- **Kind / tier / depth:** theorem · T0 · shallow. Tier rationale: Order-theoretic consequence of R6a (a few lines); restated.
- **Plain claim:** A refinement in strict is a refinement in exposed whenever every strict behaviour of the source is an exposed behaviour of it (SemRefines .strict .exposed src); a refinement in exposed is a refinement in strict whenever every strict behaviour of the target is an exposed behaviour of it (SemRefines .strict .exposed tgt). The core lemmas take the needed instance of R6a as an explicit hypothesis and are fully proved; the two principles discharge it with R6a.

Lean statements (`R6e`):

```lean
-- lean/ToyProv/Ordering.lean:172-174
-- refines_exposed_of_refines_strict_of_src_semRefines  (ToyProv/Ordering.lean:172)
theorem refines_exposed_of_refines_strict_of_src_semRefines (tgt src : Prog)
    (h : Refines .strict tgt src) (hsrc : SemRefines .strict .exposed src) :
    Refines .exposed tgt src

-- lean/ToyProv/Ordering.lean:180-182
-- refines_strict_of_refines_exposed_of_tgt_semRefines  (ToyProv/Ordering.lean:180)
theorem refines_strict_of_refines_exposed_of_tgt_semRefines (tgt src : Prog)
    (h : Refines .exposed tgt src) (htgt : SemRefines .strict .exposed tgt) :
    Refines .strict tgt src

-- lean/ToyProv/Ordering.lean:143-145
-- refines_exposed_of_refines_strict_core  (ToyProv/Ordering.lean:143)
theorem refines_exposed_of_refines_strict_core (tgt src : Prog)
    (h : Refines .strict tgt src) (hsrc : SemRefines .strict .exposed src)
    (hord : SemRefines .exposed .strict tgt) : Refines .exposed tgt src

-- lean/ToyProv/Ordering.lean:157-159
-- refines_strict_of_refines_exposed_core  (ToyProv/Ordering.lean:157)
theorem refines_strict_of_refines_exposed_core (tgt src : Prog)
    (h : Refines .exposed tgt src) (htgt : SemRefines .strict .exposed tgt)
    (hord : SemRefines .exposed .strict src) : Refines .strict tgt src
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Ordering.lean
def r6dTgt : Prog := [.alloc 0 2, .copy 1 0, .const 2 7, .store 0 2, .load 3 .int 0, .obs 3]
-- ToyProv/Ordering.lean
/-- A cast-free pair: substitute an identical copy of A's pointer for A. -/
def r6dSrc : Prog := [.alloc 0 2, .copy 1 0, .const 2 7, .store 1 2, .load 3 .int 0, .obs 3]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h : Refines .strict tgt src (resp. Refines .exposed tgt src)` | The refinement being transferred. | tight | `transfer_refines_needed` (ToyProv/Ordering.lean:187) |
| `hsrc : SemRefines .strict .exposed src (strict -> exposed)` | The source must not rely on exposed provenance: the boundary fold of R3b is a refinement in strict only because the source is UB there. | tight | `transfer_to_exposed_src_agreement_needed` (ToyProv/Ordering.lean:195) |
| `htgt : SemRefines .strict .exposed tgt (exposed -> strict)` | The target must not rely on exposed provenance: the round-trip introduction of R3c. | tight | `transfer_to_strict_tgt_agreement_needed` (ToyProv/Ordering.lean:203) |
| `hord : SemRefines .exposed .strict tgt (resp. src) (core lemmas only)` | An instance of R6a; derivable from R6a for every program, so it is not a hypothesis of the two principles. | harmless | — |

- **Non-vacuity witness:** A cast-free substitution pair (and dupBehProg, whose behaviour lists differ in length but satisfy the SemRefines hypotheses). Lean: `transfer_nonvacuous`.

```lean
-- lean/ToyProv/Ordering.lean:215-219
-- transfer_nonvacuous  (ToyProv/Ordering.lean:215)
theorem transfer_nonvacuous :
    Refines .strict r6dTgt r6dSrc ∧ SemRefines .strict .exposed r6dSrc ∧
      Refines .exposed r6dTgt r6dSrc ∧ SemRefines .strict .exposed r6dTgt ∧
      SemRefines .exposed .strict r6dTgt ∧ SemRefines .exposed .strict r6dSrc ∧
      beh .strict r6dSrc = [.done [7]]
```

Supporting declarations cited in this card's prose (quoted). They are listed in this card's `corollaries_lean` field in `results.json`: `support/revalidate.py` checks that they exist, their axioms are recorded in `audit/axioms.json` (as for every declaration of the library), and no statement hash is recorded for them.

```lean
-- lean/ToyProv/Ordering.lean:225-227
-- transfer_hyp_weaker_than_list_eq  (ToyProv/Ordering.lean:225)
theorem transfer_hyp_weaker_than_list_eq :
    SemRefines .strict .exposed dupBehProg ∧ SemRefines .exposed .strict dupBehProg ∧
      beh .exposed dupBehProg ≠ beh .strict dupBehProg
```

(`dupBehProg` is quoted under R6c.)

- **Prior art:**
  - [Lee et al. 2018] (full entry under **Evidence**)
- **Design question:** Whether choosing a stricter or more permissive provenance model lets optimization soundness results be reused.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.

### R6f: introduce roundtrip refines exposed if candidate

- **Kind / tier / depth:** theorem · T1 · substantive. Tier rationale: The precise form of 'the exposed set contains p's allocation, so int2ptr can recover it'; VIP's copy_alloc_id addresses the same need by naming the provenance explicitly.
- **Plain claim:** In the exposed model, replacing d := p by d := int2ptr k is a refinement provided that, in every reachable state at that point, k holds p's address (hk) and p's allocation is an int2ptr candidate for it (hc: exposed, live, address in its closed range); uniqueness is not needed in this direction.

Lean statement (`R6f`):

```lean
-- lean/ToyProv/Ordering.lean:387-391
-- copyToInt2ptr_refines_exposed_of_intIsAddrOf_of_provIsCand  (ToyProv/Ordering.lean:387)
theorem copyToInt2ptr_refines_exposed_of_intIsAddrOf_of_provIsCand
    (pre post : Prog) (d k p : Reg)
    (hk : AllAfter .exposed pre (intIsAddrOfC k p))
    (hc : AllAfter .exposed pre (provIsCandC p)) :
    Refines .exposed (pre ++ .int2ptr d k :: post) (pre ++ .copy d p :: post)
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/RoundTrip.lean
def r3Pre : Prog := [.alloc 0 2, .ptr2int 1 0]
-- ToyProv/RoundTrip.lean
def r3Post : Prog := [.const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hk : AllAfter .exposed pre (intIsAddrOfC k p)` | Ties the integer to p's address. | tight | `copyToInt2ptr_intIsAddrOf_needed` (ToyProv/Ordering.lean:477) |
| `hc : AllAfter .exposed pre (provIsCandC p)` | If p's allocation was never exposed the cast cannot recover it. | tight | `copyToInt2ptr_provIsCand_needed` (ToyProv/Ordering.lean:471) |

- **Non-vacuity witness:** After k := ptr2int A. Lean: `copyToInt2ptr_refines_exposed_nonvacuous`.

```lean
-- lean/ToyProv/Ordering.lean:484-486
-- copyToInt2ptr_refines_exposed_nonvacuous  (ToyProv/Ordering.lean:484)
theorem copyToInt2ptr_refines_exposed_nonvacuous :
    AllAfter .exposed r3Pre (intIsAddrOfC 1 0) ∧ AllAfter .exposed r3Pre (provIsCandC 0) ∧
      Refines .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post)
```

- **Prior art:**
  - [TS 6010 / P2318R0] (full entry under **Evidence**)
  - [Rust 1.84.0 documentation] (full entry under **Evidence**)
  - [MiniRust] (full entry under **Evidence**)
  - [Lepigre et al. 2022] (full entry under **Evidence**)
- **Design question:** When an optimizer may fold or introduce integer-pointer round trips (inttoptr(ptrtoint p) vs p) under strict and exposed provenance.
- Basis: execution (Lean kernel check) — the statement above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Captures the informal rule that `int2ptr` can recover an allocation once it is exposed; VIP's `copy_alloc_id` (Lepigre et al. 2022) addresses the same need by naming the provenance explicitly. The address restriction inside `provIsCandC` has no counterpart in MiniRust's `int2ptr`; the MiniRust analogue of this result is not examined. This is a correspondence argument, not a kernel-checked claim.

### R6g: optimization soundness table

- **Kind / tier / depth:** characterization · T1 · substantive. Tier rationale: Each row is folklore in the provenance literature (several are Coq-verified in other models: Kang et al. 2015 for dead casts, Lee et al. 2018 for pointer GVN); the table with every entry a Lean theorem or decidable counterexample in one semantics is the contribution.
- **Plain claim:** For ten transformations and the three models (flat, strict, exposed), soundness is: SubstAddrEq ✓✗✗; SubstAddrEqInBounds ✓✓✓; SubstIntEq ✓✗✗; SubstSameVal ✓✓✓; Int2ptrToCopy (fold) ✓✓✗; CopyToInt2ptr (introduce) ✓✗✗; CopyToInt2ptrIfCand (introduce when p's allocation is a candidate) ✓✗✓; DropUnusedPtr2int ✓✓✗; ForwardAcrossCast ✗✓✗; DSEAcrossCast ✗✓✗. The table has 17 ✓ and 13 ✗ entries. 14 of the 17 ✓ entries are non-vacuous: each is inhabited by a pair in the relation whose source is defined in that model (soundness_table_nonvacuous). The other 3 ✓ entries are vacuous, holding only because every matching source is UB (soundness_table_vacuous_cells): CopyToInt2ptrIfCand in flat (no flat pointer carries the provenance its candidate condition requires), and ForwardAcrossCast and DSEAcrossCast in strict. A vacuous ✓ is not evidence that the transformation is safe on defined programs. Soundness transfers neither from strict to exposed (DropUnusedPtr2int) nor from exposed to strict (CopyToInt2ptrIfCand).

Lean statements (`R6g`):

```lean
-- lean/ToyProv/FlatInv.lean:301
-- substAddrEq_sound_flat  (ToyProv/FlatInv.lean:301)
theorem substAddrEq_sound_flat : Sound .flat SubstAddrEq

-- lean/ToyProv/OnePast.lean:71
-- substAddrEq_not_sound_strict  (ToyProv/OnePast.lean:71)
theorem substAddrEq_not_sound_strict : ¬ Sound .strict SubstAddrEq

-- lean/ToyProv/OnePast.lean:74
-- substAddrEq_not_sound_exposed  (ToyProv/OnePast.lean:74)
theorem substAddrEq_not_sound_exposed : ¬ Sound .exposed SubstAddrEq

-- lean/ToyProv/Ordering.lean:527
-- substAddrEqInBounds_sound_all  (ToyProv/Ordering.lean:527)
theorem substAddrEqInBounds_sound_all : ∀ m, Sound m SubstAddrEqInBounds

-- lean/ToyProv/Ordering.lean:235
-- substIntEq_sound_flat  (ToyProv/Ordering.lean:235)
theorem substIntEq_sound_flat : Sound .flat SubstIntEq

-- lean/ToyProv/IntEq.lean:48
-- substIntEq_not_sound_strict  (ToyProv/IntEq.lean:48)
theorem substIntEq_not_sound_strict : ¬ Sound .strict SubstIntEq

-- lean/ToyProv/IntEq.lean:51
-- substIntEq_not_sound_exposed  (ToyProv/IntEq.lean:51)
theorem substIntEq_not_sound_exposed : ¬ Sound .exposed SubstIntEq

-- lean/ToyProv/IntEq.lean:77
-- substSameVal_sound  (ToyProv/IntEq.lean:77)
theorem substSameVal_sound (m : Model) : Sound m SubstSameVal

-- lean/ToyProv/Ordering.lean:244
-- int2ptrToCopy_sound_flat  (ToyProv/Ordering.lean:244)
theorem int2ptrToCopy_sound_flat : Sound .flat Int2ptrToCopy

-- lean/ToyProv/Ordering.lean:271
-- int2ptrToCopy_sound_strict  (ToyProv/Ordering.lean:271)
theorem int2ptrToCopy_sound_strict : Sound .strict Int2ptrToCopy

-- lean/ToyProv/RoundTrip.lean:64
-- int2ptrToCopy_not_sound_exposed  (ToyProv/RoundTrip.lean:64)
theorem int2ptrToCopy_not_sound_exposed : ¬ Sound .exposed Int2ptrToCopy

-- lean/ToyProv/Ordering.lean:346
-- copyToInt2ptr_sound_flat  (ToyProv/Ordering.lean:346)
theorem copyToInt2ptr_sound_flat : Sound .flat CopyToInt2ptr

-- lean/ToyProv/RoundTrip.lean:121
-- copyToInt2ptr_not_sound_strict  (ToyProv/RoundTrip.lean:121)
theorem copyToInt2ptr_not_sound_strict : ¬ Sound .strict CopyToInt2ptr

-- lean/ToyProv/Ordering.lean:380
-- copyToInt2ptr_not_sound_exposed  (ToyProv/Ordering.lean:380)
theorem copyToInt2ptr_not_sound_exposed : ¬ Sound .exposed CopyToInt2ptr

-- lean/ToyProv/Ordering.lean:577
-- copyToInt2ptrIfCand_sound_flat  (ToyProv/Ordering.lean:577)
theorem copyToInt2ptrIfCand_sound_flat : Sound .flat CopyToInt2ptrIfCand

-- lean/ToyProv/Ordering.lean:590
-- copyToInt2ptrIfCand_not_sound_strict  (ToyProv/Ordering.lean:590)
theorem copyToInt2ptrIfCand_not_sound_strict : ¬ Sound .strict CopyToInt2ptrIfCand

-- lean/ToyProv/Ordering.lean:531
-- copyToInt2ptrIfCand_sound_exposed  (ToyProv/Ordering.lean:531)
theorem copyToInt2ptrIfCand_sound_exposed : Sound .exposed CopyToInt2ptrIfCand

-- lean/ToyProv/Ordering.lean:490
-- dropUnusedPtr2int_sound_flat  (ToyProv/Ordering.lean:490)
theorem dropUnusedPtr2int_sound_flat : Sound .flat DropUnusedPtr2int

-- lean/ToyProv/Ordering.lean:494
-- dropUnusedPtr2int_sound_strict  (ToyProv/Ordering.lean:494)
theorem dropUnusedPtr2int_sound_strict : Sound .strict DropUnusedPtr2int

-- lean/ToyProv/Ordering.lean:507
-- dropUnusedPtr2int_not_sound_exposed  (ToyProv/Ordering.lean:507)
theorem dropUnusedPtr2int_not_sound_exposed : ¬ Sound .exposed DropUnusedPtr2int

-- lean/ToyProv/Forwarding.lean:40
-- forwardAcrossCast_not_sound_flat  (ToyProv/Forwarding.lean:40)
theorem forwardAcrossCast_not_sound_flat : ¬ Sound .flat ForwardAcrossCast

-- lean/ToyProv/Ordering.lean:512
-- forwardAcrossCast_sound_strict  (ToyProv/Ordering.lean:512)
theorem forwardAcrossCast_sound_strict : Sound .strict ForwardAcrossCast

-- lean/ToyProv/Forwarding.lean:37
-- forwardAcrossCast_not_sound_exposed  (ToyProv/Forwarding.lean:37)
theorem forwardAcrossCast_not_sound_exposed : ¬ Sound .exposed ForwardAcrossCast

-- lean/ToyProv/Forwarding.lean:89
-- dseAcrossCast_not_sound_flat  (ToyProv/Forwarding.lean:89)
theorem dseAcrossCast_not_sound_flat : ¬ Sound .flat DSEAcrossCast

-- lean/ToyProv/Ordering.lean:520
-- dseAcrossCast_sound_strict  (ToyProv/Ordering.lean:520)
theorem dseAcrossCast_sound_strict : Sound .strict DSEAcrossCast

-- lean/ToyProv/Forwarding.lean:86
-- dseAcrossCast_not_sound_exposed  (ToyProv/Forwarding.lean:86)
theorem dseAcrossCast_not_sound_exposed : ¬ Sound .exposed DSEAcrossCast

-- lean/ToyProv/Ordering.lean:666-669
-- soundness_table_vacuous_cells  (ToyProv/Ordering.lean:666)
theorem soundness_table_vacuous_cells :
    (∀ src tgt, CopyToInt2ptrIfCand .flat src tgt → beh .flat src = [.ub]) ∧
    (∀ src tgt, ForwardAcrossCast .strict src tgt → beh .strict src = [.ub]) ∧
    (∀ src tgt, DSEAcrossCast .strict src tgt → beh .strict src = [.ub])

-- lean/ToyProv/Ordering.lean:596-598
-- soundness_does_not_transfer_either_way  (ToyProv/Ordering.lean:596)
theorem soundness_does_not_transfer_either_way :
    (Sound .strict DropUnusedPtr2int ∧ ¬ Sound .exposed DropUnusedPtr2int) ∧
      (Sound .exposed CopyToInt2ptrIfCand ∧ ¬ Sound .strict CopyToInt2ptrIfCand)

-- lean/ToyProv/Ordering.lean:605-611
-- refines_does_not_transfer_either_way  (ToyProv/Ordering.lean:605)
theorem refines_does_not_transfer_either_way :
    (DropUnusedPtr2int .strict ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP) ([.alloc 0 2] ++ r6PostP) ∧
      Refines .strict ([.alloc 0 2] ++ r6PostP) ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP) ∧
      ¬ Refines .exposed ([.alloc 0 2] ++ r6PostP) ([.alloc 0 2] ++ .ptr2int 1 0 :: r6PostP)) ∧
    (CopyToInt2ptrIfCand .exposed (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      Refines .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) ∧
      ¬ Refines .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post))
```

Soundness table (`Sound m T` means every rewrite `T m src tgt` is a refinement in `m`). ✓ = `Sound` proved; ✗ = `¬ Sound` proved by a concrete pair in the relation that is not a refinement (a non-refinement always has a source that is not UB); **✓ vacuous** = `Sound` holds only because every source in the relation is UB in that model; the superscript gives the conjunct of `soundness_table_nonvacuous` that inhabits a non-vacuous ✓ with a pair whose source is defined.

| transformation | flat | strict | exposed |
| --- | --- | --- | --- |
| `SubstAddrEq` | ✓¹ `substAddrEq_sound_flat` | ✗ `substAddrEq_not_sound_strict` | ✗ `substAddrEq_not_sound_exposed` |
| `SubstAddrEqInBounds` | ✓² `substAddrEqInBounds_sound_all` | ✓² `substAddrEqInBounds_sound_all` | ✓² `substAddrEqInBounds_sound_all` |
| `SubstIntEq` | ✓³ `substIntEq_sound_flat` | ✗ `substIntEq_not_sound_strict` | ✗ `substIntEq_not_sound_exposed` |
| `SubstSameVal` | ✓⁴ `substSameVal_sound` | ✓⁴ `substSameVal_sound` | ✓⁴ `substSameVal_sound` |
| `Int2ptrToCopy` (fold) | ✓⁵ `int2ptrToCopy_sound_flat` | ✓⁵ `int2ptrToCopy_sound_strict` | ✗ `int2ptrToCopy_not_sound_exposed` |
| `CopyToInt2ptr` (introduce) | ✓⁶ `copyToInt2ptr_sound_flat` | ✗ `copyToInt2ptr_not_sound_strict` | ✗ `copyToInt2ptr_not_sound_exposed` |
| `CopyToInt2ptrIfCand` | **✓ vacuous** `copyToInt2ptrIfCand_sound_flat` | ✗ `copyToInt2ptrIfCand_not_sound_strict` | ✓⁷ `copyToInt2ptrIfCand_sound_exposed` |
| `DropUnusedPtr2int` | ✓⁸ `dropUnusedPtr2int_sound_flat` | ✓⁸ `dropUnusedPtr2int_sound_strict` | ✗ `dropUnusedPtr2int_not_sound_exposed` |
| `ForwardAcrossCast` | ✗ `forwardAcrossCast_not_sound_flat` | **✓ vacuous** `forwardAcrossCast_sound_strict` | ✗ `forwardAcrossCast_not_sound_exposed` |
| `DSEAcrossCast` | ✗ `dseAcrossCast_not_sound_flat` | **✓ vacuous** `dseAcrossCast_sound_strict` | ✗ `dseAcrossCast_not_sound_exposed` |

Counts: 17 ✓ and 13 ✗. **Non-vacuous ✓ (14):** `SubstAddrEq` flat (¹, `r1Src` outputs `[1, 7]`); `SubstAddrEqInBounds` in all three models (², source outputs `[7]`); `SubstIntEq` flat (³, `r2Src` outputs `[1, 7]`); `SubstSameVal` in all three models (⁴, `[7]`); `Int2ptrToCopy` flat and strict (⁵, the fold pair over `r2bPreTorn`, source outputs `[16]`); `CopyToInt2ptr` flat (⁶, `[7]`); `CopyToInt2ptrIfCand` exposed (⁷, `[7]`); `DropUnusedPtr2int` flat and strict (⁸, `[7]`). **Vacuous ✓ (3):** `CopyToInt2ptrIfCand` flat (no reachable flat pointer has a provenance, so `provIsCandC` never holds and `after .flat pre = []`; `copyToInt2ptrIfCand_flat_src_ub`), `ForwardAcrossCast` strict and `DSEAcrossCast` strict (the window stores or loads through the provenance-less result of strict `int2ptr`; `forwardAcrossCast_strict_src_ub`, `dseAcrossCast_strict_src_ub`). All three are collected in `soundness_table_vacuous_cells`. A vacuous ✓ says nothing about defined programs and must not be cited as evidence that the transformation is safe; for introducing casts in flat, the informative entry is the non-vacuous `CopyToInt2ptr` flat ✓.

The ✓ entries in `exposed` that hold in strict too (`SubstAddrEqInBounds`, `SubstSameVal`) are exactly the exposed-sound rows without a candidate side condition; `CopyToInt2ptrIfCand`, whose side condition mentions exposure, is the row that separates exposed from strict.

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Ordering.lean
/-- A at 16; after the rewrite point, A's address is guessed as 16, cast back, and stored
through. -/
def r6PostP : Prog := [.const 2 16, .int2ptr 3 2, .const 4 7, .store 3 4, .load 5 .int 0, .obs 5]
-- ToyProv/RoundTrip.lean
def r3Pre : Prog := [.alloc 0 2, .ptr2int 1 0]
-- ToyProv/RoundTrip.lean
def r3Post : Prog := [.const 3 7, .store 2 3, .load 4 .int 0, .obs 4]
-- ToyProv/OnePast.lean
/-- Source: store through `q` (register 1, B's start). -/
def r1Src : Prog := r1Pre ++ .store 1 4 :: r1Post
-- ToyProv/OnePast.lean
/-- Target: the store's pointer operand `q` replaced by the address-equal `p` (register 2,
one past A's end). -/
def r1Tgt : Prog := r1Pre ++ (Instr.store 1 4).substUse 1 2 :: r1Post
-- ToyProv/OnePast.lean
/-- Code before the rewrite point: A; `q := A`; `p := (A + 1) - 1`. -/
def r1cPreNV : Prog := [.alloc 0 2, .copy 1 0, .offset 2 0 1, .offset 2 2 (-1), .const 3 7]
-- ToyProv/IntEq.lean
/-- Source: store through `q` (B's start). -/
def r2Src : Prog := r2Pre ++ .store 1 6 :: r2Post
-- ToyProv/IntEq.lean
/-- Target: `q` replaced by `p` (one past A's end), justified by `(int)p == (int)q`. -/
def r2Tgt : Prog := r2Pre ++ (Instr.store 1 6).substUse 1 2 :: r2Post
-- ToyProv/Ordering.lean
/-- Code before the rewrite point for the `SubstSameVal` witness: A and an identical copy (register
1) of A's pointer. -/
def r6gSameValPre : Prog := [.alloc 0 2, .copy 1 0, .const 2 7]
-- ToyProv/Ordering.lean
/-- Read A back and observe it. -/
def r6gReadPost : Prog := [.load 3 .int 0, .obs 3]
-- ToyProv/IntEq.lean
/-- A (unexposed, at 16), B, C; `k := 16`; `q := int2ptr k` (no candidate, so no provenance) is
stored into B. -/
def r2bPreTorn : Prog := [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3, .store 1 4]
-- ToyProv/IntEq.lean
/-- Store `d` into C, copy B's first byte over C's first byte, load C at integer type. -/
def r2bPostTorn : Prog := [.store 2 5, .memcpy 2 1 1, .load 6 .int 2, .obs 6]
-- ToyProv/Ordering.lean
/-- After an unused `ptr2int`: store 7 into A, read it back. -/
def r6gDropPost : Prog := [.const 2 7, .store 0 2, .load 3 .int 0, .obs 3]
-- ToyProv/OnePast.lean
/-- Code before the rewrite point: A, B, `p := A + 2`, observe `p == q` (it is `1`), `t := 7`. -/
def r1Pre : Prog := [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptrEq 3 2 1, .obs 3, .const 4 7]
-- ToyProv/OnePast.lean
/-- Code after the rewrite point: read B back and observe it. -/
def r1Post : Prog := [.load 5 .int 1, .obs 5]
-- ToyProv/IntEq.lean
/-- A, B, `p := A + 2`, cast both to integers, observe that the integers are equal, `t := 7`. -/
def r2Pre : Prog :=
  [.alloc 0 2, .alloc 1 2, .offset 2 0 2, .ptr2int 3 2, .ptr2int 4 1, .intEq 5 3 4, .obs 5, .const 6 7]
-- ToyProv/IntEq.lean
def r2Post : Prog := [.load 7 .int 1, .obs 7]
```

Hypothesis ledger: none — the statement has no hypotheses.

- **Non-vacuity witness:** Each ✗ entry is witnessed by a concrete pair satisfying the transformation's side conditions. Each ✓ entry except the three vacuous ones is inhabited by a concrete pair in the relation whose source is defined in that model, with its output evaluated (soundness_table_nonvacuous). The three vacuous ✓ entries (CopyToInt2ptrIfCand in flat, ForwardAcrossCast and DSEAcrossCast in strict) are inhabited only by pairs whose source is UB (soundness_table_vacuous_cells). The non-transfer pairs are evaluated in refines_does_not_transfer_either_way. Lean: `soundness_table_nonvacuous`, `refines_does_not_transfer_either_way`.

```lean
-- lean/ToyProv/Ordering.lean:626-644
-- soundness_table_nonvacuous  (ToyProv/Ordering.lean:626)
theorem soundness_table_nonvacuous :
    (SubstAddrEq .flat r1Src r1Tgt ∧ beh .flat r1Src = [.done [1, 7]]) ∧
    (∀ m, SubstAddrEqInBounds m (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4])
        (r1cPreNV ++ (Instr.store 1 3).substUse 1 2 :: [.load 4 .int 0, .obs 4]) ∧
      beh m (r1cPreNV ++ .store 1 3 :: [.load 4 .int 0, .obs 4]) = [.done [7]]) ∧
    (SubstIntEq .flat r2Src r2Tgt ∧ beh .flat r2Src = [.done [1, 7]]) ∧
    (∀ m, SubstSameVal m (r6gSameValPre ++ .store 1 2 :: r6gReadPost)
        (r6gSameValPre ++ (Instr.store 1 2).substUse 1 0 :: r6gReadPost) ∧
      beh m (r6gSameValPre ++ .store 1 2 :: r6gReadPost) = [.done [7]]) ∧
    (∀ m, m ≠ .exposed →
      Int2ptrToCopy m (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) (r2bPreTorn ++ .copy 5 0 :: r2bPostTorn) ∧
        beh m (r2bPreTorn ++ .int2ptr 5 3 :: r2bPostTorn) = [.done [16]]) ∧
    (CopyToInt2ptr .flat (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      beh .flat (r3Pre ++ .copy 2 0 :: r3Post) = [.done [7]]) ∧
    (CopyToInt2ptrIfCand .exposed (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      beh .exposed (r3Pre ++ .copy 2 0 :: r3Post) = [.done [7]]) ∧
    (∀ m, m ≠ .exposed →
      DropUnusedPtr2int m ([.alloc 0 2] ++ .ptr2int 1 0 :: r6gDropPost) ([.alloc 0 2] ++ r6gDropPost) ∧
        beh m ([.alloc 0 2] ++ .ptr2int 1 0 :: r6gDropPost) = [.done [7]])
```

Supporting declarations cited in this card's prose (quoted). They are listed in this card's `corollaries_lean` field in `results.json`: `support/revalidate.py` checks that they exist, their axioms are recorded in `audit/axioms.json` (as for every declaration of the library), and no statement hash is recorded for them.

```lean
-- lean/ToyProv/Ordering.lean:539-541
-- copyToInt2ptrIfCand_flat_src_ub  (ToyProv/Ordering.lean:539)
theorem copyToInt2ptrIfCand_flat_src_ub (src tgt : Prog)
    (h : CopyToInt2ptrIfCand .flat src tgt) :
    beh .flat src = [.ub] ∧ beh .flat tgt = [.ub]

-- lean/ToyProv/Ordering.lean:567-568
-- not_copyToInt2ptrIfCand_flat_r3  (ToyProv/Ordering.lean:567)
theorem not_copyToInt2ptrIfCand_flat_r3 :
    ¬ CopyToInt2ptrIfCand .flat (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post)
```

- **Prior art:**
  - [Jung 2020] (full entry under **Evidence**)
  - [Jung 2022] (full entry under **Evidence**)
  - [Lee et al. 2018] (full entry under **Evidence**)
  - [Memarian et al. 2019] (full entry under **Evidence**)
  - [Kang et al. 2015] (full entry under **Evidence**)
  - [Beck et al. 2024] (full entry under **Evidence**)
- **Design question:** Whether choosing a stricter or more permissive provenance model lets optimization soundness results be reused.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — Each row is folklore in the provenance literature (Kang et al. 2015 for dead casts; Lee et al. 2018 for pointer GVN; Jung 2020 and 2022 for the round-trip and cast-exposure examples). The table is a statement about this package's ten relations in three toy models, not about any compiler's passes. This is a correspondence argument, not a kernel-checked claim.

### R7a: identical provenance decoding breaks monotonicity

- **Kind / tier / depth:** counterexample · T1 · definitional. Tier rationale: MiniRust states monotonicity of decoding as a requirement and chooses 'no provenance' for mixed pointer bytes; the concrete program-level consequences for these model orderings and cast folds are not found stated.
- **Plain claim:** In the variant semantics where a pointer is decoded from two bytes only if both carry the identical pointer (same-address fragments with different provenances are UB), adding provenance can introduce UB: the exposed model does not refine the strict model (a program outputs [16] in strict and is UB in exposed), folding d := int2ptr k into d := p with k == (int)p is not a refinement in strict, R2b's fold fails in the case with no candidate, and both transfer principles of R6e fail. With this package's decoder (mixed provenance yields a pointer without provenance) the same programs are well behaved.

Lean statements (`R7a`):

```lean
-- lean/ToyProv/EqProvDecode.lean:101-106
-- EqProvDecode.decodeEq_not_monotone  (ToyProv/EqProvDecode.lean:101)
theorem decodeEq_not_monotone :
    AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨some 0, 16⟩ 1) ∧
      decodeIntEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (16, []) ∧
      decodeIntEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = none ∧
      decodePtrEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (.inl ⟨none, 16⟩) ∧
      decodePtrEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = none

-- lean/ToyProv/EqProvDecode.lean:121-123
-- EqProvDecode.eqProvDecode_exposed_not_semRefines_strict  (ToyProv/EqProvDecode.lean:121)
theorem eqProvDecode_exposed_not_semRefines_strict :
    behE .strict tornProg = [.done [16]] ∧ behE .exposed tornProg = [.ub] ∧
      ¬ SemRefinesE .exposed .strict tornProg

-- lean/ToyProv/EqProvDecode.lean:137-143
-- EqProvDecode.eqProvDecode_fold_not_refinement  (ToyProv/EqProvDecode.lean:137)
theorem eqProvDecode_fold_not_refinement :
    AllAfterE .strict foldPre (intIsAddrOfC 3 0) ∧
      behE .strict (foldPre ++ .int2ptr 5 3 :: foldPost) = [.done [16]] ∧
      behE .strict (foldPre ++ .copy 5 0 :: foldPost) = [.ub] ∧
      ¬ RefinesE .strict (foldPre ++ .copy 5 0 :: foldPost) (foldPre ++ .int2ptr 5 3 :: foldPost) ∧
      AllAfterE .exposed foldPre (intIsAddrOfC 3 0) ∧ AllAfterE .exposed foldPre (candSubProvC 0) ∧
      ¬ RefinesE .exposed (foldPre ++ .copy 5 0 :: foldPost) (foldPre ++ .int2ptr 5 3 :: foldPost)

-- lean/ToyProv/EqProvDecode.lean:148-154
-- EqProvDecode.eqProvDecode_transfer_fails  (ToyProv/EqProvDecode.lean:148)
theorem eqProvDecode_transfer_fails :
    (RefinesE .strict tornProg [.const 0 16, .obs 0] ∧
        behE .exposed [.const 0 16, .obs 0] = behE .strict [.const 0 16, .obs 0] ∧
        ¬ RefinesE .exposed tornProg [.const 0 16, .obs 0]) ∧
      (RefinesE .exposed [.const 0 99, .obs 0] tornProg ∧
        behE .strict [.const 0 99, .obs 0] = behE .exposed [.const 0 99, .obs 0] ∧
        ¬ RefinesE .strict [.const 0 99, .obs 0] tornProg)

-- lean/ToyProv/EqProvDecode.lean:179-186
-- EqProvDecode.eqProvDecode_ptr_load_variants  (ToyProv/EqProvDecode.lean:179)
theorem eqProvDecode_ptr_load_variants :
    behE .strict tornProgPtr = [.done [16]] ∧ behE .exposed tornProgPtr = [.ub] ∧
      behE .strict (foldPre ++ .int2ptr 5 3 :: foldPostPtr) = [.done [16]] ∧
      behE .strict (foldPre ++ .copy 5 0 :: foldPostPtr) = [.ub] ∧
      beh .strict tornProgPtr = [.done [16]] ∧ beh .exposed tornProgPtr = [.done [16]] ∧
      beh .strict (foldPre ++ .copy 5 0 :: foldPostPtr) = [.done [16]] ∧
      beh .exposed (foldPre ++ .copy 5 0 :: foldPostPtr) = [.done [16]] ∧
      beh .exposed (foldPre ++ .int2ptr 5 3 :: foldPostPtr) = [.done [16]]
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Monotone.lean
/-- Information order on abstract bytes: identical, except that a pointer fragment may carry a
pointer with more provenance. -/
def AByteLE : AByte → AByte → Prop
  | .uninit, .uninit => True
  | .intFrag n i, .intFrag n' i' => n = n' ∧ i = i'
  | .ptrFrag p i, .ptrFrag q i' => PtrLE p q ∧ i = i'
  | _, _ => False
-- ToyProv/EqProvDecode.lean
/-- Integer decoding that requires the two fragments to carry identical pointers. -/
def decodeIntEq : AByte → AByte → Option (Nat × List AllocId)
  | .intFrag n 0, .intFrag n' 1 => if n = n' then some (n, []) else none
  | .ptrFrag p 0, .ptrFrag p' 1 => if p = p' then some (p.addr, p.prov.toList) else none
  | _, _ => none
-- ToyProv/EqProvDecode.lean
/-- Pointer decoding that requires the two fragments to carry identical pointers. -/
def decodePtrEq : AByte → AByte → Option (Ptr ⊕ Nat)
  | .ptrFrag p 0, .ptrFrag p' 1 => if p = p' then some (.inl p) else none
  | .intFrag n 0, .intFrag n' 1 => if n = n' then some (.inr n) else none
  | _, _ => none
-- ToyProv/EqProvDecode.lean
def behE (m : Model) (P : Prog) : List Outcome :=
  let r := runsE m P
  if r.all (fun o => decide (o = .ub)) then [.ub] else r.filter (fun o => decide (o ≠ .ub))
-- ToyProv/EqProvDecode.lean
/-- A, B, C; `r := int2ptr 16` before A is exposed (no provenance in both models); then A is
exposed and `q := int2ptr 16` (no provenance in `strict`, A's in `exposed`); `r` is stored into
B and `q` into C; one byte of B is copied over C's first byte, and C is loaded at integer type. -/
def tornProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3,
   .ptr2int 5 0, .int2ptr 6 5, .store 1 4, .store 2 6, .memcpy 2 1 1,
   .load 7 .int 2, .obs 7]
-- ToyProv/EqProvDecode.lean
def SemRefinesE (m₁ m₂ : Model) (P : Prog) : Prop :=
  Outcome.ub ∈ behE m₂ P ∨ ∀ o ∈ behE m₁ P, o ∈ behE m₂ P
-- ToyProv/EqProvDecode.lean
def AllAfterE (m : Model) (pre : Prog) (c : St → Bool) : Prop :=
  ∀ s ∈ (execE m pre init).filterMap id, c s = true
-- ToyProv/EqProvDecode.lean
/-- The programs of `int2ptrToCopy_refines_exposed_no_candidate_example` (R2b): A (unexposed),
B, C; `k := 16` (A's address); `q := int2ptr k` (no provenance) is stored into B; after the
rewrite point `d` is stored into C, B's first byte is copied over C's, and C is loaded at
integer type. -/
abbrev foldPre : Prog := r2bPreTorn
-- ToyProv/EqProvDecode.lean
abbrev foldPost : Prog := r2bPostTorn
-- ToyProv/EqProvDecode.lean
def RefinesE (m : Model) (tgt src : Prog) : Prop :=
  Outcome.ub ∈ behE m src ∨ ∀ o ∈ behE m tgt, o ∈ behE m src
-- ToyProv/EqProvDecode.lean
/-- The same programs with a pointer-typed final load. -/
def tornProgPtr : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3,
   .ptr2int 5 0, .int2ptr 6 5, .store 1 4, .store 2 6, .memcpy 2 1 1,
   .load 7 .ptr 2, .obs 7]
-- ToyProv/EqProvDecode.lean
def foldPostPtr : Prog := [.store 2 5, .memcpy 2 1 1, .load 6 .ptr 2, .obs 6]
-- ToyProv/Monotone.lean
/-- Information order on pointers: same address, provenance below. -/
def PtrLE (p q : Ptr) : Prop := p.addr = q.addr ∧ ProvLE p.prov q.prov
-- ToyProv/EqProvDecode.lean
def runsE (m : Model) (P : Prog) : List Outcome :=
  (execE m P init).map (fun o => match o with
    | none => .ub
    | some s => .done s.out)
-- ToyProv/EqProvDecode.lean
def execE (m : Model) : Prog → St → List (Option St)
  | [], s => [some s]
  | i :: is, s =>
    (stepE m s i).flatMap (fun o =>
      match o with
      | none => [none]
      | some s' => execE m is s')
-- ToyProv/IntEq.lean
/-- A (unexposed, at 16), B, C; `k := 16`; `q := int2ptr k` (no candidate, so no provenance) is
stored into B. -/
def r2bPreTorn : Prog := [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3, .store 1 4]
-- ToyProv/IntEq.lean
/-- Store `d` into C, copy B's first byte over C's first byte, load C at integer type. -/
def r2bPostTorn : Prog := [.store 2 5, .memcpy 2 1 1, .load 6 .int 2, .obs 6]
-- ToyProv/Monotone.lean
/-- Information order on provenances: `none` is below every provenance, `some id` only below
itself. -/
def ProvLE (a b : Option AllocId) : Prop := a = none ∨ a = b
-- ToyProv/EqProvDecode.lean
/-- One step of the variant semantics: `load` uses `decodeIntEq` / `decodePtrEq`; every other
instruction steps exactly as in `Toy.Prov.step`. -/
def stepE (m : Model) (s : St) : Instr → List (Option St)
  | .load d ty p =>
    match s.regs p with
    | some (.ptr x) =>
      if canAccess m s x 2 then
        match ty with
        | .int =>
          match decodeIntEq (s.mem x.addr) (s.mem (x.addr + 1)) with
          | some (n, ps) => [some ((s.setReg d (.int n)).expose ps)]
          | none => [none]
        | .ptr =>
          match decodePtrEq (s.mem x.addr) (s.mem (x.addr + 1)) with
          | some (.inl q) => [some (s.setReg d (.ptr q))]
          | some (.inr n) => castToPtr m s d n
          | none => [none]
      else [none]
    | _ => [none]
  | i => step m s i
```

Hypothesis ledger: none — the statement is a closed, fully evaluated instance.

- **Non-vacuity witness:** tornProg and the r2bPreTorn fold pair. Lean: `EqProvDecode.eqProvDecode_exposed_not_semRefines_strict`.
- **Positive control** (a nearby setting where the negative conclusion fails): `EqProvDecode.mainDecode_same_programs_ok`.

```lean
-- lean/ToyProv/EqProvDecode.lean:160-166
-- EqProvDecode.mainDecode_same_programs_ok  (ToyProv/EqProvDecode.lean:160)
theorem mainDecode_same_programs_ok :
    beh .strict tornProg = [.done [16]] ∧ beh .exposed tornProg = [.done [16]] ∧
      SemRefines .exposed .strict tornProg ∧
      beh .strict (foldPre ++ .copy 5 0 :: foldPost) = [.done [16]] ∧
      beh .strict (foldPre ++ .int2ptr 5 3 :: foldPost) = [.done [16]] ∧
      beh .exposed (foldPre ++ .copy 5 0 :: foldPost) = [.done [16]] ∧
      beh .exposed (foldPre ++ .int2ptr 5 3 :: foldPost) = [.done [16]]
```

Supporting declarations cited in this card's prose (quoted). They are listed in this card's `corollaries_lean` field in `results.json`: `support/revalidate.py` checks that they exist, their axioms are recorded in `audit/axioms.json` (as for every declaration of the library), and no statement hash is recorded for them.

```lean
-- lean/ToyProv/EqProvDecode.lean:58-59
-- EqProvDecode.stepE_eq_step_of_not_load  (ToyProv/EqProvDecode.lean:58)
theorem stepE_eq_step_of_not_load (m : Model) (s : St) (i : Instr)
    (h : ∀ d ty p, i ≠ .load d ty p) : stepE m s i = step m s i
```

- **Prior art:**
  - [MiniRust] (full entry under **Evidence**)
- **Design question:** How a byte-level semantics must decode pointer bytes with mixed provenance so that adding provenance never introduces UB, which the model ordering and the cast-fold results depend on.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — MiniRust requires decoding to be monotone and chooses "a pointer without provenance" for pointer bytes with mixed provenance (commit `063d784186d3252bee242217f218223205c0b568`, `spec/lang/representation.md`). R7a shows, in the toy, what goes wrong without that choice; it does not say which decoding any real language uses. This is a correspondence argument, not a kernel-checked claim.

### R7b: pointer byte decoding is provenance monotone

- **Kind / tier / depth:** theorem · T1 · shallow. Tier rationale: The monotonicity law MiniRust requires of decode, proved for this toy's two-byte decoders.
- **Plain claim:** If each of two abstract bytes is below the corresponding byte of a second pair in the information order (identical, except that a pointer fragment may carry more provenance: none below some id), then a defined integer decoding of the first pair is defined on the second with the same integer and a superset of exposed provenances, a pointer decoding of integer fragments gives the same bare address, and a pointer decoding of pointer fragments gives a pointer with the same address and at least as much provenance.

Lean statements (`R7b`):

```lean
-- lean/ToyProv/Monotone.lean:91-93
-- decodeInt_mono  (ToyProv/Monotone.lean:91)
theorem decodeInt_mono {b₀ b₁ c₀ c₁ : AByte} (h₀ : AByteLE b₀ c₀) (h₁ : AByteLE b₁ c₁)
    {n : Nat} {ps : List AllocId} (h : decodeInt b₀ b₁ = some (n, ps)) :
    ∃ ps', decodeInt c₀ c₁ = some (n, ps') ∧ ∀ x ∈ ps, x ∈ ps'

-- lean/ToyProv/Monotone.lean:118-121
-- decodePtr_mono  (ToyProv/Monotone.lean:118)
theorem decodePtr_mono {b₀ b₁ c₀ c₁ : AByte} (h₀ : AByteLE b₀ c₀) (h₁ : AByteLE b₁ c₁) :
    (∀ n, decodePtr b₀ b₁ = some (.inr n) → decodePtr c₀ c₁ = some (.inr n)) ∧
      (∀ q, decodePtr b₀ b₁ = some (.inl q) →
        ∃ q', decodePtr c₀ c₁ = some (.inl q') ∧ PtrLE q q')
```

Concrete programs and states used above (quoted):

```lean
-- ToyProv/Monotone.lean
/-- Information order on abstract bytes: identical, except that a pointer fragment may carry a
pointer with more provenance. -/
def AByteLE : AByte → AByte → Prop
  | .uninit, .uninit => True
  | .intFrag n i, .intFrag n' i' => n = n' ∧ i = i'
  | .ptrFrag p i, .ptrFrag q i' => PtrLE p q ∧ i = i'
  | _, _ => False
-- ToyProv/Monotone.lean
/-- Information order on pointers: same address, provenance below. -/
def PtrLE (p q : Ptr) : Prop := p.addr = q.addr ∧ ProvLE p.prov q.prov
-- ToyProv/Monotone.lean
/-- Information order on provenances: `none` is below every provenance, `some id` only below
itself. -/
def ProvLE (a b : Option AllocId) : Prop := a = none ∨ a = b
```

Hypothesis ledger:

| hypothesis | why it is needed | tightness | counterexample (all other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h₀ : AByteLE b₀ c₀` | The first bytes must be related; otherwise (e.g. different addresses) a defined decoding can become UB. | tight | `decode_mono_h₀_needed` (ToyProv/Monotone.lean:147) |
| `h₁ : AByteLE b₁ c₁` | As h₀, for the second bytes. | tight | `decode_mono_h₁_needed` (ToyProv/Monotone.lean:157) |
| `h : decodeInt b₀ b₁ = some (n, ps) (decodeInt_mono)` | Monotonicity is about defined decodings: if the smaller pair's integer decoding is UB, nothing is claimed about the larger pair (here both are UB). | tight | `decodeInt_mono_h_needed` (ToyProv/Monotone.lean:169) |

- **Non-vacuity witness:** A provenance-less fragment below the same fragment with provenance; both decodings of the smaller pair defined. Lean: `decode_mono_nonvacuous`.

```lean
-- lean/ToyProv/Monotone.lean:183-187
-- decode_mono_nonvacuous  (ToyProv/Monotone.lean:183)
theorem decode_mono_nonvacuous :
    AByteLE (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 0) ∧
      AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨some 0, 16⟩ 1) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (16, []) ∧
      decodePtr (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (.inl ⟨none, 16⟩)
```

- **Prior art:**
  - [MiniRust] (full entry under **Evidence**)
- **Design question:** How a byte-level semantics must decode pointer bytes with mixed provenance so that adding provenance never introduces UB, which the model ordering and the cast-fold results depend on.
- Basis: execution (Lean kernel check) — the statements above, built by `lake build`; axioms and statement/closure hashes recorded under **Evidence**.
- Basis: derived (modeling bridge) — This is the toy instance of MiniRust's stated law "If `bytes1 <= bytes2`, then `ty.decode(bytes1) <= ty.decode(bytes2)`" (same commit), for two-byte symbolic decoders only. This is a correspondence argument, not a kernel-checked claim.

## Boundaries

### Non-claims (per result)

Each result establishes only its Lean statement about this toy semantics. In particular:

**R1a** (one past end compares equal to adjacent start):

- Evaluates the fixed program onePastProgN n1 n2 from the initial state under the toy's deterministic bump allocator; it is not quantified over arbitrary heap states, and does not say real allocators place allocations adjacently.
- Does not say pointer equality compares provenance: ptrEq compares addresses only, by definition (ISO C18 6.5.9p6 likewise requires such pointers to compare equal; semantics in which they may compare unequal or nondeterministically are not modeled).
- Address equality does not make the two pointers interchangeable (see R1b).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R1b** (address equality substitution unsound strict exposed):

- SubstAddrEq substitutes reads of q in an arbitrary instruction i under a semantic side condition (addrEqC in every reachable state after pre); it does not require pre to contain a ptrEq. The counterexample uses a store; nothing is claimed about which instruction kinds are safe.
- Does not show SubstAddrEq is unsound for every program in strict/exposed; only that the transformation as a whole is not sound.
- Escape hatch: when both pointers are in bounds of live allocations at that point (base ≤ address < base + size), the substitution is a refinement in every model (R1c, the analogue of the in-bounds GVN condition of Lee et al. 2018); the counterexample needs a one-past-the-end pointer.
- The flat positive control is one program; general flat soundness is the separate table entry substAddrEq_sound_flat (R6g).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R1c** (in bounds address equality substitution sound):

- In bounds (inBoundsC) means base ≤ address < base + size: an allocation's start address is in bounds and its one-past-the-end address is not. It does not mean interior-only (base < address). The statement says nothing about one-past pointers.
- Relies on the toy's allocator never giving two live allocations overlapping ranges (bump allocation, alloc 0 is UB); with zero-sized or overlapping allocations it is not established.
- Says nothing about pointers to freed allocations: inBoundsC requires a live allocation.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R2a** (integer equality pointer substitution unsound even when exposed):

- SubstIntEq's side conditions are semantic (addrEqC and bothExposedC in every reachable state after pre); the transformation does not syntactically require pre to contain ptr2int or intEq, and bothExposedC holds trivially for pointers without provenance.
- Does not concern substituting integers (that is sound, R2c) or folding an integer back into a pointer (R2b).
- Does not say exposure is irrelevant in general; it matters for int2ptr, not for already-formed pointers.
- Escape hatch: if both pointers are in bounds of live allocations (base ≤ address < base + size), address equality implies equal provenance and the substitution is sound (R1c).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R2b** (int2ptr fold refines exposed if no other candidate):

- Covers the case with no candidate (the fold adds provenance to a pointer that had none); this depends on provenance-monotone decoding of pointer bytes (R7b) and is exercised by int2ptrToCopy_refines_exposed_no_candidate_example (quoted under R2b), where a mixed-provenance byte copy follows the fold. Under a decoder that makes mixed-provenance bytes UB, this case fails (R7a).
- Does not claim behaviour equality (only refinement); equality under the stronger candEqProvC is R3a.
- In-boundsness of p (base ≤ address < base + size, which includes B's start) is not enough: if an exposed live allocation A ends exactly where p's allocation B starts, then B's start is also A's one-past address and has two candidates; the fold then fails when later code moves the pointer back into A (Toy.Prov.roundTrip_fold_counterexample_exposed_base_pointer). Not proved here: an address strictly inside an allocation (interior: base < a < base + size) is never the one-past address of an adjacent live allocation. No fold theorem in this package is stated for interior-only addresses; the fold theorems assume the candidate condition hc directly.
- Does not allow removing the earlier ptr2int that exposed p's allocation or computed k (DropUnusedPtr2int is unsound in exposed, R6g).
- The rewrite is the single instruction d := int2ptr k <-> d := p with k already holding p's address; it does not insert or delete the ptr2int that computed k (an inserted ptr2int would itself expose p's allocation).
- This toy restricts int2ptr candidates to exposed live allocations whose closed range [base, base + size] contains the address (PNVI-ae-udi); MiniRust's int2ptr may pick any exposed provenance (or none) regardless of the address, so address-local side conditions such as candSubProvC/candEqProvC/provIsCandC do not carry over to MiniRust when another allocation is exposed and the pointer is later moved with wrapping offsets.
- Rust 1.84.0's with_exposed_provenance documentation does not specify which exposed provenance is picked ('we cannot provide any guarantees about which provenance the resulting pointer will have'); the angelic choice used here is MiniRust's and PNVI-ae-udi's reading, not a guarantee of the Rust library documentation.
- Not stated for strict or flat here (those are table entries in R6g).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R2c** (identical value substitution sound all models):

- A sufficient condition, not a characterization: the rewrite can also preserve behaviour when the instruction does not read q or its result is unused.
- Does not say that subsequently folding int2ptr(ip) into A+2 is sound (it is not at the boundary, R3b).
- Integers carry no provenance in this toy by construction; a semantics where integers carry provenance is not covered.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R3a** (roundtrip interchangeable exposed if unique candidate):

- 'p's allocation is live and exposed' alone does NOT suffice (R3b).
- In-boundsness of p (base ≤ address < base + size, which includes B's start) is not enough: if an exposed live allocation A ends exactly where p's allocation B starts, then B's start is also A's one-past address and has two candidates; the fold then fails when later code moves the pointer back into A (Toy.Prov.roundTrip_fold_counterexample_exposed_base_pointer). Not proved here: an address strictly inside an allocation (interior: base < a < base + size) is never the one-past address of an adjacent live allocation. No fold theorem in this package is stated for interior-only addresses; the fold theorems assume the candidate condition hc directly.
- The rewrite is the single instruction d := int2ptr k <-> d := p with k already holding p's address; it does not insert or delete the ptr2int that computed k (an inserted ptr2int would itself expose p's allocation).
- Does not justify merging two int2ptr k instructions at an ambiguous address without candEqProvC.
- Does not cover strict: there the round trip loses provenance (R3c).
- Does not say the cast ptr2int that produced k may be removed: removing it changes exposure (table: DropUnusedPtr2int unsound in exposed).
- This toy restricts int2ptr candidates to exposed live allocations whose closed range [base, base + size] contains the address (PNVI-ae-udi); MiniRust's int2ptr may pick any exposed provenance (or none) regardless of the address, so address-local side conditions such as candSubProvC/candEqProvC/provIsCandC do not carry over to MiniRust when another allocation is exposed and the pointer is later moved with wrapping offsets.
- Rust 1.84.0's with_exposed_provenance documentation does not specify which exposed provenance is picked ('we cannot provide any guarantees about which provenance the resulting pointer will have'); the angelic choice used here is MiniRust's and PNVI-ae-udi's reading, not a guarantee of the Rust library documentation.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R3b** (roundtrip fold unsound exposed at one past boundary):

- Does not say the fold is never sound in exposed (R2b, R3a give conditions).
- The source's success depends on angelic resolution of the cast; under a demonic reading the source would be UB and the example would disappear.
- Escape hatch: PNVI-ae (without -udi) gives a one-past integer an empty provenance (P2318R0); with half-open candidate ranges B's start has the unique candidate B and the base-pointer example disappears, at the cost of rejecting one-past round trips. Not modeled here.
- In the flat model the same pair is a refinement, and in the strict model the source is UB (positive control).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R3c** (roundtrip not equivalent strict):

- Says nothing about the fold direction (round trip -> p). In strict the fold is proved sound (table entry int2ptrToCopy_sound_strict, R6g), which relies on provenance-monotone decoding (R7b) and fails under a decoder that makes mixed-provenance pointer bytes UB (R7a).
- The strict model's int2ptr corresponds to Rust's std::ptr::without_provenance(addr) (a pointer with no provenance), not to Rust's `as` casts: per the Rust 1.84.0 documentation, with_exposed_provenance 'is fully equivalent to addr as *const T', i.e. `as` casts follow the exposed model.
- Strict-provenance APIs that keep the original pointer (Rust's p.with_addr(a)) or constructs that name the intended provenance (VIP's copy_alloc_id) avoid int2ptr altogether; they are not modeled.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R4a** (forwarding across cast store unsound exposed flat):

- In the strict model, the soundness of ForwardAcrossCast holds only vacuously: every program matching it is UB, because the window stores through the provenance-less result of int2ptr (forwardAcrossCast_strict_src_ub); replacing the load by anything would also 'refine'. The strict pair r4Src/r4Tgt is UB on both sides.
- The positive control is the provenance-based criterion of R4c (sound in exposed when r and a have different provenance), not the strict model.
- The variant forwardAcrossCast_counterexample_guessed_address casts the constant 16, which equals A's address only because the toy's allocator is deterministic. Under PNVI-ae-udi (P2318R0, pointer_from_integer_1ie.c) and under twin allocation (Lee et al. 2018, Theorem C.1) casting a guessed address is UB even after the allocation is exposed, so that variant does not transfer; the primary counterexample uses k := (int)A instead.
- Does not show forwarding is wrong on most programs; one counterexample.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R4b** (dse across cast load unsound exposed flat):

- In the strict model, the soundness of DSEAcrossCast holds only vacuously: every program matching it is UB, because the window loads through the provenance-less result of int2ptr (dseAcrossCast_strict_src_ub). The strict pair r4dSrc/r4dTgt is UB on both sides.
- The positive control is the provenance-based criterion of R4d, not the strict model.
- Does not cover DSE across other kinds of intervening instructions.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R4c** (forwarding refines exposed if provenances differ):

- Specific to the integer-typed load x := load int a; forwarding to a pointer-typed load of a stored pointer is a different statement, not made here.
- All values have the toy's fixed two-byte width and the store and the load use the same base register a.
- Stated for the exposed model; the strict analogue is expected but not stated (not proved either way).
- In the flat model no pointer has provenance, so provNeC can never hold there; nothing about flat follows.
- Does not say how a compiler establishes hne; R4e gives one sufficient criterion (a's allocation not exposed at the cast).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R4d** (dse refines exposed if provenances differ):

- Fixed two-byte stores through the same base register a, so store a w overwrites exactly the bytes of store a v; if v is unset, store a v is UB in every execution and the deletion refines trivially.
- Exposed model only; as in R4c nothing about flat follows.
- Only this three-instruction window.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R4e** (int2ptr picks only exposed candidates):

- Pointer-typed loads of integer bytes also go through castToPtr; this card states only the int2ptr instruction.
- Does not say an exposed-model int2ptr is defined or useful: with no candidate the result has no provenance.
- This toy restricts int2ptr candidates to exposed live allocations whose closed range [base, base + size] contains the address (PNVI-ae-udi); MiniRust's int2ptr may pick any exposed provenance (or none) regardless of the address, so address-local side conditions such as candSubProvC/candEqProvC/provIsCandC do not carry over to MiniRust when another allocation is exposed and the pointer is later moved with wrapping offsets.
- Rust 1.84.0's with_exposed_provenance documentation does not specify which exposed provenance is picked ('we cannot provide any guarantees about which provenance the resulting pointer will have'); the angelic choice used here is MiniRust's and PNVI-ae-udi's reading, not a guarantee of the Rust library documentation.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R5a** (integer load of pointer bytes strips or exposes):

- Rust does not behave like the exposed model here: per MiniRust (commit cited) ptr-to-int transmutation strips provenance without exposing (an open question there); Rust's byte-level reinterpretation corresponds to the strict column.
- Memory holds symbolic two-byte fragments (intFrag n i | ptrFrag p i), not u8 bytes: any load whose two bytes are not the fragments 0 and 1 of one integer, or pointer fragments 0 and 1 with a common address, is UB - in particular partial, misaligned, and mixed integer/pointer reads. MiniRust (any initialized bytes decode at integer type), C character-type reads, and zerocopy-style byte casts define such reads; they are not modeled.
- Does not model C's effective-type or strict-aliasing rules.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R5b** (memcpy copies abstract bytes and provenance):

- memcpy here reads all source bytes before writing (memmove semantics).
- A byte-wise copy written as a loop of integer-typed loads and stores is NOT memcpy in this toy; it is a value-level round trip (R5c).
- The out-of-range example forms A + 10 with the toy's wrapping offset (Rust wrapping_offset-like, no bounds check); in ISO C and PNVI-ae-udi forming such a pointer is already UB, so that example has no C counterpart. The copied pointer is used only after moving it back into [base, base + size).
- memcpy d r 0 still checks canAccess for both pointers (provenance required) in strict/exposed, unlike Rust, where zero-sized accesses need no provenance.
- Memory holds symbolic two-byte fragments (intFrag n i | ptrFrag p i), not u8 bytes: any load whose two bytes are not the fragments 0 and 1 of one integer, or pointer fragments 0 and 1 with a common address, is UB - in particular partial, misaligned, and mixed integer/pointer reads. MiniRust (any initialized bytes decode at integer type), C character-type reads, and zerocopy-style byte casts define such reads; they are not modeled.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R5c** (integer value roundtrip does not carry provenance):

- Beyond the step-level lemma, only three concrete programs are proved; no universally quantified program equivalence about value-level round trips is stated.
- In exposed the round trip is sometimes MORE defined than the original pointer (boundary), so 'loses provenance' is not the same as 'adds UB'.
- Pointer-typed loads of integer bytes act as int2ptr in exposed (PNVI-ae-udi reading); in Rust/MiniRust they yield no provenance.
- MiniRust's explicit int2ptr may pick any exposed provenance regardless of the address, so an explicit cast round trip of an out-of-range pointer can recover its provenance there, unlike r5cOutInt here.
- The out-of-range examples rely on the toy's wrapping offset (forming A + 10 is UB in ISO C / PNVI-ae-udi).
- Memory holds symbolic two-byte fragments (intFrag n i | ptrFrag p i), not u8 bytes: any load whose two bytes are not the fragments 0 and 1 of one integer, or pointer fragments 0 and 1 with a common address, is UB - in particular partial, misaligned, and mixed integer/pointer reads. MiniRust (any initialized bytes decode at integer type), C character-type reads, and zerocopy-style byte casts define such reads; they are not modeled.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6a** (exposed refines strict):

- The literal reverse containment 'every strict behaviour is an exposed behaviour' is false when the strict behaviour is UB (R6d).
- Does not imply that optimizations sound in one model are sound in the other (R6e, R6g).
- Relies on provenance-monotone decoding of pointer bytes (R7b): mixed-provenance pointer fragments with a common address decode without UB. Under a decoder that makes such bytes UB the statement is false (R7a, eqProvDecode_exposed_not_semRefines_strict).
- Depends on int2ptr of an address with no candidate producing a pointer without provenance whose use, not creation, is UB (as with Rust's without_provenance); a semantics that makes the cast itself UB is not covered.
- Rust 1.84.0's with_exposed_provenance documentation does not specify which exposed provenance is picked ('we cannot provide any guarantees about which provenance the resulting pointer will have'); the angelic choice used here is MiniRust's and PNVI-ae-udi's reading, not a guarantee of the Rust library documentation.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6b** (flat refines exposed):

- Relies on strictly positive, disjoint allocations (alloc 0 is UB; bump allocation), on unbounded memory (no out-of-memory on alloc or ptr2int), and on a deterministic allocator.
- Does not imply optimizations transfer between flat and exposed (R6g: forwarding across a cast is unsound in both, dead-cast elimination sound in flat only).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6c** (exposed defined behaviours coincide):

- Bounds the number of distinct outcomes, not the length of the list: beh keeps one entry per UB-free resolution (exposed_beh_may_repeat has length 2).
- Depends on the toy's deterministic bump allocator (no allocation-address nondeterminism), on strictly positive disjoint allocations (alloc 0 is UB), on deterministic address-only pointer equality (semantics with nondeterministic pointer equality are not covered), and on obs printing addresses only (a language that can observe provenance without UB is not covered).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6d** (orderings are strict):

- Two programs; says nothing quantitative about how much more UB a model has.
- The 'strictly ordered' reading uses R6a and R6b, which are general theorems; this card itself only proves the two separations.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6e** (refinement transfer principles):

- Each principle uses only its own side hypothesis; they are listed together.
- The side hypotheses are whole-program behavioural conditions on pre ++ window ++ post, not local syntactic properties of the rewritten window (DropUnusedPtr2int has no int2ptr in its window, yet post can make the models differ).
- The two principles use R6a for the other program; the core lemmas take that R6a instance as an explicit hypothesis (hord) and do not depend on R6a.
- The hypotheses are weaker than list equality of behaviours (transfer_hyp_weaker_than_list_eq, quoted under R6e).
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6f** (introduce roundtrip refines exposed if candidate):

- The reverse direction (fold) needs uniqueness (R3b).
- Unsound in strict (R3c).
- The rewrite is the single instruction d := int2ptr k <-> d := p with k already holding p's address; it does not insert or delete the ptr2int that computed k (an inserted ptr2int would itself expose p's allocation).
- Rust 1.84.0's with_exposed_provenance documentation does not specify which exposed provenance is picked ('we cannot provide any guarantees about which provenance the resulting pointer will have'); the angelic choice used here is MiniRust's and PNVI-ae-udi's reading, not a guarantee of the Rust library documentation.
- This toy restricts int2ptr candidates to exposed live allocations whose closed range [base, base + size] contains the address (PNVI-ae-udi); MiniRust's int2ptr may pick any exposed provenance (or none) regardless of the address, so address-local side conditions such as candSubProvC/candEqProvC/provIsCandC do not carry over to MiniRust when another allocation is exposed and the pointer is later moved with wrapping offsets.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R6g** (optimization soundness table):

- The strict ✓ for ForwardAcrossCast and DSEAcrossCast is vacuous: every matching straight-line source is UB (forwardAcrossCast_strict_src_ub, dseAcrossCast_strict_src_ub); it says nothing about provenance-based alias analysis on defined strict programs.
- The flat ✓ for CopyToInt2ptrIfCand is vacuous: in flat no reachable pointer has a provenance, so provIsCandC holds in no reachable state, and every matching source and target is UB (copyToInt2ptrIfCand_flat_src_ub, quoted under R6g). It says nothing about introducing casts on defined flat programs; that is the separate, non-vacuous entry CopyToInt2ptr in flat (✓). The non-transfer claim for CopyToInt2ptrIfCand concerns exposed and strict only.
- The strict ✓ for Int2ptrToCopy relies on provenance-monotone decoding (R7b); it fails under a decoder that makes mixed-provenance pointer bytes UB (R7a).
- Among the nine transformations without a candidate side condition, every row sound in exposed (SubstSameVal, SubstAddrEqInBounds) is also sound in strict; non-transfer from exposed to strict needs the exposure-dependent side condition of CopyToInt2ptrIfCand.
- A ✗ is one counterexample program; it does not say the transformation is wrong on most programs.
- The transformations are this package's definitions (fixed windows and semantic side conditions), not any compiler's passes. In particular SubstIntEq does not syntactically require the program to compare (int)p == (int)q.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R7a** (identical provenance decoding breaks monotonicity):

- Concerns one alternative decoder in this toy; it does not say every semantics with UB on mixed provenance breaks every ordering, only that these statements fail for this variant on these programs.
- The variant changes only load decoding (stepE_eq_step_of_not_load, quoted under R7a); everything else is the package semantics.
- Does not say which decoding a real language uses; MiniRust uses 'no provenance' for mixed pointer bytes (cited); C's provenance model treats representation reads differently and is not modeled.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

**R7b** (pointer byte decoding is provenance monotone):

- Byte-level only: this card's two theorems are about the decoders decodeInt and decodePtr. The program-level consequences that R2b, R6a and the strict cast fold rely on are separate proved theorems whose proofs use these lemmas (through a monotone simulation of the whole step relation); this card itself states no program-level monotonicity.
- The order relates only provenance; it does not relate initialized and uninitialized bytes or integer and pointer fragments.
- Nothing about a specific compiler, C, LLVM IR, Rust, or zerocopy follows from the Lean statement alone; any such connection is a separate modeling-bridge claim.

### Attractive stronger conclusions that are false (each refuted in Lean)

These are natural readings of the positive results. Each is false in this toy, with the named counterexample theorem.

- *"Pointers that compare equal by address are interchangeable."* False in strict and exposed: `substAddrEq_counterexample_strict`, `substAddrEq_counterexample_exposed` (R1b).
- *"Once both pointers' provenances are exposed, `(int)p == (int)q` licenses replacing `q` by `p`."* False in strict and exposed: `substIntEq_counterexample_strict`, `substIntEq_counterexample_exposed` (R2a).
- *"If `p`'s allocation is live, exposed and contains `p`'s address, `int2ptr((int)p)` may be folded into `p`."* False in exposed: `roundTrip_fold_counterexample_exposed_boundary` (R3b).
- *"In-boundsness of `p` (`base ≤ address < base + size`) makes that fold safe."* False: `roundTrip_fold_counterexample_exposed_base_pointer`, where `p` is the start of B (in bounds, with `address = base`) and the exposed A ends at B's start (R3b).
- *"`int2ptr(ptr2int p)` and `p` are interchangeable in strict."* False: `roundTrip_counterexample_strict` (R3c).
- *"A pointer obtained from an integer cannot alias an unrelated pointer, so forwarding and dead-store elimination across it are safe."* False in exposed and flat: `forwardAcrossCast_counterexample`, `dseAcrossCast_counterexample` (R4a, R4b).
- *"The orderings are equivalences: every strict behaviour (UB included) is an exposed behaviour, and every exposed behaviour is a flat behaviour."* False: `model_orderings_strict` gives a program that is UB in strict and outputs `[7]` in exposed, and one that is UB in exposed and outputs `[7]` in flat (R6d).
- *"A transformation sound in strict is sound in exposed, or conversely."* False in both directions: `soundness_does_not_transfer_either_way`, `refines_does_not_transfer_either_way` (R6g).
- *"Every ✓ in the soundness table says something about defined programs."* False for three cells: `soundness_table_vacuous_cells`, `copyToInt2ptrIfCand_flat_src_ub`, `forwardAcrossCast_strict_src_ub`, `dseAcrossCast_strict_src_ub` (R6g). `not_copyToInt2ptrIfCand_flat_r3` (quoted under R6g) shows a flat-defined introduction pair that lies outside `CopyToInt2ptrIfCand .flat`.
- *"Exposed refines strict, and the cast folds hold, whatever the pointer-byte decoder."* False for the identical-pointer decoder: `eqProvDecode_exposed_not_semRefines_strict`, `eqProvDecode_fold_not_refinement`, `eqProvDecode_transfer_fails` (R7a). With this package's decoder the same programs are well behaved (`mainDecode_same_programs_ok`).

### Escape hatches

Weakening or dropping these hypotheses or modeling choices defeats the corresponding negative result (or turns a vacuous cell into an informative one):

- **R1b, R2a:** if both pointers are in bounds of live allocations at the rewrite point (base ≤ address < base + size), the substitution is sound in every model (R1c). The counterexamples need a one-past-the-end pointer.
- **R3b:** PNVI-ae without `-udi` gives a one-past integer no provenance (P2318R0); with half-open candidate ranges `[base, base + size)` B's start would have the unique candidate B and the base-pointer counterexample would disappear, at the cost of rejecting one-past round trips. Neither variant is modeled. Under a demonic reading of the cast, the boundary source would be UB and the counterexample would disappear.
- **R3c:** strict-provenance APIs that keep the original pointer (Rust's `p.with_addr(a)`) or constructs that name the intended provenance (VIP's `copy_alloc_id`) avoid `int2ptr` altogether; they are not modeled.
- **R4a, R4b:** a provenance-based criterion (`provNeC r a`, established for instance by R4e when `a`'s allocation is not exposed at the cast) makes forwarding and dead-store elimination sound in exposed (R4c, R4d).
- **R7a:** the address-only decoder with `mergeProv` (this package's `decodePtr`) restores monotonicity (R7b) and the dependent results.

### Hypotheses with `unknown` tightness

None. Every listed hypothesis is `tight` with a kernel-checked counterexample, except two that are `harmless`: `hord` in the two core lemmas of R6e (an instance of R6a, discharged by R6a in the two transfer principles), and `hr` in `memcpy_frame` (R5b), which the frame conclusion does not need (`memcpy_frame_of_hd_hs`). In `memcpy_copies_abstract_bytes` (R5b), `hr` is tight.

### Disproved or dropped statements

None of the 26 results was dropped, weakened, or found false: every statement listed under **Findings** is kernel-checked exactly as stated. The false candidate statements recorded above are part of the package as counterexample theorems, not omissions.

### Not examined

- No compiler, IR, or language implementation was executed; the only executed subject is the Lean kernel checking this project.
- Control flow, loops, function calls, concurrency, and allocation-address nondeterminism (none exists in the toy).
- Byte-level (`u8`) representations, partial or mixed reads, alignment, and C effective types.
- Twin allocation, the quasi-concrete model, CHERI capabilities, and Stacked/Tree Borrows-style aliasing models.
- The strict-model analogues of R4c and R4d (expected, not stated).

## Evidence

### Kernel-check record

- Toolchain: Lean 4 `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, as reported by `lean --version`: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`); Lake `5.0.0-src+5045d00`. No Mathlib; no Lake dependencies.
- Build: `lake build` of `lean/` (library `ToyProv`: the root module and 19 modules under `ToyProv/`) succeeds with no `sorry` warnings. Sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, or `unsafe`.
- Axioms: all 960 declarations of the library were audited with Lean's `collectAxioms`; the union of axioms used is {Classical.choice, Quot.sound, propext}, within the standard {propext, Classical.choice, Quot.sound}. Per-declaration lists are in `audit/axioms.json`.
- Statement stability: `audit/statements.json` records, for each of the 147 Lean names referenced by the fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample` of `results.json`, the SHA-256 of its statement and of its definition closure (the hashing is defined under **Revalidation**). The 5 supporting declarations listed in `corollaries_lean` are checked for existence only (table below).
- Observation date: all evidence (build, axiom audit, hashes, and source checks) was acquired on 2026-11-20.

Per-name record (axioms: P = `propext`, C = `Classical.choice`, Q = `Quot.sound`, — = none; statement and closure hashes are SHA-256; `n` = closure size):

| Lean name | used by | axioms | statement sha256 | closure sha256 (n) |
| --- | --- | --- | --- | --- |
| `EqProvDecode.decodeEq_not_monotone` | R7a | P | `bad1c65df80abeb3b5d8fb916425bb889ebca646f83dabf3ac723b69a6cf3f26` | `8fa8b6f4afdaf2f06e26cc567bed70696e017234bb56140f306e6aacd9db3028` (36) |
| `EqProvDecode.eqProvDecode_exposed_not_semRefines_strict` | R7a | P | `8efda087df9140a971e104412b3e0293f4dae9b164185b617c9f33894707b998` | `7fec883c90acce7ec69e740375b1756197e6b2616920f4b30f064d963c8cc28f` (166) |
| `EqProvDecode.eqProvDecode_fold_not_refinement` | R7a | P | `ee67bb99796fabee2eb99a4e70bfb54a643ad1ce72bb98246f7b30b6524fa281` | `5411dc07064d7c2129b7baf1e8058a5c93a0de845c3bd9f38bf8771a26a42372` (177) |
| `EqProvDecode.eqProvDecode_ptr_load_variants` | R7a | P | `344d7d26e6a370f0db0d95aa9a0d493515e93205524fbce3ca250f870f4101d1` | `fd492e5241f388e2ab488e8b34eac69be45ee1d02cf16c3544cf5015bb70bdf1` (174) |
| `EqProvDecode.eqProvDecode_transfer_fails` | R7a | P | `72a8a6c4e8a2a321d62ab26ff5d845a54884bdd59190f46fdad152e379cb617d` | `59a4d59cd9c4b61bc51190b56bb81891fd1a38f1cf97d1050c0330b57afe46a2` (166) |
| `EqProvDecode.mainDecode_same_programs_ok` | R7a | P | `c5e0e80f66c9ea623035a9ab652627eb6c23490f97a8578b05c380ad489632ea` | `0d19925eebfba23e80f8ae7a05d360c0499617d7b35edcced2ad2aaef01ffcf2` (144) |
| `byteLoadAsInt_strict_strips_exposed_exposes` | R5a | P | `6b61b8eb683736a978dce3edcf97a9e6987e4ecc7ae7b5426c8e4751da4b7768` | `4a527f4d0910594b66815d1e827ae779c8e033f05af45f93fdff78fbc5486cf6` (141) |
| `copyToInt2ptrIfCand_not_sound_strict` | R6g | P | `0ee7be4807b832b06124afc2add1d831c9d533576809780f3130472dab961ccd` | `a48ac2916c0fe289f9d33fe8b64df7cf2354c4080a2837e066afc3e2cbddc7fd` (151) |
| `copyToInt2ptrIfCand_sound_exposed` | R6g | PCQ | `14f86fc0a35a7e2f712ed49b3bcf3bb579c10ce252165c072c507062271fbdec` | `a48ac2916c0fe289f9d33fe8b64df7cf2354c4080a2837e066afc3e2cbddc7fd` (151) |
| `copyToInt2ptrIfCand_sound_flat` | R6g | PCQ | `7fb451a4b498573f4b54d4e0c644a782ec89b63438576ad154adaa951ab2def4` | `a48ac2916c0fe289f9d33fe8b64df7cf2354c4080a2837e066afc3e2cbddc7fd` (151) |
| `copyToInt2ptr_intIsAddrOf_needed` | R6f | P | `96e33bfc6e9fc12acfba8ce991fb207a0d96efa418f0da48f196346d16abc081` | `62be77142c779dadfd79e6faab8bc190a2930c048901a793b57e7933d7d46124` (147) |
| `copyToInt2ptr_not_sound_exposed` | R6g | P | `b3422d38582233c11f636b2ebfbd86db3ba86b4339ac61f0110ab6326b040b2c` | `e32342c2ce3896dfa44fc8754d97421993b216c75f9c43aa83080b24c16565ef` (148) |
| `copyToInt2ptr_not_sound_strict` | R3c, R6g | P | `503faf85daf9279986d21e87bec479e9fd1c2c9e757ff04191ca62ea525f05bb` | `e32342c2ce3896dfa44fc8754d97421993b216c75f9c43aa83080b24c16565ef` (148) |
| `copyToInt2ptr_provIsCand_needed` | R6f | P | `d74a986379728905cd378e46777f059565b2edfe17f4fa3f3ee6949617d3a97a` | `3d370a105bbe3313a98841656dee53493f99ac45a86852dca3118e03271f379e` (148) |
| `copyToInt2ptr_refines_exposed_nonvacuous` | R6f | P | `6c905621f5ec8ada82be113f53b7030461706edab71dd84131750a978f88b01f` | `ed84390eceb3200f45fcafd93282be0f1adccb171c3c2b4406ac6df619b53d7e` (151) |
| `copyToInt2ptr_refines_exposed_of_intIsAddrOf_of_provIsCand` | R6f | PCQ | `c2bd7bb7f4b025b5140ca8ffb1fa778f42f1046570fabe403681dc40b86825aa` | `b946b63fbe6fd052844d14887fb85c202aab72d57c22c7d04ca95cf52942d61d` (149) |
| `copyToInt2ptr_sound_flat` | R6g | PCQ | `3c4e883861c3c5bdef4e0d6919e00ef410d7345566c321bea826e2aa86e965bb` | `e32342c2ce3896dfa44fc8754d97421993b216c75f9c43aa83080b24c16565ef` (148) |
| `decodeInt_mono` | R7b | PCQ | `e94ca0cd57fd506907915063ec450d0ba6de77b1fffba4f6afcac392c9ffc922` | `555b2add052a0e4c67203068aef22c5955d668323c46542c75e243207eaabe4f` (26) |
| `decodeInt_mono_h_needed` | R7b | P | `a60e6d6d03cc12930eee4805eea4b5c31aeea910d93e44e3dbb8cf62b68d8c17` | `555b2add052a0e4c67203068aef22c5955d668323c46542c75e243207eaabe4f` (26) |
| `decodeInt_ptrFrags` | R5a | P | `13d8a5a3efb23af39810368ea7fd0ae3a2154b77f37f8b854319d641676b3ae8` | `f223e54590a01a2167962b1c0c4fb23b6d3b808a5c9811983b4aadfff61e2070` (19) |
| `decodePtr_intFrags` | R5c | P | `3a6dbbb1fb3f66f3c364a572b9168e973e2257dbd75c5681214a61df863b4042` | `d11d1675c1f3f726b07bf3001338daae8b804a278cd73c0ff78908aa29f2ba34` (19) |
| `decodePtr_mono` | R7b | PCQ | `cf22e746084da2f3ee4ba2b5ad74831e0e876a9cebfe2543e3fcdb346ef32bb7` | `9ebfe97167697ce831d5183672ad8770e76b0364ebe7d8151c2c7bf05b106a3d` (26) |
| `decode_mono_h₀_needed` | R7b | P | `26c9eb55685928d008a7d4e8fe9a756f4a9ae37435e4b811878791707bdc35ab` | `352f0657a3d16735ed1bbffd3be58690cde702276ea0132f76114c050cbb8c42` (30) |
| `decode_mono_h₁_needed` | R7b | P | `a3a5447ef91be0f2b781e65277fb4da8c44fbb2cb319d7015097079f574866e3` | `352f0657a3d16735ed1bbffd3be58690cde702276ea0132f76114c050cbb8c42` (30) |
| `decode_mono_nonvacuous` | R7b | P | `853130542303fce67acfaa472218cb0346f86440311ace0020c91618903da2d1` | `352f0657a3d16735ed1bbffd3be58690cde702276ea0132f76114c050cbb8c42` (30) |
| `dropUnusedPtr2int_not_sound_exposed` | R6g | P | `c5814d5c765742c716b0f84a3233d45cf3f9f2252827ee1b5513ba37f178c6a2` | `ac25d647c747a8b80029acf2505583aad4aea6739e800533a72318ba0bb030f8` (149) |
| `dropUnusedPtr2int_sound_flat` | R6g | PQ | `28160b631d3f2783e027e805b6737e59cbde2f822581f1f5656b966bce68ab1e` | `ac25d647c747a8b80029acf2505583aad4aea6739e800533a72318ba0bb030f8` (149) |
| `dropUnusedPtr2int_sound_strict` | R6g | PQ | `a6fb638a4877335d9e6fc6d8af44d5fa7768a6b4129f0a22bd5eade33c41e777` | `ac25d647c747a8b80029acf2505583aad4aea6739e800533a72318ba0bb030f8` (149) |
| `dseAcrossCast_counterexample` | R4b | P | `44aec627f1f3e699f738f9a5bc42e474194e3295d503c40076eddd6ac59a615a` | `eee7d3ff35f1193b770bd9568d54eb207529d39e6528d3abd16dc5b046fc3f96` (143) |
| `dseAcrossCast_example_refines_strict` | R4b | P | `2097d89d1eba3a9e7dda01b916f8a49cf2ff076ecd11372a1a38fe6d44a4b745` | `eee7d3ff35f1193b770bd9568d54eb207529d39e6528d3abd16dc5b046fc3f96` (143) |
| `dseAcrossCast_not_sound_exposed` | R4b, R6g | P | `d51a0d35827fe6be8721c787e3f6f7f5a1fd19577a8ac5a0d10288761f767c06` | `555f276fc0991829c42a8c1abf3bab25def46254ca0b0e2af9bef75d04199666` (141) |
| `dseAcrossCast_not_sound_flat` | R4b, R6g | P | `74a9011f023a46763540ba0ad873a6836e67929d05c385069e37b47d16787638` | `555f276fc0991829c42a8c1abf3bab25def46254ca0b0e2af9bef75d04199666` (141) |
| `dseAcrossCast_sound_strict` | R6g | PQ | `75597d8f34c3d7a4cd1a9767891c7596d4d99797053f706ca3be26a52edead6b` | `555f276fc0991829c42a8c1abf3bab25def46254ca0b0e2af9bef75d04199666` (141) |
| `dseAcrossCast_strict_src_ub` | R4b | PQ | `d9c736f12eb5bdc8f7be588e36f7f82456e5731cd6d6342cf41dda8a913bb33b` | `79e1b63b3bb56dcb111595bf9150a953c37c8206d9b2ff78b58c2dde0ab663f9` (139) |
| `dseAcrossCast_strict_src_ub_h_needed` | R4b | PQ | `9e41d9e7a61cd575601a0dcb4c1af6445ce3ed3d6aab4ba99c39f7e8225b0302` | `3fd3e38d4427061ca6462602f9c580303ec7abbcaf1ac3002005413c01021d82` (140) |
| `dse_ne_needed` | R4d | P | `eab827b8bb1908a0fa7c9f1d0b026d7f129cf498e69427713e2a7a589070229b` | `42cdd4a472dcfdada4fdac3adc1ea09a1f674a77330b668e6288b723eb52cc5e` (146) |
| `dse_nonvacuous` | R4b, R4d | P | `b725330149e4f82a42d36beb0343db4fcdbf3ee172f82621c556c89ceb879578` | `50bb6e5082015064f659513d5d8fa07294d5a1356f202afbf25e84523512992f` (145) |
| `dse_provNe_needed` | R4d | P | `db081c30d1b3d5640f51a68bd96b6ed10d4791c3dca4783a8c130cca9a479c07` | `ab234b7462432e8138b66ea8dddd778f14502e2465d362fd2066df7f3d952286` (140) |
| `dse_refines_exposed_of_provNe_of_ne` | R4d | PCQ | `649ea599879b9af4879ba45c7a35f8d161c8629480f1e6bba8cf7f83348bacc5` | `bf89ce5ed75b342ba768bdac8d9852dc68f7e6c6a395ed7d0b8d1066dd098c0a` (145) |
| `ex_beh_angelic_pos` | R6c | P | `912b24c2e719d7382292f7cca31af48e209a41cbdc2a6a0398223e46557baa2f` | `dbcd8aefd975e3aaa88c225887c89728144cecb72995dc46d9739012b9ee3067` (139) |
| `ex_runs_two_resolutions` | R6c | P | `f763d29534db0a250d16b9385b6271556c23042f8d3fe6aa892be86fbaf5516b` | `53803a5a98776d2ecbb068c3aee459ba8b73db19ff7fb9a5794f5dcd38dae5d9` (129) |
| `exposed_beh_elements_equal` | R6c | PCQ | `276cddb9c8db3d16da04f82952f8aca92701f9b4db623795bb43b541efea1d44` | `74cf96a7d77c816160db48c1b5098c24d1e96d69e5944eadf8da7fa159620b77` (138) |
| `exposed_beh_may_repeat` | R6c | P | `e10c3195d0f8d39e04bb0511c67acfb72a5efbed46813699eb649cb985881105` | `138dc3b2fa5698e80ae9e4a00a4312137cf705dee1580a03085da4845c79a5ac` (139) |
| `exposed_semRefines_strict` | R6a | PCQ | `012259cbb7d217d6ca454270acc1061fd0129ee084f0898299361212b8b600c9` | `e7d0c28db6cdd6b5d949057e1b58b46952143115979a7eab9bf7e8408ecf2790` (139) |
| `flat_semRefines_exposed` | R6b | PCQ | `fdb5161aa7f3ca2849394f3d34801f1bc8c11a6a88a7efa104d08ee9e2604276` | `e7d0c28db6cdd6b5d949057e1b58b46952143115979a7eab9bf7e8408ecf2790` (139) |
| `forwardAcrossCast_counterexample` | R4a | P | `1d1a04abed0da1cf0e6cc88ef6f0b39a5d5cedd129f5e1c5c73c65d30e8c595a` | `5c4123d49ae4298d52a987cfef7e304b660c0620711fce86ca1928beb3a2ca29` (149) |
| `forwardAcrossCast_counterexample_guessed_address` | R4a | P | `dcdcb9b3bdd6b4e9ddedefc006a1507ca7799583a53b4bf90fd61294a437f1cc` | `8d5f583b1a9d24cdc6952a5ceaa0c1b261da96b63fc942efc106e0466668efda` (147) |
| `forwardAcrossCast_example_refines_strict` | R4a | P | `cbe02bd58b8d88f9c5ff5929656d0587f3236751038e65b0e76a5acb3165da57` | `5c4123d49ae4298d52a987cfef7e304b660c0620711fce86ca1928beb3a2ca29` (149) |
| `forwardAcrossCast_not_sound_exposed` | R4a, R6g | P | `2f17d5143fee91668c156b61987e87fc0b4fa45fbd36df9685a437a68c786ab4` | `8668af280c672e0e358540242ef8f609509a9d59054710ff688ae3a956a47286` (147) |
| `forwardAcrossCast_not_sound_flat` | R4a, R6g | P | `9f9380b5dac0952e3980cc9d7483b6d743d07508da5a5efc41e7703d35a71a1c` | `8668af280c672e0e358540242ef8f609509a9d59054710ff688ae3a956a47286` (147) |
| `forwardAcrossCast_sound_strict` | R6g | PQ | `980ddbbc4e30b4acf530c615bc0a334a3c9d98cdfbe8ac99c840949b2bda0537` | `8668af280c672e0e358540242ef8f609509a9d59054710ff688ae3a956a47286` (147) |
| `forwardAcrossCast_strict_src_ub` | R4a | PQ | `cca677a99fe11f7ef64230cb968b938a15813b058d0a4cb9ea9fc7200ed7f9ec` | `4bfe00e50801a7d12bf7d2bbe739716c01f5210c093855bc9300579a93398bd2` (145) |
| `forwardAcrossCast_strict_src_ub_h_needed` | R4a | PQ | `d361dd5b223d97bada27239b16af3fb168588e100627074ecd6a0f0fec5b5b07` | `4ef4d8fbe381b7fbf2e35d7f2db402f613e8255d794c78a6f5798d1b01c1dd8f` (146) |
| `forwardLoad_isInt_needed` | R4c | P | `cff7058625b488196c99397ca8f28926d82b73cf1b29e2d14496798dbfbfc2ec` | `2a78877ff1bb84a63643f03f6e5864984bc824bb5be4fab913d1929ae053199d` (146) |
| `forwardLoad_nonvacuous` | R4a, R4c | P | `2741c43bd029575055f651b13eb8316abb67687cb4174b8cdd632eb2acd0f5a4` | `c4408113aa5fd85238ea12266ee33517bdfac019cf220eb3b869edbe152a5e2b` (148) |
| `forwardLoad_provNe_needed` | R4c | P | `e4e14d3a1502a4f5460c0fb9ead17f059d7340895788f3b0ef74a368154a7cce` | `19ebb118980324086c8042886616d7b6837a919de5939d8dada311d954b45a21` (146) |
| `forwardLoad_refines_exposed_of_provNe_of_isInt` | R4c | PCQ | `648f33e5acc48304fe9eac4192a8192c20ce3a9fec27725efab0e156dc3a9733` | `364066e24305546c9fcdbd695cb4989b5fa3c8e05dd9ac347bb92a48d06f51d3` (148) |
| `int2ptrToCopy_beh_eq_exposed_of_intIsAddrOf_of_candEqProv` | R3a | PQ | `e087a58adb9ff2781c135dddd16dfa7b0aa8b4b115bf60a63d7025962d64a2d1` | `1cb7a6e1add524dfd3bc49336b7c40431ba40cd9fa9fe89a2797408f9434db97` (147) |
| `int2ptrToCopy_beh_eq_intIsAddrOf_needed` | R3a | P | `6aca6f13add427c5bfb47a697f68f91a73b46ae8cab3b7e4fedc66a7c0021cf3` | `ca5e5857ab0094c89aebcd8e31f4b5ddbb6e06114494dd3d32963448cdc7d2db` (146) |
| `int2ptrToCopy_beh_eq_nonvacuous` | R3a | P | `a0693d79af82f002dd68ae8e9cfd4934d07f6d5ef0f3c4762a9b1952b7b2edb0` | `c3cc0129eafad5d31578ec80bc6db47a07fb875afaf1d0966109ed50160f7161` (149) |
| `int2ptrToCopy_candSubProv_needed` | R2b | P | `f08c7801fbf3f9d56bfa91f063d49ef62c75e505c05a66058bec9126c6b44bee` | `12f021cc258ee534fb53d7210e8826900cdeecb98b49b204ade2dd68b9545891` (151) |
| `int2ptrToCopy_intIsAddrOf_needed` | R2b | P | `aab5e467473eaf4f8212a7518888ee8d0270361b76635c006d23984f28de3457` | `9cd472c244b1ae873116e16952603de3b4492f6bdf11a790deffbdef95d9702d` (147) |
| `int2ptrToCopy_not_sound_exposed` | R3b, R6g | P | `ccc9d7c91455b409b9dcf071058635957758b797970f00a9333ab764e7646185` | `9da6fb023545466bfd9cd67214723dbc9ce58f85ba8f0588349c644308c93020` (148) |
| `int2ptrToCopy_refines_exposed_no_candidate_example` | R2b | P | `a5121b205357d8a5da644a4bf0dffebf397edfb6b2c818fb1d771f87c01cef6f` | `2715e1938dc8d4472712081ba5f9ae0ec4ff3b2aa8d5675386aba94b2e43f231` (150) |
| `int2ptrToCopy_refines_exposed_nonvacuous` | R2b | P | `1eff07ced78556de5a4450eec4c6c69f51195044d9c50f0529096c39228f9ee0` | `a4f0469dcb5ccf14a0786178622a3a16812dceafc1d47ee57cf0a754822ddc3a` (149) |
| `int2ptrToCopy_refines_exposed_of_intIsAddrOf_of_candSubProv` | R2b | PCQ | `7008826b7c593fe4244dbf60934b3c788ebe828efa4675bb0dde49cfd86c1afc` | `2deed226509cf347eba9da6c0e0825fd5793b16d19b7caf48f8753a06b2ae250` (148) |
| `int2ptrToCopy_sound_flat` | R6g | PCQ | `e7e54c0dbc40fa09aa17f3dbbb8a0f6e681c9a42813202e525cdfee101930f98` | `9da6fb023545466bfd9cd67214723dbc9ce58f85ba8f0588349c644308c93020` (148) |
| `int2ptrToCopy_sound_strict` | R6g | PCQ | `8764d869ba894b7c2ccc6aed669458504c6fa546cc8f32167817e8b808f1ff0d` | `9da6fb023545466bfd9cd67214723dbc9ce58f85ba8f0588349c644308c93020` (148) |
| `int2ptr_exposed_result` | R4e | PQ | `19d3c82a4212e34f309ed2932282b1966be2856839dce113ea063d22ce52acac` | `5ad51fbfe314780368d8eea1305ddb59b28bf7c8b8a16ec1bddc5a14cfe51ed1` (118) |
| `int2ptr_exposed_result_hk_needed` | R4e | PQ | `7eeb55e0187438b27d8864cb7405a03dae58b4b4eb8e2f9b0d0856eaafb919e4` | `246b95b07dd4063c2428e8194dcbd5b8ee4719771766eb1c99ccc85af6487f58` (119) |
| `int2ptr_result_nonvacuous` | R4e | P | `eb8d6ae5da68c812641029931269171a25c72667c59ad7df93069ed43a6a1076` | `b19b52f0022f16d74de604aea9366c42e1323cce0f2d8ca5d9140f2bc9a9d8e3` (128) |
| `int2ptr_result_provNe_hA_needed` | R4e | PQ | `ac0012816e8691320f92d42b43f83c942d62bd719677a9dd10a9be0377a7f2c1` | `183ff6cdd3b311aea6db8524614a171e6889ae8791b05153a4620905437a37dd` (132) |
| `int2ptr_result_provNe_ha_needed` | R4e | PQ | `b8cb240177614a3b0ef5fb2ae3be15af174f90599e7f8b90f2580ea3fd8856a2` | `183ff6cdd3b311aea6db8524614a171e6889ae8791b05153a4620905437a37dd` (132) |
| `int2ptr_result_provNe_hda_needed` | R4e | PQ | `930ecf500205669431c9172754e18b8dccbdfd8dd6540a643f1242c5cad72a2c` | `183ff6cdd3b311aea6db8524614a171e6889ae8791b05153a4620905437a37dd` (132) |
| `int2ptr_result_provNe_hk_needed` | R4e | PQ | `cb92355b3373cf55b2264d804b7f07e2f5eb92a15009c0d788cfe02f74e24902` | `183ff6cdd3b311aea6db8524614a171e6889ae8791b05153a4620905437a37dd` (132) |
| `int2ptr_result_provNe_hnot_needed` | R4e | PQ | `ec5ea7ead3d452375725548819073096e4619c88f918629499cef773aa779385` | `fa0f31c9e21c44064d01274a515a8ad48266a38b0295ab8bae3e90b5dad80257` (132) |
| `int2ptr_result_provNe_nonvacuous` | R4e | PQ | `a842b2919e97a010bcebcd7b02e2450e6cc9462d5a99c98c710c1421d6fe630f` | `183ff6cdd3b311aea6db8524614a171e6889ae8791b05153a4620905437a37dd` (132) |
| `int2ptr_result_provNe_of_not_exposed` | R4e | PQ | `1988542c8dfdbf049908017320f81988956e17135a6fb4fc598b303950ff2b27` | `63076e5d3a03262eab6a3688a9c0bd2c839d0d5c8f18baa839d884690a104f4f` (122) |
| `int2ptr_strict_result` | R4e | P | `fd5fdd77abcf6e4b6f2912f2abf2b2e61482ef647163530e6192e96b1af36e5d` | `5ad51fbfe314780368d8eea1305ddb59b28bf7c8b8a16ec1bddc5a14cfe51ed1` (118) |
| `int2ptr_strict_result_hk_needed` | R4e | P | `c0ca1d731a5dd3db98c87f2c44d4fa45a8f8845df7ee239443f3971da671bcd0` | `246b95b07dd4063c2428e8194dcbd5b8ee4719771766eb1c99ccc85af6487f58` (119) |
| `intRoundTrip_boundary_example` | R5c | P | `6091183a1b0db6932366b099e098ff4ec03ad310e90c0353241bb9e89e84e242` | `9955db7d7094a8e11629c232576dce7e03ae3030ed0aa91aae2d3c6195f64182` (140) |
| `intRoundTrip_in_range_example` | R5c | P | `ff2fb880b59b49d0d01bbbb628c1b29f3f3b16191fde34221adb69187b4eb504` | `f26e9adff564508874861f122355c5f9b0bf0ff8329e11bebca073747c884a43` (139) |
| `intRoundTrip_out_of_range_example` | R5b, R5c | P | `3fdad7fc14ca8d3459415d0bdeffc0698a07916f3419b46fd29c56a1dc7820b0` | `41c7d1dd0d3e1145594ef86c3f034a11fa5fce028c81bc12b2556f9e0ebe537c` (140) |
| `load_int_of_ptrFrags` | R5a | P | `aab675c77a0d2307a957ca0bbcbb98c56ad207fcdd0267febc741fd72a7da396` | `5ad51fbfe314780368d8eea1305ddb59b28bf7c8b8a16ec1bddc5a14cfe51ed1` (118) |
| `load_int_of_ptrFrags_h0_needed` | R5a | P | `c351b2935c395349e5c1107d60c42ceac9f2f45188e10474507bf06b5e318333` | `bcc2eb0a558eed1f689af04ab41e4a0d27421ebe1a6817cb1a654726379249e6` (128) |
| `load_int_of_ptrFrags_h1_needed` | R5a | P | `99088f6a163918c55f568e2150990c7f63246b492ad94119750aa5d322779a86` | `6c6af3b139c43acb731d70070c483ae9fd80405bcff2355d6be6685f5292a11c` (128) |
| `load_int_of_ptrFrags_hacc_needed` | R5a | P | `8f455ad404490c3a76cefa810ce87c96476631c4c96280068869c15766a73fac` | `14645129640efc2ac53a7355fab6ec010c581928c64c6b44bf02de12dac1836a` (129) |
| `load_int_of_ptrFrags_hr_needed` | R5a | P | `1afdd1ff3b42cc03d8a080a11111474961f3a79b19dbb0a53686ee468fbebd75` | `cb3b06ecf0a6c9ee6c5a7a10412fdbfea8f76d0d712f1595fe7d696e7db914d3` (128) |
| `load_int_of_ptrFrags_nonvacuous` | R5a | P | `437d127a6517c6d32967828b483c4405a51e2554060b884006bd1c5adfa6011d` | `cb3b06ecf0a6c9ee6c5a7a10412fdbfea8f76d0d712f1595fe7d696e7db914d3` (128) |
| `load_ptr_of_intFrags` | R5c | P | `be7cc2d6af1bdaff637817a3282fd2b786fa2d7d0f73a2158a7b7dfeb7bee38d` | `5ad51fbfe314780368d8eea1305ddb59b28bf7c8b8a16ec1bddc5a14cfe51ed1` (118) |
| `load_ptr_of_intFrags_h0_needed` | R5c | P | `e4fbddc3d08e34adb897573dcde4355124d2223e8651e72b9ef327a773535ea7` | `fbf7dd61fcbd40ec860faedb06c14fb3d08c4b733103b28d3ae0e489c2dbc06e` (128) |
| `load_ptr_of_intFrags_h1_needed` | R5c | P | `27db527ab14ae31f181c845694ac6ee6eea49eae16a7fe53511f6c4f5e38d0d3` | `fbf7dd61fcbd40ec860faedb06c14fb3d08c4b733103b28d3ae0e489c2dbc06e` (128) |
| `load_ptr_of_intFrags_hacc_needed` | R5c | P | `baf39bd251dd30cc2f4a3c160723a626a38e0dc77cf3dbc5fc6256d67ca7ca1e` | `fbf7dd61fcbd40ec860faedb06c14fb3d08c4b733103b28d3ae0e489c2dbc06e` (128) |
| `load_ptr_of_intFrags_hr_needed` | R5c | P | `9ba699667df0bf717a32aaafb9ec8fcfbcae46e0a8bd6b2c91a5fea6e03c8d89` | `fbf7dd61fcbd40ec860faedb06c14fb3d08c4b733103b28d3ae0e489c2dbc06e` (128) |
| `load_ptr_of_intFrags_nonvacuous` | R5c | P | `54dc3eadd29826143e223379857a441db89c0e292bb1e224ee2161fedfd74e22` | `fbf7dd61fcbd40ec860faedb06c14fb3d08c4b733103b28d3ae0e489c2dbc06e` (128) |
| `memcpy_copies_abstract_bytes` | R5b | PQ | `bc5342257409277e8565282639a0d4dc119c7a07dad60ab976f8c345d90a7702` | `5ad51fbfe314780368d8eea1305ddb59b28bf7c8b8a16ec1bddc5a14cfe51ed1` (118) |
| `memcpy_copies_abstract_bytes_nonvacuous` | R5b | P | `920973d3ad69839e03bfe3602bee480a6f11993f38c8369516dac5d5de2920f5` | `4244d0591544f819edadd93a208c44a7406bbf8a9260a1af049b927a9fa5f1ba` (129) |
| `memcpy_copies_hd_needed` | R5b | P | `f5e718c4849502e7d1bfcf1ff021449cb33b714f8901cf0b5141321265a38c06` | `4244d0591544f819edadd93a208c44a7406bbf8a9260a1af049b927a9fa5f1ba` (129) |
| `memcpy_copies_hr_needed` | R5b | P | `904d452ce67d689fdf5b91276a7ffead0c9e75359e6a6820b96683d796115ca0` | `4244d0591544f819edadd93a208c44a7406bbf8a9260a1af049b927a9fa5f1ba` (129) |
| `memcpy_copies_hs_needed` | R5b | P | `442c948c60079423f04a2cc4d5e613bf50cf43dce2c2feebf4c312b327a04a7c` | `cb3b06ecf0a6c9ee6c5a7a10412fdbfea8f76d0d712f1595fe7d696e7db914d3` (128) |
| `memcpy_frame` | R5b | PQ | `0a429a6e3b446b7ed28833ee3a01f7bf3fc3801999fad9cac9e460d7e22e626f` | `5ad51fbfe314780368d8eea1305ddb59b28bf7c8b8a16ec1bddc5a14cfe51ed1` (118) |
| `memcpy_frame_hd_needed` | R5b | P | `83a8fe248763a5dedfa52273cc359d3c70052cd6df1084314807833060eed0b0` | `4244d0591544f819edadd93a208c44a7406bbf8a9260a1af049b927a9fa5f1ba` (129) |
| `memcpy_frame_hs_needed` | R5b | P | `e433d45ef6b73dab09b2765a66763feeea6ab13ffe5179bb86cd98dcfea69f81` | `eab67188047ec6c14ed1422a7e1c9b8265a472562111501b257783ae51b61da0` (129) |
| `memcpy_preserves_provenance_example` | R5b | P | `7c44dd7a90a392625d38767ce75f5afee40fe68cb3dbe6a6d6b6aeac4ca80ed9` | `88c5e6da23dfde9929a400d2f9c8901de09e0cf33fbb633f7c5b850f5483109e` (139) |
| `model_orderings_strict` | R6a, R6b, R6d | P | `2daef5bd74c95a8127dd2e775c4b4ddb8d2fa1f0a4413c6877abb972a8926ae8` | `d8447322a373e1d8b54355346cd2ccbbd630b0e20351d83ddbef7514c0ab32fb` (141) |
| `onePast_ptrEq_adjacent_start` | R1a | PQ | `d77cd223b81962b151f1dc169886ca0d8212fb252edadb288667307ea83557a4` | `0e1aa58d9cd1ad6b7698c9f73b535b023adcc949def53d7e5a506b87c2897436` (139) |
| `onePast_ptrEq_adjacent_start_all_models` | R1a | P | `9520827640c91fde834b46ed8b6d17962164e2bd39e93f01eddea9276172542d` | `59931b44dc298f4b28c61562bac2c18326d46e56bf45983a0c9dc8315e653c74` (139) |
| `onePast_size₁_needed` | R1a | P | `3261cf914481248085858a3177f7c5288b94c2a2c0bb66e911bbf9a70a3c4281` | `0e1aa58d9cd1ad6b7698c9f73b535b023adcc949def53d7e5a506b87c2897436` (139) |
| `onePast_size₂_needed` | R1a | P | `899c5898c30fce7b1aabf0905fdf2ef9697df798cdf9a77f422363a3ff9ae21f` | `0e1aa58d9cd1ad6b7698c9f73b535b023adcc949def53d7e5a506b87c2897436` (139) |
| `refines_does_not_transfer_either_way` | R6g | P | `f1b929fc0c43e689884c4c98926828af300982d5179de168b4e632fdd9f05f4e` | `738ae046408a17df2ff452dc5a0eabbd706ccc1e5b36e8d29f31787539d8f8a9` (157) |
| `refines_exposed_of_refines_strict_core` | R6e | P | `e528ed6c903062ef6f292ccdebc33dc02d2e1d8ae786699ae7db3c3b86c4b1fe` | `10ffa51db1aeada6fd5d6bdac4c253695fcd4b52734089db75ef0cfab6c47cfb` (140) |
| `refines_exposed_of_refines_strict_of_src_semRefines` | R6e | PCQ | `17c80c2c9f670a4c5acc0e05a32c9724eae7a304255b5cd5aed18971fc0a4579` | `10ffa51db1aeada6fd5d6bdac4c253695fcd4b52734089db75ef0cfab6c47cfb` (140) |
| `refines_strict_of_refines_exposed_core` | R6e | P | `0e90ad3ab6f5ec99b5efd17e367b23cf996004b5377f2e52d9e9b4cb4df59968` | `10ffa51db1aeada6fd5d6bdac4c253695fcd4b52734089db75ef0cfab6c47cfb` (140) |
| `refines_strict_of_refines_exposed_of_tgt_semRefines` | R6e | PCQ | `1787dc2c2d95ca6c79aa5542f8db2bfc9bb827de1790fcba25960b5ad3f2743a` | `10ffa51db1aeada6fd5d6bdac4c253695fcd4b52734089db75ef0cfab6c47cfb` (140) |
| `roundTrip_counterexample_strict` | R3c | P | `672e726e6405c19bb866ef7018c3a270ba156d9771b1bfaf153ade41d0e85a75` | `afab532e4fed2cda074489b3719e330a23089813e46bd712319d49e25a7844d7` (149) |
| `roundTrip_example_exposed` | R3c | P | `e2073943c3ed43e2f2338b0573dc102e7c95f530823c5f2f4f8b25bdf7cbc78e` | `c6b9779d24055003033777efb46f64c5f06b9c11de48bd7d6c2c06920687b5b9` (140) |
| `roundTrip_fold_boundary_flat_strict` | R3b | P | `66e4c61f4f2a8e29ee2b7e9138a4cc42f44778fb2ded71aaeb00b97b8f94a904` | `2a9bd19bc7a10fc874706f6e508556b05ba62a97cea6c3560a70abae7703e02d` (149) |
| `roundTrip_fold_counterexample_exposed_base_pointer` | R3b | P | `73aa2195ab47cd221330a5ca01bff179203864a1a5eb89b57e71adfd1b76f486` | `5ed10c7eded0975e9687912f5fae9d1d7f4755d29cf7a47e9df6a11f3db8d1aa` (155) |
| `roundTrip_fold_counterexample_exposed_boundary` | R3a, R3b | P | `eeb5c6a72300bbb981ea0f8763ee1f6f9f88052a7c062c47e7417487a94cfaf8` | `f1ffc0b3d6451ef61185e96b4445bf98959e93904e9e6e76981d903b813df43c` (152) |
| `soundness_does_not_transfer_either_way` | R6g | PCQ | `fc9ae067d1948a50bda70a3faa92a802ceb87bc3096b35d4c322a0c9f90cefff` | `9c29977e7e63864a7bc20071428079d8e9149c9e9242d67e4b4ae15a8acc04d9` (155) |
| `soundness_table_nonvacuous` | R6g | P | `61109572e23fef1fab1e5fbc4ef26cf5e90e8ceef830a33b0cb1e385f81783e5` | `2414fc277977b7f913cd08162f0b44a08d249e4783d4ad830777253018a8f46c` (200) |
| `soundness_table_vacuous_cells` | R6g | PCQ | `438117eb6b7e5407dd5eb5beb0b2c12cbceda3be749b1135ed8fd800793f8ebf` | `4bb3e8c4044f137ec7d164466f7f5b3a22709357956f35d08d4a76b9f315a58a` (153) |
| `substAddrEqInBounds_addrEq_needed` | R1c | P | `9cd82ceac5f5d381e4d5208cd35f9694902d1f44fbd773b05d4751415b17e042` | `e526b133da534ec32847439c4798a4bcbbd6714997ababcc2f8053a88479b653` (151) |
| `substAddrEqInBounds_nonvacuous` | R1c | P | `65b08c76eade5b9668f43f5aa00f04fd2e24475d3c2e7c7dd9eb81e0d4f57198` | `e083cdf4206203cbc799f58f1593bc181dc1b149f11b50c928a7c9739f290840` (151) |
| `substAddrEqInBounds_p_needed` | R1c | P | `bc3c6dcabe493ce6fb4b1f50f9b60fd9db2fdf296a795bd44c8477d0e8b84c01` | `674ecfc250cb11867627d960654cc16fe8bd64c52caddafac51f10e37cb0a465` (154) |
| `substAddrEqInBounds_q_needed` | R1c | P | `417d422e004cac80c8ed9bc0eb530ea335af92957b50da51e82b2ea44d826236` | `0eade678fba54973f0a0202f8576c787482beca7034c2855878fb0f050b2a372` (152) |
| `substAddrEqInBounds_sound` | R1c | PCQ | `906d2da1812462d88b7d20249aed69802692ecdfeae1e6d76f3870693be57ce8` | `02344f326d645badf6c5e5125a29c0197edeee8ee5e7589966494cb4d8a87998` (152) |
| `substAddrEqInBounds_sound_all` | R6g | PCQ | `906d2da1812462d88b7d20249aed69802692ecdfeae1e6d76f3870693be57ce8` | `02344f326d645badf6c5e5125a29c0197edeee8ee5e7589966494cb4d8a87998` (152) |
| `substAddrEq_counterexample_exposed` | R1b | P | `9e44e70af416db0f97d6f6c074b90dba099758c51ea20acf45936d8c87b792f2` | `292187ab5b9ca2eac86214a02b9cf1a9d43286af73a05e559d5e7bcc3f4e1978` (153) |
| `substAddrEq_counterexample_strict` | R1b, R2c | P | `26aaf63a98d1d30266f766785170093d51d5345df77b89679b064995648b65aa` | `292187ab5b9ca2eac86214a02b9cf1a9d43286af73a05e559d5e7bcc3f4e1978` (153) |
| `substAddrEq_example_refines_flat` | R1b | P | `b183bf0447aa8a1ff135f8a7b2e30f0d72ff0e4e0b050728cab15c874fb983be` | `292187ab5b9ca2eac86214a02b9cf1a9d43286af73a05e559d5e7bcc3f4e1978` (153) |
| `substAddrEq_not_sound_exposed` | R1b, R6g | P | `82ba78f132a0947ff4b34e2d32018529004877c3d7293de3bf1c0ec1a1846d71` | `04d36a3128a0c0e23606997400493d3b401ceaa8778f5245e29774b1bdac70b4` (150) |
| `substAddrEq_not_sound_strict` | R1b, R6g | P | `7e0d63f23b1f514808510f7f2efb407aa5aa47cae9c491cccf8b20b20d144c35` | `04d36a3128a0c0e23606997400493d3b401ceaa8778f5245e29774b1bdac70b4` (150) |
| `substAddrEq_sound_flat` | R6g | PCQ | `698c9ba0932f5008bc224b1bd3f28b27457444de4e6bfbc32b4f224fe3361b63` | `04d36a3128a0c0e23606997400493d3b401ceaa8778f5245e29774b1bdac70b4` (150) |
| `substIntEq_counterexample_exposed` | R2a | P | `79d7875e1784727c6c7ed97c5e4fbe062ed565c60c22596e99bc879b98b80d79` | `f2658a23780081e700cec81aa80cf5755092b07c8ec322fc5c7bd109d0cb8eba` (154) |
| `substIntEq_counterexample_strict` | R2a | P | `1453883328d3398379bcaf957435a3e71bfb8c6f2e0398f6e2fcda8c521a1a54` | `f2658a23780081e700cec81aa80cf5755092b07c8ec322fc5c7bd109d0cb8eba` (154) |
| `substIntEq_example_refines_flat` | R2a | P | `c5faa51d7f8e1ada1ea3d246d87d99d39bd32f9e80c4f022459fb869f8ae800f` | `f2658a23780081e700cec81aa80cf5755092b07c8ec322fc5c7bd109d0cb8eba` (154) |
| `substIntEq_not_sound_exposed` | R2a, R6g | P | `81e71fb8d1830396cc5e8ab7bb38ed4386e8ed4d4952a16626bda67a4cb58af0` | `802b2bc80d6efc474e5f5a9e7d65871a63b801ef4abdf8ff41e9054e43076fb8` (151) |
| `substIntEq_not_sound_strict` | R2a, R6g | P | `2c2bbbb9b3f2dfdba54818138966d1d5bfab3e637dce50ab6235f9ff0da40777` | `802b2bc80d6efc474e5f5a9e7d65871a63b801ef4abdf8ff41e9054e43076fb8` (151) |
| `substIntEq_sound_flat` | R6g | PCQ | `36efdd3bbdcaf67f3bf29803d49791c395a7ac96a2dabfbf7f3eb84b03be81a3` | `802b2bc80d6efc474e5f5a9e7d65871a63b801ef4abdf8ff41e9054e43076fb8` (151) |
| `substSameVal_beh_eq` | R2c | PQ | `9b7ea9fdeca85289abaef7e81e9dff3227e7d195916f93957148a67d62301869` | `068b0b5f9c439bacc5b14605c0d2ac1294f1a43c65206b1c9eace5b9febff22c` (163) |
| `substSameVal_int_boundary_example` | R2c | P | `57fd5e17b8f7debc44b11e8520665d32f029aa5412dac64e3302d46eca490da4` | `5736e0e809ea3c21b7e6d6ec19f5ee955f67f74e3867226f24fa6c5998031d5f` (166) |
| `substSameVal_sound` | R2c, R6g | PQ | `c2acb6063bd059c4dd934f479ea72c238731771d81071895d029d41a37011801` | `7995c03e05cf0701207760474ac9100056a1bc10fa25bb901cb51594c71bffe0` (166) |
| `transfer_nonvacuous` | R6e | P | `d6645f5f43dc336c53b02c76b6e5a6ea172a31c7c108c86723629e7de1bf2107` | `3820f24f012b959a92773a9c7fde3d4413739eb1c37e0b21689d4773a69e39d8` (142) |
| `transfer_refines_needed` | R6e | P | `32e1bd6c11dd8d567eb57bacf7e7715a9773092eaa6355c04d46e293761f338e` | `10ffa51db1aeada6fd5d6bdac4c253695fcd4b52734089db75ef0cfab6c47cfb` (140) |
| `transfer_to_exposed_src_agreement_needed` | R6e | P | `d697ff217ff91f3b550c9c2e0abd99c3032469bb88e9da551fa21630a3749a25` | `dc164563388983a4ad710563dab6d3aa1338640fc810f97cb7e503fcc0943062` (142) |
| `transfer_to_strict_tgt_agreement_needed` | R6e | P | `8c2ca2c32e5cd11cfe00ff15a88cfdf1fc3f048b24b980f1ef07630695ba31b5` | `1c43aa687dbd1192807a9c198e7c9d9672e86494b8a96f6c3460f4a98a4cce12` (142) |

Supporting declarations cited in card prose and listed in `corollaries_lean` (quoted under the named card). `support/revalidate.py` checks that they exist; their axioms are recorded in `audit/axioms.json`; no statement or closure hash is recorded for them, because they are not results, non-vacuity witnesses, positive controls, or tightness counterexamples:

| Lean name | cited by | axioms |
| --- | --- | --- |
| `memcpy_frame_of_hd_hs` | R5b | PQ |
| `transfer_hyp_weaker_than_list_eq` | R6e | P |
| `copyToInt2ptrIfCand_flat_src_ub` | R6g | PCQ |
| `not_copyToInt2ptrIfCand_flat_r3` | R6g | PCQ |
| `EqProvDecode.stepE_eq_step_of_not_load` | R7a | P |

### Sources

Each entry was checked at the cited location on 2026-11-20 (DOIs resolved through the DOI handle system; quoted passages compared with the cited documents).

- **[TS 6010 / P2318R0]** ISO/IEC TS 6010:2025, Programming languages - C - A provenance-aware memory object model for C, edition 1.0, publication date 2025-05-15 (IEC webstore entry https://webstore.iec.ch/en/publication/107524). The normative text is not publicly available; statements about PNVI-ae-udi here are checked against the public draft J. Gustedt, P. Sewell, K. Memarian, V. B. F. Gomes, M. Uecker, A Provenance-aware Memory Object Model for C, Draft Technical Specification, WG21 P2318R0 / WG14 N2577 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2021/p2318r0.pdf).
- **[Memarian et al. 2019]** K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell. Exploring C Semantics and Pointer Provenance. Proc. ACM Program. Lang. 3, POPL, Article 67 (2019). doi:10.1145/3290380. Also WG14 N2311. Source checked: Cerberus project page (https://www.cl.cam.ac.uk/~pes20/cerberus/), which lists authors, venue, article number and this DOI. Defines the PNVI-plain and PVI models and discusses one-past-the-end equality and pointer substitution; the exposure-based variants PNVI-ae and PNVI-ae-udi are from the later TS draft (see P2318R0).
- **[Jung 2022]** R. Jung. Pointers Are Complicated III, or: Pointer-integer casts exposed. Blog post, 11 April 2022, https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html. 'casting a pointer to an integer has a side-effect, and that side-effect has to be preserved even if we don't care about the result of the cast'; discusses pointer-to-integer transmutation via memcpy or unions.
- **[Jung 2020]** R. Jung. Pointers Are Complicated II, or: We need better language specs. Blog post, 14 December 2020, https://www.ralfj.de/blog/2020/12/14/provenance.html. Presents the three-step chain: integer substitution after iq == ip, removal of the int-ptr round trip on the one-past-the-end pointer, and provenance-based alias analysis; argues the round-trip removal is the incorrect step.
- **[Jung 2018]** R. Jung. Pointers Are Complicated, or: What's in a Byte? Blog post, 24 July 2018, https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html. Abstract bytes that carry pointer fragments with provenance.
- **[Lee et al. 2018]** J. Lee, C.-K. Hur, R. Jung, Z. Liu, J. Regehr, N. P. Lopes. Reconciling High-Level Optimizations and Low-Level Code in LLVM. Proc. ACM Program. Lang. 2, OOPSLA, Article 125 (November 2018). doi:10.1145/3276495. Source checked: author-hosted PDF https://people.mpi-sws.org/~jung/twinsem/twinsem.pdf. Twin-allocation model for LLVM IR; Appendix C ('Coq formalization and proof', artifact https://github.com/snu-sf/llvmtwin-coq) proves in Coq, among others, Theorem C.1 ('Twin allocation forbids pointer guessing'), Theorem C.4 (ptrtoint/inttoptr can be moved across malloc and free) and Theorem C.5 ('Soundness of GVN for pointers', for the conditions of Section 5, which include 'p and q are logical pointers, and both are either dereferenceable or point to the same block').
- **[Lepigre et al. 2022]** R. Lepigre, M. Sammler, K. Memarian, R. Krebbers, D. Dreyer, P. Sewell. VIP: Verifying Real-World C Idioms with Integer-Pointer Casts. Proc. ACM Program. Lang. 6, POPL, Article 20 (January 2022). doi:10.1145/3498681. Source checked: author PDF https://iris-project.org/pdfs/2022-popl-vip.pdf. Introduces a construct that lets programmers state the intended provenance of an integer-pointer cast (copy_alloc_id); 'we prove VIP compatible with PNVI-ae-udi'; the RefinedC-VIP tool 'produces foundational proofs in Coq'.
- **[MiniRust]** MiniRust specification, repository minirust/minirust at commit 063d784186d3252bee242217f218223205c0b568: spec/mem/intptrcast.md (int2ptr predicts a provenance that 'must be either `None` or already exposed', with no address-range check, chosen 'maximally in the programmer's favor'); spec/lang/representation.md (integer decoding 'entirely ignores provenance', i.e. ptr-to-int transmutation strips provenance without exposing, marked with an open TODO; pointer bytes 'not all having the same provenance' decode to 'a pointer without provenance'; encode and decode are required to be monotone: 'If `bytes1 <= bytes2`, then `ty.decode(bytes1) <= ty.decode(bytes2)`').
- **[Rust 1.84.0 documentation]** Rust standard library documentation, version 1.84.0: std::ptr::with_exposed_provenance (https://doc.rust-lang.org/1.84.0/std/ptr/fn.with_exposed_provenance.html) - 'This is fully equivalent to addr as *const T.'; 'The exact provenance that gets picked is not specified. The compiler will do its best to pick the "right" provenance for you (whatever that may be), but currently we cannot provide any guarantees about which provenance the resulting pointer will have - and therefore there is no definite specification for which memory the resulting pointer may access.'; 'If there is no previously "exposed" provenance that justifies the way the returned pointer will be used, the program has undefined behavior.' std::ptr::without_provenance (https://doc.rust-lang.org/1.84.0/std/ptr/fn.without_provenance.html) - 'Creates a pointer with the given address and no provenance.'; such pointers 'may be used for zero-sized memory accesses (if suitably aligned), but non-zero-sized memory accesses with a no-provenance pointer are UB.' pointer::addr ('the provenance of the pointer is discarded and not exposed').
- **[Leroy and Blazy 2008]** X. Leroy, S. Blazy. Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations. Journal of Automated Reasoning 41, 1-31 (2008). doi:10.1007/s10817-008-9099-0. Source checked: publisher page (abstract). Coq-verified block-based memory model used to prove semantic preservation for passes of the CompCert compiler; no integer-to-pointer provenance recovery.
- **[Besson et al. 2019]** F. Besson, S. Blazy, P. Wilke. CompCertS: A Memory-Aware Verified C Compiler Using a Pointer as Integer Semantics. Journal of Automated Reasoning 63, 369-392 (2019). doi:10.1007/s10817-018-9496-y. Source checked: publisher page (abstract). A verified compiler whose memory model lets 'the binary representation of pointers ... be manipulated much like integers'.
- **[Kang et al. 2015]** J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis. A Formal C Memory Model Supporting Integer-Pointer Casts. PLDI 2015. doi:10.1145/2737924.2738005. Source checked: author-hosted PDF https://sf.snu.ac.kr/publications/intptrcast.pdf. Quasi-concrete model, 'fully formalized in Coq'; 'In the quasi-concrete model, casting a pointer to an integer has a side effect on memory, and we cannot eliminate cast operations. In the fully concrete model, however, a cast from pointer to integer is a no-op'; Section 6.6 verifies in Coq a compiler from the quasi-concrete to the concrete model that eliminates dead casts. (Lee et al. 2018 note that this model does not support one-past-the-end round trips.)
- **[Beck et al. 2024]** C. Beck, I. Yoon, H. Chen, Y. Zakowski, S. Zdancewic. A Two-Phase Infinite/Finite Low-Level Memory Model. ICFP 2024 (Proc. ACM Program. Lang. 8); related DOI 10.1145/3674652 as listed on arXiv:2404.16143 (source checked: arXiv abstract page). Infinite and finite memory models of LLVM IR with pointer-integer casts, instantiated in the VIR semantics; justifies optimizations such as dead-alloca elimination.

Source facts and this package's synthesis are kept apart: the entries above say what each source states; the Findings say how the toy relates to it, always as a `derived (modeling bridge)` argument.

## Revalidation

Requirements: [`elan`](https://github.com/leanprover/elan) (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is installed; there are no Lake dependencies.

### One command

From the package directory:

```sh
python3 support/revalidate.py .
```

The script never modifies the package: it copies `lean/` to a temporary directory and then

1. runs `lake build` there;
2. rejects any Lean source containing `sorry`, `admit`, `native_decide`, or an `axiom` declaration;
3. elaborates a generated audit file that imports `ToyProv` and, for every declaration of the library, computes its axioms with Lean's `collectAxioms`, failing if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs;
4. checks that every Lean name referenced by `results.json` exists (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean`, `corollaries_lean`, and every hypothesis `counterexample`), and for every such name that is recorded in `audit/statements.json` (all of them except the `corollaries_lean` entries), recomputes two SHA-256 hashes and compares them with `audit/statements.json`: the **statement hash** is the hash of `toString (repr ci.type)` (the kernel `Expr` of the declaration's type); the **closure hash** is the hash of the newline-joined, sorted list of entries `name : repr(type) [:= repr(value)]` for every package-local constant reachable from the type (through types, definition values, and inductive constructors; theorem bodies are not included). The closure size is compared too.

Expected final lines:

```text
ok   lake build
ok   axioms (960 declarations)
ok   statement hashes (147 hashed names; 5 referenced names exist but carry no recorded hash)
REVALIDATED
```

A changed hash means that a statement or a definition it depends on changed; every result citing that name must then be re-read against the new statement.

### Manual equivalent

Build, then print the axioms of every recorded name:

```sh
cd lean
lake build
python3 - <<'EOF' > /tmp/ToyProvAxioms.lean
import json
names = sorted(json.load(open('../audit/statements.json'))['statements'])
print('import ToyProv')
for n in names:
    print(f'#print axioms {n}')
EOF
lake env lean /tmp/ToyProvAxioms.lean
```

Every output line must be `'<name>' depends on axioms: [...]` with a subset of `propext`, `Classical.choice`, `Quot.sound` (or `does not depend on any axioms`).

### Cheap discriminating checks

The counterexamples are closed evaluations, so a single file reproduces the key behaviours directly (run from `lean/` after `lake build`):

```sh
cat > /tmp/ToyProvProbe.lean <<'EOF'
import ToyProv
open Toy.Prov
#eval (beh .strict r1Src, beh .strict r1Tgt)        -- R1b
#eval (beh .exposed (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT),
       beh .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT))   -- R3b
#eval (beh .exposed r4Src, beh .exposed r4Tgt)      -- R4a
#eval (beh .exposed r6StrictUB, beh .strict r6StrictUB)     -- R6d
EOF
lake env lean /tmp/ToyProvProbe.lean
```

Expected output, one line per `#eval` (R1b, R3b, R4a, R6d):

```text
([Toy.Prov.Outcome.done [1, 7]], [Toy.Prov.Outcome.ub])
([Toy.Prov.Outcome.done [7]], [Toy.Prov.Outcome.ub])
([Toy.Prov.Outcome.done [9]], [Toy.Prov.Outcome.done [5]])
([Toy.Prov.Outcome.done [7]], [Toy.Prov.Outcome.ub])
```

These probes check only the listed programs. The general theorems (R1c, R2b, R3a, R4c–R4e, R5a–R5c, R6a–R6c, R6e, R6f, the ✓ entries of R6g, R7b) are revalidated only by the kernel check above. If the semantics in `ToyProv/Basic.lean` or `ToyProv/Transform.lean` changes, the closure hashes of essentially every result change, and all cards must be re-read.
