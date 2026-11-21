/-!
# Toy machine: registers, frame-affecting operations, CFG layout, reachability

A deliberately small model of a function body whose basic blocks are laid out
linearly in memory in an order that need not follow control flow.

* Words are `Int`; memory is a total map `Int → Int`; the stack grows downward
  and every operation occupies exactly one address unit.
* Only frame-affecting operations are modeled.  Branch conditions are not
  modeled: every CFG successor of a block is a possible continuation.
* Empty blocks are dead ends: `Reach` never enters a block without operations.
  A real CFG projected to frame-affecting operations must therefore contract
  (or pad) blocks that become empty, or paths through them are lost.
* The canonical frame address (CFA) of the function is the value of `sp` on
  entry (the toy omits the return-address slot, so the caller's `sp` equals the
  CFA).
-/

namespace Toy.CFI

/-- Toy register names: the stack pointer `sp`, the frame pointer `fp`, one more
callee-saved register `s1`, and one scratch (caller-saved) register `t1`. -/
inductive Reg
  | sp
  | fp
  | s1
  | t1
  deriving DecidableEq, Repr

/-- All registers, in a fixed order. -/
def Reg.all : List Reg := [.sp, .fp, .s1, .t1]

theorem Reg.mem_all (r : Reg) : r ∈ Reg.all := by
  cases r <;> simp [Reg.all]

/-- A register file: one value per register.  A structure (rather than a function)
so that register files of decidable values have decidable equality. -/
structure RegFile (α : Type) where
  sp : α
  fp : α
  s1 : α
  t1 : α
  deriving DecidableEq, Repr

namespace RegFile

variable {α : Type}

/-- Read a register. -/
def get (f : RegFile α) : Reg → α
  | .sp => f.sp
  | .fp => f.fp
  | .s1 => f.s1
  | .t1 => f.t1

/-- Overwrite one register. -/
def set (f : RegFile α) : Reg → α → RegFile α
  | .sp, v => { f with sp := v }
  | .fp, v => { f with fp := v }
  | .s1, v => { f with s1 := v }
  | .t1, v => { f with t1 := v }

/-- The register file holding `a` in every register. -/
def const (a : α) : RegFile α := ⟨a, a, a, a⟩

@[simp] theorem get_set_self (f : RegFile α) (r : Reg) (v : α) : (f.set r v).get r = v := by
  cases r <;> rfl

@[simp] theorem get_set_ne (f : RegFile α) {r r' : Reg} (v : α) (h : r' ≠ r) :
    (f.set r v).get r' = f.get r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

theorem get_set (f : RegFile α) (r r' : Reg) (v : α) :
    (f.set r v).get r' = if r' = r then v else f.get r' := by
  by_cases h : r' = r
  · subst h; simp
  · simp [h]

@[simp] theorem get_const (a : α) (r : Reg) : (const a).get r = a := by
  cases r <;> rfl

end RegFile

/-- Frame-affecting operations of the toy instruction set.

* `push r`: `sp := sp - 1`, then store (the old value of) `r` at `[sp]`.
* `pop r`: load `[sp]`, `sp := sp + 1`, then write the loaded value to `r`.
* `subSp n` / `addSp n`: adjust `sp` by `n`.
* `movReg dst src`: `dst := src` (any registers, including `sp`).
* `saveAt r off`: store `r` at `[sp + off]`.
* `restore r off`: load `r` from `[sp + off]`.
* `call`: a call site.  The callee is assumed frame-neutral and its effects are
  not modeled; the operation leaves the state unchanged (including the
  caller-saved scratch register `t1` and all memory).
* `ret`: return; leaves the state unchanged (a block ending in `ret` normally
  has no successors). -/
inductive Op
  | push (r : Reg)
  | pop (r : Reg)
  | subSp (n : Nat)
  | addSp (n : Nat)
  | movReg (dst src : Reg)
  | saveAt (r : Reg) (off : Int)
  | restore (r : Reg) (off : Int)
  | call
  | ret
  deriving DecidableEq, Repr

/-- Machine state: registers and memory. -/
structure MState where
  regs : RegFile Int
  mem : Int → Int

/-- Point update of memory. -/
def write (m : Int → Int) (a v : Int) : Int → Int :=
  fun x => if x = a then v else m x

/-- One-step semantics of a frame-affecting operation. -/
def step (st : MState) : Op → MState
  | .push r =>
    let sp' := st.regs.get .sp - 1
    { regs := st.regs.set .sp sp', mem := write st.mem sp' (st.regs.get r) }
  | .pop r =>
    { regs := (st.regs.set .sp (st.regs.get .sp + 1)).set r (st.mem (st.regs.get .sp)),
      mem := st.mem }
  | .subSp n => { st with regs := st.regs.set .sp (st.regs.get .sp - (n : Int)) }
  | .addSp n => { st with regs := st.regs.set .sp (st.regs.get .sp + (n : Int)) }
  | .movReg d s => { st with regs := st.regs.set d (st.regs.get s) }
  | .saveAt r off => { st with mem := write st.mem (st.regs.get .sp + off) (st.regs.get r) }
  | .restore r off => { st with regs := st.regs.set r (st.mem (st.regs.get .sp + off)) }
  | .call => st
  | .ret => st

/-- A basic block: a list of operations and the indices of its CFG successors. -/
structure Block where
  ops : List Op
  succs : List Nat
  deriving DecidableEq, Repr

/-- A function: blocks indexed by position (block `0` is the entry block) and a
linear layout, i.e. the order in which blocks are placed in memory.  The layout
need not follow control flow. -/
structure Func where
  blocks : List Block
  layout : List Nat
  deriving DecidableEq, Repr

namespace Func

/-- Operations of block `b` (empty for an out-of-range index). -/
def blockOps (f : Func) (b : Nat) : List Op := (f.blocks[b]?.map Block.ops).getD []

/-- Successors of block `b` (empty for an out-of-range index). -/
def succs (f : Func) (b : Nat) : List Nat := (f.blocks[b]?.map Block.succs).getD []

/-- The operation at offset `k` of block `b`. -/
def opAt (f : Func) (b k : Nat) : Option Op := (f.blockOps b)[k]?

/-- Linear start address of block `b` in a layout suffix, given the address `acc`
of that suffix's first block; the first occurrence of `b` counts. -/
def startIn (f : Func) : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, acc, b => if x = b then some acc else startIn f xs (acc + (f.blockOps x).length) b

/-- Linear start address of block `b`. -/
def blockStart (f : Func) (b : Nat) : Option Nat := f.startIn f.layout 0 b

/-- Linear address (PC) of offset `k` in block `b`. -/
def pcOf (f : Func) (b k : Nat) : Option Nat := (f.blockStart b).map (· + k)

end Func

/-- The caller-side ground truth an unwinder must recover: the CFA (the caller's
stack pointer at the call) and the caller's register values. -/
structure Caller where
  cfa : Int
  regs : RegFile Int

/-- State on function entry: `sp` holds the CFA, every other register holds the
caller's value, memory is arbitrary. -/
def entryState (c : Caller) (m : Int → Int) : MState :=
  { regs := c.regs.set .sp c.cfa, mem := m }

/-- `Reach f c m b k st`: state `st` is reachable at offset `k` of block `b`
(before executing the operation there), starting from `entryState c m` at the
start of block `0` and following CFG paths.  Only valid PCs are reachable:
`k` is always below the block length, and paths do not enter empty blocks. -/
inductive Reach (f : Func) (c : Caller) (m : Int → Int) : Nat → Nat → MState → Prop
  | entry : 0 < (f.blockOps 0).length → Reach f c m 0 0 (entryState c m)
  | next {b k : Nat} {st : MState} {op : Op} :
      Reach f c m b k st → f.opAt b k = some op → k + 1 < (f.blockOps b).length →
      Reach f c m b (k + 1) (step st op)
  | edge {b k b' : Nat} {st : MState} {op : Op} :
      Reach f c m b k st → f.opAt b k = some op → k + 1 = (f.blockOps b).length →
      b' ∈ f.succs b → 0 < (f.blockOps b').length →
      Reach f c m b' 0 (step st op)

theorem Reach.lt_length {f : Func} {c : Caller} {m : Int → Int} {b k : Nat} {st : MState}
    (h : Reach f c m b k st) : k < (f.blockOps b).length := by
  induction h with
  | entry h => exact h
  | next _ _ hk _ => exact hk
  | edge _ _ _ _ hpos => exact hpos

/-- Reachability ignores the layout: it depends only on the blocks (operations
and successors). -/
theorem Reach.layout_irrelevant (bs : List Block) (l₁ l₂ : List Nat)
    {c : Caller} {m : Int → Int} {b k : Nat} {st : MState} :
    Reach ⟨bs, l₁⟩ c m b k st ↔ Reach ⟨bs, l₂⟩ c m b k st := by
  constructor <;> intro h <;> induction h with
  | entry h0 => exact Reach.entry h0
  | next _ hop hk ih => exact Reach.next ih hop hk
  | edge _ hop hk hs hp ih => exact Reach.edge ih hop hk hs hp

end Toy.CFI
