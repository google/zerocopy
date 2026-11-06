-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

namespace BenchCommon

inductive Val where
  | word64 (n : Nat)
  | boolVal (b : Bool)
  deriving DecidableEq

inductive Operand where
  | slot (idx : Nat) (consume : Bool := false)
  | imm (v : Val)

inductive BinOp where
  | add
  | sub
  | bitXor
  | lt
  | eq

inductive Instr where
  | mov (dst : Nat) (src : Operand)
  | alu (op : BinOp) (dst : Nat) (lhs rhs : Operand)
  | dealloc (idx : Nat)

inductive Term where
  | ret
  | jmp (target : Nat)
  | jcc (cond : Operand) (falseTarget trueTarget : Nat)

structure Block where
  instrs : List Instr
  term : Term

structure Body where
  blocks : List Block

inductive StepOut (S : Type) where
  | step (next : S)
  | halted (ret : Val)
  | fault

def evalBinOp (op : BinOp) (v1 v2 : Val) : Option Val :=
  match op, v1, v2 with
  | .add, .word64 a, .word64 b => some (.word64 (a + b))
  | .sub, .word64 a, .word64 b => some (.word64 (a - b))
  | .bitXor, .word64 a, .word64 b => some (.word64 (Nat.xor a b))
  | .lt, .word64 a, .word64 b => some (.boolVal (decide (a < b)))
  | .eq, .word64 a, .word64 b => some (.boolVal (decide (a = b)))
  | _, _, _ => none

/-- Generic state parameterized by memory representation `M`. -/
structure MState (M : Type) where
  mem : M
  bb : Nat
  ip : Nat

structure MapOps (M : Type) where
  empty : M
  get : M → Nat → Option Val
  set : M → Nat → Option Val → M
  seq : {α : Type} → M → (M → α) → α

def natSeq {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

def mkStep {M : Type} (ops : MapOps M) (m : M) (bb ip : Nat) :
    StepOut (MState M) :=
  ops.seq m (fun m' =>
    natSeq ip (fun ip' =>
      .step { mem := m', bb := bb, ip := ip' }))

def MapOps.initArgs {M : Type} (ops : MapOps M) (args : List Val) : M :=
  let rec loop : Nat → List Val → M → M
    | _, [], acc => acc
    | idx, a :: rest, acc =>
      ops.seq (ops.set acc idx (some a)) (fun acc' =>
        loop (idx + 1) rest acc')
  loop 1 args ops.empty

def MapOps.initState {M : Type} (ops : MapOps M) (args : List Val) :
    MState M where
  mem := ops.initArgs args
  bb := 0
  ip := 0

def evalOperand {M : Type} (ops : MapOps M) (mem : M) (op : Operand) :
    Option (Val × M) :=
  match op with
  | .slot idx false =>
    match ops.get mem idx with
    | some v => some (v, mem)
    | none => none
  | .slot idx true =>
    match ops.get mem idx with
    | some v =>
      ops.seq (ops.set mem idx none) (fun mem' => some (v, mem'))
    | none => none
  | .imm v => some (v, mem)

def evalInstr {M : Type} (ops : MapOps M) (s : MState M) (instr : Instr) :
    StepOut (MState M) :=
  match instr with
  | .mov dst src =>
    match evalOperand ops s.mem src with
    | some (v, m') =>
      mkStep ops (ops.set m' dst (some v)) s.bb (s.ip + 1)
    | none => .fault
  | .alu op dst lhs rhs =>
    match evalOperand ops s.mem lhs with
    | some (v1, m1) =>
      match evalOperand ops m1 rhs with
      | some (v2, m2) =>
        match evalBinOp op v1 v2 with
        | some out =>
          mkStep ops (ops.set m2 dst (some out)) s.bb (s.ip + 1)
        | none => .fault
      | none => .fault
    | none => .fault
  | .dealloc idx =>
    mkStep ops (ops.set s.mem idx none) s.bb (s.ip + 1)

def evalTerm {M : Type} (ops : MapOps M) (s : MState M) (term : Term) :
    StepOut (MState M) :=
  match term with
  | .ret =>
    match ops.get s.mem 0 with
    | some v => .halted v
    | none => .fault
  | .jmp target =>
    mkStep ops s.mem target 0
  | .jcc cond falseTarget trueTarget =>
    match evalOperand ops s.mem cond with
    | some (.boolVal false, m') =>
      mkStep ops m' falseTarget 0
    | some (.boolVal true, m') =>
      mkStep ops m' trueTarget 0
    | _ => .fault

def evalStep {M : Type} (ops : MapOps M) (body : Body) (s : MState M) :
    StepOut (MState M) :=
  match body.blocks[s.bb]? with
  | none => .fault
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalInstr ops s instr
    | none => evalTerm ops s blk.term

def evalSteps {M : Type} (ops : MapOps M) (body : Body) :
    Nat → MState M → StepOut (MState M)
  | 0, s => .step s
  | k + 1, s =>
    match evalStep ops body s with
    | .step s' => evalSteps ops body k s'
    | .halted v => .halted v
    | .fault => .fault

/-- Structural basic-block evaluator: traverses `blk.instrs` once (`instr ::
rest`) in $O(K)$ steps instead of re-indexing `blk.instrs[s.ip]?` from `0` at
every instruction ($O(K^2)$ steps). -/
def evalInstrList {M : Type} (ops : MapOps M) :
    List Instr → MState M → StepOut (MState M)
  | [], s => .step s
  | instr :: rest, s =>
    match evalInstr ops s instr with
    | .step s' => evalInstrList ops rest s'
    | .halted v => .halted v
    | .fault => .fault

def evalBlock {M : Type} (ops : MapOps M) (body : Body) (s : MState M) :
    StepOut (MState M) :=
  match body.blocks[s.bb]? with
  | none => .fault
  | some blk =>
    match evalInstrList ops blk.instrs s with
    | .step s' => evalTerm ops s' blk.term
    | .halted v => .halted v
    | .fault => .fault

/-- Generator for sequential basic blocks of length `K` over 16 stack slots. -/
def genSeqInstrs (K : Nat) : List Instr :=
  let rec loop : Nat → Nat → List Instr
    | 0, _ => [.mov 0 (.slot 3 false)]
    | r + 1, step =>
      let dst := 3 + (step % 13)
      let src := if step < 13 then (if step % 2 == 0 then 1 else 2)
                 else 3 + ((step * 7 + 1) % 13)
      .mov dst (.slot src false) :: loop r (step + 1)
  loop (K - 1) 0

def genSeqBody (K : Nat) : Body where
  blocks := [{ instrs := genSeqInstrs K, term := .ret }]

def genDiamondBlocks : Nat → Nat → List Block
  | 0, d =>
    [{ instrs := [.mov 0 (.slot 6 true)], term := .ret }]
  | r + 1, d =>
    let bTrue := 3 * d + 1
    let bFalse := 3 * d + 2
    let bNext := 3 * (d + 1)
    { instrs := [.alu .lt 3 (.slot 1 false) (.slot 2 false)],
      term := .jcc (.slot 3 true) bFalse bTrue } ::
    { instrs := [.mov 4 (.slot 1 false), .mov 6 (.slot 4 true), .dealloc 4],
      term := .jmp bNext } ::
    { instrs := [.mov 5 (.slot 1 false), .mov 6 (.slot 5 true), .dealloc 5],
      term := .jmp bNext } ::
    genDiamondBlocks r (d + 1)

def genDiamondBody (D : Nat) : Body where
  blocks := genDiamondBlocks D 0

/-- Small-step inductive reachability for measuring per-step vs multi-step
proof terms. -/
inductive SafeFrom {M : Type} (ops : MapOps M) (body : Body)
    (P : Val → Prop) : MState M → Prop where
  | halt {s : MState M} {v : Val} :
      evalStep ops body s = .halted v →
      P v →
      SafeFrom ops body P s
  | step {s s' : MState M} :
      evalStep ops body s = .step s' →
      SafeFrom ops body P s' →
      SafeFrom ops body P s

theorem safeFrom_of_steps_halt {M : Type} (ops : MapOps M) (body : Body)
    (k : Nat) {s : MState M} {v : Val} {P : Val → Prop}
    (hsteps : evalSteps ops body k s = .halted v)
    (hP : P v) :
    SafeFrom ops body P s := by
  induction k generalizing s with
  | zero => contradiction
  | succ k' ih =>
    dsimp [evalSteps] at hsteps
    cases h1 : evalStep ops body s with
    | step s' =>
      rw [h1] at hsteps
      exact SafeFrom.step h1 (ih hsteps)
    | halted v' =>
      rw [h1] at hsteps
      injection hsteps with hv
      subst hv
      exact SafeFrom.halt h1 hP
    | fault =>
      rw [h1] at hsteps
      contradiction

theorem safeFrom_of_steps_step {M : Type} (ops : MapOps M) (body : Body)
    (k : Nat) {s s' : MState M} {P : Val → Prop}
    (hsteps : evalSteps ops body k s = .step s')
    (hnext : SafeFrom ops body P s') :
    SafeFrom ops body P s := by
  induction k generalizing s with
  | zero =>
    injection hsteps with hs
    subst hs
    exact hnext
  | succ k' ih =>
    dsimp [evalSteps] at hsteps
    cases h1 : evalStep ops body s with
    | step s_mid =>
      rw [h1] at hsteps
      exact SafeFrom.step h1 (ih hsteps)
    | halted _ =>
      rw [h1] at hsteps; contradiction
    | fault =>
      rw [h1] at hsteps; contradiction

/-!
## The 5 State Map Representations
-/

def listSeq {α β : Type} (xs : List α) (k : List α → β) : β :=
  match xs with
  | [] => k []
  | x :: rest => k (x :: rest)

-- 1. Rep 1: `FnMap` (`Nat → Option Val`)
abbrev FnMap := Nat → Option Val

def fnMapOps : MapOps FnMap where
  empty := fun _ => none
  get m i := m i
  set m idx val := fun i => if i == idx then val else m i
  seq m k := k m

-- 2a. Rep 2a: `DenseList` (Fixed-size 16 `List (Option Val)`)
abbrev DenseList := List (Option Val)

def DenseList.init : Nat → DenseList
  | 0 => []
  | n + 1 => none :: DenseList.init n

def DenseList.get : DenseList → Nat → Option Val
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, i + 1 => DenseList.get xs i

def DenseList.set : DenseList → Nat → Option Val → DenseList
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v =>
    match DenseList.set xs i v with
    | [] => [x]
    | y :: ys => x :: y :: ys

def denseListOps : MapOps DenseList where
  empty := DenseList.init 16
  get := DenseList.get
  set := DenseList.set
  seq := listSeq

-- 2b. Rep 2b: `CanonList` (Auto-padding & auto-trimming `List (Option Val)`)
abbrev CanonList := List (Option Val)

def CanonList.cons (x : Option Val) (xs : CanonList) : CanonList :=
  match xs with
  | [] =>
    match x with
    | none => []
    | some v => [some v]
  | y :: ys => x :: y :: ys

def CanonList.get : CanonList → Nat → Option Val
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, i + 1 => CanonList.get xs i

def CanonList.set : CanonList → Nat → Option Val → CanonList
  | [], 0, v => CanonList.cons v []
  | [], i + 1, v => CanonList.cons none (CanonList.set [] i v)
  | _ :: xs, 0, v => CanonList.cons v xs
  | x :: xs, i + 1, v => CanonList.cons x (CanonList.set xs i v)

def canonListOps : MapOps CanonList where
  empty := []
  get := CanonList.get
  set := CanonList.set
  seq := listSeq

-- 3. Rep 3: `DenseArray` (`Array (Option Val)`)
abbrev DenseArray := Array (Option Val)

def denseArrayOps : MapOps DenseArray where
  empty := (DenseList.init 16).toArray
  get m idx :=
    match m[idx]? with
    | some v => v
    | none => none
  set m idx val := ⟨DenseList.set m.toList idx val⟩
  seq m k := listSeq m.toList (fun l => k ⟨l⟩)

-- 4. Rep 4: `SortedAList` (`List (Nat × Val)`)
abbrev SortedAList := List (Nat × Val)

def SortedAList.cons (p : Nat × Val) (xs : SortedAList) : SortedAList :=
  match xs with
  | [] => [p]
  | y :: ys => p :: y :: ys

def SortedAList.get : SortedAList → Nat → Option Val
  | [], _ => none
  | (k, v) :: rest, idx =>
    if idx == k then some v
    else if idx < k then none
    else SortedAList.get rest idx

def SortedAList.insert : SortedAList → Nat → Val → SortedAList
  | [], idx, val => [(idx, val)]
  | (k, v) :: rest, idx, val =>
    if idx == k then (idx, val) :: rest
    else if idx < k then (idx, val) :: (k, v) :: rest
    else SortedAList.cons (k, v) (SortedAList.insert rest idx val)

def SortedAList.erase : SortedAList → Nat → SortedAList
  | [], _ => []
  | (k, v) :: rest, idx =>
    if idx == k then rest
    else if idx < k then (k, v) :: rest
    else SortedAList.cons (k, v) (SortedAList.erase rest idx)

def SortedAList.set (m : SortedAList) (idx : Nat) : Option Val → SortedAList
  | some val => SortedAList.insert m idx val
  | none => SortedAList.erase m idx

def sortedAListOps : MapOps SortedAList where
  empty := []
  get := SortedAList.get
  set := SortedAList.set
  seq := listSeq

-- 5. Rep 5: `BinTrie` (Canonical Binary Radix Trie)
inductive BinTrie where
  | leaf
  | node (val : Option Val) (left right : BinTrie)

def BinTrie.mkNode (v : Option Val) (l r : BinTrie) : BinTrie :=
  match l, r with
  | .leaf, .leaf =>
    match v with
    | none => .leaf
    | some val => .node (some val) .leaf .leaf
  | .leaf, .node rv rl rr => .node v .leaf (.node rv rl rr)
  | .node lv ll lr, .leaf => .node v (.node lv ll lr) .leaf
  | .node lv ll lr, .node rv rl rr =>
    .node v (.node lv ll lr) (.node rv rl rr)

def BinTrie.seq {α : Type} (t : BinTrie) (k : BinTrie → α) : α :=
  match t with
  | .leaf => k .leaf
  | .node v l r => k (.node v l r)

def BinTrie.getBits : BinTrie → List Bool → Option Val
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l _, false :: bs => BinTrie.getBits l bs
  | .node _ _ r, true :: bs => BinTrie.getBits r bs

def BinTrie.setBits : BinTrie → List Bool → Option Val → BinTrie
  | .leaf, [], val => BinTrie.mkNode val .leaf .leaf
  | .leaf, false :: bs, val =>
    BinTrie.mkNode none (BinTrie.setBits .leaf bs val) .leaf
  | .leaf, true :: bs, val =>
    BinTrie.mkNode none .leaf (BinTrie.setBits .leaf bs val)
  | .node _ l r, [], val => BinTrie.mkNode val l r
  | .node v l r, false :: bs, val =>
    BinTrie.mkNode v (BinTrie.setBits l bs val) r
  | .node v l r, true :: bs, val =>
    BinTrie.mkNode v l (BinTrie.setBits r bs val)

def succBits : List Bool → List Bool
  | [] => [false]
  | false :: bs => true :: bs
  | true :: bs => false :: succBits bs

def natToBits : Nat → List Bool
  | 0 => []
  | n + 1 => succBits (natToBits n)

def binTrieOps : MapOps BinTrie where
  empty := .leaf
  get t idx := BinTrie.getBits t (natToBits idx)
  set t idx val := BinTrie.setBits t (natToBits idx) val
  seq := BinTrie.seq

end BenchCommon
