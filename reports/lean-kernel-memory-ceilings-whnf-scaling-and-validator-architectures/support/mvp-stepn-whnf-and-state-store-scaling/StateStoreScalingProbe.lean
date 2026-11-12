-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import InitialCache

namespace StateStoreScalingProbe

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

-- 1. Lazy List Slot multi-step evaluator
def stepNLazy : Nat → Body → State → StepResult
  | 0, _, s => .next s
  | k + 1, body, s =>
      match step body s with
      | .next s' => stepNLazy k body s'
      | res => res

-- 2. CPS Spine-Forced List Slot multi-step evaluator
def forceList (xs : List Slot) (cont : List Slot → α) : α :=
  match xs with
  | [] => cont []
  | a :: as => forceList as (fun as' => cont (a :: as'))

def forceNat (n : Nat) (cont : Nat → α) : α :=
  match n with
  | 0 => cont 0
  | m + 1 => forceNat m (fun m' => cont (m' + 1))

def forceState (s : State) (cont : State → α) : α :=
  forceNat s.block (fun b =>
    forceNat s.statement (fun st =>
      forceList s.locals (fun locs =>
        cont ⟨b, st, locs⟩)))

def stepNForced : Nat → Body → State → StepResult
  | 0, _, s => .next s
  | k + 1, body, s =>
      match step body s with
      | .next s' => forceState s' (stepNForced k body)
      | res => res

-- 3 & 4. Fixed-Depth 7-Bit Binary Trie (BinTrie Slot, depth 7 -> 128 leaves >= 65 slots)
-- Non-recursive 7-level structural binary range split using Nat.ble and Nat.sub
-- avoids WellFounded.fix in Nat.div/Nat.mod during kernel and elaborator WHNF.
inductive BinTrie (α : Type) where
  | leaf (val : α)
  | node (left right : BinTrie α)

def get0 (d : α) : BinTrie α → α
  | .leaf v => v
  | _ => d

def get1 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 1 i then get0 d r else get0 d l
  | _ => d

def get2 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 2 i then get1 d r (i - 2) else get1 d l i
  | _ => d

def get4 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 4 i then get2 d r (i - 4) else get2 d l i
  | _ => d

def get8 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 8 i then get4 d r (i - 8) else get4 d l i
  | _ => d

def get16 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 16 i then get8 d r (i - 16) else get8 d l i
  | _ => d

def get32 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 32 i then get16 d r (i - 32) else get16 d l i
  | _ => d

def get64 (d : α) (t : BinTrie α) (i : Nat) : α :=
  match t with
  | .node l r => if Nat.ble 64 i then get32 d r (i - 64) else get32 d l i
  | _ => d

-- Lazy 7-level binary trie update
def setLazy0 (v : α) : BinTrie α := .leaf v

def setLazy1 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 1 i then .node l (setLazy0 v)
      else .node (setLazy0 v) r
  | _ => t

def setLazy2 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 2 i then .node l (setLazy1 r (i - 2) v)
      else .node (setLazy1 l i v) r
  | _ => t

def setLazy4 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 4 i then .node l (setLazy2 r (i - 4) v)
      else .node (setLazy2 l i v) r
  | _ => t

def setLazy8 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 8 i then .node l (setLazy4 r (i - 8) v)
      else .node (setLazy4 l i v) r
  | _ => t

def setLazy16 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 16 i then .node l (setLazy8 r (i - 16) v)
      else .node (setLazy8 l i v) r
  | _ => t

def setLazy32 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 32 i then .node l (setLazy16 r (i - 32) v)
      else .node (setLazy16 l i v) r
  | _ => t

def setLazy64 (t : BinTrie α) (i : Nat) (v : α) : BinTrie α :=
  match t with
  | .node l r =>
      if Nat.ble 64 i then .node l (setLazy32 r (i - 64) v)
      else .node (setLazy32 l i v) r
  | _ => t

-- CPS path-forcing 7-level binary trie update
def setCPS0 (v : α) (k : BinTrie α → β) : β := k (.leaf v)

def setCPS1 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 1 i then setCPS0 v (fun r' => k (.node l r'))
      else setCPS0 v (fun l' => k (.node l' r))
  | _ => k t

def setCPS2 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 2 i then setCPS1 r (i - 2) v (fun r' => k (.node l r'))
      else setCPS1 l i v (fun l' => k (.node l' r))
  | _ => k t

def setCPS4 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 4 i then setCPS2 r (i - 4) v (fun r' => k (.node l r'))
      else setCPS2 l i v (fun l' => k (.node l' r))
  | _ => k t

def setCPS8 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 8 i then setCPS4 r (i - 8) v (fun r' => k (.node l r'))
      else setCPS4 l i v (fun l' => k (.node l' r))
  | _ => k t

def setCPS16 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 16 i then setCPS8 r (i - 16) v (fun r' => k (.node l r'))
      else setCPS8 l i v (fun l' => k (.node l' r))
  | _ => k t

def setCPS32 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 32 i then setCPS16 r (i - 32) v (fun r' => k (.node l r'))
      else setCPS16 l i v (fun l' => k (.node l' r))
  | _ => k t

def setCPS64 (t : BinTrie α) (i : Nat) (v : α) (k : BinTrie α → β) : β :=
  match t with
  | .node l r =>
      if Nat.ble 64 i then setCPS32 r (i - 64) v (fun r' => k (.node l r'))
      else setCPS32 l i v (fun l' => k (.node l' r))
  | _ => k t

structure TrieState where
  block : Nat
  statement : Nat
  localCount : Nat
  locals : BinTrie Slot

inductive TrieStepResult where
  | next (state : TrieState)
  | ret (word : Word)
  | fault (reason : Fault)

def readLocalTrie (body : Body) (localCount : Nat) (locals : BinTrie Slot) (index : Nat) :
    Except Fault (Ty × Word) :=
  if index < localCount then
    match body.localTys[index]?, get64 .dead locals index with
    | some ty, .value value =>
        if validValue ty value then .ok (ty, value) else .error .invalidValue
    | some _, .dead => .error .deadLocal
    | some _, .uninit => .error .uninitialized
    | none, _ => .error .badLocal
  else .error .badLocal

def evalOperandTrieLazy (body : Body) (localCount : Nat) (locals : BinTrie Slot) :
    Operand → Except Fault (Ty × Word × BinTrie Slot)
  | .copy index =>
      match readLocalTrie body localCount locals index with
      | .ok (ty, value) => .ok (ty, value, locals)
      | .error reason => .error reason
  | .move index =>
      match readLocalTrie body localCount locals index with
      | .ok (ty, value) => .ok (ty, value, setLazy64 locals index .uninit)
      | .error reason => .error reason
  | .constant ty bits =>
      if rawValid ty bits then .ok (ty, BitVec.ofNat 64 bits, locals)
      else .error .invalidValue

def evalRvalueTrieLazy (body : Body) (localCount : Nat) (locals : BinTrie Slot) :
    Rvalue → Except Fault (Ty × Word × BinTrie Slot)
  | .unit => .ok (.unit, 0, locals)
  | .use operand _ => evalOperandTrieLazy body localCount locals operand
  | .binary op left right =>
      match evalOperandTrieLazy body localCount locals left with
      | .error reason => .error reason
      | .ok (lt, lv, locals') =>
          match evalOperandTrieLazy body localCount locals' right with
          | .error reason => .error reason
          | .ok (rt, rv, locals'') =>
              match evalBinary op lt lv rt rv with
              | .ok (ty, value) => .ok (ty, value, locals'')
              | .error reason => .error reason
  | .discriminant index =>
      match readLocalTrie body localCount locals index with
      | .error reason => .error reason
      | .ok (.enum _ ds, value) =>
          match ds[value.toNat]? with
          | some disc => .ok (.int 64 true, BitVec.ofNat 64 disc, locals)
          | none => .error .invalidValue
      | .ok _ => .error .typeMismatch

def writeLocalTrieLazy (body : Body) (localCount : Nat) (locals : BinTrie Slot)
    (index : Nat) (ty : Ty) (value : Word) : Except Fault (BinTrie Slot) :=
  if index < localCount then
    match body.localTys[index]?, get64 .dead locals index with
    | some targetTy, slot =>
        if targetTy != ty then .error .typeMismatch
        else if !(validValue targetTy value) then .error .invalidValue
        else match slot with
          | .dead => .error .deadLocal
          | _ => .ok (setLazy64 locals index (.value value))
    | none, _ => .error .badLocal
  else .error .badLocal

def execStatementTrieLazy (body : Body) (localCount : Nat) (locals : BinTrie Slot) :
    Statement → Except Fault (BinTrie Slot)
  | .assign index rhs =>
      match evalRvalueTrieLazy body localCount locals rhs with
      | .error reason => .error reason
      | .ok (ty, value, locals') => writeLocalTrieLazy body localCount locals' index ty value
  | .storageLive index =>
      if (index < body.localTys.length) && (index < localCount) then
        .ok (setLazy64 locals index .uninit)
      else .error .badLocal
  | .storageDead index =>
      if (index < body.localTys.length) && (index < localCount) then
        .ok (setLazy64 locals index .dead)
      else .error .badLocal
  | .nop => .ok locals

def execTerminatorTrieLazy (body : Body) (state : TrieState) : Terminator → TrieStepResult
  | .goto block => .next ⟨block, 0, state.localCount, state.locals⟩
  | .switchInt operand targets otherwise =>
      match evalOperandTrieLazy body state.localCount state.locals operand with
      | .error reason => .fault reason
      | .ok (ty, value, locals) =>
          if switchTy ty then
            .next ⟨switchTarget value.toNat targets otherwise, 0, state.localCount, locals⟩
          else .fault .typeMismatch
  | .ret =>
      match readLocalTrie body state.localCount state.locals 0 with
      | .ok (_, value) => .ret value
      | .error reason => .fault reason
  | .unreachable => .fault .unreachable

def stepTrieLazy (body : Body) (state : TrieState) : TrieStepResult :=
  match body.blocks[state.block]? with
  | none => .fault .badBlock
  | some block =>
      match block.statements[state.statement]? with
      | some statement =>
          match execStatementTrieLazy body state.localCount state.locals statement with
          | .ok locals => .next ⟨state.block, state.statement + 1, state.localCount, locals⟩
          | .error reason => .fault reason
      | none =>
          if state.statement == block.statements.length then
            execTerminatorTrieLazy body state block.terminator
          else .fault .badPosition

def stepNTrieLazy : Nat → Body → TrieState → TrieStepResult
  | 0, _, s => .next s
  | k + 1, body, s =>
      match stepTrieLazy body s with
      | .next s' => stepNTrieLazy k body s'
      | res => res

-- CPS Path-Forced Binary Trie evaluator
def evalOperandTrieCPS (body : Body) (localCount : Nat) (locals : BinTrie Slot)
    (op : Operand) (cont : Except Fault (Ty × Word × BinTrie Slot) → α) : α :=
  match op with
  | .copy index =>
      match readLocalTrie body localCount locals index with
      | .ok (ty, value) => cont (.ok (ty, value, locals))
      | .error reason => cont (.error reason)
  | .move index =>
      match readLocalTrie body localCount locals index with
      | .ok (ty, value) =>
          setCPS64 locals index .uninit (fun locals' =>
            cont (.ok (ty, value, locals')))
      | .error reason => cont (.error reason)
  | .constant ty bits =>
      if rawValid ty bits then cont (.ok (ty, BitVec.ofNat 64 bits, locals))
      else cont (.error .invalidValue)

def evalRvalueTrieCPS (body : Body) (localCount : Nat) (locals : BinTrie Slot)
    (rv : Rvalue) (cont : Except Fault (Ty × Word × BinTrie Slot) → α) : α :=
  match rv with
  | .unit => cont (.ok (.unit, 0, locals))
  | .use operand _ => evalOperandTrieCPS body localCount locals operand cont
  | .binary op left right =>
      evalOperandTrieCPS body localCount locals left (fun r1 =>
        match r1 with
        | .error reason => cont (.error reason)
        | .ok (lt, lv, locals') =>
            evalOperandTrieCPS body localCount locals' right (fun r2 =>
              match r2 with
              | .error reason => cont (.error reason)
              | .ok (rt, rv, locals'') =>
                  match evalBinary op lt lv rt rv with
                  | .ok (ty, value) => cont (.ok (ty, value, locals''))
                  | .error reason => cont (.error reason)))
  | .discriminant index =>
      match readLocalTrie body localCount locals index with
      | .error reason => cont (.error reason)
      | .ok (.enum _ ds, value) =>
          match ds[value.toNat]? with
          | some disc => cont (.ok (.int 64 true, BitVec.ofNat 64 disc, locals))
          | none => cont (.error .invalidValue)
      | .ok _ => cont (.error .typeMismatch)

def writeLocalTrieCPS (body : Body) (localCount : Nat) (locals : BinTrie Slot)
    (index : Nat) (ty : Ty) (value : Word)
    (cont : Except Fault (BinTrie Slot) → α) : α :=
  if index < localCount then
    match body.localTys[index]?, get64 .dead locals index with
    | some targetTy, slot =>
        if targetTy != ty then cont (.error .typeMismatch)
        else if !(validValue targetTy value) then cont (.error .invalidValue)
        else match slot with
          | .dead => cont (.error .deadLocal)
          | _ => setCPS64 locals index (.value value) (fun l' => cont (.ok l'))
    | none, _ => cont (.error .badLocal)
  else cont (.error .badLocal)

def stepTrieCPS (body : Body) (state : TrieState) (cont : TrieStepResult → α) : α :=
  match body.blocks[state.block]? with
  | none => cont (.fault .badBlock)
  | some block =>
      match block.statements[state.statement]? with
      | some statement =>
          let nextPos := state.statement + 1
          match statement with
          | .assign index rhs =>
              evalRvalueTrieCPS body state.localCount state.locals rhs (fun rvRes =>
                match rvRes with
                | .error reason => cont (.fault reason)
                | .ok (ty, value, locals') =>
                    writeLocalTrieCPS body state.localCount locals' index ty value (fun wrRes =>
                      match wrRes with
                      | .ok locals'' =>
                          forceNat state.block (fun b' =>
                            forceNat nextPos (fun st' =>
                              cont (.next ⟨b', st', state.localCount, locals''⟩)))
                      | .error reason => cont (.fault reason)))
          | .storageLive index =>
              if (index < body.localTys.length) && (index < state.localCount) then
                setCPS64 state.locals index .uninit (fun locals' =>
                  forceNat state.block (fun b' =>
                    forceNat nextPos (fun st' =>
                      cont (.next ⟨b', st', state.localCount, locals'⟩))))
              else cont (.fault .badLocal)
          | .storageDead index =>
              if (index < body.localTys.length) && (index < state.localCount) then
                setCPS64 state.locals index .dead (fun locals' =>
                  forceNat state.block (fun b' =>
                    forceNat nextPos (fun st' =>
                      cont (.next ⟨b', st', state.localCount, locals'⟩))))
              else cont (.fault .badLocal)
          | .nop =>
              forceNat state.block (fun b' =>
                forceNat nextPos (fun st' =>
                  cont (.next ⟨b', st', state.localCount, state.locals⟩)))
      | none =>
          if state.statement == block.statements.length then
            match block.terminator with
            | .goto target =>
                forceNat target (fun b' =>
                  cont (.next ⟨b', 0, state.localCount, state.locals⟩))
            | .switchInt operand targets otherwise =>
                evalOperandTrieCPS body state.localCount state.locals operand (fun opRes =>
                  match opRes with
                  | .error reason => cont (.fault reason)
                  | .ok (ty, value, locals') =>
                      if switchTy ty then
                        forceNat (switchTarget value.toNat targets otherwise) (fun b' =>
                          cont (.next ⟨b', 0, state.localCount, locals'⟩))
                      else cont (.fault .typeMismatch))
            | .ret =>
                match readLocalTrie body state.localCount state.locals 0 with
                | .ok (_, value) => cont (.ret value)
                | .error reason => cont (.fault reason)
            | .unreachable => cont (.fault .unreachable)
          else cont (.fault .badPosition)

def stepNTrieForced : Nat → Body → TrieState → TrieStepResult
  | 0, _, s => .next s
  | k + 1, body, s =>
      stepTrieCPS body s (fun res =>
        match res with
        | .next s' => stepNTrieForced k body s'
        | res => res)

def be64_state0 (value : Word) : State :=
  ⟨0, 0, [
    .uninit, .value 1, .value 3, .value value, .dead,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state0 (value : Word) : TrieState :=
  ⟨0, 0, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state1 (value : Word) : State :=
  ⟨0, 1, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state1 (value : Word) : TrieState :=
  ⟨0, 1, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state4 (value : Word) : State :=
  ⟨1, 1, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .value 3, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state4 (value : Word) : TrieState :=
  ⟨1, 1, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.value 3))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state8 (value : Word) : State :=
  ⟨4, 3, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .uninit, .uninit, .uninit, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state8 (value : Word) : TrieState :=
  ⟨4, 3, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit))))))) (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state12 (value : Word) : State :=
  ⟨4, 7, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .uninit, .uninit, .uninit, .uninit, .uninit,
    .uninit, .uninit, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state12 (value : Word) : TrieState :=
  ⟨4, 7, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit))))))) (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.uninit)) (.leaf (.uninit)))) (.node (.node (.leaf (.uninit)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state16 (value : Word) : State :=
  ⟨4, 11, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .uninit, .uninit, .uninit, .uninit, .uninit,
    .uninit, .uninit, .value (value &&& 255), .uninit, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state16 (value : Word) : TrieState :=
  ⟨4, 11, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit))))))) (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.uninit)) (.leaf (.uninit)))) (.node (.node (.leaf (.uninit)) (.leaf (.value (value &&& 255)))) (.node (.leaf (.uninit)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state24 (value : Word) : State :=
  ⟨4, 19, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .uninit, .uninit, .uninit, .uninit, .uninit,
    .uninit, .value ((value &&& 255) <<< (56 : Nat)), .dead, .dead, .uninit,
    .value (value &&& 65280), .uninit, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state24 (value : Word) : TrieState :=
  ⟨4, 19, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit))))))) (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.uninit)) (.leaf (.uninit)))) (.node (.node (.leaf (.value ((value &&& 255) <<< (56 : Nat)))) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.uninit))))) (.node (.node (.node (.leaf (.value (value &&& 65280))) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state33 (value : Word) : State :=
  ⟨4, 28, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .uninit, .uninit, .uninit, .uninit, .uninit,
    .value (((value &&& 255) <<< (56 : Nat)) ||| ((value &&& 65280) <<< (40 : Nat))), .dead, .dead, .dead, .dead,
    .dead, .dead, .uninit, .uninit, .uninit,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state33 (value : Word) : TrieState :=
  ⟨4, 28, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit))))))) (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.uninit)) (.leaf (.value (((value &&& 255) <<< (56 : Nat)) ||| ((value &&& 65280) <<< (40 : Nat))))))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit)))) (.node (.node (.leaf (.uninit)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

def be64_state57 (value : Word) : State :=
  ⟨4, 52, [
    .uninit, .value 1, .value 3, .value value, .uninit,
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .uninit, .uninit, .uninit, .value (((((value &&& 255) <<< (56 : Nat)) ||| ((value &&& 65280) <<< (40 : Nat))) ||| ((value &&& 16711680) <<< (24 : Nat))) ||| ((value &&& 4278190080) <<< (8 : Nat))), .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .uninit, .value (value &&& 1095216660480),
    .uninit, .dead, .dead, .dead, .dead,
    .dead, .dead, .dead, .dead, .dead,
    .dead, .uninit, .dead, .dead, .dead
  ]⟩

def be64_trie_state57 (value : Word) : TrieState :=
  ⟨4, 52, 65, (.node (.node (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value 1))) (.node (.leaf (.value 3)) (.leaf (.value value)))) (.node (.node (.leaf (.uninit)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.uninit)) (.leaf (.uninit))))))) (.node (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value (((((value &&& 255) <<< (56 : Nat)) ||| ((value &&& 65280) <<< (40 : Nat))) ||| ((value &&& 16711680) <<< (24 : Nat))) ||| ((value &&& 4278190080) <<< (8 : Nat)))))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.uninit)) (.leaf (.value (value &&& 1095216660480)))) (.node (.leaf (.uninit)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.uninit))) (.node (.leaf (.dead)) (.leaf (.dead)))))))) (.node (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))))) (.node (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))) (.node (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead))))) (.node (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))) (.node (.node (.leaf (.dead)) (.leaf (.dead))) (.node (.leaf (.dead)) (.leaf (.dead)))))))))⟩

end StateStoreScalingProbe
