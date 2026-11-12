#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Benchmark Q-C1 Remedy 2 & Remedy 3: State-store scaling across k in
{1, 4, 8, 12, 16, 24, 33, 57, 99} on the Starnix be64 path for:
  1. lazy_list: Baseline 65-slot List Slot (unforced List.set)
  2. forced_list: 65-slot List Slot with CPS spine forcing at each step
  3. bin_trie_lazy: Depth-7 binary trie (BinTrie Slot) with direct .node update
  4. bin_trie_forced: Depth-7 binary trie (BinTrie Slot) with CPS path forcing
Measures elaboration wall time, peak RSS, [reduction]/[kernel] unfolding counts,
and standalone base.toKernelEnv.replay time."""

import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

HOME = Path.home()
TOOLCHAIN_BIN = (
    HOME
    / ".cache/anneal/toolchain"
    / "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a/lean/bin"
)
LEAN = str(TOOLCHAIN_BIN / "lean")
BRAIN_ROOT = HOME / "<scratch-dir>"
STAGE_SRC = BRAIN_ROOT / "scratch/mvp-investigations/task3/profile_stage"
TRACK_C_DIR = BRAIN_ROOT / "scratch/reference-research/track_c"
WORK_DIR = TRACK_C_DIR / "scaling_probe_stage"

K_VALUES = [1, 4, 8, 12, 16, 24, 33, 57, 99]

HEADER = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""

COMMON_DEFS = """prelude
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
"""


def trace_be64(body):
  markers = set()
  for block in body["blocks"]:
    for stmt in block["statements"]:
      if stmt["kind"] in ("storage_live", "storage_dead"):
        markers.add(stmt["local"])
  locals_ = [
      ("dead" if i in markers else "uninit", None)
      for i in range(len(body["local_tys"]))
  ]
  locals_[1:4] = [
      ("value", ("1", 1)),
      ("value", ("3", 3)),
      ("value", ("value", None)),
  ]
  block = position = 0
  states = []

  def operand(op):
    kind = op["kind"]
    if kind == "constant":
      return str(op["bits"]), op["bits"]
    index = op["local"]
    assert locals_[index][0] == "value"
    value = locals_[index][1]
    if kind == "move":
      locals_[index] = ("uninit", None)
    return value

  def rvalue(rv):
    kind = rv["kind"]
    if kind == "use":
      return operand(rv["operand"])
    if kind == "discriminant":
      index = rv["local"]
      value = locals_[index][1][1]
      table = body["local_tys"][index]["discriminants"]
      return str(table[value]), table[value]
    left, _ = operand(rv["left"])
    right, right_known = operand(rv["right"])
    op = rv["op"]
    if op == "bit_and":
      return f"({left} &&& {right})", None
    if op == "bit_or":
      return f"({left} ||| {right})", None
    amount = right_known % 64
    operator = "<<<" if op == "shl" else ">>>"
    return f"({left} {operator} ({amount} : Nat))", None

  while True:
    states.append((block, position, copy.deepcopy(locals_)))
    current = body["blocks"][block]
    if position < len(current["statements"]):
      stmt = current["statements"][position]
      kind = stmt["kind"]
      if kind == "assign":
        locals_[stmt["local"]] = ("value", rvalue(stmt["value"]))
      elif kind == "storage_live":
        locals_[stmt["local"]] = ("uninit", None)
      elif kind == "storage_dead":
        locals_[stmt["local"]] = ("dead", None)
      position += 1
      continue
    term = current["terminator"]
    if term["kind"] == "ret":
      break
    if term["kind"] == "goto":
      block = term["block"]
    else:
      _, key = operand(term["operand"])
      block = dict(term["targets"]).get(key, term["otherwise"])
    position = 0
  return states


def format_state_def(name, b, p, slots):
  s = f"def {name} (value : Word) : State :=\n  ⟨{b}, {p}, [\n"
  terms = [f".value {x[1][0]}" if x[0] == "value" else "." + x[0] for x in slots]
  for j in range(0, len(terms), 5):
    s += "    " + ", ".join(terms[j : j + 5])
    if j + 5 < len(terms):
      s += ","
    s += "\n"
  s += "  ]⟩\n\n"
  return s


def build_trie_expr(terms, base, span):
  if span == 1:
    val = terms[base] if base < len(terms) else ".dead"
    return f"(.leaf ({val}))"
  half = span // 2
  left = build_trie_expr(terms, base, half)
  right = build_trie_expr(terms, base + half, half)
  return f"(.node {left} {right})"


def format_trie_state_def(name, b, p, slots):
  terms = [f".value {x[1][0]}" if x[0] == "value" else "." + x[0] for x in slots]
  trie_expr = build_trie_expr(terms, 0, 128)
  return (
      f"def {name} (value : Word) : TrieState :=\n"
      f"  ⟨{b}, {p}, {len(slots)}, {trie_expr}⟩\n\n"
  )


def parse_diag_counters(output_text):
  red = {}
  kern = {}
  for line in output_text.splitlines():
    if line.strip().startswith("[reduction]") and "↦" in line:
      m = re.search(r"\[reduction\]\s+(\S+)\s+↦\s+(\d+)", line)
      if m:
        k_name, cnt = m.group(1), int(m.group(2))
        red[k_name] = red.get(k_name, 0) + cnt
    elif line.strip().startswith("[kernel]") and "↦" in line:
      m = re.search(r"\[kernel\]\s+(\S+)\s+↦\s+(\d+)", line)
      if m:
        k_name, cnt = m.group(1), int(m.group(2))
        kern[k_name] = kern.get(k_name, 0) + cnt
  return red, kern


def main():
  out_file = TRACK_C_DIR / "state_store_scaling_probe.json"
  cached_results = []
  if out_file.exists():
    prev = json.loads(out_file.read_text())
    for r in prev.get("results", []):
      if r["representation"] == "bin_trie_lazy" and r["k"] == 99 and r["status"] == "maxRecDepth":
        continue
      if r["representation"] == "lazy_list" and r["k"] >= 16:
        r["status"] = "maxHeartbeats_timeout"
      cached_results.append(r)

  if WORK_DIR.exists():
    shutil.rmtree(WORK_DIR)
  WORK_DIR.mkdir(parents=True)
  shutil.copytree(STAGE_SRC / "target-lib", WORK_DIR / "target-lib")
  shutil.copytree(STAGE_SRC / "target-src", WORK_DIR / "target-src")
  shutil.copytree(STAGE_SRC / "capture", WORK_DIR / "capture")
  for p in STAGE_SRC.glob("*.setup.json"):
    txt = p.read_text().replace(str(STAGE_SRC), str(WORK_DIR))
    (WORK_DIR / p.name).write_text(txt)

  capture_json = json.loads((WORK_DIR / "capture" / "capture.json").read_text())
  body = capture_json["program"]["bodies"][0]
  states = trace_be64(body)
  assert len(states) == 99

  replay_probe_lean = WORK_DIR / "ReplayProbe.lean"
  base_setup = json.loads((WORK_DIR / "BenchState0_be64.setup.json").read_text())

  state_defs = []
  b0, p0, slots0 = states[0]
  state_defs.append(format_state_def("be64_state0", b0, p0, slots0))
  state_defs.append(format_trie_state_def("be64_trie_state0", b0, p0, slots0))
  for k in K_VALUES:
    if k < 99:
      bk, pk, slotsk = states[k]
      state_defs.append(format_state_def(f"be64_state{k}", bk, pk, slotsk))
      state_defs.append(
          format_trie_state_def(f"be64_trie_state{k}", bk, pk, slotsk)
      )

  common_lean_text = (
      HEADER
      + COMMON_DEFS
      + "\n"
      + "".join(state_defs)
      + "end StateStoreScalingProbe\n"
  )
  common_lean_path = WORK_DIR / "target-src" / "StateStoreScalingProbe.lean"
  common_olean_path = WORK_DIR / "target-lib" / "StateStoreScalingProbe.olean"
  common_lean_path.write_text(common_lean_text)
  (TRACK_C_DIR / "StateStoreScalingProbe.lean").write_text(common_lean_text)

  common_setup = copy.deepcopy(base_setup)
  common_setup["name"] = "StateStoreScalingProbe"
  common_setup_path = WORK_DIR / "StateStoreScalingProbe.setup.json"
  common_setup_path.write_text(json.dumps(common_setup))

  print("Compiling StateStoreScalingProbe.lean...", flush=True)
  proc_c = subprocess.run(
      [
          "anneal-lean-run",
          "--mode",
          "file",
          "--concurrency",
          "4",
          "--",
          LEAN,
          "--setup",
          str(common_setup_path),
          "-o",
          str(common_olean_path),
          str(common_lean_path),
      ],
      cwd=WORK_DIR,
      capture_output=True,
      text=True,
      check=False,
  )
  if proc_c.returncode != 0:
    raise RuntimeError(
        f"Failed compiling StateStoreScalingProbe.lean:\n{proc_c.stdout}\n{proc_c.stderr}"
    )

  replay_probe_lean.write_text(
      """import Lean
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (System.FilePath.mk (args[0]!)) [System.FilePath.mk "target-lib"]
  let baseMods : Array Import := #[
    { module := `Init },
    { module := `Trusted.Mvp.Semantics },
    { module := `Anneal.Mvp.Execution },
    { module := `Captured },
    { module := `Expected },
    { module := `InitialCache },
    { module := `StateStoreScalingProbe }
  ]
  let probeMods : Array Import := baseMods.push { module := `ProbeMod }
  enableInitializersExecution
  let env ← importModules probeMods {} 0
  let base ← importModules baseMods {} 0
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  for m in env.header.modules, data in env.header.moduleData do
    if m.module == `ProbeMod then
      for ci in data.constants do
        replayMap := replayMap.insert ci.name ci
  let t0 ← IO.monoNanosNow
  let _ ← base.toKernelEnv.replay replayMap
  let t1 ← IO.monoNanosNow
  let out := Json.mkObj [
    ("replayedCount", toJson replayMap.size),
    ("replayMs", toJson ((t1 - t0).toFloat / 1000000.0))
  ]
  IO.println out.compress
  return 0
"""
  )

  probe_setup = copy.deepcopy(base_setup)
  probe_setup["name"] = "ProbeMod"
  probe_setup["imports"] = [
      {
          "module": "StateStoreScalingProbe",
          "isMeta": False,
          "isExported": True,
          "importAll": False,
      }
  ]
  probe_setup["importArts"]["StateStoreScalingProbe"] = [
      [str(common_olean_path)],
      [],
  ]
  probe_setup_path = WORK_DIR / "ProbeMod.setup.json"
  probe_setup_path.write_text(json.dumps(probe_setup))

  representations = [
      ("lazy_list", "stepNLazy", "be64_state", False),
      ("forced_list", "stepNForced", "be64_state", True),
      ("bin_trie_lazy", "stepNTrieLazy", "be64_trie_state", True),
      ("bin_trie_forced", "stepNTrieForced", "be64_trie_state", True),
  ]

  results = list(cached_results)
  done_keys = {(r["representation"], r["k"]) for r in results}

  for rep_name, fn_name, state_prefix, need_max_rec in representations:
    print(f"=== Representation: {rep_name} ===", flush=True)
    for k in K_VALUES:
      if (rep_name, k) in done_keys:
        continue
      rhs = (
          ".ret (swap64 value)"
          if k == 99
          else f".next ({state_prefix}{k} value)"
      )
      rec_opt = "set_option maxRecDepth 100000 in\n" if need_max_rec else ""
      probe_code = f"""prelude
import StateStoreScalingProbe

namespace ProbeMod

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction StateStoreScalingProbe

{rec_opt}set_option diagnostics true in
theorem test_k (value : Word) :
    {fn_name} {k} sourceBody ({state_prefix}0 value) = {rhs} := by
  rfl

end ProbeMod
"""
      probe_lean_path = WORK_DIR / "ProbeMod.lean"
      probe_olean_path = WORK_DIR / "target-lib" / "ProbeMod.olean"
      if probe_olean_path.exists():
        probe_olean_path.unlink()
      probe_lean_path.write_text(probe_code)

      t0 = time.perf_counter()
      proc = subprocess.run(
          [
              "/usr/bin/time",
              "-f",
              "TIME_ELAPSED=%e TIME_RSS_KB=%M",
              "anneal-lean-run",
              "--mode",
              "file",
              "--concurrency",
              "4",
              "--",
              LEAN,
              "--setup",
              str(probe_setup_path),
              "-o",
              str(probe_olean_path),
              str(probe_lean_path),
          ],
          cwd=WORK_DIR,
          capture_output=True,
          text=True,
          check=False,
      )
      wall_s = time.perf_counter() - t0
      m_rss = re.search(r"TIME_RSS_KB=(\d+)", proc.stderr)
      rss_kb = int(m_rss.group(1)) if m_rss else 0
      combined_out = proc.stdout + "\n" + proc.stderr
      red_cnts, kern_cnts = parse_diag_counters(combined_out)

      if proc.returncode != 0:
        err_kind = (
            "maxHeartbeats_timeout"
            if "heartbeats" in combined_out
            else (
                "maxRecDepth"
                if "maximum recursion depth" in combined_out
                else "error"
            )
        )
        row = {
            "representation": rep_name,
            "k": k,
            "status": err_kind,
            "compile_wall_s": round(wall_s, 4),
            "compile_peak_rss_kb": rss_kb,
            "kernel_replay_ms": None,
            "reduction_unfoldings_top": dict(
                sorted(red_cnts.items(), key=lambda x: -x[1])[:8]
            ),
            "kernel_unfoldings_top": dict(
                sorted(kern_cnts.items(), key=lambda x: -x[1])[:8]
            ),
        }
        print(json.dumps(row), flush=True)
        results.append(row)
        if err_kind == "maxHeartbeats_timeout":
          for k_skip in [kv for kv in K_VALUES if kv > k]:
            results.append({
                "representation": rep_name,
                "k": k_skip,
                "status": "skipped_after_timeout",
                "compile_wall_s": None,
                "compile_peak_rss_kb": None,
                "kernel_replay_ms": None,
            })
          break
        continue

      proc_r = subprocess.run(
          [
              "anneal-lean-run",
              "--mode",
              "file",
              "--concurrency",
              "4",
              "--",
              LEAN,
              "--run",
              str(replay_probe_lean),
              str(TOOLCHAIN_BIN.parent),
          ],
          cwd=WORK_DIR,
          capture_output=True,
          text=True,
          check=True,
      )
      replay_info = json.loads(proc_r.stdout.strip().splitlines()[-1])

      row = {
          "representation": rep_name,
          "k": k,
          "status": "ok",
          "compile_wall_s": round(wall_s, 4),
          "compile_peak_rss_kb": rss_kb,
          "kernel_replay_ms": round(replay_info["replayMs"], 3),
          "olean_bytes": probe_olean_path.stat().st_size,
          "reduction_unfoldings_top": dict(
              sorted(red_cnts.items(), key=lambda x: -x[1])[:8]
          ),
          "kernel_unfoldings_top": dict(
              sorted(kern_cnts.items(), key=lambda x: -x[1])[:8]
          ),
      }
      print(json.dumps(row), flush=True)
      results.append(row)

  out_file.write_text(
      json.dumps(
          {
              "benchmark": "Q-C1_Remedy2_Remedy3_StateStoreScaling",
              "lean_version": "4.34.1",
              "path": "Starnix apply_endianness be64 (99 steps, 65 locals)",
              "k_values": K_VALUES,
              "results": results,
          },
          indent=2,
      )
      + "\n"
  )
  print(f"Saved results to {out_file}")


if __name__ == "__main__":
  main()
