-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Init.Data.UInt.BasicAux
public import Trusted.CppAst

@[expose] public section

namespace Trusted.CppSemantics

open Trusted.CppAst

/-!
# Rung-0 C11 Machine State and Value Model (`Trusted.CppSemantics.State`)

Tactic-free Ring-0 machine values (`CppByte`, `CppVal`), provenance-tracked
allocations (`CppAlloc`, `CppMemory`), call frames (`CppFrame`, `CppState`),
boundary query/output records (`CppQuery`, `CppOut`, `CppTerminalOut`), and
total lookup/update helpers.
-/

/-- Operational fault classification in Rung-0 C11 semantics:
- `undefined`: Modeled C11 Undefined Behavior (signed overflow under `isoUB`,
  division/remainder by zero, `INT_MIN / -1`, invalid shift count, null/dead/
  misaligned/OOB deref, out-of-bounds `ptrAdd`, reading `.uninit` scalar,
  writing to a `const` object, partially overlapping aggregate assignment,
  `unreachable`).
- `unsupported`: Unmodeled C11 construct, policy, or external callee. -/
inductive CppFaultKind where
  | undefined
  | unsupported

/-- Single-step execution result for Rung-0 C11. -/
inductive CppStepResult (State Out : Type) where
  | step  (next : State)
  | done  (out : Out)
  | fault (kind : CppFaultKind)

/-- Abstract byte in C11 memory:
- `uninit`: Uninitialized storage (indeterminate value).
- `data b`: Initialized raw data byte `b : UInt8`.
- `ptrFrag allocId addr subRange fragIdx`: Pointer-provenance fragment byte
  `fragIdx` of pointer `(allocId, addr, subRange)`. -/
inductive CppByte where
  | uninit
  | data (b : UInt8)
  | ptrFrag (allocId : Nat) (addr : Nat) (subRange : Option (Nat × Nat))
            (fragIdx : Nat)

/-- Canonical Rung-0 C11 runtime value. Integer values store their canonical
unsigned two's-complement bit representation `unsignedBits < 2^width.bitWidth`
alongside `(width, sign)`. Pointers store optional provenance `allocId`, byte
address `addr` (`ptr none 0 none` is `NULL`), and an optional
`subRange = some (lo, len)` narrowing arithmetic and dereference to the
subobject
`[lo, lo + len)` the pointer was derived from (a member or array element). -/
inductive CppVal where
  | void
  | bool (b : Bool)
  | int (width : CppIntWidth) (sign : Signedness) (unsignedBits : Nat)
  | ptr (allocId : Option Nat) (addr : Nat) (subRange : Option (Nat × Nat))
  | aggregate (bytes : List CppByte)

/-- Provenance- and effective-type-tracked memory allocation under PNVI-ae-udi
and C11 §6.5p7 strict aliasing. -/
structure CppAlloc where
  allocId     : Nat
  sizeBytes   : Nat
  alignBytes  : Nat
  live        : Bool
  isConst     : Bool
  effectiveTy : Option CppTy
  bytes       : List CppByte
  baseAddr    : Nat := 4096

/-- Abstract C11 memory state tracking all allocations and fresh-ID counters. -/
structure CppMemory where
  allocs      : List CppAlloc := []
  nextAllocId : Nat := 1
  nextAddr    : Nat := 4096

/-- Canonical empty `CppMemory` value (avoiding ambiguous `{}` syntax). -/
noncomputable def emptyCppMemory : CppMemory :=
  { allocs := [], nextAllocId := 1, nextAddr := 4096 }

/-- Local variable slot in an active `CppFrame`. -/
inductive CppLocalSlot where
  | dead
  | uninit
  | val (v : CppVal)
  | stackAddr (allocId : Nat)

/-- Active call-stack frame executing `prog.bodies[defId]` at
`(blockId, stmtIdx)`. `stackAllocs` records allocations owned by this frame
that are deallocated on return. -/
structure CppFrame where
  defId       : Nat
  blockId     : BlockId
  stmtIdx     : Nat
  locals      : List CppLocalSlot
  retDst      : Option (CppPlace × CppTy)
  retBlock    : BlockId
  stackAllocs : List Nat

/-- Machine execution state consisting of a non-empty call stack and memory. -/
structure CppState where
  frames : List CppFrame
  mem    : CppMemory

/-- Per-invocation entry query: argument values and initial caller memory. -/
structure CppQuery where
  args : List CppVal
  mem  : CppMemory := emptyCppMemory

/-- Per-invocation normal return output: return value and post-call memory. -/
structure CppOut where
  ret : CppVal
  mem : CppMemory := emptyCppMemory

/-- Observable terminal outcome for a Rung-0 C11 execution. -/
inductive CppTerminalOut where
  | returned (out : CppOut)
  | unwound  (mem : CppMemory := emptyCppMemory)
  | aborted  (mem : CppMemory := emptyCppMemory)

/-- Total list lookup by index without `Decidable` bounds proofs. -/
noncomputable def cppGetElem? {α : Type} : List α → Nat → Option α
  | [],      _     => none
  | x :: _,  0     => some x
  | _ :: xs, n + 1 => cppGetElem? xs n

/-- Total list update by index, returning `none` when out of bounds. -/
noncomputable def cppSetElem? {α : Type} :
    List α → Nat → α → Option (List α)
  | [],      _,     _ => none
  | _ :: xs, 0,     v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match cppSetElem? xs n v with
    | some xs' => some (x :: xs')
    | none     => none

/-- Look up a record definition by `recordId`. -/
noncomputable def findRecord? (records : List CppRecordDef) (id : String) :
    Option CppRecordDef :=
  match records with
  | [] => none
  | r :: rest =>
    if r.recordId == id then some r else findRecord? rest id

/-- Look up a body and its index in `bodies` by `identity`. -/
noncomputable def findBodyByNameAux (bodies : List CppBody) (id : String)
    (idx : Nat) : Option (Nat × CppBody) :=
  match bodies with
  | [] => none
  | b :: rest =>
    if b.identity == id then some (idx, b)
    else findBodyByNameAux rest id (idx + 1)

/-- Look up a body and its `DefId` index by `identity`. -/
noncomputable def findBodyByName? (bodies : List CppBody) (id : String) :
    Option (Nat × CppBody) :=
  findBodyByNameAux bodies id 0

/-- Build a list of `n` copies of `x`. -/
noncomputable def cppReplicate {α : Type} (n : Nat) (x : α) : List α :=
  match n with
  | 0     => []
  | k + 1 => x :: cppReplicate k x

/-- Extract a contiguous slice of `len` elements starting at `offset`. -/
noncomputable def cppListSlice {α : Type} (xs : List α) (offset len : Nat) :
    List α :=
  (xs.drop offset).take len

/-- Overwrite a contiguous slice of `xs` starting at `offset` with `patch`. -/
noncomputable def cppListWriteSlice {α : Type} :
    List α → Nat → List α → Option (List α)
  | xs, 0, [] => some xs
  | _ :: xs, 0, p :: ps =>
    match cppListWriteSlice xs 0 ps with
    | some rest => some (p :: rest)
    | none      => none
  | [], 0, _ :: _ => none
  | x :: xs, n + 1, ps =>
    match cppListWriteSlice xs n ps with
    | some rest => some (x :: rest)
    | none      => none
  | [], _ + 1, _ => none

end Trusted.CppSemantics

end
