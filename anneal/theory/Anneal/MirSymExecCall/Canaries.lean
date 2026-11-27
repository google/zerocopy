-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirSymExec
public import Anneal.MirSymExecCall

@[expose] public section

namespace Anneal.MirSymExecCall.Canaries

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.MirTotal
open Anneal.MirSymExec Anneal.MirSymExecCall

/-!
# Multi-Frame Symbolic Execution Canary: `parity_even_call`

`canaryProgParityCall` is the MIR that `anneal-rustc-capture` emits for

```rust
#![no_std]

#[inline(never)]
fn fold(b: u8, k: u32) -> u8 {
    b ^ (b >> k)
}

pub fn parity_even_call(b: u8) -> bool {
    let b = fold(b, 4);
    let b = fold(b, 2);
    let b = fold(b, 1);
    (b & 1) == 0
}
```

(edition 2021, no overflow checks), transcribed with the same statements in
the same order: body `0` is `parity_even_call` and body `1` is `fold`. The
run takes 68 steps across three intra-crate calls; eleven chunks of at most 7
steps check it under the default `maxHeartbeats`.
-/

/-- Body `0`: `parity_even_call`. -/
noncomputable def canaryBodyParityCall : Body :=
  { identity := "rust-path-v1::parity_even_call"
    isUnsafe := false
    argumentCount := 1
    locals := [.bool, .int .i8 false, .int .i8 false, .int .i8 false,
               .int .i8 false, .int .i8 false, .int .i8 false, .int .i8 false,
               .int .i8 false, .int .i8 false]
    basicBlocks :=
      [ { statements :=
            [ .storageLive 2,
              .storageLive 3,
              .assign { localId := 3, projection := [] }
                (.use (.copy { localId := 1, projection := [] })) ]
          terminator := .call 1
            [ .move { localId := 3, projection := [] },
              .constant { ty := .int .i32 false, lit := .scalar 4 } ]
            { localId := 2, projection := [] } (some 1) .continue_
          cleanup := false },
        { statements :=
            [ .storageDead 3,
              .storageLive 4,
              .storageLive 5,
              .assign { localId := 5, projection := [] }
                (.use (.copy { localId := 2, projection := [] })) ]
          terminator := .call 1
            [ .move { localId := 5, projection := [] },
              .constant { ty := .int .i32 false, lit := .scalar 2 } ]
            { localId := 4, projection := [] } (some 2) .continue_
          cleanup := false },
        { statements :=
            [ .storageDead 5,
              .storageLive 6,
              .storageLive 7,
              .assign { localId := 7, projection := [] }
                (.use (.copy { localId := 4, projection := [] })) ]
          terminator := .call 1
            [ .move { localId := 7, projection := [] },
              .constant { ty := .int .i32 false, lit := .scalar 1 } ]
            { localId := 6, projection := [] } (some 3) .continue_
          cleanup := false },
        { statements :=
            [ .storageDead 7,
              .storageLive 8,
              .storageLive 9,
              .assign { localId := 9, projection := [] }
                (.use (.copy { localId := 6, projection := [] })),
              .assign { localId := 8, projection := [] }
                (.binaryOp .bitAnd (.move { localId := 9, projection := [] })
                  (.constant { ty := .int .i8 false, lit := .scalar 1 })),
              .storageDead 9,
              .assign { localId := 0, projection := [] }
                (.binaryOp .eq (.move { localId := 8, projection := [] })
                  (.constant { ty := .int .i8 false, lit := .scalar 0 })),
              .storageDead 8,
              .storageDead 6,
              .storageDead 4,
              .storageDead 2 ]
          terminator := .return_
          cleanup := false } ] }

/-- Body `1`: `fold`. -/
noncomputable def canaryBodyFold : Body :=
  { identity := "rust-path-v1::fold"
    isUnsafe := false
    argumentCount := 2
    locals := [.int .i8 false, .int .i8 false, .int .i32 false, .int .i8 false,
               .int .i8 false, .int .i8 false, .int .i32 false]
    basicBlocks :=
      [ { statements :=
            [ .storageLive 3,
              .assign { localId := 3, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .storageLive 4,
              .storageLive 5,
              .assign { localId := 5, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .storageLive 6,
              .assign { localId := 6, projection := [] }
                (.use (.copy { localId := 2, projection := [] })),
              .assign { localId := 4, projection := [] }
                (.binaryOp .shr (.move { localId := 5, projection := [] })
                  (.move { localId := 6, projection := [] })),
              .storageDead 6,
              .storageDead 5,
              .assign { localId := 0, projection := [] }
                (.binaryOp .bitXor (.move { localId := 3, projection := [] })
                  (.move { localId := 4, projection := [] })),
              .storageDead 4,
              .storageDead 3 ]
          terminator := .return_
          cleanup := false } ] }

/-- The captured two-body program. -/
noncomputable def canaryProgParityCall : Program :=
  { pointerWidthBits := 64
    mirProfileVersion := 1
    scope := .unit
    entryDefId := 0
    bodies := [canaryBodyParityCall, canaryBodyFold]
    overflowChecks := false
    panicStrategy := .unwind
    hasLocalPanicHandler := false }

/-- The program the symbolic executor steps (`entryDefId := 0`). -/
noncomputable abbrev progP : Program := entryProgForBody canaryProgParityCall 0

/-- Symbolic `fold(b, n)`: `b ^ (b >> n)` with the `u32` shift amount. -/
noncomputable def foldSym (b : SymScalar) (n : Nat) : SymScalar :=
  .binOp .bitXor b (.shift .shr b (.lit ⟨.i32, false, BitVec.ofNat 128 n⟩))

noncomputable abbrev x0 : SymScalar := .var 0 .i8 false
noncomputable abbrev f1 : SymScalar := foldSym x0 4
noncomputable abbrev f2 : SymScalar := foldSym f1 2
noncomputable abbrev f3 : SymScalar := foldSym f2 1
noncomputable abbrev and3 : SymScalar :=
  .binOp .bitAnd f3 (.lit ⟨.i8, false, BitVec.ofNat 128 1⟩)

/-- The symbolic return value `(fold(fold(fold(b, 4), 2), 1) & 1) == 0`. -/
noncomputable def paritySymOutCall : SymBool :=
  .cmp .eq and3 (.lit ⟨.i8, false, BitVec.ofNat 128 0⟩)

noncomputable abbrev slI (v : SymScalar) : SymSlot :=
  .immediate (some (.scalar v))
noncomputable abbrev slK (n : Nat) : SymSlot :=
  .immediate (some (.conc (.scalar ⟨.i32, false, BitVec.ofNat 128 n⟩)))
noncomputable abbrev slN : SymSlot := .immediate none
noncomputable abbrev slD : SymSlot := .dead

/-- Caller frame of `parity_even_call`. -/
noncomputable abbrev rootF (blk stmt : Nat) (ls : List SymSlot) : SymFrame :=
  { core := { block := blk, stmt := stmt, slots := ls },
    hdr := ⟨0, none, none, none⟩ }

/-- `fold` frame returning into caller local `dst` at block `tgt`. -/
noncomputable abbrev foldF (stmt : Nat) (ls : List SymSlot) (dst tgt : Nat) :
    SymFrame :=
  { core := { block := 0, stmt := stmt, slots := ls },
    hdr := ⟨1, none, some ⟨dst, []⟩, some tgt⟩ }

/-- `fold` locals on entry and after its first seven statements. -/
noncomputable abbrev fold0 (x : SymScalar) (n : Nat) : List SymSlot :=
  [slN, slI x, slK n, slD, slD, slD, slD]
noncomputable abbrev fold7 (x : SymScalar) (n : Nat) : List SymSlot :=
  [slN, slI x, slK n, slI x, slN, slI x, slK n]

noncomputable abbrev st (fs : List SymFrame) : SymProg :=
  { frames := fs, conds := [] }

noncomputable abbrev callerAt1 : List SymSlot :=
  [slN, slI x0, slN, slN, slD, slD, slD, slD, slD, slD]
noncomputable abbrev callerAt2 : List SymSlot :=
  [slN, slI x0, slI f1, slD, slN, slN, slD, slD, slD, slD]
noncomputable abbrev callerAt3 : List SymSlot :=
  [slN, slI x0, slI f1, slD, slI f2, slD, slN, slN, slD, slD]
noncomputable abbrev ret1 : List SymSlot :=
  [slN, slI x0, slI f1, slN, slD, slD, slD, slD, slD, slD]
noncomputable abbrev ret2 : List SymSlot :=
  [slN, slI x0, slI f1, slD, slI f2, slN, slD, slD, slD, slD]
noncomputable abbrev ret3 : List SymSlot :=
  [slN, slI x0, slI f1, slD, slI f2, slD, slI f3, slN, slD, slD]
noncomputable abbrev tail6 : List SymSlot :=
  [slN, slI x0, slI f1, slD, slI f2, slD, slI f3, slD, slI and3, slD]

theorem chunk01 :
    symProgRunSteps progP 4 (symProgEntry 0 canaryBodyParityCall [.scalar x0]) =
      .step (st [foldF 0 (fold0 x0 4) 2 1, rootF 0 3 callerAt1]) := rfl
theorem chunk02 :
    symProgRunSteps progP 7
        (st [foldF 0 (fold0 x0 4) 2 1, rootF 0 3 callerAt1]) =
      .step (st [foldF 7 (fold7 x0 4) 2 1, rootF 0 3 callerAt1]) := rfl
theorem chunk03 :
    symProgRunSteps progP 7
        (st [foldF 7 (fold7 x0 4) 2 1, rootF 0 3 callerAt1]) =
      .step (st [rootF 1 0 ret1]) := rfl
theorem chunk04 :
    symProgRunSteps progP 5 (st [rootF 1 0 ret1]) =
      .step (st [foldF 0 (fold0 f1 2) 4 2, rootF 1 4 callerAt2]) := rfl
theorem chunk05 :
    symProgRunSteps progP 7
        (st [foldF 0 (fold0 f1 2) 4 2, rootF 1 4 callerAt2]) =
      .step (st [foldF 7 (fold7 f1 2) 4 2, rootF 1 4 callerAt2]) := rfl
theorem chunk06 :
    symProgRunSteps progP 7
        (st [foldF 7 (fold7 f1 2) 4 2, rootF 1 4 callerAt2]) =
      .step (st [rootF 2 0 ret2]) := rfl
theorem chunk07 :
    symProgRunSteps progP 5 (st [rootF 2 0 ret2]) =
      .step (st [foldF 0 (fold0 f2 1) 6 3, rootF 2 4 callerAt3]) := rfl
theorem chunk08 :
    symProgRunSteps progP 7
        (st [foldF 0 (fold0 f2 1) 6 3, rootF 2 4 callerAt3]) =
      .step (st [foldF 7 (fold7 f2 1) 6 3, rootF 2 4 callerAt3]) := rfl
theorem chunk09 :
    symProgRunSteps progP 7
        (st [foldF 7 (fold7 f2 1) 6 3, rootF 2 4 callerAt3]) =
      .step (st [rootF 3 0 ret3]) := rfl
theorem chunk10 :
    symProgRunSteps progP 6 (st [rootF 3 0 ret3]) =
      .step (st [rootF 3 6 tail6]) := rfl
theorem chunk11 :
    symProgRunSteps progP 6 (st [rootF 3 6 tail6]) =
      .ret (.bool paritySymOutCall) [] := rfl

/-- Kernel-checked multi-frame canary (`["propext"]` only, default
`maxHeartbeats`): the whole captured `parity_even_call` run, including three
calls to `fold`, returns `paritySymOutCall` with no side conditions. -/
theorem symExec_parityCall_canary :
    symProgRunSteps progP
        (4 + (7 + (7 + (5 + (7 + (7 + (5 + (7 + (7 + (6 + 6))))))))))
        (symProgEntry 0 canaryBodyParityCall [.scalar x0]) =
      .ret (.bool paritySymOutCall) [] :=
  symProgRunSteps_trans chunk01 (symProgRunSteps_trans chunk02
    (symProgRunSteps_trans chunk03 (symProgRunSteps_trans chunk04
    (symProgRunSteps_trans chunk05 (symProgRunSteps_trans chunk06
    (symProgRunSteps_trans chunk07 (symProgRunSteps_trans chunk08
    (symProgRunSteps_trans chunk09 (symProgRunSteps_trans chunk10
      chunk11)))))))))

/-- Whether `paritySymOutCall` meets `parityEvenSpec` at the input `n`. -/
noncomputable def parityCallCheck (n : Nat) : Bool :=
  decide (paritySymOutCall.eval (parityEnv n) = parityEvenSpec n)

-- Four checks of 64 inputs each, as for `parityCheck`.
theorem parityCallCheck_0 : natAllFrom 0 64 parityCallCheck = true := rfl
theorem parityCallCheck_64 : natAllFrom 64 64 parityCallCheck = true := rfl
theorem parityCallCheck_128 : natAllFrom 128 64 parityCallCheck = true := rfl
theorem parityCallCheck_192 : natAllFrom 192 64 parityCallCheck = true := rfl

theorem paritySymOutCall_eval {n : Nat} (hn : n < 256) :
    paritySymOutCall.eval (parityEnv n) = parityEvenSpec n := by
  have hChk : parityCallCheck n = true := by
    cases Nat.lt_or_ge n 128 with
    | inl h128 =>
      cases Nat.lt_or_ge n 64 with
      | inl h64 => exact natAllFrom_sound parityCallCheck_0 (Nat.zero_le n) h64
      | inr h64 => exact natAllFrom_sound parityCallCheck_64 h64 h128
    | inr h128 =>
      cases Nat.lt_or_ge n 192 with
      | inl h192 => exact natAllFrom_sound parityCallCheck_128 h128 h192
      | inr h192 => exact natAllFrom_sound parityCallCheck_192 h192 hn
  exact of_decide_eq_true hChk

/-- End-to-end functional correctness of the captured `parity_even_call`
(`["propext"]` only): for every `b : u8`, the two-body program returns `true`
exactly when `b` has an even number of set bits. -/
theorem parityEvenCall_behavior (b : BitVec 8) :
    Trusted.MirSemantics.Behavior progP
      { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩] }
      (.returned ⟨.bool (parityEvenSpec b.toNat), ⟨[]⟩⟩) := by
  have hLt : b.toNat < 256 := b.isLt
  have hTrunc :
      truncateBitsComp .i8 (BitVec.ofNat 128 b.toNat) =
        BitVec.ofNat 128 b.toNat :=
    truncateBitsComp_bitVec_of_lt b (by decide)
  have hArgs :
      ([.scalar x0] : List SymVal).map (SymVal.eval (parityEnv b.toNat)) =
        [.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩] := by
    dsimp only [List.map, SymVal.eval, SymScalar.eval, parityEnv]
    rw [hTrunc]
  have hValid :
      ValidEntryArgs canaryBodyParityCall
        (([.scalar x0] : List SymVal).map
          (SymVal.eval (parityEnv b.toNat))) := by
    rw [hArgs]
    have hBits :
        (BitVec.ofNat 128 b.toNat).toNat < intWidthModulus .i8 := by
      rw [Anneal.PureLift.BvLin.bv_toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hLt
    exact checkArgsMatch_cons_iff.mpr
      ⟨_, [], rfl, checkVal_scalar_of_toNat_lt hBits, rfl⟩
  have hB := symProgRunSteps_entry_behavior (p := canaryProgParityCall)
    (defId := 0) rfl rfl (parityEnv b.toNat) hValid symExec_parityCall_canary
    rfl
  rw [hArgs] at hB
  have hOut : (SymVal.bool paritySymOutCall).eval (parityEnv b.toNat) =
      .bool (parityEvenSpec b.toNat) :=
    congrArg Val.bool (paritySymOutCall_eval hLt)
  rw [hOut] at hB
  exact hB.2.1

/-!
# Single-`rfl` Canary: `add_u32`

`canaryBodyAddU32` is the MIR that `anneal-rustc-capture` emits for

```rust
#![no_std]

pub fn add_u32(a: u64, b: u32) -> u64 {
    a.wrapping_add(b as u64)
}
```

(edition 2021, `panic = "abort"`), transcribed with the same statements in the
same order. The run takes 13 steps across one `u64::wrapping_add` sysroot call.
Checking it with one `rfl` under the default `maxHeartbeats` relies on
`symProgRunSteps` forcing each intermediate state (`forceSymProg`).
-/

/-- Body `0`: `add_u32`. -/
noncomputable def canaryBodyAddU32 : Body :=
  { identity := "rust-path-v1::add_u32"
    isUnsafe := false
    argumentCount := 2
    locals := [.int .i64 false, .int .i64 false, .int .i32 false,
               .int .i64 false, .int .i64 false, .int .i32 false]
    basicBlocks :=
      [ { statements :=
            [ .storageLive 3,
              .assign { localId := 3, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .storageLive 4,
              .storageLive 5,
              .assign { localId := 5, projection := [] }
                (.use (.copy { localId := 2, projection := [] })),
              .assign { localId := 4, projection := [] }
                (.cast .intToInt (.move { localId := 5, projection := [] })
                  (.int .i64 false)),
              .storageDead 5 ]
          terminator := .sysrootCall ⟨.wrappingAdd, .i64, false⟩
            [ .move { localId := 3, projection := [] },
              .move { localId := 4, projection := [] } ]
            { localId := 0, projection := [] } (some 1) .unreachable
          cleanup := false },
        { statements := [.storageDead 4, .storageDead 3]
          terminator := .return_
          cleanup := false } ] }

/-- The captured one-body program. -/
noncomputable def canaryProgAddU32 : Program :=
  { pointerWidthBits := 64
    mirProfileVersion := 1
    scope := .crate
    entryDefId := 0
    bodies := [canaryBodyAddU32]
    overflowChecks := false
    panicStrategy := .abort
    hasLocalPanicHandler := false }

noncomputable abbrev addA : SymScalar := .var 0 .i64 false
noncomputable abbrev addB : SymScalar := .var 1 .i32 false

/-- Kernel-checked single-`rfl` canary (default `maxHeartbeats`): the whole
13-step run of `add_u32`, including its sysroot call, returns
`a + (b as u64)` with no side conditions. -/
theorem symExec_addU32_canary :
    symProgRunSteps (entryProgForBody canaryProgAddU32 0) 13
        (symProgEntry 0 canaryBodyAddU32 [.scalar addA, .scalar addB]) =
      .ret (.scalar (.binOp .add addA (.cast .i64 false addB))) [] := rfl

end Anneal.MirSymExecCall.Canaries

end
