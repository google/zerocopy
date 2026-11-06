-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Lean 4.34.1 `prelude`-Only String/UTF-8, `BEq`, and Recursor Probes

Self-contained `prelude` + `import Init.NotationExtra` verification probe for
Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), covering:

1. `String.ofByteArray` 2-field constructor unpacking vs. `String.toUTF8`
   opacity (`stringToBytes`).
2. `String.ofList` / `List.toByteArray.loop` `maxRecDepth` scaling via
   `congrArg String.ofList rfl` (`encodeRv64ElfHex` and chunked hex streams).
3. Opaque `Nat` `BEq` (`==`) rewriting via `nat_beq_self` and
   `nat_eq_of_beq_eq_true` (`updateLocal_self`, `updateLocal_comm`,
   `evalStmt_storageDead_of_uninit`).
4. LCNF-compatible structural folds (`List.foldr`, `List.foldl`, `@Nat.rec`)
   and recursive `theorem` declarations that emit zero `._unsafe_rec`
   declarations (`evalPlaceOffset`, `applyRelocsToCode`).
5. Spine-strict `Option` accumulators and compositional per-block `List.foldr`
   pipelines (`checkBlockPipeline_cons`).
6. `anneal-audit` preflight-compliant syntax (`secKind`, manual `BEq`,
   `.of_beq_eq_true`, `Prop` `ite` on `a <= b`, and `Nat.xor`).
-/

namespace PreludeTrapsProbe

/-!
## 1. `String.ofByteArray` 2-Field Constructor Unpacking (`stringToBytes`)

In `Init/Prelude.lean:3542-3550`, `String` is a 2-field structure:
```lean
structure String where
  ofByteArray ::
  toByteArray : ByteArray
  isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
```
Unpacking both fields `⟨bytes, _⟩` (or projecting `s.toByteArray.data.toList`)
reduces string literals to `List UInt8` in the kernel via
`string_lit_to_constructor` (`src/kernel/expr.cpp:427-446`) without referencing
`String.toUTF8` (`Init/Data/String/Defs.lean:75-77`).
-/

def stringToBytes (s : String) : List UInt8 :=
  match s with
  | ⟨bytes, _⟩ => bytes.data.toList

def stringToBytesProj (s : String) : List UInt8 :=
  s.toByteArray.data.toList

theorem stringToBytes_hi :
    stringToBytes "Hi\n" = [72, 105, 10] := rfl

theorem stringToBytesProj_hi :
    stringToBytesProj "Hi\n" = [72, 105, 10] := rfl

theorem stringToBytes_eq_proj (s : String) :
    stringToBytes s = stringToBytesProj s := by
  cases s
  rfl

/-!
## 2. `String.ofList` Scaling via `congrArg String.ofList rfl`

Proving `String.ofList cs = "..."` with syntactic `:= rfl` triggers
`inferDefEqAttr` (`Lean/DefEqAttrib.lean:33-35, 121-188`), which disables
`smartUnfolding` and expands `List.toByteArray.loop` into nested `List.brecOn` /
`List.rec` terms that exhaust `maxRecDepth = 512` at `N = 64..82` characters.
Using `exact congrArg String.ofList rfl` bypasses `isRflProofCore` and unifies
the `List Char` arguments directly before checking the terminal string literal
(up to `N = 125` characters for raw string literals, or `N = 1,042+` characters
when both sides are structured as `String.ofList`).
-/

def rv64HexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0  => '0' | 1  => '1' | 2  => '2' | 3  => '3'
  | 4  => '4' | 5  => '5' | 6  => '6' | 7  => '7'
  | 8  => '8' | 9  => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _  => 'f'

def bytesToHexChars (bs : List Nat) : List Char :=
  bs.foldr
    (fun b acc => rv64HexDigit (b / 16) :: rv64HexDigit (b % 16) :: acc)
    []

def encodeRv64ElfHex (bytes : List Nat) : String :=
  String.ofList
    ('e' :: 'l' :: 'f' :: '6' :: '4' :: '-' :: 'r' :: 'i' :: 's' :: 'c' ::
     'v' :: '-' :: 'o' :: ':' :: bytesToHexChars bytes)

/-- 118-character (`14 + 2 * 52`) ELF64 hex string equality proved under default
    `maxRecDepth = 512` via `congrArg String.ofList rfl` (where `:= rfl` fails
    with `maximum recursion depth has been reached`). -/
theorem encodeRv64ElfHex_118_chars :
    encodeRv64ElfHex (List.replicate 52 0x93) =
      "elf64-riscv-o:93939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393939393" :=
  congrArg String.ofList rfl

/-- 1,042-character (`2 * 521` bytes across 21 chunks of 25 bytes + 1 chunk of 1
    byte, keeping each `foldr` spine well below `maxRecDepth = 512`) ELF64 hex
    string equality proved under default `maxRecDepth = 512` via
    `congrArg String.ofList rfl`. -/
def encodeChunkedHex (chunks : List (List Nat)) : String :=
  String.ofList (chunks.foldr (fun c acc => bytesToHexChars c ++ acc) [])

def expectedChunkedHexChars (chunks : List (List Char)) : String :=
  String.ofList (chunks.foldr (fun c acc => c ++ acc) [])

theorem encodeChunkedHex_1042_chars :
    encodeChunkedHex
      (List.replicate 20 (List.replicate 25 0x99) ++ [List.replicate 21 0x99]) =
    expectedChunkedHexChars
      (List.replicate 20 (List.replicate 50 '9') ++ [List.replicate 42 '9']) :=
  congrArg String.ofList rfl

theorem encodeChunkedHex_2048_chars :
    encodeChunkedHex
      (List.replicate 32 (List.replicate 32 0x99)) =
    expectedChunkedHexChars
      (List.replicate 32 (List.replicate 64 '9')) :=
  congrArg String.ofList rfl

/-!
## 3. Opaque `Nat` `BEq` (`==`) Rewriting vs. `dsimp` Partial Unfolding

In `prelude` + `import Init.NotationExtra`, `(a == b)` on `Nat` resolves to
`instBEqOfDecidableEq` (`decide (a = b)` in `Init/Prelude.lean:1069-1070`).
Keeping `(· == ·)` opaque and rewriting with `nat_beq_self`,
`nat_eq_of_beq_eq_true`, and `nat_beq_comm` preserves syntactic identity
between the proposition `(k == idx) = true` and `@ite`'s hidden `[Decidable]`
instance argument `instDecidableEqBool (k == idx) true`.
-/

theorem nat_beq_self (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

theorem nat_eq_of_beq_eq_true {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

theorem nat_beq_eq_true_of_eq {a b : Nat} (h : a = b) : (a == b) = true := by
  subst h
  exact nat_beq_self _

theorem nat_beq_comm (a b : Nat) : (a == b) = (b == a) := by
  cases h1 : (a == b)
  · cases h2 : (b == a)
    · rfl
    · have hab : b = a := nat_eq_of_beq_eq_true h2
      subst hab
      rw [nat_beq_self _] at h1
      contradiction
  · have hab : a = b := nat_eq_of_beq_eq_true h1
    subst hab
    exact (nat_beq_self _).symm

abbrev LocalEnv := Nat → Option Nat

def updateLocal (locals : LocalEnv) (idx : Nat) (val : Option Nat) : LocalEnv :=
  fun k => if (k == idx) = true then val else locals k

theorem updateLocal_self (locals : LocalEnv) (idx : Nat) (val : Option Nat) :
    updateLocal locals idx val idx = val := by
  dsimp [updateLocal]
  rw [nat_beq_self idx]
  rfl

theorem updateLocal_other (locals : LocalEnv) (idx k : Nat) (val : Option Nat)
    (h : (k == idx) = false) :
    updateLocal locals idx val k = locals k := by
  dsimp [updateLocal]
  rw [h]
  rfl

theorem updateLocal_comm (locals : LocalEnv) (i j : Nat) (vi vj : Option Nat)
    (hij : (i == j) = false) :
    updateLocal (updateLocal locals i vi) j vj =
      updateLocal (updateLocal locals j vj) i vi := by
  funext k
  dsimp [updateLocal]
  cases hkj : (k == j)
  · cases hki : (k == i)
    · rfl
    · rfl
  · have h_eq : k = j := nat_eq_of_beq_eq_true hkj
    subst h_eq
    have hji : (k == i) = false := by
      rw [nat_beq_comm k i]
      exact hij
    rw [hji]
    rfl

theorem evalStmt_storageDead_of_uninit (locals : LocalEnv) (idx : Nat)
    (h_uninit : locals idx = none) :
    updateLocal locals idx none = locals := by
  funext k
  dsimp [updateLocal]
  cases h : (k == idx)
  · rfl
  · have h_eq : k = idx := nat_eq_of_beq_eq_true h
    subst h_eq
    exact h_uninit.symm

/-!
## 4. LCNF Recursor Support (`@Nat.rec` / `List.foldr`) & Zero `._unsafe_rec`

Non-`Prop` computational definitions that invoke `List.foldr`, `List.foldl`, or
`@Nat.rec` (which rewrites via `@[csimp] theorem Nat.rec_eq_recCompiled` in
`Init/Data/Nat/Basic.lean:28-29`), together with recursive `theorem`
declarations (where `shouldGenCodeFor` is `false`), emit zero `._unsafe_rec`
declarations in `env.checked`.
-/

inductive ProjectionElem where
  | field (fieldIdx offset : Nat)
  | index (localIdx stride : Nat)

/-- Evaluates a place projection list via `List.foldl` without emitting
    `evalPlaceOffset._unsafe_rec`. -/
def evalPlaceOffset (locals : LocalEnv) (projs : List ProjectionElem) :
    Option Nat :=
  projs.foldl
    (fun acc p =>
      match acc with
      | none => none
      | some base =>
        match p with
        | .field _ off => some (base + off)
        | .index l stride =>
          match locals l with
          | some idx => some (base + idx * stride)
          | none => none)
    (some 0)

/-- Updates list element at index `idx` via `List.foldr` without emitting
    `updateCodeAt._unsafe_rec`. -/
def updateCodeAt (code : List Nat) (idx : Nat) (val : Nat) : List Nat :=
  (code.foldr
    (fun w (acc : List Nat → Nat → List Nat) =>
      fun rem i =>
        match rem with
        | [] => []
        | x :: xs =>
          let _ := w
          if i == idx then val :: xs else x :: acc xs (i + 1))
    (fun _ _ => []))
    code 0

/-- Applies relocations via `List.foldl` without emitting
    `applyRelocsToCode._unsafe_rec`. -/
def applyRelocsToCode (code : List Nat) (relocs : List (Nat × Nat)) :
    List Nat :=
  relocs.foldl (fun acc r => updateCodeAt acc r.1 r.2) code

/-- Bounded fuel stepper defined via `@Nat.rec` (compiled via
    `Nat.rec_eq_recCompiled`) with zero `._unsafe_rec` auxiliary constants. -/
def stepBounded (fuel : Nat) (step : Nat → Nat) (init : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat)
    (fun s => s)
    (fun _ ih s => ih (step s))
    fuel init

/-- Recursive `theorem` declarations skip `compileDecls` /
    `addAndCompilePartialRec` (`shouldGenCodeFor = false`), emitting zero
    `._unsafe_rec` constants. -/
theorem list_length_append (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil =>
    change ys.length = 0 + ys.length
    exact (Nat.zero_add ys.length).symm
  | cons x xs ih =>
    change (x :: (xs ++ ys)).length = (x :: xs).length + ys.length
    change (xs ++ ys).length + 1 = (xs.length + 1) + ys.length
    rw [ih]
    exact (Nat.succ_add xs.length ys.length).symm

/-!
## 5. Spine-Strict `Option` Accumulators & Compositional `List.foldr`

Matching `match acc with | none => none | some w => ...` before evaluating the
step guard forces `Option.casesOn` on the `@Nat.rec` accumulator once per
instruction ($O(N)$ WHNF depth, eliminating the $O(2^N)$ `@Nat.rec` duplication
of unforced `ite`), and decomposing multi-block checks via
`checkMultiBlockPipeline_cons` (`List.foldr`) scales to $N = 1,024+$
instructions under default `maxRecDepth = 512`.
-/

def checkSyntheticBlock (n : Nat) : Bool :=
  let res : Option Nat :=
    @Nat.rec (fun _ => Option Nat) (some 0)
      (fun idx acc =>
        match acc with
        | none => none
        | some w => if w == idx then some (w + 1) else none)
      n
  match res with
  | some finalW => finalW == n
  | none => false

def checkSyntheticPipeline (n : Nat) : Bool :=
  checkSyntheticBlock n && checkSyntheticBlock n

theorem bench_stage0_rfl_block64 : checkSyntheticPipeline 64 = true := rfl

theorem bench_stage0_rfl_block128 : checkSyntheticPipeline 128 = true := rfl

def checkMultiBlockPipeline (blocks : List Nat) : Bool :=
  blocks.foldr (fun b acc => checkSyntheticPipeline b && acc) true

theorem checkMultiBlockPipeline_cons {b : Nat} {rest : List Nat}
    (hb : checkSyntheticPipeline b = true)
    (hrest : checkMultiBlockPipeline rest = true) :
    checkMultiBlockPipeline (b :: rest) = true := by
  dsimp [checkMultiBlockPipeline]
  rw [hb]
  exact hrest

theorem bench_stage0_compositional_1024 :
    checkMultiBlockPipeline [128, 128, 128, 128, 128, 128, 128, 128] = true :=
  checkMultiBlockPipeline_cons bench_stage0_rfl_block128
    (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
      (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
        (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
          (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
            (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
              (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
                (checkMultiBlockPipeline_cons bench_stage0_rfl_block128
                  rfl)))))))

/-!
## 6. `anneal-audit` Preflight & `Init.Prelude` Syntax Compliance

1. Structure field named `secKind` (avoiding reserved keyword `section`).
2. Manual `BEq` instance (avoiding rejected `deriving DecidableEq, BEq`).
3. Equality lemma named `.of_beq_eq_true` (avoiding reserved `eq_*` suffix in
   `validateUserDeclIdent`).
4. `if a <= b` using `Prop` `ite` (`Nat.decLe`) with `Decidable.byCases`
   splitting (`if h : a <= b then ... else ...`).
5. `Nat.xor` (`Init/Data/Nat/Bitwise/Basic.lean:38`) instead of `Nat.lxor`.
-/

inductive SectionKind where
  | text
  | rodata
  | data
  | bss

def SectionKind.beq : SectionKind → SectionKind → Bool
  | .text, .text => true
  | .rodata, .rodata => true
  | .data, .data => true
  | .bss, .bss => true
  | _, _ => false

instance : BEq SectionKind where
  beq := SectionKind.beq

theorem SectionKind.of_beq_eq_true {a b : SectionKind}
    (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

structure SymDef where
  name : Nat
  secKind : SectionKind
  offset : Nat

def clampToLimit (a limit : Nat) : Nat :=
  if a <= limit then a else limit

theorem clampToLimit_le (a limit : Nat) :
    clampToLimit a limit <= limit :=
  if h : a <= limit then by
    dsimp [clampToLimit]
    simp [h]
  else by
    dsimp [clampToLimit]
    simp [h, Nat.le_refl]

def xorWord64 (a b : Nat) : Nat :=
  (Nat.xor a b) % 18446744073709551616

theorem xorWord64_example :
    xorWord64 0xff00 0x0ff0 = 0xf0f0 := rfl

end PreludeTrapsProbe
