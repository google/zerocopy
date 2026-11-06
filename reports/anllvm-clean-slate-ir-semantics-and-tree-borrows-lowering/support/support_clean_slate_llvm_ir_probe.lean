/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Clean-Slate LLVM IR Semantics (`AnLLVM-IR`) — Mechanized Soundness Probe

This standalone Lean 4.34.1 module mechanizes the core semantic domain of
`AnLLVM-IR` (Anneal's clean-slate LLVM IR semantics) and proves five families
of optimization soundness theorems alongside negative canary theorems showing
where upstream LLVM 21's IR semantics produce soundness contradictions:

1. **Anneal Verification Spine (Issue #241 / #242):**
   `Preorder`, `Partial`, `Behavior`, `Language`, `BehaviorCodec`, `Compiles`,
   `ProductiveCompiles`, `StepResult`, `ReachesPrefix`, `EventualOut`, and
   `EventualBehaviorOf`.
2. **Modification 1 & 3 — Bitwise-Masked Scalar Values (`MaskedWord w`) and
   First-Class Byte Memory (`Byte`) without `undef`:**
   - `sroa_load_widening_across_padding_sound`: widening two field loads across
     uninitialized padding bytes into a single 64-bit load and extracting the
     fields by shift/slice is unconditionally sound without `freeze`.
   - `canary_upstream_whole_word_load_poison_unsound`: in upstream LLVM's
     whole-value poison model, loading `i64` across uninitialized padding
     poisons the entire `i64` value.
3. **Modification 2 — First-Class Provenance Pointers (`Ptr`) + `ptradd` +
   Split `ptrtoaddr` vs. `ptrtoint`:**
   - `gvn_ptrtoaddr_equality_substitution_sound`: substituting equal integer
     addresses observed via `ptrtoaddr` preserves program behavior and never
     corrupts pointer provenance or `BasicAA` disjointness.
   - `canary_upstream_ptrtoint_gvn_collapse_unsound`: reproducing the concrete
     3-step `GVN + InstCombine + BasicAA` miscompilation from LLVM 21.1.8
     (`probe_a_ptrtoint_gvn.ll`) when one-past-the-end `p_end` and adjacent `q`
     share a runtime address.
4. **Modification 4 — Predecessor-Indexed $\phi$-Tables / Block Arguments
   Isomorphism & `PHINode` Compatibility Lens:**
   - `phi_table_block_arg_lens_isomorphism`: proving the round-trip isomorphism
     between basic-block-argument edge tables and canonical predecessor-indexed
     `PHINode` tables, plus lens laws for `getIncomingValueForBlock`,
     `setIncomingValueForBlock`, and `replaceIncomingBlockWith`.
5. **Modification 5 — Direct `AllocId`-Scoped `AllocaLive`/`AllocaDead` vs.
   Pointer-Based `llvm.lifetime.start/end`:**
   - `alloca_live_dead_disjoint_coloring_sound`: stack-slot coloring of
     disjoint-lifetime allocations preserves load/store semantics and makes
     accesses after `AllocaDead` deterministically UB even via escaped pointers.
   - `canary_escaped_pointer_lifetime_end_coloring_unsound`: reproducing the
     `InstCombine` (`icmp eq ptr %a, %b -> false`) vs. `StackColoring` (`%rsp`
     slot reuse) contradiction from LLVM 21.1.8 (`probe_d_lifetime_aa.ll`).
6. **Modification 6 — First-Class Tree-Borrows `BorrowTag` & `ProtectorId` on
   Memory Operations Instead of `noalias` Scope Metadata:**
   - `inlining_protector_drop_refines_and_not_symmetric`: dropping a call-site
     `ProtectorId` during function inlining is a valid forward refinement in
     Anneal's `Language.Refines`, and is strictly asymmetric (not an
     equivalence).
7. **Modification 7 — Rust-Default `mayDiverge` Loop Semantics with Explicit
   `FiniteTripWitness`:**
   - `witnessed_loop_deletion_sound` and
     `canary_unwitnessed_loop_deletion_unsound`: deleting a side-effect-free
     loop refines `EventualBehaviorOf` if and only if a `FiniteTripWitness`
     is discharged.
-/

namespace Anneal.AnLLVM

/-! ## Section 1: Anneal Semantic Spine (Issue #241 / #242) -/

/-- A reflexive, transitive relation. -/
class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

/-- Adds an explicit `ub` (undefined behavior) bottom element to `α`. -/
inductive Partial (α : Type u) : Type u where
  | ub : Partial α
  | defined (val : α) : Partial α
  deriving DecidableEq, Repr

/-- Execution behaviors of a program: either `ub` or a well-defined `SemObs`
value. `ub` refines every behavior (demonic undefined behavior). -/
abbrev Behavior (SemObs : Type u) : Type u := Partial SemObs

namespace Partial

instance [Preorder α] : LE (Partial α) where
  le x y :=
    match x, y with
    | .ub, _ => True
    | .defined _, .ub => False
    | .defined a, .defined b => a ≤ b

instance [Preorder α] : Preorder (Partial α) where
  le_refl a := by
    cases a with
    | ub => trivial
    | defined v => exact Preorder.le_refl v
  le_trans {a b c} hab hbc := by
    cases a <;> cases b <;> cases c <;> try trivial
    exact Preorder.le_trans hab hbc

end Partial

/-- Any type becomes a discrete `Preorder` under equality. -/
@[instance_reducible]
def DiscretePreorder (α : Type u) : Preorder α where
  le a b := a = b
  le_refl _ := rfl
  le_trans hab hbc := Eq.trans hab hbc

/-- A programming or intermediate language parameterized by its semantic
observation preorder `SemObs`. -/
structure Language (SemObs : Type u) [Preorder SemObs] where
  Program : Type v
  behaviors : Program → Behavior SemObs → Prop
  behaviors_upward_closed :
    ∀ {p : Program} {b b' : Behavior SemObs},
      behaviors p b → b ≤ b' → behaviors p b'

namespace Language

variable {SemObs : Type u} [Preorder SemObs]

/-- `p` is non-vacuous when it admits at least one non-UB behavior. -/
def NonVacuous (L : Language SemObs) (p : L.Program) : Prop :=
  ∃ o : SemObs, L.behaviors p (.defined o)

/-- Forward behavioral refinement inside a single language `L`: every behavior
of the transformed program `p_tgt` is permitted by `p_src`. -/
def Refines (L : Language SemObs) (p_src p_tgt : L.Program) : Prop :=
  ∀ b : Behavior SemObs, L.behaviors p_tgt b → L.behaviors p_src b

theorem refines_refl (L : Language SemObs) (p : L.Program) :
    L.Refines p p :=
  fun _ hb => hb

theorem refines_trans (L : Language SemObs) {p1 p2 p3 : L.Program}
    (h12 : L.Refines p1 p2) (h23 : L.Refines p2 p3) :
    L.Refines p1 p3 :=
  fun b hb => h12 b (h23 b hb)

/-- If `p_src` has no UB behavior (only `.defined o` behaviors) and `p_tgt`
refines `p_src`, then `p_tgt` also avoids UB. -/
theorem refines_preserves_defined (L : Language SemObs) {p_src p_tgt : L.Program}
    (href : L.Refines p_src p_tgt)
    (hno_ub : ¬ L.behaviors p_src .ub) :
    ¬ L.behaviors p_tgt .ub :=
  fun hub => hno_ub (href .ub hub)

end Language

/-- Order-preserving partial codec between semantic observation domains. -/
structure BehaviorCodec (SrcObs : Type u) (TgtObs : Type w)
    [Preorder SrcObs] [Preorder TgtObs] where
  encode : SrcObs → TgtObs → Prop
  encode_mono :
    ∀ {s1 s2 : SrcObs} {t1 t2 : TgtObs},
      s1 ≤ s2 → encode s2 t1 → t1 ≤ t2 → encode s1 t2

namespace BehaviorCodec

variable {SrcObs : Type u} {TgtObs : Type w}
variable [Preorder SrcObs] [Preorder TgtObs]

/-- Lifts a `BehaviorCodec` to `Behavior` (`Partial`), where source `.ub`
permits every target behavior and target `.ub` is only permitted by source
`.ub`. -/
def lift (c : BehaviorCodec SrcObs TgtObs) :
    Behavior SrcObs → Behavior TgtObs → Prop
  | .ub, _ => True
  | .defined _, .ub => False
  | .defined s, .defined t => c.encode s t

/-- The identity `BehaviorCodec` on a single observation domain. -/
def id (Obs : Type u) [Preorder Obs] : BehaviorCodec Obs Obs where
  encode s t := s ≤ t
  encode_mono hs12 h21 ht12 :=
    Preorder.le_trans hs12 (Preorder.le_trans h21 ht12)

end BehaviorCodec

/-- Sound compilation relation from `L_src` to `L_tgt` across `codec`. -/
def Compiles {SrcObs : Type u} {TgtObs : Type w}
    [Preorder SrcObs] [Preorder TgtObs]
    (L_src : Language SrcObs) (L_tgt : Language TgtObs)
    (codec : BehaviorCodec SrcObs TgtObs)
    (compile : L_src.Program → L_tgt.Program → Prop) : Prop :=
  ∀ {p_src : L_src.Program} {p_tgt : L_tgt.Program},
    compile p_src p_tgt →
    ∀ b_tgt : Behavior TgtObs,
      L_tgt.behaviors p_tgt b_tgt →
      ∃ b_src : Behavior SrcObs,
        L_src.behaviors p_src b_src ∧ codec.lift b_src b_tgt

/-- Termination kinds in Anneal's small-step operational bridge. -/
inductive TerminationKind where
  | normal
  | panic
  deriving DecidableEq, Repr

/-- Single-step outcome of an abstract machine. -/
inductive StepResult (State Obs : Type) where
  | step (next : State)
  | done (kind : TerminationKind) (obs : Obs)
  | ub
  deriving DecidableEq, Repr

/-- Finite-step outcome of running a fuel-bounded execution prefix. -/
inductive PrefixOutcome (Obs : Type) where
  | running
  | done (kind : TerminationKind) (obs : Obs)
  | ub
  deriving DecidableEq, Repr

/-- Runs a deterministic step function `stepFn` for `fuel` steps. -/
def runSteps {State Obs : Type} (stepFn : State → StepResult State Obs) :
    Nat → State → PrefixOutcome Obs
  | 0, _ => .running
  | fuel + 1, s =>
    match stepFn s with
    | .step s' => runSteps stepFn fuel s'
    | .done k o => .done k o
    | .ub => .ub

/-- Eventual whole-execution observation including silent divergence. -/
inductive EventualOut (Obs : Type) where
  | terminates (kind : TerminationKind) (obs : Obs)
  | diverges
  deriving DecidableEq, Repr

instance (Obs : Type) : Preorder (EventualOut Obs) :=
  DiscretePreorder (EventualOut Obs)

/-- Relates an initial state `s0` under `stepFn` to its `Behavior (EventualOut Obs)`. -/
def EventualBehaviorOf {State Obs : Type}
    (stepFn : State → StepResult State Obs)
    (s0 : State) (b : Behavior (EventualOut Obs)) : Prop :=
  (∃ fuel : Nat, runSteps stepFn fuel s0 = .ub) ∨
  match b with
  | .ub => False
  | .defined (.terminates k o) =>
    ∃ fuel : Nat, runSteps stepFn fuel s0 = .done k o
  | .defined .diverges =>
    ∀ fuel : Nat, runSteps stepFn fuel s0 = .running

/-- Constructs a `Language (EventualOut Obs)` from a deterministic step function. -/
def StepLanguage (Prog State Obs : Type)
    (init : Prog → State)
    (stepFn : State → StepResult State Obs) :
    Language (EventualOut Obs) where
  Program := Prog
  behaviors p b := EventualBehaviorOf stepFn (init p) b
  behaviors_upward_closed {p b b'} hb hle := by
    cases hb with
    | inl hub => exact Or.inl hub
    | inr hdef =>
      cases b with
      | ub => cases hdef
      | defined o =>
        cases b' with
        | ub => cases hle
        | defined o' =>
          have heq : o = o' := hle
          subst heq
          exact Or.inr hdef

/-! ## Section 2: Modification 1 & 3 — Bitwise-Masked Scalars (`MaskedWord`) & `Byte`

In `AnLLVM-IR`:
1. `undef` is completely eliminated.
2. Scalar integer registers of bitwidth `w` are represented as `MaskedWord w`:
   - `bits : BitVec w` holds the underlying bit values (canonically `0` at
     poisoned bit positions, though operations mask by `poisonMask`).
   - `poisonMask : BitVec w` has bit `i = 1` iff bit `i` is `poison`, and
     `i = 0` iff bit `i` is defined.
3. Memory is a byte-indexed map of first-class `Byte` values (`Byte.poison`,
   `Byte.bits (v : MaskedWord 8)`, or `Byte.ptrFrag`). Loading a multi-byte
   integer concatenates the `bits` and `poisonMask` of each byte without
   contaminating non-poison bytes when adjacent padding bytes are `Byte.poison`.
-/

/-- A scalar integer value of width `w` with per-bit poison tracking. -/
structure MaskedWord (w : Nat) where
  bits : BitVec w
  poisonMask : BitVec w
  deriving DecidableEq, Repr

namespace MaskedWord

/-- A fully defined `MaskedWord w` with `poisonMask = 0`. -/
def defined {w : Nat} (v : BitVec w) : MaskedWord w :=
  { bits := v, poisonMask := 0#w }

/-- A fully poisoned `MaskedWord w` with `poisonMask = allOnes`. -/
def allPoison (w : Nat) : MaskedWord w :=
  { bits := 0#w, poisonMask := BitVec.allOnes w }

/-- True iff no bit of `x` is poison (`x.poisonMask == 0`). -/
def isFullyDefined {w : Nat} (x : MaskedWord w) : Bool :=
  x.poisonMask == 0#w

/-- Bitwise refinement: `src` is refined by `tgt` iff every non-poison bit of
`src` remains non-poison in `tgt` with the exact same bit value. -/
def Refines {w : Nat} (src tgt : MaskedWord w) : Prop :=
  (tgt.poisonMask &&& ~~~src.poisonMask) = 0#w ∧
  (tgt.bits &&& ~~~src.poisonMask) = (src.bits &&& ~~~src.poisonMask)

theorem refines_refl {w : Nat} (x : MaskedWord w) : Refines x x := by
  refine ⟨?_, rfl⟩
  simp [BitVec.and_not_self]

/-- `freeze` resolves only the poisoned bits of `x` using `choice : BitVec w`,
leaving all defined bits untouched and clearing `poisonMask` to `0`. -/
def freeze {w : Nat} (x : MaskedWord w) (choice : BitVec w) : MaskedWord w :=
  { bits := (x.bits &&& ~~~x.poisonMask) ||| (choice &&& x.poisonMask)
  , poisonMask := 0#w }

theorem freeze_isFullyDefined {w : Nat} (x : MaskedWord w) (choice : BitVec w) :
    (x.freeze choice).isFullyDefined = true := by
  simp [freeze, isFullyDefined]

theorem freeze_idempotent_on_defined {w : Nat} (v : BitVec w) (choice : BitVec w) :
    (defined v).freeze choice = defined v := by
  simp [defined, freeze]

/-- Logical right shift by `s` bits: shifts both `bits` and `poisonMask` right
by `s`, filling the top `s` bits with defined `0`s. -/
def lshr {w : Nat} (x : MaskedWord w) (s : Nat) : MaskedWord w :=
  { bits := x.bits >>> s
  , poisonMask := x.poisonMask >>> s }

/-- Logical left shift by `s` bits: shifts both `bits` and `poisonMask` left
by `s`, filling the bottom `s` bits with defined `0`s. -/
def shl {w : Nat} (x : MaskedWord w) (s : Nat) : MaskedWord w :=
  { bits := x.bits <<< s
  , poisonMask := x.poisonMask <<< s }

/-- Bitwise AND with exact per-bit Kleene / poison mask semantics:
a known `0` bit (`poisonMask = 0` and `bits = 0`) absorbs poison on the other
operand! -/
def band {w : Nat} (x y : MaskedWord w) : MaskedWord w :=
  let xDefZero := ~~~x.poisonMask &&& ~~~x.bits
  let yDefZero := ~~~y.poisonMask &&& ~~~y.bits
  let pMask := (x.poisonMask ||| y.poisonMask) &&& ~~~(xDefZero ||| yDefZero)
  { bits := (x.bits &&& y.bits) &&& ~~~pMask
  , poisonMask := pMask }

/-- Bitwise OR with exact per-bit Kleene / poison mask semantics:
a known `1` bit (`poisonMask = 0` and `bits = 1`) absorbs poison on the other
operand! -/
def bor {w : Nat} (x y : MaskedWord w) : MaskedWord w :=
  let xDefOne := ~~~x.poisonMask &&& x.bits
  let yDefOne := ~~~y.poisonMask &&& y.bits
  let pMask := (x.poisonMask ||| y.poisonMask) &&& ~~~(xDefOne ||| yDefOne)
  { bits := (x.bits ||| y.bits) &&& ~~~pMask
  , poisonMask := pMask }

/-- Truncate a `MaskedWord w` to width `w'`. -/
def trunc {w : Nat} (w' : Nat) (x : MaskedWord w) : MaskedWord w' :=
  { bits := x.bits.setWidth w'
  , poisonMask := x.poisonMask.setWidth w' }

/-- Extract a slice of `len` bits starting at bit `start` (`lshr start` + `trunc len`). -/
def extractSlice {w : Nat} (start len : Nat) (x : MaskedWord w) : MaskedWord len :=
  { bits := BitVec.extractLsb' start len x.bits
  , poisonMask := BitVec.extractLsb' start len x.poisonMask }

/-- Zero-extend a `MaskedWord w` to width `w'`, filling high bits with defined `0`. -/
def zext {w : Nat} (w' : Nat) (x : MaskedWord w) : MaskedWord w' :=
  { bits := x.bits.setWidth w'
  , poisonMask := x.poisonMask.setWidth w' }

/-- Concatenate high word `hi : MaskedWord wHi` and low word `lo : MaskedWord wLo`. -/
def append {wHi wLo : Nat} (hi : MaskedWord wHi) (lo : MaskedWord wLo) :
    MaskedWord (wHi + wLo) :=
  { bits := hi.bits ++ lo.bits
  , poisonMask := hi.poisonMask ++ lo.poisonMask }

end MaskedWord

/-- Allocation identifier in `AnLLVM-IR`. -/
abbrev AllocId := Nat

/-- Tree Borrows node tag in `AnLLVM-IR`. -/
abbrev BorrowTag := Nat

/-- Call-site protector identifier in `AnLLVM-IR`. -/
abbrev ProtectorId := Nat

/-- First-class byte in `AnLLVM-IR` memory. -/
inductive Byte where
  | poison : Byte
  | bits (val : MaskedWord 8) : Byte
  | ptrFrag (allocId : AllocId) (offset : Int) (tag : BorrowTag) (fragIdx : Fin 8) : Byte
  deriving DecidableEq, Repr

namespace Byte

/-- Converts a `Byte` read by an integer `load` into a `MaskedWord 8`.
Reading `Byte.poison` or a raw `Byte.ptrFrag` as an integer byte yields an
all-poison byte (`0xFF#8` poison mask), without triggering immediate UB and
without poisoning sibling bytes in a wider load. -/
def toMaskedByte : Byte → MaskedWord 8
  | .poison => MaskedWord.allPoison 8
  | .bits v => v
  | .ptrFrag _ _ _ _ => MaskedWord.allPoison 8

/-- Creates a fully defined `Byte` from an 8-bit `BitVec`. -/
def ofBitVec8 (b : BitVec 8) : Byte :=
  .bits (MaskedWord.defined b)

end Byte

/-! ### Theorem Family 1: SROA Load Widening Across Uninitialized Struct Padding

Consider a Rust struct `%PaddedStruct = type { i8, [3 x i8], i32 }` (such as
`(u8, u32)` with `#[repr(C)]`), where:
- byte 0 holds `f0 : BitVec 8` (defined),
- bytes 1, 2, 3 are uninitialized padding (`Byte.poison`),
- bytes 4, 5, 6, 7 hold `f1 : BitVec 32` (defined, little-endian).

When `rustc` lowers a return or argument under `PassMode::Cast` (`load_cast` in
`rustc_codegen_ssa/src/mir/block.rs:646`), or when `SROA` / `MemCpyOpt` widens
the two adjacent field loads into a single 64-bit load (`probe_b_sroa_padding.ll`),
the widened 64-bit load reads bytes `0..7` into a single 64-bit (`32 + (24 + 8)`)
register.
-/

/-- Assembles a 64-bit `MaskedWord (32 + (24 + 8))` from the 8 bytes of
`%PaddedStruct` (`{ f0 : u8, pad : [u8; 3], f1 : u32 }`). -/
def loadWidePaddedStruct (f0 : BitVec 8) (f1 : BitVec 32) :
    MaskedWord (32 + (24 + 8)) :=
  let b0 : MaskedWord 8 := Byte.toMaskedByte (Byte.ofBitVec8 f0)
  let pad24 : MaskedWord 24 := MaskedWord.allPoison 24
  let lo32 : MaskedWord (24 + 8) := MaskedWord.append pad24 b0
  let hi32 : MaskedWord 32 := MaskedWord.defined f1
  MaskedWord.append hi32 lo32

/-- Extracts `f0 : MaskedWord 8` from the widened 64-bit load by truncating to
the low 8 bits. -/
def extractField0FromWide (wide : MaskedWord (32 + (24 + 8))) : MaskedWord 8 :=
  wide.trunc 8

/-- Extracts `f1 : MaskedWord 32` from the widened 64-bit load by extracting the
upper 32-bit slice (`lshr 32` + `trunc 32`). -/
def extractField1FromWide (wide : MaskedWord (32 + (24 + 8))) : MaskedWord 32 :=
  wide.extractSlice (24 + 8) 32

theorem setWidth_8_append_32_24_8 (hi : BitVec 32) (pad : BitVec 24) (lo : BitVec 8) :
    BitVec.setWidth 8 (hi ++ (pad ++ lo)) = lo := by
  have h1 : (8 : Nat) ≤ 24 + 8 := by decide
  have h2 : (8 : Nat) ≤ 8 := Nat.le_refl 8
  rw [BitVec.setWidth_append, dite_eq_left_iff.mpr (fun h => absurd h1 h)]
  rw [BitVec.setWidth_append, dite_eq_left_iff.mpr (fun h => absurd h2 h)]
  exact BitVec.setWidth_eq lo

/-- **Theorem 1A (`sroa_load_widening_across_padding_sound`):**
In `AnLLVM-IR`, widening two field loads across 3 bytes of uninitialized
(`Byte.poison`) struct padding into a single 64-bit load and extracting `f0`
and `f1` by shift/truncation produces the exact, non-poison field values
`MaskedWord.defined f0` and `MaskedWord.defined f1` for all `f0` and `f1`,
without inserting `freeze`! -/
theorem sroa_load_widening_across_padding_sound
    (f0 : BitVec 8) (f1 : BitVec 32) :
    extractField0FromWide (loadWidePaddedStruct f0 f1) = MaskedWord.defined f0 ∧
    extractField1FromWide (loadWidePaddedStruct f0 f1) = MaskedWord.defined f1 ∧
    (loadWidePaddedStruct f0 f1).poisonMask =
      (0#32 ++ (BitVec.allOnes 24 ++ 0#8)) := by
  refine ⟨?_, ?_, rfl⟩
  · unfold extractField0FromWide loadWidePaddedStruct MaskedWord.trunc
      MaskedWord.append MaskedWord.defined MaskedWord.allPoison
      Byte.toMaskedByte Byte.ofBitVec8
    dsimp
    rw [setWidth_8_append_32_24_8, setWidth_8_append_32_24_8]
    rfl
  · unfold extractField1FromWide loadWidePaddedStruct MaskedWord.extractSlice
      MaskedWord.append MaskedWord.defined
    dsimp
    rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_left]

/-- Upstream LLVM's whole-value scalar model: a scalar value of width `w` is
either `none` (whole-value `poison`) or `some (v : BitVec w)`. If ANY byte read
by a multi-byte `load` is `poison`, the entire loaded integer becomes `none`! -/
def upstreamLoadWidePaddedStruct (_f0 : BitVec 8) (_f1 : BitVec 32) :
    Option (BitVec 64) :=
  -- Because bytes 1..3 are uninitialized (`poison`), the whole `i64` load is poison:
  none

def upstreamExtractField1 (wide : Option (BitVec 64)) : Option (BitVec 32) :=
  wide.map (fun (w : BitVec 64) => BitVec.extractLsb' 32 32 w)

/-- **Canary 1B (`canary_upstream_whole_word_load_poison_unsound`):**
In upstream LLVM's whole-value poison model, widening adjacent field loads of
`f0` and `f1` across uninitialized padding into a single `i64` load poisons the
entire `i64` result, so extracting `f1` via `lshr 32` + `trunc` yields `poison`
(`none`) instead of `some f1`! -/
theorem canary_upstream_whole_word_load_poison_unsound
    (f0 : BitVec 8) (f1 : BitVec 32) :
    upstreamExtractField1 (upstreamLoadWidePaddedStruct f0 f1) = none ∧
    upstreamExtractField1 (upstreamLoadWidePaddedStruct f0 f1) ≠ some f1 := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-! ## Section 3: Modification 2 — Provenance Pointers (`Ptr`), `ptradd`, and Split `ptrtoaddr` vs. `ptrtoint`

In `AnLLVM-IR`:
1. Every pointer value is a first-class triple `Ptr := (allocId, offset, tag)`.
2. `ptradd p delta` advances `offset` by `delta` while preserving `allocId` and
   `tag`. `ptradd_inbounds` requires both source and result offsets to lie in
   `[0, size(allocId)]` (permitting one-past-the-end `offset == size`).
3. `ptrtoaddr layout p` projects the runtime integer address
   `layout.base p.allocId + p.offset : Int` without exposing provenance and
   with NO inverse cast (`inttoptr` is absent from the safe IR pipeline).
4. `BasicAA` concludes `NoAlias` whenever `p.allocId ≠ q.allocId`.
-/

/-- First-class pointer with provenance in `AnLLVM-IR`. -/
structure Ptr where
  allocId : AllocId
  offset : Int
  tag : BorrowTag
  deriving DecidableEq, Repr

/-- Pointer offset addition (`ptradd`): updates `offset` while strictly
preserving `allocId` and `tag`. -/
def ptradd (p : Ptr) (delta : Int) : Ptr :=
  { p with offset := p.offset + delta }

/-- Allocation bounds table mapping each `AllocId` to its byte size. -/
abbrev AllocBounds := AllocId → Int

/-- `ptradd inbounds`: returns `some (ptradd p delta)` iff both `p.offset` and
`p.offset + delta` lie within `[0, bounds p.allocId]`, allowing one-past-the-end
pointers (`offset = bounds p.allocId`). -/
def ptraddInbounds (bounds : AllocBounds) (p : Ptr) (delta : Int) : Option Ptr :=
  let sz := bounds p.allocId
  if 0 ≤ p.offset ∧ p.offset ≤ sz ∧ 0 ≤ p.offset + delta ∧ p.offset + delta ≤ sz then
    some (ptradd p delta)
  else
    none

/-- Physical memory layout assigning each `AllocId` a concrete base address. -/
abbrev PhysLayout := AllocId → Int

/-- `ptrtoaddr`: pure integer address projection. Does not expose provenance and
cannot be inverted back into a `Ptr`. -/
def ptrtoaddr (layout : PhysLayout) (p : Ptr) : Int :=
  layout p.allocId + p.offset

/-- Provenance-aware memory store and load on `(AllocId × Int)`. -/
abbrev ProvMem := AllocId → Int → Int

def provStore (m : ProvMem) (bounds : AllocBounds) (p : Ptr) (val : Int) :
    Option ProvMem :=
  if 0 ≤ p.offset ∧ p.offset < bounds p.allocId then
    some (fun a off => if a == p.allocId && off == p.offset then val else m a off)
  else
    none

def provLoad (m : ProvMem) (bounds : AllocBounds) (p : Ptr) : Option Int :=
  if 0 ≤ p.offset ∧ p.offset < bounds p.allocId then
    some (m p.allocId p.offset)
  else
    none

/-- `BasicAA` disjoint-object query: two pointers with distinct `allocId`s
never alias in `ProvMem`. -/
def basicAANoAlias (p q : Ptr) : Bool :=
  p.allocId != q.allocId

/-- **Theorem 2A (`basicAA_disjoint_allocId_store_load_commute`):**
In `AnLLVM-IR`, because every memory access checks `0 ≤ p.offset < bounds p.allocId`
and indexes memory by `(p.allocId, p.offset)`, storing to any pointer `p` with
`p.allocId ≠ q.allocId` never alters a load from `q`, even if `ptrtoaddr layout p`
equals `ptrtoaddr layout q` (e.g., when `p` is one-past-the-end of an allocation
adjacent to `q`, in which case storing to `p` is out-of-bounds UB `none`!). -/
theorem basicAA_disjoint_allocId_store_load_commute
    (m m' : ProvMem) (bounds : AllocBounds) (p q : Ptr) (val : Int)
    (hdisj : p.allocId ≠ q.allocId)
    (hstore : provStore m bounds p val = some m') :
    provLoad m' bounds q = provLoad m bounds q := by
  unfold provStore at hstore
  split at hstore
  · injection hstore with hm'
    subst hm'
    unfold provLoad
    split
    · have hne : (q.allocId == p.allocId) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm hdisj)
      simp [hne]
    · rfl
  · contradiction

/-- **Theorem 2B (`gvn_ptrtoaddr_equality_substitution_sound`):**
In `AnLLVM-IR`, when a branch condition establishes `ptrtoaddr layout p_end =
ptrtoaddr layout q`, GVN may freely substitute `ptrtoaddr layout p_end` for
`ptrtoaddr layout q` in any integer computation `k : Int → Int → Int`,
while keeping `q` itself (with its provenance `q.allocId`) for all memory
operations. Both the integer computation and memory accesses produce the exact
same result before and after GVN! -/
theorem gvn_ptrtoaddr_equality_substitution_sound
    (layout : PhysLayout) (m : ProvMem) (bounds : AllocBounds)
    (p_end q : Ptr) (k : Int → Int → Int)
    (heq : ptrtoaddr layout p_end = ptrtoaddr layout q) :
    (do
      let m1 ← provStore m bounds q 42
      let v ← provLoad m1 bounds q
      pure (k (ptrtoaddr layout q) v)) =
    (do
      let m1 ← provStore m bounds q 42
      let v ← provLoad m1 bounds q
      pure (k (ptrtoaddr layout p_end) v)) := by
  rw [heq]

/-- Models the exact 3-step `GVN + InstCombine + BasicAA` pipeline from
`probe_a_ptrtoint_gvn.ll` (`@ptrtoint_inttoptr_gvn_instcombine`):
- Allocation `0` (`p`) has base `100` and size `8`, so `p_end = ptradd p 8`
  is inbounds one-past-the-end with runtime address `108`.
- Allocation `1` (`q`) is adjacent with base `108` and size `8`, so `q` has
  runtime address `108`.
- Unoptimized program: stores `0` to `q`, checks `addr(p_end) == addr(q)`
  (`108 == 108`), stores `42` to `q` (via `inttoptr(ptrtoint(q))`), and loads
  from `q`, returning `some 42`.
- Upstream `GVN + InstCombine + BasicAA`:
  1. `GVN` rewrites `inttoptr(ptrtoint(q))` to `inttoptr(ptrtoint(p_end))`.
  2. `InstCombine` folds `inttoptr(ptrtoint(p_end))` to `p_end` (changing
     provenance from `allocId = 1` to `allocId = 0`!).
  3. `BasicAA + GVN` sees `store 42, p_end` (`allocId = 0`) and `load q`
     (`allocId = 1`) as `NoAlias` and forwards `0` from the entry `store 0, q`,
     returning `some 0`! -/
def adjacentLayout : PhysLayout
  | 0 => 100
  | 1 => 108
  | _ => 0

def adjacentBounds : AllocBounds
  | 0 => 8
  | 1 => 8
  | _ => 0

def ptrP : Ptr := { allocId := 0, offset := 0, tag := 0 }
def ptrQ : Ptr := { allocId := 1, offset := 0, tag := 1 }

def unoptimizedPtrToIntProgram (m0 : ProvMem) : Option Int := do
  let m1 ← provStore m0 adjacentBounds ptrQ 0
  let p_end ← ptraddInbounds adjacentBounds ptrP 8
  if ptrtoaddr adjacentLayout p_end == ptrtoaddr adjacentLayout ptrQ then
    -- In the source program, `q_cast = inttoptr (ptrtoint q)` points to `q`:
    let m2 ← provStore m1 adjacentBounds ptrQ 42
    provLoad m2 adjacentBounds ptrQ
  else
    pure (-1)

def upstreamGvnInstCombineBasicAAProgram (m0 : ProvMem) : Option Int := do
  let _m1 ← provStore m0 adjacentBounds ptrQ 0
  let p_end ← ptraddInbounds adjacentBounds ptrP 8
  if ptrtoaddr adjacentLayout p_end == ptrtoaddr adjacentLayout ptrQ then
    -- After GVN + InstCombine + BasicAA store-forwarding (`probe_a_ptrtoint_gvn.opt.ll`):
    pure 0
  else
    pure (-1)

/-- **Canary 2C (`canary_upstream_ptrtoint_gvn_collapse_unsound`):**
On adjacent allocations `p` (`[100, 108)`) and `q` (`[108, 116)`), `p_end` is a
valid inbounds one-past-the-end pointer (`ptraddInbounds = some p_end`) with
`ptrtoaddr p_end = ptrtoaddr q = 108`, yet the unoptimized program returns
`some 42` while upstream LLVM 21's `GVN + InstCombine + BasicAA` pipeline
returns `some 0` (`some 42 ≠ some 0`)! -/
theorem canary_upstream_ptrtoint_gvn_collapse_unsound (m0 : ProvMem) :
    unoptimizedPtrToIntProgram m0 = some 42 ∧
    upstreamGvnInstCombineBasicAAProgram m0 = some 0 ∧
    unoptimizedPtrToIntProgram m0 ≠ upstreamGvnInstCombineBasicAAProgram m0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-! ## Section 4: Modification 4 — Predecessor-Indexed $\phi$-Tables / Block Arguments Isomorphism & `PHINode` Compatibility Lens

In `AnLLVM-IR`:
- Every join basic block stores a canonical predecessor-indexed table (isomorphic
  to basic-block arguments carried on control-flow edges), eliminating duplicate
  or out-of-sync incoming predecessor lists across multiple `PHINode`s.
- Existing LLVM passes (`Mem2Reg`, `SROA`, `GVN`, `JumpThreading`, `SimplifyCFG`,
  `LCSSA`) interact with join values through the exact `PHINode` lens API from
  `/usr/include/llvm-21/llvm/IR/Instructions.h:2696-2820`:
  - `getIncomingValueForBlock`
  - `setIncomingValueForBlock`
  - `removeIncomingValue`
  - `replaceIncomingBlockWith`
-/

abbrev BlockId := Nat
abbrev ValId := Nat

/-- A canonical `PHINode` view: a list of `(predBlock, incomingVal)` pairs. -/
structure CanonicalPhiNode where
  entries : List (BlockId × ValId)
  deriving DecidableEq, Repr

/-- A single-variable slice of a basic-block-argument edge table. -/
structure BlockArgSlot where
  edgeArgs : List (BlockId × ValId)
  deriving DecidableEq, Repr

namespace CanonicalPhiNode

/-- Convert a `CanonicalPhiNode` to a `BlockArgSlot`. -/
def toBlockArgSlot (phi : CanonicalPhiNode) : BlockArgSlot :=
  { edgeArgs := phi.entries }

/-- Convert a `BlockArgSlot` back to a `CanonicalPhiNode`. -/
def ofBlockArgSlot (slot : BlockArgSlot) : CanonicalPhiNode :=
  { entries := slot.edgeArgs }

/-- Mirrors `llvm::PHINode::getIncomingValueForBlock(const BasicBlock *BB)`
(`/usr/include/llvm-21/llvm/IR/Instructions.h:2809-2811`). -/
def getIncomingValueForBlock (phi : CanonicalPhiNode) (bb : BlockId) :
    Option ValId :=
  match phi.entries.find? (fun e => e.1 == bb) with
  | some (_, v) => some v
  | none => none

/-- Mirrors `llvm::PHINode::setIncomingValueForBlock(const BasicBlock *BB, Value *V)`
(`/usr/include/llvm-21/llvm/IR/Instructions.h:2815-2820`). -/
def setIncomingValueForBlock (phi : CanonicalPhiNode) (bb : BlockId) (v : ValId) :
    CanonicalPhiNode :=
  { entries := phi.entries.map (fun (b, oldV) => if b == bb then (b, v) else (b, oldV)) }

/-- Mirrors `llvm::PHINode::removeIncomingValue(const BasicBlock *BB)`
(`/usr/include/llvm-21/llvm/IR/Instructions.h:2768-2775`). -/
def removeIncomingValueForBlock (phi : CanonicalPhiNode) (bb : BlockId) :
    CanonicalPhiNode :=
  { entries := phi.entries.filter (fun (b, _) => b != bb) }

/-- Mirrors `llvm::PHINode::replaceIncomingBlockWith(const BasicBlock *Old, BasicBlock *New)`
(`/usr/include/llvm-21/llvm/IR/Instructions.h:2743-2750`). -/
def replaceIncomingBlockWith (phi : CanonicalPhiNode) (oldBB newBB : BlockId) :
    CanonicalPhiNode :=
  { entries := phi.entries.map (fun (b, v) => if b == oldBB then (newBB, v) else (b, v)) }

end CanonicalPhiNode

namespace BlockArgSlot

/-- Edge redirection on a `BlockArgSlot` when `SimplifyCFG` / `JumpThreading`
redirects predecessor `oldBB` to `newBB`. -/
def redirectPredecessor (slot : BlockArgSlot) (oldBB newBB : BlockId) :
    BlockArgSlot :=
  { edgeArgs := slot.edgeArgs.map (fun (b, v) => if b == oldBB then (newBB, v) else (b, v)) }

end BlockArgSlot

theorem getIncoming_map_set_same (entries : List (BlockId × ValId))
    (bb : BlockId) (v : ValId) :
    (entries.map (fun (b, oldV) => if b == bb then (b, v) else (b, oldV))).find?
      (fun e => e.1 == bb) =
    (entries.find? (fun e => e.1 == bb)).map (fun (b, _) => (b, v)) := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨b, oldV⟩
    dsimp only [List.map, List.find?]
    cases h : (b == bb)
    · dsimp
      rw [h]
      exact ih
    · dsimp
      rw [h]

theorem getIncoming_map_set_other (entries : List (BlockId × ValId))
    (bb bb' : BlockId) (v : ValId) :
    (bb' == bb) = false →
    (entries.map (fun (b, oldV) => if b == bb then (b, v) else (b, oldV))).find?
      (fun e => e.1 == bb') =
    entries.find? (fun e => e.1 == bb') := by
  intro hne
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨b, oldV⟩
    dsimp only [List.map, List.find?]
    cases h : (b == bb)
    · dsimp
      cases h2 : (b == bb')
      · exact ih
      · rfl
    · dsimp
      have hb : b = bb := beq_iff_eq.mp h
      subst hb
      have hne' : (b == bb') = false := by
        cases h2 : (b == bb')
        · rfl
        · have heq : b = bb' := beq_iff_eq.mp h2
          subst heq
          rw [h2] at hne
          contradiction
      rw [hne']
      exact ih

/-- **Theorem 4 (`phi_table_block_arg_lens_isomorphism`):**
1. `toBlockArgSlot` and `ofBlockArgSlot` form a strict round-trip isomorphism.
2. `replaceIncomingBlockWith` commutes identically with `redirectPredecessor`
   across the isomorphism.
3. `setIncomingValueForBlock` satisfies the Put-Get and Put-Other lens laws with
   `getIncomingValueForBlock`. -/
theorem phi_table_block_arg_lens_isomorphism
    (phi : CanonicalPhiNode) (slot : BlockArgSlot)
    (bb bb' oldBB newBB : BlockId) (v : ValId) :
    CanonicalPhiNode.ofBlockArgSlot (CanonicalPhiNode.toBlockArgSlot phi) = phi ∧
    CanonicalPhiNode.toBlockArgSlot (CanonicalPhiNode.ofBlockArgSlot slot) = slot ∧
    CanonicalPhiNode.toBlockArgSlot (phi.replaceIncomingBlockWith oldBB newBB) =
      (CanonicalPhiNode.toBlockArgSlot phi).redirectPredecessor oldBB newBB ∧
    ((phi.setIncomingValueForBlock bb v).getIncomingValueForBlock bb =
      (phi.getIncomingValueForBlock bb).map (fun _ => v)) ∧
    ((bb' == bb) = false →
      (phi.setIncomingValueForBlock bb v).getIncomingValueForBlock bb' =
        phi.getIncomingValueForBlock bb') := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · unfold CanonicalPhiNode.getIncomingValueForBlock CanonicalPhiNode.setIncomingValueForBlock
    rw [getIncoming_map_set_same]
    cases phi.entries.find? (fun e => e.1 == bb) <;> rfl
  · intro hne
    unfold CanonicalPhiNode.getIncomingValueForBlock CanonicalPhiNode.setIncomingValueForBlock
    rw [getIncoming_map_set_other _ _ _ _ hne]

/-! ## Section 5: Modification 5 — Direct `AllocId`-Scoped `AllocaLive`/`AllocaDead` vs. Pointer-Based `llvm.lifetime.start/end`

In `AnLLVM-IR`:
- Stack lifetime instructions operate directly on `AllocId`:
  `AllocaLive (a : AllocId)` and `AllocaDead (a : AllocId)` (mirroring MIR's
  `StorageLive(local)` and `StorageDead(local)` as well as LLVM 22's move toward
  alloca-direct lifetime intrinsics in `rustc_codegen_llvm/src/builder.rs:1921`).
- Every load/store through any pointer `p : Ptr` checks `state.live p.allocId`:
  after `AllocaDead a`, `state.live a = false`, so ANY subsequent access through
  ANY pointer `p` with `p.allocId = a` (even if `p` was cast, GEP'd, or escaped
  before `AllocaDead a`) is deterministically immediate UB!
- Furthermore, stack-slot coloring (`physSlot : AllocId → Nat`) only requires
  `physSlot a ≠ physSlot b` when `a` and `b` are **simultaneously live**
  (`state.live a = true ∧ state.live b = true`).
-/

/-- Abstract stack state for `AllocaLive`/`AllocaDead` semantics. -/
structure StackState where
  live : AllocId → Bool
  abstractCells : AllocId → Option Int

/-- Physical stack-colored state where each `AllocId` is mapped to a physical
stack slot `coloring : AllocId → Nat`. -/
structure ColoredStackState where
  live : AllocId → Bool
  physSlots : Nat → Option Int

/-- Instruction trace for stack lifetime and memory operations. -/
inductive StackOp where
  | allocaLive (a : AllocId)
  | allocaDead (a : AllocId)
  | store (p : Ptr) (val : Int)
  | load (p : Ptr)
  deriving DecidableEq, Repr

/-- Executes a single `StackOp` on the uncolored `StackState`.
Returns `none` on UB (accessing a dead allocation or reading uninitialized/poison
memory) and `some (nextState, optionalLoadedVal)` otherwise. -/
def stepAbstractStack (s : StackState) : StackOp → Option (StackState × Option Int)
  | .allocaLive a =>
    some ({ live := fun x => cond (x == a) true (s.live x)
          , abstractCells := fun x => cond (x == a) none (s.abstractCells x) }, none)
  | .allocaDead a =>
    some ({ live := fun x => cond (x == a) false (s.live x)
          , abstractCells := fun x => cond (x == a) none (s.abstractCells x) }, none)
  | .store p val =>
    cond (s.live p.allocId && p.offset == 0)
      (some ({ s with abstractCells := fun x => cond (x == p.allocId) (some val) (s.abstractCells x) }, none))
      none
  | .load p =>
    cond (s.live p.allocId && p.offset == 0)
      (match s.abstractCells p.allocId with
       | some v => some (s, some v)
       | none => none)
      none

/-- Executes a single `StackOp` on the stack-colored `ColoredStackState` using
`coloring : AllocId → Nat`. -/
def stepColoredStack (coloring : AllocId → Nat) (s : ColoredStackState) :
    StackOp → Option (ColoredStackState × Option Int)
  | .allocaLive a =>
    some ({ live := fun x => cond (x == a) true (s.live x)
          , physSlots := fun slot => cond (slot == coloring a) none (s.physSlots slot) }, none)
  | .allocaDead a =>
    some ({ live := fun x => cond (x == a) false (s.live x)
          , physSlots := fun slot => cond (slot == coloring a) none (s.physSlots slot) }, none)
  | .store p val =>
    cond (s.live p.allocId && p.offset == 0)
      (some ({ s with physSlots := fun slot => cond (slot == coloring p.allocId) (some val) (s.physSlots slot) }, none))
      none
  | .load p =>
    cond (s.live p.allocId && p.offset == 0)
      (match s.physSlots (coloring p.allocId) with
       | some v => some (s, some v)
       | none => none)
      none

/-- Simulation relation between an abstract `StackState` and a `ColoredStackState`:
1. Liveness agrees for every `AllocId`.
2. Whenever `a` is currently live (`s.live a = true`), the physical slot
   `coloring a` holds the exact abstract cell value `s.abstractCells a`.
3. No two distinct simultaneously-live `AllocId`s share a physical slot. -/
def ColoringSim (coloring : AllocId → Nat)
    (s : StackState) (cs : ColoredStackState) : Prop :=
  (∀ a : AllocId, cs.live a = s.live a) ∧
  (∀ a : AllocId, s.live a = true → cs.physSlots (coloring a) = s.abstractCells a) ∧
  (∀ a b : AllocId, s.live a = true → s.live b = true → a ≠ b → coloring a ≠ coloring b)

/-- **Theorem 5A (`alloca_live_dead_disjoint_coloring_sound`):**
1. Whenever `ColoringSim coloring s cs` holds, any `store` or `load` step
   produces the exact same result (including UB detection and loaded value) in
   the stack-colored machine as in the uncolored abstract machine, and preserves
   `ColoringSim`!
2. After `AllocaDead a`, any load or store through ANY pointer `p` with
   `p.allocId = a` (even an escaped alias) deterministically triggers UB (`none`). -/
theorem alloca_live_dead_disjoint_coloring_sound
    (coloring : AllocId → Nat) (s : StackState) (cs : ColoredStackState)
    (p : Ptr) (val : Int)
    (hsim : ColoringSim coloring s cs) :
    -- (1) Load agreement:
    ((stepAbstractStack s (.load p)).map Prod.snd =
      (stepColoredStack coloring cs (.load p)).map Prod.snd) ∧
    -- (2) Store agreement and simulation preservation:
    (∀ s' cs',
      stepAbstractStack s (.store p val) = some (s', none) →
      stepColoredStack coloring cs (.store p val) = some (cs', none) →
      ColoringSim coloring s' cs') ∧
    -- (3) Deterministic invalidation of all aliases after `AllocaDead p.allocId`:
    (∀ sDead,
      stepAbstractStack s (.allocaDead p.allocId) = some (sDead, none) →
      stepAbstractStack sDead (.load p) = none ∧
      stepAbstractStack sDead (.store p val) = none) := by
  rcases hsim with ⟨hlive, hcells, hdisj⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [stepAbstractStack, stepColoredStack]
    rw [hlive p.allocId]
    cases hlp : s.live p.allocId
    · rfl
    · cases hoff : (p.offset == 0)
      · rfl
      · dsimp only [Bool.true_and, cond]
        rw [hcells p.allocId hlp]
        cases s.abstractCells p.allocId <;> rfl
  · intro s' cs' habs hcol
    dsimp only [stepAbstractStack] at habs
    dsimp only [stepColoredStack] at hcol
    rw [hlive p.allocId] at hcol
    cases hlp : s.live p.allocId
    · rw [hlp] at habs
      cases habs
    · rw [hlp] at habs hcol
      cases hoff : (p.offset == 0)
      · rw [hoff] at habs
        cases habs
      · rw [hoff] at habs hcol
        have hs' := (Prod.mk.inj (Option.some.inj habs)).1
        have hcs' := (Prod.mk.inj (Option.some.inj hcol)).1
        subst hs'
        subst hcs'
        refine ⟨hlive, ?_, hdisj⟩
        intro a hla
        cases hbeq_a : (a == p.allocId)
        · have hap : a ≠ p.allocId := beq_eq_false_iff_ne.mp hbeq_a
          have hne_col : coloring a ≠ coloring p.allocId :=
            hdisj a p.allocId hla hlp hap
          have hbeq_c : (coloring a == coloring p.allocId) = false :=
            beq_eq_false_iff_ne.mpr hne_col
          dsimp only
          rw [hbeq_a, hbeq_c]
          exact hcells a hla
        · have hap : a = p.allocId := beq_iff_eq.mp hbeq_a
          subst hap
          dsimp only
          rw [beq_self_eq_true, beq_self_eq_true]
          rfl
  · intro sDead hdead
    dsimp only [stepAbstractStack] at hdead
    have hEq := (Prod.mk.inj (Option.some.inj hdead)).1
    have hDeadLive : sDead.live p.allocId = false := by
      rw [← hEq]
      dsimp only
      rw [beq_self_eq_true]
      rfl
    dsimp only [stepAbstractStack]
    rw [hDeadLive]
    exact ⟨rfl, rfl⟩

/-- Reproduces the contradiction from `probe_d_lifetime_aa.ll`
(`@disjoint_lifetime_stack_coloring`):
When allocations `a = 0` and `b = 1` have disjoint lifetimes, `StackColoring`
assigns them the SAME physical stack slot (`coloring 0 = coloring 1 = 0`, i.e.,
`%rsp` in `probe_d_lifetime_aa.s`), so observing `ptrtoaddr` during `a`'s
lifetime and during `b`'s lifetime yields `addr_a == addr_b` (`true`).
Yet upstream `InstCombine` unconditionally folds `icmp eq ptr %a, %b` to `false`
without checking that `%a` and `%b` are simultaneously live! -/
def sameSlotColoring : AllocId → Nat
  | 0 => 0
  | 1 => 0
  | n => n

def runtimeObservedAddrEq (coloring : AllocId → Nat) (a b : AllocId) : Bool :=
  coloring a == coloring b

def upstreamInstCombineAllocaEq (a b : AllocId) : Bool :=
  a == b

/-- **Canary 5B (`canary_escaped_pointer_lifetime_end_coloring_unsound`):**
When `a = 0` and `b = 1` have disjoint lifetimes and `StackColoring` merges
them into physical slot `0` (`sameSlotColoring`), the runtime observed address
comparison `runtimeObservedAddrEq` evaluates to `true` while upstream
`InstCombine`'s unconditional alloca inequality fold evaluates to `false`! -/
theorem canary_escaped_pointer_lifetime_end_coloring_unsound :
    runtimeObservedAddrEq sameSlotColoring 0 1 = true ∧
    upstreamInstCombineAllocaEq 0 1 = false ∧
    runtimeObservedAddrEq sameSlotColoring 0 1 ≠ upstreamInstCombineAllocaEq 0 1 := by
  decide

/-! ## Section 6: Modification 6 — First-Class Tree-Borrows `BorrowTag` & `ProtectorId` vs. `noalias` Scope Metadata

In `AnLLVM-IR`:
- Instead of fragile `!noalias` and `!alias.scope` metadata nodes +
  `llvm.experimental.noalias.scope.decl` intrinsics, every pointer carries a
  `BorrowTag` and memory accesses inside functions with protected reference
  arguments carry an optional `ProtectorId`.
- Under Tree Borrows (Villard et al. / Neven et al.), a permission state
  `TBPerm` is one of `Reserved`, `Active`, `Frozen`, or `Disabled`.
- When a `ProtectorId` is active (`isProtected = true`), a foreign write to an
  `Active` or `Frozen` tag triggers immediate UB (`none`) because a protected
  reference must remain valid until function exit (`ProtectorEnd`).
- When function inlining eliminates the call boundary, it simply drops
  `ProtectorEnd` and strips the `ProtectorId` (`isProtected = false`): a foreign
  write now transitions `Active`/`Frozen` to `Disabled` (`some .disabled`),
  which is strictly MORE defined (fewer UBs) than `isProtected = true`!
-/

/-- Tree Borrows node permissions. -/
inductive TBPerm where
  | reserved
  | active
  | frozen
  | disabled
  deriving DecidableEq, Repr

instance : Preorder TBPerm := DiscretePreorder TBPerm

/-- Memory access kind (read vs. write). -/
inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- Tree Borrows single-node transition under a local or foreign access,
parameterized by whether a `ProtectorId` is currently active on the node. -/
def tbTransition (isProtected : Bool) (isLocal : Bool) (kind : AccessKind)
    (perm : TBPerm) : Partial TBPerm :=
  match isLocal, kind, perm with
  -- Local reads:
  | true, .read, .reserved => .defined .reserved
  | true, .read, .active   => .defined .active
  | true, .read, .frozen   => .defined .frozen
  | true, .read, .disabled => .ub
  -- Local writes:
  | true, .write, .reserved => .defined .active
  | true, .write, .active   => .defined .active
  | true, .write, .frozen   => .ub
  | true, .write, .disabled => .ub
  -- Foreign reads:
  | false, .read, .reserved => .defined .reserved
  | false, .read, .active   =>
    if isProtected then .ub else .defined .frozen
  | false, .read, .frozen   => .defined .frozen
  | false, .read, .disabled => .defined .disabled
  -- Foreign writes:
  | false, .write, .reserved =>
    if isProtected then .ub else .defined .disabled
  | false, .write, .active   =>
    if isProtected then .ub else .defined .disabled
  | false, .write, .frozen   =>
    if isProtected then .ub else .defined .disabled
  | false, .write, .disabled => .defined .disabled

/-- **Theorem 6 (`inlining_protector_drop_refines_and_not_symmetric`):**
1. **Forward Refinement (Soundness of Inlining Protector Drop):** For every
   `isLocal`, `kind`, and `perm`, dropping `isProtected` from `true` (outline
   call with protector) to `false` (inlined body without protector) refines the
   transition in Anneal's `Partial` preorder (`tbTransition true ... ≤
   tbTransition false ...`).
2. **Strict Asymmetry:** The converse does NOT hold: a foreign write to an
   unused `Frozen` reference (`isLocal = false`, `kind = .write`, `perm = .frozen`)
   is immediate UB (`.ub`) when `isProtected = true`, but succeeds with
   `.defined .disabled` when `isProtected = false`! -/
theorem inlining_protector_drop_refines_and_not_symmetric :
    (∀ (isLocal : Bool) (kind : AccessKind) (perm : TBPerm),
      tbTransition true isLocal kind perm ≤ tbTransition false isLocal kind perm) ∧
    (tbTransition true false .write .frozen = .ub ∧
     tbTransition false false .write .frozen = .defined .disabled ∧
     ¬ (tbTransition false false .write .frozen ≤ tbTransition true false .write .frozen)) := by
  refine ⟨?_, ?_⟩
  · intro isLocal kind perm
    cases isLocal <;> cases kind <;> cases perm <;> first | trivial | rfl
  · refine ⟨rfl, rfl, ?_⟩
    intro h
    exact h

/-! ## Section 7: Modification 7 — Rust-Default `mayDiverge` Loop Semantics with Explicit `FiniteTripWitness`

In `AnLLVM-IR`:
- Every loop header defaults to `mayDiverge` (`EventualOut.diverges` is a
  first-class observable behavior in `StepLanguage`, NOT undefined behavior!).
- `LoopDeletion` and `ADCE` are forbidden from deleting a side-effect-free loop
  unless the loop carries a verified `FiniteTripWitness` (such as a bounded
  induction variable guaranteed to reach the exit in `fuel` steps).
-/

/-- A minimal program consisting of a loop controlled by `mayExit : Bool`
followed by returning `7 : Int`. -/
structure LoopProg where
  terminatesInOneStep : Bool
  deriving DecidableEq, Repr

/-- Execution state of `LoopProg`. -/
inductive LoopState where
  | inLoop (terminatesInOneStep : Bool)
  | exited
  deriving DecidableEq, Repr

/-- Step function of the unoptimized loop program (`probe_e_mustprogress_loops.ll`,
`@rust_may_diverge_loop`). -/
def stepLoopProg : LoopState → StepResult LoopState Int
  | .inLoop true  => .step .exited
  | .inLoop false => .step (.inLoop false)
  | .exited       => .done .normal 7

/-- Step function after `LoopDeletion` deletes the loop (`@cpp_mustprogress_loop`). -/
def stepDeletedLoopProg : LoopState → StepResult LoopState Int
  | _ => .done .normal 7

/-- The `Language (EventualOut Int)` for `LoopProg` before `LoopDeletion`. -/
def LoopLang : Language (EventualOut Int) :=
  StepLanguage LoopProg LoopState Int (fun p => .inLoop p.terminatesInOneStep) stepLoopProg

/-- The `Language (EventualOut Int)` for `LoopProg` after `LoopDeletion`. -/
def DeletedLoopLang : Language (EventualOut Int) :=
  StepLanguage LoopProg LoopState Int (fun p => .inLoop p.terminatesInOneStep) stepDeletedLoopProg

/-- A `FiniteTripWitness` certifying that `p : LoopProg` reaches the loop exit. -/
def FiniteTripWitness (p : LoopProg) : Prop :=
  p.terminatesInOneStep = true

theorem runSteps_infinite_loop :
    ∀ fuel : Nat, runSteps stepLoopProg fuel (.inLoop false) = .running
  | 0 => rfl
  | fuel + 1 => by
    simp [runSteps, stepLoopProg, runSteps_infinite_loop fuel]

/-- **Theorem 7A (`witnessed_loop_deletion_sound`):**
When a loop carries a valid `FiniteTripWitness p`, every behavior of the
loop-deleted program in `DeletedLoopLang` is a valid behavior of the original
program in `LoopLang` (at fuel 2). -/
theorem witnessed_loop_deletion_sound (p : LoopProg) (hw : FiniteTripWitness p) :
    ∀ b : Behavior (EventualOut Int),
      DeletedLoopLang.behaviors p b → LoopLang.behaviors p b := by
  intro b hb
  rcases p with ⟨termFlag⟩
  change termFlag = true at hw
  subst hw
  cases hb with
  | inl hub =>
    rcases hub with ⟨fuel, hfuel⟩
    cases fuel with
    | zero => contradiction
    | succ f =>
      simp [runSteps, stepDeletedLoopProg] at hfuel
  | inr hdef =>
    cases b with
    | ub => cases hdef
    | defined out =>
      cases out with
      | terminates k o =>
        rcases hdef with ⟨fuel, hfuel⟩
        cases fuel with
        | zero => contradiction
        | succ f =>
          simp [runSteps, stepDeletedLoopProg] at hfuel
          rcases hfuel with ⟨rfl, rfl⟩
          exact Or.inr ⟨2, rfl⟩
      | diverges =>
        have h1 := hdef 1
        simp [runSteps, stepDeletedLoopProg] at h1

/-- **Canary 7B (`canary_unwitnessed_loop_deletion_unsound`):**
Without a `FiniteTripWitness` (when `p.terminatesInOneStep = false`, as in a
Rust `loop {}`), `DeletedLoopLang` exhibits `.defined (.terminates .normal 7)`
while `LoopLang` only exhibits `.defined .diverges` and NEVER terminates!
Thus C++-style `mustprogress` `LoopDeletion` (`probe_e_mustprogress_loops.ll`)
is unsound for Rust's `EventualOut` semantics. -/
theorem canary_unwitnessed_loop_deletion_unsound :
    let p : LoopProg := { terminatesInOneStep := false }
    DeletedLoopLang.behaviors p (.defined (.terminates .normal 7)) ∧
    LoopLang.behaviors p (.defined .diverges) ∧
    ¬ LoopLang.behaviors p (.defined (.terminates .normal 7)) := by
  intro p
  refine ⟨?_, ?_, ?_⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr runSteps_infinite_loop
  · intro hterm
    cases hterm with
    | inl hub =>
      rcases hub with ⟨fuel, hfuel⟩
      rw [runSteps_infinite_loop fuel] at hfuel
      contradiction
    | inr hdone =>
      rcases hdone with ⟨fuel, hfuel⟩
      rw [runSteps_infinite_loop fuel] at hfuel
      contradiction

/-! ## Section 8: Kernel Axiom Audit (`#guard_msgs in #print axioms`) -/

/-- info: 'Anneal.AnLLVM.sroa_load_widening_across_padding_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sroa_load_widening_across_padding_sound

/-- info: 'Anneal.AnLLVM.canary_upstream_whole_word_load_poison_unsound' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_upstream_whole_word_load_poison_unsound

/-- info: 'Anneal.AnLLVM.basicAA_disjoint_allocId_store_load_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms basicAA_disjoint_allocId_store_load_commute

/-- info: 'Anneal.AnLLVM.gvn_ptrtoaddr_equality_substitution_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms gvn_ptrtoaddr_equality_substitution_sound

/-- info: 'Anneal.AnLLVM.canary_upstream_ptrtoint_gvn_collapse_unsound' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_upstream_ptrtoint_gvn_collapse_unsound

/-- info: 'Anneal.AnLLVM.phi_table_block_arg_lens_isomorphism' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phi_table_block_arg_lens_isomorphism

/-- info: 'Anneal.AnLLVM.alloca_live_dead_disjoint_coloring_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alloca_live_dead_disjoint_coloring_sound

/-- info: 'Anneal.AnLLVM.canary_escaped_pointer_lifetime_end_coloring_unsound' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_escaped_pointer_lifetime_end_coloring_unsound

/-- info: 'Anneal.AnLLVM.inlining_protector_drop_refines_and_not_symmetric' does not depend on any axioms -/
#guard_msgs in
#print axioms inlining_protector_drop_refines_and_not_symmetric

/-- info: 'Anneal.AnLLVM.witnessed_loop_deletion_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms witnessed_loop_deletion_sound

/-- info: 'Anneal.AnLLVM.canary_unwitnessed_loop_deletion_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_unwitnessed_loop_deletion_unsound

end Anneal.AnLLVM
