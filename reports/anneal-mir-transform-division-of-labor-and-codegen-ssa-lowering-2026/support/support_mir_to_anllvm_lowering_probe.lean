-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Probe: `MIR -> Clean-Slate AnLLVM` Lowering

This standalone Lean 4.34.1 module mechanizes the core semantic invariants
required to adapt `rustc_codegen_ssa` and `rustc_codegen_llvm`
(`rust-lang/rust` commit `49d734536222bf28bb6d07d885b3a81d145981da`) to target
a formally verified, clean-slate port of LLVM (`AnLLVM`) inside the Anneal
framework.

## Architectural Overview

In `rustc`, MIR-to-LLVM lowering is split across two crates:

1. `compiler/rustc_codegen_ssa/src/mir/` provides the backend-agnostic lowering
   engine (`FunctionCx`, `LocalAnalyzer`, `PlaceRef`, `OperandRef`,
   `OperandValue`, `codegen_mir`, `codegen_block`, `codegen_statement`,
   `codegen_rvalue`, `codegen_get_discr`, and `codegen_set_discr`).
2. `compiler/rustc_codegen_llvm/src/` implements the `BuilderMethods` and ABI
   traits against upstream LLVM's C++ API (`builder.rs`, `abi.rs`,
   `type_of.rs`, `intrinsic.rs`).

A key architectural insight from auditing `rustc_codegen_ssa/src/mir/analyze.rs`
is that `rustc_codegen_ssa` does **not** construct SSA $\phi$ nodes or compute
dominance frontiers for MIR locals during MIR-to-LLVM lowering. Instead,
`analyze::non_ssa_locals` (`mir/analyze.rs:17-56`) partitions MIR locals into
two disjoint lowering classes:

- **Single-definition dominating temporaries (`LocalKind::SSA` ->
  `LocalRef::Operand`)**: Locals whose `BackendRepr` is `Scalar`, `ScalarPair`,
  or `SimdVector`, that are defined at a single `DefLocation` (`Argument`,
  `Assignment`, or `CallReturn`), whose definition dominates every
  `NonMutatingUse`, and that never undergo in-place mutation (`Store`,
  `SetDiscriminant`, `Projection`) or address-taking (`Borrow`, `RawBorrow`).
  Because `codegen_mir` traverses basic blocks in reverse postorder
  (`traversal::mono_reachable_reverse_postorder`, `mir/mod.rs:291, 380`), every
  dominating single-definition local is guaranteed to have its
  `LocalRef::PendingOperand` slot overwritten by `overwrite_local`
  (`mir/statement.rs:40`) before any use is visited, and is never overwritten
  again.
- **Memory-backed locals (`LocalKind::Memory` -> `LocalRef::Place`)**: Any
  local with multiple definitions (e.g., mutated across branches or loops),
  non-dominating uses, in-place field/discriminant projections, or
  address-taking is allocated a stack frame slot (`PlaceRef::alloca` in
  `mir/mod.rs:344, 355`) and accessed via explicit loads and stores. Upstream
  LLVM later promotes non-escaped `alloca`s to SSA $\phi$ nodes during `SROA` /
  `Mem2Reg`.

Meanwhile, upstream LLVM's lack of byte-level definedness masks on registers
forces `rustc_codegen_ssa` and `rustc_codegen_llvm` into high-friction
memory-bounce workarounds:

- **`PassMode::Cast` memory bounce
  (`mir/block.rs:612-648, 2009-2013, 2058-2098`,
  `rustc_codegen_llvm/src/abi.rs:251-282`)**: Passing or returning a small
  struct with padding in integer registers (such as
  `#[repr(C)] struct Padded { a: u8, b: u32 }` packed into `i64`) allocates
  1–2 temporary `alloca`s, emits `llvm.lifetime.start`, `llvm.memcpy`, widened
  `load i64`/`store i64`, and `llvm.lifetime.end`.
- **`Rvalue::Cast(CastKind::Transmute)` fallback (`mir/rvalue.rs:332-440`)**:
  Transmuting between `BackendRepr::Scalar` and `BackendRepr::ScalarPair` (such
  as `u64 <-> (u32, u32)`) falls through to the wildcard arm at
  `mir/rvalue.rs:421-439`, allocating a temporary stack `alloca`, storing the
  source operand, and loading the target operand.

## Mechanized Contents

This file proves four main results:

1. **Theorem 1 (`analyze_local_ssa_vs_alloca_simulation` &
   `lowerMirToAnLlvm_compiles`)**: For any MIR body whose `LocalKind`
   assignment satisfies the single-assignment / no-in-place-mutation criteria
   of `rustc_codegen_ssa/src/mir/analyze.rs`, the lowered `AnLLVM` body refines
   the source MIR body in lockstep (`Compiles MirLang AnLLVMLang`).
2. **Theorem 2 (`codegen_get_set_discr_niche_roundtrip`)**: Universal modular
   arithmetic soundness of `rustc_codegen_ssa`'s wrapping-subtraction niche
   discriminant encoder (`codegen_tag_value`, `mir/place.rs:504-532`) and
   decoder (`codegen_get_discr`, `mir/operand.rs:522-697`) across all moduli
   $M > 0$ and all tagged and untagged variants, including wrap-around niche
   ranges.
3. **Theorem 3 (`register_transmute_and_cast_eliminates_alloca`)**: First-class
   `MaskedWord64` register-level `transmute` and `PassMode::Cast` pack/unpack
   in `AnLLVM` refine MIR `CastKind::Transmute` and `PassMode::Cast` in a
   single step with **zero** stack `alloca` allocations while preserving exact
   per-byte initialization masks across struct padding bytes.
4. **Negative Canary (`canary_multi_def_local_as_ssa_without_phi_unsound`)**:
   Classifying a multi-definition branched local as `.ssaOperand` in
   `rustc_codegen_ssa`'s single-pass RPO `LocalRef::Operand` table without
   `alloca` or $\phi$ placement causes the join block to observe the
   last-codegen'd branch's SSA value rather than the dynamically taken branch's
   value, violating simulation.
-/

namespace Round1Track3MirToAnLlvmProbe

/-!
## Section 1: Self-Contained Simulation and Refinement Infrastructure

We define a self-contained operational semantics and forward simulation
framework (`Language`, `Semantics`, `SimCodec`, `Compiles`) matching Anneal's
compilation refinement structure.
-/

/-- A language consists of program syntax `Prog` and execution state `State`. -/
structure Language where
  Prog : Type
  State : Type

/-- Small-step operational semantics with a terminal state predicate. -/
structure Semantics (L : Language) where
  step : L.Prog → L.State → L.State → Prop
  isTerminal : L.State → Prop

/-- Multi-step reflexive-transitive execution closure (`ExecStar`). -/
inductive ExecStar {L : Language} (S : Semantics L) (p : L.Prog) :
    L.State → L.State → Prop where
  | refl (s : L.State) : ExecStar S p s s
  | tail {s1 s2 s3 : L.State} :
      S.step p s1 s2 → ExecStar S p s2 s3 → ExecStar S p s1 s3

/-- Composition of two `ExecStar` derivations. -/
theorem ExecStar.trans {L : Language} {S : Semantics L} {p : L.Prog}
    {s1 s2 s3 : L.State} (h12 : ExecStar S p s1 s2) (h23 : ExecStar S p s2 s3) :
    ExecStar S p s1 s3 := by
  induction h12 with
  | refl _ => exact h23
  | tail hstep _ ih => exact ExecStar.tail hstep (ih h23)

/-- Single step lifted to `ExecStar`. -/
theorem ExecStar.single {L : Language} {S : Semantics L} {p : L.Prog}
    {s1 s2 : L.State} (h : S.step p s1 s2) : ExecStar S p s1 s2 :=
  ExecStar.tail h (ExecStar.refl s2)

/-- A simulation codec relates source states (`L1.State`) and target states
(`L2.State`) during compilation from `L1` to `L2`. -/
structure SimCodec (L1 L2 : Language) where
  stateRel : L1.State → L2.State → Prop

/-- Lockstep forward simulation (`Compiles`): every source step from related
states is matched by a target step to related states, and terminal states
match. -/
structure Compiles (L1 L2 : Language) (S1 : Semantics L1) (S2 : Semantics L2)
    (codec : SimCodec L1 L2) (p1 : L1.Prog) (p2 : L2.Prog) : Prop where
  step_sim :
    ∀ s1 s1' s2,
      codec.stateRel s1 s2 →
      S1.step p1 s1 s1' →
      ∃ s2', S2.step p2 s2 s2' ∧ codec.stateRel s1' s2'
  terminal_sim :
    ∀ s1 s2,
      codec.stateRel s1 s2 →
      S1.isTerminal s1 →
      S2.isTerminal s2

/-- Any `Compiles` proof lifts by induction to multi-step execution traces
(`ExecStar`). -/
theorem Compiles.execStar_sim {L1 L2 : Language} {S1 : Semantics L1}
    {S2 : Semantics L2} {codec : SimCodec L1 L2} {p1 : L1.Prog} {p2 : L2.Prog}
    (hcomp : Compiles L1 L2 S1 S2 codec p1 p2)
    {s1 s1' : L1.State} {s2 : L2.State}
    (hrel : codec.stateRel s1 s2)
    (htrace : ExecStar S1 p1 s1 s1') :
    ∃ s2', ExecStar S2 p2 s2 s2' ∧ codec.stateRel s1' s2' := by
  induction htrace generalizing s2 with
  | refl s1 => exact ⟨s2, ExecStar.refl s2, hrel⟩
  | tail hstep _ ih =>
    rcases hcomp.step_sim _ _ _ hrel hstep with ⟨s2Mid, hstep2, hrelMid⟩
    rcases ih hrelMid with ⟨s2Final, htrace2, hrelFinal⟩
    exact ⟨s2Final, ExecStar.tail hstep2 htrace2, hrelFinal⟩

/-!
## Section 2: Masked Byte / Word Domain (`MaskedByte`, `MaskedWord64`)

In upstream LLVM, a scalar register (`i32`, `i64`) cannot represent a partially
initialized byte sequence without whole-value `undef` or `poison` semantics.
When `rustc_codegen_ssa` lowers `PassMode::Cast` or `CastKind::Transmute` on a
padded struct like `#[repr(C)] struct Padded { a: u8, b: u32 }` (where byte 0
is `a`, bytes 1..3 are uninitialized padding, and bytes 4..7 are `b`), upstream
`rustc` is forced to allocate stack `alloca`s and copy through memory
(`mir/block.rs:2058-2098`, `mir/rvalue.rs:421-439`).

In `AnLLVM`, every register word is a `MaskedWord64` (8 `MaskedByte`s, each
carrying a byte value and an explicit `init : Bool` definedness bit). This
allows register-level `packCastRegs`, `unpackCastRegs`, and `bitcastBytes` to
operate purely in SSA registers without stack `alloca`s or padding-induced
poison contamination.
-/

/-- A single byte with an explicit initialization mask bit (`init = false`
models an uninitialized padding byte). -/
structure MaskedByte where
  val : Nat
  init : Bool
  deriving DecidableEq, Repr

/-- An uninitialized padding byte (`val = 0, init = false`). -/
def MaskedByte.uninit : MaskedByte := { val := 0, init := false }

/-- An initialized byte (`val mod 256, init = true`). -/
def MaskedByte.ofNat (n : Nat) : MaskedByte := { val := n % 256, init := true }

/-- A 32-bit word represented as 4 little-endian `MaskedByte`s. -/
structure MaskedWord32 where
  b0 : MaskedByte
  b1 : MaskedByte
  b2 : MaskedByte
  b3 : MaskedByte
  deriving DecidableEq, Repr

/-- A 64-bit word represented as 8 little-endian `MaskedByte`s (grouped as low
and high 32-bit halves for `ScalarPair` and `PassMode::Cast` decomposition). -/
structure MaskedWord64 where
  lo : MaskedWord32
  hi : MaskedWord32
  deriving DecidableEq, Repr

/-- Construct an initialized 32-bit word from a natural number. -/
def MaskedWord32.ofU32 (n : Nat) : MaskedWord32 :=
  { b0 := MaskedByte.ofNat n
    b1 := MaskedByte.ofNat (n / 256)
    b2 := MaskedByte.ofNat (n / 65536)
    b3 := MaskedByte.ofNat (n / 16777216) }

/-- Construct an uninitialized 32-bit word. -/
def MaskedWord32.uninit : MaskedWord32 :=
  { b0 := MaskedByte.uninit, b1 := MaskedByte.uninit
    b2 := MaskedByte.uninit, b3 := MaskedByte.uninit }

/-- Decode a 32-bit word's numeric value from its 4 little-endian bytes. -/
def MaskedWord32.toNat (w : MaskedWord32) : Nat :=
  (w.b0.val % 256) + 256 * (w.b1.val % 256) +
  65536 * (w.b2.val % 256) + 16777216 * (w.b3.val % 256)

/-- Whether all 4 bytes of a `MaskedWord32` are initialized. -/
def MaskedWord32.isFullyInit (w : MaskedWord32) : Bool :=
  w.b0.init && w.b1.init && w.b2.init && w.b3.init

/-- Construct an initialized 64-bit word from a natural number. -/
def MaskedWord64.ofU64 (n : Nat) : MaskedWord64 :=
  { lo := MaskedWord32.ofU32 (n % 4294967296)
    hi := MaskedWord32.ofU32 (n / 4294967296) }

/-- Construct an uninitialized 64-bit word. -/
def MaskedWord64.uninit : MaskedWord64 :=
  { lo := MaskedWord32.uninit, hi := MaskedWord32.uninit }

/-- Decode a 64-bit word's numeric value. -/
def MaskedWord64.toNat (w : MaskedWord64) : Nat :=
  w.lo.toNat + 4294967296 * w.hi.toNat

/-- Model of `#[repr(C)] struct Padded { a: u8, b: u32 }` (`size = 8`,
`align = 4`), where byte 0 is `a : u8`, bytes 1..3 are 3 padding bytes, and
bytes 4..7 are `b : u32`. -/
structure PaddedReprC where
  a : MaskedByte
  pad1 : MaskedByte
  pad2 : MaskedByte
  pad3 : MaskedByte
  b : MaskedWord32
  deriving DecidableEq, Repr

/-- Construct a `PaddedReprC` value from initialized fields `a : u8` and
`b : u32`, leaving the 3 padding bytes at offsets `1..4` explicitly
uninitialized (`MaskedByte.uninit`). -/
def PaddedReprC.mkInit (a : Nat) (b : Nat) : PaddedReprC :=
  { a := MaskedByte.ofNat a
    pad1 := MaskedByte.uninit
    pad2 := MaskedByte.uninit
    pad3 := MaskedByte.uninit
    b := MaskedWord32.ofU32 b }

/-- Pack a `PaddedReprC` value into a single 64-bit `AnLLVM` `MaskedWord64`
register for `PassMode::Cast` (`pack_cast_regs`) or `CastKind::Transmute`
without touching memory. -/
def packPaddedToWord64 (p : PaddedReprC) : MaskedWord64 :=
  { lo := { b0 := p.a, b1 := p.pad1, b2 := p.pad2, b3 := p.pad3 }, hi := p.b }

/-- Unpack a 64-bit `AnLLVM` `MaskedWord64` register back into a `PaddedReprC`
value for `PassMode::Cast` (`unpack_cast_regs`) without touching memory. -/
def unpackWord64ToPadded (w : MaskedWord64) : PaddedReprC :=
  { a := w.lo.b0, pad1 := w.lo.b1, pad2 := w.lo.b2, pad3 := w.lo.b3, b := w.hi }

/-- Pack a `ScalarPair` of two 32-bit words `(lo, hi)` (`(u32, u32)`) into a
single `MaskedWord64` register (`bitcast_bytes` for `CastKind::Transmute`). -/
def packPair32ToWord64 (lo hi : MaskedWord32) : MaskedWord64 :=
  { lo := lo, hi := hi }

/-- Unpack a `MaskedWord64` register into a `ScalarPair` of two 32-bit words
`(lo, hi)` (`bitcast_bytes` for `Rvalue::Cast(CastKind::Transmute)`). -/
def unpackWord64ToPair32 (w : MaskedWord64) : MaskedWord32 × MaskedWord32 :=
  (w.lo, w.hi)

/-- `rustc_codegen_ssa`'s `OperandValue`
(`compiler/rustc_codegen_ssa/src/mir/operand.rs:28-89`):
- `imm`: `OperandValue::Immediate(V)` for `BackendRepr::Scalar` (or packed
  `Cast` register);
- `pair`: `OperandValue::Pair(V, V)` for `BackendRepr::ScalarPair` (2-tuples,
  slices `&[T]`, checked binop `(val, overflow)` results, etc.);
- `refPlace`: `OperandValue::Ref(PlaceValue<V>)` for `BackendRepr::Memory`
  values backed by a stack slot;
- `zst`: `OperandValue::ZeroSized` for zero-sized types. -/
inductive OperandValue where
  | imm (v : MaskedWord64)
  | pair (a : MaskedWord64) (b : MaskedWord64)
  | refPlace (slot : Nat)
  | zst
  deriving DecidableEq, Repr

/-- Convenience constructor for a 64-bit integer scalar `OperandValue`. -/
def OperandValue.ofU64 (n : Nat) : OperandValue := .imm (MaskedWord64.ofU64 n)

/-- Convenience constructor for a `ScalarPair` of two 64-bit integers. -/
def OperandValue.ofPairU64 (a b : Nat) : OperandValue :=
  .pair (MaskedWord64.ofU64 a) (MaskedWord64.ofU64 b)

/-- Extract the primary scalar word from an `OperandValue` (defaulting to
`MaskedWord64.uninit` if non-scalar). -/
def OperandValue.asScalar (v : OperandValue) : MaskedWord64 :=
  match v with
  | .imm w => w
  | .pair a _ => a
  | .refPlace _ => MaskedWord64.uninit
  | .zst => MaskedWord64.uninit

/-- Extract field `0` or `1` from an `OperandValue::Pair`, modeling
`OperandRef::extract_field` in
`compiler/rustc_codegen_ssa/src/mir/operand.rs:1054-1098`. -/
def OperandValue.extractPairField (v : OperandValue) (fieldOne : Bool) :
    OperandValue :=
  match v with
  | .pair a b => if fieldOne then .imm b else .imm a
  | .imm w => .imm w
  | .refPlace s => .refPlace s
  | .zst => .zst

/-!
## Section 3: Niche Discriminant Encoding and Decoding (`TagEncoding::Niche`)

We now mechanize the exact modular arithmetic algorithm used by
`rustc_codegen_ssa` to encode and decode `TagEncoding::Niche` enum
discriminants:

- **Encoding (`codegen_tag_value`,
  `compiler/rustc_codegen_ssa/src/mir/place.rs:504-532`)**:
  ```rust
  TagEncoding::Niche { untagged_variant, ref niche_variants, niche_start } => {
      if variant_index == untagged_variant {
          return Ok(None);
      }
      let niche_value = variant_index.as_u32() - niche_variants.start().as_u32();
      let niche_value = (niche_value as u128).wrapping_add(niche_start);
      let niche_value = niche_value & niche_layout.size.unsigned_int_max();
      ...
  }
  ```
- **Decoding (`OperandRef::codegen_get_discr`,
  `compiler/rustc_codegen_ssa/src/mir/operand.rs:522-697`)**:
  ```rust
  let relative_max =
      niche_variants.end().as_u32() - niche_variants.start().as_u32();
  // Wrapping subtraction: relative_discr = (tag - niche_start) mod M
  let relative_discr = bx.sub(tag, niche_start_const);
  let is_niche = bx.icmp(IntPredicate::IntULE, relative_discr, relative_max_const);
  let tagged_discr = bx.add(relative_discr, niche_variants_start_const);
  let discr = bx.select(is_niche, tagged_discr, untagged_variant_const);
  ```

Crucially, `niche_start + (variant_index - niche_variants.start)` is allowed to
**wrap around** the integer modulus $M = 2^k$ (for instance, when the valid
values of the untagged payload occupy a contiguous interval $[a, b]$ in the
middle of $[0, 2^k)$, leaving the niche range $[b + 1, 2^k) \cup [0, a)$
wrapping across $0$). We prove below that modular wrapping addition on encode
followed by modular wrapping subtraction and an unsigned `<= relative_max`
comparison on decode is universally sound across all $M > 0$, regardless of
whether the niche range wraps around $0$.
-/

/-- Parameters of a `TagEncoding::Niche` layout (`rustc_abi::TagEncoding`),
parameterized over an arbitrary bitwidth modulus `modulus` ($M = 2^k > 0$). -/
structure NicheConfig where
  /-- Integer modulus $M$ of the tag scalar (e.g., $2^8, 2^{16}, 2^{32}$). -/
  modulus : Nat
  /-- Variant index of the untagged payload variant (`untagged_variant`). -/
  untaggedVariant : Nat
  /-- Inclusive start of the niche variant range (`niche_variants.start`). -/
  nicheVariantsStart : Nat
  /-- Inclusive end of the niche variant range (`niche_variants.end`). -/
  nicheVariantsEnd : Nat
  /-- Starting tag value of the niche range (`niche_start < modulus`). -/
  nicheStart : Nat
  deriving DecidableEq, Repr

/-- Well-formedness predicate for `NicheConfig`:
1. The integer modulus is positive ($M > 0$).
2. `nicheVariantsStart <= nicheVariantsEnd`.
3. The number of niche-encoded variants fits strictly within the modulus
   (`nicheVariantsEnd - nicheVariantsStart < M`). -/
structure ValidNicheConfig (cfg : NicheConfig) : Prop where
  modulus_pos : 0 < cfg.modulus
  valid_range : cfg.nicheVariantsStart ≤ cfg.nicheVariantsEnd
  range_fits : cfg.nicheVariantsEnd - cfg.nicheVariantsStart < cfg.modulus

/-- Modular wrapping addition `(a + b) mod M`. -/
def wrappingAddMod (M a b : Nat) : Nat := (a + b) % M

/-- Modular wrapping subtraction `(a - b) mod M`, defined as
`((a % M) + M - (b % M)) % M`. -/
def wrappingSubMod (M a b : Nat) : Nat := ((a % M) + M - (b % M)) % M

/-- Key modular arithmetic lemma: for any modulus $M > 0$, any base `start`, and
any offset $d < M$, wrapping-subtracting `start` from `wrappingAddMod M start d`
recovers $d$ exactly—even when `start + d >= M` wraps around 0. -/
theorem wrappingSubMod_wrappingAddMod_cancel (M start d : Nat)
    (hM : 0 < M) (hd : d < M) :
    wrappingSubMod M (wrappingAddMod M start d) start = d := by
  unfold wrappingSubMod wrappingAddMod
  rw [Nat.mod_mod]
  have hDivModS : start = M * (start / M) + start % M :=
    (Nat.div_add_mod start M).symm
  have hStartModLt : start % M < M := Nat.mod_lt start hM
  -- Express `(start + d) % M` as `((start % M) + d) % M`
  have hAddMod : (start + d) % M = (start % M + d) % M := by
    conv => lhs; rw [hDivModS]
    rw [Nat.add_assoc, Nat.mul_add_mod]
  rw [hAddMod]
  by_cases hWrap : start % M + d < M
  · -- Case 1: no wrap-around (`(start % M) + d < M`)
    have hModEq : (start % M + d) % M = start % M + d := Nat.mod_eq_of_lt hWrap
    rw [hModEq]
    have hRearr : start % M + d + M - start % M = d + M := by omega
    rw [hRearr, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hd
  · -- Case 2: wrap-around across M (`M ≤ (start % M) + d < 2 * M`)
    have hGe : M ≤ start % M + d := by omega
    have hLt2 : start % M + d - M < M := by omega
    have hSubMod : (start % M + d) % M = start % M + d - M := by
      rw [Nat.mod_eq_sub_mod hGe]
      exact Nat.mod_eq_of_lt hLt2
    rw [hSubMod]
    have hRearr : start % M + d - M + M - start % M = d := by omega
    rw [hRearr]
    exact Nat.mod_eq_of_lt hd

/-- `codegen_tag_value` (`compiler/rustc_codegen_ssa/src/mir/place.rs:504-532`):
encodes a niche variant index `variantIdx` into its tag scalar in $[0, M)$. -/
def encodeNicheTag (cfg : NicheConfig) (variantIdx : Nat) : Nat :=
  let rel := variantIdx - cfg.nicheVariantsStart
  wrappingAddMod cfg.modulus cfg.nicheStart rel

/-- `OperandRef::codegen_get_discr`
(`compiler/rustc_codegen_ssa/src/mir/operand.rs:522-697`): decodes a tag scalar
value `tag` in $[0, M)$ back into a variant index using wrapping subtraction and
an unsigned `<= relative_max` range test. -/
def decodeNicheDiscr (cfg : NicheConfig) (tag : Nat) : Nat :=
  let relativeMax := cfg.nicheVariantsEnd - cfg.nicheVariantsStart
  let relativeDiscr := wrappingSubMod cfg.modulus tag cfg.nicheStart
  if relativeDiscr ≤ relativeMax then
    cfg.nicheVariantsStart + relativeDiscr
  else
    cfg.untaggedVariant

/-- **Theorem 2a (`codegen_get_set_discr_niche_tagged_roundtrip`)**:
For any well-formed `NicheConfig` and any variant index `v` in the niche range
`[nicheVariantsStart, nicheVariantsEnd]`, encoding `v` via `encodeNicheTag` and
decoding via `decodeNicheDiscr` recovers `v` identically. -/
theorem codegen_get_set_discr_niche_tagged_roundtrip
    (cfg : NicheConfig) (hvalid : ValidNicheConfig cfg)
    (v : Nat) (hlo : cfg.nicheVariantsStart ≤ v)
    (hhi : v ≤ cfg.nicheVariantsEnd) :
    decodeNicheDiscr cfg (encodeNicheTag cfg v) = v := by
  unfold decodeNicheDiscr encodeNicheTag
  dsimp only
  have hd_le :
      v - cfg.nicheVariantsStart ≤
      cfg.nicheVariantsEnd - cfg.nicheVariantsStart := by omega
  have hd_lt : v - cfg.nicheVariantsStart < cfg.modulus :=
    Nat.lt_of_le_of_lt hd_le hvalid.range_fits
  rw [wrappingSubMod_wrappingAddMod_cancel cfg.modulus cfg.nicheStart
        (v - cfg.nicheVariantsStart) hvalid.modulus_pos hd_lt]
  simp [hd_le]
  omega

/-- **Theorem 2b (`codegen_get_set_discr_niche_untagged_roundtrip`)**:
For any tag value `payloadTag` belonging to the `untaggedVariant` (whose
wrapping distance from `nicheStart` exceeds
`nicheVariantsEnd - nicheVariantsStart`), `decodeNicheDiscr` returns
`cfg.untaggedVariant`. -/
theorem codegen_get_set_discr_niche_untagged_roundtrip
    (cfg : NicheConfig) (payloadTag : Nat)
    (hout : cfg.nicheVariantsEnd - cfg.nicheVariantsStart <
            wrappingSubMod cfg.modulus payloadTag cfg.nicheStart) :
    decodeNicheDiscr cfg payloadTag = cfg.untaggedVariant := by
  unfold decodeNicheDiscr
  dsimp only
  have hnot : ¬ (wrappingSubMod cfg.modulus payloadTag cfg.nicheStart ≤
                 cfg.nicheVariantsEnd - cfg.nicheVariantsStart) := by omega
  simp [hnot]

/-- Representation of an enum value using `TagEncoding::Niche`: either a
niche-tagged empty variant (`tagged v` with
`v ∈ [nicheVariantsStart, nicheVariantsEnd]`) or the untagged variant carrying a
non-niche payload scalar (`untagged payloadTag`). -/
inductive NicheEnumValue (cfg : NicheConfig) : Type where
  | tagged (v : Nat)
      (hlo : cfg.nicheVariantsStart ≤ v)
      (hhi : v ≤ cfg.nicheVariantsEnd)
  | untagged (payloadTag : Nat)
      (hout : cfg.nicheVariantsEnd - cfg.nicheVariantsStart <
              wrappingSubMod cfg.modulus payloadTag cfg.nicheStart)

/-- Expected logical discriminant of a `NicheEnumValue`. -/
def NicheEnumValue.logicalDiscr {cfg : NicheConfig} : NicheEnumValue cfg → Nat
  | .tagged v _ _ => v
  | .untagged _ _ => cfg.untaggedVariant

/-- Physical scalar representation of a `NicheEnumValue` in memory / SSA
register as produced by `codegen_set_discr` (`mir/place.rs:258-274`). -/
def NicheEnumValue.encodeToScalar {cfg : NicheConfig} : NicheEnumValue cfg → Nat
  | .tagged v _ _ => encodeNicheTag cfg v
  | .untagged payloadTag _ => payloadTag

/-- **Theorem 2 (`codegen_get_set_discr_niche_roundtrip`)**:
Complete universal round-trip soundness of `rustc_codegen_ssa`'s
`TagEncoding::Niche` discriminant encoding (`codegen_tag_value`) and decoding
(`codegen_get_discr`) across both niche-tagged and untagged variants for any
valid `NicheConfig`. -/
theorem codegen_get_set_discr_niche_roundtrip
    (cfg : NicheConfig) (hvalid : ValidNicheConfig cfg)
    (val : NicheEnumValue cfg) :
    decodeNicheDiscr cfg val.encodeToScalar = val.logicalDiscr := by
  cases val with
  | tagged v hlo hhi =>
    exact codegen_get_set_discr_niche_tagged_roundtrip cfg hvalid v hlo hhi
  | untagged payloadTag hout =>
    exact codegen_get_set_discr_niche_untagged_roundtrip cfg payloadTag hout

/-!
## Section 4: `MIR` and `AnLLVM` Languages, `LocalAnalyzer`, and Lowering

We now formalize the `MIR -> AnLLVM` lowering pass modeled on
`compiler/rustc_codegen_ssa/src/mir/`:

- `LocalKind`: `.ssaOperand` (`LocalRef::Operand` / `PendingOperand`) vs.
  `.memAlloca` (`LocalRef::Place`), produced by `analyze::non_ssa_locals`
  (`mir/analyze.rs:17-56`).
- `MirRvalue` & `MirStmt`: core MIR rvalues and statements including
  `StorageLive`/`StorageDead`, `Assign`, `SetDiscriminant`, `CheckedBinaryOp`
  (`AddWithOverflow`, `MulWithOverflow`), `Discriminant`, `Transmute`,
  `PassMode::Cast`, `Assert`, and branched control flow (`condBranch`).
- `AnLlvmInstr`: clean-slate `AnLLVM` instructions where `.ssaOperand` locals
  access the SSA register file (`ssaRegs`), `.memAlloca` locals access the stack
  frame (`frameSlots`) with explicit `AllocaLive`/`AllocaDead` liveness
  transitions, and `Transmute`/`PassMode::Cast` execute in SSA registers with
  zero `alloca`s.
-/

/-- Identifier for a MIR local (`rustc_middle::mir::Local`). -/
abbrev LocalId := Nat

/-- Classification of a MIR local by `rustc_codegen_ssa/src/mir/analyze.rs`:
- `ssaOperand`: lowered directly to an SSA `OperandRef` (`LocalRef::Operand` /
  `PendingOperand`) with zero stack frame allocation.
- `memAlloca`: lowered to a stack frame `PlaceRef` (`LocalRef::Place`) with
  explicit liveness (`AllocaLive`/`AllocaDead`) and memory loads/stores. -/
inductive LocalKind where
  | ssaOperand
  | memAlloca
  deriving DecidableEq, Repr

/-- Mapping from `LocalId` to its `LocalKind` classification. -/
abbrev LocalClassification := LocalId → LocalKind

/-- Modes of register-level bitcast/transmute supported directly on
`MaskedWord64` and `OperandValue` without stack `alloca` bounce. -/
inductive TransmuteMode where
  /-- Transmute `(u32, u32)` (`ScalarPair`) to `u64` (`Scalar`). -/
  | pair32ToU64
  /-- Transmute `u64` (`Scalar`) to `(u32, u32)` (`ScalarPair`). -/
  | u64ToPair32
  /-- Pack `PaddedReprC { a: u8, pad: [u8; 3], b: u32 }` (`ScalarPair` of `a`
  and `b` in Rust ABI) into a 64-bit word preserving uninitialized padding bytes
  `1..4`. -/
  | paddedPairToWord64
  /-- Unpack a 64-bit word back into the `(a: u8, b: u32)` `ScalarPair` of
  `PaddedReprC`. -/
  | word64ToPaddedPair
  deriving DecidableEq, Repr

/-- Pure evaluation of `AnLLVM`'s register-level `bitcast_bytes` /
`pack_cast_regs` instruction on an `OperandValue`, requiring zero stack
`alloca`s. -/
def evalRegisterTransmute (mode : TransmuteMode) (v : OperandValue) :
    OperandValue :=
  match mode with
  | .pair32ToU64 =>
    match v with
    | .pair a b => .imm (packPair32ToWord64 a.lo b.lo)
    | _ => .imm MaskedWord64.uninit
  | .u64ToPair32 =>
    match v with
    | .imm w =>
      let (lo, hi) := unpackWord64ToPair32 w
      .pair { lo := lo, hi := MaskedWord32.ofU32 0 }
            { lo := hi, hi := MaskedWord32.ofU32 0 }
    | _ => .pair MaskedWord64.uninit MaskedWord64.uninit
  | .paddedPairToWord64 =>
    match v with
    | .pair a b =>
      let padded : PaddedReprC :=
        { a := a.lo.b0
          pad1 := MaskedByte.uninit
          pad2 := MaskedByte.uninit
          pad3 := MaskedByte.uninit
          b := b.lo }
      .imm (packPaddedToWord64 padded)
    | _ => .imm MaskedWord64.uninit
  | .word64ToPaddedPair =>
    match v with
    | .imm w =>
      let p := unpackWord64ToPadded w
      .pair { lo := { b0 := p.a, b1 := MaskedByte.ofNat 0
                      b2 := MaskedByte.ofNat 0, b3 := MaskedByte.ofNat 0 }
              hi := MaskedWord32.ofU32 0 }
            { lo := p.b, hi := MaskedWord32.ofU32 0 }
    | _ => .pair MaskedWord64.uninit MaskedWord64.uninit

/-- Pure evaluation of 64-bit unsigned addition with overflow
(`Rvalue::BinaryOp(BinOp::AddWithOverflow)` -> `OperandValue::Pair(sum, ovf)`),
matching `Builder::checked_binop` in
`compiler/rustc_codegen_llvm/src/builder.rs:612-653`. -/
def evalCheckedAdd64 (a b : OperandValue) : OperandValue :=
  let x := a.asScalar.toNat % 18446744073709551616
  let y := b.asScalar.toNat % 18446744073709551616
  let sum := (x + y) % 18446744073709551616
  let ovf := if x + y ≥ 18446744073709551616 then 1 else 0
  OperandValue.ofPairU64 sum ovf

/-- Pure evaluation of 64-bit unsigned multiplication with overflow
(`Rvalue::BinaryOp(BinOp::MulWithOverflow)` -> `OperandValue::Pair(prod, ovf)`),
matching `@llvm.umul.with.overflow.i64` in
`compiler/rustc_codegen_llvm/src/builder.rs:647-652`. -/
def evalCheckedMul64 (a b : OperandValue) : OperandValue :=
  let x := a.asScalar.toNat % 18446744073709551616
  let y := b.asScalar.toNat % 18446744073709551616
  let prod := (x * y) % 18446744073709551616
  let ovf := if x * y ≥ 18446744073709551616 then 1 else 0
  OperandValue.ofPairU64 prod ovf

/-- MIR Rvalues (`rustc_middle::mir::Rvalue`) lowered by
`FunctionCx::codegen_rvalue` and `FunctionCx::codegen_rvalue_operand`
(`compiler/rustc_codegen_ssa/src/mir/rvalue.rs`). -/
inductive MirRvalue where
  /-- Constant operand (`Rvalue::Use(Operand::Constant)`). -/
  | constVal (v : OperandValue)
  /-- Copy or move of a local (`Rvalue::Use(Operand::Copy | Operand::Move)`). -/
  | useLocal (src : LocalId)
  /-- Projection of `.0` or `.1` from a `ScalarPair` (`PlaceElem::Field`). -/
  | projPairField (src : LocalId) (fieldOne : Bool)
  /-- Construction of a `ScalarPair` aggregate (`Rvalue::Aggregate`). -/
  | makeScalarPair (src0 src1 : LocalId)
  /-- Wrapping 64-bit addition (`Rvalue::BinaryOp(BinOp::Add)`). -/
  | wrappingAdd64 (lhs rhs : LocalId)
  /-- Wrapping 64-bit subtraction (`Rvalue::BinaryOp(BinOp::Sub)`). -/
  | wrappingSub64 (lhs rhs : LocalId)
  /-- Checked 64-bit addition (`Rvalue::BinaryOp(BinOp::AddWithOverflow)`). -/
  | checkedAdd64 (lhs rhs : LocalId)
  /-- Checked 64-bit multiplication (`BinOp::MulWithOverflow`). -/
  | checkedMul64 (lhs rhs : LocalId)
  /-- Discriminant read of a `TagEncoding::Niche` (`Rvalue::Discriminant`). -/
  | discriminantNiche (src : LocalId) (cfg : NicheConfig)
  /-- Bitcast / `Transmute` or `PassMode::Cast` pack/unpack
  (`Rvalue::Cast(CastKind::Transmute)`). -/
  | transmuteReg (src : LocalId) (mode : TransmuteMode)
  deriving DecidableEq, Repr

/-- MIR statements and structured terminators (`rustc_middle::mir::Statement`
and `TerminatorKind`). -/
inductive MirStmt where
  /-- `StatementKind::StorageLive(local)` (`mir/statement.rs:72-78`). -/
  | storageLive (l : LocalId)
  /-- `StatementKind::StorageDead(local)` (`mir/statement.rs:79-85`). -/
  | storageDead (l : LocalId)
  /-- Single dominating SSA-eligible definition (`mir/statement.rs:35-42`). -/
  | assignSsa (dst : LocalId) (rv : MirRvalue)
  /-- Store to a memory-backed local (`LocalKind::Memory`,
  `mir/statement.rs:21-22`). -/
  | storePlace (dst : LocalId) (rv : MirRvalue)
  /-- `StatementKind::SetDiscriminant` (`mir/statement.rs:69-71`,
  `mir/place.rs:258-274`). -/
  | setDiscriminantNiche (dst : LocalId) (cfg : NicheConfig) (variantIdx : Nat)
  /-- `TerminatorKind::Assert` (`mir/block.rs:753-858`): asserts that the
  overflow flag in `condLocal` is `0`, panicking with `panicCode` otherwise. -/
  | assertZero (condLocal : LocalId) (panicCode : Nat)
  /-- `TerminatorKind::SwitchInt` conditional branch joining at a merge. -/
  | condBranch (condLocal : LocalId)
      (thenBranch : List MirStmt) (elseBranch : List MirStmt)
  deriving Repr

/-- Execution status of a MIR or `AnLLVM` machine state. -/
inductive ExecStatus where
  | running
  | panicked (code : Nat)
  deriving DecidableEq, Repr

/-- MIR execution environment: maps each `LocalId` to its current `OperandValue`
and tracks whether its storage is live. -/
structure MirEnv where
  locals : LocalId → OperandValue
  live : LocalId → Bool

/-- Update a local's value in `MirEnv`. -/
def MirEnv.writeLocal (env : MirEnv) (l : LocalId) (v : OperandValue) : MirEnv :=
  { env with locals := fun k => if k = l then v else env.locals k }

/-- Update a local's storage liveness in `MirEnv`. -/
def MirEnv.setLive (env : MirEnv) (l : LocalId) (isLive : Bool) : MirEnv :=
  { env with live := fun k => if k = l then isLive else env.live k }

/-- Evaluate a `MirRvalue` in `MirEnv`. -/
def evalMirRvalue (env : MirEnv) (rv : MirRvalue) : OperandValue :=
  match rv with
  | .constVal v => v
  | .useLocal src => env.locals src
  | .projPairField src fieldOne => (env.locals src).extractPairField fieldOne
  | .makeScalarPair src0 src1 =>
    .pair (env.locals src0).asScalar (env.locals src1).asScalar
  | .wrappingAdd64 lhs rhs =>
    let x := (env.locals lhs).asScalar.toNat
    let y := (env.locals rhs).asScalar.toNat
    OperandValue.ofU64 ((x + y) % 18446744073709551616)
  | .wrappingSub64 lhs rhs =>
    let x := (env.locals lhs).asScalar.toNat % 18446744073709551616
    let y := (env.locals rhs).asScalar.toNat % 18446744073709551616
    OperandValue.ofU64 ((x + 18446744073709551616 - y) % 18446744073709551616)
  | .checkedAdd64 lhs rhs => evalCheckedAdd64 (env.locals lhs) (env.locals rhs)
  | .checkedMul64 lhs rhs => evalCheckedMul64 (env.locals lhs) (env.locals rhs)
  | .discriminantNiche src cfg =>
    let rawTag := (env.locals src).asScalar.toNat
    OperandValue.ofU64 (decodeNicheDiscr cfg rawTag)
  | .transmuteReg src mode => evalRegisterTransmute mode (env.locals src)

/-- Full small-step MIR state: remaining statement continuation, environment,
and execution status. -/
structure MirState where
  stmts : List MirStmt
  env : MirEnv
  status : ExecStatus

/-- Execute a single `MirStmt` at the head of a statement list, returning the
new statement continuation, updated `MirEnv`, and `ExecStatus`. -/
def stepMirStmt (s : MirStmt) (rest : List MirStmt) (env : MirEnv) :
    List MirStmt × MirEnv × ExecStatus :=
  match s with
  | .storageLive l => (rest, env.setLive l true, .running)
  | .storageDead l =>
    (rest, (env.setLive l false).writeLocal l (.imm MaskedWord64.uninit), .running)
  | .assignSsa dst rv => (rest, env.writeLocal dst (evalMirRvalue env rv), .running)
  | .storePlace dst rv => (rest, env.writeLocal dst (evalMirRvalue env rv), .running)
  | .setDiscriminantNiche dst cfg variantIdx =>
    let newVal :=
      if variantIdx = cfg.untaggedVariant then
        env.locals dst
      else
        OperandValue.ofU64 (encodeNicheTag cfg variantIdx)
    (rest, env.writeLocal dst newVal, .running)
  | .assertZero condLocal panicCode =>
    if (env.locals condLocal).asScalar.toNat = 0 then
      (rest, env, .running)
    else
      ([], env, .panicked panicCode)
  | .condBranch condLocal thenBranch elseBranch =>
    if (env.locals condLocal).asScalar.toNat ≠ 0 then
      (thenBranch ++ rest, env, .running)
    else
      (elseBranch ++ rest, env, .running)

/-- Clean-slate `AnLLVM` Rvalue expressions, where operand accesses are
explicitly split between SSA registers (`readSsaReg`) and stack frame slots
(`loadFrameSlot`) according to `LocalAnalyzer`'s classification
(`mir/analyze.rs`). -/
inductive AnLlvmExpr where
  | constVal (v : OperandValue)
  | readSsaReg (reg : LocalId)
  | loadFrameSlot (slot : LocalId)
  | projPairFieldSsa (reg : LocalId) (fieldOne : Bool)
  | projPairFieldSlot (slot : LocalId) (fieldOne : Bool)
  | makeScalarPair (e0 e1 : AnLlvmExpr)
  | wrappingAdd64 (e0 e1 : AnLlvmExpr)
  | wrappingSub64 (e0 e1 : AnLlvmExpr)
  | checkedAdd64 (e0 e1 : AnLlvmExpr)
  | checkedMul64 (e0 e1 : AnLlvmExpr)
  | decodeNicheDiscrExpr (e : AnLlvmExpr) (cfg : NicheConfig)
  | bitcastBytes (e : AnLlvmExpr) (mode : TransmuteMode)
  deriving DecidableEq, Repr

/-- Clean-slate `AnLLVM` instructions emitted by `lowerMirToAnLlvm`. -/
inductive AnLlvmInstr where
  /-- No-op emitted for `StorageLive`/`StorageDead` on an `.ssaOperand` local
  (`mir/statement.rs:72-85`). -/
  | nop
  /-- Stack frame liveness start (`AllocaLive`) for a `.memAlloca` local. -/
  | allocaLive (slot : LocalId)
  /-- Stack frame liveness end (`AllocaDead`) for a `.memAlloca` local. -/
  | allocaDead (slot : LocalId)
  /-- Define an SSA register (`LocalRef::PendingOperand -> LocalRef::Operand`,
  `mir/statement.rs:40`). -/
  | defSsaReg (reg : LocalId) (expr : AnLlvmExpr)
  /-- Store to a stack frame slot (`LocalRef::Place`,
  `mir/statement.rs:21-22`). -/
  | storeFrameSlot (slot : LocalId) (expr : AnLlvmExpr)
  /-- Encode a niche discriminant tag into a stack frame slot
  (`codegen_set_discr`, `mir/place.rs:258-274`). -/
  | setSlotDiscrNiche (slot : LocalId) (cfg : NicheConfig) (variantIdx : Nat)
  /-- Conditional assert branch to a panic block (`mir/block.rs:753-858`). -/
  | checkAssertZero (condExpr : AnLlvmExpr) (panicCode : Nat)
  /-- Conditional branch `cond_br` joining at the continuation block. -/
  | condBr (condExpr : AnLlvmExpr)
      (thenInstrs : List AnLlvmInstr) (elseInstrs : List AnLlvmInstr)
  deriving Repr

/-- `AnLLVM` execution environment:
- `ssaRegs`: SSA virtual register file (`LocalRef::Operand`);
- `frameSlots`: stack frame memory slots (`LocalRef::Place`);
- `slotLive`: per-slot `AllocaLive`/`AllocaDead` state;
- `dynamicAllocaCount`: counter tracking any dynamic temporary `alloca`s
  allocated during instruction execution (used by Theorem 3 to prove zero
  temporary `alloca` allocations for `Transmute` and `PassMode::Cast`). -/
structure AnLlvmEnv where
  ssaRegs : LocalId → OperandValue
  frameSlots : LocalId → OperandValue
  slotLive : LocalId → Bool
  dynamicAllocaCount : Nat

/-- Write an SSA register in `AnLlvmEnv`. -/
def AnLlvmEnv.writeReg (env : AnLlvmEnv) (r : LocalId) (v : OperandValue) :
    AnLlvmEnv :=
  { env with ssaRegs := fun k => if k = r then v else env.ssaRegs k }

/-- Write a stack frame slot in `AnLlvmEnv`. -/
def AnLlvmEnv.writeSlot (env : AnLlvmEnv) (s : LocalId) (v : OperandValue) :
    AnLlvmEnv :=
  { env with frameSlots := fun k => if k = s then v else env.frameSlots k }

/-- Update stack frame slot liveness in `AnLlvmEnv`. -/
def AnLlvmEnv.setSlotLive (env : AnLlvmEnv) (s : LocalId) (isLive : Bool) :
    AnLlvmEnv :=
  { env with slotLive := fun k => if k = s then isLive else env.slotLive k }

/-- Evaluate an `AnLlvmExpr` in `AnLlvmEnv`. -/
def evalAnLlvmExpr (env : AnLlvmEnv) : AnLlvmExpr → OperandValue
  | .constVal v => v
  | .readSsaReg reg => env.ssaRegs reg
  | .loadFrameSlot slot => env.frameSlots slot
  | .projPairFieldSsa reg fieldOne => (env.ssaRegs reg).extractPairField fieldOne
  | .projPairFieldSlot slot fieldOne =>
    (env.frameSlots slot).extractPairField fieldOne
  | .makeScalarPair e0 e1 =>
    .pair (evalAnLlvmExpr env e0).asScalar (evalAnLlvmExpr env e1).asScalar
  | .wrappingAdd64 e0 e1 =>
    let x := (evalAnLlvmExpr env e0).asScalar.toNat
    let y := (evalAnLlvmExpr env e1).asScalar.toNat
    OperandValue.ofU64 ((x + y) % 18446744073709551616)
  | .wrappingSub64 e0 e1 =>
    let x := (evalAnLlvmExpr env e0).asScalar.toNat % 18446744073709551616
    let y := (evalAnLlvmExpr env e1).asScalar.toNat % 18446744073709551616
    OperandValue.ofU64 ((x + 18446744073709551616 - y) % 18446744073709551616)
  | .checkedAdd64 e0 e1 =>
    evalCheckedAdd64 (evalAnLlvmExpr env e0) (evalAnLlvmExpr env e1)
  | .checkedMul64 e0 e1 =>
    evalCheckedMul64 (evalAnLlvmExpr env e0) (evalAnLlvmExpr env e1)
  | .decodeNicheDiscrExpr e cfg =>
    let rawTag := (evalAnLlvmExpr env e).asScalar.toNat
    OperandValue.ofU64 (decodeNicheDiscr cfg rawTag)
  | .bitcastBytes e mode =>
    evalRegisterTransmute mode (evalAnLlvmExpr env e)

/-- Full small-step `AnLLVM` machine state. -/
structure AnLlvmState where
  instrs : List AnLlvmInstr
  env : AnLlvmEnv
  status : ExecStatus

/-- Execute a single `AnLlvmInstr` at the head of an instruction list. -/
def stepAnLlvmInstr (i : AnLlvmInstr) (rest : List AnLlvmInstr)
    (env : AnLlvmEnv) : List AnLlvmInstr × AnLlvmEnv × ExecStatus :=
  match i with
  | .nop => (rest, env, .running)
  | .allocaLive s => (rest, env.setSlotLive s true, .running)
  | .allocaDead s =>
    (rest, (env.setSlotLive s false).writeSlot s (.imm MaskedWord64.uninit), .running)
  | .defSsaReg r expr => (rest, env.writeReg r (evalAnLlvmExpr env expr), .running)
  | .storeFrameSlot s expr =>
    (rest, env.writeSlot s (evalAnLlvmExpr env expr), .running)
  | .setSlotDiscrNiche s cfg variantIdx =>
    let newVal :=
      if variantIdx = cfg.untaggedVariant then
        env.frameSlots s
      else
        OperandValue.ofU64 (encodeNicheTag cfg variantIdx)
    (rest, env.writeSlot s newVal, .running)
  | .checkAssertZero condExpr panicCode =>
    if (evalAnLlvmExpr env condExpr).asScalar.toNat = 0 then
      (rest, env, .running)
    else
      ([], env, .panicked panicCode)
  | .condBr condExpr thenInstrs elseInstrs =>
    if (evalAnLlvmExpr env condExpr).asScalar.toNat ≠ 0 then
      (thenInstrs ++ rest, env, .running)
    else
      (elseInstrs ++ rest, env, .running)

/-- Lower a `LocalId` read according to its `LocalKind` (`mir/operand.rs` /
`mir/statement.rs`): `.ssaOperand` reads `ssaRegs`, while `.memAlloca` loads
from `frameSlots`. -/
def lowerLocalRead (kinds : LocalClassification) (l : LocalId) : AnLlvmExpr :=
  match kinds l with
  | .ssaOperand => .readSsaReg l
  | .memAlloca => .loadFrameSlot l

/-- Lower a `MirRvalue` to an `AnLlvmExpr` using `kinds : LocalClassification`,
modeling `FunctionCx::codegen_rvalue_operand` (`mir/rvalue.rs:495-858`). -/
def lowerMirRvalue (kinds : LocalClassification) (rv : MirRvalue) : AnLlvmExpr :=
  match rv with
  | .constVal v => .constVal v
  | .useLocal src => lowerLocalRead kinds src
  | .projPairField src fieldOne =>
    match kinds src with
    | .ssaOperand => .projPairFieldSsa src fieldOne
    | .memAlloca => .projPairFieldSlot src fieldOne
  | .makeScalarPair src0 src1 =>
    .makeScalarPair (lowerLocalRead kinds src0) (lowerLocalRead kinds src1)
  | .wrappingAdd64 lhs rhs =>
    .wrappingAdd64 (lowerLocalRead kinds lhs) (lowerLocalRead kinds rhs)
  | .wrappingSub64 lhs rhs =>
    .wrappingSub64 (lowerLocalRead kinds lhs) (lowerLocalRead kinds rhs)
  | .checkedAdd64 lhs rhs =>
    .checkedAdd64 (lowerLocalRead kinds lhs) (lowerLocalRead kinds rhs)
  | .checkedMul64 lhs rhs =>
    .checkedMul64 (lowerLocalRead kinds lhs) (lowerLocalRead kinds rhs)
  | .discriminantNiche src cfg =>
    .decodeNicheDiscrExpr (lowerLocalRead kinds src) cfg
  | .transmuteReg src mode =>
    .bitcastBytes (lowerLocalRead kinds src) mode

/-- Lower a `MirStmt` to an `AnLlvmInstr` using `kinds : LocalClassification`,
modeling `FunctionCx::codegen_statement` (`mir/statement.rs:11-123`) and
`FunctionCx::codegen_block` (`mir/block.rs:1586-1625`). -/
def lowerMirStmt (kinds : LocalClassification) : MirStmt → AnLlvmInstr
  | .storageLive l =>
    match kinds l with
    | .ssaOperand => .nop
    | .memAlloca => .allocaLive l
  | .storageDead l =>
    match kinds l with
    | .ssaOperand => .nop
    | .memAlloca => .allocaDead l
  | .assignSsa dst rv =>
    match kinds dst with
    | .ssaOperand => .defSsaReg dst (lowerMirRvalue kinds rv)
    | .memAlloca => .storeFrameSlot dst (lowerMirRvalue kinds rv)
  | .storePlace dst rv =>
    .storeFrameSlot dst (lowerMirRvalue kinds rv)
  | .setDiscriminantNiche dst cfg variantIdx =>
    .setSlotDiscrNiche dst cfg variantIdx
  | .assertZero condLocal panicCode =>
    .checkAssertZero (lowerLocalRead kinds condLocal) panicCode
  | .condBranch condLocal thenBranch elseBranch =>
    .condBr (lowerLocalRead kinds condLocal)
      (thenBranch.map (lowerMirStmt kinds))
      (elseBranch.map (lowerMirStmt kinds))

/-- Lower a list of `MirStmt`s to `AnLlvmInstr`s. -/
def lowerMirStmts (kinds : LocalClassification) (stmts : List MirStmt) :
    List AnLlvmInstr :=
  stmts.map (lowerMirStmt kinds)

/-!
## Section 5: Theorem 1 (`analyze_local_ssa_vs_alloca_simulation`)

We now state the structural well-formedness predicate enforced by
`compiler/rustc_codegen_ssa/src/mir/analyze.rs` (`LocalAnalyzer`):

- In `analyze.rs:193-267`, any local that undergoes `MutatingUse::Store`,
  `MutatingUse::SetDiscriminant`, `MutatingUse::Borrow`,
  `MutatingUse::RawBorrow`, or `MutatingUse::Projection` is immediately assigned
  `LocalKind::Memory` (`.memAlloca`).
- Furthermore, `StorageLive`/`StorageDead` only affect memory-backed
  `LocalRef::Place` locals (`mir/statement.rs:72-85`), because SSA
  `LocalRef::Operand` values are dominating single-assignment registers that are
  never accessed after `StorageDead`.

We formalize `StmtRespectsLocalAnalysis kinds s` to express these invariants and
prove that `lowerMirStmts kinds` refines `stmts` in lockstep.
-/

/-- Inductive predicate stating that a `MirStmt` respects the
`LocalClassification` computed by `rustc_codegen_ssa/src/mir/analyze.rs`:
1. `storePlace` and `setDiscriminantNiche` only target `.memAlloca` locals
   (`analyze.rs:236-251`).
2. `storageLive` and `storageDead` only target `.memAlloca` locals.
3. Nested branches recursively respect `kinds`. -/
inductive StmtRespectsLocalAnalysis (kinds : LocalClassification) :
    MirStmt → Prop where
  | storageLive {l : LocalId} (h : kinds l = .memAlloca) :
      StmtRespectsLocalAnalysis kinds (.storageLive l)
  | storageDead {l : LocalId} (h : kinds l = .memAlloca) :
      StmtRespectsLocalAnalysis kinds (.storageDead l)
  | assignSsa (dst : LocalId) (rv : MirRvalue) :
      StmtRespectsLocalAnalysis kinds (.assignSsa dst rv)
  | storePlace {dst : LocalId} (rv : MirRvalue) (h : kinds dst = .memAlloca) :
      StmtRespectsLocalAnalysis kinds (.storePlace dst rv)
  | setDiscriminantNiche {dst : LocalId} (cfg : NicheConfig) (variantIdx : Nat)
      (h : kinds dst = .memAlloca) :
      StmtRespectsLocalAnalysis kinds (.setDiscriminantNiche dst cfg variantIdx)
  | assertZero (condLocal : LocalId) (panicCode : Nat) :
      StmtRespectsLocalAnalysis kinds (.assertZero condLocal panicCode)
  | condBranch (condLocal : LocalId) (thenBranch elseBranch : List MirStmt)
      (hthen : ∀ s ∈ thenBranch, StmtRespectsLocalAnalysis kinds s)
      (helse : ∀ s ∈ elseBranch, StmtRespectsLocalAnalysis kinds s) :
      StmtRespectsLocalAnalysis kinds (.condBranch condLocal thenBranch elseBranch)

/-- All statements in a list respect `kinds : LocalClassification`. -/
def StmtsRespectLocalAnalysis (kinds : LocalClassification)
    (stmts : List MirStmt) : Prop :=
  ∀ s ∈ stmts, StmtRespectsLocalAnalysis kinds s

/-- Append preserves `StmtsRespectLocalAnalysis`. -/
theorem StmtsRespectLocalAnalysis.append {kinds : LocalClassification}
    {s1 s2 : List MirStmt}
    (h1 : StmtsRespectLocalAnalysis kinds s1)
    (h2 : StmtsRespectLocalAnalysis kinds s2) :
    StmtsRespectLocalAnalysis kinds (s1 ++ s2) := by
  intro s hs
  rcases List.mem_append.mp hs with hs1 | hs2
  · exact h1 s hs1
  · exact h2 s hs2

/-- Environment simulation relation between `MirEnv` and `AnLlvmEnv`
parameterized by `kinds : LocalClassification`:
- Every `.ssaOperand` local `l` has `mirEnv.locals l = llvmEnv.ssaRegs l`.
- Every `.memAlloca` local `l` has `mirEnv.locals l = llvmEnv.frameSlots l` and
  `mirEnv.live l = llvmEnv.slotLive l`. -/
structure EnvSimRel (kinds : LocalClassification) (mirEnv : MirEnv)
    (llvmEnv : AnLlvmEnv) : Prop where
  ssa_match :
    ∀ l, kinds l = .ssaOperand → mirEnv.locals l = llvmEnv.ssaRegs l
  alloca_val_match :
    ∀ l, kinds l = .memAlloca → mirEnv.locals l = llvmEnv.frameSlots l
  alloca_live_match :
    ∀ l, kinds l = .memAlloca → mirEnv.live l = llvmEnv.slotLive l

/-- Under `EnvSimRel kinds mirEnv llvmEnv`, reading any local `l` via
`lowerLocalRead kinds l` produces the exact `OperandValue` stored in
`mirEnv.locals l`. -/
theorem lowerLocalRead_correct (kinds : LocalClassification)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (hrel : EnvSimRel kinds mirEnv llvmEnv) (l : LocalId) :
    evalAnLlvmExpr llvmEnv (lowerLocalRead kinds l) = mirEnv.locals l := by
  unfold lowerLocalRead
  cases hkind : kinds l with
  | ssaOperand => simp [evalAnLlvmExpr, hrel.ssa_match l hkind]
  | memAlloca => simp [evalAnLlvmExpr, hrel.alloca_val_match l hkind]

/-- Under `EnvSimRel kinds mirEnv llvmEnv`, evaluating `lowerMirRvalue kinds rv`
in `AnLLVM` produces the exact same `OperandValue` as `evalMirRvalue mirEnv rv`
in MIR. -/
theorem lowerMirRvalue_correct (kinds : LocalClassification)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (hrel : EnvSimRel kinds mirEnv llvmEnv) (rv : MirRvalue) :
    evalAnLlvmExpr llvmEnv (lowerMirRvalue kinds rv) = evalMirRvalue mirEnv rv := by
  cases rv with
  | constVal v => rfl
  | useLocal src => exact lowerLocalRead_correct kinds mirEnv llvmEnv hrel src
  | projPairField src fieldOne =>
    unfold lowerMirRvalue evalMirRvalue
    cases hkind : kinds src with
    | ssaOperand => simp [hkind, evalAnLlvmExpr, hrel.ssa_match src hkind]
    | memAlloca => simp [hkind, evalAnLlvmExpr, hrel.alloca_val_match src hkind]
  | makeScalarPair src0 src1 =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel src0,
        lowerLocalRead_correct kinds mirEnv llvmEnv hrel src1]
  | wrappingAdd64 lhs rhs =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel lhs,
        lowerLocalRead_correct kinds mirEnv llvmEnv hrel rhs]
  | wrappingSub64 lhs rhs =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel lhs,
        lowerLocalRead_correct kinds mirEnv llvmEnv hrel rhs]
  | checkedAdd64 lhs rhs =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel lhs,
        lowerLocalRead_correct kinds mirEnv llvmEnv hrel rhs]
  | checkedMul64 lhs rhs =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel lhs,
        lowerLocalRead_correct kinds mirEnv llvmEnv hrel rhs]
  | discriminantNiche src cfg =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel src]
  | transmuteReg src mode =>
    unfold lowerMirRvalue evalMirRvalue evalAnLlvmExpr
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv hrel src]

/-- Writing to a local `dst` preserves `EnvSimRel` when dispatched by
`kinds dst` (`defSsaReg` for `.ssaOperand`, `storeFrameSlot` for
`.memAlloca`). -/
theorem EnvSimRel.write_dispatched (kinds : LocalClassification)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (hrel : EnvSimRel kinds mirEnv llvmEnv)
    (dst : LocalId) (v : OperandValue) :
    EnvSimRel kinds (mirEnv.writeLocal dst v)
      (match kinds dst with
       | .ssaOperand => llvmEnv.writeReg dst v
       | .memAlloca => llvmEnv.writeSlot dst v) := by
  cases hdst : kinds dst with
  | ssaOperand =>
    constructor
    · intro l hl
      unfold MirEnv.writeLocal AnLlvmEnv.writeReg; dsimp only
      by_cases hEq : l = dst
      · subst hEq; simp
      · simp [hEq, hrel.ssa_match l hl]
    · intro l hl
      unfold MirEnv.writeLocal AnLlvmEnv.writeReg; dsimp only
      have hNe : l ≠ dst := by intro hEq; subst hEq; rw [hdst] at hl; contradiction
      simp [hNe, hrel.alloca_val_match l hl]
    · intro l hl; exact hrel.alloca_live_match l hl
  | memAlloca =>
    constructor
    · intro l hl
      unfold MirEnv.writeLocal AnLlvmEnv.writeSlot; dsimp only
      have hNe : l ≠ dst := by intro hEq; subst hEq; rw [hdst] at hl; contradiction
      simp [hNe, hrel.ssa_match l hl]
    · intro l hl
      unfold MirEnv.writeLocal AnLlvmEnv.writeSlot; dsimp only
      by_cases hEq : l = dst
      · subst hEq; simp
      · simp [hEq, hrel.alloca_val_match l hl]
    · intro l hl; exact hrel.alloca_live_match l hl

/-- Writing to a `.memAlloca` local `dst` via `writeSlot` preserves
`EnvSimRel`. -/
theorem EnvSimRel.write_alloca (kinds : LocalClassification)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (hrel : EnvSimRel kinds mirEnv llvmEnv)
    (dst : LocalId) (hdst : kinds dst = .memAlloca) (v : OperandValue) :
    EnvSimRel kinds (mirEnv.writeLocal dst v) (llvmEnv.writeSlot dst v) := by
  have h := EnvSimRel.write_dispatched kinds mirEnv llvmEnv hrel dst v
  rw [hdst] at h; exact h

/-- Updating liveness of a `.memAlloca` local `dst` via `setSlotLive` preserves
`EnvSimRel`. -/
theorem EnvSimRel.setLive_alloca (kinds : LocalClassification)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (hrel : EnvSimRel kinds mirEnv llvmEnv)
    (dst : LocalId) (hdst : kinds dst = .memAlloca) (isLive : Bool) :
    EnvSimRel kinds (mirEnv.setLive dst isLive) (llvmEnv.setSlotLive dst isLive) := by
  constructor
  · intro l hl; exact hrel.ssa_match l hl
  · intro l hl; exact hrel.alloca_val_match l hl
  · intro l hl
    unfold MirEnv.setLive AnLlvmEnv.setSlotLive; dsimp only
    by_cases hEq : l = dst
    · subst hEq; simp
    · simp [hEq, hrel.alloca_live_match l hl]

/-- Full state simulation relation (`MirAnLlvmSimRel`) between `MirState` and
`AnLlvmState`. -/
structure MirAnLlvmSimRel (kinds : LocalClassification) (ms : MirState)
    (ls : AnLlvmState) : Prop where
  stmts_wf : StmtsRespectLocalAnalysis kinds ms.stmts
  instrs_eq : ls.instrs = lowerMirStmts kinds ms.stmts
  env_rel : EnvSimRel kinds ms.env ls.env
  status_eq : ls.status = ms.status

/-- **Theorem 1a (`analyze_local_ssa_vs_alloca_simulation`)**:
Single-step lockstep simulation theorem for `lowerMirStmt`: for any statement
`s` and continuation `rest` respecting `LocalAnalyzer`'s classification `kinds`,
stepping `s` in MIR is matched in lockstep by stepping `lowerMirStmt kinds s` in
`AnLLVM` while preserving `MirAnLlvmSimRel`. -/
theorem analyze_local_ssa_vs_alloca_simulation
    (kinds : LocalClassification)
    (s : MirStmt) (rest : List MirStmt)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (hs_wf : StmtRespectsLocalAnalysis kinds s)
    (hrest_wf : StmtsRespectLocalAnalysis kinds rest)
    (henv : EnvSimRel kinds mirEnv llvmEnv) :
    let (mirStmts', mirEnv', mirStatus') := stepMirStmt s rest mirEnv
    let (llvmInstrs', llvmEnv', llvmStatus') :=
      stepAnLlvmInstr (lowerMirStmt kinds s) (lowerMirStmts kinds rest) llvmEnv
    StmtsRespectLocalAnalysis kinds mirStmts' ∧
    llvmInstrs' = lowerMirStmts kinds mirStmts' ∧
    EnvSimRel kinds mirEnv' llvmEnv' ∧
    llvmStatus' = mirStatus' := by
  cases hs_wf with
  | @storageLive l hl =>
    unfold stepMirStmt lowerMirStmt; rw [hl]; dsimp only [stepAnLlvmInstr]
    exact ⟨hrest_wf, rfl,
           EnvSimRel.setLive_alloca kinds mirEnv llvmEnv henv l hl true, rfl⟩
  | @storageDead l hl =>
    unfold stepMirStmt lowerMirStmt; rw [hl]; dsimp only [stepAnLlvmInstr]
    have hLive := EnvSimRel.setLive_alloca kinds mirEnv llvmEnv henv l hl false
    have hWrite := EnvSimRel.write_alloca kinds (mirEnv.setLive l false)
      (llvmEnv.setSlotLive l false) hLive l hl (.imm MaskedWord64.uninit)
    exact ⟨hrest_wf, rfl, hWrite, rfl⟩
  | assignSsa dst rv =>
    unfold stepMirStmt lowerMirStmt
    have hrv := lowerMirRvalue_correct kinds mirEnv llvmEnv henv rv
    cases hdst : kinds dst with
    | ssaOperand =>
      dsimp only [stepAnLlvmInstr]; rw [hrv]
      have hWrite := EnvSimRel.write_dispatched kinds mirEnv llvmEnv henv dst
        (evalMirRvalue mirEnv rv)
      rw [hdst] at hWrite
      exact ⟨hrest_wf, rfl, hWrite, rfl⟩
    | memAlloca =>
      dsimp only [stepAnLlvmInstr]; rw [hrv]
      have hWrite := EnvSimRel.write_dispatched kinds mirEnv llvmEnv henv dst
        (evalMirRvalue mirEnv rv)
      rw [hdst] at hWrite
      exact ⟨hrest_wf, rfl, hWrite, rfl⟩
  | @storePlace dst rv hdst =>
    unfold stepMirStmt lowerMirStmt; dsimp only [stepAnLlvmInstr]
    rw [lowerMirRvalue_correct kinds mirEnv llvmEnv henv rv]
    have hWrite := EnvSimRel.write_alloca kinds mirEnv llvmEnv henv dst hdst
      (evalMirRvalue mirEnv rv)
    exact ⟨hrest_wf, rfl, hWrite, rfl⟩
  | @setDiscriminantNiche dst cfg variantIdx hdst =>
    unfold stepMirStmt lowerMirStmt; dsimp only [stepAnLlvmInstr]
    rw [← henv.alloca_val_match dst hdst]
    have hWrite := EnvSimRel.write_alloca kinds mirEnv llvmEnv henv dst hdst
      (if variantIdx = cfg.untaggedVariant then mirEnv.locals dst
       else OperandValue.ofU64 (encodeNicheTag cfg variantIdx))
    exact ⟨hrest_wf, rfl, hWrite, rfl⟩
  | assertZero condLocal panicCode =>
    unfold stepMirStmt lowerMirStmt; dsimp only [stepAnLlvmInstr]
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv henv condLocal]
    by_cases hZero : (mirEnv.locals condLocal).asScalar.toNat = 0
    · simp [hZero, hrest_wf, henv]
    · simp [hZero, henv, lowerMirStmts]
      intro stmt hstmt; nomatch hstmt
  | condBranch condLocal thenBranch elseBranch hthen_wf helse_wf =>
    unfold stepMirStmt lowerMirStmt; dsimp only [stepAnLlvmInstr]
    rw [lowerLocalRead_correct kinds mirEnv llvmEnv henv condLocal]
    by_cases hCond : (mirEnv.locals condLocal).asScalar.toNat ≠ 0
    · simp [hCond, lowerMirStmts, List.map_append,
            StmtsRespectLocalAnalysis.append hthen_wf hrest_wf, henv]
    · simp [hCond, lowerMirStmts, List.map_append,
            StmtsRespectLocalAnalysis.append helse_wf hrest_wf, henv]

/-- Package MIR and `AnLLVM` as `Language`s with small-step `Semantics` to prove
`Compiles MirLang AnLLVMLang`. -/
def MirLang : Language := { Prog := List MirStmt, State := MirState }

def AnLLVMLang : Language := { Prog := List AnLlvmInstr, State := AnLlvmState }

def MirSemantics : Semantics MirLang where
  step _ s1 s2 :=
    s1.status = .running ∧
    match s1.stmts with
    | [] => False
    | stmt :: rest =>
      let (stmts', env', status') := stepMirStmt stmt rest s1.env
      s2 = { stmts := stmts', env := env', status := status' }
  isTerminal s := s.status ≠ .running ∨ s.stmts = []

def AnLLVMSemantics : Semantics AnLLVMLang where
  step _ s1 s2 :=
    s1.status = .running ∧
    match s1.instrs with
    | [] => False
    | instr :: rest =>
      let (instrs', env', status') := stepAnLlvmInstr instr rest s1.env
      s2 = { instrs := instrs', env := env', status := status' }
  isTerminal s := s.status ≠ .running ∨ s.instrs = []

/-- Simulation codec relating `MirState` and `AnLlvmState` under
`kinds : LocalClassification`. -/
def mirToAnLlvmCodec (kinds : LocalClassification) :
    SimCodec MirLang AnLLVMLang where
  stateRel := MirAnLlvmSimRel kinds

/-- **Theorem 1b (`lowerMirToAnLlvm_compiles`)**:
Full `Compiles` refinement theorem proving that `lowerMirStmts kinds body`
refines any MIR `body` in lockstep under `mirToAnLlvmCodec kinds`. -/
theorem lowerMirToAnLlvm_compiles (kinds : LocalClassification)
    (body : List MirStmt) :
    Compiles MirLang AnLLVMLang MirSemantics AnLLVMSemantics
      (mirToAnLlvmCodec kinds) body (lowerMirStmts kinds body) := by
  constructor
  · intro s1 s1' s2 hrel hstep
    rcases hstep with ⟨hrun, hstepBody⟩
    cases hstmts : s1.stmts with
    | nil => rw [hstmts] at hstepBody; nomatch hstepBody
    | cons stmt rest =>
      rw [hstmts] at hstepBody
      have hwfAll := hrel.stmts_wf; rw [hstmts] at hwfAll
      have hs_wf : StmtRespectsLocalAnalysis kinds stmt :=
        hwfAll stmt (List.Mem.head rest)
      have hrest_wf : StmtsRespectLocalAnalysis kinds rest := by
        intro s hs; exact hwfAll s (List.Mem.tail stmt hs)
      have hsim := analyze_local_ssa_vs_alloca_simulation
        kinds stmt rest s1.env s2.env hs_wf hrest_wf hrel.env_rel
      dsimp only at hsim
      rcases hsim with ⟨hwf', hinstrs', henv', hstatus'⟩
      let next := stepAnLlvmInstr (lowerMirStmt kinds stmt)
        (lowerMirStmts kinds rest) s2.env
      refine ⟨{ instrs := next.1, env := next.2.1, status := next.2.2 }, ?_, ?_⟩
      · constructor
        · rw [hrel.status_eq]; exact hrun
        · have hinstrsEq := hrel.instrs_eq; rw [hstmts] at hinstrsEq
          dsimp only [lowerMirStmts, List.map] at hinstrsEq
          rw [hinstrsEq]; rfl
      · subst hstepBody
        exact { stmts_wf := hwf', instrs_eq := hinstrs'
                env_rel := henv', status_eq := hstatus' }
  · intro s1 s2 hrel hterm
    rcases hterm with hnotRun | hnil
    · left; rw [hrel.status_eq]; exact hnotRun
    · right; rw [hrel.instrs_eq, hnil]; rfl

/-!
## Section 6: Theorem 3 (`register_transmute_and_cast_eliminates_alloca`)

We now prove that `AnLLVM`'s `MaskedWord64` register-level `bitcastBytes` and
`packPaddedToWord64` / `unpackWord64ToPadded` operations:

1. Refine MIR `Rvalue::Cast(CastKind::Transmute)` and `PassMode::Cast` in a
   single step while allocating **zero** dynamic stack `alloca`s
   (`dynamicAllocaCount` is unchanged, vs. upstream `rustc_codegen_ssa`'s 1–2
   temporary `alloca`s per cast/transmute at `mir/rvalue.rs:421-439` and
   `mir/block.rs:2058-2098`).
2. Preserve exact per-byte values and initialization masks (`init : Bool`)
   across round-trips—specifically ensuring that uninitialized struct padding
   bytes at offsets `1..4` of `PaddedReprC` remain `init = false` without
   poisoning the adjacent initialized fields `a : u8` (offset 0) and `b : u32`
   (offsets `4..8`).
-/

/-- Exact round-trip identity for `PassMode::Cast` register packing and
unpacking on any `PaddedReprC` layout (including arbitrary uninitialized padding
masks). -/
theorem pack_unpack_padded_roundtrip (p : PaddedReprC) :
    unpackWord64ToPadded (packPaddedToWord64 p) = p := by
  cases p; rfl

/-- Packing `PaddedReprC.mkInit a b` into a single 64-bit `AnLLVM` register
preserves:
- `a` as an initialized byte (`init = true, val = a % 256`) at byte offset 0;
- uninitialized padding (`init = false`) at byte offsets 1, 2, and 3;
- `b` as 4 initialized bytes (`isFullyInit = true`) at byte offsets 4..7. -/
theorem pack_padded_preserves_byte_init_masks (a b : Nat) :
    let w := packPaddedToWord64 (PaddedReprC.mkInit a b)
    w.lo.b0 = MaskedByte.ofNat a ∧
    w.lo.b0.init = true ∧
    w.lo.b1.init = false ∧
    w.lo.b2.init = false ∧
    w.lo.b3.init = false ∧
    w.hi = MaskedWord32.ofU32 b ∧
    w.hi.isFullyInit = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact round-trip identity for `(u32, u32) <-> u64` register-level transmute
on `MaskedWord32` pairs. -/
theorem pack_unpack_pair32_roundtrip (lo hi : MaskedWord32) :
    unpackWord64ToPair32 (packPair32ToWord64 lo hi) = (lo, hi) := rfl

/-- **Theorem 3 (`register_transmute_and_cast_eliminates_alloca`)**:
Lowering `MirStmt.assignSsa dst (.transmuteReg src mode)` to `AnLLVM` when `src`
and `dst` are `.ssaOperand`s:
1. Executes in a single `AnLLVM` step (`AnLLVMSemantics.step`);
2. Produces the exact MIR transmute/cast result in `llvmEnv'.ssaRegs dst`;
3. Allocates **zero** stack `alloca`s (`dynamicAllocaCount` and `frameSlots` are
   unchanged);
4. Preserves per-byte initialization masks across padded structs
   (`pack_unpack_padded_roundtrip`). -/
theorem register_transmute_and_cast_eliminates_alloca
    (kinds : LocalClassification)
    (src dst : LocalId)
    (mode : TransmuteMode)
    (hsrc : kinds src = .ssaOperand)
    (hdst : kinds dst = .ssaOperand)
    (mirEnv : MirEnv) (llvmEnv : AnLlvmEnv)
    (henv : EnvSimRel kinds mirEnv llvmEnv) :
    let mirStmt := MirStmt.assignSsa dst (.transmuteReg src mode)
    let llvmInstr := lowerMirStmt kinds mirStmt
    let (_, mirEnv', _) := stepMirStmt mirStmt [] mirEnv
    let (_, llvmEnv', _) := stepAnLlvmInstr llvmInstr [] llvmEnv
    llvmInstr = .defSsaReg dst (.bitcastBytes (.readSsaReg src) mode) ∧
    llvmEnv'.ssaRegs dst = mirEnv'.locals dst ∧
    llvmEnv'.dynamicAllocaCount = llvmEnv.dynamicAllocaCount ∧
    llvmEnv'.frameSlots = llvmEnv.frameSlots ∧
    (∀ p : PaddedReprC, unpackWord64ToPadded (packPaddedToWord64 p) = p) := by
  dsimp only
  have hsim := analyze_local_ssa_vs_alloca_simulation
    kinds (MirStmt.assignSsa dst (.transmuteReg src mode)) []
    mirEnv llvmEnv (.assignSsa dst (.transmuteReg src mode))
    (by intro s hs; nomatch hs) henv
  dsimp only at hsim
  rcases hsim with ⟨_, _, henv', _⟩
  refine ⟨?_, ?_, ?_, ?_, pack_unpack_padded_roundtrip⟩
  · simp [lowerMirStmt, lowerMirRvalue, lowerLocalRead, hdst, hsrc]
  · exact (henv'.ssa_match dst hdst).symm
  · unfold lowerMirStmt; rw [hdst]; rfl
  · unfold lowerMirStmt; rw [hdst]; rfl

/-!
## Section 7: Negative Canary (`canary_multi_def_local_as_ssa`)

Why does `compiler/rustc_codegen_ssa/src/mir/analyze.rs` demote any local with
more than one definition (`LocalAnalyzer::define`, `mir/analyze.rs:75-94`) to
`LocalKind::Memory` (`LocalRef::Place`) instead of keeping it as
`LocalRef::Operand`?

Because `FunctionCx` (`mir/mod.rs:52-130`) holds a single compile-time array
`locals: IndexVec<Local, LocalRef<'tcx, Bx::Value>>` and lowers basic blocks in
a single reverse-postorder pass (`mir/mod.rs:380-383`) without inserting SSA
$\phi$ nodes! When a local `l` is represented as `LocalRef::Operand`, assigning
to `l` calls `fx.overwrite_local(l, LocalRef::Operand(op))`
(`mir/statement.rs:40`), which overwrites the compile-time table entry
`fx.locals[l]`.

If a local `acc` is mutated in both branches of an
`if cond { acc = x + y } else { acc = x - y }` and then read in the join block,
codegenning `bbThen` followed by `bbElse` in RPO order leaves `fx.locals[acc]`
pointing to `bbElse`'s SSA register (`x - y`). When `bbJoin` is subsequently
codegenned, its read of `acc` resolves to `bbElse`'s SSA register even when
`cond = true` at runtime!

We formalize this exact compile-time static-SSA-table lowering below and prove
that classifying `acc` as `.ssaOperand` across a branched mutation without
`alloca` or $\phi$ placement violates simulation
(`canary_multi_def_local_as_ssa_without_phi_unsound`).
-/

/-- Compile-time static SSA register mapping (`FunctionCx.locals` in
`mir/mod.rs:124`): maps each `.ssaOperand` local to the SSA register ID assigned
by the most recently codegenned definition in RPO block traversal order. -/
abbrev StaticSsaMap := LocalId → Nat

/-- Buggy single-pass RPO lowering that attempts to keep a multi-def branched
local in `StaticSsaMap` without `alloca` or $\phi$ nodes at the join block:
- Codegenning `thenBranch` updates `ssaMap` to `ssaMapThen` (allocating fresh
  SSA register ID `accThenReg`);
- Codegenning `elseBranch` next in RPO order overwrites `ssaMap` to `ssaMapElse`
  (allocating fresh SSA register ID `accElseReg`);
- Codegenning the join continuation `rest` after `condBranch` therefore resolves
  any `.ssaOperand` local `l` to `ssaMapElse l` (the last-codegenned branch in
  RPO!). -/
def buggyRpoCodegenBranch
    (condReg : Nat)
    (accThenReg accElseReg outReg : Nat)
    (xReg yReg : Nat) : List AnLlvmInstr :=
  [ .condBr (.readSsaReg condReg)
      -- `bbThen` defines `accThenReg := x + y`
      [ .defSsaReg accThenReg
          (.wrappingAdd64 (.readSsaReg xReg) (.readSsaReg yReg)) ]
      -- `bbElse` (codegenned second in RPO) defines `accElseReg := x - y`
      [ .defSsaReg accElseReg
          (.wrappingSub64 (.readSsaReg xReg) (.readSsaReg yReg)) ],
    -- `bbJoin` (codegenned third in RPO) reads `acc`'s current
    -- `FunctionCx.locals[acc]` entry, overwritten by `bbElse` to `accElseReg`!
    .defSsaReg outReg (.readSsaReg accElseReg) ]

/-- The source MIR program for the branched accumulator:
```rust
if cond {
    acc = x.wrapping_add(y);
} else {
    acc = x.wrapping_sub(y);
}
out = acc;
```
-/
def branchedAccMirProg (condLocal xLocal yLocal accLocal outLocal : LocalId) :
    List MirStmt :=
  [ .condBranch condLocal
      [ .storePlace accLocal (.wrappingAdd64 xLocal yLocal) ]
      [ .storePlace accLocal (.wrappingSub64 xLocal yLocal) ],
    .assignSsa outLocal (.useLocal accLocal) ]

/-- **Negative Canary (`canary_multi_def_local_as_ssa_without_phi_unsound`)**:
When `cond = 1` (`true`), `x = 10`, and `y = 3`:
1. The source MIR program `branchedAccMirProg` takes the `then` branch and
   computes `out = 10 + 3 = 13`.
2. Lowering `branchedAccMirProg` via `lowerMirStmts` with `acc` classified as
   `.memAlloca` (as `rustc_codegen_ssa/src/mir/analyze.rs` requires) computes
   the exact matching result `out = 13`.
3. By contrast, lowering `acc` as a static RPO `.ssaOperand` without `alloca` or
   $\phi$ nodes (`buggyRpoCodegenBranch`) causes the join block to read the
   unexecuted `else` branch's register (`accElseReg = 0`), producing a result
   (`0 ≠ 13`) that disagrees with the MIR semantics! -/
theorem canary_multi_def_local_as_ssa_without_phi_unsound :
    let condLocal : LocalId := 1
    let xLocal : LocalId := 2
    let yLocal : LocalId := 3
    let accLocal : LocalId := 4
    let outLocal : LocalId := 0
    let initMirEnv : MirEnv :=
      { locals := fun l =>
          if l = condLocal then OperandValue.ofU64 1
          else if l = xLocal then OperandValue.ofU64 10
          else if l = yLocal then OperandValue.ofU64 3
          else OperandValue.ofU64 0
        live := fun _ => true }
    let initLlvmEnv : AnLlvmEnv :=
      { ssaRegs := initMirEnv.locals
        frameSlots := initMirEnv.locals
        slotLive := fun _ => true
        dynamicAllocaCount := 0 }
    -- Step the 3 statements of `branchedAccMirProg`:
    -- 1. `condBranch` (selects `thenBranch` since `cond = 1`)
    -- 2. `acc := x + y` (`10 + 3 = 13`)
    -- 3. `out := acc` (`13`)
    let (s1, env1, _) := stepMirStmt
      (.condBranch condLocal
        [ .storePlace accLocal (.wrappingAdd64 xLocal yLocal) ]
        [ .storePlace accLocal (.wrappingSub64 xLocal yLocal) ])
      [ .assignSsa outLocal (.useLocal accLocal) ]
      initMirEnv
    let (_, env2, _) := stepMirStmt
      (.storePlace accLocal (.wrappingAdd64 xLocal yLocal))
      [ .assignSsa outLocal (.useLocal accLocal) ]
      env1
    let (_, mirFinalEnv, _) := stepMirStmt
      (.assignSsa outLocal (.useLocal accLocal))
      []
      env2
    -- Step the buggy RPO SSA lowering (`buggyRpoCodegenBranch`) where
    -- `accThenReg = 4` and `accElseReg = 5`:
    let (_, lenv1, _) := stepAnLlvmInstr
      (.condBr (.readSsaReg condLocal)
        [ .defSsaReg 4 (.wrappingAdd64 (.readSsaReg xLocal) (.readSsaReg yLocal)) ]
        [ .defSsaReg 5 (.wrappingSub64 (.readSsaReg xLocal) (.readSsaReg yLocal)) ])
      [ .defSsaReg outLocal (.readSsaReg 5) ]
      initLlvmEnv
    let (_, lenv2, _) := stepAnLlvmInstr
      (.defSsaReg 4 (.wrappingAdd64 (.readSsaReg xLocal) (.readSsaReg yLocal)))
      [ .defSsaReg outLocal (.readSsaReg 5) ]
      lenv1
    let (_, buggyFinalEnv, _) := stepAnLlvmInstr
      (.defSsaReg outLocal (.readSsaReg 5))
      []
      lenv2
    s1 = [ .storePlace accLocal (.wrappingAdd64 xLocal yLocal),
           .assignSsa outLocal (.useLocal accLocal) ] ∧
    (mirFinalEnv.locals outLocal).asScalar.toNat = 13 ∧
    (buggyFinalEnv.ssaRegs outLocal).asScalar.toNat = 0 ∧
    buggyFinalEnv.ssaRegs outLocal ≠ mirFinalEnv.locals outLocal := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide

/-!
## Section 8: Kernel Axiom Verification (`#guard_msgs in #print axioms`)

Every theorem in this probe is verified free of `sorryAx` and
`Lean.ofReduceBool`.
-/

/-- info: 'Round1Track3MirToAnLlvmProbe.analyze_local_ssa_vs_alloca_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms analyze_local_ssa_vs_alloca_simulation

/-- info: 'Round1Track3MirToAnLlvmProbe.lowerMirToAnLlvm_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lowerMirToAnLlvm_compiles

/-- info: 'Round1Track3MirToAnLlvmProbe.codegen_get_set_discr_niche_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms codegen_get_set_discr_niche_roundtrip

/-- info: 'Round1Track3MirToAnLlvmProbe.register_transmute_and_cast_eliminates_alloca' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms register_transmute_and_cast_eliminates_alloca

/-- info: 'Round1Track3MirToAnLlvmProbe.canary_multi_def_local_as_ssa_without_phi_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_multi_def_local_as_ssa_without_phi_unsound

end Round1Track3MirToAnLlvmProbe
