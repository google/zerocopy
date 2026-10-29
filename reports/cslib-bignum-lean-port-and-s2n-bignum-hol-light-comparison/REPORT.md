# `cslib-community/bignum` Lean 4 Port of `s2n-bignum`, Comparison with HOL Light and Kraken, and Anneal Assembly Bridge Synthesis

## Summary

This report presents a primary-source architectural audit of [`cslib-community/bignum`](https://github.com/cslib-community/bignum) at commit `92dc3ee58280db51bbbb4dd51b85a91abd0178ba` (observed 2026-10-29; last upstream commit 2026-10-28), compares its Lean 4 formalization line-by-line against its upstream HOL Light source [`awslabs/s2n-bignum`](https://github.com/awslabs/s2n-bignum) (`9f2cd960e11892a582e7facb0c191b4a2959ea91` and corpus baseline `4d1356a7470663c752660a59375dc3a9ef548428`) and [`AeneasVerif/kraken`](https://github.com/AeneasVerif/kraken) (`c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`), and mechanizes the bridge from `s2n-bignum`/`cslib-community/bignum` relational specifications into Anneal's (`joshlf/anneal-private` at `42f4571d761b46c7142815f38b69c3781b3555e3`) Layer 1A/1B `SmallStepMachine` and `Language.SpecOn` refinement hierarchy.

The principal findings are:

1. **Scope and Maturity of `cslib-community/bignum` (`92dc3ee58280db51bbbb4dd51b85a91abd0178ba`):** The repository is an early-stage, foundational Lean 4 (`v4.36.0-rc1`, `requiresModuleSystem = true`, depending on `leanprover-community/batteries`) port of `s2n-bignum`'s common relational/component infrastructure and a minimal AArch64 core. Across 37 Lean source and test files (2,331 lines total), it ports the `Component` lens hierarchy (`Bignum/Component/`), total byte-addressed `Memory` (`Bignum/Memory/`), relational Hoare logic (`Eventually`, `Ensures`, `MayChange` in `Bignum/Relational/` and `Bignum/Component/Relational.lean`), `match_bv` bit-pattern decoding (`Bignum/BitVec/MatchBV.lean`, adapted from `lean-mlir`/AWS `LNSym`), and an AArch64 `State`/`Decode`/`Semantics` skeleton (`Bignum/Arm/`). Zero x86_64 files and zero cryptographic bignum proofs have been ported yet.
2. **Primary-Source Diagnosis of the Unprovable `Simple.lean` Tutorial Theorem:** The repository contains exactly one active `sorry` (`BignumTest/Tutorial/Simple.lean:28`, `simple_spec`, porting `s2n-bignum/arm/tutorial/simple.ml:23-32`) and two commented-out `sorry` lemmas in `Bignum/Memory/Lemmas.lean` (`writeBytesLE_take_padright` at lines 290–308 and `readBytesLE_writeBytesLE` at lines 447–451). We prove in [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean) (`upstream_simple_stuck_at_entry`) that `simple_spec` is **mathematically unprovable as stated** against `Bignum/Arm/Decode.lean` at `92dc3ee58`: `simple` loads `0x8b000022` (`add x2, x1, x0`) and `0xcb010042` (`sub x2, x2, x1`), which belong to the AArch64 **Add/subtract (shifted register)** encoding class (`bits[28:24] = 0b01011`), whereas `Bignum/Arm/Decode.lean:37-46` implements only a single `match_bv` arm for **Add/subtract (immediate)** (`bits[28:23] = 0b100010`). Consequently, `Decode.decode` returns `none` on both words (`upstream_decode_simple_word0_is_none`, `upstream_decode_simple_word1_is_none`), `s.decode (s.read PC)` is uninhabited, and `arm` is stuck (`¬ ∃ s', upstreamArm s s'`). Extending the decoder with the shifted-register arm allows `simple_spec` to be proved with zero `sorry` (`simple_spec_proven`).
3. **Rapid October 2026 Stabilization of `Eventually` and `Ensures`:** Between 2026-10-21 and 2026-10-28, `cslib-community/bignum` corrected two foundational specification bugs in `Bignum/Relational/Basic.lean`:
   - Commit `5c042a0` (2026-10-21) originally parameterized `Ensures` by a single state `(a : α)` (`pre a → step.Eventually (fun a' ↦ post a' ∧ frame a a') a`), which prevented sequential composition (`ensures_trans`); commit `d05fddf` (2026-10-22) changed `Ensures` to universally quantify over the initial state (`∀ a, pre a → ...`), matching `s2n-bignum`'s `ensures` (`common/relational.ml:1240`).
   - Commit `326f811` / `92dc3ee` (2026-10-28) restored universal successor quantification `hss : ∀ a', step a a' → step.Eventually P a'` alongside existential progress `hs : ∃ a', step a a'` in `Eventually.step` and proved `ensures_frame_invariant` and `ensures_trans`.
   - Commit `997b904` (2026-10-27) deleted the earlier prototype `Bignum/ArmOld/` (`ArmOld/Machine.lean`, `ArmOld/Spec.lean`, `ArmOld/Tutorial.lean`) in favor of the `Component`-based `Bignum/Arm/` architecture.
4. **`Component` Lens Algebra Findings (Homogeneous `MayChange`, `Orthogonal.symm` Typo, and Missing Frame-Preservation Lemmas):**
   - Because Lean's `List` is homogeneously typed, `MayChange : List (Component α β) → Relation α α` (`Bignum/Component/Relational.lean:26`) can only group components sharing a single value type `β` in one list (e.g., `MayChange [PC, X2]` where both have type `Component State (BitVec 64)`). Heterogeneous frames spanning 64-bit general-purpose registers, 128-bit SIMD registers, 1-bit flags, byte-slice memory lenses, and `List (UArchEvent 64)` traces must be chained across `Relation.Seq` (`,,`), mirroring `s2n-bignum`'s `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` (`arm/proofs/instruction.ml:652-658`).
   - In `Bignum/Component/Basic.lean:111`, `Orthogonal.symm` is accidentally restricted to `cp₁ cp₂ : Component α β` (same codomain `β`), even though `class Orthogonal (cp₁ : Component α β) (cp₂ : Component α γ)` (line 105) is heterogeneous in `β` and `γ`.
   - At `92dc3ee58`, `Bignum/Component/RelationalLemmas.lean` proves `assign_valid`, `assign_weaklyValid`, `assigns_id`, and `mayChange_idem`, but does **not** yet prove the fundamental frame-preservation theorem connecting `Orthogonal` to `Assigns` and `MayChange`. We state and prove `Assigns_preserves_orthogonal`, `MayChange_preserves_orthogonal`, and `Seq_preserves_read` in [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean).
5. **Anneal (`joshlf/anneal-private`) Bridge Synthesis (`Issue #102`):** We prove (`ensuresN_safety_refines_anneal_specOn`) that an `s2n-bignum`/`cslib-community/bignum` step-indexed `EnsuresN + Safety` contract—combining functional postcondition `post`, `MayChange` clobber frame orthogonal to ABI-preserved registers/flags, and `memaccess_inbounds` containment over emitted `UArchEvent`s—soundly discharges Anneal's guarded `SmallStepMachine` transition (`Trusted/StepResult.lean`) and refines `Language.SpecOn` (`Trusted/Refinement.lean`) across all finite step budgets `q.steps`. Conversely, we prove (`mayChange_alone_cannot_exclude_unauthorized_load`) that `Ensures` with `MayChange` *alone* (without `Safety`/`memaccess_inbounds`) is unsound as an Anneal MIR-to-assembly bridge because `MayChange` constrains only net state modifications between entry and exit and cannot detect unauthorized memory reads (`EventLoad`) or transient out-of-bounds scratch writes that restore original bytes before exit.

## Applicability

This report applies directly to:

- **Anneal (`joshlf/anneal-private` at `42f4571d761b46c7142815f38b69c3781b3555e3`):**
  - `trusted/lean/Trusted/Refinement.lean` (Layer 1A: `Partial`, `Preorder`, `Behavior`, `Outcome`, `Outcome.Satisfies`, `Language`, `Language.SpecOn`).
  - `trusted/lean/Trusted/StepResult.lean` (Layer 1B: `StepResult`, `PrefixOutcome`, `SmallStepMachine`, `ReachesPrefix`, `SmallStepMachine.BehaviorOf`, `SmallStepMachine.toLanguage`).
  - `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` (Layer 2 MIR syntax and semantics, specifically `Issue #102` on inline and global assembly integration).
- **Primary-Source Upstream Targets:**
  - `cslib-community/bignum` at `92dc3ee58280db51bbbb4dd51b85a91abd0178ba` (Lean `v4.36.0-rc1`).
  - `awslabs/s2n-bignum` at `9f2cd960e11892a582e7facb0c191b4a2959ea91` (and prior reference baseline `4d1356a7470663c752660a59375dc3a9ef548428`).
  - `AeneasVerif/kraken` at `c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0` (Lean `v4.34.1`).
- **Companion Reference Reports in this Corpus:**
  - `reports/hol-light-s2n-bignum-add-native-replay-b19af693/`
  - `reports/jasmin-vale-s2n-artifact-and-access-boundaries/`
  - `reports/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/`
  - `reports/kraken-wp-foundation-directive-refactor-and-syntax-elaborators-c9aa45e/`
  - `reports/rust-inline-global-assembly-nightly-2026-05-31/`

## Findings

### 1. Complete Architectural Inventory of `cslib-community/bignum` (`92dc3ee58280db51bbbb4dd51b85a91abd0178ba`)

`cslib-community/bignum` is developed by the CSLib community (principally Henrik Böving and collaborators) as a Lean 4 port of `awslabs/s2n-bignum`. At commit `92dc3ee58280db51bbbb4dd51b85a91abd0178ba` (2026-10-28), the project targets `leanprover/lean4:v4.36.0-rc1` (`lean-toolchain:1`), enables Lean's experimental module system (`requiresModuleSystem = true` in `lakefile.toml:3`, using `module`, `public import`, and `@[expose] public section` across files), and depends on `leanprover-community/batteries` (`main`, resolved to `e5b86dc7d3ab1cabdbccffbfd3c7be1fa5fdce1d` in `lake-manifest.json:10`).

#### 1.1 File-by-File Inventory and HOL Light Correspondence

| `cslib-community/bignum` File (`92dc3ee58`) | Lines | `awslabs/s2n-bignum` Counterpart (`9f2cd960e`) | Key Declarations & Port Status |
| :--- | ---: | :--- | :--- |
| `Bignum/Component/Basic.lean` | 127 | `common/components.ml:1-130` (and HOL Light `Library/components.ml`) | `Component α β`, `ReadOverWrite`, `WeakReadOverWrite`, `WriteOverRead`, `WriteOverWrite`, `Valid`, `WeaklyValid`, `StronglyValid`, `ExtensionallyValid`, `Orthogonal`, `compose` (`:>`), `entirety`. |
| `Bignum/Component/BasicLemmas.lean` | 109 | `common/components.ml:131-310` | `compose_assoc`, `compose_entirety_left`, `compose_entirety_right`, typeclass preservation instances for `:>`, `entirety`, and `Valid`/`StronglyValid`. |
| `Bignum/Component/Extra.lean` | 91 | `common/components.ml:311-569` | `element`, `rvalue`, `through`, `bitelement`, `subword`, `bottomhalf`, `tophalf`, `bottom8..256`, `top8..256`, `zerotop8..256`, `bytesLE`. |
| `Bignum/Component/ExtraLemmas.lean` | 48 | `common/components.ml:311-569` | `ReadOverWrite`, `WriteOverRead`, `WriteOverWrite` instances for `element`; `Orthogonal (rvalue b) cp`. |
| `Bignum/Component/Relational.lean` | 30 | `common/components.ml:570-620`, `common/maychange.ml` | `Assign` (`≔`), `Assigns`, `MayChange`. |
| `Bignum/Component/RelationalLemmas.lean` | 150 | `common/components.ml:621-729` | `Assign_zerotop8..256`, `assign_valid`, `assign_weaklyValid`, `assign_id`, `assign_seq`, `assigns_id`, `assigns_seq`, `mayChange_id`, `mayChange_idem`. |
| `Bignum/Relational/Basic.lean` | 49 | `common/relational.ml:1-1255` | `Relation α β`, `Relation.Seq` (`,,`), `Relation.Subsumed` (`⊆`), `Relation.Eventually`, `Relation.Ensures`. |
| `Bignum/Relational/Lemmas.lean` | 105 | `common/relational.ml:40-1360` | `eq_seq`, `seq_eq`, `seq_assoc`, `Eventually.mono`, `Eventually.idem`, `Eventually.trans`, `ensures_frame_mono`, `ensures_frame_subsumed`, `ensures_frame_invariant`, `ensures_trans`. |
| `Bignum/Memory/Basic.lean` | 107 | `common/components.ml:450-569`, `common/code_loading.ml:1-130` | `Byte`, `ByteList`, `Memory w := BitVec w → Byte`, `ByteList.ofNatLE`, `ByteList.toNatLE`, `readBytesLE`, `writeBytesLE`, `readBytesNatLE`, `writeBytesNatLE`, `writeBytesNatLE'`, `AlignedBytesLoadedLE`. |
| `Bignum/Memory/Lemmas.lean` | 531 | `common/components.ml:450-569`, `common/code_loading.ml:1-219` | `toNatLE_ofNatLE`, `ofNatLE_toNatLE`, `writeBytesNatLE_eq_writeBytesLE`, `writeBytesNatLE'_eq` (requires `hk : k ≤ 2^w`), `alignedBytesLoadedLE_iff` (`Decidable` instance), `readBytesLE_append`. Contains 2 commented-out `sorry` theorems. |
| `Bignum/Safety/Basic.lean` | 25 | `common/safety.ml:35-51` | `UArchEvent (w : Nat)` (`EventLoad`, `EventStore`, `EventJump`). Does not yet port `memaccess_inbounds`, `contained_modulo`, or `EventX86PEXT`/`EventX86POPCNT`. |
| `Bignum/BitVec/Basic.lean` | 21 | `Library/words.ml`, `common/words2.ml` | `BitVec.getElem_extractLsb'`, `BitVec.replicate`. |
| `Bignum/BitVec/Lemmas.lean` | 14 | `Library/words.ml` | `extractLsb'_append_eq_left`, `extractLsb'_append_eq_right`. |
| `Bignum/BitVec/MatchBV.lean` | 222 | `Library/bitmatch.ml` (and `lean-mlir`/AWS `LNSym`) | `match_bv` macro and elaborator compiling bit-pattern slices `[sf:1, op:1, S:1, 100010, ...]` into `extractLsb'` comparisons and `let`-bindings. |
| `Bignum/Arm/State.lean` | 73 | `arm/proofs/arm.ml:20-58` | `Arm.State` (`_pc`, `_regs`, `_sregs`, `_flags`, `_mem`, `_events`), `PC`, `regs`, `sregs`, `flags`, `mem`, `events`, `AlignedBytesLoaded`. |
| `Bignum/Arm/StateLemmas.lean` | 75 | `arm/proofs/arm.ml:20-58` | `ReadOverWrite`, `WriteOverRead`, `WriteOverWrite` instances for `PC`, `regs`, `sregs`, `flags`, `mem`, `events`; `Decidable (s.AlignedBytesLoaded addr bs)`. |
| `Bignum/Arm/Component.lean` | 36 | `arm/proofs/arm.ml:60-150` | `XREG`, `WREG`, `XREG'`, `WREG'`, `QREG`, `DREG`, `SREG`, `HREG`, `BREG`, `NF`, `ZF`, `CF`, `VF`. |
| `Bignum/Arm/Abbrev.lean` | 194 | `arm/proofs/arm.ml:60-190` | Named register abbreviations `X0..X30`, `SP`, `XZR`, `W0..W30`, `WSP`, `WZR`, `Q0..Q31`, `D0..D31`, `S0..S31`, `H0..H31`, `B0..B31`. |
| `Bignum/Arm/Condition.lean` | 91 | `arm/proofs/arm.ml:192-265` | `Arm.Condition` (`EQ`, `NE`, `CS`, `CC`, `MI`, `PL`, `VS`, `VC`, `HI`, `LS`, `GE`, `LT`, `GT`, `LE`, `AL`, `NV`), `Condition.read`. |
| `Bignum/Arm/Operand.lean` | 150 | `arm/proofs/instruction.ml:260-470` | `ShiftType`, `ExtendedType`, `Shiftedreg`, `Extendedreg`, `OffsetType`, ` PostIndex`, `PreIndex`, `ShiftedOffset`, `ExtendedOffset`. |
| `Bignum/Arm/Instruction.lean` | 32 | `arm/proofs/instruction.ml:671-760` | `ADD` and `SUB` only (`(Rd ≔ (n + m))` and `(Rd ≔ (n - m))`). |
| `Bignum/Arm/Decode.lean` | 50 | `arm/proofs/decode.ml:820-850` | `Decode.addOp` (`panic! "not implemented"` when `S = true`) and `Decode.decode` (single `match_bv` arm for Add/subtract immediate `100010`). |
| `Bignum/Arm/Semantics.lean` | 29 | `arm/proofs/arm.ml:270-310` | `State.decode` structure and `arm : Relation State State`. |
| `BignumTest/Tutorial/Simple.lean` | 29 | `arm/tutorial/simple.ml:1-56` | `simple` byte array (`0x8b000022`, `0xcb010042`) and `simple_spec` (sole active `sorry` at line 28). |

#### 1.2 Commit-by-Commit Evolution of the Core Semantics (2026-10-21 to 2026-10-28)

Inspecting the git history of `cslib-community/bignum` reveals how the relational Hoare foundation was iteratively debugged during October 2026:

1. **Pointwise-to-Universal `Ensures` Fix (`5c042a0` → `d05fddf`, 2026-10-21 to 2026-10-22):**
   - In commit `5c042a0ff1347f5d96747755fd694d0591df1bf0` (`Bignum/Relational/Basic.lean:36`), `Ensures` took a specific initial state `(a : α)` as a parameter:
     ```lean
     def Ensures (step : Relation α α) (pre post : α → Prop) (frame : Relation α α) (a : α) : Prop :=
       pre a → step.Eventually (fun a' ↦ post a' ∧ frame a a') a
     ```
   - Because `Ensures` was parameterized by a single state `a` rather than universally quantifying over all states satisfying the intermediate predicate `Q`, sequential composition (`ensures_trans`) could not be stated cleanly. Commit `d05fddf1158eafa66029975fd9f58e90bf2707f3` (`Bignum/Relational/Basic.lean:45-47`) removed the `(a : α)` parameter and universally quantified over `a`:
     ```lean
     def Ensures (step : Relation α α) (pre post : α → Prop) (frame : Relation α α) : Prop :=
       forall a, pre a → step.Eventually (fun a' ↦ post a' ∧ frame a a') a
     ```
     This matches `s2n-bignum/common/relational.ml:1240`:
     ```ocaml
     let ensures = new_definition
      `ensures (step:S->S->bool) (precondition:S->bool) (postcondition:S->bool) (frame:S->S->bool) <=>
         !s. precondition s ==> eventually step (\s'. postcondition s' /\ frame s s') s`;;
     ```
2. **Universe Parameter Fix on `State.decode` (`6325d36` → `bbdcd12`, 2026-10-22):**
   - Commit `6325d36da280db9c5cb698ee7fb06139c4ceba89` introduced `Bignum/Arm/Semantics.lean` with `structure State.decode (s : State) (addr : BitVec 64) : Type u`, leaving a dangling universe variable `u` in `arm : Relation State State`. Commit `bbdcd12242343898cf5c8bd58dc41c881cf3bc7d` fixed `State.decode` to live in `Type`.
3. **Removal of `Bignum/ArmOld` (`997b904`, 2026-10-27) and Restoration of Universal `Eventually.step` (`326f811` → `92dc3ee`, 2026-10-28):**
   - Commit `997b9044b6a8f397fd3ce8f4af5d6debe5e8b224` deleted the legacy non-component prototype `Bignum/ArmOld.lean` (`ArmOld/Machine.lean`, `ArmOld/Spec.lean`, `ArmOld/Tutorial.lean`).
   - Commits `326f811eb59560caab763b699e1a05f181f8e767` and `92dc3ee58280db51bbbb4dd51b85a91abd0178ba` finalized `Relation.Eventually` with both existential progress `hs : ∃ a', step a a'` and universal successor continuation `hss : ∀ a', step a a' → step.Eventually P a'`, and proved `ensures_frame_invariant` and `ensures_trans` in `Bignum/Relational/Lemmas.lean:87-105`.

---

### 2. The `Component` Lens Hierarchy: `cslib-community/bignum` vs. `s2n-bignum` vs. Kraken

Both `s2n-bignum` (`common/components.ml`) and `cslib-community/bignum` (`Bignum/Component/Basic.lean`) represent every readable/writable projection of architectural state (registers, sub-registers, status flag bits, byte ranges in memory, and microarchitectural event traces) as a first-class lens:

```lean
structure Component (α : Type u) (β : Type v) where
  read : α → β
  write : β → α → α
```

#### 2.1 Lens Laws and Why `WeakReadOverWrite` Exists

`Bignum/Component/Basic.lean:33-112` organizes HOL Light's component predicates into an 8-class Lean typeclass hierarchy:

1. `ReadOverWrite cp`: `∀ (b : β) (a : α), cp.read (cp.write b a) = b` (`write` is a right inverse of `read`).
2. `WeakReadOverWrite cp`: `∃ (f : β → β), ∀ (b : β) (a : α), cp.read (cp.write b a) = f b` (reading after writing applies an idempotent normalization/truncation function `f` to `b`).
3. `WriteOverRead cp`: `∀ (a : α), cp.write (cp.read a) a = a`.
4. `WriteOverWrite cp`: `∀ (b₁ b₂ : β) (a : α), cp.write b₂ (cp.write b₁ a) = cp.write b₂ a`.
5. Composite validity classes:
   - `Valid cp := ReadOverWrite cp + WriteOverWrite cp`
   - `WeaklyValid cp := WeakReadOverWrite cp + WriteOverWrite cp`
   - `StronglyValid cp := Valid cp + WriteOverRead cp`
   - `ExtensionallyValid cp := WeaklyValid cp + WriteOverRead cp`

Why does `s2n-bignum` (`common/components.ml:75-125`) and `cslib-community/bignum` need `WeakReadOverWrite` and `WeaklyValid` in addition to standard lens laws (`StronglyValid`)?
- First, for **truncating or fixed-length slice lenses** such as `bytesLE addr len : Component (Memory w) ByteList` (`Bignum/Component/Extra.lean:89`) or `asnumber` in HOL Light (`common/components.ml:411`): writing a `ByteList` `bs` whose length differs from `len` (or writing a `Nat` larger than $2^{8k}$) and then reading `len` bytes back does not return `bs` verbatim, but rather `bs` truncated/padded to `len` bytes (`f bs`).
- Second, for **upper-zeroing sub-register lenses** such as `WREG i := XREG i :> .zerotop32` (`Bignum/Arm/Component.lean:16`), where `zerotop32 : Component (BitVec 64) (BitVec 32) := .through (.truncate 32) (.truncate 64)` (`Bignum/Component/Extra.lean:87`, note `.truncate 64` on `BitVec 32` zero-extends to 64 bits):
  - `zerotop32` satisfies `ReadOverWrite` (`truncate 32 (zeroExtend 64 v) = v`) and `WriteOverWrite` (`zeroExtend 64 v₂` ignores the old 64-bit value), so `WREG i` is `Valid` (`ReadOverWrite` + `WriteOverWrite`).
  - However, `WREG i` intentionally **violates** `WriteOverRead`: reading the lower 32 bits of `XREG i` and writing them back through `WREG i` zeroes the upper 32 bits of `XREG i`! Thus `WREG i` is `Valid` (and `WeaklyValid`), **not** `StronglyValid`.
  - In `Bignum/Component/RelationalLemmas.lean:45-46`, `Assign_zerotop32` proves by `rfl` that assigning a 32-bit value to `cp :> .zerotop32` is definitionally identical to assigning the 64-bit zero-extension to `cp`:
    ```lean
    theorem Assign_zerotop32 (cp : Component α (BitVec 64)) (bv : BitVec 32) :
        ((cp :> .zerotop32) ≔ bv) = (cp ≔ bv.zeroExtend 64) := rfl
    ```
- Third, for **zero-register / immediate pseudo-lenses** `rvalue b : Component α β` (`read _ := b`, `write _ a := a`, `Bignum/Component/Extra.lean:24`), used for `XZR := .rvalue 0#64` (`Bignum/Arm/Abbrev.lean:47`), `WZR := .rvalue 0#32` (`Bignum/Arm/Abbrev.lean:81`), and immediate operands in `Decode.lean:43,45`: `rvalue b` satisfies `WeakReadOverWrite` with constant function `f _ := b` and `WriteOverWrite`, making it `ExtensionallyValid` without satisfying `ReadOverWrite`.

#### 2.2 Three Primary-Source Findings in `cslib-community/bignum`'s `Component` Library

1. **Accidental Homogeneous Restriction on `Orthogonal.symm` (`Bignum/Component/Basic.lean:111`):**
   `class Orthogonal (cp₁ : Component α β) (cp₂ : Component α γ) : Prop` (`Basic.lean:105`) properly allows two components on the same state `α` to have distinct value types `β : Type v` and `γ : Type w` (for example, `X2 : Component State (BitVec 64)` and `NF : Component State Bool`, or `X2` and `events : Component State (List (UArchEvent 64))`). However, line 111 declares:
   ```lean
   theorem Orthogonal.symm (cp₁ cp₂ : Component α β) (h : Orthogonal cp₁ cp₂) : Orthogonal cp₂ cp₁
   ```
   forcing `cp₁` and `cp₂` to have the same codomain `β`. In [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean) (`Component.Orthogonal.symm`), we generalize the signature to `{cp₁ : Component α β} {cp₂ : Component α γ}` with an identical 3-line proof.
2. **Homogeneous List Typing of `MayChange` (`Bignum/Component/Relational.lean:26`):**
   In HOL Light (`common/maychange.ml:19-41`), `MAYCHANGE [c1; c2; ...]` is also typed over a homogeneous list `(S, A) component list`, which is why `s2n-bignum` chains separate `MAYCHANGE` clauses with `,,` whenever the modified components have different types (e.g., `MAYCHANGE [PC] ,, MAYCHANGE MODIFIABLE_GPRS ,, MAYCHANGE MODIFIABLE_SIMD_REGS ,, MAYCHANGE MODIFIABLE_UPPER_SIMD_REGS ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events]` in `arm/proofs/instruction.ml:655-658`), and why `common/maychange.ml` provides custom OCaml conversions (`MAYCHANGE_STARTER_TAC`, `simplify_maychanges`) to normalize chains of `MAYCHANGE`. In `cslib-community/bignum`, `MayChange : List (Component α β) → Relation α α` inherits this exact typing constraint: `[PC, X2]` is well-typed as `List (Component State (BitVec 64))`, whereas combining `X2` (`BitVec 64`), `NF` (`Bool`), `mem :> bytesLE addr 8` (`ByteList`), and `events` (`List (UArchEvent 64)`) requires sequential composition `MayChange [PC, X2] ,, MayChange [NF] ,, MayChange [mem :> bytesLE addr 8] ,, MayChange [events]`.
3. **Missing `Orthogonal` Frame-Preservation Theorems (`Bignum/Component/RelationalLemmas.lean`):**
   At commit `92dc3ee58`, `Bignum/Component/RelationalLemmas.lean` proves algebraic laws for `Assign`, `Assigns`, and `MayChange` on a *single* component (`assign_valid`, `assign_seq`, `assigns_seq`, `mayChange_idem`), and `Bignum/Component/ExtraLemmas.lean` proves `Orthogonal (rvalue b) cp` (without proving `Orthogonal (element a₁) (element a₂)` for `a₁ ≠ a₂`). Crucially, the repository does not yet contain the theorem that `MayChange cps s s'` preserves `cp.read s' = cp.read s` whenever `Orthogonal cp w` holds for all `w ∈ cps`. In [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean), we prove:
   - `Component.element_orthogonal`: `a₁ ≠ a₂ → Orthogonal (element a₁) (element a₂)`,
   - `Component.orthogonal_compose_left` and `Component.orthogonal_compose_right`: preservation of `Orthogonal` under `:>` lens composition,
   - `Component.Assigns_preserves_orthogonal`: `Orthogonal cp w → w.Assigns a a' → cp.read a' = cp.read a`,
   - `Component.MayChange_preserves_orthogonal`: `(∀ w ∈ cps, Orthogonal cp w) → MayChange cps a a' → cp.read a' = cp.read a`, and
   - `Component.Seq_preserves_read`: preservation of `cp.read` across heterogeneous `r₁ ,, r₂` frame compositions.

---

### 3. Primary-Source Diagnosis of `BignumTest/Tutorial/Simple.lean` and the `Decode.lean` Bug

#### 3.1 Why `simple_spec` in `BignumTest/Tutorial/Simple.lean:16-28` is Unprovable at `92dc3ee58`

`BignumTest/Tutorial/Simple.lean` is a direct port of `s2n-bignum/arm/tutorial/simple.ml:1-32`:

```lean
def simple : ByteList :=
  -- 0x8b000022, 0xcb010042
  [ 0x22, 0x00, 0x00, 0x8b, 0x42, 0x00, 0x01, 0xcb ]

theorem simple_spec (pc : Nat) (a b : BitVec 64) :
    arm.Ensures
      (fun s ↦ s.AlignedBytesLoaded (BitVec.ofNat 64 pc) simple
        ∧ s.read PC = BitVec.ofNat 64 pc
        ∧ s.read X0 = a
        ∧ s.read X1 = b)
      (fun s ↦ s.read PC = BitVec.ofNat 64 (pc + 8)
        ∧ s.read X2 = a)
      (MayChange [PC, X2]) := by
  sorry
```

In `s2n-bignum/arm/tutorial/simple.ml:12-14`, the two 32-bit AArch64 instruction words are:
- Word 0: `0x8b000022` = `add x2, x1, x0` (`0b1_0_0_01011_00_0_00000_000000_00001_00010`)
- Word 1: `0xcb010042` = `sub x2, x2, x1` (`0b1_1_0_01011_00_0_00001_000000_00010_00010`)

Both instructions belong to the AArch64 **Add/subtract (shifted register)** encoding class (`sf | op | S | 01011 | shift(2) | 0 | Rm(5) | imm6(6) | Rn(5) | Rd(5)`), which is decoded in `s2n-bignum/arm/proofs/decode.ml:858-866`:
```ocaml
  | [sf:1; op:1; S:1; 0b01011:5; shift:2; 0b0:1; Rm:5; imm6:6; Rn:5; Rd:5] ->
      if shift = word 3 then NONE else
      SOME(arm_add_op (bitval op) (bitval S) ( bitval sf )
             (if bitval S then XREG' Rd else XREG' Rd) (XREG' Rn)
             (Shiftedreg (XREG' Rm) (decode_shift shift) (val imm6)))
```

However, in `cslib-community/bignum` at `92dc3ee58`, `Bignum/Arm/Decode.lean:36-47` implements **only** the **Add/subtract (immediate)** encoding class (`sf | op | S | 100010 | sh(1) | imm12(12) | Rn(5) | Rd(5)`):
```lean
def decode (bv : BitVec 32) : Option (Relation State State) :=
  match_bv bv with
  | [sf:1, op:1, S:1, 100010, sh:1, imm12:12, Rn:5, Rd:5] =>
    let val : Nat := imm12.toNat <<< (12 * sh.toNat)
    if sf != 0 then
      let Rd := if S != 0 then XREG' Rd else XREG Rd
      .some <| addOp (op != 0) (S != 0) Rd (XREG Rn) (.rvalue (.ofNat 64 val))
    else
      let Rd := if S != 0 then WREG' Rd else WREG Rd
      .some <| addOp (op != 0) (S != 0) Rd (WREG Rn) (.rvalue (.ofNat 32 val))
  | _ => .none
```

Because `0x8b000022` and `0xcb010042` have bits `[28:23] = 0b010110 ≠ 0b100010`, `Decode.decode 0x8b000022#32 = none` and `Decode.decode 0xcb010042#32 = none`. In `Bignum/Arm/Semantics.lean:16-28`:
```lean
structure State.decode (s : State) (addr : BitVec 64) : Type where
  instr : Relation State State
  data : BitVec 32
  loaded : s.AlignedBytesLoaded addr (.ofNatLE 4 data.toNat)
  decode : Decode.decode data = .some instr

def arm : Relation State State :=
  fun s s' ↦ ∃ d : s.decode (s.read PC), (PC ≔ (s.read PC + 4#64) ,, d.instr) s s'
```
Because `s.AlignedBytesLoaded (s.read PC) (.ofNatLE 4 data.toNat)` uniquely determines `data = 0x8b000022#32` via injectivity of `ByteList.ofNatLE 4` on `BitVec 32`, `Decode.decode data = .some instr` reduces to `none = some instr`, so `s.decode (s.read PC)` is empty and `¬ ∃ s', arm s s'`. Since `Eventually` requires either the postcondition `s.read PC = BitVec.ofNat 64 (pc + 8)` to hold initially (impossible since `BitVec.ofNat 64 pc ≠ BitVec.ofNat 64 (pc + 8)`) or `∃ s', arm s s'`, `simple_spec` is **false** against upstream `Bignum/Arm/Decode.lean` at `92dc3ee58`.

In [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean), we formally prove both:
1. `Arm.upstream_simple_stuck_at_entry`: under upstream `Decode.decode`, any state `s` satisfying the precondition of `simple_spec` has no `upstreamArm` successor (`¬ ∃ s', upstreamArm s s'`), and
2. `Arm.simple_spec_proven`: once the Add/subtract (shifted register) arm (`bits[28:21] == 0b01011000`) is added to the decoder (`FixedDecode.decode`), `simple_spec` holds for all `pc : Nat` and `a b : BitVec 64` with zero `sorry` and zero custom axioms, and `Arm.simple_frame_preserves_abi_state` derives preservation of `X19`, `SP`, and `flags` from `MayChange [PC, X2]`.

#### 3.2 Secondary Decoder Hazard: `panic! "not implemented"` in `Decode.addOp` (`Bignum/Arm/Decode.lean:31`)

In `Bignum/Arm/Decode.lean:27-32`, `addOp` dispatches on `(op : Bool)` and `(S : Bool)`:
```lean
def addOp : Bool → Bool → (Component α (BitVec w) → Component α (BitVec w) →
    Component α (BitVec w) → Relation α α)
  | false, false => Instruction.ADD
  | true, false => Instruction.SUB
  | false, true
  | true, true => panic! "not implemented"
```
In Lean 4, `panic! msg` is **not** a partial/failing option return; it returns `default` from `Inhabited`. Because `Relation α α` (`α → α → Prop`) has default `fun _ _ ↦ False` (via `Inhabited Prop`), `Decode.decode` on an `ADDS` or `SUBS` immediate instruction returns **`Option.some (fun _ _ ↦ False)`** rather than `Option.none`! While `arm s s'` still has no successor when `d.instr = fun _ _ ↦ False`, returning `Option.some` on an unimplemented instruction means `Decode.decode bv |>.isSome` falsely reports that `ADDS`/`SUBS` is implemented. Returning `Option.none` in `Decode.decode` when `S = true` (until `ADDS`/`SUBS` flag semantics are added to `Bignum/Arm/Instruction.lean`) avoids creating inhabitable `State.decode` witnesses with empty transition relations.

---

### 4. Memory Model, Wrapping Semantics, and Microarchitectural `Safety`

#### 4.1 Total Byte-Addressed Memory and the `k ≤ 2^w` Wrapping Condition (`Bignum/Memory/`)

`Bignum/Memory/Basic.lean:20` models memory as a total function `abbrev Memory (w : Nat) := BitVec w → Byte` (where `Byte := BitVec 8`).
A subtle discrepancy between `cslib-community/bignum` and `s2n-bignum` arises in multi-byte little-endian writes:
- `cslib-community/bignum` defines `writeBytesNatLE` recursively from lowest address `addr` upward to `addr + (k - 1)` (`Bignum/Memory/Basic.lean:77-80`), whereas
- `s2n-bignum` (`common/components.ml:458-466`) defines `write_bytes` recursively from highest index `k - 1` downward, so the lowest address `addr` is updated **outermost** (last).

In `Bignum/Memory/Basic.lean:87-90` and `Bignum/Memory/Lemmas.lean:376-408`, `cslib-community/bignum` defines `writeBytesNatLE'` to match `s2n-bignum`'s reverse write order and proves `writeBytesNatLE'_eq`:
```lean
theorem writeBytesNatLE'_eq (mem : Memory w) (addr : BitVec w) (k n : Nat) (hk : k ≤ 2 ^ w) :
    mem.writeBytesNatLE' addr k n = mem.writeBytesNatLE addr k n
```
Why is the hypothesis `hk : k ≤ 2 ^ w` required? Because `BitVec w` addresses wrap modulo $2^w$: if a write spans $k > 2^w$ bytes, the write wraps completely around the $2^w$-byte address space and writes to the same address twice. Under forward order (`writeBytesNatLE`), the high byte at index $i + 2^w$ overwrites index $i$, whereas under reverse order (`writeBytesNatLE'`), index $i$ overwrites index $i + 2^w$! When $k \le 2^w$, all $k$ addresses are distinct modulo $2^w$ and the two write orders commute.

#### 4.2 Microarchitectural `Safety`: `s2n-bignum/common/safety.ml` vs. `Bignum/Safety/Basic.lean`

In `s2n-bignum/common/safety.ml:35-158`, every machine state carries an `events : uarch_event list` component, and instructions that perform memory accesses, control-flow jumps, or data-dependent variable-time operations append events to `events`:
- `EventLoad (addr, sz)` and `EventStore (addr, sz)`: emitted by `arm_LDR`, `arm_STR`, `arm_LDRB`, `arm_STRB`, `arm_LDP`, `arm_STP`, etc. (`arm/proofs/instruction.ml:2944-3050`).
- `EventJump (src, dst)`: emitted by branch/call/return instructions (`arm/proofs/arm.ml:290-305`).
- `EventX86PEXT (src1, src2)` and `EventX86POPCNT src`: emitted on x86_64 for instructions excluded from Intel's Data Operand Independent Timing (DOIT) list (`common/safety.ml:39-48`).

From this single `events` trace, `s2n-bignum` derives **both** constant-time execution and memory-footprint containment (`common/safety.ml:142-158`):
```ocaml
let contained_modulo = new_definition
  `contained_modulo modulus (ptr:num,sz:num) (base:num,len:num) <=>
    sz = 0 \/ (sz <= len /\ ((ptr + modulus - (base MOD modulus)) MOD modulus) + sz <= len)`;;

let memaccess_inbounds = new_definition
  `memaccess_inbounds (events:(uarch_event)list)
      (read_ranges:(int64#num)list) (write_ranges:(int64#num)list) <=>
    ALL (\e. case e of
      | EventJump (_,_) -> T
      | EventLoad (p,sz) ->
          EXISTS (contained_modulo (2 EXP 64) (val p,sz))
            (MAP (\(p,sz). (val p,sz)) read_ranges)
      | EventStore (p,sz) ->
          EXISTS (contained_modulo (2 EXP 64) (val p,sz))
            (MAP (\(p,sz). (val p,sz)) write_ranges)
      | EventX86PEXT (_,_) -> T
      | EventX86POPCNT _ -> T) events`;;
```
An `s2n-bignum` `_SAFE` theorem (`arm/proofs/consttime.ml` / `common/consttime.ml`) asserts `ensures arm Pre Post Frame` where:
1. `Post s'` includes `∃ e_trace, f_events (public_inputs) e_trace ∧ read events s' = APPEND e_trace e` (proving that the entire trace of load/store addresses and jump targets is a deterministic function `f_events` of public inputs only, independent of secret register/memory values), and
2. `memaccess_inbounds e_trace read_ranges write_ranges` holds (proving that every transient memory read or write during execution stayed within `read_ranges` / `write_ranges`).

At commit `92dc3ee58`, `cslib-community/bignum` has ported only the `UArchEvent` inductive (`Bignum/Safety/Basic.lean:16-23`, with `EventLoad`, `EventStore`, `EventJump`) and the `_events : List (UArchEvent 64)` field on `Arm.State` (`Bignum/Arm/State.lean:24`), but has not yet ported `contained_modulo`, `memaccess_inbounds`, `f_events` constant-time specifications, or any load/store/branch instruction in `Bignum/Arm/Instruction.lean`. We port `containedModulo64`, `memaccessInbounds`, `LDR64`, and `STR64` in [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean).

---

### 5. Three-Way Architectural Comparison: `s2n-bignum` (HOL Light) vs. `cslib-community/bignum` (Lean 4) vs. `Kraken` (Lean 4)

| Dimension | `awslabs/s2n-bignum` (`9f2cd960e`) | `cslib-community/bignum` (`92dc3ee58`) | `AeneasVerif/kraken` (`c9aa45ee1`) |
| :--- | :--- | :--- | :--- |
| **Theorem Prover & Kernel** | HOL Light (OCaml LCF kernel, `jrh13/hol-light`). | Lean 4 (`v4.36.0-rc1`, `requiresModuleSystem = true`, `Batteries`). | Lean 4 (`v4.34.1`, `requiresModuleSystem = true`). |
| **Program Representation & Byte Binding** | Concrete machine-code byte list loaded in memory via `bytes_loaded s (word pc) bytes` (`common/code_loading.ml`) or `aligned_bytes_loaded s (word pc) bytes` (`arm/proofs/arm.ml:273`). | Concrete `ByteList` loaded in `State._mem` via `s.AlignedBytesLoaded addr bs` (`Bignum/Arm/State.lean:69`, `4 ∣ addr.toNat ∧ s._mem.readBytesLE addr bs.length = bs`). | Structured AST (`Kraken.Directive Instr` in `Host.exe : Executable`) with abstract address layout `Host.Valid`; **no** binary instruction decoder from raw bytes in `Kraken/` (`reports/kraken-checked-aarch64-byte-leaf-resource-adapter-8af7806/`). |
| **Instruction Decoding** | Total/partial bit-pattern matching via `bitmatch` (`arm/proofs/decode.ml`, `x86/proofs/decode.ml`) at every step over memory at `PC`/`RIP`. | `match_bv` macro (`Bignum/BitVec/MatchBV.lean`) in `Decode.decode : BitVec 32 → Option (Relation State State)`, invoked at every step via `State.decode s (s.read PC)`. Currently 1 arm (`ADD`/`SUB` immediate). | Textual/macro assembly parser (`Kraken/AArch64/Parser.lean`, `Kraken/X64/Parser/Basic.lean`) elaborating assembly syntax into `Instr` AST at compile time. |
| **State & Register Model** | `armstate` / `x86state` record accessed uniformly via `(S, A) component` lenses (`X0..X30`, `W0..W30`, `Q0..Q31`, `NF..VF`, `memory :> bytes`, `events`). | `Arm.State` structure accessed via `Component State β` lenses (`PC`, `XREG`, `WREG`, `QREG..BREG`, `NF..VF`, `mem :> bytesLE`, `events`). | `MachineState` (`MachineData` + `pc : Int64`) with explicit `Reg64s` struct fields (`X0..X30`, `SP`), `StatusFlags` struct (`n`, `z`, `c`, `v`), and `DataMem := Mem 64`. |
| **Memory Model & Permissions** | Total map `int64 -> byte`. Frame modification tracked via `MAYCHANGE [memory :> bytes(addr, len)]`; transient read/write bounds tracked via `events` + `memaccess_inbounds` (`common/safety.ml:150`). | Total map `BitVec 64 → BitVec 8`. Frame modification tracked via `MayChange [mem :> bytesLE addr len]`; `UArchEvent` defined in `Bignum/Safety/Basic.lean` (`memaccess_inbounds` not yet ported upstream). | Partial byte map `Mem 64` (`Std.ExtTreeMap Int64 Byte`) with CPS permission gates (`Effects.require_read_access`, `require_write_access`, `require_exec_access`, `nonmem_load`, `nonmem_store`), though `Executable.eval` erases permission checks (`Semantics.lean:987-989`). |
| **Hoare / Temporal Logic** | `eventually` & `ensures` (`common/relational.ml:1240`) + step-indexed `eventually_n` & `ensures_n` (`common/relational_n.ml:348`). | `Relation.Eventually` & `Relation.Ensures` (`Bignum/Relational/Basic.lean:38-47`). Step-indexed `EnsuresN` not yet ported upstream. | `OmniSemantics.Eventually` (`Kraken/OmniSemantics.lean:13`) & weakest precondition `Program.wp` (`Kraken/WP/Basic.lean`) over `Effects.All`. |
| **Constant-Time & Leakage Model** | First-class (`UArchEvent` trace + `f_events` existential + DOIT discipline). | `UArchEvent` inductive and `State.events` component present; instruction emission and `f_events` not yet ported. | None (no microarchitectural event trace or DOIT model). |
| **ISA Coverage** | Production AArch64 and x86_64 (~280k+ lines of proofs across Curve25519, P-256/384/521, RSA, ML-KEM, ML-DSA, SHA-3). | AArch64 `ADD`/`SUB` immediate only (`Bignum/Arm/Instruction.lean`, `Decode.lean`); 0 x86_64 instructions. | Broad user-space integer/branch AArch64 and X64 AST semantics (`Kraken/AArch64/Semantics.lean`, `Kraken/X64/Semantics.lean`), minimal SIMD. |

---

### 6. Synthesis for Anneal (`joshlf/anneal-private`): Bridging `Ensures` + `Safety` into `SmallStepMachine` and `Language.SpecOn` (`Issue #102`)

#### 6.1 Structural Mismatch Between `Ensures` and Anneal's `SmallStepMachine`

In Anneal (`trusted/lean/Trusted/Refinement.lean` and `trusted/lean/Trusted/StepResult.lean`), a target language semantics is packaged as a `SmallStepMachine Prog State` with `step : State → StepResult State` (`StepResult.step next | StepResult.done final | StepResult.uck`), whose behavioral semantics `BehaviorOf M s₀ : StepQuery → Set (Outcome State)` inspects finite execution prefixes `ReachesPrefix M s₀ q.steps po` at every step budget `q.steps : Nat`:
- If `po = .exhausted current`, `po.toOutcome = .running current`, which satisfies `Outcome.Satisfies post` (`True`).
- If `po = .terminated final`, `po.toOutcome = .terminated final`, which satisfies `Outcome.Satisfies post` iff `post final` holds.
- If `po = .uck`, `po.toOutcome = .stuck`, which **never** satisfies `Outcome.Satisfies post` (`False`).

Comparing `s2n-bignum` / `cslib-community/bignum`'s `Ensures arm pre post frame` with Anneal's `SmallStepMachine` exposes three exact boundary conditions that an Anneal MIR-to-assembly bridge (`Issue #102`) must mediate:

1. **Stopping Criterion (`Eventually` vs. `StepResult.done`):**
   In `s2n-bignum` and `cslib-community/bignum`, `arm : State → State → Prop` is an unstopped small-step relation (it has no `.done` state; if `PC` at the end of a block points to further valid instruction bytes, `arm` can continue stepping). `Eventually arm P s₀` holds as soon as *some* state `s_n` along the trace satisfies `P s_n` (`Eventually.base`). To embed an assembly block (spanning entry `pc_start` to exit `pc_exit`) as a sub-computation inside Anneal's `SmallStepMachine`, the bridge machine must recognize `s.read PC == pc_exit` as the stopping boundary (`StepResult.done s`) and verify that `s.read PC ≠ pc_exit` at all intermediate steps $0 \le k < n$. In `s2n-bignum`, this is captured either by `ensures_n` (`common/relational_n.ml:348`) with explicit step count `n` or by bounding `PC` inside the code range before exit.
2. **Clobber and ABI Preservation (`MayChange` vs. `clobber_abi` / `options(preserves_flags)`):**
   When Rust `asm!` / `global_asm!` enters an assembly block, the Rust abstract machine requires that any register not declared as an output or clobber (and condition flags when `options(preserves_flags)` is set, or `SP` and callee-saved registers `X18..X30`, `V8..V15` lower 64 bits under `clobber_abi("C")` as in `s2n-bignum/arm/proofs/instruction.ml:626-658`) retain their entry values upon exit. Our theorem `Component.MayChange_preserves_orthogonal` (and `Seq_preserves_read` for heterogeneous `MayChange` chains) converts an `s2n-bignum`/`cslib-community/bignum` `MayChange` frame directly into equality of all orthogonal state components (`Arm.simple_frame_preserves_abi_state`).
3. **Why `Ensures` + `MayChange` Alone is Unsound for Memory Safety (`mayChange_alone_cannot_exclude_unauthorized_load`):**
   `MayChange` is an **extensional input-output relation** between the initial state `s₀` and the final state `s_n`:
   - It places **zero constraints on memory reads** (`LDR`): an instruction that reads unmapped or unpermitted memory only modifies its destination register `Rt` and `events`, so `MayChange [PC, Rt] ,, MayChange [events]` holds even when the load address is out of bounds!
   - It places **zero constraints on transient scratch writes that restore original values**: if an assembly block overwrites an unpermitted address `p` and restores the original byte `s₀._mem p` before exiting, `(State.mem :> bytesLE ...)` is unchanged between `s₀` and `s_n` (`s_n._mem = s₀._mem`), so `MayChange [PC, ...]` holds with no memory component in `MayChange`, even though writing to `p` is immediate undefined behavior (`StepResult.uck`) in the Rust/MIR abstract machine!

   Consequently, an Anneal assembly bridge **must** pair `Ensures` / `EnsuresN` with `s2n-bignum`'s microarchitectural `Safety` predicate (`memaccessInbounds` over `State.events`), which records every individual `EventLoad` and `EventStore` in the execution trace and verifies that every read falls within `readableRanges` and every write falls within `writableRanges`.

#### 6.2 Mechanized Bridge Theorem (`ensuresN_safety_refines_anneal_specOn`)

In [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean), we mechanize:
- `AnnealAsmBridgeContract`: bundles `pcExit`, `preservedStateEq` (register/flag preservation across the block), `readableRanges`, and `writableRanges`.
- `asmBridgeMachine`: an Anneal `SmallStepMachine Unit Arm.State` that steps the AArch64 state while checking at every step that newly emitted `UArchEvent`s satisfy `memaccessInbounds` (returning `StepResult.uck` on any out-of-bounds load/store or decode failure) and returning `StepResult.done s` when `s.read PC == pcExit` (or `StepResult.uck` if `preservedStateEq s₀ s` fails at exit).
- `ensuresN_safety_refines_anneal_specOn`: proves that any `SafeExecutionN` proof whose `MayChange` frame implies `preservedStateEq` refines Anneal's `Language.SpecOn` across all `StepQuery` budgets `q.steps`, with a concrete 2-step instantiation `simple_safeExecutionN_refines_anneal_specOn` for `simple` (`add x2, x1, x0; sub x2, x2, x1`).

## Boundaries

1. **Upstream `cslib-community/bignum` Completeness Boundary (`92dc3ee58`):**
   - Only `ADD` and `SUB` (`Bignum/Arm/Instruction.lean:16-31`) and only the Add/subtract (immediate) decoding pattern (`Bignum/Arm/Decode.lean:38`) are implemented upstream. All other AArch64 instructions (including shifted/extended-register `ADD`/`SUB`, flag-setting `ADDS`/`SUBS`, `ADC`/`SBC`, `MUL`/`UMULH`, `LDR`/`STR`/`LDP`/`STP`, branches, and SIMD instructions) and all x86_64 instructions remain unported.
   - `Bignum/Memory/Lemmas.lean` contains two commented-out `sorry` theorems (`writeBytesLE_take_padright` at lines 290–308 and `readBytesLE_writeBytesLE` at lines 447–451).
   - `Bignum/Safety/Basic.lean` defines `UArchEvent` (`EventLoad`, `EventStore`, `EventJump`) but does not yet port `contained_modulo`, `memaccess_inbounds`, or constant-time `f_events` predicates.
2. **Toolchain Boundary (`v4.36.0-rc1` vs. `v4.34.1`):**
   - `cslib-community/bignum` pins `leanprover/lean4:v4.36.0-rc1` (`lean-toolchain:1`) and `Batteries` (`main`), whereas Anneal (`joshlf/anneal-private`) and Kraken (`AeneasVerif/kraken`) pin `leanprover/lean4:v4.34.1`. Our standalone mechanization [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean) is self-contained and verified directly under `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768` with zero external package dependencies.
3. **System-Level Architectural Boundaries:**
   - Neither `s2n-bignum` nor `cslib-community/bignum` models page tables, MMU translation, self-modifying code (when instructions and data overlap without explicit disjointness hypotheses), asynchronous interrupts/exceptions, or relaxed-memory concurrency. Memory is modeled as a single flat sequential address space `BitVec 64 → BitVec 8`.

## Evidence

- **Standalone Mechanized Lean 4.34.1 Probe:**
  - [`support/cslib_bignum_component_and_ensures_probe.lean`](support/cslib_bignum_component_and_ensures_probe.lean) (1,320 lines, SHA256 `c9618e915e52d85585303445562521842949449aaa0949d39ff0fea1f6f234d2`), verified with `/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768` (exit code 0, zero warnings, zero `sorryAx`, zero custom axioms verified via `#guard_msgs in #print axioms`):
    - `CslibBignumStudy.Component.Orthogonal.symm`: heterogeneous symmetry of `Orthogonal`.
    - `CslibBignumStudy.Component.MayChange_preserves_orthogonal` (`does not depend on any axioms`): orthogonal frame preservation for `MayChange`.
    - `CslibBignumStudy.Arm.upstream_decode_simple_word0_is_none` and `upstream_decode_simple_word1_is_none`: `UpstreamDecode.decode` returns `none` on `0x8b000022#32` and `0xcb010042#32`.
    - `CslibBignumStudy.Arm.upstream_simple_stuck_at_entry` (`depends on axioms: [propext, Quot.sound]`): proof that `upstreamArm` has no successor from the `Simple.lean` entry state (`¬ ∃ s', upstreamArm s s'`).
    - `CslibBignumStudy.Arm.simple_spec_proven` (`depends on axioms: [propext, Quot.sound]`): complete zero-`sorry` proof of `BignumTest/Tutorial/Simple.lean`'s `simple_spec` under `fixedArm`.
    - `CslibBignumStudy.Arm.simple_frame_preserves_abi_state` (`depends on axioms: [propext, Quot.sound]`): proof that `MayChange [PC, X2]` preserves `X19`, `SP`, and `flags`.
    - `CslibBignumStudy.ensuresN_safety_refines_anneal_specOn` and `CslibBignumStudy.simple_safeExecutionN_refines_anneal_specOn` (`depends on axioms: [propext, Classical.choice, Quot.sound]`): end-to-end refinement from `SafeExecutionN` (`EnsuresN` + `MayChange` + `memaccessInbounds`) to Anneal's `SmallStepMachine.BehaviorOf ≤ Language.SpecOn`.
    - `CslibBignumStudy.mayChange_alone_cannot_exclude_unauthorized_load` (`depends on axioms: [propext]`): negative control proving that `MayChange` alone permits unauthorized loads (`EventLoad`) that trap to `StepResult.uck` in `asmBridgeStep`.
- **Source Manifest:**
  - [`support/source-manifest.json`](support/source-manifest.json): records full 40-character commit SHAs, tree SHAs, recent commit history, and per-file SHA256 digests and line counts across `cslib-community/bignum` (`92dc3ee58280db51bbbb4dd51b85a91abd0178ba`), `awslabs/s2n-bignum` (`9f2cd960e11892a582e7facb0c191b4a2959ea91`), `AeneasVerif/kraken` (`c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0`), and `joshlf/anneal-private` (`42f4571d761b46c7142815f38b69c3781b3555e3`).

## Revalidation

To revalidate the standalone Lean 4.34.1 mechanization from the repository root:

```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M768 \
  reports/cslib-bignum-lean-port-and-s2n-bignum-hol-light-comparison/support/cslib_bignum_component_and_ensures_probe.lean
```

Expected output: exit code `0` with no errors or warnings (all `#guard_msgs in #print axioms` assertions verified).

To revalidate against upstream `cslib-community/bignum` when new commits land:
1. Check whether `Bignum/Arm/Decode.lean` has added the Add/subtract (shifted register) `match_bv` pattern (`01011`) and replaced `panic! "not implemented"` in `Decode.addOp` (`Decode.lean:31`), and whether `BignumTest/Tutorial/Simple.lean:28` (`simple_spec`) has replaced `sorry` with a proof.
2. Check whether `Bignum/Component/Basic.lean:111` (`Orthogonal.symm`) has been generalized to heterogeneous codomain types `β` and `γ`, and whether `MayChange` orthogonality preservation (`MayChange_preserves_orthogonal`) has been added to `Bignum/Component/RelationalLemmas.lean`.
3. Check whether `Bignum/Safety/Basic.lean` has ported `contained_modulo` and `memaccess_inbounds` from `s2n-bignum/common/safety.ml:142-158`.

*Authored by an AI agent acting on joshlf's behalf.*
