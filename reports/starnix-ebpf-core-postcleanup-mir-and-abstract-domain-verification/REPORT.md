# Fuchsia Starnix `ebpf_core` `Runtime(PostCleanup)` MIR Census, Tier 0 End-to-End Proofs, `EbpfInstruction` Lens Semantics, and `U64Range` / `U64ScalarValueData` Abstract-Domain Soundness

## Summary

This report synthesizes a complete non-short-circuiting `Runtime(PostCleanup)` MIR census across all `1,052` MIR bodies (`879` callable functions/closures) of Fuchsia Starnix's `ebpf_core` crate (`fuchsia/fuchsia@823a15538f191b9dbd9ebafaa6ba23220b87d2e1`, `src/starnix/lib/ebpf/core/src`), end-to-end Tier 0 proofs on Anneal's unmodified prefix-safety scalar MIR model (`joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b`), a mechanized extension and bitfield-lens proof for `EbpfInstruction`'s 11 accessors and mutators, and mechanized soundness and host-vs-guest duality proofs for `U64Range` and `U64ScalarValueData` in Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):

1. **First-Refusal Masking vs. Complete Non-Short-Circuiting `Runtime(PostCleanup)` MIR Inventory (`support/mir_probe.rs`)**:
   - Because `anneal-rustc-capture` short-circuits on the first unsupported construct in a signature or basic block, whole-crate capture reports only the shallowest refusal (typically a `&self` reference parameter in signature validation) and conceals deeper body and transitive-callee requirements:
     - `U64Range::add_range`: First refusal reports `parameter 1 uses unsupported type: &scalar_value::U64Range`, concealing `7` distinct body/callee construct families (tuple `CheckedBinaryOp` `(u64, bool)`, `Place::Deref`/`Field`, `Rvalue::Ref`, `Rvalue::Aggregate(Adt)`, `TerminatorKind::Call` to `core::num::<impl u64>::overflowing_add` and `U64Range::new`/`max`, and `U64Range::MAX` associated constant).
     - `U64ScalarValueData::bitand_scalar`: First refusal reports `parameter 1 uses unsupported type: scalar_value::U64ScalarValueData`, concealing `9` distinct construct families across a `4`-level call DAG (`bitand_scalar -> bitand_raw -> new -> {leading_zeros, mask_low_bits, min, max}`).
   - Across all `879` callable bodies in `ebpf_core`, **17 monomorphic functions (`16` beyond `interpreter::apply_endianness`)** are already admitted (`status: "captured"`) by the unmodified baseline scalar model (**Tier 0**), including `scalar_value::U64Range::mask_low_bits`, `scalar_value::U32Range::mask_low_bits`, and the cyclic-CFG loop `verifier::popcount_u64`.

2. **End-to-End Tier 0 Starnix Proofs (`U64Range::mask_low_bits` and Cyclic-CFG `verifier::popcount_u64`) on Unmodified `Trusted.Mvp`**:
   - Both `scalar_value::U64Range::mask_low_bits(value: u64, bit_count: u32) -> u64` (`def_id = 1996`, `7` blocks, `32` statements) and `verifier::popcount_u64(x: u64) -> usize` (`def_id = 559`, `4` blocks, `26` statements, cyclic loop `bb1 -> bb2 -> bb1`) were captured from the 10-file Starnix source bundle and verified end-to-end through `cargo-anneal verify` + `anneal-audit` (`status: "selected_unit_verified"`, axioms `[propext, Classical.choice, Quot.sound]` only) with **zero changes to `Trusted.Mvp` or `Anneal.Mvp.Execution`**.
   - **Symbolic `runN` `whnf` Chunking Law**: Over symbolic `State` records, unflattened `runN` exhibits exponential `whnf` blowup in step count $n$ ($n=5$: `77 ms`, $n=6$: `273 ms`, $n=8$: `5,648 ms`, $n \ge 10$: `>200,000` heartbeats timeout) due to nested `List.set` chains over `state.locals`. Flattening `State` every `5–6` steps via `runN_executes (n := 5) rfl` keeps every symbolic chunk under `450 ms`.
   - **Dual Cyclic-CFG Verification Styles**: In [`support/starnix-popcount-u64/Proof.lean`](support/starnix-popcount-u64/Proof.lean), we mechanized both cyclic loop verification styles side by side: (a) **Style A (`spin` style)**: `popcount_safe_via_invariant : ∀ x, Safe popBody [x]` via `safeFrom_invariant PopcountInv` (`30` control states, `8`-line step proof, no ranking function required), and (b) **Style B (`Executes` style)**: `exec_popcount : ∀ x, Executes popBody (initial popBody [x]) (popcountSpec x)` via `Nat.strongRecOn` on `x.toNat` using Brian Kernighan's bit-clearing lemma `kernighan_lt : (x &&& (x - 1)).toNat < x.toNat`.

3. **Minimal Semantic & Capture Delta for `EbpfInstruction` Accessors and Mutators (`support/EbpfInstructionExtensionProbe.lean`)**:
   - Inspecting the `Runtime(PostCleanup)` MIR of `EbpfInstruction::{get, code, set_code, dst_reg, set_dst_reg, src_reg, set_src_reg, offset, set_offset, imm, set_imm}` shows that all `11` methods require only `5` localized syntax/semantic additions (`Ty.struct1`, `Ty.ref`, `ProjectionElem.{deref, field 0}`, `Rvalue.castInt`, `UnOp.not`, and `Terminator.panic` on dead shift-overflow branches) with **zero heap-aliasing or interprocedural-call machinery** (under a copy-in/copy-out reference convention `ExecutesMut` for `&mut self` on 1-field structs).
   - [`support/EbpfInstructionExtensionProbe.lean`](support/EbpfInstructionExtensionProbe.lean) (`567` lines, `0` `sorry`, compiles in `6.67 s`) mechanizes this extension and proves symbolic execution (`exec_*`) for all `6` getters and `5` mutators, all `15` bitfield lens laws (`Get-Put`, `Put-Get`, `Put-Put` across `code`, `dst_reg`, `src_reg`, `offset`, `imm`), cross-field frame preservation (`set_code_preserves_*`), and unconditional `< 16` register bounds (`dstRegSpec_lt_16`, `srcRegSpec_lt_16`).

4. **Mechanized Abstract-Domain Soundness (`U64Range` & `U64ScalarValueData`) and Formal Host-vs-Guest Duality (`support/StarnixAbstractDomainSoundness.lean`)**:
   - [`support/StarnixAbstractDomainSoundness.lean`](support/StarnixAbstractDomainSoundness.lean) (`680` lines, `0` `sorry`, compiles in `1.47 s`) proves wrapping interval well-formedness and concretization soundness for `U64Range::{add_range, sub_range, rem_range}` (including `rem_range_sound_ebpf`, which proves why `rem_range` returns `self` when `rhs.max == 0` and sets `max = self.max` when `rhs.min == 0` under eBPF `BPF_MOD` div-by-zero semantics `ebpfRem x 0 = x`), plus tnum + `unwritten_mask` + interval soundness for `U64ScalarValueData::{new, bitand_scalar, bitor_scalar, bitxor_scalar}`.
   - We prove formal contrast theorems establishing the algebraic and order-theoretic duality between **guest eBPF** (`U64ScalarValueData`) and **host Rust** (`Trusted.Mvp.Semantics`):
     - In guest eBPF, `0 & UNINITIALIZED` absorbs unknown/unwritten bits to yield `from_known 0` (`is_fully_initialized = true`, `guest_bitand_zero_uninitialized_initializes`), and `UNINITIALIZED` is the **Top (`⊤`)** element of Starnix's state-pruning specificity partial order (`guest_uninitialized_is_top`).
     - In host Rust (`Trusted.Mvp.Semantics`), `0 & uninit` faults immediately with `.fault .uninitialized` (`host_bitand_zero_uninit_faults`), and `Slot.uninit` is the **Bottom (`⊥`)** element of the host definedness order (`host_uninit_is_bottom`).

## Applicability

These findings apply to:

- **Fuchsia Starnix `ebpf_core`**: `fuchsia/fuchsia@823a15538f191b9dbd9ebafaa6ba23220b87d2e1` (`src/starnix/lib/ebpf/core/src/{api.rs,conformance.rs,converter.rs,interpreter.rs,lib.rs,mem.rs,program.rs,range.rs,scalar_value.rs,verifier.rs,visitor.rs}`).
- **Anneal Prefix-Safety Scalar MIR Verification Pipeline**: `joshlf/anneal@f2bc17e9be87b777d63c785b31f3370ff058d69b` (`trusted/lean/Trusted/Mvp/{Syntax,Semantics,Theorem}.lean`, `trusted/rustc-capture/src/{capture.rs,extract.rs}`, `theory/Anneal/Mvp/{Execution,Step}.lean`).
- **Rust Nightly Compiler**: `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, `--edition=2021 -C opt-level=0 -C debug-assertions=off -C overflow-checks=no`).
- **The Rust Reference**: `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`.
- **Lean 4 Kernel**: `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).

## Findings

### 1. Non-Short-Circuiting `Runtime(PostCleanup)` MIR Census Across All `1,052` Bodies in Starnix `ebpf_core`

#### 1.1 Global Construct Gap Histogram and Tier 0–4 Milestone Hierarchy
Running [`support/mir_probe.rs`](support/mir_probe.rs) ([`support/mir_probe_out.json`](support/mir_probe_out.json) and [`support/candidate_mir_extracts.txt`](support/candidate_mir_extracts.txt)) across the 10-file Starnix `ebpf_core` source bundle (`1,052` MIR bodies: `879` `Fn`/`AssocFn`/`Closure` bodies and `173` `Const`/`AnonConst` bodies) inventories every MIR construct per body without short-circuiting on the first refusal:

| Milestone Tier | Construct Extensions Required Beyond Baseline `Trusted.Mvp` | Functions Unlocked | Representative Starnix `ebpf_core` Targets |
| :--- | :--- | :---: | :--- |
| **Tier 0 (Zero TCB Changes)** | *None* (already captured with `status: "captured"` by baseline `anneal-rustc-capture`) | **`17`** (`16` new + `apply_endianness`) | `U64Range::mask_low_bits`, `U32Range::mask_low_bits`, `verifier::popcount_u64`, `interpreter::swap_bytes`, `interpreter::extract_bit`, `interpreter::sign_extend` |
| **Tier 0.5 (Phase 1 Capture Adapter Only)** | `tcx.const_eval_resolve` on `mir::Const::Unevaluated` (`u32::MAX`) | `+1` (`18`) | `verifier::saturating_inc_u32` |
| **Tier 1 (`EbpfInstruction` Accessors & Mutators)** | 1-field `#[repr(C)]` struct `Ty.struct1`, copy-in/copy-out `&T`/`&mut T` (`Ty.ref`), `ProjectionElem.{deref, field 0}`, `Rvalue.castInt` (`IntToInt`), `UnOp.not`, `Terminator.panic` | `+11` (`29`) | `EbpfInstruction::{get, code, set_code, dst_reg, set_dst_reg, src_reg, set_src_reg, offset, set_offset, imm, set_imm}` |
| **Tier 2 (`U64Range` & `U32Range` Interval Domain)** | Multi-field value structs (`min`, `max`), tuple `(T, bool)` + `CheckedBinaryOp`, associated constants (`U64Range::MAX`), non-recursive `TerminatorKind::Call` summaries / inlining (`overflowing_add`, `overflowing_sub`, `Ord::min`) | `+24` (`53`) | `U64Range::{new, max, is_Canonical, add_range, sub_range, rem_range}`, `U32Range::{new, max, add_range, sub_range}` |
| **Tier 3 (`U64ScalarValueData` Tnum + `unwritten_mask` Domain)** | 4-field nested struct (`value`, `unknown_mask`, `unwritten_mask`, `urange: U64Range`), `u64::leading_zeros` intrinsic/call, 4-level acyclic call DAG composition | `+18` (`71`) | `U64ScalarValueData::{new, from_known, is_known, is_zero, is_uninitialized, is_fully_initialized, bitand_raw, bitor_raw, bitxor_raw, bitand_scalar, bitor_scalar, bitxor_scalar}` |

#### 1.2 First-Refusal Diagnostic vs. Complete Transitive Construct Inventory
| Candidate Function | `anneal-rustc-capture` First-Refusal Diagnostic | Complete Non-Short-Circuiting Body + Callee Inventory (`support/mir_probe_out.json`) |
| :--- | :--- | :--- |
| `U64Range::mask_low_bits(u64, u32) -> u64` | **`status: "captured"`** (0 gaps) | `7` BBs (`bb0..bb6`), `32` stmts; `Eq`, `Ge`, `BitAnd`, `Lt`, `Shl`, `Sub`; `bb6: Unreachable` (guarded by `bit_count < 64`). **Zero gaps.** |
| `verifier::popcount_u64(u64) -> usize` | **`status: "captured"`** (0 gaps) | `4` BBs (`bb0..bb3`), `26` stmts; cyclic `while x != 0` loop (`bb1 -> bb2 -> bb1`); `Ne`, `Sub`, `BitAnd`, `Add`. **Zero gaps.** |
| `verifier::saturating_inc_u32(u32) -> u32` | `body requires constant evaluation` | `4` BBs, `9` stmts; sole gap is `u32::MAX` as `mir::Const::Unevaluated` in `body.required_consts` and `Operand::Constant`. |
| `EbpfInstruction::code(&self) -> u8` | `parameter 1 uses unsupported type: &api::EbpfInstruction` | `1` BB, `3` stmts: `_2 = copy ((*_1).0)` (`Deref`, `Field(0, u64)`), `_0 = move _2 as u8 (IntToInt)`. **0 calls, 0 loops.** |
| `EbpfInstruction::set_code(&mut self, u8)` | `parameter 1 uses unsupported type: &mut api::EbpfInstruction` | `1` BB, `13` stmts: `Deref`, `Field(0, u64)`, `UnOp::Not(255_u64)`, `BitAnd`, `CastKind::IntToInt(u8 -> u64)`, `BitOr`, `((*_1).0) = move _5`. **0 calls, 0 loops.** |
| `EbpfInstruction::offset(&self) -> i16` / `set_offset(&mut self, i16)` | `parameter 1 uses unsupported type: &api::EbpfInstruction` | `2` BBs (`bb1` calls `panic_const_shr_overflow` on dead shift `16 >= 64` check); `Deref`, `Field(0, u64)`, `Shr(16)`, `CastKind::IntToInt(u64 -> u16 -> i16` and `i16 -> u16 -> u64)`, `Shl(16)`, `BitAnd`, `BitOr`. |
| `U64Range::add_range(&self, &Self) -> Self` | `parameter 1 uses unsupported type: &scalar_value::U64Range` | `7` BBs, `42` stmts: `&U64Range`, `Deref`/`Field(0..1)`, `(u64, bool)` tuple fields, `Aggregate(Adt U64Range)`, associated const `U64Range::MAX`, and `Call`s to `u64::overflowing_add` (which uses `CheckedBinaryOp(Add)`), `U64Range::max`, and `U64Range::new`. |
| `U64ScalarValueData::bitand_scalar(self, Self) -> Self` | `parameter 1 uses unsupported type: scalar_value::U64ScalarValueData` | `6` BBs, `29` stmts + 4-level call DAG (`bitand_scalar -> bitand_raw -> new -> {u64::leading_zeros, U64Range::mask_low_bits, Ord::min, Ord::max}`): nested struct `Field` projections (`_1.0.._1.3.1`), `&u64` refs for `Ord::min`/`max`, `UnOp::Not`, `BitAnd`, `BitOr`, `BitXor`, `Sub`. |

Basis: **source** and **execution** ([`support/mir_probe.rs`](support/mir_probe.rs), [`support/mir_probe_out.json`](support/mir_probe_out.json), [`support/candidate_mir_extracts.txt`](support/candidate_mir_extracts.txt)).

---

### 2. End-to-End Tier 0 Starnix Proofs (`U64Range::mask_low_bits` and Cyclic-CFG `verifier::popcount_u64`)

#### 2.1 `scalar_value::U64Range::mask_low_bits` (`support/starnix-mask-low-bits/`)
In [`support/starnix-mask-low-bits/Spec.lean`](support/starnix-mask-low-bits/Spec.lean) and [`support/starnix-mask-low-bits/Proof.lean`](support/starnix-mask-low-bits/Proof.lean) ([`support/receipt_mask_low_bits.json`](support/receipt_mask_low_bits.json)), we verified `U64Range::mask_low_bits` end-to-end (`status: "selected_unit_verified"`, standalone `lean` compile `3.82 s`, full `cargo-anneal verify` `16.68 s`), proving both `UnitTheorem` (`Safe`) and full symbolic execution across all 3 paths (`bit_count == 0`, `bit_count >= 64`, and `0 < bit_count < 64`):

```lean
def maskLowBitsSpec (value bitCount : Word) : Word :=
  if bitCount == 0#64 then 0#64
  else if decide (bitCount.toNat >= 64) then value
  else value &&& ((1#64 <<< bitCount) - 1#64)

theorem exec_mask_low_bits (value bitCount : Word) (hbc : ValidU32 bitCount) :
    Executes maskBody (initial maskBody [value, bitCount]) (maskLowBitsSpec value bitCount)
```

While constructing `exec_mask_low_bits`, we measured the elaboration scaling of `runN_executes (n := k) rfl` over symbolic `State`:
- $k = 5$ (`bb0 -> bb1`): `77 ms`; $k = 6$ (`bb0 -> bb2`): `273 ms`; $k = 8$ (`bb2 -> return`): `5,648 ms` ($20\times$ slower than $k = 6$); $k = 10$: timeout at `>200,000` heartbeats (`>15 s`).
- Chaining `runN_executes` in chunks of $k \le 6$ steps with flattened `State` literals between chunks eliminates nested `List.set` spine re-traversal and keeps every step chunk under `450 ms`.

#### 2.2 Cyclic-CFG `verifier::popcount_u64` (`support/starnix-popcount-u64/`)
In [`support/starnix-popcount-u64/Spec.lean`](support/starnix-popcount-u64/Spec.lean) and [`support/starnix-popcount-u64/Proof.lean`](support/starnix-popcount-u64/Proof.lean) ([`support/receipt_popcount_u64.json`](support/receipt_popcount_u64.json)), we verified `verifier::popcount_u64` end-to-end (`status: "selected_unit_verified"`, standalone `lean` compile `3.21 s`, full `cargo-anneal verify` `14.87 s`), mechanizing **both** cyclic-CFG verification styles side by side:
1. **Style A — Coinductive Prefix-Safety Invariant (`safeFrom_invariant PopcountInv`)**:
   Defines a 30-state inductive invariant `PopcountInv : State → Prop` over `bb0` (`4` states), `bb1` (`6` states), `bb2` (`17` states, enforcing `x ≠ 0` so `_6 = x - 1` never underflows), and `bb3` (`3` states). `popcountInv_step` closes in `8` lines of tactic script without requiring any ranking function or termination measure, proving `popcount_safe_via_invariant : ∀ x, Safe popBody [x]`.
2. **Style B — Well-Founded Fuel Induction (`Executes` via `kernighan_lt`)**:
   Proves Brian Kernighan's bit-clearing termination lemma `kernighan_lt (hx : x ≠ 0#64) : (x &&& (x - 1#64)).toNat < x.toNat` and uses `Nat.strongRecOn` on `x.toNat` to prove `exec_popcount : ∀ x, Executes popBody (initial popBody [x]) (popcountSpec x)` (`Safe` + `Returns` + recursive functional equation `popcountSpec x = popcountSpec (x &&& (x - 1#64)) + 1#64` for `x ≠ 0#64`).

Basis: **source** and **execution** ([`support/starnix-mask-low-bits/Proof.lean`](support/starnix-mask-low-bits/Proof.lean), [`support/starnix-popcount-u64/Proof.lean`](support/starnix-popcount-u64/Proof.lean), [`support/receipt_mask_low_bits.json`](support/receipt_mask_low_bits.json), [`support/receipt_popcount_u64.json`](support/receipt_popcount_u64.json)).

---

### 3. Minimal Semantic & Capture Delta for `EbpfInstruction` (`support/EbpfInstructionExtensionProbe.lean`)

In [`support/EbpfInstructionExtensionProbe.lean`](support/EbpfInstructionExtensionProbe.lean) (`567` lines, `0` `sorry`, `6.67 s` compile), we mechanized the minimal extension to `Trusted.Mvp.{Syntax,Semantics}` required to execute and verify all `11` methods of `#[repr(C)] struct EbpfInstruction(u64)`:
- **Types and Projections**: `Ty.struct1 (inner : Ty)`, `Ty.ref (mutable : Bool) (pointee : Ty)`, `ProjectionElem.deref`, `ProjectionElem.field (idx : Nat)`, and `Place { local : Nat, projection : List ProjectionElem }`. Under copy-in/copy-out reference semantics for non-aliasing 1-field structs, reading/writing `((*_1).0)` accesses local `1`'s 64-bit word directly, and `&mut self` mutators expose the post-state word via `ExecutesMut body state retVal mutatedSelf`.
- **Two's-Complement `evalCastInt`**:
  ```lean
  def evalCastInt (srcTy dstTy : Ty) (w : Word) : Option Word :=
    match srcTy, dstTy with
    | .int srcBits srcSigned, .int dstBits _ =>
        let val : Int := if srcSigned then decodeSigned srcBits w else Int.ofNat w.toNat
        some (encodeSigned dstBits val)
    | _, _ => none
  ```
  Proving `cast_u16_to_i16_eq_self`, `cast_i16_to_u16_eq_self`, `cast_u32_to_i32_eq_self`, and `cast_i32_to_u32_eq_self` establishes why Starnix's `set_offset` (`val as u16 as u64`) and `set_imm` (`val as u32 as u64`) zero-extend the low 16/32 bits without sign-extending into adjacent bitfields.
- **Verified Theorems (`38` Theorems Total)**:
  - Symbolic execution for all `6` getters (`exec_get`, `exec_code`, `exec_dst_reg`, `exec_src_reg`, `exec_offset`, `exec_imm`) and all `5` mutators (`exec_set_code`, `exec_set_dst_reg`, `exec_set_src_reg`, `exec_set_offset`, `exec_set_imm`);
  - All `15` bitfield lens laws (`get_put_*`, `put_get_*`, `put_put_*` for `code`, `dst_reg`, `src_reg`, `offset`, `imm`);
  - Cross-field frame preservation (`set_code_preserves_{dst_reg,src_reg,offset,imm}`); and
  - Unconditional `< 16` register bounds (`dstRegSpec_lt_16`, `srcRegSpec_lt_16`).

Basis: **source** and **execution** ([`support/EbpfInstructionExtensionProbe.lean`](support/EbpfInstructionExtensionProbe.lean)).

---

### 4. Mechanized Abstract-Domain Soundness (`U64Range` & `U64ScalarValueData`) and Host-vs-Guest Duality (`support/StarnixAbstractDomainSoundness.lean`)

In [`support/StarnixAbstractDomainSoundness.lean`](support/StarnixAbstractDomainSoundness.lean) (`680` lines, `0` `sorry`, `1.47 s` compile), we mechanized Starnix's `range.rs` and `scalar_value.rs` abstract domains and proved three families of theorems:

1. **Wrapping 64-Bit Interval Soundness (`U64Range`)**:
   - `add_range_wf` & `add_range_sound`, `sub_range_wf` & `sub_range_sound`: When `min_overflowed == max_overflowed` (either neither endpoint wraps or both endpoints wrap across $2^{64}$), `[self.min ± rhs.min, self.max ± rhs.max]` modulo $2^{64}$ soundly bounds `x ± y`; when `min_overflowed != max_overflowed`, the sum/difference straddles $2^{64}$ and falls back to `maxRange` (`[0, u64::MAX]`).
   - `rem_range_wf`, `rem_range_sound_nonzero`, and `rem_range_sound_ebpf`: Formalizes why Starnix's `rem_range` returns `self` when `rhs.max == 0` and sets `max = self.max` (rather than `min(self.max, rhs.max - 1)`) when `rhs.min == 0`: in the eBPF ISA (`BPF_MOD`), unsigned remainder by zero does not trap and instead leaves the dividend `x` unchanged (`ebpfRem x 0 = x`).
2. **Tnum + `unwritten_mask` + Interval Soundness (`U64ScalarValueData`)**:
   - Formalizes the two-part representation invariant `MaskWF` (`value &&& unknown_mask = 0#64` and `unwritten_mask &&& ~~~unknown_mask = 0#64`, i.e., $\text{unwritten\_mask} \subseteq \text{unknown\_mask}$).
   - Proves `newWithCommonMask_maskWF`, `bitand_raw_maskWF`, `bitor_raw_maskWF`, `bitxor_raw_maskWF`, `bitand_raw_sound`, `bitor_raw_sound`, and `bitxor_raw_sound`.
3. **Formal Host-vs-Guest Initialization and Lattice Polarity Contrast**:
   - **Guest eBPF (`U64ScalarValueData`)**: Uninitialized bits are tracked bit-by-bit in `unwritten_mask` (`UNINITIALIZED` has `unwritten_mask = u64::MAX`). Bitwise `AND` with `0` (`guest_bitand_zero_uninitialized_initializes`) and bitwise `OR` with `u64::MAX` (`guest_bitor_allOnes_uninitialized_initializes`) absorb `unwritten_mask` to `0`, turning an uninitialized register into a fully initialized constant (`from_known 0` / `from_known maxU64`), whereas non-relational `bitxor_raw UNINITIALIZED UNINITIALIZED` remains `UNINITIALIZED` (`guest_bitxor_uninitialized_remains_uninitialized`; Starnix handles same-register `r ^= r` in `verifier.rs` before calling `bitxor_scalar`). In Starnix's state-pruning order (`moreGeneralOrEqual`), `UNINITIALIZED` is the **Top (`⊤`)** element (`guest_uninitialized_is_top`).
   - **Host Rust (`Trusted.Mvp.Semantics`)**: Uninitialized state is tracked per-local via `Slot.uninit`. Because `evalRvalue` evaluates both operands via `evalOperand` before `evalBinary`, `0 & uninit` faults immediately with `.fault .uninitialized` (`host_bitand_zero_uninit_faults`), and `Slot.uninit` is the **Bottom (`⊥`)** element of the host definedness order (`host_uninit_is_bottom`, `host_value_not_le_uninit`).

Basis: **source** and **execution** ([`support/StarnixAbstractDomainSoundness.lean`](support/StarnixAbstractDomainSoundness.lean)).

## Boundaries

- **Known not to apply (copy-in/copy-out `&mut T` semantics for aliasing mutable references)**: The zero-heap copy-in/copy-out reference model in `EbpfInstructionExtensionProbe.lean` (`ExecutesMut`) is sound for single-reference methods (`&self` and `&mut self` on `EbpfInstruction`), which Rust's borrow checker guarantees do not alias any other argument, but does not model reborrowing through structs holding references or interior mutability (`UnsafeCell`).
- **Known not to apply (non-relational `bitxor_raw` for `r ^= r`)**: `bitxor_raw UNINITIALIZED UNINITIALIZED` returns `UNINITIALIZED` because `bitxor_raw` is a non-relational binary transformer on two independent abstract values; clearing a register via `xor dst, dst` is handled relationally when `dst == src` in `verifier.rs`.
- **Not examined (full `VerificationContext` worklist fixpoint and packet/map pointer domains)**: `StarnixAbstractDomainSoundness.lean` mechanizes the scalar value domain (`U64Range` and `U64ScalarValueData`); pointer-offset tracking (`Type::PtrToMemory`, `Type::PtrToPacket`) and `verify_worklist_entry` require heap/collection models (`HashMap`, `Vec`, `Arc`) beyond Tier 3.

## Evidence

All `rustc_driver` census probes, end-to-end verified Starnix proof fixtures, JSON verification receipts, and standalone Lean `v4.34.1` mechanizations are preserved under `support/`:

1. **Whole-Crate `Runtime(PostCleanup)` MIR Census Probe and Extracts**:
   - [`support/mir_probe.rs`](support/mir_probe.rs), [`support/mir_probe_out.json`](support/mir_probe_out.json), and [`support/candidate_mir_extracts.txt`](support/candidate_mir_extracts.txt).
2. **End-to-End Tier 0 Verified Fixtures and Receipts (`U64Range::mask_low_bits` & `verifier::popcount_u64`)**:
   - [`support/starnix-mask-low-bits/request.json`](support/starnix-mask-low-bits/request.json), [`support/starnix-mask-low-bits/Spec.lean`](support/starnix-mask-low-bits/Spec.lean), [`support/starnix-mask-low-bits/Proof.lean`](support/starnix-mask-low-bits/Proof.lean), and [`support/receipt_mask_low_bits.json`](support/receipt_mask_low_bits.json).
   - [`support/starnix-popcount-u64/request.json`](support/starnix-popcount-u64/request.json), [`support/starnix-popcount-u64/Spec.lean`](support/starnix-popcount-u64/Spec.lean), [`support/starnix-popcount-u64/Proof.lean`](support/starnix-popcount-u64/Proof.lean), and [`support/receipt_popcount_u64.json`](support/receipt_popcount_u64.json).
3. **Mechanized `EbpfInstruction` Extension and Bitfield Lens Laws (`567` lines, `0` `sorry`)**:
   - [`support/EbpfInstructionExtensionProbe.lean`](support/EbpfInstructionExtensionProbe.lean).
4. **Mechanized `U64Range` & `U64ScalarValueData` Soundness and Host-vs-Guest Contrast (`680` lines, `0` `sorry`)**:
   - [`support/StarnixAbstractDomainSoundness.lean`](support/StarnixAbstractDomainSoundness.lean).

## Revalidation

1. **Re-verify the standalone Lean `v4.34.1` mechanizations (`EbpfInstructionExtensionProbe.lean` and `StarnixAbstractDomainSoundness.lean`)**:
   ```bash
   lean -DwarningAsError=true support/EbpfInstructionExtensionProbe.lean
   lean -DwarningAsError=true support/StarnixAbstractDomainSoundness.lean
   ```
2. **Re-verify the end-to-end Tier 0 Starnix fixtures (`starnix-mask-low-bits` and `starnix-popcount-u64`)**:
   Stage `support/starnix-mask-low-bits/` and `support/starnix-popcount-u64/` alongside the 10-file Starnix `ebpf_core` source bundle (`fuchsia@823a15538f191b9dbd9ebafaa6ba23220b87d2e1`) and run `cargo-anneal verify --request request.json`, confirming `status == "selected_unit_verified"` and `axioms == ["propext", "Classical.choice", "Quot.sound"]`.
3. **Re-run the non-short-circuiting `Runtime(PostCleanup)` MIR census**:
   Compile [`support/mir_probe.rs`](support/mir_probe.rs) against `librustc_driver` (`rustc 1.98.0-nightly`) and run it on `ebpf_core/src/lib.rs --edition=2021 -C opt-level=0 -C debug-assertions=off -C overflow-checks=no`.
