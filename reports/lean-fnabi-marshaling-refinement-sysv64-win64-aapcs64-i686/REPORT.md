# Mechanized `FnAbi` Classification and Bidirectional Caller/Callee Marshaling Refinement in Lean 4

## Summary

Generalizing the single-register `sysvEntryState` boundary (`SEAM-4`) into the `731`-line (`680` code lines, `4,265,352`-byte `.olean`, `247.18 ms` build time, `0` `sorry`, `0` `native_decide`) Lean `v4.34.1` mechanization [`support/LeanFnAbiRefinement/LeanFnAbiRefinement.lean`](support/LeanFnAbiRefinement/LeanFnAbiRefinement.lean) and cross-validating its executable `#eval` classifiers against `rustc 1.99.1` across all `8` Tier 1 targets (`2,048` procedural target-signature pairs in [`support/verify_fnabi_oracle.py`](support/verify_fnabi_oracle.py) and [`support/fnabi_refinement_metrics.json`](support/fnabi_refinement_metrics.json)) establishes:

1. **Executable Lean 4 Mechanization of `rustc_target::callconv` (`FnAbi`) Across All 8 Tier 1 Targets:**
   - Models `RegKind` (`Integer`, `Float`, `Vector`), `Reg` (`i8..i128`, `f16..f128`, `v64..v256`), `ArgExtension` (`None`, `Zext`, `Sext`), `ArgAttributes` (`inReg`, `nonNull`, `noUndef`, `pointeeSize`, `pointeeAlign`), `CastTarget` (`single`, `pair`, `uniform`), `PassMode` (`Ignore`, `Direct`, `Pair`, `Cast`, `Indirect`), and `TyLayout` (`sizeBytes`, `alignBytes`, `unadjustedAlignBytes`, `passIndirectlyInNonRustic`, `BackendReprKind`).
   - Implements executable classifiers for System V AMD64 (`classifySysV64`), Windows x64 (`classifyWin64`, parameterized by `isMingwFix` and `isVectorcall`), AArch64 (`classifyAapcs64` across `AapcsKind.{AAPCS, DarwinPCS, Win64}`), and 32-bit x86 (`classifyI686` across `I686Conv.{Cdecl, Stdcall, Fastcall, Thiscall, Vectorcall}` and `isMsvc`).
2. **`100.0%` Differential Oracle Agreement Across All `2,048` Tier 1 Target-Signature Pairs (`8` Targets $\times$ `256` Signatures):**
   - `classifySysV64` captures the exact `ABI-03` 6th-GPR `u128` straddling rule (`compiler/rustc_target/src/callconv/x86_64.rs:210-224`): when `intAvail == 1` (`%r9`), a 16-byte `ScalarInt 16` (`u128`) argument spills to `stackSlot stkIdx` while leaving `intAvail = 1` intact so a subsequent 64-bit integer argument is backfilled into `.gpr 5` (`%r9`).
   - `classifyAapcs64` captures the `ABI-05` Linux `AAPCS` vs. `DarwinPCS` inversion between `u128` (even-aligned `.gprPair 2 3` on Linux/WinARM64 vs. `.gprPair 1 2` on Darwin) and `#[repr(C, align(16))] struct Align16Pair(u64, u64)` (`unadjustedAlignBytes = 8` $\to$ `.gprPair 1 2` on Linux vs. `alignBytes = 16` $\to$ `.gprPair 2 3` on Darwin), as well as `sretX8` (`XR` in `x8`) leaving all 8 argument registers `x0..x7` unconsumed.
   - `classifyWin64` captures both `rustc 1.99.1`'s `ABI-01` behavior (`isMingwFix = false` $\to$ `.sretGpr 0` in `%rcx`) and the corrected MinGW `f128` rule (`isMingwFix = true` $\to$ `.fpVec 0` in `%xmm0`), plus mandatory indirect passing for ZSTs and aggregates whose byte size is not in $\{1, 2, 4, 8\}$.
   - `classifyI686` captures the Linux `cdecl` vs. MSVC 8-byte aggregate return difference (`.sretStackSlot0` with `calleePopBytes = 4` via `ret $4` on SysV i386 vs. `.gprPair 0 1` in `eax:edx` with `calleePopBytes = 0` on MSVC) and `fastcall`/`stdcall`/`thiscall`/`vectorcall` `inreg` (`%ecx, %edx`) and `ret imm16` stack cleanup.
3. **Kernel-Checked Caller/Callee Marshaling Refinement Theorems (`[propext, Quot.sound]` Only):**
   - Proves `readLoc_writeLoc_id`, `writeLoc_preserves_calleeSaved`, `writeLoc_preserves_spOffset`, `readLoc_with_spOffset`, `abi_locations_disjoint`, `decode_encode_call_args_id`, and `decode_encode_ret_id` over `CallMachineState`, discharging `SEAM-4` across direct registers, register pairs, mixed GPR+XMM eightbytes, stack slots, `byval` stack copies, indirect pointer buffers, and `sret` (`%rdi`, `%rcx`, `x8`, and `[esp]`) with callee stack-pop (`ret $4` / `ret imm16`) restoration.

## Applicability

- **Extends:** `tier1-exhaustive-procedural-abi-differential-campaign-and-fixes`, `tier1-calling-conventions-fnabi-and-llvm-lowering`, `configured-rust-capture-fnabi-placement-and-formality-specr-boundaries`, `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`, `anneal-mir-to-x86-compiler-vcgen-and-variable-step-refinement`
- **Subjects Examined:**
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`);
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `compiler/rustc_target/src/callconv/`).

## Findings

### 1. Target Classifier Architecture and Edge-Case Rules (`LeanFnAbiRefinement.lean`)

`Basis: execution + source (support/LeanFnAbiRefinement/LeanFnAbiRefinement.lean, support/verify_fnabi_oracle.py, compiler/rustc_target/src/callconv/)`

| Classifier Function | `rustc_target` Source Counterpart | Register State Tracked | Key Edge-Case Invariants Mechanized and Verified via `#eval checkAll` |
| :--- | :--- | :--- | :--- |
| `classifySysV64` | `callconv/x86_64.rs:178-270` | `(intAvail : 0..6, sseAvail : 0..8, stkIdx)` | `sretGpr 0` (`%rdi`) initializes `intAvail := 5`; `ScalarInt 16` (`u128`) requires `intAvail >= 2` and otherwise spills to `stackSlot stkIdx` **without** decrementing `intAvail` (`ABI-03` `%r9` backfilling); `hasUnaligned` (`ABI-04`) or `intAvail < needInt \|\| sseAvail < needSse` rolls back the entire aggregate to `byvalStack`. |
| `classifyWin64` | `callconv/x86_win64.rs:8-70` | Coupled `(slot : Nat, bufId : Nat)` + `shadowSpaceBytes = 32` | `sretGpr 0` (`%rcx`) advances `startSlot := 1`; non-power-of-two aggregates (`size ∉ {1,2,4,8}`) and ZSTs lower to `indirectPtrGpr slot bufId` / `indirectPtrStack`; `ScalarInt 16` returns in `.fpVec 0` (`%xmm0`); `isMingwFix` switches `ScalarFloat 16` (`f128`, `ABI-01`) from `.sretGpr 0` to `.fpVec 0`; `isVectorcall` enables `.fpVecBlock slot cnt` up to 4 elements. |
| `classifyAapcs64` | `callconv/aarch64.rs:19-191` | `(gprIdx : 0..8, fpIdx : 0..8, stkIdx)` + `AapcsKind` | Indirect returns use `.sretX8` (`x8`), leaving `gprIdx := 0` (`x0..x7` all available); 1..4 element HFA/HVA uses `.fpVecBlock fpIdx cnt` or saturates `fpIdx := 8`; non-HFA composites $\le 16\text{ B}$ (including `PackedCross8`, `ABI-04`) pass in `i64`/`i128` chunks; `AAPCS` uses `unadjustedAlignBytes` for aggregates and even-aligns `u128`, whereas `DarwinPCS` uses `alignBytes` for `#[repr(align(16))]` aggregates and tightly packs `u128` (`ABI-05`). |
| `classifyI686` | `callconv/x86.rs` & `x86_win32.rs` | `(freeRegs : 0..2, stkIdx)` + `calleePopBytes` | Linux `cdecl` returns every composite via `.sretStackSlot0` and sets `calleePopBytes := 4` (`ret $4`), whereas MSVC returns 1/2/4/8-byte structs in `eax` / `eax:edx` (`calleePopBytes := 0`); `Fastcall`/`Vectorcall` allocate 2 `inReg` GPRs (`%ecx, %edx`) and `Thiscall` allocates 1 (`%ecx`), setting `calleePopBytes := endStackSlot * 4` (`ret imm16`). |

---

### 2. Kernel-Checked Marshaling Refinement Theorems and Build Metrics

`Basis: execution (support/LeanFnAbiRefinement/LeanFnAbiRefinement.lean, support/fnabi_refinement_metrics.json)`

| Theorem Name | Statement Summary | Proof Strategy | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `readLoc_writeLoc_id` | `wfLocForVal loc v → readLoc (writeLoc st loc v) loc v = v` | Exhaustive case split over `Option AbiLoc` (13 constructors) and `MirVal` (5 constructors) with `omega` for `.gprPair i j` (`i ≠ j`). | `[propext, Quot.sound]` |
| `writeLoc_preserves_calleeSaved` | `(writeLoc st loc v).calleeSaved = st.calleeSaved` | Structural case analysis over `loc` and `v`; no ABI argument/return write touches `calleeSaved`. | `(none — definitional / Eq.refl)` |
| `writeLoc_preserves_spOffset` | `(writeLoc st loc v).spOffset = st.spOffset` | Structural case analysis over `loc` and `v`. | `(none — definitional / Eq.refl)` |
| `readLoc_with_spOffset` | `readLoc { st with spOffset := sp' } loc v = readLoc st loc v` | Structural case analysis showing location reads are invariant under stack-pointer delta updates. | `(none — definitional / Eq.refl)` |
| `abi_locations_disjoint` | `i ≠ j → readLoc (writeLoc (writeLoc st (.gpr i) (.word v1)) (.gpr j) (.word v2)) (.gpr i) (.word v1) = .word v1` | Simplifies nested functional updates on `st.gprs` and discharges `j = i` via `hne`. | `[propext, Quot.sound]` |
| `decode_encode_call_args_id` | `wfLocForVal loc v → (marshalStep st loc v).2 = v ∧ (marshalStep st loc v).1.calleeSaved = st.calleeSaved` | Combines `readLoc_writeLoc_id` and `writeLoc_preserves_calleeSaved` for each marshaled parameter. | `[propext, Quot.sound]` |
| `decode_encode_ret_id` | `let stFinal := executeCallReturn abi st retVal; readLoc stFinal abi.ret.loc retVal = retVal ∧ stFinal.spOffset = st.spOffset ∧ stFinal.calleeSaved = st.calleeSaved` | Rewrites with `readLoc_with_spOffset` and `writeLoc_preserves_spOffset`, then closes `st.spOffset - pushedBytes + pushedBytes = st.spOffset` via `omega`. | `[propext, Quot.sound]` |

- **Artifact Compilation Metrics (`support/fnabi_refinement_metrics.json`):**
  - Lean toolchain: `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
  - Source size: `731` total lines (`680` non-comment, non-blank code lines); compiled `LeanFnAbiRefinement.olean`: `4,265,352` bytes; warm build time: `247.18 ms`.
  - Axiom and soundness audit: `0` `sorry`, `0` `native_decide`, `#eval checkAll = true`, and `100.0%` agreement across all `2,048` Tier 1 target-signature pairs.

## Boundaries

- **Bit-Level Sub-Eightbyte Packing (`abstracted` via `MirVal`):** `CallMachineState` models coerced eightbytes, register pairs, stack slots, and indirect buffers using structured `MirVal` words/pairs/quads rather than bit-sliced byte arrays; bit-level packing of two `f32` fields into a single 64-bit `Reg.i64` / `Reg.f64` eightbyte is handled prior to `writeLoc` by the `CastTarget` coercion step.
- **Unstable Scalable Vector (`SVE` / `RVV`) Calling Conventions (`excluded`):** Scalable vector registers (`z0..z31`, `p0..p15`) are outside `rustc 1.99.1`'s stable Tier 1 `FnAbi` contract.

## Evidence

- **Primary Upstream Sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_target/src/callconv/mod.rs:1-620` (`RegKind`, `Reg`, `ArgExtension`, `ArgAttributes`, `CastTarget`, `PassMode`, `ArgAbi`, `FnAbi`).
  - `compiler/rustc_target/src/callconv/x86_64.rs:178-270` (System V AMD64 eightbyte classification and `int_regs` / `sse_regs` depletion).
  - `compiler/rustc_target/src/callconv/x86_win64.rs:8-70` (Windows x64 4-slot positional calling convention and `vectorcall`).
  - `compiler/rustc_target/src/callconv/aarch64.rs:19-191` (`AAPCS`, `DarwinPCS`, and `Win64` AArch64 classification).
  - `compiler/rustc_target/src/callconv/x86.rs:138-246` and `compiler/rustc_target/src/callconv/x86_win32.rs:1-136` (32-bit x86 `cdecl`, `stdcall`, `fastcall`, `thiscall`, and `vectorcall`).
- **Preserved Support Artifacts:**
  - [`support/LeanFnAbiRefinement/LeanFnAbiRefinement.lean`](support/LeanFnAbiRefinement/LeanFnAbiRefinement.lean): Self-contained Lean `v4.34.1` mechanization of `FnAbi` classification and caller/callee marshaling refinement.
  - [`support/verify_fnabi_oracle.py`](support/verify_fnabi_oracle.py): Build, axiom-audit, and `#eval` differential oracle verification script.
  - [`support/fnabi_refinement_metrics.json`](support/fnabi_refinement_metrics.json): Recorded Lean build metrics, `#print axioms` output, and differential oracle results.

## Revalidation

```bash
python3 reports/lean-fnabi-marshaling-refinement-sysv64-win64-aapcs64-i686/support/verify_fnabi_oracle.py
```

Verify that `lake build` succeeds with `0` warnings, `#eval checkAll` outputs `true`, `#print axioms` lists only `[propext, Quot.sound]`, and `sorry_count == 0` in `support/fnabi_refinement_metrics.json`.
