# RISC-V RVV, PowerPC AltiVec/VSX, LoongArch LSX/LASX, MIPS MSA/MMI, and WebAssembly SIMD ISA Formalizations

## Summary

Across the five non-`x86`/non-`Arm` SIMD architectures targeted by production multimedia codecs (`FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`), executable and mechanized vector ISA specifications partition sharply into **two architectures with complete executable formalizations (`riscv64` and `wasm`)** and **three architectures with zero formalized vector operational semantics (`ppc64le`, `loongarch64`, and `mips`)** (`Basis: source + derived`):

1. **`riscv64` (`RVV 1.0`, `Zba`, `Zbb`, `Zvbb`) — Complete Executable Sail + Extracted Lean 4, Blocked Only on `AGNOSTIC` Nondeterminism & Purification (`Basis: source`):**
   - `riscv/sail-riscv` (`ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`, BSD-2-Clause) implements the full RISC-V Vector 1.0 extension (`vset{i}vl{i}`, fractional/integral `LMUL` $\in \{1/8..8\}$, `SEW` $\in \{8, 16, 32, 64\}$, `vxrm` CSR `0x00A`, `vxsat` CSR `0x009`, `Zve32x`–`Zve64d`, unit/strided/indexed/segment/fault-only-first memory ops, integer/fixed-point/FP/reduction/mask instructions, and `Zvbb`/`Zvk*` vector crypto) alongside `Zba` and `Zbb`.
   - `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) **already compiles all 16 RVV modules (`LeanRV64D/Vext*.lean` + `Vector.lean`) and `ZbaInsts.lean`/`ZbbInsts.lean` into kernel-checked Lean 4 with zero `sorry` axioms**. However, two critical verification boundaries remain: (a) `sail-riscv` deterministically collapses tail-agnostic (`ta`) and mask-agnostic (`ma`) policies to `AGNOSTIC => vd_val[i] // TODO: configuration support` (`vext_arith_insts.sail:402, 871, 1301, 2014`), under-approximating RVV 1.0's nondeterministic `{undisturbed, all-1s}` specification on kernels like FFmpeg's `ff_h264_idct_add_8_rvv` (`vsetivli zero, 4, e16, mf2, ta, ma`), and (b) `opencompl/riscv-lean` (`0e3365ac7b670d79d70e9b4a8b7fba782607c44f`) purifies `Zba`/`Zbb` into pure `BitVec 64` operations (`RISCV/Instructions.lean`) while purifying **zero** RVV instructions.

2. **`wasm` (`SIMD128` & `relaxed-simd`) — Complete Executable SpecTec/OCaml Wasm 3.0 vs Uninterpreted Mechanized `WasmCert` Vector Ops (`Basis: source + execution`):**
   - `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`) and `Wasm-DSL/spectec` (`acc6e834ff403c82554d081237f327346190ad96`) provide complete formal specifications and executable interpreters for all `236` deterministic Wasm 2.0 `SIMD128` opcodes plus Wasm 3.0 `relaxed-simd` (`WebAssembly/relaxed-simd@c3f9359af2cd607cc46b0a3274f90ea52543a2f2`).
   - Crucially, **neither Isabelle nor Rocq mechanizes Wasm SIMD lane arithmetic inside the prover kernel**: `WasmCert/WasmCert-Isabelle` (`d9b4659c8b38879a5fc7e0213950751a61091908`, BSD-2-Clause) declares `v128 = 128 word` (`Wasm_Ast.thy:24`) but leaves `app_unop_vec_v`, `app_binop_vec_v`, `app_ternop_vec_v`, `app_test_vec_v`, and `app_shift_vec_v` as uninterpreted `consts` (`Wasm_Base_Defs.thy:137-138`) delegated at OCaml extraction time (`WebAssembly/code/README.md:3`), while `WasmCert/WasmCert-Coq` (`58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`, MIT + LGPL-2.1 `src/Parray/`) defines `v128 := bytes` (`theories/simd.v:25`) and axiomatizes `Parameter app_v*op_str` (`theories/simd_execute.v:15-20`) backed externally by `src/SIMD_ops.ml`. Furthermore, real execution on Node.js `v24.21.0` (`x86_64`) demonstrates that `WebAssembly/spec/interpreter/exec/eval_vec.ml:64, 84` evaluates only one deterministic projection of `relaxed-simd`, returning `0x0` and `+32767` where V8 on `x86_64` returns `0xa3` and `-32768`.

3. **`ppc64le` (`AltiVec`/`VMX` & `VSX`), `loongarch64` (`LSX` & `LASX`), and `mips` (`MSA` & `MMI`) — Complete Vector Formalization Vacuum (`Basis: source`):**
   - **PowerPC (`ppc64le`):** `open-power-sdk/PowerISA` (`ea48c49e9fe0271106e2e540cb6cbccad20c8afe`, Apache-2.0) extracts `380` Vector Facility (`VMX`) and `283` `VSX` entries into unparsed RTL strings in `ISA.json`, while `antonblanchard/microwatt` (`f341bed306a9a7281bf65200df8cc1f0a002617d`), `rems-project/sail` (`old/power/power.sail`), and `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`, `powerpc/Asm.v:33-65`, INRIA Non-Commercial) formalize scalar `GPR` + scalar `FPR` only (**zero** 128-bit `VR`/`VSR` registers).
   - **LoongArch (`loongarch64`):** `loongson/LoongArch-Documentation` (`e0d6592229d9e00e512bd28b688a7f20b171714f`, **CC-BY-NC-ND-4.0** restrictive license) leaves `docs/LoongArch-Vol2-EN.adoc` (*Volume 2: Vector Extensions*) as `*TBD*` (`L13`), and `loongson-community/loongarch-opcodes` (`e269905901feb91e13444c0ce4b52f6ea06e9969`) provides bitmask/format tables only (`717` `lsx.txt` + `735` `lasx.txt` lines) with zero operational semantics in any theorem prover.
   - **MIPS (`mips`):** `CTSRD-CHERI/sail-cheri-mips` (`13a9c3fb0c3f8d320d4f4650a63d23d3a8b12724`, BSD-2-Clause) and `coruus/L3` (`isa-models/mips/mips.spec`) formalize 64-bit scalar MIPS + CP0/TLB (+ CHERI), with **zero** MIPS SIMD Architecture (`MSA` 128-bit `w0..w31`) and **zero** Loongson `MMI`.

---

## Applicability

This report governs target-tier verification strategy, formal semantics reuse, and clean-rewrite architecture decisions across all five non-`x86`/non-`Arm` SIMD targets supported by `FFmpeg/FFmpeg` (`libavutil/cpu.h:65-118`):
- **`riscv64`:** `AV_CPU_FLAG_RVI`, `AV_CPU_FLAG_RVV_{I32,F32,I64,F64}`, `AV_CPU_FLAG_RVB_BASIC` (`Zba`/`Zbb`), `AV_CPU_FLAG_RVB`, `AV_CPU_FLAG_RV_ZVBB` (`libavutil/cpu.h:98-106`, `libavutil/riscv/{cpu.h,asm.S}`).
- **`ppc64le` / `ppc`:** `AV_CPU_FLAG_ALTIVEC` (`VMX`), `AV_CPU_FLAG_VSX` (Power ISA v2.06), `AV_CPU_FLAG_POWER8` (Power ISA v2.07) (`libavutil/cpu.h:65-67`, `libavutil/ppc/cpu.h:25-27`).
- **`loongarch64`:** `AV_CPU_FLAG_LSX` (128-bit `$vr0..$vr31`) and `AV_CPU_FLAG_LASX` (256-bit `$xr0..$xr31`) (`libavutil/cpu.h:94-95`, `libavutil/loongarch/cpu.h:28-29`).
- **`mips` / `mips64el`:** `AV_CPU_FLAG_MMI` (Loongson Multimedia Instructions) and `AV_CPU_FLAG_MSA` (128-bit MIPS SIMD Architecture) (`libavutil/cpu.h:90-91`, `libavutil/mips/cpu.h:25-26`).
- **`wasm32` / `wasm64`:** `AV_CPU_FLAG_SIMD128` (`libavutil/cpu.h:109`, `libavcodec/wasm/hevc/{idct.c,sao.c}`) plus Wasm 3.0 `relaxed-simd`.

To avoid repeating existing reference-corpus material, this report builds on and cross-references:
- `sail-isa-models-lean-backend-and-rv64d-decoding-framing` for `sail` Lean codegen architecture, `SailM` monad structure, and RV64D scalar decoding/framing;
- `opencompl-riscv-lean-lean-mlir-and-ship-your-interpreter-2026` for OpenCompl's scalar `RV64IM` + `Zba`/`Zbb`/`Zbs` `Lean-MLIR` dialect and `SailPureToInstructions` equivalence framework;
- `rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation` for compiler VLA autovectorization register-pressure and fault-only-first `vle*ff.v` speculation hazards;
- `direct-surface-operational-semantics-jscert-k-spectec-and-desugaring-proofs` for `Wasm-DSL/spectec`'s surface/IL/AL compilation pipeline (`Breitner et al., PLDI 2024`).

---

## Findings

### 1. Cross-ISA Formalization Taxonomy: Complete Executable vs Partial vs Missing Vector Semantics

`Basis: source + derived`

Every candidate repository across the five architectures falls into one of four rigorous maturity levels—**Level A** (mechanized theorem-prover kernel lane semantics), **Level B** (complete executable formal DSL/interpreter semantics), **Level C** (syntax/typing/encoding tables with uninterpreted or unformalized vector execution), or **Level D** (scalar-only model, vector extension absent):

| Target ISA & FFmpeg Vector Extensions | Candidate Repository / Artifact (Pinned SHA) | Maturity Level | Vector Register & Control State Modeled | License | Lean 4 Mechanization Status & Viability |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`riscv64`** (`RVV 1.0`, `Zve32x`–`Zve64d`, `Zba`, `Zbb`, `Zvbb`) | `riscv/sail-riscv` (`ec5200bd`) + `opencompl/sail-riscv-lean` (`51c635c4`) | **Level A** (with deterministic `AGNOSTIC` caveat) | `vr0..vr31` (`vlenbits`), `vtype` (`vill`, `vma`, `vta`, `vsew`, `vlmul`), `vl`, `vstart`, `vxrm` (`0x00A`), `vxsat` (`0x009`), `vlenb` | **BSD-2-Clause** (`sail-riscv/LICENCE:1-10`) | **Already in Lean 4 (`0` `sorry`):** 16 `LeanRV64D/Vext*.lean` + `ZbaInsts.lean` + `ZbbInsts.lean` files (~`9,500` LOC Lean). Needs nondeterministic `ta`/`ma` refinement. |
| **`riscv64`** (purified `BitVec` dialect) | `opencompl/riscv-lean` (`0e3365ac`) | **Level A for `Zba`/`Zbb`; Level D for `RVV`** | Pure `BitVec 64` scalar GPR semantics (`RISCV/Instructions.lean`, `760` LOC); **0** vector state | **Apache-2.0** | Native Lean 4 `Lean-MLIR` dialect; covers `RV64IM` + `Zba`/`Zbb`/`Zbs` (`SailToRV64.lean`), zero `RVV` ops. |
| **`wasm`** (`SIMD128` + Wasm 3.0 `relaxed-simd`) | `WebAssembly/spec` (`d0b2e8d5`) + `Wasm-DSL/spectec` (`acc6e834`) + `WebAssembly/relaxed-simd` (`c3f9359a`) | **Level B** (executable DSL + OCaml ref interpreter) | `v128` value stack/locals/globals + linear memory; deterministic `SIMD128` (`236` ops) + host-projected relational `relaxed-simd` (`20` ops) | **Apache-2.0** (`spectec`, W3C software) | **High viability (`~2,000` LOC Lean 4):** Fixed 128-bit width, zero flags/CSRs, pure lane functions (`eval_vec.ml`, `340` LOC + `v128.ml`), plus SpecTec Lean backend path. |
| **`wasm`** (Isabelle & Rocq mechanizations) | `WasmCert/WasmCert-Isabelle` (`d9b4659c`) & `WasmCert/WasmCert-Coq` (`58a3d3f8`) | **Level C** (mechanized typing/memory, **opaque** SIMD ALU) | Isabelle: `v128 = 128 word`, `consts app_binop_vec_v` (`Wasm_Base_Defs.thy:138`); Rocq: `v128 := bytes`, `Parameter app_vbinop_str` (`simd_execute.v:16`) | Isabelle: **BSD-2-Clause**; Coq: **MIT + LGPL-2.1** (`src/Parray/LICENSE.LGPL`) | **Low value for SIMD ALU reuse:** Both prove Wasm 2.0 type soundness over uninterpreted SIMD operators and delegate execution to unverified OCaml (`SIMD_ops.ml`); **0** `relaxed-simd`. |
| **`ppc64le`** (`AltiVec`/`VMX`, `VSX` ISA 2.06–3.1C) | `open-power-sdk/PowerISA` (`ea48c49e`) | **Level C** (scraped JSON strings, non-executable) | `380` `Vector Facility` + `283` `Vector-Scalar Extension Facility` JSON records (`ISA.json`, `122,699` lines) containing untyped pseudo-RTL text | **Apache-2.0** (`LICENSE:1-15`) | **Low (requires full parser + typechecker + hardware co-sim):** `README.md:9-10` warns schema is unstable; pseudo-RTL strings (`code: [...]`) are not typechecked or executable. |
| **`ppc64le`** (VHDL, Sail, & CompCert) | `antonblanchard/microwatt` (`f341bed3`), `rems-project/sail` (`97aa617d`), `AbsInt/CompCert` (`2685140b`) | **Level D** (scalar + FPU only; **0** `VMX`/`VSX`) | `GPR0..31`, `FPR0..31` (64-bit scalar), `CR`, `XER`, `VRSAVE` (`power.sail:177`); **0** `VR0..31` / `VSR0..63` | `microwatt`: **CC-BY-4.0**; `CompCert`: **INRIA Non-Commercial** (`powerpc/Asm.v:9`) | **None for SIMD.** `microwatt/README.md:199` lists `Vector/VMX/VSX` as unimplemented; `CompCert` `powerpc/Asm.v` is both scalar-only and non-commercial. |
| **`loongarch64`** (`LSX` 128-bit, `LASX` 256-bit) | `loongson/LoongArch-Documentation` (`e0d65922`) & `loongson-community/loongarch-opcodes` (`e2699059`) | **Level C** (encoding tables only; Vol 2 AsciiDoc `*TBD*`) | `lsx.txt` (`717` opcodes over `Vd`/`Vj`/`Vk`) & `lasx.txt` (`735` opcodes over `Xd`/`Xj`/`Xk`); **0** formal operational semantics anywhere | Docs: **CC-BY-NC-ND-4.0**; Opcodes: open community Go/text tables | **Blocked by specification & formalization vacuum:** No Sail, ASL, HOL, Rocq, Isabelle, ACL2, K, or Lean semantics exist; official manual repo carries CC-BY-NC-ND-4.0. |
| **`mips` / `mips64el`** (`MSA` 128-bit, Loongson `MMI`) | `CTSRD-CHERI/sail-cheri-mips` (`13a9c3fb`) & `coruus/L3` (`d6558e67` `isa-models/mips/`) | **Level D** (64-bit scalar + CP0/CHERI; **0** `MSA`/`MMI`) | `GPR[0..31]`, `HI`/`LO`, `CP0` TLB (`91` `ast` clauses in `mips_insts.sail`); **0** `MSA` `w0..w31` or `MSACSR` | **BSD-2-Clause** (`sail-cheri-mips/LICENCE:3-5`), **BSD-3-Clause** (`L3`) | **None for SIMD.** Scalar MIPS64 is mechanized, but `MSA` (`MD00867`) and `MMI` have zero formal ISA models. |

---

### 2. RISC-V (`riscv64`): Primary-Source Audit of `sail-riscv`, `sail-riscv-lean`, and `riscv-lean`

`Basis: normative + source`

FFmpeg's RISC-V backend (`libavutil/riscv/cpu.h:30-56`, `libavutil/riscv/asm.S:39-55`, `libavcodec/riscv/h264idct_rvv.S`, `libavcodec/riscv/vp9mc_rvv.S`) stands out from every other FFmpeg assembly backend because it writes **hand-crafted Vector-Length Agnostic (VLA) RVV 1.0 assembly** paired with `Zba`/`Zbb`/`Zbs` scalar address/bit-manipulation instructions (`archadd zba, zbb, zbs` at `asm.S:43`) and `Zvbb` vector bitmanip (`AV_CPU_FLAG_RV_ZVBB` at `libavutil/cpu.h:104`). For example, `ff_h264_idct_add_8_rvv` (`h264idct_rvv.S:47-55`) executes:
```asm
func ff_h264_idct_add_8_rvv, zve32x
        lpad    0
        csrwi       vxrm, 0
.Lidct4_add_8_rvv:
        vsetivli    zero, 4, e16, mf2, ta, ma
        addi        t1, a1, 1 * 4 * 2
        vle16.v     v0, (a1)
```

Auditing `riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` alongside `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f` and `opencompl/riscv-lean@0e3365ac7b670d79d70e9b4a8b7fba782607c44f` reveals four exact technical properties:

1. **Complete RVV 1.0 + `Zba`/`Zbb` + `Zvbb` Extraction in `sail-riscv-lean` (`Basis: source`):**
   - Unlike `sail-arm` (whose monolithic Lean output still requires `noncomputable` and `sorry`), `opencompl/sail-riscv-lean` **already includes all 16 translated RVV Lean modules plus `Zba`/`Zbb`**, compiling cleanly with zero `sorry` tokens:
     - Configuration & state: `LeanRV64D/VextRegs.lean` (`vr0..vr31`, `vtype.vill/vma/vta/vsew/vlmul`, `vxrm` `0x00A`, `vxsat` `0x009`), `VextControl.lean` (`Ext_Zvl32b`..`Ext_Zvl65536b`, `Ext_Zve32x`..`Ext_Zve64d`, `Ext_V`, `get_num_elem`), `VextVsetInsts.lean` (`VSETVLI`, `VSETVL`, `VSETIVLI`, `calculate_new_vl`), `VextUtilsInsts.lean` (`illegal_vstart`, `valid_eew_emul`, `valid_rd_mask`, `valid_reg_group`, `valid_reg_overlap`).
     - Vector execution (`Defs.lean:916-958`): `VextArithInsts.lean` (`1,730` LOC: `VVTYPE` `vadd`/`vsub`/`vsaddu`/`vsadd`/`vssubu`/`vssub`/`vsmul`/`vssrl`/`vssra`/`vrgather`/`vrgatherei16`, `MVVTYPE`, `WVVTYPE`, `WMVVTYPE` `vwmaccu`/`vwmacc`/`vwmaccsu`, narrowing `NVTYPE`/`NVSTYPE`), `VextMemInsts.lean` (`VLSEGTYPE`, `VLSEGFFTYPE` fault-only-first, `VSSEGTYPE`, strided `VLSSEGTYPE`, indexed `VLXSEGTYPE`, whole-register `VLRETYPE`), `VextRedInsts.lean` (`vwredsum[u]`, `vredsum`/`vredmax`/`vredmin`), `VextMaskInsts.lean` (`vmand`..`vmxnor`, `vcpop.m`, `vfirst.m`, `viota.m`, `vid.v`), and `VextFp*.lean` (`1,096` + `310` + `813` + `158` LOC).
     - Scalar bitmanip: `LeanRV64D/ZbaInsts.lean` (`slli.uw`, `add.uw`, `sh1add[.uw]`, `sh2add[.uw]`, `sh3add[.uw]` from `zba_insts.sail:13-77`) and `LeanRV64D/ZbbInsts.lean` (`andn`, `orn`, `xnor`, `clz[w]`, `ctz[w]`, `cpop[w]`, `max[u]`, `min[u]`, `sext.b/h`, `zext.h`, `rol[w]`, `ror[i][w]`, `orc.b`, `rev8` from `zbb_insts.sail:13-340`).

2. **Soundness Gap 1 — Deterministic Collapse of `vta = ta` and `vma = ma` (`AGNOSTIC`) (`Basis: normative + source`):**
   - Normative RVV 1.0 (`riscvarchive/riscv-v-spec@2f68ef7256d6ec53e4d2bd7cb12862f406d64e34`, §3.4.3 *Vector Tail Agnostic and Vector Mask Agnostic `vta` and `vma`*) specifies that when `vta = 1` (`ta`) or `vma = 1` (`ma`), each inactive destination element ($i < \text{vl}$ with $\text{vm}[i] = 0$ under `ma`) or tail element ($i \ge \text{vl}$ up to the end of the destination register group under `ta`) may **either retain its prior value (`undisturbed`) or be overwritten with all `1`s (`0xFF..FF`)**, even lane-by-lane or bit-by-bit across microarchitectures (e.g., out-of-order register-renaming RVV cores overwrite whole tail registers with `1`s to break false read-after-write dependencies on old `vd`).
   - Direct inspection of `riscv/sail-riscv` (`model/extensions/V/vext_arith_insts.sail:402, 871, 1301, 2014`, `vext_fp_insts.sail:1364, 1462`, `vext_mem_insts.sail:168-173, 648-651`, `vext_red_insts.sail:70, 145`) shows that every instruction implements `AGNOSTIC` as deterministic `UNDISTURBED`:
     ```sail
     AGNOSTIC => vd_val[i] // TODO: configuration support
     ```
   - **Verification Consequence:** Because `LeanRV64D` is mechanically generated from `sail-riscv`, `LeanRV64D` inherits `AGNOSTIC => vd_val[i]`. On `ff_h264_idct_add_8_rvv` (`vsetivli zero, 4, e16, mf2, ta, ma`), on any CPU with `VLEN >= 128` (`VLEN = 256` gives `VLMAX = (1/2)*256/16 = 8 > vl = 4`), elements `4..7` of `v0` are tail elements! If subsequent instructions (e.g., a whole-register move `vmv1r.v`, a wider `vsetvli` with `vl = 8`, or a `vslidedown`) read lanes `4..7` expecting `vd_val[4..7]` to survive, **a proof against unmodified `LeanRV64D` succeeds while real RVV 1.0 hardware legally writes `0xFFFF` (`-1`) into lanes `4..7`**. Sound verification in Lean 4 requires wrapping `LeanRV64D` vector writes in a relational angelic/demonic specification (`∀ ag_mask : BitVec VLMAX, ...`) that havoc-choices each inactive/tail element in `{vd_old[i], all_ones SEW}`.

3. **Soundness Gap 2 — `AVL` Clamping Nondeterminism in `vset{i}vl{i}` (`Basis: normative + source`):**
   - In `vext_vset_insts.sail:82-92`, when `VLMAX < AVL < 2 * VLMAX`, RVV 1.0 permits **any** hardware `vl` satisfying $\lceil \text{AVL} / 2 \rceil \le \text{vl} \le \text{VLMAX}$, whereas `calculate_new_vl` picks a single deterministic config boolean (`if vl_use_ceil then (AVL + 1) / 2 else VLMAX`). Strip-mined RVV loop proofs (`while avl > 0`) must quantify over all admissible `vl` in $[\lceil \text{AVL}/2 \rceil, \text{VLMAX}]$ rather than assuming `vl == VLMAX`.

4. **Purification Gap in `opencompl/riscv-lean` (`Basis: source`):**
   - `opencompl/riscv-lean` (`RISCV/Instructions.lean:1-760`, `RISCV/SailToRV64.lean`) proves refinement from monadic `SailM` to pure `BitVec 64` SSA operations for `RV64IM` + `Zba` + `Zbb` + `Zbs`, enabling fast SMT/Lean rewriting, **but contains zero RVV types or instructions**. Verifying RVV media kernels in Lean 4 today must therefore execute directly over `sail-riscv-lean`'s `SailM` state monad (parameterized by `vlen_exp`) or build a purified `BitVec (2^vlen_exp)` RVV layer proved against `LeanRV64D/Vext*.lean`.

---

### 3. PowerPC (`ppc64le`), LoongArch (`loongarch64`), and MIPS (`mips`): Primary-Source Audit of the Vector Formalization Vacuum

`Basis: source + documentation`

1. **PowerPC `ppc64le` (`AltiVec`/`VMX` & `VSX`, Power ISA v2.03–v3.1C):**
   - FFmpeg's `ppc64le` codecs (`libavutil/ppc/cpu.h:25-27`, `libavcodec/ppc/{h264qpel.c,vp9dsp_altivec.c}`) rely on C intrinsics (`<altivec.h>`: `vec_perm`, `vec_msum`, `vec_adds`, `vec_packsu`, `vec_xl`/`vec_xst`) targeting `32` 128-bit `VMX` registers (`VR0..VR31`, plus sticky saturation bit `VSCR.SAT`) and `64` 128-bit `VSX` registers (`VSR0..VSR63`, overlapping `FPR0..31` and `VR0..31`).
   - **`open-power-sdk/PowerISA`** (`ea48c49e9fe0271106e2e540cb6cbccad20c8afe`, Apache-2.0): `ISA.json` (`1,042` total instruction entries across `122,699` lines) contains `380` `"Vector Facility"` (`VMX`) entries and `283` `"Vector-Scalar Extension Facility"` (`VSX`) entries scraped from OpenPOWER LaTeX and PVIPR DocBook sources (`README.md:4-10`). Each entry's `"code"` array holds untyped, unparsed pseudo-RTL text lines (e.g., `"if MSR.VEC=0 then Vector_Unavailable()"`), with no formal grammar, typechecker, or interpreter, and big-endian bit numbering (`0..63` / `0..127` MSB-zero!) pervasive throughout Power ISA pseudocode.
   - **Hardware, Sail, and CompCert Models:** `antonblanchard/microwatt` (`f341bed3`, VHDL 2008, CC-BY-4.0) implements scalar FXU + FPU (`decode1.vhdl:12`) and explicitly documents in `README.md:132-134, 199` that `Vector/VMX/VSX` is unimplemented (requiring a patched `VMX`-free `glibc`). `rems-project/sail` (`97aa617d`, `old/power/power.sail:106-183`, paired with `rems-project/rmem@b2d346393eaa83d84c657eeec7d70b01b0656643`) models `GPR0..31`, `CR`, `XER`, `CTR`, `LR`, and scalar `VRSAVE` (`bit[32:63]`) for user-mode weak-memory litmus tests, with **zero** `VR`/`VSR` registers or `VMX`/`VSX` instructions. `AbsInt/CompCert` (`2685140b`, `powerpc/Machregs.v:29-49`, `powerpc/Asm.v:33-65`) models only `GPR0..31` and 64-bit scalar `FPR0..31` under the **INRIA Non-Commercial License Agreement** (`LICENSE:12-18`, `powerpc/Asm.v:9`).

2. **LoongArch `loongarch64` (`LSX` 128-bit & `LASX` 256-bit):**
   - FFmpeg includes extensive `LSX` (`$vr0..$vr31`, 128-bit) and `LASX` (`$xr0..$xr31`, 256-bit) kernels (`libavutil/loongarch/cpu.h:28-29`, `libavcodec/loongarch/h264idct_lasx.c`).
   - **`loongson/LoongArch-Documentation`** (`e0d6592229d9e00e512bd28b688a7f20b171714f`) is licensed under **CC-BY-NC-ND-4.0** (Creative Commons Attribution-NonCommercial-NoDerivatives 4.0, blocking commercial derivative formalizations from manual text!) and contains complete AsciiDoc chapters only for `LoongArch-Vol1-EN` (scalar integer, basic FP, CSRs), whereas `docs/LoongArch-Vol2-EN.adoc` (*Volume 2: Vector Extensions*, `L1-14`) consists literally of the placeholder `*TBD*`.
   - **`loongson-community/loongarch-opcodes`** (`e269905901feb91e13444c0ce4b52f6ea06e9969`) provides clean machine-readable 32-bit opcode masks and operand-slot formats (`lsx.txt`: `717` instructions such as `09100000 vfmadd.s VdVjVkVa`; `lasx.txt`: `735` instructions such as `0a100000 xvfmadd.s XdXjXkXa`; parsed by `scripts/go/common/parse.go:11-25` to generate Go disassemblers and QEMU TCG boilerplate `scripts/go/genqemutcgdefs/main.go`), but contains **zero** arithmetic or memory semantics. No formal ISA model of LoongArch exists in Sail, Lean, Rocq, Isabelle, HOL, ACL2, or K.

3. **MIPS `mips` / `mips64el` (`MSA` 128-bit & Loongson `MMI`):**
   - FFmpeg's legacy MIPS codecs (`libavutil/mips/cpu.h:25-26`, `libavcodec/mips/h264idct_msa.c:21-55`) use 128-bit `MSA` intrinsics (`v8i16`, `__msa_fill_w`, `ILVL_D2_SH`) defined in *MIPS64 SIMD Architecture Module* (`MD00867`) and Loongson 64-bit `MMI`.
   - **`CTSRD-CHERI/sail-cheri-mips`** (`13a9c3fb0c3f8d320d4f4650a63d23d3a8b12724`, BSD-2-Clause, `mips/mips_insts.sail` `1,877` LOC, `91` `union clause ast` constructors) and **`coruus/L3`** (`isa-models/mips/mips.spec` `1,624` LOC) formalize 64-bit MIPS III/MIPS64 scalar integer, branch-delay slots, CP0 system registers, and CHERI 128/256-bit capabilities, with **zero** `MSA` (`w0..w31`) or `MMI` vector instructions.

---

### 4. WebAssembly (`wasm`): SpecTec, Deterministic `SIMD128`, Wasm 3.0 `relaxed-simd`, and `WasmCert` Opacity

`Basis: normative + source + execution`

FFmpeg supports WebAssembly 128-bit SIMD via C `<wasm_simd128.h>` intrinsics (`libavutil/cpu.h:109`, `libavcodec/wasm/hevc/idct.c:23-55`, `libavcodec/wasm/hevc/sao.c:23-55`, using `wasm_i16x8_shuffle`, `wasm_i32x4_shuffle`, `wasm_v128_load64_zero`, `wasm_v128_load64_lane`). Auditing the Wasm formal ecosystem uncovers three crucial architectural facts:

1. **Authoritative Executable Semantics in `WebAssembly/spec` and `Wasm-DSL/spectec` (`Basis: source`):**
   - `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`) integrates **SpecTec** (`Wasm-DSL/spectec@acc6e834ff403c82554d081237f327346190ad96`, `Breitner et al., PLDI 2024`, DOI `10.1145/3656440`) alongside the OCaml reference interpreter (`interpreter/exec/{v128.ml,eval_vec.ml}`) and conformance suite (`spectec/test-interpreter/spec-test-2/simd/*.wast`), covering all `236` fixed-width `v128` `SIMD128` opcodes (`WebAssembly/simd@a78b98a6899c9e91a13095e560767af6e99d98fd`) **and** all `20` Wasm 3.0 `relaxed-simd` opcodes (`WebAssembly/relaxed-simd@c3f9359af2cd607cc46b0a3274f90ea52543a2f2`).

2. **Why `WasmCert-Isabelle` and `WasmCert-Coq` Cannot Discharge Media SIMD Proofs (`Basis: source`):**
   - Although both mechanizations updated their ASTs and typecheckers to Wasm 2.0 (`T_v128`, `ConstVec128`), **both leave vector arithmetic uninterpreted inside the theorem prover**:
     - In `WasmCert/WasmCert-Isabelle` (`d9b4659c`), `WebAssembly/Wasm_Base_Defs.thy:137-138` declares `app_unop_vec_v :: "unop_vec => v128 => v128"` and `app_binop_vec_v :: "binop_vec => v128 => v128 => v128 option"` inside an uninterpreted `consts` block (defining only byte-level `splat`/`insert_lane` at `L674-693`), and `WebAssembly/code/README.md:3` states that extracted `WasmRef_Isa.ocaml` delegates numeric and vector evaluation externally to the unverified OCaml reference interpreter.
     - In `WasmCert/WasmCert-Coq` (`58a3d3f8`, underpinning `Iris-Wasm`, `Rao et al., PLDI 2023`, DOI `10.1145/3591265`), `theories/simd.v:25` defines `Definition v128 := bytes`, `theories/simd_execute.v:15-20` postulates `Parameter app_vunop_str`, `app_vbinop_str`, `app_vternop_str`, `app_vtestop_str`, `app_vshiftop_str` over serialized `string` values, and `README.md:13` + `src/SIMD_ops.ml:5-45` dispatch raw binary opcodes to OCaml's `Wasm.V128` at extraction time. (Note also that `WasmCert-Coq` vendors `src/Parray/` under **LGPL-2.1+**, `LICENSE.txt:1-10`.)
   - Consequently, proving functional correctness of a Wasm `SIMD128` HEVC IDCT or SAO filter in Lean 4 cannot reuse `WasmCert` vector theories; instead, translating `WebAssembly/spec/interpreter/exec/eval_vec.ml` (`340` LOC) + `v128.ml` (or generating Lean 4 from `Wasm-DSL/spectec` IL) yields a compact, self-contained `BitVec 128` semantics with zero flags or undefined memory padding.

3. **Target-Dependent Relational Nondeterminism in Wasm 3.0 `relaxed-simd` vs Deterministic `eval_vec.ml` (`Basis: normative + source + execution`):**
   - `WebAssembly/relaxed-simd` (`proposals/relaxed-simd/Overview.md:5-95`) introduces **host-environment-projected nondeterminism** specifically so Wasm engines on `x86_64` and `aarch64` can emit single native SIMD instructions without software fixup masks:
     - `i8x16.relaxed_swizzle` (`0xfd 0x100`): for index $s[i] \in [0, 15]$, returns $a[s[i]]$; for $s[i] \in [128, 255]$, returns `0`; for $s[i] \in [16, 127]$, returns `IMPLEMENTATION_DEFINED_ONE_OF(0, a[s[i] % 16])` (`0` on AArch64 `TBL`, `a[s[i] % 16]` on x86 `PSHUFB`!).
     - `i16x8.relaxed_q15mulr_s` (`0xfd 0x111`): returns `+32767` on AArch64 `SQRDMULH` vs `-32768` on x86 `PMULHRSW` when both lanes are `-32768`.
     - `i16x8.relaxed_dot_i8x16_i7x16_s` (`0xfd 0x112`) & `i32x4.relaxed_dot_i8x16_i7x16_add_s` (`0xfd 0x113`): deterministic when the second operand sits in `[-64, +63]` / unsigned 7-bit `[0, 127]`, but diverges between x86 signed/unsigned `PMADDUBSW`/`VPDPBUSD` and AArch64 `SDOT` when bit 7 of the `i7x16` input is set, plus intermediate `i16` saturation when `i16x8.relaxed_dot` overflows!
     - `f32x4.relaxed_madd`/`nmadd`, `relaxed_min`/`max`, `relaxed_laneselect`, `relaxed_trunc_*`: single-rounded FMA vs unfused multiply+add, and NaN/out-of-range selection.
   - **Critical Trap in `WebAssembly/spec/interpreter/exec/eval_vec.ml:64-85, 113-138, 211-214`:** Inspection of `eval_vec.ml` shows that the OCaml reference interpreter collapses every `Relaxed*` constructor onto its deterministic `SIMD128` counterpart (`| I8x16 RelaxedSwizzle -> V128.V8x16.swizzle`, `| I16x8 RelaxedQ15MulRS -> V128.I16x8.q15mulr_sat_s`)!
   - **Real V8 Execution Witness (`Basis: execution`):** Executing a minimal Wasm binary containing both deterministic `SIMD128` (`0xfd 0x0e`, `0xfd 0x82 0x01`) and `relaxed-simd` (`0xfd 0x80 0x02`, `0xfd 0x91 0x02`) on Node.js `v24.21.0` (`linux-x86_64`) produces:
     `{"swizzle_det":"0x0","swizzle_rel":"0xa3","q15_det":32767,"q15_rel":-32768}`.
     Thus, verifying a Wasm 3.0 module against `eval_vec.ml` alone is **unsound on `x86_64` V8**; a sound Lean 4 Wasm semantics must formalize `relaxed-simd` relationally (quantifying over host environment projections per `Overview.md:64-70`) and prove media kernels deterministic by establishing input-domain preconditions ($s[i] \in [0, 15] \cup [128, 255]$, $(a,b) \ne (-32768,-32768)$, `i7` $\in [0, 127]$).

---

### 5. Verification Priority Stack, Performance Reality, and Clean-Rewrite Architecture

`Basis: derived + source`

1. **Verification Priority Stack Across Secondary ISAs:**
   - **Tier 1 (UB-Freedom) & Tier 2 (Panic/Trap Freedom):**
     - On **`wasm`**, sandboxed linear memory bounds checks guarantee host memory safety by construction, turning out-of-bounds vector loads into deterministic WebAssembly `trap`s (`load_vec_None` in `Wasm.thy:320-327`); Tier 2 panic-freedom reduces to proving linear-memory index bounds `addr + offset + 16 <= mem.size` and avoiding integer divide-by-zero (`binop_vec_None`).
     - On **`riscv64`**, Tier 1/2 require proving `vtype.vill == 0`, register-group alignment `vd % EMUL == 0` (`valid_reg_group`, `vext_utils_insts.sail:98`), non-overlapping mask destination `vm == 0 -> vd != v0` (`valid_rd_mask`, `L92`), widening/narrowing source-destination overlap legality (`valid_reg_overlap`, `L116`), `vstart == 0` (`illegal_vstart`, `L50`), and fault-only-first `vle*ff.v` `vl`-truncation handling.
     - On **`ppc64le`**, **`loongarch64`**, and **`mips`**, **no formal ISA model exists to verify inline or standalone vector assembly** even at Tier 1! Any hand-written `VSX`, `LASX`, or `MSA` assembly added to a verified media library directly enlarges the unverified TCB.
   - **Tier 3 (SIMD-vs-Scalar Equivalence) & Tier 4 (Bit-Exact Codec Conformance):**
     - On `riscv64`, Tier 3 VLA loop invariants must hold for **all** `vlen` $\in \{128, 256, 512, \dots, 65536\}$ (`Ext_Zvl128b`+), **all** legal `vl` returned by `vsetvli`, and **all** `{undisturbed, all-1s}` choices on `ta`/`ma` lanes.
     - On `wasm`, deterministic `SIMD128` guarantees bit-identical Tier 3/4 integer results across `x86_64`, `aarch64`, and `riscv64` browsers/runtimes; `relaxed-simd` preserves bit-exact video conformance **only** when the kernel's verification precondition excludes the nondeterministic input corners above.

2. **Performance Reality vs Formalization ROI for a Clean Media Rewrite:**
   - **High-ROI Verified Targets (`riscv64` + `wasm`):**
     - `wasm` `SIMD128` delivers `2.5x`–`6x` speedups over scalar Wasm in browser/sandboxed HEVC/AV1/VP9 decoding while exposing only `1` 128-bit vector type (`v128`) and ~`256` pure total/relational instructions—making a complete, zero-axiom Lean 4 Wasm `SIMD128` + relational `relaxed-simd` mechanization the **highest assurance-per-LOC investment** in the entire corpus.
     - `riscv64` `RVV 1.0` + `Zba`/`Zbb` already has `9,500`+ LOC of Sail-generated Lean 4 (`opencompl/sail-riscv-lean`); patching the `AGNOSTIC` nondeterministic choice and building lane-level `BitVec` lemmas unlocks verified VLA assembly without authoring an ISA spec from scratch.
   - **Eliminate Hand-Written Assembly on `ppc64le`, `loongarch64`, and `mips`:**
     - Maintaining bespoke C-intrinsics/assembly files for `AltiVec`/`VSX`, `LSX`/`LASX`, and `MSA`/`MMI` (as FFmpeg does across hundreds of files) creates an unverifiable TCB hole because none of those three architectures has a formal vector ISA specification, and two of their ecosystems carry restrictive non-commercial licenses (`CompCert` PowerPC INRIA Non-Commercial; `LoongArch-Documentation` CC-BY-NC-ND-4.0).
     - Instead, a clean verified rewrite should route `ppc64le`, `loongarch64`, and `mips` exclusively through **portable, verified fixed-chunk Rust SIMD abstractions** (`portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates` and `core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras`), letting LLVM's backend legalize verified lanewise IR while reserving ISA-level assembly verification strictly for `x86_64`, `aarch64`, `riscv64`, and `wasm`.

---

## Boundaries

1. **RISC-V Matrix Extensions (`Zacas`, `Zvbc`, `IME`/`AME` proposals) (`not examined`):** While `sail-riscv` includes ratified vector crypto (`zvbb`, `zvbc`, `zvkg`, `zvkned`, `zvknhab`, `zvksed`, `zvksh`), unratified RISC-V matrix extensions are outside scope and absent from `FFmpeg/FFmpeg`.
2. **Closed/Internal Vendor Models for PowerPC, LoongArch, and MIPS (`unknown`):** IBM, Loongson, or Imagination/MIPS may maintain internal proprietary RTL/validation models for `VSX`, `LSX`/`LASX`, or `MSA`, but no public, open-source, machine-checkable operational semantics exists as of `2026-11-20`.
3. **LoongArch Volume 2 Documentation Licensing (`known not to apply` for open-source redistribution):** Because `loongson/LoongArch-Documentation` is licensed under `CC-BY-NC-ND-4.0` and leaves `LoongArch-Vol2-EN.adoc` as `*TBD*`, open-source formalizations cannot copy specification text from Loongson's manual repository (`unsupported`).
4. **CompCert PowerPC Backend Licensing & Scope (`unsupported` for commercial SIMD verification):** `AbsInt/CompCert` `powerpc/` both lacks `VMX`/`VSX` vector registers (`Asm.v:33-65`) and prohibits commercial use of `powerpc/Asm.v` and `powerpc/Machregs.v` without an AbsInt commercial license (`LICENSE:12-58`, where only `Archi.v`, `Builtins1.v`, `CBuiltins.ml`, and `extractionMachdep.v` are dual-licensed LGPL-2.1).
5. **Floating-Point NaN Canonicalization Overhead in Wasm `SIMD128` (`not examined` empirically across Arm hosts):** Native `x86_64` V8 execution was measured directly (`Node.js v24.21.0`), whereas AArch64 V8 JIT codegen for `relaxed-simd` was reasoned from `WebAssembly/relaxed-simd` normative rules rather than executed on Arm hardware (`Basis: normative + derived`).

---

## Evidence

### Primary Upstream Source Citations (Verified 2026-11-20)

1. **`FFmpeg/FFmpeg`** (`7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`):
   - `libavutil/cpu.h:65-67` (`ALTIVEC`, `VSX`, `POWER8`), `L90-91` (`MMI`, `MSA`), `L94-95` (`LSX`, `LASX`), `L98-106` (`RVI`, `RVV_I32/F32/I64/F64`, `RVB_BASIC`, `RV_ZVBB`, `RVB`), `L109` (`SIMD128`).
   - `libavutil/riscv/cpu.h:30-56`; `libavutil/riscv/asm.S:39-55` (`archadd zba, zbb, zbs`); `libavcodec/riscv/h264idct_rvv.S:32-55` (`csrwi vxrm, 0`, `vsetivli zero, 4, e16, mf2, ta, ma`); `libavutil/ppc/cpu.h:25-27`; `libavutil/loongarch/cpu.h:28-29`; `libavutil/mips/cpu.h:25-26`; `libavcodec/mips/h264idct_msa.c:21-55`; `libavcodec/wasm/hevc/{idct.c:23-55, sao.c:23-55}`.
2. **`riscv/sail-riscv`** (`ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`), **`opencompl/sail-riscv-lean`** (`51c635c460125ac87955d061fcd902ce03b8011f`), **`opencompl/riscv-lean`** (`0e3365ac7b670d79d70e9b4a8b7fba782607c44f`), **`riscvarchive/riscv-v-spec`** (`2f68ef7256d6ec53e4d2bd7cb12862f406d64e34`), & **`riscv/riscv-isa-manual`** (`c05f1725f25526dd8463bac6ca75cfcfbee17d05`):
   - `sail-riscv`: `LICENCE:1-10` (BSD-2-Clause); `model/extensions/B/{zba_insts.sail:9-77, zbb_insts.sail:9-340}`; `model/extensions/V/vext_vset_insts.sail:15-130` (`calculate_new_vl` `L82-92`, `execute_vsetvl_type` `L95-130`); `vext_utils_insts.sail:50-130`; `vext_control.sail:9-60`; `vext_regs.sail:29-55, 255-338` (`vill`, `vma`, `vta`, `vxrm`, `vxsat`); `vext_arith_insts.sail:17-55, 402, 871, 1301, 2014` (`AGNOSTIC => vd_val[i]`); `vext_fp_insts.sail:1364, 1462`; `vext_mem_insts.sail:168-173, 648-651`; `vext_red_insts.sail:70, 145`; `model/extensions/vector_crypto/{zvbb_insts.sail,zvbc_insts.sail,zvk*_insts.sail}`.
   - `sail-riscv-lean`: `LeanRV64D/Defs.lean:389, 599-790, 916-958`; `LeanRV64D/{Vector,VextArithInsts,VextControl,VextFpInsts,VextFpRedInsts,VextFpUtilsInsts,VextFpVmInsts,VextMaskInsts,VextMemInsts,VextRedInsts,VextRegs,VextTypes,VextUtilsInsts,VextVmInsts,VextVsetInsts,ZbaInsts,ZbbInsts}.lean`.
   - `riscv-lean`: `RISCV/Instructions.lean:1-760` (`BitVec 64` scalar + `Zba`/`Zbb`/`Zbs`, zero RVV); `RISCV/SailToRV64.lean`.
3. **PowerPC Repositories:**
   - `open-power-sdk/PowerISA` (`ea48c49e9fe0271106e2e540cb6cbccad20c8afe`): `LICENSE:1-15` (Apache-2.0), `README.md:1-11`, `ISA.json:1-425` (`380` `Vector Facility` + `283` `Vector-Scalar Extension Facility` entries out of `1,042`).
   - `antonblanchard/microwatt` (`f341bed306a9a7281bf65200df8cc1f0a002617d`): `LICENSE:1-8` (CC-BY-4.0), `README.md:132-134, 199` (`Vector/VMX/VSX` unimplemented), `decode1.vhdl:10-45`.
   - `rems-project/sail` (`97aa617dcd4d01575f773cb58ea1e8686858c8c2`): `old/power/power.sail:106-183` & `rems-project/rmem` (`b2d346393eaa83d84c657eeec7d70b01b0656643`): `src_isa_defs/powerIsa.lem`.
   - `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`): `LICENSE:1-64` (INRIA Non-Commercial), `powerpc/Machregs.v:17-65`, `powerpc/Asm.v:31-65` (`ireg` `GPR0..31` + `freg` `FPR0..31` only).
4. **LoongArch & MIPS Repositories:**
   - `loongson/LoongArch-Documentation` (`e0d6592229d9e00e512bd28b688a7f20b171714f`): `LICENSE` (CC-BY-NC-ND-4.0), `docs/LoongArch-Vol2-EN.adoc:1-14` (`*TBD*`), `docs/LoongArch-Vol3-EN.adoc:1-14` (`*TBD*`).
   - `loongson-community/loongarch-opcodes` (`e269905901feb91e13444c0ce4b52f6ea06e9969`): `lsx.txt:1-717`, `lasx.txt:1-735`, `scripts/go/common/{mod.go:10-25, parse.go:11-25}`, `scripts/go/genqemutcgdefs/main.go:1-26`.
   - `CTSRD-CHERI/sail-cheri-mips` (`13a9c3fb0c3f8d320d4f4650a63d23d3a8b12724`): `LICENCE:1-40` (BSD-2-Clause), `README.md:18-30`, `mips/mips_insts.sail:1-1877` (`91` scalar/CP0 AST clauses, `0` MSA/MMI).
   - `coruus/L3` (`d6558e679a25ffaaf16a47a3189f8f8111e45e0c`): `isa-models/mips/mips.spec:1-35`.
5. **WebAssembly Repositories:**
   - `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`): `interpreter/exec/eval_vec.ml:1-215` (`RelaxedSwizzle` `L64`, `RelaxedQ15MulRS` `L84`, `RelaxedDot` `L85`, `RelaxedDotAddS` `L138`), `spectec/test-interpreter/spec-test-2/simd/*.wast`.
   - `Wasm-DSL/spectec` (`acc6e834ff403c82554d081237f327346190ad96`), `WebAssembly/simd` (`a78b98a6899c9e91a13095e560767af6e99d98fd`), & `WebAssembly/relaxed-simd` (`c3f9359af2cd607cc46b0a3274f90ea52543a2f2`: `proposals/relaxed-simd/Overview.md:1-95`).
   - `WasmCert/WasmCert-Isabelle` (`d9b4659c8b38879a5fc7e0213950751a61091908`): `LICENSE:1-21` (BSD-2-Clause), `WebAssembly/Wasm_Ast.thy:24, 134-148, 207-211, 256-262`, `WebAssembly/Wasm_Base_Defs.thy:137-138, 651-693` (uninterpreted `consts app_*_vec_v`), `WebAssembly/Wasm.thy:234-249, 320-327`, `WebAssembly/code/README.md:1-3`.
   - `WasmCert/WasmCert-Coq` (`58a3d3f8b7af4dc8aa9351f254a9e672643b21f8`): `LICENSE.txt:1-34` (MIT + LGPL-2.1 `src/Parray/`), `README.md:9-14`, `theories/simd.v:12-38`, `theories/simd_execute.v:13-24` (`Parameter app_v*op_str`), `src/SIMD_ops.ml:1-45`.

### Executed WebAssembly `SIMD128` vs `relaxed-simd` Witness (`Basis: execution`)

Executed on Linux `x86_64` using Node.js `v24.21.0` (`WebAssembly.Instance`), comparing deterministic `i8x16.swizzle` (`0xfd 0x0e`) and `i16x8.q15mulr_sat_s` (`0xfd 0x82 0x01`) against Wasm 3.0 `i8x16.relaxed_swizzle` (`0xfd 0x80 0x02`) and `i16x8.relaxed_q15mulr_s` (`0xfd 0x91 0x02`):

```python
import subprocess, json

def uleb(n):
    out = []
    while True:
        b, n = n & 0x7f, n >> 7
        out.append(b | (0x80 if n else 0))
        if not n: return bytes(out)

def sec(i, p): return bytes([i]) + uleb(len(p)) + p
def exp(k, i): return uleb(len(k)) + k.encode() + bytes([0, i])
def vconst(b): return bytes([0xfd, 0x0c]) + b
def fn(body):  return uleb(len(body) + 2) + b"\x00" + body + b"\x0b"

tbl = bytes([0xa0 + i for i in range(16)])
idx = bytes([0x13] + [0x80] * 15)
m16 = (0x8000).to_bytes(2, "little") * 8

wasm = (b"\x00asm\x01\x00\x00\x00"
  + sec(1, b"\x01\x60\x00\x01\x7f") + sec(3, b"\x04\x00\x00\x00\x00")
  + sec(7, b"\x04" + exp("swizzle_det",0) + exp("swizzle_rel",1) + exp("q15_det",2) + exp("q15_rel",3))
  + sec(10, b"\x04"
      + fn(vconst(tbl) + vconst(idx) + b"\xfd\x0e\xfd\x16\x00")
      + fn(vconst(tbl) + vconst(idx) + b"\xfd" + uleb(0x100) + b"\xfd\x16\x00")
      + fn(vconst(m16) + vconst(m16) + b"\xfd" + uleb(0x82)  + b"\xfd\x18\x00")
      + fn(vconst(m16) + vconst(m16) + b"\xfd" + uleb(0x111) + b"\xfd\x18\x00")))

js = """
const m = new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(%s))).exports;
console.log(JSON.stringify({
  swizzle_det: "0x" + m.swizzle_det().toString(16),
  swizzle_rel: "0x" + m.swizzle_rel().toString(16),
  q15_det: m.q15_det(), q15_rel: m.q15_rel()
}));
""" % list(wasm)
print(subprocess.check_output(["node", "-e", js]).decode().strip())
```

Recorded output (2026-11-20, `node v24.21.0` on `linux-x86_64`):
```json
{"swizzle_det":"0x0","swizzle_rel":"0xa3","q15_det":32767,"q15_rel":-32768}
```

---

## Revalidation

To cheaply determine whether any of the five target architectures' formalization boundaries have changed upstream:

1. **Check `riscv/sail-riscv` & `opencompl/sail-riscv-lean` `AGNOSTIC` nondeterminism (`<5s`):**
   Fetch `model/extensions/V/vext_arith_insts.sail` from `riscv/sail-riscv` and grep for `AGNOSTIC`; if `AGNOSTIC => vd_val[i] // TODO: configuration support` has been replaced by nondeterministic/all-ones support, re-check `LeanRV64D/VextArithInsts.lean` in `opencompl/sail-riscv-lean`.
2. **Check `opencompl/riscv-lean` for purified RVV instructions (`<5s`):**
   Inspect `RISCV/Instructions.lean` in `opencompl/riscv-lean` for `vset` or `vadd` definitions.
3. **Check `WasmCert-Isabelle` & `WasmCert-Coq` for kernel-verified `v128` ALU definitions (`<5s`):**
   Check `WebAssembly/Wasm_Base_Defs.thy` (`consts` block around `app_binop_vec_v`) in `WasmCert/WasmCert-Isabelle` and `theories/simd_execute.v` (`Parameter app_vbinop_str`) in `WasmCert/WasmCert-Coq`, plus check `Wasm-DSL/spectec` backends for a Lean 4 target.
4. **Check `ppc64le`, `loongarch64`, and `mips` vector formalization status (`<10s`):**
   Check `docs/LoongArch-Vol2-EN.adoc` in `loongson/LoongArch-Documentation` (whether `*TBD*` has been populated and whether `LICENSE` remains `CC-BY-NC-ND-4.0`), `README.md` in `antonblanchard/microwatt` (`Vector/VMX/VSX` TODO item), and search `rems-project` / GitHub for new `sail-power` or `sail-loongarch` repositories.
5. **Re-run the embedded Python + Node.js `relaxed-simd` binary probe (`<2s`):**
   Run the script in `## Evidence` on any `x86_64`, `aarch64`, or `riscv64` host with `node` to observe the host JIT's concrete `relaxed-simd` projection versus deterministic `SIMD128`.
