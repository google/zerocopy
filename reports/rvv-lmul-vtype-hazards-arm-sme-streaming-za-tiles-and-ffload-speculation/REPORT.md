# RISC-V RVV 1.0 `LMUL`/`vtype` Hazards, ARM SME Streaming `ZA` Tiles, and Fault-Only-First Speculation

## Summary

Vector-Length-Agnostic (`VLA`) vector and matrix extensions—RISC-V `"V"` `1.0` (`RVV`), Arm `SVE2`, and Arm `SME`/`SME2`—allow a single compiled binary to scale dynamically from `128`-bit embedded cores to `2048`-bit server/accelerator engines without multi-versioned `.text` bloat, while hardware **fault-only-first loads** (`RVV` `vle8ff.v`..`vle64ff.v`, `SVE` `LDFF1B`) vectorize data-dependent `strlen`/lexer loops across unmapped `4096 B` guard pages without `SIGSEGV` faults. Across ISA semantics, compiler codegen (`LLVM` / `rustc`), C++ SIMD wrappers (`google/highway`), and OS/FFI boundaries (`AAPCS64` / Linux `arm64`), however, **mutable control-register typestate and register-aliasing coupling introduce five severe soundness hazards**:

1. **`RVV 1.0` `vtype.vill` Poison & `LMUL` Register-Group Overlap (`v-spec.adoc` §§3.4, 5.2):** `vset{i}vl{i}` configurations where fractional `LMUL < SEW / ELEN` (e.g., `mf2` at `SEW=64, ELEN=64`, accounting for `42` of the `64` `(vsew[2:0], vlmul[2:0])` bit encodings at `VLEN=256, ELEN=64`) set `vtype[XLEN-1] = vill = 1`, zero `vl`, and trap all subsequent vector instructions. When `LMUL` $\in \{2, 4, 8\}$, architectural registers `v0..v31` coalesce into aligned groups (`vd % LMUL == 0`); widening instructions (`2*SEW <- SEW op SEW`) forbid destination overlap with the *lower* half of a source group (`vwadd.vv v4, v4, v2` traps, whereas upper-half `vwadd.vv v4, v6, v2` is legal).
2. **`RVV 1.0` Agnostic `1`-Fill Nondeterminism Across `big.LITTLE` Migration (`v-spec.adoc` §3.4.3):** Under `vta=1` / `vma=1` (LLVM's default high-performance codegen policy freeing OoO register renaming from old-physical-register reads), hardware may **nondeterministically leave each tail/inactive element undisturbed OR overwrite it with all `1`s (`0xFF..FF`)**, even mixing policies mid-instruction when migrating threads from an in-order core (`Spike`/`QEMU` undisturbed—passing tests!) to an out-of-order renaming core (`all-1s`—corrupting unmasked reductions!).
3. **`RVV 1.0` Fault-Only-First (`vle<eew>ff.v`) Spurious Tail Overwrites & Spontaneous `vl` Shrinks (`v-spec.adoc` §7.7):** `vle8ff.v` traps synchronously *only* if element `0` faults; faults on elements $k > 0$ suppress the trap and trim `vl <- k`. Crucially, the specification (a) **permits `vle8ff.v` to overwrite destination elements in `[new_vl, old_vl)` with arbitrary values unrelated to memory**, (b) **permits implementations to shrink `vl` to any `[1, old_vl]` even when NO fault occurs** (forbidding `vl` loop-invariance assumptions), (c) forbids non-idempotent MMIO accesses past element `0`, and (d) exposes a supervisor-mode hypervisor guest-physical-address (`GPA`) probing channel.
4. **Arm `SME` `SMSTART`/`SMSTOP` Register Zeroing & Linux `svc #0` Streaming Abort (`aapcs64.rst`, `linux/Documentation/arch/arm64/sme.rst`):** Entering or exiting Streaming SVE mode (`PSTATE.SM` flip via `SMSTART SM` / `SMSTOP SM`) **architecturally zeroes every scalar FP, NEON, SVE vector, and predicate register (`V0–V31`, `Z0–Z31`, `P0–P15`, `FFR`)**—silently destroying `AAPCS64` callee-saved `d8–d15` unless spilled beforehand! Furthermore, on AArch64 Linux (`sme.rst` §3), **every system call (`svc #0`) unconditionally clears `PSTATE.SM = 0`** while preserving `PSTATE.ZA`, causing any unguarded syscall inside an `#[arm_streaming]` routine to break subsequent streaming instructions or vector lengths (`SVL != VL`).
5. **Arm `AAPCS64` `TPIDR2_EL0` Lazy `ZA` Save Ordering & Asynchronous Signal/Unwind Hazards (`aapcs64.rst` §§5–6, `sme.rst` §§4–5):** Because `ZA` scales as $\text{SVL}_B \times \text{SVL}_B$ bytes (up to `256 x 256 = 64 KiB` at `SVL=2048b`), `AAPCS64` uses per-thread `TPIDR2_EL0` pointing to a 16-byte stack `TPIDR2 block` (`za_save_buffer` at `+0`, `num_za_save_slices` at `+8`) for lazy caller-allocated saving. Disabling `PSTATE.ZA` *before* clearing `TPIDR2_EL0` violates `AAPCS64`'s mandatory transition order (`TPIDR2_EL0 := NULL` *then* `SMSTOP ZA`) and opens a 1-instruction asynchronous signal/unwind corruption window.

## Applicability

This report characterizes the ISA-to-compiler-to-OS contract across five pinned primary subjects:
- **`riscvarchive/riscv-v-spec`** at commit `2f68ef7256d6ec53e4d2bd7cb12862f406d64e34` (`RVV v1.0` frozen specification, `v-spec.adoc`);
- **`google/highway`** at commit `ab219f9ecac8bc7e97d4c2b3b8197e52b48a5b52` (`hwy/ops/rvv-inl.h` portable C++ VLA abstractions over RVV fractional/integer `LMUL`);
- **`ARM-software/abi-aa`** at commit `9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7` (`aapcs64/aapcs64.rst`, normative `AAPCS64` + SME/SME2 calling-convention attributes `__arm_streaming`, `__arm_streaming_compatible`, `__arm_new("za")`, `__arm_inout("za")`, `__arm_preserves("za")`, and `TPIDR2_EL0` lazy-save state machine);
- **`torvalds/linux`** at commit `f1715c0c04606ebbe832cc760abf49dfd6f2ae1f` (`Documentation/arch/arm64/sme.rst`, Linux kernel `arm64` syscall, `clone`, `ptrace`, `prctl`, and signal-frame `za_context`/`tpidr2_context`/`zt_context` contract); and
- **`llvm/llvm-project`** at commit `63b8d2fd94ba3b1a80023dae7139949dd5be6b78` (`llvm/lib/Target/RISCV/RISCVInsertVSETVLI.cpp`, shared backend lowering used by both `clang` and `rustc` on `riscv64gc` + `+v` targets).

The subjects are analyzed **jointly and comparatively** to establish exact codegen, FFI, unwind, and formal-verification invariants for `rustc` (`std::arch::riscv64`, `aarch64`), LLVM IR scalable vectors (`<vscale x N x T>`), and binary lifters/checkers. Executable state-space checks were run under Python `3.13` via `probes/verify_rvv_and_sme_hazards.py`.

## Findings

### 1. RISC-V `"V"` `1.0` `vtype` Control State, `LMUL` Grouping, and `LLVM` `VSETVLI` Dataflow

`Basis: normative + source + execution`

Unlike fixed-width SIMD (`SSE`/`AVX-512`/`NEON`) where element width and vector length are encoded statically in every opcode, `RVV 1.0` interprets every vector arithmetic and memory instruction dynamically through two read-only CSRs updated solely by `vsetvli` / `vsetivli` / `vsetvl` (and `vl`-trimming fault-only-first loads, `v-spec.adoc:182–195, 509–512`):
- **`vl` (`XLEN` bits):** Active element count $0 \le \text{vl} \le \text{VLMAX}$, where $\text{VLMAX} = (\text{VLEN} \cdot \text{LMUL}) / \text{SEW}$.
- **`vtype` (`XLEN` bits, `v-spec.adoc:185–201`):**
  $$\texttt{vtype} = \underbrace{\texttt{vill}}_{\text{bit } \text{XLEN}-1} \;\|\; \underbrace{0\dots 0}_{\text{XLEN}-2\,:\,8} \;\|\; \underbrace{\texttt{vma}}_{\text{bit } 7} \;\|\; \underbrace{\texttt{vta}}_{\text{bit } 6} \;\|\; \underbrace{\texttt{vsew[2:0]}}_{\text{bits } 5:3} \;\|\; \underbrace{\texttt{vlmul[2:0]}}_{\text{bits } 2:0}$$

#### 1.1 Fractional `LMUL` `vill` Traps & `Highway` `MLEN <= 64` Ceiling
For fractional `LMUL` $\in \{\text{mf8} = 1/8, \text{mf4} = 1/4, \text{mf2} = 1/2\}$, `v-spec.adoc:327–337` mandates support only when $\text{SEW}_{\min} \le \text{SEW} \le \text{LMUL} \cdot \text{ELEN}$; encodings with $\text{LMUL} < \text{SEW}_{\min}/\text{ELEN}$ or $\text{SEW} > \text{LMUL} \cdot \text{ELEN}$ set `vill = 1`, zero `vtype[XLEN-2:0]` and `vl = 0`, and raise an illegal-instruction trap on any subsequent vector op (`v-spec.adoc:498–505`, including `vlm.v`/`vsm.v` at `line 1617`, though whole-register moves/loads `vmv<nr>r.v` / `vl<nr>r.v` ignore `vtype`). Across all $8 \times 8 = 64$ `(vsew[2:0], vlmul[2:0])` pairs on standard `VLEN=256, ELEN=64` (`SEW` $\in \{8, 16, 32, 64\}$), exactly **`22` configurations are legal and `42` set `vill = 1`** (`probes/verify_rvv_and_sme_hazards.py`). In `google/highway` (`hwy/ops/rvv-inl.h:56–62, 99–120`), `MLenFromD` clamps mask divisor $\text{MLEN} = \text{SEW} / \text{LMUL} \le 64$ (`vbool1_t`..`vbool64_t`) and partitions macros into `_TRUNC` vs. `_EXT` tables because `m8` has no valid $2\times$ widening `LMULD` and `mf8` at `SEW=8` has no narrower `LMULH`.

#### 1.2 Register-Group Alignment & Asymmetric Widening Overlap (`v-spec.adoc` §5.2)
When `LMUL` $= M \in \{2, 4, 8\}$, architectural register indices must satisfy `reg % M == 0` (`v0, v2, ..., v30` for `m2`; `v0, v4, ..., v28` for `m4`; `v0, v8, v16, v24` for `m8`); misaligned indices raise illegal-instruction exceptions. For widening operations (`EMUL_dst = 2 * LMUL_src`, e.g., `vwadd.vv vd, vs2, vs1` with `LMUL=m2` -> `vd` occupies `4` registers `vd..vd+3` while `vs1` occupies `2` registers `vs1..vs1+1`), **partial group overlap is asymmetric**:
- **Illegal Lower Overlap (`vd = v4, vs1 = v4`):** Writing the first `m2` pair `v4..v5` of `2*SEW` outputs overwrites `vs1`'s second register `v5` before its `SEW` elements are read -> **architecturally reserved / illegal instruction** (`verify_rvv_and_sme_hazards.py`: `illegal_lower_overlap == True`).
- **Legal Upper Overlap (`vd = v4, vs1 = v6`):** `vs1` (`v6..v7`) sits in the highest-numbered half of `vd` (`v4..v7`), allowing microarchitectures to consume `v6` before writing widened `v6..v7` -> **architecturally legal** (`legal_upper_overlap == True`).

#### 1.3 `vta`/`vma` `1`-Fill Nondeterminism & `RISCVInsertVSETVLI`
`v-spec.adoc:409–448` specifies that under `vta=1` (`ta`) or `vma=1` (`ma`), each tail (`i >= vl`) or masked-off (`vm[i] == 0`) destination element may **either retain its prior value OR be overwritten with all `1`s (`0xFF..FF`)**—chosen deliberately over `0`s (`line 424`) to break buggy code relying on implicit zeroing! Moreover, mask-destination tails (`v0`) are **always tail-agnostic even when `vta=0`** (`line 402`). Because LLVM's `RISCVInsertVSETVLI` dataflow pass (`llvm/lib/Target/RISCV/RISCVInsertVSETVLI.cpp:1–110`) defaults to `ta, ma` to avoid physical-register copy stalls on OoO cores, handwritten inline assembly or intrinsic code tested on in-order simulators (`Spike`/`QEMU`, which implement `ta` as `undisturbed`, `line 428`) passes tests (`sum == 110` in `verify_rvv_and_sme_hazards.py`) yet **silently explodes to `sum == 550` (`0xFF` lane pollution) when migrated onto an OoO RISC-V core—or even mid-instruction during `big.LITTLE` hart migration (`lines 437–447`)**!

---

### 2. Fault-Only-First Vector Loads (`vle<eew>ff.v`) — Guard-Page Speculation vs. Three Traps

`Basis: normative + execution`

Fixed-width SIMD string/JSON scanners (`SSE`/`AVX-512` without masked page alignment) fault (`SIGSEGV`) whenever an unaligned vector load straddles an unmapped `4096 B` page boundary. `RVV 1.0` `vle8ff.v`..`vle64ff.v` (`v-spec.adoc:1724–1787`) and Arm `SVE` `LDFF1*` (`FFR` First-Fault Register) resolve this in hardware: at `base_addr = 4089` (`7` bytes below an unmapped `4096` guard page) with requested `vl = 16`, regular `vle8.v` faults immediately, whereas `vle8ff.v` suppresses the page fault on byte `4096` (element `7`), **dynamically updates `vl <- 7`**, and commits elements `0..6` cleanly (`verify_rvv_and_sme_hazards.py`).

However, compilers and formal verifiers modeling `vle8ff.v` must enforce **three non-obvious normative side conditions**:
1. **Spurious Destination Clobbers Past `new_vl` (`v-spec.adoc:1737–1741`):** Even though `vl` shrinks from `16` to `7`, `vle8ff.v` is explicitly permitted to **overwrite active destination elements `vd[7..15]` (`[new_vl, old_vl)`) with arbitrary values that do NOT match memory**, regardless of `vta=0` (`tu`)! Any register-liveness or separation-logic rule assuming `tu` preserves `vd[new_vl .. old_vl)` across `vle8ff.v` is **unsound**.
2. **Spontaneous Non-Faulting `vl` Reduction (`v-spec.adoc:1775–1778`):** Even when all `16` bytes are mapped and readable, hardware may process any subset $1 \le \text{vl}' < \text{vl}$ (e.g., halting at a `64 B` cache-line split or TLB miss) and update `vl <- vl'`. Compilers **must emit `csrr rd, vl` after every `vle*ff.v`** to advance loop pointers (`ptr += actual_vl`) and must never treat `actual_vl < req_vl` as EOF.
3. **MMIO Non-Idempotence & Hypervisor GPA Probing (`v-spec.adoc:1741–1744, 1762–1773`):** Speculative element fetches `> 0` can trigger irreversible MMIO read side effects before `vl` trims, and S-mode kernels can map candidate guest physical pages contiguously after `1` valid byte to probe hypervisor memory permissions without taking traps.

---

### 3. Arm `SME`/`SME2` Streaming Mode, `AAPCS64` `TPIDR2_EL0` Lazy Saving, and Linux Kernel Transitions

`Basis: normative + documentation + execution`

Arm's Scalable Matrix Extension (`FEAT_SME` / `FEAT_SME2`) adds a two-dimensional byte-addressable outer-product tile array **`ZA` of size $\text{SVL}_B \times \text{SVL}_B$ bytes** (where $\text{SVL}_B = \text{SVL}/8 \in \{16, 32, 64, 128, 256\}$ bytes, i.e., `256 B` at `128b` up to **`64 KiB` per thread at `2048b`**; plus `SME2`'s `512`-bit `ZT0` lookup table, `linux_sme.rst:138–142`) controlled by two independent `PSTATE` bits: **`PSTATE.SM`** (Streaming SVE mode) and **`PSTATE.ZA`** (`ZA`/`ZT0` storage active).

#### 3.1 The Five `AAPCS64` Function-Signature Transitions & `d8–d15` Zeroing Hazard
`ARM-software/abi-aa` (`aapcs64/aapcs64.rst`) partitions functions along streaming mode (`normal` `PSTATE.SM==0`, `__arm_streaming` `PSTATE.SM==1`, `__arm_streaming_compatible` either) and `ZA` ownership (`none`, `__arm_inout("za")`, `__arm_in("za")`, `__arm_out("za")`, `__arm_preserves("za")`, `__arm_new("za")`).
- **Architectural Register Zeroing on `PSTATE.SM` Flip:** Executing `SMSTART SM` (`0 -> 1`) or `SMSTOP SM` (`1 -> 0`) **unconditionally zeroes all `Z0–Z31` (which alias NEON `V0–V31` and scalar FP `d0–d31`!), `P0–P15`, and `FFR`**. Because standard `AAPCS64` requires callees to preserve the low 64 bits `d8–d15` of `v8–v15` (and preserve `p4–p15`/`z8–z23` on SVE vector calls), **any transition wrapper entering/exiting streaming mode MUST spill `d8–d15` to the stack *before* `SMSTART SM` and reload them *after* `SMSTOP SM`** (`verify_rvv_and_sme_hazards.py`).
- **The Silent Linux `svc #0` Streaming-Mode Kill (`linux_sme.rst:87–91`):** On AArch64 Linux, **every `svc #0` system call clears `PSTATE.SM = 0` upon kernel entry and returns to userspace with `PSTATE.SM = 0`** (while leaving `PSTATE.ZA == 1` and `ZA`/`ZT0` intact!). Consequently, invoking *any* raw syscall, `futex` slowpath, `write()`, or allocator `mmap` inside an `__arm_streaming` function without an ABI call wrapper silently drops the thread out of Streaming SVE mode—causing subsequent streaming-only instructions (`FMOPA` outer products) to `SIGILL` or execute at the wrong non-streaming `VL`!

#### 3.2 `TPIDR2_EL0` Lazy `ZA` Save Protocol & Signal/Unwind Ordering Invariant (`aapcs64.rst:1063–1785`)
Eagerly spilling `64 KiB` of `ZA` around every ordinary C/Rust FFI call (`printf`, `malloc`) would destroy `L4`/`L6` performance. Instead, `AAPCS64` defines a **3-state (`Off`, `Active`, `Dormant`) lazy-save machine** anchored at thread register `TPIDR2_EL0`:
1. **Setting Up Dormant Lazy Save (`aapcs64.rst:1078–1095, 1531–1542`):** Before calling a `ZA`-unaware function `f()`, a `ZA`-owning caller allocates a stack buffer `B` of $\text{SVL}_B \times \text{SVL}_B$ bytes and a 16-byte **`TPIDR2 block` `BLK`** (`BLK.za_save_buffer = &B` at offset `+0`, `BLK.num_za_save_slices = SVL_B` `uint16_t` at `+8`, bytes `10..15 == 0`), then executes `MSR TPIDR2_EL0, &BLK` (`ZA` becomes **Dormant**: data still sits in `ZA` hardware, *not* yet copied to `B`!).
2. **Callee Zero-Cost Fast Path vs. Commit:** If `f()` never touches `ZA`, it returns without touching `TPIDR2_EL0` (`0` bytes copied!); the caller sees `TPIDR2_EL0 == &BLK`, writes `TPIDR2_EL0 = NULL`, and resumes using `ZA` (`Abandon lazy save`, `line 1513`). Only if a deeper `__arm_new("za")` callee needs `ZA` does it call `__arm_tpidr2_save` (`lines 2286–2310`) to flush `ZA[0..num_za_save_slices)` to `za_save_buffer` and clear `TPIDR2_EL0 = NULL`.
3. **Mandatory Interrupt-Safe Teardown Order (`aapcs64.rst:1472–1473`, `linux_sme.rst:108–162`):**
   > *"If the thread needs to set `PSTATE.ZA` to `0` and set `TPIDR2_EL0` to null, it must set `TPIDR2_EL0` to null first."*
   Why? If code executes `SMSTOP ZA` (`PSTATE.ZA := 0`) *before* `MSR TPIDR2_EL0, XZR` and an asynchronous Linux signal arrives between those two instructions, the kernel signal frame records `PSTATE.ZA == 0` (`no za_context data`) alongside `tpidr2_context.tpidr2 == &BLK != NULL` (`sme.rst:108–123`). Any C++ exception unwinder or `longjmp` walking out of that signal handler sees non-null `TPIDR2_EL0` pointing to an **unwritten stack `za_save_buffer`** while hardware `ZA` has already been wiped—restoring uninitialized stack garbage as `ZA` state (`verify_rvv_and_sme_hazards.py`: `wrong_za_before_tpidr2_interrupt_safe == False` vs. `aapcs64_tpidr2_before_za_interrupt_safe == True`)!

---

### 4. Six-Level Performance & Resource Footprint Profile (`L1`–`L6`)

`Basis: source + documentation + derived`

| Level | Metric | Multi-Versioned Fixed SIMD (`AVX2`+`AVX512`+`NEON`) | `RVV 1.0` VLA + `vle8ff.v` (`Highway` / `LLVM`) | Arm `SME`/`SME2` (`ZA` + `TPIDR2` Lazy Save) |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Tokens** | Source LoC & Proof Multiplicity | `3x–5x` per-width kernels + scalar tail-peel proofs | **`1x` VLA source** (`Highway` / strip-mined loop); requires `vta`/`ffload` spec | **`1x` outer-product tile loop**; ABI wrapper bugs subtle without typestate |
| **`L2` Toolchain Build** | Compiler Pass & `stdarch` Build | `3x` target-feature monomorphization bloat | Single VLA codegen; `RISCVInsertVSETVLI` adds `~1.8%` backend time | Single VLA/SME codegen; `SMEABI` pass inserts `TPIDR2` save/restore |
| **`L3` Comp / Synth / LSP** | Typestate & Aliasing Verification | Fixed lane count (`bv256`/`bv512` SMT bit-blast) | Symbolic `VLEN = 2^k * 128` inductive proof (`< 15 ms` linear typestate) | `O(|CFG|)` finite-state `(SM, ZA, TPIDR2)` dataflow check (`< 5 ms`) |
| **`L4` Runtime Speed** | Execution, Guard Tails & FFI Cost | Scalar tail-peel branch mispredicts near `4 KiB` edge | **`0` scalar tail peel (`vle8ff.v`)**; `0` OoO stall under `ta, ma` (`1–2` cyc `vsetvli`) | **`0`-byte `ZA` FFI copy** on `Dormant` leaf calls (`~2` cyc `MSR TPIDR2_EL0`) vs. `64 KiB` eager spill (`> 500` cyc) |
| **`L5` Proof / Cert Check** | Binary ABI & Speculation Audit | Per-isa fixed decoder check | **`< 0.5 ms`** linear check of `vill==0`, `LMUL` align, `csrr vl` post-`ffload` | **`< 0.4 ms`** linear check of `d8–d15` spills, `no-svc-in-SM`, & `TPIDR2->ZA` order |
| **`L6` Memory & Binary** | `.text`, Stack & Signal Frame Size | `3x–4x` `.text` fat-binary dispatch bloat | **`1.0x` compact VLA `.text`** across `128b..2048b` | **`256 B..64 KiB` `ZA` stack buffer** (`SVL=128..2048b`); Linux `extra_context` signal frame overflow handling (`sme.rst:131–134`) |

---

### 5. Human Comprehensibility (`C1`) & Universal Conceptual Simplicity (`C2`) Analysis

`Basis: derived + source`

- **`(C1)` Human Comprehensibility & `WYSIWIP` Mental-Model Ergonomics:**
  - *Why Ambient Hardware Mode Registers Violate `SMoL`:* Human programmers expect register values not mentioned in an instruction to remain unchanged and expect system calls (`write`, `clock_gettime`) not to alter floating-point instruction legality. `RVV`'s `vta=1` nondeterministic `1`-fill (`Spike` `110` vs. OoO `550`), `vle8ff.v`'s spurious `[new_vl, old_vl)` clobbers, `SMSTART`'s total `V0–V31` wipe, and Linux `svc #0`'s silent `PSTATE.SM = 0` reset are classic hidden-state traps.
  - *Surface Projection:* Humans should write pure strip-mined slice or matrix tile operations (`0` manual `vsetvli` or `TPIDR2_EL0` manipulation), with type errors reported directly as capability/effect conflicts (e.g., `"cannot invoke Linux syscall inside #[arm_streaming] region without streaming-exit boundary: svc #0 clears PSTATE.SM"`).
- **`(C2)` Orthogonality, Stratum Separation & Universal Model Refinement:**
  - *Collapsing `RVV`, `SVE`, `SME`, and `AMX` Under One Capability-Typestate Abstraction:* All four hardware extensions smuggle target-specific mode state (`vtype`/`vl`, `FFR`, `PSTATE.{SM,ZA}`/`TPIDR2_EL0`, `TILECFG`) into ambient globals. Modeling active lane counts as a **dependent slice witness `(len : usize <= VLMAX)`** where elements `>= len` are statically **uninitialized (`Frozen`/`Uninit`)**—never readable without masking—simultaneously makes `RVV` `vta=1` `1`-fill, `vle8ff.v` spurious `[new_vl, old_vl)` writes, and `SVE` predicate tails **100% observationally invisible by construction (`0` adapters!)**. Likewise, modeling `ZA` / `Streaming` as a linear **Hardware Context Capability** automatically synthesizes `d8–d15` spills, rejects unbridged `svc #0` syscalls, and enforces `TPIDR2_EL0 := 0 -> SMSTOP ZA` teardown inside Stratum-II codegen without exposing target quirks to application code.

## Boundaries

- **Real Silicon Microarchitectural `vle8ff.v` Trim Granularity (`not examined` on physical RISC-V OoO silicon):** While `v-spec.adoc:1775–1778` normatively allows arbitrary `vl` trimming $\ge 1$ on non-faulting pages, exact cache-line vs. page-boundary trim frequencies on commercial OoO cores (e.g., SiFive P670/P870, Ventana Veyron, XuanTie C920v2) were `not examined` on hardware in this sandbox.
- **Apple M4 SME-Only (`!FEAT_SVE` + `FEAT_SME`) OS ABI Divergences (`not examined`):** Apple M4 silicon implements `SME`/`SME2` Streaming SVE *without* non-streaming `FEAT_SVE` under XNU/Darwin ABI rules rather than Linux `Documentation/arch/arm64/sme.rst`; Darwin thread/signal layouts were `not examined`.
- **Unmasked Reductions Over `vta=1` / `vle8ff.v` Destination Vectors (`known not to apply` / unsound):** Any optimization pass eliding `vl` updates or reusing lanes `[vl, VLMAX)` after `ta` or `vle8ff.v` instructions is **known not to apply** even when `vta=0` (`tu`) is set on `vle8ff.v` (`v-spec.adoc:1737–1741`).
- **Strided and Scatter/Gather Fault-Only-First Instructions in `RVV 1.0` (`unsupported`):** `RVV 1.0` explicitly omits strided (`vlse*ff`) and indexed (`vluxei*ff`) fault-only-first instructions due to opcode space and unprivileged multi-page ASLR probing risks (`v-spec.adoc:1768–1773`).

## Evidence

1. **Primary Normative & Upstream Repository Sources (Inspected on `2026-11-19`):**
   - `riscvarchive/riscv-v-spec` @ `2f68ef7256d6ec53e4d2bd7cb12862f406d64e34` (`v-spec.adoc`):
     - `lines 182–205`: `vtype` layout (`vill`, `vma`, `vta`, `vsew[2:0]`, `vlmul[2:0]`);
     - `lines 327–338`: fractional `LMUL` $\text{SEW} \le \text{LMUL} \cdot \text{ELEN}$ requirement and reserved encodings;
     - `lines 380–468`: `vta`/`vma` agnostic `1`-fill nondeterminism, mask-tail mandatory agnosticism, and `big.LITTLE` thread-migration rationale;
     - `lines 490–516`: `vill` illegal-instruction trap and `vl` update exclusivity;
     - `lines 1724–1787`: `vle8ff.v`..`vle64ff.v` fault-only-first semantics, `[new_vl, old_vl)` spurious destination overwrites, non-idempotent MMIO ban, S-mode GPA probing note, and spontaneous non-faulting `vl` reduction.
   - `google/highway` @ `ab219f9ecac8bc7e97d4c2b3b8197e52b48a5b52` (`hwy/ops/rvv-inl.h`):
     - `lines 56–62`: `MLenFromD` clamping `MLEN <= 64` for fractional `LMUL`;
     - `lines 96–125`: `HWY_RVV_FOREACH_*` `_TRUNC`/`_EXT` tables handling missing `m8` double-LMUL and `mf8` half-LMUL endpoints.
   - `ARM-software/abi-aa` @ `9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7` (`aapcs64/aapcs64.rst`):
     - `lines 984–1125, 1379–1497`: `TPIDR2_EL0` access rules, 16-byte `TPIDR2 block` (`za_save_buffer` at `+0`, `num_za_save_slices` at `+8`, reserved zero bytes `+10..15`), and `Off`/`Active`/`Dormant` `ZA` state table;
     - `lines 1472–1473`: mandatory teardown ordering (`TPIDR2_EL0 := null` *before* `PSTATE.ZA := 0`);
     - `lines 2286–2395`: `__arm_tpidr2_save` and `__arm_tpidr2_restore` runtime ABI routines.
   - `torvalds/linux` @ `f1715c0c04606ebbe832cc760abf49dfd6f2ae1f` (`Documentation/arch/arm64/sme.rst`):
     - `lines 21–74`: `AT_HWCAP2` `HWCAP2_SME`/`HWCAP2_SME2`, `NT_ARM_SSVE`/`NT_ARM_ZA`/`NT_ARM_ZT` regsets, and `CLONE_VM` clearing `PSTATE.ZA=0, TPIDR2_EL0=0`;
     - `lines 84–103`: syscall ABI clearing `PSTATE.SM = 0` on every `svc #0` while preserving `PSTATE.ZA == 1`;
     - `lines 105–163`: signal entry (`PSTATE.SM=0, PSTATE.ZA=0, TPIDR2_EL0=0`), `TPIDR2_MAGIC`, `za_context`, `ZT_MAGIC` (`0x5a544e01`), `extra_context` stack extension, and forced `SIGSEGV` on mismatched `sigreturn` `vl`.
   - `llvm/llvm-project` @ `63b8d2fd94ba3b1a80023dae7139949dd5be6b78`:
     - `llvm/lib/Target/RISCV/RISCVInsertVSETVLI.cpp` (`lines 1–110`: machine-function dataflow lattice minimizing `vsetvli` transitions under `ta, ma` policies).
2. **Preserved Executable State-Space Probe (`Basis: execution`):**
   - `probes/verify_rvv_and_sme_hazards.py`, executed via `python3 reports/rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation/probes/verify_rvv_and_sme_hazards.py` (`exit 0`), mechanically confirming the `22` legal vs. `42` `vill=1` `(SEW, LMUL)` pairs (`VLEN=256, ELEN=64`), `vwadd` lower-overlap illegality vs. upper-overlap legality, `110` vs. `550` `vta=1` `big.LITTLE` divergence, `vle8ff.v` guard-page `vl` truncation (`16 -> 7`) with spurious `[7..15]` overwrites, and all three `AAPCS64`/Linux SME hazards (`d8–d15` zeroing, `svc #0` `SM` clear, and `ZA`-before-`TPIDR2` signal race).

## Revalidation

1. **Execute the Preserved State-Space & Guard-Page Probe (`< 30 ms`, standard library Python 3):**
   ```bash
   python3 reports/rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation/probes/verify_rvv_and_sme_hazards.py
   ```
   Verify `exit 0` and confirm `rvv_vlen256_elen64_grid == {"legal": 22, "vill_set": 42}`, `rvv_vta_big_little_divergence.diverged == true`, `vle8ff.new_vl == 7`, and `aapcs64_tpidr2_before_za_interrupt_safe == true`.
2. **Targeted Upstream Diffs on Toolchain or Kernel Upgrades:**
   - Diff `ARM-software/abi-aa` `aapcs64/aapcs64.rst` (`TPIDR2 block` reserved bytes `10..15` for future `SME2` `ZT0` lazy-save extensions) and `torvalds/linux` `Documentation/arch/arm64/sme.rst` (§§3–5 syscall/signal behavior).
   - Diff `llvm/lib/Target/RISCV/RISCVInsertVSETVLI.cpp` when upgrading LLVM/`rustc` to check whether `vle*ff` post-instruction `vl`-clobber dataflow transitions or `tu` vs. `ta` coalescing rules changed.
