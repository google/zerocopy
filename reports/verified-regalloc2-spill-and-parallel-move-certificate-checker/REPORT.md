# Verified `RegAlloc2`-Style Allocation, Spill-Slot, and Parallel-Move Certificate Checker in Lean 4.34.1

## Summary

A complete, self-contained, zero-`sorry`, zero-`native_decide` Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization (`support/RegAllocCert/`) designs, verifies, and benchmarks a total, linear-time **register-allocation, spill-slot, and parallel-move cycle-resolution certificate checker (`checkRegAllocCert`)** that discharges `MiniSSA → MiniMach` lowering in a single `HybridTrace` macro-step (`support/run_regalloc_bench.py`, `support/metrics.json`):

1. **Kernel-Checked Simulation Soundness and Bidirectional Completeness (`1,188` Lines / `927` Code Lines):**
   - Across six Lean 4 modules (`Syntax.lean`, `Semantics.lean`, `Certificate.lean`, `Soundness.lean`, `Completeness.lean`, and `Corpus.lean`), the mechanization proves both **simulation soundness (`checkRegAllocCert_sound`)**—establishing that whenever `checkRegAllocCert ssaFn machFn cert = true` under an injective, scratch-disjoint allocation map `ValidAllocMap`, `MiniMach` execution refines `MiniSSA` execution (`Outcome.val`, `Outcome.panic`, `Outcome.ub`)—and **bidirectional checker completeness (`checkRegAllocCert_complete` and `checkRegAllocCert_iff_valid`)** against the inductive specification `ValidRegAlloc`.
   - Clean compilation under `anneal-lean-run --mode build --concurrency 4 -- lake build` finishes in **`4.97` seconds wall-clock** (`5.27s` user CPU, `824.06 MB` peak RSS, `5.10 MB` total `.olean` size). `#print axioms` confirms that `checkRegAllocCert_sound` and all ten positive function refinement theorems (`fnT01_refines`..`fnT10_refines`) depend **only** on `[propext, Quot.sound]`, `checkRegAllocCert_complete` depends only on `[propext]`, and all five negative bug-rejection theorems (`bug1_rejected`..`bug5_rejected`) depend on **zero axioms (`[]`)**.
2. **`26.44x` Certificate Byte Reduction and `330.0x` Step Compression Over Micro-Step `HybridTrace`:**
   - Across the 10 register-pressure-heavy `-O3` benchmark functions (`T01`–`T10`, spanning `11` to `80` live virtual registers, `1` to `65` stack spill slots `[0, 600)`, 2-cycle `xchg` and `%r11`-scratch swaps, 3-cycle loop-backedge rotations, and caller-saved call clobbers), `RegAllocCert` compresses **`3,300` micro-step `HybridTrace` steps (`79,200` bytes)** into **`10` macro-steps (`2,996` bytes)**—a **`26.44x` reduction in certificate bytes** and a **`330.0x` reduction in step count**.
   - Applied to the 12-crate Rust `1.99.1` sample from `rustc-build-ir-and-pass-transformation-volume-statistics` (`404,450` `RegAlloc`/`Spill`/`PrologEpilog` micro-steps occupying `9.26 MB`), elevating `RegAllocCert` to a first-class `HybridTrace` macro-step shrinks backend allocation certificates to **`13,683` macro-steps (`0.35 MB`)**.

## Applicability

- **Extends:** `regalloc2-symbolic-checker-stacking-and-quantitative-stack-bounds-2026`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`, `lean-derivation-checker-soundness-and-completeness-prototype`
- **Metadata:** Created: 2026-11-14 · Updated: 2026-11-14
- **Subjects:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, standard `Init` prelude without Mathlib).
  - `bytecodealliance/regalloc2` at `969bad6297dfca4db2db4eeefebba6c1ebafcf27` (`v0.15.2`, `src/checker.rs` symbolic checker and `src/ion/Moves.rs` parallel-move cycle resolver).
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, LLVM `23.1.1` `RAGreedy` and `PrologEpilogInserter`).
  - `AbsInt/CompCert` at `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (`v3.18`, `backend/Allocproof.v` and `backend/Stackingproof.v`).

## Findings

### 1. Certificate Format and Linear-Time Checker Architecture (`RegAllocCert`)

**Basis: source + execution (`support/RegAllocCert/RegAllocCert/`, `support/metrics.json`)**

In `llvm-o3-derivation-formats-expressiveness-and-checking-cost` and `rustc-build-ir-and-pass-transformation-volume-statistics`, register allocation (`RAGreedy`), live-range splitting, parallel-move resolution on split CFG edges, and `PrologEpilogInserter` account for `6.9%` of all derivation steps (`404,450` steps across the 12-crate sample). Decomposing these passes into elementary micro-rewrites forces the trace to justify intermediate physical-register clobbers and stack-frame `[rsp + offset]` non-aliasing at every move instruction.

To discharge `MiniSSA → MiniMach` lowering in a single macro-step, `RegAllocCert` (`RegAllocCert/Syntax.lean`, `RegAllocCert/Certificate.lean`) couples functional endpoint synthesis (`inferInstPair : (VReg → Loc) → InstCert → SSAInst × MachInst`) with four decidable side-condition checkers:

1. **Unified Virtual-to-Location Map (`alloc : VReg → Loc` where `Loc := PReg ⊎ SpillSlot`):**
   - Each `MiniSSA` virtual register maps to either a physical register `PReg` (`16` GPRs `0..15` + `16` XMMs in `PRegBank`) or a bounded stack spill slot `SpillSlot` (`[offset, offset + sizeBytes)`).
   - Live-range splitting and spill stores/reloads are unified under `.copyVReg dst src ↦ .moveLoc (alloc dst) (alloc src)`, while arithmetic and assertions operate uniformly over `Loc`.
2. **Pairwise Spill-Slot Disjointness and Frame Bounds (`checkSpillListValid`):**
   - `checkSpillInBounds frameSize s` verifies `0 < s.sizeBytes ∧ s.offset + s.sizeBytes ≤ frameSize`, guaranteeing that no spill slot underflows or overflows `[0, frameSize)` into the return address or caller stack frame.
   - `checkSpillDisjoint s1 s2` verifies `s1.offset + s1.sizeBytes ≤ s2.offset ∨ s2.offset + s2.sizeBytes ≤ s1.offset`.
3. **Parallel-Move Cycle Resolution (`parSwap2` and `parRotate3`):**
   - When lowering $\phi$-nodes on split CFG edges, permutation cycles among physical registers or spill slots cannot be executed as naive sequential moves without overwriting a source before it is read.
   - `RegAllocCert` models simultaneous parallel assignments in `MiniSSA` (`parSwap2 v1 v2` and `parRotate3 v1 v2 v3`) and verifies their sequential `MiniMach` decompositions (`execSwap2Mach` via hardware `xchg` or 3-step `viaScratch %r11`, and 4-step `execRotate3Mach` via `%r11`) under `checkScratchDisjoint2` and `checkScratchDisjoint3`.
4. **Caller-Saved Call Clobber Isolation and Callee-Saved ABI Preservation (`checkABICalleeSaved`):**
   - `evalMachInst` models `.callClobberLoc dst arg delta clob` by reading `arg`, clobbering `Loc.preg clob` to `0`, and writing `dst`. `checkCertSideConds` verifies `clob = reservedScratch`, while `checkABICalleeSaved` checks that every modified callee-saved register (`%rbx, %rbp, %r12..%r15` on SysV x86-64) saved in the prologue is restored from the identical bounded spill slot in the epilogue.

---

### 2. Lean 4.34.1 Mechanization Metrics and Verified Boundary Theorems

**Basis: source + execution (`support/RegAllocCert/`, `support/metrics.json`)**

| Module | Total Lines | Code Lines | `.olean` Size (`B`) | Primary Definitions & Kernel-Checked Theorems |
| :--- | ---: | ---: | ---: | :--- |
| `RegAllocCert/Syntax.lean` | `102` | `65` | `2,201,048` | `VReg`, `PRegBank`, `PReg`, `SpillSlot`, `Loc`, `CycleResolution`, `SSAInst`, `MachInst`, `SSAFunc`, `MachFunc` |
| `RegAllocCert/Semantics.lean` | `173` | `125` | `362,992` | `Outcome`, `refines`, `SSAState`, `MachState`, `execSwap2Mach`, `execRotate3Mach`, `evalSSAInst`, `evalMachInst` |
| `RegAllocCert/Certificate.lean` | `134` | `94` | `1,085,800` | `checkSpillListValid`, `checkScratchDisjoint2`, `checkScratchDisjoint3`, `InstCert`, `inferInstPair`, **`checkRegAllocCert`** |
| `RegAllocCert/Soundness.lean` | `255` | `224` | `797,424` | `ValidAllocMap`, `stateSim`, `stateSim_swap2`, `stateSim_rotate3`, `inferInstPair_sound`, **`checkRegAllocCert_sound`** |
| `RegAllocCert/Completeness.lean` | `163` | `138` | `229,024` | `ValidInstCert`, `ValidRegAlloc`, `checkInstCert_iff_valid`, **`checkRegAllocCert_complete`**, **`checkRegAllocCert_iff_valid`** |
| `RegAllocCert/Corpus.lean` | `361` | `281` | `420,792` | `stdAlloc_valid`, `fnT01_refines`..`fnT10_refines` (`10` `-O3` functions), `bug1_rejected`..`bug5_rejected` (`5` bug injections) |
| **Total (`RegAllocCert`)** | **`1,188`** | **`927`** | **`5,097,080`** | **Built in `4.97s` wall (`824.06 MB` RSS); zero `sorry`, zero `native_decide`** |

The top-level soundness and completeness theorems verified by the Lean `v4.34.1` kernel are:

```lean
theorem checkRegAllocCert_sound
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle)
    (h_wf : ValidAllocMap cert.alloc cert.reservedScratch)
    (h_check : checkRegAllocCert ssaFn machFn cert = true)
    (st : SSAState) (ms : MachState)
    (h_sim : stateSim cert.alloc st ms)
    (argVal : Int) :
    refines (evalSSAFunc ssaFn st argVal) (evalMachFunc machFn ms argVal)

theorem checkRegAllocCert_iff_valid
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle) :
    checkRegAllocCert ssaFn machFn cert = true ↔ ValidRegAlloc ssaFn machFn cert
```

---

### 3. Quantitative Comparison Against Micro-Step `HybridTrace` Across 10 `-O3` Functions and 5 Injected Bugs

**Basis: execution (`support/RegAllocCert/RegAllocCert/Corpus.lean`, `support/metrics.json`)**

| Function ID | Live VRegs | Spill Slots | Callee Saves | `MiniSSA` Insts | Cycle Resolution Mode | Micro-Step `HybridTrace` Steps / Bytes | `RegAllocCert` Macro-Steps / Bytes | Byte Reduction | Kernel Check Status |
| :--- | ---: | ---: | ---: | ---: | :--- | ---: | ---: | ---: | :--- |
| **`T01_regalloc_with_spills`** | `13` | `2` | `2` | `18` | 2-cycle via `%r11` | `112` / `2,688 B` | `1` / `96 B` | **`28.00x`** | `= true` (`rfl`) |
| **`T02_loop_backedge_rotate3`** | `11` | `1` | `1` | `16` | 3-cycle via `%r11` | `98` / `2,352 B` | `1` / `80 B` | **`29.40x`** | `= true` (`rfl`) |
| **`T03_pressure_68vregs_xchg`** | `68` | `53` | `5` | `94` | 2-cycle via `xchg` | `642` / `15,408 B` | `1` / `616 B` | **`25.01x`** | `= true` (`rfl`) |
| **`T04_dual_call_clobber_spill`** | `22` | `8` | `3` | `31` | Call live-range splits | `204` / `4,896 B` | `1` / `176 B` | **`27.82x`** | `= true` (`rfl`) |
| **`T05_diamond_swap2_rotate3`** | `19` | `4` | `2` | `28` | 2-cycle + 3-cycle | `186` / `4,464 B` | `1` / `144 B` | **`31.00x`** | `= true` (`rfl`) |
| **`T06_bitmix_ub_guard_spill`** | `26` | `11` | `2` | `36` | 2-cycle via `%r11` | `228` / `5,472 B` | `1` / `204 B` | **`26.82x`** | `= true` (`rfl`) |
| **`T07_spill_to_spill_cycle`** | `34` | `19` | `4` | `48` | Spill 2-cycle via `%r11` | `334` / `8,016 B` | `1` / `292 B` | **`27.45x`** | `= true` (`rfl`) |
| **`T08_mixed_gpr_spill_rot3`** | `42` | `27` | `4` | `62` | GPR/spill 3-cycle | `418` / `10,032 B` | `1` / `380 B` | **`26.40x`** | `= true` (`rfl`) |
| **`T09_chained_bounds_reload`** | `30` | `15` | `3` | `44` | Live-range split reload | `286` / `6,864 B` | `1` / `256 B` | **`26.81x`** | `= true` (`rfl`) |
| **`T10_sysv_80vregs_unwind`** | `80` | `65` | `6` | `115` | 2-cycle + unwind frame | `792` / `19,008 B` | `1` / `752 B` | **`25.28x`** | `= true` (`rfl`) |
| **Total (10-Function Corpus)** | — | `205` | `32` | **`492`** | — | **`3,300` / `79,200 B`** | **`10` / `2,996 B`** | **`26.44x`** | **`10 / 10` verified** |

All five injected allocator bugs in `RegAllocCert/Corpus.lean` are deterministically rejected in $O(1)$–$O(N)$ time by kernel `rfl`:
1. **`bug1_rejected` (`bug1_ClobberLiveReg`):** Caller-saved clobber targets live GPR `0` (`%rax`) across a call instead of `reservedScratch` (`%r11`).
2. **`bug2_rejected` (`bug2_OverlappingSpills`):** Two 8-byte/4-byte spill slots `[0, 8)` and `[4, 8)` overlap by 4 bytes (`checkSpillDisjoint = false`).
3. **`bug3_rejected` (`bug3_BadCycleScratch`):** A 2-way parallel swap uses live register `GPR 1` as its cycle-breaking scratch register, overwriting `v1` before reading it.
4. **`bug4_rejected` (`bug4_MachFuncMissingCalleeRestore`):** Callee-saved register `%r12` is saved to `[rsp+24..32)` in the prologue but omitted from `epilogueRestores`.
5. **`bug5_rejected` (`bug5_MachFuncMissingReload`):** An `add` instruction after a call reads un-reloaded `GPR 3` (`%rbx`) instead of the spilled slot `stdAlloc 12` (`[rsp+8..16)`).

## Boundaries

- **Rematerialization across non-pure memory loads — not examined:** `RegAllocCert` verifies register-to-spill copies, constant rematerialization (`constI`), and arbitrary 2-way/3-way cycle decompositions, but does not model rematerializing loads from read-only global memory (`RIP`-relative constant pools).
- **Sub-register aliasing (`%eax` / `%ax` / `%al` inside `%rax`) — known not to apply to flat `PReg` indices without width masks:** `MiniMach` models each `PReg` as a full-width architectural register (`GPR 0..15`, `XMM 0..15`) while tracking exact byte intervals `[offset, offset + sizeBytes)` on stack `SpillSlot`s. Supporting x86 partial-register writes (`%ah` vs. `%al`) requires either normalizing sub-register writes to full-register shifts/masks in `MiniMach` or attaching a 64-bit lane mask to `PReg`.

## Evidence

- **Lean `v4.34.1` Mechanization (`support/RegAllocCert/`):**
  - `support/RegAllocCert/RegAllocCert/Syntax.lean` (lines `1`–`102`)
  - `support/RegAllocCert/RegAllocCert/Semantics.lean` (lines `1`–`173`)
  - `support/RegAllocCert/RegAllocCert/Certificate.lean` (lines `1`–`134`)
  - `support/RegAllocCert/RegAllocCert/Soundness.lean` (lines `1`–`255`)
  - `support/RegAllocCert/RegAllocCert/Completeness.lean` (lines `1`–`163`)
  - `support/RegAllocCert/RegAllocCert/Corpus.lean` (lines `1`–`361`)
- **Benchmark Runner and Telemetry (`support/run_regalloc_bench.py`, `support/metrics.json`):**
  - Records clean build timing (`4.969s`), peak RSS (`824.06 MB`), per-module `.olean` sizes, axiom footprints, and per-function byte reductions (`26.44x`).

## Revalidation

Run the self-contained verification and benchmark script from the package directory:

```bash
python3 support/run_regalloc_bench.py
```

The script cleans `.lake/build`, compiles all six `RegAllocCert` modules under `anneal-lean-run --mode build --concurrency 4 -- lake build`, verifies that `fnT01_refines`..`fnT10_refines` and `bug1_rejected`..`bug5_rejected` elaborate with zero `sorry` and zero `native_decide`, and regenerates `support/metrics.json`.
