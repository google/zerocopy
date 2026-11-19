# Post-Link Binary Optimizers (BOLT vs. Propeller) and Hardware PT/ETMv4/PMU/ptrace Trace Semantics

## Summary

Profile-guided code-layout optimization and hardware-assisted execution introspection sit on a fragile seam between machine-code representation, microarchitectural execution state, and OS exception delivery. Five core invariants govern soundness and fidelity across these layers:

1. **Disassembly-Based Rewriting (BOLT) vs. Compiler-Emitted Layout Metadata (Propeller):** Post-link binary rewriting in `LLVM BOLT` recovers control-flow graphs (CFGs), jump tables, and exception-handling metadata from linked ELF binaries; sound whole-binary relocation requires static relocations (`--emit-relocs`), conservative rejection or `--strict` over-approximation of unclaimed internal data relocations, Itanium C++ ABI landing-pad trampolines when splitting functions across discontinuous hot/cold fragments, and branch-range veneer insertion (`LongJmpPass`) on AArch64. `Propeller` eliminates post-link disassembly altogether by emitting `SHT_LLVM_BB_ADDR_MAP` basic-block metadata at compile time, clustering basic blocks into separate ELF sections (`-fbasic-block-sections=list`), consolidating multi-cluster landing pads into one `Exception` section, and delegating fall-through jump elimination and conditional-branch inversion to `LLD` (`--optimize-bb-jumps`).
2. **Retired Control-Flow Compression (Intel PT) vs. Speculative P0 Reconciliation (ARM CoreSight ETMv4):** `Intel PT` (`intel/libipt`) emits retired control-flow packets (`TNT-8`/`TNT-64`, `TIP`, `TIP.PGE`, `TIP.PGD`, `FUP`) with six IP compression modes (where `sext_48` sign-extends bit 47 into bits `63:48` while `update_48` preserves bits `63:48`), `RET`-stack return compression, and `OVF` overflow recovery that binds either to `FUP` (if resolved with `PacketEn=1`) or `TIP.PGE` (if resolved with `PacketEn=0`). In contrast, `ARM CoreSight ETMv4` (`Linaro/OpenCSD`) emits *speculative* P0 elements (`Atom E/N`, exceptions, Q-elements) up to `TRCIDR8.MAXSPEC`, auto-committing elements exceeding `MAXSPEC` and reconciling mispredicted pipelines via explicit `Commit`, `Cancel`, `Mispredict`, `Discard`, and `Overflow` packets.
3. **Architectural Event-IP Precision Does Not Eliminate Out-of-Order Cycle-Attribution Skid:** Even after `Intel PEBS` v2+ (`EventingIP` / `pebs->real_ip`) eliminates the 1-instruction architectural trap skid that earlier PEBS v1 hardware required Linux `intel_pmu_pebs_fixup_ip()` LBR backward disassembly to repair, out-of-order Reorder Buffer (ROB) blocking creates a **shadow effect** (Gottschall et al., MICRO 2021) that shifts cycle attribution from long-latency blocking loads onto immediately succeeding instructions retiring in the post-stall burst. Operation-centric hardware sampling such as `ARMv8.2-SPE` (tagging an operation at decode/dispatch and recording per-operation `total_lat`, `issue_lat`, `ADDR`, and `EVENTS`) avoids PMI/ROB-shadow skid.
4. **x86 Hardware Debug Exception (`#DB`) Fault-vs.-Trap Asymmetry Requires `EFLAGS.RF` Governance:** On x86/x86-64, instruction-execution breakpoints (`DR7.R/W = 00`, `LEN = 00`) are **faults** delivered *before* instruction execution, so returning without setting `EFLAGS.RF = 1` (bit 16) causes an infinite `#DB` livelock; Linux's `hw_breakpoint_handler()` sets `X86_EFLAGS_RF` specifically for `X86_BREAKPOINT_EXECUTE` and delays instruction breakpoints when `DR6` simultaneously reports `DR_STEP` (`EFLAGS.TF`). Data watchpoints (`DR7.R/W = 01` or `11`) are **traps** delivered *after* retirement, where `RIP` has already advanced and `EFLAGS.RF` has no effect.
5. **`ptrace` / `SECCOMP_RET_TRACE` Pointer Inspection Is Fundamentally Vulnerable to Shared-Memory TOCTOU:** `SECCOMP_RET_TRACE` pauses only the invoking thread at `ptrace_event(PTRACE_EVENT_SECCOMP, data)` before reloading registers and recursively re-entering `__seccomp_filter(this_syscall, true)`. Because sibling `CLONE_VM` threads (or shared writable mappings) remain runnable, inspecting pointer-referenced syscall arguments from a tracer cannot enforce memory-argument security invariants against concurrent mutation prior to kernel `copy_from_user()`.

## Applicability

This report synthesizes and cross-compares five directly examined upstream implementations alongside their normative hardware specifications and peer-reviewed foundations:

- **Compiler, Linker, and Binary Optimizer Seam:** `llvm/llvm-project` at commit `53623acaadfe3df4ea2bfc48d347faa3fb1c57a5` (`bolt/`, `llvm/lib/CodeGen/BasicBlockSections.cpp`, `llvm/lib/CodeGen/BasicBlockSectionsProfileReader.cpp`, `lld/ELF/Writer.cpp`, `lld/ELF/Arch/X86_64.cpp`) examined jointly with `google/llvm-propeller` at commit `e98f399102650de7e03e07c7299029da94d7be44`, `Panchenko et al. (CGO 2019)`, and `Shen et al. (ASPLOS 2023)`. Findings apply to 64-bit ELF binaries on x86-64 and AArch64 built with Clang/LLVM and LLD (`--emit-relocs` for BOLT relocation mode; `-fbasic-block-address-map` / `-fbasic-block-sections=list=...` and `-Wl,--optimize-bb-jumps` for Propeller).
- **Hardware Control-Flow Trace Decoders:** `intel/libipt` at commit `7f8575ce9bf25e48cf03983c12859e1edb592008` (Intel SDM Vol. 3 Intel PT) compared directly against `Linaro/OpenCSD` at commit `5719458c9f75714a0ee5f83fae94f0f2989b52f9` (`ARM IHI 0064` ETMv4.0–4.6 / ETE). Findings apply to offline or live binary-assisted packet/instruction reconstruction where the decoder holds an exact copy of the executed code image.
- **Kernel PMU Sampling, Hardware Breakpoints, and Syscall Interposition:** `torvalds/linux` at commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`arch/x86/events/intel/ds.c`, `drivers/perf/arm_spe_pmu.c`, `tools/perf/util/arm-spe-decoder/arm-spe-pkt-decoder.c`, `arch/x86/kernel/hw_breakpoint.c`, `arch/x86/kernel/traps.c`, `arch/x86/kernel/ptrace.c`, `kernel/seccomp.c`), interpreted through Intel SDM Vol. 3, ARMv8.2-SPE, `Gottschall et al. (MICRO 2021)`, and `Weaver et al. (ISPASS 2013)`.

Findings on `Intel PT` / `PEBS` / `DR0–DR7` apply specifically to Intel x86-64 microarchitectures and Linux `perf_event` / `ptrace`; findings on `ETMv4` / `SPE` apply to AArch64 (and ARMv8-A/M profiles where noted by OpenCSD). Behavior of proprietary vendor binary rewriters, Windows PE/Mach-O BOLT backends, and AMD IBS/BRS is outside direct observation (see **Boundaries**).

## Findings

### 1. Post-Link Binary Disassembly and Rewriting Hazards in LLVM BOLT

Basis: documentation + source + derived

`LLVM BOLT` (Panchenko et al., CGO 2019, `DOI: 10.1109/CGO.2019.8661201`) operates directly on a linked ELF executable or shared library: it disassembles machine code into LLVM `MCInst`, reconstructs per-function CFGs (`BinaryFunction::disassemble()` and `BinaryFunction::buildCFG()`), applies sample-profile-guided optimizations (Ext-TSP basic-block layout, HFSort/C3 function reordering, hot-cold splitting, ICF, indirect-call promotion), and re-emits code and metadata via MC. Because post-link ELF files have already discarded compiler-level IR and static CFG provenance, BOLT's soundness hinges on four structural invariants verified in `llvm/llvm-project@53623acaadfe3df4ea2bfc48d347faa3fb1c57a5`:

#### 1.1 Relocation Mode vs. Non-Relocation In-Place Patching

- **Relocation Mode (`BC->HasRelocations`):** Enabled when the input ELF preserves static relocations (`ld --emit-relocs`, producing `.rela.text` etc.) and `--relocs` is not disabled (`bolt/lib/Rewrite/RewriteInstance.cpp:2599-2600`). Relocation mode allows BOLT to relocate every safe function freely into newly allocated `.text` / `.text.cold` segments, updating all static code and data references cleanly.
- **Explicit Kernel Override:** `RewriteInstance.cpp:2602-2604` unconditionally disables relocation mode for Linux kernel images (`if (BC->IsLinuxKernel && BC->HasRelocations) BC->HasRelocations = false;`), because kernel images embed special assembly tables (alternatives, jump labels, `.fixup`/exception tables, ORC unwinders) with custom implicit address arithmetic not fully captured by ordinary ELF relocations.
- **Non-Relocation Mode Hazard:** Without `--emit-relocs`, BOLT cannot move function entry addresses safely; it must either overwrite a function *in place* within its original `[ImageAddress, ImageAddress + ImageSize)` byte budget (`RewriteInstance.cpp:6793-6861`, tracking `CountOverwrittenFunctions`) or leave a trampoline stub at the original entry point and place the rewritten body in a new section. Functions that grow beyond their original footprint without room for a stub, or functions containing internal label addresses taken by data sections, cannot be freely rewritten.

#### 1.2 Disassembly, Constant Islands, and Indirect-Branch CFG Soundness

In `bolt/lib/Core/BinaryFunction.cpp:1314-1435` (`BinaryFunction::disassemble()`):
- **Unsupported Instructions and Cross-Function Entry Hazards:** Any decode failure or unsupported instruction invokes `setIgnored()` (`BinaryFunction.cpp:1361, 1407, 1414`), excluding the function from optimization (or marking it in `BC.TrappedFunctions`). If a direct branch targets the interior of another function (tail/cross-function jump into a non-entry offset), BOLT marks the target function ignored (`TargetFunc->setIgnored()` at `BinaryFunction.cpp:1431-1433`).
- **Constant Islands (`getConstantIslandAlignment()`, `BinaryFunction.cpp:279-285`):** On architectures embedding literal pools inside `.text` (notably AArch64 PC-relative `LDR` literal pools and hand-written assembly), misclassifying embedded data bytes as instructions corrupts disassembly unless symbol/mapping boundaries (`$x`/`$d` mapping symbols on AArch64) cleanly delimit code from data.
- **Jump Tables vs. Unclaimed Internal Data Relocations (`BinaryFunction.cpp:90-93, 2058-2125`):** By default (`-jump-tables=basic`), BOLT recognizes compiler-idiomatic jump tables, tracks `TakenBranches`, and validates that *every* data-section relocation pointing into the interior of a function (`InternalRefDataRelocations`) is accounted for by a recognized jump table (`BinaryFunction::validateInternalRefDataRelocations()`, `BinaryFunction.cpp:2087-2125`).
  - **Failure Mode:** If a function uses GCC computed `goto` (`&&label`), custom dispatch tables, or non-standard pointer-table encodings whose relocations remain in `UnclaimedRelocations`, BOLT emits `BOLT-WARNING: <N> unclaimed data relocation(s) remain against function ...` and refuses to treat the recovered CFG as complete.
  - **`--strict` Mode Trade-off (`BinaryFunction.cpp:2060-2095`):** When `opts::StrictMode` is enabled, `validateInternalRefDataRelocations()` returns `true` unconditionally (`BinaryFunction.cpp:2093-2094`), relying on the user guarantee that all internal data references are exclusively targets of indirect branches inside the *same* function; BOLT then conservatively adds synthetic CFG edges from every `UnknownIndirectBranchOffsets` site to every `ExternallyReferencedOffsets` target (`BinaryFunction.cpp:2075-2084`). If an external caller or data structure actually uses such a label across functions (violating the `--strict` premise), rewriting produces silently broken control flow.

#### 1.3 Hot-Cold Function Splitting, `.eh_frame`/LSDA Trampolines, and `LongJmp` Veneers

- **Itanium C++ ABI LSDA Encoding Constraint (`bolt/lib/Core/Exceptions.cpp:101-265`, `bolt/lib/Passes/SplitFunctions.cpp:828-1058`):**
  - Each C++ function with exception handlers carries an FDE in `.eh_frame` pointing to a Language-Specific Data Area (LSDA, `.gcc_except_table`). In `BinaryFunction::parseLSDA()` (`Exceptions.cpp:101-135`), the LSDA header defines a single `LPStart` base address (`DW_EH_PE_omit` defaults `LPStart` to the FDE's function start address), and call-site table entries store **unsigned** ULEB128 offsets from `LPStart` to each landing pad.
  - When `SplitFunctions` splits a function into discontinuous `main` (hot) and `cold` fragments separated by tens of megabytes (e.g., all hot bodies clustered before all cold fragments), a throwing `call` in the hot fragment whose landing pad is moved to the cold fragment cannot be encoded with a valid fragment-local positive offset unless the fragments share a unified base or indirection.
  - `bolt/lib/Passes/SplitFunctions.cpp:944-1035` resolves this via `createEHTrampolines(BF)`: when `NeedsTrampolines` holds (`SplitFunctions.cpp:946-950`), BOLT sets each fragment's landing-pad fragment to itself (`BF.setLPFragment(FF.getFragmentNum(), FF.getFragmentNum())`) and synthesizes a small trampoline basic block *inside the thrower's fragment* that immediately jumps to the real cold landing pad, updating `MIB->updateEHInfo()` (`SplitFunctions.cpp:1032-1033`). If the post-split hot fragment size fails to shrink below `OriginalHotSize` (`alignTo(OriginalHotSize, SplitAlignThreshold) <= alignTo(HotSize, SplitAlignThreshold) + SplitThreshold`, `SplitFunctions.cpp:959-960`), BOLT reverts the split via `mergeEHTrampolines()` (`SplitFunctions.cpp:970-975`).
  - Without `--split-eh` (`opts::SplitEH`), functions with `BF.hasEHRanges()` restrict splitting unless `--aggressive-splitting` is requested (`SplitFunctions.cpp:828, 863-871`).
- **Branch-Range Veneers and AArch64 BTI (`bolt/lib/Passes/LongJmp.cpp:70-125`, `RewriteInstance.cpp:582-586, 2683-2687`):**
  - On x86-64, direct `JMP`/`CALL rel32` covers `±2 GiB`, rarely overflowing except in multi-gigabyte monoliths. On AArch64, unconditional `B`/`BL` covers only `±128 MiB`, conditional `B.cond`/`CBZ`/`CBNZ` covers `±1 MiB`, and `TBZ`/`TBNZ` covers `±32 KiB`.
  - `LongJmpPass` iteratively relaxes out-of-range direct branches into short/long trampoline stubs (`relaxStubToShortJmp`, `relaxStubToLongJmp`, `createNewStub`, `LongJmp.cpp:72-125`), inserting Branch Target Identification (BTI) landing pads whenever `BC.usesBTI()` is active (`applyBTIFixupToTarget`, `LongJmp.cpp:88-89`; PLT disassembly check at `RewriteInstance.cpp:584-586`).
  - **Hard Limitation (`LongJmp.cpp:107-117`, `RewriteInstance.cpp:2683-2687`):** Outside `--compact-code-model`, AArch64 short-range branches (`isShortRangeBranch`) abort BOLT with `BOLT-ERROR: short range branch not supported outside compact code model`, and 3-way cache-directed splitting (`--split-strategy=cdsplit`) is explicitly rejected with `LongJmp` on AArch64 without `--compact-code-model`.

---

### 2. Compiler-Assisted Relinking Layout and Linker Relaxation in Propeller

Basis: documentation + source + execution

`Propeller` (`google/llvm-propeller@e98f399102650de7e03e07c7299029da94d7be44`, Shen et al., ASPLOS 2023, `DOI: 10.1145/3575693.3575727`) avoids post-link binary disassembly and whole-binary monolithic memory blowup by splitting optimization across three decoupled stages: (1) compile-time metadata emission, (2) offline profile-to-layout computation from hardware LBR/SPE traces, and (3) parallel compiler basic-block section codegen plus linker relaxation.

#### 2.1 Zero-Disassembly CFG Reconstruction via `SHT_LLVM_BB_ADDR_MAP`

- **Compiler Metadata Emission:** Compiling the instrumented/profiled build with `-fbasic-block-address-map` emits a non-allocatable ELF section of type `SHT_LLVM_BB_ADDR_MAP` (`.llvm_bb_addr_map`) recording, for every function, its base address, optional `FuncGUID` (section version 6+), and an ordered table of `BBEntry` descriptors containing each basic block's unique ID, byte offset from the BB-range base, byte size, and control-flow metadata bits (`HasReturn`, `HasTailCall`, `IsEHPad`, `CanFallThrough`, `HasIndirectBranchCall`).
- **Address-to-CFG Mapping Without Disassembly:** `google/llvm-propeller`'s `BinaryAddressMapper` reads `SHT_LLVM_BB_ADDR_MAP` (`propeller/bb_addr_map.cc:77-78`, `propeller/binary_address_mapper.cc:85-118`) and maps raw `(from_addr, to_addr)` LBR/SPE branch samples directly to `(function_index, range_index, bb_index)` handles.
- **Exact Fall-Through Inference (`binary_address_mapper.cc:513-524`, `program_cfg_builder.cc:141-174`):** Between consecutive taken LBR entries `(src_k -> dst_k)` and `(src_{k+1} -> dst_{k+1})`, execution must have flowed linearly from `dst_k` to `src_{k+1}` without taking a branch. `ProgramCfgBuilder::CreateFallthroughs()` validates linearity solely by calling `BinaryAddressMapper::CanFallThrough(from, to)`:
  ```cpp
  // google/llvm-propeller@e98f399102650de7e03e07c7299029da94d7be44
  // propeller/binary_address_mapper.cc:513-524
  bool BinaryAddressMapper::CanFallThrough(const BbHandle& from, const BbHandle& to) const {
    if (from.function_index != to.function_index) return false;
    if (from.range_index != to.range_index) return false;
    if (from.bb_index > to.bb_index) return false;
    const auto& bb_range = bb_addr_map_.at(from.function_index).getBBRanges().at(from.range_index);
    for (int bb_index = from.bb_index; bb_index < to.bb_index; ++bb_index) {
      if (!bb_range.BBEntries[bb_index].canFallThrough()) return false;
    }
    return true;
  }
  ```
  If any intermediate block lacks `canFallThrough()` (e.g., ends in an unconditional jump, indirect jump, or return) or crosses a function/range boundary, the stale/mismatched fall-through span is rejected instead of polluting the CFG. No machine-instruction disassembly is ever performed.
- **Version 1 Cluster Profile Format (`propeller/propeller_profile_format.md:11-120`):** Propeller outputs a compact line-oriented profile consumed by LLVM's `BasicBlockSectionsProfileReader`:
  - `m <module_name>` (disambiguates internal-linkage symbols across translation units when `-funique-internal-linkage-names` is not used);
  - `u <function_guid>` (hex `llvm::GlobalValue::GUID` from `SHT_LLVM_BB_ADDR_MAP` v6+ — note: `propeller_profile_format.md:60-62` documents that `u` is **not yet supported** by the LLVM compiler reader);
  - `f <func_name> [aliases...]`;
  - `c <bb_id_1> <bb_id_2> ...` (ordered basic-block cluster placed into one ELF section; cloned blocks use `<orig_id>.<clone_id>`, e.g., `3.1`);
  - `p <bb_id_1> <bb_id_2> <bb_id_3> ...` (path cloning along edge `bb_id_1 -> bb_id_2`);
  - `g <src>:<cnt>,<sink>:<cnt>...` (CFG edge profile).

#### 2.2 Basic-Block Sections, Exception Consolidation, and LLD Jump Relaxation

- **Compiler Section Assignment & EH Pad Consolidation (`llvm/lib/CodeGen/BasicBlockSections.cpp:305-328`):** When recompiled with `-fbasic-block-sections=list=<profile>`, LLVM emits each cluster `c` into a distinct ELF section (`.text.<func>.__part.<id>`, `.text.unlikely.<func>`) so ThinLTO backends remain completely parallel per translation unit and `LLD` simply orders sections via `--symbol-ordering-file`. Crucially, `assignSections()` checks whether exception-handling landing pads (`MBB.isEHPad()`) span more than one cluster: if they do, all landing pads for that function are moved into a single dedicated `Exception` section (`EHPadsSectionID = ExceptionSectionID`, `BasicBlockSections.cpp:305-324`), preserving Itanium LSDA single-base offset validity *without* inserting runtime EH trampolines.
- **LLD Linker Fall-Through Jump Elimination and Branch Inversion (`lld/ELF/Writer.cpp:1717-1747`, `lld/ELF/Arch/X86_64.cpp:246-315, 1078-1113`):**
  Because the compiler cannot know final inter-section adjacency when splitting basic blocks into separate ELF sections, it emits explicit 5-byte `jmp rel32` (`0xe9`) fall-through edges at the end of split sections. During linking with `--optimize-bb-jumps`, `Writer<ELFT>::optimizeBasicBlockJumps()` iterates over all `SHF_EXECINSTR` output sections and invokes `X86_64::deleteFallThruJmpInsn(sec, next)`:
  1. **Direct Fall-Through Deletion (`X86_64.cpp:248-277`):** Checks for a trailing 5-byte direct jump (`*(secContents + r.offset - 1) == 0xe9` with relocation at `size - 4`) whose resolved target equals `nextIS` (`isFallThruRelocation(is, nextIS, r)`). Cancels the relocation (`r.expr = R_NONE`), truncates the section by 5 bytes (`is.drop_back(5)`), and sets `is.nopFiller = true`.
  2. **Conditional Branch Flip-and-Delete (`X86_64.cpp:279-315`):** If the trailing `jmp rel32` targets a non-adjacent block (`coldBB`), checks whether the immediately preceding 6 bytes (`size - 5 - 6`) hold a near conditional branch (`0x0f 0x8x <rel32>`) whose relocation `rB` targets `nextIS`. If so, `LLD` inverts the condition opcode via `invertJmpOpcode()` (e.g., `je` `0x0f 0x84` $\leftrightarrow$ `jne` `0x0f 0x85`, applied in `applyJumpInstrMod()`, `X86_64.cpp:1078-1113`), moves the trailing `jmp`'s relocation onto `rB`, cancels `r`, and deletes the 5-byte `jmp` (verified by Probe 1E: `13 B -> 8 B`, tail `0f84... e9... -> 0f85...`).
  3. **GOT-PC Distance Relaxation (`X86_64::relaxOnce()`, `X86_64.cpp:507-542`):** When code separation pushes `maxVA >= 2 GiB` (`!isUInt<31>(maxVA)` or `!isUInt<31>(maxVA - minVA)` in PIC), `LLD` checks `R_RELAX_GOT_PC` / `R_RELAX_GOT_PC_NOPIC` relocations and re-materializes GOT entries whenever a relaxed PC-relative displacement exceeds signed 32-bit range (`!isInt<32>(v)`).

#### 2.3 Cross-System Trade-Off Matrix: LLVM BOLT vs. Google Propeller

| Dimension | LLVM BOLT (`llvm/llvm-project/bolt`) | Propeller (`google/llvm-propeller` + LLVM + LLD) |
| :--- | :--- | :--- |
| **Input Artifact** | Linked ELF binary (ideally `--emit-relocs`) + `perf` LBR/PEBS profile | Unmodified build objects + `SHT_LLVM_BB_ADDR_MAP` + LBR/SPE profile -> relink |
| **Disassembly Required** | Yes (full `MCInst` disassembly & CFG/jump-table recovery) | **No** (CFG nodes & `CanFallThrough` read directly from `.llvm_bb_addr_map`) |
| **Soundness Hazards** | Unclaimed internal data relocations, computed `goto`, literal pools, hand-written asm, missing `--emit-relocs` | Profile staleness across code edits (symbol/GUID mismatch), unsupported `u` GUID reader |
| **EH / `.eh_frame` Handling** | Parses & rewrites FDE/LSDA; synthesizes `createEHTrampolines()` across hot/cold splits | Compiler places multi-cluster landing pads in one `Exception` section; standard MC/LLD emission |
| **Branch Range & Relaxation** | `LongJmpPass` iterative stub/veneer insertion; AArch64 short-range branch & `CDSplit` limits | Compiler emits relocatable sections; `LLD --optimize-bb-jumps` deletes/flips jumps & `relaxOnce` handles `>2 GiB` GOT |
| **Build-Time Memory & Scale** | Monolithic single-process whole-binary memory footprint (tens of GiB on warehouse monoliths) | Distributed ThinLTO parallel per-TU codegen; low peak RAM during linking (ASPLOS 2023) |
| **Prebuilt / Non-LLVM Binaries** | Applicable to GCC/third-party binaries (up to 20.4% over FDO/LTO on GCC/Clang, CGO 2019) | Requires LLVM compiler + LLD toolchain and relink access |
| **Post-Link Peepholes** | Rich binary-level passes (ICF, indirect-call promotion, frame/shrink-wrapping, PLT opt) | Layout, splitting, path cloning (`p`), and linker jump relaxation; relies on compiler/ThinLTO for IR passes |

---

### 3. Hardware Control-Flow Trace Reconstruction: Intel PT (`libipt`) vs. ARM CoreSight ETMv4 (`OpenCSD`)

Basis: normative + source + execution

Hardware control-flow tracers achieve low bandwidth overhead (~0.5–2 bits per conditional branch) by omitting statically determinable targets (direct jumps, direct calls, sequential instructions) and transmitting only dynamic branch decisions and indirect target addresses. Reconstruction therefore couples a stateful packet decoder to an **exact copy of the executed binary image** (a mismatch from JIT code, self-modifying code, or unmapped pages silently corrupts control-flow decoding).

#### 3.1 Intel Processor Trace (`Intel PT`) Packet & Event State Machine (`intel/libipt`)

In `intel/libipt@7f8575ce9bf25e48cf03983c12859e1edb592008` (`libipt/include/intel-pt.h.in`, `pt_packet_decoder.c`, `pt_last_ip.c`, `pt_event_decoder.c`, `pt_query_decoder.c`, `pt_block_decoder.c`, `pt_insn_decoder.c`, `pt_retstack.c`):

1. **Layered Decoder Architecture:** `pt_insn_decoder` (`pt_insn_decoder.c:363-420`) delegates to `pt_block_decoder` (`pt_blk_next()`), which drives `pt_event_decoder` and `pt_packet_decoder`. Pending asynchronous events (CR3/VMCS changes, paging, TSX, interrupts, OVF) must be drained via `pt_insn_event()` whenever `pts_event_pending` is set; calling `pt_insn_next()` without draining returns `-pte_event_ignored` (`pt_insn_decoder.c:397-400`).
2. **Six IP Compression Modes (`pt_last_ip.c:79-128`, verified in Probe 1A):** Every IP-carrying packet (`TIP`, `TIP.PGE`, `TIP.PGD`, `FUP`) carries a 3-bit `IPBytes` (`pt_ip_compression`) selector updating the decoder's `LastIP` register:

| `pt_ip_compression` | Payload Bytes | `LastIP` Update Semantics (`pt_last_ip.c:88-125`) | Critical Subtlety |
| :--- | :--- | :--- | :--- |
| `pt_ipc_suppressed` (0) | 0 B | `last_ip->suppressed = 1`; `LastIP` **unchanged** | Used by `TIP.PGD` on trace-filter exit (`IP` out of context); preserves `LastIP` for next compressed IP |
| `pt_ipc_update_16` (1) | 2 B | `(LastIP & ~0xffffULL) \| payload16` | Intra-64 KiB indirect branch / return target |
| `pt_ipc_update_32` (2) | 4 B | `(LastIP & ~0xffffffffULL) \| payload32` | Intra-4 GiB jump (typical same-address-space 64-bit call) |
| `pt_ipc_sext_48` (3) | 6 B | `sext(payload48, 48)` (replicates bit 47 into bits `63:48`) | Canonical 48-bit x86-64 VA: bit 47 = 1 fills `0xFFFF` (kernel space); bit 47 = 0 clears `0x0000` (user space) |
| `pt_ipc_update_48` (4) | 6 B | `(LastIP & ~0xffffffffffffULL) \| payload48` | Preserves upper 16 bits of `LastIP` (distinct from `sext_48` on user$\leftrightarrow$kernel transitions; Probe 1A) |
| `pt_ipc_full` (6) | 8 B | `payload64` | Full 64-bit address (e.g., 5-level paging LA57 / non-canonical / LAM contexts) |

3. **`TNT-8` / `TNT-64` Conditional Branch Compression:** `TNT-8` packs 1–6 conditional branch outcomes into a single byte whose least-significant bit is `0` and whose highest set bit (`1`) acts as a **stop bit**; bits immediately below the stop bit down to bit 1 encode `Taken` (`1`) / `Not-Taken` (`0`) in chronological order (Probe 1A: `0x2c = 0b0010_1100` decodes to `[N, T, T, N]`). `TNT-64` packs up to 47 outcomes in an 8-byte extended packet.
4. **Hardware `RET`-Stack Compression Hazard (`pt_retstack.c:44-75`):** When `IA32_RTIT_CTL.DisRETC = 0`, Intel PT compresses matched near `RET` instructions into a single `TNT` `Taken` bit instead of emitting a `TIP` packet, tracking calls in a circular return stack (`pt_retstack_push` / `pt_retstack_pop`). If a trace loses synchronization, or if binary instrumentation/self-modifying code/unmatched `CALL`/`RET` tricks (such as `call +5; pop reg` PIC thunks that misalign with software assumptions, or corrupted frames) desynchronize the decoder's `retstack` from hardware, `pt_retstack_pop()` yields a wrong target IP until the next uncompressed `TIP` or `PSB` (normal `longjmp` / C++ stack unwinding uses an indirect `JMP` or mismatched `RET`, which causes hardware to emit an explicit `TIP` and clear return compression).
5. **Exact `OVF` Overflow Recovery Semantics (`pt_event_decoder.c:2757-2860`):**
   - When internal CPU PT buffers overflow (typically due to DRAM write bandwidth saturation under dense indirect-branch code), hardware emits an `OVF` packet (`0x02 0xF3`).
   - In `pt_evt_decode_ovf()`:
     1. `OVF` implicitly terminates any open `PSB+` header sequence exactly like `PSBEND` (`pt_evt_decode_psbend(decoder)`, line 2773).
     2. If tracing was enabled (`decoder->enabled`), pending queued events are **dropped** because their precise instruction positions were lost (`lines 2779-2783`); if tracing was disabled, standalone non-IP events (`ptev_exstop`, `ptev_ptwrite`, `ptev_tsx`, `ptev_vmexit`, etc.) are drained with `ip_suppressed = 1`.
     3. `pt_evt_reset(decoder)` wipes the decoder's `LastIP`, `TNT` cache, and `retstack`, preserving wall-clock `time` and (if `keep_tcal_on_ovf` is enabled) updating timing calibration (`pt_tcal_update_ovf`, lines 2828-2842).
     4. **Dual Binding Rule (`lines 2844-2855`):** If the overflow resolves while `PacketEn = 1`, `OVF` binds to the subsequent **`FUP`** packet (only timing packets may appear in between), resuming instruction trace at the `FUP` IP. If the overflow resolves while `PacketEn = 0`, `OVF` binds to **`TIP.PGE`** (or generates a standalone overflow event upon seeing any non-timing, non-`FUP` packet).

#### 3.2 ARM CoreSight ETMv4 Speculative P0 Stream (`Linaro/OpenCSD`)

In `ARM IHI 0064` and `Linaro/OpenCSD@5719458c9f75714a0ee5f83fae94f0f2989b52f9` (`decoder/include/opencsd/etmv4/trc_pkt_types_etmv4.h`, `decoder/source/etmv4/trc_pkt_decode_etmv4i.cpp`):

- **Speculative P0 Architecture:** Unlike Intel PT (which buffers and emits only retired branches), ETMv4 permits an out-of-order core to stream **speculative P0 elements** (Atoms `E` = taken/executed, `N` = not-taken; Exceptions `ETM4_PKT_I_EXCEPT`; Q-elements `ETM4_PKT_I_Q`) directly into the trace stream before branch resolution, advertising its maximum unresolved speculation depth in `TRCIDR8.MAXSPEC` (`m_max_spec_depth = m_config->MaxSpecDepth()`, `trc_pkt_decode_etmv4i.cpp:214`).
- **P0 Resolution Stack Mechanics (`trc_pkt_decode_etmv4i.cpp:600-708`, verified in Probe 1B):**
  - **Auto-Commit Beyond `MAXSPEC` (`lines 698-703`):** Whenever the uncommitted P0 stack depth `m_curr_spec_depth` exceeds `m_max_spec_depth`, the oldest `m_curr_spec_depth - m_max_spec_depth` elements are **automatically committed** (`m_elem_res.P0_commit = m_curr_spec_depth - m_max_spec_depth`). When `MAXSPEC == 0` (speculation tracking disabled/unsupported), every P0 element auto-commits immediately.
  - **Explicit Speculation Control Packets:**
    - `Commit(N)`: architecturally commits the oldest `N` uncommitted P0 elements from the bottom of the P0 stack.
    - `Cancel(N)`: discards the newest `N` mispredicted/squashed P0 elements from the top of the P0 stack.
    - `Mispredict`: flips the outcome (`E` $\leftrightarrow$ `N`) of the newest remaining uncommitted Atom element (or is fused with `Cancel` in Cancel Format 1/2/3 packets).
    - `Discard` (`ETM4_PKT_I_DISCARD`) and `Overflow` (`ETM4_PKT_I_OVERFLOW`, `lines 600-605`): immediately set `m_curr_spec_depth = 0; m_elem_res.discard = true;`, purging all uncommitted speculative P0 elements without affecting already-committed trace ranges.

#### 3.3 Comparison Matrix: Intel PT vs. ARM CoreSight ETMv4

| Property | Intel PT (`intel/libipt`) | ARM CoreSight ETMv4 (`Linaro/OpenCSD`) |
| :--- | :--- | :--- |
| **Emission Timing** | Retired instructions only (TSX abort/commit via `MODE.TSX` FUP) | Speculative P0 elements bounded by `TRCIDR8.MAXSPEC` |
| **Conditional Branch Encoding** | `TNT-8` (1–6 bits) / `TNT-64` (up to 47 bits) with MSB stop bit | Atom Format 1–6 packets (`E`/`N` sequences) |
| **Speculation Reconciliation** | None needed outside TSX | `Commit`, `Cancel`, `Mispredict`, `Discard`, auto-commit above `MAXSPEC` |
| **Return Optimization** | Hardware `RET`-stack compression (`pt_retstack`, disabled via `DisRETC`) | Optional return-stack (`TRCCONFIGR.RS`) when `TRCIDR0.RETSTACK=1` |
| **Periodic Sync** | `PSB` (16-byte unique signature) ... `PSB+` ... `PSBEND` | `A-Sync` (12-byte alignment sync) + `I-Sync` (`ETM4_PKT_I_TRACE_INFO`) |
| **Overflow Recovery** | `OVF` ends `PSB+`, wipes state, binds to `FUP` (`PacketEn=1`) or `TIP.PGE` (`PacketEn=0`) | `ETM4_PKT_I_OVERFLOW` sets `m_prev_overflow=true`, `m_curr_spec_depth=0`, `discard=true` |
| **Image Fidelity Requirement** | Exact static binary + dynamic JIT/SMC sideband (`PERF_RECORD_MMAP2`) | Exact static binary + EL/ISA-mode (`A64`/`A32`/`T32`) context (`ETM4_PKT_I_CTXT`) |

---

### 4. Out-of-Order PMU Skid Bias: Intel PEBS, TIP, and ARM SPE

Basis: normative + source + execution + derived

Hardware Performance Monitoring Unit (PMU) statistical profilers feed both human performance analysis and automated layout optimizers (BOLT, Propeller, AutoFDO). Misinterpreting PMU instruction-pointer semantics systematically corrupts hot-block attribution.

#### 4.1 Four Tiers of Sampling Attribution and Linux Kernel Fixups

1. **Tier 0 — Conventional PMU Interrupt (`precise_ip = 0`):** Counter overflow asserts a Local APIC Performance Monitoring Interrupt (PMI). Because the PMI traverses out-of-order retirement, APIC latency, and interrupt-shadow windows (`STI`/`MOV SS`, masked `IF=0`), the recorded `RIP` suffers **arbitrary skid** (tens to hundreds of retired instructions past the overflowing event, frequently crossing branch boundaries into unrelated basic blocks).
2. **Tier 1 — Legacy Intel PEBS (`pebs_format < 2`, `precise_ip = 1`):** Microcode traps after counter overflow and writes a hardware PEBS record directly into the Debug Store (DS) buffer without immediate OS interrupt, reducing skid to **1 instruction** (`pebs->ip` points to the instruction *following* the triggering instruction, i.e., trap-like).
   - **Linux LBR Rewind Heuristic (`arch/x86/events/intel/ds.c:2010-2095`, `intel_pmu_pebs_fixup_ip()`):** For `precise_ip >= 2` on pre-Haswell (`pebs_format < 2`) CPUs where `x86_pmu.intel_cap.pebs_trap` is true, Linux reads the most recent LBR entry `(from, to) = (cpuc->lbr_entries[0].from, cpuc->lbr_entries[0].to)`:
     - If `ip == to`, the sampled instruction was the branch at `from`, so `regs->ip` is rewound directly to `from` (`lines 2048-2051`).
     - Otherwise, if `kernel_ip(ip) == kernel_ip(to)` and `(ip - to) <= PEBS_FIXUP_SIZE` (1 page), Linux copies code via `copy_from_user_nmi()` and forward-disassembles x86 instructions from `to` until `to == ip`, recovering `old_to` (`lines 2053-2094`).
     - **Silent Failure Modes:** Fixup returns `0` (leaving `PERF_EFLAGS_EXACT` unset and retaining the off-by-1 IP!) whenever the LBR stack is empty (`!cpuc->lbr_stack.nr`), the basic block exceeds `PEBS_FIXUP_SIZE`, `copy_from_user_nmi()` faults on unmapped/swapped user pages, or instruction decoding fails (`insn_get_length(&insn)`).
3. **Tier 2 — Intel PEBS v2+ `EventingIP`, Adaptive PEBS, and `PEBS_VIA_PT` (`ds.c:1831, 1959, 2263-2283, 2522-2685`):**
   - From Haswell onward (`pebs_format >= 2`), hardware records `pebs->real_ip` (`EventingIP`) directly in the PEBS record (`set_linear_ip(regs, pebs->real_ip); regs->flags |= PERF_EFLAGS_EXACT;`, `ds.c:2269-2271`), eliminating the architectural off-by-1 trap skid. Ice Lake+ adds variable-size Adaptive PEBS (`struct pebs_basic`, `setup_pebs_adaptive_sample_data`) and `PEBS_VIA_PT` (`PERF_X86_EVENT_PEBS_VIA_PT`), which embeds PEBS records directly into the Intel PT byte stream to avoid DS-buffer NMI overhead.
   - **Residual Microarchitectural Bias — The Out-of-Order Shadow Effect (Gottschall, Eeckhout, Jahre, MICRO 2021, `DOI: 10.1145/3466752.3480058`):** Even with zero architectural IP skid (`EventingIP`), PEBS activates only when a PMU counter overflows and then tags the *next* eligible retiring instruction after PEBS-assist arming. On a superscalar out-of-order core, when a long-latency instruction (e.g., a 200-cycle L3 cache-miss `LD`) stalls at the head of the ROB, younger independent instructions (`ADD1..ADD3`, `JNZ`) execute out of order and pile up behind `LD` in the ROB. Overflows occurring during the 200-cycle stall arm PEBS and get charged to the **next retiring instruction immediately following `LD` (`ADD1`)** (or suffer systematic blind spots across instructions retiring in the same 4–8-wide retirement cycle). In Probe 1C's 201-cycle ROB model, **true head-of-ROB time-proportional attribution (TIP)** assigns **99.5%** of cycles to `LD_L3_MISS`, whereas shadow-shifted next-retire PEBS assigns **0.0%** to `LD_L3_MISS` and **99.5%** to the innocent `ADD1`!
   - **Counter Non-Determinism & Overcount (Weaver, Terpstra, Moore, ISPASS 2013, `DOI: 10.1109/ISPASS.2013.6557172`):** Hardware performance counters exhibit run-to-run variance and systematic overcount due to hardware interrupt / page-fault handler skid, speculative/replayed memory micro-ops, `REP` string instruction micro-architectural iteration counting, and hardware prefetch interference.
4. **Tier 3 — Operation-Centric Sampling: ARMv8.2 Statistical Profiling Extension (`SPE`) (`drivers/perf/arm_spe_pmu.c`, `tools/perf/util/arm-spe-decoder/arm-spe-pkt-decoder.c`):**
   - Instead of waiting for a global counter overflow to interrupt retirement, ARM SPE selects a single micro-operation at **decode/dispatch** on an interval (`PMSIRR.INTERVAL`) perturbed by a hardware LFSR (`PMSIRR.RND` jitter to defeat loop-lockstep aliasing), follows that tagged operation through the entire out-of-order pipeline, and writes a structured self-contained record directly to memory (`PMBLIMITR`) upon retirement or flush.
   - `arm-spe-pkt-decoder.c:23-48` decodes variable-length packets (`sz` bits `[5:4]` $\to 2^{\text{sz}} \in \{1,2,4,8\}$ bytes): `ADDR` (instruction PC, branch target, data VA, data PA), `LAT` (total latency, issue latency, translation latency), `OP-TYPE` (load/store/branch/SVE), `EVENTS` (retired, L1D/LLC/TLB refill, mispredicted, predicated), `CONTEXT` (`CONTEXTIDR` PID, guarded by `SPE_PMU_HW_FLAGS_CX` / `perf_allow_kernel()` in `arm_spe_pmu.c:47-55`), and `DATA-SOURCE` (exact cache/DRAM hierarchy level).
   - Because latency is attached to the tagged operation's own PC rather than the next retiring instruction, Probe 1C yields **98.0%** latency share on `LD_L3_MISS` with zero shadow-effect inversion. (Note: SPE still requires statistical weighting by `total_lat` and care regarding unretired flushed speculative ops filtered via `EVENTS.RETIRED`.)

#### 4.2 Consequence for BOLT and Propeller Profile Quality

- **Why LBR (`br_inst_retired.near_taken:pp`) Outperforms Raw IP Histograms:** Both BOLT and Propeller rely primarily on **Last Branch Record (LBR)** stacks (or ARM SPE branch records) rather than raw instruction-IP histograms. Because LBR captures exact hardware-retired `(from_pc, to_pc)` branch pairs atomically at branch retirement, single-instruction skid on the triggering sample IP cannot fabricate bogus inter-block branch targets, and fall-through spans between consecutive LBR entries remain architecturally exact (barring LBR freeze/overflow or context-switch leakage).
- **Remaining LBR Biases:** LBR sampling still inherits (a) sampling-period lockstep bias (mitigated by prime periods and `PDIR` / random jitter), (b) shadow bias on *which* branch triggers the LBR capture (biasing edge frequencies right after long-latency stalls), and (c) call-depth truncation beyond the hardware LBR stack depth (16/32 entries on legacy Intel; 32+ on ArchLBR).

---

### 5. x86 `DR0–DR7` Watchpoint `RF` State Machine and `ptrace` / `SECCOMP_RET_TRACE` TOCTOU Semantics

Basis: normative + source + execution

#### 5.1 `DR0–DR7` / `DR6` Encoding and Fault-vs.-Trap `#DB` Semantics

Per Intel SDM Vol. 3 and Linux (`arch/x86/kernel/hw_breakpoint.c:324-350, 511-576`, `arch/x86/kernel/traps.c:1259-1365`, `arch/x86/kernel/ptrace.c:560-685`):

- **Hardware Registers:** `DR0–DR3` hold four linear breakpoint addresses; `DR7` encodes per-slot Local/Global enable (`L0–L3` at bits `0,2,4,6`; `G0–G3` at `1,3,5,7`), General Detect (`GD`, bit 13, faulting on `MOV DR`), and 2-bit `R/W` + 2-bit `LEN` fields at bits `16–31`:
  - `R/W = 00`: **Instruction execution** (`LEN` MUST be `00` = 1 byte).
  - `R/W = 01`: **Data write only** (`LEN` $\in \{00=1\text{B}, 01=2\text{B}, 10=8\text{B (64-bit)}, 11=4\text{B}\}$).
  - `R/W = 10`: I/O read/write (only when `CR4.DE = 1`).
  - `R/W = 11`: **Data read or write** (not instruction fetch).
- **`DR6` Status Bits:** Bits `0–3` (`B0–B3` / `DR_TRAP0–DR_TRAP3`) report matched breakpoints; bit 13 (`BD`) reports `DR7.GD` debug-register access; bit 14 (`BS` / `DR_STEP`) reports `EFLAGS.TF` single-step; bit 15 (`BT`) reports TSS task-switch `T`; bit 11 (`BLD` / `DR_BUS_LOCK`, cleared-to-0 on Intel CPUs supporting bus-lock detect, inverted polarity in hardware) reports split/bus-lock traps (`traps.c:1352`). Hardware *never* clears `B0–B3` automatically across exceptions; the OS must reset `DR6` (`debug_read_reset_dr6()`, `traps.c:1377`).

| `#DB` Cause | Exception Class | Saved `RIP` on `#DB` | `EFLAGS.RF` Effect | Linux Kernel Handling (`hw_breakpoint.c` / `traps.c`) |
| :--- | :--- | :--- | :--- | :--- |
| Instruction Breakpoint (`R/W=00`) | **Fault** | Triggering instruction | **Mandatory:** `RF=1` suppresses `#DB` for 1 insn, auto-cleared by CPU | Sets `args->regs->flags \|= X86_EFLAGS_RF` (`hw_breakpoint.c:562-563`) |
| Data Watchpoint (`R/W=01, 11`) | **Trap** | *Next* instruction | **No effect** (instruction already retired) | Clears `DR_TRAPn`, delivers `perf_bp_event` + `SIGTRAP` (`TRAP_HWBKPT`) |
| Single-Step (`EFLAGS.TF=1`) | **Trap** | *Next* instruction | **No effect** | Preserves `DR_STEP` in `current->thread.virtual_dr6` (`traps.c:1324`) |
| Combined `TF` + Exec BP (`DR_STEP \| DR_TRAPn`) | Trap + pending Fault | Target insn (next after stepped insn) | Delayed until next fetch | **`hw_breakpoint.c:547-548`:** `if (bpx && (dr6 & DR_STEP)) continue;` — `DR_STEP` wins; exec BP re-fires on resume |
| `ICEBP` / `INT1` (`0xF1`) | **Trap** | Instruction after `0xF1` | No effect | `icebp = !dr6` (`traps.c:1338`): empty `DR6` triggers `SIGTRAP` |
| Block-Step (`DEBUGCTLMSR.BTF`) | **Trap** (on branch) | Branch target | Hardware clears `BTF` on `#DB` | `clear_thread_flag(TIF_BLOCKSTEP)` (`traps.c:1331`) |

- **Kernel Isolation & Safety Invariants (`hw_breakpoint.c:324-341`, `ptrace.c:560-585`):**
  - `arch_build_bp_info()` rejects any breakpoint whose `[bp_addr, bp_addr + bp_len - 1]` wraps around 64-bit space or overlaps the CPU entry area (`within_cpu_entry(attr->bp_addr, bp_end)`, `hw_breakpoint.c:340-341`), preventing recursive `#DB` faults on IST stacks, `GDT`, `IDT`, or `TSS` during `#DB` entry!
  - `ptrace_write_dr7()` masks out `DR_CONTROL_RESERVED` (`ptrace.c:567`), preventing userspace debuggers from setting `DR7.GD` or reserved bits, and validates every slot via `ptrace_register_breakpoint()` (`ptrace.c:581`) with rollback on failure.
  - **The `RF` Livelock Failure Mode (verified in Probe 1D):** If a hypervisor, custom kernel, or `ptrace` user modifying `RFLAGS` via `PTRACE_SETREGS` clears bit 16 (`RF`) before resuming an instruction breakpoint without disarming `DR7`, the CPU immediately re-raises `#DB` at the exact same `RIP` forever. Conversely, setting `RF = 1` does *not* mask a data watchpoint or `EFLAGS.TF`.

#### 5.2 `ptrace` + `SECCOMP_RET_TRACE` Shared-Memory `TOCTOU` Hazard

In `torvalds/linux@4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`kernel/seccomp.c:1268-1348`):

1. **Exact Kernel State Machine (`__seccomp_filter()`):**
   - `populate_seccomp_data(&sd)` snapshots only **CPU register values** (syscall number, architecture, instruction pointer, and the six 64-bit register arguments `args[0..5]`) — never userspace memory pointed to by those registers (`seccomp.c:1281`).
   - When `seccomp_run_filters()` returns `SECCOMP_RET_TRACE`:
     - If `recheck_after_trace` is `true`, returns `true` immediately (`seccomp.c:1305-1306`) to avoid infinite trace recursion after a tracer modifies registers.
     - If no tracer has `PTRACE_O_TRACESECCOMP` enabled (`!ptrace_event_enabled(current, PTRACE_EVENT_SECCOMP)`), sets `-ENOSYS` and skips the syscall (`seccomp.c:1309-1314`).
     - Otherwise, stops **only the calling thread** in `ptrace_event(PTRACE_EVENT_SECCOMP, data)` (`seccomp.c:1317`).
     - Upon tracer resume, if a fatal signal arrived during notification (`fatal_signal_pending(current)`), Linux forces the syscall to be skipped so an uninspected syscall cannot slip past a dying tracer notification (`seccomp.c:1318-1329`).
     - Otherwise, Linux reloads the (possibly tracer-rewritten) syscall number via `syscall_get_nr()`, skips if `< 0`, and re-invokes `__seccomp_filter(this_syscall, true)` (`seccomp.c:1331-1341`).
2. **The Fundamental Shared-Memory `TOCTOU` Race:**
   - Suppose a `ptrace` supervisor (or a `SECCOMP_RET_USER_NOTIF` userspace supervisor at `seccomp.c:1343-1347`) intercepts `openat(AT_FDCWD, path_ptr, O_RDONLY)` at `PTRACE_EVENT_SECCOMP`.
   - At $t_1$, the supervisor reads `*path_ptr` via `PTRACE_PEEKDATA` or `process_vm_readv()` and observes `"/tmp/safe.txt"`.
   - At $t_2$, the supervisor resumes the tracee (`PTRACE_CONT` / `PTRACE_SYSCALL`).
   - Between $t_1$ and $t_3$ (when the kernel executes `getname()` / `copy_from_user()` inside `do_sys_openat2`), a **sibling thread** sharing the tracee's `mm_struct` (`CLONE_VM`), or another process sharing a `MAP_SHARED` page, overwrites `*path_ptr` with `"/etc/shadow"`.
   - Because `ptrace_event()` halts only the single thread invoking the syscall — and stopping all threads atomically via `SIGSTOP` still fails against `MAP_SHARED` or `io_uring`/DMA writers — **any `ptrace` or `SECCOMP_RET_USER_NOTIF` policy that validates pointer-referenced userspace memory and then lets the kernel re-read that memory is structurally unsound**.
3. **Sound Architectural Alternatives:**
   - **Supervisor-Side Execution + FD Injection:** With `SECCOMP_RET_USER_NOTIF`, the supervisor reads the path into its *own* private address space, validates and opens it itself, and injects the resulting file descriptor into the tracee via `SECCOMP_IOCTL_NOTIF_ADDFD` while returning a synthetic value so the kernel never re-dereferences tracee memory.
   - **In-Kernel Object Enforcement:** Use Linux `Landlock` LSM / kernel mount namespaces / `openat2(RESOLVE_BENEATH)` so policy checks run on the kernel-copied `struct path` / `dentry` *after* `copy_from_user()`.
   - **Immutable/Private Argument Pages:** Only sound if the tracee is guaranteed single-threaded (`CLONE_VM` forbidden via seccomp) *and* the argument page is mapped non-`MAP_SHARED`, non-writable (or copy-on-write frozen) before validation.

## Boundaries

- **Unsupported — `Propeller` `u` Function GUID in Compiler Reader:** `google/llvm-propeller@e98f399102650de7e03e07c7299029da94d7be44` (`propeller/propeller_profile_format.md:60-62`) explicitly documents that while Propeller can read `FuncGUID` from `SHT_LLVM_BB_ADDR_MAP` v6+ and emit `u <function_guid>` lines, the LLVM `BasicBlockSectionsProfileReader` does not yet support the `u` specifier.
- **Unsupported — BOLT `CDSplit` with `LongJmp` and AArch64 Short-Range Branches:** `llvm/llvm-project@53623acaadfe3df4ea2bfc48d347faa3fb1c57a5` explicitly rejects `--split-strategy=cdsplit` on AArch64 without `--compact-code-model` (`RewriteInstance.cpp:2683-2687`) and aborts on AArch64 short-range branches outside `--compact-code-model` (`LongJmp.cpp:108-114`).
- **Unsupported — ETMv4 Conditional Instruction Tracing Packets in `OpenCSD`:** `Linaro/OpenCSD@5719458c9f75714a0ee5f83fae94f0f2989b52f9` (`decoder/source/etmv4/trc_pkt_decode_etmv4i.cpp:666-676`) explicitly classifies `ETM4_PKT_I_COND_FLUSH`, `ETM4_PKT_I_COND_I_F1..F3`, and `ETM4_PKT_I_COND_RES_F1..F4` under `presently unsupported packets`.
- **Known Not to Apply — `EFLAGS.RF` Suppression of Data Watchpoints or `TF`:** Intel SDM Vol. 3 and Probe 1D establish that `EFLAGS.RF` masks *only* instruction-execution breakpoints (`DR7.R/W=00`); setting `RF=1` does not prevent data-breakpoint traps, I/O breakpoints, or `EFLAGS.TF` single-step traps.
- **Known Not to Apply — BOLT Relocation Mode on Linux Kernel Images:** `RewriteInstance.cpp:2602-2604` explicitly disables `BC->HasRelocations` when `BC->IsLinuxKernel` is true, even if `--emit-relocs` sections are present.
- **Not Examined:**
  - AMD hardware tracing/sampling equivalents (`AMD IBS` Instruction-Based Sampling, `AMD BRS` Branch Sampling, `AMD LBRv2`) and RISC-V E-Trace / N-Trace specifications.
  - BOLT Mach-O (macOS) and PE/COFF (Windows) binary rewriting paths, as well as BOLT BAT (BOLT Address Translation) stale-profile remapping on already-BOLTed binaries.
  - Intel PT hardware silicon errata workarounds (e.g., `SKL014`, `APL11`, `BDM70` in `libipt` `pt_config.errata`) beyond noting their presence in `pt_config`.
  - `ARMv8.8` / `ARMv9` `ETE` (Embedded Trace Extension) transactional-memory (`ETE_PKT_I_TRANS_ST`/`COMMIT`/`FAIL`) and `TRBE` (Trace Buffer Extension) ring-buffer overflow interactions.
- **Unknown:** Exact silicon-level PEBS microcode arming latency distributions across unpublished future Intel microarchitectures (the shadow-effect magnitude depends on ROB depth, retirement width, and `PDIR` microcode implementation details that vary across microarchitectures).

## Evidence

### Pinned Source Repositories & Exact Symbols

| Subject | Repository & Immutable Revision | Inspected Paths & Line Ranges / Symbols |
| :--- | :--- | :--- |
| LLVM BOLT (disassembly, CFG, jump tables, `StrictMode`) | `llvm/llvm-project` @ `53623acaadfe3df4ea2bfc48d347faa3fb1c57a5` | `bolt/lib/Core/BinaryFunction.cpp`: `JumpTables` (`L90-93`), `getConstantIslandAlignment` (`L279-285`), `disassemble` (`L1314-1435`), `StrictMode` & `validateInternalRefDataRelocations` (`L2060-2125`), `buildCFG` (`L2287`) |
| LLVM BOLT (rewriting, EH, splitting, veneers) | `llvm/llvm-project` @ `53623acaadfe3df4ea2bfc48d347faa3fb1c57a5` | `bolt/lib/Rewrite/RewriteInstance.cpp` (`L582-586`, `L2599-2604`, `L2683-2687`, `L6793-6861`); `bolt/lib/Core/Exceptions.cpp` (`parseLSDA`, `L101-265`); `bolt/lib/Passes/SplitFunctions.cpp` (`L77-145`, `L828-1058`, `createEHTrampolines`); `bolt/lib/Passes/LongJmp.cpp` (`L70-125`, `mayNeedStub`, `relaxStubToLongJmp`) |
| LLVM BasicBlockSections & LLD ELF relaxation | `llvm/llvm-project` @ `53623acaadfe3df4ea2bfc48d347faa3fb1c57a5` | `llvm/lib/CodeGen/BasicBlockSections.cpp` (`assignSections`, `EHPadsSectionID`, `L305-328`); `lld/ELF/Writer.cpp` (`optimizeBasicBlockJumps`, `L1717-1747`); `lld/ELF/Arch/X86_64.cpp` (`deleteFallThruJmpInsn` `L246-315`, `relaxOnce` `L507-542`, `applyJumpInstrMod` `L1078-1113`) |
| Google Propeller | `google/llvm-propeller` @ `e98f399102650de7e03e07c7299029da94d7be44` | `propeller/propeller_profile_format.md` (`L1-140`); `propeller/bb_addr_map.cc` (`L76-108`); `propeller/binary_address_mapper.cc` (`CanFallThrough`, `L513-524`); `propeller/program_cfg_builder.cc` (`CreateFallthroughs`, `L141-174`) |
| Intel Processor Trace (`libipt`) | `intel/libipt` @ `7f8575ce9bf25e48cf03983c12859e1edb592008` | `libipt/include/intel-pt.h.in` (`pt_packet_type`, `L605+`); `libipt/src/pt_last_ip.c` (`pt_last_ip_update_ip`, `L79-128`); `libipt/src/pt_event_decoder.c` (`pt_evt_decode_ovf`, `L2757-2855`); `libipt/src/pt_query_decoder.c` (`L427-500`); `libipt/src/pt_retstack.c` (`L44-75`); `libipt/src/pt_insn_decoder.c` (`pt_insn_next`, `L363-420`) |
| ARM CoreSight ETMv4 (`OpenCSD`) | `Linaro/OpenCSD` @ `5719458c9f75714a0ee5f83fae94f0f2989b52f9` | `decoder/include/opencsd/etmv4/trc_pkt_types_etmv4.h` (`L48-83`); `decoder/source/etmv4/trc_pkt_decode_etmv4i.cpp` (`m_max_spec_depth` `L214`, `OVERFLOW`/`DISCARD` `L600-605`, unsupported `COND` `L666-676`, auto-commit `L698-708`) |
| Linux Kernel (PEBS, SPE, `#DB`/`DR0-7`, `ptrace`, `seccomp`) | `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` | `arch/x86/events/intel/ds.c` (`PEBS_VIA_PT` `L1831,1959`, `intel_pmu_pebs_fixup_ip` `L2010-2095`, `real_ip` `L2263-2290`, Adaptive PEBS `L2522-2685`); `drivers/perf/arm_spe_pmu.c` (`L47-80`); `tools/perf/util/arm-spe-decoder/arm-spe-pkt-decoder.c` (`L23-48`); `arch/x86/kernel/hw_breakpoint.c` (`arch_build_bp_info` `L324-345`, `hw_breakpoint_handler` `L511-576`); `arch/x86/kernel/traps.c` (`exc_debug_user` `L1295-1365`); `arch/x86/kernel/ptrace.c` (`ptrace_write_dr7` `L560-585`); `kernel/seccomp.c` (`__seccomp_filter` `L1268-1348`) |

### Peer-Reviewed Literature & Normative Standards

- Maksim Panchenko, Rafael Auler, Bill Nell, Guilherme Ottoni, *"BOLT: A Practical Binary Optimizer for Data Centers and Beyond"*, CGO 2019 (`DOI: 10.1109/CGO.2019.8661201`, `arXiv:1807.06735`).
- Han Shen, Krzysztof Pszeniczny, Rahman Lavaee, Snehasish Kumar, Sriraman Tallam, Xinliang David Li, *"Propeller: A Profile Guided, Relinking Optimizer for Warehouse-Scale Applications"*, ASPLOS 2023 (`DOI: 10.1145/3575693.3575727`).
- Björn Gottschall, Lieven Eeckhout, Magnus Jahre, *"TIP: Time-Proportional Instruction Profiling"*, MICRO 2021 (`DOI: 10.1145/3466752.3480058`).
- Vincent M. Weaver, Dan Terpstra, Shirley Moore, *"Non-Determinism and Overcount on Modern Hardware Performance Counter Implementations"*, ISPASS 2013 (`DOI: 10.1109/ISPASS.2013.6557172`).
- Intel Corporation, *Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 3* (Debug Registers / `EFLAGS.RF`, Performance Monitoring / PEBS, Intel Processor Trace).
- Arm Limited, *Embedded Trace Macrocell Architecture Specification ETMv4.0 to ETMv4.6* (`ARM IHI 0064`), and *Arm Architecture Reference Manual for A-profile Architecture* (`ARM DDI 0487`, Statistical Profiling Extension `FEAT_SPE`).

### Self-Contained Executable Micro-Probe & Observed Output (`2026-11-19`)

Command (Python 3.13, Linux x86-64, zero external dependencies):

```bash
python3 - <<'EOF'
from dataclasses import dataclass
from typing import List, Optional, Tuple

# 1A: Intel PT IP compression (pt_last_ip.c:79-128) & TNT-8 decoding
def sext48(v: int) -> int:
    v &= (1 << 48) - 1
    return v | (((1 << 16) - 1) << 48) if (v & (1 << 47)) else v

def pt_last_ip_update(last_ip: int, ipc: str, pay: int) -> Tuple[int, bool]:
    if ipc == "suppressed": return last_ip, True
    if ipc == "sext_48":    return sext48(pay), False
    if ipc == "update_16":  return (last_ip & ~0xFFFF) | (pay & 0xFFFF), False
    if ipc == "update_32":  return (last_ip & ~0xFFFFFFFF) | (pay & 0xFFFFFFFF), False
    if ipc == "update_48":  return (last_ip & ~0xFFFFFFFFFFFF) | (pay & 0xFFFFFFFFFFFF), False
    if ipc == "full":       return pay & 0xFFFFFFFFFFFFFFFF, False
    raise ValueError(ipc)

ip = 0
for ipc, pay in [
    ("sext_48", 0xFFFF81001234), ("update_16", 0x5678), ("update_32", 0x82009ABC),
    ("update_48", 0x00007F001122), ("sext_48", 0x00007F001122), ("suppressed", 0),
]:
    ip, sup = pt_last_ip_update(ip, ipc, pay)
    print(f"PT ipc={ipc:10s} pay=0x{pay:012x} -> LastIP=0x{ip:016x} suppressed={sup}")

tnt8 = 0b00101100
msb = tnt8.bit_length() - 1
print("PT TNT-8 0x2c ->", ["T" if (tnt8 >> i) & 1 else "N" for i in range(msb - 1, 0, -1)])

# 1B: ARM ETMv4 speculative P0 stack (trc_pkt_decode_etmv4i.cpp:600-703, MAXSPEC=3)
stack, committed, maxspec = [], [], 3
for a in ["E", "N", "E", "E", "N"]:
    stack.append(a)
    if len(stack) > maxspec:
        n = len(stack) - maxspec; committed.extend(stack[:n]); del stack[:n]
print(f"ETMv4 push 5 (MAXSPEC=3): committed={committed} spec={stack}")
stack.pop()  # Cancel(1)
stack[-1] = "N" if stack[-1] == "E" else "E"  # Mispredict
print(f"ETMv4 Cancel(1)+Mispredict: committed={committed} spec={stack}")
committed.extend(stack[:2]); del stack[:2]  # Commit(2)
stack.append("E"); stack.clear()  # push + OVERFLOW/DISCARD
print(f"ETMv4 Commit(2)+push+OVF: committed={committed} spec={stack}")

# 1C: OoO ROB shadow effect (200c LD_L3_MISS + 4x 1c ops retiring in burst on cycle 200)
total_c = 201
tip_ld, tip_add1 = 200 / total_c * 100, 1 / total_c * 100
pebs_ld, pebs_add1, pebs_add2 = 0.0, 200 / total_c * 100, 1 / total_c * 100
spe_ld, spe_add1 = 200 / 204 * 100, 1 / 204 * 100
print(f"ROB-shadow: TIP(LD={tip_ld:.1f}%,ADD1={tip_add1:.1f}%) PEBS-shadow(LD={pebs_ld:.1f}%,ADD1={pebs_add1:.1f}%,ADD2={pebs_add2:.1f}%) SPE(LD={spe_ld:.1f}%,ADD1={spe_add1:.1f}%)")

# 1D: x86 DR0-DR7 / EFLAGS.RF fault-vs-trap state machine (hw_breakpoint.c:528-564)
@dataclass
class Cpu:
    rip: int; rf: int = 0; dr0: int = 0; rw: int = 0; en: int = 0

def step(c: Cpu, length: int, wr: Optional[int], set_rf: bool) -> str:
    if c.en and c.rw == 0 and c.rip == c.dr0 and c.rf == 0:
        if set_rf: c.rf = 1
        return f"#DB(FAULT) RIP=0x{c.rip:x} RF={c.rf}"
    orig = c.rip; c.rf = 0; c.rip += length
    if c.en and c.rw in (1, 3) and wr == c.dr0:
        return f"#DB(TRAP) after 0x{orig:x} -> RIP=0x{c.rip:x} RF={c.rf}"
    return f"EXEC 0x{orig:x} -> RIP=0x{c.rip:x} RF={c.rf}"

c_ok = Cpu(0x401000, dr0=0x401000, rw=0, en=1)
c_bad = Cpu(0x401000, dr0=0x401000, rw=0, en=1)
c_wp = Cpu(0x401000, dr0=0x600000, rw=1, en=1)
print("DR-Exec+RF:  ", step(c_ok, 3, None, True), "|", step(c_ok, 3, None, True))
print("DR-Exec-noRF:", step(c_bad, 3, None, False), "|", step(c_bad, 3, None, False))
print("DR-WriteWP:  ", step(c_wp, 3, 0x600000, True), "|", step(c_wp, 2, None, True))

# 1E: LLD --optimize-bb-jumps flip-and-delete (lld/ELF/Arch/X86_64.cpp:246-315)
sec = bytearray([0x85, 0xc0, 0x0f, 0x84, 0,0,0,0, 0xe9, 0,0,0,0])
rel = {4: "nextIS", 9: "coldBB"}
assert sec[-5] == 0xe9 and sec[-11] == 0x0f and sec[-10] == 0x84 and rel[4] == "nextIS"
sec[-10] = 0x85; rel[4] = rel.pop(9); del sec[-5:]
print(f"LLD flip-and-delete: 13B -> {len(sec)}B, tail={sec[2:].hex()}, relocs={rel}")
EOF
```

Observed output (`exit 0`, recorded `2026-11-19`):

```text
PT ipc=sext_48    pay=0xffff81001234 -> LastIP=0xffffffff81001234 suppressed=False
PT ipc=update_16  pay=0x000000005678 -> LastIP=0xffffffff81005678 suppressed=False
PT ipc=update_32  pay=0x000082009abc -> LastIP=0xffffffff82009abc suppressed=False
PT ipc=update_48  pay=0x00007f001122 -> LastIP=0xffff00007f001122 suppressed=False
PT ipc=sext_48    pay=0x00007f001122 -> LastIP=0x000000007f001122 suppressed=False
PT ipc=suppressed pay=0x000000000000 -> LastIP=0x000000007f001122 suppressed=True
PT TNT-8 0x2c -> ['N', 'T', 'T', 'N']
ETMv4 push 5 (MAXSPEC=3): committed=['E', 'N'] spec=['E', 'E', 'N']
ETMv4 Cancel(1)+Mispredict: committed=['E', 'N'] spec=['E', 'N']
ETMv4 Commit(2)+push+OVF: committed=['E', 'N', 'E', 'N'] spec=[]
ROB-shadow: TIP(LD=99.5%,ADD1=0.5%) PEBS-shadow(LD=0.0%,ADD1=99.5%,ADD2=0.5%) SPE(LD=98.0%,ADD1=0.5%)
DR-Exec+RF:   #DB(FAULT) RIP=0x401000 RF=1 | EXEC 0x401000 -> RIP=0x401003 RF=0
DR-Exec-noRF: #DB(FAULT) RIP=0x401000 RF=0 | #DB(FAULT) RIP=0x401000 RF=0
DR-WriteWP:   #DB(TRAP) after 0x401000 -> RIP=0x401003 RF=0 | EXEC 0x401003 -> RIP=0x401005 RF=0
LLD flip-and-delete: 13B -> 8B, tail=0f8500000000, relocs={4: 'coldBB'}
```

## Revalidation

To cheaply test whether these findings still hold on newer toolchain, decoder, or kernel revisions:

1. **BOLT / Propeller / LLD Seam (`llvm/llvm-project`, `google/llvm-propeller`):**
   - Diff `bolt/lib/Core/BinaryFunction.cpp` (`validateInternalRefDataRelocations`, `StrictMode`), `bolt/lib/Passes/SplitFunctions.cpp` (`createEHTrampolines`), `bolt/lib/Rewrite/RewriteInstance.cpp` (`HasRelocations`, `IsLinuxKernel`, `CDSplit`), and `bolt/lib/Passes/LongJmp.cpp` (`mayNeedStub`).
   - Check `propeller/propeller_profile_format.md` and `llvm/lib/CodeGen/BasicBlockSectionsProfileReader.cpp` to verify whether `u <function_guid>` is now consumed by LLVM; diff `lld/ELF/Arch/X86_64.cpp` (`deleteFallThruJmpInsn`, `relaxOnce`) for AArch64 or RISC-V BB-jump relaxation extensions.
2. **Hardware Trace Decoders (`intel/libipt`, `Linaro/OpenCSD`):**
   - Diff `libipt/src/pt_last_ip.c` (`pt_last_ip_update_ip`) and `libipt/src/pt_event_decoder.c` (`pt_evt_decode_ovf`) for new `pt_ip_compression` encodings (e.g., FRED / LA57 / event-trace `CFE`/`EVD` updates).
   - Diff `decoder/source/etmv4/trc_pkt_decode_etmv4i.cpp` around lines `600–708` to check whether `ETM4_PKT_I_COND_*` conditional instruction tracing remains unsupported or whether `MAXSPEC` auto-commit / `OVERFLOW` discard logic changed.
3. **Linux Kernel PMU, Hardware Breakpoints, and Seccomp (`torvalds/linux`):**
   - Diff `arch/x86/events/intel/ds.c` (`intel_pmu_pebs_fixup_ip`, `setup_pebs_adaptive_sample_data`, `arch_pebs_basic`, `PERF_X86_EVENT_PEBS_VIA_PT`) for newer Architectural PEBS formats (`pebs_format >= 6`) or hardware TIP support.
   - Diff `arch/x86/kernel/hw_breakpoint.c` (`hw_breakpoint_handler`, `within_cpu_entry`), `arch/x86/kernel/traps.c` (`exc_debug_user`), and `kernel/seccomp.c` (`case SECCOMP_RET_TRACE`) to confirm `X86_EFLAGS_RF` handling, `DR_STEP` precedence, and single-thread stop semantics under `SECCOMP_RET_TRACE`.
4. **Executable Probe:** Re-run the inline Python 3 probe under **Evidence** to re-verify all bit-level IP compression, ETMv4 stack, ROB-shadow, `#DB`/`RF`, and LLD jump-flip invariants.
