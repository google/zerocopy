# Verified SSA Register Allocation, Coalescing, and Sub-Register Lane Liveness

## Summary

No deployed or mechanized compiler currently unifies SSA chordal register allocation, move coalescing, live-range splitting, rematerialization, and overlapping sub-register bit-lane liveness inside a theorem-prover kernel. Primary-source analysis and live execution across `AbsInt/CompCert`, `bytecodealliance/regalloc2`, `CakeML/cakeml`, `llvm/llvm-project`, `rustc` (`1.98.0-nightly`, bundled `LLVM 22.1.6`), and `Lean 4` (`v4.34.1`) establish five core results for a drop-in verified `rustc` backend targeting `x86_64`, `aarch64`, and `i686`:

1. **Bibliographic conflation and mechanized allocator scope:** No paper titled *"Verified SSA-Based Register Allocation"* by *"Buchwald-Lohr-Zwinkau"* exists at CC 2016. Buchwald, Lohner, and Ullrich (CC 2016, `10.1145/2892208.2892211`) mechanized Braun et al.'s **CFG-to-SSA construction** in Isabelle/HOL (`Formal_SSA`), whereas Buchwald, Zwinkau, and Bersch (CC 2011, `10.1007/978-3-642-19861-8_4`) implemented an **unverified** C allocator in libFirm extending Hack-Grund-Goos (CC 2006) and Braun-Hack (CC 2009). Existing mechanized allocators and validators—CompCert (`Allocation.v` / `Allocproof.v`), CompCertSSA (TOPLAS 2014), Blazy-Robillard-Appel (ESOP 2010), and CakeML (`reg_allocScript.sml` / `reg_allocProofScript.sml`)—all operate post-SSA over flat whole registers without sub-register lane aliasing.
2. **Live soundness bug in `regalloc2` (`v0.15.3`):** In `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f`, `CheckerState::update` (`src/checker.rs:545-562`) steps `CheckerInst::Move { into, from }` via `if let Some(val) = self.get_value(&from).cloned() { self.set_value(into, val); }` **with no `else` branch to invalidate `into`**. Executing unmodified `regalloc2` reproduces two concrete counterexamples where `Checker::run()` returns `Ok(())` while runtime execution corrupts a live SSA return value (`0x0000000020001111` overwritten with `0xc10bbe2010001112` via a clobbered-source move, and with `0xbad0cafeeead1111` via `MoveAndScratchResolver` borrowed-scratch save/restore). Upstream `regalloc2` also removed all safepoint and GC reference-type (`reftype`) support, models `PReg` as a flat 6-bit index without sub-registers, and panics in `Algorithm::Fastalloc` (`src/fastalloc/mod.rs:670-672`) on `OperandConstraint::Limit(4)` (`i686` `AL`/`CL`/`DL`/`BL` byte constraints).
3. **LLVM disables `SubRegLiveness` (`LaneBitmask`) by default on both X86 and non-streaming AArch64:** In `llvm/llvm-project@984202b7bd448b1c8da65689ecd2dd27aa891175`, X86 never overrides `TargetSubtargetInfo::enableSubRegLiveness()` (`false` at `TargetSubtargetInfo.h:354`) and omits `CoveredBySubRegs = 1` on `RAX`, `YMM0..31`, and `ZMM0..31` (`X86RegisterInfo.td:280-288,383-403`). On AArch64, `-aarch64-enable-subreg-liveness-tracking` defaults to `false` outside SME streaming mode (`AArch64Options.td:214-217`, `AArch64Subtarget.cpp:316-324`): coalescing `SUBREG_TO_REG` loses implicit upper-lane zeroing, dropping super-register `implicit-def`s in `LLVM 22.1.6` (`FADDSrr` losing `implicit-def $q1`, `ADDWrr` losing `implicit-def $x8`) and requiring a post-RA repair pass (`AArch64SRLTDefineSuperRegs.cpp:9-82`) in upstream `main`.
4. **Asymmetric partial-width write hazards require explicit `WriteMode` framing:** Native `x86_64` execution verifies that 32-bit GPR writes (`movl`) zero `[63:32]` (`0xdeadbeef11223344 -> 0x0000000033334444`), 8-bit/16-bit writes (`movb` to `AL`/`AH`, `movw` to `AX`) preserve upper lanes (`0xdeadbeef1122bbaa`, `0xdeadbeef1122ccdd`), legacy SSE `addss` preserves `YMM[255:128]`, and VEX-128 `vaddss` zeroes `YMM[255:128]` (and `ZMM[511:256]`).
5. **Linear witness-seeded `RegAllocCert` unifies ABI, register allocation, and DWARF value accuracy:** Pairing untrusted heuristics (`Ion` / `RAGreedy`) with explicit block-entry `(PhysLoc, VRegId)` witnesses and per-write `WriteMode` eliminates iterative dataflow fixpoints, closes both `regalloc2` checker holes, checks **6.29x–20.87x faster** than `regalloc2`'s fixpoint `Checker` across 15 target-workload runs (`9.90–204.09 us` vs `62.25–2275.19 us` median), and proves DWARF `DW_OP_piece` / `DW_OP_bit_piece` / `DW_OP_regx` **value accuracy** (stronger than CompCert `Debugvarproof.v:393-558`, which proves only trace non-interference).

## Applicability

This report governs ahead-of-time verified Rust backend design across `x86_64-unknown-linux-gnu` (`LP64` System V), `aarch64-unknown-linux-gnu` (`AAPCS64`), and `i686-unknown-linux-gnu` (`ILP32` cdecl). The 17 subjects in `REPORT.json` relate as follows:

- **Inspected upstream codebases:** `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f` (`v0.15.3`, compiled offline with `--cfg feature="checker" --cfg feature="std"` against `rust-lang/rustc-hash@f16da569fcb867fa1bc3b5dba18c9b8f7ca99483` and `fitzgen/bumpalo@482e18d57f386fe3e0ecabc08ee448b561a14239`); `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`; `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`; and `llvm/llvm-project@984202b7bd448b1c8da65689ecd2dd27aa891175`.
- **Executed host toolchains (`x86_64-unknown-linux-gnu`):** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (2026-05-31)` and bundled `llc` `LLVM 22.1.6`) and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`Lean 4.34.1`). Note the explicit version distinction between executed `LLVM 22.1.6` (which predates `AArch64SRLTDefineSuperRegs.cpp`) and inspected `llvm/llvm-project@984202b7bd448b1c8da65689ecd2dd27aa891175` (which adds that pass).
- **Peer-reviewed papers (9 DOI-pinned subjects):** Hack-Grund-Goos (CC 2006, `10.1007/11688834_18`), Rideau-Serpette-Leroy (JAR 2008, `10.1007/s10817-007-9096-8`), Braun-Hack (CC 2009, `10.1007/978-3-642-00722-4_13`), Rideau-Leroy (CC 2010, `10.1007/978-3-642-11970-5_13`), Blazy-Robillard-Appel (ESOP 2010, `10.1007/978-3-642-11957-6_9`), Buchwald-Zwinkau-Bersch (CC 2011, `10.1007/978-3-642-19861-8_4`), Barthe-Demange-Pichardie (TOPLAS 2014, `10.1145/2579080`), Buchwald-Lohner-Ullrich (CC 2016, `10.1145/2892208.2892211`), and Tan et al. (ICFP 2016, `10.1145/2951913.2951924`).

Hardware inline-assembly probes executed natively on `x86_64` Linux (AVX enabled); `aarch64` and `i686` object code and DWARF sections were cross-compiled and inspected via `llvm-objdump` and `readelf`.

## Findings

### 1. SSA Register Allocation Theory vs Mechanized Allocators

**1.1 Chordal SSA decoupling and its three practical breakdowns.**
Hack, Grund, and Goos (`10.1007/11688834_18`) showed that strict SSA live ranges over uniform registers form dominance-tree subtrees whose interference graph $G$ is **chordal**: $\chi(G) = \omega(G)$ (maximum live clique size), allowing polynomial-time greedy dominance-order coloring once Braun-Hack SSA spilling (`10.1007/978-3-642-00722-4_13`) bounds $\max_p |\text{Live}(p)| \le k$. Three real-ISA properties break polynomial chordal coloring:

1. **Aggressive $\phi$- and copy-coalescing:** Contracting move edges breaks chordality; optimal conflict-free SSA coalescing remains NP-complete (Hack-Grund-Goos CC 2006, Section 4).
2. **Pre-colored fixed-register constraints (`RAX:RDX` `MUL`/`DIV`, `CL` shifts, ABI call clobbers):** Physical registers carry multiple non-SSA live segments.
3. **Irregular sub-register classes (`AL`/`AH`/`AX`/`EAX`, `i686` 4-GPR `ABCD` byte constraints):** Buchwald, Zwinkau, and Bersch (`10.1007/978-3-642-19861-8_4`) showed in libFirm that chordal coloring cannot express asymmetric sub-register overlap or `ABCD`-restricted byte ops, motivating Partitioned Boolean Quadratic Programming (PBQP).

`Basis: normative (published proofs in Hack-Grund-Goos CC 2006, Braun-Hack CC 2009, Buchwald-Zwinkau-Bersch CC 2011)`

**1.2 Resolution of the CC 2016 Isabelle/HOL citation conflation and mechanized allocator survey.**
Citations to *"Buchwald-Lohr-Zwinkau, Verified SSA-Based Register Allocation (CC 2016)"* conflate **Buchwald, Lohner, and Ullrich** (*"Verified Construction of Static Single Assignment Form"*, CC 2016, `10.1145/2892208.2892211`, Isabelle/HOL AFP `Formal_SSA`, verifying CFG-to-SSA construction) with **Buchwald, Zwinkau, and Bersch** (*"SSA-Based Register Allocation with PBQP"*, CC 2011, `10.1007/978-3-642-19861-8_4`, unverified C in libFirm). Similarly, CompCertSSA (`10.1145/2579080`) destructs CSSA back to RTL before register allocation.

Among mechanized allocators, Blazy-Robillard-Appel (`10.1007/978-3-642-11957-6_9`) verified George-Appel Iterated Register Coalescing (IRC) in Coq without live-range splitting or sub-registers. In CakeML (`compiler/backend/reg_alloc/`), `reg_allocScript.sml` (`1,493` LOC) and `proofs/reg_allocProofScript.sml` (`3,482` LOC; `2.33x` proof-to-code ratio) prove `Theorem reg_alloc_correct` (`lines 3451-3468`) over flat `tag = Fixed num | Atemp | Stemp` (`reg_allocScript.sml:41-43`), with zero sub-register lanes, zero rematerialization, and unverified performance invariants (`reg_allocScript.sml:19-32`: sorted `adj_ls` and `coalesced[x] = x` orientation are documented as *"secret invariants that are important for performance but are not verified"*).

`Basis: documentation + source (DOI records; CakeML reg_allocScript.sml:19-81, reg_allocProofScript.sml:3451-3468)`

---

### 2. CompCert RTL-to-LTL Translation Validation and Parallel Moves

**2.1 Backward Kildall equation validation (`Allocation.v`, `Allocproof.v`, `Locations.v`).**
CompCert delegates splitting (`Splitting.ml:1-186`) and George-Appel IRC (`IRC.ml:546-690`, `Regalloc.ml`) to an untrusted OCaml oracle (`Parameter regalloc`, `Allocation.v:1355`) and validates `RTL -> LTL` via `check_function` (`Allocation.v:1345-1350`, proved sound in `Allocproof.transf_program_correct`, `Allocproof.v:2528-2538`, across `4,505` Coq LOC). Backward dataflow `analyze` (`Allocation.v:1129-1340`) propagates sets of equations `r = l [k]` with `Inductive equation_kind := Full | Low | High` (`Allocation.v:376`). Three structural boundaries apply:

- **No general sub-register slices:** `Low` and `High` apply exclusively to 32-bit `Archi.splitlong` halves of 64-bit `Tlong` values (`Twolong l_hi l_lo`, `Allocation.v:212-269,783,1292-1312`).
- **Whole-register disjointness (`Loc.diff`):** `Locations.v:146-156` defines `Loc.diff (R r1) (R r2)` as `r1 <> r2`. `x86/Machregs.v:28-125` models only 16 whole GPRs and `XMM0..15` (omitting `AH`, `YMM`, `ZMM`), `aarch64/Machregs.v:23-195` aliases `"w0"` and `"x0"` to the same constructor `X0`, and `driver/ExtendedAsm.ml:160-168` rejects `"al"`/`"ah"`/`"ymm0"` inline-asm register names.
- **Iterative fixpoint overhead and non-interfering debug proofs:** `analyze` iterates to a post-fixpoint over loop back-edges; `track_moves` (`Allocation.v:695-745`) validates emitted sequential moves backward, while `Moves.v` (Rideau-Serpette-Leroy, `10.1007/s10817-007-9096-8`) breaks whole-register cycles via a windmill DFS automaton. Finally, `Debugvarproof.v:393-558` (`match_states` over `EF_debug` `E0` steps) proves **only execution-trace non-interference**, not that emitted debug locations hold the source variable's value.

`Basis: source + normative (CompCert Allocation.v, Allocproof.v, Locations.v, Debugvarproof.v, ExtendedAsm.ml; Rideau-Leroy CC 2010)`

---

### 3. `bytecodealliance/regalloc2` Internals and Live Symbolic Checker Counterexamples

**3.1 Flat `PReg` model, removed safepoints/`reftypes`, and `Fastalloc` `Limit(4)` panic.**
In `regalloc2` (`v0.15.3`), `Algorithm::Ion` (`src/ion/{mod,liveranges,merge,process,spill}.rs`) performs backtracking bundle allocation and bundle-merge coalescing, while `Algorithm::Fastalloc` (`src/fastalloc/mod.rs`) performs single-pass backward linear scan. Inspection and execution establish:
- **Flat `PReg` (`src/lib.rs:110-145`):** 2-bit `RegClass` + 6-bit `hw_enc` (`0..63`), with zero sub-register aliasing.
- **Safepoints and `reftypes` removed:** Zero references remain in `src/{lib,checker,moves}.rs` or `src/{ion,fastalloc}/*`; only an unread fuzzer Vec `reftype_vregs` survives at `src/fuzzing/func.rs:58,159,483`.
- **`Fastalloc` panics on `OperandConstraint::Limit(4)`:** Approximating `i686` byte-addressable `ABCD` registers via `Limit(4)` (`src/checker.rs:679-688`) triggers `todo!("limit constraints are not yet supported in fastalloc")` at `src/fastalloc/mod.rs:670-672` (`"fastalloc_supported": false` in `support/empirical_results.json`).

**3.2 Live-confirmed soundness bug in `CheckerState::update` (`src/checker.rs:545-562`).**
In `src/checker.rs:545-562`, `CheckerInst::Move { into, from }` executes `if let Some(val) = self.get_value(&from).cloned() { self.set_value(*into, val); }` **without an `else { self.remove_value(&into); }` branch** (inserting `CheckerValue::Universe` would hit `unreachable!()` in `remove_vreg` at `src/checker.rs:236-240`). When `from` is uninitialized, clobbered (`src/checker.rs:664-667`), or an unallocated spill slot, `into` retains its stale `CheckerValue::Reg(vreg)` tag even though the machine move overwrites `into` at runtime. Running `support/regalloc2_probe.rs` against unmodified `regalloc2` confirms two end-to-end soundness failures accepted with `Checker::run() == Ok(())`:

- **Witness 1 (Clobbered-source `Edit::Move`):** `v0` (`0x20001111`) is live in `p0`; an instruction clobbers `p1` (`0xc10bbe2010001112`, removing `p1` from `allocations`); a bogus `Edit::Move { from: p1, to: p0 }` overwrites `p0` before `ret v0`. `Checker::run()` returns `Ok(())`, while runtime execution returns `0xc10bbe2010001112`.
- **Witness 2 (`MoveAndScratchResolver` borrowed-scratch save/restore, `src/moves.rs:324-446`):** Cycle resolution spills an unallocated scratch `p2` to `save_slot` (`None`), routes `v0` through `p2`, and emits `Move(save_slot -> p2)` to restore uninitialized stack bytes (`0xbad0cafeeead1111`). Because `save_slot` is `None`, `p2` falsely retains `Reg(v0)`; reading `v0` from `p2` passes `Checker::run() == Ok(())` while returning `0xbad0cafeeead1111`.

Both witnesses are rejected (`Err("early use mismatch or clobbered")`) by our fixed linear certificate checker (`support/regalloc2_probe.rs`) and proved in `UnifiedRegAllocLaneCert.lean:400-460`.

**3.3 Empirical `regalloc2` (`L2`, `L3`, `L4`, `L5`, `L6`) measurements.**
Compiling `libregalloc2.rlib` (`opt-level=3`, `feature="checker"`) takes `5.2873 s` (`297.86 MiB` max RSS, `3,968,656` B `.rlib`, `L2`/`L6`). Across 5 SSA loop/diamond CFGs and 3 target environments (`x86_64` 14 GPRs, `aarch64` 27 GPRs, `i686` 6 GPRs), `support/regalloc2_probe.rs` measures median latencies and footprints:

| Workload (`B` / `I` / `V`) | Target | `Ion` `L3` (`us`) | `Fast` `L3` (`us`) | `Ion`/`Fast` Spills (`L4`) | `Ion`/`Fast` Edits (`L4`) | `regalloc2` `Checker` `L5` (`us`) | Linear Cert `L5` (`us`) | Cert Bytes (`Out`+`Wit`=`Tot`) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `small_loop_w6` (`9`/`39`/`44`) | `x86_64` | `43.63` | `7.49` | `0` / `35` | `4` / `109` | `62.25` | `9.90` | `340+516=856` |
| `small_loop_w6` (`9`/`39`/`44`) | `aarch64` | `43.28` | `12.99` | `0` / `35` | `4` / `109` | `64.73` | `10.33` | `340+516=856` |
| `small_loop_w6` (`9`/`39`/`44`) | `i686` | `121.53` | `13.19` | `5` / `37` | `36` / `113` | `91.55` | `10.94` | `724+580=1,304` |
| `medium_loops_w12` (`33`/`177`/`248`) | `x86_64` | `843.35` | `51.51` | `1` / `229` | `51` / `761` | `383.86` | `25.86` | `2,176+3,612=5,788` |
| `medium_loops_w12` (`33`/`177`/`248`) | `aarch64` | `163.62` | `36.58` | `0` / `221` | `4` / `745` | `330.28` | `51.66` | `1,612+3,732=5,344` |
| `medium_loops_w12` (`33`/`177`/`248`) | `i686` | `590.68` | `62.64` | `10` / `229` | `229` / `761` | `609.89` | `29.22` | `4,312+3,612=7,924` |
| `high_pressure_spill_w20` (`33`/`257`/`392`) | `x86_64` | `1,002.59` | `60.66` | `15` / `365` | `260` / `1,225` | `1,385.92` | `92.16` | `5,580+5,724=11,304` |
| `high_pressure_spill_w20` (`33`/`257`/`392`) | `aarch64` | `568.69` | `105.25` | `0` / `365` | `4` / `1,225` | `926.42` | `70.29` | `2,508+5,636=8,144` |
| `high_pressure_spill_w20` (`33`/`257`/`392`) | `i686` | `1,055.43` | `97.43` | `18` / `365` | `409` / `1,225` | `1,152.66` | `88.30` | `7,368+5,668=13,036` |
| `byte_subreg_limit4_w10` (`25`/`147`/`188`) | `x86_64` | `223.63` | *panics* | `0` / — | `44` / — | `229.95` | `21.07` | `1,764+2,308=4,072` |
| `byte_subreg_limit4_w10` (`25`/`147`/`188`) | `aarch64` | `208.25` | *panics* | `0` / — | `44` / — | `250.44` | `40.50` | `1,764+2,308=4,072` |
| `byte_subreg_limit4_w10` (`25`/`147`/`188`) | `i686` | `520.84` | *panics* | `9` / — | `158` / — | `436.84` | `25.35` | `3,132+2,444=5,576` |
| `large_cfg_loops_w16` (`97`/`585`/`896`) | `x86_64` | `2,327.05` | `178.76` | `5` / `857` | `299` / `2,913` | `1,976.56` | `204.09` | `9,120+13,852=22,972` |
| `large_cfg_loops_w16` (`97`/`585`/`896`) | `aarch64` | `1,559.53` | `254.01` | `0` / `857` | `4` / `2,913` | `2,275.19` | `139.48` | `5,580+13,828=19,408` |
| `large_cfg_loops_w16` (`97`/`585`/`896`) | `i686` | `3,503.12` | `284.94` | `13` / `857` | `883` / `2,913` | `1,950.76` | `113.92` | `16,128+13,852=29,980` |

Upstream `Checker::run()` consumes **85%–146% of `Ion` allocation time** on `585`-instruction loops because it iterates `FxHashMap` dataflow meets to a fixpoint; seeding explicit block-entry witnesses reduces checking to one linear array scan (**6.29x–20.87x speedup**). Meanwhile, `Fastalloc` incurs `857` spills (`2,913` edits) vs `Ion`'s `0–13` spills, showing why untrusted heuristic allocation + linear certificate checking strictly dominates simplifying the allocator to ease verification.

`Basis: source + execution (synthetic SSA CFG benchmark over unmodified regalloc2 0.15.3 in support/regalloc2_probe.rs; full-crate rustc L4 runtime not measured)`

---

### 4. LLVM `RAGreedy`, `LaneBitmask`, and Hardware Partial-Write Asymmetries

**4.1 Why LLVM keeps `SubRegLiveness` disabled by default on X86 and non-streaming AArch64.**
In `RAGreedy::selectOrSplitImpl` (`RegAllocGreedy.cpp:2777-2860`), allocation cascades through `tryAssign`, `tryEvict` (`lines 594-750`), `tryRegionSplit` / `tryLocalSplit` (`lines 1242-2045`), and `LiveRangeEdit::allUsesAvailableAt` / `rematerializeAt` (`LiveRangeEdit.cpp:78-165`), tracking `SubRange` intervals via 64-bit `LaneBitmask` (`LaneBitmask.h:40-44`) only when `enableSubRegLiveness()` is enabled (`DetectDeadLanes.cpp:550-575`). Yet:

- **X86 (`TargetSubtargetInfo.h:354`, `X86RegisterInfo.td:187-403`):** `enableSubRegLiveness()` is `false`. While `AX` (`line 187`) and `EAX` (`line 235`) set `CoveredBySubRegs = 1`, `RAX` (`line 281`), `YMM0..31` (`lines 383-394`), and `ZMM0..31` (`lines 398-403`) omit `CoveredBySubRegs = 1` and lack upper-lane pseudo-subregisters; X86 relies instead on `hasPartialRegUpdate` / `breakPartialRegDependency` (`X86InstrInfo.cpp:6607,7386`) to insert `vxorps`/`xorps` dependency breakers.
- **AArch64 (`AArch64RegisterInfo.td:95-169,319-325`, `AArch64Options.td:214-217`, `AArch64Subtarget.cpp:316-325`):** Despite defining `W0_HI..W30_HI` and `B0_HI..Q31_HI` with `CoveredBySubRegs = 1`, `-aarch64-enable-subreg-liveness-tracking` defaults to `false` outside `IsStreaming` (SME2). As documented in `AArch64SRLTDefineSuperRegs.cpp:9-82`, coalescing `SUBREG_TO_REG` discards the fact that 32-bit `W` and scalar `B`/`H`/`S`/`D` writes zero upper bits of `X`/`Q`. Running `LLVM 22.1.6` `llc` (which lacks `AArch64SRLTDefineSuperRegs.cpp`) on `zext_coalesce_and_tuple` confirms this directly (`support/empirical_results.json:110-148`): under default `false`, `FADDSrr` emits `implicit-def $q1` and `ADDWrr` emits `implicit-def $x8`; under `-aarch64-enable-subreg-liveness-tracking=true`, **both `implicit-def`s vanish**. Upstream `main` patches them back post-RA assuming four unverified invariants `(A)–(D)` (`lines 39-58`), notably Invariant `(B)`: rematerialization must never execute a narrow zero-extending def when upper lanes hold live data.

**4.2 Native `x86_64` silicon verification and cross-target codegen probes.**
Native `x86_64` inline-assembly execution (`support/run_toolchain_subreg_dwarf_probes.py`) confirms all five hardware lane behaviors (`support/empirical_results.json:20-37`):
- `mov eax, 0x33334444` over `0xdeadbeef11223344` yields `0x0000000033334444` (`zeroExtend64`).
- `mov al, 0xaa; mov ah, 0xbb` yields `0xdeadbeef1122bbaa`, and `mov ax, 0xccdd` yields `0xdeadbeef1122ccdd` (`preserveUpper`).
- Over a seeded 256-bit `YMM0` (`[0x3f80000040000000, 0xcafebabe11112222, 0xdeadbeef33334444, 0xfeedface55556666]`), legacy SSE `addss xmm0, xmm1` preserves `YMM0[255:128]` (`[0x3ff0000040400000, 0xcafebabe11112222, 0xdeadbeef33334444, 0xfeedface55556666]`), whereas VEX-128 `vaddss xmm0, xmm0, xmm1` zeroes `YMM0[255:128]` (`[0x3ff0000040400000, 0xcafebabe11112222, 0, 0]`, `zeroExtend512`).

Cross-compiling our 3-function Rust probe (`-C opt-level=2 -C debuginfo=2`) shows `i686`'s 4-register `ABCD` byte constraint forces `12` `(%esp)` stack accesses in `six_byte_predicates` vs `1` on `x86_64` and `0` on `aarch64`, while `x86_64` inserts `14` `xorps`/`xorl` false-dependency clears vs `0` on `aarch64`.

`Basis: source + execution (LLVM source; native x86_64 inline-asm + LLVM 22.1.6 llc + rustc cross-target disassembly)`

---

### 5. Unified Physical-Slice Representation (`PhysLoc`) Across ABI, `RegAllocCert`, and DWARF

**5.1 Eliminating three-way representation drift.**
In LLVM, `X86RegisterInfo.td:235-243,363-403` assigns `DwarfRegNum = -2` to `EAX`/`AX`/`AL`/`AH` (forcing `DwarfExpression::addMachineReg` at `DwarfExpression.cpp:113-195` to walk `TRI.superregs` to `RAX` (`DW_OP_reg0`) + `DW_OP_piece`/`DW_OP_bit_piece(8, 8)`), maps `XMM16..31` to `67..82` (`DW_OP_regx: 71` on `xmm20`, verified via `readelf` in `empirical_results.json:102-108`), and drops multi-register composite locations under `DW_OP_entry_value`/`DW_OP_deref` (`DwarfExpression.cpp:355-388`).

`support/UnifiedRegAllocLaneCert.lean` (`787` LOC, `23` theorems, `0` `sorry`, `0` `native_decide`, checked by `Lean 4.34.1` in `13.3659 s`, `604,488 KB` max RSS) unifies `FnAbi`, `RegAllocCert`, rematerialization, and DWARF emission around one `PhysLoc` type (`reg r slice | stack s slice`) over `11` disjoint `LaneId`s (`b0`, `b1` for `AH`, `b2..b3`, `b4..b7` for `hi32`, `xmmHi`, `ymmHi`, `zmmHi`), `9` `SubRegSlice`s (`lo8..zmm512`), and `4` `WriteMode`s (`preserveUpper`, `zeroExtend64`, `zeroExtend128`, `zeroExtend512`):

1. **Lane framing & `AL`/`AH` co-allocation (`applyRegWrite_preserves_untouched`, `x86_al_ah_disjoint_coallocation`, `partial_write_mode_asymmetries`):** Proves untouched-lane preservation and exact `zeroExtend64`/`zeroExtend512` vs `preserveUpper` behavior.
2. **Sound `Edit::Move` vs `regalloc2` bug (`stepMoveSound_preserves_refinement`, `buggyRegalloc2Move_unsound_witness`):** Unconditionally evicts `dst` and overlapping lanes via `nonInterferingWrite` before consulting `lookupSym sym src`, preserving `SymRefines` when `src` is clobbered (`none`).
3. **Sub-register parallel-move cycles (`stepOriginMove_sound`, `parmove_3cycle_and_subreg_swap_verified`):** Domain-seeded `OriginEnv` + `sliceShapeEq` verifies simultaneous 3-GPR cycles and in-place `AL <-> AH` swaps via byte scratch `bl5` (`[propext]` only).
4. **Rematerialization safety (`checkRematSafe_sound`, `remat_narrow_zeroext_destroys_upper_lane`):** Proves narrow rematerialization sound iff `checkRematSafe` holds, rejecting `lo32` `zeroExtend64` rematerialization when `hi32` is live (formalizing `AArch64SRLTDefineSuperRegs` Invariant `B`).
5. **DWARF value accuracy (`emitCompositeDwarf_sound`, `unified_regalloc_abi_dwarf_value_accuracy`):** Emitting `DW_OP_reg0..31`, `DW_OP_regx`, `DW_OP_fbreg`, `DW_OP_piece`, and `DW_OP_bit_piece(8, 8)` / `(32, 32)` (matching real `i686` `DW_OP_bit_piece: size: 8 offset: 8` at `empirical_results.json:95`) from certified `(PhysLoc, VRegId)` pairs guarantees `evalDwarfAtoms` reconstructs exact SSA values.

`Basis: execution (Lean 4.34.1 kernel verification of support/UnifiedRegAllocLaneCert.lean; rustc/readelf DWARF dumps)`

---

### 6. Architecture Trade-Offs Across Cost (`L1`–`L6`), Simplicity (`C1`–`C2`), and Validation (`V1`–`V4`)

We compare three candidate verification designs across **Authoring/proof velocity (`L1`)**, **Toolchain build time (`L2`)**, **Allocation/synthesis latency (`L3`)**, **Generated code quality (`L4`)**, **Certificate checking latency (`L5`)**, **Memory/binary/certificate footprint (`L6`)**, **Specification auditability (`C1`)**, **Conceptual orthogonality / Felleisen expressibility (`C2`)**, and **Validation (`V1`–`V4`)**:

| Axis | Verified In-Kernel Allocator (`CakeML` IRC) | Fixpoint Translation Validator (`CompCert` / `regalloc2` `Checker`) | Linear Witness-Seeded `RegAllocCert` (Untrusted `Ion`/`RAGreedy` + Block-Entry Witnesses + `WriteMode`) |
| --- | --- | --- | --- |
| **`L1` Proof Velocity** | `3,482` HOL4 proof LOC for `1,493` LOC of basic whole-reg IRC; every heuristic change breaks proofs. | `2,545` Coq proof LOC (`Allocproof.v`) decoupled from `2,331` OCaml allocator LOC; lacks sub-reg lanes. | `787` Lean 4 LOC (`23` theorems) covers 11-lane `WriteMode`, `Move`, parallel moves, remat, and DWARF; heuristics untrusted. |
| **`L2` Build Time** | High theorem-prover rebuild on heuristic edits (*full `rustc` build not measured*). | `libregalloc2.rlib` (`opt-level=3`, `checker`) builds in `5.2873 s` (`297.86 MiB` RSS). | `5.2873 s` (`regalloc2`) + `13.3659 s` (`590.32 MiB` RSS) standalone Lean 4 kernel check. |
| **`L3` Compile Latency** | Constrained by verified functional structures (`CakeML` leaves sorted-list invariant unverified). | `Ion`: `43.28–3,503.12 us`; `Fastalloc`: `7.49–284.94 us` on `39–585` inst CFGs (*crate `L3` not measured*). | Identical allocator `L3` + `O(|Blocks| * |LiveIn|)` block-entry witness emission. |
| **`L4` Code Quality** | Degraded unless splitting, coalescing, remat, and sub-regs are proved (`Fastalloc`: `857` vs `0–13` spills). | Full `Ion` (`0–18` spills across 15 runs) / `RAGreedy` quality on whole regs. | Full `Ion` / `RAGreedy` quality + sound `AL`/`AH` co-allocation and sub-reg rematerialization. |
| **`L5` Checker Speed** | `0 us` per compile (proved statically). | `regalloc2` fixpoint `Checker`: `62.25–2,275.19 us` (**85%–146%** of `Ion` `L3` on `585`-inst CFGs). | **Single linear scan (`6.29x–20.87x` faster):** `9.90–204.09 us` median (`113.92 us` vs `1,950.76 us` on `585`-inst `i686`). |
| **`L6` Footprint** | `0` cert bytes; large verified TCB. | `340–16,128` B `Output` + per-block heap `FxHashMap` fixpoint states. | `516–13,852` B entry witnesses (`856–29,980` B total on `39–585` inst CFGs); `0` heap hash-maps. |
| **`C1` / `C2` Simplicity** | Low: mixes NP-hard coloring worklists with semantics. | High decoupling, but `regalloc2`'s `None`-preserving `Move` rule caused silent unsoundness. | Highest: one local step rule (`stepMoveSound` + `WriteMode` + `checkRematSafe`) shared macro-free across ABI, RA, and DWARF. |

**Validation requirements (`V1`–`V4`):**
- **`V1` (Spec adequacy & non-vacuity):** Retain executable negative-control counterexamples (`buggyRegalloc2Move_unsound_witness`, `remat_narrow_zeroext_destroys_upper_lane`) and kernel `#print axioms` gates (`0` `sorryAx`, `0` `Lean.ofReduceBool`).
- **`V2` (Differential checker fuzzing):** Extend `regalloc2/src/fuzzing/` with `SubRegSlice`, `WriteMode`, `Limit(4)`, and borrowed-scratch moves against a concrete machine-state interpreter.
- **`V3` (Silicon hazard validation):** Execute native lane-preservation canaries on `x86_64` (GPR `movl`/`movb`/`movw`, legacy SSE vs VEX/EVEX) and native `aarch64` (`W` -> `X[63:32]`, scalar `B`/`H`/`S`/`D` -> `Q[127:width]`, SVE/SME).
- **`V4` (Held-out multi-target replay):** Replay `RegAllocCert` + DWARF location evaluation across `libcore` and held-out crates on `x86_64`, `aarch64`, and `i686` under GDB/LLDB checkpoints.

`Basis: derived + execution (upstream source inspection, support/regalloc2_probe.rs, support/UnifiedRegAllocLaneCert.lean)`

## Boundaries

- **Full-compiler `rustc` crate compile-time (`L3`) and generated-binary runtime (`L4`) (`not examined`):** Benchmarks in `support/regalloc2_probe.rs` measure standalone `regalloc2` and linear-certificate execution on five synthetic SSA CFGs (`39–585` instructions), not end-to-end Cargo crate builds; full-compiler `L2`/`L3`/`L4` remain `not measured`.
- **Native `aarch64` and `i686` hardware execution (`not examined`):** Silicon inline-assembly probes ran on `x86_64-unknown-linux-gnu` only; `aarch64` and `i686` results come from architecture specifications, cross-compilation (`LLVM 22.1.6`), `llvm-objdump` / `readelf`, and upstream source.
- **Scalable vector (`SVE` / `SME2` `vscale`) predication (`not examined`):** `UnifiedRegAllocLaneCert.lean` models fixed-width slices up to `512` bits (`zmm512`), not variable-length SVE `Z`/`P` merging vs zeroing predication.
- **`i686` legacy x87 FP stack (`ST(0)..ST(7)`) (`unsupported` in `UnifiedRegAllocLaneCert.lean`):** Stack-permuting `FXCH` state is outside `PhysLoc` (`rustc` `i686-unknown-linux-gnu` defaults to SSE2 `XMM0..7` for scalar floats, using `ST(0)` only on C ABI returns).
- **`regalloc2` `Fastalloc` with `OperandConstraint::Limit` (`unsupported` upstream):** Panics at `src/fastalloc/mod.rs:670-672`.
- **Composite multi-register DWARF under `DW_OP_entry_value` / `DW_OP_deref` (`unsupported` in LLVM):** Dropped (`LocationKind = Unknown`) at `DwarfExpression.cpp:355-388`.

## Evidence

1. **Pinned Upstream Repositories (40-character Git commit SHAs):**
   - `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f` (`v0.15.3`): `src/lib.rs:110-145,567-595,1483-1510`, `src/checker.rs:236-240,519-562,664-688`, `src/moves.rs:31-65,304-446`, `src/fastalloc/mod.rs:670-672,803`, `src/ion/{mod,merge,process,spill}.rs`, `src/fuzzing/func.rs:58,159,483` (built with `rust-lang/rustc-hash@f16da569fcb867fa1bc3b5dba18c9b8f7ca99483` and `fitzgen/bumpalo@482e18d57f386fe3e0ecabc08ee448b561a14239`).
   - `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`: `backend/Locations.v:114-156`, `backend/Allocation.v:212-269,376,695-783,1129-1374`, `backend/Allocproof.v:2528-2538`, `backend/Debugvar.v:356-369`, `backend/Debugvarproof.v:393-558`, `backend/IRC.ml:546-690`, `backend/Splitting.ml:1-186`, `driver/ExtendedAsm.ml:160-168`, `x86/Machregs.v:28-125`, `aarch64/Machregs.v:23-195`.
   - `llvm/llvm-project@984202b7bd448b1c8da65689ecd2dd27aa891175`: `llvm/include/llvm/MC/LaneBitmask.h:40-44`, `llvm/include/llvm/CodeGen/TargetSubtargetInfo.h:354`, `llvm/lib/CodeGen/RegAllocGreedy.cpp:543-750,1242-2045,2365-2860`, `llvm/lib/CodeGen/LiveRangeEdit.cpp:78-165`, `llvm/lib/CodeGen/DetectDeadLanes.cpp:550-575`, `llvm/lib/Target/X86/X86RegisterInfo.td:187-403`, `llvm/lib/Target/X86/X86InstrInfo.cpp:6607,7386`, `llvm/lib/Target/AArch64/{AArch64RegisterInfo.td:95-169,319-325, AArch64Options.td:214-217, AArch64Subtarget.cpp:315-327, AArch64SRLTDefineSuperRegs.cpp:9-115}`, `llvm/lib/CodeGen/AsmPrinter/DwarfExpression.cpp:56-195,355-388`.
   - `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`: `compiler/backend/reg_alloc/{reg_allocScript.sml:19-81, proofs/reg_allocProofScript.sml:3451-3468}`.
   - Executed host toolchains (`2026-11-20`): `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `LLVM 22.1.6`) and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`Lean 4.34.1`).

2. **Package Support Artifacts (`support/`):**
   - `support/regalloc2_probe.rs`: Reproduces both `Checker` soundness counterexamples (`Witness 1` & `Witness 2`), `Fastalloc` `Limit(4)` panic handling, and 15 target-workload `L3`/`L4`/`L5`/`L6` benchmarks.
   - `support/UnifiedRegAllocLaneCert.lean`: `787`-LOC Lean 4 mechanization (`23` theorems, `0` `sorry`, `0` `native_decide`) of 11-lane `PhysLoc` framing, `stepMoveSound`, cross-lane `AL`/`AH` parallel moves, `checkRematSafe`, and DWARF value accuracy.
   - `support/run_toolchain_subreg_dwarf_probes.py` & `support/empirical_results.json` (`19,558` B): Executes native `x86_64` lane tests, cross-target DWARF/disassembly probes, `llc` SRLT MIR differential dumps, and Lean 4 kernel axiom checks.

## Revalidation

1. **Kernel-check the Lean 4 mechanization (`Lean 4.34.1`):**
   ```bash
   lean reports/verified-ssa-register-allocation-coalescing-and-subregister-lane-liveness/support/UnifiedRegAllocLaneCert.lean
   ```
   Confirm exit code `0`, zero warnings, and `#print axioms` listing only `[propext]` or `[propext, Classical.choice, Quot.sound]` (zero `sorryAx`, zero `Lean.ofReduceBool`).

2. **Compile and run `support/regalloc2_probe.rs` against `bytecodealliance/regalloc2@4eb655fa745fba271af74be8495154a4b0cac56f`:**
   ```bash
   # Build rustc_hash, bumpalo, and regalloc2 (--cfg feature="checker" --cfg feature="std") into /tmp/ra2_rlibs:
   rustc --edition 2021 -C opt-level=3 \
     reports/verified-ssa-register-allocation-coalescing-and-subregister-lane-liveness/support/regalloc2_probe.rs \
     --extern regalloc2=/tmp/ra2_rlibs/libregalloc2.rlib \
     -L dependency=/tmp/ra2_rlibs -o /tmp/regalloc2_probe_bin
   /tmp/regalloc2_probe_bin > /tmp/regalloc2_probe_results.json
   ```
   Confirm `upstream_checker_accepted == true` and `fixed_linear_cert_checker_accepted == false` on both witnesses, and `"fastalloc_supported": false` on `byte_subreg_limit4_w10`.

3. **Re-run the toolchain/hardware/DWARF probes and corpus validator:**
   ```bash
   REGALLOC2_PROBE_JSON=/tmp/regalloc2_probe_results.json \
     python3 reports/verified-ssa-register-allocation-coalescing-and-subregister-lane-liveness/support/run_toolchain_subreg_dwarf_probes.py
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
