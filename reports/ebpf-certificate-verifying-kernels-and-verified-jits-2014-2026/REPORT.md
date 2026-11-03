# Certificate-Verifying eBPF Kernels, Post-Verification Rewrites, and Verified JITs (2014–2026)

## Summary

Admitting untrusted native-speed extensions into a privileged kernel address space requires a soundness chain from static admission checking through bytecode rewriting to machine-code lowering. Across the 2014–2026 trajectory of Linux eBPF verification (`kernel/bpf/verifier.c`), abstract-interpretation and refinement-type certificate checkers (`PREVAIL`, Abstraction-Carrying Code, `VeRefine`), verified JIT compilers (`Jitk`, `Jitterbug`, `CertrBPF`), hardware/SFI sandboxes (`SafeBPF`), and extralingual Rust kernel extensions (`Rex`), four structural invariants govern the Trusted Computing Base (TCB):

1. **Stateful Path-Pruning In-Kernel Analysis vs. Single-Pass Certificate Checking**:
   Linux's `bpf_check` (`kernel/bpf/verifier.c`, `states.c`, `backtrack.c`, `tnum.c`, `cnum.c`; 28,600+ lines at `torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`) embeds fixpoint discovery inside Ring 0 via symbolic path enumeration (`BPF_COMPLEXITY_LIMIT_INSNS = 1,000,000`), heuristic state-subsumption pruning (`is_state_visited` / `regsafe` in `states.c:505-607`), backward demand-driven precision tainting (`mark_chain_precision` / `backtrack_insn` in `backtrack.c:265-550`), and four-stage cross-domain interval/bitmask reduction (`reg_bounds_sync` in `verifier.c:2118-2135`). Bugs in either cross-domain abstract transformers (`CVE-2020-8835`, `CVE-2021-3490`) or state-pruning precision backtracking (`CVE-2023-2163`) yield arbitrary Ring-0 read/write primitives. Decoupling fixpoint/type inference (`PREVAIL` PLDI 2019 WTO fixpoint iteration over `SplitDBM` Zones; `VeRefine` OOPSLA 2025 flow-sensitive refinement types with slack variables and `r_ghost`) into an untrusted user-space producer reduces the in-kernel checker to a **single linear pass $O(|V| + |E|)$ over basic-block or cutpoint certificates** with zero fixpoint iteration and zero path-pruning state machinery (`pcc_ebpf_single_pass_soundness`, `untrusted_fixpoint_producer_soundness`, `relational_packet_cert_single_pass_soundness`).
2. **Certificate Checking Still Requires Machine-Checked Transfer Soundness**:
   Eliminating in-kernel fixpoint search eliminates `is_state_visited` / `backtrack_insn` bugs (`certificate_checker_rejects_cve2023_2163_exploit`), **but does not protect against bugs in the checker's own abstract instruction transformers (`transferInstr#`) or subsumption relation (`subsumes#`)**. If a single-pass certificate checker's transformer contains a `CVE-2020-8835`-style 32-bit `tnum`/interval synchronization bug, an attacker can craft a false certificate that the single-pass checker accepts while concrete execution escapes the sandbox (`buggy_tnum_sync_breaks_certificate_checker`). Shrinking the checker to a single-pass validator is essential because it makes machine-checked proofs of `TransferSound` and `SubsumesSound` tractable in Coq or Lean 4 (`foundational_verified_checker_impossibility_of_exploit`, `Agni` CAV 2023, `CertrBPF` CAV 2022/2024).
3. **The Post-Verification Bytecode Rewrite and JIT Lowering Gap**:
   After `do_check_main` succeeds and frees `env->explored_states` (`verifier.c:21409`), Linux's `bpf_check` mutates `prog->insnsi` through **10+ unverified post-verification bytecode rewrite passes** in `kernel/bpf/fixups.c` (`bpf_remove_fastcall_spills_fills`, `bpf_optimize_bpf_loop`, `sanitize_dead_code`, `bpf_convert_ctx_accesses`, `bpf_do_misc_fixups`, `bpf_opt_subreg_zext_lo32_rnd_hi32`, `bpf_fixup_call_args`, `bpf_jit_blind_constants`) before invoking architecture-specific JIT compilers (`arch/*/net/bpf_jit_comp*.c`). An unverified post-check rewrite (`post_verification_rewrite_breaks_safety`) or a single `ALU32` sign-extension JIT bug (`jitterbug_style_alu32_sign_ext_jit_bug`, modeling Linux RV64 JIT bug `1e692f09e091` found by `Jitterbug`) invalidates a 100% sound pre-rewrite certificate. Closing this gap requires either checking certificates **after** all bytecode rewrites (`post_rewrite_recheck_soundness`) and lowering via a verified JIT (`Jitterbug` / `CertrBPF`), or composing machine-checked simulation theorems across both rewrite and JIT stages (`verified_ebpf_end_to_end_pipeline_soundness`).
4. **Instrumentation Boundary Hazards in SFI (`SafeBPF`) and Extralingual Rust Unwinding (`Rex`)**:
   Primary-source inspection of `SafeBPF` (`SafeBPF.patch@710b33fe3cecb2624e4b1e4a2653692e3dc57638`) and `Rex` (`rex-rs/rex@9188a85bc40b54c98d661d512648f9efa1310f2b`) revealed three concrete soundness hazards that are mechanized and repaired in `support/EbpfCertificateKernelsAndVerifiedJits.lean`:
   - In **`SafeBPF`**, `gen_or_mask(p, s)` (`include/linux/bpf_sandbox.h:2030-2035`) computes `(uintptr_t)p & ~((1 << (msb(s)+1)) - 1 - s)`. In `kernel/bpf/arraymap.c:2593-2608` (and `kernel/bpf/hashtab.c:3576-3581`), `array->value` for multi-page arrays (e.g. `valueBase = 0x9000`, `size = 0x2000`) is only 4 KB page-aligned (`0x1000`), not `size`-aligned. Consequently, `gen_or_mask(0x9000, 0x2000)` rounds down to `0x8000`—the page holding `struct bpf_array` and `struct bpf_map`'s `ops` vtable—and SFI masking rewrites valid second-page array accesses (`0xa000`) directly onto `0x8000` (`safebpf_unaligned_or_mask_corrupts_header`). Enforcing the static alignment certificate `valueBase &&& and_mask = 0` or switching to base-relative offset masking `valueBase + (offset &&& and_mask)` eliminates this hazard (`safebpf_aligned_mask_soundness`).
   - In **`SafeBPF`'s JIT**, `map_reg_bitmap` (`arch/arm64/net/bpf_jit_comp.c:538-616`) is updated in a flow-insensitive linear scan without resetting or joining at basic-block boundaries, and `BPF_LDX` (`line 608`) marks scalar load destinations as map pointers (`safebpf_flow_insensitive_bitmap_unsound_and_cert_repair`). Attaching per-block pointer/scalar region tags from a flow-sensitive certificate (`checkSfiBlockTagCert`) eliminates both bugs.
   - In **`Rex`**, `rex_spinlock_guard` (`rex/src/spinlock.rs:19-55`) registers its panic cleanup entry (`entry.valid = 1`) **before** calling `ffi::bpf_spin_lock(lock)` in `new()`, and deregisters it (`entry.valid = 0`) **before** calling `ffi::bpf_spin_unlock(self.lock)` in `drop()`. Any fault or asynchronous unwind in those two windows either unlocks an unheld spinlock or leaks a held kernel spinlock (`rex_spinlock_registration_window_hazard`). Performing lock+register and unlock+deregister atomically inside the kernel helper transition restores soundness across all fault PCs (`rex_atomic_lock_registration_sound`).

## Applicability

The findings and mechanizations in this report apply to the following subjects and their architectural relationships:

- **Linux Kernel eBPF Subsystem (`torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`)**:
  Covers `kernel/bpf/verifier.c`, `kernel/bpf/states.c`, `kernel/bpf/backtrack.c`, `kernel/bpf/fixups.c`, `kernel/bpf/tnum.c`, `kernel/bpf/cnum.c`, `include/linux/bpf_verifier.h`, and `include/linux/tnum.h`, along with historical commits for `CVE-2020-8835` (`581738a681b6fa8fcff2fd9a6fe8f3e3b4b2f8d3` and fix `f2d67fec0b43edce8c416101cdc52e71145b5fef`), `CVE-2021-3490` (fix `049c4e13714ecbca567b4d5f6d563f05d431c80e`), `CVE-2023-2163` (fix `71b547f561247897a0a14f3082730156c0533fed`), and RV64 JIT `ALU32` zero-extension bug fix `1e692f09e091`.
- **Abstract-Interpretation & Refinement-Type Certificate Producers/Checkers**:
  - `PREVAIL` (`vbpf/prevail@b88da311df4d99175ca2d5fe91d9fe2a43fb11b7`, PLDI 2019 DOI `10.1145/3314221.3314590`): Bourdoncle WTO fixpoint iterator (`src/fwd_analyzer.cpp`) and local assertion checker (`src/crab/ebpf_checker.cpp`) over the `SplitDBM` Zone domain.
  - `VeRefine` (PACMPL 9 OOPSLA2 Article 410, Oct 2025, DOI `10.1145/3763799`): Flow-sensitive refinement type inference (`Alg. 3`) and linear-time $O(|I|)$ certificate checking over slack-variable pointer types and `r_ghost`.
  - Abstraction-Carrying Code (Albert et al., TACAS 2006, DOI `10.1007/978-3-540-31980-1_25`) and `Agni` (`agni-verification/agni`, CAV 2023 DOI `10.1007/978-3-031-37709-9_14`).
- **Verified eBPF / cBPF JIT Compilers and Virtual Machines**:
  - `Jitk` (Wang et al., USENIX OSDI 2014): Coq/CompCert verified cBPF-to-native compiler.
  - `Jitterbug` (`uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d`, USENIX OSDI 2020): Rosette/Serval specification and verification of Linux Arm32, Arm64, RV32, RV64, x86-32, and x86-64 eBPF JITs.
  - `CertrBPF` (`future-proof-iot/CertFC@75690097c946c555cc4ce1e69d13ef86dc738180`, CAV 2022 DOI `10.1007/978-3-031-13188-2_15` and CAV 2024 `hal-04762503`): Coq/CompCert verified `rBPF` verifier, dynamic memory-region checker (`check_mem`), and hybrid Thumb-2 `ALU32` JIT.
- **Hardware/SFI Defense-in-Depth & Extralingual Rust Kernel Extensions**:
  - `SafeBPF` (`SafeBPF.patch@710b33fe3cecb2624e4b1e4a2653692e3dc57638`, ACM CCSW 2024 / `arXiv:2409.07508`).
  - `Rex` (`rex-rs/rex@9188a85bc40b54c98d661d512648f9efa1310f2b`, USENIX ATC 2025).
- **Target Architecture Comparison (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**:
  All 23 theorems in `support/EbpfCertificateKernelsAndVerifiedJits.lean` are machine-checked in Lean `v4.34.1` with zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`, and zero `Quot.sound`.

---

## Findings

### 1. In-Kernel Stateful Abstract Interpretation vs. Certificate-Verifying eBPF

`Basis: source + execution + derived`

#### 1.1 Coupled Interval + Bitmask (`Tnum`) Domain & Four-Stage `reg_bounds_sync`
In `torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`, each register's abstract state (`struct bpf_reg_state` in `include/linux/bpf_verifier.h:38-168`) tracks a reduced product of:
- **Tristate bitmask (`struct tnum var_off` in `include/linux/tnum.h:11-14`)**: `(u64 value, u64 mask)` with invariant `(value & mask) == 0`, where `mask` marks unknown bits (`1`) and `value` marks known-`1` bits.
- **64-bit and 32-bit Signed/Unsigned Intervals (`struct cnum64 r64`, `struct cnum32 r32`, `{u,s}{64,32}_{min,max}_value`)**: `include/linux/cnum.h:42-80` represents signed and unsigned bounds via circular modular intervals `(base, size)` on $\mathbb{Z}/2^{64}\mathbb{Z}$ and $\mathbb{Z}/2^{32}\mathbb{Z}$.
- **Relational Scalar Aliasing & Precision Tracking (`u32 id`, `s32 delta`, `u32 parent_id`, `bool precise`)**: Tracks constant-offset scalar copies (`find_equal_scalars`) and backward demand-driven precision taint (`precise`).

After every ALU or conditional branch instruction, `reg_bounds_sync` (`kernel/bpf/verifier.c:2118-2135`) runs a four-step mutual reduction:
1. `__update_reg_bounds(reg)` (`verifier.c:2081-2090`): intersects `r64` with `[var_off.value, var_off.value | var_off.mask]` and `r32` with its low-32-bit projection, plus `tnum_step` singleton overlap narrowing (`verifier.c:2054-2078`).
2. `__reg_deduce_bounds(reg)` twice (`verifier.c:2126-2127`): transfers bounds across signed/unsigned/32-bit/64-bit views when an interval does not straddle the sign bit or 32-bit boundary.
3. `__reg_bound_offset(reg)` (`verifier.c:2104-2114`): intersects `reg->var_off` with `tnum_range(umin, umax)` and its low 32 bits with `tnum_range(u32_min, u32_max)`.
4. `__update_reg_bounds(reg)` a second time (`verifier.c:2129`).

#### 1.2 Concrete Mechanics of Historical Verifier Soundness CVEs
We mechanized three representative Linux verifier soundness vulnerabilities in Sections 1 and 2 of `support/EbpfCertificateKernelsAndVerifiedJits.lean`:

- **CVE-2020-8835 (`581738a681b6` -> fixed in `f2d67fec0b43`; `cve_2020_8835_subreg_bound_offset32_unsound`)**:
  Before dedicated `[u32_min, u32_max]` fields were added, `__reg_bound_offset32` refined the low 32 bits of `reg->var_off` by computing `tnum_range(reg->umin_value & 0xffffffff, reg->umax_value & 0xffffffff)`. When `umin = 0x1_0000_0000` ($2^{32}$) and `umax = 0x2_0000_0000` ($2^{33}$), masking both endpoints by `0xffffffff` collapsed the 32-bit range to `tnum_range(0, 0) = (0, 0)`, falsely proving that the low 32 bits of `reg` were identically `0` even for concrete value $x = 2^{32} + 1$ (`lo32 x = 1`).
- **CVE-2021-3490 (`2921c90d4718` -> fixed in `049c4e13714e`; `cve_2021_3490_alu32_and_missing_update_unsound`)**:
  In `scalar32_min_max_and`, `scalar32_min_max_or`, and `scalar32_min_max_xor`, the verifier returned early whenever `tnum_subreg_is_const(src_reg->var_off) && tnum_subreg_is_const(dst_reg->var_off)`, assuming the 64-bit handler `scalar_min_max_and` would see `src_known && dst_known` for the full 64-bit registers and call `__mark_reg_known`. When `dst_reg` had unknown upper-32 bits (`var_off = (0x1, 0xffffffff00000000)`, `u32_min = 1, u32_max = 1`) and `src_reg = 0x100000002` (`lo32 = 2`), `1 & 2 = 0` updated `var_off`'s low 32 bits to `0`, `scalar32_min_max_and` skipped updating `u32_min`, and `reg_bounds_sync` lowered `u32_max` to `0`, creating inverted bounds `u32_min = 1 > u32_max = 0`.
- **CVE-2023-2163 (`b5dc0163d8fd` -> fixed in `71b547f56124`; `unsound_pruning_cve2023_2163_style_exploit`)**:
  To avoid path explosion, `regsafe` (`kernel/bpf/states.c:549`) treats any checkpointed scalar register with `!rold->precise` as subsuming **any** incoming scalar register (`if (!rold->precise && exact == NOT_EXACT) return true;`). When a scalar `r6` later feeds pointer arithmetic (`r0 += r6`), `mark_chain_precision` walks `jmp_history` via `backtrack_insn` (`kernel/bpf/backtrack.c:265`) to mark `r6` and its constraining registers `precise = true`. Prior to `71b547f56124`, `backtrack_insn` propagated precision across `BPF_ALU | BPF_MOV | BPF_X` but **completely omitted `BPF_JMP | BPF_X`** (`if r6 <= r9 goto ...`). When path 1 had `r6 = 0, r9 = 8` and took `if r6 <= r9`, `r9` remained `precise = false` at the checkpoint, allowing path 2 (`r6 = 1024, r9 = 2048`) to be pruned as subsumed even though `1024 <= 2048` enters the branch and writes out of bounds at `r0 + 1024 >= mapSize (64)`.

#### 1.3 Single-Pass Certificate Checking (`PREVAIL`, `VeRefine`, and Foundational Transfer Soundness)
- **`PREVAIL` (`vbpf/prevail@b88da311df4d99175ca2d5fe91d9fe2a43fb11b7`, PLDI 2019)**:
  `InterleavedFwdFixpointIterator::run` (`src/fwd_analyzer.cpp:200-266`) builds a Bourdoncle Weak Topological Ordering (`wto_t _wto`) over the CFG, iterates with widening and narrowing (`_extrapolator.compute_fixpoint` at line 242) over relational Zones (`SplitDBM` in `EbpfDomain`), and produces an `InvariantMapPair{pre, error, post}` per basic block label. Local safety checking (`ebpf_domain_check` in `src/crab/ebpf_checker.cpp:141-154`) simply checks whether each block's pre-invariant entails its local `Assertion` guards (`ValidAccess`, `ValidDivisor`, `BoundedLoopCount`, `Comparable`, `Addable`, `ValidStore`, `TypeConstraint`, `ZeroCtxOffset`).
- **`VeRefine` (OOPSLA 2025, DOI `10.1145/3763799`)**:
  Replaces in-kernel abstract interpretation with a **flow-sensitive refinement type system** where user-space type inference (`Alg. 3` in §6) annotates each instruction/block with a typing environment $\Gamma : \mathcal{V} \to \mathcal{T}$ and region environment $\Delta$ over refined numeric types $\{ \nu : \text{num} \mid \nu = t_n \wedge \varphi \}$ and pointer types $\{ \nu : \rho \mid \text{offset}(\nu) = t_p \wedge \varphi \}$. Bounded **slack variables** $s_i \in [n, m]$ (`§4`, p. 410:6–8) and a ghost register $r_{\text{ghost}}$ with `T-Prop` (`§5`, p. 410:15) preserve relational packet bounds (`begin + s_0 + access_sz <= end`) across register overwrites without requiring polyhedral operations in the kernel checker.
- **Mechanized Soundness and Vulnerability Boundaries (`support/EbpfCertificateKernelsAndVerifiedJits.lean`, Sections 2 & 6)**:
  1. `certificate_checker_rejects_cve2023_2163_exploit` & `pcc_ebpf_single_pass_soundness`: A single-pass certificate checker `checkAbstractCertificate` rejects the false checkpoint certificate from `CVE-2023-2163` and guarantees `oobViolation = false` across all concrete executions (`runCfg prog fuel bid st`) without fixpoint iteration or `is_state_visited`.
  2. `untrusted_fixpoint_producer_soundness`: Even if the user-space producer (`untrustedProducer : CfgProg → Certificate`) uses an arbitrary buggy widening operator or heuristic solver, `checkAbstractCertificate` never admits an unsafe program provided the checker's own local block check is sound.
  3. `buggy_tnum_sync_breaks_certificate_checker` & `foundational_verified_checker_impossibility_of_exploit`: If the single-pass certificate checker's own `transferInstr#` contains the `CVE-2020-8835` 32-bit projection bug (`checkSingleBlockBuggy`), a crafted certificate (`cve2020_8835_certPre` on `cve2020_8835_certExploitBlock`) is accepted and triggers `oobViolation = true`. Proving `hCheckerSound` in Lean 4 / Coq makes such exploits mathematically impossible.
  4. `non_relational_interval_fails_on_dynamic_packet`, `l2_l3_l4_packet_parser_accepted`, & `relational_packet_cert_single_pass_soundness`: Non-relational interval certificates `[umin, umax]` fail on dynamic packet buffers `[pktBase, pktEnd)` (`nonRelIntervalPacketCheck = false`). By contrast, our single-pass relational certificate checker `checkRelPktCertificate` tracking `(RelRegType.PktPtr minOff maxOff, verifiedPktLen)` verifies variable-length L2 (14B Ethernet) + L3 (IPv4 with dynamic `ihl & 15`) + L4 (20B TCP) packet parsing (`l2_l3_l4_parser_prog`) in $O(|I|)$ time and guarantees `pktOobViolation = false` across all dynamic packet buffers.

---

### 2. The Post-Verification Bytecode Rewrite & Verified JIT Lowering Boundary

`Basis: source + execution + derived`

#### 2.1 Linux's Post-Verification Bytecode Rewrite Pipeline (`kernel/bpf/verifier.c` & `kernel/bpf/fixups.c`)
In `torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`, **after** `do_check_main` and `do_check_subprogs` complete and `env->explored_states` is freed (`verifier.c:21409`), `bpf_check` mutates `prog->insnsi` through the following unverified passes in `kernel/bpf/fixups.c`:
1. `bpf_remove_fastcall_spills_fills(env)` (`fixups.c:2659`): removes stack spills/fills around fastcall helpers and adjusts `stack_depth`.
2. `bpf_optimize_bpf_loop(env)` (`fixups.c:2611`): inlines `bpf_loop` helper calls into a 19-instruction loop template (`inline_bpf_loop` at `fixups.c:2547`) and increases `stack_depth` by 24 bytes.
3. `bpf_opt_hard_wire_dead_code_branches` / `bpf_opt_remove_dead_code` / `bpf_opt_remove_nops` (`fixups.c:589-662`) or `sanitize_dead_code` (`verifier.c:21433`): overwrites instructions not marked `insn_aux_data[i].seen` with `JA -1` (`goto pc - 1`).
4. `bpf_convert_ctx_accesses(env)` (`fixups.c:766-1069`): inserts program prologue/epilogue, inserts `BPF_ST_NOSPEC()`, expands every `PTR_TO_CTX` load/store into up to 16 instructions via `convert_ctx_access` (`fixups.c:966`) plus narrow-load shift/mask sequences, and rewrites `PTR_TO_BTF_ID` / `PTR_TO_MEM | MEM_RDONLY` accesses to `BPF_PROBE_MEM`. Notably, `convert_ctx_access` dispatches on `insn->off` alone, ignoring any offset added to `r1` (documented in `PREVAIL` `src/crab/ebpf_checker.cpp:431-436`).
5. `bpf_do_misc_fixups(env)` (`fixups.c:1533-2517`): marks/rewrites `BPF_ALU64` when `insn_no_def(insn)`, expands `BPF_DIV`/`BPF_MOD` into 2–7 instruction division-by-zero/overflow guards, inserts 4-instruction Spectre v1 branchless pointer masking (`BPF_ALU_SANITIZE` at `fixups.c:1753-1803` using `BPF_REG_AX`), expands `BPF_JCOND` (`may_goto`), and inlines map lookups (`ops->map_gen_lookup` at `fixups.c:1995-2025`, e.g. `array_map_gen_lookup`).
6. `bpf_opt_subreg_zext_lo32_rnd_hi32(env)` (`fixups.c:664-759`): inserts `BPF_ZEXT_REG` after instructions marked `aux[adj_idx].zext_dst` when `bpf_jit_needs_zext()` holds.
7. `bpf_fixup_call_args(env)` (`fixups.c:1487`) and `bpf_jit_subprogs(env)` (`fixups.c:1299-1452`): runs `bpf_jit_blind_constants` and invokes `bpf_int_jit_compile`.

#### 2.2 Verified JIT Lowering (`Jitk`, `Jitterbug`, `CertrBPF`) and End-to-End Composition
- **`Jitk` (OSDI 2014)**: Compiles stateless cBPF to CompCert Cminor/RTL and machine code via an intermediate abstract register machine (`Arm` IR).
- **`Jitterbug` (`uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d`, OSDI 2020)**: Verifies Linux's production eBPF JITs (Arm32, Arm64, RV32, RV64, x86-32, x86-64) against a per-instruction relational specification in Rosette/Serval, uncovering 16 bugs in merged Linux JITs (`src/jitterbug/README.md:19-34`) including the RV64 `ALU32` missing zero-extension bug (`1e692f09e091`) where `rv_addw` sign-extended bit 31 into bits `[63:32]`.
- **`CertrBPF` (`future-proof-iot/CertFC@75690097c946c555cc4ce1e69d13ef86dc738180`, CAV 2022 & CAV 2024)**: Proves end-to-end Coq/CompCert isolation of `rBPF` where static verification checks syntactic/CFG well-formedness (`src/certfc/isolation/VerifierInv.v:40-120`), dynamic `check_mem` guards memory loads/stores against `bpf_mrs`, and `jit_alu32` lowers `ALU` blocks to Arm Thumb-2.
- **Mechanized Theorems (`support/EbpfCertificateKernelsAndVerifiedJits.lean`, Section 3)**:
  - `post_verification_rewrite_breaks_safety`: `preRewriteProg` passes `checkAbstractCertificate = true` and executes safely (`oobViolation = false`), but after unverified `rewriteProgUnverified` clobbers `R6`, execution hits `oobViolation = true` (which post-rewrite certificate re-checking immediately catches and rejects).
  - `post_rewrite_recheck_soundness` & `verified_rewrite_simulation_soundness`: Prove the two sound architectures for bytecode rewrites (re-checking certificates on `R(P)` vs. proving `RewriteSimulates P (R P)`).
  - `jitterbug_style_alu32_sign_ext_jit_bug`: Models Linux RV64 JIT bug `1e692f09e091`, proving `alu32_add(0x80000000, 0) >> 32` yields `0` (`oobViolation = false`) under eBPF bytecode semantics but `0xffffffff` (`oobViolation = true`) under `rv_addw` sign-extension.
  - `verified_ebpf_end_to_end_pipeline_soundness`: Composes `InductiveCertInvariant P C`, `RewriteSimulates P (R P)`, and `JitSimulates (R P) M_native` to prove `NativeRing0Safe M_native st_init`.

---

### 3. Hardware/SFI Defense-in-Depth (`SafeBPF`) and Extralingual Rust Extensions (`Rex`)

`Basis: source + execution + derived`

#### 3.1 `SafeBPF` (`SafeBPF.patch@710b33fe3cecb2624e4b1e4a2653692e3dc57638`)
- **Unaligned `gen_or_mask` Header-Aliasing Bug (`safebpf_unaligned_or_mask_corrupts_header`)**:
  In `include/linux/bpf_sandbox.h:2030-2035`, `gen_or_mask(p, s)` computes `(uintptr_t)p & ~(((1UL << (msb(s) + 1)) - 1) - s)`. For $s = 2^k$, this equals `p & ~(s - 1)`, which is only equal to `p` when `p` is naturally aligned to $s$. In `kernel/bpf/arraymap.c:2593-2608`, `data` is 4 KB page-aligned (`0x8000`), `struct bpf_array` occupies `[0x8000, 0x9000)`, and `array->value` starts at `0x9000`. When `total_elem_size = 0x2000` (8 KB), `gen_or_mask(0x9000, 0x2000)` rounds down to `0x8000` (`data`), and SFI masking `(addr & 0x1fff) | 0x8000` rewrites valid second-page array accesses (`0xa000`) to `0x8000`, overwriting `struct bpf_array` and `struct bpf_map.ops`. The same misalignment occurs in `kernel/bpf/hashtab.c:3576-3581` (`value = l->key + round_up(map->key_size, 16)`).
- **Flow-Insensitive `map_reg_bitmap` Bug (`safebpf_flow_insensitive_bitmap_unsound_and_cert_repair`)**:
  In `arch/arm64/net/bpf_jit_comp.c:538-616` (and `arch/x86/net/bpf_jit_comp.c:1176-1197`), `SafeBPF` updates a single `map_reg_bitmap` linearly across `for (i = 0; i < prog->len; i++)` without resetting or joining at basic-block boundaries, and `BPF_LDX` (`line 608`) calls `bitmap_set(map_reg_bitmap, dst, 1)` when loading a scalar from a map pointer. In `safebpfBranchPollutionProg`, Block 1 sets `R6 := R0` (`MapSandbox`) and exits, polluting `map_reg_bitmap[R6] = 1` for Block 2 (reachable only from Block 0's `else` edge where `R6 = PrivateSandbox`) and mis-masking Block 2's private stack store with `.MapSandbox`.
- **Mechanized Repairs (`safebpf_aligned_mask_soundness` & `checkSfiBlockTagCert`)**:
  Enforcing `checkAlignedSfiCert` (`valueBase &&& and_mask = 0 ∧ headerPage + 4096 ≤ valueBase`) or switching to base-relative offset masking `sfiBaseOffsetMask valueBase and_mask offset = valueBase + (offset &&& and_mask)` eliminates header aliasing even for unaligned `valueBase = 0x9000`. Attaching per-block `RegTagState` certificates (`checkSfiBlockTagCert`) eliminates both the cross-branch bitmap pollution and the `BPF_LDX` scalar mis-tagging.

#### 3.2 `Rex` (`rex-rs/rex@9188a85bc40b54c98d661d512648f9efa1310f2b`)
- **Spinlock Registration/Deregistration Window Hazard (`rex_spinlock_registration_window_hazard`)**:
  In `rex/src/spinlock.rs:19-55`, `rex_spinlock_guard::new` calls `CleanupEntries::register_cleanup` (`entryValid := true` at line 23) before `ffi::bpf_spin_lock(lock)` (`lockHeld := true` at line 29), and `drop` calls `CleanupEntries::deregister_cleanup` (`entryValid := false` at line 50) before `ffi::bpf_spin_unlock(self.lock)` (`lockHeld := false` at line 53). Any fault/panic between lines 23 and 29 causes `CleanupEntries::cleanup_all()` (`rex/src/panic.rs:121-129`) to unlock an unheld spinlock (`doubleOrUnheldUnlock = true`), and any asynchronous unwind between lines 50 and 53 leaves `lockHeld = true`.
- **Mechanized Atomic Repair (`rex_atomic_lock_registration_sound`)**:
  Making `(lockHeld, entryValid)` transition atomically (`rexAtomicAcquireAndRegister` and `rexAtomicReleaseAndDeregister`) preserves `lockHeld == entryValid` across all fault points (`BeforeAcquire`, `InsideCriticalSection`, `AfterRelease`), guaranteeing `lockHeld = false ∧ doubleOrUnheldUnlock = false` after `rexPanicCleanupAll`.

---

### 4. Empirical Complexity & Certificate-Size Probe (`support/ebpf_cert_complexity_probe.py`)

`Basis: execution + derived`

#### 4.1 Diamond Chain CFGs ($D_k$): Exponential Path Explosion ($2^k$) vs. Single-Pass Certificate Checking
In $D_k$, $k$ sequential diamond conditionals accumulate increments into `acc` before `r0 += acc; *(u8 *)(r0 + 0) = 0`. Because `r0 += acc` triggers `mark_chain_precision` on `acc`, Linux's `regsafe` (`states.c:549`) cannot merge `[1, 1]` and `[2, 2]` at any join block $J_i$, forcing $2^k$ path enumeration:

| Diamonds ($k$) | Static Blocks ($|V|$) | Static Insns ($|I|$) | Linux `bpf_check` Paths ($2^k$) | Linux `bpf_check` Insns Evaluated | Admitted under `1M` Limit? | User-Space WTO Producer Insns | In-Kernel Single-Pass Checker Insns | Cutpoint Cert Size (Bytes) | Checker Speedup vs. Linux |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **4** | 14 | 21 | 16 | 110 | Yes | 21 | **21** | 128 B | $5.2\times$ |
| **8** | 26 | 37 | 256 | 1,790 | Yes | 37 | **37** | 256 B | $48.4\times$ |
| **12** | 38 | 53 | 4,096 | 28,670 | Yes | 53 | **53** | 384 B | $540.9\times$ |
| **16** | 50 | 69 | 65,536 | 458,750 | Yes | 69 | **69** | 512 B | $6,648.6\times$ |
| **18** | 56 | 77 | 262,144 | **1,835,006** | **No (Rejected)** | 77 | **77** | 576 B | $23,831.2\times$ |
| **20** | 62 | 85 | 1,048,576 | **7,340,030** | **No (Rejected)** | 85 | **85** | 640 B | $86,353.3\times$ |
| **24** | 74 | 101 | 16,777,216 | **117,440,510** | **No (Rejected)** | 101 | **101** | 768 B | **$1,162,777.3\times$** |

#### 4.2 Nested Bounded Loops ($L_{d, N}$): Dynamic Unrolling ($N^d$) vs. WTO Producer ($3^d$) vs. Single-Pass Checker ($O(d)$)

| Loop Depth & Bound $(d, N)$ | Static Blocks ($|V|$) | Static Insns ($|I|$) | Linux `bpf_check` Unrolled Insns | Admitted under `1M` Limit? | User-Space WTO Fixpoint Insns | In-Kernel Single-Pass Checker Insns | Cutpoint Cert Size (Bytes) | Speedup vs. Linux Unrolling | Speedup vs. WTO Producer |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **(1, 100)** | 5 | 10 | 604 | Yes | 22 | **10** | 32 B | $60.4\times$ | $2.2\times$ |
| **(2, 100)** | 8 | 16 | 60,004 | Yes | 76 | **16** | 96 B | $3,750.3\times$ | $4.8\times$ |
| **(3, 50)** | 11 | 22 | 750,004 | Yes | 238 | **22** | 192 B | $34,091.1\times$ | $10.8\times$ |
| **(3, 100)** | 11 | 22 | **6,000,004** | **No (Rejected)** | 238 | **22** | 192 B | $272,727.5\times$ | $10.8\times$ |
| **(4, 30)** | 14 | 28 | **4,860,004** | **No (Rejected)** | 724 | **28** | 320 B | $173,571.6\times$ | $25.9\times$ |
| **(4, 50)** | 14 | 28 | **37,500,004** | **No (Rejected)** | 724 | **28** | 320 B | **$1,339,285.9\times$** | **$25.9\times$** |

---

### 5. Summary of Lean 4 Mechanization (`support/EbpfCertificateKernelsAndVerifiedJits.lean`)

`Basis: execution + derived`

All **23 theorems** in `support/EbpfCertificateKernelsAndVerifiedJits.lean` compile under Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with **zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`, and zero `Quot.sound`**:

| Section | Theorem Name | Formal Statement & Significance | Axioms |
| :--- | :--- | :--- | :--- |
| **Sec 1** | `cve_2020_8835_subreg_bound_offset32_unsound` | Masking `umin = 2^32` and `umax = 2^33` by `0xffffffff` in `__reg_bound_offset32` collapses `u32_max` to `0`, excluding concrete witness `2^32 + 1` (`lo32 = 1`). | `[propext]` |
| **Sec 1** | `cve_2021_3490_alu32_and_missing_update_unsound` | Early return in `scalar32_min_max_and` when both 32-bit subregs have known `tnum` masks (`lo32 = 1` & `lo32 = 2`) but `dst` has unknown upper-32 mask leaves `u32_min = 1 > u32_max = 0`. | `[propext]` |
| **Sec 2a** | `unsound_pruning_cve2023_2163_style_exploit` | `regsafeBuggy_CVE_2023_2163` prunes incoming branch `(r6=1024, r9=2048)` against checkpoint `(r6=0, r9=8 imprecise)`, admitting `cve2023_2163_prog` which hits `oobViolation = true`. | `[propext]` |
| **Sec 2b** | `certificate_checker_rejects_cve2023_2163_exploit` | Single-pass `checkAbstractCertificate` rejects `cve2023_2163_prog` under the false checkpoint certificate. | `[propext]` |
| **Sec 2b** | `pcc_ebpf_single_pass_soundness` | Parametric induction over `fuel`: any CFG `prog` and certificate `cert` satisfying `InductiveCertInvariant` executes with `oobViolation = false` for all steps. | `[propext]` |
| **Sec 2c** | `untrusted_fixpoint_producer_soundness` | For any arbitrary/buggy user-space fixpoint producer `untrustedProducer`, `checkAbstractCertificate prog (untrustedProducer prog) initAbs = true` guarantees concrete memory safety. | `[propext]` |
| **Sec 2d** | `buggy_tnum_sync_breaks_certificate_checker` | If the single-pass checker's own `transferInstr#` has the CVE-2020-8835 bug, `checkSingleBlockBuggy` accepts `cve2020_8835_certExploitBlock` which triggers `oobViolation = true`. | `[propext]` |
| **Sec 2e** | `foundational_verified_checker_impossibility_of_exploit` | When `checkAbstractCertificate` is backed by a machine-checked `hCheckerSound` proof, `¬∃ prog cert fuel, checkAbstractCertificate prog cert initAbs = true ∧ oobViolation = true`. | `[propext]` |
| **Sec 3a** | `post_verification_rewrite_breaks_safety` | `preRewriteProg` passes `checkAbstractCertificate = true` and is safe (`oobViolation = false`), but after unverified `rewriteProgUnverified`, execution hits `oobViolation = true` (caught by post-rewrite recheck). | `[propext]` |
| **Sec 3b** | `post_rewrite_recheck_soundness` | Running `checkAbstractCertificate` on the post-rewrite program `R(P)` guarantees concrete safety of `R(P)` even if `R` is unverified. | `[propext]` |
| **Sec 3b** | `verified_rewrite_simulation_soundness` | Pre-rewrite certificate acceptance + `RewriteSimulates P (R P)` guarantees concrete safety of `R(P)`. | `[propext]` |
| **Sec 3c** | `jitterbug_style_alu32_sign_ext_jit_bug` | Models Linux RV64 JIT bug `1e692f09e091`: `alu32_add(0x80000000, 0) >> 32` is `0` (`oobViolation = false`) in bytecode but `0xffffffff` (`oobViolation = true`) under `rv_addw` sign-extension. | `[propext]` |
| **Sec 3d** | `verified_ebpf_end_to_end_pipeline_soundness` | End-to-end composition: `InductiveCertInvariant P C ∧ RewriteSimulates P (R P) ∧ JitSimulates (R P) M_native ⟹ NativeRing0Safe M_native st_init`. | `[propext]` |
| **Sec 4a** | `safebpf_aligned_sfi_contains_verifier_escape` | When `base = 0x8000` is aligned to `size = 0x1000`, `sfiMaskAddr` confines rogue address `0xdeadbeef` inside `[base, base + size)`. | `[propext]` |
| **Sec 4a** | `safebpf_unaligned_or_mask_corrupts_header` | Models `SafeBPF.patch` `arraymap.c:2593-2608`: for `valueBase = 0x9000` and `size = 0x2000`, `safebpfGenOrMask` rounds down to `0x8000` (`headerPage`), aliasing valid second-page access `0xa000` onto `struct bpf_array`. | `[propext]` |
| **Sec 4b** | `rex_synchronous_cleanup_releases_all_locks` | Synchronous panics inside a `rex_spinlock_guard` critical section or after normal drop leave `lockHeld = false` and `doubleOrUnheldUnlock = false`. | **none (`0 axioms`)** |
| **Sec 4b** | `rex_spinlock_registration_window_hazard` | Unwinding in the `register_cleanup` -> `bpf_spin_lock` window causes `doubleOrUnheldUnlock = true`, and unwinding in the `deregister_cleanup` -> `bpf_spin_unlock` window leaks `lockHeld = true`. | **none (`0 axioms`)** |
| **Sec 5a** | `safebpf_aligned_mask_soundness` | Static certificate obligation `checkAlignedSfiCert` (`valueBase &&& and_mask = 0 ∧ headerPage + 0x1000 ≤ valueBase`) guarantees `sfiMaskAddr` is strictly disjoint from `headerPage`, and `sfiBaseOffsetMask valueBase and_mask offset = valueBase + (offset &&& and_mask)` is sound even for unaligned `valueBase = 0x9000`. | `[propext]` |
| **Sec 5b** | `safebpf_flow_insensitive_bitmap_unsound_and_cert_repair` | Proves a concrete counterexample (`safebpfBranchPollutionProg`) where `SafeBPF`'s flow-insensitive single-pass `map_reg_bitmap` (`bpf_jit_comp.c:538-616`) misclassifies `R6` across a branch and where `BPF_LDX` (`line 608`) tags a scalar load as a map pointer; proves `checkSfiBlockTagCert` eliminates both hazards. | `[propext]` |
| **Sec 5c** | `rex_atomic_lock_registration_sound` | Replacing `Rex`'s split user-space `entry.valid = 1; bpf_spin_lock(lock)` with atomic helper-side lock+register transitions (`rexAtomicAcquireAndRegister`, `rexAtomicReleaseAndDeregister`) preserves `lockHeld == entryValid` across all fault PCs (`BeforeAcquire`, `InsideCriticalSection`, `AfterRelease`), eliminating both unheld-unlock and leaked-lock hazards. | **none (`0 axioms`)** |
| **Sec 6a** | `non_relational_interval_fails_on_dynamic_packet` | Any non-relational interval abstraction `(r_pkt, r_end)` covering two dynamic packet buffers `[0x1000, 0x1040]` and `[0x9000, 0x9040]` fails `nonRelIntervalPacketCheck r_pkt r_end 14 = false`. | `[propext]` |
| **Sec 6b** | `l2_l3_l4_packet_parser_accepted` | Single-pass relational certificate checker `checkRelPktCertificate` (`RelRegType.PktPtr minOff maxOff`, `verifiedPktLen`) verifies variable-length L2 (14B Ethernet) + L3 (IPv4 with dynamic `ihl & 15`) + L4 (20B TCP) packet parsing (`l2_l3_l4_parser_prog`) in $O(|I|)$ without path explosion. | `[propext]` |
| **Sec 6b** | `relational_packet_cert_single_pass_soundness` | Universal soundness theorem: for any packet parser CFG `prog` and relational certificate `cert` satisfying `InductiveRelPktCertInvariant`, multi-step execution `runPktCfg prog fuel bid st` is free of out-of-bounds packet reads (`pktOobViolation = false`) across all dynamic `[pktBase, pktEnd)` buffers. | `[propext]` |

---

## Boundaries

- **Known not to apply (Unverified Single-Pass Certificate Checkers)**:
  Switching from stateful path-pruning symbolic execution (`bpf_check`) to a single-pass certificate checker (`checkAbstractCertificate`) does **not** by itself eliminate vulnerabilities in per-instruction abstract transformers (`buggy_tnum_sync_breaks_certificate_checker`). Soundness against adversarial certificates requires machine-checked proofs of `TransferSound` and `SubsumesSound` (`foundational_verified_checker_impossibility_of_exploit`).
- **Known not to apply (Pre-Rewrite Verification without Rewrite Simulation or Post-Rewrite Recheck)**:
  A valid certificate `(P, C)` checked on pre-rewrite eBPF bytecode does **not** guarantee memory safety of the executed kernel image if unverified post-verification rewrites (`bpf_convert_ctx_accesses`, `bpf_do_misc_fixups`, `bpf_optimize_bpf_loop`) or unverified JIT passes mutate instructions afterward (`post_verification_rewrite_breaks_safety`, `jitterbug_style_alu32_sign_ext_jit_bug`).
- **Not examined (Hardware Microarchitectural Transient Execution Beyond Spectre v1 ALU Masking)**:
  While we inspected Linux's Spectre v1 pointer masking (`BPF_ALU_SANITIZE` in `kernel/bpf/fixups.c:1753-1803`) and `BPF_ST_NOSPEC()`, hardware microarchitectural side channels (e.g., BHB/Spectre-v2 branch predictor poisoning across eBPF helper calls) were not mechanized.
- **Not examined (ARM64 MTE Tag-Granule Overflows in `SafeBPF`)**:
  Our `SafeBPF` formalization in Sections 4a and 5a–5b covers software fault isolation (`CONFIG_BPF_SANDBOX_SFI`). Under `CONFIG_BPF_SANDBOX_MTE`, ARM64 MTE enforces 16-byte tag granules (`BPF_MTE_TAG_SANDBOX`) rather than power-of-2 bitmasks, which avoids the `gen_or_mask` power-of-2 alignment bug but permits up to 15 bytes of intra-granule overflow when an object size is not a multiple of 16 bytes.

---

## Evidence

1. **Linux Kernel eBPF Verifier and Post-Check Fixups (`torvalds/linux@0fcb05b72344f40806cbe810de8872f1698bf053`, observed `2026-11-02`)**:
   - `include/linux/tnum.h:11-14`, `include/linux/cnum.h:42-80`, `include/linux/bpf_verifier.h:38-168`: `struct tnum`, `struct cnum64`/`cnum32`, and `struct bpf_reg_state`.
   - `kernel/bpf/verifier.c:2054-2135`: `__update_reg_bounds`, `__reg_bound_offset`, and four-stage `reg_bounds_sync`.
   - `kernel/bpf/states.c:505-607`: `regsafe` and `is_state_visited` (`!rold->precise` pruning shortcut at line 549).
   - `kernel/bpf/backtrack.c:265-550`: `backtrack_insn` and `mark_chain_precision`.
   - `kernel/bpf/verifier.c:21409-21501` and `kernel/bpf/fixups.c:589-2689`: post-verification rewrite pipeline (`bpf_remove_fastcall_spills_fills`, `bpf_optimize_bpf_loop`, `bpf_convert_ctx_accesses`, `bpf_do_misc_fixups`, `bpf_opt_subreg_zext_lo32_rnd_hi32`, `bpf_fixup_call_args`, `bpf_jit_subprogs`).
   - Historical CVE commits in `torvalds/linux`: `581738a681b6fa8fcff2fd9a6fe8f3e3b4b2f8d3` and `f2d67fec0b43edce8c416101cdc52e71145b5fef` (`CVE-2020-8835`); `049c4e13714ecbca567b4d5f6d563f05d431c80e` (`CVE-2021-3490`); `71b547f561247897a0a14f3082730156c0533fed` (`CVE-2023-2163`).
2. **`PREVAIL` (`vbpf/prevail@b88da311df4d99175ca2d5fe91d9fe2a43fb11b7`, PLDI 2019 DOI `10.1145/3314221.3314590`, observed `2026-11-02`)**:
   - `src/fwd_analyzer.cpp:200-266`: `InterleavedFwdFixpointIterator::run` WTO fixpoint iteration with widening/narrowing.
   - `src/crab/ebpf_checker.cpp:141-154` & `431-436`: local assertion checking `ebpf_domain_check` and context-offset rewrite note.
3. **`VeRefine` (PACMPL 9 OOPSLA2 Article 410, Oct 2025, DOI `10.1145/3763799`, observed `2026-11-02`)**:
   - Sections 4–6 (`pp. 410:6–410:19`, Figs. 3, 5, 7, Alg. 3): flow-sensitive refinement type rules (`T-PtrNum`, `T-PktLD`, `T-AssumePtr`, `T-Prop`, `T-Sub`), slack variables $s_i \in [n, m]$, and ghost register $r_{\text{ghost}}$.
4. **`Jitk` (USENIX OSDI 2014), `Jitterbug` (`uw-unsat/jitterbug@78d1e75ad506498b585fbac66985ff9d9d05952d`, USENIX OSDI 2020), and `CertrBPF` (`future-proof-iot/CertFC@75690097c946c555cc4ce1e69d13ef86dc738180`, CAV 2022 DOI `10.1007/978-3-031-13188-2_15` & CAV 2024 `hal-04762503`, observed `2026-11-02`)**:
   - `src/jitterbug/README.md:19-34` and OSDI 2020 Table 4: 16 Linux kernel JIT bugs found and fixed, including RV64 `ALU32` missing zero-extension (`1e692f09e091`), Arm64 `PROLOGUE_OFFSET` (`b0f47fd7fd93`), and x86-64 jump offset (`1f9a2ea02776`).
   - `src/certfc/isolation/VerifierInv.v:40-120` and `Verifylet.v`: Coq specification of `rBPF` static control-flow verification and dynamic `check_mem` spatial isolation.
5. **`SafeBPF` (`SafeBPF.patch@710b33fe3cecb2624e4b1e4a2653692e3dc57638`, ACM CCSW 2024 / `arXiv:2409.07508`) and `Rex` (`rex-rs/rex@9188a85bc40b54c98d661d512648f9efa1310f2b`, USENIX ATC 2025, observed `2026-11-02`)**:
   - `SafeBPF.patch`: `include/linux/bpf_sandbox.h:2030-2050` (`gen_or_mask`, `gen_and_mask`), `kernel/bpf/arraymap.c:2593-2608` (page-aligned `array->value` at `data + 0x1000`), `kernel/bpf/hashtab.c:3576-3581` (`htab_map_lookup_elem`), `arch/arm64/net/bpf_jit_comp.c:538-616` and `arch/x86/net/bpf_jit_comp.c:1176-1197` (flow-insensitive `map_reg_bitmap` and `BPF_LDX` scalar mis-tagging).
   - `rex-rs/rex`: `rex/src/panic.rs:24-156` (`CleanupEntries::cleanup_all`, `__rex_check_stack`, `__rex_handle_timeout`), `rex/src/base_helper.rs:13-42` (`termination_check!`), `rex/src/spinlock.rs:19-55` (`rex_spinlock_guard::new` and `drop`).
6. **Preserved Package Artifacts (`support/`, observed `2026-11-02`)**:
   - `support/EbpfCertificateKernelsAndVerifiedJits.lean`: 2,057-line Lean 4.34.1 mechanization containing all 23 zero-axiom theorems.
   - `support/ebpf_cert_complexity_probe.py` and `support/ebpf_cert_complexity_probe_results.json`: deterministic complexity and certificate-size probe over diamond chains $D_k$ ($k \in [4, 24]$) and nested bounded loops $L_{d, N}$.

---

## Revalidation

To revalidate the machine-checked proofs and empirical probe results in this package:

1. **Verify all 23 Lean 4 theorems and their zero-axiom footprint**:
   ```bash
   lean reports/ebpf-certificate-verifying-kernels-and-verified-jits-2014-2026/support/EbpfCertificateKernelsAndVerifiedJits.lean
   ```
   Confirm that `lean` (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`) exits with code `0` and that all 23 `#print axioms` outputs depend only on `[propext]` or `does not depend on any axioms` (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`, zero `Quot.sound`).

2. **Re-run the empirical complexity and certificate-size probe**:
   ```bash
   python3 reports/ebpf-certificate-verifying-kernels-and-verified-jits-2014-2026/support/ebpf_cert_complexity_probe.py
   ```
   Confirm that `support/ebpf_cert_complexity_probe_results.json` is regenerated identically (`D_18` reaches `1,835,006` instructions under Linux path enumeration vs. `77` instructions and `576` bytes for the single-pass cutpoint certificate checker).
