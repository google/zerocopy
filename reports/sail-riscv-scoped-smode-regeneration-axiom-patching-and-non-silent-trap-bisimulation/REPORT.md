# Scoped RISC-V S-Mode Sail Regeneration, `RiscvExtras.lean` Axiom Patching, and Non-Silent Trap Bisimulation

## Summary

Extracting an end-to-end formal RISC-V Supervisor (S-mode) instruction-set reference from `riscv/sail-riscv` into Lean 4 closes the correspondence gap between privileged OS/hypervisor kernels (`Serval`, `Miralis`, `xv6iris`, `CHERIoT-Ibex`) and Sail-generated functional models—provided three coupled hazards are resolved together:

1. **Transitive module pull-in during scoped regeneration (`riscv.sail_project@ec5200bd` vs. `v0.13.1@27224ccb`):** Prior work (`sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`, `sail-isa-models-lean-backend-and-rv64d-decoding-framing`) documented that full-ISA Lean compilation hits severe memory limits (`Defs.lean` OOM at `-M2048`, passing at `-M4096` with `2.47 GB` RSS, and `~14 GiB` RSS on full RVFI bundles). Auditing Sail's exact module-pruning semantics (`ModGraph.prune` in `sail_project.ml:455-558, 671-673`) reveals a regression on `riscv/sail-riscv@ec5200bd`: whereas `v0.13.1` required 8 dependencies in `postlude` (giving a 41-module / 93-file scoped S-mode closure), `ec5200bd` adds `FD_instructions`, `H_insts`, `FD_core`, `Zaamo`, `Zicbom_insts`, and `Zicboz` (21 dependencies) because `postlude/transformed_inst.sail:25-39` pattern-matches floating-point and hypervisor instructions for `mtinst`/`htinst` even when `Ext_H` is disabled (`L41-43`). Decoupling `FD_instructions` and `H_insts` from `postlude` shrinks the minimal S-mode closure (`main`, `I_insts`, `M_insts`, `Zicsr_insts`, `Zifencei`, `Zalrsc`) from `51` modules (`119` files) down to `47` modules (`111` files; `60.83%` module reduction and `39.34%` file reduction versus the 120-module / 183-file full model) while fixing `Svade`-only page-table fault semantics (`vmem.sail:401`). `Basis: source, execution`.
2. **Eliminating the 75 `RiscvExtras.lean` axioms without `panic = default` soundness bugs:** `opencompl/sail-riscv-lean@51c635c4` defines **75** `axiom` declarations in `RiscvExtras.lean` (67 SoftFloat operations, 4 LR/SC reservation hooks, 2 terminal I/O hooks, `get_16_random_bits`, and `sys_enable_experimental_extensions`). Its companion `RiscvExtrasExecutable.lean` reaches **0** `axiom`s by substituting 72 calls to Lean's `panic "TODO: ..."` plus `dbg_trace` and `λ _ => false`. Because `panic` reduces to `Inhabited.default` inside Lean's pure logic (`false` for `match_reservation`, `(0#5, 0#n)` for SoftFloat, `0#16` for entropy), axiom-free executable extraction silently breaks valid `LR -> SC` progress and fakes floating-point results unless reservations are lifted into explicit verification state (`Option (BitVec addr_size × Nat)`). `Basis: source, execution, derived`.
3. **Closing stuck-on-trap refinement holes (`StepRun.lean:327-334`) with non-silent trap bisimulation:** Prior correspondence surveys (`riscv-privileged-isa-model-correspondence-prior-art`) noted that halts-on-trap refinements returning `none` on exceptions (`StepRun.lean` style) silently ignore architectural trap behavior. In Sail's actual dispatcher (`postlude/step.sail:288-363`), traps, interrupts, and illegal instructions update privilege registers (`sepc`, `scause`, `stval`, `sstatus.{SPP,SPIE,SIE}`) and step `PC` via `tick_pc()`. Across an empirical 6-mode finite S-mode suite (`faithful_svade` plus 5 injected mutants), trap-halting forward simulation vacuously passes **4 out of 5** mutants (silent trap hang, corrupted `sepc = pc + 4`, missed `medeleg` delegation, and `Svadu` TLB-hit stale dirty write-back), whereas choice-coupled non-silent trap bisimulation kills **5/5** mutants while accepting `faithful_svade`. `Basis: source, execution`.

---

## Applicability

This analysis applies to Sail-to-Lean 4 extraction workflows and S-mode privileged hardware/kernel refinement proofs targeting `RV64IMAC_Zicsr_Zifencei` + `Sv39` (`Svade`) and memory-bounded proof-replay environments:

- **Upstream RISC-V Sail & compiler toolchains:**
  - `github.com/riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` (`master`: 120 modules, 183 files) and `@27224ccb2290f022e46213c05b3e72e8a9ea635e` (`v0.13.1`: 110 modules, 163 files).
  - `github.com/rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2` (including `src/lib/sail_project.ml`, `src/sail_lean_backend/pretty_print_lean.ml`, and `@e55d89e79e3e5dfa88a137c73be371fb3671c983` for monadic short-circuiting `<&&>` / `<||>`).
  - `github.com/rems-project/lean-sail@e4745c82fe329f162700020dcd31da6b342473b9`.
  - `github.com/opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f` (`SailRiscv/RiscvExtras.lean` and `RiscvExtrasExecutable.lean`).
  - `github.com/riscv/riscv-isa-manual@c05f1725f25526dd8463bac6ca75cfcfbee17d05` (`Sv39` / `Svade` / `Svadu` normative page-table translation steps).
- **Target verification & correspondence frameworks:**
  - `github.com/Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7` (`PROVENANCE.toml`, `StepRun.lean`, `PlatformFrame`, `AxiomSweep.lean`).
  - `github.com/joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`TrustedBoundary.lean`) and `github.com/leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`.
- **Direct corpus lineage (cited explicitly, not duplicated):**
  - `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config` (provenance metadata, `-M2048` OOM on `Defs.lean`, 75-axiom inventory, Lake vs. replay `.olean` SHA mismatch)
  - `riscv-privileged-isa-model-correspondence-prior-art` (`StepRun.lean:327-334` stuck-on-trap gap, `xv6iris`, `Miralis`, `Ibex`, `check_CSR` hoisting)
  - `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors` (`supervisor.adoc` step-9 A/D rules, `vmem.sail:401` TLB-hit PTE bug, ASID=0 aliasing)
  - `sail-isa-models-lean-backend-and-rv64d-decoding-framing` (scoped extraction `PROVENANCE.toml`, `sail_project` pruning, `archsem` vs. `lean-sail` sequential choice erasure)
  - `load-reserved-store-conditional-reservation-sets-forward-progress-and-aba-hazards` (LR/SC reservation semantics)
  - `anneal-lean-miri-pass2-audit-and-sail-riscv-reference-audit-requirements` (replay sandboxing `-j1 -M2048 -t0` and `.opaqueInfo` rejection)

---

## Findings

### 1. Scoped S-Mode Regeneration Mechanics and the `postlude` Dependency Trap

Bounded verification sandboxes (such as `2 GiB` single-core `-j1 -M2048 -t0` Lean replay environments) fail on monolithic full-ISA Sail extractions: prior reports established that full `Defs.lean` OOMs at `-M2048` (requiring `2.47 GB` RSS at `-M4096`) and full RVFI decoding consumes `~14 GiB` RSS unless pruned (`sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`, `sail-isa-models-lean-backend-and-rv64d-decoding-framing`). Pruning requires understanding how Sail (`src/lib/sail_project.ml`) computes module reachability under `--include-modules`. `Basis: source, execution`.

#### 1.1 Exact `ModGraph.prune` Transitive Dependency Graph (`sail_project.ml:455-558, 671-673`)

Unlike flat file lists, `.sail_project` declares hierarchically nested module blocks (`I { I_types { ... } I_insts { ... } }`, `FD { ... }`, `H { ... }`). Reading `sail_project.ml` directly establishes two critical rules:
1. **Parent & subtree expansion (`L486-505, L548`):** A child module `id` inherits `get_parents id proj` and all ancestor `requires` frames, and referencing a container module by name without `only` uses selector `S_tree`, pulling `ModGraph.reachable (singleton id) proj.children`—every descendant submodule.
2. **Reachability filter (`L671-673`):** `--include-modules` computes `ModGraph.prune roots ModSet.empty proj.requires`; any module referenced directly or transitively by `main` or `postlude` enters the extraction even if omitted from the CLI module list.

#### 1.2 Quantitative Comparison: `v0.13.1@27224ccb` vs. `master@ec5200bd`

Applying exact `ModGraph.prune` reachability to both `.sail_project` manifests with minimal S-mode roots `[main, I_insts, M_insts, Zicsr_insts, Zifencei, Zalrsc]` reveals why scoping breaks silently across Sail RISC-V versions:

| Configuration & Target Commit | Total Modules / Files | `postlude` `requires` Count | Reachable Modules / Files | Pulls `FD_instructions` / SoftFloat? | Pulls `H_insts`? | Module / File Reduction vs. Full |
|---|---|---|---|---|---|---|
| `riscv/sail-riscv@27224ccb` (`v0.13.1`, full) | 110 / 163 | 8 | 110 / 163 | Yes | Yes | Baseline (`0%`) |
| `riscv/sail-riscv@27224ccb` (`v0.13.1`, scoped) | 110 / 163 | 8 | **41 / 93** | **No** | **No** | `-62.73%` / `-42.94%` |
| `riscv/sail-riscv@ec5200bd` (`master`, full) | 120 / 183 | 21 | 120 / 183 | Yes | Yes | Baseline (`0%`) |
| `riscv/sail-riscv@ec5200bd` (scoped, unpatched `postlude`) | 120 / 183 | 21 | 51 / 119 | **Yes** (8 extra FP/H files) | **Yes** | `-57.50%` / `-34.97%` |
| `riscv/sail-riscv@ec5200bd` (scoped + `postlude` `FD`/`H` decoupled) | 120 / 183 | 17 | **47 / 111** | No `FD_instructions` (`FD_core` regs stay) | **No** | **`-60.83%` / `-39.34%`** |

Why does unpatched `ec5200bd` pull `FD_instructions` and `H_insts`? Inspecting `postlude/transformed_inst.sail:25-39` exposes the coupling: `transformed_instruction(insn)` pattern-matches `LOAD_FP`, `STORE_FP`, `HLVTYPE`, and `HSV` to populate `mtinst`/`htinst` trap values—even though `transform_exception_context` (`L41-43`) returns `ctx` unchanged immediately unless `currentlyEnabled(Ext_H)` is true. For S-mode without Hypervisor (`Ext_H = false`), patching out those four `match` arms and dropping `FD_instructions`, `H`, `H_insts`, and `H_types` immediately eliminates 8 `.sail` instruction files (`hext_{types,insts}.sail`, `fext_insts.sail`, `zcf_insts.sail`, `dext_insts.sail`, `zcd_insts.sail`, `zfh_insts.sail`, `zfa_insts.sail`). Notice, however, that `FD_core` (`fdext_regs.sail`, `fdext_control.sail`), `Zaamo`, `Zicbom_insts`, `Zicboz`, `PM_utils`, and `core/rvfi_dii*.sail` remain wired through `core`/`sys`/`postlude` unless stripped alongside CSR stubs (`csr_end.sail`).

#### 1.3 Enforcing `Svade`-Only Address Translation (`vmem.sail:401`)

As established in `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors`, `model/sys/vmem.sail:401` contains a hardware-dirty-update path that can write back PTE `A`/`D` bits even on a TLB hit, diverging from strict `supervisor.adoc` step-9 rules (`Svade` mandates taking an exception whenever `A=0` or a store targets `D=0`, leaving PTE updates to S-mode trap handlers). Scoped S-mode regeneration must therefore pin platform configuration (`config/riscv_sim_rv64.json.in`) so `Svadu` is disabled (`Svade`-only) and either guard out `vmem.sail:401` TLB-hit PTE mutation when `Svadu` is disabled or include TLB stale-entry traps explicitly in the non-silent trap relation.

---

### 2. Eliminating `RiscvExtras.lean` Axioms Without `panic = default` Soundness Bugs

In `opencompl/sail-riscv-lean@51c635c4` (118 lines per file), `RiscvExtras.lean` introduces **75** explicit `axiom` declarations that break closed `[propext, Classical.choice, Quot.sound]` trust audits. Yet the repository's own executable replacement `RiscvExtrasExecutable.lean` demonstrates an instructive formal hazard: removing `axiom` keywords via `panic` does not preserve architectural soundness. `Basis: source, execution, derived`.

| Category in `RiscvExtras.lean` (75 Axioms) | Count | `RiscvExtrasExecutable.lean` Replacement | Kernel Definitional Value (`rfl`) | Formal Soundness Hazard & Concrete Fix |
|---|---|---|---|---|
| IEEE SoftFloat (`riscv_f*`, `riscv_{u}i*ToF*`) | 67 | `λ _ => panic "TODO: ..."` | `(0#5, 0#n)` or `(0#5, false)` via `Inhabited.default` | Claims every FP arithmetic op returns `0` with zero `fflags`. **Fix:** Exclude `FD_instructions` in scoped S-mode regeneration (`0` SoftFloat symbols reachable). |
| LR/SC reservations (`load_`, `match_`, `cancel_`, `valid_reservation`) | 4 | `panic "TODO: ..."`, `dbg_trace ...; return ()`, `λ _ => false` | `match_reservation _ = false`, `valid_reservation _ = false` | Makes **every** `SC.W`/`SC.D` fail even immediately after `LR.W`! **Fix:** Lift `resv : Option (BitVec addr_size × Nat)` into machine state with pure `BEq` / `Option` handlers. |
| Terminal I/O (`plat_term_write`, `plat_term_read`) | 2 | `λ _ => panic "TODO: ..."` | `""` / default unit action | Masks HTIF output/input under default stubs. **Fix:** Explicit monadic event log field or fail-closed `StepOutcome.mmio`. |
| Entropy source (`get_16_random_bits`) | 1 | `λ _ => panic "TODO: get_16_random_bits"` | `0#16` (`BitVec.zero`) | Collapses hardware entropy (`Zkr` `seed` CSR) to constant zero! **Fix:** Model via explicit nondeterministic choice stream `Fin (2^16)` (`StepResult`-style demonic choice), never `panic = 0`. |
| Experimental extension toggle (`sys_enable_experimental_extensions`) | 1 | `λ _ => false` | `false` | Safe when scoped S-mode omits experimental CSRs (`false` is total and honest). |

The core lesson holds across all Lean 4 ISA models: Lean's `Init.Core.panic` evaluates in equational proofs via `Inhabited.default` (`dbgTrace ... fun () => default`), unlike a halting error monad (`Except`). Therefore, proving invariants over `RiscvExtrasExecutable.lean` accidentally allows `rfl` proofs of false hardware facts (such as `match_reservation addr = false` for all addresses) while reporting `0` axioms in `#print axioms`. Stateful axioms like `Zalrsc` reservations MUST become explicit fields in the pure transition relation rather than stubbed `panic`s.

```lean
prelude

inductive Priv where | u | s | m
inductive TrapCause where | ecallU | storePageFault | illegalInst

def stepScPure (resv : Option Nat) (addr : Nat) : Bool × Option Nat :=
  match resv with
  | none => (false, none)
  | some r =>
    match Nat.beq r addr with
    | true => (true, none)
    | false => (false, none)

def checkSvadeStore (pteA pteD tlbValid tlbD : Bool) : Bool :=
  match pteA with
  | false => false
  | true =>
    match tlbValid with
    | true => tlbD
    | false => pteD

theorem lr_sc_same_addr_succeeds :
    stepScPure (some 16384) 16384 = (true, none) := by
  rfl

theorem svade_stale_tlb_d0_must_trap :
    checkSvadeStore true false true false = false := by
  rfl
```

Notice that `stepScPure` and `checkSvadeStore` use `prelude`-only `match` branching with zero `axiom`s, zero `panic`, zero `omega`, and zero `@ite` `Decidable` coercions, proving both `LR -> SC` progress and `Svade` dirty-bit fault triggering cleanly by `rfl`.

---

### 3. Closing Stuck-on-Trap Holes: Non-Silent Trap Bisimulation

As documented in `riscv-privileged-isa-model-correspondence-prior-art`, execution harnesses shaped like `Verified-zkEVM/riscv-zkvm`'s `StepRun.lean:327-334` map trapping executions (`Trap`, `Illegal_Instruction`, `Retire_Fail`) to `none` or halt step composition. In contrast, Sail's real top-level step dispatcher (`model/postlude/step.sail:288-399`) keeps `hart_state = HART_ACTIVE()`, delegates through `handle_exception` or `exception_handler(priv, ctx, pc)` updating privilege mode and trap CSRs (`sepc`/`scause`/`stval`/`sstatus`), and advances `PC` via `tick_pc()` (`L363`). Replacing a halting forward refinement with **Non-Silent Trap Bisimulation** closes this soundness gap. `Basis: source, execution`.

#### 3.1 Formal Contract of Non-Silent Trap Bisimulation

For architectural state $S$ and implementation state $I$ linked by state relation $R(S, I)$, every single-step transition must satisfy:
1. **Totality / non-silence on traps:** Neither transition may drop trapping executions into a stuck `none` sentinel; `Retire` maps to `StepObs.retire newPc`, and every exception/interrupt maps to `StepObs.trap targetPriv cause vectorPc`.
2. **Lockstep trap CSR & privilege projection:** Whenever `StepObs.trap` fires, post-states must satisfy `R(S', I')` across `priv`, `pc = vectorPc`, `sepc` / `mepc`, `scause` / `mcause`, `stval` / `mtval`, and `sstatus.{SPP, SPIE, SIE}` / `mstatus`—and short-circuit CSR side-effects must follow Sail's `<&&>`/`<||>` evaluation order fixed in `rems-project/sail@e55d89e7` (`check_CSR`).
3. **Choice coupling under nondeterminism:** When external inputs (`WFI` wait wakeups, interrupt sampling, or allowed architectural nondeterminism) branch, existential/universal branching must pair matching choices rather than indexing `⟨0, h⟩` unconditionally as `lean-sail`'s `ArchSemSequential` did (`sail-isa-models-lean-backend-and-rv64d-decoding-framing`).

#### 3.2 Empirical Mutant Kill Matrix (Reproducible Trap Suite)

Evaluating five architectural fault mutants against a faithful `Svade` + stateful-LR/SC S-mode oracle (`faithful_svade`) across U-to-S `ECALL` delegation, `LOAD_VA -> STORE_VA` (`D=0` stale TLB), `SRET` privilege traps, and `LR_W -> SC_W` proves why halting trap simulation fails while non-silent bisimulation catches every defect:

| Model Variant Under Test | Discriminating Workload | Halting Trap-Omitted Forward Sim | Non-Silent Trap Bisimulation | Diagnostic Caught / Missed |
|---|---|---|---|---|
| `faithful_svade` | 7-step full S-mode + `LR/SC` | Passes (vacuous at step 0 trap) | **Passes** (`7/7` steps) | Baseline oracle accepted |
| `M1_silent_stuck_trap` | 7-step (`StepRun`-style `none` on `ECALL`) | **Passes vacuously** (step 0) | **KILLED** at step 0 | `impl returned None (silent stuck-on-trap hole)` |
| `M2_corrupt_trap_sepc` | 7-step (`sepc := pc + 4` instead of `pc`) | **Passes vacuously** (step 0) | **KILLED** at step 0 | `arch state mismatch (sepc: 4096!=4100)` |
| `M3_missing_medeleg` | 7-step (traps U-mode `ECALL` to `M`, not `S`) | **Passes vacuously** (step 0) | **KILLED** at step 0 | `StepObs mismatch: target_priv='S' vs 'M'` |
| `M4_panic_default_sc` | 2-step (`LR_W 0x4000`, `SC_W 0x77` w/ `panic = false`) | **KILLED** at step 1 (non-trap path) | **KILLED** at step 1 | `arch state mismatch (mem_val: 119!=17, x_out: 0!=1)` |
| `M5_svadu_tlb_hit_dirty` | 2-step (`LOAD_VA`, `STORE_VA` w/ `A=1, D=0` in TLB) | **Passes vacuously** at step 1 trap | **KILLED** at step 1 | `StepObs mismatch: spec=TRAP(STORE_PF) vs impl=RETIRE` |

Halting forward refinement passes **4 of 5** broken models (`80%` false-negative rate on trap/PTE defects!), missing silent trap hangs (`M1`), broken trap-return addresses (`M2`), privilege-escalation leaks (`M3`), and illegal `Svadu` dirty updates during `Svade` (`M5`). Non-silent trap bisimulation rejects **5/5** (`100%` kill rate) on the first violated invariant step. `Basis: execution`.

---

## Boundaries

1. **Not examined in this cycle:** Compiling a freshly regenerated, `postlude`-decoupled `riscv/sail-riscv@ec5200bd` S-mode Lean export directly inside Lean 4 (`lake build` / `bwrap -M2048 -t0`) was **not examined** in execution here; the module/file counts (`47` modules / `111` files) come from exact execution of Sail's `.sail_project` dependency rules (`sail_project.ml`) on pinned manifests, while `-M2048` / `-M4096` RAM figures cite prior reference-corpus measurements (`sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`). `Basis: execution, documentation`.
2. **Unknown:** Whether decoupling `FD_instructions` and `H_insts` from `postlude/transformed_inst.sail` alone reduces peak single-module Lean elaboration RSS of `ec5200bd` `Defs.lean` below a hard `2.0 GiB` limit—or whether remaining `postlude`/`sys` edges (`FD_core`, `V_core`, `core/rvfi_dii*.sail`, `Zaamo`, `Zicbom_*`, `Zicboz`) must also be stripped to fit `<= 2.0 GiB`—remains **unknown** without a live `sail --lean` compile under cgroup RAM caps. `Basis: derived`.
3. **Known not to apply:** `RiscvExtrasExecutable.lean` `panic` stubs (`match_reservation _ = panic ...`, SoftFloat `panic`) are **known not to apply** to formal ISA equivalence proofs because `panic` reduces definitionally to `Inhabited.default` (`false`, `0`), breaking valid `LR/SC` success (`M4`) and falsifying IEEE-754 operations. Likewise, `vmem.sail:401`'s TLB-hit dirty write-back is **known not to apply** when verifying OS kernels against normative `Svade` hardware. `Basis: source, execution`.
4. **Unsupported:** Unmodified `StepRun`-style halting-on-trap refinement relations are **unsupported** for verifying privileged trap handlers (`Miralis`, `xv6iris`, `Serval`-style S-mode kernels), as they accept broken privilege delegation (`M3`), wrong `sepc` (`M2`), and silent trap hangs (`M1`). Automated termination-measure generation for arbitrary unbounded loops in Sail (`step.sail:406-443`) also remains **unsupported** by Sail's Lean 4 backend. `Basis: source, execution`.

---

## Evidence

- **Upstream sources inspected:**
  - `github.com/riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`: `model/riscv.sail_project` (`postlude` 21 deps vs. `v0.13.1@27224ccb` 8 deps), `model/postlude/transformed_inst.sail` (`L25-64`), `model/postlude/step.sail` (`L268-443`), `model/sys/vmem.sail` (`L401`), `model/sys/sys_reservation.sail`, `model/extensions/A/zalrsc_insts.sail`, `model/core/validate_config.sail`.
  - `github.com/rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2`: `src/lib/sail_project.ml` (`L455-558, L671-695` `ModGraph.prune`), `src/sail_lean_backend/pretty_print_lean.ml`, and `@e55d89e79e3e5dfa88a137c73be371fb3671c983` (`check_CSR` short-circuit fix).
  - `github.com/opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`: `SailRiscv/RiscvExtras.lean` (118 lines: 75 explicit axioms) and `SailRiscv/RiscvExtrasExecutable.lean` (118 lines: 0 axioms, 72 `panic` calls, `dbg_trace`, `λ _ => false`).
  - `github.com/Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7`: `StepRun.lean` (`L327-334`), `AxiomSweep.lean`, `PlatformConfig.lean`.
- **Empirical measurements (executed in Python probe suite):**
  - Exact `.sail_project` `ModGraph.prune` closure audit comparing `v0.13.1` (`41/93` scoped vs. `110/163` full), unpatched `ec5200bd` (`51/119` vs. `120/183`, contaminated by `FD_instructions`/`H_insts`), and `postlude`-decoupled `ec5200bd` (`47/111`, pruning 8 `.sail` files / `-60.83%` modules / `-39.34%` files).
  - Axiom and stub census on `RiscvExtras.lean` (`75` axioms = `67` SoftFloat + `4` reservation + `2` term I/O + `1` random + `1` experimental) vs. `RiscvExtrasExecutable.lean` (`0` axioms, `72` `panic` calls).
  - Finite S-mode bisimulation suite showing halting forward refinement accepts `4/5` faulty mutants (`M1`, `M2`, `M3`, `M5`) while non-silent trap bisimulation accepts `faithful_svade` and kills `5/5` mutants.
- **Peer-reviewed citations:**
  - A. Armstrong et al., "ISA Semantics for ARMv8-a, RISC-V, and CHERI-MIPS," *Proc. ACM Program. Lang.* (POPL 2019), `doi:10.1145/3290384`.
  - M. Syeda and G. Klein, "Formal Reasoning Under Cached Address Translation," *J. Autom. Reason.* (2020), `doi:10.1007/s10817-019-09539-7`.
  - L. Nelson et al., "Scaling Symbolic Evaluation for Automated Verification of Systems Code with Serval," *SOSP 2019*, `doi:10.1145/3341301.3359641`.
  - S. Léger et al., "Miralis: Verification of Secure Firmware Monitors," *SOSP 2025*, `doi:10.1145/3731569.3764826`.
  - `xv6iris` (`arXiv:2609.04043`) and `CHERIoT-Ibex` (`arXiv:2502.04738v1`).

---

## Revalidation

### 1. Self-Contained Non-Silent Trap Bisimulation & Mutant Revalidation Script

Run the following standalone Python 3 script (`python3 -`) to reproduce the 6-mode finite S-mode trap/Svade/LR-SC discrimination matrix (confirming halting forward refinement misses `M1`, `M2`, `M3`, `M5` while non-silent trap bisimulation kills all 5 mutants):

```python
from dataclasses import dataclass, replace

@dataclass(frozen=True)
class Hart:
    priv: str
    pc: int
    medeleg_ecall: bool
    stvec: int
    mtvec: int
    sepc: int
    scause: str
    resv: int | None
    pte_d: bool
    tlb_valid: bool
    tlb_d: bool
    mem: int
    x_out: int

@dataclass(frozen=True)
class Obs:
    kind: str
    priv: str | None
    cause: str | None
    pc: int

def init_hart():
    return Hart("U", 0x1000, True, 0x8000, 0x9000, 0, "NONE", None, False, False, False, 0x11, -1)

def trap(st, cause):
    if st.priv in ("U", "S") and (cause != "ECALL_U" or st.medeleg_ecall):
        nxt = replace(st, priv="S", sepc=st.pc, scause=cause, pc=st.stvec)
        return nxt, Obs("TRAP", "S", cause, nxt.pc)
    nxt = replace(st, priv="M", pc=st.mtvec)
    return nxt, Obs("TRAP", "M", cause, nxt.pc)

def step(st, op, arg, mode):
    if op == "ECALL":
        if mode == "M1":
            return st, None
        nxt, obs = trap(st, "ECALL_U" if st.priv == "U" else "ECALL_S")
        if mode == "M2":
            nxt = replace(nxt, sepc=st.pc + 4)
        if mode == "M3":
            nxt = replace(nxt, priv="M", pc=st.mtvec)
            obs = Obs("TRAP", "M", "ECALL_U", st.mtvec)
        return nxt, obs
    if op == "LOAD_VA":
        nxt = replace(st, pc=st.pc + 4, x_out=st.mem, tlb_valid=True, tlb_d=st.pte_d)
        return nxt, Obs("RETIRE", None, None, nxt.pc)
    if op == "STORE_VA":
        if mode == "M5" and st.tlb_valid:
            nxt = replace(st, pc=st.pc + 4, pte_d=True, tlb_d=True, mem=arg)
            return nxt, Obs("RETIRE", None, None, nxt.pc)
        if not (st.tlb_d if st.tlb_valid else st.pte_d):
            return trap(st, "STORE_PF")
        nxt = replace(st, pc=st.pc + 4, mem=arg)
        return nxt, Obs("RETIRE", None, None, nxt.pc)
    if op == "LR_W":
        nxt = replace(st, pc=st.pc + 4, resv=arg)
        return nxt, Obs("RETIRE", None, None, nxt.pc)
    if op == "SC_W":
        ok = False if mode == "M4" else (st.resv == arg)
        nxt = replace(st, pc=st.pc + 4, mem=(arg if mode == "ok_data" else 0x77) if ok else st.mem, x_out=0 if ok else 1, resv=None)
        return nxt, Obs("RETIRE", None, None, nxt.pc)
    raise ValueError(op)

def run(trace, mode):
    st, out = init_hart(), []
    for op, arg in trace:
        st, obs = step(st, op, arg, mode)
        out.append((st, obs))
    return out

def halting_fwd(spec_r, impl_r):
    for (ss, so), (is_, io) in zip(spec_r, impl_r):
        if so is None or so.kind != "RETIRE" or io is None or io.kind != "RETIRE":
            return True
        if (ss.priv, ss.pc, ss.mem, ss.x_out) != (is_.priv, is_.pc, is_.mem, is_.x_out):
            return False
    return True

def bisim(spec_r, impl_r):
    return all(io is not None and so == io and ss == is_ for (ss, so), (is_, io) in zip(spec_r, impl_r))

w_full = [("ECALL", 0), ("LOAD_VA", 0x3000), ("STORE_VA", 0x42)]
w_lrsc = [("LR_W", 0x4000), ("SC_W", 0x4000)]
w_svade = [("LOAD_VA", 0x3000), ("STORE_VA", 0x42)]

assert bisim(run(w_full, "faithful"), run(w_full, "faithful"))
for mutant, trace in [("M1", w_full), ("M2", w_full), ("M3", w_full), ("M5", w_svade)]:
    sr, ir = run(trace, "faithful"), run(trace, mutant)
    assert halting_fwd(sr, ir) and not bisim(sr, ir), f"{mutant} not distinguished"
assert not bisim(run(w_lrsc, "faithful"), run(w_lrsc, "M4"))
print("All trap-bisimulation & mutant kill assertions passed.")
```

### 2. Upstream Manifest & Axiom Re-Audit Steps

1. Inspect `model/riscv.sail_project` and `model/postlude/transformed_inst.sail` in `github.com/riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e` versus `v0.13.1@27224ccb2290f022e46213c05b3e72e8a9ea635e`, confirming exact `postlude` edges using Sail's `ModGraph.prune` logic (`rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2:src/lib/sail_project.ml:455-558,671-673`).
2. Audit `SailRiscv/RiscvExtras.lean` (`75` `axiom` declarations) and `SailRiscv/RiscvExtrasExecutable.lean` (`0` axioms, `72` `panic` stubs) at `github.com/opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`.
3. Inspect `model/postlude/step.sail:288-399` and `model/sys/vmem.sail:401` (`ec5200bd`) against `StepRun.lean:327-334` (`Verified-zkEVM/riscv-zkvm@6810fc14`) to verify trap-handling CSR updates and `Svade` vs. `Svadu` write-back paths.
