# RISC-V Privileged-Architecture Model Correspondence: Prior Art Relating Hand-Written Models, Implementations, and Sail (riscv-zkvm, riscv-lean, xv6iris, Ibex/CHERIoT-Ibex, Miralis, and Gap Admissions)

## Summary

- **Central result (bounded `not found`).** Within the search scope in **Applicability**, no proof in any prover was found that relates a hand-written *software* RISC-V machine model to Sail (or another authoritative ISA model) for trap entry/return, CSR semantics, or Sv39 address translation. This is a statement about the examined artifacts and searches, not a claim that no such proof exists.
- **`Verified-zkEVM/riscv-zkvm` `SailEquiv`** (`6810fc14`, Lean v4.33.1) is the only mechanized hand-model↔Sail correspondence for RISC-V found. Its scope is user-level RV64IM executed in M-mode with bare translation and all PMP entries off:
  - The run-level theorem is a forward, success-only simulation against a hand-written one-instruction "Sail step" that skips fetch, decode and interrupt checks.
  - CSR instructions, `ECALL`/`EBREAK`/`FENCE`, `mret`/`sret` and Sv39 are outside it.
  - Hand-model traps are represented as getting stuck (`none`), and a probe shows the theorem's shape places no constraint on trap behaviour.
- **`opencompl/riscv-lean`** (`main` = `0e3365ac`) still relates only pure register-to-register operations. Nothing privileged is covered.
- **Closest privileged artifacts.** None of them is a hand-model↔Sail theorem at a trust level admitting only `propext`/`Classical.choice`/`Quot.sound`:
  1. **`mit-pdos/xv6iris`** (Lean 4.32.2 + iris-lean, arXiv 2609.04043) verifies an S-mode kernel and user programs directly over a *forked* Sail RV64 model:
     - Covered: Sv39, PMP, a TLB, traps/interrupts, `sret`/`satp`/`sfence.vma`, and a non-coherent instruction-fetch model for `fence.i`.
     - Its user-mode layer `Xv6.userProof : USER` is a separation-logic contract proved against Sail.
     - Its axiom baseline admits `bv_decide` certificate axioms.
  2. **Ibex and CHERIoT-Ibex**: the RTL is model-checked for trace equivalence with Sail. The flow covers RV32 M/U mode, PMP, CSRs, IRQs, and illegal-instruction and fetch-error traps, with listed holes. It goes through an unverified Sail→SMT→SystemVerilog translation, and neither core has an MMU.
  3. **Miralis**: Kani bounded model checks compare its emulation of `mret`/`sret`/`wfi`/`sfence.vma`, CSR access, trap injection, interrupt dispatch and PMP against `softcore-rv64`:
     - `softcore-rv64` is an unverified Sail→Rust translation of patched sail-riscv. It has no page-table walk, a stubbed `flush_TLB`, and 552 `todo!`/`unimplemented!` sites.
     - The harnesses' symbolic state gives all GPRs one shared value, and likewise all `pmpaddr`s.
- **Explicit gap statements in primary sources:**
  - Komodo: its ARM model "must be fully trusted".
  - ACE-RISCV: `(* TODO: have file for translated sail specs and then link up with this *)`.
  - Serval: its ISA interpreter is "trusted to be correct" and tested with user-mode `riscv-tests` only; `mret`/`sret` are `notimplemented`.
  - seL4 `l4v` RISCV64: `sfence`, `hwASIDFlush` and `setVSpaceRoot` are unspecified `machine_op_lift` operations, with no TLB or CSR state.
  - Islaris RISC-V: traces are pinned to `cur_privilege = Machine`, PMP off and `MPRV = 0`.
- **Extraction hazard on the privileged path.** In both inspected Sail→Lean RV64 extractions, `check_CSR` has the pre-`e55d89e7` shape `pure ((← a) && … (← b) …)`. Lean executes `b` even when `a` is false, whereas Sail short-circuits. The fix is in `rems-project/sail` `e55d89e7` but not in release `0.20.3`.

## Applicability

**Question addressed.** What prior art establishes a correspondence between some RISC-V model and Sail RISC-V (or another authoritative ISA model), and how far does it reach into the privileged architecture? Here that means S/M-mode trap entry and return, CSR read/write legality, delegation, PMP, Sv39 translation and TLB maintenance (`sfence.vma`), and `fence.i`. For each artifact the report records:

- the two related models;
- the prover or checker;
- the statement shape and direction;
- how stateful Sail effects and platform hooks are treated;
- the assumptions or holes;
- the axiom or trust footprint.

**Search scope behind the `not found` result.**

- *Primary-source inspection* covered:
  - the repositories at the revisions in `REPORT.json`;
  - the Serval, Komodo and CHERIoT-Ibex papers (PDF text);
  - arXiv abstract pages for 2502.04738, 2502.06609 and 2609.04043.
- *Web searches* (2026-11-20) looked for hand-written-model↔Sail proofs of traps, CSRs or Sv39 in Lean, Coq/Rocq, Isabelle, HOL4, ACL2, Rosette and Kani, 2019–2026. Candidates named in those searches and checked at least at repository level:
  - ACE-RISCV;
  - Keystone (via Serval and Sailor);
  - riscv-coq/bedrock2;
  - HOL4 L3 RISC-V;
  - CHERI-RISC-V Sail prover snapshots;
  - CHERIoT;
  - the Ibex formal flow;
  - xv6iris.
- *Not examined in source:* Kami, TestRIG/RVFI-DII, Forvis/Flute, GRIFT, Kestrel's ACL2 RISC-V model, CertiKOS's machine model, the Sail↔Spike tandem flow, the Morello Isabelle proofs, and seL4's RISC-V binary-verification ISA model. A proof hidden in one of these, in an unindexed repository, or in a paper not surfaced by the searches would not have been found.

**Subjects and their relationship.** The subjects are independent prior-art artifacts compared along one axis: what they relate to Sail and how. The Sail compiler commit `e55d89e7` and release `0.20.3` matter only for Finding 9. The Lean `v4.34.1` toolchain and `rustc` were used only to run the standalone probes. Probe P1 characterises the riscv-zkvm theorem *shape*, not the correctness of its proofs. Probe P4 characterises Rust array-repeat semantics as used in Miralis's harness.

**Derived design conclusions** (Finding 10) are stated for a generic "small kernel-reducible trusted RV64 S-mode model" whose fidelity is to be established by correspondence to Sail. They are labelled `derived`.

**Related packages** (context only; this report does not depend on them): `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config` (extraction provenance, the 75 extern axioms, configuration), `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors` (what the privileged spec permits and what Spike/QEMU/Sail do), `lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs` (`bv_decide`/`native_decide` axiom mechanism and native-free proof techniques).

All evidence was observed on 2026-11-20.

## Findings

### 1. Central negative result and what comes closest

Basis: source + documentation + derived (synthesis of Findings 2–9).

| Artifact | What is related to what | Checker | Privileged coverage | Trust/axiom footprint |
|---|---|---|---|---|
| riscv-zkvm `SailEquiv` (`6810fc14`) | hand-written computable RV64IM `step` ↔ scoped Sail Lean extraction | Lean 4.33.1 kernel | none: M-mode, bare translation, PMP off; CSR/`ecall`/`mret` excluded | `propext`, `Classical.choice`, `Quot.sound` + 4 Sail platform axioms |
| riscv-lean (`0e3365ac`) | Sail `execute_*` ↔ pure `BitVec 64` functions | Lean 4.32.2 | none (ALU only) | 7 `bv_decide` uses |
| xv6iris (`5cb9df99`) | xv6 kernel/user binaries ↔ forked Sail RV64 (direct, no hand model) | Lean 4.32.2 + iris-lean | Sv39, PMP, TLB, traps, IRQs, `sret`, `satp`, `sfence.vma`, `fence.i` | std. 3 axioms + `bv_decide` certificate family (README) |
| Ibex (`f5b14392`) | RTL ↔ Sail RISC-V (lowRISC forks) via Sail→SV | Jasper or Yosys+rIC3 | M/U, PMP (4 regions), CSRs (some unchecked), IRQs, illegal-instr/fetch-error traps; no MMU | trusted Sail→SV translation, model checker |
| CHERIoT-Ibex (`56357b6d`) | RTL ↔ "minor variant" of CHERIoT Sail via Sail→SMT→SV | Jasper | as Ibex + CHERI; no MMU | same |
| Miralis (`f5ab1955`) | Rust emulation code ↔ Sail→Rust translation (`softcore-rv64`) | Kani (bounded) | `mret`/`sret`/`wfi`/`sfence.vma`, CSR read/write, trap injection, IRQ dispatch, PMP check; no PTW | unverified translator, patched Sail, narrowed symbolic state |
| Serval, Komodo, seL4 RISCV64, ACE-RISCV | hand-written models with no Sail tie | — | various | models trusted (explicitly stated) |

No row relates a hand-written software model to Sail for privileged behaviour.

### 2. `Verified-zkEVM/riscv-zkvm` `SailEquiv`: scope and theorem shape

Basis: source + documentation + execution (P1, P2). Revision `6810fc14d9c40373101321cefaec59df8d82e3e7`, equal to upstream `main` on 2026-11-20; `lean-toolchain` `leanprover/lean4:v4.33.1`. Package `sail-isa-models-lean-backend-and-rv64d-decoding-framing` describes the extraction architecture; this section records the privileged-scope facts.

1. **Mode invariant: M-mode, bare translation, PMP off.** Load/store theorems consume `BareModeInv` (`RiscvZkvm/Rv64/SailEquiv/VmemReduction.lean:956-971`). Its fields include:
   ```lean
   h_priv : s.regs.get? Register.cur_privilege = some Privilege.Machine
   h_mprv : _get_Mstatus_MPRV mst = 0#1
   h_pmm  : _get_Seccfg_PMM msec = 0#2
   h_off  : ∀ i : Nat, pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (cfgs[i]!)) = PmpAddrMatchType.OFF
   ```
   Per-instruction theorems export `PlatformFrame s s'` (`StateRel.lean:347-365`). It asserts that `cur_privilege`, `mstatus`, `mseccfg`, `pmpcfg_n`, `pmpaddr_n`, `pma_regions`, `misa` and `htif_tohost_base` are unchanged, and that byte memory only grows. So by construction no covered step changes privilege, a CSR or the translation mode. The state relation `StateRel` (`StateRel.lean:264`) couples only the 32 integer registers and 8-aligned doublewords of memory. `StateRelPC` (`:295`) adds the PC.
2. **Excluded instructions.** `Instr.simulable` (`StepSim.lean:81-83`):
   ```lean
   def Instr.simulable : Instr → Bool
     | .ECALL | .EBREAK | .FENCE | .MV .. | .LI .. | .NOP | .CSRS .. => false
     | _ => true
   ```
   The theorem-facing dispatcher maps generated `CSRReg`/`CSRImm` constructors to `execute_ILLEGAL` (`InstrMap.lean:99`). `MRET`, `SRET`, `WFI` and `SFENCE_VMA` are dispatched to Sail, but the hand model has no counterpart instruction. `docs/validation.md:117-120`: "`Instr`'s only CSR form is `CSRS`, the ZisK accelerator call `csrrs x0, csr, rs1`; general M-mode CSR access, `mtvec` setup and `mret` are not modeled at all."
3. **The "Sail step" in the run theorem is hand-written.** `StepRun.lean:77-81`:
   ```lean
   noncomputable def sailStep (si : SailInstr) : SailM Unit := do
     let pc ← readReg Register.PC
     set_next_pc (pc + 4)
     let _ ← executeSupported si
     tick_pc ()
   ```
   Its docstring states that the fetch-side default is the only part of the vendored fetch modelled. It also says the decode tie between the hand model's `code` map and Sail's byte memory "is roadmap item P7 and explicitly out of scope". Sail's real step loop (interrupt dispatch, fetch translation and PMP, decode, `minstret`, timer tick) is therefore not related. `docs/validation.md:133-137`: "No theorem relates `RiscvZkvm.Interpreter.decode` to `RiscvZkvm.Sail.Functions.encdec_backwards` … the proof extraction is `noncomputable`, so the Sail decoder does not evaluate."
4. **Direction and trap treatment.** `sailStep_run_sim` (`StepRun.lean:327-334`) states, under fetch, `simulable` and side-condition premises:
   ```lean
   RunInv lo hi sRv sSail → … → step sRv = some sRv' →
     ∃ sSail', runSail (sailStep si) sSail = some ((), sSail') ∧ RunInv lo hi sRv' sSail'
   ```
   `sailStepN_run_sim` (`StepRun.lean:381-387`) iterates it; `jalr_sideCond_satisfiable` (`:460`) is a non-vacuity witness for the `JALR` side condition. The hand model represents traps as `none`, e.g. `Execution.lean:344-348`:
   ```lean
   | some (.LD rd rs1 offset) =>
     let addr := s.getReg rs1 + signExtend12 offset
     if isValidDwordAccess addr then some (execInstrBr s (.LD rd rs1 offset))
     else none  -- trap: invalid dword memory access
   ```
   No theorem relates a hand-model `none` to Sail's trap behaviour (exception cause, `mepc`/`mtval`, `mtvec` target). Probe P1 (Init-only Lean) proves two things for this success-only forward shape:
   - it holds for a hand model stuck everywhere, for every reference and relation (`trapEverywhere_fwd`);
   - it holds for a model that agrees with a total reference on all non-trapping steps but is stuck where the reference jumps to a handler (`hand_fwd`, `hand_ref_disagree_on_trap`).

   A "no silent trap" clause (`step s = none → tstep t = none`) rejects both models.
5. **Counts and axioms.** There are 66 distinct theorem names matching `*_sail_equiv*`. Stripping `_step`/`_of_present` variants leaves 51 base instructions, matching README's "51 per-instruction" (P2). The allowed axiom set is `scripts/AxiomSweep.lean:47-52`:
   ```lean
   [ `propext, `Classical.choice, `Quot.sound,
     `load_reservation, `match_reservation, `plat_term_write, `sys_enable_experimental_extensions ]
   ```
   So the library sits four Sail platform axioms above the three standard ones. No `sorry`, `native_decide` or `bv_decide` use was found in `SailEquiv/` by grep (P2). `#print axioms` was not run.
6. **Validation evidence is user-ISA only.** The executable Lean emulator passed "all 50 selected `rv64ui-p-*` ELF tests" (`docs/validation.md:56`). The project explicitly does not claim "that the proof-oriented and executable backend modes are identical" (`:66`), and `riscv-tests` images do not run on the hand model (`:109-127`). No privileged (`rv64mi`/`rv64si`) tests are mentioned.

### 3. `opencompl/riscv-lean` at `main`

Basis: source + execution (P2).

- Upstream `main` was `0e3365ac7b670d79d70e9b4a8b7fba782607c44f` (2026-11-02, "add operations (#61)"). Compared with `7c6b500c1744f40d928fb131125cd06edf9f4fce`, it changes only `RISCV/Instructions.lean`, `SailPure.lean`, `SailPureToInstructions.lean` and `SailToRV64.lean` (+55/−10 lines). The changes:
  - adds `brev8` (`zbkb_brev8_eq`);
  - changes `shamt : BitVec 5` to `BitVec 6` in `shiftiop_slli_eq`, `shiftiop_srli_eq`, `shiftiop_srai_eq` and `zbb_rori_eq`;
  - keeps the same `Lean_RV64D` dependency (`opencompl/sail-riscv-lean@11d8fa21`) and toolchain v4.32.2.
- `^theorem` counts: 77 (`SailToRV64.lean`) + 104 (`SailPureToInstructions.lean`) at `7c6b500c`, and 78 + 106 at `0e3365ac`. `bv_decide` occurrences: 1 + 4 at `7c6b500c`, 1 + 6 at `0e3365ac`.
- No `mret|sret|satp|ecall|csrr|translateAddr` occurs in `RISCV/` at `0e3365ac`. Loads, stores, control flow, CSRs and system instructions remain unrelated.

### 4. `mit-pdos/xv6iris`: privileged proofs directly over (forked) Sail

Basis: documentation (in-repo README and design notes) + source (manifests, file inventory, audit baseline). The proofs were not built. Revision: `lean` branch HEAD `5cb9df992c45829f6210b3e4176962d7b7a4c408` (2026-11-06); the archived Rocq development is branch `rocq`. Paper: arXiv 2609.04043, "Extending concurrent separation logic to the hardware level to verify the xv6 OS kernel on RISC-V with AI agents" (2026-09-03).

1. **What is proved** (README §"What is proved", lines 24-45). Three closed theorems:
   - `Xv6.xv6FsAdequacy_closed` (system adequacy including crash durability);
   - `Xv6.userProof : USER`: "every user instruction the decoder can produce behaves as the kernel's user-execution contract says (retire, trap into the kernel, or fault), over Sv39 translation, PMP and the TLB; it has no hypotheses" (line 33ff);
   - `Xv6.unionAdequacyClosed` (user programs).

   Toolchain `leanprover/lean4:v4.32.2`; iris-lean `728a17140939e49af9236f7cb0d037da9ec52435`. The framework tree includes `MachCSL/UTrap.lean`, `UTlb.lean`, `UWalk.lean`, `UIcacheFencei.lean`, `WpSmodeSfence.lean`, `WpSmodeSatp.lean`, `WpSmodeSret.lean`, `WpSmodeIntr.lean` and `WpMmodeMret.lean`.
2. **Model provenance and deltas.** `tools/regen_sail_model.sh:25-60` says the model comes from fork `zeldovich/sail-riscv` branch `xv6`, pinned at `SAIL_RISCV_REV=070832a1e4b086f0c6f7635de54cc2b4cfd66993`. "Its deltas against riscv/sail-riscv upstream are the atomic PTE A/D-bit update and the AK_ifetch/AK_ttw tagging of fetches and page-table walks at the concurrency interface". The fork was not fetched or diffed.

   The model is compiled by Sail built from `rems-project/sail` `5745ea9e` plus the short-circuit fix. `5745ea9e` itself lacks `e55d89e7` (P2). `model/Xv6Extras.lean` is "the one hand-written file", realising the reservation hooks, `plat_term_write` and the experimental-extensions flag. `vendor/lean-sail` redefines `PreSailM` as a free monad over events so harts and devices interleave (README lines 129-130).
3. **Instruction-fetch and TLB non-coherence modelled beyond sequential Sail** (`claude-notes/design/icache.md`, lines 14-31):
   - Each hart has an instruction view `itv`. A fetch reads at any view `itv ≤ tvn ≤ length log` "so there is NO store forwarding: a hart's own store to code is not fetched until its own `fence.i`".
   - "`fence.i` raises `itv` past the hart's data floor AND past the drain of its own stores".
   - "Page-walk reads (`AK_ttw`) stay on the DATA arm: PTW reads are coherent, and TLB non-coherence is the sfence layer's business".
   - Hardware observation: on the VisionFive 2's U74 a rewritten instruction is fetched stale until `fence.i`.
4. **Axioms.** README line 43: "Their axioms are Lean's `propext`, `Classical.choice`, `Quot.sound` and `bv_decide` certificates, and nothing else". `tools/audit/baseline.json` pins axioms "outside the `<decl>._native.bv_decide.ax_*` certificate family (which is counted, shape-checked, and not pinned by name)". The `Xv6.userProof` entry allows `[propext, Classical.choice, Quot.sound]` plus opaques `LeanRV64D.Functions.xv6_resv_is_valid`, `LeanRV64D.Functions.xv6_resv_matches` and `MachCSL.bootImageSealed`.
5. **Relevance.** xv6iris does not relate a hand-written machine model to Sail. The kernel and user binaries are verified against the (forked) Sail model itself. The `USER` contract plays the role of an abstraction of Sail's U-mode behaviour, but it is a separation-logic specification proved against Sail. It is not a standalone reference-model correspondence.

### 5. RTL ↔ Sail by model checking: Ibex and CHERIoT-Ibex

Basis: documentation (in-repo READMEs; paper).

- **Ibex** (`lowRISC/ibex@f5b1439295048c6eead73ad4ef8a55cc564e7d6f`, `dv/formal/README.md`) presents itself as "End-to-End Formal Verification of Ibex Trace Equivalence against the Sail Model".
  - Tooling: Cadence Jasper, or Yosys + rIC3. The reference is built with the Sail compiler from `lowrisc/sail` branch `lowrisc` and `lowrisc/sail-riscv`.
  - Claim: "(up to base case) Ibex is trace equivalent to the Sail (i.e. where the Sail main function is run in a loop)".
  - Per-instruction checks cover RF address/write-enable, RF data, "the CSRs" and the PC, plus checks for "IRQs, illegal instructions and fetch errors".
  - Configuration: 4 PMP regions, `RV32MFast`, `RV32BNone`.
  - "Proof Holes" (lines 170-190):
    1. some CSRs are unchecked (`ex_is_checkable_csr`), after which "anything can happen";
    2. bus errors assumed absent;
    3. no NMIs or fast IRQs;
    4. debug mode forbidden;
    5. `ResetAll` and no clock gating assumed;
    6. "I don't check that Ibex ever handles interrupts. If it does handle an interrupt, it does so correctly.";
    7. correctness, not security;
    8. no instruction-fetch correctness proof;
    9. no reset proof.
  - Ibex has no MMU.
- **CHERIoT-Ibex** (`lowRISC/cheriot-ibex@56357b6da56b690c608c2cc97a7f9489ae67a3ac`, `dv/formal/README.md`; arXiv 2502.04738v1, Ploix, Armstrong, Melham, Lin, Wang, Courtney).
  - The reference is "a minor variant of the full and definitive ISA description written in the Sail ISA specification language".
  - The prototype Sail→SystemVerilog translation goes through Sail's SMT fragment. It was "tested … by re-using the existing Sail test suite"; the translation is not verified.
  - Bugs found include illegal-instruction and EBreak MTVAL values, exception priorities, user-mode WFI and CSR instruction problems (paper Fig. 2).
  - The README adds that stack zeroing and reservation/revocation are not covered.

### 6. Miralis and `softcore-rv64`: bounded checking of privileged emulation against Sail-derived Rust

Basis: source + execution (P4) + derived. Revisions: `CharlyCst/miralis@f5ab1955192833ac025a6719a71c6e36a3f643ab` and `CharlyCst/softcore-rs@8c238f4103ce43b00078c7b3dc909f7dae05bfc4`. Paper: Castes et al., SOSP 2025, DOI 10.1145/3731569.3764826 (paper text not read).

1. **Harnesses.** `model_checking/src/lib.rs` defines 14 `#[cfg_attr(kani, kani::proof)]` functions: `mret`, `sret`, `wfi`, `fences` (`sfence.vma`; `hfence.*` commented out), `read_csr`, `write_csr`, `interrupt_virtualization`, `exception_virtualization`, `pmp_virtualization`, `verify_decoder`, `verify_compressed_loads`, `verify_load`, `verify_compressed_stores`, `verify_stores`. Each runs the Miralis operation and the Sail-derived function from related states and asserts equality of the virtual context. For example (`lib.rs:26-38`):
   ```rust
   ctx.emulate_mret(&mut mctx);
   model::execute_MRET(&mut core);
   assert_eq!(ctx, adapters::rv_core_to_miralis(core, &mctx), "mret instruction emulation is not correct");
   ```
   Kani is a bounded model checker for Rust, not a proof assistant.
2. **The reference is an unverified Sail→Rust translation.**
   - `softcore-rv64` (crate `0.6.0`, Miralis `Cargo.toml:55`) is generated by a custom OCaml Sail plugin (`softcore-rs/sail_rust_backend/sail_plugin_rust.ml`) from `riscv/sail-riscv@b6f7b1df64157e6b9d250e552842f963394bc2ba` (`justfile:1`).
   - It also applies `sail_models/riscv.patch`, which, besides build glue, changes Sail semantics: `is_CSR_defined(0x3A) @ idx` goes from `sys_pmp_count() > unsigned(idx)` to `sys_pmp_count() > 4 * unsigned(idx)`, and `zvk_check_encdec` is rewritten.
   - `readme.md`: "The generated code does not provide any guarantees regarding completeness or correctness."
   - `rv64/src/raw.rs` (20,062 lines) contains 552 `todo!`/`unimplemented!` sites, including the `LOAD`, `STORE`, `LOADRES`, `STORECON` and `AMO` execute arms (`raw.rs:11215-11237`). It has no page-table-walk or address-translation function.
   - Miralis keeps hand-adapted "automatically translated fragments" in `model_checking/src/model.rs` (`execute_MRET`, `execute_SRET`, `execute_WFI`, `execute_SFENCE_VMA`, `exception_handler`). There `flush_TLB` is a no-op stub (`model.rs:248-250`, body `// todo!("E_for")`).
3. **Harness exclusions** (source):
   - `generate_csr_register` (`lib.rs:72-102`) maps `sedeleg`/`sideleg`, `scontext` and the non-deterministic `cycle`/`instret`/`minstret`/`mcycle`/`time` to CSR 0.
   - `write_csr` skips `mideleg` and re-masks `medeleg` because "The softcore model predates the `medeleg` delegatable bits of the Sail model".
   - `interrupt_virtualization` sets `mideleg = 0`.
   - `exception_virtualization` uses causes 0..15 with an M-mode target only.
   - `pmp_virtualization` fixes access width 8, clears `MPRV`, and compares the native M-mode PMP check against the U-mode virtualized check outside Miralis/device ranges.
4. **Narrowed symbolic state.** `model_checking/src/symbolic.rs:144-145,197` initialises:
   ```rust
   ctx.csr.pmpcfg = [any!(); 8];
   ctx.csr.pmpaddr = [any!(usize) >> 10; 64];
   ctx.regs = [any!(usize); 32];
   ```
   A Rust array-repeat expression evaluates its operand once and copies the value (P4 prints `calls=2 all_regs_equal=true all_pmpaddr_equal=true`). Under Kani (derived):
   - all 31 non-zero GPRs share one symbolic value;
   - the eight `pmpcfg` words share one value, since the later normalisation is applied identically to each;
   - the 16 active `pmpaddr` entries (indices ≥ 16 are zeroed) share one value.

   So `pmp_virtualization` explores only configurations in which all active PMP entries have equal addresses.

### 7. Hand-written models whose trust is stated explicitly

Basis: documentation + source.

- **Komodo** (Ferraiuolo et al., SOSP 2017, DOI 10.1145/3132747.3132782), §5.1:
  - The Dafny ARMv7 model covers "core registers R0–R12, stack pointer (SP), link register (LR), portions of the current and saved program status registers (CPSR and SPSRs), privilege modes, control flow, interrupts, and exceptions. We model the semantics of 25 instructions".
  - "At present, our model must be fully trusted, but this could be avoided by proving its correctness against another formal model for ARM … we adopt the methodology termed idiomatic specification".
- **Serval** (`uw-unsat/serval@72adc495…`; Nelson et al., SOSP 2019, DOI 10.1145/3341301.3359641).
  - Paper §3.5: "A verifier written using Serval is a specification of the corresponding instruction set and is trusted to be correct. Since such verifiers are also executable interpreters, we write unit tests and reuse existing CPU validation tests". §6.4: these tests found "one bug in the RISC-V specification developed by the Sail project".
  - Source:
    - `test/riscv-tests/riscv-tests.mk:2-18` runs `rv64ui`/`rv64um`/`rv64ua`/`rv32ui`/`rv32um`/`rv32ua` (the `uc` lines are commented out) and no `mi`/`si` tests;
    - `serval/riscv/interp/r-type.rkt:80-82` maps `uret`/`sret`/`mret` to `notimplemented`, and `sfence.vma` (`r-type.rkt:91`), `wfi` (`r-type.rkt:84`) and `fence.i` (`i-type.rkt:71`) are `skip`;
    - `interp.rkt:45` stops at `mret`, because each trap handler is verified from an entry state to `mret`;
    - `pmp.rkt` supports only `OFF`/`TOR`, and other modes hit `(assert #f)`.
  - The paper's three-level page walk for S/U-mode accesses belongs to the monitor specification and is not validated against Sail.
- **seL4 `l4v` RISCV64** (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`).
  - `spec/machine/RISCV64/MachineOps.thy:197-223`: `hwASIDFlush`, `sfence`, `ifence` and `setVSpaceRoot` are each `machine_op_lift` of an unspecified constant, e.g. `consts' sfence_impl :: "unit machine_rest_monad"`.
  - `spec/machine/MachineMonad.thy:76-77`: `machine_op_lift ≡ machine_rest_lift o ignore_failure`. The operation may change only `machine_state_rest`, nondeterministically and without failing, and cannot touch `underlying_memory`, `device_state` or `irq_masks`.
  - `spec/design/m-skel/RISCV64/MachineTypes.thy:52-62`: `record machine_state = irq_masks, irq_state, underlying_memory, device_state, machine_state_rest`, with `axiomatization irq_oracle … where irq_oracle_max_irq`.
  - There is no TLB, CSR or translation state, and these files do not mention Sail.
- **ACE-RISCV** (`IBM/ACE-RISCV@42cf582eef21f9ab661ec7008d65c6de141b4be1`) is verified with RefinedRust in Rocq. `verification/theories/page_table/page_table.v:14-15`:
  ```coq
  (** * Architectural ground-truth *)
  (* TODO: have file for translated sail specs and then link up with this *)
  ```
  The Sv48/Sv57 page-table ground truth is hand-written. The repository README cites Sailor (USENIX Security 2025; arXiv 2502.06609, "Automatic ISA analysis for Secure Context Switching"), which uses Sail and Isla to classify ISA state that must be swapped across contexts and generates tests. That is analysis and testing, not a correspondence proof.
- **riscv-coq** (`mit-plv/riscv-coq@03881b21aa36115d436e06b9e1a40836e9b927c7`). README: "Generated from the RISCV Semantics in Haskell … using hs-to-coq".
  - `Spec/ExecuteCSR.v` contains `Ecall`, `Mret`, `Sret`, `Sfence_vma` and `raiseException`.
  - `translate` and `flushTLB` are abstract `RiscvMachine` methods; the default instance uses `translate accessType alignment := @Return M MM t` and `flushTLB := Return tt` (`Spec/Machine.v:81-82,141-142`).
  - No Sail relation exists.
- **HOL4 L3 RISC-V** (`HOL-Theorem-Prover/HOL@0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`, `examples/l3-machine-code/riscv/src/riscv.spec`, 5,354 lines, © 2014-2015) models an early privileged spec (`hstatus`, `MPRV` at bit 16, `Sv39`). The step library evaluates `translateAddr` under the `[[bare]]` hypothesis (`step/riscv_stepScript.sml:626-629`). No relation to Sail exists.
- **CHERI-RISC-V** (`CTSRD-CHERI/sail-cheri-riscv@cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b`) ships Isabelle/Coq *snapshots* of the generated model and helper lemmas (`prover_snapshots/`), with no correspondence proofs.

### 8. Islaris RISC-V configuration pins the privileged state

Basis: source. Revision `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`.

- `theories/riscv64/sys_regs.v:64-80` fixes:
  - `rv_enable_pmp = false` and `rv_enable_misaligned_access = false`;
  - the RAM/ROM/CLINT/HTIF bases;
  - `cur_privilege = Machine` (`ExactShape (RVal_Enum "Machine")`);
  - `misa = 0x800000000015312d`;
  - `mstatus` via `MaskShape 64 0x20000 0` ("MPRV disabled").
- `examples/riscv64_test.v:112-118` (`riscv_test_adequate`) assumes `Z.land mstatus_bits 0x20000 = 0`.
- The Sail-linked proofs case-split on `cur_privilege = Machine` to reduce `translateAddr` (`sail-riscv/riscv64_test.v:96-97`, `sail-riscv/memcpy.v:99`).
- `etc/riscv64_isla_coq.toml` `[registers.defaults]` sets `rv_enable_pmp = false` and `rv_enable_dirty_update = false`.

No RISC-V Islaris proof covers trap entry, S-mode, PMP or Sv39. The AArch64 side does contain privileged examples (`pkvm_handler/`, `examples/el2_to_el1.s`, `etc/aarch64_isla_coq_pkvm.toml`), all under fixed system-register defaults.

### 9. `check_CSR` short-circuit hazard in Sail→Lean RV64 extractions

Basis: source + execution (P3) + derived.

- `Verified-zkEVM/riscv-zkvm@6810fc14` `RiscvZkvm/Sail/SysControl.lean:392-394` and `opencompl/sail-riscv-lean@51c635c4` `LeanRV64D/SysControl.lean:526-528` both contain:
  ```lean
  def check_CSR (csr : (BitVec 12)) (p : Privilege) (access_type : CSRAccessType) : SailM Bool := do
    (pure ((← (check_CSR_priv csr p)) && ((check_CSR_access csr access_type) && ((← (is_CSR_accessible
                csr p access_type)) && (← (stateen_allows_CSR_access csr p access_type))))))
  ```
- Lean lifts each `(← e)` to the enclosing `do` statement and runs it before the `&&` is evaluated. So `is_CSR_accessible` and `stateen_allows_CSR_access` execute, and may throw or change state, even when `check_CSR_priv` returns `false`. Sail's `&` short-circuits. P3 reproduces the divergence in `ExceptT String (StateM Nat)`: the hoisted form returns `.error …` where the short-circuit form returns `.ok false`, and the hoisted form performs the right operand's state update.
- The fix is `rems-project/sail` `e55d89e79e3e5dfa88a137c73be371fb3671c983` ("Lean: support short-circuiting && || with effects", 2026-10-19). `git merge-base --is-ancestor` shows release tags `0.20.2` and `0.20.3` do not contain it (P2). riscv-zkvm records generating with Sail 0.20.3 (`docs/validation.md:55-56`); the revision it actually pins, `60695b1ea377048f0adc39c62671cd099b2ed9f6` (the `0.20.3-binary` tag, 2026-09-23; see package `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`), also lacks it (P2).
- xv6iris documents a concrete consequence under a scoped module subset: the unpatched backend lets "`check_CSR` reach `currentlyEnabled Ext_Zkr`, an `assert false`, on a user access to mseccfg" (`tools/regen_sail_model.sh:37-42`).
- Derived: for a scoped extraction, where omitted `currentlyEnabled` clauses become a failing catch-all (riscv-zkvm `docs/validation.md`, "Scoped-model execution adapter"), a U-mode access to a privileged CSR can therefore be modelled as a Sail error rather than an illegal-instruction trap.

### 10. Derived conclusions for a small kernel-reducible trusted RV64 S-mode model

All items in this section are **derived** from Findings 1–9.

1. **No reusable privileged correspondence exists in the examined prior art.** A correspondence covering traps, CSRs and Sv39 against Sail would be new work.
   - Reusable patterns: riscv-zkvm's state relation, platform-frame and mode-invariant structure, scoped extraction and axiom sweep (user tier); xv6iris's per-level Sv39 walk lemmas, TLB and `fence.i` treatment, and `sret`/`satp`/`sfence` rules.
   - Cost evidence: xv6iris shows Sail's privileged semantics is tractable in Lean, at a different trust level and over a forked model.
2. **The correspondence statement must carry traps and privileged state.** P1 shows a success-only forward simulation is vacuous for a model that encodes traps as stuck. The step relation must:
   - include privilege, the relevant CSRs (`sstatus`/`sepc`/`scause`/`stval`/`stvec`/`satp`/`sie`/`sip`) and the translation mode in the coupling relation, rather than in a frame invariant that forbids them from changing;
   - require that a trapping step on one side corresponds to the same trap (cause, `epc`, `tval`, target) on the other;
   - include the bidirectional fault-kind clause described in package `reference-model-bisimulation-executable-semantics-and-differential-oracles`.
3. **`fence.i` and `sfence.vma` obligations need more than stock sequential Sail.**
   - Stock sequential Sail treats barrier, cache and TLB-maintenance hooks as `pure ()`; see package `riscv64-sv39-opensbi-trap-wx-and-sail-lean-semantics`.
   - xv6iris needed a Sail fork that tags instruction fetches and page-table walks, plus a free-monad `lean-sail` and a memory model with a per-hart instruction view.
   - A correspondence to stock Sail can therefore establish functional privileged semantics, but not the coherence obligations a kernel relies on (code writes followed by `fence.i`; PTE writes followed by `sfence.vma`). Those need either an effect-tree-level correspondence or an explicitly trusted extension.
4. **The reference extraction must be generated by a Sail compiler containing `e55d89e7`,** or audited for hoisted effectful `&&`/`||` operands, because the CSR-permission path is affected (Finding 9).
5. **Bounded and testing evidence is not correspondence evidence.** Miralis, Ibex, CHERIoT-Ibex, Serval's `riscv-tests` runs and riscv-zkvm's `rv64ui` emulator runs found real bugs in Sail, QEMU and RTL. That makes them useful differential oracles, but they do not establish that a trusted model agrees with Sail on privileged behaviour.

## Boundaries

- **Search coverage (`not found`, not `does not exist`).** The central result is limited to the scope in **Applicability**. Artifacts in private repositories, unpublished theses, and papers not surfaced by the searches were not covered.
- **Not examined:**
  - Kami (and the lightbulb pipeline relating riscv-coq to a Kami processor, PLDI 2021, DOI 10.1145/3453483.3454065);
  - TestRIG/RVFI-DII;
  - Forvis/Flute and GRIFT;
  - Kestrel's ACL2 RISC-V model;
  - CertiKOS's machine model;
  - the Sail↔Spike tandem flow;
  - the Morello Isabelle proofs (Bauereiss et al., ESOP 2022, DOI 10.1007/978-3-030-99336-8_7; these concern properties of a Sail model, not a hand-model correspondence);
  - seL4's RISC-V binary-verification ISA model;
  - the xv6iris paper text;
  - the Miralis paper text;
  - the `zeldovich/sail-riscv` fork diff.
- **Unknown:**
  - Whether riscv-zkvm's declarations pass `#print axioms` with exactly the documented seven axioms. The CI gate exists, but the 60k-line extraction was not built here.
  - Whether xv6iris's `Xv6.userProof` cone actually contains `_native.bv_decide.ax_*` axioms.
  - Whether the Miralis SOSP 2025 artifact harnesses use the same array-repeat initialisation as `f5ab1955`.
  - Whether the `7c6b500c` riscv-lean shift theorems (`shamt : BitVec 5`) covered RV64 shift amounts ≥ 32. Resolving this needs the `execute_SHIFTIOP` signature at `opencompl/sail-riscv-lean@11d8fa21`.
  - Whether the `check_CSR` hoisting changes any observable result in the *full* (unscoped) `sail-riscv-lean` model. This depends on whether `is_CSR_accessible`/`stateen_allows_CSR_access` can throw or write state when `check_CSR_priv` is false; that was not traced.
- **Known not to apply:**
  - riscv-zkvm `SailEquiv` does not apply to S-mode, U-mode, any privilege change, CSR instructions, `ecall`, `mret`/`sret`, Sv39, PMP-enabled configurations, or the hand model's trap (`none`) cases.
  - Ibex and CHERIoT-Ibex do not apply to virtual memory (no MMU) or to RV64.
  - Islaris RISC-V proofs do not apply outside `cur_privilege = Machine` with PMP off and `MPRV = 0`.
- **Unsupported (by the subject):**
  - softcore-rv64 does not support loads, stores, LR/SC or AMOs (`todo!`) or page-table walks.
  - Serval's RISC-V interpreter does not support `mret`/`sret`/`uret` (`notimplemented`) or PMP `NAPOT`.
  - riscv-coq's default machine instance does not translate addresses.
- **Stronger conclusions not established:**
  - That xv6iris's `USER` contract is a reference-model correspondence usable as a trusted-model fidelity theorem.
  - That Ibex or CHERIoT-Ibex results transfer to any software model.
  - That Miralis's harnesses are exhaustive over CSR or PMP states.
  - That riscv-zkvm's 51 theorems say anything about trapping executions.
  - That passing `riscv-tests` or `rv64ui` runs validates privileged semantics.

## Evidence

All observations were made on 2026-11-20. Git sources were read at the full revisions below; `support/counts.sh` re-derives each cited count, line and excerpt.

**Repositories (path : lines or symbol)**

- `Verified-zkEVM/riscv-zkvm@6810fc14d9c40373101321cefaec59df8d82e3e7`:
  - `RiscvZkvm/Rv64/SailEquiv/VmemReduction.lean:956-971` (`BareModeInv`);
  - `StateRel.lean:264` (`StateRel`), `:295` (`StateRelPC`), `:347-365` (`PlatformFrame`);
  - `StepSim.lean:81-83` (`Instr.simulable`);
  - `InstrMap.lean:99`;
  - `StepRun.lean:70-81` (`sailStep` and docstring), `:327-334` (`sailStep_run_sim`), `:381-387` (`sailStepN_run_sim`), `:460` (`jalr_sideCond_satisfiable`); the file has 483 lines;
  - `RiscvZkvm/Rv64/Execution.lean:341-371` (`step`), `:718-723` (`step_sh_trap`);
  - `scripts/AxiomSweep.lean:47-52`;
  - `RiscvZkvm/Sail/SysControl.lean:392-394` (`check_CSR`);
  - `docs/validation.md:55-56, 66, 109-127, 133-137`;
  - `lean-toolchain`.
- `opencompl/riscv-lean@7c6b500c1744f40d928fb131125cd06edf9f4fce` and `@0e3365ac7b670d79d70e9b4a8b7fba782607c44f`: `RISCV/SailToRV64.lean:72` (`shiftiop_slli_eq` signature at both revisions); theorem and `bv_decide` counts per file.
- `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`: `LeanRV64D/SysControl.lean:526-528`.
- `rems-project/sail`: commit `e55d89e79e3e5dfa88a137c73be371fb3671c983` (2026-10-19); tags `0.20.2` and `0.20.3` (`0.20.3` = `3df54034910b31a1e00d948ee965b2e9603d68e0`) and `0.20.3-binary` = `60695b1ea377048f0adc39c62671cd099b2ed9f6` (fix contained in none); commit `5745ea9e5369ab4fc51de6f8b773dd8ebc323357` (fix not contained).
- `mit-pdos/xv6iris@5cb9df992c45829f6210b3e4176962d7b7a4c408`:
  - `README.md:8, 24-45, 97-110, 129-130`;
  - `tools/regen_sail_model.sh:25-60`;
  - `tools/audit/baseline.json:1-22`;
  - `claude-notes/design/icache.md:14-31`;
  - `lean-toolchain`;
  - `lake-manifest.json` (iris-lean `728a1714…`).
- `lowRISC/ibex@f5b1439295048c6eead73ad4ef8a55cc564e7d6f`: `dv/formal/README.md` (sections "Conclusivity", "Code Tour", "Proof Holes" lines 170-190).
- `lowRISC/cheriot-ibex@56357b6da56b690c608c2cc97a7f9489ae67a3ac`: `dv/formal/README.md`.
- `CharlyCst/miralis@f5ab1955192833ac025a6719a71c6e36a3f643ab`:
  - `model_checking/src/lib.rs` (harnesses at lines 26, 41, 56, 104, 165, 198, 252, 273, 350, 453, 472, 500, 526, 558; `generate_csr_register` 72-102);
  - `model_checking/src/model.rs:1-6, 13-29, 85-122, 248-250`;
  - `model_checking/src/symbolic.rs:144-145, 197`;
  - `Cargo.toml:55`.
- `CharlyCst/softcore-rs@8c238f4103ce43b00078c7b3dc909f7dae05bfc4`: `readme.md`, `justfile:1`, `sail_models/riscv.patch:38-39`, `rv64/src/raw.rs:11215-11237`, `sail_rust_backend/sail_plugin_rust.ml`.
- `uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`: `serval/riscv/interp/r-type.rkt:80-82, 84, 91`, `serval/riscv/interp/i-type.rkt:71`, `serval/riscv/interp.rkt:45`, `serval/riscv/pmp.rkt:14, 65-68`, `test/riscv-tests/riscv-tests.mk:2-18`.
- `seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`: `spec/machine/RISCV64/MachineOps.thy:115-126, 197-223`, `spec/machine/MachineMonad.thy:76-77`, `spec/design/m-skel/RISCV64/MachineTypes.thy:52-62`.
- `IBM/ACE-RISCV@42cf582eef21f9ab661ec7008d65c6de141b4be1`: `verification/theories/page_table/page_table.v:14-15`, `README.md` (Sailor citation).
- `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`: `theories/riscv64/sys_regs.v:64-80`, `examples/riscv64_test.v:112-118`, `sail-riscv/riscv64_test.v:96-97`, `sail-riscv/memcpy.v:99`, `etc/riscv64_isla_coq.toml`.
- `mit-plv/riscv-coq@03881b21aa36115d436e06b9e1a40836e9b927c7`: `README.md:3`, `src/riscv/Spec/Machine.v:81-82, 141-142`, `src/riscv/Spec/ExecuteCSR.v`.
- `HOL-Theorem-Prover/HOL@0c30bdb71aafd4e6a354f5b0b43fffbff6fa8d47`: `examples/l3-machine-code/riscv/src/riscv.spec`, `step/riscv_stepScript.sml:626-629`.
- `CTSRD-CHERI/sail-cheri-riscv@cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b`: tree listing (`prover_snapshots/`).

**Papers**

- Nelson et al., SOSP 2019, DOI 10.1145/3341301.3359641, §3.5 and §6.4. Author PDF `unsat.cs.washington.edu/papers/nelson-serval.pdf`.
- Ferraiuolo et al., SOSP 2017, DOI 10.1145/3132747.3132782, §5.1. Author PDF from microsoft.com.
- Ploix et al., arXiv 2502.04738v1: abstract, the section describing the Sail→SystemVerilog translation, Fig. 2.
- Kalani et al., arXiv 2502.06609 (title checked on arxiv.org).
- Castes et al., SOSP 2025, DOI 10.1145/3731569.3764826 (DOI resolves to dl.acm.org; text not read).
- arXiv 2609.04043 (title, authors and date read from the abstract page).

**Probes** (`support/`, details in `support/README.md`)

| ID | File | Command | Environment | Recorded result |
|---|---|---|---|---|
| P1 | `ForwardSuccessSimVacuity.lean` | `lean -j1 -M768 ForwardSuccessSimVacuity.lean` | Lean v4.34.1, Init only | exit 0; `trapEverywhere_fwd` and `hand_ref_disagree_on_trap` use no axioms; `hand_fwd`, `trapEverywhere_not_noSilentTrap` and `hand_not_noSilentTrap` use `[propext]` |
| P2 | `counts.sh` | `WORK=/tmp/rvpriv-src bash counts.sh > counts.out` | bash + git, network | `counts.out` |
| P3 | `LeanDoShortCircuit.lean` | `lean -j1 -M768 LeanDoShortCircuit.lean` | Lean v4.34.1, Init only | exit 0; four `rfl` examples; `hoisted_ne_short` uses no axioms |
| P4 | `array_repeat_once.rs` | `rustc -O array_repeat_once.rs -o probe && ./probe` | rustc 1.102.0-nightly (3ef0c22cd 2026-11-11) | `calls=2 all_regs_equal=true all_pmpaddr_equal=true` |

## Revalidation

1. **Did riscv-zkvm grow privileged coverage?** In a newer revision, rerun the riscv-zkvm block of `support/counts.sh` (adjust `ZK=`). Check:
   - `Instr.simulable`;
   - whether `BareModeInv` is still required by load/store theorems;
   - whether `sailStep` is still hand-written;
   - whether any theorem has a hand-model `none` (trap) premise.

   Then read `docs/validation.md` "Known gaps".
2. **riscv-lean**: rerun the riscv-lean block (theorem/`bv_decide` counts and the privileged-identifier grep) at the new `main`.
3. **xv6iris**: check `README.md` "What is proved", `tools/audit/baseline.json` and `tools/regen_sail_model.sh` (fork pin and deltas). To settle the axiom question, run `tools/ci/audit.sh` on a full build.
4. **Short-circuit hazard**: for any Sail-generated Lean model, grep `SysControl.lean` for `check_CSR` and inspect whether effectful `(← …)` operands appear inside `&&`/`||`. For a Sail compiler, run `git merge-base --is-ancestor e55d89e79e3e5dfa88a137c73be371fb3671c983 <rev>`. P3 demonstrates the Lean semantics on any toolchain.
5. **Miralis**: re-read `model_checking/src/symbolic.rs` for array-repeat initialisation and `model.rs` `flush_TLB`. Rerun P4 only if the Rust array-repeat semantics is in doubt; the Rust Reference defines it.
6. **Ibex / CHERIoT-Ibex**: diff `dv/formal/README.md` "Proof Holes" at the new revision.
7. **Central `not found` result**: repeat the searches in **Applicability**. In particular, check xv6iris, riscv-zkvm, ACE-RISCV (the `page_table.v` TODO) and any new Lean/Rocq/Isabelle project that cites Sail RISC-V together with `mret`, `sret`, `satp` or `stvec`.
