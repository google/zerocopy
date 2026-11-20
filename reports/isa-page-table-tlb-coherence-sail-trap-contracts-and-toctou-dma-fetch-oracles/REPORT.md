# ISA Page-Table Walks, TLB Coherence, Sail Trap Contracts, and TOCTOU DMA Fetch Oracles

## Summary

Verifying operating-system kernels, confidential hypervisors, and memory-mapped device drivers in Rust exposes three hardware-software seams where purely safe Rust memory models break down: (1) multi-level virtual-address translation interacting with split hardware page-walk caches (PWCs), global (`G=1`) TLB entries, and asynchronous SMP frame reclamation; (2) `InlineAsm` register-frame trap entry and confidential-VM exit instructions lowered outside MIR (`TerminatorKind.unsupported` in Anneal); and (3) shared-memory time-of-check-to-time-of-use (TOCTOU) double-fetches across untrusted hypervisor buffers, DMA descriptors, or userspace `IoRing` submission queues. **Basis: source, documentation.**

Drawing on primary artifacts from `VeriSMo` (OSDI 2024, `ISBN 978-1-939133-40-3`), `CortenMM` (SOSP 2025, `doi:10.1145/3731569.3764836`), `Islaris` (PLDI 2022, `doi:10.1145/3519939.3523434`), `opencompl/sail-riscv-lean`, `seL4/l4v`, `seL4/seL4`, `asterinas/vostd`, and double-fetch taxonomy studies (Wang et al., USENIX Security 2017, `ISBN 978-1-931971-40-9`), this report distills Pass-1-compatible Lean 4 verification patterns for Anneal `theory/`: `Anneal.Sys.PageWalk` (3-level `Sv39` and 4-level x86-64 walks separating non-leaf PWCs from leaf TLBs across `sfence.vma`/`invlpg`), `Anneal.Sys.ShootdownPcm` (per-core acknowledgment masks gating frame reuse), `Anneal.Sys.TrapContract` (`seL4`-style register-frame & Sail `MaskShape` companion obligations), and universal `SharedFetchOracle` quantification for single-fetch TOCTOU immunity without mutating `Trusted.MirSemantics`. **Basis: source, derived.**

## Applicability

This report targets kernel and systems crates verified under Anneal (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`) on Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) under `trusted/audit/TrustedBoundary.lean` (L442–596, L1117–1366). Standard kernel allocator or queue logic runs cleanly inside `Trusted.MirSemantics.evalStep` (`L643–647` deterministic `ValidChoice := c = 0`, `L1597–1676` `SatisfiesPost`), whereas `InlineAsm` traps, `invlpg`/`sfence.vma`, and hypervisor exits (`vmmcall`) lower to `TerminatorKind.unsupported` (`Trusted/MirAst.lean` L782–795). Hardware instructions therefore require external companion contracts anchored to Sail ISA traces, while translation walks, SMP shootdowns, and `SharedFetchOracle` snapshot proofs live cleanly in Pass-1 `theory/` (`prelude` + 51 `Init.*` modules, zero `Std.*`/`omega`/`bv_decide`/`native_decide`). **Basis: normative, source.**

Within `reference-corpus/1`, this study extends rather than duplicates adjacent systems reports: security-monitor unwinding, `PAS` confinement, and single-core `BarrierGhostState` (`capability-noninterference-pas-confinement-and-hw-sw-seam-proofs`); `Verus` ghost views/prophecies (`verus-vstd-views-permissions-prophecies-and-os-verification`); assembly verifiers (`machine-code-verification-frameworks-and-assembly-contracts`); `rustc` `asm!` syntax (`rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax`); and weak-memory atomics (`anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`). Here the focus is multi-level page walks with non-leaf PWCs, multi-core shootdown reclamation ghost state, Sail-linked trap frames, and queue-level DMA/IoRing snapshot verification. **Basis: documentation.**

## Findings

### Multi-Level Page-Table Walks and Non-Leaf PWC vs. Leaf TLB Discrepancies

Formalizing hardware address translation across architectures exposes recurring mismatches between abstract `VA -> Option PA` maps and real hardware caching structures: **Basis: source, documentation.**

1. **Three-level `Sv39` in `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`) and RISC-V Priv Spec (`c05f1725f25526dd8463bac6ca75cfcfbee17d05`):** In `LeanRV64D/Vmem.lean` (L256–371, L406–559), `pt_walk` first enforces canonical sign-extension (`L537–539`, top bit 38 extended cleanly through bits 39..63), indexes three 9-bit page-table levels (`lvl ∈ {2, 1, 0}` at bit shifts 30, 21, 12), and enforces superpage alignment at leaf PTEs (`PTW_Misaligned` when `pte.ppn` masked by `levelMask` is nonzero, L310–322). Cache lookup splits into `translate_TLB_hit` (L406–429) and `translate_TLB_miss` (L431–465). Critically, `LeanRV64D/VmemTlb.lean` (L246–351) models a 64-entry flat leaf/superpage `tlb`, where `add_to_TLB` caches resolved leaf translations *only* (omitting intermediate non-leaf Page-Walk Caches) and `flush_TLB_Entry` (L276–289, matching `L279`) filters `(ent.asid == asid) && (not ent.global)`—leaving `G=1` global mappings intact across ASID-scoped flushes! **Basis: source.**
2. **Four-level x86-64 in `VeriSMo` (`5e1c159aec20491653550e39b00bd0855f543a7e`) and `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):** `VeriSMo` defines 4-level page-table page sizes in `pgtable_e/pte.rs` (L53–152: `lvl_to_size` returning `0x1000`, `0x20_0000`, `0x10_0000_0000`, `0x1_0000_0000_0000` up to `L4_MAX_ADDR`), pairing each entry with `PtePerm` ownership bounds. `seL4/l4v/spec/abstract/X64/ArchVSpace_A.thy` (L32–89, L146–292) models `PML4`/`PDPT`/`PD`/`PT` walks where non-leaf unmapping (`unmap_pdpt`, `unmap_pd`) triggers `flush_pdpt` and `flush_pd` aliasing full ASID/global invalidation (`flush_all` / `invalidateASID`). In contrast, `seL4/l4v/spec/abstract/RISCV64/ArchVSpace_A.thy` (L85–190) distinguishes `unmap_page` from `unmap_page_table` and `delete_asid` paired with `sfence`. **Basis: source.**
3. **Why omitting non-leaf PWC rules creates soundness holes (Syeda & Klein, JAR 2020, `doi:10.1007/s10817-019-09539-7`):** Hardware CPUs cache intermediate non-leaf directory pointers (`lvl > 0` PWC entries mapping `cur_ppn, va_prefix -> next_ppn`) separately from leaf TLBs. On RISC-V, a targeted `sfence.vma va, asid` (`rs1 ≠ x0, rs2 ≠ x0`) guarantees eviction of non-global leaf entries matching `(va, asid)`, yet **neither** clears `G=1` entries **nor** guarantees eviction of stale non-leaf directory entries in hardware PWCs—requiring `sfence.vma x0, asid` (`va = None`) on intermediate table teardown or `sfence.vma x0, x0` (`va = None, asid = None`) when `G=1` mappings change. Verifying only against a leaf-only `sail-riscv-lean` cache model misses non-leaf stale-PWC bugs unless Anneal explicitly separates `PWC` and `LeafTLB` tiers! Both behaviors are exercised concretely in `reval_pkg2.py`. **Basis: documentation, execution.**

A distilled `prelude`-compatible Pass-1 module `Anneal.Sys.PageWalk` captures split `WalkEntry` caches and characterizes non-leaf vs. leaf flush equivalence cleanly: **Basis: derived.**

```lean
/- Module assumes crate prelude + locked Init.* foundation imports from TrustedBoundary. -/
namespace Anneal.Sys.PageWalk

def eqNat : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => eqNat a b
  | _, _ => false

structure WalkEntry where
  asid : Nat
  vaPrefix : Nat
  level : Nat
  global : Bool
  targetPpn : Nat

inductive FlushCmd where
  | all
  | byAsid (asid : Nat)
  | singleVa (va : Nat) (asid : Nat)

structure CachedTlb where
  pwc : List WalkEntry
  leaves : List WalkEntry

def matchesVaAsid (va asid : Nat) (e : WalkEntry) : Bool :=
  eqNat e.asid asid && eqNat e.vaPrefix va

def keepNotAsid (a : Nat) (e : WalkEntry) : Bool :=
  e.global || ! (eqNat e.asid a)

def keepNotSingle (va a : Nat) (e : WalkEntry) : Bool :=
  e.global || ! (matchesVaAsid va a e)

def filterList {A : Type} (p : A → Bool) : List A → List A
  | [] => []
  | x :: xs =>
      match p x with
      | true => x :: filterList p xs
      | false => filterList p xs

def applyFlush (cmd : FlushCmd) (st : CachedTlb) : CachedTlb :=
  match cmd with
  | FlushCmd.all => { pwc := [], leaves := [] }
  | FlushCmd.byAsid a =>
      { pwc := filterList (keepNotAsid a) st.pwc
      , leaves := filterList (keepNotAsid a) st.leaves }
  | FlushCmd.singleVa va a =>
      { pwc := st.pwc
      , leaves := filterList (keepNotSingle va a) st.leaves }

theorem singleVa_preserves_pwc (va a : Nat) (st : CachedTlb) :
    (applyFlush (FlushCmd.singleVa va a) st).pwc = st.pwc := by
  dsimp only [applyFlush]
  rfl

theorem flushAll_clears_both (st : CachedTlb) :
    applyFlush FlushCmd.all st = { pwc := [], leaves := [] } := by
  dsimp only [applyFlush]
  rfl

end Anneal.Sys.PageWalk
```

### Partial-Walk TLB Shootdown PCMs and Concurrent Frame Reclamation

Unmapping a page table or leaf frame on an SMP kernel creates a race window between mutating the architectural PTE in RAM, sending inter-processor interrupts (IPIs) to invalidate remote core TLBs/PWCs, and handing the freed physical frame back to the allocator—especially if remote cores can hold *partial page-walk cursors* mid-walk under RCU/lock-free traversal. **Basis: source, documentation.**

Three primary industrial/academic systems demonstrate the required state-machine abstractions:
1. **`VeriSMo` per-`MemID` TLB abstraction (`microsoft/verismo@5e1c159aec20491653550e39b00bd0855f543a7e`, OSDI 2024):** In `arch/tlb/{def_s.rs,tlb_s.rs}`, `VeriSMo` models hardware caching as `TLB { db: FMap<MemID, Map<GVN, SpecGuestPTEntry>> }` indexed per memory-space `MemID` with `invlpg` and `flush_memid`. In `pgtable_e/tlb.rs` (L12–36), `ensure_invlpg` trusts an `#[verifier(external_body)]` contract over `asm!("invlpg [{}]")` whose postcondition collapses the ghost sequence of speculative/buffered writes to the latest entry: `snp.pte =~~= seq![prev_snp.pte.last()]`. Until `invlpg` executes, a core's ghost trace retains older PTE permissions, preventing memory reclamation. **Basis: source.**
2. **`CortenMM` tokenized `strays` + `cursors` state machine (`TELOS-syslab/CortenMM-Artifact@604592d815cb1cb7d4619f202b5d7ff471a3a7af`, SOSP 2025 `doi:10.1145/3731569.3764836`):** Eliminating coarse global VMA trees yields `1.2×–26×` throughput gains over Linux page-fault paths by letting concurrent cursors lock subtrees fine-grainedly. Inside `verification/lock-protocol-rcu/src/spec/rcu/tree.rs` (L21–220; `VERIFICATION_WALKTHROUGH.md` L43–78), `TreeSpec` coordinates lock-free walks and page-table reclamation via four invariants:
   - `cursors: Map<CpuId, CursorState>` obeys `inv_non_overlapping` (L108–118), guaranteeing mutually disjoint locked tree ranges across concurrent CPUs.
   - `strays: Map<(NodeId, Paddr), bool>` records unlinked physical nodes still reachable by in-flight RCU/walk readers: `inv_stray_at_most_one_false_per_node` (L136) ensures at most one active `false` (live-owning) token exists, `inv_pte_is_alive_implies_stray_has_false` (L145–161) binds PTE liveness to the non-stray state, and `inv_free_paddr_not_in_strays` (L188–192) forbids freeing any `Paddr` until all active cursor/TLB references drain out of `strays`. **Basis: source, documentation.**
3. **`Asterinas` `vostd` frame-pinning protocol (`asterinas/vostd@eb1a9d044617c2abff58f959ccc50f9571d561e9`):** In `ostd/src/mm/tlb.rs` (L68–185), `issue_tlb_flush_with` pins `drop_after_flush: Option<Frame<dyn AnyFrameMeta>>` in `OpsStack` until local (`dispatch_tlb_flush`) and remote IPI synchronization (`sync_tlb_flush`, waiting on `ACK_REMOTE_FLUSH` with deadlock guard `assert!(irq::is_local_enabled())` at L171) complete. However, `ostd/specs/mm/tlb.rs` (L77–88) defines `dispatch_tlb_flush_spec` without calling `.flush_all()` on `TlbFlushOp::All` and flushes only `range.start` on `TlbFlushOp::Range` (see also `counterexample-trace-shrinking-span-blame-assignment-and-agent-proof-repair`), severing drop safety from TLB emptiness. **Basis: source.**

Because Anneal separates trusted `MirSemantics` from un-trusted `theory/` algebras, we can encode SMP shootdown-gated frame reclamation cleanly as a deterministic ghost state machine (`ShootdownPcm`) over per-core acknowledgment bitmasks (verified executable in `reval_pkg2.py`): **Basis: derived.**

```lean
/- Module assumes crate prelude + locked Init.* foundation imports from TrustedBoundary. -/
namespace Anneal.Sys.ShootdownPcm

inductive FramePhase where
  | mapped
  | pendingShootdown (acked : List Nat) (required : List Nat)
  | reclaimable
  | freed

def hasNat (c : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => Anneal.Sys.PageWalk.eqNat c x || hasNat c xs

def allAcked (acked : List Nat) : List Nat → Bool
  | [] => true
  | c :: cs => hasNat c acked && allAcked acked cs

def ackCore (coreId : Nat) (st : FramePhase) : FramePhase :=
  match st with
  | FramePhase.pendingShootdown acked req =>
      let acked' := coreId :: acked
      match allAcked acked' req with
      | true => FramePhase.reclaimable
      | false => FramePhase.pendingShootdown acked' req
  | other => other

def tryFreeFrame (st : FramePhase) : Option FramePhase :=
  match st with
  | FramePhase.reclaimable => Option.some FramePhase.freed
  | _ => Option.none

/-- Safety gate: physical frame reuse succeeds only after transition into `reclaimable`
    (all cores holding stale TLB/PWC entries have acknowledged flush). -/
theorem free_requires_reclaimable (st st' : FramePhase)
    (h : tryFreeFrame st = Option.some st') :
    st = FramePhase.reclaimable ∧ st' = FramePhase.freed := by
  cases st with
  | mapped =>
      dsimp only [tryFreeFrame] at h
      nomatch h
  | pendingShootdown acked req =>
      dsimp only [tryFreeFrame] at h
      nomatch h
  | reclaimable =>
      dsimp only [tryFreeFrame] at h
      injection h with h_eq
      subst h_eq
      exact ⟨rfl, rfl⟩
  | freed =>
      dsimp only [tryFreeFrame] at h
      nomatch h

end Anneal.Sys.ShootdownPcm
```

Wait—let's keep zero speculative imports or un-checked constructs: in `Anneal.Sys.ShootdownPcm`, notice `List.elem` requires `BEq Nat` which exists in `Init.Prelude` for `List.elem` (if `BEq` instance for `Nat` is in `Init.Prelude`). Wait—to be 100% immune even to whether `List.elem` uses `BEq` in `Init.Prelude` vs `Init.Data.List.Basic`, let's write an explicit 4-line helper `hasNat (c : Nat) (xs : List Nat) : Bool` using `Nat.beq`! That uses ONLY `Nat`, `Bool`, `List`, and `Nat.beq` from core `Init.Prelude`—zero imports needed beyond `prelude`! Let's make sure we do that!

### Linking InlineAsm Register-Frame Trap Contracts to Sail ISA Models

Anneal lowers MIR `TerminatorKind::InlineAsm` to `TerminatorKind.unsupported` (`Trusted/MirAst.lean` L782–795). Therefore, kernel trap entry, privilege-level context switches, and instructions such as `sret`, `sfence.vma`, `invlpg`, and `vmmcall` cannot be executed inside `Trusted.MirSemantics.evalStep`. Bridging Safe Rust kernel code to real trap frames without inflating the TCB requires linking companion pre/post register-frame contracts directly to authoritative ISA semantics: **Basis: source, documentation.**

1. **`Islaris` trace refinement (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`, PLDI 2022 `doi:10.1145/3519939.3523434`):** Islaris compiles authoritative Sail ISA models via `isla-axiomatic` symbolic execution into Coq/Rocq symbolic traces (`theories/opsem.v` L63–189: `Inductive isla_trace := tnil | tcons | tcases`, constraining registers via `valu_shape` = `ExactShape | StructShape | MaskShape | BitsShape`), embeds them inside Iris separation logic (`theories/lifting.v` L87–139: `WPasm`, `WPreadreg`, `instr_pre`), and proves machine-trace adequacy (`theories/adequacy.v` L91–145: `isla_adequacy`). On RISC-V (`theories/riscv64/{arch.v,specs.v,sys_regs.v}`), `mstatus` invariants use `MaskShape 64 0x20000 0` to pin bit 17 (`MPRV` disabled) across traps so supervisor/machine loads do not silently adopt user translation permissions. **Basis: source.**
2. **`seL4` RISC-V trap register-frame specification (`seL4/seL4@08c7e5fddb3111ff377745c8eefb07feb5c4cfb7/src/arch/riscv/traps.S` L24–147):** The assembly trap entry performs atomic scratch swap (`csrrw sp, sscratch, sp` on SMP vs. `csrrw t0, sscratch, t0` on UP), saves a fixed **35-word** trap frame covering `x1..x31`, `scause`, `sstatus`, `sepc`, and computes `NextIP`: when `scause == 8` (user `ecall`), `NextIP` advances to `sepc + 4` (`L104–113`); on synchronous exceptions or asynchronous interrupts (`scause ≠ 8`), `NextIP` preserves `sepc` verbatim (`L137–145`, probed in `reval_pkg2.py`). **Basis: source, execution.**
3. **Sail RISC-V Lean 4 (`opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`, `LeanRV64D/Step.lean`) & `VeriSMo` `vmgexit` (`registers/core_exit_t.rs` L6–59):** `sail-riscv-lean` provides executable/kernel-checkable Lean 4 single-step transitions alongside `Vmem.lean`, making direct Sail-to-Anneal trace comparison possible in Lean 4 without Rocq translation. In confidential VMs, `VeriSMo` wraps `rep vmmcall` inside `vmgexit` (`registers/core_exit_t.rs` L6–59) guarded by `is_none_or_sharedmem` (`memperm@.snp().is_hv_shared()`) and `hvupdate_none_or_sharedmem` (`spec_write_rel`), bounding untrusted hypervisor register/memory side effects purely to explicitly shared GHCB pages. **Basis: source.**

In Anneal, an `InlineAsm` trap shim enters verification via an explicit `TrapContract` premise attached to the caller's assumption boundary—never modifying `Trusted.MirSemantics`, and audited explicitly against Sail `MaskShape`/`ExactShape` trace assertions (e.g., `seL4` `NextIP` advance vs. `mstatus` bit-17 mask invariance): **Basis: derived.**

```lean
/- Module assumes crate prelude + locked Init.* foundation imports from TrustedBoundary. -/
namespace Anneal.Sys.TrapContract

def eqNat : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => eqNat a b
  | _, _ => false

theorem eqNat_true_eq : ∀ a b : Nat, eqNat a b = true → a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => nomatch h
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ a, Nat.succ b, h => congrArg Nat.succ (eqNat_true_eq a b h)

structure RegFrame where
  gprs : Nat → Nat
  sepc : Nat
  scause : Nat
  sstatus : Nat
  nextIp : Nat

def mprvClear (sstatus : Nat) : Bool :=
  eqNat (Nat.mod (Nat.div sstatus 131072) 2) 0  -- bit 17 = 0x20000 clear

def trapNextIp (scause sepc : Nat) : Nat :=
  cond (eqNat scause 8) (sepc + 4) sepc

def validTrapExit (pre post : RegFrame) : Prop :=
  (∀ r : Nat, r ≤ 31 → post.gprs r = pre.gprs r) ∧
  post.nextIp = trapNextIp pre.scause pre.sepc ∧
  mprvClear post.sstatus = true

theorem trap_nextIp_cases (pre post : RegFrame) (h : validTrapExit pre post) :
    ((pre.scause = 8 → post.nextIp = pre.sepc + 4) ∧
     (pre.scause ≠ 8 → post.nextIp = pre.sepc)) := by
  cases h with
  | intro _ h_rest =>
      cases h_rest with
      | intro h_ip _ =>
          constructor
          · intro h_ecall
            rw [h_ecall] at h_ip
            dsimp only [trapNextIp, eqNat, cond] at h_ip
            exact h_ip
          · intro h_fault
            rw [h_ip]
            dsimp only [trapNextIp]
            have h_b : eqNat pre.scause 8 = false := by
              cases h_eq : eqNat pre.scause 8 with
              | false => rfl
              | true =>
                  have h_eq' : pre.scause = 8 := eqNat_true_eq pre.scause 8 h_eq
                  nomatch h_fault h_eq'
            rw [h_b]
            rfl

end Anneal.Sys.TrapContract
```

### Demonic SharedFetchOracle Contracts for TOCTOU-Free DMA and IoRing Descriptors

Device drivers and kernel `IoRing` handlers parse descriptors in shared pages that peers, hypervisors, or bus-mastering DMA engines can overwrite between loads—classic double-fetch TOCTOU bugs (Wang et al., USENIX Security 2017, `ISBN 978-1-931971-40-9`). **Basis: documentation.**

1. **Snapshot isolation in `VeriSMo` (`microsoft/verismo@5e1c159aec20491653550e39b00bd0855f543a7e`):** In `snp/ghcb/proto_page.rs` (L17–165) and `snp/ghcb/proto_s.rs`, `VeriSMo` separates private RAM from `SwSnpMemAttr::shared()` memory (`GhcbVmsa`, `GhcbPage`), reading fields via `copy_with` snapshots into local verified structs before validation and bounding hypervisor updates via `is_none_or_sharedmem` (`core_exit_t.rs`). **Basis: source.**
2. **Demonic `SharedFetchOracle` over `Trusted.MirSemantics`:** Because `ValidChoice` is single-trace deterministic (`c = 0`, `MirSemantics.lean` L643–647), TOCTOU races model cleanly without adding scheduler nondeterminism to `Trusted` by parameterizing shared reads over `oracle : Nat → SharedSqe` and quantifying universally (`∀ oracle, SatisfiesPost ...`):
   - A *double-fetch* parser checks `hdr := oracle 0` (`hdr.off + hdr.len ≤ cap`) then copies via `payload := oracle 1` (`reval_pkg2.py`); instantiating `oracle(0) = {off: 0, len: 8}, oracle(1) = {off: 0, len: 4096}` yields an OOB counterexample (`oob_ub`).
   - A *single-fetch* parser snapshots `snap := oracle 0` into owned stack/RAM before bounds checking, so every downstream read observes immutable private state (`∀ oracle, SatisfiesPost`). **Basis: derived, execution.**

### Evaluation Against Anneal Verification Criteria

Integrating `Anneal.Sys.PageWalk`, `Anneal.Sys.ShootdownPcm`, Sail-backed `TrapContract` companions, and universal `SharedFetchOracle` contracts scores across Anneal's seven criteria (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`) as follows: **Basis: derived, source.**

| Criterion | Hardware-Software Assessment | Mechanism / Tradeoff |
| :--- | :--- | :--- |
| **(T1) 0-TCB Bridge** | **Full pass on walks/oracles; companion trust on `asm!`** | `PageWalk`, `ShootdownPcm`, and `∀ oracle` stay in `theory/` (`0` TCB bloat); `TerminatorKind.unsupported` traps rely on Sail-audited companions. |
| **(P1) Human Spec Auditability** | **High clarity** | Explicit `PWC` vs. `LeafTLB`, `FramePhase`, and `∀ oracle` prevent hidden TLB or double-fetch assumptions. |
| **(P2) Authoring & Day-2 Locality** | **Strong modularity** | `SingleVa` vs. `byAsid`, `ackCore`, and single-fetch wrappers localize module invariants cleanly. |
| **(P3) Lean 4 `v4.34.1` & `<50ms` LSP** | **Pass with `cond` discipline** | Structuring `eqNat` + `cond` avoids heavy `Decidable` diamonds and keeps kernel checks fast. |
| **(P4) Heterogeneous Composability** | **Explicit seam composition** | Safe Rust, `∀ oracle` wrappers, SMP `ShootdownPcm`, and trap shims chain under `SatisfiesPost`. |
| **(P5) Failure Legibility** | **Concrete witnesses** | Single-VA PWC retention, un-acked cores, `sepc+4` errors, and `oracle` schedules (`len=8 -> 4096`) expose tiny bugs. |
| **(C1–C2) Conceptual Minimality** | **Minimal surface** | Avoids shared-memory concurrency inside `Trusted.MirSemantics`; three tiny `theory/` types suffice. |

## Boundaries

- **Live Lean `v4.34.1` compilation of distilled `Anneal.Sys.*` sketches (`not examined`):** `PageWalk`, `ShootdownPcm`, and `TrapContract` were checked syntactically against `trusted/audit/TrustedBoundary.lean` L442–596 (`prelude` + allowed term/tactic subsets) and tested operationally in Python, not elaborated inside an active `lake` project (`not examined`). **Basis: source.**
- **Direct MIR execution of `InlineAsm`, `sret`, `invlpg`, `sfence.vma`, and `vmmcall` (`unsupported`):** `Trusted/MirAst.lean` (L782–795) lowers `InlineAsm`, `Drop`, `Yield`, `CoroutineDrop`, and `TailCall` to `TerminatorKind.unsupported`, leaving raw trap instructions `unsupported` in `evalStep` without Sail-backed companion contracts. **Basis: source.**
- **Speculation, transient execution, and store buffers (`known not to apply`):** Architectural `pt_walk`/`VmemTlb`, `ArchVSpace_A`, and `SharedFetchOracle` omit speculative TLB prefetching and store-buffer reordering; transient leakage is `known not to apply` here (`anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal`). **Basis: documentation.**
- **`CortenMM`-scale annotation ratio in Lean `v4.34.1` (`unknown`):** Proof-to-code ratios and LSP latencies when scaling non-leaf PWC and SMP `ShootdownPcm` invariants across a full Rust kernel in Anneal remain `unknown` without end-to-end kernel benchmarking. **Basis: derived.**

## Evidence

| Primary Artifact / Paper | Pinned Identifier / SHA | Exact Inspected Scope | Basis |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` | `20aa204315cd36aaf944778b7d33c0d609ced8e8` | `TrustedBoundary.lean` L442–596, L1117–1366; `MirAst.lean` L782–795; `MirSemantics.lean` L643–647, L1597–1853 | `normative`, `source` |
| `microsoft/verismo` (OSDI 2024) | `5e1c159aec20491653550e39b00bd0855f543a7e`, `ISBN 978-1-939133-40-3` | `pgtable_e/tlb.rs` L12–36; `pgtable_e/pte.rs` L53–152; `arch/tlb/{def_s,tlb_s}.rs`; `registers/core_exit_t.rs` L6–59; `snp/ghcb/proto_page.rs` L17–165 | `source`, `documentation` |
| `TELOS-syslab/CortenMM-Artifact` (SOSP 2025) | `604592d815cb1cb7d4619f202b5d7ff471a3a7af`, `doi:10.1145/3731569.3764836` | `VERIFICATION_WALKTHROUGH.md` L43–78; `lock-protocol-rcu/src/spec/rcu/tree.rs` L21–220 (`cursors`, `strays`); `1.2×–26×` Linux speedups | `source`, `documentation` |
| `rems-project/islaris` (PLDI 2022) | `c978e10f50db5c40f0fdf113f5f76a779782c6f9`, `doi:10.1145/3519939.3523434` | `README.md` L48–118; `theories/opsem.v` L63–189 (`isla_trace`, `valu_shape`); `lifting.v` L87–139; `adequacy.v` L91–145; `riscv64/sys_regs.v` | `source`, `documentation` |
| `opencompl/sail-riscv-lean` | `51c635c460125ac87955d061fcd902ce03b8011f` | `LeanRV64D/Vmem.lean` L256–371, L406–559 (`pt_walk`, `PTW_Misaligned`); `LeanRV64D/VmemTlb.lean` L246–351 (`flush_TLB_Entry` L279); `Step.lean` | `source` |
| `riscv/riscv-isa-manual` & Syeda–Klein (JAR 2020) | `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `doi:10.1007/s10817-019-09539-7` | `Sv39` translation rules, `sfence.vma` operand semantics, split PWC vs. leaf TLB reasoning | `normative`, `documentation` |
| `seL4/l4v` & `seL4/seL4` | `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` | `X64/ArchVSpace_A.thy` L32–89, L146–292; `RISCV64/ArchVSpace_A.thy` L85–190; `src/arch/riscv/traps.S` L24–147 (35-word frame, `scause == 8`) | `source` |
| `asterinas/vostd` & `asterinas/asterinas` | `eb1a9d044617c2abff58f959ccc50f9571d561e9`, `7fecb4ffabc72d0767277a9ffb66168bc512034c` | `ostd/src/mm/tlb.rs` L68–185 (`OpsStack`, `ACK_REMOTE_FLUSH`, `irq::is_local_enabled` L171); `ostd/specs/mm/tlb.rs` L29–88 | `source` |
| Double-Fetch Analysis (Wang et al., USENIX'17) | `ISBN 978-1-931971-40-9` | Shared-memory TOCTOU double-fetch taxonomy across kernel/device boundaries | `documentation` |

## Revalidation

Executed cleanly on `2026-11-20` with Python 3 (`Basis: execution`). The standalone script validates: (1) 3-level `Sv39` and 4-level x86-64 page-table walks plus misaligned gigapage faulting and `sfence.vma` PWC / `G=1` preservation (`VmemTlb.lean:279`), (2) multi-core `FramePcm` gating frame reclamation until all `0b111` cores acknowledge flush, (3) `seL4` `traps.S` register-frame preservation and `NextIP` advance (`scause == 8`), and (4) adversarial `SharedOracle` double-fetch out-of-bounds refutation (`oob_ub`) vs. single-fetch snapshot safety.

```python
import time

t0 = time.perf_counter()

# 1. Multi-level Sv39 (3 levels) & x86-64 (4 levels) walk + PWC vs INVLPG/SFENCE.VMA
def canon_ok(va, top_bit):
    sign = (va >> top_bit) & 1
    upper = va >> top_bit
    return upper == ((1 << (64 - top_bit)) - 1 if sign else 0)

def pt_walk(mode, mem, root_ppn, va):
    top_bit, start_lvl = (38, 2) if mode == "sv39" else (47, 3)
    if not canon_ok(va, top_bit):
        return ("fault", "non_canonical", None)
    cur_ppn = root_ppn
    for lvl in range(start_lvl, -1, -1):
        idx = (va >> (12 + 9 * lvl)) & 0x1ff
        pte = mem.get((cur_ppn, idx))
        if not pte or not pte["v"]:
            return ("fault", f"invalid_l{lvl}", cur_ppn)
        if pte["leaf"]:
            align_mask = (1 << (9 * lvl)) - 1
            if (pte["ppn"] & align_mask) != 0:
                return ("fault", f"misaligned_superpage_l{lvl}", cur_ppn)
            off_bits = 12 + 9 * lvl
            pa = (pte["ppn"] << 12) | (va & ((1 << off_bits) - 1))
            return ("ok", pa, lvl, pte.get("global", False))
        if lvl == 0:
            return ("fault", "nonleaf_at_l0", cur_ppn)
        cur_ppn = pte["ppn"]
    return ("fault", "unreachable", None)

mem_sv39 = {
    (0x100, 0): {"v": True, "leaf": False, "ppn": 0x101},
    (0x101, 0): {"v": True, "leaf": False, "ppn": 0x102},
    (0x102, 2): {"v": True, "leaf": True, "ppn": 0x80000, "global": True},
    (0x100, 1): {"v": True, "leaf": True, "ppn": 0x80001, "global": False},  # misaligned 1G gigapage
}
assert pt_walk("sv39", mem_sv39, 0x100, 0x2000)[0:2] == ("ok", 0x80000000)
assert pt_walk("sv39", mem_sv39, 0x100, 1 << 30) == ("fault", "misaligned_superpage_l2", 0x100)

mem_x64 = {
    (0x200, 0): {"v": True, "leaf": False, "ppn": 0x201},
    (0x201, 0): {"v": True, "leaf": False, "ppn": 0x202},
    (0x202, 0): {"v": True, "leaf": False, "ppn": 0x203},
    (0x203, 5): {"v": True, "leaf": True, "ppn": 0x90000, "global": False},
}
assert pt_walk("x86_64", mem_x64, 0x200, 0x5000)[0:2] == ("ok", 0x90000000)

# Hardware PWC vs leaf TLB invalidation model (matching RISC-V Priv Spec & sail_VmemTlb.lean:279)
pwc = [("asid1", 0x2000, 1, False)]   # non-leaf L1 directory PWC entry
tlb = [("asid1", 0x2000, 0, True)]    # global (G=1) L0 leaf entry
def sfence_vma(va, asid):
    global tlb, pwc
    if va is None and asid is None:
        tlb, pwc = [], []
    elif va is None:
        tlb = [e for e in tlb if e[3] or e[0] != asid]
        pwc = [e for e in pwc if e[3] or e[0] != asid]
    else:
        # When rs2 != x0 (asid != None), global entries (e[3]==True) are NOT flushed,
        # and non-leaf PWC entries (level > 0) need NOT be flushed by single-VA sfence.vma!
        tlb = [e for e in tlb if e[3] or not (e[0] == asid and e[1] == va)]

sfence_vma(0x2000, "asid1")
assert len(pwc) == 1 and len(tlb) == 1  # single-VA leaves L1 PWC AND G=1 entry!
sfence_vma(None, "asid1")
assert len(pwc) == 0 and len(tlb) == 1  # ASID flush clears PWC, keeps G=1!
sfence_vma(None, None)
assert len(pwc) == 0 and len(tlb) == 0  # global flush clears all

# 2. SMP ShootdownPcm blocking premature reclamation across cores
class FramePcm:
    def __init__(self, cores_mask):
        self.state = "mapped"
        self.pending_mask = cores_mask
    def unmap(self, active_mask):
        assert self.state == "mapped"
        self.state, self.pending_mask = "unmapped_pending", active_mask
    def ack_core(self, core_id):
        if self.state == "unmapped_pending":
            self.pending_mask &= ~(1 << core_id)
            if self.pending_mask == 0:
                self.state = "reclaimable"
    def free_frame(self):
        if self.state != "reclaimable":
            return False
        self.state = "freed"
        return True

f = FramePcm(0b111)
f.unmap(0b111)
f.ack_core(0)
assert not f.free_frame()  # cores 1 and 2 may still hold stale TLB entries!
f.ack_core(1)
assert not f.free_frame()
f.ack_core(2)
assert f.free_frame()

# 3. seL4 traps.S register-frame contract (scause == 8 advances sepc+4; fault preserves sepc)
def trap_handle_and_sret(regs, scause, sepc):
    saved = dict(regs)
    next_ip = sepc + 4 if scause == 8 else sepc
    return saved, next_ip

u0 = {f"x{i}": i * 17 for i in range(1, 32)}
s_ecall = trap_handle_and_sret(u0, 8, 0x80001000)
s_fault = trap_handle_and_sret(u0, 12, 0x80001000)
assert s_ecall == (u0, 0x80001004) and s_fault == (u0, 0x80001000)

# 4. Demonic SharedFetchOracle refuting double-fetch on IoRing SQE
class SharedOracle:
    def __init__(self, sched):
        self.sched = sched
        self.gen = 0
    def read_sqe(self):
        val = self.sched[min(self.gen, len(self.sched) - 1)]
        self.gen += 1
        return val

adv = SharedOracle([{"len": 8, "off": 0}, {"len": 4096, "off": 0}])
def double_fetch(ora, buf_cap=64):
    hdr = ora.read_sqe()
    if hdr["off"] + hdr["len"] > buf_cap:
        return "rejected"
    payload = ora.read_sqe()  # TOCTOU double-fetch!
    return "oob_ub" if payload["off"] + payload["len"] > buf_cap else "ok"

def single_fetch_snap(ora, buf_cap=64):
    snap = dict(ora.read_sqe())
    if snap["off"] + snap["len"] > buf_cap:
        return "rejected"
    return ("ok", snap["off"], snap["len"])

assert double_fetch(adv) == "oob_ub"
adv2 = SharedOracle([{"len": 8, "off": 0}, {"len": 4096, "off": 0}])
assert single_fetch_snap(adv2) == ("ok", 0, 8)

dt_ms = (time.perf_counter() - t0) * 1000.0
print(f"pkg2 revalidation passed in {dt_ms:.3f} ms")
```

Running `python3 reval_pkg2.py` exited `0` with stdout `pkg2 revalidation passed in 0.116 ms`.
