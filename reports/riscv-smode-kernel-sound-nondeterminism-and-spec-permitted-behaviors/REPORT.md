# RISC-V S-Mode Kernels: Spec-Permitted Nondeterminism, Reference-Model Choices, and a Minimal Sound Environment

## Summary

This report covers a single-hart RV64 S-mode kernel: RV64IM + Zicsr + Zifencei + Zalrsc, traps and `sret`, `ecall`
to an SBI firmware (TIME, DBCN, SRST), Sv39 user address spaces with ASIDs, `sfence.vma`, `fence.i`, LR/SC, a timer
interrupt and a `wfi` idle loop. Verified claims about such a kernel must admit every behaviour the RISC-V
specification permits. The executable references (Sail, Spike, QEMU) each fix that nondeterminism differently and
more narrowly. The points worth retaining:

1. **Translation caching is per level and includes invalid entries.**
   - The privileged spec lets every step-2 PTE read be cached, including V=0 entries, with arbitrary capacity.
     Caches may be filled speculatively whenever `satp` is active, and only a subsuming `sfence.vma` empties them.
   - The spec also says an implicit read returns "any translation … valid at any time since the most recent
     SFENCE.VMA". These two statements are **not equivalent**: per-level caching can combine a stale non-leaf PTE
     with a fresh read of a repurposed table and produce a translation that was never valid (probe P1).
   - A sound model must take the per-level reading. `sfence.vma rs1=x0` before reusing a page-table frame makes
     the two readings coincide.
2. **Sail can do something the spec forbids, found by source reading only.**
   - On a TLB hit with hardware A/D updating enabled, Sail at `ec5200bd` writes the *cached* PTE (with A/D set)
     back to memory without comparing it against memory.
   - The spec's step 9 requires an atomic compare-and-retry and says the translation cache "cannot be used in
     step 9".
   - This has not been confirmed by running Sail. Any correspondence "trusted model ⊇ Sail" must make that path
     unreachable.
3. **Reference models hide bugs a sound model must catch.** None of Sail, Spike or QEMU caches non-leaf or invalid
   PTEs.
   - Spike and QEMU flush the TLB on every `satp` change.
   - QEMU clears the LR/SC reservation on every trap and xRET, and treats `fence.i` as a no-op with coherent
     self-modifying code.
   - Missing `sfence.vma` after an ASID switch, a missing dummy SC on context switch (probe P2), and a missing
     `fence.i` are therefore undetectable on some or all of them.
4. **ASIDLEN aliasing.** ASIDLEN is unspecified and may be 0. Both `satp` and `sfence.vma` ignore ASID bits at or
   above ASIDLEN. Address spaces whose kernel ASIDs differ only above ASIDLEN share hardware tags.
5. **No authoritative formal reference exists for the hard parts.** The RVWMO chapter states that the
   interaction with I/O, instruction fetch, `fence.i`, page-table walks and `sfence.vma` "is not (yet) formalized".
   No formal semantics of SBI or OpenSBI was found. Fidelity for these parts must be argued clause by clause
   against the prose specification.
6. **SBI v3.0 is internally inconsistent on one error code.** The DBCN tables return `SBI_ERR_INVALID_PARAM` for a
   bad buffer. The generic shared-memory rule says the implementation "MUST" return `SBI_ERR_INVALID_ADDRESS`.
   OpenSBI returns INVALID_PARAM. DBCN write may write only part of the buffer.
7. **A minimal sound environment** (derived, §10) consists of:
   - a per-boot platform parameter record Π;
   - per-level translation history since the last fence;
   - environment steps between instructions: time, interrupt-pending edges with delay, interrupt-taking latency,
     and opaque M-mode excursions;
   - `wfi` as `skip` plus environment steps;
   - SC outcome: may always fail, may succeed only under the spec's conditions;
   - fetch of bytes written since the last `fence.i` treated as an error;
   - SBI result sets;
   - arbitrary initial CSR state;
   - user steps that can change unsaved user-visible state.

   A short kernel discipline list turns most remaining spec freedom into checked proof obligations.

## Applicability

**Target regime.** One RV64 hart running an S-mode kernel compiled for RV64IM + Zicsr + Zifencei + Zalrsc, with U-mode
user tasks in Sv39 address spaces, under an SBI implementation in M-mode. The hart may implement more extensions than
the kernel uses; this matters for user-mode steps (§10). Multi-hart shootdown, the hypervisor extension, Svpbmt,
Svnapot, pointer masking and CFI extensions are out of scope except where noted.

**Normative baseline.** The ISA manual is cited at a development snapshot and at three releases:

| Version | Commit | Notes |
| --- | --- | --- |
| Development snapshot | `riscv/riscv-isa-manual@c05f1725f25526dd8463bac6ca75cfcfbee17d05` (2026-11-19) | Line numbers below refer to this tree unless stated otherwise. |
| Ratified release `20250508` | `584390d9d872835b1bc45ab9ea946b56db3ad485` | Latest release. |
| Release `20240411` | `6ee57d8997021aaa8025e208164763fe12e03c19` | Privileged 1.13. |
| Tag `Priv-v1.12` | `98964261c931d51884f733664b22efe43de93033` | Privileged 1.12, LaTeX sources. |

For each normative claim, the text was diffed or grepped across these four versions. Differences are stated where
they exist; otherwise the clause is present in all four.

**Reference implementations and models compared.**

- Sail RISC-V model `riscv/sail-riscv@ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`.
- Spike `riscv-software-src/riscv-isa-sim@e53c8ccf3448ae459877ed3236cb39b2a1d493bf`.
- QEMU `qemu/qemu@08ed97c33c3818ef51a7c852347a28e9f66807b5` (`target/riscv/`).
- OpenSBI `riscv-software-src/opensbi@61f1973bd50338b36c52dc34006f76d464ca4f34` (134 commits after `v1.9` =
  `cbf9f6734dd85a982c63e3cb5db7ffe09da839ca`).
- SBI specification `riscv-non-isa/riscv-sbi-doc` tag `v3.0` = `c33ad9f414505806f084e8677e04d2744f76c8df`.
- Research and verification artefacts: `daniellustig/riscv_axiomatic@0cc125df660a45160ed1602b61b288d2d6f01b26`,
  `uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`, `CharlyCst/miralis@f5ab1955192833ac025a6719a71c6e36a3f643ab`,
  `IBM/ACE-RISCV@42cf582eef21f9ab661ec7008d65c6de141b4be1`.

The relationship among subjects is a comparison: what the specification permits (normative) versus what each
implementation or model chooses (source).

**Not executed.** Sail, Spike, QEMU and OpenSBI were not built or run for this report; their behaviour is from source
reading. The two probes are Lean 4 v4.34.1 counterfactual formulations of spec clauses.

**Related packages, for context only.**

- `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` (same ISA-manual and sail-riscv revisions):
  - the cross-ISA `SFENCE.VMA` / `TLBI` / `INVLPG` matrix;
  - seL4's operand choices;
  - Sail's leaf-only TLB and `fence.i` no-op as under-approximations;
  - a compiled ghost dirty-set automaton (`DirtyPteEntry`, `icacheDirtyPpn`).
  This report does not repeat those. It adds per-level staleness, the Sail A/D deviation, Spike/QEMU choices, and the
  non-TLB topics.
- `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config`: Sail's TLB internals (hit-path permission re-check, no flush on `satp` writes, superpage
  duplication) and the 75-axiom Lean import file.
- `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`: oracle models for memory written by DMA or untrusted peers.
- `sel4-riscv64-abi-fastpath-revocation-and-l4v-infoflow`: seL4/l4v's RISCV64 machine interface. It models no TLB,
  cache or reservation, axiomatises the interrupt oracle, and has a dummy `sc.w` only on the slowpath.
- `riscv64-sv39-opensbi-trap-wx-and-sail-lean-semantics`: OpenSBI boot state.

## Findings

### 1. Address-translation caching

#### 1.1 The normative cache

Basis: normative.

- **What may be cached.** `src/priv/supervisor.adoc` L1769–1778, `[[sv32algorithm]]`: "The results of implicit
  address-translation reads in step 2 may be held in a read-only, incoherent *address-translation cache* but not
  shared with other harts. The address-translation cache may hold an arbitrary number of entries, including an
  arbitrary number of entries for the same address and ASID. Entries in the address-translation cache may then
  satisfy subsequent step 2 reads if the ASID associated with the entry matches the ASID loaded in step 1 or if the
  entry is associated with a *global* mapping."
- **Invalid entries.** L1338–1341: "This specification permits the caching of PTEs whose V (Valid) bit is clear."
- **Speculative fill.** L1797–1808: walks may run "speculatively at any time, for any virtual address, as long as
  `satp` is active". Speculative walks must not set D, must not raise exceptions, and "must not create
  address-translation cache entries if those entries would have been invalidated by any SFENCE.VMA instruction
  executed by the hart since the speculative execution of the algorithm began". L1831–1834: "at any time, all page
  table entries reachable by executing the algorithm may be loaded into the address-translation cache."
- **Where walks may go.** L1344–1349: implicit reads only follow `satp` and subsequent V=1 entries. Exceptions are
  raised only for non-speculative walks.
- **satp active.** L1106–1120: `satp` is *active* in effective S/U mode. Walks that began while active "are not
  required to complete or terminate when `satp` is no longer active", for example while M-mode firmware runs,
  "unless an SFENCE.VMA instruction matching the address and ASID is executed".
- **Version check.** Present at `20240411` (step-3 clause L1362, speculative-A clause L1266), at `20250508` (L1541,
  L1442) and at `Priv-v1.12` (`src/supervisor.tex` L1292 V=0 caching, L1678 reserved bits, L1760 speculative walks).

#### 1.2 Per-level caching admits translations that were never valid (probe P1)

Basis: normative + execution (probe) + derived.

- **Summary clause.** L1285–1288, `[[norm:sfence_vma_ordering_semantics]]`: "An implicit read of the
  memory-management data structures may return any translation for an address that was valid at any time since the
  most recent SFENCE.VMA that subsumes that address."
- **Algorithm clause.** §1.1 caches *step-2 read results*, one per level. A walk may therefore use a cached stale
  non-leaf PTE pointing at old table A and then read A's slot from memory after software has repurposed A's frame.
- **Probe P1** (`support/PerLevelStaleTranslation.lean`) builds the history m0 (root→A, A→P) → m1 (root→B, B→Q) →
  m2 (A's slot rewritten to R).
  - Theorem `perLevel_admits_never_valid` shows R is produced under per-level caching but is not the translation of
    any snapshot.
  - Theorem `fenced_no_gap` shows that a fence between retargeting the root and reusing A removes the gap.
- *Derived:* a model that is sound with respect to the algorithm text must use the per-level reading. The spec's own
  advice closes the gap. L1376–1379: "If software modifies a non-leaf PTE, it should execute SFENCE.VMA with
  rs1=x0." L1784–1794 likewise allows old non-leaf and new leaf entries to coexist.

#### 1.3 Implicit reads are unordered with the hart's own stores

Basis: normative.

- L1185–1189: implicit references "are ordinarily not ordered with respect to explicit loads and stores."
- L1296–1298: "These implicit loads also need not otherwise obey normal program order semantics with respect to
  prior loads or stores to the same address."
- L1306–1313: after an unfenced leaf change, "either the new translation or any older translation since the last
  subsuming SFENCE.VMA was executed will be used … subsequent accesses to the same virtual address might use
  different translations from that set."
- Observable outcomes therefore include the old mapping, an old fault (cached V=0), the new mapping, or a per-level
  mix (§1.2). They can differ between consecutive accesses.
- L1384–1389: for permission upgrades and invalid→valid changes, software may fence lazily, but "a page-fault
  exception might occur".
- L1331–1334: updating a PTE with narrower stores is unsafe, because the walker may read it "at any time".
- **New at the snapshot, absent at `20250508`** (L1315–1322): staleness applies "even if the virtual-address width
  for that translation differs from the width currently specified by `satp`.MODE", and a global stale translation
  may be used "regardless of both ASID and virtual-address width".

#### 1.4 What `sfence.vma` guarantees, and the ASIDLEN aliasing hazard

Basis: normative + derived.

| rs1, rs2 | Orders | Invalidates |
| --- | --- | --- |
| x0, x0 | all levels, all address spaces | all entries |
| x0, ≠x0 | all levels for ASID rs2 except global mappings | entries matching ASID, except global |
| ≠x0, x0 | leaf PTEs for VA rs1, all address spaces | leaf entries for VA, all ASIDs, *including global* |
| ≠x0, ≠x0 | leaf PTEs for VA rs1 in ASID rs2, except global | leaf entries for VA and ASID, except global |

Sources and related rules:

- The table: L1232–1259.
- An invalid VA in rs1 makes `sfence.vma` a no-op without a trap (L1261–1264). Over-fencing is always legal
  (L1266–1275).
- With rs2≠x0, bits SXLEN-1:ASIDMAX are reserved, and "if ASIDLEN<ASIDMAX, the implementation shall ignore bits
  ASIDMAX-1:ASIDLEN of the value held in rs2" (L1277–1283).
- `sfence.vma` is local to the hart (L1209–1210). Writing `satp` "does not imply any ordering constraints between
  page-table updates and subsequent address translations, nor does it imply any invalidation of address-translation
  caches" (L1122–1124).
- Changes to SUM, MXR, `satp`.MODE and `satp`.ASID take effect immediately (L1351–1356).
- ASID-recycling protocol: L1363–1369. Rules for modified non-leaf/leaf PTEs with G on the path: L1376–1383.
- With `mstatus.TVM=1`, S-mode `satp` access and `sfence.vma` raise illegal-instruction (`src/priv/machine.adoc`
  L728–734).

The cross-ISA counterparts of this table, and how seL4 uses these forms, are in package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` §2. Only the
RISC-V rules needed below are kept here.

**ASIDLEN aliasing** (derived).

- `[#norm:asidlen]` (L1054–1060): "The number of ASID bits is UNSPECIFIED and may be zero." Only `ASID[ASIDLEN-1:0]`
  is writable, and ASIDLEN is discovered by write-ones/read-back.
- Combined with the rs2 rule above, two address spaces whose kernel-assigned ASIDs differ only above ASIDLEN share
  one hardware tag. Stale entries of one then satisfy walks of the other.
- A sound model takes ASIDLEN ∈ [0,16] as a platform parameter and tags entries with `asid mod 2^ASIDLEN`.
- Kernel discipline: discover ASIDLEN at boot and keep at most 2^ASIDLEN live tags. With ASIDLEN=0, execute
  `sfence.vma x0, r` with r holding 0 after every `satp` write; L1370–1375 recommends exactly this, sparing global
  entries.

#### 1.5 Svvptc and Svinval

Basis: normative + derived.

- **Svvptc** (`src/priv/svvptc.adoc`, `[#norm:Svvptc_explicit_stores_update_valid_bit]`): V 0→1 stores "will
  eventually become visible within a bounded timeframe". This is a liveness bound only. The note still allows an
  "occasional gratuitous additional page fault".
- **Svinval** (`src/priv/svinval.adoc`): `SFENCE.W.INVAL; SINVAL.VMA*; SFENCE.INVAL.IR` has "the same effect as a
  hypothetical SFENCE.VMA" with the same rs1/rs2. With TVM=1 only SINVAL.VMA traps.
- *Derived:* a kernel that does not use Svinval need not model it. Svvptc only removes behaviours, so ignoring it is
  sound.

#### 1.6 How reference implementations choose

Basis: source + documentation.

| Choice | Specification | Sail `ec5200bd` | Spike `e53c8ccf` | QEMU `08ed97c3` |
| --- | --- | --- | --- | --- |
| Status of the TLB | permitted cache of arbitrary size | Explicitly non-architectural: `model/sys/vmem_tlb.sail` L9–13, "Although a TLB is not part of the RISC-V Architecture specification, we model a simple TLB so that (1) we can meaningfully test SFENCE.VMA … (2) we can greatly speed up simulation"; also `model/sys/vmem.sail` L20–29 | software TLB | softmmu TLB |
| Non-leaf / V=0 entries | permitted | leaf only; no V=0 entries | leaf only | leaf only; faults not cached |
| Flush on `satp` write | not implied (L1122–1124) | none: `model/sys/vmem.sail` L297–298 call only `legalize_satp` | flushes TLB and decode cache when the value changes: `riscv/csrs.cc` L1269–1274; `riscv/mmu.cc` L61–68 | flushes on any MODE/ASID/PPN change: `target/riscv/tcg/csr.c` L2000–2024 (`legalize_xatp` → `tlb_flush`) |
| Global entries on ASID-scoped flush | kept | kept: `vmem_tlb.sail` L142–143, `asid_matches = ent.asid == asid & not(ent.global)` | not examined | not examined |

- More Sail TLB detail (hit-path permission re-check, superpage duplication) is in package `sail-riscv-lean-extraction-provenance-extern-axioms-and-privileged-config` §8.
  Package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` §1 analyses the leaf-only design as an under-approximation.
- *Derived:* none of the three exhibits per-level staleness or cached faults. Spike and QEMU cannot exhibit stale
  entries across a `satp` switch, so ASID-reuse and missing-fence-after-switch bugs are invisible on them.
- Serval's RISC-V interpreter treats `sfence.vma` as `skip` and has no virtual memory
  (`serval/riscv/interp/r-type.rkt` L91).

#### 1.7 Sail's TLB-hit A/D write-back is outside the spec envelope

Basis: source + normative + derived. **Found by source reading. Not confirmed by running Sail.**

- In `model/sys/vmem.sail` at `ec5200bd`, `translate_TLB_hit` (L370–413) takes the PTE from the cached entry:
  `let pte = tlb_get_pte(pte_size, ent);  // Step 2 of VATP.` (L386).
- It then calls `update_and_write_pte(ent.pteAddr, pte_size, pte, access, stage, ext_ptw)` (L401).
- `update_and_write_pte` (L95–119) computes the A/D-updated value from that cached `pte`. When `hw_updates_pte(stage)`
  holds, it stores the value with `write_pte(write_paddr, pteWidth, pte)`, with no comparison against the current
  memory contents.
- `hw_updates_pte` (`model/sys/vmem_pte.sail` L302–309) holds when Svadu is enabled with `menvcfg.ADUE=1`, or when
  neither Svadu nor Svade is supported. The latter is described as "the current default".
- The specification's step 9 (`supervisor.adoc` L1739–1749) says to perform atomically: "Compare *pte* to the value
  of the PTE at address a+va.vpn[i]×PTESIZE. If the values match, set *pte*.a to 1 … Then store *pte* … If the
  comparison fails, return to step 2." L1780–1781 adds: "The address-translation cache cannot be used in step 9;
  accessed and dirty bits may only be updated in memory directly."
- *Derived:* consider software that rewrites a leaf PTE without `sfence.vma` while a stale TLB entry for it exists.
  An access that hits the TLB and needs an A/D update makes Sail write the *old* PTE contents back over the new
  value. The spec forbids this: the compare would fail and the walk would restart.
- *Derived consequences:*
  - Sail is not a pure under-approximation of the spec on HW-A/D configurations.
  - A correspondence of the form "every Sail behaviour is a trusted-model behaviour" must exclude this path. Options:
    an Svade-only configuration, states where every TLB entry matches memory, or a kernel discipline under which
    step 9 never fires (§3, discipline D-AD).

### 2. Instruction fetch, `fence.i`, Ziccif and Ziccid

**2.1 Base ISA.** Basis: normative.

- `src/unpriv/zifencei.adoc` L66–80: "RISC-V does not guarantee that stores to instruction memory will be made
  visible to instruction fetches on a RISC-V hart until that hart executes a fence.i instruction". Also
  `[[norm:fence-i_op]]`: "A fence.i instruction orders all explicit memory accesses and instruction fetches that
  precede the fence.i in program order before all instruction fetches that follow the fence.i in program order."
- L107–108: "An instruction fetch is always ordered before any explicit memory accesses that instruction gives
  rise to."
- No clause bounds what a fetch returns for bytes written since the hart's last `fence.i`, and none guarantees fetch
  atomicity without Ziccif.

**2.2 Ziccif and Ziccid.** Basis: normative + documentation.

- `src/unpriv/ziccif.adoc` (`[[norm:Ziccif_if_atomicity]]`): with Ziccif, naturally aligned fetches of
  ≤ min(ILEN,XLEN) bits are atomic. It defines an operational fetch state machine and safe-harbour rules for
  concurrent code modification.
- `src/unpriv/ziccid.adoc` gives an operational model:
  - fetches appear in the global memory order, in program order (`[#norm:Ziccid_fetch_global_order]`);
  - each hart has a bounded instruction buffer (`[#norm:Ziccid_fetch_order]`);
  - stores *eventually* become visible to fetches;
  - FENCE.I makes older explicit accesses globally visible, then flushes the buffer (`[[norm:Ziccid_fence-i_op]]`);
  - the model applies only to coherent, cacheable PMA regions (`[#norm:Ziccid_model_scope]`).
- **Status.**
  - Ziccid was added by commit `f0b597df25de3f8304dbfc2bb9a02d4696b82b2a` (2026-06-11, "Add Ziccid draft spec").
  - `src/unpriv/preface.adoc` L35 at the snapshot lists `ziccid 1.0` among modules "all of which have been
    ratified".
  - Ziccid is absent from release `20250508`.
  - `src/profiles/rva23.adoc` L181–184 still says Ziccid "might be added as an option in the future".
- **Implementations.** Spike implements Ziccid by mutual exclusion of store-TLB and instruction-TLB pages
  (`riscv/mmu.cc` L138–146, L352–358). Without Ziccid, Spike's decoded-instruction cache is flushed only by
  `fence.i`, a TLB flush or triggers (`riscv/mmu.cc` L55–68, L225–236, L455–459).
- QEMU (`target/riscv/tcg/insn_trans/trans_rvi.c.inc` L976–990): "FENCE_I is a no-op in QEMU, however we need to
  end the translation block". QEMU's self-modifying-code tracking keeps fetches coherent, so a missing `fence.i` is
  invisible.
- Sail's `execute FENCEI` only emits `sail_barrier(Barrier_RISCV_i)` (`model/extensions/Zifencei/zifencei_insts.sail`
  L24–31) over a single memory.

**2.3 Zicbom is not an ifetch fence.** Basis: normative.

- `src/unpriv/cmo.adoc` L180–184: CBO operations act on "coherent instruction caches" only as members of the set of
  coherent caches.
- L244–248: invalidate, clean and flush "are *not* ordered by other instructions that order stores, e.g. fence.i and
  sfence.vma".

**2.4 Relative order of `sfence.vma` and `fence.i` on one hart.** Basis: normative + derived.

- A fetch that follows both instructions in program order receives both guarantees: `fence.i` (zifencei L77–80)
  and `sfence.vma` (supervisor L1190–1196). Neither clause depends on their relative order.
- *Derived:* on a single hart either order is normatively sufficient for executing newly written code under a newly
  installed mapping. Placing `sfence.vma` first is a conservative choice, not a specification requirement.

### 3. Accessed and dirty bits

Basis: normative + source.

**Normative rules** (`supervisor.adoc` L1596–1690 and step 9 L1739–1749):

- Svade: an access with A=0, or a store with D=0, page-faults (L1604–1606).
- Without Svade, hardware updates:
  - the update is atomic with the walk checks, and is a compare-and-retry;
  - the A bit "may be performed as a result of speculation, even if the associated memory access ultimately is not
    performed architecturally";
  - D updates from explicit stores must be exact and in program order;
  - "a trap may occur between the PTE update and the memory access that caused the PTE update";
  - "The A and D bits are never cleared by the implementation";
  - page tables need hardware page-table-write and RsrvEventual PMAs (L1650–1651).
- `menvcfg.ADUE` (`machine.adoc` L2194–2207): with Svadu, ADUE=1 selects hardware update and ADUE=0 behaves as
  Svade. After changing ADUE, `sfence.vma x0,x0` suffices (L2209–2211).
- Non-leaf D/A/U are reserved and must be cleared by software (L1697–1699). Step 3 faults on any reserved bit
  (L1726).

**Version difference.**

- `Priv-v1.12` (`src/supervisor.tex` L1595–1618) says "Two schemes to manage the A and D bits are permitted" (fault
  or hardware update), with no control and no names.
- From `20240411` on: "When the Svade extension is not implemented, the following [hardware-update] scheme applies."
- The step-3 reserved-bits fault is already present at v1.12 (L1678).
- *Derived:* on a hart conforming only to v1.12 that advertises neither extension, the A/D scheme is unknown to
  software.

**OpenSBI** (`lib/sbi/sbi_hart.c` L131–169):

- It clears ADUE by default ("Disable HW A/D updating by default", L135).
- It sets ADUE only if Svadu is present and Svade is not.
- The comment at L160–165: "Assume only Svadu is supported when it is the only extension present in the ISA string.
  Svade is assumed when neither are present. When both are present we must default to Svade (see the zero reset
  value of FWFT.PTE_AD_HW_UPDATING)."
- *Derived:* the A/D scheme is also mutable at runtime through the SBI firmware-features (FWFT) extension, whose
  semantics are not examined here.

**Discipline D-AD.**

- A=1 on every valid leaf, D=1 iff W=1, never clear A/D, and non-leaf A=D=U=0.
- *Derived:* step 9's trigger condition is then never met on a permitted access. Both schemes, and Sail's §1.7 path,
  become unreachable. (Step 8 rejects stores to W=0 pages before step 9.)

### 4. WARL and WLRL CSRs visible to S-mode

Basis: normative + source.

**General rules** (`src/priv/csrs.adoc`):

- WARL writes never trap. "Implementations can return any legal value on the read of a WARL field when the last
  write was of an illegal value, but the legal value returned *should* deterministically depend on the illegal
  written value and the architectural state of the hart" (L668–672). Note the "should".
- WLRL: an illegal write may raise illegal-instruction, and later reads are arbitrary (L632–656).
- **Field modulation** (L676–690): if a write to one CSR changes the legal set of a field in another, that field
  "immediately gets an UNSPECIFIED value from among its new legal values … even if the field's value before the
  write remains legal".
- At reset: "No WARL field contains an illegal value" and "All other hart state is UNSPECIFIED" (`machine.adoc`
  ~L2776–2790).

**S-mode specifics** (`supervisor.adoc`):

| CSR | Rule |
| --- | --- |
| `satp` | Writing an unsupported MODE means "the entire write has no effect; no fields in `satp` are modified" (L1049–1052). ASIDLEN is discovered by read-back (L1054–1060). If MODE is read-only zero, `sfence.vma` may raise illegal-instruction (L1408–1411). |
| `stvec` | BASE is WARL, MODE ≥2 is reserved, and Vectored mode may require stricter alignment (L328–363). |
| `sip`/`sie` | "All bits in `sip` and `sie` are WARL" (L467–469). Each `sip` bit may be read-only (L400–405). STIP is read-only and SEE-driven without Sstc; with Sstc it reflects `stimecmp` (L431–439). |
| `scounteren` | Bits may be read-only zero, so they are "effectively WARL" (L517–521). |
| `sstatus` | UXL is WARL (L144). SUM and MXR must be writable when `satp`.MODE is not read-only zero (`machine.adoc` L599–625). FS/VS exist whenever the hart implements F/V, regardless of the kernel's ISA. |

Sail resolves these with a static JSON configuration, for example `"xtvec_mode": "Xtvec_Ignore"` (keep the old
mode on reserved writes, `config/config.json.in` L243–246) and `"asidlen"` (L331–336). QEMU's `legalize_xatp`
keeps the old `satp` on an invalid MODE (L2013–2023). *Derived:* each tool is one legal choice, not the envelope.

### 5. LR/SC reservations (probe P2)

**Normative envelope.** Basis: normative.

- **Reservation set.** "An implementation can register an arbitrarily large reservation set on each LR, provided
  the reservation set includes all bytes of the addressed data word or doubleword" (`src/unpriv/zalrsc.adoc`
  L91–93). With paged VM it lies within one 4 KiB physical page (`supervisor.adoc` L1701–1705).
- **SC may succeed only if** no store *from another hart* to the reservation set and no device write to the LR's
  bytes is observed, and there is no intervening SC (L94–99). It must fail in the converse cases (L117–125). **A
  store from the same hart is not a failure condition.** An SC to a different address inside the reservation set may
  succeed (L99–101: "this LR might have had a different effective address and data size").
- **Every SC kills the reservation.** "Regardless of success or failure, executing an SC instruction invalidates
  any reservation held by this hart" (L23–24).
- **Spurious failure.** SC "may spuriously fail for implementation reasons, provided progress is eventually made"
  (L266–270). Unconstrained sequences may always fail (L225–229).
- **Constrained loops** (≤16 instructions; only base-ISA instructions between LR and SC; no loads, stores, backward
  branches, JALR, FENCE or SYSTEM) carry an eventual-success guarantee unless the hart traps or exits the loop
  (L183–241). This is liveness only.
- **xRET.** "the xRET instruction is allowed to clear any outstanding LR address reservation but is not required
  to. Trap handlers should explicitly clear the reservation if required (e.g., by using a dummy SC) before executing
  the xRET" (`machine.adoc` L2667–2670).
- **Other clearing.** The context-switch dummy SC is recommended at zalrsc L137–142. No valid reservation exists
  after reset (`machine.adoc` L2777). No clause says traps or interrupts clear a reservation.

**Probe P2** (`support/LrScContextSwitch.lean`), with thread A doing LR, a switch to thread B which stores, and a
switch back for A's SC:

- `lost_update_permitted`: with no dummy SC, no clear on xRET, and no clear on a same-hart store, A's SC is
  permitted to succeed.
- `dummy_sc_sound`: with a dummy SC on every switch, the SC can never succeed, for every implementation choice.
- `qemu_like_masks_bug`: clearing on xRET hides the missing dummy SC.

**Implementation choices.** Basis: source.

| | Sail `ec5200bd` | Spike `e53c8ccf` | QEMU `08ed97c3` |
| --- | --- | --- | --- |
| Where state lives | outside the model (`model/sys/sys_reservation.sail` L8–24 externs) | `mmu_t::load_reservation_address` | `env->load_res` |
| Reservation set | config `reservation_set_size_exp` (default 3) and `require_exact_reservation_addr` (`config/config.json.in` L556–573) | mask match (`riscv/mmu.h` L276–293) | not examined |
| Cleared by a same-hart store | config `invalidate_on_same_hart_store` (default false; `c_emulator/riscv_model_impl.cpp` L67–69) | no | not examined |
| Cleared by xRET | config `invalidate_on_xret` (default false; `model/extensions/I/base_insts.sail` L650, L724) | no (`processor.cc`, `insns/sret.h`, `insns/mret.h` do not reference it) | **yes**, on every trap and xRET: `riscv_cpu_set_mode` sets `env->load_res = -1` (`target/riscv/tcg/cpu_helper.c` L937–962; called from L2385, L2471 and `op_helper.c` L371, L458) |
| Spurious SC failure | never (`riscv_model_impl.cpp` L250–270) | never | not examined |

QEMU's comment at L955–961 explains: "Version 2.2 of the ISA specification explicitly requires this behaviour, while
later revisions say that the kernel 'should' use an SC instruction … As a result, do both."

**Firmware leaves dangling reservations.** Basis: source + derived. OpenSBI's `spin_trylock` executes `lr.w.aq` and
branches out without an SC when the lock is held (`lib/sbi/riscv_locks.c` L22–45). After any M-mode excursion, the
S-mode reservation may therefore be unchanged, cleared, or replaced by an M-mode address.

*Derived:* an S-mode SC succeeds only in the "unchanged" case. An SC to the replaced address targets firmware memory,
which PMP protects from S-mode, so it would fault rather than succeed. For modelling, "reservation may be lost at any
M-mode excursion" is subsumed by spurious failure.

### 6. Interrupts, Sstc and `wfi`

**6.1 When an interrupt is taken.** Basis: normative.

- An interrupt *i* traps to S-mode if (priv=S ∧ SIE=1, or priv<S) ∧ `sip[i]` ∧ `sie[i]` (`supervisor.adoc` L382–386).
- L388–394: "These conditions for an interrupt trap to occur must be evaluated in a bounded amount of time from
  when an interrupt becomes, or ceases to be, pending in sip, and must also be evaluated immediately following the
  execution of an SRET instruction or an explicit write to a CSR on which these interrupt trap conditions expressly
  depend (including sip, sie and sstatus)."
- Priority order is SEI > SSI > STI (L485–487).
- *Derived:* model an unknown but bounded latency between "pending" and "taken". The interrupt may also never be
  taken if it stops being pending. The exception is immediately after `sret` or a write to `sip`, `sie` or
  `sstatus`.
- Sail dispatches pending-and-enabled interrupts at every step before fetch, i.e. zero latency
  (`model/postlude/step.sail` L115–133).

**6.2 Sstc versus SBI TIME.** Basis: normative + source.

- With Sstc, "If the result of this comparison changes, it is guaranteed to be reflected in STIP eventually, but
  not necessarily immediately". The spec warns that spurious timer interrupts are possible after advancing
  `stimecmp`. Text: `supervisor.adoc` L1145–1163 at the snapshot; `src/sstc.adoc` L37–54 at `20250508`.
- SBI v3.0 `src/ext-time.adoc`: `sbi_set_timer` "Programs the clock for next event after stime_value time … This
  function must clear the pending timer interrupt bit when stime_value is set to some time in the future, regardless
  of whether timer interrupts are masked or not. This function always returns SBI_SUCCESS". No latency bound is
  given.
- OpenSBI `lib/sbi/sbi_timer.c`:
  - with Sstc, `sbi_timer_smode_event_start` writes `stimecmp` directly;
  - otherwise it clears `mip.STIP` and arms an M-mode timer event (L283–300), whose callback sets `mip.STIP`
    (L265–275);
  - `menvcfg.STCE` is set iff Sstc is present (`lib/sbi/sbi_hart.c` L157).
- *Derived:* without Sstc, every supervisor timer tick passes through an M-mode MTIP trap. That trap can occur at
  any S/U instruction boundary, because M-level interrupts are globally enabled below M.

**6.3 `wfi`.** Basis: normative + source.

- `machine.adoc` L2705–2707: "Implementations are permitted to resume execution for any reason, even if an enabled
  interrupt has not become pending. Hence, a legal implementation is to simply implement the WFI instruction as a
  NOP."
- L2718–2727: WFI "must be unaffected by the global interrupt bits in mstatus (MIE and SIE) and the delegation
  register mideleg … but should honor the individual interrupt enables". The "should" means waking on
  pending-but-disabled interrupts is also permitted. WFI must resume for locally enabled interrupts pending at any
  privilege level.
- L2728–2729: with no trap, execution resumes at pc+4. L2694–2696: on a trap, `xepc` = pc+4.
- TW=1: an S-mode `wfi` that does not complete within a bounded time raises illegal-instruction, and may always do
  so (L747–757).
- OpenSBI never sets TW, TSR or TVM. `mstatus_init` writes only FS/VS (`lib/sbi/sbi_hart.c` L28–43). The only other
  `mstatus` write (L807, the mode-switch path) edits MPP/MPIE. No reference to `MSTATUS_TVM`, `MSTATUS_TSR` or
  `MSTATUS_TW` exists under `lib/` or `platform/`.
- Sail: S-mode `wfi` enters a wait state (`model/extensions/I/base_insts.sail` L751–767). It leaves the wait when
  `shouldWakeForInterrupt()` holds, i.e. `mip & mie ≠ 0` (`model/sys/sys_control.sail` L173). It also leaves when the
  externally supplied `exit_wait` input forces it, checking TW in that case (`model/postlude/step.sail` L23–80).
  Spurious resumption is therefore an input to the top-level step, not an internal choice.
- *Derived:* the wake set is `mip & mie`. It includes M-level MTIP armed by the firmware when Sstc is absent. An idle
  loop must re-check `sip` after each `wfi`.

### 7. The SBI environment

**7.1 No formal SBI semantics was found.** Basis: source + documentation; search-limited.

- Miralis (`CharlyCst/miralis@f5ab1955`, `model_checking/src/lib.rs`) checks M-mode *instruction emulation* with
  Kani against a Sail-derived Rust model. For example, its `mret()` proof compares `ctx.emulate_mret` with
  `model::execute_MRET`. It does not specify SBI calls. Package `riscv-privileged-isa-model-correspondence-prior-art` §6 covers its bounded checking against
  `softcore-rv64` in more detail.
- ACE (`IBM/ACE-RISCV@42cf582e`, `verification/readme.md`) verifies security-monitor allocator and page-table code
  with RefinedRust/Rocq.
- Serval (`uw-unsat/serval@72adc495`) treats `fence.i`, `sfence.vma` and `wfi` as `skip` and `sret` as
  `notimplemented` (`serval/riscv/interp/i-type.rkt` L71; `r-type.rkt` L81–91).

**7.2 SBI v3.0 contract for TIME, DBCN and SRST.** Basis: normative (`riscv-sbi-doc` tag `v3.0`).

- **Calling convention** (`src/binary-encoding.adoc`):
  - a7 holds the EID, a6 the FID, a0–a5 the arguments.
  - "All registers except a0 & a1 must be preserved across an SBI call by the callee."
  - a0 returns the error code. a1 "is unspecified unless explicitly defined" on error.
  - An unsupported EID or FID must return `SBI_ERR_NOT_SUPPORTED`.
  - Error codes: 0 SUCCESS, −1 FAILED, −2 NOT_SUPPORTED, −3 INVALID_PARAM, −4 DENIED, −5 INVALID_ADDRESS,
    −6 … −14 others.
- **TIME** (EID 0x54494D45, FID 0): see §6.2.
- **DBCN** (EID 0x4442434E, `src/ext-debug-console.adoc`):
  - write (FID 0): takes a *physical* address as lo/hi. "This is a non-blocking SBI call and it may do partial/no
    writes". Returns the number of bytes written. Errors: INVALID_PARAM, DENIED, FAILED.
  - read (FID 1): non-blocking.
  - write_byte (FID 2): blocking. Errors: DENIED, FAILED.
- **SRST** (EID 0x53525354, `src/ext-sys-reset.adoc`): "a synchronous call and does not return if it succeeds".
  Errors: INVALID_PARAM (reserved, or platform-specific and unimplemented, type/reason), NOT_SUPPORTED, FAILED.
- **HSM entry state** (`src/ext-hsm.adoc` L97–101, L237–241): `satp`=0, `sstatus.SIE`=0, a0=hartid, a1=opaque.
  "All other registers remain in an undefined state." The spec does not fix the boot hart's state.

**7.3 Internal inconsistency in SBI v3.0, and OpenSBI's choice.** Basis: normative + source + derived.

- The DBCN write/read tables give `SBI_ERR_INVALID_PARAM` when the buffer "does not satisfy the requirements
  described in" the shared-memory rule.
- That rule (`src/binary-encoding.adoc` L116–135) says: "The SBI implementation MUST check that the specified
  physical memory range is composed of accessible physical addresses and return SBI_ERR_INVALID_ADDRESS when any
  address in the range is not accessible." It also permits SBI_ERR_FAILED for stricter implementation-specific
  ranges.
- OpenSBI (`lib/sbi/sbi_ecall_dbcn.c` L19–60):
  - returns `SBI_ERR_FAILED` when a2 (the high address word) is non-zero;
  - returns `SBI_ERR_INVALID_PARAM` when the domain range check fails;
  - checks `SBI_DOMAIN_READ|SBI_DOMAIN_WRITE` even for console *write*;
  - registers DBCN only when a console device exists (L68–73), so otherwise the call returns NOT_SUPPORTED.
- OpenSBI SRST (`lib/sbi/sbi_ecall_srst.c` L15–40) maps unknown types or reasons to INVALID_PARAM and unsupported
  ones to NOT_SUPPORTED.
- *Derived:* the sound result set for DBCN write is error ∈ {0 with 0 ≤ value ≤ num_bytes, −1, −2, −3, −4, −5}.

### 8. RVWMO scope for one hart

Basis: normative + source + derived.

- **No normative model.** `src/unpriv/rvwmo.adoc` L28–33: "The interaction of the memory model with I/O memory,
  instruction fetches (Ziccif), fence.i, page-table walks, and sfence.vma is not (yet) formalized."
- **Research model.** The only virtual-memory-aware axiomatic model found, `daniellustig/riscv_axiomatic@0cc125df`
  (2021), says in its README that it "has not been officially adopted by RISC-V". It also states that rmem, herd and
  Alloy do not "yet support virtual memory and SFENCE.VMA semantics". It encodes implicit operations and
  `sfence_po` ordering in `riscv_axiomatic/rvwmo.py` (L58–160, L618–648). Its litmus tests include
  `PTE_activate_satp_one_thread+sfence.vma`, `PTE_OoO_fetch`, `PTE_update_ad_lrsc` and `sc_d_bit`.
- *Derived:* on one hart with no other memory masters, explicit main-memory accesses are observed by the hart in
  program order. RVWMO adds observers only through:
  - the page-table walker (§1.3);
  - instruction fetch (§2);
  - DMA devices and MMIO: FENCE predecessor/successor I/O bits, and `menvcfg.FIOM` (`machine.adoc` L2141–2157). For
    oracle models of DMA-written memory and single-fetch disciplines, see package `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`.
- Supporting text: SFENCE.VMA "does not necessarily place prior explicit accesses before subsequent explicit
  accesses in the global memory order" (`supervisor.adoc` L1292–1296); this matters only to other observers.
- Firmware runs on the same hart, so it is program-ordered. It accesses SBI shared memory physically, with PMA
  attributes, bypassing S-mode translations.

### 9. M-mode controls visible to S-mode (OpenSBI `61f1973b` defaults)

Basis: source + normative.

- **`mstatus`.** FS/VS only, so TVM=TSR=TW=0 and MPRV=0 (`lib/sbi/sbi_hart.c` L28–43). `scounteren`=0x02 (L48).
  `mcounteren`=−1 (L56).
- **`mideleg`.** SSIP|STIP|SEIP plus the PMU interrupt (`lib/sbi/sbi_trap.c` L434–435).
- **`medeleg`.** Misaligned fetch, breakpoint and user ecall. It *additionally* includes fetch, load and store page
  faults and SW_CHECK **only if** `sbi_platform_has_mfaults_delegation(plat)` (L437–443).
  `SBI_PLATFORM_DEFAULT_FEATURES` is `SBI_PLATFORM_HAS_MFAULTS_DELEGATION` (`include/sbi/sbi_platform.h` L72–74), and
  `platform/generic/platform.c` L359 uses the defaults.
- **`menvcfg`** (L131–169): ADUE per §3; STCE iff Sstc; PBMTE iff Svpbmt; CBZE/CBCFE/CBIE iff Zicboz/Zicbom.
- **`senvcfg`** is not initialized on boot (only swapped by domain contexts, `lib/sbi/sbi_domain_context.c` L147).
- **PMP and translation caching.** PMP decisions may be cached alongside translations. After changing PMP, M-mode
  "must synchronize … by executing an SFENCE.VMA instruction with rs1=x0 and rs2=x0" (`machine.adoc` L3622–3634).
  Implicit page-table accesses are PMP-checked at effective privilege S (L3614–3620).

### 10. Derived design consequences for a small kernel-reducible trusted RV64 S-mode model

Everything in this section is **derived** from §1–§9.

**10.1 Platform parameter record Π.** Fixed per boot and universally quantified in every claim:

- ASIDLEN ∈ [0,16];
- supported `satp` modes (Sv39 may be unsupported, in which case the write is silently ignored);
- `stvec` modes and alignment;
- implemented `sie`/`sip`/`scounteren` bits;
- A/D scheme ∈ {Svade, hardware update} (also FWFT-mutable);
- Sstc present or not;
- reservation-set size and shape (⊇ the addressed bytes, ⊆ one 4 KiB page);
- the set of extra extensions the hart implements and U-mode may execute;
- whether page faults are delegated.

Sail's JSON configuration fixes one point of Π.

**10.2 Nondeterminism that must remain in the model.** Kernel discipline cannot replace these, because the discipline
itself must be checked against them.

1. **Translation history.** Each step-2 read at level *i* returns either the current PTE value or any value that slot
   held since the most recent `sfence.vma` subsuming it. This includes V=0 values. Entries are tagged by
   `asid mod 2^ASIDLEN` or G, and persist across `satp` writes (§1.1–§1.4).
   - A kernel-reducible encoding: a per-slot write log since the last subsuming fence, and an oracle index per level
     per translation.
   - Discipline then becomes a proof that every oracle choice gives the same result. A ghost dirty-set that records
     unfenced PTE writes per level is one way to discharge it; see package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` §3 and §5.
2. **Environment steps between instructions.** These cover:
   - advancing `time`;
   - STIP edges: rise at or after the deadline, with a delayed fall (§6.2);
   - interrupt-taking latency: bounded but unknown, except immediately after `sret` or a write to `sip`, `sie` or
     `sstatus` (§6.1);
   - opaque M-mode excursions. These preserve all S-visible state except: STIP when Sstc is absent; the reservation
     (may be lost); `time`; and possibly additional translation-cache invalidation.
3. **`wfi`** = `skip` plus arbitrary environment steps (§6.3).
4. **SC outcome.**
   - SC may always fail.
   - SC may succeed only if: a reservation from the latest LR survived; no SC intervened; the target is in the
     Π-chosen set; and no device wrote the LR's bytes.
   - Survival across traps and xRET is nondeterministic (§5).
5. **Fetching bytes written since the hart's last `fence.i`.** Encoding this as an *error* (a dirty set cleared only
   by `fence.i`) is sound for safety claims. The dirty set must include M-mode writes (for example a DBCN read
   buffer) and DMA writes. Package `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` §5 mechanizes the same encoding as `HarvardCodeState`.
6. **SBI results** per §7.2–§7.3: only a0/a1 change; all other registers are preserved.
7. **Initial S-mode state.** Arbitrary legal values for every CSR not fixed by the boot protocol (§7.2 HSM; §9
   `senvcfg`). Pin firmware-specific values only under an explicit firmware-revision assumption.
8. **User-mode steps.** If users are adversaries, a user step is an arbitrary transformation of U-accessible state.
   That state includes *hidden* user-visible state the kernel does not save: FP/vector registers when FS/VS ≠ Off,
   `fcsr`, and CFI state when enabled. The step ends in a trap or interrupt.

**10.3 Kernel discipline.** Each item turns a spec freedom into a checked obligation. The model should make the
violating path an error rather than delete it.

| Spec freedom | Discipline |
| --- | --- |
| Hardware A/D updates, speculative A-sets, A/D faults, and Sail's §1.7 path | D-AD (§3) |
| Stale translations | Matching `sfence.vma` after every PTE change before any dependent access. `rs1=x0` for non-leaf changes and before reusing a page-table frame (§1.2). `rs2=x0` when any G bit is on the path. Recycle ASIDs per L1363–1369. Keep at most 2^ASIDLEN live tags (§1.4). |
| Spurious faults after lazy fences | Fence eagerly, or retry the fault |
| Stale reservation success | Dummy SC on every context switch (§5, P2) |
| Misaligned-access emulation in firmware | Naturally aligned accesses only |
| WARL read-back | Write only values validated by boot-time read-back |
| `wfi` resumption | `wfi; check sip; loop` with SIE=0 |
| DBCN partial writes and PA/VA | Loop on the returned count; pass physical addresses, or use write_byte |
| Hidden user state | FS=VS=Off, `senvcfg`=0, `scounteren`=0 |

**10.4 Correspondence scope.**

- A proof that the trusted model contains every behaviour of a pinned Sail configuration establishes fidelity for:
  instruction semantics, trap entry and exit, and CSR legalization *of that configuration*.
- It cannot establish fidelity for §10.2 items 1–5, because Sail fixes them deterministically or omits them
  (§1.6, §2.2, §5, §6.3). No authoritative formal reference exists for those items (§8).
- For those items, fidelity must be argued against the prose clauses cited here.
- The correspondence must also exclude Sail's out-of-spec A/D write-back (§1.7).

## Boundaries

**Not examined**

- Execution of Sail, Spike, QEMU or OpenSBI. In particular the §1.7 Sail behaviour is established only by source
  reading.
- Multi-hart behaviour: remote fences, SBI RFENCE/IPI, cross-hart LR/SC.
- The hypervisor extension, Svpbmt, Svnapot, pointer masking, CFI extensions, and FWFT semantics.
- Islaris's RISC-V configuration constraints. Package `riscv-privileged-isa-model-correspondence-prior-art` Finding 8 examined them: traces are pinned to
  `cur_privilege = Machine`, PMP off and `MPRV = 0` (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`
  `theories/riscv64/sys_regs.v:64-80`).
- Whether OpenSBI's Smepmp temporary PMP mapping (`sbi_hart_protection_temp_map_range`) executes the
  `sfence.vma x0,x0` required by `[#norm:pmp_sfence_required]`.
- Monotonicity and wrap of `time`, and firmware emulation of `rdtime`.
- Promising-ARM/RISC-V (PLDI 2019, doi:10.1145/3314221.3314624), which covers RVWMO without virtual memory, was not
  read; it is noted only as the relevant operational model.

**Unknown**

- Whether the specification authors intend the per-level reading of §1.2. The two clauses conflict, and no
  clarification was found.
- Whether Ziccid's "ratified" listing in the development snapshot's preface reflects formal ratification. It is
  absent from release `20250508`.
- Whether a formal SBI or OpenSBI semantics exists. The search found none, which is weaker than "none exists".
- Which A/D scheme a hart conforming only to Privileged 1.12 uses when it advertises neither Svade nor Svadu.

**Known not to apply**

- The single-hart sufficiency statements (`fence.i`, `sfence.vma`, P2's scenario) do not extend to multi-hart
  systems.
- Svinval semantics do not apply to a kernel that never issues Svinval instructions.

**Unsupported**

- SFENCE.VMA with an invalid virtual address in rs1 is defined as a no-op without a trap (L1261–1264). Software
  cannot use it to flush everything.
- A hart whose `satp`.MODE is read-only zero may raise illegal-instruction on SFENCE.VMA (L1408–1411).

**Stronger conclusions the evidence does not establish**

- "A model that matches Sail is spec-sound." Sail under-approximates caching and, on hardware-A/D configurations,
  deviates outside the spec (§1.7).
- "Passing QEMU or Spike tests shows correct TLB, `fence.i` or reservation handling." Each hides at least one class
  of bug (§1.6, §2.2, §5).
- "Svvptc removes the need to handle spurious faults." It bounds visibility latency only.
- "The derived Π and environment-step set is minimal." It is a sound set argued clause by clause. Minimality is not
  proved.
- "OpenSBI always delegates page faults." Delegation is conditional on a platform feature flag (§9).

## Evidence

All observations were made on 2026-11-20. Durable identities are in `REPORT.json`.

**Specifications (normative).**

`riscv/riscv-isa-manual@c05f1725f25526dd8463bac6ca75cfcfbee17d05`:

- `src/priv/supervisor.adoc`: L144, L317–531, L965–1174 (`satp`, `stimecmp`), L1180–1411 (SFENCE.VMA), L1560–1846
  (PTE bits, A/D, algorithm, cache, speculation).
- `src/priv/machine.adoc`: L599–625, L725–784, L2141–2211, L2655–2790, L3614–3634.
- `src/priv/csrs.adoc`: L632–700.
- `src/priv/svvptc.adoc` and `src/priv/svinval.adoc`.
- `src/unpriv/zalrsc.adoc`: L9–24, L86–153, L183–270.
- `src/unpriv/zifencei.adoc`: L1–121.
- `src/unpriv/ziccif.adoc` and `src/unpriv/ziccid.adoc`.
- `src/unpriv/rvwmo.adoc`: L18–33.
- `src/unpriv/cmo.adoc`: L180–250.
- `src/unpriv/preface.adoc`: L10–40.
- `src/profiles/rva23.adoc`: L175–190.

Releases and introduction commits:

- `20250508` (`584390d9…`): `src/supervisor.adoc` and `src/sstc.adoc` L35–55, diffed for the cited clauses.
- `20240411` (`6ee57d89…`): `src/supervisor.adoc`.
- `Priv-v1.12` (`98964261…`): `src/supervisor.tex` L1292, L1595–1630, L1678, L1760.
- Ziccid introduction: `f0b597df25de3f8304dbfc2bb9a02d4696b82b2a`.

`riscv-non-isa/riscv-sbi-doc` tag `v3.0` (`c33ad9f4…`): `src/binary-encoding.adoc`, `src/ext-time.adoc`,
`src/ext-debug-console.adoc`, `src/ext-sys-reset.adoc`, `src/ext-hsm.adoc` L90–101, L230–241. The repository head
`8a545effe9b50484ff897d9815d7d9015cdef203` does not change these files.

**Implementations and models (source).**

`riscv/sail-riscv@ec5200bd…`:

- `model/sys/vmem_tlb.sail`: L9–13, L135–163.
- `model/sys/vmem.sail`: L20–29, L95–119, L297–298, L365–494.
- `model/sys/vmem_pte.sail`: L302–340.
- `model/extensions/I/base_insts.sail`: L640–801.
- `model/extensions/Zifencei/zifencei_insts.sail` and `model/extensions/A/zalrsc_insts.sail`.
- `model/sys/sys_reservation.sail`.
- `model/sys/sys_control.sail`: L155–180, L565–580.
- `model/postlude/step.sail`: L20–135.
- `config/config.json.in`: L243–246, L331–336, L556–573.
- `c_emulator/riscv_model_impl.cpp`: L38–70, L246–270.

`riscv-software-src/opensbi@61f1973b…`:

- `lib/sbi/sbi_hart.c`: L20–180, L795–810.
- `lib/sbi/sbi_trap.c`: L310–470.
- `include/sbi/sbi_platform.h`: L55–80, L253–254.
- `platform/generic/platform.c`: L359.
- `lib/sbi/sbi_timer.c`: L160–300.
- `lib/sbi/sbi_ecall_time.c`, `lib/sbi/sbi_ecall_dbcn.c`, `lib/sbi/sbi_ecall_srst.c`.
- `lib/sbi/riscv_locks.c`: L20–75.
- `lib/sbi/sbi_domain_context.c`: L147.

`riscv-software-src/riscv-isa-sim@e53c8ccf…`:

- `riscv/mmu.h`: L265–310.
- `riscv/mmu.cc`: L40–68, L138–146, L225–236, L345–359, L450–459.
- `riscv/csrs.cc`: L1269–1274.
- `riscv/insns/fence_i.h`, `riscv/insns/sfence_vma.h`, `riscv/insns/sc_w.h`.
- `riscv/sim.cc`: L370–382.
- `riscv/processor.cc`: L412–430.

`qemu/qemu@08ed97c3…`:

- `target/riscv/tcg/csr.c`: L2000–2024, L4656–4665.
- `target/riscv/tcg/cpu_helper.c`: L935–970.
- `target/riscv/tcg/op_helper.c`: L371, L458.
- `target/riscv/tcg/insn_trans/trans_rvi.c.inc`: L976–990.

Other models:

- `daniellustig/riscv_axiomatic@0cc125df…`: `README.md`, `litmus/`, `riscv_axiomatic/rvwmo.py`.
- `uw-unsat/serval@72adc495…`: `serval/riscv/interp/i-type.rkt` L71, `serval/riscv/interp/r-type.rkt` L75–117.
- `CharlyCst/miralis@f5ab1955…`: `model_checking/src/lib.rs` L1–40.
- `IBM/ACE-RISCV@42cf582e…`: `verification/readme.md`.

**Execution (probes).** `support/`:

| File | SHA-256 |
| --- | --- |
| `PerLevelStaleTranslation.lean` | `8ef99a1d926b0d5f7ca013d02a98f9f7f27500b74f9a185c14a49ecd8efc8ec7` |
| `LrScContextSwitch.lean` | `6f951c42a3ca155ad7140c47e1940de8b562660e6c0034ab093e86b64f01cbb9` |

- Runner: `run_probes.sh`. Recorded output: `probe_output.txt`.
- Toolchain: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52,
  Release)`.
- Result: exit 0. All five theorems report "does not depend on any axioms".
- The probes formalize the spec clauses quoted in §1.2 and §5. They do not model any implementation.

## Revalidation

1. **Probes.** Run `LEAN=<lean 4.x> support/run_probes.sh` from the package directory, then compare with
   `support/probe_output.txt`. This rechecks only the finite counterexamples.
2. **Specification drift.** In a newer `riscv-isa-manual`, grep `src/priv/supervisor.adoc` for:
   - "caching of PTEs whose V";
   - "may be held in a read-only, incoherent";
   - "valid at any time since the most recent";
   - "cannot be used in step 9";
   - "ASIDLEN".

   Also grep `src/priv/machine.adoc` for "allowed to clear any outstanding LR" and "simply implement the WFI
   instruction as a NOP", and `src/unpriv/rvwmo.adoc` for "not (yet) formalized". A change to any of these clauses
   invalidates the corresponding finding. Check `src/unpriv/preface.adoc` and the next tagged release for Ziccid.
3. **Sail §1.7.**
   - Inspect `translate_TLB_hit` and `update_and_write_pte` in `model/sys/vmem.sail` for a compare against memory
     before `write_pte`.
   - Confirm by execution: configure Svadu with `menvcfg.ADUE=1` (or neither Svadu nor Svade), map a page with A=0,
     access it (TLB fill), rewrite the PTE in memory without `sfence.vma`, access it again, and dump the PTE. The
     spec forbids the old contents reappearing.
4. **Reference choices.**
   - Sail: `config/config.json.in` `reservation` block and `xtvec_mode`.
   - Spike: `base_atp_csr_t::unlogged_write` and `mmu_t::yield_load_reservation` call sites.
   - QEMU: `legalize_xatp`, `riscv_cpu_set_mode` (`load_res`) and `trans_fence_i`.
5. **OpenSBI.** Diff `delegate_traps` (`lib/sbi/sbi_trap.c`), `mstatus_init` (`lib/sbi/sbi_hart.c`),
   `sbi_timer_smode_event_start` (`lib/sbi/sbi_timer.c`) and `sbi_ecall_dbcn_handler`.
6. **SBI specification.** Check whether a later `riscv-sbi-doc` reconciles the DBCN error tables with the
   shared-memory rule in `src/binary-encoding.adoc`.
