# Non-Coherent DMA Cache Maintenance, Zicbom Granules, and Adjacent-Field Tearing Hazards

## Summary

Non-coherent Direct Memory Access (DMA) peripherals read and write physical memory outside the processor's hardware cache-coherence domain, requiring operating system kernels and device drivers to bridge CPU caches and the Point of Coherence (PoC) explicitly via cache-block management instructions—specifically RISC-V `Zicbom` (`cbo.clean`, `cbo.flush`, `cbo.inval`) and Arm A-profile data-cache operations (`DC CVAC`, `DC CIVAC`, `DC IVAC`). Whereas software memory models such as Rust's MiniRust and Tree Borrows define aliasing, `Freeze`, and `UnsafeCell` interior mutability at **1-byte granularity**, architectural cache-block operations act atomically on **naturally aligned power-of-two (NAPOT) cache granules** $B = 2^k$ bytes (typically $64\text{ B}$ on RISC-V systems implementing `Zicbom` and $64\text{ B}$–$128\text{ B}$ up to the Cache Writeback Granule `CTR_EL0.CWG` on AArch64).

When a streaming DMA buffer $S_{\text{dma}}$ is not both base-aligned and size-padded to $B$, it shares at least one physical cache block $L = [b \cdot B, (b+1) \cdot B)$ with colocated CPU-owned fields $S_{\text{cpu}} \subseteq L \setminus S_{\text{dma}}$. Across all $16$ pairs $(op_{\text{pre}}, op_{\text{post}}) \in \{\text{NOP}, \text{CLEAN}, \text{FLUSH}, \text{INVAL}\}^2$ of pre-transfer and post-transfer whole-block operations, **zero** combinations preserve both an inbound non-coherent DMA write to $S_{\text{dma}}$ and a concurrent CPU store to $S_{\text{cpu}}$ under write-back, write-allocate caching:

1. Issuing `cbo.inval` or `DC IVAC` after DMA completion (as in Linux RISC-V's `ALT_CMO_OP(INVAL, ...)` macro, which rounds misaligned start addresses down to `_start & ~(_cachesize - 1)` and invalidates boundary blocks unconditionally) discards dirty cache lines without writeback, silently rolling concurrent CPU modifications in $S_{\text{cpu}}$ back to stale DRAM values.
2. Promoting partial boundary blocks to clean-and-invalidate (`DC CIVAC` in Linux AArch64's `__dcache_inval_poc_nosync`, or `cbo.flush`) protects *quiescent* pre-dirty sibling bytes only when zero CPU stores touch $S_{\text{cpu}}$ during the active DMA window; any CPU store to $S_{\text{cpu}}$ during the transfer write-allocates stale DRAM bytes for $S_{\text{dma}}$ into the dirty cache line, causing either autonomous cache eviction or post-DMA clean/flush writeback to overwrite the peripheral's transferred payload in $S_{\text{dma}}$.
3. Even without CPU stores to $S_{\text{cpu}}$, speculative execution, hardware prefetchers, or CPU reads of $S_{\text{cpu}}$ can allocate an `Unmodified` cached copy of $L$ mid-transfer; pre-DMA invalidation alone leaves stale cached bytes visible to post-DMA CPU loads unless paired with post-DMA invalidation ordered after device completion.

Crucially, authoritative sequential ISA specifications—including the official Sail RISC-V model (`riscv/sail-riscv`)—check privilege (`menvcfg`/`senvcfg`/`henvcfg` `CBIE` and `CBCFE`), page-table permissions (`pte_R || pte_W` without setting `PTE.D`), and Physical Memory Attributes/Protection (PMA/PMP) for `Zicbom`, yet model `process_clean_inval` as an architectural `RETIRE_SUCCESS` no-op on flat memory once permission checks succeed. Sound formal verification of non-coherent DMA drivers therefore cannot rely solely on sequential Sail semantics or byte-granular separation logic ($\ell \mapsto v$); it requires lifting spatial ownership to cache-granule predicates (`#[repr(C, align(64))]` or `ARCH_DMA_MINALIGN` padding) with explicit clean-before-handoff and invalidate-before-read transitions.

## Applicability

The findings in this report govern the joint interaction of the eight subjects recorded in `REPORT.json`:

- **RISC-V `Zicbom` Normative and Formal ISA Models**: Applies to RV32 and RV64 implementations of the ratified `Zicbom` v1.0.1 extension in the RISC-V ISA Manual (`riscv/riscv-isa-manual` at `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/unpriv/cmo.adoc`, and archival source `riscvarchive/riscv-CMOs` at `615baa163b15c02f32bdbdeeab401ca486a3a9bc`) together with the executable Sail specification (`riscv/sail-riscv` at `76f1ce3c184797178864b9869963e8b44465889e`, `model/extensions/Zicbom/zicbom_insts.sail` and `model/sys/vmem_pte.sail`). `Zicbom` v1.0.1 requires uniform system-wide cache-block sizes (`src/unpriv/cmo.adoc`, norm `cache_block_size_uniform`), discovered via platform firmware/Devicetree (`riscv,cbom-block-size`) rather than an unprivileged CSR.
- **Arm A-Profile Cache Maintenance and Relaxed Memory Models**: Applies to AArch64 implementations under `ARM DDI 0487` (`DC CVAC`, `DC CIVAC`, `DC IVAC`, `CTR_EL0.DminLine`, `CTR_EL0.CWG`, `SCTLR_EL1.UCI`, and `DSB SY` completion barriers) and their axiomatic `cat` formalization in `herd/herdtools7` (`1ae595498c7af7d9d2f00e29aea328b36663104c`, `herd/libdir/aarch64.cat`).
- **Linux Kernel Non-Coherent DMA and Rust Abstractions**: Applies to `torvalds/linux` at `d0f871bfb831705d9f55479f5b2b40f636ea7b16`—specifically `arch/riscv/mm/dma-noncoherent.c`, `arch/riscv/include/asm/cache.h`, `arch/riscv/include/asm/errata_list.h`, `arch/arm64/include/asm/cache.h`, `arch/arm64/mm/dma-mapping.c`, `arch/arm64/mm/cache.S`, `kernel/dma/direct.c`, `include/linux/dma-mapping.h`, and `rust/kernel/dma.rs`—when `CONFIG_RISCV_DMA_NONCOHERENT` or non-coherent AArch64 devices (`!dev_is_dma_coherent(dev)`) operate without hardware I/O snooping.
- **Rust Language Memory Model and Aliasing Semantics**: Applies to `core::cell::UnsafeCell` and the `#[lang = "freeze"]` auto trait `core::marker::Freeze` in `rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `library/core/src/marker.rs`) interpreted under the operational byte-indexed `AbstractByte` and Tree Borrows model in `RalfJung/minirust` (`063d784186d3252bee242217f218223205c0b568`, `spec/mem/interface.md`, `spec/mem/tree_borrows/memory.md`, `spec/mem/tree_borrows/reborrow_settings.md`).

For general Rust weak-memory atomics and byte-level Tree Borrows protector rules independent of non-coherent DMA cache blocks, consult corpus packages `rust-atomics-weak-memory-and-aliasing-operational-models` and `minirust-tree-borrows-protectors-and-program-logic-correspondence`. The cross-layer tearing hazards and separation-logic protocols derived below extend beyond Linux to standalone Rust microkernels, hypervisors, and embedded `no_std` drivers whenever cacheable pages (`MainMemory` / `Normal Write-Back`) are accessed directly by non-coherent bus masters without `swiotlb` bounce-buffering or non-cacheable page-attribute remapping.

## Findings

### 1. Normative Granularity, Privilege Modulation, and Fault Asymmetries (`Zicbom` vs. AArch64)

`Basis: normative + source`

Both RISC-V `Zicbom` and Armv8-A/Armv9-A define data-cache maintenance instructions by virtual/effective address up to a system-wide Point of Coherence (PoC), yet they differ sharply in granule discovery, unprivileged delegation, and page-table permission rules:

| Architectural Dimension | RISC-V `Zicbom` (`cbo.clean`, `cbo.flush`, `cbo.inval`) | AArch64 (`DC CVAC`, `DC CIVAC`, `DC IVAC`) |
| --- | --- | --- |
| Encoding & Addressing | `MISC-MEM` (`0x0F`), `funct3 = 0x2`, `rd = x0`, base `rs1`, zero offset; `funct12` = `0x000` (`inval`), `0x001` (`clean`), `0x002` (`flush`). Never raises misaligned-address exceptions (`src/unpriv/cmo.adoc:409-410, 815-892`). | `SYS` instruction taking 64-bit register `Xt` holding any virtual address within the target line; no alignment requirement on `Xt` (`ARM DDI 0487`). |
| Granule Discovery | Uniform NAPOT block size $B = 2^k$ across the coherent domain (`src/unpriv/cmo.adoc:86-94`); no unprivileged CSR—software discovers $B$ via firmware/DT (`riscv,cbom-block-size`). | Split into **minimum stride** `CTR_EL0.DminLine` ($4 \cdot 2^{\text{DminLine}}$ B, bits `[19:16]`) and **maximum writeback granule** `CTR_EL0.CWG` ($4 \cdot 2^{\text{CWG}}$ B, bits `[27:24]`, fallback $128\text{ B}$ in `arch/arm64/include/asm/cache.h:35, 79-84`). |
| Unprivileged (`U` / `EL0`) Access Control | Controlled via `menvcfg`, `senvcfg`, and `henvcfg`: 1-bit `CBCFE` (bit `6`) gates `clean`/`flush`; 2-bit `CBIE` (bits `[5:4]`) maps `00` $\to$ trap, `01` $\to$ **executes `cbo.inval` as `cbo.flush`**, `10` $\to$ reserved, `11` $\to$ executes destructive `cbo.inval` (`src/unpriv/cmo.adoc:524-604`). | `SCTLR_EL1.UCI = 1` enables `EL0` execution of `DC CVAU`, `DC CIVAC`, and `IC IVAU`, whereas **`DC IVAC` is unconditionally restricted to `EL1` and higher** (`ARM DDI 0487`). |
| Translation Permission & `A`/`D` Bits | Permitted whenever **either load or store** access is allowed (`pte_R \|\| pte_W`, honoring `MXR` on `pte_X`); checks/sets `PTE.A` (`Accessed`) without checking or setting `PTE.D` (`Dirty`). When denied, **always raises Store/AMO Page/Guest-Page/Access Fault** (`scause = 15` / `7`), writing unaligned `rs1` to `*tval` (`src/unpriv/cmo.adoc:352-405, 865-900`; `VmemPte.lean:373, 389`). | `DC CVAC` and `DC CIVAC` require **Read** permission on the translated VA, whereas privileged `DC IVAC` requires **Write** permission (`ARM DDI 0487`). |
| Cacheability Override | Operates on coherent caches **irrespective of PMA cacheability or `Svpbmt` PBMT non-cacheable attributes** (`src/unpriv/cmo.adoc:710-714`), cleaning stale linear-map aliases after non-cacheable remapping. | `DC *VAC` operates to PoC even if the current translation marks memory Non-Cacheable, maintaining stale cached aliases (`ARM DDI 0487`). |
| Ordering & Completion | Behaves as a store in RVWMO Preserved Program Order (PPO) plus an overlapping-address rule ordering a CBO before program-order-subsequent overlapping loads (`src/unpriv/cmo.adoc:229-248`). Device handoff requires `fence rw, io` / `fence io, rw` (or `fence w, o` / `fence i, r`). | Ordered against explicit memory accesses only via `DSB` (`dsb sy` / `dsb ish`); `DMB` alone does **not** order `DC *VAC` completion to PoC (`arch/arm64/include/asm/cache.h:90-93`; `herd/libdir/aarch64.cat:54, 144`). |

The interaction between `Zicbom`'s permissive PTE check (`pte_R || pte_W`) and `CBIE` establishes a critical supervisor invariant (`src/unpriv/cmo.adoc:564-576`; `zicbom_insts.sail:49-70, 139-145`): because `cbo.inval` passes translation on a **read-only (`R=1, W=0, U=1`)** user mapping, setting `senvcfg.CBIE = 0b11` in an OS kernel would let unprivileged user code execute `cbo.inval` on shared read-only page-cache or IPC mappings, discarding uncommitted dirty writes made by privileged writers. General-purpose OS kernels must configure `senvcfg.CBIE` to `0b00` (trap) or `0b01` (`CBIE_EXEC_FLUSH`, transparently upgrading `cbo.inval` to `cbo.flush`).

### 2. The Sequential Sail Blind Spot: Why Authoritative ISA Models Erase Non-Coherent DMA Bugs

`Basis: source + derived`

In the official Sail RISC-V specification (`riscv/sail-riscv` at `76f1ce3c184797178864b9869963e8b44465889e`, `model/extensions/Zicbom/zicbom_insts.sail:72-123`), all three `Zicbom` instructions delegate after CSR privilege checks (`CBCFE` or `cbop_priv_check`) to `process_clean_inval`:

```sail
private function process_clean_inval(rs1 : regidx, cbop : cbop_zicbom) -> ExecutionResult = {
  let rs1_val = X(rs1);
  let cache_block_size = 2 ^ plat_cache_block_size_exp;
  let access : MemoryAccessType(mem_payload) = CacheAccess(CB_manage(cbop));
  ...
  let negative_offset = (rs1_val & ~(zero_extend(ones(plat_cache_block_size_exp)))) - rs1_val;
  match get_transformed_data_addr(rs1, negative_offset, access, access_info, cache_block_size) {
    ...
    Ext_DataAddr_OK(vaddr) => {
      let vaddr_for_error = vaddr - negative_offset;
      match translateAddr(vaddr, access, eff_priv) {
        Ok(paddr, pbmt, _) => {
          match phys_access_check(access, pbmt, eff_priv, paddr, cache_block_size, false) {
            Err(e) => { ... memory_exception(e, exc_vaddr, access_info) },
            // If there is no error, the model has no caches so there's no
            // more action required.
            Ok(_)  => RETIRE_SUCCESS
          }
        },
        Err(e, _) => trap({ e with excinfo = bits_of(vaddr_for_error) }),
      }
    }
  }
}
```

Two formal consequences follow from `process_clean_inval` and the Lean 4 Sail runtime (`rems-project/lean-sail`, `Sail/ConcurrencyInterfaceV1.lean:271` `sail_cache_op _ := pure ()` and `Sail/ArchSemSequential.lean:75` `| .cacheOp _op => pure ()`):

1. **Observational Collapse of `CBO_CLEAN`, `CBO_FLUSH`, and `CBO_INVAL`**: Once privilege checks pass, `CacheAccess(CB_manage(cbop))` is handled identically across all three constructors by `check_PTE_permission` (`VmemPte.lean:373`), `update_PTE_Bits` (`VmemPte.lean:389`), `translationException` (`VmemPtw.lean:253-254`), and `phys_access_check`, retiring with `RETIRE_SUCCESS` without modifying `mem` or recording cache state.
2. **Vacuity of Flat-Memory Driver Verification**: Proving a C or Rust DMA driver against sequential Sail (`SequentialState` with flat `mem : ExtHashMap Nat (BitVec 8)`) catches privilege traps, PMP/PMA block violations, and `*tval` fault-address bugs (`vaddr_for_error` vs. aligned `vaddr`), **but cannot detect missing `cbo.clean`, missing `cbo.inval`, wrong CMO direction (`cbo.clean` instead of `cbo.inval` post-RX), or adjacent-field cache-line clobbering**. Even in `herdtools7` (`herd/libdir/aarch64.cat:54-55, 134-146`), explicit cache-maintenance relations in the baseline model cover instruction-fetch coherence (`DC-after`, `IC-after`; Simner et al., ESOP 2020) and persistent memory (`DC.CVAP`; Raad et al., OOPSLA 2019) rather than non-coherent DMA write transfers. Sound DMA verification requires an explicit split between cached coherent views and PoC/DRAM backing memory.

### 3. Linux Kernel RISC-V vs. AArch64 Asymmetry and the Cache-Line Sharing Impossibility Result

`Basis: normative + source + execution + derived`

Linux (`torvalds/linux` at `d0f871bfb831705d9f55479f5b2b40f636ea7b16`) exhibits an instructive asymmetry between AArch64 and RISC-V streaming DMA invalidation over `[start, start + size)`:

- **AArch64 Boundary Promotion (`arch/arm64/mm/cache.S:135-151` and `arch/arm64/mm/dma-mapping.c:15-32`)**: `arch_sync_dma_for_device` calls `dcache_clean_poc_nosync` (`DC CVAC`), and `arch_sync_dma_for_cpu` calls `__dcache_inval_poc_nosync`. If `start` or `end` is misaligned (`tst x1, x3` or `tst x0, x3`, with `x3 = DminLine - 1`), the partial head and tail cache lines are promoted to **`dc civac`** (clean-and-invalidate), while only fully covered interior lines execute destructive **`dc ivac`**.
- **RISC-V Unconditional Block Invalidation (`arch/riscv/include/asm/errata_list.h:138-152` and `arch/riscv/mm/dma-noncoherent.c:59-115`)**: `ALT_CMO_OP(_op, _start, _size, _cachesize)` rounds base down to `(_start) & ~((_cachesize) - 1UL)` and executes `CBO_##_op(a0)` uniformly across every touched block **without promoting partial boundary blocks from `cbo.inval` to `cbo.flush`**. To preserve pre-existing dirty sibling bytes in boundary blocks, `arch/riscv/mm/dma-noncoherent.c:59-91` sets `arch_sync_dma_clean_before_fromdevice() = true`, running `ALT_CMO_OP(CLEAN, ...)` before `DMA_FROM_DEVICE` transfers and `ALT_CMO_OP(INVAL, ...)` upon completion.

**Derived Impossibility under Concurrent Sibling Mutation**: Partition one cache block $L$ of size $B$ into non-empty slices $S_{\text{dma}} \subset L$ and $S_{\text{cpu}} = L \setminus S_{\text{dma}}$. Under write-back, write-allocate caching permitted by `Zicbom` (`src/unpriv/cmo.adoc:80-84, 191-215`) and `ARM DDI 0487`, each block $L$ is in state `Invalid`, `Unmodified(v_cache)` (autonomous speculative or demand fill; never written back on eviction), or `Modified(v_cache)` (dirty; eligible for autonomous writeback eviction at any instant and written back on `CLEAN`/`FLUSH`). Suppose `dma_map_single` runs $op_{\text{pre}} \in \{\text{NOP}, \text{CLEAN}, \text{FLUSH}, \text{INVAL}\}$, and during the transfer window the CPU stores $v_{\text{cpu}}$ to $S_{\text{cpu}}$ before the peripheral writes $v_{\text{dma}}$ to DRAM slice $S_{\text{dma}}$:
- On a cache miss (after `FLUSH` or `INVAL`) or hit, the CPU store write-allocates stale DRAM $v_{\text{old}}$ on $S_{\text{dma}}$, producing `Modified(v_old, v_cpu)` in cache before DRAM receives $v_{\text{dma}}$.
- If $op_{\text{post}} \in \{\text{CLEAN}, \text{FLUSH}, \text{NOP}\}$ (including AArch64's `dc civac` edge promotion), either autonomous dirty eviction or $op_{\text{post}}$ writes stale `v_old` back over DRAM's `v_dma` (or `NOP` reads stale `v_old` from cache), **corrupting $S_{\text{dma}}$**.
- If $op_{\text{post}} = \text{INVAL}$ (Linux RISC-V's `ALT_CMO_OP(INVAL, ...)`), then whenever no eviction precedes unmap, `INVAL` discards `Modified(v_old, v_cpu)` without writeback, **losing the concurrent CPU store $v_{\text{cpu}}$ on $S_{\text{cpu}}$** (while if dirty eviction occurs after the DMA write, `v_old` already overwrote `v_dma` in DRAM).

Exhaustive model checking confirms **`0 / 16`** `(op_pre, op_post)` pairs preserve both $S_{\text{dma}}$ and concurrent $S_{\text{cpu}}$ writes. When $S_{\text{cpu}}$ is *quiescent* during DMA (dirty only before `map`), **`4 / 16`** pairs pass: `{(CLEAN, INVAL), (CLEAN, FLUSH), (FLUSH, INVAL), (FLUSH, FLUSH)}`. Because Linux reduced `ARCH_KMALLOC_MINALIGN` to `8` while keeping `ARCH_DMA_MINALIGN` at `64` on RISC-V (`arch/riscv/include/asm/cache.h:15-16`) and `128` on AArch64 (`arch/arm64/include/asm/cache.h:35-36`), `dma_direct_map_phys` (`kernel/dma/direct.c:716-721`) bounces small `kmalloc` allocations through cache-line-isolated `swiotlb` slots via `dma_kmalloc_needs_bounce`, and `include/linux/dma-mapping.h:739-750` provides `__dma_from_device_group_begin`/`_end` to pad embedded struct DMA regions to `ARCH_DMA_MINALIGN`.

### 4. Byte-Granular Rust `Freeze` / `UnsafeCell` Aliasing vs. Hardware Cache-Block Tearing

`Basis: source + derived`

In `rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `library/core/src/marker.rs:905-919`), `Freeze` (`#[lang = "freeze"]`) is negated structurally by `UnsafeCell<T>`. In MiniRust's Tree Borrows model (`RalfJung/minirust` at `063d784186d3252bee242217f218223205c0b568`, `spec/mem/interface.md:15-34` and `spec/mem/tree_borrows/reborrow_settings.md:18-48, 95-134`), memory is indexed per `AbstractByte<Provenance>` and `cells_to_freeze_mask(cells, size)` computes per-byte `Frozen` vs. `Cell` permissions. Consider an unaligned ring descriptor on RV64GC (`B = 64`):

```rust
#[repr(C)] // Alignment is 8 bytes, NOT 64 or 128 bytes
pub struct UnalignedRxSlot {
    pub payload: core::cell::UnsafeCell<[u8; 48]>, // [0..48): !Freeze (Cell)
    pub seq_no: u64,                               // [48..56): Freeze
    pub state_flags: core::sync::atomic::AtomicU64,// [56..64): !Freeze (Cell)
}
```

Although byte ranges `[0..48)`, `[48..56)`, and `[56..64)` are disjoint in MiniRust/Miri, colocating them in one 64-byte hardware cache block `[0..64)` breaks three soundness invariants:

1. **Compiler-Level UB on `Freeze` References (`&slot.seq_no`)**: If `slot.seq_no = 10` sits dirty in L1D (DRAM holds `9`) when `cbo.inval` targets `payload.get()`, all 64 bytes `[0..64)` are invalidated, rolling `slot.seq_no` back to `9` mid-lifetime while live `&u64` (`PermissionProt::Frozen`, lowered to LLVM `readonly`/`noalias`; see corpus package `rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute`) forbids underlying byte mutation.
2. **Silent Loss of Committed `AtomicU64` RMWs (`Zaamo` / `Zalrsc` + `Zicbom`)**: Atomic RMWs (`amoor.d`, `lr.d`/`sc.d`) update `state_flags` in coherent cache (`Modified`) without forcing DRAM writeback; `cbo.inval` on `payload` wipes out committed atomic increments at `[56..64)` and cancels cross-hart `LR` reservations covering that block (`src/unpriv/cmo.adoc:482-504`).
3. **Why Upstream Linux `rust/kernel/dma.rs` Restricts Direct Views to `Coherent<T>`**: In `torvalds/linux` (`rust/kernel/dma.rs:369-696, 1184-1221`), `CoherentBox<'a, T>` and `Coherent<'a, T>` wrap page-aligned `dma_alloc_attrs` buffers cleared of dirty linear-map lines via `arch_dma_prep_coherent` (`ALT_CMO_OP(FLUSH, ...)` on RISC-V; `dcache_clean_poc` on AArch64) and mapped non-cacheable or coherent. Even there, `as_ref`/`as_mut` (`lines 639-657`) remain `unsafe` during active device access; safe partial reads/writes copy through `zerocopy::FromBytes` / `zerocopy::IntoBytes` (`copy_read` / `copy_write`, `lines 1213-1220`).

### 5. Separation-Logic Cache-Line Ownership Protocol for Verified Non-Coherent DMA

`Basis: derived`

To verify non-coherent DMA in concurrent separation logics (Iris, RefinedC, Islaris), byte points-to tokens $a \mapsto_{\text{cpu}} v$ must be projections of **cache-granule ownership assertions** at $B = \max(B_{\text{cbo}}, B_{\text{cwg}}) = 2^k$. For physical block $b = \lfloor \text{pa}/B \rfloor$, model hardware block state $(m_b, \gamma_b)$ with PoC vector $m_b \in \text{Byte}^B$ and coherent cache state $\gamma_b \in \{\mathsf{Inv}, \mathsf{Unmod}(c_b), \mathsf{Mod}(c_b)\}$, closed under autonomous steps $\leadsto_{\text{hw}}$: speculative fill $(m_b, \mathsf{Inv}) \leadsto_{\text{hw}} (m_b, \mathsf{Unmod}(m_b))$, clean eviction $(m_b, \mathsf{Unmod}(c_b)) \leadsto_{\text{hw}} (m_b, \mathsf{Inv})$, and dirty writeback $(m_b, \mathsf{Mod}(c_b)) \leadsto_{\text{hw}} (c_b, \mathsf{Unmod}(c_b)) \mid (c_b, \mathsf{Inv})$.

Define four $\leadsto_{\text{hw}}$-stable spatial predicates over granule $b$:
- **$\mathsf{CpuOwn}_B(b, v)$**: $(\gamma_b = \mathsf{Mod}(v)) \lor (m_b = v \land \gamma_b \in \{\mathsf{Inv}, \mathsf{Unmod}(v)\})$, splitting into bytes *only* while CPU-owned:
  $$\mathsf{CpuOwn}_B(b, v) \dashv\vdash \operatorname*{\Large\ast}_{i=0}^{B-1} (bB + i) \mapsto_{\text{cpu}} v[i]$$
  Reassembling $\mathsf{CpuOwn}_B(b, v)$ to initiate DMA forces the caller to surrender all $B$ byte tokens in block $b$, structurally ruling out live `&T` or `&mut T` borrows to sibling fields in the same line.
- **$\mathsf{PoCClean}_B(b, v)$**: $m_b = v \land \gamma_b \in \{\mathsf{Inv}, \mathsf{Unmod}(v)\}$ (zero dirty lines).
- **$\mathsf{DevTx}_B(b, v, q)$** and **$\mathsf{DevRx}_B(b)$**: Device read ($m_b = v$) and exclusive write tokens ($\gamma_b \in \{\mathsf{Inv}, \mathsf{Unmod}(\_)\}$, strictly forbidding $\gamma_b = \mathsf{Mod}(\_)$).
- **$\mathsf{DmaDoneRx}_B(b, v')$**: $m_b = v' \land \gamma_b \in \{\mathsf{Inv}, \mathsf{Unmod}(\_)\}$ (DRAM holds $v'$, cache may hold a speculatively prefetched stale `Unmodified` copy).

The verified handoff Hoare triples are:

$$\begin{aligned}
\{\mathsf{CpuOwn}_B(b, v)\} \;\;&\texttt{cbo.clean / cbo.flush / DC CVAC}(bB + \delta); \;\texttt{fence rw,io / dsb sy}\;\; \{\mathsf{PoCClean}_B(b, v)\} \\
\{\mathsf{CpuOwn}_B(b, v_0)\} \;\;&\texttt{cbo.clean / cbo.flush / cbo.inval / DC CIVAC}(bB + \delta); \;\texttt{fence rw,io / dsb sy}\;\; \{\mathsf{PoCClean}_B(b, \_)\} \\
\{\mathsf{PoCClean}_B(b, \_)\} \;\;&\texttt{mmio\_doorbell\_rx}(bB)\;\; \{\mathsf{DevRx}_B(b)\} \\
\{\mathsf{DevRx}_B(b)\} \;\;&\texttt{irq\_or\_poll\_complete}(); \;\texttt{fence io,r / dsb sy}\;\; \{\exists v'.\; \mathsf{DmaDoneRx}_B(b, v')\} \\
\{\mathsf{DmaDoneRx}_B(b, v')\} \;\;&\texttt{cbo.inval / cbo.flush / DC IVAC}(bB + \delta); \;\texttt{fence r,rw / dsb sy}\;\; \{\mathsf{CpuOwn}_B(b, v')\}
\end{aligned}$$

Pre-RX maintenance is mandatory even for overwritten RX buffers because $\mathsf{CpuOwn}_B(b, v_0)$ allows $\gamma_b = \mathsf{Mod}(v_0)$, which could otherwise write back mid-DMA; post-RX `inval`/`flush` cannot be weakened to `clean` because `clean` is a no-op on speculatively filled $\mathsf{Unmod}(v_{\text{stale}})$. In Rust, wrapping a DMA buffer in `#[repr(C, align(64))]` (or `align(128)` for AArch64 `ARCH_DMA_MINALIGN`) enforces both $\operatorname{align\_of}() \ge B$ and $\operatorname{size\_of}() \bmod B = 0$.

## Boundaries

- **Hardware-Coherent DMA Topologies (`known not to apply`)**: When peripherals belong to the hardware coherence domain—such as snooping PCIe endpoints on x86-64, AArch64 `dma-coherent` devices (`CLIDR_EL1.LoC == 0` in `arch/arm64/mm/dma-mapping.c:45-48`), or RISC-V coherent TileLink/CHI agents—explicit `Zicbom` / `DC *VAC` cache maintenance is **known not to apply**.
- **Per-Byte Dirty Writeback Masks in Specific Microarchitectures (`unknown`)**: Whether all caches up to PoC on a given SoC maintain per-byte dirty strobes without full-line read-modify-write merging is architecturally **unknown** to portable software; both `Zicbom` (`src/unpriv/cmo.adoc:123-125`) and `ARM DDI 0487` (`CTR_EL0.CWG`) permit full-granule writebacks.
- **Non-Uniform Multi-Cluster `Zicbom` Block Sizes (`unsupported`)**: Heterogeneous cache-block sizes across coherent agents are explicitly **unsupported** by `Zicbom` v1.0.1 (`src/unpriv/cmo.adoc:92-99`, norm `cache_block_size_uniform`), unlike AArch64's split `DminLine` / `CWG` discovery.
- **Vendor Pre-`Zicbom` Errata and Cache Timing Side Channels (`not examined`)**: Vendor-custom RISC-V CMO encodings (`ERRATA_THEAD_CMO` in `arch/riscv/mm/dma-noncoherent.c:22-27`), IOMMU (`riscv-iommu` / ARM SMMUv3) translation-cache invalidation, and unprivileged `Flush+Reload` microarchitectural timing channels were **not examined**.
- **Attractive Stronger Conclusion Not Established**: Aligning only the start of a struct or field without rounding its padded size to a multiple of $B$ does **not** prevent tearing: in `#[repr(C, align(64))] struct Bad { buf: [u8; 48], tail: u64 }`, `tail` still occupies bytes `[48..56)` of the first 64-byte line. The DMA buffer itself must be a distinct `#[repr(C, align(64))]` type so its `size_of` rounds up to `64`, pushing `tail` to offset `64`.

## Evidence

All source and execution evidence was acquired and verified on `2026-11-20`:

1. **RISC-V Normative `Zicbom` Specification**:
   - `riscv/riscv-isa-manual` commit `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/unpriv/cmo.adoc`: NAPOT uniform block rules (`lines 86-109`), clean eviction prohibition (`lines 187-215`), RVWMO PPO overlapping-address load rules and Load Value Axiom (`lines 225-292`), `pte_R || pte_W` check omitting `PTE.D`, Store/AMO fault reporting with `*tval = rs1`, and no misaligned exceptions (`lines 319-410`), `CBIE`/`CBCFE` privilege modulation, PBMT override note, and `cbo.{clean,flush,inval}` semantics (`lines 521-604, 640-915`).
   - `riscvarchive/riscv-CMOs` commit `615baa163b15c02f32bdbdeeab401ca486a3a9bc`, `cmobase/Zicbom.adoc` (`lines 1-68`) and `cmobase/csr_state.adoc` (`lines 26-145`): Ratified `Zicbom` v1.0.1 text.
2. **Sail RISC-V Formal Model**:
   - `riscv/sail-riscv` commit `76f1ce3c184797178864b9869963e8b44465889e`, `model/extensions/Zicbom/zicbom_types.sail` (`line 9`) and `model/extensions/Zicbom/zicbom_insts.sail` (`lines 11-145`: `cbop_priv_check` and `process_clean_inval` `Ok(_) => RETIRE_SUCCESS` at `lines 114-116`); extracted Lean 4 definitions in `opencompl/sail-riscv-lean` (`51c635c460125ac87955d061fcd902ce03b8011f`), `LeanRV64D/VmemPte.lean` (`lines 358-401`) and `LeanRV64D/VmemPtw.lean` (`lines 253-254`).
3. **Arm A-Profile Specification, `herdtools7`, and Literature**:
   - `ARM DDI 0487`: `DC CVAC`, `DC CIVAC`, `DC IVAC` (EL1+ only), `CTR_EL0.{CWG,DminLine}`, `SCTLR_EL1.UCI`.
   - `herd/herdtools7` commit `1ae595498c7af7d9d2f00e29aea328b36663104c`, `herd/libdir/aarch64.cat` (`lines 51-56, 80-90, 134-146`).
   - Peer-reviewed papers: Simner et al., ESOP 2020, DOI `10.1007/978-3-030-44914-7_22`; Raad, Wickerson, and Vafeiadis, OOPSLA 2019, DOI `10.1145/3360561`; Armstrong et al., POPL 2019, DOI `10.1145/3290384`; Sammler et al., PLDI 2021, DOI `10.1145/3453483.3454036`; Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`; Jung et al., POPL 2018, DOI `10.1145/3158154`; Klein et al., ACM TOCS 2014, DOI `10.1145/2560537`.
4. **Linux Kernel and Rust Aliasing Sources**:
   - `torvalds/linux` commit `d0f871bfb831705d9f55479f5b2b40f636ea7b16`: `arch/riscv/mm/dma-noncoherent.c` (`lines 15-157`), `arch/riscv/include/asm/cache.h` (`lines 10-17`), `arch/riscv/include/asm/errata_list.h` (`lines 138-152`), `arch/arm64/include/asm/cache.h` (`lines 28-37, 72-93`), `arch/arm64/mm/dma-mapping.c` (`lines 15-59`), `arch/arm64/mm/cache.S` (`lines 135-151`), `kernel/dma/direct.c` (`lines 220-359, 684-739`), `include/linux/dma-mapping.h` (`lines 739-750`), and `rust/kernel/dma.rs` (`lines 369-696, 1184-1221`).
   - `rust-lang/rust` commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `library/core/src/marker.rs` (`lines 892-920`).
   - `RalfJung/minirust` commit `063d784186d3252bee242217f218223205c0b568`, `spec/mem/interface.md` (`lines 13-50`), `spec/mem/tree_borrows/memory.md` (`lines 100-138`), and `spec/mem/tree_borrows/reborrow_settings.md` (`lines 18-48, 95-134`).
5. **Executable State-Space Model Check (`Basis: execution`)**:
   - Python 3.11 exhaustive check over all $16$ `(op_pre, op_post)` CMO pairs closed under speculative fills, clean evictions, and dirty writebacks confirmed: **`0 / 16`** passing with concurrent sibling CPU writes; **`4 / 16`** passing with quiescent pre-dirty siblings (`{CLEAN, FLUSH} × {FLUSH, INVAL}`); and **`6 / 16`** passing on dedicated cache granules (`{CLEAN, FLUSH, INVAL} × {FLUSH, INVAL}`).

## Revalidation

1. **Self-Contained Exhaustive Protocol Probe (< 1 second, Python 3.10+ stdlib only)**:
   ```bash
   python3 - <<'PY'
   from itertools import product
   OPS = ("NOP", "CLEAN", "FLUSH", "INVAL")
   def cmo(st, op):
       m, cs, cl = st
       if op == "NOP": return st
       if op == "INVAL": return (m, "I", None)
       if op == "CLEAN": return (cl, "U", cl) if cs == "M" else st
       if op == "FLUSH": return (cl if cs == "M" else m, "I", None)
   def close(sts):
       q, seen = list(sts), set(sts)
       while q:
           m, cs, cl = q.pop()
           nxt = (m, "U", m) if cs == "I" else ((m, "I", None) if cs == "U" else (cl, "I", None))
           if nxt not in seen: seen.add(nxt); q.append(nxt)
       return seen
   def cpu_w(sts, v):
       return close({(m, "M", (m[0] if cs == "I" else cl[0], v)) for m, cs, cl in sts})
   def dma_w(sts, v):
       return close({((v, m[1]), cs, cl) for m, cs, cl in sts})
   init = close({((0, 0), "M", (1, 1)), ((0, 0), "U", (0, 0)), ((0, 0), "I", None)})
   init_q = close({((0, 0), "M", (0, 1))})
   ok_conc, ok_quiesc, ok_ded = [], [], []
   for pre, post in product(OPS, OPS):
       s1 = close({cmo(s, pre) for s in init})
       s2c = cpu_w(dma_w(s1, 3), 2) | dma_w(cpu_w(s1, 2), 3)
       s3c = close({cmo(s, post) for s in s2c})
       if all((m if cs == "I" else cl) == (3, 2) and m[0] == 3 and (cs != "I" or m[1] == 2) for m, cs, cl in s3c):
           ok_conc.append((pre, post))
       s3q = close({cmo(s, post) for s in dma_w(close({cmo(s, pre) for s in init_q}), 3)})
       if all((m if cs == "I" else cl) == (3, 1) and m == (3, 1) for m, cs, cl in s3q):
           ok_quiesc.append((pre, post))
       s3d = close({cmo(s, post) for s in dma_w(s1, 3)})
       if all((m if cs == "I" else cl)[0] == 3 and m[0] == 3 for m, cs, cl in s3d):
           ok_ded.append((pre, post))
   assert len(ok_conc) == 0 and len(ok_quiesc) == 4 and len(ok_ded) == 6
   print("Verified:", len(ok_conc), ok_quiesc, len(ok_ded))
   PY
   ```
2. **Upstream Source Drift Checks**:
   - Diff `model/extensions/Zicbom/zicbom_insts.sail` and `model/sys/vmem_pte.sail` in `riscv/sail-riscv` to check whether `process_clean_inval` still ends in `Ok(_) => RETIRE_SUCCESS` or emits cache effects to a memory model, and whether `CB_manage` still checks `pte_R || pte_W` without setting `PTE.D`.
   - Diff `arch/riscv/include/asm/errata_list.h` (`ALT_CMO_OP`), `arch/riscv/mm/dma-noncoherent.c`, `arch/arm64/mm/cache.S` (`__dcache_inval_poc_nosync`), and `rust/kernel/dma.rs` in `torvalds/linux` if RISC-V adopts partial-line `cbo.flush` boundary promotion or Rust adds streaming DMA slice wrappers.
