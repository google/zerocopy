# Colored-Pointer Load Barriers, Generational ZGC Shift Uncoloring, Immix Block/Line Defragmentation, and MMTk LXR Invariants

## Summary

Modern ultra-low-pause concurrent and hybrid garbage collectors decouple heap compaction latency from live heap size through two orthogonal architectural mechanisms:

1. **Colored-pointer load-barrier compaction (Azul C4, Classic Single-Generation ZGC, and OpenJDK Generational ZGC):** Metadata encoding reachability, relocation epoch, and inter-generational tracking lives inside each 64-bit object reference rather than only in side bitmaps. In classic high-bit designs (Azul C4 Loaded Value Barrier and single-generation ZGC), upper virtual address bits (`[45:42]` in classic ZGC or `[63:48]` under Intel Linear Address Masking `LAM` / ARMv8 Top-Byte Ignore `TBI`) encode pointer color, requiring either multi-mapped virtual-address aliases (`mmap`ing the same physical heap across disjoint high-bit views) or hardware address masking so unmasked loads do not fault. **OpenJDK Generational ZGC** (`openjdk/jdk` @ `8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73`) inverts this layout: a colored `zpointer` places **16 metadata bits in the low-order bits `[15:0]`** (`RRRRMMmmFFrr0000`) and left-shifts the uncolored `zaddress` by `13..16` bits (`ZPointerLoadShiftTable`). On x86-64, a single speculative shift (`shrq ref, imm8`) followed by `ja slow_path` (`CF == 0 && ZF == 0`) simultaneously checks the active `Remapped` bit and uncolors `zpointer -> zaddress`, at the cost that any slow-path miss destroys the shifted register and must reload from memory (`volatile zpointer* p`).
2. **Coarse-block / fine-line mark-region heaps (`Immix` and `LXR` in `mmtk/mmtk-core`):** Instead of continuously evacuating every live region behind a read barrier, `Immix` (`PLDI 2008`, `10.1145/1375581.1375586`) and `LXR` (`PLDI 2022`, `10.1145/3519939.3523440`) partition contiguous `32 KiB` blocks (`Block::LOG_BYTES = 15`) into fine lines (`128 B` in JikesRVM Immix; `256 B` / `Line::LOG_BYTES = 8`, `128` lines per block in `mmtk/mmtk-core` @ `d154f4f0dcca27439b920165ce5c948ca18aef24`), enabling mutators to bump-allocate into free line holes while reserving single-pass opportunistic copying only for fragmented defragmentation-source blocks. **LXR** pairs Immix block/line reclamation with a coalesced field-unlog write barrier (`ProcessIncs` / lazy `ProcessDecs`), `RCArray` wide-integer dead-line sweeping, conservative first-dead-line straddle protection (`Block::has_holes`), and concurrent Snapshot-at-the-Beginning (`SATB`) backup cycle tracing.

Across both families, soundness hinges on three hardware-software boundary invariants: (i) **monotonic publication and release-acquire ordering** so a mutator observing a forwarded address or self-healed slot never reads pre-copy bytes; (ii) **strict FFI uncoloring and pinning isolation**, where passing a raw Generational ZGC `zpointer` to native C/Rust FFI shifts virtual addresses by `13..16` bits (rendering `LAM`/`TBI` insufficient), while `ZJNICritical` blocks all mutator entry into JNI critical sections during GC stalls in contrast to MMTk's per-object `LOCAL_PINNING_BIT_SPEC` in-place pinning; and (iii) **virtual-bit budget partitioning** between GC color bits, relocation table indices (`ZForwardingEntry` 45-bit offset limit), and ARM64 `PAC`/`MTE`.

## Applicability

This report covers and contrasts the following verified systems, revisions, and literature:

- **OpenJDK HotSpot Generational ZGC** (`openjdk/jdk` @ `8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73`): Specifically `src/hotspot/share/gc/z/{zAddress.hpp, zAddress.cpp, zAddress.inline.hpp, zBarrier.hpp, zBarrier.inline.hpp, zForwardingEntry.hpp, zForwarding.inline.hpp, zRelocate.cpp, zJNICritical.cpp, zUncoloredRoot.hpp}` and architecture backends `src/hotspot/cpu/x86/gc/z/{zAddress_x86.cpp, zAddress_x86.inline.hpp, zBarrierSetAssembler_x86.hpp, zBarrierSetAssembler_x86.cpp, z_x86_64.ad}` and `src/hotspot/cpu/aarch64/gc/z/{zAddress_aarch64.cpp, zAddress_aarch64.inline.hpp, zBarrierSetAssembler_aarch64.cpp}`. This revision reflects post-JEP 439/474 Generational ZGC where low-order 16-bit `zpointer` coloring and generational store+load barriers replaced single-generation high-bit multi-mapped pointers.
- **Classic Single-Generation ZGC** (`Yang & Wrigstad, ACM TOPLAS 2022`, `DOI: 10.1145/3538532`) and **Azul C4** (`Tene, Iyengar, Wolf, ISMM 2011`, `DOI: 10.1145/1993478.1993491`): Referenced to trace the architectural contrast between high-bit colored pointers (multi-mapping, x86 `LAM`, ARM64 `TBI`) and Generational ZGC's low-order shift encoding.
- **MMTk Core Immix and LXR Collectors** (`mmtk/mmtk-core` @ `d154f4f0dcca27439b920165ce5c948ca18aef24`): Specifically `src/policy/immix/{block.rs, line.rs, defrag.rs, immixspace.rs}`, `src/plan/lxr/{mod.rs, barrier.rs, global.rs, mature_evac.rs}`, and `src/util/object_forwarding.rs`, compared against the original Immix (`Blackburn & McKinley, PLDI 2008`, `DOI: 10.1145/1375581.1375586`) and LXR (`Zhao, Blackburn, McKinley, PLDI 2022`, `DOI: 10.1145/3519939.3523440`) designs.
- **Weak-Memory Collector Verification**: Grounded in `Gammie, Hosking, Engelhardt, PLDI 2015` (`DOI: 10.1145/2737924.2738006`) for x86-TSO store-buffer collector invariants, and directly cross-checked against atomic orderings (`Ordering::SeqCst`, `OrderAccess::release()`, `AtomicAccess::load_acquire`) in `mmtk/mmtk-core` and `openjdk/jdk`.

Behavior observed in Generational ZGC's low-bit `zpointer` architecture does **not** apply to pre-generational OpenJDK ZGC (JDK 11–20), and `mmtk-core`'s 256-byte line configuration (`Line::LOG_BYTES = 8`) differs from the 128-byte lines evaluated in the PLDI 2008 Immix paper.

## Findings

### 1. From High-Bit Colored Pointers (`LAM`/`TBI`/Multi-Mapping) to Generational ZGC Low-Bit Shift Coloring

**Basis:** `documentation` (`10.1145/1993478.1993491`, `10.1145/3538532`) + `source` (`openjdk/jdk` `zAddress.hpp`, `zAddress.cpp`, `zAddress_x86.cpp`, `zAddress_x86.inline.hpp`, `zAddress_aarch64.cpp`, `zAddress_aarch64.inline.hpp`, `zBarrier.hpp`, `zBarrierSetAssembler_x86.cpp`, `z_x86_64.ad`) + `execution` (micro-probe).

#### 1.1 High-Bit Designs and Address-Space Contention

Both **Azul C4** (`10.1145/1993478.1993491`) and **Single-Generation ZGC** (`10.1145/3538532`) embedded GC metadata directly in upper bits of a 64-bit reference:

- **Azul C4 Loaded Value Barrier (LVB):** Placed an `NMT` (Not Marked Through) bit and space/relocation bits in upper virtual address bits (`[63:42]` class). C4's fast path executes a bit test and conditional jump (`test` + `jnz`) before dereference, repairing stale pointers via an off-heap forwarding table and self-healing `CAS`, originally leveraging specialized page-trap/multi-map support on Azul Vega and software `test`+branch LVBs on commodity x86-64.
- **Classic Single-Generation ZGC (`TOPLAS 2022`):** Encoded four mutually exclusive metadata bits—`Marked0`, `Marked1`, `Remapped`, `Finalizable`—in upper bits `[45:42]` above a 42-bit (`4 TiB`) to 44-bit (`16 TiB`) heap offset. Because x86-64 CPUs lacking Linear Address Masking (`LAM`) treat bits `[47:0]` (or `[56:0]` with 5-level paging) as significant canonical address bits, classic ZGC mapped each physical heap backing granule into **three overlapping virtual address views** (`Marked0`, `Marked1`, `Remapped`) via `mmap`/`memfd`. On hardware supporting **ARMv8 Top-Byte Ignore (`TBI`, `TCR_EL1.TBI0 = 1`)**—which ignores bits `[63:56]` during address translation—or **Intel `LAM_U48` (`[62:48]`) / `LAM_U57` (`[62:57]`)** and **AMD `UAI` (`[63:57]`)**, hardware ignores upper tag bits automatically, eliminating virtual multi-mapping aliasing and TLB duplication.
- **Why Generational ZGC Abandoned High-Bit Multi-Mapping:** Supporting separate concurrent young and old cycles (`MarkedYoung`, `MarkedOld`, `Finalizable`, `Remembered`, and joint `Remapped`) requires **12 active metadata bits plus 4 reserved bits (16 total color bits)**. Placing 16 color bits in high virtual bits leaves only `48 - 16 = 32` bits (`4 GiB`) under 4-level x86 paging without `LAM`, collides with ARM64 Pointer Authentication Codes (`PAC`, typically `[54:48]`/`[63:56]` minus TBI) and Memory Tagging Extension (`MTE`, bits `[59:56]`), and would require dozens of `mmap` aliases if unmasked.

#### 1.2 Generational ZGC 16-Bit Low-Order `zpointer` Layout

In `openjdk/jdk` @ `8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73` (`src/hotspot/share/gc/z/zAddress.hpp:48-196`), an uncolored heap pointer (`zaddress`, bit `ZAddressHeapBase` set + `ZAddressOffsetBits` offset) is converted into a colored `zpointer` by left-shifting `zaddress` and packing 16 metadata bits in `[15:0]`:

| Bit Range | Width | Field (`zAddress.hpp:138-176`) | Symbolic Colors & Purpose |
| :--- | :--- | :--- | :--- |
| `[3:0]` | 4 | `ZPointerReservedMask` | Reserved (`0` in valid `zpointer`s; checked by `is_valid`) |
| `[5:4]` | 2 | `ZPointerRememberedMask` (`rr`) | `Remembered0` (`bit 4`), `Remembered1` (`bit 5`); `11` marks old-to-old / forgotten slots (`zBarrier.inline.hpp:228-235`) |
| `[7:6]` | 2 | `ZPointerFinalizable[0,1]` (`FF`) | Alternating phase bit for finalizer-reachable old references |
| `[9:8]` | 2 | `ZPointerMarkedYoung[0,1]` (`mm`) | Alternating young-mark phase bits (`0b01` vs `0b10`) |
| `[11:10]` | 2 | `ZPointerMarkedOld[0,1]` (`MM`) | Alternating old-mark phase bits (`0b01` vs `0b10`) |
| `[15:12]` | 4 | `ZPointerRemappedMask` (`RRRR`) | One-hot joint relocation state `Remapped00` (`0x1000`), `Remapped01` (`0x2000`), `Remapped10` (`0x4000`), `Remapped11` (`0x8000`) |

Rather than maintaining separate `RemappedYoung` and `RemappedOld` bits, `ZGlobalsPointers::set_good_masks()` (`zAddress.cpp:78-88, 120-152`) maintains two 4-bit alternating parity masks:

- `ZPointerRemappedOldMask` alternates between `RemappedOld0 = 0b0011` (`01 | 00`) and `RemappedOld1 = 0b1100` (`11 | 10`).
- `ZPointerRemappedYoungMask` alternates between `RemappedYoung0 = 0b0101` (`10 | 00`) and `ZPointerRemapped1 = 0b1010` (`11 | 01`).
- Their bitwise intersection `ZPointerRemapped = ZPointerRemappedOldMask & ZPointerRemappedYoungMask` always yields **a single one-hot bit** in `[15:12]` (`0001`, `0010`, `0100`, or `1000`).

#### 1.3 Speculative Single-Instruction `SHR` + `JA` Uncoloring vs. AArch64 Complemented Bits

On **x86-64** (`zAddress.hpp:75-106, 179-189`, `zAddress_x86.inline.hpp:29-37`, `zBarrier.hpp:31-68`, `zBarrierSetAssembler_x86.cpp:1028-1080`, `z_x86_64.ad:44-82`), JIT-compiled strong load barriers combine good-bit testing and uncoloring into **two instructions** (`shrq` + `jcc(Assembler::above)`):

1. `ZPointerLoadShiftTable` maps the active one-hot `Remapped` bit to shift distance `ZPointerLoadShift ∈ {13, 14, 15, 16}` (`ZPointerRemappedShift + 1..4` where `ZPointerRemappedShift = 12`).
2. Coloring (`ZAddress::color` / `z_color`) computes `(zaddress << ZPointerLoadShift) | color`, overlapping `0..3` low-order zero alignment bits of an 8-byte-aligned object address (`addr[2:0] == 0b000`) with the unused upper `Remapped` zeros (`zAddress.hpp:78-92`).
3. The JIT fast path executes `shrq ref, <patched_ZPointerLoadShift>` followed by `ja slow_path`:
   - If `ref` holds the active `Remapped` bit (`1` at position `ZPointerLoadShift - 1`), that `1` shifts out into the x86 carry flag **`CF = 1`**, `ZF = 0`, `ref` holds the exact uncolored `zaddress`, and `JA` (`CF == 0 && ZF == 0`) falls through with **zero extra mask/shift instructions**.
   - If `ref == 0` (raw `null`), `shrq` sets **`ZF = 1`**, `CF = 0`, and `JA` falls through cleanly to `0`.
   - Otherwise (`CF == 0 && ZF == 0`), `JA` branches to the slow-path stub, which **must reload the original `zpointer` from `[ref_addr]`** (`zBarrierSetAssembler_x86.cpp:1078-1079`) because the speculative shift destroyed the low metadata bits and used a different shift from the slot's writer!
4. **Alignment Constraint & Barrier-Bypass Failure Mode:** As `zBarrier.hpp:55-60` warns and our micro-probe confirms, shifts may span only 4 values (`13..16`, difference `<= 3`) because heap object addresses only guarantee **3 low-order zero bits** (`8-byte` alignment, `zAddress.inline.hpp:444`). If an invalid or FFI-corrupted 4-byte-aligned pointer (`addr & 0x4 != 0`) is colored with `Remapped00` (`shift = 13`), address bit 2 (`0x4`) shifts left to bit `2 + 13 = 15`, which collides with `Remapped11` (`0x8000`)! When GC flips to `Remapped11` (`shift = 16`), `shrq ref, 16` shifts bit 15 into `CF = 1`, creating a **false-good barrier bypass** that hands the mutator a bit-shifted garbage address (`addr >> 3`) without entering the slow path.
5. **AArch64 Complemented Design (`zAddress_aarch64.cpp`, `zAddress_aarch64.inline.hpp`):** AArch64 does *not* overlap address zeros with metadata zeros and always shifts by fixed `ZPointerLoadShift` (probed via `probe_valid_max_address_bit` using `msync`/`mmap` downward from `DEFAULT_MAX_ADDRESS_BIT = 46`, subtracting 3 to leave headroom for metadata shifts). Critically, `ZPointer::remap_bits` on AArch64 returns `(colored ^ ZPointerRemappedMask) & ZPointerRemappedMask` (`zAddress_aarch64.inline.hpp:30`), making `ZPointerLoadBadMask` single-bit and `ZPointerLoadGoodMask` 3-bit complemented (`zAddress.hpp:104-106`).

### 2. Off-Heap Forwarding Tables, Monotonic Self-Healing, and Double-Remap-Bad Resolution

**Basis:** `source` (`openjdk/jdk` `zForwardingEntry.hpp`, `zForwarding.inline.hpp`, `zRelocate.cpp`, `zBarrier.inline.hpp`, `mmtk/mmtk-core` `src/util/object_forwarding.rs`) + `execution` (micro-probe).

#### 2.1 `ZForwardingEntry` Layout vs. MMTk In-Header/Side Forwarding

- **ZGC Off-Heap Linear-Probing Forwarding (`zForwardingEntry.hpp:38-80`, `zForwarding.inline.hpp:43-50, 207-293`):** Rather than overwriting object headers (Brooks/to-space forwarding pointers), ZGC allocates an off-heap `ZForwarding` hash table sized to `round_up_power_of_2(page->live_objects() * 2)` (`<= 50%` load factor) per relocated page. Each 64-bit `ZForwardingEntry` packs:
  - Bit `0`: `populated` flag (`1 bit`).
  - Bits `[45:1]`: `to_offset` (`45 bits`, directly fixing the maximum heap virtual offset at $2^{45}$ bytes / bit `46` ceiling in `DEFAULT_MAX_ADDRESS_BIT = 46`).
  - Bits `[63:46]`: `from_index` (`18 bits`, granule-relative object index `(from_offset - page_start) >> object_alignment_shift`).
  Concurrent mutators and GC workers execute `relocate_object_inner` (`zRelocate.cpp:355-381`): allocate target memory, copy bytes (`ZUtils::object_copy_disjoint`), execute `OrderAccess::release()` (`zForwarding.inline.hpp:273`), and `cmpxchg` into the table. Losers undo their target allocation (`undo_alloc_object_for_relocation`) and read the winner's entry via `AtomicAccess::load_acquire` (`zForwarding.inline.hpp:210`).
- **MMTk 2-Bit In-Place Forwarding Protocol (`src/util/object_forwarding.rs:8-145`):** MMTk uses a 3-state protocol (`FORWARDING_NOT_TRIGGERED_YET = 0b00`, `BEING_FORWARDED = 0b10`, `FORWARDED = 0b11`) in `LOCAL_FORWARDING_BITS_SPEC`:
  - `attempt_to_forward` atomically CASes `0b00 -> 0b10` (`Ordering::SeqCst` on success).
  - Concurrent losers spin in `spin_and_get_forwarded_object` while state is `0b10`.
  - Winners copy the object, run `on_after_forwarding`, and store `(new_addr | (0b11 << shift))` with `Ordering::SeqCst` (when both forwarding pointer and bits share one header word) or store pointer then `0b11` with `Ordering::SeqCst`.
  - **Opportunistic Rollback Edge Case (`mmtk/mmtk-core#579`, `object_forwarding.rs:64-75`, `immixspace.rs:945-961`):** In Immix, a worker that won `0b00 -> 0b10` and then discovers the object is pinned or defrag space is exhausted calls `clear_forwarding_bits` (`0b10 -> 0b00`) and leaves the object unmoved; spinning threads exiting `while forwarding_bits == BEING_FORWARDED` must check `forwarding_bits == FORWARDED` and return the original `object` on `0b00`.

#### 2.2 Monotonic `self_heal` Lattice and Double-Remap-Bad Disambiguation

`ZBarrier::self_heal` (`zBarrier.inline.hpp:72-108`) upgrades stale slot colors in place with `AtomicAccess::cmpxchg(p, ptr, heal_ptr, memory_order_relaxed)` in a CAS loop:

1. **Null-Healing Guard (`zBarrier.inline.hpp:73-79`):** If a weak/phantom load barrier resolves a dead referent to `null` (`!allow_null && is_null_assert_load_good(heal_ptr)`), it refuses to overwrite a non-null slot so mutators cannot race ahead of `Reference` discovery (`Reference.clear()`).
2. **Transition Monotonicity (`assert_transition_monotonicity`, `zBarrier.inline.hpp:41-70`):** Under the barrier strength ordering $\text{LoadGood} \preceq \text{FinalizableGood} \preceq \text{MarkGood} \preceq \text{StoreGood}$, every CAS retry checks that no previously good property (`is_load_good`, `is_mark_good`, `is_store_good`, `is_marked_young`, `is_marked_old`) is ever downgraded by a concurrent slower barrier.
3. **Double-Remap-Bad Disambiguation (`ZBarrier::remap_generation`, `zBarrier.inline.hpp:110-292`):** Because Generational ZGC runs young and old collections concurrently/interleaved, a slot in a promoted or survivor object whose remembered-set entry was forgotten (`zBarrier.inline.hpp:228-235`) can become **neither young-load-good nor old-load-good** (`double remap bad`), meaning its `zaddress_unsafe` could match a relocated page in *either* generation's forwarding table. ZGC resolves this without extra metadata tables via a crisp two-step invariant:
   - Whenever a barrier forgets a pointer or heals an old-to-any field via a non-store barrier, it writes **both remembered bits** (`rr == 0b11`, `ZPointerRememberedMask`), ensuring subsequent stores hit `store_bad` while distinguishing old-to-old slots from young-generation slots (which only ever receive a single remembered bit).
   - Thus, if `remembered_bits == ZPointerRememberedMask` (`0b11`), `remap_generation` returns `ZGeneration::old()`; otherwise (single remembered bit), the young and old relocation sets are guaranteed disjoint at that snapshot, so checking `ZGeneration::young()->forwarding(addr) != nullptr` uniquely identifies the owning generation!

### 3. Immix Coarse-Block / Fine-Line Mark-Region Heap and Opportunistic Defragmentation

**Basis:** `documentation` (`10.1145/1375581.1375586`) + `source` (`mmtk/mmtk-core` `src/policy/immix/{block.rs, line.rs, defrag.rs, immixspace.rs}`) + `execution` (micro-probe).

#### 3.1 Block & Line Geometry and Side-Metadata State Encoding

| Parameter | JikesRVM Immix (`PLDI 2008`) | `mmtk/mmtk-core` (`d154f4f0...`) | Source / Rationale |
| :--- | :--- | :--- | :--- |
| Block size (`Block::LOG_BYTES`) | `32 KiB` (`15`) | `32 KiB` (`15`; `8 KiB`/page if `immix_smaller_block`) | `block.rs:89-97`; `UnstraddlableRegion` guarantees objects never cross blocks |
| Line size (`Line::LOG_BYTES`) | `128 B` (`7`) | `256 B` (`8`) | `line.rs:21`; trades line-table footprint/scan cost vs hole granularity |
| Lines per block (`Block::LINES`) | `256` | `128` | `block.rs:124-126`; fits `Block::LINES / 2 = 64 <= 253` in `u8` hole/state fields |
| `BlockState` encoding (`u8`) | Enum/byte tags | `0=Unallocated`, `255=Unmarked`, `254=Marked`, `253=Nursery`, `252=Reusing`, `1..=251=Reusable{unavailable_lines}` | `block.rs:36-74`; single-byte atomic `IX_BLOCK_MARK` state machine |
| Line mark epochs (`Line::MAX_MARK_STATE`) | Single bit cleared per GC | Rolling `u8` state `1..=127` (`RESET_MARK_STATE = 1`) | `line.rs:37-38`, `block.rs:455-459`, `immixspace.rs:634-640`; avoids bulk clearing on normal GCs, clearing `0` only when `line_mark_state > 125` |
| Object straddle marking | Small objects mark object line + next line | Exact `[start, end)` range in `mark_lines_for_object` | `line.rs:70-89`; avoids unconditional +1 overflow line mark when object size is available |

#### 3.2 Hole Counting, Histogram-Bounded Defragmentation, and Opportunistic Fallback

During `Block::sweep` (`block.rs:441-508`), `mmtk-core` scans each block's 128 lines sequentially, counting `marked_lines` and contiguous unmarked gaps (`holes`). Blocks with `0` marked lines are released immediately (`BlockSweepResult::Swept`); blocks with `0 < marked_lines < 128` transition to `BlockState::Reusable { unavailable_lines }`, push onto `space.reusable_blocks`, record `holes` in `IX_BLOCK_DEFRAG` (`set_holes(holes)`), and increment `mark_histogram[holes] += marked_lines`.

When defragmentation triggers (`Defrag::decide_whether_to_defrag`, `defrag.rs:66-116`, disabled whenever `rc_enabled` is true because LXR uses its own `MatureEvacuationSet`):

1. `establish_defrag_spill_threshold` (`defrag.rs:198-238`) computes `available_lines` from free lines in reusable blocks plus `available_clean_pages_for_defrag` headroom (scaled by `DEFRAG_LINE_REUSE_RATIO = 0.99`), then iterates hole buckets **top-down** from `NUM_BINS - 1` (`64`) down to `MIN_SPILL_THRESHOLD` (`2`), accumulating `required_lines` (live lines in evacuated blocks) and subtracting `this_bucket_avail` (free holes lost by evacuating those blocks) until `limit < required_lines`.
2. Any block with `holes >= threshold` is flagged `DEFRAG_SOURCE_STATE = u8::MAX` (`set_as_defrag_source(true)`).
3. During tracing (`immixspace.rs:891-996`), workers copy objects in defrag-source blocks into clean/reusable target lines; if `defrag.space_exhausted()` flips `true` (`notify_new_clean_block`, `defrag.rs:131-148`) or the object is pinned, `trace_object_with_opportunistic_copy` seamlessly switches to **in-place marking without moving**, guaranteeing defragmentation never causes fatal copy-reserve OOM.

### 4. LXR Coalesced Reference Counting, Straddle-Safe `RCArray` Sweeping, and SATB Tracing

**Basis:** `documentation` (`10.1145/3519939.3523440`) + `source` (`mmtk/mmtk-core` `src/plan/lxr/{mod.rs, barrier.rs, global.rs, mature_evac.rs}`, `src/policy/immix/{block.rs, line.rs}`) + `execution` (micro-probe).

Unlike ZGC's load-barrier collector, `LXR` (`Latency-Critical Reference Counting`) minimizes pause durations and write-barrier traffic through five tightly coupled mechanisms in `mmtk-core`:

1. **Coalesced Field-Unlog Write Barrier (`lxr/barrier.rs:97-170, 224-302`):**
   - Instead of emitting RC increments/decrements on every heap pointer store, `LXRFieldBarrierSemantics` checks a per-field side bit (`GLOBAL_FIELD_UNLOG_BIT_SPEC`). The fast path skips already-logged fields (`state == LOGGED_VALUE`); only the **first modification to a slot within an epoch** CASes `UNLOGGED_VALUE -> LOGGED_VALUE` (`log_slot_and_get_old_target`, `barrier.rs:127-137`), reads `old = slot.load()`, pushes `old` to the local `decs` buffer, and pushes the **slot address `slot`** (not the new referent!) to `incs`.
   - For bulk array/slice writes (`memory_region_copy_slow`, `barrier.rs:247-270`), LXR scans aligned `u128` words of `UNLOG_BITS` (`cursor.load::<u128>() == 0`, since `LOGGED_VALUE == 0`!) to skip already-logged slices in constant chunks before iterating individual slots.
   - Deferring `incs` evaluation to `ProcessIncs` at the pause automatically coalesces temporary local mutations and requires scanning only the latest value in `slot` once per epoch (`lxr_inc_buffer_limit` bounds pause time, `lxr/global.rs:112-114`).
2. **Dual-Purpose `decs` + `SATB` Barrier During Concurrent Cycle Collection (`lxr/barrier.rs:172-211`):**
   - When concurrent backup tracing is active (`should_create_satb_packets()`), `flush_decs_and_satb` wraps the `decs` vector in an `Arc` and dispatches it **both** to `WorkBucketStage::FinishConcurrentWork` (`ProcessModBufSATB`) and to `ProcessDecs` (queued onto `WorkBucketStage::Concurrent` when `LAZY_DECREMENTS` is enabled, or `STWRCDecsAndSweep` otherwise). Overwritten `old` targets therefore preserve Snapshot-at-the-Beginning reachability without a second write barrier, and `load_weak_reference` (`barrier.rs:272-280`) enqueues unmarked weak referents into `ProcessModBufSATB` on concurrent read.
3. **Line-Granularity `RCArray` Dead Detection & Straddle-Guard `has_holes` (`immix/line.rs:259-279`, `immix/block.rs:140-149, 560-643`):**
   - LXR stores object reference counts in side `RC_TABLE`. `RCArray::of(block)` indexes the block's `RC_TABLE` as an array of 128 wide unsigned integers `<Uint<{ BITS_PER_LINE }>>` (`u8`..`u2048`), testing an entire 256-byte line's liveness with a single integer `is_zero` check (`line.rs:276-278`).
   - Crucially, **`Block::has_holes` (`block.rs:623-643`) skips the first dead line immediately following any non-dead line (`if i == 0 || found_free_line`)**! Because an object whose header resides in live line `i - 1` can straddle into line `i` without holding a non-zero RC entry on line `i` itself (unlike mark-sweep `line.mark_lines_for_object`), line `i` is only proven free if line `i - 1` was also dead (or `i == 0`). Our probe verifies that alternating single-line dead gaps yield `has_holes == false`, preventing mutator hole-reuse from clobbering straddling object tails!
4. **Epoch-Reused RemSet Entries for Mature Evacuation (`lxr/mature_evac.rs:28-44, 134-230`):**
   - `MatureEvacuationSet` caps pause-time copying bytes to `max_copy_bytes` (`available_clean_pages_for_defrag << LOG_BYTES_IN_PAGE`) over the most fragmented blocks (`SelectDefragBlocks`). Remembered slots recorded for mature relocation store `(VMSlot, reuse_epoch)` (`RemSetEntry`, sampling `IX_LINE_REUSE_COUNT` / `LOS_PAGE_REUSE_COUNT`, `mature_evac.rs:31-43`) so stale remembered-set entries whose source lines were lazily swept and reused are safely discarded rather than corrupting newly allocated objects.
   - `LXR::new` (`lxr/global.rs:427-431`) strictly asserts that `LOCAL_FORWARDING_BITS_SPEC.is_in_header()` whenever `LXR_CONSTRAINTS.moves_objects` is true, rejecting side-table forwarding bits during evacuating builds.

### 5. Weak-Memory Ordering, Conservative Pinning, FFI Uncoloring, and Verification Invariants

**Basis:** `normative` (`10.1145/2737924.2738006`) + `source` (`openjdk/jdk` `zForwarding.inline.hpp`, `zBarrier.inline.hpp`, `zJNICritical.cpp`, `zUncoloredRoot.hpp`; `mmtk/mmtk-core` `object_forwarding.rs`, `immixspace.rs`, `lxr/global.rs`) + `derived`.

#### 5.1 Weak-Memory Ordering Constraints (x86-TSO vs. ARMv8)

1. **Object Copy vs. Forwarding Publication (`Release -> Acquire`):** Copying an object's fields to `to_addr` and installing the forwarding pointer cannot rely on relaxed writes on ARM64 or even out-of-order stores on TSO when non-trivial copy routines are used. Generational ZGC places an explicit `OrderAccess::release()` (`zForwarding.inline.hpp:273`) before the `cmpxchg` inserting the `ZForwardingEntry`, paired with `AtomicAccess::load_acquire` (`zForwarding.inline.hpp:210`) on lookup. MMTk enforces `Ordering::SeqCst` on both the forwarding pointer write (`object_forwarding.rs:86-100`) and `read_forwarding_pointer` / `get_forwarding_status` (`object_forwarding.rs:148-208`). Note that ZGC's `self_heal` uses `memory_order_relaxed` (`zBarrier.inline.hpp:92`) *only* because the target object's forwarding entry publication already established `release -> acquire` visibility before `self_heal` constructs `heal_ptr`.
2. **On-the-Fly TSO Tricolor Verification (`Gammie et al., PLDI 2015`, `10.1145/2737924.2738006`):** Under x86-TSO store buffers, a mutator writing a white reference into a black object can delay draining its store buffer until after a collector checks handshake flags; formalized Isabelle/HOL proofs of Schism establish that maintaining strong tricolor safety under TSO requires either a handshake drain (store-buffer flush fence per mutator) before color-phase transitions or read/write barriers that treat buffered/unhealed references monotonically (`assert_transition_monotonicity`).

#### 5.2 FFI Uncoloring, Conservative Line Pinning, and Cross-System Comparison

| Collector / Mechanism | Address Representation | FFI Dereference Safety | Pinning / Non-Moving Model | Bit Budget Conflict (`PAC` / `MTE` / `LAM` / `TBI`) |
| :--- | :--- | :--- | :--- | :--- |
| **Azul C4** (`10.1145/1993478.1993491`) | High-bit colored pointer (`NMT` + space bits) | Unsafe without LVB uncoloring unless multi-mapped or masked | VM-coordinated safepoint / page pinning or handle indirection | High bits contend with OS/CPU VA limits or `LAM`/`TBI` |
| **Classic ZGC** (`10.1145/3538532`) | High-bit `[45:42]` multi-mapped alias | Multi-mapped VA alias dereferenceable if `Remapped`, *not* safe across relocation without barrier | `ZJNICritical` / handle uncoloring | Multi-mapping consumes 3x virtual address ranges; `TBI`/`LAM` removes alias need if `[63:56]` used |
| **Generational ZGC** (`8ef2f5dd...`) | Low-bit 16-bit shifted `zpointer` (`[15:0]`) | **Immediately fatal** if passed raw to FFI (`LAM`/`TBI` do **not** unshift low bits!) | Global `ZJNICritical` gate (`_count`: `>=0` active, `-(count+1)` draining, `-1` blocked; `zJNICritical.cpp:56-181`) | Low 16 bits avoid `PAC`/`MTE` upper bits; max heap offset capped at 45 bits by `ZForwardingEntry` (`zForwardingEntry.hpp:55`) |
| **MMTk Immix** (`d154f4f0...`) | Uncolored native `ObjectReference` + side/header metadata | Direct pointer if non-moving or pinned (`LOCAL_PINNING_BIT_SPEC`) | Per-object `pin_object` (`immixspace.rs:180-200`, `945-961`) + `TRACE_KIND_TRANSITIVE_PIN` leaves line/block intact without global GC stall | Zero VA color bits consumed; completely compatible with hardware `PAC`/`MTE`/`LAM`/`TBI` |
| **MMTk LXR** (`d154f4f0...`) | Uncolored native `ObjectReference` + side `RC_TABLE`/`UNLOG_BITS` | Direct pointer if pinned or `non_moving_root` (`lxr/global.rs:367-378`) | `RCProcessIncsNonMoving` scans non-moving/conservative roots before evacuating; mature evac skips non-selected blocks | Zero VA color bits; requires in-header forwarding bits when evacuation enabled (`lxr/global.rs:427-431`) |

**Formal Movable-Reference & FFI Verification Obligations:**
For any verified runtime or FFI boundary bridging a moving collector (`zpointer` or evacuating Immix/LXR) and unsafe native code (C/Rust):

1. **Disjoint Representation Types (`zpointer` vs. `zaddress` vs. `zaddress_unsafe`):** Never expose raw `zpointer` values as dereferenceable C/Rust pointers (`*const T`). Even on hardware with `LAM` or `TBI`, Generational ZGC shifts heap addresses left by `13..16` bits (`zAddress.inline.hpp:735`); hardware high-bit masking cannot invert a left-shift. Uncoloring must pass through `ZBarrier::load_barrier_on_oop_field` (producing `zaddress`) or external-color `ZUncoloredRoot` barriers (`zUncoloredRoot.hpp:56-84`).
2. **Evacuation-Exclusion Lease (Pinning or Critical-Region Token):** A native FFI slice `&[u8]` derived from a GC-managed object requires a linear non-relocation witness $\mathcal{L}_{\text{pin}}(obj)$ during its entire lifetime: either (a) entering `ZJNICritical` (which stalls concurrent relocation phases in ZGC when `_count` blocks at `-1`, risking tail-latency spikes if held across blocking I/O), or (b) setting `LOCAL_PINNING_BIT_SPEC` / conservative stack-root line pinning (`TRACE_KIND_TRANSITIVE_PIN`) in Immix/LXR, which immobilizes only the containing object/line (`256 B`) while letting all other blocks evacuate concurrently.
3. **Invariant Check on Forwarding & Write Barriers:** Any verifier proving safety of an optimizing JIT or Rust runtime binding over Generational ZGC or MMTk LXR must preserve:
   - *Alignment invariant*: $\forall a \in \text{zaddress},\; (a \bmod 8) = 0$ (required by ZGC `shr`+`ja` shift span `<= 3`).
   - *Monotonicity invariant*: $\text{barrier\_heal}(p, \text{old}, \text{new}) \implies \text{strength}(\text{old}) \le \text{strength}(\text{new})$ and $\text{old} \neq \text{null} \implies \text{new} \neq \text{null}$ (unless authorized by reference-clearing weak/phantom clean phase).
   - *Release-before-publish invariant*: $\text{copy}(src, dst) <_{\text{hb}} \text{release} <_{\text{hb}} \text{publish\_forwarding}(src, dst) <_{\text{hb}} \text{acquire}(dst) <_{\text{hb}} \text{read\_payload}(dst)$.

## Boundaries

- **OpenJDK Shenandoah Brooks / Load-Reference Barriers:** `not examined`. This study inspected Generational ZGC in `openjdk/jdk` (`8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73`) and MMTk Immix/LXR (`d154f4f0dcca27439b920165ce5c948ca18aef24`), not Shenandoah's object-header forwarding word or SATB barrier implementation.
- **RISC-V `Ssnpm`/`Smnpm` Pointer Masking Hardware Behavior:** `not examined`. While ARM64 `TBI`/`PAC`/`MTE` and x86 `LAM_U48`/`LAM_U57` bit budgets were analyzed against Generational ZGC's low-bit layout, RISC-V pointer-masking CSR behavior was not tested.
- **Direct Dereference of `zpointer` via `LAM`/`TBI` Hardware Tagging:** `known not to apply` to Generational ZGC (`8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73`). Hardware `LAM`/`TBI` only masks upper virtual bits (`[62:48]` / `[63:56]`), whereas Generational ZGC places 16 metadata bits in `[15:0]` and left-shifts the address by `13..16` bits (`zAddress.hpp:48-106`, `zAddress.inline.hpp:734-736`), making unshifted dereference impossible without a `shr` barrier.
- **Fine-Grained Per-Object Non-Blocking FFI Array Pinning in ZGC:** `unsupported` in `openjdk/jdk` @ `8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73`'s `ZJNICritical` (`zJNICritical.cpp:56-181`), which uses a global counter (`_count < 0`) to block JNI critical entry and drain active critical threads rather than pinning individual pages/lines in place during relocation.
- **Side-Table Forwarding Bits During Evacuating LXR Builds:** `unsupported` in `mmtk/mmtk-core` @ `d154f4f0dcca27439b920165ce5c948ca18aef24`, enforced by a runtime panic in `LXR::new` (`src/plan/lxr/global.rs:427-431`).
- **LXR Line-Level Straddle Pinning Interaction With `object_pinning` Feature:** `unknown` without inspecting a concrete VM binding's `non_moving_root` + `object_pinning` configuration together, as `ImmixSpace::side_metadata_specs(rc_enabled: true)` (`immixspace.rs:376-389`) omits `LOCAL_PINNING_BIT_SPEC` in the `rc_enabled` branch.

## Evidence

- **OpenJDK HotSpot Generational ZGC** (`openjdk/jdk` @ `8ef2f5dd58a42a77909639d0c04ca09ebe4cdf73`):
  - `src/hotspot/share/gc/z/zAddress.hpp` (L48–196, L246–325): 16-bit `zpointer` layout, `ZPointerLoadShiftTable`, `ZAddress`/`ZPointer` separation.
  - `src/hotspot/share/gc/z/zAddress.cpp` (L78–168): `ZGlobalsPointers::set_good_masks`, `initialize`, and phase flip masks.
  - `src/hotspot/share/gc/z/zAddress.inline.hpp` (L320–390, L432–463, L552–813): `is_valid` alignment check (`value & 0x7`), `zaddress` vs `zaddress_unsafe`, `ZPointer::uncolor`, `ZAddress::color`, `load_good`, `mark_good`, `store_good`.
  - `src/hotspot/cpu/x86/gc/z/zAddress_x86.inline.hpp` (L29–37), `zBarrierSetAssembler_x86.cpp` (L1028–1119, L1338–1385), `z_x86_64.ad` (L37–83): x86 `shrq`+`ja` speculative barrier and slow-path oop reload.
  - `src/hotspot/cpu/aarch64/gc/z/zAddress_aarch64.cpp` (L41–109), `zAddress_aarch64.inline.hpp` (L29–35): `DEFAULT_MAX_ADDRESS_BIT = 46`, `msync`/`mmap` probing, complemented remap bits.
  - `src/hotspot/share/gc/z/zBarrier.hpp` (L31–85), `zBarrier.inline.hpp` (L41–292): Shift constraint (`<= 3` bits difference), `assert_transition_monotonicity`, `self_heal` CAS loop, and `remap_generation` double-remap-bad resolution.
  - `src/hotspot/share/gc/z/zForwardingEntry.hpp` (L38–80), `zForwarding.inline.hpp` (L43–57, L207–293), `zRelocate.cpp` (L355–417): 45-bit `to_offset` + 18-bit `from_index` packing, `OrderAccess::release()` before forwarding insertion, `load_acquire` on read.
  - `src/hotspot/share/gc/z/zJNICritical.cpp` (L31–181) and `zUncoloredRoot.hpp` (L32–84): `_count` blocking state machine and external-color root barriers.
- **MMTk Core** (`mmtk/mmtk-core` @ `d154f4f0dcca27439b920165ce5c948ca18aef24`):
  - `src/policy/immix/block.rs` (L19–127, L401–508, L560–643): `Block::LOG_BYTES = 15`, `BlockState` `u8` encoding, `Block::sweep`, `Block::has_holes` straddle-line skip.
  - `src/policy/immix/line.rs` (L18–89, L259–279): `Line::LOG_BYTES = 8`, `MAX_MARK_STATE = 127`, `RCArray` wide dead-line checks.
  - `src/policy/immix/defrag.rs` (L44–238): `establish_defrag_spill_threshold` reverse bucket selection, `DEFRAG_LINE_REUSE_RATIO = 0.99`.
  - `src/policy/immix/immixspace.rs` (L179–201, L375–412, L634–640, L891–1060): `pin_object`, `side_metadata_specs`, `trace_object_with_opportunistic_copy` in-place pinning/exhaustion fallback.
  - `src/plan/lxr/{mod.rs, barrier.rs, global.rs, mature_evac.rs}`: Coalesced field `UNLOG_BITS` barrier, `u128` zero-skip, `ProcessModBufSATB` dual-use `decs`, `RemSetEntry` reuse epoch, `LXR::new` in-header forwarding assertion (`global.rs:427-431`).
  - `src/util/object_forwarding.rs` (L8–145): 2-bit `0b00/0b10/0b11` `SeqCst` forwarding state machine and `#579` rollback check.
- **Peer-Reviewed Papers:**
  - Tene, Iyengar, Wolf, *C4: The Continuously Concurrent Compacting Collector*, ISMM 2011 (`DOI: 10.1145/1993478.1993491`).
  - Yang & Wrigstad, *Deep Dive into ZGC: A Modern Garbage Collector in OpenJDK*, ACM TOPLAS 2022 (`DOI: 10.1145/3538532`).
  - Blackburn & McKinley, *Immix: A Mark-Region Garbage Collector with Space Efficiency, Fast Collection, and Mutator Performance*, PLDI 2008 (`DOI: 10.1145/1375581.1375586`).
  - Zhao, Blackburn, McKinley, *Low-Latency, High-Throughput Garbage Collection*, PLDI 2022 (`DOI: 10.1145/3519939.3523440`).
  - Gammie, Hosking, Engelhardt, *Relaxing Safely: Verified On-the-Fly Garbage Collection for x86-TSO*, PLDI 2015 (`DOI: 10.1145/2737924.2738006`).
- **Self-Contained Executable Micro-Probe (`python3`):**

```bash
python3 - <<'PY'
REMAPPED = {"00": (0x1000, 13), "01": (0x2000, 14), "10": (0x4000, 15), "11": (0x8000, 16)}

def color_x86(addr: int, remap_tag: str, store_bits: int = 0x0550) -> int:
    bit, shift = REMAPPED[remap_tag]
    return (addr << shift) | bit | store_bits

def shr_x86_64(val: int, shift: int) -> tuple[int, int, int]:
    val64 = val & ((1 << 64) - 1)
    cf = (val64 >> (shift - 1)) & 1 if shift > 0 else 0
    res = val64 >> shift
    zf = 1 if res == 0 else 0
    return res, cf, zf

def ja_taken(cf: int, zf: int) -> bool:
    return cf == 0 and zf == 0

heap_addr = 0x0000400000001008
good_matches, bad_catches = 0, 0
for phase_tag, (_, phase_shift) in REMAPPED.items():
    for ptr_tag in REMAPPED:
        zp = color_x86(heap_addr, ptr_tag)
        res, cf, zf = shr_x86_64(zp, phase_shift)
        slow = ja_taken(cf, zf)
        if phase_tag == ptr_tag:
            assert not slow and cf == 1 and zf == 0 and res == heap_addr
            good_matches += 1
        else:
            assert slow and res != heap_addr
            bad_catches += 1
        if phase_tag == "10":
            print(f"phase={phase_tag}(shr {phase_shift}) ptr={ptr_tag} zptr=0x{zp:016x} -> res=0x{res:012x} CF={cf} ZF={zf} slow={slow}")

res_null, cf_null, zf_null = shr_x86_64(0, 16)
assert not ja_taken(cf_null, zf_null) and zf_null == 1
print(f"null: res=0x{res_null:x} CF={cf_null} ZF={zf_null} slow={ja_taken(cf_null, zf_null)}")
print(f"matrix: fast_path_exact={good_matches}/4 slow_path_catches={bad_catches}/12")

bad_align = 0x0000400000001004
zp_mis = color_x86(bad_align, "00")
res_b, cf_b, zf_b = shr_x86_64(zp_mis, REMAPPED["11"][1])
assert not ja_taken(cf_b, zf_b) and cf_b == 1
print(f"misaligned bypass: zptr=0x{zp_mis:016x} shr16 CF={cf_b} ZF={zf_b} slow={ja_taken(cf_b, zf_b)} res=0x{res_b:012x}")

def has_holes_lxr(dead_lines: list[bool]) -> bool:
    found_free = False
    free_lines = 0
    for i, dead in enumerate(dead_lines):
        if dead:
            if i == 0 or found_free:
                free_lines += 1
            else:
                found_free = True
            if free_lines > 0:
                return True
        else:
            free_lines = 0
            found_free = False
    return False

a = [False] * 128; a[1] = True
b = [False] * 128; b[1] = b[2] = True
c = [False] * 128; c[0] = True
assert not has_holes_lxr(a) and has_holes_lxr(b) and has_holes_lxr(c)
print(f"lxr has_holes: single_gap={has_holes_lxr(a)} double_gap={has_holes_lxr(b)} line0_gap={has_holes_lxr(c)}")
PY
```

Recorded execution output (`2026-11-19`):

```text
phase=10(shr 15) ptr=00 zptr=0x0800000002011550 -> res=0x100000000402 CF=0 ZF=0 slow=True
phase=10(shr 15) ptr=01 zptr=0x1000000004022550 -> res=0x200000000804 CF=0 ZF=0 slow=True
phase=10(shr 15) ptr=10 zptr=0x2000000008044550 -> res=0x400000001008 CF=1 ZF=0 slow=False
phase=10(shr 15) ptr=11 zptr=0x4000000010088550 -> res=0x800000002011 CF=0 ZF=0 slow=True
null: res=0x0 CF=0 ZF=1 slow=False
matrix: fast_path_exact=4/4 slow_path_catches=12/12
misaligned bypass: zptr=0x0800000002009550 shr16 CF=1 ZF=0 slow=False res=0x080000000200
lxr has_holes: single_gap=False double_gap=True line0_gap=True
```

## Revalidation

To verify whether these findings hold against newer revisions of `openjdk/jdk` or `mmtk/mmtk-core`:

1. **Generational ZGC bit layout and forwarding-table limit check:** Fetch `src/hotspot/share/gc/z/zAddress.hpp`, `zForwardingEntry.hpp`, and `zBarrier.inline.hpp` at target `<rev>` and verify `ZPointerRemappedShift`, `ZPointerLoadShiftTable`, `ZForwardingEntry::field_to_offset` width (`45` bits), and `ZBarrier::self_heal` monotonicity checks remain unchanged:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/openjdk/jdk/<rev>/src/hotspot/share/gc/z/zAddress.hpp" | grep -E "ZPointer(Reserved|Remembered|Marked|Remapped)Shift|ZPointerLoadShiftTable"
   curl -sSL "https://raw.githubusercontent.com/openjdk/jdk/<rev>/src/hotspot/share/gc/z/zForwardingEntry.hpp" | grep "ZBitField"
   ```
2. **MMTk Immix/LXR geometry and straddle-hole check:** Fetch `src/policy/immix/{block.rs, line.rs}` and `src/plan/lxr/{barrier.rs, global.rs}` at target `<rev>` and verify `Block::LOG_BYTES`, `Line::LOG_BYTES`, `Block::has_holes`, and `LOCAL_FORWARDING_BITS_SPEC.is_in_header()`:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/mmtk/mmtk-core/<rev>/src/policy/immix/line.rs" | grep -E "LOG_BYTES|MAX_MARK_STATE"
   curl -sSL "https://raw.githubusercontent.com/mmtk/mmtk-core/<rev>/src/plan/lxr/global.rs" | grep -A4 "LOCAL_FORWARDING_BITS_SPEC.is_in_header"
   ```
3. **Bit-math & hole-accounting invariants:** Re-run the inline Python micro-probe in `## Evidence` (checking `fast_path_exact=4/4`, `slow_path_catches=12/12`, misaligned bypass detection, and `lxr has_holes` outcomes) whenever `ZPointerRemappedShift` or `ZPointerLoadShiftTable` shifts change.
