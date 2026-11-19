# RowHammer, RowPress, DRAM Disturbance Physics, and Software Fault Isolation

## Summary

DRAM memory isolation assumes that reading or activating one physical row does not alter stored charge in unaddressed rows. Two distinct read-disturbance mechanisms violate this assumption in scaled commodity DRAM: (1) **RowHammer** (activation-count disturbance, where repeated wordline toggles accelerate charge leakage in nearby victim rows) and (2) **RowPress** (open-row duration disturbance, where keeping an aggressor row open for an extended `t_AggON` window reduces the activation count required to induce flips by one to two orders of magnitude).

In-DRAM Target Row Refresh (TRR) heuristics and linear SECDED Error-Correcting Codes (ECC) do not provide deterministic security guarantees: bounded sampler-based TRR fails against non-uniform or multi-sided access patterns (`TRRespass`, `Blacksmith`) and distance-2 coupling (`Half-Double`), while extended Hamming `(72, 64)` SECDED silently miscorrects `73.07%` of weight-3 bit-error patterns. Principled defenses therefore combine bounded row-open timing (`t_AggON` caps paired with scaled activation-tracking thresholds such as `PARA`/`Graphene`/`RFM`), spatial guard-row isolation (`ZebRAM`), or cryptographic memory integrity (`CSI:Rowhammer`).

## Applicability

This report relates the physical disturbance characterizations, memory-controller simulators, and software/cryptographic isolation architectures listed in `REPORT.json`:

- **Physical disturbance mechanisms and TRR limits:** Kim et al. (ISCA 2014) establish RowHammer; `vusec/trrespass` (`7ea523a4149daf1f1c4d8b099c2b3584f973d086`) and `comsec-group/blacksmith` (`60bae8e591e39859252dbe6049d536bcb2fb5656`) characterize in-DRAM TRR sampler limitations; `CMU-SAFARI/RowPress` (`5b6f1502594e9ea7a1557b98b5544c096a30eec5`, `arXiv:2306.17061`) characterizes RowPress across 164 real DDR4 chips and evaluates adapted mitigations.
- **Controller-level mitigation models:** `CMU-SAFARI/ramulator2` (`7bead6cb7c4b03e095c6d4769ae3181a8e0bf6da`) provides reference controller plugins for refresh-based and tracking-based defenses (`PARA`, `Graphene`, `TWiCe`, `Hydra`, `RRS`, `AQUA`, `RFM`, vendor TRR models, and closed-cap row policies).
- **OS/software and cryptographic defenses:** `vusec/zebram` (`05d5427e069b35afc1117ef00450b36f2634f063`) implements row-level spatial isolation in Linux/KVM; `CSI:Rowhammer` (IEEE S&P 2023) replaces linear SECDED guarantees with cryptographic MAC integrity; `ECCploit`, `RAMBleed`, `Half-Double`, and `Flip Feng Shui` define the threat boundaries those defenses must cover.

Findings apply to commodity DDR3/DDR4/DDR5 and LPDDR memory subsystems on x86-64 and ARM servers/clients. Quantitative mitigation configurations from `CMU-SAFARI/RowPress` reflect DDR4-3200 (`DDR4_8Gb_x8`, `0.625 ns` clock period) evaluated in cycle-accurate simulation; exact `HC_first` and `t_AggON` thresholds vary across DRAM vendors, die revisions, and temperatures.

## Findings

### 1. Physical Disturbance Taxonomy and Security Impact Classes

Basis: normative + documentation + derived

DRAM read-disturbance vulnerabilities and their architectural impacts organize into three high-level parent categories:

| Parent Category | Physical / Architectural Mechanism | Representative Studies | System Isolation Consequence |
| :--- | :--- | :--- | :--- |
| Activation-Count Disturbance (RowHammer & Multi-Row Variants) | Repeated `ACT`/`PRE` wordline voltage transitions capacitively couple charge out of neighboring cell capacitors faster than the refresh interval (`t_REFI` / `t_REFW`); distance-2 energy accumulation (`Half-Double`) extends coupling beyond immediate neighbors. | RowHammer (ISCA 2014), TRRespass (IEEE S&P 2020), Blacksmith (IEEE S&P 2022), Half-Double (USENIX Security 2022) | Breaks physical memory integrity across security domains; overwhelms finite-capacity in-DRAM TRR samplers via multi-sided or frequency-domain non-uniform activation schedules. |
| Open-Row Duration Disturbance (RowPress) | Holding an aggressor wordline actively asserted (`t_AggON`) for extended periods induces steady-state leakage in adjacent rows, reducing required activations by 1–2 orders of magnitude (down to a single activation in extreme regimes) and disturbing a distinct cell population with different temperature sensitivity than RowHammer. | RowPress (ISCA 2023, `arXiv:2306.17061`, 164 DDR4 chips across 3 major vendors) | Invalidates pure activation-count mitigations and open-page memory-controller policies that keep rows open across sequential hits; requires bounding maximum `t_AggON`. |
| Integrity, Confidentiality & ECC Boundary Failures | Data-dependent charge coupling leaks neighbor cell states without modifying victim memory (`RAMBleed`); deterministic physical page placement targets page tables or cryptographic state (`Flip Feng Shui`); multi-bit flips exceed linear SECDED distance (`ECCploit`). | Flip Feng Shui (USENIX Security 2016), ECCploit (IEEE S&P 2019), RAMBleed (IEEE S&P 2020) | Converts physical DRAM disturbance into both integrity compromise (privilege/key-corrupting faults) and confidentiality side channels, even on ECC-equipped hosts. |

### 2. Memory-Controller Defenses and RowPress Adaptation

Basis: source + documentation

In-DRAM TRR implementations rely on undocumented, finite-entry activation trackers and periodic opportunistic refreshes during `REF` commands, making them non-compositional under adversarial scheduling. Hardware-controller defenses modeled in `CMU-SAFARI/ramulator2` (`src/ramulator/controller/CMakeLists.txt`) formalize deterministic or probabilistically bounded alternatives:

- **Probabilistic & Counter-Based Refresh:** `PARA` (`plugin/impl/para.cpp`), `Graphene` (`plugin/impl/graphene.cpp`, Misra-Gries frequent-item tracking), `TWiCe` (`plugin/impl/twice.cpp`), `Hydra` (`plugin/impl/hydra.cpp`), and JEDEC Refresh Management `RFM` (`plugin/impl/rfm_manager.cpp`).
- **Row Remapping / Quarantine:** `RRS` (`plugin/impl/rrs.cpp`) and `AQUA` (`plugin/impl/aqua.cpp`), which physically relocate frequently activated rows to isolate neighbors.
- **RowPress Co-Mitigation (`CMU-SAFARI/RowPress`):** Because RowPress lowers the effective activation threshold as `t_AggON` increases, `CMU-SAFARI/RowPress` adapts existing trackers via two coupled controls verified in `mitigation/configs/`:
  1. **Bounded open-row policy:** Enforcing `close_after_nticks` (e.g., `1017` ticks at `period: 0.625 ns` = `~636 ns` in `Graphene419OpenUntil636.yaml`, compared to `36 ns` in `PARA1000OpenUntil36.yaml` and `Graphene1000OpenUntil36.yaml`), matching `rowpolicy/impl/closed_cap.cpp` in Ramulator 2.0.
  2. **Scaled activation thresholds:** Tightening refresh triggers for the worst-case bounded `t_AggON` (e.g., scaling the target disturbance threshold from `1000` at `36 ns` down to `419` at `636 ns`, configured in `Graphene419OpenUntil636.yaml` as `no_table_entries: 4858`, `activation_threshold: 139`, `reset_period: 32000000` ns; or `PARA` `probability_threshold: 0.034` at threshold `1000` in `PARA1000OpenUntil36.yaml`).

### 3. Software/OS Spatial Isolation (`ZebRAM`) and Cryptographic Integrity (`CSI:Rowhammer`)

Basis: source + normative + derived

When commodity memory controllers cannot guarantee hardware disturbance immunity, system-level isolation relies on two complementary software/architectural invariants:

- **Spatial Row Isolation (`ZebRAM`, `vusec/zebram`):** Reserves contiguous DRAM regions at boot (`kernel.patch`: `alloc_bootmem_low_pages` allocating `reserved_mem_zebra` / `reserved_mem_zebra_2`) and partitions physical DRAM rows in an alternating ("zebra") pattern of **safe rows** (holding live guest/OS data) separated by **unsafe guard rows**. To avoid losing half of DRAM capacity, guard rows are repurposed as compressed, software-integrity-checked swap space, absorbing disturbance flips before they reach live data rows.
- **Cryptographic Integrity (`CSI:Rowhammer`, IEEE S&P 2023):** Replaces non-cryptographic SECDED parity with a low-latency cryptographic Message Authentication Code (MAC) over memory blocks plus fault-handling traps. Unlike linear error-correcting codes, any arbitrary multi-bit disturbance fault triggers integrity verification failure with overwhelming probability (`1 - 2^-k` for `k`-bit tag), preventing silent miscorrection and fault-based privilege or cryptographic state corruption.

### 4. Execution Verification: Linear SECDED Miscorrection Boundary & Guard-Row Geometry

Basis: execution + derived

A self-contained Python coding-theory and geometry probe verified two fundamental defensive boundaries:

1. **Extended Hamming `(72, 64)` SECDED Multi-Bit Boundary:** Constructing a standard 8-bit SECDED parity-check matrix (`72` distinct columns with overall parity bit = `1` and non-zero 7-bit Hamming syndromes):
   - **Weight-1 errors:** `72 / 72` (`100.0%`) map to unique odd-parity syndromes (fully correctable).
   - **Weight-2 errors:** `2,556 / 2,556` (`100.0%`) map to non-zero even-parity syndromes (fully detectable, uncorrectable).
   - **Weight-3 errors:** `43,580 / 59,640` (`73.07%`) alias a valid single-bit error column (`0` zero-syndrome collisions because odd weight preserves odd overall parity), causing the ECC decoder to **silently miscorrect** a fourth bit and return corrupted data without raising a machine-check exception.
2. **Spatial Guard-Row Striping Overhead:** For physical blast radius `r`, deterministic isolation requires `r` guard rows between adjacent safe rows, yielding usable direct-mapped fraction `1 / (r + 1)`:
   - For standard adjacent-row coupling (`r = 1`), safe fraction is `50.00%` (`50.00%` guard rows, reclaimed as integrity-checked swap in `ZebRAM`).
   - For distance-2 coupling (`r = 2`, as in `Half-Double`), safe fraction drops to `33.33%` (`66.67%` guard rows), demonstrating why single-row zebra striping does not isolate distance-2 disturbance without widening guard bands or adding controller refresh guarantees.

## Boundaries

- **not examined:** Physical silicon characterization on live DDR5/LPDDR5 DIMMs with JEDEC Per-Row Activation Counting (PRAC) hardware enabled; findings on PRAC/RFM rely on controller-model architecture rather than live hardware measurements.
- **not examined:** Cross-architecture DRAM address-mapping reverse-engineering functions beyond noting that `TRRespass` (`drama`) and `Blacksmith` (`DRAMAddr.cpp`) depend on CPU-specific physical-to-bank/row XOR functions.
- **unknown:** Exact proprietary internal row-remapping tables, post-package repair (PPR) layouts, and undocumented on-die ECC + TRR interactions inside closed-source commercial DDR5 dies.
- **known not to apply:** Linear SECDED ECC does not prevent silent data corruption when disturbance induces three or more bit flips within a single 64-bit codeword (`73.07%` silent miscorrection rate in standard `(72, 64)` SECDED), and single-row guard striping (`r = 1`) does not isolate distance-2 (`Half-Double`) disturbance.
- **unsupported:** Pure activation-count hardware mitigations without a bounded row-open policy (`t_AggON` cap) do not bound RowPress read disturbance.

## Evidence

- **RowPress (`CMU-SAFARI/RowPress` @ `5b6f1502594e9ea7a1557b98b5544c096a30eec5`, `doi:10.48550/arXiv.2306.17061`):**
  - `arXiv:2306.17061v5` abstract and `README.md`: characterization of 164 real DDR4 chips from three major manufacturers; 1–2 orders of magnitude reduction in activation threshold under extended `t_AggON`.
  - `mitigation/configs/PARA1000OpenUntil36.yaml` and `mitigation/configs/Graphene419OpenUntil636.yaml`: `period: 0.625`, `close_after_nticks: 1017` (`~636 ns`), `PARA` (`probability_threshold: 0.034`), and `Graphene` (`no_table_entries: 4858`, `activation_threshold: 139`, `reset_period: 32000000`).
- **Ramulator 2.0 (`CMU-SAFARI/ramulator2` @ `7bead6cb7c4b03e095c6d4769ae3181a8e0bf6da`):**
  - `src/ramulator/controller/CMakeLists.txt` (lines 1–55): verified controller mitigation and policy implementations (`rowpolicy/impl/closed_cap.cpp`, `plugin/impl/{rfm_manager,para,twice,graphene,hydra,rrs,aqua,samsung_trr,hynix_trr,ideal_trr}.cpp`).
- **ZebRAM (`vusec/zebram` @ `05d5427e069b35afc1117ef00450b36f2634f063`):**
  - Top-level tree (`diff_qemu`, `kernel.patch`, `lkm_modules_for_guest`) and `kernel.patch` (lines 1–50): boot-time reservation of contiguous zebra memory pools (`alloc_bootmem_low_pages`, `reserved_mem_zebra`, `reserved_mem_zebra_2`).
- **TRRespass (`vusec/trrespass` @ `7ea523a4149daf1f1c4d8b099c2b3584f973d086`, `doi:10.1109/SP40000.2020.00090`)** and **Blacksmith (`comsec-group/blacksmith` @ `60bae8e591e39859252dbe6049d536bcb2fb5656`, `doi:10.1109/SP46214.2022.9833772`):**
  - `README.md` in both repositories documenting DDR4 TRR bypass conditions across commodity DIMMs (e.g., 40 tested DIMMs in Blacksmith) and dependence on memory-controller physical-to-DRAM address mapping.
- **Foundational literature:** RowHammer (`doi:10.1145/2678373.2665726`), Flip Feng Shui (USENIX Security 2016), ECCploit (`doi:10.1109/SP.2019.00089`), RAMBleed (`doi:10.1109/SP40000.2020.00020`), Half-Double (USENIX Security 2022), CSI:Rowhammer (`doi:10.1109/SP46215.2023.10179390`).
- **Execution probe (observed `2026-11-19`, Python 3):** Exhaustive combinatorial check over extended Hamming `(72, 64)` SECDED (`72/72` single-bit unique, `2556/2556` double-bit detected, `43580/59640 = 73.07%` triple-bit silent miscorrection, `0` zero-syndrome weight-3 aliases) and guard-row striping ratios (`0.5000` for `r = 1`, `0.3333` for `r = 2`).

## Revalidation

1. **Controller mitigation drift check:** Compare `HEAD` of `CMU-SAFARI/ramulator2` (`src/ramulator/controller/CMakeLists.txt`) against commit `7bead6cb7c4b03e095c6d4769ae3181a8e0bf6da` to check for updated DDR5/PRAC or RowPress-specific mitigation plugins.
2. **Row-open policy audit:** For any target memory controller or BIOS/firmware configuration, check whether maximum row-open timeout (`t_AggON` / `closed_cap`) is bounded alongside JEDEC `RFM`/`PRAC` activation thresholds; an unbounded open-page policy invalidates pure activation-count mitigation assumptions.
3. **ECC and isolation recheck:** Re-run the exhaustive `(72, 64)` SECDED syndrome check for any alternative linear ECC code (e.g., chipkill/Reed-Solomon or wider Hsiao codes) before relying on ECC for adversarial fault integrity, and verify physical blast radius `r` before deploying row-striping isolation.
