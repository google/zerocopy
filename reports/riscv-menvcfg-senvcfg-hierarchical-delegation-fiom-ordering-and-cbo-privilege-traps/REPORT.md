# RISC-V menvcfg and senvcfg Hierarchical Delegation: FIOM Ordering and CBO Privilege Traps

## Summary

The RISC-V Privileged Architecture (v1.12 and v1.13+) controls execution-environment capabilities across `M`, `S`/`HS`, `U`, `VS`, and `VU` modes via three hierarchical CSRs: `menvcfg` (`0x30A`, high half `menvcfgh` `0x31A`), `henvcfg` (`0x60A`, high half `henvcfgh` `0x61A`), and `senvcfg` (`0x10A`). Four structural invariants govern formal verification, firmware, and OS-kernel testing:

1. **Dual Lattice Polarity (`AND` vs. `OR`)**: Feature enables (`CBZE`, `CBCFE`, `CBIE`, `PBMTE`, `ADUE`, `STCE`, `SSE`, `DTE`) compose via **conjunction/meet** (`∧` / `min`) down the privilege stack, whereas `FIOM` (bit 0) composes via **disjunction/join** (`∨`): `FIOM_active(U) = menvcfg.FIOM ∨ senvcfg.FIOM` and `FIOM_active(VU) = menvcfg.FIOM ∨ henvcfg.FIOM ∨ senvcfg.FIOM`. Applying `&` instead of `|` corrupts I/O-to-memory ordering on `14/40` combinations whenever M-mode leaves `menvcfg.FIOM = 0`.
2. **Non-Commutative `Zicbom`/`Zicboz` Trap-Cause Priority and Flush Downgrade**: An unset `menvcfg` control (for `priv != M`) or unset `senvcfg` control (in non-virtualized `U`) *always* raises **Illegal Instruction (`cause = 2`)**—even in `VS`/`VU`—whereas `henvcfg == 0` (or `senvcfg == 0` in `VU`) with `menvcfg != 0` raises **Virtual Instruction (`cause = 22`)**. For `cbo.inval`, `CBIE = 0b01` in any governing CSR downgrades invalidation to `cbo.flush`. Downstream PTW/PMP/PMA faults on any `CBO.*` always report a **Store/AMO fault** (`cause = 7, 15, 23`) with the *unaligned* `rs1` address in `xtval`.
3. **Read-Masking Asymmetry**: `henvcfg.{STCE, PBMTE, ADUE, DTE, SSE}` and `senvcfg.SSE` read as zero when `menvcfg`'s bit is `0` (and `senvcfg.SSE` also when `V=1 ∧ henvcfg.SSE=0`), whereas `senvcfg.{FIOM, CBIE, CBCFE, CBZE, LPE, PMM}` store and read back `1` even when `menvcfg == 0`. Write-then-read probing of `senvcfg` in S-mode is therefore **unsound** for detecting M-mode CMO delegation.
4. **`FIOM` Writability & Emulator Fidelity Hazards**: Whenever S-mode exists and `satp.MODE` is not read-only zero (`Bare` only)—i.e., `Sv32`/`Sv39`/`Sv48`/`Sv57` is supported—`FIOM` **must** be writable. Cross-checking Sail and Spike against QEMU TCG exposes concrete bugs: QEMU accepts reserved `CBIE = 0b10` without WARL legalization (diverging on `75/320` tuples), lacks read-zeroing on `senvcfg.SSE`, and turns `cbo.inval`/`cbo.flush` into cache no-ops that mask non-coherent memory corruption.

## Applicability

These findings cover **RISC-V Privileged Architecture v1.12** (defining `menvcfg`, `senvcfg`, `henvcfg`, `FIOM`, `PBMTE`, `CBZE`, `CBCFE`, `CBIE`) and **v1.13+ ratified extensions** in `riscv/riscv-isa-manual` (`c05f1725f25526dd8463bac6ca75cfcfbee17d05`):

- **v1.12 Baseline**: `FIOM` (0), `CBIE` (5:4), `CBCFE` (6), `CBZE` (7), `PBMTE` (62, RV64 `Svpbmt`), plus `henvcfg` virtualization counterparts.
- **v1.13 & Ratified Additions**: `LPE` (2, `Zicfilp`), `SSE` (3, `Zicfiss`), `UKTE` (8 in `senvcfg`, `Svukte`), `PMM` (33:32, `Smnpm`/`Ssnpm`, RV64), `DTE` (59, `Ssdbltrp`), `CDE` (60 in `menvcfg`, `Smcdeleg`), `ADUE` (61, `Svadu`), and `STCE` (63, `Sstc`).
- **RV64 vs. RV32**: On RV64, all three CSRs are 64-bit (`menvcfgh`/`henvcfgh` do not exist). On RV32, `menvcfgh` (`0x31A`) and `henvcfgh` (`0x61A`) alias bits `63:32`, while `senvcfg` is 32-bit with no high-half CSR.

The six subjects in `REPORT.json` map specification (`riscv-isa-manual`, `sail-riscv`), simulators (`riscv-isa-sim`/Spike, `qemu/qemu` TCG), firmware (`opensbi`), and OS kernel probing (`linux`). Related reference-model methodology appears in `reference-model-bisimulation-executable-semantics-and-differential-oracles`.

## Findings

### 1. CSR Existence, Bit Layout, and Read-Modulation Partition

`Basis: normative + source`

#### Existence and `Smstateen` Access Gating

- **`menvcfg` (`0x30A`) / `menvcfgh` (`0x31A`)**: Mandatory when **U-mode is supported** (`norm:menvcfg_mandatory_u_mode`, `machine.adoc:2316-2320`); non-existent if U-mode is absent (`machine.adoc:2319-2320`). `menvcfgh` is mandatory on RV32 with S-mode and absent on RV64 (`machine.adoc:2314,2318`).
- **`senvcfg` (`0x10A`)**: Exists whenever **S-mode is supported** (`sys_regs.sail:619`). RISC-V defines **no `vsenvcfg` CSR** (`sys_regs.sail:637`): when `V=1` (`VS`-mode), accesses to `0x10A` touch `senvcfg` directly, requiring HS-mode hypervisors to context-switch `senvcfg` per vCPU.
- **`henvcfg` (`0x60A`) / `henvcfgh` (`0x61A`)**: Exists when **H-extension is supported** (`sys_regs.sail:621-622`, `hypervisor.adoc:837-841`).
- **`Smstateen` / `Ssstateen` (`mstateen0.ENVCFG`, `hstateen0.ENVCFG`, Bit 62)**: Per `smstateen.adoc:203, 224, 275-277`, `mstateen0[62] == 0` raises Illegal Instruction on CSR access to `henvcfg`/`henvcfgh`/`senvcfg` below M-mode, and `hstateen0[62] == 0` (when `mstateen0[62] == 1` and `V=1`) raises Virtual Instruction on `senvcfg` access (`spike/csrs.cc:1879-1889, 1903-1910`; `qemu/csr.c:3495, 3555`). `Smstateen` gates *CSR accesses*, leaving execution-time reading of cached `*envcfg` bits governed by `smstateen.adoc:100-104`.

#### Bit Layout and Read-Modulation Partition

From `machine.adoc:2136-2314`, `supervisor.adoc:790-955`, `hypervisor.adoc:676-841`, and `sail-riscv/model/core/sys_regs.sail:446-506`:

| Bit(s) | Field | Extension | `menvcfg` | `henvcfg` | `senvcfg` | Composition | Read-Only-Zero When Ancestor Is `0`? |
|---|---|---|---|---|---|---|---|
| `0` | `FIOM` | Priv v1.12 | Yes | Yes | Yes | **Disjunction (`∨`)** | No (independent storage) |
| `2` | `LPE` | `Zicfilp` | Yes | Yes | Yes | Target-mode (`S/VS/U`) | No |
| `3` | `SSE` | `Zicfiss` | Yes | Yes | Yes | **Conjunction (`∧`)** | **Yes**: `henvcfg.SSE` & `senvcfg.SSE` masked (`sys_regs.sail:598-606`) |
| `5:4` | `CBIE` | `Zicbom` | Yes | Yes | Yes | **Meet (`00 < 01 < 11`)** | No (`norm:cbxe_unaffected`, `cmo.adoc:634-635`) |
| `6` | `CBCFE` | `Zicbom` | Yes | Yes | Yes | **Conjunction (`∧`)** | No (`cmo.adoc:634-635`) |
| `7` | `CBZE` | `Zicboz` | Yes | Yes | Yes | **Conjunction (`∧`)** | No (`cmo.adoc:634-635`) |
| `8` | `UKTE` | `Svukte` | WPRI | WPRI | Yes | Direct (`U` timing) | N/A |
| `33:32` | `PMM` | `Smnpm`/`Ssnpm` | RV64 | RV64 | RV64 | Target-mode (`S/VS/U`) | No (`0b01` reserved) |
| `59` | `DTE` | `Ssdbltrp` | Yes | Yes | WPRI | **Conjunction (`∧`)** | Yes (`read_henvcfg` / `spike` masks by `menvcfg.DTE`) |
| `60` | `CDE` | `Smcdeleg` | Yes | WPRI | WPRI | Direct (`S/HS`) | N/A |
| `61` | `ADUE` | `Svadu` | Yes | Yes | WPRI | **Conjunction (`∧`)** | **Yes**: `henvcfg.ADUE` R0 if `menvcfg.ADUE == 0` |
| `62` | `PBMTE` | `Svpbmt` | RV64 | RV64 | WPRI | **Conjunction (`∧`)** | **Yes**: `henvcfg.PBMTE` R0 if `menvcfg.PBMTE == 0` |
| `63` | `STCE` | `Sstc` | Yes | Yes | WPRI | **Conjunction (`∧`)** | **Yes**: `henvcfg.STCE` R0 if `menvcfg.STCE == 0` |

Sail's `read_henvcfg()` and `read_senvcfg()` (`sys_regs.sail:592-606`) and Spike (`csrs.h:542`, `csrs.cc:1892-1895`) dynamically mask modulated fields without destroying backing bits if an ancestor toggles `1 → 0 → 1`. Notably, `cmo.adoc:634-635` prohibits cross-CSR read/write modulation for `CBIE`/`CBCFE`/`CBZE`: S-mode can set `senvcfg.CBZE = 1` and read back `1` even when `menvcfg.CBZE = 0` causes U-mode `cbo.zero` to trap.

### 2. Necessary-and-Sufficient Conditions for `Zicbom` / `Zicboz` Execution vs. Trapping vs. Flush-Downgrade

`Basis: normative + source + derived`

From `cmo.adoc:524-635`, `sys_regs.sail:1300-1317`, `zicbom_insts.sail:36-70, 125-145`, and `zicboz_insts.sail:24-30`, let `m`, `h`, `s` denote the field in `menvcfg`, `henvcfg`, `senvcfg`, and `ext_S` indicate S-mode presence:

1. **`cbo.clean`, `cbo.flush` (`CBCFE`), and `cbo.zero` (`CBZE`)** (`feature_enabled_for_priv`, `sys_regs.sail:1306-1317`):
   - **Illegal Instruction (`cause = 2`)** iff `((priv != M) ∧ (m == 0)) ∨ ((priv == U) ∧ ext_S ∧ (s == 0))`.
   - **Virtual Instruction (`cause = 22`)** iff NOT Illegal AND `((priv == VS) ∧ (h == 0)) ∨ ((priv == VU) ∧ ((h == 0) ∨ (s == 0)))`.
   - **Execute** iff: `M: true`; `S/HS: m == 1`; `U: (m == 1) ∧ (¬ext_S ∨ s == 1)`; `VS: (m == 1) ∧ (h == 1)`; `VU: (m == 1) ∧ (h == 1) ∧ (s == 1)`.
2. **`cbo.inval` (`CBIE ∈ {0b00, 0b01, 0b11}`; `0b10` reserved)** (`cmo.adoc:532-558`, `zicbom_insts.sail:49-70`):
   - **Illegal Instruction (`cause = 2`)** iff `((priv != M) ∧ (m == 0b00)) ∨ ((priv == U) ∧ ext_S ∧ (s == 0b00))`.
   - **Virtual Instruction (`cause = 22`)** iff NOT Illegal AND `((priv == VS) ∧ (h == 0b00)) ∨ ((priv == VU) ∧ ((h == 0b00) ∨ (s == 0b00)))`.
   - **Execute as Flush (`cbo.flush`)** iff neither trap holds AND `0b01` appears in any governing register (`m` for `priv != M`; `s` for `U`/`VU`; `h` for `VS`/`VU`).
   - **Execute as Raw Invalidate** iff all governing registers equal `0b11`.

#### Trap-Routing Priority Across Virtualized Modes (`VS` / `VU`)

| Mode (`V`) | `menvcfg` | `henvcfg` | `senvcfg` | `cbo.{zero,clean,flush}` | `cbo.inval` | Trap Target (Standard Delegation) |
|---|---|---|---|---|---|---|
| `M` (`V=0`) | `0` / `0b00` | Ignored | Ignored | Executes | Executes (`INVAL`) | N/A |
| `S/HS` (`V=0`) | `0` / `0b00` | Ignored | Ignored | **`Illegal (2)`** | **`Illegal (2)`** | M-mode (unless `medeleg[2]=1`) |
| `U` (`V=0`, `ext_S`) | `1` / `0b11` | Ignored | `0` / `0b00` | **`Illegal (2)`** | **`Illegal (2)`** | HS-mode if `medeleg[2]=1` |
| `VS` (`V=1`) | `0` / `0b00` | `1` / `0b11` | Ignored | **`Illegal (2)`** | **`Illegal (2)`** | **M-mode** (NOT `hedeleg[22]`!) |
| `VS` (`V=1`) | `1` / `0b11` | `0` / `0b00` | Ignored | **`Virtual (22)`** | **`Virtual (22)`** | **HS-mode** (if `medeleg[22]=1`) |
| `VU` (`V=1`) | `1` / `0b11` | `1` / `0b11` | `0` / `0b00` | **`Virtual (22)`** | **`Virtual (22)`** | **HS-mode** (`senvcfg` failure virtualized!) |
| `VU` (`V=1`) | `1` / `0b11` | `0b01` (or `s=0b01`) | `0b11` | Executes | **Downgraded `FLUSH`** | N/A (prevents exposing stale RAM, `cmo.adoc:564-576`) |

#### Post-Gate Translation, Permission, Shadow-Stack, and `xtval` Rules

- **Permission Check vs. Fault Type**: `cbo.clean`/`flush`/`inval` pass whenever **Read OR Write** is permitted (`qemu/op_helper.c:244-267`, `sail/vmem_pte.sail:260`), whereas `cbo.zero` requires **Write** (`op_helper.c:195-198`). Yet **every** PTW, PMP, or PMA failure on all four `CBO.*` instructions raises a **Store/AMO fault (`cause = 7, 15, 23`)** (`vmem_ptw.sail:117-120`, `op_helper.c:261-266`) with `xtval` set to the **unaligned `rs1` effective address** (`zicbom_insts.sail:94, 110-112`, `zicboz_insts.sail:55-68`).
- **Shadow-Stack Pages (`Zicfiss`)**: Any `CBO.*` targeting a shadow-stack page (`pte.xwr = 0b010`) raises **Store/AMO Access Fault (`cause = 7`)** (`vmem_pte.sail:215-218`, `spike_mmu.cc:789-791`).

### 3. `FIOM` (Bit 0) Disjunctive Delegation, `FENCE`/`AMO` Rules, and `satp` Hardwiring

`Basis: normative + source + derived`

When `is_fiom_active()` holds (`machine.adoc:2141-2170`, `supervisor.adoc:823-855`, `hypervisor.adoc:699-725`):
- `FENCE` bits expand dynamically: `PI → PI | PR`, `PO → PO | PW`, `SI → SI | SR`, `SO → SO | SW`.
- Atomic (`AMO`/`LR`/`SC`) instructions touching I/O regions with `.aq` and/or `.rl` are ordered as accessing **both I/O and main memory**.

Unlike CMO enables, `FIOM` composes by **disjunction (`∨`)** (`sail-riscv/model/core/sys_regs.sail:651-659`):
`S → menvcfg[FIOM]`, `U → menvcfg[FIOM] | senvcfg[FIOM]`, `VS → menvcfg[FIOM] | henvcfg[FIOM]`, `VU → menvcfg[FIOM] | henvcfg[FIOM] | senvcfg[FIOM]`.
Because hypervisors use `FIOM = 1` when emulating I/O device rings inside guest-visible main memory (`supervisor.adoc:858-888`), `henvcfg.FIOM = 1` must strengthen guest `FENCE` instructions even when `menvcfg.FIOM = 0` and `senvcfg.FIOM = 0`. Across all `40` `(priv, m, h, s)` tuples, using `&` instead of `|` fails on **`14` cases (`35%`)**.

**Normative `FIOM` Writability Mandate**: `norm:menvcfg_fiom_rdonly0_ok` (`machine.adoc:2153-2154`) and `norm:senvcfg_fiom_acc` (`supervisor.adoc:837-839`) allow `FIOM` to be read-only zero *only* if S-mode is unsupported or `satp.MODE` is always `Bare`. Contrapositively, whenever S-mode supports **any** paged translation mode (`Sv32`, `Sv39`, `Sv48`, or `Sv57`), `FIOM` in `menvcfg` and `senvcfg` **must** be writable (`sys_regs.sail:84-86`; `spike/csr_init.cc:239-242, 358`).

### 4. `PBMTE` and `ADUE` Two-Level Translation Delegation and Synchronization Rules

`Basis: normative + source`

`PBMTE` (bit 62, `Svpbmt`, RV64-only per `svpbmt.adoc:4-9`) and `ADUE` (bit 61, `Svadu`, `svadu.adoc:6-9`) govern hardware page-table walks (`satp`, `vsatp`, `hgatp`) and are therefore `WPRI` in `senvcfg` (`supervisor.adoc:794-821`):

1. **`PBMTE` (`Svpbmt`)** (`machine.adoc:2178-2187`, `hypervisor.adoc:727-733`, `svpbmt.adoc:43-51, 123-137`, `sail/vmem_pte.sail:112-114`, `sail/vmem.sail:247-249, 747-749`):
   - `menvcfg.PBMTE == 0`: `henvcfg.PBMTE` is read-only zero and `Svpbmt` is disabled across `satp`, `hgatp`, and `vsatp`; any non-zero `pte[62:61]` triggers a Page Fault (`12/13/15`) or Guest-Page Fault (`20/21/23`).
   - `menvcfg.PBMTE == 1 ∧ henvcfg.PBMTE == 0`: `satp` and `hgatp` permit `PBMT ∈ {1 (NC), 2 (IO)}`, while `vsatp` treats non-zero `PBMT` as reserved (VS-level Page Fault).
   - Both `1`: G-level `PBMT` (`hgatp`) overrides PMA to yield intermediate attributes, which non-zero VS-level `PBMT` (`vsatp`) overrides (`vmem.sail:747-749`); `PBMT = 3` and non-leaf `PBMT != 0` always fault.
2. **`ADUE` (`Svadu` vs. `Svade`)** (`machine.adoc:2194-2216`, `hypervisor.adoc:734-743`, `svadu.adoc:6-14`):
   - `ADUE == 1` (`menvcfg.ADUE` for S/G-level; `menvcfg.ADUE ∧ henvcfg.ADUE` for VS-level) enables hardware PTE A/D updates; `0` falls back to `Svade` (raising Page/Guest-Page Fault when A/D updates are needed).
   - OpenSBI (`lib/sbi/sbi_hart.c:136, 150-168`) **clears `ENVCFG_ADUE` whenever `Svade` is present**, matching the SBI FWFT reset default (`0`), while enabling `CBZE`, `CBCFE`, `CBIE_INV`, `PBMTE`, `STCE`, and `CDE` on harts with `priv_version >= 1.12`.
3. **Mandatory TLB Synchronization**:
   - Changing `menvcfg.{PBMTE, ADUE}` requires `SFENCE.VMA x0, x0` (`machine.adoc:2188-2211`) and `HFENCE.GVMA x0, x0` (which synchronizes both G-level and VS-level caches without `HFENCE.VVMA`, `hypervisor.adoc:2113-2116`).
   - Changing `henvcfg.{PBMTE, ADUE}` requires `HFENCE.VVMA x0, x0` for the active `VMID`, or bracketing the update inside `vsatp = 0 ... vsatp = new` (`hypervisor.adoc:2118-2129`). By contrast, `senvcfg.PMM` takes effect immediately without a fence (`supervisor.adoc:928-930`), except when `XLEN - PMLEN` becomes narrower than `hgatp`'s GPA width with `vsatp.MODE = Bare` (`hypervisor.adoc:2156-2166`).

### 5. Emulator, Simulator, and Firmware CSR-Stub Fidelity Hazards

`Basis: source + derived`

1. **QEMU Reserved `CBIE = 0b10` WARL Acceptance Bug** (`qemu/target/riscv/tcg/csr.c:3398-3400, 3511-3513, 3580-3582`; `op_helper.c:165-177, 278-285`):
   - Unlike Sail (`sys_regs.sail:515-524`) and Spike (`csrs.cc:1243-1244`, clamping `0b10 → 0b00`), QEMU masks `MENVCFG_CBIE` (`0b11 << 4`) without checking `CBIE != 2`. Writing `0b10` persists `0b10` and bypasses `!get_field(env->*envcfg, MENVCFG_CBIE)`, executing `cbo.inval` without trapping on **`75` of `320` (`23.4%`)** `(priv, m, h, s)` tuples where Sail/Spike trap.
2. **QEMU Missing Dynamic `senvcfg.SSE` Read-Zeroing and Destructive `henvcfg` Clear** (`csr.c:3448, 3490-3502, 3535-3540, 3631`):
   - `read_senvcfg` returns raw `env->senvcfg` even if M/HS-mode clears `menvcfg.SSE` or `henvcfg.SSE` after `write_senvcfg`, whereas Spike (`csrs.cc:1892-1895`) and Sail (`sys_regs.sail:604-606`) read-mask `SSE`. Meanwhile, `write_menvcfg` (`csr.c:3448`) calls `write_henvcfg`, destructively wiping `env->henvcfg` fields instead of masking on read (`csrs.h:542`, `sys_regs.sail:592-599`).
3. **Cache-No-Op Collapse & `FIOM` Unmodeled Execution** (`op_helper.c:275, 284`, `trans_rvi.c.inc:969-974`, `csr.c:3394, 3507, 3575`):
   - QEMU and Sail skip cache-line simulation (`cbo.inval` vs `cbo.flush` collapse to no-ops), QEMU emits unconditional `TCG_MO_ALL | TCG_BAR_SC` barriers in `trans_fence` without querying `FIOM`, and QEMU leaves `FIOM` writable even on Bare-only `satp` (`csr.c:3394, 3507`). Only Spike's `MMU.clean_inval` (`cbo_inval.h:6-11`) distinguishes `CBIE = 0b01` flush-downgrade from `0b11` dirty-line discard.
4. **QEMU `CONFIG_USER_ONLY` `menvcfg` Bypass** (`op_helper.c:155-163`): Checks only `env->senvcfg`, masking guest firmware failures that forget `menvcfg`.
5. **M-Mode Firmware / Linux DTB Desynchronization**: OpenSBI (`sbi_hart.c:132-172`) programs `menvcfg` only when `priv_version >= 1.12`, while Linux (`cpufeature.c:93-155, 564-566`) enables `Zicbom`/`Zicboz` via `riscv_xlinuxenvcfg_exts` solely from ISA-string + power-of-two DTB `cbom-block-size`/`cboz-block-size` validation. OS boot harnesses with `menvcfg = 0` trap on U-mode `cbo.*` despite valid DTB properties and `senvcfg = -1`.

## Boundaries

- **known not to apply**: Write-then-read probing of `senvcfg.{FIOM, CBIE, CBCFE, CBZE}` in S-mode is **known not to apply** as a check for `menvcfg` or `henvcfg` enablement (`cmo.adoc:634-635`). Likewise, `Zicbop` prefetch hints (`cbo.prefetch.{i,r,w}`) are **known not to apply** to `*envcfg` illegal/virtual trap gating (`cmo.adoc:308-309`: prefetch hints never raise illegal-instruction or virtual-instruction traps).
- **unsupported**: `senvcfg` leaves `PBMTE`, `ADUE`, `STCE`, `CDE`, and `DTE` **unsupported** (`WPRI`). RV32 leaves `Svpbmt` (`PBMTE`) and `PMM` (`Smnpm`/`Ssnpm`) **unsupported** (read-only zero, `machine.adoc:2270`, `hypervisor.adoc:797`, `svpbmt.adoc:4-9`), and harts without U-mode leave `menvcfg`/`menvcfgh` **unsupported** (`machine.adoc:2319-2320`).
- **not examined**: Microarchitectural cache-controller timing side channels between `cbo.inval` and `cbo.flush`, CHERI capability-bounds interaction with misaligned `rs1` in `Zicbom` (open `TODO` at `zicbom_insts.sail:84-86`), and vendor-custom CSRs (e.g., T-Head `mxstatus`/`sxstatus`) were **not examined**.
- **unknown**: Whether an arbitrary compliant hardware core handles reserved `CBIE = 0b10` or `PMM = 0b01` writes via permission-clearing (`Xenvcfg_ClearPermissions`, matching Spike) or ignoring (`Xenvcfg_Ignore`) is **unknown** without per-core empirical probing (`sys_regs.sail:515-524`).

## Evidence

### Primary Specifications and Source Coordinates

| Subject | Coordinate / Revision | Observed Content |
|---|---|---|
| **RISC-V ISA Manual** | `riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05` | `src/priv/machine.adoc:2128-2320`; `supervisor.adoc:782-960`; `hypervisor.adoc:667-842, 2113-2169`; `smstateen.adoc:198-284`; `svpbmt.adoc:1-137`; `svadu.adoc:1-14`; `src/unpriv/cmo.adoc:304-310, 518-635` |
| **Sail RISC-V** | `riscv/sail-riscv` @ `71dc9c251a82eb3ecf6f271b02b0161ea8345dfd` | `model/core/sys_regs.sail:84-86, 445-662, 1300-1317`; `Zicbom/zicbom_insts.sail:36-145`; `Zicboz/zicboz_insts.sail:24-96`; `sys/vmem_pte.sail:91-118, 215-218`; `sys/vmem_ptw.sail:117-120`; `sys/vmem.sail:247-249, 747-749` |
| **Spike** | `riscv-software-src/riscv-isa-sim` @ `e53c8ccf3448ae459877ed3236cb39b2a1d493bf` | `riscv/csrs.h:526-550`; `riscv/csrs.cc:1235-1262, 1874-1915`; `riscv/csr_init.cc:239-259, 358-382`; `riscv/decode_macros.h:335-349`; `riscv/insns/cbo_*.h`; `riscv/mmu.cc:618-635, 756-791` |
| **QEMU TCG** | `qemu/qemu` @ `225d5bd4691fc75e32536428fc9a23ddb8e30784` | `target/riscv/tcg/csr.c:3381-3665`; `op_helper.c:145-285`; `cpu_helper.c:1215-1224, 1317-1410`; `insn_trans/trans_rvi.c.inc:969-974` |
| **OpenSBI** | `riscv-software-src/opensbi` @ `61f1973bd50338b36c52dc34006f76d464ca4f34` | `lib/sbi/sbi_hart.c:132-178`; `include/sbi/riscv_encoding.h:229-251, 890-891` |
| **Linux RISC-V** | `torvalds/linux` @ `5f22fb20497f4983094131f00a734362300d22d2` | `arch/riscv/kernel/cpufeature.c:93-155, 564-575` |

### Standalone Derived Truth-Table Verification (`verify_envcfg_matrix.py`)

`Basis: derived` — exhaustive Python 3 verification across `320` `(priv, m, h, s)` `CBIE` tuples and `40` `FIOM` tuples:

```python
#!/usr/bin/env python3
from itertools import product

PRIVS = ("M", "S", "U", "VS", "VU")
CBIE_VALS = (0b00, 0b01, 0b10, 0b11)

def sail_legalize_cbie(val: int, old: int = 0, mode: str = "clear") -> int:
    return (0b00 if mode == "clear" else old) if val == 0b10 else val

def spike_legalize_cbie(val: int) -> int:
    return 0b00 if val == 0b10 else val

def eval_cbo_inval_spec_sail(priv: str, m: int, h: int, s: int, ext_s: bool = True) -> str:
    if (priv != "M" and m == 0b00) or (priv == "U" and ext_s and s == 0b00):
        return "ILLEGAL"
    if (priv == "VS" and h == 0b00) or (priv == "VU" and (h == 0b00 or s == 0b00)):
        return "VIRTUAL"
    if ((priv != "M" and m == 0b01) or (priv == "U" and ext_s and s == 0b01)
            or (priv == "VS" and h == 0b01) or (priv == "VU" and (h == 0b01 or s == 0b01))):
        return "FLUSH"
    return "INVAL"

def eval_cbo_inval_spike(priv: str, m_raw: int, h_raw: int, s_raw: int, ext_s: bool = True) -> str:
    m, h, s = spike_legalize_cbie(m_raw), spike_legalize_cbie(h_raw), spike_legalize_cbie(s_raw)
    v = priv in ("VS", "VU")
    bp = {"M": "M", "S": "S", "U": "U", "VS": "S", "VU": "U"}[priv]
    if (bp != "M" and m == 0) or (ext_s and bp == "U" and not v and s == 0):
        return "ILLEGAL"
    if v and (h == 0 or (bp == "U" and s == 0)):
        return "VIRTUAL"
    if (bp != "M" and m == 1) or (not v and bp == "U" and ext_s and s == 1) or (v and (h == 1 or (bp == "U" and s == 1))):
        return "FLUSH"
    return "INVAL"

def eval_cbo_inval_qemu_sys(priv: str, m: int, h: int, s: int) -> str:
    v, p = priv in ("VS", "VU"), {"M": 3, "S": 1, "U": 0, "VS": 1, "VU": 0}[priv]
    if p < 3 and not m:
        return "ILLEGAL"
    if v and (((p <= 1) and not h) or ((p < 1) and not s)):
        return "VIRTUAL"
    if p < 1 and not s:
        return "ILLEGAL"
    return "EXEC_NOP"

def eval_fiom_active(priv: str, m: int, h: int, s: int) -> bool:
    return {"M": False, "S": bool(m), "U": bool(m | s), "VS": bool(m | h), "VU": bool(m | h | s)}[priv]

def main() -> None:
    legal_vals = (0b00, 0b01, 0b11)
    for priv, m, h, s in product(PRIVS, legal_vals, legal_vals, legal_vals):
        sp = eval_cbo_inval_spec_sail(priv, m, h, s)
        assert sp == eval_cbo_inval_spike(priv, m, h, s)
        q = eval_cbo_inval_qemu_sys(priv, m, h, s)
        assert (q == sp) if q in ("ILLEGAL", "VIRTUAL") else (sp in ("FLUSH", "INVAL"))
    print("LEGAL_CBIE_TUPLES=135 (100% Spec==Sail==Spike agreement; QEMU trap classification exact)")

    divs = sum(
        (eval_cbo_inval_spec_sail(p, sail_legalize_cbie(m), sail_legalize_cbie(h), sail_legalize_cbie(s)) in ("ILLEGAL", "VIRTUAL"))
        != (eval_cbo_inval_qemu_sys(p, m, h, s) in ("ILLEGAL", "VIRTUAL"))
        for p, m, h, s in product(PRIVS, CBIE_VALS, CBIE_VALS, CBIE_VALS)
    )
    print(f"ALL_CBIE_TUPLES=320 RESERVED_0b10_TRAP_DIVERGENCES_IN_QEMU={divs}")

    fiom_diffs = sum(
        eval_fiom_active(p, m, h, s) != (False if p == "M" else (bool(m) if p == "S" else (bool(m & s) if p == "U" else (bool(m & h) if p == "VS" else bool(m & h & s)))))
        for p, m, h, s in product(PRIVS, (0, 1), (0, 1), (0, 1))
    )
    print(f"FIOM_TUPLES=40 DISJUNCTIVE_VS_CONJUNCTIVE_DIFFS={fiom_diffs}")

if __name__ == "__main__":
    main()
```

Observed output (`2026-11-20`, Python 3):

```text
LEGAL_CBIE_TUPLES=135 (100% Spec==Sail==Spike agreement; QEMU trap classification exact)
ALL_CBIE_TUPLES=320 RESERVED_0b10_TRAP_DIVERGENCES_IN_QEMU=75
FIOM_TUPLES=40 DISJUNCTIVE_VS_CONJUNCTIVE_DIFFS=14
```

## Revalidation

1. **Check Sail `*envcfg` Legalization, Read Masking, and `CBIE` Rules**:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/riscv/sail-riscv/<NEW_SHA>/model/core/sys_regs.sail \
     | grep -n -E "legalize_[msh]envcfg|read_[sh]envcfg|is_fiom_active|feature_enabled_for_priv"
   curl -fsSL https://raw.githubusercontent.com/riscv/sail-riscv/<NEW_SHA>/model/extensions/Zicbom/zicbom_insts.sail \
     | sed -n '36,75p;125,145p'
   ```
2. **Check QEMU `CBIE = 0b10` & `read_senvcfg` Masking**:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/qemu/qemu/<NEW_SHA>/target/riscv/tcg/csr.c \
     | sed -n '3390,3645p' | grep -n -E "CBIE|SENVCFG_SSE|read_senvcfg"
   ```
3. **Check OpenSBI `menvcfg` Defaults**:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/riscv-software-src/opensbi/<NEW_SHA>/lib/sbi/sbi_hart.c \
     | grep -n -C 8 "CSR_MENVCFG"
   ```
4. **Re-run the Matrix Check**: Save `verify_envcfg_matrix.py` from `## Evidence` to `/tmp/verify_envcfg_matrix.py` and run `python3 /tmp/verify_envcfg_matrix.py`.
