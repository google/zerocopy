# Exokernel LibOS Multiplexing, MPK/PKU Domains, and VT-x User Rings

## Summary

Separating hardware **protection** (enforced by a minimal kernel or hardware domain boundary) from resource **management** (delegated to untrusted library operating systems, dataplane stacks, and intra-process compartments) defines a shared design arc spanning MIT's Aegis/Xok Exokernel, modern kernel-bypass dataplanes (Arrakis, IX, Demikernel, Unikraft), intra-address-space memory protection keys (Intel MPK/PKU and ARMv8.9 `FEAT_S1POE`), hardware-virtualized Ring-0 user spaces (Dune), and share-nothing multikernels (Barrelfish).

Across these architectures, three load-bearing invariants determine both performance and security soundness:
1. **Secure-Binding & Revocation Separation**: Exokernels decouple bind-time authorization checks from zero-trap datapath enforcement (Aegis software-TLB capabilities, Xok hardware PTE checks, XN UDF templates, downloaded ASH/DPF packet filters, and Arrakis SR-IOV NIC queues), while requiring **visible revocation** and bounded-time **abort protocols** when physical frames or device queues must be reclaimed.
2. **Thread-Local Domain Registers Cannot Self-Police Syscalls or Signal Frames**: Intel MPK (`PKRU`) switches data-plane permissions in ~11–26 cycles with zero TLB shootdowns, and binary scanners (`ERIM` `isBenignWRPKRU`, `Hodor` debug watchpoints, `Cerberus` monitor vetting) prevent unvetted `WRPKRU`/`XRSTOR` gadgets—including mid-instruction immediate-operand jumps—from executing in untrusted text. However, because `PKRU` is a data-only per-thread register, kernel memory-mapping syscalls (`pkey_mprotect`, `mmap(MAP_FIXED)`), kernel `FOLL_FORCE` / async worker side doors (`/proc/self/mem`, `io_uring`), and user-writable signal frames (`rt_sigreturn` executing `XRSTOR` over attacker-controlled `ucontext_t`) bypass pure binary scanning unless mediated by kernel/seccomp enforcement (`Jenny`, published at USENIX Security 2022).
3. **Instruction-Fetch Overlays (`ARMv8.9 FEAT_S1POE`) and Virtualized Ring-0 (`Dune`) Close Expressiveness Gaps at Different Latencies**: Whereas x86 `PKRU` governs only `AD`/`WD` (unable to revoke execute permissions or enforce execute-only code pages), ARMv8.9 `POR_EL0` stores 16 4-bit `{R, W, X}` overlays intersected with Stage-1 PTEs without TLB maintenance. Conversely, `Dune` uses Intel VT-x (`DUNE_ENTER`) to place a libOS at guest Ring 0 inside an EPT-isolated Linux process, exchanging `WRPKRU`'s 15-cycle switch for ~100–150-cycle guest `SYSCALL` transitions in return for full hardware page-table switching (`CR3`), direct exception delivery (`IDT`), and kernel-free `CPL 3` sandboxing.

## Applicability

This report documents architectural invariants, source-level mechanisms, and threat boundaries across the concrete upstream systems and published specifications pinned in `REPORT.json`:

- **MIT Exokernel Lineage**: Aegis/ExOS (Engler, Kaashoek, O'Toole, SOSP 1995 `doi:10.1145/224056.224076`) and Xok/XN (Kaashoek et al., SOSP 1997 `doi:10.1145/268998.266644`).
- **Modern Kernel-Bypass & Modular LibOSes**: Arrakis (Peter et al., OSDI 2014 / ACM TOCS 2016 `doi:10.1145/2812806`), IX (`ix-project/ix` at `550bf28a4ddd5fafcec707a14acd502712a10dae`, OSDI 2014), Microsoft Demikernel (`microsoft/demikernel` at `42655abdffbdfc7283e30f913b153c7b39c9ee90`, SOSP 2021 `doi:10.1145/3477132.3483569`), and Unikraft (`unikraft/unikraft` at `7814c9dc529092edc4cfd52f4fffe54205eaca70`, EuroSys 2021 `doi:10.1145/3447786.3456248`).
- **Intel MPK/PKU Isolation Systems & Security Analyses**: ERIM (`vahldiek/erim` at `7232f4762c5ff51035116f9664ec6e7af3b236af`, USENIX Security 2019 / `arXiv:1801.06822`), Hodor (Hedayati et al., USENIX ATC 2019), Jenny (`isec-tugraz/Jenny` at `39bb0c696ce3c178e9593b7dbc034b2447ba2d00`, USENIX Security 2022), Connor et al. *PKU Pitfalls* (USENIX Security 2020), and Cerberus (Voulimeneas et al., EuroSys 2022 `doi:10.1145/3492321.3519560`).
- **ARMv8.9 Permission Overlays**: `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`), specifically `arch/arm64/include/asm/por.h` and `arch/arm64/include/asm/sysreg.h`.
- **VT-x Ring-0 User Processes & Multikernels**: Dune (`project-dune/dune` at `af3e3bdddb81d80e900ef1e1fa9df6b54cdfcae9`, OSDI 2012) and Barrelfish (`BarrelfishOS/barrelfish` at `06a9f54721a8d96874a8939d8973178a562c342f`, SOSP 2009 `doi:10.1145/1629575.1629579`).

Note on bibliographic accuracy: the Jenny PKU syscall/signal system (`isec-tugraz/Jenny`) appeared at **USENIX Security 2022** (Schrammel et al., pp. 936–952), whereas Cerberus (*You Shall Not (by)Pass!*) appeared at **EuroSys 2022** (`doi:10.1145/3492321.3519560`). Probe B executes concrete byte-scanning, mid-instruction ROP control-flow simulation, and ARMv8.9 bitwise overlay intersections in Python 3.13.15 without invoking bare-metal x86 PKU or ARMv8.9 silicon directly.

## Findings

### 1. Exokernel Multiplexing Invariants vs. Modern Kernel-Bypass LibOS Dataplanes

Basis: normative + source (`doi:10.1145/224056.224076`, `doi:10.1145/268998.266644`, `doi:10.1145/2812806`, `ix-project/ix`, `microsoft/demikernel`, `unikraft/unikraft`).

The MIT Exokernel thesis (Engler, Kaashoek, O'Toole, SOSP 1995) argues that monolithic OS abstractions (virtual memory regions, file descriptors, TCP sockets, page cache replacement) conflate *multiplexing protection* with *management policy*. Instead of hiding hardware behind high-level abstractions, an exokernel exports raw physical names (physical page frames, TLB slots, disk sectors, NIC ring buffers, CPU time slices) to untrusted user-level **Library Operating Systems (libOSes)** through three architectural primitives:

1. **Secure Bindings**: Authorization checks occur once at bind time, decoupling permission verification from high-frequency access-time checks:
   - In **Aegis** (MIPS R2000/R3000 software-managed TLB), a libOS binds a virtual-to-physical translation into a software capability-checked TLB cache (`STLB`), allowing subsequent TLB misses to refill directly from kernel-verified mappings without invoking full POSIX VM faults.
   - In **Xok** (x86 hardware-walked page tables; Kaashoek et al., SOSP 1997), untrusted libOSes inspect their own hardware page tables directly in read-only memory and batch privileged PTE updates through capability-checked system calls, eliminating shadow VM state duplication.
   - In **XN** (Xok's disk multiplexing layer), untrusted deterministic functions (**UDFs** — Untrusted Deterministic Functions) supply metadata layout interpretation for disk blocks so Xok can verify block-ownership invariants without embedding ext2/FFS/database format logic inside the kernel.
2. **Downloaded Code (ASH & DPF)**: Rather than waking a user scheduler on every incoming packet interrupt, Aegis/Xok download **Application-Specific Safe Handlers (ASH)** and **Dynamic Packet Filters (DPF)** into kernel context, compiling packet demultiplexing into native machine code that terminates directly into zero-copy user-mapped DMA rings.
3. **Visible Revocation and Abort Protocols**: Because physical frames and NIC/CPU slices are scarce, the exokernel issues an asynchronous **visible revocation** upcall asking a libOS to release $N$ frames (allowing the libOS to pick cold pages per its own LRU/working-set heuristic and write dirty buffers cleanly). If the libOS stalls past a bounded deadline, the kernel executes an **abort protocol** that forcibly breaks the secure binding, replaces reclaimed slots with guarded/repossessed stubs in the libOS's exception table, and notifies the libOS of the involuntary loss.

#### Cross-System Evolution: Exokernels to Kernel-Bypass & Unikernel Dataplanes

| Architecture | Isolation Boundary | Control Plane vs. Data Plane | Zero-Copy I/O ABI | Multi-Tenant Hardware Multiplexing | Management Delegation Scope |
|---|---|---|---|---|---|
| **Aegis / Xok** (SOSP 1995 / 1997) | Ring-0 exokernel + per-libOS virtual address space | Kernel validates secure bindings & DPF/ASH; libOS owns page tables & FS | DMA rings + STLB/PTE capability batching | Fine-grained CPU time slices, physical frames, XN disk extents | Page replacement, IPC, TCP/IP, filesystem metadata (via UDF) |
| **Arrakis** (OSDI 2014 / TOCS 2016) | Hypervisor-like control-plane OS + IOMMU + SR-IOV | OS configures NIC/storage Virtual Functions (VFs) once; zero OS on I/O path | Hardware NIC SR-IOV RX/TX rings & VIC directly in user DMA memory | Hardware SR-IOV queues + hardware packet steering filters | User libOS runs lwIP / POSIX emulation directly over hardware queues |
| **IX** (`ix-project/ix`, OSDI 2014) | VT-x Dune guest Ring 0 (dataplane) vs. Ring 3 (app) + EPT | Control plane allocates cores/NIC queues; IX dataplane polls DPDK-like rings | Batch system calls (`dp/core/init.c`, mbuf rings) with bounded run-to-completion | Per-core dedicated RSS NIC queues; EPT memory partitioning | Elastic run-to-completion networking + adaptive batching (`lwIP` in Ring 0) |
| **Demikernel** (`microsoft/demikernel`, SOSP 2021) | Process boundary or hardware RDMA/VF isolation | Standardized PDPIX queue-token ABI (`demi_qtoken_t`) decoupled from kernel/DPDK/RDMA libOS | Packed scatter-gather (`demi_sgarray_t`, max 20 `demi_sgaseg_t` segments in `include/demi/types.h`) | Depends on backend (`catnip` DPDK VF, `catpowder` raw sockets, `catloop`, RDMA) | Unified async `push`/`pop`/`wait` queue futures across heterogeneous OS-bypass NICs |
| **Unikraft** (`unikraft/unikraft`, EuroSys 2021) | Hypervisor / VMM (KVM/Xen/Firecracker) around single VM | Single Ring-0 address space; no intra-VM user/kernel trap (`lib/ukalloc`) | Direct virtio/VF rings inside single address space | Inter-VM via VMM (zero intra-unikernel isolation by default) | Compile-time composition of `ukalloc`, `uknetdev`, `lwip` micro-libraries |

In `microsoft/demikernel` (`include/demi/types.h:35-69`), `demi_sgarray_t` standardizes zero-copy I/O across kernel-bypass backends via a fixed-size packed array (`DEMI_SGARRAY_MAXSIZE = 20`) of `demi_sgaseg_t { void *sgaseg_md; void *data_buf_ptr; uint32_t data_len_bytes; }` alongside opaque 64-bit `demi_qtoken_t` completion tokens—preserving Exokernel-style explicit memory ownership (`sgaseg_md` pins underlying DPDK mbuf/RDMA MR lifetimes) without exposing raw hardware descriptor formats to applications.

### 2. Intra-Address-Space Fault Isolation with Intel MPK/PKU: Binary Scanning and Call-Gate Invariants

Basis: source + execution + normative (`vahldiek/erim` at `7232f4762c5ff51035116f9664ec6e7af3b236af`, USENIX Security 2019, USENIX ATC 2019 Hodor, EuroSys 2022 Cerberus, and Probe B).

When a single address space hosts both an untrusted application/libOS and sensitive dataplane or cryptographic state (such as IX's Ring-0/Ring-3 split or a zero-copy buffer manager protecting descriptor metadata), hardware `CR3` address-space switching incurs ~100–800+ cycles plus TLB/PCID pressure, and `mprotect` triggers cross-core TLB shootdown IPIs. Intel **Memory Protection Keys for Userspace (PKU / MPK)** assigns a 4-bit protection key (`0..15`) inside bits `[62:59]` of every leaf page-table entry (`pkey_mprotect`) and exposes a per-hardware-thread 32-bit user register **`PKRU`**:
- For each key $k \in \{0, \dots, 15\}$, bit `2*k` (`AD_k`) disables all user data reads and writes, and bit `2*k + 1` (`WD_k`) disables writes while allowing reads.
- Crucially, `WRPKRU` (`0f 01 ef`, requiring `ECX == 0` and `EDX == 0`, else `#GP`) and `RDPKRU` (`0f 01 ee`) are **unprivileged Ring-3 instructions** completing in ~11–26 cycles with zero kernel trap and zero TLB flush.

Because untrusted Ring-3 code can execute any `WRPKRU` present in executable memory—including unaligned mid-instruction byte sequences—MPK isolation systems depend on two strict invariants: **code-page immutability (W^X)** and **executable-text vetting**.

#### 2.1 ERIM's Self-Healing `__wrpkrucheck` Call Gate and Byte Scanner (`vahldiek/erim`)

Inspecting `vahldiek/erim` (`src/erim/erim_api_inlined.h:35-145`, `src/erim/pkeys.h:35-69`, `src/erim/erim.c:17-120`) exposes the exact low-level mechanics required to prevent untrusted ROP/JOP gadgets from hijacking a legitimate `WRPKRU`:
- **Domain Assignments (`erim_api_inlined.h:42-80`)**:
  - `ERIM_TRUSTED_PKRU = 0x55555550` (`0b...0101_0000`: domains 0 and 1 unlocked `[AD=0, WD=0]`, domains `2..15` `[WD=1, AD=0]`).
  - `ERIM_PKRU_ISOTRS_UNTRUSTED_CI = 0x5555555C` (trusted domain 1 has `AD_1=1, WD_1=1`: neither read nor write by untrusted code).
  - `ERIM_PKRU_ISOTRS_UNTRUSTED_IO = 0x55555558` (integrity-only: untrusted code may read domain 1 but `WD_1=1` blocks writes).
  - **Trusted Stack Switching (`ERIM_SWITCH_TO_ISOLATED_STACK`)**: switching domains without changing `%rsp` leaves trusted return addresses, spilled keys, and register saves on an untrusted-writable stack, allowing a second concurrent untrusted thread to overwrite a return pointer mid-call. ERIM copies 128 bytes of arguments and pivots `%rsp` to `ERIM_ISOLATED_STACK` (`11ull << 43`) before invoking trusted logic.
- **Self-Healing Exit Gate (`src/erim/pkeys.h:38-63`)**: A naive `xor %ecx,%ecx; xor %edx,%edx; mov $untrusted,%eax; wrpkru` sequence can be subverted by jumping directly to `wrpkru` with attacker-chosen `EAX = ERIM_TRUSTED_PKRU`. ERIM therefore compiles `__wrpkrucheck(ERIM_UNTRUSTED_PKRU)` as a closed, zero-memory-write verification loop:
  - GCC (`19` bytes): `31 c9 31 d2 b8 <imm32> 0f 01 ef 3d <imm32> 75 ed` (`xor %ecx,%ecx; xor %edx,%edx; mov $imm32,%eax; wrpkru; cmp $imm32,%eax; jne -19`).
  - Clang (`23` bytes): uses `0f 85 e9 ff ff ff` (`jne rel32`) checked in `isBenignWRPKRU` (`src/erim/erim.c:69-71`).
  - If an attacker jumps directly onto `0f 01 ef` with `EAX = 0x55555550` (trusted), `PKRU` briefly elevates for **two register-only instructions** (`cmp`, `jne`) that perform zero memory accesses and zero indirect jumps, immediately fails `cmp`, branches back `-19` bytes to `xor %ecx,%ecx; xor %edx,%edx; mov $0x5555555c,%eax; wrpkru`, overwrites `PKRU` with the untrusted mask, and only exits after `PKRU == untrustedPKRU`. (Note: entry gates switching *to* `ERIM_TRUSTED_PKRU` must only appear inside trusted-only code pages or immediately precede trusted non-returnable call targets vetted by CFI/static call sites, since jumping to an entry gate inside untrusted-callable code without an immediate `WRPKRU` back or trusted call target grants trusted privileges.)
- **Cross-Instruction & `XRSTOR` Scanning (`src/erim/erim.c:17-33`)**: `erim_scanMemForWRPKRUXRSTOR` scans every **byte offset** (not merely disassembled instruction boundaries!) for both `0f 01 ef` (`WRPKRU`) and `0f ae /5` (`XRSTOR`, which restores `PKRU` from memory when XSAVE component bit 9 `XFEATURE_PKRU` is set in `EAX`). Any unaligned `WRPKRU`/`XRSTOR` hidden inside immediate operands (such as `mov $0xef010f00, %eax` = `b8 00 0f 01 ef`) or branch displacements fails inspection and must be rewritten or have its containing page stripped of `PROT_EXEC`.

#### 2.2 Comparing ERIM, Hodor, and Cerberus

| System | `WRPKRU`/`XRSTOR` Prevention | Runtime Hardware Requirement | Dynamic Code (`JIT` / `dlopen`) & Multi-Thread Race Handling |
|---|---|---|---|
| **ERIM** (USENIX Sec 2019, `vahldiek/erim`) | Ahead-of-time / load-time byte scan (`erim_memScanRegion`) + binary rewriting + `__wrpkrucheck` call gates | Standard Intel MPK (`PKRU`) | Assumes W^X & static code vetting before execution; dynamic `mprotect(PROT_EXEC)` requires intercepting loader/mmap |
| **Hodor** (USENIX ATC 2019) | Places hardware instruction-breakpoint debug registers (`DR0–DR3`) on any vetted `WRPKRU` sites + ptrace/kernel trap for unvetted sites | Intel MPK + `x86` hardware debug registers (`DR0–DR3`) | Limited to **4 hardware debug-register slots per thread**; extra `WRPKRU` sites spill to page-level trap emulation; tailored to protected DPDK/SPDK dataplane libraries |
| **Cerberus** (EuroSys 2022, `doi:10.1145/3492321.3519560`) | Hybrid hardware breakpoints (for single-threaded startup sites) + non-executable (`NX`) trapping for post-fork/new pages monitored out-of-process | Intel MPK + `DR0–DR3` + out-of-process seccomp/ptrace monitor | Explicitly closes **multi-threaded TOCTOU code-modification races** (where one thread executes code while another thread `mprotect`/`mmap`s an unvetted `WRPKRU` page before the monitor updates breakpoints) |

#### 2.3 Executable Micro-Probe B: Byte-Offset `WRPKRU` Scanning, Mid-Gadget ROP Recovery, and `POR_EL0` Intersection

Basis: execution (Python 3.13.15 standard library micro-probe modeling exact byte encoding from `vahldiek/erim/src/erim/erim.c:48-75` and `torvalds/linux/arch/arm64/include/asm/por.h`).

```bash
python3 - <<'PY'
#!/usr/bin/env python3
"""Micro-probe B: ERIM WRPKRU gadget scanner, self-healing ROP simulation, and MPK vs ARMv8.9 POE matrix."""


def scan_wrpkru_xrstor(code: bytes) -> list[tuple[int, str]]:
    hits = []
    for i in range(len(code)):
        if code[i:i + 3] == b"\x0f\x01\xef":
            hits.append((i, "WRPKRU"))
        elif i + 2 < len(code) and code[i:i + 2] == b"\x0f\xae" and ((code[i + 2] >> 3) & 0x7) == 5:
            hits.append((i, "XRSTOR"))
    return hits


def is_benign_gcc_exit_gate(code: bytes, wrpkru_off: int, untrusted_pkru: int) -> bool:
    if wrpkru_off < 9 or wrpkru_off + 10 > len(code):
        return False
    w = code[wrpkru_off - 9:wrpkru_off + 10]
    expected_pkru = untrusted_pkru.to_bytes(4, "little")
    return (
        w[0:4] == b"\x31\xc9\x31\xd2"
        and w[4] == 0xb8
        and w[5:9] == expected_pkru
        and w[9:12] == b"\x0f\x01\xef"
        and w[12] == 0x3d
        and w[13:17] == expected_pkru
        and w[17:19] == b"\x75\xed"
    )


def simulate_mid_gadget_rop(untrusted_pkru: int = 0x5555555C) -> list[str]:
    eax, ecx, edx = 0x00000000, 0, 0
    pkru = untrusted_pkru
    pc = 9
    trace = []
    for step in range(12):
        if pc == 0:
            ecx, edx, pc = 0, 0, 4
            trace.append(f"step={step} pc=0..3: xor ecx,ecx; xor edx,edx")
        elif pc == 4:
            eax, pc = untrusted_pkru, 9
            trace.append(f"step={step} pc=4..8: mov eax,0x{untrusted_pkru:08x}")
        elif pc == 9:
            assert ecx == 0 and edx == 0
            pkru, pc = eax, 12
            trace.append(f"step={step} pc=9..11: WRPKRU -> pkru=0x{pkru:08x}")
        elif pc == 12:
            zf = (eax == untrusted_pkru)
            pc = 17
            trace.append(f"step={step} pc=12..16: cmp eax,0x{untrusted_pkru:08x} -> ZF={zf}")
        elif pc == 17:
            if not zf:
                pc = 0
                trace.append(f"step={step} pc=17..18: jne -19 TAKEN -> pc=0")
            else:
                trace.append(f"step={step} pc=17..18: jne -19 NOT TAKEN -> exit pc=19, pkru=0x{pkru:08x}")
                break
    assert pkru == untrusted_pkru
    return trace


def poe_intersection_matrix() -> list[tuple[str, tuple[int, int, int], tuple[int, int, int], tuple[int, int, int]]]:
    cases = [
        ("Execute-Only code page (XOM)", (1, 0, 1), (0, 0, 1)),
        ("Domain-isolated RW data",       (1, 1, 0), (1, 1, 0)),
        ("Revoked JIT W^X -> R-only",     (1, 1, 1), (1, 0, 0)),
        ("Full deny (POE_NONE)",          (1, 1, 1), (0, 0, 0)),
    ]
    return [(label, pte, por, (pte[0] & por[0], pte[1] & por[1], pte[2] & por[2])) for label, pte, por in cases]


def main() -> None:
    untrusted_pkru = 0x5555555C
    benign_gcc_gate = (
        b"\x31\xc9\x31\xd2"
        b"\xb8" + untrusted_pkru.to_bytes(4, "little") +
        b"\x0f\x01\xef"
        b"\x3d" + untrusted_pkru.to_bytes(4, "little") +
        b"\x75\xed"
    )
    assert len(benign_gcc_gate) == 19
    hits_benign = scan_wrpkru_xrstor(benign_gcc_gate)
    assert hits_benign == [(9, "WRPKRU")] and is_benign_gcc_exit_gate(benign_gcc_gate, 9, untrusted_pkru)
    print("BENIGN_GATE:", len(benign_gcc_gate), hits_benign, "vetted=True")

    inadvertent = b"\xb8\x00\x0f\x01\xef\xc3"  # mov $0xef010f00, %eax; ret
    hits_bad = scan_wrpkru_xrstor(inadvertent)
    assert hits_bad == [(2, "WRPKRU")] and not is_benign_gcc_exit_gate(inadvertent, 2, untrusted_pkru)
    print("UNALIGNED_GADGET:", hits_bad, "vetted=False")

    print("ROP_SIMULATION:")
    for line in simulate_mid_gadget_rop(untrusted_pkru):
        print(" ", line)

    print("POE_MATRIX:")
    for label, pte, por, eff in poe_intersection_matrix():
        print(f"  {label}: PTE={pte} & POR={por} => EFF={eff}")


if __name__ == "__main__":
    main()
PY
```

Observed output:

```text
BENIGN_GATE: 19 [(9, 'WRPKRU')] vetted=True
UNALIGNED_GADGET: [(2, 'WRPKRU')] vetted=False
ROP_SIMULATION:
  step=0 pc=9..11: WRPKRU -> pkru=0x00000000
  step=1 pc=12..16: cmp eax,0x5555555c -> ZF=False
  step=2 pc=17..18: jne -19 TAKEN -> pc=0
  step=3 pc=0..3: xor ecx,ecx; xor edx,edx
  step=4 pc=4..8: mov eax,0x5555555c
  step=5 pc=9..11: WRPKRU -> pkru=0x5555555c
  step=6 pc=12..16: cmp eax,0x5555555c -> ZF=True
  step=7 pc=17..18: jne -19 NOT TAKEN -> exit pc=19, pkru=0x5555555c
POE_MATRIX:
  Execute-Only code page (XOM): PTE=(1, 0, 1) & POR=(0, 0, 1) => EFF=(0, 0, 1)
  Domain-isolated RW data: PTE=(1, 1, 0) & POR=(1, 1, 0) => EFF=(1, 1, 0)
  Revoked JIT W^X -> R-only: PTE=(1, 1, 1) & POR=(1, 0, 0) => EFF=(1, 0, 0)
  Full deny (POE_NONE): PTE=(1, 1, 1) & POR=(0, 0, 0) => EFF=(0, 0, 0)
```

### 3. Syscall Confused Deputies and Signal-Frame `PKRU` Squatting (PKU Pitfalls & Jenny)

Basis: source + normative (`isec-tugraz/Jenny` at `39bb0c696ce3c178e9593b7dbc034b2447ba2d00`, USENIX Security 2022 Jenny; USENIX Security 2020 Connor et al. *PKU Pitfalls*).

User-space `WRPKRU`/`XRSTOR` scanning alone is **unsound** because the Linux kernel honors `PKRU` inconsistently across syscall confused deputies and signal delivery paths. Connor et al. (*PKU Pitfalls*, USENIX Security 2020) and Schrammel et al. (*Jenny*, USENIX Security 2022) categorize the systemic kernel/ABI bypass vectors:

| Bypass Vector | Mechanism | Why Pure `WRPKRU` Scanning Misses It | Required Kernel / Monitor Mitigation (Jenny & Descendants) |
|---|---|---|---|
| **1. Memory-Mapping & Key Reassignment Syscalls** | Untrusted compartment invokes `pkey_mprotect`, `mprotect`, `mmap(MAP_FIXED)`, `mremap`, or `shmat` to overwrite key `k` or remap a secret page with key `0` | Contains zero `WRPKRU` instructions (`syscall` opcode `0f 05` is ubiquitous in untrusted libc) | Intercept and policy-filter VM syscalls (`seccomp` / `SYS_mmap` / `Jenny` `kernel_module_syscall_hook`), forbidding key `0` overwriting over isolated ranges |
| **2. Kernel `FOLL_FORCE` & Async Worker Side Doors** | Opening `/proc/self/mem` (`lseek` + `write`/`read`), `process_vm_writev`/`readv`, `ptrace(PTRACE_POKEDATA)`, or `io_uring` `IORING_OP_WRITEV`/`READV` | Kernel `access_remote_vm` (`FOLL_FORCE`) ignores `PKRU`, and `io-wq` kernel worker threads do not enforce the submitting thread's transient untrusted `PKRU` | Block `/proc/self/mem` open/write, `process_vm_*`, `ptrace` on self-process, and scrub/validate `io_uring` buffer pointers against compartment domain bounds |
| **3. Signal-Frame `PKRU` Squatting (`rt_sigreturn`)** | Untrusted code crafts a synthetic `ucontext_t` XSAVE frame on the stack with `PKRU = 0` (`XFEATURE_PKRU` bit set) and executes `rt_sigreturn` | Kernel `rt_sigreturn` executes privileged **`XRSTOR`** directly inside Ring 0 to restore user-supplied XSAVE `PKRU`, completely bypassing user-text scanning | Kernel signal-frame binding or shadow PKRU verification (`Jenny` `0001-Add-support-for-PKRU-secure-signal-handlers.patch` storing `SS_PKEY_SHIFT` / `SS_PKEY_PREV_AD` in `sas_ss_flags` and clamping `PKRU` on `handle_signal` + `rt_sigreturn`) |
| **4. Async Signal Preemption Inside Trusted Call Gates** | An asynchronous signal (e.g., `SIGALRM`/`SIGVTALRM`) fires while a thread executes inside trusted domain with `PKRU == ERIM_TRUSTED_PKRU`; Linux delivers the handler onto an untrusted signal stack or invokes untrusted handler code with trusted registers/key | Hardware `PKRU` is not reset to untrusted automatically upon kernel->user signal upcall unless patched (`init_pkru_value` vs. `new_pkru`) | Dedicated per-domain `sigaltstack` with domain key check (`SS_PKEY_MASK` in Jenny patch `arch/x86/kernel/signal.c:663-678,729-733`) or deferring async signals across trusted call gates |
| **5. Syscall Pointer Arguments as Confused Deputies** | Untrusted domain calls `read(fd, trusted_secret_addr, len)` or `write(fd, trusted_secret_addr, len)` | Syscalls execute in Ring 0; kernel `copy_to_user` / `copy_from_user` only checks `PKRU` on architectures/kernels enforcing `PKU` in kernel user-access (`SMAP` + user `PKRU` on newer x86 CPUs), whereas async kernel subsystems, DMA, or older kernels ignore `PKRU` | Syscall filter validates `[buf, buf + len)` lies exclusively within the caller compartment's active `PKRU` domain permissions |

Inspecting `isec-tugraz/Jenny` (`code/kernel_patch_signal_handler/0001-Add-support-for-PKRU-secure-signal-handlers.patch:26-84`) reveals how deeply signal handling interacts with PKU soundness:
- Without kernel patching, Linux saves the interrupted thread's `PKRU` into the signal frame's XSAVE buffer on the user stack and resets `PKRU` to `init_pkru` (or leaves it unmodified on older kernels); worse, on `rt_sigreturn`, an untrusted signal handler can edit `uc_mcontext` XSAVE `PKRU` bytes before invoking `SYS_rt_sigreturn`.
- Jenny's patch extends `sigaltstack` flags (`SS_PKEY_MASK`, `SS_PKEY_PREV_AD`, `SS_PKEY_PREV_WD`) in `arch/x86/include/uapi/asm/signal.h:134-140` so `handle_signal` sets `new_pkru` appropriate for the target signal stack's domain key and `SYSCALL_DEFINE0(rt_sigreturn)` explicitly enforces `write_pkru(pkru | pkru_mask)` from kernel-protected `current->sas_ss_flags`, preventing user-stack `ucontext_t` tampering from restoring elevated keys.

### 4. ARMv8.9-A Permission Overlay Extension (`FEAT_S1POE` / `POR_EL0`)

Basis: source + normative (`torvalds/linux` at `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `arch/arm64/include/asm/por.h:1-35` and `arch/arm64/include/asm/sysreg.h:992-1006`).

Intel MPK suffers a major structural asymmetry for self-protecting libOSes and JIT sandboxes: `PKRU` encodes only `AD` (Access Disable = no data read/write) and `WD` (Write Disable = no data write). **MPK cannot disable instruction fetch (`X`)**, nor can it grant execute-only (`X`-only, non-readable) permissions without relying on hardware/EPT page tables. An untrusted compartment with `AD_k = 1` over a trusted domain's code page still executes ROP gadgets inside those pages unless restricted at the PTE level.

ARMv8.9-A **`FEAT_S1POE`** (Stage 1 Permission Overlay Extension, paired with `FEAT_S1PIE` Permission Indirection) removes this asymmetry in hardware:
- **Overlay Register Layout (`arch/arm64/include/asm/sysreg.h:992-1006`)**: `POR_EL0` is an unprivileged 64-bit system register holding **16 4-bit overlay entries** (`POR_ELx_BITS_PER_IDX = 4`), indexed by `POIndex` stored in the Stage-1 PTE. Each 4-bit nibble encodes explicit `{R, W, X}` permissions:
  - `POE_NONE = 0x0`, `POE_R = 0x1`, `POE_X = 0x2`, `POE_RX = 0x3`, `POE_W = 0x4`, `POE_RW = 0x5`, `POE_WX = 0x6`, `POE_RWX = 0x7`.
- **Kernel Helper Semantics (`arch/arm64/include/asm/por.h:11-31`)**: `POR_EL0_INIT = POR_ELx_PERM_PREP(0, POE_RWX)` unlocks key `0` for `R|W|X` while `por_elx_allows_read`, `por_elx_allows_write`, and `por_elx_allows_exec` extract `POR_ELx_PERM_GET(pkey, por)` and test bits `POE_R`, `POE_W`, and `POE_X`.
- **Architectural Consequences**:
  1. **Per-Domain Execute-Only Memory (XOM) & Code Domain Separation**: Setting Stage-1 PTE to `RX` and `POR_EL0[k] = POE_X` (`0x2`) strips data reads (`EFF = (0, 0, 1)` in Probe B's `POE_MATRIX`), blocking gadget harvesting/disclosure by untrusted domains in the same address space without touching page tables.
  2. **TLB-Free W^X / JIT Execution Revocation**: Transitioning an untrusted compartment away from a JIT buffer with `POR_EL0[k] = POE_R` (`0x1`) immediately disables both writes and instruction fetches across that key via `MSR POR_EL0, Xn` + `ISB` without issuing cross-core `TLBI` broadcasts.
  3. **Equivalent Binary-Vetting & Signal-Frame Surface**: Because `MSR POR_EL0, Xn` is unprivileged at EL0 (and because ARM64 instructions are fixed 32-bit aligned, eliminating x86 variable-length mid-instruction `WRPKRU` byte smuggling—though `AArch64` variable-bit-pattern immediate gadgets or arbitrary `MSR POR_EL0` sites in untrusted code still require static vetting / CFI), Linux must also preserve and sanitize `POR_EL0` across `POE_MAGIC` signal-context frames to prevent signal-return overlay squatting analogous to x86 `rt_sigreturn`.

### 5. VT-x User-Level Ring-0 Processes (Dune) and Multikernel State Replication (Barrelfish)

Basis: source + normative (`project-dune/dune` at `af3e3bdddb81d80e900ef1e1fa9df6b54cdfcae9`, `BarrelfishOS/barrelfish` at `06a9f54721a8d96874a8939d8973178a562c342f`, OSDI 2012 Dune, SOSP 2009 Barrelfish).

#### 5.1 Dune: VT-x Virtualized Ring-0 in Userspace (`project-dune/dune`)

When an application or libOS needs capabilities neither MPK nor `FEAT_S1POE` provides—such as **unlimited virtual address spaces (`CR3` switching), hardware Ring-3/Ring-0 privilege separation, user-managed page-fault handlers (`IDT`), or dirty/accessed PTE bit scanning for concurrent GC**—Dune (Belay et al., OSDI 2012) repurposes Intel VT-x hardware virtualization (`kern/dune.h`, `kern/vmx.c`, `kern/ept.c`):
- **Entering Guest Ring 0 (`kern/dune.h:16-48`)**: Opening `/dev/dune` and calling `ioctl(DUNE_ENTER, struct dune_config *)` launches `vmx_launch` (`kern/vmx.c:1887`), switching the process into **VMX non-root mode at guest CPL 0**.
- **Privileged Features Without VM Exits**: Inside guest Ring 0, the Dune libOS executes normally un-emulated privileged instructions directly on hardware:
  - Switching guest `CR3` (with VPID tagging) isolates untrusted Ring-3 guest sandboxes from the Ring-0 libOS with full PTE/TLB control;
  - Programming `MSR_LSTAR` (`vmx_init_syscall`) allows guest Ring-3 untrusted code to invoke `SYSCALL` directly into guest Ring-0 libOS interposition handlers in ~100–150 cycles **with zero VM exit and zero host-Linux transition**;
  - Installing a guest `IDT` routes hardware `#PF` page faults directly to user-space libOS handlers in ~300 cycles rather than crossing host Linux signal delivery.
- **Host Isolation via EPT & `VMCALL` (`kern/vmx.c:1954-1960`)**: The host Linux kernel restricts all guest physical memory inside **Extended Page Tables (EPT)** (`ept.c`) so guest Ring 0 cannot touch host kernel memory or unowned physical pages; legitimate Linux system calls execute via `VMCALL` hypercalls handled by `vmx_handle_syscall(vcpu)`.
- **Microarchitectural Comparison vs. MPK**:

| Dimension | Intel MPK (`WRPKRU`) | ARMv8.9 `FEAT_S1POE` (`POR_EL0`) | Dune (`VT-x` Guest Ring 0 / Ring 3) | Full Host Process (`fork`/`CR3` + IPC) |
|---|---|---|---|---|
| **Domain Switch Mechanism** | `WRPKRU` (Ring 3) | `MSR POR_EL0, Xn` + `ISB` (EL0) | Guest `SYSCALL`/`SYSRET` (CPL3 <-> CPL0) or guest `CR3` | Host `SYS_write`/futex + host `CR3` switch |
| **Typical Switch Cost** | ~11–26 cycles | Single register + ISB (low tens of cycles) | ~100–150 cycles (zero VM exit); ~700–1,200 cycles on `VMCALL` to host | ~1,000+ cycles + cache/TLB disruption |
| **Number of Domains** | 16 keys (`0..15`) | 16 overlay indices (`0..15`) | Arbitrary (`CR3` address spaces + guest Ring 0/3) | Arbitrary OS processes |
| **Instruction-Fetch Isolation** | No (`AD`/`WD` data-only) | Yes (`POE_X` per key) | Yes (full guest PTE `NX` + U/S bit + EPT) | Yes (full hardware PTE) |
| **Untrusted Code Safety Requirement** | W^X + `WRPKRU`/`XRSTOR` scan + syscall/signal filter | W^X + `MSR POR_EL0` check + syscall/signal filter | None inside guest CPL 3 (hardware `SYSCALL` / PTE enforced!) | None inside process (MMU enforced) |

Notably, **IX** (OSDI 2014, `ix-project/ix`) uses Dune's exact VT-x split to run the protected IX TCP/IP dataplane and NIC driver at guest Ring 0 while running untrusted application logic in guest Ring 3—recreating an Exokernel-style secure boundary inside a single Linux process via EPT + VT-x privilege rings instead of software-scanned `WRPKRU`.

#### 5.2 Barrelfish Multikernel: Explicit Message-Passing State Replication (`BarrelfishOS/barrelfish`)

Whereas Dune/IX scale within single-core or core-partitioned hardware threads and Exokernels still share kernel capability tables inside a symmetric shared-memory kernel, **Barrelfish** (Baumann et al., SOSP 2009 `doi:10.1145/1629575.1629579`) treats a multicore/heterogeneous machine as a **distributed network of independent nodes**:
- **Zero Inter-Core Kernel Memory Sharing**: Each core executes an independent single-threaded privileged **CPU driver** owning only local physical frames, local page tables, and local capability tables—eliminating cross-socket kernel spinlocks and hardware cache-coherence bouncing on shared VM/capability metadata.
- **User-Level Monitors & Cache-Coherent UMP Rings (`include/barrelfish/ump_chan.h:45-90`)**: Cross-core capability transfers, virtual memory mappings, and global state updates run via per-core user-level **Monitor** processes communicating over **User-level Message Passing (`UMP`)** channels (`struct ump_chan` wrapping shared cache-line ring buffers `send_chan` and `endpoint` with `max_send_msgs` / `max_recv_msgs`). Polling cache-line ownership transitions avoids expensive inter-processor interrupts (IPIs) during normal capability operations.
- **Explicit State Replication & Synchronous Shootdowns**: When a shared page mapping or capability is revoked across cores, Barrelfish executes an explicit distributed message protocol across affected core Monitors (analogous to two-phase commit + explicit per-core local TLB invalidation notifications) rather than silently mutating a global page-table tree under a reader-writer lock. This directly connects Exokernel visible revocation and capability derivation trees to multi-socket hardware scalability: explicit message-passing makes cross-core revocation latency observable, bounded, and verifiable per core without hidden cache-coherence stalls.

## Boundaries

- **Bare-metal silicon benchmarks (`not examined`)**: Exact cycle counts cited for `WRPKRU` (~11–26 cycles), Dune `SYSCALL` (~100–150 cycles), and `VMCALL` (~700–1,200 cycles) reflect published literature baselines and architectural structure in upstream papers/codebases; live hardware microbenchmarking on bare-metal Ice Lake/Sapphire Rapids MPK, ARMv8.9 Neoverse silicon, or Intel VT-x hosts was not executed in this environment.
- **ARMv8.9 `FEAT_S1POE` hardware deployment and binary gadget tooling (`unknown` / `not examined`)**: Linux `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) exposes `arch/arm64/include/asm/por.h` and `POR_EL0` register helpers, and fixed-width 32-bit `AArch64` instructions eliminate unaligned x86-style mid-instruction byte smuggling; however, full runtime enforcement frameworks equivalent to `Cerberus`/`Jenny` specifically audited against `ARMv8.9` PAC/BTI + `POR_EL0` + `sigcontext` (`POE_MAGIC`) were not verified end-to-end here.
- **MPK hardware key limit (`unsupported`)**: Intel PKU provides 16 hardware protection keys (`0..15`, 4 bits in `PTE[62:59]`), and ARMv8.9 `POR_EL0` provides 16 4-bit overlay entries (`0..15`). Neither hardware register natively supports hundreds or thousands of fine-grained mutually distrusting compartments concurrently on a thread without software key multiplexing (e.g., key virtualization via `mprotect`/`CR3` fallback) or VT-x/process isolation.
- **Unikraft single-address-space intra-libOS isolation (`known not to apply`)**: Unikraft (`unikraft/unikraft` `7814c9dc529092edc4cfd52f4fffe54205eaca70`) focuses on single-address-space hypervisor-isolated specialization (`lib/ukalloc`) rather than intra-process MPK or Ring-0/Ring-3 compartmentalization out of the box; enforcing intra-unikernel fault isolation requires layering MPK/POE or SFI/Rust safety boundaries on top of its core allocator and driver modules.
- **Side-channel / transient-execution confidentiality (`known not to apply`)**: Neither Intel MPK (`PKRU`), ARMv8.9 `POR_EL0`, nor Dune guest `CR3` switching protects by itself against speculative-execution / cache-timing leakage (Spectre-PHT/BTB, Meltdown-class microarchitectural bugs) across compartments sharing physical cores or caches without complementary hardware/compiler mitigations (LFENCE, retpoline/IBRS, core pinning).

## Evidence

- **Primary Git Sources (verified at exact 40-hex commit SHAs on 2026-11-19)**:
  - `vahldiek/erim` (`7232f4762c5ff51035116f9664ec6e7af3b236af`):
    - `src/erim/erim.h` (lines 1–95: isolation flags `ERIM_FLAG_ISOLATE_TRUSTED`, `ERIM_FLAG_INTEGRITY_ONLY`, `ERIM_FLAG_SWAP_STACK`, scanner APIs).
    - `src/erim/erim_api_inlined.h` (lines 35–145: `ERIM_TRUSTED_PKRU = 0x55555550`, `ERIM_PKRU_ISOTRS_UNTRUSTED_CI = 0x5555555C`, `ERIM_PKRU_ISOTRS_UNTRUSTED_IO = 0x55555558`, `ERIM_SWITCH_TO_ISOLATED_STACK`, `erim_switch_to_trusted`/`untrusted`).
    - `src/erim/pkeys.h` (lines 20–75: `__rdpkru`, `__wrpkrucheck` GCC `asm goto` and Clang loop variants).
    - `src/erim/erim.c` (lines 17–115: `erim_scanMemForWRPKRUXRSTOR`, `isBenignWRPKRU`, `erim_memScanRegion`).
  - `isec-tugraz/Jenny` (`39bb0c696ce3c178e9593b7dbc034b2447ba2d00`):
    - `README.md` (repository layout: `code/OurLib`, `code/kernel_module_syscall_hook`, `code/kernel_patch_signal_handler`).
    - `code/kernel_patch_signal_handler/0001-Add-support-for-PKRU-secure-signal-handlers.patch` (`arch/x86/include/uapi/asm/signal.h:134-140` `SS_PKEY_*`, `arch/x86/kernel/signal.c:663-678,729-733` `rt_sigreturn` and `handle_signal` PKRU enforcement).
  - `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):
    - `arch/arm64/include/asm/sysreg.h` (lines 992–1005: `POE_NONE` through `POE_RWX`, `POR_ELx_BITS_PER_IDX`, `POR_ELx_PERM_GET`/`PREP`).
    - `arch/arm64/include/asm/por.h` (lines 1–35: `POR_EL0_INIT`, `por_elx_allows_read`, `por_elx_allows_write`, `por_elx_allows_exec`).
  - `project-dune/dune` (`af3e3bdddb81d80e900ef1e1fa9df6b54cdfcae9`):
    - `kern/dune.h` (lines 16–55: `DUNE_ENTER`, `DUNE_GET_SYSCALL`, `struct dune_config` with `cr3`, `rip`, `rsp`, `rflags`).
    - `kern/vmx.c` (lines 1253, 1447, 1887–1960: `vmx_init_ept`, `vmx_init_syscall`, `vmx_launch`, `vmx_handle_syscall` on `EXIT_REASON_VMCALL`).
  - `ix-project/ix` (`550bf28a4ddd5fafcec707a14acd502712a10dae`):
    - `dp/core/init.c` (`#include <dune.h>`, `init_dune`, PCI/ethdev dataplane initialization).
  - `microsoft/demikernel` (`42655abdffbdfc7283e30f913b153c7b39c9ee90`):
    - `include/demi/types.h` (lines 32–69: `DEMI_SGARRAY_MAXSIZE = 20`, `demi_qtoken_t`, `demi_sgaseg_t`, `demi_sgarray_t`), `include/demi/libos.h` (`demi_init`, `demi_socket`).
  - `unikraft/unikraft` (`7814c9dc529092edc4cfd52f4fffe54205eaca70`):
    - `lib/ukalloc/include/uk/alloc.h` (`struct uk_alloc` modular allocator interface).
  - `BarrelfishOS/barrelfish` (`06a9f54721a8d96874a8939d8973178a562c342f`):
    - `include/barrelfish/ump_chan.h` (lines 45–90: `struct ump_chan`, `ump_chan_init`, `ump_chan_bind`, `ump_chan_accept`).
- **Peer-Reviewed Papers**:
  - Engler, Kaashoek, and O'Toole, *Exokernel: An Operating System Architecture for Application-Level Resource Management*, SOSP 1995, pp. 251–266, `doi:10.1145/224056.224076`.
  - Kaashoek et al., *Application Performance and Flexibility on Exokernel Systems*, SOSP 1997, pp. 52–65, `doi:10.1145/268998.266644`.
  - Baumann et al., *The Multikernel: A New OS Architecture for Scalable Multicore Systems*, SOSP 2009, `doi:10.1145/1629575.1629579`.
  - Belay et al., *Dune: Safe User-level Access to Privileged CPU Features*, OSDI 2012, pp. 335–348.
  - Peter et al., *Arrakis: The Operating System is the Control Plane*, OSDI 2014 / ACM TOCS 2016, `doi:10.1145/2812806`.
  - Belay et al., *IX: A Protected Dataplane Operating System for High Throughput and Low Latency*, OSDI 2014, pp. 49–65.
  - Vahldiek-Oberwagner et al., *ERIM: Secure, Efficient In-process Isolation with Protection Keys (MPK)*, USENIX Security 2019, pp. 1221–1238 (`doi:10.48550/arXiv.1801.06822`).
  - Hedayati et al., *Hodor: Intra-Process Isolation for High-Throughput Data Plane Libraries*, USENIX ATC 2019, pp. 489–504.
  - Connor et al., *PKU Pitfalls: Attacks on PKU-based Memory Isolation Systems*, USENIX Security 2020, pp. 1409–1426.
  - Kuenzer et al., *Unikraft: Fast, Specialized Unikernels the Easy Way*, EuroSys 2021, pp. 376–394, `doi:10.1145/3447786.3456248`.
  - Zhang et al., *The Demikernel Datapath OS Architecture for Microsecond-scale Datacenter Systems*, SOSP 2021, pp. 195–211, `doi:10.1145/3477132.3483569`.
  - Voulimeneas et al., *You Shall Not (by)Pass!: Practical, Secure, and Fast PKU-based Sandboxing* (Cerberus), EuroSys 2022, pp. 266–282, `doi:10.1145/3492321.3519560`.
  - Schrammel et al., *Jenny: Securing Syscalls for PKU-based Memory Isolation Systems*, USENIX Security 2022, pp. 936–952.
- **Execution Evidence (2026-11-19)**:
  - Self-contained Python 3.13.15 micro-probe embedded in Findings Section 2.3 (`scan_wrpkru_xrstor`, `is_benign_gcc_exit_gate`, `simulate_mid_gadget_rop`, `poe_intersection_matrix`), confirming detection of cross-instruction `WRPKRU` inside `mov $0xef010f00, %eax`, full self-healing recovery from mid-gadget ROP jump at `+9` back to `0x5555555C`, and exact Stage-1 PTE & `POR_EL0` bitwise overlay intersection (`EFF = (0, 0, 1)` XOM).

## Revalidation

To verify whether upstream MPK/POE/VMX primitives, scatter-gather ABIs, or the byte-level gadget probe still hold across newer upstream revisions:

1. **Re-run the embedded Python 3 micro-probe (self-contained, standard library only)**:
   Execute the `python3 - <<'PY' ... PY` block in **Findings §2.3** and verify identical outputs (`UNALIGNED_GADGET: [(2, 'WRPKRU')] vetted=False`, ROP exit state `pkru=0x5555555c`, and `Execute-Only code page (XOM) ... EFF=(0, 0, 1)`).
2. **Check upstream ARMv8.9 POE, Demikernel ABI, and ERIM call-gate stability**:
   ```bash
   git -c protocol.version=0 ls-remote https://github.com/torvalds/linux.git HEAD
   curl -sSL https://raw.githubusercontent.com/torvalds/linux/<NEW_SHA>/arch/arm64/include/asm/por.h
   curl -sSL https://raw.githubusercontent.com/torvalds/linux/<NEW_SHA>/arch/arm64/include/asm/sysreg.h | grep -n -A 15 "POE_NONE"
   curl -sSL https://raw.githubusercontent.com/microsoft/demikernel/<NEW_SHA>/include/demi/types.h | grep -n -A 35 "DEMI_SGARRAY_MAXSIZE"
   curl -sSL https://raw.githubusercontent.com/vahldiek/erim/<NEW_SHA>/src/erim/pkeys.h | grep -n -A 25 "__wrpkrucheck("
   ```
3. **Audit Linux kernel signal-frame `PKRU` restoration semantics on target host kernels**:
   Inspect `arch/x86/kernel/signal.c` (`handle_signal` and `SYSCALL_DEFINE0(rt_sigreturn)`) and `arch/arm64/kernel/signal.c` (`POE_MAGIC` handling) at the exact deployed kernel commit before relying on any PKU/POE isolation guarantee for untrusted native code.
