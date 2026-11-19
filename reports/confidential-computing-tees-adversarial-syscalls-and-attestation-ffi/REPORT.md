# Confidential Computing TEEs, Adversarial Syscall Boundaries, and Attestation-Witnessed FFI

## Summary

Hardware Trusted Execution Environments (TEEs) — both process-level enclaves (Intel SGX, Komodo) and Confidential Virtual Machines (Intel TDX, AMD SEV-SNP, Arm CCA Realms) — invert the foundational trust assumption of operating systems and foreign function interfaces (FFIs). When the host OS kernel or hypervisor is an active adversary, every syscall return, ABI entry transition, shared-memory read, device MMIO/DMA transfer, and injected interrupt becomes an untrusted FFI crossing whose receiver must treat all host-supplied values as adversarial (`Untrusted<T>`) and validate them strictly after snapshotting into private memory.

Five load-bearing architectural findings govern sound verification and runtime design across confidential-computing boundaries:

1. **The syscall and ABI layers are adversarial RPCs with open-ended sanitization obligations.** Checkoway and Shacham (ASPLOS 2013) proved that a malicious kernel breaks shielded applications without touching private memory by returning semantically invalid values from `mmap`, `brk`, `getpid`, and clock calls. Van Bulck et al. (CCS 2019) showed that host-to-enclave entry/exit transitions break calling-convention preconditions at both an ABI tier (flags, stack pointers, floating-point/extended state) and an API tier (pointer range checks, double fetches, padding leakage). Direct source inspection of `gramineproject/gramine@918e832b` (`pal/src/host/linux-sgx/enclave_entry.S`) confirms that even production hardened entry stubs clear `RFLAGS.DF`/`RFLAGS.AC` and reset x87/SSE via `fxrstor`, while leaving an explicit `TODO` for upper AVX `YMM`/`ZMM` extended state until `XFRM` is read.
2. **Standard constant-time and MMIO proofs fail under TEE host observation and interrupt injection.** Host-controlled page tables and interrupt timers yield single-instruction execution traces (`Controlled-Channel Attacks`, S&P 2015; `SGX-Step`; `SEV-Step`; mitigated partially by `AEX-Notify`, USENIX Security 2023). Deterministic address-tweaked memory encryption (`CIPHERLEAKS`, USENIX Security 2021; S&P 2022) leaks plaintext equality across writes to the same physical block even for branchless constant-time code — confirmed via an executable micro-probe on constant-time conditional swap (`ct_cswap`). Host-injected `#VC` exceptions (`WeSee`, S&P 2024) and non-timer interrupts (`Heckler`, USENIX Security 2024) turn interrupt handlers into adversarial FFI entry points, while emulated virtual devices expose double-fetch TOCTOU and DMA hazards (`VIA`, ACSAC 2021) requiring shared `SWIOTLB` bounce buffers and copy-in-then-validate until hardware confidential I/O (`SPDM` + `TDISP` + PCIe IDE via TDX Connect / SEV-TIO) is deployed.
3. **Verified security monitors establish ISA-level noninterference with explicit declassifications, strictly above physical channels.** Direct inspection of `microsoft/Komodo@de1865c8` (`verified/secprop/sec_prop.s.dfy`, `conf_ni.i.dfy`, `integ_ni.i.dfy`) shows that confidentiality and integrity noninterference (`lemma_conf_ni`, `lemma_enc_ni`) explicitly declassify enclave page-table entries (`L1PTable`, `L2PTable`), dispatcher entry flags/entry points, and `KOM_SMC_STOP` calls, and rely on two `{:axiom}` SHA-256 trace bridge lemmas. Arm CCA RMM verification (OSDI 2022, OOPSLA 2023) extends mechanized proofs to concurrent relaxed-memory firmware, whereas physical memory-bus interposition lies entirely outside ISA-level monitor proofs.
4. **Remote attestation quotes have a finite, revocable half-life and measure bytes rather than properties.** Physical interposition attacks (`BadRAM` S&P 2025 / CVE-2024-21944; `Battering RAM` S&P 2026; `WireTap` 2025; `TEE.fail` S&P 2026 / INTEL-2025-10-28-001) extract platform attestation keys from patched servers using sub-$1,000 DDR4/DDR5 interposers and forge quotes accepted by vendor verifiers. Offline binary decoding of real Sapphire Rapids TDX Quote v4 (`tdx_prod_quote_SPR_E4.dat`, 4,974 bytes, 39 trailing bytes) and TDX 1.5 Quote v5 (`quote_sample_v5.dat`, 5,006 bytes) directly demonstrates runtime TCB drift (`TEE_TCB_SVN` = `0x0b` at launch vs. `TEE_TCB_SVN_2` = `0x0d` after live TDX module update).
5. **Typing a quote as a dependent code-identity witness requires five unbroken links plus channel binding and durable linearity.** Turning a remote RPC into verified-module linking (`connect : (h : Hash) -> ValidQuote h t -> Proof (Spec h S) -> Channel S`) requires (T) a source theorem, (C) verified compilation/translation validation, (R) reproducible whole-image build & measurement prediction, (M) time- and TCB-indexed hardware attestation, and (B) transcript channel binding (`REPORTDATA` / RA-TLS / TCG DICE OID `2.23.133.5.4.9`) to defeat cuckoo relays — plus external state continuity (`Memoir`, `ROTE`, `Nimble`) so host rollbacks cannot duplicate linear resources across restarts.

## Applicability

This report synthesizes primary source implementations, normative attestation standards, peer-reviewed security analyses, and executable micro-probes across five interacting layers:

- **Enclave Shielding Runtimes (`gramineproject/gramine@918e832b`):** Applies directly to Linux-SGX process-enclave entry/exit assembly (`enclave_entry.S`), untrusted OCALL wrappers (`enclave_ocalls.c`), enclave virtual memory checks (`pal_memory.c`), and RA-TLS attestation extensions (`ra_tls_attest.c`). Comparisons with other runtimes (Intel SGX SDK, Open Enclave, Rust-EDP, Asylo, Keystone, Sancus, Occlum, Ryoan) derive from the cited peer-reviewed studies at the revisions evaluated in those papers.
- **Confidential VM Architectures and Guest Kernels (`torvalds/linux@4405c18c`, `google/go-tdx-guest@dd3f7929`, `google/go-sev-guest@64934b57`, `TF-RMM/tf-rmm@8d7961df`, `intel/tdx-module@859989ac`, `intel/SGXDataCenterAttestationPrimitives@72f800e9`):** Applies to Intel TDX 1.0 (Quote v4, 584-byte `TDQuoteBody`) and TDX 1.5 (Quote v5, 648-byte `TDQuoteBody` with `TEE_TCB_SVN_2` and `MR_SERVICE_TD`), AMD SEV-SNP ABI report versions 2 through 5 (1,184-byte `ReportSize = 0x4A0`), and Arm CCA Realm Management Monitor (RMI/RSI SMC ABI). Hardware errata and kernel hardening findings (`Documentation/arch/x86/tdx.rst`, `arch/x86/coco/tdx/tdx.c`, `arch/x86/coco/sev/vc-handle.c`, `arch/x86/coco/core.c`) are exact for Linux at commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`.
- **Formally Verified Monitors (`microsoft/Komodo@de1865c8`, `uw-unsat/serval@72adc495`):** Komodo's Dafny/Vale proofs apply to its ARMv7 TrustZone research monitor (explicitly unmaintained upstream). Serval's symbolic verification results apply to the retrofitted monitors and BPF JITs evaluated at SOSP 2019. Arm CCA verification results apply to the Arm CCA RMM models verified in OSDI 2022 and OOPSLA 2023.
- **Attestation Standards and Endorsements (`RFC 9334`, `RFC 9711`, `project-oak/transparent-release@dd29c625`):** Applies to RATS entity roles, CBOR/JSON Entity Attestation Tokens (EAT), and in-toto v0.1 claim transparency envelopes (`schema/claim/v1`) used to bind provenance and audit claims to binary digests.
- **Executable Micro-Probes:** Python 3.13 probes executed offline on Linux x86-64 directly validate binary quote parsing against real embedded testdata (`tdx_prod_quote_SPR_E4.dat`, `quote_sample_v5.dat`), deterministic SHA-384 RTMR extension, channel-binding rejection of cuckoo relays, Iago `mmap` interval disjointness checks, and deterministic ciphertext-equality leakage under branchless constant-time swap.

Do not generalize exact Linux kernel mitigations or microcode TCB status numbers across unexamined kernel versions or CPU steppings without re-checking the relevant ABI headers and vendor advisories (see **Revalidation**).

## Findings

### 1. Cross-Architecture TEE Comparison: Isolation, Measurements, Injection Surface, and Continuity

Basis: normative + documentation + source (`go-tdx-guest/abi/abi.go`, `go-sev-guest/abi/abi.go`, `TF-RMM/tf-rmm/lib/smc/include/smc-{rmi,rsi}.h`, `torvalds/linux/Documentation/arch/x86/tdx.rst`, `microsoft/Komodo/verified/smcapi.s.dfy`)

Hardware TEEs differ sharply along five axes that directly determine the FFI surface exposed to an untrusted host: isolation granularity, measured state, host-injectable events, host observational channels, and built-in state continuity.

| Dimension | Intel SGX (Process Enclave) | Intel TDX 1.0 / 1.5 (CVM) | AMD SEV-SNP (CVM) | Arm CCA Realms (CVM) | Komodo (Verified Monitor) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Isolation unit** | User-space enclave pages (EPC) inside untrusted host process | Full VM (Trust Domain) managed by SEAM-mode TDX Module | Full VM isolated via Reverse Map Table (RMP) + ASP firmware | Full VM (Realm) in Realm World managed by EL2 RMM + EL3 Root | Enclave address spaces in ARMv7 TrustZone Secure World |
| **Root of trust / monitor** | CPU microcode + Architectural Enclaves (QE, PCE) | SEAM-mode TDX Module (`MR_SEAM`) + SGX Quoting Enclave (`TDREPORT` -> Quote) | AMD Secure Processor (ASP) firmware + VCEK/VLEK signing | EL3 Monitor + Granule Protection Table (GPT) + EL2 RMM | Formally verified ARMv7 assembly monitor (`verified/*.vad`) |
| **Initial measurement** | `MRENCLAVE` (32B SHA-256 of initial pages, attributes, layout) + `MRSIGNER` | `MR_TD` (48B SHA-384 of initial TDVF/config/pages) + `MR_CONFIG_ID`/`MR_OWNER` | `MEASUREMENT` (48B SHA-384 launch digest) + `HOST_DATA` (32B) | `RIM` (Realm Initial Measurement, index 0, up to 64B via `SMC_RSI_MEASUREMENT_READ`) | `Addrspace.measurement` (SHA-256 trace over `mapSecure` calls) |
| **Runtime measurements** | None in hardware (must be emulated in software) | 4x `RTMR[0..3]` (48B SHA-384 each, extended via `TDG.MR.RTMR.EXTEND`) | None in SNP report body (delegated to vTPM / SVSM / guest) | 4x `REM[1..4]` (extended via `SMC_RSI_MEASUREMENT_EXTEND`, FID `0xC4000193`) | None beyond launch measurement |
| **Quote / report format & size** | DCAP Quote v3 (`sgx_quote3_t`), ECDSA-P256 | Quote v4 (`header=48B`, `body=584B`, min `1020B`); Quote v5 TDX 1.5 (`body=648B`, min `1026B`, adds `TEE_TCB_SVN_2` 16B + `MR_SERVICE_TD` 48B) | SNP Report v2–v5 (`ReportSize = 0x4A0` = 1,184B: 672B body + 512B ECDSA-P384-SHA384 sig at `0x2A0`) | CCA Platform + Realm Attestation Token (COSE/CBOR EAT via `SMC_RSI_ATTESTATION_TOKEN_*`) | `KOM_SMC_ATTEST` HMAC/signature over `measurement` + user data |
| **Host-injectable events** | Asynchronous Enclave Exit (AEX) via any interrupt/exception; ECALL entry state | Posted/virtual interrupts, `#VE` triggers on shared memory / MSR / CPUID / MMIO / PIO | Arbitrary interrupts, `#VC` (vector 29), `#HV` doorbell (restricted when Alternate Injection / Restricted Injection enabled) | Virtual interrupts / aborts mediated by `SMC_RMI_REC_ENTER` / `REC_EXIT` | Normal-world interrupts trapped to monitor, `KOM_SMC_ENTER`/`RESUME` |
| **Memory encryption & replay defense** | SGX1 MEE (Merkle tree integrity on client); SGX2 / scalable Xeon drops integrity tree (AES-XTS only) | Multi-key TME (AES-XTS-128, 28-bit MAC integrity on private memory in Li/TME-MK; no replay tree across physical bus) | AES-128/256-XEX/XTS + RMP ownership check; optional `CipherTextHidingDRAM` (policy bit 24) & `PageSwapDisable` (bit 25) | Hardware Memory Encryption Contexts (MEC) + GPT physical-granule isolation | TrustZone TZASC physical memory partitioning (no DRAM encryption) |
| **Hardware state continuity / clock** | Legacy monotonic counters deprecated; no trusted wall clock | No rollback-resistant NVRAM; no trusted wall clock | No rollback-resistant NVRAM; Secure TSC optional (attacked in ACNS 2024) | No built-in rollback-resistant storage; generic timers host-influenced | None |

In `google/go-sev-guest@64934b57` (`abi/abi.go`, lines 73–84 and 246–260), the 64-bit `SnpPolicy` bitmask directly encodes critical host-restriction controls that a verifier must check: bit 16 (`SMT`), bit 17 (reserved must-be-1), bit 18 (`MigrateMA`), bit 19 (`Debug`), bit 20 (`SingleSocket`), bit 21 (`CLXAllow`), bit 22 (`MemAES256XTS`), bit 23 (`RAPLDis`), bit 24 (`CipherTextHidingDRAM`), and bit 25 (`PageSwapDisable`). Failing to verify `Debug == 0` (in SEV-SNP policy bit 19 or TDX `TD_ATTRIBUTES` bit 0) allows the host to inspect or mutate guest state legally.

### 2. Iago Attacks and the System-Call API as an Adversarial RPC

Basis: normative + documentation + source (`gramineproject/gramine@918e832b`, `pal/src/host/linux-sgx/pal_memory.c` & `enclave_ocalls.c`) + execution (Probe 1C)

Checkoway and Shacham (ASPLOS 2013) demonstrated that once a hardware isolation mechanism prevents an OS kernel from directly reading or modifying application memory, the application and kernel become mutually distrusting peers communicating across the system-call boundary as an **untrusted RPC interface**. Because POSIX and `libc` were architected under the assumption of a benign kernel, a malicious kernel can compromise application integrity and confidentiality purely by returning crafted, syntactically valid return values — **Iago attacks**:

1. **Memory-management overlap (`mmap`, `brk`):** Standard allocators (`glibc` `malloc`) trust the virtual addresses returned by `brk` and `mmap` to be disjoint from existing stacks, heaps, and code mappings. A malicious kernel returning an `mmap`/`brk` address that overlaps the application's own stack or internal allocator metadata tricks the application's own subsequent writes into overwriting its saved return addresses or function pointers, achieving arbitrary code execution inside the protected domain.
2. **Entropy and identifier replay (`getpid`, `gettimeofday`, `time`):** Even scalar, pointer-free syscalls are exploitable. In the ASPLOS 2013 case study against Apache `mod_ssl`, forked worker processes seeded their PRNG state using `getpid()` and timestamps; a malicious kernel replaying PIDs and clock values collapsed child entropy pools and enabled SSL session/key prediction.
3. **Stateful and I/O return manipulation (`read`, `stat`, `lseek`, `poll`):** Returning a byte count larger than the requested buffer length, negative error codes outside the POSIX contract (`-EINVAL` vs. unexpected positive/negative integers), or inconsistent file metadata induces buffer over-reads/over-writes and logic bypasses inside `libc`.

Cui, Zhao, and Lie (`Emilia`, NDSS 2021) built a greybox fuzzer specifically targeting Iago return-value bugs in legacy shielded applications, demonstrating that naive syscall pass-through runtimes routinely fail stateful return validation, whereas full library OSes (such as Graphene-SGX, the predecessor to Gramine) catch local and stateful Iago cases by internalizing kernel abstractions rather than forwarding raw syscalls.

#### Per-Interface Classification for Adversarial OS Boundaries

Basis: derived (from Checkoway–Shacham ASPLOS 2013, Emilia NDSS 2021, and Gramine PAL source)

Every host-provided OS interface falls into one of three structural classes with distinct verification obligations:

| Interface Class | Examples | Sound Defense Pattern | Residual Guarantee |
| :--- | :--- | :--- | :--- |
| **Checkable** | `mmap` (untrusted shared buffer), `read`/`write` byte counts, `errno` codes, cryptographic ciphertexts from disk/network | Copy return values once (`COPY_UNTRUSTED_VALUE`), enforce range/alignment/disjointness/bounds invariants, authenticate MACs/Merkle roots | Full integrity & confidentiality (host limited to DoS) |
| **Internalizable** | Virtual address space layout (`mmap`/`brk`/`mprotect` for private memory), PIDs, file descriptor table, signals/threading metadata, CSPRNG (`RDRAND`/`RDSEED` + enclave pool), allocator | Implement inside the TEE library OS / guest kernel; never consult host for security-critical state | Eliminates Iago surface completely at cost of larger in-TEE TCB |
| **Unverifiable (Availability / External Truth)** | Wall-clock time (`clock_gettime`), thread scheduling/preemption, physical entropy if hardware RNG is absent, durable non-volatile persistence (rollback prevention) | Cannot be locally verified from host return values alone; require cryptographic external witnesses (Roughtime/TLS timestamps, quorum state-continuity services) or explicitly downgrade to availability-only | No local freshness or liveness against a malicious host |

#### Concrete Validation Invariants in Gramine (`gramineproject/gramine@918e832b`)

Direct inspection of Gramine's Linux-SGX Platform Adaptation Layer (PAL) shows how both *internalization* and *checkable OCALL validation* are implemented in practice:

- **Internalized private memory allocation (`pal/src/host/linux-sgx/pal_memory.c`, lines 22–44, 50–87):** `_PalVirtualMemoryAlloc` asserts `IS_ALIGNED_PTR(addr, PAGE_SIZE)`, `access_ok(addr, size)`, and **`sgx_is_completely_within_enclave(addr, size)`** — the LibOS itself manages the enclave virtual address map and never trusts a host `mmap` address for private memory. `_PalVirtualMemoryFree` (lines 67–85) checks `sgx_is_valid_untrusted_ptr(addr, size, 1)` for untrusted buffers and invokes `BUG()` if a requested range partially overlaps `[shared_address_start, shared_address_end)`.
- **Single-fetch and allow-list validation on untrusted OCALLs (`pal/src/host/linux-sgx/enclave_ocalls.c`, lines 221–248):** In `ocall_mmap_untrusted`:
  1. Host `errno` values are filtered against an explicit allow-list (`-EACCES`, `-EAGAIN`, `-EBADF`, `-EINVAL`, `-ENFILE`, `-ENODEV`, `-ENOMEM`, `-EEXIST`, `-EPERM`); any unexpected negative value is coerced to `-EPERM` (lines 221–226).
  2. The host-returned address is snapshotted exactly once out of untrusted shared memory via **`void* returned_addr = COPY_UNTRUSTED_VALUE(&ocall_mmap_args->addr);`** (line 231), preventing double-fetch TOCTOU.
  3. Under `MAP_FIXED` / `MAP_FIXED_NOREPLACE`, the returned address must equal `requested_addr` (lines 232–237); otherwise it must satisfy **`sgx_is_valid_untrusted_ptr(returned_addr, size, PAGE_SIZE)`** — guaranteeing canonical user-space alignment, absence of 64-bit integer wraparound (`addr + size >= addr`), and complete disjointness from the enclave address range (lines 239–244).

Executable Probe 1C (`probe_p1_tee.py`) verified this exact interval predicate against four cases (benign outside buffer, Iago stack-overlap address `0x1fff0000`, partial lower-boundary overlap `0x0ffff000` + `0x2000`, and `u64` wraparound `0xfffffffffffff000` + `0x2000`), accepting only the disjoint aligned outside region and rejecting all three Iago payloads.

**Verification consequence:** Any proof about enclave or confidential-guest code conducted against a standard POSIX or `libc` axiomatization is vacuous under the TEE threat model because its kernel axioms are false. A sound FFI typing discipline must type every host-crossing return value as `Untrusted<T>`, eliminable only through a verified, single-fetch validator whose postcondition determines all safety invariants assumed by downstream code.

### 3. ABI-Tier and API-Tier Crossing Hazards Across Enclave Entry/Exit

Basis: documentation + source (`gramineproject/gramine@918e832b`, `pal/src/host/linux-sgx/enclave_entry.S`) + normative (Van Bulck et al. CCS 2019, Alder et al. ACSAC 2020)

Platform Application Binary Interfaces (such as the System V AMD64 ABI) assume caller and callee occupy a single trust domain: compiled code relies on callee-visible processor flags, stack alignment, and floating-point control words being in canonical initial states on function entry. Crossing a hardware TEE boundary invalidates every one of those unverified ABI preconditions.

Van Bulck, Oswald, Marin, Aldoseri, Garcia, and Piessens (*A Tale of Two Worlds*, ACM CCS 2019, `10.1145/3319535.3363206`) audited eight enclave shielding runtimes (including Intel SGX SDK, Open Enclave, Graphene-SGX, Rust-EDP, Asylo, Keystone, and Sancus) and uncovered over 35 boundary sanitization vulnerabilities structured into two tiers:

1. **Tier 1 — ABI-tier vulnerabilities (architectural state at `EENTER`/`EEXIT` or monitor entry):**
   - **Flag poisoning:** Leaving `RFLAGS.DF = 1` (direction flag) reverses `rep movs`/`stos` string copies (causing buffer underflows instead of overflows); leaving `RFLAGS.AC = 1` (alignment check) triggers `#AC` exceptions on unaligned enclave accesses, creating an attacker-controlled side channel.
   - **Stack and register corruption:** Unvalidated entry stack pointers (`RSP`) or unsaved/unscrubbed GPRs leak secrets on exit or pivot the enclave stack into untrusted host memory on entry.
   - **Floating-point and vector state poisoning:** Alder, Van Bulck, Oswald, and Piessens (*Faulty Point Unit*, ACSAC 2020) demonstrated that unsanitized x87 FPU control/status words (`FCW`, `FSW`, tag word) and SSE `MXCSR` rounding/exception masks silently corrupt numerical computations inside SGX enclaves (e.g., flipping rounding modes or triggering unexpected SIMD exceptions) even when integer registers are fully scrubbed.
2. **Tier 2 — API-tier vulnerabilities (marshaling, IDL wrappers, and pointer checks):**
   - Missing or integer-overflow-prone pointer-in-enclave / pointer-outside-enclave range checks (`ptr + len < ptr`), enabling confused-deputy reads/writes of enclave secrets.
   - Unterminated untrusted strings (`strlen` scanning past untrusted memory into enclave pages).
   - **Double-fetch (TOCTOU) races:** Checking a pointer or length field directly in untrusted memory and then re-reading it during copy or execution while a concurrent host thread mutates it. (Cloosters, Rodler, and Davi, `TeeRex`, USENIX Security 2020, used symbolic execution to uncover memory-corruption exploits in SGX enclave interfaces automatically.)
   - **Uninitialized struct padding leakage:** Copying C structs containing uninitialized compiler padding bytes from enclave stack to untrusted OCALL buffers leaks residual enclave stack secrets.

#### Primary-Source Audit of Gramine's Entry Trampoline (`enclave_entry.S`)

Direct inspection of `gramineproject/gramine@918e832b` (`pal/src/host/linux-sgx/enclave_entry.S`) shows both mature ABI hardening and the structural difficulty of maintaining completeness across evolving ISA extensions:

- **Direction flag (`L83–L84`):** Immediately executes `cld` to enforce `RFLAGS.DF = 0` for the System V AMD64 ABI.
- **Stack switch and GPR scrubbing (`L125–L137`):** Loads trusted stack `%gs:SGX_INITIAL_STACK_ADDR` into `%rsp` and zeroes `%rax` through `%r15`.
- **Alignment Check clearing (`L139–L141`):** Explicitly clears `RFLAGS.AC` on the stack via `pushfq` / bitmask / `popfq` to prevent the `#AC`-fault side channel.
- **SSA exception-handler rewiring (`L519–L527`):** Clears `SSA.GPRSGX.EXITINFO` and masks `~(RFLAGS_DF | RFLAGS_AC)` inside `SSA[0].GPRSGX.RFLAGS` before returning to stage-2 exception handling.
- **Residual extended-state sanitization gap (`L145–L151`):** Contains the explicit comment and code:
  ```asm
  # Clear "extended" state (FPU aka x87, SSE, AVX, ...).
  # TODO: We currently clear only state covered by FXRSTOR but not by XRSTOR (e.g., no clearing of
  #       YMM/ZMM regs). This is because we didn't read the value of XFRM yet, so we don't know
  #       whether XRSTOR is safe at this point.
  leaq g_xsave_reset_state(%rip), %rax
  fxrstor (%rax)
  ```
  Because every new ISA extension (AVX-512 `ZMM`/`k`-mask registers, AMX tile registers, APX extended GPRs) enlarges the architectural state vector, **cross-trust ABI sanitization is an open-ended, ISA-indexed proof obligation**. Any source-level or LLVM-IR verification proof that begins *after* the calling-convention boundary starts too late unless the entry trampoline itself is verified against an authoritative machine ISA model to establish the complete ABI precondition from arbitrary host machine state.

### 4. Controlled Channels, Single-Stepping, Ciphertext Visibility, and Injected Interrupts

Basis: documentation + source (`torvalds/linux@4405c18c`, `arch/x86/coco/sev/vc-handle.c` & `arch/x86/coco/tdx/tdx.c`; `google/go-sev-guest@64934b57`, `abi/abi.go`) + execution (Probe 1C)

Conventional constant-time verification assumes an observer who sees coarse execution timing or cache-set contention. A malicious TEE host possesses qualitatively stronger observational and fault-injection primitives:

#### A. Page-Fault Controlled Channels and Instruction Single-Stepping

- **Deterministic page-granular traces:** Xu, Cui, and Peinado (*Controlled-Channel Attacks*, IEEE S&P 2015, `10.1109/SP.2015.45`) demonstrated that because the untrusted OS owns page tables (or nested EPT/NPT tables in CVMs), clearing page present bits forces deterministic page faults on every cross-page code or data access, reconstructing document text and images with near-zero noise.
- **Single-instruction stepping:** Van Bulck et al. (`SGX-Step`, SysTEX 2017) and Wilke et al. (`SEV-Step`, TCHES 2024) configure local APIC timer interrupts with sub-instruction precision to interrupt an enclave or CVM after every single retired instruction, amplifying cache, branch, and memory side channels to 1-instruction resolution.
- **Hardware and OS mitigations:** `AEX-Notify` (Constable et al., USENIX Security 2023) adds an Intel SGX ISA extension that notifies the enclave upon asynchronous enclave exits so it can detect abnormal interrupt rates and execute defensive mitigation code; `Autarky` (Orenbach, Baumann, Silberstein, ASPLOS 2020) eliminates OS paging visibility via self-paging enclaves; AMD SEV-SNP exposes `SnpPolicy.PageSwapDisable` (bit 25 in `go-sev-guest/abi/abi.go` L83) to prevent hypervisor page swapping.

#### B. Deterministic Ciphertext Side Channels (`CIPHERLEAKS` and `Cipherfix`)

- **Mechanism:** Under deterministic, address-tweaked memory encryption (AES-XEX/AES-XTS without per-write freshness nonces, as deployed in AMD SEV/SEV-ES/SEV-SNP without ciphertext hiding), encrypting the same 16-byte plaintext at physical address $p$ always produces the identical 16-byte ciphertext $E_K(\text{tweak}(p), m)$. A hypervisor inspecting encrypted guest DRAM (or reading memory via bus interposition) observes a **write-equality oracle**: whether a store to address $p$ changed the plaintext value or rewrote an identical value.
- **Breaking constant-time cryptography:** `CIPHERLEAKS` (Li, Zhang, Wang, Li, Cheng, USENIX Security 2021) and its generalization to all guest memory (Li, Wilke, Wichelmann, Eisenbarth, Teodorescu, Zhang, IEEE S&P 2022) broke constant-time RSA, ECDSA, and EdDSA implementations on AMD SEV-SNP by reading ciphertext-equality patterns across register spills and conditional-swap writes.
- **Executable verification (Probe 1C):** Running a branchless, constant-address conditional swap (`diff = (a ^ b) & mask; a ^= diff; b ^= diff`) under a deterministic address-tweaked block cipher confirms that control flow and memory access addresses are 100% identical for `secret_bit = 0` and `secret_bit = 1`, yet the hypervisor's ciphertext-change observation is `(False, False)` for `bit = 0` and `(True, True)` for `bit = 1` — a deterministic 1-bit distinguisher.
- **Mitigations:** In software, `Cipherfix` (Wichelmann, Pätschke, Wilke, Eisenbarth, USENIX Security 2023) transforms binaries to mask/randomize stored values (rolling PRNG masks per store) so every write produces fresh ciphertext. In hardware, AMD added `CipherTextHidingDRAM` (`SnpPolicy` bit 24 in `go-sev-guest/abi/abi.go` L82) to block hypervisor CPU reads of encrypted guest DRAM — though `TEE.fail` (S&P 2026) later bypassed CPU-enforced ciphertext hiding via physical DDR5 bus interposition.

#### C. Adversarial Event Injection (`WeSee`, `Heckler`, `CacheWarp`)

In Confidential VMs, the hypervisor historically controls interrupt and exception delivery, turning guest interrupt handlers into unverified FFI entry points that the adversary can invoke at arbitrary instruction boundaries:

- **`WeSee` (Schlüter, Sridhara, Bertschi, Shinde, IEEE S&P 2024, `arXiv:2404.03526`):** Injects malicious `#VC` (VMM Communication Exception, x86 vector 29) interrupts into AMD SEV-SNP guests. Because the guest's `#VC` handler assumes `#VC` was legitimately triggered by the hardware on an intercepted instruction, crafted `#VC` injections trick the guest handler into copying attacker-chosen values between the guest and the shared GHCB — leaking NGINX kTLS keys, corrupting kernel firewall rules, and spawning a root shell. Inspection of `torvalds/linux@4405c18c` (`arch/x86/coco/sev/vc-handle.c`, lines 134–195, 390–434, 562–635) shows how the Linux `#VC` handler must decode the faulting instruction at `RIP` (`vc_decode_insn`) and check its opcode and exit code (`SVM_EXIT_MSR`, `insn_decode_mmio`, etc.) rather than trusting host-supplied exit semantics blindly.
- **`Heckler` (Schlüter et al., USENIX Security 2024):** Demonstrates that on both AMD SEV-SNP and Intel TDX, an untrusted hypervisor can inject malicious **non-timer interrupts** (such as legacy syscall vector `0x80` or device IRQs) whose handlers modify global architectural register state (`RAX` return values), bypassing OpenSSH and `sudo` authentication. Mitigating this requires hardware Restricted/Alternate Injection modes and guest kernel interrupt-vector filtering.
- **`CacheWarp` (Zhang et al., USENIX Security 2024):** Uses software-triggered cacheline invalidation (`INVD`/architectural state resets) on AMD SEV-ES/SEV-SNP to roll back modified dirty guest cachelines to stale DRAM values, functioning as a software fault-injection attack that bypasses authentication and extracts RSA keys.
- **Linux TDX `#VE` re-entrancy defense (`torvalds/linux@4405c18c`):** `Documentation/arch/x86/tdx.rst` (lines 454–466) and `arch/x86/coco/tdx/tdx.c` (lines 781, 843) document that upon delivering a `#VE`, the TDX module blocks all further interrupts (including NMIs) and nested `#VE`s until the guest invokes `TDG.VP.VEINFO.GET`; any nested `#VE` triggered while blocked escalates immediately to `#DF` (Double Fault) to prevent stack/state re-entrancy corruption.

### 5. Hostile Virtual Devices, Bounce Buffers, Double Fetches, and Hardware TEE I/O

Basis: documentation + source (`torvalds/linux@4405c18c`, `Documentation/arch/x86/tdx.rst`, `arch/x86/coco/core.c`, `arch/x86/coco/tdx/tdx.c`) + normative (VIA ACSAC 2021, PCI-SIG TDISP / DMTF SPDM)

A Confidential VM's private memory is encrypted and inaccessible to the hypervisor or unauthenticated PCIe devices. Consequently, all emulated I/O (VirtIO rings, MMIO registers, port I/O, ACPI tables, CPUID leaves, MSRs, DMA buffers) crosses **shared, unencrypted memory** controlled concurrently by an adversarial host.

- **Empirical device-interface fragility (`VIA`, Hetzelt et al., ACSAC 2021, `arXiv:2109.10660`):** Fuzzing 22 Linux 5.10.0-rc6 device drivers across MMIO, PIO, and DMA interfaces uncovered **50 bugs** (buffer overflows, out-of-bounds reads/writes, double fetches, missing sanitization of host-supplied lengths/indices) and demonstrated three concrete hypervisor-to-guest exploits achieving guest kernel memory corruption and code execution under SEV-ES (and structurally applicable to SEV-SNP and TDX).
- **Linux TDX guest hardening surface (`torvalds/linux@4405c18c`):**
  - *Shared/private memory conversions:* `Documentation/arch/x86/tdx.rst` (lines 491–511) documents that all TDX guest memory starts private; drivers convert buffers via `set_memory_decrypted()` / `set_memory_encrypted()`. Standard DMA allocations route through **`SWIOTLB` bounce buffers** converted to shared at boot, while coherent DMA enforces `force_dma_unencrypted()`.
  - *Platform capability queries (`arch/x86/coco/core.c`, lines 31–42):* `intel_cc_platform_has()` enables `CC_ATTR_GUEST_UNROLL_STRING_IO`, `CC_ATTR_GUEST_MEM_ENCRYPT`, and `CC_ATTR_MEM_ENCRYPT` (forcing unrolled I/O emulation rather than `REP INS`/`OUTS` string transfers over private memory).
  - *First-generation TDX partial-write erratum (`Documentation/arch/x86/tdx.rst`, lines 267–281):* A sub-cacheline (partial) write to TDX private memory (e.g., via `MOVNTI`, UC/WC mappings, or misconfigured DMA) silently poisons the cacheline, triggering a fatal Machine Check Exception on subsequent read.
  - *Attack-surface reduction:* Linux confidential guest hardening shrinks the exposed driver set via device allow-listing (`authorized_default` / bus-level authorization filters restricting enumeration to audited drivers such as hardened `virtio`) and strict `#VE` exit-reason whitelisting in `tdx.c` (handling only `EXIT_REASON_HLT`, `MSR_READ`, `MSR_WRITE`, `CPUID`, `IO_INSTRUCTION`, and `EPT_VIOLATION` for explicit MMIO; lines 371–378, 823–835).
- **FFI and memory-model consequence (`Shared<T>` vs. `Private<T>`):** In Rust or verified systems languages, shared CVM I/O memory is **volatile memory with a concurrent Byzantine writer**. Forming an ordinary immutable reference `&[u8]` or `&T` over shared bounce-buffer memory is unsound (violating Rust's aliasing/immutability guarantees and inviting LLVM to re-read fields, introducing double-fetch TOCTOU bugs). Sound zero-copy/low-level FFI design must distinguish `Shared<T>` from `Private<T>`, permitting reads only through a single-fetch volatile snapshot (`read_once() -> Untrusted<T>` into private memory) followed by total byte-validity and invariant validation before producing a typed `T`.
- **Hardware confidential I/O (`SPDM` + `TDISP` + PCIe IDE):** To eliminate `SWIOTLB` bounce-buffer copy overhead and remove emulated hypervisor drivers from the data path, industry standards pair **DMTF SPDM** (cryptographic device authentication and firmware measurement) with **PCI-SIG TDISP** (TEE Device Interface Security Protocol locking a PCIe function's configuration/MMIO/DMA state to a specific CVM) and **PCIe IDE** (link-layer Integrity and Data Encryption), instantiated as **Intel TDX Connect** and **AMD SEV-TIO**. Crucially, TDISP does not eliminate trust — it shifts trust from the hypervisor's emulated device to the physical peripheral's attested firmware, bringing the device's firmware measurement into the CVM's TCB.

### 6. Physical Key Extraction, Platform Revocation, and Evidence Half-Life

Basis: documentation + normative (vendor advisories & peer-reviewed papers) + execution (Probe 1A)

Hardware roots of trust exhibit transient, fault-injection, and physical bus-interposition failure modes that directly compromise platform attestation keys. Because a forged attestation quote forged with an extracted hardware signing key is cryptographically indistinguishable from a genuine quote until revoked, **attestation evidence is non-monotonic and has a finite half-life**.

| Attack | Authors & Venue | Target Architecture | Mechanism | Exposed Material / Impact | Vendor Response / CVE |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Foreshadow (L1TF)** | Van Bulck et al., USENIX Security 2018 | Intel SGX | L1 Terminal Fault transient execution across page faults | Enclave secrets and Intel SGX EPID/PCK attestation sealing keys | CVE-2018-3615; microcode updates, L1D flush, TCB recovery |
| **Plundervolt** | Murdock et al., IEEE S&P 2020 | Intel SGX | Software-controlled dynamic voltage scaling (undervolting) fault injection | AES-NI / RSA-CRT private keys inside SGX enclaves | CVE-2019-11157; BIOS/microcode lock on voltage MSRs |
| **SGAxe** | van Schaik et al., 2020 | Intel SGX | CrossTalk / SRBDS transient buffer sampling targeting Intel's Quoting Enclave | Extraction of SGX Quoting Enclave EPID attestation private key | CVE-2020-0543; microcode update, Intel TCB recovery |
| **BadRAM** | De Meulemeester et al., IEEE S&P 2025 | AMD SEV-SNP | Manipulated DIMM SPD metadata / static address-line aliasing bypassing RMP | Replay and tampering of SEV-SNP encrypted memory and attestation forgery | **CVE-2024-21944** (AMD-SB-3015); BIOS/AGESA boot-time aliasing checks |
| **Battering RAM** | De Meulemeester, Oswald, Verbauwhede, Van Bulck, IEEE S&P 2026 | Intel SGX, AMD SEV-SNP | ~$50 active DRAM interposer switching address lines dynamically *after* boot checks | Plaintext memory access on SGX; attestation forgery on patched SEV-SNP | No CVE; vendors classify physical bus interposition out of threat model |
| **WireTap** | Chuang, Seto, Amer, Duran, Garman, Genkin, 2025 | Intel SGX (DDR4) | Passive DDR4 memory bus interposer + deterministic AES-XTS ciphertext dictionary | Recovers SGX Quoting Enclave ECDSA key from a single signing operation; forges DCAP-accepted quotes | No CVE; out of threat model per Intel |
| **TEE.fail** | Chuang, Seto, Berrios, van Schaik, Garman, Genkin, IEEE S&P 2026 | Intel TDX, AMD SEV-SNP (incl. Ciphertext Hiding), Nvidia GPU CC (DDR5) | Sub-$1,000 custom DDR5 bus interposer defeating deterministic memory encryption & CPU ciphertext hiding | Extracts platform attestation keys, forges TDX/SEV-SNP quotes, subverts GPU Confidential Computing attestation | Advisory **INTEL-2025-10-28-001**; no CVE assigned (physical access excluded) |

**Direct quote evidence of dynamic TCB evolution (Probe 1A):** Parsing the upstream TDX 1.5 quote specimen `quote_sample_v5.dat` (`google/go-tdx-guest@dd3f7929`) reveals `TEE_TCB_SVN = 0b010400000000000000000000000000` (launch-time TCB SVN = `0x0b`) alongside `TEE_TCB_SVN_2 = 0d010400000000000000000000000000` (runtime-updated TCB SVN = `0x0d`). This confirms Linux `Documentation/arch/x86/tdx.rst` (lines 198–201): a live TDX module update changes `TEE_TCB_SVN_2` without restarting the TD, while `TEE_TCB_SVN` preserves the launch-time TCB state — so a relying party verifying a Quote v5 must evaluate *both* SVNs against a current revocation list (a TD launched under a compromised `TEE_TCB_SVN` may already have had its initial memory compromised before the module update).

**Verification consequence:** Treating an attestation quote as an eternal, timeless proof term is unsound. Any formal verification judgment grounded in remote attestation must be parameterized by an explicit revocable trust hypothesis $\text{ValidPlatform}(\text{vendor}, \text{TCB\_SVN} \ge v, [t_{\text{start}}, t_{\text{end}}])$, or diversify across independent hardware vendors/substrates via a threshold trust formula.

### 7. Verified Security Monitors: Guarantees, Explicit Declassifications, and Proof Gaps

Basis: source (`microsoft/Komodo@de1865c8`, `TF-RMM/tf-rmm@8d7961df`, `uw-unsat/serval@72adc495`) + normative (Ferraiuolo et al. SOSP 2017, Nelson et al. SOSP 2019, Li et al. OSDI 2022, Fox et al. OOPSLA 2023)

Because opaque microcode and vendor firmware modules (such as Intel's SGX microcode or the TDX Module, whose public assurance artifacts consist of third-party security audits rather than a published machine-checked proof) expand the unverified TCB, verified security monitors formalize enclave/CVM isolation directly in machine-checked logic:

- **Komodo (`microsoft/Komodo@de1865c8`, Ferraiuolo et al., SOSP 2017, `10.1145/3132747.3132782`):** Implements an SGX-style enclave monitor in verified ARMv7 assembly (Vale/Dafny/Boogie/Z3) over TrustZone Secure World. Primary-source inspection of `verified/secprop/` establishes the exact security theorems and their explicit boundaries:
  - *Confidentiality (`verified/secprop/conf_ni.i.dfy`, lines 20–31):* `lemma_conf_ni` proves that for two low-equivalent executions `conf_loweq(s1, d1, s2, d2, atkr)` with `same_cpsr(s1, s2)` and identical nondeterministic oracle `s1.conf.nondet == s2.conf.nondet`, executing any SMC preserves `conf_loweq(s1', d1', s2', d2', atkr)` *except* when `callno == KOM_SMC_STOP && asp == atkr`.
  - *Integrity (`verified/secprop/integ_ni.i.dfy`, lines 14–27):* `lemma_enc_ni` proves that a malicious OS colluding with another enclave preserves `loweq_pdb(d1', d2', obs)` for any non-stopped observer enclave `obs`, again excluding `KOM_SMC_STOP` on `obs`.
  - *Explicit declassifications (`verified/secprop/sec_prop.s.dfy`, lines 46–95):* The `loweq_entry` predicate explicitly equates `L1PTable` and `L2PTable` (`e1 == e2`), exposes `Dispatcher.entered` and `Dispatcher.entrypoint`, and hides only `DataPage` contents, `SparePage` contents, saved dispatcher register context, and `Addrspace.{shatrace, measurement, refcount}` — formalizing the exact architectural observation surface available to the host OS.
  - *Trusted axioms (`verified/smcapi.s.dfy`, lines 100–115):* Measurement specification relies on two `{:axiom}` lemmas (`lemma_SHATracesAreEqual`, `lemma_SHATraceExists`) bridging byte sequences to `SHA256Trace` objects in the `PageDb` abstract model.
- **Serval (`uw-unsat/serval@72adc495`, Nelson et al., SOSP 2019, `10.1145/3341301.3359641`):** Replaces manual interactive proofs with automated symbolic evaluation (lifting ISA interpreters in Rosette/SMT). Retrofitting Komodo, CertiKOS, Keystone, and Linux eBPF JITs into Serval uncovered **18 new bugs** across evaluated systems code — demonstrating both the tractability of push-button monitor verification and the fragility of hand-maintained proof-to-implementation boundaries.
- **Arm CCA Realms and RMM (`TF-RMM/tf-rmm@8d7961df`, Li et al. OSDI 2022, Fox et al. OOPSLA 2023):** Li et al. (OSDI 2022) produced the first machine-checked proof of confidentiality and integrity for concurrent Arm CCA firmware on relaxed-memory hardware while allowing the untrusted normal-world hypervisor to manage dynamic memory allocation via granule delegation (`SMC_RMI_GRANULE_RANGE_DELEGATE` / `UNDELEGATE`, `SMC_RMI_REALM_CREATE`, `SMC_RMI_REC_ENTER` in `lib/smc/include/smc-rmi.h`). Fox et al. (OOPSLA 2023) established the industrial specification-to-implementation verification methodology bridging Arm's formal ASL/Sail architecture models to safe RMM code.
- **Compositional gap:** While monitor interfaces (`KOM_SMC_*`, `SMC_RMI_*`/`RSI_*`, `TDG.*` TDCALLs) are the cleanest trust boundaries in the stack, verified monitors (Dafny/Vale, Coq, Isabelle/HOL), verified guests, and host VMM stubs reside in separate proof assistants with incompatible ISA models and do not compose mechanically end-to-end. Furthermore, all monitor noninterference theorems are stated at the ISA level and remain completely blind to microarchitectural stepping, deterministic ciphertext equality, and physical bus interposition (Sections 4 and 6).

### 8. Attestation Binary Formats, Semantic Gap, Dependent Code-Identity Witnesses, and Continuity

Basis: normative (`RFC 9334`, `RFC 9711`) + source (`go-tdx-guest`, `go-sev-guest`, `gramine/tools/sgx/ra-tls/ra_tls_attest.c`, `project-oak/transparent-release`) + execution (Probes 1A, 1B) + derived

#### A. Binary Quote Specimens and Live Parsing Observations (Probe 1A)

Direct execution of our offline parser (`probe_p1_tee.py`) against upstream Intel TDX testdata in `google/go-tdx-guest@dd3f7929` verified exact wire-format structure across Quote v4 and Quote v5:

| Field | `tdx_prod_quote_SPR_E4.dat` (TDX 1.0, Quote v4) | `quote_sample_v5.dat` (TDX 1.5, Quote v5) |
| :--- | :--- | :--- |
| **Total size / SHA-256 prefix** | 4,974 bytes (`6dde5548bec99147...`) | 5,006 bytes (`cf77a6e91e48291d...`) |
| **Header (`48 B`, `0x00..0x30`)** | `version = 4`, `att_key_type = 2` (ECDSA-P256), `tee_type = 0x00000081` | `version = 5`, `att_key_type = 2`, `tee_type = 0x00000081` |
| **Body descriptor / size** | Implicit v4 (`584 B`, `0x30..0x278`) | `body_type = 3` (TDX 1.5), `body_size = 648 B` (`0x36..0x2be`) |
| **Signed auth data size** | `4,299 B` (plus **39 trailing bytes** beyond signed envelope!) | `4,300 B` (`0` trailing bytes) |
| **`TEE_TCB_SVN` (launch, `16 B`)** | `03000400000000000000000000000000` | `0b010400000000000000000000000000` |
| **`TEE_TCB_SVN_2` (runtime, `16 B`)** | *Absent in v4* | `0d010400000000000000000000000000` (updated live) |
| **`TD_ATTRIBUTES` / `Debug` bit** | `0x0000000040000000` (`debug_bit = False`) | `0x0000000010000000` (`debug_bit = False`) |
| **`XFAM` (`8 B`)** | `0x0000000000061ae7` | `0x00000000000602e7` |
| **`MR_TD` (`48 B` SHA-384)** | `6363b8043668a3ad953278e10389574d...d7215cbb` | `7348651a34b2d2d3462822e3a750ec61...3bc8f876` |
| **`RTMR[0]` (`48 B` SHA-384)** | `2927da70461cd63266f43230cc1849c0...6593f32a` | `5c8daf76063a71ac8fcef4067564661f...cec24619` |

The 39 trailing bytes in the production Sapphire Rapids Quote v4 specimen (`48 + 584 + 4 + 4299 = 4935 < 4974`) highlight a concrete parser-differential hazard: strict verifiers must reject or explicitly account for trailing bytes when hashing quotes for replay caches or transparency logs.

#### B. Standards, Semantic Gap, and the Five-Link Dependent Witness Chain

The **IETF RATS Architecture** (`RFC 9334`, January 2023) defines five distinct roles — **Attester**, **Verifier**, **Relying Party**, **Endorser**, and **Reference Value Provider** — separating raw cryptographic *Evidence* from appraised *Attestation Results*. **Entity Attestation Token (EAT)** (`RFC 9711`, April 2025) standardizes CBOR Web Token (CWT) and JWT claim sets conveying measurements, debug status, and hardware identity. Yet a measurement digest (`MRENCLAVE`, `MR_TD`, `MEASUREMENT`, `RIM`) certifies only *which bytes were loaded*, never *what security property those bytes satisfy* — the **attestation semantic gap** (Haldar, Chandra, Franz, 2004; Sadeghi & Stüble, 2004; Coker et al., 2011).

Closing that gap so a remote FFI call carries a **dependent code-identity type witness**:
```text
connect : (h : Digest)
       -> ValidQuote(h, vendor, tcb_svn >= v, nonce, eph_pk, [t_0, t_1])
       -> Proof(Refines(ImageBytes(h), Spec_S))
       -> AttestedChannel(Spec_S, [t_0, t_1])
```
requires **five sequential links**:
1. **Link T (Source theorem):** A machine-checked theorem that source program $P$ satisfies contract $S$ under an adversarial-host model.
2. **Link C (Verified lowering):** Verified compilation or translation validation proving the emitted object/binary refines $P$.
3. **Link R (Reproducible build & image measurement):** Deterministic compilation, linking, and VM/enclave image assembly plus a deterministic measurement calculator predicting $h = \text{Measure}(\text{Image})$ from the build graph (Probe 1B verifies deterministic `RTMR = SHA-384(RTMR_old || SHA-384(event))` repeatability).
4. **Link M (Hardware quote + transparency endorsement):** A fresh, time-bounded hardware quote binding $h$, accompanied by signed, validity-bounded transparency endorsements. Direct inspection of `project-oak/transparent-release@dd29c625` (`docs/claim-transparency.md`, lines 25–85) shows how in-toto v0.1 statements (`predicateType: "https://github.com/project-oak/transparent-release/schema/claim/v1"`) attach `claimType`, `claimSpec`, `evidence` digests, and mandatory `validity.{notBefore, notAfter}` passive-revocation windows to binary digests — providing the exact metadata envelope needed for formal-verification claims, though no IANA/RATS claim type for machine-checked proof terms is standardized yet.
5. **Link B (Session channel binding):** Cryptographically binding the transport session's ephemeral public key and verifier freshness nonce into the quote's `REPORTDATA` field to defeat **cuckoo (relay) attacks** (Parno, HotSec 2008), where a malicious host proxies attestation challenges to a genuine remote TEE while terminating the TLS session itself. In **RA-TLS** (Knauth et al., 2018) and `gramineproject/gramine@918e832b` (`tools/sgx/ra-tls/ra_tls_attest.c`, lines 148–156), the enclave embeds its quote inside a self-signed X.509 certificate under both a legacy OID and the standard **TCG DICE "tagged evidence" OID `2.23.133.5.4.9`** with `REPORTDATA` committing to the certificate's public key. Formal protocol verification of Intel TDX attestation (Sardar, Musaev, Fetzer, 2021) confirmed that underspecified channel-binding steps in draft specs admit relay/ambiguity flaws unless transcript binding (`SHA-256(eph_pk || nonce)`) is enforced — demonstrated in Probe 1B, where swapping the endpoint key from `eph_pk_honest` to `eph_pk_mitm` immediately fails the `REPORTDATA[0:32]` check.

Historical research precedents established pieces of this chain: **Proof-Carrying Code** (Necula, POPL 1997) linked binary bytes to checkable proofs locally; **Logical Attestation** (`Nexus`, Sirer et al., SOSP 2011) replaced raw hashes with authorization-logic formulas; and **Ironclad Apps** (Hawblitzel et al., OSDI 2014) verified a full stack down to x86 assembly (Dafny/Boogie/Z3) and paired it with TPM remote attestation so a remote user could verify the running binary met its formal security spec. On modern confidential-computing hardware (SGX/TDX/SEV-SNP/CCA), however, no deployed production system examined in this study joins all five links (`T` through `B`) across the entire measured image (firmware + kernel + runtime + application).

#### C. Rollback, Trusted Time, Bidirectional Distrust, and TEE-Aware Languages

- **Durable linearity and state continuity:** Because an adversarial host controls persistent storage and VM snapshots, it can roll back sealed state or fork two concurrent instances of a TEE. Any resource treated as **linear** inside a language (differential-privacy budgets, one-time cryptographic nonces, MPC preprocessing triples, certificate revocation epochs) becomes unsound across crashes or restarts unless backed by a state-continuity service: TPM NVRAM (`Memoir`, Parno et al., IEEE S&P 2011), distributed SGX counter quorums (`ROTE`, Matetic et al., USENIX Security 2017), or high-throughput crash-tolerant replicated ledgers (`Nimble`, Angel et al., OSDI 2023). Likewise, hardware clocks remain vulnerable: **Not So Secure TSC** (Juffinger, Neela, Gruss, ACNS 2024) demonstrated attacks undermining AMD SEV-SNP's Secure TSC feature, reinforcing that confidential guests cannot assume monotonic or accurate local wall-clock time without external cryptographic time protocols.
- **Bidirectional and three-party distrust:** Hardware confidentiality also shields buggy or malicious enclave code from host inspection: `Dark-ROP` (Lee et al., USENIX Security 2017) exploited unreadable SGX enclaves via blind ROP, while Schwarz, Weiser, and Gruss (DIMVA 2019) built enclave-resident malware attacking the host process from unreadable EPC memory. Conversely, data owners may distrust both the host and the enclave service code, motivating two-way sandboxes inside enclaves: `Ryoan` (Hunt et al., OSDI 2016, TOCS 2018 `10.1145/3177123`) confines untrusted compute modules using NaCl SFI inside SGX to prevent secret exfiltration, and `Occlum` (Shen et al., ASPLOS 2020, `10.1145/3373376.3378469`) isolates concurrent processes inside one SGX enclave via SFI.
- **TEE-aware information-flow and partitioning calculi:** `DFLATE` (Gollamudi, Chong, Arden, IEEE CSF 2019, `10.1109/CSF.2019.00028`) formalizes distributed IFC across TEEs with an explicit attestation-aware label lattice, and `JE` (Oak, Ahmadian, Balliu, Salvaneschi, IEEE CSF 2021, `10.1109/CSF51455.2021.00009`) provides language-level enclave partitioning abstractions. Because TEE hardware substrates churn rapidly (e.g., Intel removed SGX from 11th/12th-generation client CPUs while introducing TDX on Xeon servers and SPDM-based GPU confidential computing), FFI and compiler interfaces should treat each TEE substrate as a backend parameterized by `(isolation_granularity, leakage_contract, attestation_format, trust_formula)` rather than hard-coding vendor SDK primitives.

## Boundaries

- **not examined:** Live online cryptographic signature-chain verification against Intel Provisioning Certification Service (PCS) or AMD Key Distribution Service (KDS) root CAs and live CRL/TCB-info JSON feeds was not executed (offline execution environment without live PKI access); Probe 1A parses the binary quote envelopes and checks structural invariants, RTMR extension, and channel binding without performing live network PKI lookups.
- **not examined:** Exhaustive auditing of every Linux driver in the default TDX `authorized_default` device allow-list or full formalization of the PCI-SIG TDISP state machine was not conducted; findings rest on Linux `Documentation/arch/x86/tdx.rst`, `arch/x86/coco/`, VIA (ACSAC 2021), and architectural TDISP/SPDM specifications.
- **unknown:** Whether any non-public or proprietary deployment currently joins all five links (`T`, `C`, `R`, `M`, `B`) of the dependent code-identity witness chain end-to-end across a complete measured CVM image (firmware, kernel, runtime, and application) on TDX, SEV-SNP, or Arm CCA; no such deployed open-source system was located in examined repositories or literature.
- **unknown:** Whether `gramineproject/gramine` has an out-of-tree branch resolving the `enclave_entry.S` L146 `TODO` for `XRSTOR` sanitization of `YMM`/`ZMM` registers; at pinned commit `918e832b8ab4f583bc878ae33cb6b15dfd3e84a9`, only `FXRSTOR` state is reset on initial entry.
- **known not to apply:** Classical constant-time security proofs (secret-independent control flow and memory-access addresses) are *known not to apply* as sufficient confidentiality guarantees under AMD SEV/SEV-SNP without ciphertext hiding or under physical DRAM bus interposition (`CIPHERLEAKS`, `TEE.fail`, Probe 1C), nor under instruction-granular single-stepping (`SGX-Step`, `SEV-Step`).
- **known not to apply:** ISA-level monitor noninterference theorems (`Komodo`, `Serval`, Arm CCA RMM) are *known not to apply* to microarchitectural transient execution (`Foreshadow`, `SGAxe`), voltage fault injection (`Plundervolt`), or physical DRAM interposition (`BadRAM`, `Battering RAM`, `WireTap`, `TEE.fail`).
- **unsupported:** Intel SGX is explicitly unsupported on 11th-generation and newer Intel client processors (restricted to server Xeon platforms and largely superseded by Intel TDX for cloud VM workloads). `microsoft/Komodo` is explicitly marked unmaintained in its upstream `README.md`.

## Evidence

All primary-source inspections and micro-probe executions were acquired on `2026-11-19`.

### Pinned GitHub Source Inspections (`Basis: source`)

- **`gramineproject/gramine`** at `918e832b8ab4f583bc878ae33cb6b15dfd3e84a9`:
  - `pal/src/host/linux-sgx/enclave_entry.S` L68–L152 (`enclave_entry`: `cld`, GPR zeroing, `RFLAGS.AC` clear, `fxrstor` with explicit `TODO` for `YMM`/`ZMM`), L519–L527 (`SSA[0].GPRSGX.RFLAGS` clearing of `RFLAGS_DF | RFLAGS_AC`).
  - `pal/src/host/linux-sgx/pal_memory.c` L22–L88 (`_PalVirtualMemoryAlloc` asserting `sgx_is_completely_within_enclave`, `_PalVirtualMemoryFree` checking `sgx_is_valid_untrusted_ptr` and `BUG()` on partial shared-range overlap).
  - `pal/src/host/linux-sgx/enclave_ocalls.c` L221–L249 (`ocall_mmap_untrusted`: `errno` allow-list, single-fetch `COPY_UNTRUSTED_VALUE`, `MAP_FIXED` equality check, `sgx_is_valid_untrusted_ptr`).
  - `tools/sgx/ra-tls/ra_tls_attest.c` L79–L156 (`generate_x509`: embedding legacy SGX quote OID and TCG DICE tagged evidence OID `2.23.133.5.4.9`).
- **`microsoft/Komodo`** at `de1865c8bd0d85cdfd9a980ad7131448acfaf136`:
  - `README.md` (unmaintained notice, DOI `10.1145/3132747.3132782`, ARMv7 TrustZone architecture).
  - `verified/subdir.mk` L3 (top-level verification targets `conf_ni.i.verified`, `integ_ni.i.verified`).
  - `verified/smcapi.s.dfy` L1–L120 (`allocatePage`, `{:axiom}` `lemma_SHATracesAreEqual` & `lemma_SHATraceExists`, `updateMeasurement`).
  - `verified/secprop/sec_prop.s.dfy` L46–L95 (`conf_loweq`, `loweq_pdb`, `loweq_entry` declassifying `L1PTable`, `L2PTable`, `Dispatcher.{entered,entrypoint}`).
  - `verified/secprop/conf_ni.i.dfy` L20–L55 (`lemma_conf_ni` excluding `KOM_SMC_STOP`).
  - `verified/secprop/integ_ni.i.dfy` L14–L49 (`lemma_enc_ni` excluding `KOM_SMC_STOP`).
- **`torvalds/linux`** at `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
  - `Documentation/arch/x86/tdx.rst` L192–L202 (`TEE_TCB_SVN_2` vs `TEE_TCB_SVN` on live module update), L267–L281 (first-gen TDX partial-write cacheline-poisoning erratum), L454–L466 (`#VE` re-entrancy blocking via `TDG.VP.VEINFO.GET`), L491–L555 (`set_memory_decrypted`/`encrypted`, `SWIOTLB`, `TDG.MR.REPORT` + QE quoting).
  - `arch/x86/coco/core.c` L31–L42 (`intel_cc_platform_has` enabling `CC_ATTR_GUEST_UNROLL_STRING_IO`, `CC_ATTR_GUEST_MEM_ENCRYPT`).
  - `arch/x86/coco/tdx/tdx.c` L131 (`TDG_MR_REPORT`), L371–L378 & L823–L843 (`tdx_handle_virt_exception` allow-listed `#VE` exit reasons), L781 (`TDG_VP_VEINFO_GET`).
  - `arch/x86/coco/sev/vc-handle.c` L134–L195 (`vc_decode_insn`), L390–L434 (`__vc_handle_msr`), L562–L635 (`vc_handle_mmio`).
- **`google/go-tdx-guest`** at `dd3f79297a6c6fbd308f1b4bc8ad93f39c2a3a14`:
  - `abi/abi.go` L30–L67, L196–L216, L269–L304 (Quote v4/v5 header `0x30`, `tdQuoteBodySize = 0x248` / `584`, TDX 1.5 `648`, `TeeTDX = 0x00000081`, `QuoteMinSize = 0x3FC`, `QuoteMinSizeV5 = 1026`).
  - `testing/testdata/tdx_prod_quote_SPR_E4.dat` (4,974 bytes, SHA-256 `6dde5548bec99147fef832643301f113df99931547be26df8ac376c4eaa5b5a7`).
  - `testing/testdata/quote_sample_v5.dat` (5,006 bytes, SHA-256 `cf77a6e91e48291d5d338c5f3b5d0674225a4d13e7d83ff5e537a4914bf22e1d`).
- **`google/go-sev-guest`** at `64934b575821b47a27a370ffbb23664897408382`:
  - `abi/abi.go` L43–L155, L220–L260 (`ReportSize = 0x4A0`, `signatureOffset = 0x2A0`, `SnpPolicy` bits 16–25 including `CipherTextHidingDRAM` bit 24 and `PageSwapDisable` bit 25, `VcekGUID`/`VlekGUID`, `ReportVersion2..5`, AMD Publications #56860 and #56421).
- **`TF-RMM/tf-rmm`** at `8d7961df074f08fd83a2460ab3a2ca0b658fde92`:
  - `lib/smc/include/smc-rmi.h` L417 (`SMC_RMI_REALM_CREATE`), L455 (`SMC_RMI_REC_ENTER`), L961–L971 (`SMC_RMI_GRANULE_RANGE_DELEGATE`/`UNDELEGATE`).
  - `lib/smc/include/smc-rsi.h` L107–L139 (`SMC_RSI_MEASUREMENT_READ` indices 0..4, `SMC_RSI_MEASUREMENT_EXTEND` indices 1..4 FID `0xC4000193`).
- **`project-oak/transparent-release`** at `dd29c625ef9426d9a2be9f7448ecefb8f65fc2c5`:
  - `docs/claim-transparency.md` L25–L90 (in-toto v0.1 Statement, `schema/claim/v1`, `validity.{notBefore, notAfter}` passive revocation).

### Verified Standards and Peer-Reviewed Literature (`Basis: normative | documentation`)

- IETF `RFC 9334` (Birkholz, Thaler, Richardson, Smith, Pan, Jan 2023) — *Remote ATtestation procedureS (RATS) Architecture*.
- IETF `RFC 9711` (Lundblade, Mandyam, O'Donoghue, Wallace, Apr 2025) — *The Entity Attestation Token (EAT)*.
- Checkoway & Shacham (ASPLOS 2013) — *Iago Attacks: Why the System Call API is a Bad Untrusted RPC Interface*.
- Cui, Zhao, Lie (NDSS 2021) — *Emilia: Catching Iago in Legacy Code*.
- Van Bulck, Oswald, Marin, Aldoseri, Garcia, Piessens (ACM CCS 2019, `10.1145/3319535.3363206`) — *A Tale of Two Worlds: Assessing the Vulnerability of Enclave Shielding Runtimes*.
- Alder, Van Bulck, Oswald, Piessens (ACSAC 2020) — *Faulty Point Unit: ABI Poisoning Attacks on Intel SGX*.
- Xu, Cui, Peinado (IEEE S&P 2015, `10.1109/SP.2015.45`) — *Controlled-Channel Attacks: Deterministic Side Channels for Untrusted Operating Systems*.
- Constable et al. (USENIX Security 2023) — *AEX-Notify: Thwarting Precise Single-Stepping Attacks through Interrupt Awareness for Intel SGX Enclaves*.
- Li et al. (USENIX Security 2021) — *CIPHERLEAKS*; Wichelmann et al. (USENIX Security 2023) — *Cipherfix*.
- Schlüter, Sridhara, Bertschi, Shinde (IEEE S&P 2024, `10.48550/arXiv.2404.03526`) — *WeSee*; Schlüter et al. (USENIX Security 2024) — *Heckler*; Zhang et al. (USENIX Security 2024) — *CacheWarp*.
- Hetzelt, Radev, Buhren, Morbitzer, Seifert (ACSAC 2021, `10.48550/arXiv.2109.10660`) — *VIA: Analyzing Device Interfaces of Protected Virtual Machines*.
- De Meulemeester et al. (IEEE S&P 2025, CVE-2024-21944) — *BadRAM*; De Meulemeester et al. (IEEE S&P 2026) — *Battering RAM*; Chuang et al. (2025) — *WireTap*; Chuang, Seto, Berrios, van Schaik, Garman, Genkin (IEEE S&P 2026, INTEL-2025-10-28-001) — *TEE.fail*.
- Ferraiuolo et al. (SOSP 2017, `10.1145/3132747.3132782`) — *Komodo*; Nelson et al. (SOSP 2019, `10.1145/3341301.3359641`) — *Serval*; Li et al. (OSDI 2022) & Fox et al. (OOPSLA 2023) — Arm CCA verification.
- Hawblitzel et al. (OSDI 2014) — *Ironclad Apps*; Sirer et al. (SOSP 2011) — *Logical Attestation*; Parno (HotSec 2008) — *Cuckoo Attack*; Knauth et al. (2018) — *RA-TLS*; Sardar, Musaev, Fetzer (2021) — *Demystifying Attestation in Intel TDX via Formal Verification*.
- Parno et al. (IEEE S&P 2011) — *Memoir*; Matetic et al. (USENIX Security 2017) — *ROTE*; Angel et al. (OSDI 2023) — *Nimble*; Juffinger, Neela, Gruss (ACNS 2024) — *Not So Secure TSC*.
- Hunt et al. (OSDI 2016 / TOCS 2018 `10.1145/3177123`) — *Ryoan*; Shen et al. (ASPLOS 2020 `10.1145/3373376.3378469`) — *Occlum*; Gollamudi, Chong, Arden (IEEE CSF 2019 `10.1109/CSF.2019.00028`) — *DFLATE*; Oak et al. (IEEE CSF 2021 `10.1109/CSF51455.2021.00009`) — *JE*.

### Executable Micro-Probes (`Basis: execution`)

Environment: Python 3.13.15 on Linux x86-64. Reproducible standalone script (`/tmp/tee_probe.py`) operating on `tdx_prod_quote_SPR_E4.dat` and `quote_sample_v5.dat` fetched from `google/go-tdx-guest@dd3f79297a6c6fbd308f1b4bc8ad93f39c2a3a14/testing/testdata/`:

```python
import hashlib, hmac, struct
from pathlib import Path

def parse_tdx_quote(raw: bytes) -> dict:
    version, att_key_type, tee_type, qe_svn, pce_svn = struct.unpack_from("<HHIHH", raw, 0)
    off = 48
    if version == 4:
        body_type, body_size = None, 584
    elif version == 5:
        body_type, body_size = struct.unpack_from("<HI", raw, off)
        off += 6
    body = raw[off:off + body_size]; off += body_size
    signed_data_size = struct.unpack_from("<I", raw, off)[0]; off += 4
    out = {
        "version": version, "tee_type": f"0x{tee_type:08x}", "body_type": body_type,
        "body_size": body_size, "signed_data_size": signed_data_size,
        "trailing_bytes": len(raw) - (off + signed_data_size),
        "tee_tcb_svn": body[0:16].hex(), "td_attrs": f"0x{struct.unpack_from('<Q', body, 120)[0]:016x}",
        "mr_td": body[136:184].hex(), "rtmr0": body[328:376].hex(),
    }
    if body_size >= 648:
        out["tee_tcb_svn_2"] = body[584:600].hex()
    return out

# CIPHERLEAKS write-equality check on branchless constant-time swap:
def det_enc(key: bytes, paddr: int, pt16: bytes) -> bytes:
    return hmac.new(key, struct.pack("<Q", paddr) + pt16, hashlib.sha256).digest()[:16]

def ct_cswap_changed(bit: int, a0: bytes, b0: bytes) -> tuple[bool, bool]:
    k = b"HARDWARE-VM-KEY-32BYTES-FIXED!!!"
    mask = 0xFF if bit else 0x00
    c0 = (det_enc(k, 0x4000, a0), det_enc(k, 0x4010, b0))
    diff = bytes((x ^ y) & mask for x, y in zip(a0, b0))
    a1, b1 = bytes(x ^ d for x, d in zip(a0, diff)), bytes(y ^ d for y, d in zip(b0, diff))
    c1 = (det_enc(k, 0x4000, a1), det_enc(k, 0x4010, b1))
    return (c0[0] != c1[0], c0[1] != c1[1])
```

Observed output (`exit 0`):
```text
File: tdx_prod_quote_SPR_E4.dat (len=4974, sha256=6dde5548bec99147...)
  version: 4 | att_key_type: 2 | tee_type: 0x00000081 | body_size: 584 | signed_data_size: 4299 | trailing_bytes: 39
  tee_tcb_svn: 03000400000000000000000000000000 | td_attrs: 0x0000000040000000 | debug_bit: False
File: quote_sample_v5.dat (len=5006, sha256=cf77a6e91e48291d...)
  version: 5 | att_key_type: 2 | tee_type: 0x00000081 | body_type: 3 | body_size: 648 | signed_data_size: 4300 | trailing_bytes: 0
  tee_tcb_svn: 0b010400000000000000000000000000 | tee_tcb_svn_2: 0d010400000000000000000000000000
RTMR extend run 1 == run 2: True (bbde5aec640ac7f7b2769338b62ea039...)
Channel-binding check (honest endpoint): True | Channel-binding check (cuckoo relay): False
mmap check [benign_outside] -> accepted=True
mmap check [iago_inside_stack | iago_partial_overlap | iago_u64_wrap] -> accepted=False
CIPHERLEAKS ct_cswap(bit=0) ciphertext_changed=(False, False)
CIPHERLEAKS ct_cswap(bit=1) ciphertext_changed=(True, True)
```

## Revalidation

Use these narrow, low-cost checks to determine whether the findings still hold for newer revisions or target platforms:

1. **Gramine ABI entry sanitization:** Diff `pal/src/host/linux-sgx/enclave_entry.S` (around `fxrstor` / `g_xsave_reset_state`) and `enclave_ocalls.c` (`ocall_mmap_untrusted`) in `gramineproject/gramine` against commit `918e832b8ab4f583bc878ae33cb6b15dfd3e84a9` to check whether `XRSTOR` clearing of `YMM`/`ZMM`/AMX state has replaced `FXRSTOR` and whether any new OCALL omits `COPY_UNTRUSTED_VALUE`.
2. **TDX / SEV-SNP / Arm CCA wire formats and policy flags:** Diff `abi/abi.go` in `google/go-tdx-guest` and `google/go-sev-guest` and `lib/smc/include/smc-{rmi,rsi}.h` in `TF-RMM/tf-rmm` for new quote/report versions, new `SnpPolicy` bits (beyond bit 25), or new TDISP/TDX-Connect / SEV-TIO attestation claims, and re-run `/tmp/tee_probe.py` on newly added testdata specimens.
3. **Linux guest hardening surface:** Diff `Documentation/arch/x86/tdx.rst`, `arch/x86/coco/tdx/tdx.c` (`tdx_handle_virt_exception` switch cases), and `arch/x86/coco/sev/vc-handle.c` (`vc_decode_insn` / `vc_handle_*`) against commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to verify newly permitted `#VE`/`#VC` exit reasons, Restricted Injection support, or changes to `SWIOTLB` / `force_dma_unencrypted()`.
4. **Physical revocation & TCB half-life:** Re-check Intel Security Advisories (PCS TCB Info JSON) and AMD Security Bulletins (KDS VCEK/VLEK TCB status) whenever adopting a new CPU stepping or memory generation (DDR5/CXL) to verify whether physical interposition or transient-execution attacks have invalidated prior TCB SVNs.
5. **Five-link witness gap:** Re-check `project-oak/oak` and IETF RATS working-group drafts (`EAT` / `CoRIM`) for any standardized claim type binding machine-checked formal verification certificates to hardware measurements; closing the `unknown` boundary requires inspecting an end-to-end build + proof + measurement artifact covering every measured byte of a real CVM image.
