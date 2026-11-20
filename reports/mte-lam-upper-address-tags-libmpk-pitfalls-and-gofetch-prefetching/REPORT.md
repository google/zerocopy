# Hardware Upper-Address Tagging Contracts, MPK/PKU Isolation Pitfalls, and Data-Memory-Dependent Prefetcher Activation

## Summary

Three hardware contracts constrain any compiler, language runtime, or cryptographic verification stack that relies on upper-bit pointer tagging, intra-process protection-key sandboxing, or software-tagged secret representations:

1. **Upper 16 address bits (`[63:48]`) are hardware- and kernel-partitioned, not free software space.** On `AArch64` Linux (`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854`), `VA_BITS=48` with `TBI0=1`, `MTE`, and `PAC` leaves **only 4 free software bits (`[63:60]`)**: bits `[59:56]` belong to `MTE` logical tags, bit `55` selects `TTBR0`/`TTBR1`, and `[54:48]` (`GENMASK_ULL(54, vabits_actual)`) belong to `PAC` (shrinking to `[54:52]` = 3 bits when `VA_BITS=52`). On `x86-64` Linux, `LA57` 5-level paging consumes `[55:0]` for user virtual addresses (`[63:56] = 0xff` in kernel space, not `0xffff` across `[63:48]`), and mainline Linux `arch/x86/kernel/process_64.c:800-856` enables **only `LAM_U57` (`6` tag bits in `[62:57]`)**, rejecting `nr_bits > 6` with `-EINVAL` and reserving bit `63` for user/supervisor separation (blocking `AMD UAI`'s `[63:57]` mask). Consequently, any software-chosen 16-bit tag partition over `[63:48]` collides with `10–16` hardware-owned bits across mainstream Linux targets.
2. **User-space `MPK`/`PKU` domain switching costs `~11–26` serialized cycles per `WRPKRU` (`~20–23.3` cycles typical in `libmpk` / `ERIM`), scales to `3k–104k` cycles under cross-thread synchronization, and is bypassed by OS confused-deputy paths unless syscalls and signals are mediated.** Linux kernel source (`arch/x86/kernel/signal.c:73-79`, `arch/x86/kernel/fpu/signal.c:260-344,462-516`, `Documentation/core-api/protection-keys.rst:118-120`) directly confirms three structural `PKU` hazards: `sig_prepare_pkru()` executes `write_pkru(0)` (temporarily enabling all 16 keys) when building signal frames; `fpu__restore_sig()` executes `xrstor_from_user_sigframe()` restoring arbitrary user-written `PKRU` from `sigcontext`; and kernel threads (`io_uring`) ignore userspace `PKRU`. Direct source audit of `sslab-gatech/libmpk` at `a0c86673783643aa9e9045606cf7a35b30488bc6` further uncovers concrete implementation bugs in both its user library (`lib/mpt.cc:160,282,340`) and kernel module (`kernel/libmpk/libmpk.c:15-17,139-147`) alongside an explicit concurrent-`pkey_sync` race (`kernel/mm/mprotect.c:747-751`).
3. **Upper-byte tagging (`[63:56]`) does *not* suppress Apple Silicon Data-Memory-Dependent Prefetchers (`DMP`), while reserving upper 16 bits (`[63:48]`) inside cryptographic secret words incurs `1.47×–20.60×` measured arithmetic/SIMD slowdown and `+34.4%–50%` state bloat without providing a portable silicon guarantee.** In `FPSG-UIUC/gofetch` (`13e2533b930f1ece5f0cee4969c0f0f184f65854`, `re/tbi.sh`, `re/src/dmp.h:16`, `re/src/quick_check.c`), Apple's M1/M2/M3 `DMP` monitors L1 cache fills, fires on a single load without architectural pointer dereference, requires the pointer container and target to share bits `[55:32]` (`4 GiB` region), and **ignores bit flips in `[63:56]` (`TBI`)**. Only setting `PSTATE.DIT` suppresses the `DMP` in silicon—and only on Apple **M3** (not M1/M2). Reserving bits `[63:48]` (e.g., `0x5AA5`) breaks Apple's `[55:32]` region match for low user addresses, but on `AMD EPYC 7B12` (`gcc -O3 -march=native`) our direct microbenchmark measures **`4.02×`** slowdown on 256-bit multi-limb multiplication (`6×48`-bit vs. `4×64`-bit, `+50%` RAM), **`20.60×`** slowdown on packed `int16_t` Kyber NTT layers (`AVX2` vs. `3×16`-bit-per-`u64` repack, `+34.4%` RAM), and **`1.47×`** slowdown on `AES-NI` 10-round encryption (`+50%` round-key RAM), while remaining vulnerable to page-walk side channels (`Peek-a-Walk`) when microarchitectures attempt translation before discarding non-canonical upper bits.

## Applicability

These findings apply to 64-bit user-space and kernel-adjacent systems software, compilers, sandboxes, and constant-time cryptographic libraries targeting:

- **`AArch64` (`Armv8.0-A` through `Armv8.7-A+` / Apple M1–M3)** under Linux (`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854`), Android/SysV ELF toolchains conforming to `ARM-software/abi-aa` (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`, `2026Q3` issue dated 3 November 2026), and macOS `arm64`/`arm64e` (as probed by `FPSG-UIUC/augury` at `e38f7232e579c071f195fb4320fc013c7a56e443` and `FPSG-UIUC/gofetch` at `13e2533b930f1ece5f0cee4969c0f0f184f65854`).
- **`x86-64`** under Linux (`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854`) across 4-level paging (`48`-bit VA), `LA57` 5-level paging (`57`-bit VA), Intel `LAM` (`LAM_U48` hardware spec vs. Linux `LAM_U57` ABI), AMD `UAI`, Intel `MPK`/`PKU` (Skylake-SP/Tiger Lake through Sapphire Rapids), AMD `PKU` (Zen 4+), and the `sslab-gatech/libmpk` virtualization prototype (`a0c86673783643aa9e9045606cf7a35b30488bc6`).

**Relationships among examined subjects:**
- `torvalds/linux` and `ARM-software/abi-aa` are analyzed jointly as the authoritative OS-kernel and ELF-toolchain contracts governing upper-address bit allocation (`TBI`, `MTE`, `PAC`, `LA57`, `LAM_U57`) and protection-key transitions (`PKRU` signal frames, `FEAT_S1POE`).
- `sslab-gatech/libmpk` is evaluated against Park et al. (USENIX ATC 2019), Connor et al. (USENIX Security 2020), and modern `torvalds/linux` `PKRU` signal/kthread code to separate architectural `WRPKRU` costs from OS-boundary bypasses and prototype bugs.
- `FPSG-UIUC/augury` and `FPSG-UIUC/gofetch` (with Vicarte et al. IEEE S&P 2022 and Chen et al. USENIX Security 2024) establish silicon `DMP` activation rules on Apple M1–M3 and contrast them with Intel Raptor Lake's `DDP`, while an explicit host-side C/AVX2/AES-NI microbenchmark on `AMD EPYC 7B12` quantifies the software representation cost of reserving upper 16 bits in cryptographic arithmetic limbs (explicitly distinguished from silicon `DMP` tests).

## Findings

### 1. Architectural Upper-Address Bit Layouts and ABI Collisions

`Basis: normative + source + execution (bit-layout audit)`

Software designs that claim a uniform 16-bit tag space in bits `[63:48]`—for example, partitioning the `65,536` values of bits `[63:48]` across pointer authentication, memory tags, kernel pointers (`0xFFFF`), MMIO tags, and secret tags (`0x5AA5`)—fail against real hardware bit assignments on both `AArch64` and `x86-64`. Hardware decoders fix the bit indices of virtual addresses, sign/translation-table selectors, memory tags, and authentication codes independently of compiler choices.

| Architecture / OS Configuration | Live VA Bits | HW Tag / PAC / Select Bits in `[63:48]` | Free SW Bits in `[63:48]` | Colliding Bits with Arbitrary `High16` | Primary Source Reference |
| :--- | :--- | :--- | :---: | :---: | :--- |
| `AArch64` Linux `VA48` + `TBI0=1` + `MTE` + `PAC` (EL0) | `[47:0]` | `[54:48]` `PAC` (`7` b), `[55]` `TTBR0/1`, `[59:56]` `MTE` (`4` b) | `4` (`[63:60]`) | `12` | `torvalds/linux` `arch/arm64/include/asm/pointer_auth.h:17`, `Documentation/arch/arm64/memory-tagging-extension.rst:21` |
| `AArch64` Linux `VA52` + `TBI0=1` + `MTE` + `PAC` (EL0) | `[51:0]` | `[51:48]` VA (`4` b), `[54:52]` `PAC` (`3` b), `[55]` `TTBR0/1`, `[59:56]` `MTE` (`4` b) | `4` (`[63:60]`) | `12` | `torvalds/linux` `arch/arm64/include/asm/pointer_auth.h:17`, `Documentation/arch/arm64/pointer-authentication.rst:52-54` |
| `AArch64` `VA48` + `TBI0=0` + `PAC` (EL0/EL1) | `[47:0]` | `[54:48]` ∪ `[63:56]` `PAC` (`15` b), `[55]` `TTBR0/1` | `0` | `16` | `torvalds/linux` `arch/arm64/include/asm/pointer_auth.h:15-18` |
| `x86-64` 4-level paging (no `LAM`/`UAI`) | `[47:0]` | `[63:48]` canonical sign extension of bit `47` | `0` | `16` | `torvalds/linux` `Documentation/arch/x86/x86_64/5level-paging.rst:9-11` |
| `x86-64` `LA57` 5-level paging (no `LAM`/`UAI`) | `[55:0]` user (`[56]` sign) | `[55:48]` live VA (`8` b), `[56]` canonical sign, `[63:57]` sign-ext | `0` | `16` | `torvalds/linux` `Documentation/arch/x86/x86_64/5level-paging.rst:15-35` |
| `x86-64` Intel `LAM_U48` (hardware spec only; **not** Linux ABI) | `[47:0]` | `[63]` user/kernel discriminator (`0` = user, `1` = supervisor) | `15` (`[62:48]`) | `1` | `torvalds/linux` `arch/x86/include/asm/mmu.h:52` (comment only; disabled in `process_64.c`) |
| `x86-64` Intel `LAM_U57` (**only** Linux mainline LAM ABI) | `[56:0]` (`LA57` compatible) | `[56:48]` live VA/sign (`9` b), `[63]` user/kernel bit | `6` (`[62:57]`) | `10` | `torvalds/linux` `arch/x86/kernel/process_64.c:800,816-817,853-856,964-969` |
| `x86-64` AMD `UAI` (hardware spec; unmerged in Linux) | `[56:0]` | `[56:48]` live VA/sign (`9` b); masks `[63:57]` **including bit 63** | `7` (`[63:57]`) | `9` | AMD APM (`EFER.UAIE` bit 20); overlaps kernel bit `63` |

#### 1.1 AArch64 Linux `TBI`, `MTE`, `PAC`, and ELF Relocation Contracts

`Basis: normative + source`

- **Exact `PAC` bit mask (`torvalds/linux` `arch/arm64/include/asm/pointer_auth.h:17-18`):**
  ```c
  #define ptrauth_user_pac_mask()    GENMASK_ULL(54, vabits_actual)
  #define ptrauth_kernel_pac_mask()  GENMASK_ULL(63, vabits_actual)
  ```
  Under `TBI0=1`, `PAC` occupies `55 - VA_BITS` contiguous bits immediately below bit `55` (`7` bits `[54:48]` at `VA_BITS=48`; `3` bits `[54:52]` at `VA_BITS=52`). Bit `55` is never touched by `PAC` because it selects `TTBR0_EL1` (user) vs. `TTBR1_EL1` (kernel). Because `PAC` bits are pseudorandom outputs of `QARMA`/`PACGA` over `(ptr, modifier, 128-bit key)`, signed user pointers span **all** `2^(55 - VA_BITS)` bit patterns in `[54:VA_BITS]` and cannot be confined to a reserved software sub-range (such as `0x1000..0x1FFF`).
- **AArch64 Tagged Address Syscall ABI (`Documentation/arch/arm64/tagged-address-abi.rst:25-134`):** Even though `TCR_EL1.TBI0=1` permits EL0 loads/stores with non-zero `[63:56]`, kernel syscalls reject tagged user buffers by default until the thread opts in via `prctl(PR_SET_TAGGED_ADDR_CTRL, PR_TAGGED_ADDR_ENABLE, 0, 0, 0)` (inherited on `fork`/`clone`, cleared on `exec`, disableable globally via `sysctl abi.tagged_addr_disabled=1`). Even with the ABI enabled, **`brk()`, `mmap()`, `mremap()` (`new_address`), `shmat()`, `shmdt()`, and `UFFDIO_*` `ioctl` ranges MUST remain untagged** (lines `50-65, 115-131`).
- **Memory Tagging Extension (`Documentation/arch/arm64/memory-tagging-extension.rst:16-248` and `arch/arm64/include/asm/mte.h:225-243`):**
  - `MTE` assigns a 4-bit allocation tag to each 16-byte physical tag granule (`PROT_MTE` on `MAP_ANONYMOUS`, `tmpfs`, or `memfd` only; cannot be cleared by `mprotect()`). The logical tag occupies bits `[59:56]`—the lower nibble of the TBI top byte—leaving only `[63:60]` free for software tags.
  - Fault modes are `PR_MTE_TCF_NONE`, `PR_MTE_TCF_SYNC` (`SIGSEGV`/`SEGV_MTESERR` with exact `.si_addr`), `PR_MTE_TCF_ASYNC` (`SEGV_MTEAERR`, `.si_addr = 0`), and Armv8.7 Asymmetric (sync reads, async writes). Notably, `PSTATE.TCO = 1` disables tag checking for a user thread, **signal handlers always start with `PSTATE.TCO = 0`**, and kernel `uaccess` (e.g., `read()`/`write()`) **skips tag checks in `NONE` and `ASYNC` modes** and provides only best-effort checking in `SYNC` mode (lines `101-118`; `mte.h:230-243`).
  - Core dumps emit `PT_AARCH64_MEMTAG_MTE` segments sized `p_memsz / 32` (`128 B` per `4 KiB` page, two 4-bit tags per byte, lines `229-247`).
- **ELF Toolchain Contracts for `PAuthABI` and `MemtagABI` (`ARM-software/abi-aa` at `9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`, issue `2026Q3`):**
  - **`pauthabielf64.rst:645-761, 912-925, 1245-1297`:** Relocations encode a 32-bit signing schema in the upper half of `*P` (`bit 63`: address diversity; `bits 61:60`: key `APIA=0b00`, `APIB=0b01`, `APDA=0b10`, `APDB=0b11`; `bits 47:32`: 16-bit discriminator; `bits 31:0`: addend or Memtag addend correction). Key dynamic relocations are `R_AARCH64_AUTH_ABS64` (`0x244`/`580`), `R_AARCH64_AUTH_RELATIVE` (`0x411`/`1041`), `R_AARCH64_AUTH_GLOB_DAT` (`0x412`/`1042`), `R_AARCH64_AUTH_TLSDESC` (`0x413`/`1043`), and `R_AARCH64_AUTH_IRELATIVE` (`0x414`/`1044`), gated by `.note.gnu.property` `GNU_PROPERTY_AARCH64_FEATURE_PAUTH` (`0xc0000001`). `R_AARCH64_COPY` and traditional TLS (`-mtls-dialect=traditional`) are forbidden (`lines 470-480`).
  - **`memtagabielf64.rst:375-405, 485-542, 558-717`:** Tagged globals must be 16-byte size- and alignment-rounded and accessed exclusively via GOT (PC-relative references from non-Memtag assembly fail with tag faults; linkers conservatively untag mismatched declarations). Global descriptors compress into `SHT_AARCH64_MEMTAG_GLOBALS_DYNAMIC` (`0x70000008`) as ULEB128 granule deltas packing sizes `< 8` granules into the low 3 bits. A documented ABI erratum (`lines 389-405`) warns that binaries shipped on Android via `clang-17`/`lld-17` inverted the ELF dynamic-tag even/odd `d_ptr`/`d_val` convention: `DT_AARCH64_MEMTAG_STACK` (`0x7000000c`, even) is `d_val` (must *not* receive load-bias relocation), whereas `DT_AARCH64_MEMTAG_GLOBALS` (`0x7000000d`, odd) is `d_ptr`. Out-of-bounds global initializers (e.g., `&foo[32]`) store a negative tag-derivation offset in `*P` (`LDG(Delta + A + *P) - *P`), which disables `SHT_RELR` compression and forces zero-initialized `.bss` globals into `.data`.
  - **Combined `PAuthABI + MemtagABI` ordering (`pauthabielf64.rst:1257-1296`):** The dynamic linker **must materialize the `MTE` logical tag via `LDG` before signing the pointer with `PAC`**: `SIGN(LDG(S) + A, SCHEMA(*P))` for `AUTH_ABS64`/`AUTH_GLOB_DAT` and `SIGN(LDG(Delta + A + ADDEND(*P)) - ADDEND(*P), SCHEMA(*P))` for `AUTH_RELATIVE`. Reversing the order fails because `LDG` overwrites bits `[59:56]` while `AddPAC` computes its MAC over bits `[55:0]` (or `[63:0]` under `TBI=0`) and preserves `[63:56]` under `TBI=1`.

#### 1.2 x86-64 `LA57`, Intel `LAM_U57`, and AMD `UAI` Constraints

`Basis: normative + source`

- **`LA57` 5-level paging (`Documentation/arch/x86/x86_64/5level-paging.rst:15-49`):** Expands virtual address space from `256 TiB` (`48` bits) to `128 PiB` (`57` bits; `56`-bit user VA `[55:0]`, `4 PiB` PA). Kernel canonical addresses occupy `0xff00000000000000`–`0xffffffffffffffff` (bits `[63:56] = 0xff`), refuting any invariant assuming kernel pointers always have `0xffff` in `[63:48]`. Linux defaults `mmap()` below `2^47` unless userspace passes a hint above 47 bits explicitly because legacy JITs pack tags in `[63:48]`.
- **Mainline Linux `LAM` restricts userspace strictly to `LAM_U57` (`6` bits, `[62:57]`) (`arch/x86/kernel/process_64.c:798-864, 953-969`):**
  ```c
  #define LAM_U57_BITS 6
  ...
  mm->context.lam_cr3_mask = X86_CR3_LAM_U57;
  mm->context.untag_mask = ~GENMASK(62, 57); // 0x81ffffffffffffff
  ```
  - `arch_prctl(ARCH_GET_MAX_TAG_BITS, &bits)` returns `6` (`LAM_U57_BITS`), never `15` (`LAM_U48`), even on 4-level paging kernels (`lines 964-969`).
  - `arch_prctl(ARCH_ENABLE_TAGGED_ADDR, nr_bits)` returns `-EINVAL` if `nr_bits == 0 || nr_bits > 6` (`lines 853-856`), `-EBUSY` if any thread has already been spawned (`MM_CONTEXT_LOCK_LAM` set on `clone()`, `lines 844-851`), and `-EINVAL` if Shared Virtual Addressing (`PASID`) is active without prior `ARCH_FORCE_TAGGED_SVA` (`lines 837-839`).
  - Enabling `LAM` triggers a synchronous cross-CPU IPI (`on_each_cpu_mask(mm_cpumask(mm), enable_lam_func, mm, true)`, `line 824`) to rewrite `CR3 | X86_CR3_LAM_U57` on any kernel threads sharing `mm`.
- **Intel `LAM` vs. AMD `UAI` security split:** Intel `LAM` explicitly leaves bit `63` unmasked so hardware distinguishes user (`bit 63 == 0`) from supervisor (`bit 63 == 1`) pointers. AMD `UAI` (`EFER.UAIE`) masks bits `[63:57]` including bit `63`, creating user/kernel canonical-address confusion risks in kernel `access_ok()` / `untagged_addr()` paths and preventing drop-in Linux ABI parity.

---

### 2. `MPK`/`PKU` Domain-Switch Costs, Thread Synchronization, and Kernel Confused-Deputy Pitfalls

`Basis: normative + source + documentation`

#### 2.1 Hardware `WRPKRU` Serialization Latency vs. Multi-Thread `pkey_sync`

`x86-64` `PKU` dedicates 4 PTE bits (`16` keys, key `0` default-allowed) governed by the thread-local 32-bit `PKRU` register (`2` bits per key: `AD` access-disable, `WD` write-disable; data accesses only—never instruction fetch). On `AArch64`, Linux (`Documentation/core-api/protection-keys.rst:34-49`) additionally supports `FEAT_S1POE` (3 PTE bits = `8` keys, 64-bit `POR_EL0`, enforcing read, write, **and execute** overlays).

| Operation / Isolation Primitive | Published / In-Source Measured Cost | Scope & Serialization Semantics | Source Basis |
| :--- | :--- | :--- | :--- |
| `RDPKRU` (read `PKRU`) | `~1–3` cycles (GPR-class) | Non-serializing, thread-local | Park et al. (ATC '19); `libmpk` `lib/headers/pkey.h:34-40` |
| `WRPKRU` (single switch, Intel Skylake–Sapphire Rapids / AMD Zen 4) | **`~11–26` cycles** (`20–23.3` cycles typical in `libmpk`; `11–260` cycles in `ERIM` depending on pipeline drain) | Non-speculative; blocks all subsequent `PKRU`-governed loads/stores until `PKRU` commits | Intel SDM (`WRPKRU`); Park et al. (ATC '19); Vahldiek-Oberwagner et al. (`ERIM`, USENIX Sec '19) |
| Round-trip domain call (`WRPKRU` enter + `WRPKRU` exit) | **`~40–60+` cycles** (`~15–25 ns` at `2.5–3.0 GHz`) before register scrubbing | Two serialized `WRPKRU` barriers + caller/callee stack swap & state clearing | Derived from Intel SDM + Park et al. (ATC '19) |
| `mprotect()` syscall (1 page, single-thread / multi-core TLB shootdown) | `~1,094` cycles (single-core) to `>10,000` cycles (cross-core TLB shootdown IPIs) | Process-wide page-table + TLB invalidation | Park et al. (ATC '19) |
| `libmpk` `sys_pkey_sync` (`2` threads / `1` remote hook) | `~1 µs` (`~3,000` cycles) | `task_work_add` + `TIF_NOTIFY_RESUME` + `smp_call_function_many` IPI | `sslab-gatech/libmpk` `kernel/mm/mprotect.c:765,891-916` |
| `libmpk` `sys_pkey_sync` (`11` threads / `10` hooks) | `~6 µs` (`~15,000` cycles) | Linear in thread count + cross-CPU IPI wait | `sslab-gatech/libmpk` `kernel/mm/mprotect.c:766` |
| `libmpk` `sys_pkey_sync` (`101` threads / `100` hooks) | `~43 µs` (`~104,000` cycles) | Linear in thread count + cross-CPU IPI wait; **racy under concurrent callers** | `sslab-gatech/libmpk` `kernel/mm/mprotect.c:747-751,767` |

**Key refutation of single-digit-cycle claims:** Claims that an `MPK` domain portal costs `3–4` cycles confuse `RDPKRU` or a register move with `WRPKRU`. Because the Intel SDM forbids speculative execution of `WRPKRU` and stalls all subsequent `PKRU`-checked memory operations until `PKRU` updates, a single transition requires `~11–26` cycles (typically `~20–23` cycles), and a full bidirectional call-and-return portal requires at least two `WRPKRU` instructions (`~40–50+` cycles before ABI register/XMM sanitization). Furthermore, `PKRU` is **strictly thread-local**: updating permissions process-wide (as `libmpk` requires when virtualizing keys across threads) demands kernel IPIs (`3,000–104,000` cycles).

#### 2.2 Linux Kernel `PKRU` Signal-Frame & Confused-Deputy Bypasses (`PKU Pitfalls`)

`Basis: source + documentation`

Connor et al. (USENIX Security 2020, *"PKU Pitfalls"*) demonstrated that `PKU` enforces permissions only on direct user-mode data accesses under the current thread's `PKRU`, while the OS kernel treats the entire process as a single trust domain. Direct inspection of `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854` confirms these exact mechanisms remain architectural features of Linux:

1. **Signal-delivery temporary full-unlock (`arch/x86/kernel/signal.c:63-79, 160-170`):**
   ```c
   static inline u32 sig_prepare_pkru(void) {
       u32 orig_pkru = read_pkru();
       write_pkru(0); // Enable ALL 16 pkeys to write sigframe onto current or altstack
       return orig_pkru;
   }
   ```
   When delivering a signal, the kernel temporarily sets `PKRU = 0` (all keys readable/writable) so `copy_fpstate_to_sigframe()` can push the signal frame onto the thread stack or `sigaltstack`, and only afterward resets `PKRU` to `init_pkru_value` (`0x55555554`, `arch/x86/mm/pkeys.c:120-127`) via `fpu__clear_user_states()` (`signal.c:310`). If an untrusted domain can register `sigaltstack()` pointing into a `PKU`-protected page (or modify `RSP` before triggering a synchronous fault), the kernel writes controlled sigframe bytes over protected memory while `PKRU == 0`.
2. **Signal-return `XRSTOR` `PKRU` forge (`arch/x86/kernel/fpu/signal.c:260-303, 462-516`):** `rt_sigreturn` invokes `fpu__restore_sig()`, which executes `xrstor_from_user_sigframe(buf, xrestore_mask)` directly from user-writable memory. Even if static binary verification (`ERIM`/`Jenny`) eliminates every `0f 01 ef` (`WRPKRU`) byte sequence in untrusted executable pages—and blocks `mprotect`/`mmap` code injection—an untrusted thread that can invoke `rt_sigreturn` (syscall `15` on `x86-64`) overwrites `PKRU` to `0x00000000` via the kernel's own `XRSTOR`.
3. **Kernel-thread `PKRU` bypass (`Documentation/core-api/protection-keys.rst:118-120`):** Linux explicitly documents that asynchronous kernel worker threads (specifically `io_uring` `io-wq` threads) execute user-memory copies with the kernel's default `PKRU` rather than the submitting user thread's `PKRU`—allowing an untrusted domain to read/write protected pages by submitting `io_uring` read/write requests.
4. **Additional `PKU Pitfalls` syscall confused deputies (Connor et al. 2020):** `/proc/self/mem` (`open` + `pread`/`pwrite` bypasses page-table/PKU checks via `access_remote_vm` / `FOLL_FORCE`), `process_vm_readv`/`process_vm_writev`, `ptrace`, `pkey_mprotect` (reassigning a protected VMA back to pkey `0`), `mremap` (aliasing protected pages), `userfaultfd`, and `seccomp`-unfiltered `fork`/`clone` (inheriting or racing key state). Closing these requires interposing **all** memory-, signal-, procfs-, and `io_uring`-related syscalls (as later engineered in *Jenny*, USENIX Security 2022), adding substantial syscall-filtering overhead (`seccomp-BPF` / binary rewriting / `SYS_USER_DISPATCH`) and non-trivial kernel/monitor complexity.
5. **Unaligned instruction-stream `WRPKRU` gadgets:** On variable-length `x86-64`, the 3-byte opcode `0f 01 ef` (`WRPKRU`) can appear accidentally across instruction boundaries or immediate operands unless the binary scanner/rewriter verifies every byte offset (and blocks `XRSTOR` `0f ae /5` too!).

#### 2.3 Direct Source Audit of `sslab-gatech/libmpk` (`a0c86673783643aa9e9045606cf7a35b30488bc6`)

`Basis: source`

Inspecting `sslab-gatech/libmpk` at its pinned revision exposes five concrete correctness and memory-safety defects in the published artifact (illustrative of the complexity of virtualizing 15 hardware keys across threads and kernel metadata):

| File & Line | Upstream Code Excerpt | Technical Defect & Impact |
| :--- | :--- | :--- |
| `lib/mpt.cc:160` | `if((pkey_indomain_map &= (1 << i)))` | Bitwise assignment `&=` instead of `&`: **silently clears every other active in-domain bit** in `pkey_indomain_map`, allowing `mpt_find()` to evict a physical key currently held open by a concurrent active domain. |
| `lib/mpt.cc:282` | `if (((mn_prot \| PROT_EXEC) && !(prot \| PROT_EXEC)) \|\| (!(mn_prot \| PROT_EXEC) && (prot \| PROT_EXEC)))` | Bitwise OR `\|` instead of `&`: since `PROT_EXEC == 0x4 != 0`, `!(prot \| PROT_EXEC)` is identically `0`; the entire `syscall(339)` exec-transition branch is **dead code**. |
| `lib/mpt.cc:340` | `pkey_indomain_map \|= (1 << mn->pkey);` | Executed in `mpt_begin()` **before** `do_mpt_mprotect()` assigns a physical key; on first entry `mn->pkey == -1`, invoking C++ **undefined behavior** (`1 << -1`). |
| `kernel/libmpk/libmpk.c:15-17` | `memset(mn, 0, sizeof(mpt_node)); pkey_arr[mn->pkey] = -1;` | Zeroes `mn->pkey` to `0` *before* indexing `pkey_arr[mn->pkey]`, clobbering `pkey_arr[0]` instead of releasing the old hardware key slot (`pkey_arr[old_pkey]`). |
| `kernel/libmpk/libmpk.c:139-147` | `table = kzalloc(TABLE_SIZE * sizeof(HashEntry), GFP_KERNEL); ... mmap_table = (HashEntry *)(table + 0x1000); for (i = 0; i < TABLE_SIZE; i++) mmap_table[i].key = -1;` | Shifts `mmap_table` forward by `0x1000` bytes without adding `0x1000` to the `kzalloc` size, causing a **`4 KiB` kernel heap out-of-bounds write** during initialization! |
| `kernel/mm/mprotect.c:747-751` | *"Unhandled corner case: The current implementation may not handle the synchronization correctly if more than one threads initiates the synchronization at the same time."* | Documented upstream concurrency race in `do_pkey_sync()`: `task_work_cancel` + `init_task_work` + `task_work_add` on shared `p->pkru_callback_head` without synchronization corrupts kernel task-work lists if two threads call `pkey_sync()` concurrently. |

---

### 3. Silicon Data-Memory-Dependent Prefetchers (`Augury`, `GoFetch`) and Cryptographic Tagging Costs

`Basis: source + documentation + execution (host microbenchmark)`

#### 3.1 Verified Silicon Activation Criteria on Apple M1/M2/M3 vs. Intel Raptor Lake

Direct inspection of `FPSG-UIUC/augury` (`e38f7232e579c071f195fb4320fc013c7a56e443`) and `FPSG-UIUC/gofetch` (`13e2533b930f1ece5f0cee4969c0f0f184f65854`) establishes the exact microarchitectural activation rules of Apple's `DMP`:

- **Single-load, zero-dereference trigger (`gofetch/README.md:62-66`, `re/src/no_deref.c`):** Unlike the original `Augury` model (`augury.c:65-67`, which assumed an Array-of-Pointers dereference loop `*aop[i]`), `GoFetch` proved that Apple's `DMP` activates on **a single architectural load** (`noderef.sh 8 8 0 1`) with **zero pointer dereferences in the program**—scanning all 8 aligned 64-bit words in the fetched `64 B` L1 cache line (`re/src/lib/basics/arch.h:18`, `L1_LINE_SIZE = 64`, `L2_LINE_SIZE = 128`, `PAGE_SIZE = 16 KiB`).
- **L1 cache fill & Do-Not-Scan hint (`gofetch/README.md:71-73`, `re/src/l2l1_fetch.c`):** The `DMP` scans words brought into the L1 data cache on fills from DRAM/L2, unless the line carries a "do-not-scan" metadata hint set when a line was previously evicted from L1→L2. Evicting the victim buffer out of L2 (via L2 eviction sets, `12`-way `12 MiB` on M1; `16`-way `16 MiB` on M2/M3, `arch.h:12-25`) clears that hint and re-arms the `DMP`.
- **4 GiB region filter (`gofetch/re/src/dmp.h:16`, `re/src/addr_sweep.c`):**
  ```c
  #define ADDR_CHECK(addr1, addr2) ((addr1 >> 32) == (addr2 >> 32))
  ```
  The `DMP` dereferences a candidate 64-bit value `v` stored at container address `a` only if `(v >> 32) == (a >> 32)` (after top-byte ignoring)—meaning bits `[55:32]` of the candidate word must match bits `[55:32]` of the containing line's virtual address (the same aligned `4 GiB` VA region).
- **Top-Byte Ignore (`TBI`) pass-through (`gofetch/re/tbi.sh:14`, `re/src/no_deref.c:93-124`, `README.md:78`):** `tbi.sh` sweeps single-bit flips across bits `48..63` (`for bit_flip_position in {48..63}`). Setting **any bit in `[63:56]` does NOT suppress Apple's `DMP`** because the prefetcher strips the top byte per `AArch64` `TBI`. Flipping any bit in `[55:48]` *does* suppress Apple's M1/M2/M3 `DMP` when the container resides in a standard low user region (`bits [55:48] == 0x00`), because bits `[55:32]` no longer match the container's `4 GiB` prefix.
- **`FEAT_DIT` (`PSTATE.DIT`) hardware kill switch (`gofetch/re/src/quick_check.c:19-60`):** Enabling `DIT` (`__builtin_arm_wsr64("DIT", 1)`, bit 24) **disables the `DMP` on Apple M3**, yielding zero `DMP` signal, **but has NO effect on Apple M1 or M2** (leaving M1/M2 unpatchable in microcode and requiring algorithmic blinding or running constant-time code on `Icestorm` efficiency cores, which lack the Firestorm/Avalanche/Everest `DMP`).
- **End-to-end breaks of constant-time cryptography (`gofetch/poc/crypto_attacker/examples/`):** Using chosen-input mixtures that form a secret-dependent valid pointer inside the victim's `4 GiB` VA slice (plus `Prime+Probe` L2 eviction sets), `GoFetch` extracts full secret keys from constant-time **OpenSSL Diffie-Hellman** (windowed exponentiation), **Go RSA-CRT** (`c mod p`), **CRYSTALS-Kyber / ML-KEM** (leaking the Fujisaki-Okamoto intermediate mismatch buffer `KYBER_SYMBYTES = 32` bytes treated as `4` `u64` words in `kyber_attacker.rs:32-50`), and **CRYSTALS-Dilithium / ML-DSA** (`z = y + c·s1`, leaking nonce `y` for lattice reduction in `dilithium_attacker.rs:112-140`).
- **Intel Raptor Lake `DDP` and Page-Walk Side Channels (`Peek-a-Walk`):** Intel 13th/14th-Gen Raptor Lake implements a more restrictive Data-Dependent Prefetcher (`DDP`) that requires explicit stride/pointer-chasing training and does not cross privilege rings, blocking naive `GoFetch` single-load exploits (Chen et al. 2024; Intel DDP security guidance). However, follow-up work (*Peek-a-Walk*, 2024) demonstrated that even **invalid / non-mapped pointer patterns** can trigger hardware page-table walks (`PWSC`) when evaluated by pointer-chasing prefetchers, and Intel `LAM` explicitly masks `[62:57]`/`[62:48]`—meaning software tag bits placed in `LAM`-masked positions would be *ignored* by a `LAM`-aware `DMP` just as Apple's `DMP` ignores `TBI` `[63:56]`!

#### 3.2 Measured Software Representation Cost of Tagging Secret Limbs (`0x5AA5` in `[63:48]`)

`Basis: execution (host microbenchmark on AMD EPYC 7B12, gcc -O3 -march=native; measures arithmetic/memory cost, not silicon DMP activation)`

A common software defense proposal—inspired by Apple's `[55:32]` region check—is to reserve the top 16 bits (`[63:48]`, e.g. constant `0x5AA5`) of every 64-bit word holding cryptographic secrets so that no aligned 64-bit word in memory can match a low canonical virtual address. While `0x5AA5` in `[63:48]` does mismatch bits `[55:48]` of `0x0000_0001_xxxx_xxxx` on Apple M1/M2 (verified in our bit-filter check: `DMP_region_match = False`, whereas `TBI`-only `0x5A << 56` gives `DMP_region_match = True`), **it is NOT zero-cost**. Reserving 16 bits per 64-bit word breaks native 64×64→128 multipliers (`mulx`/`umulh`), 16-bit packed SIMD NTT lanes (`AVX2`/`NEON`), and 128-bit hardware AES registers (`AES-NI`/`ARMv8 Crypto`).

Direct 5-run median measurement on `AMD EPYC 7B12` (`8` logical cores, `AVX2` + `AES-NI`, `gcc -Wall -Wextra -O3 -march=native`, `N = 2,000,000` iterations per run):

| Cryptographic Kernel | Native Dense Layout | Tagged `0x5AA5` `[63:48]` Layout | Native Median (ns/op) | Tagged Median (ns/op) | Median Slowdown (5-Run Range) | State Memory Overhead |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: |
| **256-bit schoolbook multiply** (RSA/DH/ECC building block) | `4 × u64` limbs (`32 B` operand; `16` `u64×u64` products) | `6 × 48`-bit payload in `u64` (`48 B` operand; `36` products + mask/retag) | `15.10 ns` | `60.73 ns` | **`4.02×`** (`2.97×–4.33×`) | **`+50.0%`** (`48 B` vs. `32 B`) |
| **ML-KEM (Kyber) NTT layer** (`256 × int16_t`, `q = 3329`) | Dense `int16_t[256]` (`512 B`; `16` lanes/`YMM` in `AVX2`) | `3 × int16_t` per `u64` (`86` `u64`s = `688 B`; unpack→`AVX2`→repack) | `9.06 ns` | `186.64 ns` | **`20.60×`** (`18.82×–23.15×`) | **`+34.4%`** (`688 B` vs. `512 B`) |
| **AES-128 10-round encrypt** (`AES-NI`) | Dense `16 B` block + `176 B` round keys (`11 × __m128i`) | `3 × 48`-bit per `128`-bit block (`24 B` state, `264 B` round keys) | `16.00 ns` | `23.47 ns` | **`1.47×`** (`1.43×–1.61×`) | **`+50.0%`** (`264 B` vs. `176 B`) |

*(Note: Furthermore, if `kyber_layer_tagged3x16` spills its unpacked `int16_t tmp[258]` buffer to the stack in L1/L2—as occurred in the unpack/repack wrapper—those temporary stack cache lines hold untagged 64-bit words and re-open the `DMP` window unless the entire `256`-coefficient polynomial stays strictly in SIMD registers or uses scalar/masked `48`-bit arithmetic throughout!)*

---

### 4. Multi-Level Performance and Resource Footprint Synthesis (L1–L6)

`Basis: source + documentation + execution (host microbenchmark) + derived`

| Level | Metric / Phenomenon | Quantitative Evidence Across Examined Systems | Basis & Qualifications |
| :--- | :--- | :--- | :--- |
| **L1: Human & Agent Authoring Velocity** | Engineering & audit effort per isolation / tagging boundary | `libmpk` required custom Linux kernel syscalls (`333–341`, `~175 LoC` in `kernel/libmpk/libmpk.c` + `~250 LoC` `pkey_sync` in `kernel/mm/mprotect.c` + `~450 LoC` userspace `mpt.cc`/`pkey.cc`) and still shipped 5 memory-safety/logic bugs + 1 concurrency race. Mediating all `PKU Pitfalls` syscalls (`Jenny`, USENIX Sec '22) requires auditing >300 Linux syscalls and signal/clone paths. `PAuthABI`+`MemtagABI` specifications span `2,209` lines of normative `.rst` (`1,384` + `825` lines in `ARM-software/abi-aa`). | `source` + `documentation` |
| **L2: Framework & Toolchain Build Time** | Linker / loader / binary-rewriter integration | `PAuthABI`/`MemtagABI` require coordinated compiler (`clang`/`gcc`), static linker (`lld`/`ld`), and dynamic loader (`glibc`/`bionic`) support; `libmpk` requires a full custom Linux kernel rebuild (`kernel/`). `ERIM`/`Jenny` require static binary inspection or compiler pass verification over all executable code segments to eliminate `0f 01 ef` (`WRPKRU`) and `0f ae /5` (`XRSTOR`) byte sequences. | `source` + `documentation` |
| **L3: Compilation, Elaboration & Synthesis Latency** | Static relocation / verification / policy checking overhead | `MemtagABI` out-of-bounds global initializers disable `SHT_RELR` compression and move globals from `.bss` to `.data`; `PAuthABI` adds `SHT_AARCH64_AUTH_RELR` (`0x70000004`) and per-symbol `.symauth`/`.dynauth` (`4 B`/global symbol). No interactive `<50 ms` LSP cost exists for hardware bit-layout checks themselves (trivial bitmask arithmetic), whereas whole-binary gadget scanning scales linearly with `.text` size. | `normative` + `derived` |
| **L4: Generated Code Execution Performance** | Domain switches, tag checks, and `DMP`-safe arithmetic | `WRPKRU`: `~11–26` cycles (`20–23.3` typical); bidirectional portal: `~40–60+` cycles; `libmpk` `pkey_sync`: `~3k` cycles (2 threads) to `~104k` cycles (101 threads); `libmpk` macro-benchmark overhead `<1%` vs. `8.1×` faster than `mprotect` (Park et al. ATC '19). `PSTATE.DIT` on Apple M3 disables `DMP` only during constant-time sections (`msr dit, #1`/`#0`, single-cycle sysreg toggle, avoiding non-crypto slowdown). Software `High16` `0x5AA5` limb tagging incurs **`1.47×` (`AES-NI`), `4.02×` (`256`-bit mul), and `20.60×` (`Kyber NTT AVX2`)** measured slowdown on `AMD EPYC 7B12`. | `documentation` + `source` + `execution (host microbenchmark)` |
| **L5: Proof / Certificate Verification Speed** | Hardware vs. static admission checking | Hardware `MTE` (`SYNC`/`ASYNC`/`ASYMM`), `PAC` (`autia`/`braa`), and `PKU` check permissions inline in the load/store/branch pipeline on every access (zero admission-time checker latency), whereas `ERIM`-style `PKU` safety requires load-time `0f 01 ef` binary verification over every `PROT_EXEC` page before admission (`O(bytes(.text))`). | `normative` + `derived` |
| **L6: RAM, Disk & Binary Footprints** | Tag storage, ELF metadata, and cryptographic state bloat | `MTE` physical allocation tags cost `1/32` (`3.125%`) of tagged DRAM (`4` bits per `16 B` granule; `128 B` per `4 KiB` page in `PT_AARCH64_MEMTAG_MTE` core dumps). `x86-64` `PKU` uses `4` existing PTE bits (`0 B` extra page-table RAM) + `4 B` in `XSAVE` per thread; `AArch64` `FEAT_S1POE` uses `3` PTE bits + `8 B` `POR_EL0`. `libmpk` maps `0x1000 + TABLE_SIZE * sizeof(HashEntry)` shared metadata per process. Software `0x5AA5` `High16` secret-limb tagging adds **`+34.4%` (`Kyber`) to `+50.0%` (`AES`/256-bit BigInt)** memory footprint and cache pressure. | `normative` + `source` + `execution` |

---

### 5. Human Comprehensibility and Conceptual Simplicity / Model Refinement (C1–C2)

`Basis: derived + source + normative`

- **(C1) Human Comprehensibility & Mental-Model Ergonomics:**
  - **Working-memory overload from bit-packing conflation:** Humans reliably reason about **typed pointers** and **cryptographic secrets** as orthogonal abstractions, not as overlapping 64-bit bit-fields whose meaning shifts silently with kernel config (`VA_BITS=48` vs. `52`, `LA57` vs. 4-level, `TBI0=1` vs. `0`, `LAM_U57` vs. `UAI`). Even expert ABI authors tripped over subtle metadata encodings—witness the shipped Android `clang-17`/`lld-17` `DT_AARCH64_MEMTAG_STACK` / `DT_AARCH64_MEMTAG_GLOBALS` odd/even parity inversion (`memtagabielf64.rst:389-405`) and the five bit-twiddling / order-of-operations bugs in `libmpk`'s ~650-line core (`&=`, `| PROT_EXEC`, `1 << -1`, `memset` before read, `kzalloc` offset overflow).
  - **Nonlocal security assumptions (`PKU` & `DMP`):** Both `PKU` and `DMP` break local programmer reasoning. A C/Rust engineer auditing a constant-time function sees zero secret-dependent branches or memory loads—yet `GoFetch` leaks the key from *data sitting passively in L1/L2 cache*. Similarly, an engineer auditing `WRPKRU` gates sees watertight user-space isolation—yet `rt_sigreturn`, `sigaltstack`, `/proc/self/mem`, and `io_uring` silently bypass `PKRU` via kernel code paths completely outside the user function's lexical scope.
  - **Human vs. LLM/agent asymmetry:** An LLM/agent can mechanically check bit-range disjointness tables or scan ELF relocations across hundreds of lines, yet without an explicit hardware-contract model an agent readily hallucinates that `0x5AA5` tagging stops all `DMP`s at zero cost or that `WRPKRU` costs `3.5` cycles—making explicit, machine-checked hardware capability descriptors essential for both human auditors and automated verifiers.
- **(C2) Simplicity, Orthogonality & Universal Model Refinement:**
  - **Separating semantic invariants from silicon accidents:** Four genuinely distinct invariants are routinely conflated under "upper-bit tagging":
    1. *Spatial/temporal memory-safety coloring* (`MTE` `[59:56]`, `CHERI` hardware tags — checked on dereference);
    2. *Cryptographic pointer integrity* (`PAC` `[54:VA_BITS]` — authenticated explicitly before dereference/branch);
    3. *Domain-level memory access authority* (`PKU` `PKRU` / `AArch64` `POR_EL0` — page-table + per-thread register, NOT pointer bits);
    4. *Microarchitectural value-oblivious execution* (`PSTATE.DIT` / `DOITM` — CPU pipeline mode disabling data-dependent timing and prefetchers).
  - **Felleisen macro-expressibility & Ousterhout deep-module test:** Attempting to macro-express *microarchitectural value-obliviousness* (`#4`) or *kernel-mediated isolation* (`#3`) solely via software upper-bit pointer/word tags (`High16`) fails Ousterhout's deep-module test: it leaks a `1.47×–20.60×` performance tax and stack-spill fragility into every cryptographic inner loop while failing on `TBI`-ignored bits (`[63:56]`) and page-walk side channels (`Peek-a-Walk`). Conversely, hardware `PSTATE.DIT` (on M3+) and `IA32_UARCH_MISC_CTL.DOITM` (Intel) provide a single narrow, orthogonal hardware interface (`enter_secret_mode` / `exit_secret_mode`) with zero data-layout distortion—provided the platform descriptor honestly records whether the host silicon implements `DIT` over its `DMP` (true on Apple M3, **false** on M1/M2!). Likewise, `PKU` cannot be treated as a deep isolation module unless paired with a mandatory OS-boundary contract (`seccomp`/syscall interposition + signal-stack confinement + `WRPKRU`/`XRSTOR` binary enforcement).

---

### 6. End-to-End Solution and Implementation Validation (V1–V4)

`Basis: source + documentation + derived`

Formal proofs over idealized ISA or software-tagging models routinely miss silicon prefetchers, kernel signal frames, and dynamic-linker ABI mismatches. End-to-end validation across this domain requires all four layers:

- **(V1) Specification Adequacy, Mutation & Non-Vacuity Validation:**
  - Encode hardware bit-field ownership (`VA_BITS`, `TBI`, `MTE`, `PAC`, `LA57`, `LAM_U57`, `UAI`) as an explicit satisfiability/disjointness specification per `(arch, os, kernel_config)` tuple, and validate non-vacuity via mutant policies (e.g., asserting that a 16-bit software tag partition is **rejected** on `AArch64 VA48+MTE+PAC` and `x86-64 Linux LAM_U57`, and that `PAuthABI`+`MemtagABI` rejects signing before `LDG`).
  - For `PKU` domain monitors, run property-based and mutant tests injecting all `PKU Pitfalls` syscalls (`rt_sigreturn`, `sigaltstack`, `/proc/self/mem`, `process_vm_writev`, `pkey_mprotect`, `io_uring`) to verify that the `seccomp`/interposition filter kills 100% of confused-deputy mutants rather than only testing direct pointer dereferences.
- **(V2) Compiler, Lowering & Checker Soundness Fuzzing:**
  - Differential and binary-level verification of compiled artifacts: verify that no untrusted `.text` section contains unintended `0f 01 ef` (`WRPKRU`) or `0f ae /5` (`XRSTOR`) byte sequences at *any* byte offset (even unaligned mid-instruction offsets on `x86-64`!).
  - Validate ELF `PAuthABI` + `MemtagABI` relocations (`R_AARCH64_AUTH_*`, `DT_AARCH64_MEMTAG_*`, `SHT_AARCH64_MEMTAG_GLOBALS_DYNAMIC`) differentially across `lld`, `ld.bfd`, and dynamic loaders (`glibc`/`bionic`), specifically fuzzing out-of-bounds global initializers (`&arr[N]`) and mixed tagged/untagged translation units (`memtagabielf64.rst:519-542,660-717`).
- **(V3) Concurrency, Crash, Silicon & Physical Leakage Validation:**
  - **Post-silicon microarchitectural fuzzing (`Revizor` / `GoFetch` `quick_check.out`):** Never extrapolate `DMP` immunity from software simulators or earlier silicon steppings. Run hardware `quick_check.out <set_dit>` (`gofetch/re/src/quick_check.c`) and `tbi.sh` (`bit_flip_position ∈ 48..63`) directly on target silicon to verify whether `PSTATE.DIT` / `DOITM` actually suppresses `DMP` L1 fills and page-walk side channels (`Peek-a-Walk`).
  - **Concurrency model checking & stress testing for `PKRU` sync:** Because `PKRU` is thread-local, test multi-threaded key revocation and `libmpk`-style `pkey_sync` under concurrent callers (`KCSAN`/lockdep/stress-ng) to catch races like `kernel/mm/mprotect.c:747-751` and `lib/mpt.cc:160` (`pkey_indomain_map &=`).
  - **Side-channel trace testing (`TVLA` / `Prime+Probe`):** Run fixed-vs-random Welch's $t$-test timing and cache-contention evaluations (`GoFetch` `crypto_accuracy.py`) on compiled constant-time binaries with `DIT` enabled vs. disabled, checking specifically for stack spills of unpacked cryptographic intermediates.
- **(V4) Telemetry / Production Replay & Human Comprehension Validation:**
  - **Kernel-ABI telemetry replay:** Replay real syscall/signal traces (`strace`/eBPF) through `AArch64` `PR_TAGGED_ADDR_ENABLE` and `x86-64` `LAM_U57` kernels to catch untagged-pointer exceptions (`mmap`, `brk`, `UFFDIO_*`, `shmat`) and `MM_CONTEXT_LOCK_LAM` `-EBUSY` failures when libraries attempt late `LAM` enablement after thread creation.
  - **Human auditor litmus checks:** Validate whether systems engineers inspecting a platform's pointer/isolation card can accurately predict (a) whether `TBI` tags survive `GoFetch`, (b) whether `LAM` gives 6 or 15 bits on Linux, and (c) whether `rt_sigreturn` bypasses `WRPKRU`-free sandboxes.

## Boundaries

- **Apple Silicon M4 and post-2024 Arm/x86 silicon `DMP` behavior (`not examined`):** Direct hardware execution on Apple M1/M2/M3/M4, Intel Arrow Lake/Lunar Lake, or AMD Zen 5 silicon was not performed on this host (`AMD EPYC 7B12`, which lacks `OSPKE`/`PKU`, `LA57`, `LAM`, and Apple's `DMP`). All Apple Silicon `DMP` activation findings rest on direct source inspection of `FPSG-UIUC/gofetch` (`13e2533b930f1ece5f0cee4969c0f0f184f65854`), `FPSG-UIUC/augury` (`e38f7232e579c071f195fb4320fc013c7a56e443`), Vicarte et al. (IEEE S&P 2022), and Chen et al. (USENIX Security 2024).
- **Direct host measurement of `WRPKRU` cycles (`unsupported` on host CPU):** `/proc/cpuinfo` on the measurement host (`AMD EPYC 7B12`, Zen 2) does not expose `ospke`/`pku` (AMD added `PKU` in Zen 4). `WRPKRU` cycle latencies (`11–26` cycles; `20–23.3` typical) are grounded in published measurements (Park et al., USENIX ATC 2019; Vahldiek-Oberwagner et al., `ERIM`, USENIX Security 2019) and `libmpk` in-source `pkey_sync` measurements (`kernel/mm/mprotect.c:765-767`), not executed locally.
- **Software `High16` (`0x5AA5`) tagging as a universal `DMP` defense (`known not to apply` / `unsupported`):** Our host microbenchmark measures **arithmetic and memory representation cost only** (`1.47×–20.60×` slowdown, `+34.4%–50%` RAM) on `AMD EPYC 7B12`, not silicon `DMP` suppression. Moreover, tagging `[63:56]` alone is **known not to apply** against Apple's `DMP` (which ignores `[63:56]` via `TBI`), and tagging `[63:48]` does **not** eliminate page-walk side channels (`Peek-a-Walk`) or stack-spill windows in `SIMD`/register-allocated crypto code.
- **Exact `LAM_U48` Linux kernel enablement (`known not to apply` on mainline Linux):** Although `arch/x86/include/asm/mmu.h:52` mentions `X86_CR3_LAM_U48` in a struct comment, `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854` (`arch/x86/kernel/process_64.c:800-856,964-969`) exclusively implements `LAM_U57` (`6` bits) and rejects `nr_bits > 6` with `-EINVAL`.
- **CHERI / Morello 129-bit tagged capabilities (`not examined`):** Hardware capability architectures storing out-of-band 1-bit validity tags in DRAM metadata (e.g., Arm Morello, CHERI-RISC-V) avoid upper-address bit contention altogether and are outside the scope of this report.
- **Kernel-mode `PKS` (Protection Keys Supervisor) and `AArch64` `FEAT_S1POE` microarchitectural latencies (`unknown`):** While `torvalds/linux` documents `FEAT_S1POE` (`POR_EL0`, 8 keys, read/write/execute), silicon cycle counts for `MSR POR_EL0` pipeline serialization across commercial Armv8.9/Armv9.4 cores were not publicly benchmarked in the examined sources.

## Evidence

All primary evidence was acquired and verified on `2026-11-19`–`2026-11-20`:

1. **`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854`:**
   - `Documentation/arch/arm64/tagged-address-abi.rst` (lines `16-135`: `TCR_EL1.TBI0`, two-stage `PR_SET_TAGGED_ADDR_CTRL` relaxation, untagged exceptions `brk`/`mmap`/`mremap`/`shmat`/`shmdt`/`UFFDIO_*`).
   - `Documentation/arch/arm64/memory-tagging-extension.rst` (lines `16-248`: `[59:56]` logical tag, 16-byte granule, `PROT_MTE`, `SYNC`/`ASYNC`/`ASYMM`, `PSTATE.TCO`, kernel `uaccess` checking caveats, `PT_AARCH64_MEMTAG_MTE` core dump `128 B`/`4 KiB`).
   - `Documentation/arch/arm64/pointer-authentication.rst` (lines `52-55`: `55 - VA_BITS` PAC width) and `arch/arm64/include/asm/pointer_auth.h` (lines `17-18`: `ptrauth_user_pac_mask() = GENMASK_ULL(54, vabits_actual)`, `ptrauth_kernel_pac_mask() = GENMASK_ULL(63, vabits_actual)`).
   - `Documentation/arch/x86/x86_64/5level-paging.rst` (lines `9-58`: `LA57` `128 PiB` VA, `56`-bit user VA, default `<47`-bit `mmap` compatibility).
   - `arch/x86/kernel/process_64.c` (lines `798-864, 953-969`: `LAM_U57_BITS = 6`, `untag_mask = ~GENMASK(62, 57)`, `MM_CONTEXT_LOCK_LAM`, `ARCH_GET_MAX_TAG_BITS`) and `arch/x86/include/asm/mmu.h` (lines `15-18, 51-57`).
   - `Documentation/core-api/protection-keys.rst` (lines `11-49`: x86 `PKU` vs. arm64 `FEAT_S1POE`; lines `118-120`: `io_uring`/kthread `PKRU` inconsistency), `arch/x86/mm/pkeys.c` (lines `120-127`: `init_pkru_value = 0x55555554`), `arch/x86/kernel/signal.c` (lines `63-79, 160-170, 310`: `sig_prepare_pkru()` calling `write_pkru(0)`), and `arch/x86/kernel/fpu/signal.c` (lines `260-344, 462-516`: `fpu__restore_sig()` invoking `xrstor_from_user_sigframe()`).
2. **`ARM-software/abi-aa` at `9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7` (`2026Q3`, 3 Nov 2026):**
   - `pauthabielf64/pauthabielf64.rst` (lines `470-480, 604, 645-761, 912-925, 1245-1297`: signing schema layout, `AUTH` relocations `0x244`/`0x411`–`0x414`, `GNU_PROPERTY_AARCH64_FEATURE_PAUTH`, and `SIGN(LDG(...))` Memtag+PAuth composition).
   - `memtagabielf64/memtagabielf64.rst` (lines `375-405, 449-456, 485-542, 558-717`: `DT_AARCH64_MEMTAG_*` Android parity erratum, ULEB128 global descriptor packing, `R_AARCH64_RELATIVE` out-of-bounds tag-derivation offset).
3. **`sslab-gatech/libmpk` at `a0c86673783643aa9e9045606cf7a35b30488bc6`:**
   - `lib/mpt.cc` (lines `110-185, 225-352`: raw `.byte 0x0f,0x01,0xee`/`0xef`, defects at lines `160`, `282`, `340`), `lib/pkey.cc` (lines `39-42`), `lib/headers/pkey.h` (lines `7-60`), `kernel/libmpk/libmpk.c` (defects at lines `15-17`, `139-147`), and `kernel/mm/mprotect.c` (lines `741-966`: `do_pkey_sync` IPI latency numbers `1 µs / 6 µs / 43 µs` and documented concurrent-caller race).
4. **`FPSG-UIUC/gofetch` at `13e2533b930f1ece5f0cee4969c0f0f184f65854` and `FPSG-UIUC/augury` at `e38f7232e579c071f195fb4320fc013c7a56e443`:**
   - `gofetch/README.md` (lines `52-80`: `DIT`, single-load `noderef.sh`, L1 fill monitor, do-not-scan hint, `4 GiB` region, `TBI` top-byte pass-through), `re/tbi.sh` (line `14`: `48..63` bit-flip sweep), `re/src/dmp.h` (line `16`: `ADDR_CHECK`), `re/src/quick_check.c` (lines `19-60`: `hw.optional.arm.FEAT_DIT` + `__builtin_arm_wsr64("DIT", ...)`), `re/src/lib/basics/arch.h` (M1/M2/M3 cache geometry), `poc/crypto_attacker/examples/{kyber,dilithium}_attacker.rs`, and `augury/augury.c` + `augury/make_addrs.py`.
5. **Reproducible local probes executed on Linux `x86-64` (`AMD EPYC 7B12`, `8` CPUs, `AVX2` + `AES-NI`, `gcc -Wall -Wextra -O3 -march=native`):**
   - **Bit-layout audit (`pkg1_bitlayout_audit.py`):** Verified exact bit counts across all 8 hardware configurations and confirmed `DMP_region_match = True` for `0x5A << 56` (`TBI` tag) and `0xA << 56` (`MTE` tag) vs. `False` for `0x5AA5 << 48` and `0x3D << 48` (`PAC`) against `0x0000000140008000` in container `0x0000000140010000`.
   - **Crypto-limb microbenchmark (`pkg1_crypto_limb_bench.c`, `N = 2,000,000` iterations, 5 runs):**
     - `256`-bit schoolbook mul: native `[13.60, 15.09, 15.10, 15.88, 20.43]` ns (median `15.10 ns`) vs. tagged `6×48`-bit `[56.37, 58.92, 60.73, 63.13, 66.03]` ns (median `60.73 ns`, `4.02×`).
     - `Kyber` `256×i16` NTT layer: native `AVX2` `[7.70, 8.11, 9.06, 9.30, 10.69]` ns (median `9.06 ns`) vs. tagged `3×16b/u64` `[177.64, 178.24, 186.64, 193.85, 201.17]` ns (median `186.64 ns`, `20.60×`).
     - `AES-128` 10-round (`AES-NI`): native `[15.82, 15.98, 16.00, 16.03, 16.07]` ns (median `16.00 ns`) vs. tagged `3×48b` `[22.89, 23.33, 23.47, 25.80, 27.06]` ns (median `23.47 ns`, `1.47×`).
6. **Peer-reviewed literature:** Vicarte et al. (IEEE S&P 2022, DOI `10.1109/SP46214.2022.9833570`), Chen et al. (USENIX Security 2024, `gofetch.fail`), Park et al. (USENIX ATC 2019), and Connor et al. (USENIX Security 2020).

## Revalidation

Use the following targeted checks when adopting a newer kernel, ABI release, or CPU microarchitecture:

1. **Linux `LAM`, `LA57`, `PAC`, and `PKRU` contract diff:** Diff `arch/x86/kernel/process_64.c` (`LAM_U57_BITS`, `ARCH_ENABLE_TAGGED_ADDR`), `arch/x86/kernel/signal.c` (`sig_prepare_pkru`), `arch/x86/kernel/fpu/signal.c` (`fpu__restore_sig`), `Documentation/core-api/protection-keys.rst` (`io_uring`/kthread caveat), and `arch/arm64/include/asm/pointer_auth.h` (`ptrauth_user_pac_mask`) against `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854`. Specifically check whether `LAM_U48` or `AMD UAI` has been enabled in `do_arch_prctl_64()` and whether `io_uring` propagates per-request `PKRU`.
2. **Arm `PAuthABI` / `MemtagABI` promotion check:** Check `ARM-software/abi-aa` `pauthabielf64/pauthabielf64.rst` and `memtagabielf64/memtagabielf64.rst` for graduation out of Alpha status, relocation-code renumbering, or updates to `SIGN(LDG(...))` composition.
3. **Target-silicon `DMP` + `DIT` / `DOITM` probe:** On any new Apple Silicon or `x86-64` CPU generation, compile and run `FPSG-UIUC/gofetch` `re/src/quick_check.c` with `set_dit=0` and `set_dit=1`, and sweep `re/tbi.sh` across bits `48..63` (plus `LAM`-masked bits `[62:57]` on Intel `LAM` silicon) to verify whether the prefetcher ignores `TBI`/`LAM` tag bits and whether `DIT`/`DOITM` suppresses both data prefetching and page-walk side channels.
4. **Target-CPU `WRPKRU` & tagged-limb re-benchmark:** On a `PKU`-capable host (`grep -w ospke /proc/cpuinfo`), time back-to-back dependent `WRPKRU` pairs (`0f 01 ef`) alongside `rdtscp` fences, and re-run the `256`-bit mul / `Kyber` NTT / `AES-NI` tagged-limb C benchmark (`gcc -O3 -march=native`) on target microarchitectures (`NEON`/`SVE` on `AArch64`, `AVX-512` on `x86-64`) before budgeting software-tagged secret representations.
