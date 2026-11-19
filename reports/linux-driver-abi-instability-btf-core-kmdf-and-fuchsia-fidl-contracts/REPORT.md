# Kernel Driver ABI Instability, eBPF CO-RE Relocations, Versioned Framework Tables, and Capability-Routed Arena Contracts

## Summary

Operating systems face an irreconcilable coupling between **in-kernel evolution velocity** and **binary extension stability**: exposing raw C structs across dynamically loaded drivers freezes internal memory layouts and synchronization protocols, whereas hiding layouts behind coarse IPC traps or indirect tables introduces runtime marshaling, IOMMU mapping, or semantic-drift hazards. Direct inspection of mainline Linux, `libbpf`, Windows Driver Frameworks (KMDF), XNU DriverKit, Fuchsia Driver Framework v2 (DFv2), and Rust-for-Linux reveals five foundational invariants:

1. **Linux treats internal ABI breakage as a core engineering invariant and enforces exact build equivalence via symbol CRCs and layout randomization.** Unlike its userspace syscall ABI (`Documentation/process/stable-api-nonsense.rst`), Linux alters struct layouts, lock types, and inline helpers continuously. `CONFIG_MODVERSIONS` verifies exact binary compatibility at `insmod` time via `check_version()` (`kernel/module/version.c:13-73`), comparing 32-bit `___kcrctab+` CRCs (`include/linux/export-internal.h:65-71`) computed historically by `genksyms` over preprocessed C tokens—which breaks on Rust name mangling and compiler-reordered `repr(Rust)` types—and superseded for Rust and modern DWARF toolchains by `gendwarfksyms` (`scripts/gendwarfksyms/gendwarfksyms.h`), which hashes DWARF DIE graphs and supports explicit kABI masking rules (`.discard.gendwarfksyms.kabi_rules`, `scripts/gendwarfksyms/kabi.c:12-78`). With `RANDSTRUCT` (`scripts/gcc-plugins/randomize_layout_plugin.c`), compile-time field permutation breaks any binary module compiled without the kernel's 256-bit `randstruct.seed`.
2. **eBPF CO-RE (`__builtin_preserve_access_index`) solves syntactic layout relocation, but fails silently across four semantic synchronization walls.** `libbpf` (`src/relo_core.c`) resolves `BPF_CORE_FIELD_BYTE_OFFSET`, integer widening (`orig_sz != new_sz`), bitfield shift parameters (`LSHIFT_U64`/`RSHIFT_U64`), and missing-field branch poisoning (`0xbad2310` invalid helper call, `relo_core.c:986-1007`) against target kernel BTF at load time. However, because BTF encodes only field names, types, and bit offsets—never concurrency protocols—CO-RE relocations still succeed syntactically while violating **split locks** (e.g., `mmap_lock` to per-VMA locks), **RCU/SeqLock ordering**, **refcount/`SLAB_TYPESAFE_BY_RCU` lifetimes**, and **compound-descriptor/inlined-helper invariants** (e.g., `struct page` to `struct folio`).
3. **Windows KMDF preserves binary compatibility across framework versions through handle scrambling, context-header separation, and versioned dispatch tables—but Ring-0 ABI stability does not establish Ring-0 memory isolation.** KMDF (`microsoft/Windows-Driver-Frameworks`) binds drivers dynamically to `Wdf01000.sys` via `WdfBindClientHelper` (`version.cpp:474-540`), routes every DDI call through monotonic table indices (`WDFFUNCENUM`, `wdffuncenum.h`), versions config structs by `.Size` (`fxversionedstructures.h`), and scrambles `WDFOBJECT` handles (`handle = ((ULONG_PTR)Object) ^ FxHandleValueMask`, `fxobject.hpp:672-680`) while locating driver-owned state past `this + m_ObjectSize` via `FxContextHeader` (`fxhandle.h:30-98`). Yet as the July 19, 2024 CrowdStrike Falcon Channel File 291 incident demonstrated (an out-of-bounds 21st-parameter read in a WHQL-signed Ring-0 `.sys` interpreter crashing ~8.5 million hosts into boot loops), stable Ring-0 ABIs leave the entire kernel vulnerable to data-driven faults—catalyzing Microsoft's Windows Resiliency Initiative to move endpoint sensors out of Ring 0.
4. **macOS DriverKit and Fuchsia DFv2 replace shared kernel struct layouts with explicit IPC/wire boundaries, trading direct-call cycles for fault isolation and arena-backed schema evolution.** DriverKit (`apple-oss-distributions/xnu` `iokit/Kernel/IOUserServer.cpp`) isolates drivers as userspace `DriverExtension` processes communicating via Mach `IORPC` messages and `IOMapper::copyMapperForDevice` DART IOMMU mappings (`L951-1073`), eliminating kernel panics on driver bugs at the cost of kernel-boundary traps and buffer mapping/copy operations (`PerformOperation_Impl`, `L1146-1230`). Fuchsia DFv2 (`RFC-0126`, `sdk/lib/driver/runtime/include/lib/fdf/arena.h`) splits the boundary into two tiers: untrusted/remote capability-routed `zx_channel` IPC and co-located `driver_host` processes sharing refcounted `fdf_arena_t` memory blocks alongside FIDL v2 8-byte `(word0, num_handles, flags)` table envelopes—though RFC-0126 (`L917-938`) flags that skipping linearization risks leaking Zircon handles inside unknown table/union ordinals unless handles remain in an out-of-band handle table.
5. **Rust-for-Linux enforces ownership, pinning, and lock invariants statically at source co-evolution boundaries instead of freezing binary ABIs.** Mainline `rust/kernel/types.rs` (`L331-432`) and `rust/kernel/sync/lock.rs` (`L104-324`) compose `Opaque<T>` (`UnsafeCell<MaybeUninit<T>> + PhantomPinned`, neutralizing Rust validity/aliasing UB across C-mutated FFI structs), `PinInit<T, E>` (`Rust-for-Linux/pin-init` `src/lib.rs:973-1055`, initializing self-referential C `mutex`/`list_head` slots in-place without moves), and `Lock<T, B>` (binding `LockClassKey` lockdep tracking and mutual exclusion directly to `Guard<'_, T, B>` types). This turns Day-2 ABI evolution into compile-time type-checking inside one source tree rather than silent runtime corruption.

## Applicability

This report characterizes and compares seven durable systems and four peer-reviewed analyses inspected at pinned revisions on `2026-11-19`:

- **Linux Kernel Internal ABI & Rust-for-Linux** (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`; `Rust-for-Linux/linux` @ `aebb7274476403040d582c61478df8f4a7bf9cd3`; `Rust-for-Linux/pin-init` @ `578ad6b8f9d136aeb365f2175f6ef9f0e3dab288`): Applies to loadable kernel modules (`CONFIG_MODVERSIONS`), `genksyms`, `gendwarfksyms` (upstream since Linux 6.14), `GCC_PLUGIN_RANDSTRUCT`, and in-tree Rust kernel abstractions (`Opaque<T>`, `Lock<T, B>`, `PinInit`). Does **not** govern Linux's stable userspace syscall ABI (`uapi/`).
- **eBPF CO-RE** (`libbpf/libbpf` @ `4f05fb027a08a8a66d03916cf6a68a91e2c720ea`): Applies to Clang `__builtin_preserve_access_index` / `BPF_CORE_READ` programs relocated against `vmlinux` BTF at load time (`src/relo_core.{h,c}`, `src/bpf_core_read.h`), evaluated alongside kernel verifier bounds (`10.1145/3314221.3314590`, `10.1145/3593856.3595892`, `10.1145/3627703.3629562`).
- **Windows KMDF/UMDF** (`microsoft/Windows-Driver-Frameworks` @ `b6191d9543441329154da32f7ab9bdd97228dd3c`): Covers KMDF v1.15–v1.33 (`Wdf01000.sys` dynamic loader binding, `WDFFUNCENUM`, `FxObject`/`FxContextHeader`), contrasted with non-WDF raw WDM/filter drivers (such as legacy kernel-mode endpoint security sensors implicated in the July 2024 CrowdStrike Channel File 291 incident).
- **macOS DriverKit** (`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`): Covers XNU's userspace driver runtime (`iokit/Kernel/IOUserServer.cpp`, `IOMemoryDescriptor`, `IODMACommand`), excluding in-kernel legacy KPI KEXTs deprecated for third-party macOS distribution.
- **Fuchsia DFv2 & FIDL Wire Format v2** (`fuchsia.googlesource.com/fuchsia` @ `15f8bdfdea9a506c78363f84b842dae3b61e120f`): Covers RFC-0126 co-located `fdf_arena_t` driver transport, FIDL v2 envelope/table layout, and component capability routing.

## Findings

### 1. Linux's Deliberate Internal ABI Instability (`CONFIG_MODVERSIONS`, `genksyms` vs. `gendwarfksyms`, and `RANDSTRUCT`)

**Basis:** `normative` (`Documentation/process/stable-api-nonsense.rst`) + `source` (`torvalds/linux` `include/linux/export-internal.h`, `kernel/module/version.c`, `scripts/genksyms/genksyms.c`, `scripts/gendwarfksyms/{gendwarfksyms.h,kabi.c}`, `scripts/gcc-plugins/randomize_layout_plugin.c`).

Linux rejects both a stable in-kernel binary ABI and a stable in-kernel C source API (`stable-api-nonsense.rst:10-120`) so maintainers can refactor locks, reorder fields, eliminate stale callbacks, and let config flags (`CONFIG_SMP`, lockdep, KASAN, compiler alignment) reshape every `struct` without preserving dead compatibility padding. To prevent out-of-tree or stale `.ko` binaries from silently corrupting changed layouts, Linux embeds structural hashes directly in ELF symbol tables:

1. **Symbol Table & CRC Admission (`export-internal.h:40-78`, `module/version.c:13-146`):** For each exported symbol, macros emit string entries into `__ksymtab_strings`, relative (`PREL32`) or pointer entries into `___ksymtab+<sym>`, and 32-bit checksums into `___kcrctab+<sym>` (`__crc_<sym>`). During module loading, `check_version()` (`module/version.c:13-73`) scans the module's `__versions` (`struct modversion_info` or extended `vers_ext_crc`/`vers_ext_name`) and rejects any symbol whose 32-bit CRC differs (`disagrees about version of symbol %s`), while `check_modstruct_version()` (`L75-94`) anchors `struct module` itself via the synthetic export `module_layout(mod, ver, kp, ks, tp)` (`L139-146`).
2. **`genksyms` Preprocessed C AST Hashing vs. `gendwarfksyms` DWARF DIE Hashing:**
   - Legacy `genksyms` (`scripts/genksyms/genksyms.c:565-638`) runs a bespoke C lexer/parser over `-E` preprocessed translation units, recursively expanding referenced typedefs and structs into token streams hashed by `crc32` (`L119-133`). As documented in upstream Linux kernel integration notes and LWN coverage of Linux 6.14 (Sami Tolvanen / Jonathan Corbet), `genksyms` fails on **Rust-for-Linux** crates because `rustc` emits no C header declarations for Rust generic monomorphizations, enum niche layouts, or `#[repr(Rust)]` field-reordered types, and its mangled symbols exceed simple C identifier rules.
   - `gendwarfksyms` (`scripts/gendwarfksyms/gendwarfksyms.h:79-289`, `scripts/gendwarfksyms/kabi.c:12-140`) resolves this language barrier by reading **post-codegen DWARF Debugging Information Entries (DIEs)** via `libdw` (`DW_TAG_structure_type`, `DW_TAG_member`, `DW_TAG_variant_part`, `DW_TAG_typedef`, `L80-87`) for symbols tagged via `__gendwarfksyms_ptr_<sym>` (`SYMBOL_PTR_PREFIX`, `L93`). Downstream LTS/GKI maintainers requiring selective kABI stability pass `--stable`, which parses ELF `.discard.gendwarfksyms.kabi_rules` (`kabi.c:12-70`) supporting five structural escape hatches: `declonly` (opaque forward declaration), `enumerator_ignore`, `enumerator_value`, `byte_size`, and `type_string`—letting distribution kernels append reserved struct fields without perturbing downstream module CRCs, at the strict burden of manual review that invariants remain sound.
3. **`RANDSTRUCT` (`scripts/gcc-plugins/randomize_layout_plugin.c:426-565, 915-931`):** When `GCC_PLUGIN_RANDSTRUCT` is enabled, any struct annotated with `__randomize_layout` or classified as `is_pure_ops_struct(type)` (structs containing solely function pointers) has its field order permuted using a compile-time 256-bit hexadecimal `randstruct_seed` (`L915-920`, keeping cache-line boundaries via `randomized_struct_fields_start`/`end`). Because `RANDSTRUCT` changes offsets per kernel build even at identical source versions, any precompiled `.ko` lacking the exact `randstruct.seed` jumps to arbitrary function pointers or corrupts memory immediately unless `CONFIG_MODVERSIONS` catches the layout hash change first.

### 2. eBPF CO-RE Relocation Engine (`libbpf`) and Its Four Exact Semantic Walls

**Basis:** `documentation` (`libbpf` CO-RE model; Nakryiko CO-RE guide) + `source` (`libbpf/libbpf` `src/relo_core.{h,c}`, `src/bpf_core_read.h`) + `execution` (inline Python relocation/layout probe in `## Evidence`) + `derived`.

To let observability and security eBPF programs compile once and load across thousands of heterogeneous Linux kernel layouts without shipping Clang and kernel headers to production hosts, `libbpf` couples Clang compiler metadata with load-time instruction rewriting:

#### 2.1 Load-Time Relocation Mechanics (`relo_core.h:22-69`, `relo_core.c:690-1441`)

1. **Symbolic Access Path Recording:** Clang's `__builtin_preserve_access_index` and `__builtin_preserve_field_info` (`bpf_core_read.h:15-44`) freeze field access chains (`struct bpf_core_spec`, up to `BPF_CORE_SPEC_MAX_LEN = 64` nested `bpf_core_accessor` steps recording `type_id`, `idx`, and field `name`, `relo_core.h:20-45`) into `.BTF.ext` alongside the compiled BPF ELF bytecode.
2. **Target BTF Resolution & Multi-Candidate Ambiguity Checking:** `bpf_core_calc_relo_insn()` (`relo_core.c:1301-1441`) parses `local_spec`, scans all target BTF candidate types (`cands`) matching the essential name (`bpf_core_essential_name_len`, stripping compiler/version suffixes like `___old`), and verifies that *every* matching candidate resolves to the identical `bit_offset` (`L1382-1389`) and identical relocation decision (`L1390-1403`), rejecting ambiguous multi-candidate matches with `-EINVAL`.
3. **Instruction Patching, Integer Widening, and Dead-Branch Poisoning (`relo_core.c:737-818, 986-1160`):**
   - `bpf_core_patch_insn()` validates expected immediate/offset values (`res->validate`), rewrites `BPF_ALU`/`BPF_ALU64` immediates, `BPF_LDX`/`BPF_ST`/`BPF_STX` memory offsets (`off`), and `LDIMM64` 64-bit immediates (`L1048-1160`), and automatically adjusts memory access width (`BPF_B`/`BPF_H`/`BPF_W`/`BPF_DW`) when a kernel field widens (e.g., `u32 -> u64`, `L1109-1129`).
   - For bitfields (`bit_sz > 0`, `L742-811`), `libbpf` computes minimal aligned storage `byte_off`/`byte_sz` plus `BPF_CORE_FIELD_LSHIFT_U64` and `BPF_CORE_FIELD_RSHIFT_U64` shift distances (`bpf_core_read.h:72-147`) and disables `orig_val` validation (`*validate = !bitfield`, `L770-771`).
   - When a field does not exist in target BTF (`!spec` -> `-EUCLEAN`, `L700-701`), `bpf_core_poison_insn()` (`L986-1007`) replaces the instruction with `BPF_JMP | BPF_CALL` targeting invalid helper `imm = 195896080` (`0xbad2310`, `"bad relo"`). If the program guards that access with `bpf_core_field_exists(...)`, the kernel BPF verifier prunes the dead branch and accepts the program; if reachable, the verifier rejects loading (`invalid func unknown#195896080`).

#### 2.2 The Four Semantic Walls Where Syntactic CO-RE Silently Fails

BTF encodes structural geometry (names, types, bit offsets) and **zero concurrency or ownership invariants**. Consequently, `bpf_core_calc_relo_insn()` reports clean relocation success across four classes of kernel refactors that silently produce torn reads, data races, use-after-free bugs, or misclassified pointers:

| Semantic Wall | Concrete Upstream Evolution Pattern | Why CO-RE Syntactic Check Passes | Resulting Failure Mode (`derived` + `execution`) |
| :--- | :--- | :--- | :--- |
| **1. Split Locks & Lock-Hierarchy Shifts** | Coarse `struct mm_struct::mmap_lock` augmented or split into per-VMA locks (`vm_lock`), or global lock partitioned per-CPU/sharded | `vm_flags` or list field still exists in target `struct` (`offset`/`size` patched cleanly, as verified by the `## Evidence` probe) | BPF helper/iterator holding old coarse lock—or reading locklessly via `bpf_probe_read_kernel`—observes inconsistent partial updates under concurrent per-VMA writers |
| **2. RCU / `seqcount_t` (`SeqLock`) Discipline Shifts** | Field migrated from mutex-protected inplace overwrite to RCU-swapped pointer or `seqcount_t` (`d_seq` / `u64_stats_sync`) optimistic reader protocol | Target pointer or counter field retains identical name and type; `BPF_CORE_READ` emits plain load without sequence retry or RCU grace-period barrier | Non-atomic torn 64-bit / multi-field reads on 32-bit or weakly ordered CPUs, or dereferencing RCU-freed pointer outside `rcu_read_lock()` |
| **3. Refcount & SLAB Lifetime Reordering** | Object allocator switches to `SLAB_TYPESAFE_BY_RCU` reuse, or `kref` zero-transition semantics shift (`refcount_inc_not_zero` required before deref) | Refcount integer offset relocates cleanly; `bpf_probe_read_kernel` bypasses type-state refcount checks | ABA type-confusion: reader traverses a recycled slab slot belonging to a different logical entity while refcount field offset still holds a valid integer |
| **4. Inlined Helper & Compound Descriptor Shifts** | Macro/inline helper changes bit-encoding invariants (e.g., `struct page` migration to `struct folio` where tail pages share a `struct page` slot, or `compound_head` low-bit tagging) | `struct page` fields still exist in target BTF at shifted offsets (`BPF_CORE_READ` succeeds on tail page) | Caller reads uninitialized/overloaded `union` alias bytes on a tail page instead of redirecting through `folio_page` / `compound_head()` |

### 3. Head-to-Head Comparison: KMDF, DriverKit, Fuchsia DFv2, and Rust-for-Linux

**Basis:** `normative` (`fuchsia` `RFC-0126`, FIDL Wire Format v2) + `source` (`microsoft/Windows-Driver-Frameworks`, `apple-oss-distributions/xnu`, `fuchsia`, `torvalds/linux`, `Rust-for-Linux/pin-init`) + `documentation` (CrowdStrike Channel File 291 RCA, Microsoft WRI) + `execution` (inline Python layout/envelope probe in `## Evidence`).

#### 3.1 Windows KMDF (`microsoft/Windows-Driver-Frameworks` @ `b6191d9543441329154da32f7ab9bdd97228dd3c`)

KMDF decouples third-party driver binaries from Microsoft's internal C++ implementation classes (`FxDevice`, `FxRequest`, `FxQueue`) through four complementary ABI firewalls:

1. **Dynamic Version Loader & Monotonic Dispatch Table (`version.cpp:474-540`, `wdffuncenum.h:25-747`):** On `DriverEntry`, the statically linked stub calls `WdfVersionBind` -> `WDF_LIBRARY_REGISTER_CLIENT`, validating client major/minor versions against `Wdf01000.sys` (`WdfBindClientHelper`, `version.cpp:488-518`) and binding `WdfFunctions` (an append-only array of function pointers indexed by `WDFFUNCENUM`). `wdffuncenum.h:25-32` marks `WDF_FIRST_VERSION_SUPPORTING_CLIENT_VERSION_HIGHER_THAN_FRAMEWORK = 25` (`WDF_ALWAYS_AVAILABLE_FUNCTION_COUNT = 453`), allowing drivers compiled against newer SDK headers to degrade gracefully via `WDF_IS_FUNCTION_AVAILABLE` on older Windows builds.
2. **Size-Tagged Versioned Input Structs (`fxversionedstructures.h`, `wdffuncenum.h`):** Every driver-allocated config struct embeds `ULONG Size` as its first field (`WDF_DRIVER_CONFIG_V1_0` -> `V1_1`, `fxversionedstructures.h:31-52`), paired with `WDF_STRUCTURE_TABLE_NUM_ENTRIES = 81` (`wdffuncenum.h:742`). The runtime uses `Size` to distinguish truncated legacy callers from newer callers.
3. **Handle XOR Scrambling & Context-Header Decoupling (`fxobject.hpp:604, 626-680`, `fxhandle.h:30-98`):** Externally visible `WDFOBJECT` handles are never raw `FxObject*` pointers; `_ToHandle()` computes `((ULONG_PTR) Object) ^ FxHandleValueMask` where `FxHandleFlagMask = 0x7` and `FxHandleValueMask = ~0x7` (`fxhandle.h:62,69`, `fxobject.hpp:672-680`), preserving low 3-bit flags (such as `FxHandleFlagIsOffset`) while scrambling the pointer bits so drivers cannot cast handles to inspect internal C++ members. Driver-defined state is appended *after* the framework object at `this + m_ObjectSize` (`GET_CONTEXT_HEADER()`, `fxobject.hpp:604`), chaining `FxContextHeader` records (`fxhandle.h:62-93`) whose `Context[1]` offset is invariant to growth of Microsoft's private `FxObject` C++ subclasses.
4. **The Ring-0 Fault Isolation Gap (CrowdStrike Channel File 291 Incident, July 19, 2024):** KMDF protects binary ABI compatibility across OS updates, yet both KMDF drivers and legacy raw WDM kernel drivers (`csagent.sys`) still execute in Ring 0 with unrestricted access to nonpaged kernel memory. As established in CrowdStrike's Root Cause Analysis and Microsoft's subsequent **Windows Resiliency Initiative (WRI)** disclosures, CrowdStrike shipped Channel File 291 containing a dynamic IPC template configured for **21 input fields** while the kernel sensor interpreter supplied only **20 values**; the Ring-0 interpreter executed an out-of-bounds read (`0x50` / `0x7E` bugcheck) milliseconds into early boot, bricking ~8.5 million Windows hosts into infinite reboot loops before remote management could recover. Stable Ring-0 ABI contracts do not contain interpreter, bounds, or logic bugs inside kernel drivers—motivating Microsoft's shift toward the user-mode **Windows Endpoint Security Platform** and phased canary deployment rules (`MVI 3.0`).

#### 3.2 macOS DriverKit (`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`)

Apple deprecated third-party kernel-space KPI KEXTs in favor of **DriverKit**, which runs each driver (`.dext`) as an unprivileged userspace process supervised by `IOUserServer` (`iokit/Kernel/IOUserServer.cpp`):

- **IPC & Interface Generation (`IOUserServer.cpp:141, 2870-3025`):** Interface definitions (`.iig`) compile into Mach `IORPC` marshalers (`IORPCMessageMach`, `OSObject_Instantiate_Rpl`). Method calls cross the kernel/user boundary via Mach IPC queues (`IODispatchQueue`, `ipc_port_copy_send_mqueue`, `L3023`), confining any driver OOB read or null dereference to a restartable userspace process crash instead of a kernel panic.
- **IOMMU Hardware Isolation & DMA Copy Overhead (`IOUserServer.cpp:666-741, 951-1230`):** Because userspace drivers cannot program physical DMA addresses safely, `IODMACommand::Create_Impl()` binds an `IOMapper` (`IOMapper::copyMapperForDevice(device)`, `L977`, e.g., Apple Silicon DART IOMMU) with `kIODMAMapOptionDextOwner | kIODMAMapOptionMapped` (`L982-983`). `PrepareForDMA_Impl()` pins pages, generates IOMMU-mapped `IOAddressSegment`s (`genIOVMSegments`, `L1050`), and `CreateMapping_Impl()` maps `IOMemoryDescriptor`s into the driver task (`kIOMapGuardedSmall`/`Large`, `L690-732`). Crucially, small/unaligned control transfers via `IODMACommand::PerformOperation_Impl()` (`L1146-1230`) allocate kernel bounce buffers (`OSDataAllocation<uint8_t>`, `L1178`) and copy payloads across `IOMemoryDescriptor`, adding Mach syscall traps and memory-copy/IOMMU-TLB latency for every non-ring-mapped transaction.

#### 3.3 Fuchsia Driver Framework v2 (`fuchsia.googlesource.com/fuchsia` @ `15f8bdfdea9a506c78363f84b842dae3b61e120f`)

Fuchsia's DFv2 (`RFC-0126`, `docs/contribute/governance/rfcs/0126_driver_runtime.md`) eliminates the legacy Banjo C-vtable ABI (`RFC-0126:31-116`, which offered zero wire evolution and suffered cross-driver lock reentrancy deadlocks) while avoiding paying full kernel-IPC syscall costs between trusted co-located drivers:

- **Two-Tier Capability-Routed Transport (`RFC-0126:11-26, 610-617`):** Component manifests (`driver_runtime`, `colocate`) place drivers sharing a trust boundary inside a single userspace `driver_host` process communicating via in-process `fdf` runtime channels (`fdf_channel_*`) and non-reentrant asynchronous `fdf` dispatchers (`RFC-0126:71-96, 1027-1045`), while drivers crossing trust boundaries automatically communicate over Zircon kernel channels (`zx_channel`) with identical FIDL protocol schemas.
- **Refcounted Zero-Copy Arenas (`sdk/lib/driver/runtime/include/lib/fdf/arena.h:12-84`):** Senders allocate messages directly inside an `fdf_arena_t*` (`fdf_arena_create`, `fdf_arena_allocate`, `fdf_arena_contains`) and pass an arena reference alongside `fdf_channel_write` (`L18-21`), achieving zero-copy payload ownership transfer inside a `driver_host` until the final consumer calls `fdf_arena_drop_ref`.
- **FIDL Wire Format v2 Evolution & Handle-Leak Subtlety (`fidl_wire_format.md:427-495`, `RFC-0126:917-938`):** Evolvable FIDL `table` and `flexible union` types encode each field inside a fixed **8-byte envelope** carrying `(num_bytes_or_inline, num_handles, flags)` where `flags & 1` denotes an inline `<= 4`-byte value and `0` denotes an out-of-line 8-byte-aligned payload (`fidl_wire_format.md:429-453`). Receivers seamlessly skip unknown ordinals by advancing `num_bytes` and closing `num_handles` handles. Critically, `RFC-0126:917-938` identifies a subtle tension: skipping FIDL encoding/linearization altogether inside `fdf_arena` saves a copy, *but* makes the receiver blind to Zircon handles embedded inside unknown table/union fields—leaking kernel resources unless a partial out-of-band handle table is still stripped on send and drained on receive (`L931-937`).

#### 3.4 Rust-for-Linux (`torvalds/linux` @ `4405c18c...`, `Rust-for-Linux/pin-init` @ `578ad6b8...`)

Rather than stabilizing a binary ABI, Rust-for-Linux embraces Linux's in-tree co-evolution model (`10.1109/ACSAC63791.2024.00054` and Asahi Lina's M1 GPU driver experience, where upstream C API refactors break out-of-tree assumptions immediately while in-tree Rust wrappers catch changes at compile time) and eliminates C FFI invariant drift at compile time:

- **`Opaque<T>` (`torvalds/linux` `rust/kernel/types.rs:331-432`):** Wraps C-owned structs (`struct mutex`, `struct device`, `struct folio`) in `#[repr(transparent)] pub struct Opaque<T> { value: UnsafeCell<MaybeUninit<T>>, _pin: PhantomPinned }`, disabling Rust's strict validity invariants (e.g., `bool` `0/1`, initialized padding), suppressing `noalias` uniqueness assumptions even when `&Opaque<T>` coexists with concurrent C mutation, and pinning the slot (`L283-296`).
- **`PinInit<T, E>` (`Rust-for-Linux/pin-init` `src/lib.rs:973-1055`):** C kernel structs frequently embed self-referential `list_head`, `spinlock_t`, or `wait_queue_head` pointers whose address must never change post-initialization. Standard Rust `Self { ... }` constructors construct values on the stack and `memcpy`-move them into `Box`/`Arc`, invalidating self-pointers. `PinInit<T, E>` passes the destination `*mut T` slot directly into an in-place initializer closure (`pin_init_from_closure`), running sub-field C `init` hooks in-place and cleaning up partially initialized fields automatically on fallible `Err(e)` paths (`raw_try_init`, `L1052-1055`).
- **`Lock<T, B>` & Lockdep Type Tokens (`rust/kernel/sync/lock.rs:104-324`):** Couples the protected data `UnsafeCell<T>` directly inside the pinned C lock struct (`#[pin_data] struct Lock<T, B>`), requires a pinned `&'static LockClassKey` for kernel lockdep cycle checking at creation (`L131-145`), and permits access to `&mut T` / `Pin<&mut T>` strictly through the RAII `Guard<'a, T, B>` (`!Send` via `NotThreadSafe`, `L204`, unlocking on `Drop`, `L299-305`).

### 4. Six-Level Performance, Verification, and Footprint Matrix (`L1`–`L6`)

**Basis:** `source` (inspected frameworks and `libbpf` / `gendwarfksyms` / `IOUserServer`) + `normative` (`RFC-0126`, `PREVAIL` `10.1145/3314221.3314590`, `HotOS 2023` `10.1145/3593856.3595892`, `EuroSys 2024` `10.1145/3627703.3629562`, `ACSAC 2024` `10.1109/ACSAC63791.2024.00054`) + `derived` (architectural scaling and cycle-class bounds from trap/copy/table mechanisms).

| Dimension | Linux `.ko` (`MODVERSIONS` + `gendwarfksyms`) | eBPF CO-RE (`libbpf`) | Windows KMDF (`Wdf01000.sys`) | macOS DriverKit (`IOUserServer`) | Fuchsia DFv2 (`fdf_arena` + FIDL v2) | Rust-for-Linux (`pin-init` + `Opaque<T>`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **(L1) Authoring & Day-2 Maintenance Velocity** | Zero wrapper boilerplate inside tree; **high Day-2 rebase toil** for out-of-tree `.ko` drivers across kernel releases (`stable-api-nonsense.rst`) | Moderate (requires `BPF_CORE_READ` macros + verifier appeasement loops; silent Day-2 breakage across semantic lock/RCU shifts) | Low Day-2 binary churn across Windows updates (`1.15 -> 1.33`), moderate C config/context macro boilerplate | Moderate (`.iig` IDL + async `OSAction` + `IOMemoryDescriptor` lifecycle callbacks) | Low-moderate (`.fidl` schema + explicit `fdf::Arena` + async dispatcher wiring; avoids Banjo reentrancy bugs) | High initial `unsafe` wrapper/abstraction audit cost (`ACSAC 2024`); **very low Day-2 driver breakage** as compiler catches C drift immediately |
| **(L2) Framework & Toolchain Build Time** | `genksyms` adds per-TU C preprocessing; `gendwarfksyms` needs full `-g` DWARF generation (`libdw` pass at link time) | Requires `vmlinux` DWARF -> BTF deduplication (`pahole -J`) during kernel build | SDK header/stub generation (`stubwork`, `wdfglobals.h`); drivers compile independently of OS tree | `.iig` (`iig` compiler) + Xcode DriverKit SDK build; independent of XNU build | `fidlc` + `fidlgen_cpp`/`rust` codegen; driver links `libdriver_runtime.so` | Requires `bindgen` over kernel headers + `rustc` with `pin-init` proc macros (`CONFIG_RUST`); incremental rebuilds track C header hashes |
| **(L3) Compile, Relocation & Synthesis Speed** | C/Rust compile-time layout fixed; zero load-time field relocation | Clang emits `.BTF.ext` relos at compile time; `libbpf` `bpf_core_calc_relo_insn` resolves candidates in `O(cands * spec_len)` (`<= 64` steps) in **single-digit ms** at load | Static stub binds once at `DriverEntry` (`WdfVersionBind`) | `.iig` generates C++ Mach RPC stubs statically | `fidlc` validates wire layouts statically; zero runtime struct relocation | Monomorphizes `PinInit` closures statically (`#[inline(always)]` `raw_try_init`, `pin_init_lib.rs:1036-1055`); zero runtime overhead |
| **(L4) Runtime Call, Isolation & IPC Performance** | Direct C function call / inline field offset (`~1–3` cycles; **0 trap/copy**) | Direct patched load/store (`1–3` cycles) or `bpf_probe_read_kernel` helper call (`~15–40` cycles + page-fault handling) | Indirect call through `WdfFunctions[idx]` + XOR handle unscramble (`handle ^ ~0x7`) + `GET_CONTEXT_HEADER()` pointer arithmetic (`~5–20` cycles) | Cross-process **Mach IPC** syscall trap + `IORPC` serialization + DART IOMMU mapping (`IOMapper`); microsecond-class control latency (`~1.5–5+ us`) | **Two-tier:** in-process `fdf_channel_write` + zero-copy `fdf_arena` refcount transfer (~sub-microsecond, no kernel trap) vs cross-process `zx_channel_call` kernel IPC + copy/linearization | Direct inline C FFI / monomorphized Rust (`~1–3` cycles; identical to C `.ko` once compiled; `Guard` compiles away to lock/unlock calls) |
| **(L5) Load / Admission Verification Speed** | `check_version()` scans `__versions` CRC table (`module/version.c:48-64`) in **`< 1 ms`** (`0` semantic safety proof) | Linux kernel BPF verifier runs abstract-interpretation fixed point (capped at `1M` processed insns; `10–200+ ms` on complex loops; vulnerable to logic bugs `10.1145/3627703.3629562`, `HotOS 2023`) | WHQL Authenticode signature + `WdfBindClientHelper` major/minor check (`< 1–5 ms`; no bounds check on custom data interpreters) | Code-signed `.dext` entitlement check (`DriverKit` entitlements) + IOMMU hardware DMA isolation | Capability routing (Component Framework) + optional `fidlc` wire validation (`RFC-0126:547-563` skips redundant handle-rights checks inside same `driver_host`) | Verified **at compile time** by `rustc` borrow/lifetime checker + `PinInit` invariants; load admission reduces to standard `.ko` `check_version` CRC |
| **(L6) Memory, Artifact & Binary Footprints** | `.ko` carries `__versions` / `___kcrctab+` CRC tables; optional DWARF stripped post-`gendwarfksyms` | Kernel `vmlinux` embeds ~`4–6 MB` deduplicated `.BTF` section in non-pageable kernel memory or `/sys/kernel/btf/vmlinux` | `FxObject` + `FxContextHeader` (`fxhandle.h:62-93`, ~48–64B header per WDF object) + `WdfFunctions` table; shared `Wdf01000.sys` runtime | Separate userspace `.dext` process address space + Mach port tables + DART IOMMU page tables + `OSDataAllocation` bounce buffers | Per-`driver_host` process RSS + `fdf_arena` slab pools; FIDL v2 table headers cost `8 B` per sparse ordinal (`fidl_wire_format.md:430,459`) | Zero runtime type/BTF metadata; `Opaque<T>` (`#[repr(transparent)]`) and `Lock<T, B>` (`#[repr(C)]`) add **0 bytes** over raw C structs (aside from explicit Rust metadata) |

*(Note: Quantitative latencies in `(L4)`/`(L5)`/`(L6)` reflect architectural bounds derived from syscall/trap/IOMMU mechanisms and documented kernel verifier limits in `PREVAIL`/`HotOS 2023`; exact microbenchmark ns figures depend on host CPU, kernel version, and IOMMU TLB state.)*

### 5. Human Comprehensibility (`C1`) and Universal Conceptual Simplicity (`C2`)

**Basis:** `derived` from inspected architectures (`torvalds/linux`, `libbpf`, `microsoft/Windows-Driver-Frameworks`, `xnu`, `fuchsia`, `Rust-for-Linux`) and `HotOS 2023` (`10.1145/3593856.3595892`).

#### 5.1 (C1) Human Comprehensibility & Day-2 Diagnostic Legibility

- **Implicit C Lock/Lifetime Assumptions (Linux `.ko` & CO-RE):** A driver author reading `vma->vm_flags` in C or `BPF_CORE_READ(vma, vm_flags)` sees no mention of `mmap_lock` vs `vma_lock`, RCU grace periods, or `folio` aliasing in the type signature. Comprehensibility requires **global working memory** across dozens of undocumented `.c` callsites; failures manifest nonlocally as sporadic production deadlocks, verifier `R1 offset is outside of the packet` state-pruning errors (`HotOS 2023`), or silent stale reads.
- **Indirection-Masked Errors (KMDF):** When a KMDF driver passes a corrupt `WDFOBJECT` or leaks a context reference, `FxObject::_GetObjectFromHandle` crashes in `FxVerifierBugCheck(WDF_INVALID_HANDLE)` (`fxhandle.h:397`), hiding the underlying C++ object behind XOR masking and requiring Windows Driver Verifier / WinDbg `!wdfkd` triage extensions to invert `handle ^ FxHandleValueMask`.
- **Local Auditable Contracts (FIDL + `PinInit` + `Lock<T, B>`):** Fuchsia `.fidl` files fit a protocol's wire evolution contract, optionality, and capability permissions on **< 1 page**, isolating wire-mismatch bugs to explicit `unknown` ordinal paths. Similarly, Rust-for-Linux `Lock<T, B>` and `PinInit<T, E>` lift lock ownership and address stability into **local type-level preconditions** so the compiler rejects missing lock guards or stack-moving constructors before code links—at the remaining C1 cost of macro-expanded `pin_init!` diagnostics when traits fail to unify.

#### 5.2 (C2) Simplicity, Adapter Conservation & Minimal Universal Representation

Evaluating each mechanism under **adapter conservation** exposes where complexity was genuinely eliminated versus merely relocated:

1. **CO-RE and KMDF relocate ABI complexity rather than eliminating it:** eBPF CO-RE shifts compile-time header synchronization out of build pipelines—only to push lock/RCU/folio *semantic coupling* onto runtime bugs with zero static checking. KMDF eliminates direct C++ struct offset dependencies across `Wdf01000.sys` updates—at the cost of dual layers (`WDFFUNCENUM` + `.Size` headers + XOR handles + `FxContextHeader`), while leaving drivers vulnerable to arbitrary Ring-0 memory corruption (CrowdStrike Channel File 291).
2. **DriverKit's coarse Mach IPC eliminates Ring-0 panics by pushing copy/IOMMU complexity onto every call path**, even when communicating components share trust.
3. **Minimal Universal Kernel-Driver Architecture (*Capability-Routed Schema-Typed Zero-Copy Arenas + Linear Ownership/Typestate Tokens*):** Combining Fuchsia DFv2's transport boundary split with Rust-for-Linux's linear resource types collapses six ad-hoc ABI adapters (`genksyms`, `gendwarfksyms` kABI rules, CO-RE `.BTF.ext` relocations, KMDF `WDFFUNCENUM`/XOR handles, DriverKit bounce copies, and unguarded C locks) into **two orthogonal primitives**:
   - **Across Trust / Upgrade Domains (Isolated Driver Hosts):** Explicit schema-evolving **Envelope Tables over Capability-Bounded Zero-Copy Arenas** (FIDL v2 `8 B` envelopes + out-of-band handle tables + IOMMU-scoped DMA descriptors). Receivers skip unknown extensions safely, kernel-level crashes are impossible, and co-located drivers pay zero serialization copies while preserving wire compatibility.
   - **Within Co-Evolved Kernel Fast Paths:** **Pinned Linear Ownership & Lock-Token Wrappers (`PinInit<T>` + `Lock<T, B>` + `Opaque<T>`)** compiled statically with no binary ABI promise. Because lock guards and in-place initialization lifetimes are verified once by the type checker, neither load-time bytecode verifiers (`1M`-insn limits) nor field-offset guessers are needed.

## Boundaries

- **eBPF Arena / BPF Tokens / Kernel `struct_ops` Extensions:** `not examined` in detail beyond `libbpf` `relo_core.{h,c}` CO-RE field/type relocations; `bpf_arena` user-kernel shared pointers and `BPF_PROG_TYPE_STRUCT_OPS` callback-table versioning introduce additional verifier constraints not profiled here.
- **Linux `gendwarfksyms` Implementation Internals (`dwarf.c`, `types.c`) Beyond Header & `kabi.c`:** Exact DWARF DIE canonicalization string formatting in `scripts/gendwarfksyms/{dwarf.c,types.c}` was `not examined`; only `gendwarfksyms.h` and `kabi.c` rule parsing were inspected directly.
- **Exact Quantitative Latency Benchmarks Across Hardware:** Micro-second/cycle ranges in `## Findings §4` (`L4`–`L6`) are `derived` architectural bounds from inspected IPC/syscall/IOMMU/table code paths (`IOUserServer.cpp`, `RFC-0126`, `fxobject.hpp`, `relo_core.c`) and cited verifier papers, not same-hardware microbenchmark runs (because Windows KMDF, macOS DriverKit, and Fuchsia kernels cannot execute natively inside the Linux analysis environment).
- **CO-RE Preservation of Synchronization Semantics:** `known not to apply`—inspected `libbpf/src/relo_core.c` performs purely structural BTF type/offset/bitfield/existence matching (`bpf_core_calc_relo_insn`) and carries no representation of locks, RCU grace periods, refcounts, or compound page invariants.
- **Stable Binary Driver ABI in Upstream Linux:** `unsupported` by normative Linux kernel policy (`Documentation/process/stable-api-nonsense.rst`) and actively broken by `RANDSTRUCT` (`scripts/gcc-plugins/randomize_layout_plugin.c`).
- **Handle Leak Prevention in Unlinearized Fuchsia `fdf_arena` Messages Without Handle Tables:** `unknown` at runtime if an implementation omits RFC-0126's proposed partial handle-table extraction (`RFC-0126:917-938`) for unknown table/union fields; Fuchsia's production `fidlgen_cpp` driver-transport implementation details beyond RFC-0126 and `fdf/arena.h` were `not examined`.

## Evidence

- **Linux Kernel Mainline (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):**
  - `Documentation/process/stable-api-nonsense.rst` (L1–204): Normative rationale against stable in-kernel binary and source driver interfaces.
  - `include/linux/export-internal.h` (L40–78) & `kernel/module/version.c` (L13–146): `__KSYMTAB`, `SYMBOL_CRC`, `check_version()`, `check_modstruct_version()`, `module_layout`.
  - `scripts/genksyms/genksyms.c` (L119–133, L565–638): Preprocessed C token CRC32 calculation.
  - `scripts/gendwarfksyms/gendwarfksyms.h` (L79–289) & `scripts/gendwarfksyms/kabi.c` (L12–140): DWARF DIE traversal and `.discard.gendwarfksyms.kabi_rules` (`declonly`, `enumerator_ignore`, `enumerator_value`, `byte_size`, `type_string`).
  - `scripts/gcc-plugins/randomize_layout_plugin.c` (L426–565, L915–931): `__randomize_layout`, `is_pure_ops_struct`, 256-bit `randstruct_seed`.
  - `rust/kernel/types.rs` (L278–432) & `rust/kernel/sync/lock.rs` (L37–324): `Opaque<T>`, `Backend`, `Lock<T, B>`, `Guard<'a, T, B>`.
- **Rust-for-Linux (`Rust-for-Linux/linux` @ `aebb7274476403040d582c61478df8f4a7bf9cd3`; `Rust-for-Linux/pin-init` @ `578ad6b8f9d136aeb365f2175f6ef9f0e3dab288`):**
  - `Rust-for-Linux/linux/rust/kernel/sync/lock.rs` (L104–324): `#[pin_data] struct Lock<T, B>` & `Guard` RAII unlock.
  - `Rust-for-Linux/pin-init/src/lib.rs` (L970–1075): `PinInit<T, E>`, `raw_init`, `raw_try_init`, `ChainPinInit`.
- **eBPF CO-RE (`libbpf/libbpf` @ `4f05fb027a08a8a66d03916cf6a68a91e2c720ea`):**
  - `src/relo_core.h` (L20–69): `BPF_CORE_SPEC_MAX_LEN = 64`, `bpf_core_accessor`, `bpf_core_spec`, `bpf_core_relo_res`.
  - `src/relo_core.c` (L690–860, L968–1160, L1301–1441): `bpf_core_calc_relo_insn`, `bpf_core_poison_insn` (`0xbad2310`), `bpf_core_patch_insn` (including `res->new_sz != res->orig_sz` mem-size adjustment).
  - `src/bpf_core_read.h` (L15–147): `__builtin_preserve_field_info`, `BPF_CORE_READ_BITFIELD{_PROBED}`.
- **Windows KMDF (`microsoft/Windows-Driver-Frameworks` @ `b6191d9543441329154da32f7ab9bdd97228dd3c`):**
  - `src/framework/kmdf/src/dynamic/version/version.cpp` (L470–540): `WDF_LIBRARY_REGISTER_CLIENT`, `WdfBindClientHelper`.
  - `src/publicinc/wdf/kmdf/1.33/wdffuncenum.h` (L25–32, L735–747) & `wdfglobals.h` (L53–72): `WDF_ALWAYS_AVAILABLE_FUNCTION_COUNT = 453`, `WDF_STRUCTURE_TABLE_NUM_ENTRIES = 81`, `WDF_DRIVER_GLOBALS`.
  - `src/framework/shared/inc/private/common/fxhandle.h` (L30–98, L380–427), `fxobject.hpp` (L457–473, L604, L625–680), `fxversionedstructures.h` (L31–60): `FxContextHeader`, `_ToHandle` (`Object ^ FxHandleValueMask`), `_GetObjectFromHandle`.
- **macOS DriverKit (`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`):**
  - `iokit/Kernel/IOUserServer.cpp` (L666–741, L951–1230, L2870–3025): `IOMemoryDescriptor::CreateMapping_Impl`, `IODMACommand::{Create,PrepareForDMA,CompleteDMA,PerformOperation}_Impl` (`IOMapper::copyMapperForDevice`, `OSDataAllocation`), Mach `IORPC` dispatch.
- **Fuchsia DFv2 & FIDL (`fuchsia.googlesource.com/fuchsia` @ `15f8bdfdea9a506c78363f84b842dae3b61e120f`):**
  - `docs/contribute/governance/rfcs/0126_driver_runtime.md` (L11–116, L491–617, L917–938, L1027–1045): In-process `driver_host`, reentrancy elimination, leaked-handle subtlety on unlinearized unknown fields.
  - `sdk/lib/driver/runtime/include/lib/fdf/arena.h` (L12–84): `fdf_arena_{create,allocate,free,contains,add_ref,drop_ref}`.
  - `docs/reference/fidl/language/wire-format/README.md` (L427–495): 8-byte `Envelope`, `Tables`, and `Unions` wire evolution.
- **Peer-Reviewed & Non-Academic Primary Sources:**
  - Gershuni et al., *Simple and Precise Static Analysis of Untrusted Linux Kernel Extensions*, PLDI 2019 (`DOI: 10.1145/3314221.3314590`).
  - Jia et al., *Kernel Extension Verification is Untenable*, HotOS 2023 (`DOI: 10.1145/3593856.3595892`).
  - Sun et al., *Finding Correctness Bugs in eBPF Verifier*, EuroSys 2024 (`DOI: 10.1145/3627703.3629562`).
  - Li et al., *Rust for Linux: Understanding the Security Impact of Rust in the Linux Kernel*, ACSAC 2024 (`DOI: 10.1109/ACSAC63791.2024.00054`).
  - Non-academic engineering reports & disclosures: Linux `stable-api-nonsense.rst`; LWN.net Linux 6.14 `gendwarfksyms` engineering summaries; Andrii Nakryiko *BPF CO-RE Reference Guide*; CrowdStrike Falcon Channel File 291 Root Cause Analysis (Aug 2024) and Microsoft Windows Resiliency Initiative (2024).
- **Self-Contained Executable Micro-Probe (`python3`):**

```bash
python3 - <<'PY'
from dataclasses import dataclass

@dataclass(frozen=True)
class Field:
    name: str
    offset: int
    size: int
    lock_guard: str

def core_relocate(local_struct: dict[str, Field], target_struct: dict[str, Field], field_name: str, expected_lock: str) -> dict:
    lf = local_struct[field_name]
    tf = target_struct.get(field_name)
    if tf is None:
        return {"status": "poisoned", "insn_imm": 0xbad2310}
    return {
        "status": "patched",
        "orig_off": lf.offset,
        "new_off": tf.offset,
        "orig_sz": lf.size,
        "new_sz": tf.size,
        "syntactic_ok": True,
        "semantic_ok": (tf.lock_guard == expected_lock),
        "target_lock": tf.lock_guard,
    }

def kmdf_context_layout(base_addr: int, raw_cpp_obj_size: int, align: int = 16, ctx_hdr_size: int = 48) -> dict:
    assert (base_addr & 0x7) == 0
    m_obj_size = (raw_cpp_obj_size + align - 1) & ~(align - 1)
    fx_handle_value_mask = ((1 << 64) - 1) ^ 0x7
    wdf_handle = (base_addr ^ fx_handle_value_mask) & ((1 << 64) - 1)
    driver_ctx_ptr = base_addr + m_obj_size + ctx_hdr_size
    assert (((wdf_handle & ~0x7) ^ fx_handle_value_mask) & ((1 << 64) - 1)) == base_addr
    return {
        "base_addr": hex(base_addr),
        "m_object_size": m_obj_size,
        "wdf_handle": hex(wdf_handle),
        "driver_ctx_ptr": hex(driver_ctx_ptr),
    }

def fidl_v2_envelope_decode(envelopes: list[tuple[int, int, int]], known_ordinals: set[int]) -> dict:
    decoded, skipped_unknown, closed_handles = [], [], 0
    for idx, (word0, num_handles, flags) in enumerate(envelopes, start=1):
        if word0 == 0 and num_handles == 0 and flags == 0:
            continue
        is_inline = bool(flags & 1)
        if idx in known_ordinals:
            decoded.append((idx, "inline" if is_inline else "ool", word0, num_handles))
        else:
            skipped_unknown.append(idx)
            closed_handles += num_handles
    return {"decoded": decoded, "skipped_unknown": skipped_unknown, "closed_handles": closed_handles}

kernel_v5_15 = {
    "mm_lock": Field("mmap_lock", 96, 8, "mmap_lock"),
    "vm_flags": Field("vm_flags", 80, 4, "mmap_lock"),
    "legacy_field": Field("legacy_field", 104, 4, "mmap_lock"),
}
kernel_v6_6_split = {
    "mm_lock": Field("mmap_lock", 112, 8, "mmap_lock"),
    "vm_flags": Field("vm_flags", 88, 8, "vma_lock_plus_mmap_write"),
}
print("core_relo_vm_flags:", core_relocate(kernel_v5_15, kernel_v6_6_split, "vm_flags", "mmap_lock"))
print("core_relo_missing:", core_relocate(kernel_v5_15, kernel_v6_6_split, "legacy_field", "mmap_lock"))

v1_15 = kmdf_context_layout(0xffff880012340000, raw_cpp_obj_size=248)
v1_33 = kmdf_context_layout(0xffff880012340000, raw_cpp_obj_size=312)
assert v1_15["wdf_handle"] == v1_33["wdf_handle"]
print("kmdf_v1_15:", v1_15)
print("kmdf_v1_33:", v1_33)

fidl_res = fidl_v2_envelope_decode([(0x2a, 0, 1), (0, 0, 0), (24, 2, 0)], known_ordinals={1, 2})
assert fidl_res["closed_handles"] == 2 and fidl_res["skipped_unknown"] == [3]
print("fidl_v2_table:", fidl_res)
PY
```

Recorded execution output (`2026-11-19`):

```text
core_relo_vm_flags: {'status': 'patched', 'orig_off': 80, 'new_off': 88, 'orig_sz': 4, 'new_sz': 8, 'syntactic_ok': True, 'semantic_ok': False, 'target_lock': 'vma_lock_plus_mmap_write'}
core_relo_missing: {'status': 'poisoned', 'insn_imm': 195896080}
kmdf_v1_15: {'base_addr': '0xffff880012340000', 'm_object_size': 256, 'wdf_handle': '0x77ffedcbfff8', 'driver_ctx_ptr': '0xffff880012340130'}
kmdf_v1_33: {'base_addr': '0xffff880012340000', 'm_object_size': 320, 'wdf_handle': '0x77ffedcbfff8', 'driver_ctx_ptr': '0xffff880012340170'}
fidl_v2_table: {'decoded': [(1, 'inline', 42, 0)], 'skipped_unknown': [3], 'closed_handles': 2}
```

## Revalidation

To test whether these architectural boundaries change against newer upstream revisions:

1. **Linux `gendwarfksyms` & Rust `Opaque<T>`/`Lock<T, B>`:** Fetch `scripts/gendwarfksyms/gendwarfksyms.h`, `scripts/gendwarfksyms/kabi.c`, and `rust/kernel/{types.rs,sync/lock.rs}` at target `<rev>` and verify supported `.discard.gendwarfksyms.kabi_rules` rule types and `Opaque<T>`/`Lock<T, B>` field invariants:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/torvalds/linux/<rev>/scripts/gendwarfksyms/kabi.c" | grep "KABI_RULE_TAG_"
   curl -sSL "https://raw.githubusercontent.com/torvalds/linux/<rev>/rust/kernel/types.rs" | grep -A8 "pub struct Opaque"
   ```
2. **eBPF CO-RE Semantic Enforcement Check:** Inspect `src/relo_core.c` (`bpf_core_calc_relo_insn` and `bpf_core_poison_insn`) at newer `libbpf/libbpf` revisions to check whether any lock/RCU/lifetime annotations were added beyond `BPF_CORE_FIELD_*`/`BPF_CORE_TYPE_*`:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/libbpf/libbpf/<rev>/src/relo_core.c" | grep -E "case BPF_CORE_|0xbad2310"
   ```
3. **KMDF Handle/Table & Fuchsia DFv2 Arena/Wire Checks:** Inspect `wdffuncenum.h` (`WDF_ALWAYS_AVAILABLE_FUNCTION_COUNT`, `WDF_STRUCTURE_TABLE_NUM_ENTRIES`), `fxobject.hpp` (`_ToHandle`), and Fuchsia's `sdk/lib/driver/runtime/include/lib/fdf/arena.h` + `docs/contribute/governance/rfcs/0126_driver_runtime.md` (handle-table handling for unlinearized driver messages) and re-run the Python micro-probe in `## Evidence`.
