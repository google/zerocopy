# Cross-Platform Windows and macOS Media Sandboxing, Remaining AVHWDeviceType C-ABI Layouts, and Drop-In cdylib Binary Compatibility

## Summary

Drop-in cross-platform replacement of FFmpeg's shared libraries (`libavutil`, `libavcodec`, `libavformat`, `libavfilter`, `libswscale`, `libswresample`, `libavdevice`) by a memory-safe Rust implementation with out-of-process isolation for retained C/C++ encoders (`libx264`, `libx265`, `SVT-AV1`) and cryptographic transport helpers requires platform-specific OS sandboxing primitives, hardware-context struct layouts, and dynamic-linker ABI contracts that differ structurally from Linux ELF + `memfd_create` (`F_SEAL_FUTURE_WRITE`) + `seccomp-bpf`:

1. **Windows and macOS Zero-Copy Shared-Memory Rings and Process Containment (`Basis: source + documentation + normative`):**
   - **Windows NT (`x86_64` / `aarch64`):** Linux inode-level `F_SEAL_FUTURE_WRITE` has no direct object-level equivalent on NT section objects (`CreateFileMappingW`). Instead, read-only zero-copy input rings rely on **per-handle `ACCESS_MASK` stripping**: the broker creates a pagefile-backed `PAGE_READWRITE` section with an explicit **empty DACL** (`InitializeAcl` + `SetSecurityDescriptorDacl`), strips `WRITE_DAC | WRITE_OWNER | DELETE` from its own writable handle via `DuplicateHandle`, and duplicates a worker handle with `dwDesiredAccess = SECTION_MAP_READ | SECTION_QUERY` (`0x0005`, omitting `FILE_MAP_WRITE` and `SECTION_EXTEND_SIZE`). The NT Memory Manager (`NtMapViewOfSection`) caps any worker `VAD` mapped from that handle at `MM_READONLY`, rejecting `MapViewOfFile(..., FILE_MAP_WRITE)` and `VirtualProtect(..., PAGE_READWRITE)` with `STATUS_ACCESS_DENIED` (`0xC0000022`). Worker containment combines an AppContainer (`CreateAppContainerProfile` + `PROC_THREAD_ATTRIBUTE_SECURITY_CAPABILITIES`) or low/untrusted-integrity Restricted Token (`CreateRestrictedToken` with `DISABLE_MAX_PRIVILEGE`), a Job Object (`JOB_OBJECT_LIMIT_ACTIVE_PROCESS = 1`, `JOB_OBJECT_LIMIT_PROCESS_MEMORY`, `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE`, `JOB_OBJECT_UILIMIT_ALL`), and birth-time / early-init `SetProcessMitigationPolicy` (`ProcessDynamicCodePolicy` with `ProhibitDynamicCode = 1`, and `ProcessSystemCallDisablePolicy` with `DisallowWin32kSystemCalls = 1`). Because `libx264`, `libx265`, and `SVT-AV1` dispatch pre-assembled AOT `.obj` SIMD kernels via CPUID function tables rather than runtime JIT, `ProhibitDynamicCode = 1` does not impede SIMD acceleration.
   - **macOS / Darwin (`arm64` / `x86_64`):** High-level `xpc_shmem_create` inherits the creator's `VM_PROT_READ | VM_PROT_WRITE` maximum protection and provides no mechanism to strip write rights for an XPC recipient, while `IOSurfaceLock(..., kIOSurfaceLockReadOnly, ...)` is an advisory CPU/GPU cache-coherency protocol that a compromised worker holding an `IOSurfaceRef` send right can bypass by calling `IOSurfaceLock(surface, 0, NULL)`. Live zero-copy host-writable / worker-read-only rings on XNU must instead export a Mach named memory entry via `mach_make_memory_entry_64(mach_task_self(), &size, (memory_object_offset_t)ring_va, MAP_MEM_VM_SHARE | VM_PROT_READ, &ro_port, MACH_PORT_NULL)` (`xnu` `osfmk/vm/vm_memory_entry.c:653,740-748,848-860,1184-1189`). Including `MAP_MEM_VM_SHARE` shares the live `vm_object_t` pages rather than snapshotting copy-on-write, while setting `user_entry->protection = VM_PROT_READ` forces recipient `mach_vm_map` mappings to `max_protection = VM_PROT_READ` (`mach_vm_protect(..., VM_PROT_WRITE)` fails with `KERN_PROTECTION_FAILURE`). XPC worker processes combine Seatbelt profiles (`sandbox_init` / App Sandbox denying `file-read*`, `file-write*`, outbound `network*`, and `iokit-open` GPU/IOSurface user clients) with Hardened Runtime code-signing flags (`CS_RUNTIME | CS_HARD | CS_KILL | CS_REQUIRE_LV` in `osfmk/kern/cs_blobs.h:44-55`, omitting `com.apple.security.cs.allow-jit`).

2. **Remaining Nine `AVHWDeviceType` C-ABI Layouts and Ownership Invariants (`Basis: source + execution`):**
   - Across `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, a 64-bit C11 `sizeof`/`_Alignof`/`offsetof` probe over all nine `libavutil/hwcontext_{drm,videotoolbox,mediacodec,qsv,opencl,vdpau,dxva2,amf,oh}.h` headers and their five companion `libavcodec/{videotoolbox,mediacodec,qsv,vdpau,dxva2}.h` headers establishes exact byte layouts and zero packing divergence between SysV LP64 and `-mms-bitfields` (once Windows `DWORD` is fixed at 4-byte `uint32_t`). Critical layout and ownership invariants include: `AVDRMFrameDescriptor` is **528 bytes** (`objects[4]` at offset 8, `layers[4]` at offset 112); `AVVDPAUDeviceContext` (16 B) and `AVVDPAUContext` (24 B) embed **32-bit `uint32_t` handles** (`VdpDevice`, `VdpDecoder`), while `hwcontext_vdpau.c` stores `(uint8_t *)(uintptr_t)VdpVideoSurface`—a non-dereferenceable integer-in-pointer—inside `AVFrame.data[3]`; hardware frame payload slots split across `AVFrame.data[0]` (`DRM`, `AMF`), `AVFrame.data[0..nb_planes-1]` (`OpenCL`), and `AVFrame.data[3]` (`VideoToolbox`, `QSV`, `VDPAU`, `DXVA2`, `MediaCodec`); and five backends (`VideoToolbox`, `MediaCodec`, `QSV`, `VDPAU`, `DXVA2`) allocate larger private wrapper structs (`VTFramesContext`, `MediaCodecDeviceContext`, `QSVDeviceContext`, `VDPAUDeviceContext`, `DXVA2FramesContext`) behind `AVHWDeviceContext.hwctx` / `AVHWFramesContext.hwctx`, forbidding caller-side struct reallocation or `sizeof`-based copying.

3. **Windows LLP64 (`.dll`) and macOS Mach-O (`.dylib`) Drop-In `cdylib` Contracts (`Basis: source + execution + normative`):**
   - **Windows LLP64 (`sizeof(unsigned long) == 4`):** Scanning 57 public FFmpeg headers at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` isolates `AVIOContext` (`libavformat/avio.h:244-246`) as a critical 64-bit layout divergence: `unsigned long checksum` sits immediately after five 4-byte `int` fields (`offset 100` with 0 padding on Windows x64 LLP64 vs `offset 104` after 4 bytes of alignment padding on Linux/macOS LP64), shrinking `sizeof(AVIOContext)` from **208 bytes (LP64) to 200 bytes (Windows x64 LLP64)** and shifting **13 subsequent public fields** (`checksum_ptr`, `update_checksum`, `read_pause`, `read_seek`, etc.) by **-8 bytes**. Rust FFI definitions must type `checksum` and `update_checksum` with `core::ffi::c_ulong`, never `u64` or `usize`.
   - **`va_list`, C `enum` Signedness, and Mach-O `__TEXT,__unwind_info`:** `va_list` (`av_vlog`, `av_log_set_callback`, `av_vbprintf`, `avio_vprintf`) is an 8-byte `char *` on Windows x64 and macOS `arm64`, a 24-byte `struct __va_list_tag[1]` (passed as `&tag[0]`) on x86_64 SysV/macOS, and a 32-byte `struct __va_list` on Linux AArch64. Non-negative C enums (`enum AVHWDeviceType`, `enum AVColorRange`, `enum AMF_MEMORY_TYPE`) compile to `u32` under SysV GCC/Clang C11 but `i32` under MSVC `cl.exe`, and must be typed as transparent integer newtypes in Rust (`#[repr(transparent)] pub struct AVHWDeviceType(pub c_int)` / `c_uint`) to avoid UB on out-of-range C inputs. On macOS, `ld64` / `lld` packs `__LD,__compact_unwind` into `__TEXT,__unwind_info` using a 2-bit personality index (`UNWIND_PERSONALITY_MASK = 0x30000000`), causing a hard link error if a single `.dylib` references **more than 3 distinct unwind personality functions** (`llvm/llvm-project` `lld/MachO/UnwindInfoSection.cpp:436-438`) and zeroing the 24-bit fast-lookup hint when `__TEXT,__eh_frame` exceeds **16 MiB (`0x00FFFFFF`)**.

## Applicability

This report governs non-Linux host/worker isolation, hardware-acceleration context FFI, and shared-library binary compatibility for clean-room Rust replacements of FFmpeg targeting **Windows 10/11 (`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`)** and **macOS 11+ (`aarch64-apple-darwin`, `x86_64-apple-darwin`)**, alongside the cross-platform C-ABI struct layouts of the nine `AVHWDeviceType` headers not covered in `ffmpeg-c-abi-libav-struct-layout-callbacks-and-rust-ffi-compatibility-layer` or `hardware-video-acceleration-apis-vaapi-nvdec-vulkan-video-videotoolbox-mediacodec`.

Relationships among the twelve subjects recorded in `REPORT.json`:
- **`FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`** defines the target C ABI: library major versions (`libavutil` 61, `libavcodec` 63, `libavformat` 63, `libavdevice` 63, `libavfilter` 12, `libswscale` 10, `libswresample` 7), `libavutil/hwcontext*.h` and `libavcodec/{videotoolbox,mediacodec,qsv,vdpau,dxva2}.h` struct layouts, `libavutil/hwcontext_*.c` ownership lifecycles, `libavformat/avio.h` and `libavutil/log.h` ABI surfaces, `configure` Darwin/MinGW/MSVC shared-library link flags, and `compat/windows/makedef` PE export generation.
- **`chromium/chromium@35a0816efc03ad8fed8920050497050ed1d23a08`**, **`apple-oss-distributions/xnu@f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`**, and **`mingw-w64/mingw-w64@7095c702af7836f12a4d904555546d6abbf28b2c`** provide verified kernel and user-space source definitions for Windows NT section handle permission stripping, AppContainer / mitigation / Job Object structures, and XNU `mach_make_memory_entry_64`, `mach_vm_remap`, and Hardened Runtime `CS_*` code-signing flags, interpreted alongside the normative Microsoft Win32/PE and Apple macOS Security/XPC/IOSurface/ARM64 ABI specifications.
- **`oneapi-src/oneVPL@ec718e8ede859f16d29c3cdeba3a3025031bc83d`**, **`GPUOpen-LibrariesAndSDKs/AMF@57ee0cfb0e1a08d9041f77435653794c1b012be0`**, **`KhronosGroup/OpenCL-Headers@82f60316cc142e7b21dc1d8983b26de18858fbd9`**, and **`vdpau/libvdpau` (`include/vdpau/vdpau.h`)** establish exact vendor handle and enum widths (`mfxSession`, `mfxLoader`, `AMF_MEMORY_TYPE`, `cl_mem`, `VdpDevice`, `VdpDecoder`, `VdpVideoSurface`) consumed by the 64-bit C11 layout probe executed on `x86_64` Linux (`GCC` C11 under both default SysV LP64 and `-mms-bitfields`).
- **`llvm/llvm-project@c51c6d10cd1b612b8d0c8913ed3f449c535c6933`** (`libunwind/include/mach-o/compact_unwind_encoding.h`, `lld/MachO/UnwindInfoSection.cpp`) and **`rust-lang/rust@5c56312f346d7cc8209d9fc0fd660c72e6fc6950`** (`compiler/rustc_target/src/spec/base/{windows_msvc.rs,apple/mod.rs}`) define the compiler and linker invariants for Rust `cdylib` targets on Windows and macOS.

Companion corpus packages cited without duplication:
- Linux ELF symbol versioning (`@@LIBAVCODEC_63` vs unversioned Darwin/PE exports) and `avpriv_*` elimination: `drop-in-libav-cdylib-symbol-versioning-avpriv-elimination-and-h264-mbaff-interop`.
- Core `AVCodecContext`, `AVFrame`, `AVPacket`, `AVBufferRef` struct layouts (LP64) and callback safety: `ffmpeg-c-abi-libav-struct-layout-callbacks-and-rust-ffi-compatibility-layer`.
- External C/C++ codec and crypto library inventory (`libx264`, `libx265`, `SVT-AV1`, OpenSSL/BoringSSL) and Linux `memfd` + `seccomp-bpf` worker model: `ffmpeg-external-codec-and-crypto-library-ecosystem-replacement-vs-ffi-contracts` and `io-uring-async-rings-seccomp-landlock-and-container-path-toctou-isolation`.
- `VA-API`, `NVDEC`/`CUDA`, `Vulkan Video`, `D3D11VA`, and `D3D12VA` operational pipelines: `hardware-video-acceleration-apis-vaapi-nvdec-vulkan-video-videotoolbox-mediacodec`.
- Shared-memory double-fetch prevention and Rust `c-unwind` ABI semantics: `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics` and `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`.

## Findings

### 1. Windows Out-of-Process Media Sandboxing and Read-Only Zero-Copy Section Rings

`Basis: source + normative + documentation`

On Linux, an untrusted C/C++ encoder (`libx264`, `libx265`, `SVT-AV1`) or FIPS DTLS worker is isolated via `CLONE_NEWUSER | CLONE_NEWNS | CLONE_NEWNET | CLONE_NEWIPC | CLONE_NEWPID`, `seccomp-bpf` (`SECCOMP_FILTER_FLAG_TSYNC`), and `memfd_create` sealed with `F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_SEAL | F_SEAL_FUTURE_WRITE`. Windows NT lacks POSIX namespaces, `seccomp-bpf`, and inode-level future-write seals; achieving equivalent containment and zero-copy memory safety requires composing four distinct NT kernel mechanisms.

#### 1.1 Token Isolation: AppContainer vs. Restricted Token

Windows provides two primary token-level sandboxes for worker processes spawned via `CreateProcessW` / `CreateProcessAsUserW`:

1. **AppContainer (`CreateAppContainerProfile` + `PROC_THREAD_ATTRIBUTE_SECURITY_CAPABILITIES`):**
   - Declared in `userenv.h:235` (`mingw-w64@7095c702af7836f12a4d904555546d6abbf28b2c`):
     ```c
     HRESULT WINAPI CreateAppContainerProfile(
         PCWSTR pszAppContainerName, PCWSTR pszDisplayName, PCWSTR pszDescription,
         PSID_AND_ATTRIBUTES pCapabilities, DWORD dwCapabilityCount,
         PSID *ppSidAppContainerSid);
     ```
   - Available to **unpackaged Win32 desktop processes** since Windows 8 (`WINVER >= 0x0602`); if the profile already exists, `CreateAppContainerProfile` returns `HRESULT_FROM_WIN32(ERROR_ALREADY_EXISTS)` (`0x800700B7`), in which case the broker resolves the existing SID via `DeriveAppContainerSidFromAppContainerName` (`userenv.h:239`).
   - At worker spawn, the broker populates `SECURITY_CAPABILITIES` (`winnt.h:4507`: `{ PSID AppContainerSid; PSID_AND_ATTRIBUTES Capabilities; DWORD CapabilityCount; DWORD Reserved; }`) with **`CapabilityCount = 0` and `Capabilities = NULL`** for pure compute encoders (`libx264`, `libx265`, `SVT-AV1`), attaches it to `STARTUPINFOEXW` via `UpdateProcThreadAttribute(..., PROC_THREAD_ATTRIBUTE_SECURITY_CAPABILITIES, &sec_caps, sizeof(sec_caps), NULL, NULL)` (`processthreadsapi.h:246`), and passes `EXTENDED_STARTUPINFO_PRESENT` to `CreateProcessW`.
   - **Kernel enforcement:** An AppContainer token runs at **Low Mandatory Integrity Level** (`S-1-16-4096`) and fails every discretionary ACL check unless an object's DACL explicitly grants access to `AppContainerSid` or `ALL APPLICATION PACKAGES` (`S-1-15-2-1`). With zero capabilities, the NT kernel blocks all filesystem opens outside the AppContainer's private profile directory, all outbound/inbound Winsock/AFD network connections (no `internetClient` / `privateNetworkClientServer` SID), device opens, and cross-process handle opens.
   - **DLL load path caveat:** Because `AppContainerSid` cannot traverse an arbitrary user directory lacking an `ALL APPLICATION PACKAGES` ACE, the worker `.exe` and its dependent DLLs (`x264`, `x265`, `SvtAv1Enc`) must either reside in a directory carrying `RX` permissions for `ALL APPLICATION PACKAGES` (such as `%ProgramFiles%` or an explicitly ACL'd application bin directory) or have their image/dependency handles pre-opened/mapped via broker policy.

2. **Restricted Token (`CreateRestrictedToken` + Untrusted/Low Integrity):**
   - When a host library is loaded inside a portable unpackaged directory where adding `ALL APPLICATION PACKAGES` filesystem ACEs is undesirable (and modifying DACLs at install time is unavailable), the broker follows the Chromium renderer lockdown sequence:
     1. `OpenProcessToken(GetCurrentProcess(), TOKEN_DUPLICATE | TOKEN_QUERY | TOKEN_ADJUST_DEFAULT | TOKEN_ASSIGN_PRIMARY, &hBaseToken)`.
     2. `CreateRestrictedToken(hBaseToken, DISABLE_MAX_PRIVILEGE, nDisableSids, sidsToDisable, 0, NULL, nRestrictSids, sidsToRestrict, &hRestrictedToken)` (`DISABLE_MAX_PRIVILEGE = 0x1` strips every privilege except `SeChangeNotifyPrivilege`).
     3. Lower mandatory integrity via `SetTokenInformation(hRestrictedToken, TokenIntegrityLevel, &tml, sizeof(tml))` to `SECURITY_MANDATORY_LOW_RID` (`0x1000`) during image loader bootstrap and drop the impersonation/primary token to `SECURITY_MANDATORY_UNTRUSTED_RID` (`0x0000`) after DLL imports resolve (`Lockdown` phase).

#### 1.2 Job Object Resource, Child-Spawn, and UI Handle Containment

Tokens govern object ACL checks; they do **not** cap memory allocation, CPU fork bombs, or Win32 USER/GDI handle table access if Win32k is reachable. Every Windows Tier-3 media worker must be assigned to a dedicated anonymous Job Object (`CreateJobObjectW(NULL, NULL)` + `AssignProcessToJobObject`, or birth-time `PROC_THREAD_ATTRIBUTE_JOB_LIST`):

| `SetInformationJobObject` Class | Struct (`winnt.h` Line) | Mandatory Flags & Field Values | Security / Reliability Guarantee |
| :--- | :--- | :--- | :--- |
| `JobObjectExtendedLimitInformation` (`9`) | `JOBOBJECT_EXTENDED_LIMIT_INFORMATION` (`winnt.h:5023`) | `LimitFlags = JOB_OBJECT_LIMIT_ACTIVE_PROCESS (0x0008) \| JOB_OBJECT_LIMIT_PROCESS_MEMORY (0x0100) \| JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE (0x2000) \| JOB_OBJECT_LIMIT_DIE_ON_UNHANDLED_EXCEPTION (0x0400)`; `ActiveProcessLimit = 1`; `ProcessMemoryLimit = <codec_cap>` | Prevents compromised worker from spawning `cmd.exe`/`powershell.exe` (`ActiveProcessLimit = 1`); bounds per-worker commit charge (preventing host OOM on adversarial 8K GOP lookahead); guarantees orphan reaping if the Rust host crashes (`KILL_ON_JOB_CLOSE`, `winnt.h:5302`). |
| `JobObjectBasicUIRestrictions` (`4`) | `JOBOBJECT_BASIC_UI_RESTRICTIONS` (`winnt.h:5038`) | `UIRestrictionsClass = JOB_OBJECT_UILIMIT_HANDLES (0x01, winnt.h:5327) \| READCLIPBOARD (0x02) \| WRITECLIPBOARD (0x04) \| SYSTEMPARAMETERS (0x08) \| DISPLAYSETTINGS (0x10) \| GLOBALATOMS (0x20) \| DESKTOP (0x40) \| EXITWINDOWS (0x80)` (`0x000000FF`) | Blocks cross-process HWND message shattering, clipboard exfiltration, global atom table exhaustion, and desktop switching. |

#### 1.3 Exploit Mitigations: `DynamicCode` (ACG) and `Win32k` Syscall Disable

To match the kernel-attack-surface reduction of Linux `seccomp-bpf` + W^X:
- **Birth-time enforcement (`PROC_THREAD_ATTRIBUTE_MITIGATION_POLICY`):** Applied via `UpdateProcThreadAttribute` prior to `CreateProcessW` so policies take effect inside `NtCreateUserProcess` before any user-mode instruction executes in the child, or self-applied at the first line of `wmain` via `SetProcessMitigationPolicy` (`processthreadsapi.h:249`).
- **Arbitrary Code Guard (`ProcessDynamicCodePolicy`):** Configured via `PROCESS_MITIGATION_DYNAMIC_CODE_POLICY` (`winnt.h:4868-4878`):
  ```c
  PROCESS_MITIGATION_DYNAMIC_CODE_POLICY dcp = {0};
  dcp.ProhibitDynamicCode = 1;     /* winnt.h:4872 */
  dcp.AllowThreadOptOut = 0;       /* winnt.h:4873 */
  dcp.AllowRemoteDowngrade = 0;    /* winnt.h:4874 */
  SetProcessMitigationPolicy(ProcessDynamicCodePolicy, &dcp, sizeof(dcp));
  ```
  When `ProhibitDynamicCode = 1`, the NT Memory Manager blocks `VirtualAlloc(..., PAGE_EXECUTE_READWRITE)`, `VirtualProtect(..., PAGE_EXECUTE_READ)` on previously writable private pages, and `MapViewOfFile(..., FILE_MAP_EXECUTE | FILE_MAP_WRITE)` (`STATUS_DYNAMIC_CODE_BLOCKED`, `0xC0000404`). Crucially, `libx264`, `libx265`, `SVT-AV1`, and OpenSSL/BoringSSL compile their x86_64/ARM64 assembly routines ahead-of-time into read-only PE `.text` sections (`IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ`, without `IMAGE_SCN_MEM_WRITE`), so ACG does not disable SIMD acceleration.
- **Win32k Kernel Syscall Disable (`ProcessSystemCallDisablePolicy`):** Configured via `PROCESS_MITIGATION_SYSTEM_CALL_DISABLE_POLICY` (`winnt.h:4824-4832`):
  ```c
  PROCESS_MITIGATION_SYSTEM_CALL_DISABLE_POLICY scdp = {0};
  scdp.DisallowWin32kSystemCalls = 1; /* winnt.h:4828 */
  SetProcessMitigationPolicy(ProcessSystemCallDisablePolicy, &scdp, sizeof(scdp));
  ```
  Eliminates the entire `win32k.sys` / `win32kfull.sys` graphical syscall table (`NtUser*`, `NtGdi*`, syscall numbers `>= 0x1000`), provided the worker links only `kernel32.dll` / `ucrtbase.dll` / `bcryptprimitives.dll` (and never loads `user32.dll` or `gdi32.dll`). Add `PROCESS_MITIGATION_EXTENSION_POINT_DISABLE_POLICY` (`DisableExtensionPoints = 1`, `winnt.h:4834-4838`) and `PROCESS_MITIGATION_IMAGE_LOAD_POLICY` (`NoRemoteImages = 1`, `NoLowMandatoryLabelImages = 1`) to block AppInit/hook DLL injection and UNC/SMB DLL loads.

#### 1.4 Zero-Copy Shared-Memory Rings on Windows (`CreateFileMappingW` + `DuplicateHandle`)

`Basis: source + derived`

Verified directly against `chromium/chromium@35a0816efc03ad8fed8920050497050ed1d23a08` (`base/memory/platform_shared_memory_region_win.cc:58-176,238-370`) and `mingw-w64@7095c702af7836f12a4d904555546d6abbf28b2c` (`winnt.h:5883-5890`, `memoryapi.h:43-50,91-94`, `handleapi.h:20`), a newly created NT section handle carries **two independent permission domains** in its `ACCESS_MASK`:
1. **Standard object security rights:** `DELETE` (`0x00010000`), `READ_CONTROL` (`0x00020000`), `WRITE_DAC` (`0x00040000`), `WRITE_OWNER` (`0x00080000`).
2. **Section-specific mapping rights (`winnt.h:5883-5887`):** `SECTION_QUERY` (`0x0001`), `SECTION_MAP_WRITE` (`0x0002`, aliased as `FILE_MAP_WRITE` in `memoryapi.h:43`), `SECTION_MAP_READ` (`0x0004`, aliased as `FILE_MAP_READ` in `memoryapi.h:44`), `SECTION_MAP_EXECUTE` (`0x0008`), `SECTION_EXTEND_SIZE` (`0x0010`).

To construct a **unidirectional zero-copy raw-frame ring** where the trusted Rust host writes decoded/input video frames and the untrusted Windows Tier-3 encoder worker can **only read** them (never corrupting frames shared with other pipeline stages or triggering TOCTOU writes in host memory):

1. **Empty-DACL Anonymous Section Creation:** The Rust host initializes an empty `ACL` (`InitializeAcl(&dacl, sizeof(dacl), ACL_REVISION)`) inside a `SECURITY_DESCRIPTOR` (`SetSecurityDescriptorDacl(&sd, TRUE, &dacl, FALSE)`), sets `SECURITY_ATTRIBUTES sa = { sizeof(sa), &sd, FALSE }` (`bInheritHandle = FALSE`), and calls `CreateFileMappingW(INVALID_HANDLE_VALUE, &sa, PAGE_READWRITE, size_hi, size_lo, NULL)` (`platform_shared_memory_region_win.cc:112-113,303-326`). Passing `lpName = NULL` prevents namespace squatting (`ERROR_ALREADY_EXISTS`), and the empty DACL denies any handle re-opening by SID.
2. **Host Handle Permission Reduction:** Immediately duplicate the raw handle inside the host process with `DuplicateHandle(hSelf, hRaw, hSelf, &hHostRW, FILE_MAP_READ | FILE_MAP_WRITE | SECTION_QUERY, FALSE, 0)` and `CloseHandle(hRaw)` (`platform_shared_memory_region_win.cc:160-166`). Stripping `WRITE_DAC` and `WRITE_OWNER` guarantees that even accidental `DUPLICATE_SAME_ACCESS` handle leakage cannot grant DACL modification rights. The host maps its persistent writable ring view via `MapViewOfFile(hHostRW, FILE_MAP_READ | FILE_MAP_WRITE, 0, 0, ring_bytes)` (aligned to Windows's 64 KiB `dwAllocationGranularity`).
3. **Read-Only Worker Handle Derivation:** To grant the untrusted worker zero-copy read access without closing or unmapping `hHostRW`, the host calls:
   ```c
   HANDLE hWorkerRO = NULL;
   BOOL ok = DuplicateHandle(
       GetCurrentProcess(), hHostRW,
       hWorkerProcess,      &hWorkerRO,
       SECTION_MAP_READ | SECTION_QUERY, /* 0x0005: NO FILE_MAP_WRITE, NO WRITE_DAC, NO EXTEND_SIZE */
       FALSE, 0);
   ```
   (`platform_shared_memory_region_win.cc:250-252`). The handle integer value `(uintptr_t)hWorkerRO` is transmitted over a named-pipe / ALPC control channel to the worker.
4. **Worker Mapping and Kernel Immutability Proof:**
   - The worker validates `NtQuerySection(hWorkerRO, SectionBasicInformation, ...)` (`(Attributes & SEC_IMAGE) != SEC_IMAGE`, `platform_shared_memory_region_win.cc:58-73`, which requires `SECTION_QUERY`) and maps `MapViewOfFile(hWorkerRO, FILE_MAP_READ, 0, 0, ring_bytes)`.
   - Any attempt by a compromised worker to call `MapViewOfFile(hWorkerRO, FILE_MAP_WRITE, ...)`, `MapViewOfFile(hWorkerRO, FILE_MAP_ALL_ACCESS, ...)`, `VirtualProtect(view, sz, PAGE_READWRITE, &old)`, or `DuplicateHandle(GetCurrentProcess(), hWorkerRO, GetCurrentProcess(), &hEscalated, FILE_MAP_WRITE, FALSE, 0)` (`platform_shared_memory_region_win.cc:350-361`) fails inside the NT kernel (`ObDuplicateObject` / `NtMapViewOfSection` / `NtProtectVirtualMemory`) with `STATUS_ACCESS_DENIED` because `GrantedAccess` (`0x0005`) lacks `SECTION_MAP_WRITE` (`0x0002`) and `WRITE_DAC` (`0x00040000`). Note: `MapViewOfFile(hWorkerRO, FILE_MAP_COPY, ...)` creates a private copy-on-write view in the worker's own commit quota and **never mutates** the host's physical section pages.
5. **Reverse Output Ring (Worker -> Host):** Encoded bitstream packets (`AVPacket` payloads) or DTLS records flow over a **separate** smaller output section duplicated into the worker with `FILE_MAP_READ | FILE_MAP_WRITE | SECTION_QUERY` (still omitting `WRITE_DAC` and `SECTION_EXTEND_SIZE`). Because the untrusted worker retains `FILE_MAP_WRITE` on the output ring, the Rust host **must never parse bitstream headers or slice lengths in place**; it reads volatile ring head/tail indices once with acquire ordering, bounds-checks `(offset, len)` against ring capacity, and executes a single `core::ptr::copy_nonoverlapping` into host-owned `AVBufferRef` heap memory before validation (see `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`).

---

### 2. macOS Out-of-Process Media Sandboxing, Mach Memory Entry Rings, and Hardened Runtime

`Basis: source + normative + documentation`

#### 2.1 XPC Architecture, Seatbelt (`sandbox_init`), and Hardened Runtime (`CS_RUNTIME`)

On macOS (`aarch64-apple-darwin` and `x86_64-apple-darwin`), process-level media isolation combines three Darwin mechanisms:

1. **XPC Helper Processes vs. Standalone Helpers:**
   - Bundled `.app` / framework deployments package untrusted codecs inside `.xpc` bundles (`Contents/XPCServices/<CodecWorker>.xpc`) managed by `launchd` on demand via `xpc_connection_create("...", queue)` with declarative `com.apple.security.app-sandbox = true` entitlements and automatic lifecycle/idle reclamation.
   - Non-bundled CLI or standalone `.dylib` installations (`ffmpeg` CLI or server processes linking `libavcodec.63.dylib`) cannot rely on bundled `.xpc` discovery by `launchd`; instead, they spawn a helper executable via `posix_spawn` and immediately lock down the child before ingesting untrusted bytes using Seatbelt's `sandbox_init_with_parameters` (declared in `<sandbox.h>`). Although Apple marks `sandbox_init` deprecated for App Store third-party apps in favor of declarative App Sandbox entitlements, it remains the underlying user-space entry point into XNU's `Sandbox.kext` MAC policy used by Chromium (`sandbox/policy/mac/*.sb`), Firefox, and WebKit for unpackaged helper processes.
   - **Minimal Compute-Encoder Seatbelt Policy:** Default `(deny default)`, allowing only `(allow process-exec)` on the worker binary itself (prior to locking down child `process-fork`), `(allow sysctl-read)` for CPU feature/cache-line queries (`hw.optional.arm.FEAT_*`, `hw.ncpu`), `(allow mach-lookup)` restricted to zero or the minimal Libsystem logging/trust endpoints, and **explicitly denying** `(deny file-read* file-write* network* iokit-open mach-task-name)`. Denying `iokit-open` severs access to `IOSurfaceRootUserClient`, `AGXDeviceUserClient` (Apple Silicon GPU driver), and `AppleAVE2UserClient`, eliminating the largest historical XNU kernel privilege-escalation surface from a CPU-only `libx264`/`libx265`/`SVT-AV1` sandbox.

2. **Hardened Runtime (`CS_RUNTIME`) and Hardware W^X Enforcement:**
   - Verified in `apple-oss-distributions/xnu@f6217f891ac0bb64f3d375211650a4c1ff8ca1ea` (`osfmk/kern/cs_blobs.h:36-86` and `bsd/sys/codesign.h:40-61`), signing binaries with `codesign --options runtime` sets `CS_RUNTIME` (`0x00010000`), which activates:
     - `CS_HARD` (`0x00000100`, *"don't load invalid pages"*) and `CS_KILL` (`0x00000200`, *"kill process if it becomes invalid"*): any attempt to fault in a modified code page or call `mmap`/`mprotect` with `PROT_WRITE | PROT_EXEC` fails (`EACCES` / `KERN_PROTECTION_FAILURE`) or terminates the process with `SIGKILL` (`EXC_BAD_ACCESS` / `CODESIGNING` exit reason).
     - `CS_REQUIRE_LV` (`0x00002000`, *"require library validation"*): `dyld` and the XNU MAC hook reject `dlopen` of any `.dylib` not signed either by Apple or with the exact same **Team ID** (`CS_OPS_TEAMID`, `codesign.h:57`), unless weakened by `com.apple.security.cs.disable-library-validation`.
     - Environment variable scrubbing (`CS_RESTRICT`, `0x00000800`): `dyld` ignores `DYLD_INSERT_LIBRARIES`, `DYLD_LIBRARY_PATH`, and `DYLD_FRAMEWORK_PATH`, preventing interposition injection into media workers.
   - **Entitlement rule for media workers:** Omit `com.apple.security.cs.allow-jit` (`CS_EXECSEG_JIT = 0x40`, `cs_blobs.h:83`), `com.apple.security.cs.allow-unsigned-executable-memory` (`CS_EXECSEG_ALLOW_UNSIGNED = 0x10`, `cs_blobs.h:81`), and `com.apple.security.cs.allow-dyld-environment-variables`. Pre-compiled NEON / x86_64 `.s` / NASM objects in `libx264`, `libx265`, and `SVT-AV1` reside in signed `__TEXT,__text` (`VM_PROT_READ | VM_PROT_EXECUTE`) and require zero JIT entitlements.

#### 2.2 Darwin Zero-Copy Shared Memory: Three Critical Security Distinctions

`Basis: source + documentation + derived`

Replacing Linux `memfd_create` + `F_SEAL_FUTURE_WRITE` on Darwin exposes three platform traps verified against `apple-oss-distributions/xnu@f6217f891ac0bb64f3d375211650a4c1ff8ca1ea` (`osfmk/vm/vm_memory_entry.c:58-90,638-860,1019-1197`, `osfmk/mach/vm_prot.h:87-101`, `osfmk/mach/mach_vm.defs:390-480`) and `chromium/chromium@35a0816efc03ad8fed8920050497050ed1d23a08` (`base/memory/platform_shared_memory_region_apple.cc:73-191`):

| Darwin IPC Memory Mechanism | Host Retains Live `VM_PROT_WRITE`? | Untrusted Worker Blocked from `VM_PROT_WRITE` by XNU MMU? | Verdict for Host -> Tier-3 Worker Zero-Copy Frame Ring |
| :--- | :--- | :--- | :--- |
| `xpc_shmem_create(va, len)` + `xpc_shmem_map` | Yes | **No** — `xpc_shmem_create` wraps the region's existing `max_protection` (`VM_PROT_READ \| VM_PROT_WRITE`); recipient can map or `vm_protect` writable | **Unsound** for untrusted read-only input rings; usable only for worker-writable output packet rings with host single-fetch copy. |
| `IOSurfaceCreateXPCObject` / `IOSurfaceCreateMachPort` + `IOSurfaceLock(..., kIOSurfaceLockReadOnly, ...)` | Yes | **No** — `kIOSurfaceLockReadOnly` is an advisory user-space cache-coherency flag; worker holding `IOSurfaceRef` can call `IOSurfaceLock(s, 0, NULL)` and overwrite backing pages | **Unsound** across a trust boundary when the recipient is untrusted C/C++; safe only between mutually trusted processes (e.g., host <-> Apple `VTDecoderXPCService` system daemon). |
| `mach_make_memory_entry_64` with `VM_PROT_READ` **without** `MAP_MEM_VM_SHARE` (`platform_shared_memory_region_apple.cc:102-105`) | **No** (or triggers COW split on subsequent host write) | Yes (`user_entry->protection = VM_PROT_READ`) | **One-shot immutable buffers only** (where host writes once, unmaps its writable view, converts to `VM_PROT_READ`, and never mutates the buffer again). |
| `mach_make_memory_entry_64(mach_task_self(), &sz, ring_va, MAP_MEM_VM_SHARE \| VM_PROT_READ, &ro_port, MACH_PORT_NULL)` + `xpc_dictionary_set_mach_send` | **Yes** (live shared `vm_object_t` pages) | **Yes** (`user_entry->protection = VM_PROT_READ`; worker `mach_vm_map` `max_protection` capped at `VM_PROT_READ`) | **Sound & zero-copy** for persistent reusable host-producer / worker-consumer YUV frame rings. |

**Exact XNU Kernel Trace for `MAP_MEM_VM_SHARE | VM_PROT_READ` (`vm_memory_entry.c`):**
1. The trusted Rust host allocates a page-aligned (`vm_page_size` = **16 KiB** on `arm64-apple-darwin`, **4 KiB** on `x86_64-apple-darwin`!) anonymous ring via `mach_vm_allocate(mach_task_self(), &ring_va, ring_bytes, VM_FLAGS_ANYWHERE)` (`VM_PROT_DEFAULT = VM_PROT_READ | VM_PROT_WRITE`, `vm_prot.h:95`).
2. The host creates a read-only shared memory-entry send right:
   ```c
   memory_object_size_t entry_sz = ring_bytes;
   mach_port_t ro_port = MACH_PORT_NULL;
   kern_return_t kr = mach_make_memory_entry_64(
       mach_task_self(),
       &entry_sz,
       (memory_object_offset_t)ring_va,
       MAP_MEM_VM_SHARE | VM_PROT_READ,
       &ro_port,
       MACH_PORT_NULL);
   ```
3. Inside XNU `mach_make_memory_entry_internal` (`vm_memory_entry.c:1184-1189`), `(permission & MAP_MEM_VM_SHARE)` dispatches to `mach_make_memory_entry_share` (`vm_memory_entry.c:591-860`). `vm_memory_entry_decode_perm` (`lines 85-87`) extracts `protections = VM_PROT_READ` (`0x01`) and `mask_protections = false`. `vm_map_copy_extract` (`lines 740-748`) extracts a shared `vm_map_copy_t` (`copy = FALSE`, `VM_INHERIT_SHARE`) backed by the live underlying `vm_object_t`, verifying `(cur_prot & VM_PROT_READ) == VM_PROT_READ` (`lines 777-787`), and stores **`user_entry->protection = VM_PROT_READ`** (`line 853`).
4. The host transmits `ro_port` via `xpc_dictionary_set_mach_send(msg, "input_ring", ro_port)` (or Mach IPC `MACH_MSG_TYPE_COPY_SEND`) and releases its local send-right reference (`mach_port_deallocate`).
5. The worker extracts the send right via `xpc_dictionary_copy_mach_send(msg, "input_ring")` and maps it via:
   ```c
   mach_vm_address_t worker_va = 0;
   kern_return_t kr = mach_vm_map(
       mach_task_self(), &worker_va, ring_bytes, 0, VM_FLAGS_ANYWHERE,
       ro_port, 0, FALSE /* copy = FALSE -> live shared view */,
       VM_PROT_READ, VM_PROT_READ, VM_INHERIT_NONE);
   ```
   If a compromised worker attempts `mach_vm_map` with `cur_protection` or `max_protection` containing `VM_PROT_WRITE` (`0x02`), XNU rejects the call with **`KERN_INVALID_RIGHT`** (`platform_shared_memory_region_apple.cc:167-182` uses this exact `vm_map(..., VM_PROT_READ | VM_PROT_WRITE) == KERN_INVALID_RIGHT` probe as its runtime read-only handle assertion!). Once mapped with `max_protection = VM_PROT_READ`, any subsequent `mach_vm_protect(mach_task_self(), worker_va, ring_bytes, FALSE, VM_PROT_READ | VM_PROT_WRITE)` returns **`KERN_PROTECTION_FAILURE`**.
6. **Page-size alignment invariant (`16 KiB` vs `4 KiB`):** On Apple Silicon (`arm64`), `PAGE_MASK` is `0x3FFF` (`16,384` bytes); `mach_make_memory_entry_64` truncates `map_start` and rounds `map_end` to `PAGE_MASK` (`vm_memory_entry.c:964-966`). If `ring_va` or `ring_bytes` is only 4 KiB-aligned, `mach_make_memory_entry_64` silently exposes adjacent bytes within the enclosing 16 KiB physical page! Every shared ring allocation on Darwin must therefore allocate whole multiples of `mach_vm_round_page(ring_bytes)` via `mach_vm_allocate`, never sub-page `malloc` slabs.
7. **Same-host broker remapping (`mach_vm_remap`):** When the broker holds `task_t` control over a child task (before child privilege drop), `mach_vm_remap` (`mach_vm.defs:390-410`, `vm_user.c:956`) can also project `ring_va` directly into `child_task` with `inheritance = VM_INHERIT_NONE`, returning `cur_protection` and `max_protection`; however, `mach_vm_remap` derives `max_protection` from the **source map entry's** `max_protection` unless masked via `mach_vm_remap_new` (`mach_vm.defs:527`, `vm_user.c:869`) or an intermediate `VM_PROT_READ`-capped mapping. Passing a `MAP_MEM_VM_SHARE | VM_PROT_READ` named memory entry port over XPC avoids holding the child's privileged `task_t` control port (`task_for_pid` / `mach-task-name`) altogether.

---

### 3. Complete 64-Bit Layout Census and Ownership Contracts for the Remaining Nine `AVHWDeviceType` Families

`Basis: source + execution`

At `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`, `enum AVHWDeviceType` (`libavutil/hwcontext.h:27-44`) defines 14 concrete hardware backends (`1..14`, plus `AV_HWDEVICE_TYPE_NONE = 0`). Five backends (`CUDA`, `VAAPI`, `Vulkan`, `D3D11VA`, `D3D12VA`) are detailed in `hardware-video-acceleration-apis-vaapi-nvdec-vulkan-video-videotoolbox-mediacodec`. Here we provide the complete 64-bit C-ABI layout census, private wrapper sizing, `AVFrame.data[i]` conventions, and destructor invariants for the **remaining nine device families** (`DRM`, `VIDEOTOOLBOX`, `MEDIACODEC`, `QSV`, `OPENCL`, `VDPAU`, `DXVA2`, `AMF`, `OHCODEC`) and their five companion `libavcodec/*.h` hwaccel headers.

#### 3.1 Base Enclosing Structs (`libavutil/hwcontext.h`)

Executed 64-bit C11 probe measurements (`sizeof(void*) == 8`, identical under SysV LP64 and `-mms-bitfields`):
- **`AVHWDeviceContext` (`sizeof = 40`, `alignof = 8`, `libavutil/hwcontext.h:63-106`):** `av_class` (`0`, 8 B), `type` (`8`, 4 B + 4 B pad `12..16`), `hwctx` (`16`, 8 B), `free` (`24`, 8 B), `user_opaque` (`32`, 8 B).
- **`AVHWFramesContext` (`sizeof = 80`, `alignof = 8`, `libavutil/hwcontext.h:118-221`):** `av_class` (`0`, 8 B), `device_ref` (`8`, 8 B), `device_ctx` (`16`, 8 B), `hwctx` (`24`, 8 B), `free` (`32`, 8 B), `user_opaque` (`40`, 8 B), `pool` (`48`, 8 B), `initial_pool_size` (`56`, 4 B), `format` (`60`, 4 B), `sw_format` (`64`, 4 B), `width` (`68`, 4 B), `height` (`72`, 4 B + 4 B tail pad `76..80`).

#### 3.2 Complete 64-Bit Struct `sizeof` / `alignof` / `offsetof` Table (22 Public Structs)

All byte offsets and sizes below were measured by compiling and executing `layout_probe.c` against unmodified `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` headers under GCC C11 (`-O2 -Wall -Wextra -Werror`, verified bit-for-bit identical with and without `-mms-bitfields`). Vendor typedef assumptions verified from pinned upstream SDK headers:
- **OpenCL** (`KhronosGroup/OpenCL-Headers@82f60316cc142e7b21dc1d8983b26de18858fbd9`, `CL/cl.h:36-39`): `cl_device_id`, `cl_context`, `cl_command_queue`, `cl_mem` are opaque struct pointers (`8 B`).
- **Intel QSV / oneVPL** (`oneapi-src/oneVPL@ec718e8ede859f16d29c3cdeba3a3025031bc83d`, `api/vpl/mfxsession.h:19`, `api/vpl/mfxdispatcher.h:19`): `mfxSession` (`struct _mfxSession *`) is an `8 B` pointer; `loader` in `AVQSVDeviceContext` is `void *` (`8 B`, cast to `mfxLoader`).
- **Apple VideoToolbox / CoreVideo / CoreMedia**: `VTDecompressionSessionRef`, `CMVideoFormatDescriptionRef`, `CVPixelBufferRef`, `CFStringRef` are `8 B` opaque pointers; `OSType` (`FourCharCode` = `UInt32`) is `4 B` (`uint32_t`).
- **VDPAU** (`vdpau/libvdpau`, `include/vdpau/vdpau.h:839,1538,1732`): `VdpDevice`, `VdpVideoSurface`, `VdpDecoder`, `VdpChromaType` are **`uint32_t` (4-byte integer handles, NOT pointers)**; `VdpGetProcAddress *` and `VdpDecoderRender *` are `8 B` function pointers.
- **DirectX 9 / DXVA2** (`mingw-w64@7095c702af7836f12a4d904555546d6abbf28b2c`, `d3d9.h`, `dxva2api.h`): `DWORD` on Windows 64-bit LLP64 is **`4 B` (`uint32_t`)**; `IDirect3DDeviceManager9 *`, `IDirect3DSurface9 **` (`LPDIRECT3DSURFACE9 *`), `IDirectXVideoDecoder *`, `const DXVA2_ConfigPictureDecode *` are `8 B` pointers.
- **AMD AMF** (`GPUOpen-LibrariesAndSDKs/AMF@57ee0cfb0e1a08d9041f77435653794c1b012be0`, `amf/public/include/core/Data.h:53-68`): `AMF_MEMORY_TYPE` is a C `enum` (`0..12`, `4 B`); `AMFFactory *`, `AMFContext *` are `8 B` C-vtable struct pointers (`pThis->pVtbl`).

| Backend & Header (`FFmpeg@7ddf7bc8...`) | Struct Name | `sizeof` (B) | `alignof` (B) | Exact Field Offsets, Sizes, and Internal/Tail Padding |
| :--- | :--- | ---: | ---: | :--- |
| **1. DRM** (`libavutil/hwcontext_drm.h:48-66`) | `AVDRMObjectDescriptor` | `24` | `8` | `fd`: `@0` (4 B `int`), *pad `@4..8` (4 B)*, `size`: `@8` (8 B `size_t`), `format_modifier`: `@16` (8 B `uint64_t`) |
| **1. DRM** (`libavutil/hwcontext_drm.h:74-88`) | `AVDRMPlaneDescriptor` | `24` | `8` | `object_index`: `@0` (4 B `int`), *pad `@4..8` (4 B)*, `offset`: `@8` (8 B `ptrdiff_t`), `pitch`: `@16` (8 B `ptrdiff_t`) |
| **1. DRM** (`libavutil/hwcontext_drm.h:96-111`) | `AVDRMLayerDescriptor` | `104` | `8` | `format`: `@0` (4 B `uint32_t`), `nb_planes`: `@4` (4 B `int`), `planes[4]`: `@8` (`4 * 24 = 96 B` `AVDRMPlaneDescriptor[4]`) |
| **1. DRM** (`libavutil/hwcontext_drm.h:133-150`) | `AVDRMFrameDescriptor` | `528` | `8` | `nb_objects`: `@0` (4 B `int`), *pad `@4..8` (4 B)*, `objects[4]`: `@8` (`4 * 24 = 96 B`), `nb_layers`: `@104` (4 B `int`), *pad `@108..112` (4 B)*, `layers[4]`: `@112` (`4 * 104 = 416 B`) |
| **1. DRM** (`libavutil/hwcontext_drm.h:157-167`) | `AVDRMDeviceContext` | `4` | `4` | `fd`: `@0` (4 B `int`) |
| **2. VideoToolbox** (`libavutil/hwcontext_videotoolbox.h:45-47`) | `AVVTFramesContext` | `4` | `4` | `color_range`: `@0` (4 B `enum AVColorRange`) |
| **2. VideoToolbox** (`libavcodec/videotoolbox.h:57-79`) | `AVVideotoolboxContext` | `32` | `8` | `session`: `@0` (8 B `VTDecompressionSessionRef`), `cv_pix_fmt_type`: `@8` (4 B `OSType`), *pad `@12..16` (4 B)*, `cm_fmt_desc`: `@16` (8 B `CMVideoFormatDescriptionRef`), `cm_codec_type`: `@24` (4 B `int`), *tail pad `@28..32` (4 B)* |
| **3. MediaCodec** (`libavutil/hwcontext_mediacodec.h:27-59`) | `AVMediaCodecDeviceContext` | `24` | `8` | `surface`: `@0` (8 B `void *` JNI `jobject`), `native_window`: `@8` (8 B `void *` `ANativeWindow *`), `create_window`: `@16` (4 B `int`), *tail pad `@20..24` (4 B)* |
| **3. MediaCodec** (`libavcodec/mediacodec.h:33-40`) | `AVMediaCodecContext` | `8` | `8` | `surface`: `@0` (8 B `void *` JNI `jobject`) |
| **4. QSV** (`libavutil/hwcontext_qsv.h:35-48`) | `AVQSVDeviceContext` | `16` | `8` | `session`: `@0` (8 B `mfxSession`), `loader`: `@8` (8 B `void *` `mfxLoader`) |
| **4. QSV** (`libavutil/hwcontext_qsv.h:53-84`) | `AVQSVFramesContext` | `24` | `8` | `surfaces`: `@0` (8 B `mfxFrameSurface1 *`), `nb_surfaces`: `@8` (4 B `int`), `frame_type`: `@12` (4 B `int`), `info`: `@16` (8 B `mfxFrameInfo *`) |
| **4. QSV** (`libavcodec/qsv.h:36-100`) | `AVQSVContext` | `56` | `8` | `session`: `@0` (8 B), `iopattern`: `@8` (4 B `int`), *pad `@12..16` (4 B)*, `ext_buffers`: `@16` (8 B `mfxExtBuffer **`), `nb_ext_buffers`: `@24` (4 B `int`), `opaque_alloc`: `@28` (4 B `int`), `nb_opaque_surfaces`: `@32` (4 B `int`), *pad `@36..40` (4 B)*, `opaque_surfaces`: `@40` (8 B `AVBufferRef *`), `opaque_alloc_type`: `@48` (4 B `int`), *tail pad `@52..56` (4 B)* |
| **5. OpenCL** (`libavutil/hwcontext_opencl.h:47-56`) | `AVOpenCLFrameDescriptor` | `72` | `8` | `nb_planes`: `@0` (4 B `int`), *pad `@4..8` (4 B)*, `planes[8]`: `@8` (`8 * 8 = 64 B` `cl_mem[AV_NUM_DATA_POINTERS]`) |
| **5. OpenCL** (`libavutil/hwcontext_opencl.h:63-82`) | `AVOpenCLDeviceContext` | `24` | `8` | `device_id`: `@0` (8 B `cl_device_id`), `context`: `@8` (8 B `cl_context`), `command_queue`: `@16` (8 B `cl_command_queue`) |
| **5. OpenCL** (`libavutil/hwcontext_opencl.h:89-98`) | `AVOpenCLFramesContext` | `8` | `8` | `command_queue`: `@0` (8 B `cl_command_queue`) |
| **6. VDPAU** (`libavutil/hwcontext_vdpau.h:35-38`) | `AVVDPAUDeviceContext` | `16` | `8` | `device`: `@0` (4 B `VdpDevice` = `uint32_t`), *pad `@4..8` (4 B)*, `get_proc_address`: `@8` (8 B `VdpGetProcAddress *`) |
| **6. VDPAU** (`libavcodec/vdpau.h:78-94`) | `AVVDPAUContext` | `24` | `8` | `decoder`: `@0` (4 B `VdpDecoder` = `uint32_t`), *pad `@4..8` (4 B)*, `render`: `@8` (8 B `VdpDecoderRender *`), `render2`: `@16` (8 B `AVVDPAU_Render2`) |
| **7. DXVA2** (`libavutil/hwcontext_dxva2.h:39-41`) | `AVDXVA2DeviceContext` | `8` | `8` | `devmgr`: `@0` (8 B `IDirect3DDeviceManager9 *`) |
| **7. DXVA2** (`libavutil/hwcontext_dxva2.h:46-73`) | `AVDXVA2FramesContext` | `32` | `8` | `surface_type`: `@0` (4 B `DWORD` = `uint32_t`), *pad `@4..8` (4 B)*, `surfaces`: `@8` (8 B `IDirect3DSurface9 **`), `nb_surfaces`: `@16` (4 B `int`), *pad `@20..24` (4 B)*, `decoder_to_release`: `@24` (8 B `IDirectXVideoDecoder *`) |
| **7. DXVA2** (`libavcodec/dxva2.h:54-84`) | `struct dxva_context` | `48` | `8` | `decoder`: `@0` (8 B `IDirectXVideoDecoder *`), `cfg`: `@8` (8 B `const DXVA2_ConfigPictureDecode *`), `surface_count`: `@16` (4 B `unsigned`), *pad `@20..24` (4 B)*, `surface`: `@24` (8 B `LPDIRECT3DSURFACE9 *`), `workaround`: `@32` (8 B `uint64_t`), `report_id`: `@40` (4 B `unsigned`), *tail pad `@44..48` (4 B)* |
| **8. AMF** (`libavutil/hwcontext_amf.h:35-47`) | `AVAMFDeviceContext` | `72` | `8` | `library`: `@0` (8 B `void *`), `factory`: `@8` (8 B `AMFFactory *`), `trace_writer`: `@16` (8 B `void *`), `version`: `@24` (8 B `int64_t`), `context`: `@32` (8 B `AMFContext *`), `memory_type`: `@40` (4 B `AMF_MEMORY_TYPE`), *pad `@44..48` (4 B)*, `lock`: `@48` (8 B fnptr), `unlock`: `@56` (8 B fnptr), `lock_ctx`: `@64` (8 B `void *`) |
| **9. OpenHarmony** (`libavutil/hwcontext_oh.h:27-32`) | `AVOHCodecDeviceContext` | `8` | `8` | `native_window`: `@0` (8 B `void *` `OHNativeWindow *`) |

*(Note: Table includes 22 total public struct rows across the 9 device types: 5 DRM + 2 VideoToolbox + 2 MediaCodec + 3 QSV + 3 OpenCL + 2 VDPAU + 3 DXVA2 + 1 AMF + 1 OpenHarmony.)*

#### 3.3 Private Wrapper Subtyping, `AVFrame.data[i]` Slot Conventions, and Ownership Invariants

Direct inspection of `libavutil/hwcontext_{drm,videotoolbox,mediacodec,qsv,opencl,vdpau,dxva2,amf,oh}.c` at `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` reveals five load-bearing FFI invariants that header signatures alone hide:

1. **C Prefix-Subtyping of `hwctx` Allocations (`HWContextType.{device,frames}_hwctx_size`):**
   `av_hwdevice_ctx_alloc(type)` and `av_hwframe_ctx_alloc(dev_ref)` do **not** allocate `sizeof(AV*DeviceContext)` / `sizeof(AV*FramesContext)` directly; they allocate `HWContextType.device_hwctx_size` and `frames_hwctx_size`, placing the public struct at offset `0` (`struct Priv { AVPublic p; ... }`) inside a larger private allocation:
   - `VIDEOTOOLBOX` (`hwcontext_videotoolbox.c:37-43,840-857`): `device_hwctx_size = 0` (**`AVHWDeviceContext.hwctx` is always `NULL`!**); `frames_hwctx_size = sizeof(VTFramesContext)` (`16 B`: `AVVTFramesContext p` `@0..4`, pad `@4..8`, `CVPixelBufferPoolRef pool` `@8..16`).
   - `MEDIACODEC` (`hwcontext_mediacodec.c:31-36,107-121`): `device_hwctx_size = sizeof(MediaCodecDeviceContext)` (`40 B`: `AVMediaCodecDeviceContext ctx` `@0..24`, `void *libmedia` `@24..32`, `create_surface` fnptr `@32..40`); `frames_hwctx_size = 0` (no `AVHWFramesContext` pool).
   - `QSV` (`hwcontext_qsv.c:77-90,2621-2644`): `device_hwctx_size = sizeof(QSVDeviceContext)` (`AVQSVDeviceContext p` `@0..16` followed by `mfxHDL handle`, `mfxHandleType`, `mfxVersion`, `mfxIMPL`, `child_device_type`, `child_pix_fmt`); `frames_hwctx_size = sizeof(QSVFramesContext)`.
   - `OPENCL` (`hwcontext_opencl.c:87,3045-3074`): `device_hwctx_size = sizeof(OpenCLDeviceContext)`, `frames_hwctx_size = sizeof(OpenCLFramesContext)`.
   - `VDPAU` (`hwcontext_vdpau.c:85,513-533`): `device_hwctx_size = sizeof(VDPAUDeviceContext)`, `frames_hwctx_size = sizeof(VDPAUFramesContext)` (even though `hwcontext_vdpau.h:41` states `AVHWFramesContext.hwctx` has no public struct!).
   - `DXVA2` (`hwcontext_dxva2.c:60-73,595-612`): `device_hwctx_size = sizeof(AVDXVA2DeviceContext)` (`8 B`), `frames_hwctx_size = sizeof(DXVA2FramesContext)` (`AVDXVA2FramesContext p` `@0..32` followed by `surfaces_internal`, `nb_surfaces_used`, `device_handle`, `service`, `format`).
   - `AMF` (`hwcontext_amf.c:107-109,986-1006`): `device_hwctx_size = sizeof(AVAMFDeviceContext)` (`72 B`), `frames_hwctx_size = sizeof(AMFFramesContext)` (`8 B` dummy `struct { void *dummy; }`).
   - `DRM` (`hwcontext_drm.c:307-326`) & `OHCODEC` (`hwcontext_oh.c:38-47`): `device_hwctx_size = sizeof(AVDRMDeviceContext)` (`4 B`) / `sizeof(AVOHCodecDeviceContext)` (`8 B`); `frames_hwctx_size = 0`.
   - **Rust FFI Rule:** A Rust drop-in library implementing `av_hwdevice_ctx_alloc` / `av_hwframe_ctx_alloc` must store its backend-private fields inside the same `#[repr(C)]` tail after the public struct at offset `0` (so C callers casting `ctx->hwctx` read valid prefix bytes), and Rust callers consuming an external `AVHWDeviceContext` must project `&mut *(ctx.hwctx as *mut AV*DeviceContext)` without ever moving or resizing `*ctx.hwctx`.

2. **Asymmetric `AVFrame.data[i]` Hardware Payload Slots and the VDPAU Integer-in-Pointer Hazard:**
   FFmpeg's hardware pixel formats split across **`data[0]`**, **`data[0..nb_planes-1]`**, and **`data[3]`**:
   - **`AV_PIX_FMT_DRM_PRIME` (`hwcontext_drm.c:81-90`):** `frame->data[0] = (uint8_t *)frame->buf[0]->data`, pointing to a `528`-byte `AVDRMFrameDescriptor`. Plane bounds invariant (`hwcontext_drm.h:128-149`): `0 <= nb_objects <= 4`, `0 <= nb_layers <= 4`, `sum(layers[i].nb_planes) <= 4`, and for every active plane `0 <= object_index < nb_objects`. PRIME `fd` ownership belongs to `frame->buf[0]`'s custom `free` callback (`close(objects[i].fd)` when the last `AVBufferRef` drops), unless exported/borrowed without `close` during `av_hwframe_map()`.
   - **`AV_PIX_FMT_VIDEOTOOLBOX` (`hwcontext_videotoolbox.c:313-324`):** `frame->data[3] = frame->buf[0]->data` (`CVPixelBufferRef` in **`data[3]`**, `data[0..2] == NULL`!). Pool destructor calls `CVPixelBufferRelease((CVPixelBufferRef)data)`. Furthermore, in `hwcontext_videotoolbox.h:70-111`, `av_map_videotoolbox_chroma_loc_from_av` and `av_map_videotoolbox_color_{matrix,primaries,trc}_from_av` return **unowned/borrowed `CFStringRef` constants or CoreVideo codepoint-cache entries**; calling `CFRelease` on them corrupts CoreVideo's process-global cache (`hwcontext_videotoolbox.h:79-82`)!
   - **`AV_PIX_FMT_MEDIACODEC` (`libavcodec/mediacodec.h:73-103`):** `frame->data[3]` holds `AVMediaCodecBuffer *`. Single-shot release invariant: `av_mediacodec_release_buffer` / `av_mediacodec_render_buffer_at_time` transitions an atomic serial/released flag and returns `AVERROR(ENOENT)` if already released or invalidated by `avcodec_flush_buffers()`. In `AVMediaCodecDeviceContext` (`hwcontext_mediacodec.c:92-105`), `mc_device_uninit` calls `ANativeWindow_release(dev->native_window)` **only** when `s->libmedia != NULL` (i.e., FFmpeg auto-created the persistent input surface via `create_window = 1`); user-supplied `surface` (`jobject` global ref) and user-supplied `native_window` remain caller-owned!
   - **`AV_PIX_FMT_QSV` (`hwcontext_qsv.c:1479-1491`):** `frame->data[3] = frame->buf[0]->data` (`mfxFrameSurface1 *` in **`data[3]`**). In `AVQSVFramesContext` (`hwcontext_qsv.h:59-84`), `surfaces` is valid when `nb_surfaces > 0` (fixed pool) and `info` is valid when `nb_surfaces == 0` (oneVPL 2.9+ dynamic pool). Teardown order in `qsv_device_free` (`hwcontext_qsv.c:2354-2366`): **always** `MFXClose(hwctx->session)` strictly before `MFXUnload(hwctx->loader)` (unloading the oneVPL dispatcher DLL before closing the session unmaps `MFXClose`'s vtable code page and segfaults!), followed by `av_buffer_unref(&priv->child_device_ctx)`.
   - **`AV_PIX_FMT_OPENCL` (`hwcontext_opencl.c:1632-1648,1769-1788`):** `frame->buf[0]->data` points to `AVOpenCLFrameDescriptor` (`72 B`), while `opencl_get_buffer` unpacks **`frame->data[p] = (uint8_t *)desc->planes[p]`** (`cl_mem` handles across `data[0..nb_planes-1]`, NOT `data[3]`). Pool free calls `clReleaseMemObject(desc->planes[p])` for `0 <= p < desc->nb_planes`.
   - **`AV_PIX_FMT_VDPAU` (`hwcontext_vdpau.c:224-260,297-309`):** `frame->buf[0]->data` and `frame->data[3]` hold **`(uint8_t *)(uintptr_t)surf`**, where `surf` is a **32-bit integer ID (`VdpVideoSurface`, e.g., `1`, `2`, `3`)**, NOT a valid memory address! **Rust Soundness Rule:** `AVBufferRef.data` and `AVFrame.data[0..8]` in Rust FFI **must** remain raw pointers (`*mut u8`), never `&u8`, `&[u8]`, or `NonNull<T>` assumed aligned/dereferenceable; constructing `&*frame.data[3]` on a VDPAU frame (`0x1 as *const u8`) is immediate Rust undefined behavior even without a load instruction.
   - **`AV_PIX_FMT_DXVA2_VLD` (`hwcontext_dxva2.c:109-135,255-267`):** `frame->data[3] = frame->buf[0]->data` (`IDirect3DSurface9 *` in **`data[3]`**). Driver teardown-order invariant (`dxva2_frames_uninit`, `lines 116-125`): if `AVDXVA2FramesContext.decoder_to_release` is non-NULL, `IDirectXVideoDecoder_Release(decoder_to_release)` **must execute strictly before** releasing `surfaces_internal[i]` (`IDirect3DSurface9_Release`), because legacy WDDM DXVA2 drivers crash in kernel/UMD callbacks if render-target surfaces are destroyed while the decoder object still references them.
   - **`AV_PIX_FMT_AMF_SURFACE` (`hwcontext_amf.c:374-420,528-555`):** Note an upstream quirk in `amf_pool_alloc` (`line 379`): the default dummy pool creates `av_buffer_create(NULL, 0, amf_dummy_free, hwfc, AV_BUFFER_FLAG_READONLY)`, while real `AMFSurface *` instances allocated by `AMFContext::AllocSurface` wrap `AMFSurface_Release` in a per-surface `AVBufferRef` stored in `frame->buf[0]` and `frame->data[0]`. In `amf_device_uninit` (`lines 534-550`), `context->pVtbl->Terminate(context)` and `Release(context)` plus `trace->pVtbl->UnregisterWriter` **must precede** `dlclose(amf_ctx->library)` (`FreeLibrary` on Windows). Also note `AMF_STD_CALL`: on 32-bit Windows x86 (`i686`), AMF vtable methods use `__stdcall` (`extern "system"`), whereas on 64-bit Windows x64 and Linux LP64 `AMF_STD_CALL` lowers to the single platform 64-bit C calling convention (`AMF_Platform.h:114-129`).
   - **`AV_PIX_FMT_OHCODEC` (`hwcontext_oh.c:27-47`):** Device-only stub holding caller-owned `OHNativeWindow *native_window` (`8 B`); `oh_device_create` rejects non-empty device strings and performs no `OHNativeWindow` unref on device destruction (caller retains lifetime responsibility).

#### 3.4 Reference Rust `#[repr(C)]` Definitions for Key Cross-Platform Contexts

To prevent both C-enum niche UB (`libavutil/hwcontext.h:236` explicitly permits callers to pass invalid `enum AVHWDeviceType` integers to `av_hwdevice_get_type_name`) and VDPAU/MediaCodec raw-handle UB, public FFI structs must use transparent integer newtypes for C enums and raw pointers (`*mut c_void`, never Rust references) for opaque vendor handles:

```rust
use core::ffi::{c_int, c_uchar, c_uint, c_ulong, c_void};

/// Transparent C-ABI wrapper avoiding Rust enum niche/validity UB on out-of-range C values.
/// Note: Underlying C type is `unsigned int` on SysV GCC/Clang and `int` on MSVC `cl.exe` (both 4 B, align 4).
#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AVHWDeviceType(pub c_int);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AVColorRange(pub c_int);

#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AmfMemoryType(pub c_int);

pub const AV_DRM_MAX_PLANES: usize = 4;
pub const AV_NUM_DATA_POINTERS: usize = 8;

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct AVDRMObjectDescriptor {
    pub fd: c_int,               // @0  (4 B) + 4 B pad @4..8 on 64-bit
    pub size: usize,             // @8  (8 B)
    pub format_modifier: u64,    // @16 (8 B) -> sizeof = 24, align = 8
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct AVDRMPlaneDescriptor {
    pub object_index: c_int,     // @0  (4 B) + 4 B pad @4..8 on 64-bit
    pub offset: isize,           // @8  (8 B)
    pub pitch: isize,            // @16 (8 B) -> sizeof = 24, align = 8
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct AVDRMLayerDescriptor {
    pub format: u32,                                         // @0 (4 B)
    pub nb_planes: c_int,                                    // @4 (4 B)
    pub planes: [AVDRMPlaneDescriptor; AV_DRM_MAX_PLANES],   // @8 (96 B) -> sizeof = 104, align = 8
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct AVDRMFrameDescriptor {
    pub nb_objects: c_int,                                   // @0   (4 B) + 4 B pad @4..8
    pub objects: [AVDRMObjectDescriptor; AV_DRM_MAX_PLANES], // @8   (96 B)
    pub nb_layers: c_int,                                    // @104 (4 B) + 4 B pad @108..112
    pub layers: [AVDRMLayerDescriptor; AV_DRM_MAX_PLANES],   // @112 (416 B) -> sizeof = 528, align = 8
}

#[repr(C)]
pub struct AVVideotoolboxContext {
    pub session: *mut c_void,          // @0  VTDecompressionSessionRef (8 B)
    pub cv_pix_fmt_type: u32,          // @8  OSType (4 B) + 4 B pad @12..16
    pub cm_fmt_desc: *const c_void,    // @16 CMVideoFormatDescriptionRef (8 B)
    pub cm_codec_type: c_int,          // @24 (4 B) + 4 B tail pad @28..32 -> sizeof = 32
}

#[repr(C)]
pub struct AVMediaCodecDeviceContext {
    pub surface: *mut c_void,          // @0  JNI jobject android/view/Surface (8 B)
    pub native_window: *mut c_void,    // @8  ANativeWindow * (8 B)
    pub create_window: c_int,          // @16 (4 B) + 4 B tail pad @20..24 -> sizeof = 24
}

#[repr(C)]
pub struct AVQSVDeviceContext {
    pub session: *mut c_void,          // @0  mfxSession (8 B)
    pub loader: *mut c_void,           // @8  mfxLoader (8 B) -> sizeof = 16
}

#[repr(C)]
pub struct AVQSVFramesContext {
    pub surfaces: *mut c_void,         // @0  mfxFrameSurface1 * (8 B)
    pub nb_surfaces: c_int,            // @8  (4 B)
    pub frame_type: c_int,             // @12 (4 B)
    pub info: *mut c_void,             // @16 mfxFrameInfo * (8 B) -> sizeof = 24
}

#[repr(C)]
pub struct AVVDPAUDeviceContext {
    pub device: u32,                   // @0  VdpDevice (32-bit uint32_t handle!) + 4 B pad @4..8
    pub get_proc_address: Option<unsafe extern "C" fn(u32, u32, *mut *mut c_void) -> c_int>, // @8 (8 B) -> sizeof = 16
}

#[repr(C)]
pub struct AVDXVA2FramesContext {
    pub surface_type: u32,             // @0  Windows DWORD (4 B on LLP64!) + 4 B pad @4..8
    pub surfaces: *mut *mut c_void,    // @8  IDirect3DSurface9 ** (8 B)
    pub nb_surfaces: c_int,            // @16 (4 B) + 4 B pad @20..24
    pub decoder_to_release: *mut c_void, // @24 IDirectXVideoDecoder * (8 B) -> sizeof = 32
}

#[repr(C)]
pub struct AVAMFDeviceContext {
    pub library: *mut c_void,          // @0  (8 B)
    pub factory: *mut c_void,          // @8  AMFFactory * (8 B)
    pub trace_writer: *mut c_void,     // @16 (8 B)
    pub version: i64,                  // @24 (8 B)
    pub context: *mut c_void,          // @32 AMFContext * (8 B)
    pub memory_type: AmfMemoryType,    // @40 (4 B) + 4 B pad @44..48
    pub lock: Option<unsafe extern "C" fn(*mut c_void)>,   // @48 (8 B)
    pub unlock: Option<unsafe extern "C" fn(*mut c_void)>, // @56 (8 B)
    pub lock_ctx: *mut c_void,         // @64 (8 B) -> sizeof = 72
}
```

---

### 4. Windows PE/COFF (LLP64) and macOS Mach-O (`ld64` / `dyld`) Drop-In `cdylib` Binary Compatibility

`Basis: source + execution + normative`

While Linux drop-in replacement centers on ELF `DT_SONAME` and GNU symbol versioning (`@@LIBAVCODEC_63`, covered in `drop-in-libav-cdylib-symbol-versioning-avpriv-elimination-and-h264-mbaff-interop`), neither Windows PE/COFF nor macOS Mach-O encodes per-symbol ELF version nodes. Instead, binary compatibility is governed by **major-versioned DLL/dylib filenames**, **linker export lists (`.def` / `-exported_symbols_list`)**, **LLP64 vs. LP64 primitive widths**, **architecture-specific `va_list` layouts**, **Mach-O two-level symbol namespaces**, and **compact unwind / SEH unwind tables**.

#### 4.1 Shared-Library Naming, Major ABI Versions, and Export Symbol Lists

Verified against `FFmpeg/FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` (`configure:6119-6260`, `compat/windows/makedef:1-149`, and `libav*/version_major.h` / `libavutil/version.h`):

| Library | Major Version at `7ddf7bc8...` (`version_major.h`) | Windows PE/COFF DLL Name (`SLIBNAME_WITH_MAJOR`, `configure:6178,6229`) | Windows Import Lib (MSVC / MinGW, `configure:6189-6190,6233`) | macOS Mach-O Install Name (`configure:6122,6129`) |
| :--- | ---: | :--- | :--- | :--- |
| `libavutil` | `61` (`libavutil/version.h:39`) | `avutil-61.dll` | `avutil.lib` / `libavutil.dll.a` | `$(INSTALL_NAME_DIR)/libavutil.61.dylib` |
| `libavcodec` | `63` (`libavcodec/version_major.h:28`) | `avcodec-63.dll` | `avcodec.lib` / `libavcodec.dll.a` | `$(INSTALL_NAME_DIR)/libavcodec.63.dylib` |
| `libavformat` | `63` (`libavformat/version_major.h:32`) | `avformat-63.dll` | `avformat.lib` / `libavformat.dll.a` | `$(INSTALL_NAME_DIR)/libavformat.63.dylib` |
| `libavdevice` | `63` (`libavdevice/version_major.h:28`) | `avdevice-63.dll` | `avdevice.lib` / `libavdevice.dll.a` | `$(INSTALL_NAME_DIR)/libavdevice.63.dylib` |
| `libavfilter` | `12` (`libavfilter/version_major.h:30`) | `avfilter-12.dll` | `avfilter.lib` / `libavfilter.dll.a` | `$(INSTALL_NAME_DIR)/libavfilter.12.dylib` |
| `libswscale` | `10` (`libswscale/version_major.h:27`) | `swscale-10.dll` | `swscale.lib` / `libswscale.dll.a` | `$(INSTALL_NAME_DIR)/libswscale.10.dylib` |
| `libswresample` | `7` (`libswresample/version_major.h:29`) | `swresample-7.dll` | `swresample.lib` / `libswresample.dll.a` | `$(INSTALL_NAME_DIR)/libswresample.7.dylib` |

*(Note: Cygwin builds use `cygavcodec-63.dll` via `SLIBPREF="cyg"` at `configure:6247`, whereas native Windows `win32|win64` and `mingw32*|mingw64*` use `SLIBPREF=""` and `rust-lang/rust` `windows_msvc.rs:11-12` matches `dll_prefix: ""`, `dll_suffix: ".dll"`.)*

**Windows PE `.def` Export Rules (`compat/windows/makedef` + `configure:6180-6239`):**
1. FFmpeg disables ELF `symver` on Windows (`configure:6214`) and invokes `compat/windows/makedef <subdir>/lib<name>.ver <objs>` (`configure:6191,6230`), which parses the `global:` regex patterns from `libavcodec/libavcodec.v` (`av*;` etc.), matches defined global symbols from `nm --defined-only -g` or `dumpbin.exe -linkermember:1` (or `:32` on `arm64ec`, `makedef:124-130`), strips `$entry_thunk` / `$exit_thunk`, and emits an **unnumbered, ordinal-free `EXPORTS` list** sorted lexicographically (`makedef:148-149`).
2. **Name-based vs. ordinal-based PE binding:** Because `makedef` emits `    av_packet_alloc` without `@ordinal` or `NONAME`, downstream Windows binaries linked against `avcodec.lib` import by **symbol name (`Hint/Name Table`)** rather than hardcoded ordinal, provided the Rust `cdylib` passes `/DEF:avcodec-63.def` (`-C link-arg=/DEF:avcodec-63.def` on `x86_64-pc-windows-msvc` / `-C link-arg=avcodec-63.def` on `x86_64-pc-windows-gnu`). However, if a new minor symbol is inserted alphabetically without `NONAME`, hint indices shift benignly (the PE loader falls back from O(1) hint check to binary search of the Export Name Pointer Table).
3. **PE `DATA` export hazard:** Unlike ELF/Mach-O GOT indirection, PE/COFF distinguishes function exports (which generate an `__imp_<sym>` pointer *plus* a direct jump thunk `<sym>: jmp [__imp_<sym>]` in the `.lib` import library) from global data exports (`av_pix_fmt_descriptors`, `av_codec_ffversion`, `avutil_String` tables), which **must** be marked `DATA` in `.def` when consumed via `__declspec(dllimport)`. In a unified or strictly function-API clean-room Rust `cdylib` that eliminates cross-DLL `avpriv_*` variables (see `drop-in-libav-cdylib-symbol-versioning-avpriv-elimination-and-h264-mbaff-interop`), any remaining public global data symbol in `libavutil/libavutil.v` (e.g., `av_reverse` if legacy, or `ff_*` never exported) must be audited against `.def` `DATA` attributes so C callers reading `extern __declspec(dllimport)` globals dereference `__imp_<sym>` rather than reading x86 `FF 25` thunk machine bytes as table data!
4. **Windows ASLR / HEASLR image-base contract (`configure:6197-6211`):** FFmpeg's 64-bit Windows shared builds enable `--nxcompat --dynamicbase --high-entropy-va` and relocate DLL default image bases above 4 GiB (`--image-base,0x180000000` on MinGW, default `/HIGHENTROPYVA /DYNAMICBASE` on MSVC `link.exe`), ensuring any latent 64->32-bit pointer truncation crashes deterministically at first dereference rather than succeeding silently in the low 2 GiB arena.

#### 4.2 Windows 64-Bit LLP64 (`sizeof(long) == 4`) Layout Drift in `AVIOContext`

`Basis: source + execution`

On 64-bit Linux and macOS (`LP64`), `sizeof(long) == sizeof(unsigned long) == 8`. On 64-bit Windows (`LLP64`, across **both** `x86_64-pc-windows-msvc` / `aarch64-pc-windows-msvc` and `x86_64-pc-windows-gnu`), `sizeof(long) == sizeof(unsigned long) == 4` (`core::ffi::c_long = i32`, `core::ffi::c_ulong = u32`).

Scanning all 57 public FFmpeg headers at `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` for bare `long` / `unsigned long` (excluding `long long`) identifies `AVIOContext` (`libavformat/avio.h:244-246`) as a severe cross-platform binary layout divergence:

```c
/* libavformat/avio.h:237-246 */
    int64_t pos;            /* @72 (8 B) */
    int eof_reached;        /* @80 (4 B) */
    int error;              /* @84 (4 B) */
    int write_flag;         /* @88 (4 B) */
    int max_packet_size;    /* @92 (4 B) */
    int min_packet_size;    /* @96 (4 B) -> ends at byte 100 (NOT 8-byte aligned!) */
    unsigned long checksum;
    unsigned char *checksum_ptr;
    unsigned long (*update_checksum)(unsigned long checksum, const uint8_t *buf, unsigned int size);
```

Executed `layout_probe.c` measurements demonstrate a **double layout shift** (4 bytes from eliminating pre-`checksum` alignment padding + 4 bytes from shrinking `checksum` itself = **8 bytes total shift** across every trailing field):

| `AVIOContext` Metric / Field | 64-Bit Linux & macOS (`LP64`) | 64-Bit Windows (`LLP64`) | Byte Delta (`Win64 - LP64`) | Consequence of Hardcoding `u64` / `usize` in Rust on Windows |
| :--- | ---: | ---: | ---: | :--- |
| `min_packet_size` offset | `96` (4 B) | `96` (4 B) | `0` | Aligned identically up to byte `100`. |
| Implicit alignment pad after `min_packet_size` | `4 B` (`@100..104`) | **`0 B`** | `-4 B` | `u32` requires only 4-byte alignment; byte `100` is already 4-byte aligned. |
| `checksum` offset & size | `@104` (`8 B`) | **`@100` (`4 B`)** | `-4 B` offset, `-4 B` size | High 32 bits of `u64` overwrite low 32 bits of `checksum_ptr`! |
| `checksum_ptr` offset | `@112` (`8 B`) | **`@104` (`8 B`)** | **`-8 B`** | Pointer read/write shifted by one full 64-bit word. |
| `update_checksum` fnptr offset & signature | `@120`, `fn(u64, *const u8, u32) -> u64` | **`@112`**, `fn(u32, *const u8, u32) -> u32` | **`-8 B`** + 32-bit return | Calling C `av_adler32_update` / zlib `crc32` reads uninitialized upper 32 bits of `%rax` if typed `-> u64`; shifted offset invokes `read_pause` as `update_checksum`! |
| `read_pause`, `read_seek`, `seekable`, `direct`, `protocol_whitelist`, `protocol_blacklist`, `write_data_type`, `ignore_boundary_point`, `buf_ptr_max`, `bytes_read`, `bytes_written` | `@128 .. @200` | **`@120 .. @192`** | **`-8 B`** across all 11 fields | Total corruption of custom `AVIOContext` seek/pause callbacks and protocol whitelists. |
| Total `sizeof(AVIOContext)` | **`208 B`** | **`200 B`** | **`-8 B`** | Heap overread if Rust copies `size_of::<AVIOContext>()` (`208 B`) from a `200 B` C allocation. |

**Mandatory Rust FFI Rule:** Every occurrence of C `long` / `unsigned long` (`AVIOContext::checksum`, `AVIOContext::update_checksum`) must be typed with `core::ffi::c_ulong`, and every Windows SDK `DWORD` / `LONG` / `ULONG` / `HRESULT` (`AVDXVA2FramesContext::surface_type`) must be typed as fixed-width `u32` / `i32`, never `c_ulong` on non-Windows host tests.

#### 4.3 Variadic `va_list` ABI Matrix (`av_vlog`, `av_log_set_callback`, `av_vbprintf`, `avio_vprintf`)

`Basis: normative + source + execution`

Scanning `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` public headers locates six public `va_list` entry points/callbacks:
- `libavutil/log.h:307`: `void av_vlog(void *avcl, int level, const char *fmt, va_list vl);`
- `libavutil/log.h:337`: `void av_log_set_callback(void (*callback)(void*, int, const char*, va_list));`
- `libavutil/log.h:352-353`: `void av_log_default_callback(void *avcl, int level, const char *fmt, va_list vl);`
- `libavutil/log.h:372,389`: `av_log_format_line` / `av_log_format_line2(..., va_list vl, ...)`
- `libavutil/bprint.h:165`: `void av_vbprintf(AVBPrint *buf, const char *fmt, va_list vl_arg);`
- `libavformat/avio.h:528`: `int avio_vprintf(AVIOContext *s, const char *fmt, va_list ap);`

Unlike fixed-arity C functions, `va_list` has **four pairwise-incompatible representations** across Tier-1 64-bit targets:

| Target Triple | `sizeof(va_list)` | Underlying C Representation | Function Parameter Passing (`f(..., va_list vl)`) | Variadic Argument Storage Layout |
| :--- | ---: | :--- | :--- | :--- |
| `x86_64-pc-windows-msvc` / `gnu` | **`8 B`** (`align 8`) | `char *` (`__builtin_ms_va_list`, verified `sizeof = 8` in `layout_probe.c`) | Passed by value in 4th GPR (`%r9` for `av_vlog`) as a raw `char *` stack pointer | Caller spills variadic GPRs (`%rcx`, `%rdx`, `%r8`, `%r9`) into the 32-byte contiguous **shadow/home space** immediately above return address; FP variadics are duplicated in GPRs + XMMs, so `va_arg` simply increments `char *` by 8 bytes! |
| `aarch64-apple-darwin` (Apple ARM64 ABI) | **`8 B`** (`align 8`) | `char *` (diverging from standard ARM AAPCS64!) | Passed by value in `x3` as a raw `char *` stack pointer | Apple ARM64 ABI mandates that **all anonymous variadic arguments (`...`) are passed purely on the stack** (8-byte slots, never in `x0..x7` / `v0..v7`!), allowing `va_list` to be a single `char *`. |
| `x86_64-apple-darwin` & `x86_64-unknown-linux-gnu` (SysV AMD64) | **`24 B`** (`align 8`) | `struct __va_list_tag { u32 gp_offset; u32 fp_offset; void *overflow_arg_area; void *reg_save_area; }[1]` (verified `sizeof = 24`) | Array-to-pointer decay passes **`__va_list_tag *` (`8 B` pointer in `%rcx`)**! **Mutation trap:** Calling `va_arg` inside a callee mutates the caller's `gp_offset`/`fp_offset` in place unless copied with `va_copy`! | Split register save area (`48 B` for 6 GPRs + `128 B` for 8 XMMs) plus stack `overflow_arg_area`. |
| `aarch64-unknown-linux-gnu` & `aarch64-linux-android` (AAPCS64) | **`32 B`** (`align 8`) | `struct __va_list { void *__stack; void *__gr_top; void *__vr_top; int __gr_offs; int __vr_offs; }` | Struct > 16 B passed by **indirect pointer (`__va_list *`)** in `x3`, **without** C array decay (copying semantics differ from x86_64 `[1]` array when taking `&vl`!) | Separate general-register (`__gr_top + __gr_offs`) and vector-register (`__vr_top + __vr_offs`) save areas plus `__stack`. |

**Architectural Consequence for Clean-Room Rust `av_log` / `av_vbprintf`:**
1. **Never cast `va_list` to `*mut c_void`:** On x86_64 SysV/macOS, passing a `va_list` twice to two formatting helpers without `va_copy` advances `gp_offset` during the first call and reads garbage registers on the second call (`av_log_format_line2` + `fputs`), whereas on Windows x64 and macOS `arm64` `va_list` is passed by `char *` value!
2. **Rust `c_variadic` vs. Tiny Verified C/MIR Formatting Shim:** Either use nightly Rust's `core::ffi::VaList` (`va_copy` via `VaListImpl::with_copy`) or bound `va_list` consumption inside a minimal ~40-line `vsnprintf`-equivalent C/Rust-intrinsic boundary that immediately materializes `(fmt, va_list)` into a stack/heap UTF-8/byte buffer via `va_copy` before invoking pure safe Rust logging/BPrint state machines, while storing registered C `av_log_set_callback` pointers with their exact target `VaList` ABI type so forwarding `av_vlog` to a C application's custom log callback preserves register/stack state across all four ABIs.

#### 4.4 C `enum` Underlying Signedness and Sub-32-Bit Register Extension

`Basis: normative + execution + source`

Executed `layout_probe.c` output confirms a subtle C11 vs. MSVC ABI split:
- **Enums with negative sentinels** (`enum AVPixelFormat` with `AV_PIX_FMT_NONE = -1` at `pixfmt.h:71`; `enum AVSampleFormat` with `AV_SAMPLE_FMT_NONE = -1` at `samplefmt.h:55`; `enum AVMediaType` with `AVMEDIA_TYPE_UNKNOWN = -1` at `avutil.h:198`; `enum AVChannel` with `AV_CHAN_NONE = -1` at `channel_layout.h:47`; `enum AVDiscard` with `AVDISCARD_NONE = -16` at `defs.h:239`) compile to **4-byte `signed int` (`i32`)** across SysV GCC/Clang and MSVC.
- **Enums with exclusively non-negative enumerators** (`enum AVHWDeviceType` `0..14` at `hwcontext.h:27-44`; `enum AVColorRange`, `enum AVColorPrimaries`, `enum AVColorTransferCharacteristic`, `enum AVColorSpace`, `enum AVChromaLocation` at `pixfmt.h`; `enum AMF_MEMORY_TYPE` `0..12` at `AMF_Data.h:53-68`) compile to **4-byte `unsigned int` (`u32`)** under SysV GCC/Clang (`(enum AVHWDeviceType)-1 < 0` evaluates to `0`), but compile to **4-byte `signed int` (`i32`)** under Microsoft `cl.exe` (`x86_64-pc-windows-msvc`)!
- **Calling-convention and `bool` extension on `aarch64-apple-darwin`:** Unlike standard ARM AAPCS64 (where upper bits of 32/64-bit registers holding `< 32-bit` integer/boolean values are unspecified at call boundaries), Apple's ARM64 ABI requires the **caller** to sign-extend signed `< 32-bit` integers (`int8_t`, `int16_t`) and zero-extend unsigned `< 32-bit` integers (`uint8_t`, `uint16_t`, C23/`stdbool.h` `bool`, such as `bool full_range` in `av_map_videotoolbox_format_from_pixfmt2(enum AVPixelFormat pix_fmt, bool full_range)` at `hwcontext_videotoolbox.h:65`) to 32 bits in `w0..w7`. `rustc` enforces this automatically via LLVM `zeroext`/`signext` attributes on `aarch64-apple-darwin` (`rust-lang/rust` `apple/mod.rs`) **if and only if** the Rust FFI signature uses `bool` (not `u32` or `c_int`!) for C `bool` parameters. For 32-bit C enums (`i32` vs `u32`), both occupy full 32-bit `wN` / `%edi` registers without sub-32-bit extension divergence, so `#[repr(transparent)] pub struct AVHWDeviceType(pub c_int)` (or `#[cfg_attr(windows, ...)]` `i32`/`u32` alias) is register-compatible across all 64-bit targets while remaining 100% immune to Rust enum niche UB.

#### 4.5 macOS Darwin `ld64` / `lld` Linking (`@rpath`, Two-Level Namespaces) and `__LD,__compact_unwind` vs. Windows SEH

`Basis: source + normative`

1. **`-install_name` (`@rpath`), Versioning, and `-exported_symbols_list` (`configure:6121-6140`):**
   - Upstream FFmpeg links Darwin `.dylib` targets with:
     ```text
     -dynamiclib -Wl,-single_module -Wl,-install_name,$(INSTALL_NAME_DIR)/$(SLIBNAME_WITH_MAJOR),-current_version,$(LIBVERSION),-compatibility_version,$(LIBMAJOR)
     ```
     (`configure:6122`). For relocatable app bundles, frameworks, and Python/Rust wheels, `$(INSTALL_NAME_DIR)` is set to **`@rpath`** (`LC_ID_DYLIB = @rpath/libavcodec.63.dylib`), while inter-library dependencies (`libavformat.63.dylib` -> `libavcodec.63.dylib` + `libavutil.61.dylib`) record `@rpath/libavcodec.63.dylib` (`LC_LOAD_DYLIB`) together with `LC_RPATH = @loader_path` so co-located `.dylib` siblings resolve cleanly without `DYLD_LIBRARY_PATH` (which Hardened Runtime `CS_RESTRICT` strips!).
   - Notice `dyld` version check semantics (`apple-oss-distributions/dyld@fd8d0c4d52320ebf64db34f3cb280310d905c5ae`): if an existing host binary was linked against `libavcodec.63.dylib` with `compatibility_version = 63.0.0`, a drop-in Rust `cdylib` **must** pass `-Wl,-compatibility_version,63.0.0 -Wl,-current_version,63.<minor>.<micro>`; omitting `-compatibility_version` defaults `LC_ID_DYLIB` compatibility version to `0.0.0` in `rustc`, which `dyld` rejects at load time (`incompatible library version: requires version 63.0.0 or later, but libavcodec.63.dylib provides version 0.0.0`)!
   - Mach-O prepends a leading underscore (`_`) to all C symbols (`avcodec_open2` -> `_avcodec_open2`). FFmpeg transforms `libavcodec.v` into a Darwin export file via `VERSION_SCRIPT_POSTPROCESS_CMD` (`configure:6139-6140`), prefixing `_` and passing `-Wl,-exported_symbols_list,<file>` so internal Rust/C symbols (`_ZN...`, helper functions) remain `N_PEXT` private-external rather than polluting the global export trie.

2. **Mach-O Two-Level Namespaces (`MH_TWOLEVEL`) vs. ELF Flat Interposition:**
   - By default since macOS 10.1, `ld64` and `lld` emit Mach-O images with `MH_TWOLEVEL` in `mach_header_64.flags`. Every imported symbol in `__DATA_CONST,__got` / dyld chained fixups binds a **pair `(library_ordinal, _symbol_name)`** (e.g., `(libavutil.61.dylib, _av_malloc)`), **not** a flat process-wide symbol name!
   - **Architectural upside and trap:** Unlike Linux ELF (where a monolithic `libavcodec.so` or `LD_PRELOAD` shim can accidentally or intentionally interpose symbols across shared libraries), on macOS `dyld` resolves `_av_frame_alloc` in a caller strictly against the ordinal of `libavutil.61.dylib`. Consequently, splitting vs. merging FFmpeg's 7 libraries on macOS cannot rely on flat symbol fallback: if a prebuilt C binary records `LC_LOAD_DYLIB @rpath/libavutil.61.dylib` and `LC_LOAD_DYLIB @rpath/libavcodec.63.dylib`, **both** `.dylib` files must exist at `@rpath` (either as separate Rust `cdylib` crates or as thin Mach-O `-reexport_library` umbrella stubs forwarding `_av_*` exports via `LC_REEXPORT_DYLIB`!).

3. **Mach-O `__LD,__compact_unwind` -> `__TEXT,__unwind_info` Binary Encoding (`llvm/llvm-project@c51c6d10cd1b612b8d0c8913ed3f449c535c6933`):**
   Verified directly in `libunwind/include/mach-o/compact_unwind_encoding.h:18-485` and `lld/MachO/UnwindInfoSection.cpp:36-65,386-441`:
   - Compilers emit per-function 32-byte relocatable rows (`range-start` 8 B, `range-length` 4 B, `compact_unwind_encoding_t` 4 B, `personality` 8 B, `lsda` 8 B; `compact_unwind_encoding.h:358-385`) into `__LD,__compact_unwind`, which `ld64` / `lld` folds into a two-level page-indexed binary search table in **`__TEXT,__unwind_info`** (`UNWIND_SECTION_VERSION = 1`, `4096`-byte second-level regular pages holding 511 entries or compressed pages holding up to 1,021 entries indexing up to **`COMMON_ENCODINGS_MAX = 127`** shared 32-bit encodings; `compact_unwind_encoding.h:420-484`, `UnwindInfoSection.cpp:36`).
   - **Architecture Modes (`compact_unwind_encoding.h:205-343`):**
     - **`arm64` / `arm64e`:** `rustc` sets `FramePointer::NonLeaf` (`rust-lang/rust` `apple/mod.rs:157`). Non-leaf functions with standard `stp x29, x30, [sp, #-N]! ; mov x29, sp` prologues and contiguously ordered register pairs (`x19..x28` bits `0..4`, `d8..d15` bits `8..11`) use **`UNWIND_ARM64_MODE_FRAME` (`0x04000000`)** (or **`UNWIND_ARM64_MODE_FRAME_PAUTH_LR` (`0x05000000`)** on `arm64e` with `pacibsppc`). Leaf functions without `FP/LR` push use **`UNWIND_ARM64_MODE_FRAMELESS` (`0x02000000`)**, encoding `stack_size / 16` in bits `12..23` (`UNWIND_ARM64_FRAMELESS_STACK_SIZE_MASK = 0x00FFF000`, max frame `65,520 B`). Functions with dynamic stack realignment (e.g., 32/64-byte stack-aligned scratch buffers), non-contiguous callee-saved register spills, or hand-written `.S` assembly lacking canonical prologues fall back to **`UNWIND_ARM64_MODE_DWARF` (`0x03000000`)**.
     - **`x86_64`:** `rustc` sets `FramePointer::Always` (`apple/mod.rs:158`), emitting **`UNWIND_X86_64_MODE_RBP_FRAME` (`0x01000000`)** (`RBP` offset up to `2,040 B` in `0x00FF0000`, up to five 3-bit register IDs `rbx, r12..r15` in `0x00007FFF`), or frameless `STACK_IMMD` (`0x02000000`, Lehmer permutation in `0x000003FF`) / `STACK_IND` (`0x03000000`), else **`UNWIND_X86_64_MODE_DWARF` (`0x04000000`)**.
   - **Two Hard Mach-O Linker / Runtime Limits:**
     1. **Maximum 3 Unwind Personalities per Mach-O `.dylib` (`UnwindInfoSection.cpp:436-439`):** Because `UNWIND_PERSONALITY_MASK` (`0x30000000`, `compact_unwind_encoding.h:47`) is a **2-bit field** (`0` = no personality, `1..3` = 1-based index into `personalities[]`), `ld64` and `lld` abort linking with **`error: too many personalities (> 3) for compact unwind to encode`** if a single `.dylib` combines more than three distinct personality routines (e.g., `rust_eh_personality` + C++ `___gxx_personality_v0` + Objective-C `___objc_personality_v0` + a custom C/ASM personality). Compiling the Rust `cdylib` with `panic = "abort"` (eliminating `rust_eh_personality` and LSDA tables) **and** isolating C++ codecs (`libx265`) into out-of-process XPC helpers keeps personality count at `0..1` and maximizes compressed `__unwind_info` density.
     2. **16 MiB (`0x00FFFFFF`) `__TEXT,__eh_frame` Offset Cap (`UnwindInfoSection.cpp:54-59,386-390`):** `UNWIND_ARM64_DWARF_SECTION_OFFSET` and `UNWIND_X86_64_DWARF_SECTION_OFFSET` occupy the low 24 bits (`0x00FFFFFF = 16,777,215 B`). If non-canonical hand-written SIMD assembly or DWARF-only object files inflate `__TEXT,__eh_frame` past 16 MiB, `lld` zeros `dwarfOffsetHint` (`line 389`), degrading exception/backtrace unwinding to slow section scans (and older `ld64` versions reject large `__eh_frame` sections outright). Every hand-written Darwin `.S` SIMD kernel should therefore either preserve a frameless leaf / canonical `x29/x30` prologue or omit unnecessary `.cfi_*` bloat when `nounwind`.

4. **Cross-Language Unwind & Windows x64 `.pdata` / `.xdata` (`requires_uwtable: true`):**
   - On Windows x64 (`rust-lang/rust` `windows_msvc.rs:19`: `requires_uwtable: true`), every non-leaf function—including `extern "C"` functions and hand-written `.asm` / `global_asm!` SIMD kernels that allocate stack space or save non-volatile registers (`rbx, rbp, rdi, rsi, r12..r15, xmm6..xmm15`)—**must** emit PE `.pdata` (`RUNTIME_FUNCTION`) and `.xdata` (`UNWIND_INFO`) records; otherwise `RtlVirtualUnwind` fails during Vectored Exception Handling, ETW stack sampling, or C++ callback exceptions.
   - Across both Windows and macOS, Rust `#[no_mangle] pub unsafe extern "C" fn av_*` entry points enforce `nounwind` abort barriers against internal panics (which are already absent under panic-free / `panic = "abort"` compilation), whereas invoking user-supplied C callbacks (`AVCodecContext::get_buffer2`, `AVIOContext::read_packet`) that a C++/Objective-C host might unwind through requires `extern "C-unwind"` function pointer types if host-side longjmp/C++ exception pass-through is supported (see `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`).

## Boundaries

1. **Not examined — Native Windows Kernel Execution and macOS XNU Runtime Benchmarks:**
   - Because validation executed on an `x86_64` Linux build host (`GCC` C11), Windows `CreateAppContainerProfile` / `DuplicateHandle` / `SetProcessMitigationPolicy` and macOS `mach_make_memory_entry_64` / `sandbox_init` / `ld64` contracts were verified from **primary kernel/browser/compiler source code** (`apple-oss-distributions/xnu`, `chromium/chromium`, `llvm/llvm-project`, `mingw-w64/mingw-w64`, `rust-lang/rust`) and normative Microsoft/Apple documentation rather than live Windows 11 or macOS 15 kernel syscalls. End-to-end IPC round-trip latency (microseconds per 4K frame over Windows Named Pipes + Section views vs. macOS XPC + Mach memory entries) was **not examined** experimentally and must not be extrapolated from Linux `memfd` + `eventfd` numbers.
2. **Not examined — Vendor SDK Private Internal Structs (`mfxFrameSurface1`, `DXVA2_ConfigPictureDecode`, `AMFSurfaceVtbl`):**
   - The executed `layout_probe.c` verified exact `sizeof`/`alignof`/`offsetof` for all 22 FFmpeg public hardware-context structs using minimal verified handle/pointer typedefs (`mfxSession`, `VdpDevice`, `DWORD`, `cl_mem`, `OSType`). The internal field layouts of opaque vendor-owned structs pointed to *by* those pointers (such as `mfxFrameSurface1` in `oneVPL` `api/vpl/mfxstructures.h` or `AMFSurfaceVtbl` in `AMF/core/Surface.h`) were **not examined** in `layout_probe.c`; implementations calling vendor SDK methods directly must bind against the vendor SDK headers at the pinned revisions (`oneapi-src/oneVPL@ec718e8...`, `GPUOpen-LibrariesAndSDKs/AMF@57ee0cf...`).
3. **Known not to apply — `xpc_shmem_create` and `IOSurfaceLock(..., kIOSurfaceLockReadOnly, ...)` as Untrusted Read-Only Memory Boundaries:**
   - Neither `xpc_shmem_create` nor `IOSurfaceLock` with `kIOSurfaceLockReadOnly` enforces kernel MMU write denial against a compromised XPC worker holding the resulting `xpc_object_t` / `IOSurfaceRef` send right. Treating either primitive as equivalent to Linux `F_SEAL_FUTURE_WRITE` is **known not to apply**.
4. **Known not to apply — LP64 `AVIOContext` Offsets on 64-Bit Windows (`x86_64-pc-windows-*`, `aarch64-pc-windows-*`):**
   - Assuming 64-bit pointer width implies 8-byte `unsigned long` is **known not to apply** on all 64-bit Windows targets (`LLP64`), where `AVIOContext` shrinks from `208 B` to `200 B` and shifts 13 fields after `min_packet_size` by `-8 B`.
5. **Unsupported — 32-Bit (`i686` / `armv7`) Struct Offsets and `__stdcall` Name Decorations:**
   - All `sizeof`/`offsetof` tables in Section 3.2 apply strictly to **64-bit targets** (`LP64` and `LLP64`, which agree on all 22 Section 3.2 structs because none of those 22 structs uses bare `long`). On 32-bit `i686-pc-windows-msvc` / `armv7`, pointer and `size_t`/`ptrdiff_t` fields shrink from `8 B` to `4 B` (changing `AVDRMFrameDescriptor` from `528 B` to `352 B`), and 32-bit Windows COM/AMF vtables use callee-cleanup `__stdcall` (`@N` stack decoration). 32-bit layout tables are **not examined** here.
6. **Unknown — Future Apple Removal of `sandbox_init` for Unpackaged CLI Helpers:**
   - While `sandbox_init` / `sandbox_init_with_parameters` remains functional in current macOS releases and underpins Chromium/Firefox unpackaged helper sandboxes, Apple marks the C API deprecated without providing a public non-bundled replacement outside `.app`-embedded App Sandbox `.xpc` services; whether a future macOS major release restricts `sandbox_init` to platform/entitled binaries is **unknown**.

## Evidence

### 1. Primary-Source Repository Coordinates

All GitHub commit revisions below are full 40-hex immutable commits recorded in `REPORT.json` `subjects` and inspected on `2026-11-20`:

- **`FFmpeg/FFmpeg` @ `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80`:**
  - Base contexts & enum: `libavutil/hwcontext.h:27-221`.
  - Nine `AVHWDeviceType` headers & implementations: `libavutil/hwcontext_drm.{h,c}`, `libavutil/hwcontext_videotoolbox.{h,c}`, `libavutil/hwcontext_mediacodec.{h,c}`, `libavutil/hwcontext_qsv.{h,c}`, `libavutil/hwcontext_opencl.{h,c}`, `libavutil/hwcontext_vdpau.{h,c}`, `libavutil/hwcontext_dxva2.{h,c}`, `libavutil/hwcontext_amf.{h,c}`, `libavutil/hwcontext_oh.{h,c}`.
  - Companion `libavcodec` hwaccel headers: `libavcodec/videotoolbox.h:57-79`, `libavcodec/mediacodec.h:33-103`, `libavcodec/qsv.h:36-107`, `libavcodec/vdpau.h:62-135`, `libavcodec/dxva2.h:54-84`.
  - LLP64, `va_list`, enum, and linker contracts: `libavformat/avio.h:231-275,528`, `libavutil/log.h:307-389`, `libavutil/bprint.h:165`, `libavutil/pixfmt.h:71`, `libavutil/samplefmt.h:55`, `libavutil/avutil.h:198`, `libavutil/channel_layout.h:47`, `libavcodec/defs.h:239`, `libav*/version_major.h`, `libavutil/version.h:39`, `configure:6119-6260`, `compat/windows/makedef:1-149`.
- **`chromium/chromium` @ `35a0816efc03ad8fed8920050497050ed1d23a08`:**
  - Windows NT section permission stripping, empty DACL, `NtQuerySection` (`SEC_IMAGE`), and `DuplicateHandle(..., FILE_MAP_READ | SECTION_QUERY, ...)`: `base/memory/platform_shared_memory_region_win.cc:58-176,238-370`.
  - Darwin Mach memory entry read-only conversion and `KERN_INVALID_RIGHT` write-probe verification: `base/memory/platform_shared_memory_region_apple.cc:73-191`.
- **`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`:**
  - `mach_make_memory_entry_64` and `MAP_MEM_VM_SHARE` shared-object vs. copy semantics, `user_entry->protection`, and `PAGE_MASK` rounding: `osfmk/vm/vm_memory_entry.c:58-90,638-860,956-966,1019-1197`.
  - `mach_vm_remap` / `mach_vm_remap_new` MIG definitions and external entry points: `osfmk/mach/mach_vm.defs:390-540`, `osfmk/vm/vm_user.c:851-1055`, `osfmk/mach/vm_prot.h:87-170`.
  - Hardened Runtime (`CS_RUNTIME`, `CS_HARD`, `CS_KILL`, `CS_RESTRICT`, `CS_REQUIRE_LV`, `CS_EXECSEG_JIT`): `osfmk/kern/cs_blobs.h:36-86`, `bsd/sys/codesign.h:40-61`.
- **`llvm/llvm-project` @ `c51c6d10cd1b612b8d0c8913ed3f449c535c6933`:**
  - Darwin `__LD,__compact_unwind` and `__TEXT,__unwind_info` format, x86_64/arm64/arm64e mode encodings, Lehmer register permutations: `libunwind/include/mach-o/compact_unwind_encoding.h:18-485`.
  - LLD Mach-O `COMMON_ENCODINGS_MAX = 127`, `DWARF_SECTION_OFFSET` (`0x00FFFFFF` 16 MiB hint cap), and `personalities.size() > 3` link error: `lld/MachO/UnwindInfoSection.cpp:36,54-59,386-391,436-439`.
- **`rust-lang/rust` @ `5c56312f346d7cc8209d9fc0fd660c72e6fc6950`:**
  - Windows MSVC `cdylib` defaults and `requires_uwtable: true`: `compiler/rustc_target/src/spec/base/windows_msvc.rs:6-37`.
  - Apple Darwin Mach-O `FramePointer::NonLeaf` (`arm64`) / `FramePointer::Always` (`x86_64`), `.dylib` suffix, `has_rpath: true`, `eh_frame_header: false`: `compiler/rustc_target/src/spec/base/apple/mod.rs:122-207`.
- **`mingw-w64/mingw-w64` @ `7095c702af7836f12a4d904555546d6abbf28b2c`:**
  - `PROCESS_MITIGATION_SYSTEM_CALL_DISABLE_POLICY`, `PROCESS_MITIGATION_DYNAMIC_CODE_POLICY`, `SECURITY_CAPABILITIES`, `JOBOBJECT_EXTENDED_LIMIT_INFORMATION`, `JOBOBJECT_BASIC_UI_RESTRICTIONS`, `SECTION_MAP_READ`/`WRITE`: `mingw-w64-headers/include/winnt.h:4507,4824-4884,5023-5045,5289-5335,5883-5890`.
  - `CreateFileMappingW`, `MapViewOfFile`, `FILE_MAP_READ`/`WRITE`: `mingw-w64-headers/include/memoryapi.h:43-50,91-94`.
  - `DuplicateHandle`: `mingw-w64-headers/include/handleapi.h:20`.
  - `UpdateProcThreadAttribute`, `SetProcessMitigationPolicy`: `mingw-w64-headers/include/processthreadsapi.h:246-249`.
  - `CreateAppContainerProfile`: `mingw-w64-headers/include/userenv.h:235-239`.
- **Vendor SDK Type Definitions:**
  - `oneapi-src/oneVPL` @ `ec718e8ede859f16d29c3cdeba3a3025031bc83d`: `api/vpl/mfxsession.h:19` (`typedef struct _mfxSession *mfxSession;`), `api/vpl/mfxdispatcher.h:19` (`typedef struct _mfxLoader *mfxLoader;`).
  - `GPUOpen-LibrariesAndSDKs/AMF` @ `57ee0cfb0e1a08d9041f77435653794c1b012be0`: `amf/public/include/core/Data.h:53-68` (`enum AMF_MEMORY_TYPE`), `amf/public/include/core/Platform.h:114-129,182-188` (`AMF_STD_CALL`, `amf_int64`).
  - `KhronosGroup/OpenCL-Headers` @ `82f60316cc142e7b21dc1d8983b26de18858fbd9`: `CL/cl.h:35-39` (`cl_device_id`, `cl_context`, `cl_command_queue`, `cl_mem`).
  - `vdpau/libvdpau` (`https://gitlab.freedesktop.org/vdpau/libvdpau`, `include/vdpau/vdpau.h:839,1538,1732`): `typedef uint32_t VdpChromaType;`, `typedef uint32_t VdpDevice;`, `typedef uint32_t VdpVideoSurface;`, `typedef uint32_t VdpDecoder;`.

### 2. Reproducible 64-Bit C11 `layout_probe.c` and Recorded Output

`Basis: execution`

Executed on `x86_64` Linux (`GCC` C11, `-std=c11 -O2 -Wall -Wextra -Werror` and `-std=c11 -O2 -Wall -Wextra -Werror -mms-bitfields`, `diff -u` exit code `0`) against the unmodified `FFmpeg@7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` headers with minimal vendor handle typedef shims (`mock_sdk/`):

```c
/* Minimal vendor SDK typedef shims (mock_sdk/) used when vendor SDKs are absent on host:
 * - CL/cl.h: typedef struct _cl_{device_id,context,command_queue,mem} *cl_{device_id,context,command_queue,mem};
 * - VideoToolbox/VideoToolbox.h: typedef uint32_t OSType; typedef const struct __CFString *CFStringRef;
 *   typedef struct __CVBuffer *CVPixelBufferRef; typedef struct OpaqueVTDecompressionSession *VTDecompressionSessionRef;
 *   typedef const struct opaqueCMFormatDescription *CMVideoFormatDescriptionRef;
 * - mfxvideo.h: typedef struct _mfxSession *mfxSession; struct mfxFrameSurface1; struct mfxFrameInfo; struct mfxExtBuffer;
 * - vdpau/vdpau.h: typedef int VdpStatus; typedef uint32_t VdpDevice, VdpVideoSurface, VdpDecoder, VdpChromaType;
 *   typedef VdpStatus VdpGetProcAddress(VdpDevice, uint32_t, void **);
 *   typedef VdpStatus VdpDecoderRender(VdpDecoder, VdpVideoSurface, const void *, uint32_t, const struct VdpBitstreamBuffer *);
 * - d3d9.h / dxva2api.h: typedef uint32_t DWORD; struct IDirect3DSurface9; typedef struct IDirect3DSurface9 *LPDIRECT3DSURFACE9;
 *   struct IDirect3DDeviceManager9; struct IDirectXVideoDecoder; struct DXVA2_ConfigPictureDecode;
 * - AMF/core/Factory.h: struct AMFFactory; struct AMFContext; struct AMFHDRMetadata;
 *   enum AMF_MEMORY_TYPE { AMF_MEMORY_UNKNOWN = 0 }; enum AMF_SURFACE_FORMAT { AMF_SURFACE_UNKNOWN = 0 };
 *   enum AMF_VIDEO_CONVERTER_COLOR_PROFILE_ENUM { AMF_VIDEO_CONVERTER_COLOR_PROFILE_UNKNOWN = -1 };
 */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>

#include "libavutil/hwcontext.h"
#include "libavutil/hwcontext_drm.h"
#include "libavutil/hwcontext_videotoolbox.h"
#include "libavutil/hwcontext_mediacodec.h"
#include "libavutil/hwcontext_qsv.h"
#include "libavutil/hwcontext_opencl.h"
#include "libavutil/hwcontext_vdpau.h"
#include "libavutil/hwcontext_dxva2.h"
#include "libavutil/hwcontext_amf.h"
#include "libavutil/hwcontext_oh.h"
#include "libavcodec/videotoolbox.h"
#include "libavcodec/mediacodec.h"
#include "libavcodec/qsv.h"
#include "libavcodec/vdpau.h"
#include "libavcodec/dxva2.h"
#include "libavformat/avio.h"

#define SHOW_STRUCT(T) printf("STRUCT %-28s sizeof=%3zu alignof=%2zu\n", #T, sizeof(T), _Alignof(T))
#define SHOW_FIELD(T, F) printf("  FIELD %-27s offset=%3zu sizeof=%3zu\n", #F, offsetof(T, F), sizeof(((T *)0)->F))

typedef struct AVIOContext_Win64_LLP64 {
    const AVClass *av_class; unsigned char *buffer; int buffer_size;
    unsigned char *buf_ptr; unsigned char *buf_end; void *opaque;
    int (*read_packet)(void *, uint8_t *, int);
    int (*write_packet)(void *, const uint8_t *, int);
    int64_t (*seek)(void *, int64_t, int);
    int64_t pos; int eof_reached, error, write_flag, max_packet_size, min_packet_size;
    uint32_t checksum; /* Windows x64 LLP64: sizeof(unsigned long) == 4, alignof == 4 */
    unsigned char *checksum_ptr;
    uint32_t (*update_checksum)(uint32_t, const uint8_t *, unsigned int);
    int (*read_pause)(void *, int);
    int64_t (*read_seek)(void *, int, int64_t, int);
    int seekable, direct; const char *protocol_whitelist, *protocol_blacklist;
    int (*write_data_type)(void *, const uint8_t *, int, enum AVIODataMarkerType, int64_t);
    int ignore_boundary_point; unsigned char *buf_ptr_max;
    int64_t bytes_read, bytes_written;
} AVIOContext_Win64_LLP64;

int main(void) {
    SHOW_STRUCT(AVHWDeviceContext); SHOW_STRUCT(AVHWFramesContext);
    SHOW_STRUCT(AVDRMObjectDescriptor); SHOW_FIELD(AVDRMObjectDescriptor, fd);
    SHOW_FIELD(AVDRMObjectDescriptor, size); SHOW_FIELD(AVDRMObjectDescriptor, format_modifier);
    SHOW_STRUCT(AVDRMPlaneDescriptor); SHOW_STRUCT(AVDRMLayerDescriptor);
    SHOW_STRUCT(AVDRMFrameDescriptor); SHOW_FIELD(AVDRMFrameDescriptor, nb_objects);
    SHOW_FIELD(AVDRMFrameDescriptor, objects); SHOW_FIELD(AVDRMFrameDescriptor, nb_layers);
    SHOW_FIELD(AVDRMFrameDescriptor, layers); SHOW_STRUCT(AVDRMDeviceContext);
    SHOW_STRUCT(AVVTFramesContext); SHOW_STRUCT(AVVideotoolboxContext);
    SHOW_STRUCT(AVMediaCodecDeviceContext); SHOW_STRUCT(AVMediaCodecContext);
    SHOW_STRUCT(AVQSVDeviceContext); SHOW_STRUCT(AVQSVFramesContext); SHOW_STRUCT(AVQSVContext);
    SHOW_STRUCT(AVOpenCLFrameDescriptor); SHOW_STRUCT(AVOpenCLDeviceContext); SHOW_STRUCT(AVOpenCLFramesContext);
    SHOW_STRUCT(AVVDPAUDeviceContext); SHOW_STRUCT(AVVDPAUContext);
    SHOW_STRUCT(AVDXVA2DeviceContext); SHOW_STRUCT(AVDXVA2FramesContext); SHOW_STRUCT(struct dxva_context);
    SHOW_STRUCT(AVAMFDeviceContext); SHOW_STRUCT(AVOHCodecDeviceContext);
    SHOW_STRUCT(AVIOContext); SHOW_FIELD(AVIOContext, checksum); SHOW_FIELD(AVIOContext, checksum_ptr);
    SHOW_STRUCT(AVIOContext_Win64_LLP64); SHOW_FIELD(AVIOContext_Win64_LLP64, checksum);
    SHOW_FIELD(AVIOContext_Win64_LLP64, checksum_ptr);
    printf("VA_LIST sysv=%zu ms=%zu | ENUM pixfmt_signed=%d hwdev_signed=%d\n",
           sizeof(__builtin_sysv_va_list), sizeof(__builtin_ms_va_list),
           (int)((enum AVPixelFormat)-1 < 0), (int)((enum AVHWDeviceType)-1 < 0));
    return 0;
}
```

Recorded verbatim probe summary lines:
```text
STRUCT AVHWDeviceContext            sizeof= 40 alignof= 8  (av_class@0, type@8, hwctx@16, free@24, user_opaque@32)
STRUCT AVHWFramesContext            sizeof= 80 alignof= 8  (av_class@0..pool@48, initial_pool_size@56, format@60, sw_format@64, width@68, height@72)
STRUCT AVDRMObjectDescriptor        sizeof= 24 alignof= 8  (fd@0, size@8, format_modifier@16)
STRUCT AVDRMPlaneDescriptor         sizeof= 24 alignof= 8  (object_index@0, offset@8, pitch@16)
STRUCT AVDRMLayerDescriptor         sizeof=104 alignof= 8  (format@0, nb_planes@4, planes@8[96])
STRUCT AVDRMFrameDescriptor         sizeof=528 alignof= 8  (nb_objects@0, objects@8[96], nb_layers@104, layers@112[416])
STRUCT AVDRMDeviceContext           sizeof=  4 alignof= 4  (fd@0)
STRUCT AVVTFramesContext            sizeof=  4 alignof= 4  (color_range@0)
STRUCT AVVideotoolboxContext        sizeof= 32 alignof= 8  (session@0, cv_pix_fmt_type@8, cm_fmt_desc@16, cm_codec_type@24)
STRUCT AVMediaCodecDeviceContext    sizeof= 24 alignof= 8  (surface@0, native_window@8, create_window@16)
STRUCT AVMediaCodecContext          sizeof=  8 alignof= 8  (surface@0)
STRUCT AVQSVDeviceContext           sizeof= 16 alignof= 8  (session@0, loader@8)
STRUCT AVQSVFramesContext           sizeof= 24 alignof= 8  (surfaces@0, nb_surfaces@8, frame_type@12, info@16)
STRUCT AVQSVContext                 sizeof= 56 alignof= 8  (session@0, iopattern@8, ext_buffers@16, nb_ext_buffers@24, opaque_alloc@28, nb_opaque_surfaces@32, opaque_surfaces@40, opaque_alloc_type@48)
STRUCT AVOpenCLFrameDescriptor      sizeof= 72 alignof= 8  (nb_planes@0, planes@8[64])
STRUCT AVOpenCLDeviceContext        sizeof= 24 alignof= 8  (device_id@0, context@8, command_queue@16)
STRUCT AVOpenCLFramesContext        sizeof=  8 alignof= 8  (command_queue@0)
STRUCT AVVDPAUDeviceContext         sizeof= 16 alignof= 8  (device@0[4], get_proc_address@8)
STRUCT AVVDPAUContext               sizeof= 24 alignof= 8  (decoder@0[4], render@8, render2@16)
STRUCT AVDXVA2DeviceContext         sizeof=  8 alignof= 8  (devmgr@0)
STRUCT AVDXVA2FramesContext         sizeof= 32 alignof= 8  (surface_type@0[4], surfaces@8, nb_surfaces@16[4], decoder_to_release@24)
STRUCT struct dxva_context          sizeof= 48 alignof= 8  (decoder@0, cfg@8, surface_count@16[4], surface@24, workaround@32, report_id@40[4])
STRUCT AVAMFDeviceContext           sizeof= 72 alignof= 8  (library@0, factory@8, trace_writer@16, version@24, context@32, memory_type@40[4], lock@48, unlock@56, lock_ctx@64)
STRUCT AVOHCodecDeviceContext       sizeof=  8 alignof= 8  (native_window@0)
STRUCT AVIOContext                  sizeof=208 alignof= 8  (min_packet_size@96, checksum@104[8], checksum_ptr@112, update_checksum@120, bytes_written@200)
STRUCT AVIOContext_Win64_LLP64      sizeof=200 alignof= 8  (min_packet_size@96, checksum@100[4], checksum_ptr@104, update_checksum@112, bytes_written@192)
VA_LIST sizeof(__builtin_sysv_va_list)=24 alignof=8 | sizeof(__builtin_ms_va_list)=8 alignof=8
ENUM signedness: AVPixelFormat(<0? 1, sizeof=4), AVHWDeviceType(<0? 0, sizeof=4)
```

## Revalidation

To revalidate these findings cheaply when targeting a newer FFmpeg revision, OS SDK, or Rust `cdylib` build:

1. **FFmpeg Header & Major-Version Drift Check (< 5 seconds):**
   - Diff `libav*/version_major.h`, `libavutil/version.h`, `libavutil/hwcontext*.h`, `libavcodec/{videotoolbox,mediacodec,qsv,vdpau,dxva2}.h`, `libavformat/avio.h`, `configure` (`darwin)` and `win32|win64)` stanzas), and `compat/windows/makedef` between `7ddf7bc8a482cf28b4fab2e63b7093ba35cb6a80` and the target FFmpeg commit, then rerun `layout_probe.c` under both native C11 and `-mms-bitfields` (plus `cl.exe` / `clang-cl --target=x86_64-pc-windows-msvc` and `clang --target=arm64-apple-macos13` in CI) and assert zero `offsetof`/`sizeof` diff against Rust `core::mem::{size_of, align_of, offset_of!}` const assertions.
   - Re-scan all public headers for newly introduced bare `long` fields (`grep -rnE '\blong\b' libav*/ | grep -v 'long long'`).

2. **Windows & macOS Shared-Memory Read-Only Enforcement Negative Tests (< 1 second in CI):**
   - **Windows CI:** Duplicate a host `PAGE_READWRITE` section handle with `SECTION_MAP_READ | SECTION_QUERY` and assert in a test child process that (a) `DuplicateHandle(hSelf, hRO, hSelf, &hTmp, FILE_MAP_WRITE, FALSE, 0) == FALSE` (`ERROR_ACCESS_DENIED`), (b) `MapViewOfFile(hRO, FILE_MAP_WRITE, 0, 0, 0) == NULL`, and (c) `VirtualProtect(roView, 4096, PAGE_READWRITE, &old) == FALSE`, while host writes to `rwView` become immediately visible through `roView`.
   - **macOS CI:** Export a `16 KiB`-aligned `mach_vm_allocate` ring via `mach_make_memory_entry_64(..., MAP_MEM_VM_SHARE | VM_PROT_READ, &ro_port, MACH_PORT_NULL)` and assert in an XPC/child process that (a) `mach_vm_map(..., ro_port, ..., VM_PROT_READ | VM_PROT_WRITE, ...) == KERN_INVALID_RIGHT`, (b) `mach_vm_protect(..., ro_va, 16384, FALSE, VM_PROT_READ | VM_PROT_WRITE) == KERN_PROTECTION_FAILURE`, and (c) live stores to the host's writable mapping appear immediately at `ro_va` without COW detachment.

3. **Drop-In `cdylib` Binary Artifact Inspection (< 2 seconds):**
   - **Windows PE:** Run `llvm-readobj --coff-exports avcodec-63.dll` to verify unmangled C symbol names, absence of `avpriv_*` leaks, `IMAGE_DLLCHARACTERISTICS_HIGH_ENTROPY_VA | DYNAMIC_BASE | NX_COMPAT`, and non-empty `.pdata`/`.xdata` unwind directories (`llvm-readobj --unwind avcodec-63.dll`).
   - **macOS Mach-O:** Run `otool -L -l libavcodec.63.dylib` and `xcrun dyld_info -exports -unwind libavcodec.63.dylib` (or `llvm-objdump --macho --unwind-info --exports-trie`) to verify `LC_ID_DYLIB` (`@rpath/libavcodec.63.dylib`, `compatibility version 63.0.0`), `MH_TWOLEVEL`, `CS_RUNTIME` code-signature flags (`codesign -dvvv`), `<= 3` personalities in `__TEXT,__unwind_info`, and `__TEXT,__eh_frame` size `< 16 MiB`.
