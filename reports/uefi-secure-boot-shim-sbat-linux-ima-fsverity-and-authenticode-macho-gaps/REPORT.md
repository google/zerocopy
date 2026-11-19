# UEFI Secure Boot, SBAT Generation Revocation, Linux IMA/fs-verity/dm-verity, PE Authenticode Exclusions, and Mach-O Code Signing & Thread-Local W^X

## Summary

Operating-system boot chains and runtime executable verifiers enforce cryptographic integrity along two axes: **(1) verification timing** (whole-file load-time hashing vs. lazy page-fault Merkle/slot verification) and **(2) format-coverage strictness** (whether the container parser can admit unhashed slack bytes, mutable backing files, or writable-and-executable pages). Examining primary implementations across UEFI firmware (`tianocore/edk2`, `rhboot/shim`), Linux (`kernel/module`, `IMA`/`EVM`, `fs-verity`, `dm-verity`), Windows Authenticode/HVCI/WDAC, and Apple Darwin (`xnu`, `libpthread`) establishes four foundational architectural invariants:

1. **Image-Hash Revocation Exhausts NVRAM; Metadata Generation Revocation Compresses Revocation State:** Blocking a single vulnerability across many vendor-signed boot binaries via SHA-256 `dbx` entries consumes scarce motherboard NVRAM (`BootHole` consumed ~10 KiB of typical 32 KiB NVRAM). `rhboot/shim` **SBAT** (Secure Boot Advanced Targeting) replaces per-binary hashes with compact monotonic `(component, generation)` pairs stored in `.sbat` PE sections and the `SbatLevel` UEFI variable—yet revocation of older signed binaries (as seen in `BlackLotus` `CVE-2022-21894` / `CVE-2023-24932`) still fails unless `dbx`/`SbatLevel` updates are actively applied and bound into TPM `PCR[7]`.
2. **Whole-File Load Checks vs. Immutable Page-Fault Verification:** Whole-file PKCS#7 checks (`kernel/module/signing.c`) and traditional `IMA` `open`/`mmap`/`exec` appraisal assume the backing file cannot mutate post-verification (`S_VERITY` vs. mutable filesystems) and stall execution until the entire binary is hashed. By contrast, Linux `fs-verity` (`fs/verity/verify.c`), block-layer `dm-verity` with Reed-Solomon FEC (`drivers/md/dm-verity-fec.c`), and Mach-O `LC_CODE_SIGNATURE` (`ubc_subr.c`) verify $4\text{ KiB}$/$16\text{ KiB}$ pages lazily on page-in, caching verified interior Merkle blocks (`fs-verity`) or enforcing immediate process termination (`CS_KILL`) on mismatch (`XNU`). Critically, `dm-verity` FEC error correction executes strictly *before* cryptographic Merkle verification (`-EILSEQ` on hash mismatch) so repair never admits unauthenticated blocks.
3. **PE Authenticode Excludes Specific Byte Ranges—Strict Parsers Must Bound Slack and Section Gaps:** Both `edk2`'s `HashPeImage()` (`DxeImageVerificationLib.c:292-606`) and Windows Authenticode exclude `OptionalHeader.CheckSum` (4 bytes), `DataDirectory[SECURITY]` (8 bytes), and the `WIN_CERTIFICATE` region (`[FileSize - CertSize, FileSize)`). Unless `CertSize` strictly matches the 8-byte-aligned PKCS#7 ASN.1 DER length (`EnableCertPaddingCheck`, `CVE-2013-3900`) and sections are contiguous without file-offset gaps (which shift `SumOfBytesHashed` in Step 16), unhashed bytes persist inside signed binaries.
4. **Hardware Page-Level `W^X` Requires Eliminating Shared `RWX` Windows:** Windows HVCI (VTL1 hypervisor EPT/SLAT enforcement) and Apple Silicon `MAP_JIT` + `pthread_jit_write_protect_np()` (`APRR` thread-local `RW-`/`R-X` toggles) decouple writable JIT emission from cross-thread executable injection, while Apple's `libpthread` locks JIT write transitions behind an immutable `VM_FLAGS_PERMANENT` callback allowlist frozen with `mach_vm_protect(..., set_maximum=true, VM_PROT_READ)`.

## Applicability

Findings in this report apply to the following pinned specifications and upstream trees observed on `2026-11-19`:

- **UEFI Secure Boot & `shim`:** `UEFI Specification` v2.10, `tianocore/edk2` (`SecurityPkg/Library/DxeImageVerificationLib/DxeImageVerificationLib.c` at `556dcfb466e9f05affeaff881d738807f8156d3c`), and `rhboot/shim` (`SBAT.md`, `sbat.c`, `SbatLevel_Variable.txt`, `pe.c` at `e794a714339b1277abe9f890fc98de6e415681b0`). Applies to UEFI firmware image verification and two-stage Linux shim bootloaders (`MokList`/`SBAT`), with differences noted between `edk2` and `shim`'s stricter `pe.c` checks.
- **Linux Kernel Integrity Mechanisms:** `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) across `kernel/module/signing.c`, `security/integrity/ima/ima_appraise.c`, `security/integrity/evm/evm_main.c`, `fs/verity/verify.c`, `include/uapi/linux/fsverity.h`, and `drivers/md/dm-verity-fec.c`. Applicability distinguishes kernel modules, mutable VFS xattr appraisal (`IMA`/`EVM`), immutable per-file Merkle trees (`fs-verity`), and block-device read-only Merkle trees (`dm-verity`).
- **Windows PE Authenticode / HVCI / WDAC:** Derived from the normative PE/COFF Authenticode hashing algorithm (verified directly in `edk2` `HashPeImage` source) and Microsoft security documentation for `CVE-2013-3900` (`EnableCertPaddingCheck`), `BlackLotus` (`CVE-2022-21894` / `CVE-2023-24932`), HVCI, and WDAC. Windows kernel (`ci.dll`) closed-source binary internals were not disassembled.
- **macOS / iOS Darwin Code Signing & JIT Enforcement:** `apple-oss-distributions/xnu` (`osfmk/kern/cs_blobs.h`, `bsd/kern/ubc_subr.c`, `osfmk/vm/vm_map.c` at `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`), `apple-oss-distributions/libpthread` (`src/pthread.c` at `42d026df5b07825070f60134b980a1ec2552dfee`), and `apple-oss-distributions/Security` (`db15acbe6a7f257a859ad9a3bb86097bfe0679d9`). Explicit `XNU_TARGET_OS_OSX` vs. embedded iOS distinctions in `vm_map.c` and `libpthread` are preserved.

## Findings

### 1. Cross-Platform Code-Signing, Page-Measurement, and `W^X` Enforcement Matrix

Basis: normative + source + derived

Every code-verification boundary trades off **startup latency**, **mutable-backing-store vulnerability**, **revocation state growth**, and **runtime `W^X` guarantees**:

| Mechanism | Container & Hash Tree / Signature Format | Verification Timing | Backing Store Mutability Defense | Revocation Primitive & State Scaling | Runtime `W^X` / Code-Page Invariant |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **UEFI Secure Boot (`edk2`)** | PE/COFF + Authenticode `WIN_CERTIFICATE` (PKCS#7) | Load-time (`LoadImage`, whole PE buffer in RAM) | In-memory copy prior to relocations/execution | `dbx` SHA-256 hashes or X.509 certs in NVRAM (scales poorly: $O(\text{binaries})$) | Firmware `EFI_MEMORY_ATTRIBUTES_TABLE` RO/XP (optional on older FW) |
| **`rhboot/shim` + `SBAT`** | PE/COFF + `.sbat` CSV section + `MokList` / `SbatLevel` | Load-time (shim verifies 2nd stage before executing) | In-memory PE buffer copied prior to verify | `SbatLevel` (`component,gen` tuples: $O(\text{component families})$) + `MokListX` | Enforces section alignment & memory attributes where supported |
| **Linux Module Signing** | ELF + trailing `module_signature` PKCS#7 + magic marker | `init_module` / `finit_module` load-time | `kernel_read_file` buffer in kernel RAM | Kernel `.blacklist` keyring / cert revocation | Module `.text` `RO+X`, `.rodata` `RO+NX` via `module_enable_ro` |
| **Linux `IMA` / `EVM`** | `security.ima` (hash or RSA/ECDSA sig) + `security.evm` HMAC/sig | `open` / `mmap` / `bprm_check` whole-file measurement | Relies on `i_version` cache invalidation; vulnerable if offline disk mutates without `EVM` | Kernel `.ima` / `.blacklist` keyrings; no built-in version counter | Enforces file integrity at load; does not lock anonymous JIT `mmap` |
| **Linux `fs-verity`** | Per-inode post-EOF $128$-ary Merkle tree + `fsverity_descriptor` | **Lazy per-block** (`4 KiB` bio/folio page-in) | Kernel flips inode to **immutable** `S_VERITY` (`FS_IOC_ENABLE_VERITY`) | Built-in PKCS#7 `"FSVerity"` keyring or userspace policy (e.g., IMA) | Read-only file (`EROFS`/`EACCES` on write open); verified at page fault |
| **Linux `dm-verity` + `FEC`** | Block-device Merkle tree + interleaved Reed-Solomon `FEC` parity | **Lazy per-block** (`4 KiB` block bio read) | Read-only block target; unverified writes impossible through mapper | Entire root hash pinned by signed kernel cmdline / `initramfs` | Guarantees block authenticity; FEC decode verified by hash before return |
| **Windows Authenticode + HVCI/WDAC** | PE/COFF + `WIN_CERTIFICATE` + Catalog `.cat` | Load-time (`ci.dll`) + **HVCI** dynamic page check | `EnableCertPaddingCheck` eliminates trailing PKCS#7 slack (`CVE-2013-3900`) | Microsoft Vulnerable Driver Blocklist, WDAC policy, `dbx`, `SbatLevel` | **HVCI**: VTL1 hypervisor intercepts SLAT/EPT page transitions; enforces strict `W^X` |
| **macOS / iOS `LC_CODE_SIGNATURE` + `MAP_JIT`** | Mach-O `CS_SuperBlob` + `CS_CodeDirectory` page slots + CMS + DER entitlements | Header/entitlements at `execve`; **code pages lazily** on page fault | Page re-hashed on every page-in (`cs_validate_page`); `CS_KILL` on tamper | `AMFI` trust cache / OCSP / notarization revocation / CDHash blocklist | Apple Silicon `MAP_JIT`: hardware `APRR` thread-local `RW-`/`R-X` + frozen callback allowlist |

---

### 2. UEFI Secure Boot (`PK`/`KEK`/`db`/`dbx`), `rhboot/shim`, and `SBAT` Revocation

Basis: normative + source + documentation

#### UEFI Authenticated Variable Trust Hierarchy (UEFI 2.10 §32)

UEFI Secure Boot establishes a four-variable trust hierarchy stored in authenticated non-volatile storage (`EFI_VARIABLE_TIME_BASED_AUTHENTICATED_WRITE_ACCESS`):
- **`PK` (Platform Key):** Single root key controlling updates to `PK` itself and `KEK` (or clearing `PK` to enter Setup Mode).
- **`KEK` (Key Exchange Keys):** Keys authorized to append or update `db` (Signature Database of allowed certificates/Authenticode hashes) and `dbx` (Forbidden Signature Database).
- **`db` vs. `dbx` Precedence:** During `LoadImage()`, `DxeImageVerificationHandler()` in `tianocore/edk2` checks `dbx` **before** admitting any match in `db`. If either the image's Authenticode digest (`HashPeImage`) or any certificate in the signer chain matches `dbx` (unless timestamped strictly before a `TimeOfRevocation`), execution fails with `EFI_ACCESS_DENIED`.

#### Why `BootHole` Broke Image-Hash `dbx` Scaling and Motivated `rhboot/shim` `SBAT`

As documented in `rhboot/shim/SBAT.md:21-35` (`e794a714339b1277abe9f890fc98de6e415681b0`), third-party UEFI CAs (specifically the Microsoft UEFI CA) sign shims and firmware utilities for dozens of Linux distributions and OEMs. Revoking a signing CA certificate in `dbx` bricks unrelated bootloaders and Option ROMs, forcing revocations onto individual PE Authenticode SHA-256 hashes. During the `BootHole` GRUB2 parser vulnerability (`CVE-2020-10713`), revoking 3 certificates and 150 image hashes consumed **~10 KiB of the typical 32 KiB** UEFI NVRAM variable budget (`SBAT.md:23-26`), bringing cumulative `dbx` usage to ~15 KiB (~50% capacity).

`rhboot/shim` resolves this $O(\text{distros} \times \text{versions})$ state explosion via **SBAT**:
1. **`.sbat` PE Section (`sbat.c:18-122`):** Every downstream EFI binary (`shim`, `grub`, `fwupd-efi`) embeds a read-only CSV `.sbat` section covered by the PE Authenticode signature with 6 mandatory columns (`component_name`, `component_generation`, `vendor_name`, `vendor_package_name`, `vendor_version`, `vendor_url`). Note an important delegation edge case in `pe.c:489-496`: when `sbat_var` (`SbatLevel`) is populated, `.sbat` is **mandatory** for images loaded directly by `shim` (`EFI_SECURITY_VIOLATION` if absent), yet **optional** (`in_protocol ? EFI_SUCCESS : EFI_SECURITY_VIOLATION`) when third-party callers invoke the `SHIM_LOCK` protocol directly.
2. **Monotonic Generation Check (`sbat.c:134-158`):** `verify_single_entry()` matches `entry->component_name` against each entry in `SbatLevel` and rejects whenever `atoi(entry->component_generation) < atoi(sbat_var_entry->component_generation)` (`EFI_SECURITY_VIOLATION`). Because failed `atoi()` conversions evaluate to `0`, malformed generation fields fail closed against any positive `SbatLevel >= 1`.
3. **Self-Revocation Guard & Ratcheting (`sbat.c:501-615`, `SbatLevel_Variable.txt:14-156`):** `shim` carries two compiled-in revocation payloads (`sbat_var_automatic` and opt-in `sbat_var_latest`, stored in `SbatLevel` under vendor GUID `605dab50-e046-4300-abb6-3dd810dd8b23` with attributes `NV | BS`, *not* runtime-writable from the OS!). Before deleting and rewriting `SbatLevel`, `set_sbat_uefi_variable()` calls `verify_sbat_section()` on `shim`'s own `&_sbat..&_esbat` section (`sbat.c:562-571`), refusing to apply a policy that would self-revoke the currently running `shim`. `SbatLevel_Variable.txt` tracks monotonic global floors from `sbat,1,2021030218` up through `sbat,1,2026102600` (`shim,4`, `grub,7`, `fwupd-efi,2`).

#### Rollback & `TPM PCR[7]` Lessons from `BlackLotus` (`CVE-2022-21894` / `CVE-2023-24932`)

`BlackLotus` demonstrated a fundamental architectural hazard of asymmetric signing without hardware anti-rollback counters: **patching the OS bootloader does not neutralize older, still-valid Microsoft-signed bootloaders (`bootmgr`) brought alongside an attacker payload.** Until the pre-fix binary digests or `SbatLevel` entries are persisted into `dbx`/`SbatLevel` NVRAM, an adversary with local admin or physical ESP write access can downgrade the bootloader on disk to bypass Secure Boot. Furthermore, because **TPM `PCR[7]`** measures the active Secure Boot policy state (`PK`, `KEK`, `db`, `dbx` contents and signer certificates used during boot), pushing `dbx` revocations alters `PCR[7]`—requiring coordinated BitLocker/LUKS key protector re-sealing (`TPM2_PolicyPCR`) so security updates neither leave downgrade windows open nor lock out disk decryption.

---

### 3. Linux Kernel Module Signing, IMA/EVM Appraisal, `fs-verity`, and `dm-verity` FEC

Basis: source + normative

#### Loadable Kernel Module PKCS#7 Signing (`kernel/module/signing.c`)

In `torvalds/linux/kernel/module/signing.c:43-125` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):
- `module_sig_check()` inspects the final bytes of the module buffer for `MODULE_SIGNATURE_MARKER` (`"~Module signature appended~\n"`). Critically, lines `76-84` set `mangled_module = flags & (MODULE_INIT_IGNORE_MODVERSIONS | MODULE_INIT_IGNORE_VERMAGIC)` and refuse signature acceptance if either flag is set, because stripping `modversions`/`vermagic` alters module ABI behavior without matching the signed payload.
- `mod_verify_sig()` reads the fixed `struct module_signature` footer, truncates `info->len` by `sig_len + sizeof(ms)`, and invokes `verify_pkcs7_signature(..., VERIFY_USE_SECONDARY_KEYRING, VERIFYING_MODULE_SIGNATURE, NULL, NULL)`.
- **Silent Failure Hazard When `sig_enforce == false` (`signing.c:99-124`):** Unsigned (`-ENODATA`), missing-key (`-ENOKEY`), or unsupported-crypto (`-ENOPKG`) modules fall through to `security_locked_down(LOCKDOWN_MODULE_SIGNATURE)`, allowing loading unless `CONFIG_MODULE_SIG_FORCE`, `module.sig_enforce=1`, or kernel lockdown (e.g., Secure Boot active) forbids it. However, *corrupted/malformed* signatures (`default:` branch, line `116`) fail unconditionally even when `sig_enforce` is false.

#### Whole-File `IMA`/`EVM` Appraisal vs. `fs-verity` Lazy Merkle Verification

`security/integrity/ima/ima_appraise.c:462-599` and `security/integrity/evm/evm_main.c:38-159` illustrate the structural limits of mutable-filesystem appraisal:
- **`IMA` Appraisal (`ima_appraise_measurement`):** Evaluates `security.ima` (either a hash `IMA_XATTR_DIGEST_NG` or asymmetric signature `EVM_IMA_XATTR_DIGSIG`, or an appended `modsig`) when a file is opened/executed/mmapped. Because traditional files remain writable on disk, `IMA` must re-hash the *entire file* whenever `i_version` changes or `iint` cache invalidates, creating $O(\text{file size})$ latency at launch and risking `TOCTOU` races on filesystems lacking reliable change tracking (`SB_I_IMA_UNVERIFIABLE_SIGNATURE` + `SB_I_UNTRUSTED_MOUNTER`, `ima_appraise.c:561-567`).
- **`EVM` Metadata Binding (`evm_main.c:38-114`):** Protects `security.ima`, `security.selinux`, `security.smack*`, `security.apparmor`, `security.capability`, and inode metadata (`i_uid`, `i_gid`, `i_mode`, optional `FSUUID`) via `security.evm` HMAC (local symmetric TPM/kernel key) or portable `EVM` signature (`INTEGRITY_PASS_IMMUTABLE`), preventing offline xattr transplant attacks.
- **`fs-verity` Immutable Lazy Page-Fault Verification (`fs/verity/verify.c:159-470`, `include/uapi/linux/fsverity.h:47-84`):**
  1. Calling `FS_IOC_ENABLE_VERITY` freezes the file as **read-only (`S_VERITY`)**, constructs a hidden post-EOF Merkle tree (with configurable block size—typically `4096` bytes, yielding $4096/32 = 128$-ary fanout for SHA-256—plus optional `salt`), and hashes `struct fsverity_descriptor` (`version=1`, `hash_algorithm`, `log_blocksize`, `salt_size`, `data_size`, `root_hash`, `salt`) to produce the single **fs-verity file digest**.
  2. When signed in-kernel, `struct fsverity_formatted_digest` (`fsverity.h:79-84`) prepends the 8-byte domain-separation magic `"FSVerity"` + `__le16 digest_algorithm` + `__le16 digest_size` so a signature over an `fs-verity` digest cannot be confused with raw file signatures.
  3. On every read/page-fault (`fsverity_verify_blocks` / `fsverity_verify_bio`), `verify_data_block()` (`verify.c:159-325`) hashes the `4 KiB` data block (using `sha256_finup_2x` SIMD batching when available) and walks upward through `level = 0 .. num_levels - 1`. At each level, if `is_hash_block_verified(vi, hpage, hblock_idx)` is already true (`verify.c:259-268`), traversal short-circuits immediately (`goto descend`); otherwise, it descends from `vi->root_hash` (or the verified upper block), checks `memcmp(want_hash, real_hash, hsize) == 0`, and atomically caches the block via `set_bit(hblock_idx, vi->hash_block_verified)`. Any non-zero byte past `inode->i_size` on an EOF-straddling page triggers corruption (`memchr_inv`, `verify.c:206-213`).
  4. **Composition with `IMA` (`ima_appraise.c:497`):** `IMA_VERITY_REQUIRED` allows `IMA` to appraise *only* the compact `fs-verity` file digest at `open`/`exec` while delegating $O(\log_{128} N)$ incremental block enforcement to `fs-verity` page faults.

#### `dm-verity` Forward Error Correction Ordering (`drivers/md/dm-verity-fec.c`)

At the block-device layer, `dm-verity` applies the same read-only Merkle tree model to entire partitions (`squashfs` / `erofs` system images). When optional Reed-Solomon Forward Error Correction (`FEC`) is enabled to tolerate flash bit-rot, `fec_decode()` (`drivers/md/dm-verity-fec.c:320-369`) enforces a strict cryptographic invariant: Reed-Solomon erasure/error decoding reconstructs candidate bytes in `fio->output`, and **must unconditionally re-hash `fio->output` via `verity_hash()` and verify `memcmp(io->tmp_digest, want_digest, v->digest_size) == 0`** (`fec.c:359-367`), returning `-EILSEQ` on mismatch. As the kernel source explicitly notes (`fec.c:320`), this ordering ensures noisy or adversarially crafted parity blocks can never trick `dm-verity` into surfacing unauthenticated blocks.

---

### 4. PE Authenticode Exclusion Zones, Certificate Padding (`CVE-2013-3900`), and HVCI/WDAC

Basis: source + normative + execution + documentation

#### Exact Byte-Interval Coverage of `HashPeImage()` (`edk2` `DxeImageVerificationLib.c`)

Line-by-line inspection of `HashPeImage()` in `tianocore/edk2/SecurityPkg/Library/DxeImageVerificationLib/DxeImageVerificationLib.c:292-606` (`556dcfb466e9f05affeaff881d738807f8156d3c`) reconstructs the exact PE/COFF Authenticode coverage partition over `[0, mImageSize)`:

1. **Header Prefix (`lines 375-400`):** Hashes `[0, offset(OptionalHeader.CheckSum))`. **Excludes** the 4-byte `CheckSum` field.
2. **Post-Checksum Header (`lines 430-478`):** Hashes `[offset(CheckSum) + 4, offset(DataDirectory[SECURITY]))`, skips the 8-byte `DataDirectory[EFI_IMAGE_DIRECTORY_ENTRY_SECURITY]` (`VirtualAddress`, `Size`), and hashes `[offset(DataDirectory[SECURITY]) + 8, SizeOfHeaders)`. Initializes `SumOfBytesHashed = SizeOfHeaders`.
3. **Section Table Walk (`lines 521-554`):** Insertion-sorts section headers by `PointerToRawData` ascending, hashes `[Section->PointerToRawData, Section->PointerToRawData + Section->SizeOfRawData)` for each non-zero section, and adds `Section->SizeOfRawData` to `SumOfBytesHashed`.
4. **Tail Hashing (`lines 562-592`):** If `mImageSize > SumOfBytesHashed`, obtains `CertSize = DataDirectory[SECURITY].Size`. If `mImageSize > CertSize + SumOfBytesHashed`, hashes `mImageSize - CertSize - SumOfBytesHashed` bytes starting at `mImageBase + SumOfBytesHashed`.

#### Two Structural Format Bypasses and Their Strict Defensive Invariants

This algorithm exposes two structural ambiguities whenever parsers accept non-minimal PE containers:

1. **Certificate Slack / Trailing Padding (`CVE-2013-3900`):** Because Step 16 subtracts the *declared* `CertSize = DataDirectory[SECURITY].Size` from the end of the file, the entire interval `[FileSize - CertSize, FileSize)` is omitted from the Authenticode digest. Inside that region sits a `WIN_CERTIFICATE` header (8 bytes: `dwLength`, `wRevision`, `wCertificateType`) followed by an ASN.1 DER PKCS#7 `SignedData` payload. When `WIN_CERTIFICATE.dwLength` (and `CertSize`) exceeds `align8(8 + asn1_der_total_len)`, the trailing `slack = CertSize - align8(8 + asn1_der_total_len)` bytes are **never hashed by Authenticode** and **ignored by loose PKCS#7 parsers** that stop after reading the outer ASN.1 `SEQUENCE` length.
   - *Defensive Fix:* Enforcing Windows `EnableCertPaddingCheck = 1` (`HKLM\SOFTWARE\Microsoft\Cryptography\Wintrust\Config`) requires strict length equality (`CertSize == align8(8 + asn1_der_total_len)` with zero trailing non-padding bytes). Note also `edk2` `HashPeImageByType` (`DxeImageVerificationLib.c:645-660`), which hardcodes a two-byte long-form DER length check and fixed offset `+32` OID lookup—rejecting unusual ASN.1 length encodings with `EFI_BAD_BUFFER_SIZE`.
2. **Section-Gap `SumOfBytesHashed` Offset Drift:** As confirmed by comparing `edk2` (`DxeImageVerificationLib.c:562-584`) against `rhboot/shim` (`pe.c:395-408`), `SumOfBytesHashed` sums *only* `SizeOfHeaders + sum(Section.SizeOfRawData)`. If a PE contains an unaligned file gap `[SizeOfHeaders, Section[0].PointerToRawData)` (or a gap between consecutive sections), `SumOfBytesHashed` advances *less* than the physical file cursor of the last section's end! Consequently, Step 16 (`HashBase = mImageBase + SumOfBytesHashed`) **re-hashes trailing bytes of the last section while silently skipping bytes immediately preceding `WIN_CERTIFICATE`**, whereas `shim/pe.c:400` explicitly blocks this via `SumOfBytesHashed + hashsize != context->SecDir->VirtualAddress`.

#### Windows `HVCI` and `WDAC` Defense-in-Depth

Because file-level Authenticode alone cannot protect mutable runtime memory or signed-yet-vulnerable drivers (`BYOVD`), Windows pairs strict `EnableCertPaddingCheck` and **WDAC** (Windows Defender Application Control allowlists + Microsoft Vulnerable Driver Blocklist) with **HVCI** (Hypervisor-Protected Code Integrity):
- Under HVCI (`VTL1` Secure Kernel + Hyper-V EPT/SLAT), kernel-mode `VTL0` pages can never transition to executable (`X`) unless `VTL1` validates their signature and page hashes and marks the EPT permissions strictly `R-X` (non-writable), preventing `VTL0` kernel arbitrary-write primitives from mutating executable pages or disabling `ci!g_CiOptions`.

---

### 5. macOS / iOS Mach-O `LC_CODE_SIGNATURE`, AMFI/Notarization, `CS_KILL`, and `MAP_JIT` Thread-Local `W^X`

Basis: source + documentation + execution

#### `CS_SuperBlob`, `CS_CodeDirectory`, Negative Special Slots, and Lazy Page Validation (`XNU`)

In `apple-oss-distributions/xnu` (`osfmk/kern/cs_blobs.h:36-170` and `bsd/kern/ubc_subr.c:5820-6112`, commit `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`):
- The `LC_CODE_SIGNATURE` load command points to a `CS_SuperBlob` (`CSMAGIC_EMBEDDED_SIGNATURE = 0xfade0cc0`) indexing typed sub-blobs:
  - `CSSLOT_CODEDIRECTORY` (`0`, `CSMAGIC_CODEDIRECTORY = 0xfade0c02`): The core hash directory whose own digest (`CDHash`) uniquely identifies the signed binary for AMFI, trust caches, and notarization tickets.
  - **Negative Special Slots (`-1` through `-nSpecialSlots`):** Stored immediately *before* the `hashOffset` base of page hashes in `CS_CodeDirectory`, pinning Mach-O metadata: `CSSLOT_INFOSLOT` (`1`, i.e., `-1` `Info.plist`), `CSSLOT_REQUIREMENTS` (`2` / `-2`), `CSSLOT_RESOURCEDIR` (`3` / `-3`), `CSSLOT_ENTITLEMENTS` (`5` / `-5`, XML `0xfade7171`), and `CSSLOT_DER_ENTITLEMENTS` (`7` / `-7`, DER `0xfade7172`), plus `CSMAGIC_EMBEDDED_LAUNCH_CONSTRAINT` (`0xfade8181`) on modern releases.
  - **Positive Page-Hash Slots (`0 .. nCodeSlots - 1`):** Each slot stores the cryptographic digest (typically SHA-256) of a `4 KiB` (or `16 KiB` / multi-level) slice up to `codeLimit`.
  - `CSMAGIC_BLOBWRAPPER` (`0xfade0b01`): CMS/PKCS#7 signature signing `CS_CodeDirectory` (plus an optional stapled notarization ticket blob on macOS so offline Gatekeeper/AMFI verification succeeds without querying Apple servers).
- **Lazy Page-Fault Validation & `CS_KILL` Semantics (`ubc_subr.c:5820-6112`, `cs_blobs.h:36-65`):** Rather than hashing a 200 MiB executable synchronously at `execve`, `XNU` hashes only the `CS_CodeDirectory`, entitlements, and CMS wrapper at load time, then invokes `cs_validate_page()` / `cs_validate_range()` in the pager on page-in.
  - If a page fails digest comparison (`bcmp != 0`, `ubc_subr.c:5906-5919`), `cs_validate_page` sets `CS_VALIDATE_TAINTED`. Under legacy unsigned/adhoc policies without `CS_HARD`/`CS_KILL`, the kernel merely cleared `CS_VALID` (`0x00000001`). When **`CS_HARD` (`0x00000100`)** and **`CS_KILL` (`0x00000200`)** are active (enforced via `CS_RUNTIME` Hardened Runtime / AMFI / iOS mandatory flags), `XNU` refuses to map the tampered page, marks `CS_KILLED` (`0x01000000`), and **immediately terminates the process with `SIGKILL`**—closing post-exec disk-swapping and dirty-page tamper windows.

#### `MAP_JIT`, Hardware `APRR` Thread-Local `W^X`, and Frozen Callback Allowlists (`libpthread`)

JIT compilers traditionally faced a fatal `W^X` dilemma on `CS_HARD | CS_KILL` systems: calling `mprotect(RW <-> RX)` across threads leaves brief `RWX` or global-`RW` race windows across multi-threaded processes. Apple Silicon addresses this via **hardware-enforced thread-local permissions (`APRR` / `SPRR`)** combined with two software layers:

1. **Kernel Single-Mapping Invariant (`xnu/osfmk/vm/vm_map.c:3029-3051`):** `mmap(..., MAP_JIT)` creates a private anonymous region (`VM_PROT_ALL` on `MAP_JIT` under Apple Silicon `APRR`, strictly rejecting non-`RWX` `MAP_JIT` on embedded OSes per `vm_map.c:3050`), while the hardware page-table permission register guarantees that **no single CPU thread simultaneously holds both Write and Execute permissions** on `MAP_JIT` pages.
2. **Thread-Local Toggle & Callback Allowlist Lockdown (`libpthread/src/pthread.c:1231-1475`):**
   - On standard macOS (`TARGET_OS_OSX`) without allowlist lockdown, `pthread_jit_write_protect_np(enable)` calls `os_thread_self_restrict_rwx_to_rx()` (`enable != 0`) or `os_thread_self_restrict_rwx_to_rw()` (`enable == 0`) (`pthread.c:1368-1379`), flipping *only the calling thread's* `APRR` register while peer threads executing JIT code stay `R-X`.
   - Under JIT allowlist lockdown (`_PTHREAD_CONFIG_JIT_LOCKDOWN_DEFAULT` or JIT-allowlist entitlement, `pthread.c:1236-1392`), calling `pthread_jit_write_protect_np()` directly **crashes the process** (`PTHREAD_CLIENT_CRASH`). Instead:
     - `_pthread_jit_write_protect_global_init()` (`pthread.c:1258-1271`) maps `_pthread_jit_config` with **`VM_FLAGS_PERMANENT`**;
     - `_pthread_jit_write_protect_bulk_image_load_callback()` (`pthread.c:1275-1326`) harvests function pointers solely from signed `__DATA_CONST,__pth_jit_func` sections (ignoring post-freeze `dlopen`s);
     - `_pthread_jit_write_protect_freeze_config()` (`pthread.c:1329-1342`) seals `_pthread_jit_config` with `mach_vm_protect(..., /* set_maximum */ true, VM_PROT_READ)` so even an attacker with memory-write primitives cannot alter the allowlist;
     - `pthread_jit_write_with_callback_np(callback, ctx)` (`pthread.c:1404-1449`) toggles `RW-`, verifies `config->allowlist_frozen` and `callback` membership (explicitly toggling *before* validating to thwart mid-function ROP jumps, `pthread.c:1412-1415`, and toggling back to `RX` before crashing on mismatch), executes `callback(ctx)`, and unconditionally restores `os_thread_self_restrict_rwx_to_rx()`.

---

### 6. Reproducible Verification Micro-Probe Results

Basis: execution

A Python 3 standard-library micro-probe executed on `2026-11-19` verified: (1) `HashPeImage()` interval partitioning on both a clean PE (`SumOfBytesHashed = 0x1c00`, excluding only `CheckSum`, `DataDirectory[SECURITY]`, and `[0x1c00, 0x2400)`) and a non-contiguous section-gap PE (`SizeOfHeaders = 0x400`, section at `[0x600, 0x1600)`, `FileSize = 0x1e00`, `CertSize = 0x800`), confirming that `SumOfBytesHashed = 0x1400` causes Step 16 to re-hash `[0x1400, 0x1600)` while leaving `[0x400, 0x600)` excluded; (2) strict `WIN_CERTIFICATE` padding verification (`slack == 0` vs. `slack == 256`); (3) `fs-verity` Merkle geometry for a 64 MiB binary (`4 KiB` blocks, 2 levels: `[128, 1]` hash blocks = `528,384` bytes); and (4) Mach-O `CS_CodeDirectory` slot indexing (`-7..-1` special slots, `0..24` code slots for `100 KiB` `codeLimit`):

```text
pe_clean sum=0x1c00 excluded=[('0x158', '0x15c'), ('0x1c8', '0x1d0'), ('0x1c00', '0x2400')] pad_ok=True(slack=0) pad_padded=False(slack=256)
pe_gap sum=0x1400 step16_hashed_window=(0x1400, 0x1600) excluded=[('0x158', '0x15c'), ('0x1c8', '0x1d0'), ('0x400', '0x600'), ('0x1600', '0x1e00')]
fsverity_64MiB levels=2 blocks_per_level_leaf_to_root=[128, 1] merkle_bytes=528384
macho_codedir={'n_special_slots': 7, 'special_slot_range': (-7, -1), 'n_code_slots': 25, 'code_slot_range': (0, 24)}
```

## Boundaries

- **Known not to apply:**
  - *`EnableCertPaddingCheck` default state on legacy/unconfigured Windows hosts:* Microsoft implemented strict `WIN_CERTIFICATE` padding validation (`CVE-2013-3900`) as an opt-in registry toggle (`EnableCertPaddingCheck = 1`) rather than unconditionally enabling it across all builds due to legacy third-party installer compatibility; hosts without that setting or strict WDAC policies remain exposed to trailing-slack manipulation inside `WIN_CERTIFICATE`.
  - *`rhboot/shim` SBAT coverage via `SHIM_LOCK` protocol:* Per `rhboot/shim/pe.c:489-497`, mandatory `.sbat` enforcement fails closed when `shim` directly boots a stage-2 PE image, **not** when external binaries query the `SHIM_LOCK` protocol (`in_protocol == true`), where missing `.sbat` sections still return `EFI_SUCCESS`.
  - *macOS vs. iOS `MAP_JIT` and Code-Signing Monitor parity:* Per `xnu/osfmk/vm/vm_map.c:3032-3058`, XNU on `XNU_TARGET_OS_OSX` continues to tolerate non-RWX legacy `MAP_JIT` mappings and does not enforce the hardware page-table code-signing monitor identically to embedded Apple platforms (`!XNU_TARGET_OS_OSX`), where non-RWX `MAP_JIT` is strictly rejected.
  - *Linux `module.sig_enforce` default behavior:* Per `kernel/module/signing.c:99-124`, unsigned or unknown-key modules are permitted whenever `is_module_sig_enforced()` is false and `security_locked_down(LOCKDOWN_MODULE_SIGNATURE)` returns `0`; only malformed/corrupted signatures fail unconditionally.
- **Not examined / Unknown / Unsupported:**
  - *Windows `ci.dll` / `SecureKernel` proprietary source:* Internal disassembly of Windows `ci.dll`, `VTL1` `skci.dll`, and Apple `AMFI.kext` closed-source kernel extensions was **not examined**; Windows HVCI/WDAC and AMFI behaviors are grounded in Microsoft/Apple specifications and open-source `edk2`/`xnu`/`libpthread` boundaries.
  - *Vendor-specific UEFI firmware deviations:* OEM-customized firmware forks of `DxeImageVerificationLib` beyond upstream `tianocore/edk2` (`556dcfb466e9f05affeaff881d738807f8156d3c`) were **not examined**.
  - *OS-level `pthread_jit_write_protect_np` fallback on pre-Apple-Silicon `x86_64` Macs:* Unsupported in hardware `APRR`; `os_thread_self_restrict_rwx_is_supported()` returns `false` and `pthread_jit_write_with_callback_np()` invokes `callback(ctx)` directly (`pthread.c:1408-1410`).

## Evidence

All primary repositories, specifications, and execution outputs were verified on `2026-11-19`:

- **UEFI & `shim` Sources:**
  - `UEFI Specification`, Version 2.10, Chapter 32 (Secure Boot `PK`/`KEK`/`db`/`dbx` authenticated variables).
  - `tianocore/edk2` @ `556dcfb466e9f05affeaff881d738807f8156d3c`:
    - `SecurityPkg/Library/DxeImageVerificationLib/DxeImageVerificationLib.c:291-674` (`HashPeImage`, `HashPeImageByType`)
  - `rhboot/shim` @ `e794a714339b1277abe9f890fc98de6e415681b0`:
    - `SBAT.md:1-80` (`BootHole` `CVE-2020-10713` 10 KiB / 32 KiB `dbx` capacity analysis)
    - `sbat.c:18-630` (`parse_sbat_section`, `verify_single_entry`, `verify_sbat_helper`, `set_sbat_uefi_variable`, self-revocation check)
    - `SbatLevel_Variable.txt:1-156` (`sbat,1,2021030218` .. `sbat,1,2026102600`)
    - `pe.c:380-560` (`SecDir->VirtualAddress` check, `verify_sbat_section`, `in_protocol` check)
- **Linux Kernel Sources (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):**
  - `kernel/module/signing.c:22-125` (`mod_verify_sig`, `module_sig_check`, `mangled_module`, `LOCKDOWN_MODULE_SIGNATURE`)
  - `security/integrity/ima/ima_appraise.c:462-599` (`ima_appraise_measurement`, `SB_I_IMA_UNVERIFIABLE_SIGNATURE`, `IMA_VERITY_REQUIRED`)
  - `security/integrity/evm/evm_main.c:38-159` (`evm_config_default_xattrnames`, `evm_hmac_attrs`)
  - `fs/verity/verify.c:159-470` (`verify_data_block`, `fsverity_verify_blocks`, `fsverity_verify_bio`, `sha256_finup_2x`)
  - `include/uapi/linux/fsverity.h:16-102` (`fsverity_descriptor`, `fsverity_formatted_digest`, `FS_IOC_ENABLE_VERITY`)
  - `drivers/md/dm-verity-fec.c:320-413` (`fec_decode`, `verity_fec_decode`, post-FEC `verity_hash` check)
- **Apple Darwin Sources:**
  - `apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`:
    - `osfmk/kern/cs_blobs.h:36-170` (`CS_VALID`, `CS_HARD`, `CS_KILL`, `CS_RUNTIME`, `CS_KILLED`, `CSMAGIC_*`, `CSSLOT_*`)
    - `bsd/kern/ubc_subr.c:5820-6204` (`cs_validate_hash`, `cs_validate_range`, `cs_validate_page`, `ubc_cs_getcdhash`)
    - `osfmk/vm/vm_map.c:3029-3058, 23362-23378` (`MAP_JIT` / `VM_PROT_ALL` / `vmkf_remap_prot_copy`)
  - `apple-oss-distributions/libpthread` @ `42d026df5b07825070f60134b980a1ec2552dfee`:
    - `src/pthread.c:1221-1475` (`_pthread_jit_write_protect_global_init`, `_pthread_jit_write_protect_bulk_image_load_callback`, `_pthread_jit_write_protect_freeze_config`, `pthread_jit_write_protect_np`, `pthread_jit_write_with_callback_np`, `pthread_jit_write_freeze_callbacks_np`)
  - `apple-oss-distributions/Security` @ `db15acbe6a7f257a859ad9a3bb86097bfe0679d9`: Security framework tree reference.
- **External Advisories:**
  - Microsoft Security Bulletin MS13-098 / `CVE-2013-3900` (`EnableCertPaddingCheck`), `CVE-2022-21894`, `CVE-2023-24932` (`BlackLotus` bootloader downgrade & `dbx`/`PCR[7]` mitigation).

## Revalidation

To verify the PE interval-exclusion model, `fs-verity` tree geometry, and Mach-O `CS_CodeDirectory` slot layout invariants cleanly with Python 3.10+ (standard library only):

1. **Run the Self-Contained Verification Probe:**
   ```bash
   python3 - <<'EOF'
   import math

   def pe_hash_intervals(checksum_off, sec_dir_off, size_of_headers, sections, file_size, cert_size):
       covered = [(0, checksum_off), (checksum_off + 4, sec_dir_off), (sec_dir_off + 8, size_of_headers)]
       s = size_of_headers
       for raw_ptr, raw_sz in sorted(sections):
           if raw_sz:
               covered.append((raw_ptr, raw_ptr + raw_sz))
               s += raw_sz
       if file_size > s and file_size > cert_size + s:
           covered.append((s, file_size - cert_size))
       merged = []
       for a, b in sorted(covered):
           if a < b:
               if not merged or a > merged[-1][1]: merged.append((a, b))
               else: merged[-1] = (merged[-1][0], max(merged[-1][1], b))
       excluded, cur = [], 0
       for a, b in merged:
           if cur < a: excluded.append((cur, a))
           cur = max(cur, b)
       if cur < file_size: excluded.append((cur, file_size))
       return excluded, s

   exc_clean, sum_clean = pe_hash_intervals(0x158, 0x1C8, 0x400, [(0x400, 0x1000), (0x1400, 0x800)], 0x2400, 0x800)
   exc_gap, sum_gap = pe_hash_intervals(0x158, 0x1C8, 0x400, [(0x600, 0x1000)], 0x1E00, 0x800)
   assert exc_clean == [(0x158, 0x15C), (0x1C8, 0x1D0), (0x1C00, 0x2400)]
   assert (0x400, 0x600) in exc_gap and sum_gap == 0x1400
   print("revalidation_ok=True")
   EOF
   ```
   Expected output: `revalidation_ok=True` (exit `0`).
2. **Targeted Upstream Diff Checks:**
   - Check `tianocore/edk2` `HashPeImage()` (`DxeImageVerificationLib.c`) and `rhboot/shim` `pe.c` (`verify_image` / `verify_sbat_section`) for changes to `CertSize` / `SecDir->VirtualAddress` validation or `in_protocol` SBAT enforcement.
   - Check `torvalds/linux` `fs/verity/verify.c` and `drivers/md/dm-verity-fec.c` for changes to post-FEC hash verification or `hash_block_verified` caching.
   - Check `apple-oss-distributions/libpthread` (`src/pthread.c`) for changes to `_pthread_jit_write_protect_freeze_config` and `__DATA_CONST,__pth_jit_func` allowlist enforcement.
