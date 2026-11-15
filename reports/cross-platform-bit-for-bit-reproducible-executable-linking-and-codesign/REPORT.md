# Cross-Platform Bit-for-Bit Reproducible Executable Linking and Deterministic Mach-O/PE Signing Across All 8 Tier 1 Targets

## Summary

Closes the final-linker timestamp, UUID, debug-directory, and cryptographic code-signing reproducibility boundary across all `8` Tier 1 targets (`ELF64`/`ELF32`, `PE32+`/`PE32` MSVC & MinGW, and `Mach-O` `aarch64-apple-darwin`) for `rustc 1.99.1` and `rust-lld` (`LLVM 23.1.1`), achieving **`0` diff bytes** across dual-directory, dual-timestamp (`mtime` `1700000100` vs. `1850000999`), and multi-thread (`1` vs. `8` linker threads) builds on all `8` targets while mechanizing environment-scrubbing invariance (`repro_macho_pipeline_env_invariant`, `repro_pe_pipeline_env_invariant`), Mach-O `LC_CODE_SIGNATURE` (`CS_SuperBlob` `0xfade0cc0` + `CS_CodeDirectory` `0xfade0c02`) 4 KiB SHA-256 page-hash coverage of `.anneal.evidence` (`codesign_covers_anneal_evidence`), and PE Authenticode digest coverage (`pe_authenticode_covers_anneal_evidence_and_excludes_checksum`) in `243` lines of self-contained Lean `v4.34.1` (`280` total lines, `0` `sorry`, `0` `native_decide`).

## Applicability

- **Subjects and pinned revisions:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`): `--remap-path-prefix`, `-C codegen-units=1`, `-C symbol-mangling-version=v0`, and `-C debuginfo=2` deterministic object emission.
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`): `rust-lld` (`ld.lld --build-id=sha1 --no-insert-timestamp`, `lld-link /BREPRO /TIMESTAMP:0 /pdbaltpath:... /pdbsourcepath:...`, and `ld64.lld -oso_prefix ... -adhoc_codesign`).
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): kernel-checked proofs in [support/VerifiedReproducibleLinkAndSign.lean](support/VerifiedReproducibleLinkAndSign.lean) (`859.61 ms` verification time).
- **Upstream foundation:** Resolves the explicit boundary in `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility` (`X7`), which established bit-for-bit reproducibility on `x86_64-unknown-linux-gnu` `.o`/`.rlib` artifacts while leaving cross-platform final executable linking (`PE/COFF` timestamps/PDB GUIDs, `Mach-O` `N_OSO` `.o` `st_mtime` stabs, `LC_UUID`, and `LC_CODE_SIGNATURE`) open.

## Findings

### 1. Root Causes of Cross-Platform Linker Non-Determinism and the Complete Normalization Recipe

When building and linking the same Rust program (`repro_app.rs` with `-C debuginfo=2` and an embedded `ANNEAL_EVIDENCE_ROOT` static in `.anneal` / `__DATA,__anneal_evid`) across two distinct build directories (`unnorm_alpha` vs. `unnorm_beta_longer_dir`), two `.o` modification timestamps (`1700000100` vs. `1850000999`), and two thread counts (`1` vs. `8`), unnormalized `rustc` + `rust-lld` builds differ across **all `8` Tier 1 targets** by `60` to `2,937` bytes ([support/verify_8target_reproducible_link.py](support/verify_8target_reproducible_link.py) and [support/reproducible_8target_link_audit.json](support/reproducible_8target_link_audit.json)):

1. **ELF64 / ELF32 (`*-unknown-linux-gnu`, `2,732`–`2,937` diff bytes unnormalized):** Unmapped `DW_AT_comp_dir` strings in `.debug_info`/`.debug_str` and `.symtab` `STT_FILE` entries shift section offsets and alter the 20-byte `.note.gnu.build-id` SHA-1 digest.
2. **Mach-O `aarch64-apple-darwin` (`542` diff bytes unnormalized):** Even when `rustc --remap-path-prefix` scrubs DWARF inside `repro_app.o`, `ld64.lld` synthesizes `N_SO` (`0x64`) and `N_OSO` (`0x66`) stab entries in the Mach-O `__LINKEDIT` symbol table directly from:
   - the **command-line path** of `repro_app.o` passed to `ld64.lld` (unless stripped via `-oso_prefix ${BUILD_DIR}/` and relative object path `repro_app.o`), and
   - the **filesystem `st_mtime`** of `repro_app.o` stored in the 32-bit `n_value` field of the `N_OSO` stab entry!
   Because `ld64.lld` computes `LC_UUID` and the `LC_CODE_SIGNATURE` `__LINKEDIT` page hashes over the symbol table, a 1-second change in `repro_app.o`'s `st_mtime` cascades into `LC_UUID` and `CS_CodeDirectory` unless `st_mtime` is normalized to `0` (`os.utime(obj_file, (0, 0))` / `ZERO_AR_DATE=1`) before invoking `ld64.lld`.
3. **PE32+ / PE32 MSVC (`*-pc-windows-msvc`, `60`–`63` diff bytes unnormalized):** `lld-link /debug` embeds the absolute host PDB path into `IMAGE_DEBUG_DIRECTORY` (`CV_INFO_PDB70`), hashes the `.o` command-line path passed to `lld-link` into the PDB `ModInfo` stream (which alters the 16-byte deterministic `RSDS` GUID even under `/BREPRO`), and writes the wall-clock timestamp into the COFF header unless `/BREPRO /TIMESTAMP:0 /pdbaltpath:repro_app.pdb /pdbsourcepath:C:\workspace` and relative `"repro_app.o"` are used.
4. **PE32+ MinGW (`x86_64-pc-windows-gnu`, `1,612` diff bytes unnormalized):** `ld.lld -m i386pep` writes the current epoch timestamp into `IMAGE_FILE_HEADER.TimeDateStamp` unless `--no-insert-timestamp` is passed, alongside DWARF path strings.

#### 1.1 Empirical 8-Target Reproducibility Audit (`0` Diff Bytes Across All `8` Targets)

Applying the complete normalization contract in [support/verify_8target_reproducible_link.py](support/verify_8target_reproducible_link.py) eliminates `100%` of byte differences across all `8` Tier 1 targets ([support/reproducible_8target_link_audit.json](support/reproducible_8target_link_audit.json)):

| Target Triple | Unnormalized Size (`alpha` / `beta`) | Unnormalized Diff Bytes | Normalized Size | Normalized Diff Bytes | Normalized SHA-256 Digest (`alpha == beta`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `6,744 B` / `6,768 B` | `2,766 B` | `6,504 B` | **`0 B`** | `9d4031721ff5f6ab7dc6ad2e295795e4d895a2431dc3264347110f1861e205aa` |
| `i686-unknown-linux-gnu` | `6,344 B` / `6,364 B` | `2,937 B` | `6,100 B` | **`0 B`** | `53681b65b04c05c9175b4d9a8015864441c5a30232a9509ae82766afacdbe253` |
| `aarch64-unknown-linux-gnu` | `7,272 B` / `7,288 B` | `2,732 B` | `7,024 B` | **`0 B`** | `d70a077ee07c542cc45d9830bc6d86508618f3af5868661dfd63f6b80f39ef63` |
| `aarch64-apple-darwin` | `34,064 B` / `34,080 B` | `542 B` | `33,968 B` | **`0 B`** | `a44f77f737a5aa0cfdc49486c0083d55d0adb2491913046663e50ed3b682f22c` |
| `x86_64-pc-windows-msvc` | `3,584 B` / `3,584 B` | `62 B` | `3,584 B` | **`0 B`** | `2ee2ea1149754e38ca03909ed8800fffd0951426a2c707eefe82bb0c5da0c3ea` |
| `x86_64-pc-windows-gnu` | `10,240 B` / `10,240 B` | `1,612 B` | `9,728 B` | **`0 B`** | `c3e3e3d049a5fc47699e019c7aa13853261eb910c79241c70f104a47e56948fe` |
| `i686-pc-windows-msvc` | `3,584 B` / `3,584 B` | `60 B` | `3,584 B` | **`0 B`** | `82079b996560dd789a43d461df24f6d50c110e197ff01420b273176a04cc45c0` |
| `aarch64-pc-windows-msvc` | `3,584 B` / `3,584 B` | `63 B` | `3,584 B` | **`0 B`** | `c4663c3aab2654abbfaf810cfe212b26791deb6648877b1dfdd9fa851e966cf4` |

### 2. Mach-O `LC_CODE_SIGNATURE` 4 KiB Page-Hash Tree and `.anneal.evidence` Binding

On `aarch64-apple-darwin`, macOS kernel enforcement (`AppleMobileFileIntegrity`) requires every arm64 executable to carry a valid `LC_CODE_SIGNATURE` in `__LINKEDIT`. If a build tool attempts to append or modify `.anneal.evidence` *after* linking using `llvm-objcopy`, the modified page inside `[0, codeLimit)` invalidates the `CS_CodeDirectory` page-hash slot and triggers an immediate `SIGKILL` (`EXC_BAD_ACCESS (Code Signature Invalid)`).

By emitting `ANNEAL_EVIDENCE_ROOT` directly as a linker input section (`#[link_section = "__DATA,__anneal_evid"]`) *before* `ld64.lld -adhoc_codesign` computes `LC_UUID` and `LC_CODE_SIGNATURE`, the `.anneal.evidence` descriptor is cryptographically bound into the Mach-O code signature itself. Our parser `verify_macho_code_signature` in [support/verify_8target_reproducible_link.py](support/verify_8target_reproducible_link.py) inspects the linked `33,968`-byte `aarch64-apple-darwin` binary ([support/reproducible_8target_link_audit.json](support/reproducible_8target_link_audit.json)):

- **`CS_SuperBlob` (`0xfade0cc0`):** Located at file offset `33,536` (`length = 432 B`).
- **`CS_CodeDirectory` (`0xfade0c02`, version `0x20400`):** Uses `hashType = 2` (`SHA-256`), `pageSize = 4,096 B` (`2^12`), `codeLimit = 33,536 B`, and `nCodeSlots = 9`.
- **Page-hash verification:** All `9 / 9` 4 KiB page slots in `[0, 33536)` match their recorded SHA-256 digests in `CS_CodeDirectory`.
- **`.anneal.evidence` coverage:** `ANNEAL_EVID_V1` is placed at file offset `16,384` (page slot `4`), and flipping `1` byte at `evid_off + 16` deterministically mismatches slot `4`'s recorded SHA-256 hash (`post_sign_evidence_tamper_rejected = true`).

### 3. Lean 4 Mechanization (`VerifiedReproducibleLinkAndSign.lean`)

In [support/VerifiedReproducibleLinkAndSign.lean](support/VerifiedReproducibleLinkAndSign.lean), we formalize `HostBuildEnv`, `PureSourceSpec`, `NormalizedEnv`, `SignedMachOBinary`, and `SignedPeBinary`, and prove six machine-checked theorems (`0` `sorry`, `0` `native_decide`):

1. **`scrubHostEnv_invariant`:** For any two host environments `envA envB : HostBuildEnv` with arbitrary paths, wall-clock times, `.o` `st_mtime`s, and thread counts, `scrubHostEnv envA = scrubHostEnv envB`.
2. **`hashPageIdeal_injective`:** Injective collision-free page digest lemma for `CS_CodeDirectory` and Authenticode verification.
3. **`repro_macho_pipeline_env_invariant`:** Building and ad-hoc signing a Mach-O executable from `envA` and `envB` yields identical `SignedMachOBinary` structures (`buildDeterministicMachO envA spec = buildDeterministicMachO envB spec`) and passes `verifyMachOCodeDirectory = true`.
4. **`codesign_covers_anneal_evidence`:** Any post-sign mutation of `annealEvidPage` (`tamperedEvidPage ≠ spec.annealEvidPage`) inside `[0, codeLimit)` causes `verifyMachOCodeDirectory` to evaluate to `false`.
5. **`repro_pe_pipeline_env_invariant`:** Building a PE32/PE32+ image under `/BREPRO /TIMESTAMP:0` from `envA` and `envB` yields identical `SignedPeBinary` images (`buildDeterministicPe envA spec = buildDeterministicPe envB spec`) and passes `verifyPeAuthenticode = true`.
6. **`pe_authenticode_covers_anneal_evidence_and_excludes_checksum`:** Updating the excluded PE header fields (`peCheckSum` and `certTableDirEntry` at `DataDirectory[4]`) preserves `verifyPeAuthenticode = true`, whereas mutating the `.anneal` evidence section (`tamperedEvid ≠ spec.annealEvidPage`) falsifies `verifyPeAuthenticode = false`.

## Boundaries

1. **Hardware PKCS#7 / CMS Apple Developer ID and Windows Authenticode timestamp-authority signatures:** Our pipeline mechanizes and empirically verifies deterministic ad-hoc `LC_CODE_SIGNATURE` (`CS_CodeDirectory` version `0x20400` SHA-256 4 KiB page hashes) and canonical PE Authenticode image digests. When an external RFC 3161 TSA (Time Stamping Authority) countersignature or non-deterministic ECDSA nonce is appended into the CMS blob (`BlobWrapper` in `__LINKEDIT` or `WIN_CERTIFICATE` in PE `DataDirectory[4]`), reproducibility applies to the canonical signed payload (`[0, codeLimit)` and `computePeAuthenticodeDigest`) while the external CMS signature envelope carries the certificate signature.
2. **Host-filesystem case-folding differences on `#include` / `include_bytes!` paths:** The normalization contract requires consistent case in relative source paths inside the workspace (`repro_app.rs`).
3. **Parallel incremental ThinLTO cache ordering with `codegen-units > 1`:** As established in `X7`, bit-for-bit reproducible verified builds pin `-C codegen-units=1`, `-C incremental=false`, and linker `--threads=1` (`/threads:1`).

## Evidence

- **Lean 4 mechanization ([support/VerifiedReproducibleLinkAndSign.lean](support/VerifiedReproducibleLinkAndSign.lean)):** `280` total lines (`243` non-comment code lines), `6` theorems (`scrubHostEnv_invariant`, `hashPageIdeal_injective`, `repro_macho_pipeline_env_invariant`, `codesign_covers_anneal_evidence`, `repro_pe_pipeline_env_invariant`, `pe_authenticode_covers_anneal_evidence_and_excludes_checksum`), `0` `sorry`, `0` `native_decide`, `#eval checkAllM8 = true`, verified in `859.61 ms`.
- **8-target reproducibility & `LC_CODE_SIGNATURE` audit ([support/verify_8target_reproducible_link.py](support/verify_8target_reproducible_link.py) and [support/reproducible_8target_link_audit.json](support/reproducible_8target_link_audit.json)):** Verifies `0` diff bytes across all `8` Tier 1 targets and validates all `9` SHA-256 4 KiB page slots of `CS_CodeDirectory`.

## Revalidation

```bash
python3 support/verify_8target_reproducible_link.py
```
