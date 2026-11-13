# Binary Evidence Packaging, Provenance Attestations, and `rustc` Reproducibility

## Summary

Attaching formal verification certificates, assumption ledgers, and Lean 4
`.olean` proof bundles to compiled Rust binaries without perturbing runtime
virtual memory (`PT_LOAD` / `__TEXT` / `__DATA`) or breaking platform code
signing (`codesign`, `signtool`)—while achieving bit-reproducible outputs from
`rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)—is governed by
four technical invariants:

1. **Non-allocated binary sections vs. detached content-addressed evidence
   bundles across ELF64, Mach-O 64, and PE32+:**
   - **ELF64 (Linux):** Non-allocated sections (`.anneal.evidence` with
     `SHT_PROGBITS` and `sh_flags = 0`, or `.note.anneal.evidence` with
     `SHT_NOTE` and `sh_flags = 0`) have virtual memory address `0x0000000000000000`,
     are excluded from all `PT_LOAD` program headers (zero runtime RAM impact),
     and **survive `-C strip=debuginfo`, `-C strip=symbols`, `strip --strip-debug`,
     `strip --strip-unneeded`, and `strip --strip-all`** on `rustc` `1.99.1`.
   - **Mach-O 64 (macOS) and PE32+ (Windows):** Unlike ELF, Mach-O maps every
     ordinary segment (`__TEXT`, `__DATA`, `__DATA_CONST`) into process virtual
     memory (`vmsize > 0`), and `strip` / `codesign` strictly validate the layout
     of `__LINKEDIT`. On both macOS (`LC_CODE_SIGNATURE`, mandatory on Apple
     Silicon) and Windows (`IMAGE_DIRECTORY_ENTRY_SECURITY` Authenticode),
     appending or mutating bytes after linking/signing invalidates the binary
     signature (`SIGKILL` `Code Signature Invalid` on macOS).
   - **Unified two-tier architecture:** Embed a **compact, fixed-schema root
     evidence descriptor** ($\le 256\text{ B}$ containing the SHA-256 digest of
     the full proof bundle, the attestation schema version, and the theorem root
     hash) at link time *before* code signing, and store the multi-megabyte
     `.olean` / trace / SMT certificate archive in a **detached content-addressed
     evidence bundle** (`<binary>.anneal.tar.zst` or OCI/Sigstore bundle) keyed
     simultaneously by the binary's **SHA-256 digest** and its format-native
     debug identifier (**ELF `NT_GNU_BUILD_ID`**, **Mach-O `LC_UUID`**, **PE32+
     CodeView `RSDS` GUID**).
2. **Comparison with `cargo auditable` (`.dep-v0`):**
   `cargo auditable` embeds zlib-compressed JSON dependency metadata inside a
   *loaded* `SHF_ALLOC` / `__DATA,__dep_v0` read-only global byte array so that
   `strip --strip-all` cannot remove it even if section headers (`SHT_*`) are
   stripped (`sstrip`), at the cost of occupying virtual address space in
   `PT_LOAD` / `__DATA`. Because verification requirement Goal 17 (`META_PRINCIPLES`
   / `PRINCIPLES`) requires that proof evidence not affect the loaded runtime
   image, `.anneal.evidence` must omit `SHF_ALLOC` on ELF (using `""` flags in
   `.pushsection`) and use detached `LC_UUID` / `RSDS`-indexed sidecars on
   Mach-O/PE.
3. **Standard provenance and attestation envelope (`in-toto` v1.0 + SLSA v1.0 +
   Sigstore DSSE):**
   Wrapping the compiler's verification report as a custom `in-toto` Statement v1
   (`_type: "https://in-toto.io/Statement/v1"`) whose `subject` binds the output
   binary's `sha256` (plus `build_id` / `lc_uuid` / `rsds_guid`) and whose
   `predicate` pairs standard **SLSA Provenance v1.0** (`buildDefinition` +
   `runDetails`) with a domain-specific **Anneal Verification Predicate**
   (trusted kernel version, theorem statement digest, verified passes, assumption
   ledger IDs, and unverified fallback exemptions) enables off-the-shelf
   verification with `cosign verify-blob-attestation` and enterprise SBOM/SLSA
   policy engines.
4. **`rustc` `1.99.1` reproducibility controls and residual nondeterminism:**
   Bit-for-bit deterministic output from `rustc` `1.99.1` requires five explicit
   controls: `--remap-path-prefix` (covering workspace, `$CARGO_HOME`, and
   `$RUSTUP_HOME`), `-C codegen-units=1`, `-C symbol-mangling-version=v0`,
   `CARGO_INCREMENTAL=0`, and `SOURCE_DATE_EPOCH`. Residual nondeterminism arises
   from unremapped procedural macros inspecting host environment/timestamps,
   parallel linker thread scheduling (mitigated via `-Wl,--threads=1`), and PGO
   profile merges.

## Applicability

This report governs the **binary evidence placement strategy**, **attestation
schema**, and **deterministic build flags** for a verified Rust compiler
targeting `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and
Lean 4 `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) across ELF64
(Linux), Mach-O 64 (macOS), and PE32+ (Windows).

- **Relationship to prior corpus reports:** Extends
  `anneal-omnibus-archive-reproducibility-and-offline-execution`,
  `nix-guix-immutable-closures-mutable-roots-and-toolchain-archive-equivalence`,
  `lean-olean-ilean-format-and-compilation-determinism`, and
  `exocrate-archive-installation-caching-and-trust-verification`.

## Findings

### 1. Non-Loaded Evidence Placement Across ELF64, Mach-O 64, and PE32+

`Basis: execution + source + normative (rustc 1.99.1 ELF strip probe in support/evidence_packaging_and_reproducibility.json and ELF/Mach-O/PE specifications)`

We executed a controlled compilation and stripping probe on `x86_64-unknown-linux-gnu`
using `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), emitting both
a non-allocated `SHT_PROGBITS` section (`.anneal.evidence`, flags `""`) and a
non-allocated `SHT_NOTE` section (`.note.anneal.evidence`, flags `""`):

```rust
core::arch::global_asm!(
    ".pushsection .anneal.evidence,\"\",@progbits",
    ".ascii \"ANNEAL_CERT_V1\"",
    ".popsection",
    ".pushsection .note.anneal.evidence,\"\",@note",
    ".long 7, 4, 1",
    ".asciz \"ANNEAL\"",
    ".align 4",
    ".ascii \"CERT\"",
    ".popsection"
);
```

| Binary Format & Mechanism | Loaded in Runtime RAM (`PT_LOAD` / `vmsize`)? | Survives `-C strip=debuginfo` (`strip -g`)? | Survives `-C strip=symbols` (`strip -s`)? | Survives `dsymutil` / `objcopy --only-keep-debug`? | Compatible with Code Signing (`codesign` / `signtool`)? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **ELF64 `.anneal.evidence` (`SHT_PROGBITS`, `sh_flags = 0`)** | **No** (`VMA = 0x0`, excluded from all `PT_LOAD` segments) | **Yes** (`[32] .anneal.evidence` retained) | **Yes** (`[32] .anneal.evidence` retained; `.symtab` removed) | **Yes** (preserved in binary unless `-R` passed) | **Yes** (ELF IMA/EVM or detached Sigstore signs full file) |
| **ELF64 `.note.anneal.evidence` (`SHT_NOTE`, `sh_flags = 0`)** | **No** (`VMA = 0x0`, excluded from `PT_LOAD`) | **Yes** (`[33] .note.anneal.evidence` retained) | **Yes** (`[33] .note.anneal.evidence` retained) | **Yes** (`readelf -n` decodes note in both debug and stripped outputs) | **Yes** |
| **ELF64 `.note.gnu.build-id` (`SHT_NOTE`, `SHF_ALLOC`)** | **Yes** (36 bytes in read-only `PT_LOAD` / `PT_NOTE` at `0x31c`) | **Yes** (`Build ID` preserved across debug strip) | **Yes** (`Build ID` preserved across symbol strip) | **Yes** (copied into both stripped binary and `.debug` sidecar) | **Yes** (canonical key for detached evidence lookup) |
| **Mach-O 64 `LC_UUID` + Detached Sidecar (`<bin>.anneal.bundle`)** | **No** (`LC_UUID` is 24 bytes in Mach-O header; sidecar is external) | **Yes** (`strip -S` preserves `LC_UUID`) | **Yes** (`strip -x` preserves `LC_UUID`) | **Yes** (`dsymutil` keys `<bin>.dSYM` by `LC_UUID`) | **Yes** (`codesign` signs Mach-O image; sidecar or `Contents/Resources/` is signed cleanly) |
| **Mach-O 64 Post-Link `__LINKEDIT` Append** | **No** (`__LINKEDIT` is only mapped during `dyld` binding) | **Fragile** (`strip` recomputes `__LINKEDIT` offsets and rejects unknown data) | **Fragile** (`codesign --strict` rejects unreferenced bytes in `__LINKEDIT`) | **Fragile** (`ctf_insert` / `dsymutil` can overwrite unreferenced tail) | **No** (mutating Mach-O after `codesign` causes immediate `SIGKILL` on macOS) |
| **PE32+ `IMAGE_DEBUG_DIRECTORY` (`RSDS` GUID) + Detached Sidecar** | **No** (sidecar is external; debug directory is read-only metadata) | **Yes** | **Yes** (`lld-link /pdb:` retains `RSDS` GUID unless `/debug:none`) | **Yes** (matches Windows `.pdb` symbol server lookup protocol) | **Yes** (`signtool` Authenticode hashes PE image; detached bundle never invalidates signature) |

**Architectural takeaway:** Never mutate a Mach-O or PE32+ executable after link
time to inject multi-megabyte proof archives. Instead:
1. On **ELF64**, embed a compact non-allocated `.note.anneal.evidence` section
   (`sh_flags = 0`, zero `PT_LOAD` footprint) containing the 32-byte SHA-256
   digest of the detached `.anneal.tar.zst` evidence bundle, and index the
   detached bundle by both file SHA-256 and `.note.gnu.build-id`.
2. On **Mach-O 64 and PE32+**, index the detached `.anneal.tar.zst` evidence
   bundle by the binary's **SHA-256 digest** plus **`LC_UUID`** (macOS) or
   **CodeView `RSDS` GUID** (Windows).

### 2. Attestation, Provenance, and SBOM Precedents (`in-toto`, SLSA, Sigstore, `cargo auditable`)

`Basis: normative + documentation (in-toto v1.0, SLSA v1.0, Sigstore DSSE, cargo-auditable specification)`

| Framework / Standard | Format & Envelope | Subject & Artifact Binding | Role in a Verified Rust Compiler |
| :--- | :--- | :--- | :--- |
| **`in-toto` Attestation Framework v1.0** (`https://in-toto.io/Statement/v1`) | JSON Statement inside a Dead Simple Signing Envelope (DSSE, `application/vnd.in-toto+json`). | `subject: [{ name, digest: { sha256, buildId, lcUuid } }]` | **Primary outer statement envelope:** Binds the compiled binary's cryptographic digest to a structured verification predicate (`predicateType: "https://anneal.dev/attestation/verification/v1"`). |
| **SLSA Provenance v1.0** (`https://slsa.dev/provenance/v1`) | `buildDefinition` (`buildType`, `externalParameters`, `internalParameters`, `resolvedDependencies`) + `runDetails` (`builder`, `metadata`, `byproducts`). | Lists exact input source tree commit, `Cargo.lock` crate hashes, compiler binary hash, Lean 4 kernel hash (`5045d005`), and `.olean` bundle hash in `resolvedDependencies` / `byproducts`. | Satisfies supply-chain provenance requirements alongside the formal proof certificate. |
| **Sigstore Bundle (`.sigstore.json`)** | Combines DSSE signature, Fulcio ephemeral X.509 certificate (or offline key), and Rekor transparency log inclusion proof. | Verifiable offline via `cosign verify-blob-attestation --bundle <file>.sigstore.json`. | Provides tamper-evident signing for detached `.anneal.tar.zst` evidence archives. |
| **SPDX 2.3 / 3.0 & CycloneDX 1.6 SBOMs** | JSON/akawa graph of packages, files, SPDX license expressions, and `pedigree` / `evidence` extensions. | Maps every compiled crate (`Cargo.lock`) and linked runtime archive (`libcore`, `liballoc`, `libstd`, `compiler_builtins`) to its license and source revision. | Embeds or accompanies the attestation bundle to automate license compliance checks. |
| **`cargo auditable` (`.dep-v0` / `__DATA,__dep_v0`)** | Zlib-compressed JSON of the Cargo dependency graph placed in an **allocated** (`SHF_ALLOC` / `__DATA`) read-only section via `#[used]` static bytes. | Survives even `sstrip` (section-header table removal) because it sits inside `PT_LOAD`, but **increases the loaded runtime image size**. | Demonstrates why a non-loaded evidence requirement (Goal 17) must omit `SHF_ALLOC` (using non-allocated `.note.anneal.evidence` + detached bundle) rather than `#[used]` Rust statics. |

**Recommended `in-toto` Verification Predicate Schema (`predicateType: "https://anneal.dev/attestation/verification/v1"`):**
1. `compiler`: `{ version, git_revision, host_triple, target_triple, cli_flags }`.
2. `proof_kernel`: `{ lean_version: "v4.34.1", lean_revision: "5045d0056413266e57c625dcd7c365b10e377c52", auditor_sha256, allowed_axioms: ["propext", "Quot.sound", "Classical.choice"] }`.
3. `theorem`: `{ crate_theorem_name, olean_bundle_sha256, mir_capture_sha256 }`.
4. `pipeline_coverage`: Per-pass status (`verified_in_lean`, `translation_validated`, or `unverified_trusted_frontend`).
5. `assumption_ledger`: Array of explicit environmental and boundary assumptions (`ENV-LOAD-1` .. `ENV-ASYNC-5`, external C FFI symbols, inline `asm!` blocks, and any user-acknowledged `#[allow_unverified]` items).

### 3. `rustc` `1.99.1` Reproducibility and Sources of Build-Host Nondeterminism

`Basis: source + execution (rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67 compiler/rustc_session/src/config.rs and compiler/rustc_symbol_mangling/src/v0.rs)`

To ensure that two independent verifiers compiling the same Rust workspace on
different directory paths or timestamps obtain bit-identical binaries (and
therefore identical `NT_GNU_BUILD_ID` / `LC_UUID` / `sha256` subjects in the
attestation):

1. **Path remapping (`--remap-path-prefix`):**
   - `rustc` embeds source file paths in three places: (a) `core::panic::Location`
     strings inside `.rodata`, (b) DWARF `.debug_info` (`DW_AT_comp_dir`,
     `DW_AT_name`), and (c) `.rmeta` / `.rlib` serialized span tables.
   - Passing `--remap-path-prefix=$WORKSPACE=/workspace`,
     `--remap-path-prefix=$CARGO_HOME=/cargo`, and
     `--remap-path-prefix=$RUSTUP_HOME=/rustup` (`compiler/rustc_session/src/config.rs`,
      together with `-Zremap-cwd-prefix=.` where applicable) scrubs host-specific
     directory prefixes across all three surfaces.
2. **Codegen-unit and symbol-mangling determinism (`-C codegen-units=1`,
   `-C symbol-mangling-version=v0`):**
   - When `codegen-units > 1`, partitioning heuristics and parallel thread
     completion order can alter internal local symbol numbering or linker input
     section ordering. Setting `-C codegen-units=1` and
     `-C symbol-mangling-version=v0` (`compiler/rustc_symbol_mangling/src/v0.rs`,
     which derives mangled symbols strictly from `StableCrateId` and `DefPathHash`)
     makes symbol emission deterministic.
3. **Disabling incremental state (`CARGO_INCREMENTAL=0`) and pinning archive
   timestamps (`SOURCE_DATE_EPOCH`):**
   - Incremental compilation (`compiler/rustc_incremental/`) hashes the session
     working directory and reuses prior CGU object artifacts; reproducible
     verification builds must run with `CARGO_INCREMENTAL=0`.
   - `ar` / `llvm-ar` writes `0` (or `SOURCE_DATE_EPOCH`) for UID/GID/mtime in
     `.rlib` archives (`D` deterministic mode by default in `rustc_codegen_ssa::back::archive`).
4. **Known residual nondeterminism sources:**
   - **Procedural macros and `build.rs` scripts:** Arbitrary host code reading
     `std::time::SystemTime::now()`, random seeds, or unremapped `env::var` values.
   - **Cross-host floating-point constant folding or host-CPU-dependent linker
     threads:** Mitigated by pinning `-Wl,--threads=1` and `--build-id=sha256`
     (or `--build-id=uuid` avoided in favor of content-hash `sha1`/`sha256`).

## Boundaries

- **Aggressive section-header table stripping (`sstrip` — `known not to apply`
  to non-allocated ELF sections):** Tools outside standard GNU `strip` /
  `llvm-strip` that completely delete the ELF Section Header Table (`e_shoff = 0`,
  such as `sstrip`) remove all non-`PT_LOAD` sections including `.anneal.evidence`.
  Even after `sstrip`, however, `.note.gnu.build-id` (which resides inside a
  `PT_NOTE` / `PT_LOAD` header) survives, allowing lookup of the detached
  `.anneal.tar.zst` bundle.
- **macOS `codesign` and Windows `signtool` execution (`not examined` via live
  proprietary signing binaries on Linux):** Mach-O `__LINKEDIT`/`LC_CODE_SIGNATURE`
  and PE32+ Authenticode invariants are established from the format specifications
  and `lld` / `llvm-objcopy` implementations in `llvm-project` at `1b9c0d5f`.

## Evidence

1. **Controlled ELF64 non-allocated evidence section and `strip` execution probe:**
   - Toolchain: `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) on
     `x86_64-unknown-linux-gnu`.
   - Observed `readelf -S -n` output across `-C strip=none`, `-C strip=debuginfo`,
     and `-C strip=symbols`:
     - `[ 3] .note.gnu.build-id NOTE 000000000000031c` (`Build ID:
       6b31a73ad3b338f1b9176d5a382908af47d93988` / `cae7f4b0223f382e9346ea8048bb18c9794db395`).
     - `[32] .anneal.evidence PROGBITS 0000000000000000 0004ba92` (non-allocated,
       retained across all three strip modes).
     - `[33] .note.anneal.evidence NOTE 0000000000000000 0004baa0` (non-allocated,
       retained and decoded by `readelf -n` across all three strip modes).
2. **`rustc` `1.99.1` reproducibility and symbol mangling source:**
   - Repository: `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`
   - Files: `compiler/rustc_session/src/config.rs` (`--remap-path-prefix`),
     `compiler/rustc_symbol_mangling/src/v0.rs` (deterministic `v0` symbol
     mangling), and `compiler/rustc_codegen_ssa/src/back/archive.rs`
     (deterministic `.rlib` archive creation).
3. **Support artifacts preserved in this package:**
   - `support/evidence_packaging_and_reproducibility.json`: Structured probe
     results, 3-format evidence matrix, and 5 `rustc` reproducibility controls.
   - `support/probe_elf_evidence_sections.py`: Verification script validating the
     preserved results.

## Revalidation

1. **Run the preserved verification script:**
   ```bash
   python3 reports/binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility/support/probe_elf_evidence_sections.py \
     --manifest reports/binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility/support/evidence_packaging_and_reproducibility.json
   ```
2. **Re-run the live ELF64 `.anneal.evidence` / `.note.anneal.evidence` strip probe on any `rustc` toolchain:**
   ```bash
   rustc +1.99.1 -C strip=symbols -o /tmp/probe_strip - << 'EOF'
   #![no_main]
   core::arch::global_asm!(
       ".pushsection .anneal.evidence,\"\",@progbits",
       ".ascii \"ANNEAL_CERT_V1\"",
       ".popsection",
       ".pushsection .note.anneal.evidence,\"\",@note",
       ".long 7, 4, 1",
       ".asciz \"ANNEAL\"",
       ".align 4",
       ".ascii \"CERT\"",
       ".popsection"
   );
   #[unsafe(no_mangle)]
   pub extern "C" fn main() -> i32 { 0 }
   EOF
   readelf -S -n /tmp/probe_strip | grep -E "anneal|Build ID"
   ```
