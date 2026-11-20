# Rust Sysroot `.rlib` Artifact Provenance, Reproducible Capture, and TOCTOU Hardening

## Summary

In any compiler-integrated Rust verifier, precompiled sysroot libraries (`libcore-*.rlib`, `liballoc-*.rlib`, `libstd-*.rlib`, `libcompiler_builtins-*.rlib`) sit **inside the soundness-critical Trusted Computing Base (TCB)** even when proofs target only crate-local functions. Closing the sysroot trust gap across extraction, compilation, and linking requires enforcing four coupled invariants:

1. **Authenticating `librustc_driver.so` Does Not Authenticate `--sysroot` `.rlib` Semantics:** `rustc` resolves type layouts, niche discriminants, trait coherence, `const fn` CTFE MIR (`mir_for_ctfe`), promoted constants (`promoted_mir`), and cross-crate inlinable MIR (`optimized_mir`) lazily out of `lib.rmeta` inside sysroot `.rlib` archives (`rustc_metadata/src/rmeta/decoder/cstore_impl.rs:238–243`). Checking `rustc_interface::util::rustc_version_str()` or verifying `lib/rustlib` directory existence leaves the compiler vulnerable to substituted or tampered `.rlib`/`.rmeta` binaries via `--sysroot`, `RUSTFLAGS`, or ambient toolchain directories.
2. **Three-Way File-Admission & `Mmap` TOCTOU Hazards:** Both `DefaultMetadataLoader::get_rlib_metadata` (`rustc_codegen_ssa/src/back/metadata.rs:43–79`) and `get_rmeta_metadata_section` (`rustc_metadata/src/locator.rs:934–951`) open dependency files via `File::open` and map them via `unsafe { Mmap::map(file) }` (`memmap2::MmapOptions::new().map_copy_read_only(&file)`, `rustc_data_structures/src/memmap.rs:14–29`). Pre-hashing paths before `rustc` runs leaves three distinct time-of-check-to-time-of-use (TOCTOU) gaps: (a) inter-open path replacement (`remove_file` + `rename` or symlink race); (b) live page-cache mutation or `ftruncate` `SIGBUS` under `PROT_READ, MAP_PRIVATE` *after* `MetadataBlob::new`'s one-shot `MemDecoder::new` validation (`rmeta/decoder.rs:64–70`), which `memmap.rs:16–18` explicitly flags as *"likely unsound"*; and (c) **Capture-vs-Link Split-Brain**, where `CrateLocator::extract_lib` (`locator.rs:536–593`) resolves `.rmeta` before `.rlib` and skips `.rlib` under `only_needs_metadata` (or relies on 64-bit `Svh` crate hashes), letting tampered `.rcgu.o` code members link behind benign `lib.rmeta`.
3. **OS-Enforced Read-Only Sealing + Post-Analysis Source Reconciliation:** Sound capture requires copying or bind-mounting the sysroot into a kernel-enforced immutable substrate (`bwrap --unshare-all --ro-bind` over private staged artifacts, Linux `memfd_create` + `F_SEAL_WRITE|F_SEAL_SHRINK|F_SEAL_GROW|F_SEAL_SEAL`, or `fs-verity` `FS_IOC_ENABLE_VERITY` after write-FD exclusion), computing SHA-256 over the sealed bytes, and checking every crate in `tcx.crates(())` / `tcx.used_crate_source(cnum)` (`cstore_impl.rs:399`) inside `after_analysis` against a locked manifest.
4. **Deterministic `-Zbuild-std` Provenance:** Rebuilding sysroot `.rlib`s reproducibly from `rust-src` requires normalizing three distinct path prefixes (workspace, `$CARGO_HOME`, and `rust-src` sysroot) under `--remap-path-scope=all` (`rustc_session/src/config.rs:1311–1340`), pinning `-C metadata` / `RUSTFLAGS` / `CARGO_INCREMENTAL=0` / `-C codegen-units=1`, and normalizing `ar` headers and `SOURCE_DATE_EPOCH`.

## Applicability

This report governs sysroot trust boundaries, compiler-driver artifact admission, and reproducible standard-library builds across Rust verification pipelines. The nine subjects in `REPORT.json` relate as follows:

- **Core `rustc` & Cargo Substrate (`rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rust-lang/cargo` at `9ae79c984e55ee94ed9642ea101abd3f16f82916`):** Supply exact source definitions for sysroot path discovery (`filesearch.rs`), `CrateLocator` (`locator.rs`), `DefaultMetadataLoader` (`metadata.rs`), `Mmap` (`memmap.rs`), `MetadataBlob` (`rmeta/decoder.rs`), `--remap-path-scope` (`config.rs`), and `-Zbuild-std` compilation.
- **Verification Toolchain Architectures (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `model-checking/kani` at `0601bc57f00a5b7f4d8fb4dd76acd6ec9355227a`, `verus-lang/verus` at `0dab219272ac2353320bd177ebb3929453b90a9e`, `AeneasVerif/charon` at `ab5b6d60f53691bc4edee3b11cc52656c090071d`, and `creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`):** Enable a direct source-level comparison of how Anneal's Nix/Lean SHA-256 lock manifests, Kani's `-Zbuild-std` `.rmeta` pipeline, Verus's `--extern vstd` / `Vstd::IsCore` driver, Charon's full-MIR sysroot, and Creusot's toolchain setup manage stdlib TCB boundaries.
- **OS Immutability & Supply-Chain Baselines (`torvalds/linux` at `65e4fd942f72a9dba0e4e257290c4fa1aa756854`, DOI `10.1109/MS.2021.3073045`, SLSA v1.0, and in-toto):** Anchor kernel-enforced `memfd` seals (`mm/memfd.c`) and `fs-verity` (`fs/verity/enable.c`) alongside reproducible build provenance standards.

This report extends rather than repeats prior corpus coverage of `.rs` source-map ingestion (`compiler-concurrent-source-modification-and-hermetic-input-binding`), foreign `lib.rmeta` MIR inlining (`rustc-cross-crate-rmeta-provenance-and-foreign-mir-inlining`), Nix archive relocation (`anneal-nix-toolchain-packaging-and-binary-relocation`), and Lean `.olean` boundary auditing (`anneal-trusted-boundary-audit-olean-stubbing-and-conservativity`), focusing specifically on **compiled Rust sysroot `.rlib`/`.rmeta` provenance, `Mmap` TOCTOU races, `rmeta`/`rlib` split-brain, and `-Zbuild-std` determinism**.

## Findings

### 1. `rustc` Sysroot Discovery, `.rlib` Archive Structure, and Zero-Copy `Mmap` Decoding

`Basis: source + documentation`

When `rustc` resolves `core`, `alloc`, `std`, or `--extern` dependencies during MIR capture, four internal subsystems control which bytes enter compiler memory:

1. **Sysroot Path Resolution (`rustc_session/src/filesearch.rs:47–58, 189–256`, `config.rs:1342–1346`):**
   `Config::opts.sysroot` (`Sysroot { explicit, default }`) selects `explicit` if `--sysroot` was supplied, or falls back to `default_sysroot()` (`filesearch.rs:189–256`): first checking whether `env::args_os().next()` is a symlink (`fs::read_link`, `#79253`) pointing near a `lib/rustlib` directory (`lines 233–252`), and otherwise calling `dladdr` (`libc::dladdr`, `lines 74–90`) on `librustc_driver.so` to walk up two or three directories to `<sysroot>`, and finally joining `lib/rustlib/<target>/lib` (`make_target_lib_path`, `lines 47–50`). Any toolchain wrapper overriding `--sysroot` or relocating `librustc_driver.so` silently redirects sysroot `.rlib` discovery unless explicitly gated.
2. **Candidate Discovery, `rmeta`-First Precedence, and 64-bit `Svh` (`rustc_metadata/src/locator.rs:380–696, 741–797`):**
   `CrateLocator::find_library_crate` (`lines 380–520`) scans search paths for `lib<crate><extra_prefix>*.{rlib,rmeta}` and platform dylibs (`lines 430–468`), deduplicating by `try_canonicalize(&spf_path)` (`line 452`). Inside `extract_lib` (`lines 522–548`), **`CrateFlavor::Rmeta` is always extracted before `CrateFlavor::Rlib`** (`lines 536–537`), and `extract_one` skips `.rlib` entirely whenever `slot.is_some()` and `!self.needs_crate_flavor(flavor)` (`lines 555–560, 589–592`—true whenever `only_needs_metadata` is set!). When `--extern name=path` is passed (`find_commandline_library`, `lines 741–797`), `locator.rs:761–782` intentionally matches the `"lib*.rlib"` / `"lib*.rmeta"` extension against the **non-canonicalized symlink name** (`loc_orig`) before inserting `loc_canon`, accommodating extensionless CAS stores (such as Nix or Bazel CAS symlinks). Crate matching (`crate_matches`, `lines 698–739`) checks only `is_proc_macro_crate`, `name`, `triple`, and **`Svh` (`header.hash`, a 64-bit hash)**—providing zero cryptographic collision resistance against malicious artifact substitution.
3. **`.rlib` Container & Lazy Zero-Copy `MetadataBlob` (`rustc_codegen_ssa/src/back/metadata.rs:43–79, 108–126`; `rustc_metadata/src/fs.rs:18`; `rmeta/decoder.rs:52–74`; `memmap.rs:14–29`):**
   An `.rlib` file is a GNU `ar` archive (`!<arch>\n`) bundling object members (`*.rcgu.o`) alongside a metadata object containing `"lib.rmeta"` (`METADATA_FILENAME`, `fs.rs:18`; encoded during compilation into `full.rmeta` or `stub.rmeta`, `fs.rs:48–55`). To read it, `DefaultMetadataLoader::get_rlib_metadata` (`metadata.rs:56–79`) calls `File::open(path)` and `unsafe { Mmap::map(file) }` (`metadata.rs:47–53`), parses the archive via `object::read::archive::ArchiveFile::parse`, locates `"lib.rmeta"`, extracts the `.rmeta` ELF/Mach-O/COFF section (`search_for_section`, `lines 108–126`) as a zero-copy `&'a [u8]` slice, wraps it in `OwnedSlice`, and passes it to `MetadataBlob::new` (`rmeta/decoder.rs:64–67`). `MetadataBlob::new` runs `MemDecoder::new(&slice, 0)` **once at construction time**, and downstream `TyCtxt` providers (`cstore_impl.rs:221–243`) decode `optimized_mir`, `mir_for_ctfe`, `promoted_mir`, `eval_static_initializer`, and ADT layouts **lazily on demand** through `&[u8]` slices backed directly by that `mmap`. Standalone `.rmeta` files take the same `unsafe { Mmap::map(file) }` path inside `get_rmeta_metadata_section` (`locator.rs:934–951`).

### 2. Threat Taxonomy: Inter-Open TOCTOU, Live `MAP_PRIVATE` Mutation, and Split-Brain

`Basis: source + normative + derived`

Inspecting `rustc`'s loader paths exposes four distinct ways unsealed or unverified sysroot reads compromise formal verification soundness:

| Failure Mode | Vulnerable Mechanism & Source Locus | Concrete Attack / Race Trace | Impact on Formal Verification |
| :--- | :--- | :--- | :--- |
| **1. Inter-Open Path TOCTOU (`open_hash` vs. `open_rustc`)** | Verification wrapper hashes `--sysroot` `.rlib`s before spawning `rustc_driver`; `File::open` runs later (`metadata.rs:48`, `locator.rs:936`), and `rustc` writes metadata via `non_durable_rename` (`remove_file` + `rename`, `fs.rs:127–130`). | Concurrent `rustup`, build cache, or sibling job replaces `libcore-<hash>.rlib` between driver pre-hash and `DefaultMetadataLoader`'s `File::open`. | Verified proof receipt binds SHA-256 of clean `libcore.rlib`, while `rustc` captures MIR/layouts from poisoned `.rlib`. |
| **2. Live `MAP_PRIVATE` Page-Cache Mutation & `SIGBUS`** | `Mmap::map` uses `memmap2::MmapOptions::new().map_copy_read_only(&file)` (`memmap.rs:28`, `locator.rs:942`). Comment at `memmap.rs:16–18` warns: *"in practice most callers do not ensure this, so uses of this function are likely unsound."* | On POSIX (`PROT_READ, MAP_PRIVATE`), clean pages share the kernel page cache without copy-on-write snapshotting. A concurrent writer mutating `libcore.rlib` via `pwrite()` *after* `MetadataBlob::new` (`rmeta/decoder.rs:65`) alters `&[u8]` bytes behind live `LazyArray` tables, violating Rust reference immutability and corrupting decoded MIR/layouts (or raising `SIGBUS` on `ftruncate`). Only `#[cfg(any(miri, target_arch = "wasm32"))]` falls back to eager `file.read_to_end` (`memmap.rs:32–42`). | Silent MIR/type-table corruption *after* header checks, or compiler crash (`SIGBUS`) during verification. |
| **3. Capture-vs-Link `.rmeta`/`.rlib` Split-Brain** | `CrateLocator::extract_lib` prioritizes `.rmeta` over `.rlib` (`locator.rs:536–537`), skips `.rlib` under `only_needs_metadata` (`lines 555–560, 589–592`), and matches crates via 64-bit `Svh` (`line 727`). | Analysis-only capture (`Compilation::Stop` or `--emit=metadata`) reads benign `libcore.rmeta` (skipping `libcore.rlib`), while final binary compilation links a tampered `libcore.rlib` with matching `lib.rmeta` and altered `core.rcgu.o` machine code (`probe_sysroot_toctou.py` Case 3). | Verified MIR semantics match clean `lib.rmeta`, while the linked executable runs unverified `core` machine code! |
| **4. Implicit Prelude & `dlopen` Proc-Macro Escape** | Sysroot crates (`core`, `compiler_builtins`, `alloc`, `std`, `panic_abort`, `proc_macro`) are absent from `Cargo.lock`; `CrateFlavor::Dylib` proc-macros execute native code inside the driver (`locator.rs:433, 551–553`, `rmeta/decoder.rs:108`). | Compromised `libproc_macro.so` or crate proc-macro executes arbitrary in-process code (`dlopen`), tampering with `TyCtxt` or memory before MIR capture completes. | Total TCB bypass inside the capture process unless compilation runs inside an isolated OS sandbox. |

### 3. Hardened Capture Admission Architecture and Sealed Manifest Reconciliation

`Basis: source + derived + execution`

Mitigating all four hazards requires enforcing **kernel-level write exclusion before cryptographic measurement** and **post-analysis crate-source reconciliation**:

| Admission Strategy | Pre-Open TOCTOU Immune? | `MAP_PRIVATE` Mutation Immune? | Covers Linker & `.rlib` Objects? | Host OS Scope & Primary Mechanism |
| :--- | :---: | :---: | :---: | :--- |
| **User-Space Pre-Hash on Writable Path** | No | No | Partial | Portable, **unsound** against concurrent writers or cache eviction. |
| **Custom `Config::file_loader` (`rustc_interface.rs:331, 404`)** | `.rs` only | **No** (`.rlib` bypasses `FileLoader` via `metadata.rs:48`) | No | `RealFileLoader` covers source `.rs` ingestion; `DefaultMetadataLoader` and `ld` bypass it entirely. |
| **Private Staging + `bwrap --unshare-all --ro-bind`** | **Yes** | **Yes** | **Yes** | Linux user namespaces (`joshlf/anneal` Pass-2 `trusted/audit/src/lib.rs:68–73, 2298–2310`): stream-hash into private staging, mount `--ro-bind`, block network/host writes. |
| **Linux `memfd_create` + `F_ADD_SEALS`** | **Yes** | **Yes** (VFS blocks writes & waits for pins) | When passed via `/proc/self/fd` | `torvalds/linux` `mm/memfd.c:239–318`: `F_SEAL_SHRINK \| F_SEAL_GROW \| F_SEAL_WRITE \| F_SEAL_SEAL` calls `mapping_deny_writable` and `memfd_wait_for_pins`. |
| **Linux `fs-verity` (`FS_IOC_ENABLE_VERITY`)** | **Yes** | **Yes** (Merkle check per backing read) | **Yes** | `torvalds/linux` `fs/verity/enable.c:334–419`: requires `O_RDONLY` fd, invokes `deny_write_access` (`-ETXTBSY` if any write FD open), hashes Merkle tree into inode; note `lines 396–410` intentionally leave pre-existing clean pagecache pages intact after `enable_verity`. |

**Mandatory Two-Step Capture Protocol:**
1. **Immutable Substrate Admission:** Stage the entire target sysroot (or verify a read-only Nix `/nix/store` / `bwrap --ro-bind` tree with `follow_links(false)` rejecting symlinks inside `lib/rustlib`, mirroring `verify_sysroot_foundation_dir` in `joshlf/anneal` `trusted/audit/src/lib.rs:1647–1710`), compute `sha256` over every `.rlib`/`.rmeta`/`.so` regular file *after* write access is revoked, and seal `memfd`s or enter the `bwrap --ro-bind` namespace before spawning `rustc_driver`.
2. **Post-Analysis `tcx.used_crate_source` Reconciliation:** Inside `Callbacks::after_analysis`, after `tcx.dcx().has_errors().is_none()`, iterate over every `cnum` in `tcx.crates(())`, read `tcx.used_crate_source(cnum)` (`cstore_impl.rs:399` returning `Arc<CrateSource>` with `.rmeta`, `.rlib`, `.dylib`, `.sdylib_interface`), verify **every** non-`None` path resolves inside the sealed sysroot/artifact manifest with matching SHA-256 (requiring `.rlib` presence whenever native linking occurs, defeating `.rmeta`/`.rlib` split-brain), and record `(crate_name, svh, flavor_paths, sha256)` into the verification receipt.

#### Executable `.rlib` Parser & Pass-1-Compatible Lean 4 Admission Model

We verified the GNU `ar` `.rlib` layout (`!<arch>\n`, 60-byte headers, `"lib.rmeta"`, `*.rcgu.o`, even-byte `\n` padding) and all TOCTOU / split-brain rejection paths using a standalone pure-Python 3 probe (`/tmp/probe_sysroot_toctou.py`, `exit 0`). Below is a self-contained Pass-1-compatible (`prelude` + `Init.*`, zero `sorry`, zero `Classical.choice`) Lean 4 (`v4.34.1`) formalization proving that sealed read-only substrate enforcement plus dual `rmeta`/`rlib` digest checking excludes both concurrent `mmap` tampering and split-brain attacks:

```lean
-- Self-contained Pass-1-compatible Lean 4 (v4.34.1) sysroot admission model
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace SysrootProvenanceToctou

inductive MountPerm where
  | writable
  | roSealed

structure ArtifactState where
  rmetaDigest : Nat
  rlibDigest  : Nat
  mountPerm   : MountPerm

structure CapturePolicy where
  expectedRmeta : Nat
  expectedRlib  : Nat
  requireFullRlib : Bool

def admitAndVerify (preCheck : ArtifactState) (atMmapAndLink : ArtifactState) (pol : CapturePolicy) : Bool :=
  let preOk := Nat.beq preCheck.rlibDigest pol.expectedRlib &&
               Nat.beq preCheck.rmetaDigest pol.expectedRmeta
  let sealedOk := match atMmapAndLink.mountPerm with
    | .roSealed => true
    | .writable => false
  let postOk := Nat.beq atMmapAndLink.rmetaDigest pol.expectedRmeta &&
                (!pol.requireFullRlib || Nat.beq atMmapAndLink.rlibDigest pol.expectedRlib)
  preOk && sealedOk && postOk

/-- Kernel read-only sealing prevents concurrent mutation between pre-check and mmap/link. -/
def fsInvariant (pre post : ArtifactState) : Prop :=
  pre.mountPerm = .roSealed → post = pre

theorem sealed_admission_sound (pre post : ArtifactState) (pol : CapturePolicy)
    (hFs : fsInvariant pre post)
    (hRequireRlib : pol.requireFullRlib = true)
    (hAdmit : admitAndVerify pre post pol = true) :
    post.rmetaDigest = pol.expectedRmeta ∧ post.rlibDigest = pol.expectedRlib := by
  unfold admitAndVerify at hAdmit
  cases hPerm : post.mountPerm with
  | writable =>
    rw [hPerm] at hAdmit
    simp at hAdmit
  | roSealed =>
    rw [hPerm] at hAdmit
    rw [hRequireRlib] at hAdmit
    cases hRm : Nat.beq post.rmetaDigest pol.expectedRmeta with
    | false => rw [hRm] at hAdmit; simp at hAdmit
    | true  =>
      cases hRl : Nat.beq post.rlibDigest pol.expectedRlib with
      | false => rw [hRm, hRl] at hAdmit; simp at hAdmit
      | true  => exact ⟨Nat.eq_of_beq_eq_true hRm, Nat.eq_of_beq_eq_true hRl⟩

/-- Witness 1: Writable mount allows pwrite after pre-check, rejected by `roSealed` requirement. -/
theorem writable_mount_attack_rejected :
    let pre  := ArtifactState.mk 100 200 .writable
    let post := ArtifactState.mk 999 888 .writable
    let pol  := CapturePolicy.mk 100 200 true
    admitAndVerify pre post pol = false := rfl

/-- Witness 2: Metadata-only capture misses `.rlib` `.rcgu.o` tampering unless `requireFullRlib = true`. -/
theorem rmeta_only_split_brain_caught :
    let sealed := ArtifactState.mk 100 666 .roSealed
    admitAndVerify sealed sealed (CapturePolicy.mk 100 200 false) = true ∧
    admitAndVerify sealed sealed (CapturePolicy.mk 100 200 true)  = false := ⟨rfl, rfl⟩

end SysrootProvenanceToctou
```

### 4. Reproducible Sysroot Builds (`-Zbuild-std`, `--remap-path-prefix`, and Archive Determinism)

`Basis: source + documentation + derived`

When verifiers cannot consume prebuilt rustup `.rlib`s (for instance, when enabling MIR-for-all-crates or custom panic strategies via `-Zbuild-std=panic_abort,core,std` as in `model-checking/kani`), Lamb & Zacchiroli (*Reproducible Builds: Increasing the Integrity of Software Supply Chains*, IEEE Software 2021, DOI `10.1109/MS.2021.3073045`) and `rust-lang/rust` source reveal **five independent sources of sysroot build non-determinism**:

1. **Three-Root Path Leakage into `lib.rmeta` & DWARF:** Compiling `core`, `alloc`, and `std` embeds file paths from three distinct directory trees: (a) the invoking workspace root, (b) `$CARGO_HOME/registry/src/...` (for `compiler_builtins`, `cfg-if`, `libc`, `hashbrown`, etc.), and (c) `<sysroot>/lib/rustlib/src/rust/library/` (`rust-src`). Every build must supply distinct `--remap-path-prefix` flags (`rustc_session/src/config.rs:2384–2407`) mapping all three roots to canonical virtual prefixes (e.g., `/build/ws`, `/build/cargo`, `/build/rust-src`) plus `-Zremap-cwd-prefix` if relative working-directory paths appear.
2. **`--remap-path-scope` Must Include Metadata Scopes (`config.rs:1311–1340, 1425`):** `rustc` splits path remapping across six `RemapPathScopeComponents` flags: `macro`, `diagnostics`, `documentation` (unstable), `debuginfo`, `coverage`, and `object`, defaulting to `RemapPathScopeComponents::all()` (`line 1425`). Passing `--remap-path-scope=debuginfo` alone leaves unremapped host paths inside `lib.rmeta` `SourceMap` entries (`MACRO` and `DIAGNOSTICS` scopes), breaking bit-for-bit `.rlib` reproducibility across hosts.
3. **`-C metadata` & `RUSTFLAGS` Salting (`StableCrateId` / `Svh`):** Cargo derives `-C metadata` and `-C extra-filename` hashes from target triple, profile, Cargo feature sets, and serialized `RUSTFLAGS` paths; unremapped paths passed inside flags alter `Svh` (`locator.rs:727`) and symbol mangling hashes across machines.
4. **Parallel Codegen Unit (`CGU`) & Incremental Non-Determinism:** `CARGO_INCREMENTAL=1` injects host-dependent work-product metadata, while multi-CGU parallel LLVM emission can vary archive member ordering unless `CARGO_INCREMENTAL=0` and `-C codegen-units=1` (or deterministic sorted CGU names) are enforced.
5. **GNU `ar` Member Timestamps and Ownership (`probe_sysroot_toctou.py`):** Non-deterministic `ar` headers embed build UID/GID and wall-clock timestamps; deterministic `-D` (`SOURCE_DATE_EPOCH`, `uid=0`, `gid=0`, `mtime=0`, `mode=100644`) is required for identical `lib*.rlib` SHA-256 digests, matching SLSA v1.0 / in-toto provenance attestations tying `git` source commits + `Cargo.lock` + `rustc` digest to exact `.rlib` outputs.

### 5. Verification-Boundary Comparison Across Rust Verification Toolchains

`Basis: source`

Inspecting five contemporary Rust verification systems at pinned upstream commits exposes wide variance in how sysroot `.rlib`/`.rmeta` artifacts are provisioned, trusted, and authenticated:

| Verifier & Pinned Revision | Sysroot Provisioning Strategy | Runtime Auth Before MIR Use | TOCTOU / `mmap` / Split-Brain Posture | Observed Source Evidence |
| :--- | :--- | :--- | :--- | :--- |
| **`joshlf/anneal`** (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | Nix fixed-output derivation pins `rust-toolchain` (`rustSha256`) + Lean `foundation-lock.json` (`lean-toolchain` v4.34.1) into `omnibus-archive` (`patchelf` RPATH `$ORIGIN/../rust/lib`); Pass-2 Lean audit runs inside `bwrap --unshare-all`. | `rustc-capture` checks `rustc_version_str() == COMPILER_VERSION` (`1.98.0-nightly (f8a08b688 2026-05-30)`) and `lib/rustlib` dir existence; Lean audit checks SHA-256 of every `Init`/`Std`/`Lean` `.olean*` via `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256` inside `bwrap`. | **Strong on Lean sysroot** (`verify_sysroot_foundation_dir` + `bwrap` ro-binds); **gap on Rust `--sysroot` at capture runtime** (allows unhashed `--sysroot` override without per-`.rlib` SHA-256 or `used_crate_source` reconciliation). | `flake.nix:23–44, 123–174, 204–226, 259–337`; `trusted/rustc-capture/src/driver.rs:25, 45–73`; `trusted/audit/src/lib.rs:68–73, 133–143, 1627–1710, 2298–2310`. |
| **`model-checking/kani`** (`0601bc57f00a5b7f4d8fb4dd76acd6ec9355227a`) | Invokes Cargo with `-Z build-std=panic_abort,core,std` (`RUSTC=kani-compiler`, `--ignore-global-asm`, `__CARGO_TESTS_ONLY_SRC_ROOT`) and injects `kani_core`. | Consumes Cargo JSON `CompilerArtifact` paths in mutable `target/kani`; `map_kani_artifact` consumes `.rmeta`/`*.kani-metadata` and explicitly **skips `.rlib`** (`call_cargo.rs:547–550`). | Susceptible to mutable `target/` TOCTOU and `.rmeta`-vs-`.rlib` split-brain (`--reachability=None` on deps); no OS read-only sealing or cryptographic manifest lock. | `kani-driver/src/call_cargo.rs:84–139, 200–258, 542–555`; `kani-driver/src/project.rs:125–160`. |
| **`verus-lang/verus`** (`0dab219272ac2353320bd177ebb3929453b90a9e`) | Passes `--extern verus_builtin=.../libverus_builtin.rlib --extern vstd=.../libvstd.rlib` over precompiled rustup sysroot `libcore.rlib` (or `--cfg verus_verify_core` when verifying `core` directly). | Resolves `VerusRoot` paths and `VERUS_Z3_PATH`; relies on serialized `vstd` contracts (`external_fn_specification`) rather than runtime SHA-256 locks on `libcore.rlib`. | Relies on unsealed host filesystem (`rustc` `Mmap::map`) for `libcore.rlib` and `libvstd.rlib`; external `std` functions are trusted axioms outside `vstd` proofs. | `source/rust_verify/src/driver.rs:168–195, 268–298`; `source/rust_verify/src/externs.rs:34–75`. |
| **`AeneasVerif/charon`** (`ab5b6d60f53691bc4edee3b11cc52656c090071d`) | Provisions a full-MIR custom sysroot (`charon print-sysroot` / `--sysroot`) or falls back to Aeneas hand-written Lean/Rocq external stdlib models. | Selects toolchain/sysroot directory by CLI flag or Charon toolchain lookup without cryptographic `.rlib` manifest hashing. | Same unsealed `rustc` `Mmap::map` posture when extracting opaque `core`/`std` MIR; Aeneas external-model drift replaces `.rlib` provenance for hand-modeled APIs. | `charon/src/bin/charon/cli.rs:27–29, 96–105`; `charon/src/bin/charon-driver/main.rs:84–142`. |
| **`creusot-rs/creusot`** (`601d97891bb0bc0b569686cc946ef4980560b5d8`) | Pins Rust channel via `include_str!("../../rust-toolchain")` under `$XDG_DATA_HOME/creusot/toolchains/<channel>` and axiomatizes `core`/`std` via `creusot-std` / `extern_spec!`. | Toolchain directory lookup by version string (`toolchain_dir`), without runtime SHA-256 verification of sysroot `.rlib`s. | Relies on mutable `$XDG_DATA_HOME` toolchain directory and `rustc` `Mmap::map`; trusts `extern_spec!` stdlib contracts. | `creusot-setup/src/lib.rs:84–92`; `cargo-creusot/src/main.rs:4–5, 37–45`. |

## Boundaries

- **`known not to apply` — `rustc_version_str()` / `rustc -vV` authenticating sysroot `.rlib` contents:** Verifying compiler driver version strings checks only `librustc_driver.so`; `--sysroot` overrides or mutated files in `lib/rustlib/<target>/lib` pass version checks cleanly unless hashed directly (`driver.rs:45–73`).
- **`known not to apply` — `MmapOptions::map_copy_read_only` (`MAP_PRIVATE`) protecting against concurrent in-place file mutation:** Clean read-only file mappings still fault in backing inode page-cache updates and raise `SIGBUS` on truncation (`memmap.rs:16–29`).
- **`known not to apply` — `Config::file_loader` intercepting `.rlib` or `.rmeta` loads:** `Config::file_loader` (`rustc_interface.rs:331, 404`) applies only to source files; `DefaultMetadataLoader` (`metadata.rs:48`) and `get_rmeta_metadata_section` (`locator.rs:936`) call `std::fs::File::open` directly.
- **`known not to apply` — `--remap-path-scope=debuginfo` producing bit-identical `.rlib` archives:** Unremapped `DIAGNOSTICS` and `MACRO` spans persist inside `lib.rmeta` unless `--remap-path-scope=all` (`config.rs:1332, 1425`) is active across workspace, `$CARGO_HOME`, and `rust-src`.
- **`unsupported` — Kernel `memfd_create` `F_ADD_SEALS` and `fs-verity` on macOS or Windows:** Host-enforced descriptor sealing and page-fault Merkle verification are Linux-specific (`mm/memfd.c`, `fs/verity/enable.c`); non-Linux hosts require read-only VM/container mounts or Nix store guarantees.
- **`unsupported` — Full foreign `.rlib` MIR verification in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** On `main`, `trusted/rustc-capture/src/driver.rs:79–84, 148–150` reaches `after_analysis` as an extraction scaffold (`"verification not performed"`) and does not yet emit a runtime SHA-256 sysroot manifest.
- **`not examined` — Dynamic linker (`ld.so`) `libc.so.6` TOCTOU outside `bwrap`, physical RAM/DMA bit-flips after `fs-verity` admission, and Windows `.dll.lib` PE import-library determinism:** Left outside this study's boundary.
- **`unknown` — Whether future `rustc_public` (StableMIR) stabilization will provide an FD-pinned or non-`mmap` `MetadataLoader` hook:** Upstream `Config::make_codegen_backend` (`rustc_interface.rs:364`) requires unstable `rustc_private`, and whether `rustc_public` will seal sysroot metadata reads natively remains unstandardized.

## Evidence

| Subject / Source | Exact Coordinates | Role & Verified Fact |
| :--- | :--- | :--- |
| `rust-lang/rust` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `compiler/rustc_data_structures/src/memmap.rs:14–42`; `rustc_codegen_ssa/src/back/metadata.rs:43–126`; `rustc_metadata/src/fs.rs:18, 48–55, 127–130`; `rustc_metadata/src/locator.rs:380–797, 934–951`; `rustc_metadata/src/rmeta/decoder.rs:50–74`; `cstore_impl.rs:238–243, 399`; `rustc_session/src/filesearch.rs:47–58, 189–256`; `rustc_session/src/config.rs:1311–1356, 1425, 2384–2407`; `rustc_interface/src/interface.rs:331, 364, 404` | `source`: `Mmap::map` unsafety warning (`memmap.rs:16–18`), `MetadataLoader` `File::open` bypass of `FileLoader`, `rmeta`-before-`rlib` & `only_needs_metadata` skip (`locator.rs:536–592`), 64-bit `Svh`, `used_crate_source`, and `RemapPathScopeComponents`. |
| `rust-lang/cargo` | `9ae79c984e55ee94ed9642ea101abd3f16f82916`, `Cargo.toml:1–300` | `source`: Workspace layout and `memfd` / `sha2` / `gix` build-system dependencies. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `flake.nix:23–44, 123–174, 204–226, 259–337`; `trusted/rustc-capture/src/driver.rs:25, 45–84, 148–150`; `trusted/audit/src/lib.rs:68–73, 133–143, 1627–1710, 2298–2310` | `source`: Fixed-output Nix `rustSha256`, `foundation-lock.json` checks, `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`, `bwrap --unshare-all` Pass-2 isolation, and `rustc-capture` driver scaffold. |
| `model-checking/kani` | `0601bc57f00a5b7f4d8fb4dd76acd6ec9355227a`, `kani-driver/src/call_cargo.rs:84–139, 200–258, 542–555`; `kani-driver/src/project.rs:125–160` | `source`: `-Z build-std=panic_abort,core,std` sysroot rebuild, `__CARGO_TESTS_ONLY_SRC_ROOT`, and `map_kani_artifact` skipping `.rlib` in favor of `.rmeta`. |
| `verus-lang/verus` | `0dab219272ac2353320bd177ebb3929453b90a9e`, `source/rust_verify/src/driver.rs:168–195, 268–298`; `source/rust_verify/src/externs.rs:34–75` | `source`: `VerusExterns` `--extern` bindings (`libverus_builtin.rlib`, `libvstd.rlib`) and `Vstd::IsCore` mode. |
| `AeneasVerif/charon` & `creusot-rs/creusot` | Charon `ab5b6d60f53691bc4edee3b11cc52656c090071d` (`charon/src/bin/charon/cli.rs:27–29, 96–105`; `charon-driver/main.rs:84–142`); Creusot `601d97891bb0bc0b569686cc946ef4980560b5d8` (`creusot-setup/src/lib.rs:84–92`; `cargo-creusot/src/main.rs:4–5, 37–45`) | `source`: Charon `print-sysroot` / `--sysroot` CLI; Creusot `rust-toolchain` channel pinning under `$XDG_DATA_HOME`. |
| `torvalds/linux` | `65e4fd942f72a9dba0e4e257290c4fa1aa756854`, `mm/memfd.c:232–345`; `fs/verity/enable.c:230–420` | `source`: `memfd_add_seals` (`mapping_deny_writable`, `memfd_wait_for_pins`) and `fsverity_ioctl_enable` (`O_RDONLY` + `deny_write_access` + pagecache retention note `lines 396–410`). |
| Supply-Chain Standards & Literature | DOI `10.1109/MS.2021.3073045` (Lamb & Zacchiroli, IEEE Software 2021); SLSA v1.0; in-toto Attestation v1.0 | `documentation`: Reproducible builds threat model (path/timestamp determinism) and cryptographic provenance attestations. |
| Python 3 `.rlib` & TOCTOU Probe | Pure-Python GNU `ar` builder/parser + admission state probe (Python 3.13, `2026-11-20`) | `execution`: Built/parsed deterministic 164-byte `.rlib` (`lib.rmeta` + `.rcgu.o`), verified `REJECT_WRITABLE_SUBSTRATE` under concurrent `pwrite`, and caught split-brain `.rcgu.o` tampering (`exit 0`). |

## Revalidation

1. **Upstream `rustc` Loader & Mmap Diff Check (`< 2s`):** Inspect `compiler/rustc_data_structures/src/memmap.rs`, `compiler/rustc_codegen_ssa/src/back/metadata.rs` (`DefaultMetadataLoader`), and `compiler/rustc_metadata/src/locator.rs` (`extract_lib`, `get_rmeta_metadata_section`) in `rust-lang/rust` to check whether `.rlib`/`.rmeta` loading migrates away from `MmapOptions::map_copy_read_only` or adds sealed file-descriptor pinning.
2. **Anneal Runtime Sysroot Hardening Check (`< 2s`):** Diff `trusted/rustc-capture/src/driver.rs` and `trusted/audit/src/lib.rs` in `joshlf/anneal` to verify whether `rustc-capture` adds `--sysroot` SHA-256 verification and `tcx.used_crate_source` receipt reconciliation matching `verify_sysroot_foundation_dir`.
3. **Standalone Lean 4 (`v4.34.1`) & Reproducible `-Zbuild-std` Checks:**
   - Check the Lean 4 model in **Findings §3** (`lean -DElab.async=false -Ddebug.skipKernelTC=false /tmp/reval_sysroot_toctou.lean`, appending `#print axioms` for `SysrootProvenanceToctou.sealed_admission_sound`, `writable_mount_attack_rejected`, and `rmeta_only_split_brain_caught`; verify exit `0` and zero `sorryAx`).
   - On a host with `rust-src` and nightly `rustc`, compile `-Zbuild-std=core` inside two disjoint directories (`/tmp/repro_a` and `/tmp/repro_b`) with distinct `--remap-path-prefix` maps, `CARGO_INCREMENTAL=0`, `-C codegen-units=1`, and `SOURCE_DATE_EPOCH=0`, and compare `sha256sum` across the resulting `libcore-*.rlib` files.
