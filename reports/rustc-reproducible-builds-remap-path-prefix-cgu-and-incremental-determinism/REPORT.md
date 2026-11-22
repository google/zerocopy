# Bit-Exact Reproducible Compilation in `rustc`: Path Remapping, Parallel Multi-CGU Repeatability, Deterministic Archiving, and the `-C incremental` Bit-Identity Cliff

## Summary

Bit-exact reproducible compilation in `rustc` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, cross-checked against upstream `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) is governed by four separable compiler subsystems whose interactions determine whether cross-directory, parallel, and incremental builds produce identical `.rmeta`, `.o`, `.rlib`, and linked ELF artifacts:

1. **Path remapping (`FilePathMapping` and `RealFileName`) is necessary and sufficient for cross-directory bit-exactness of clean builds, provided the full `all` scope is active.** Without remapping, compiling an identical crate from two directories of unequal length (`dir_alpha` vs. `dir_beta`) leaks raw checkout paths in three places inside `lib.rmeta` (`InnerRealFileName.{name, working_directory, embeddable_name}`), one place inside `.rcgu.o` at `-C debuginfo=0` (NUL-terminated `#[track_caller]` `Location::file()` in `.rodata.str1.1`, giving `4` `.rlib` leaks total), and five places inside `.rcgu.o` at `-C debuginfo=2` (`1` `.rodata.str1.1` + `2` `.debug_str` referenced by `DW_AT_comp_dir`/`DW_AT_name` + `2` `.llvmbc` embedded bitcode debug metadata, giving `8` `.rlib` leaks total). Applying `--remap-path-prefix=<dir>=/repro` with the default `--remap-path-scope=all` eliminates `100%` of raw path leaks across `.rmeta`, `.o`, `.rlib`, and linked ELF binaries (`4,381,272 B`, identical SHA-256 and runtime stdout). Narrowing to `--remap-path-scope=object` produces bit-exact `.o` files (`0` leaks) while still breaking `.rmeta` and `.rlib` cross-directory bit-exactness (`3` leaks retained in `RealFileName.local` because `RealFileName::update_for_crate_metadata` strips `local` only when `was_fully_remapped() || was_not_remapped()`). Adding `-Z remap-cwd-prefix=/repro` changes the `lib.rmeta` digest relative to `--remap-path-prefix` alone while leaving `.o` bytes identical, because `remap_path_prefix` is `[TRACKED_NO_CRATE_HASH]` whereas `remap_cwd_prefix` is `[TRACKED]` (entering the crate hash).
2. **Non-incremental parallel multi-CGU compilation (`-C codegen-units=16 -Z threads=4`) is bit-for-bit repeatable across repeated runs and identical to single-threaded execution (`-Z threads=1`).** Although backend worker threads append completed modules in nondeterministic completion order, `OngoingCodegen::join` deterministically sorts `compiled_modules.modules` by CGU name before archive construction, and `ArArchiveBuilder::build_inner` hardcodes zeroed archive metadata (`mtime = 0`, `uid = 0`, `gid = 0`, `perms = 0o644`). Across `4` repeated runs each of `cgu1_t1`, `cgu16_t1` (`6` CGUs), and `cgu16_t4` (`6` CGUs), all `4` runs yield `1` unique SHA-256 for `.rmeta`, `.o` bundle, and `.rlib`, and `cgu16_t1` matches `cgu16_t4` byte-for-byte (`37,138 B`).
3. **Enabling `-C incremental` introduces a two-mechanism bit-identity cliff that breaks raw `.rlib` hashing in two distinct ways.** First, clean vs. cold-incremental builds diverge in `.rmeta`, `.rcgu.o` code bytes, CGU count, and `.rlib` size because `incremental.is_some()` (a) disables the MIR `Inline` pass at default `mir_opt_level() == 2` under `-C opt-level=2|3` (`rustc_mir_transform/src/inline.rs`), (b) switches CGU naming from size-ordered numbered names (`-cgu.0`) to 25-character base-36 SipHash-128 module hashes (`CodegenUnit::mangle_name`), and (c) alters CGU partitioning (`7` CGUs vs. `6` under `-C codegen-units=16`). Second, cold vs. warm incremental builds of unmodified source produce **bit-identical `lib.rmeta`, bit-identical `.rcgu.o` object payloads, and identical `.rlib` byte lengths** (`17,984 B` for 1 CGU; `40,784 B` for 7 CGUs), yet **strictly unequal `.rlib` SHA-256 digests**. The entire byte difference equals `2 * M * d_H(s_1, s_2)` (up to `14 * M` bytes for `M` CGUs), where `s_1, s_2` are per-invocation random 7-character base-36 `OutputFilenames.invocation_temp` tokens (`rng().next_u32().to_base_fixed_len(36)`) written verbatim into both the GNU `ar` extended filename table (`//`) and the `lib.rmeta-link` `.rmeta-link` section (`RmetaLink.rust_object_files`).
4. **For proof-carrying compilation, Diverse Double-Compiling (DDC), and Anneal's trusted boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), raw `.rlib` digests are sound cache keys only for non-incremental builds with full-scope path remapping.** If `-C incremental` is active, verification and build caches must either disable incremental mode for certified builds or normalize `.rlib` archives by erasing session-varying member basenames (`//` and `lib.rmeta-link`) while hashing `(lib.rmeta, sorted .rcgu.o payloads)` directly. All four invariants and four constructive counterexamples are mechanized in a standalone, axiom-minimal Lean `v4.34.1` proof module (`support/ReproducibleBuildDeterminismSoundness.lean`, `35` theorems, `0` `sorry`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`).

## Applicability

This report characterizes the combination of five pinned, independently resolvable artifacts recorded in `REPORT.json`:

- **Executed compiler toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with `LLVM 22.1.6` targeting `x86_64-unknown-linux-gnu`. All empirical measurements (`support/reproducible_builds_probe.json`), ELF section inspections (`readelf`), `ar` archive parses, and binary executions were acquired directly against this compiler on `2026-11-22`.
- **Upstream compiler source cross-check (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):** Direct source inspection on `2026-11-22` verifying continuity and recording exact structural deltas relative to `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
- **Trusted verification boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Direct source inspection of `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`, `trusted/lean/foundation-lock.json`, and `trusted/rustc-capture/src/driver.rs` to establish how `rustc` determinism interacts with Anneal's SHA-256 authentication discipline, compiler-version pinning, and proof-carrying cache reuse.
- **Mechanization kernel (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Kernel verification of `support/ReproducibleBuildDeterminismSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.
- **Archive tool (`GNU ar`, GNU Binutils 2.47):** Host binutils environment alongside `rustc`'s internal `ar_archive_writer` crate (GNU/SVR4 `!<arch>\n` format).

### Shared vs. Version-Specific Behavior (`14210df0e` vs. `342d74463`)

Basis: source

Direct line-by-line comparison across all 19 inspected compiler source files establishes both shared architectural invariants and concrete version-specific differences between `14210df0e` (May 2026) and `342d74463` (November 2026):

| Subsystem / File | Shared Invariant Across Both Revisions | Concrete Delta (`14210df0e` -> `342d74463`) |
| :--- | :--- | :--- |
| `rustc_span/src/source_map.rs` | `FilePathMapping::map_prefix` applies rules in reverse CLI order (`mapping.iter().rev()`); `to_real_filename` retains `local: Some(...)` during compilation. | Line offset shifts (`1121` -> `1123`); core prefix-stripping and `to_real_filename` semantics unchanged. |
| `rustc_span/src/lib.rs` | `RealFileName::update_for_crate_metadata` clears `self.local = None` iff `was_fully_remapped() \|\| was_not_remapped()`. | Struct/method definitions shifted by `+4` lines (`304..484` -> `308..488`); logic identical. |
| `rustc_session/src/config.rs` | `remap_path_prefix` is `[TRACKED_NO_CRATE_HASH]`, `remap_cwd_prefix` is `[TRACKED]`; `temp_path_ext_for_cgu` appends `.{invocation_temp}` before `.rcgu.{ext}`. | **Material fix (`rust-lang/rust#132132`):** In `14210df0e:2399-2405`, `parse_remap_path_prefix` pushed `(current_dir(), to)` into `opts.remap_path_prefix` (leaking absolute `cwd` into the tracked option used by incremental fingerprinting). In `342d74463:1490-1507`, `file_path_mapping` applies `remap_cwd_prefix` on the fly so absolute `cwd` is never stored in `opts.remap_path_prefix`. |
| `rustc_mir_transform/src/inline.rs` | At default `mir_opt_level() == 2` and `OptLevel::More \| Aggressive`, MIR `Inline` is disabled whenever `incremental.is_some()`. | Refactored from `fn is_enabled` (`14210df0e:46-59`, `sess.opts.incremental == None` at L55) to `PassPolicy::optional` (`342d74463:50-58`, `ctx.opts.incremental.is_none()` at L58). |
| `rustc_monomorphize/src/partitioning.rs` | Non-incremental builds merge tiny CGUs (`incremental.is_none()`) and assign zero-padded numeric names (`-cgu.0`) reverse-sorted by size; incremental builds retain volatile/non-volatile splits and 25-char base-36 SipHash-128 CGU names (`mangle_name`). | Minor line shifts (`465` -> `472`, `663` -> `678`); partitioning and naming rules identical. |
| `rustc_codegen_ssa/src/back/write.rs` | `OngoingCodegen::join` sorts `compiled_modules.modules.sort_by(\|a, b\| a.name.cmp(&b.name))` after parallel workers complete. | `14210df0e:2181` -> `342d74463:2207`; incremental work-product copying moved inside `catch_fatal_errors` (`342d74463:2138-2144`) before the sort, while final `produce_final_output_artifacts` and returned `CompiledModules` remain sorted. |
| `rustc_codegen_ssa/src/back/archive.rs` & `link.rs` | `ArArchiveBuilder::build_inner` sets `mtime: 0, uid: 0, gid: 0, perms: 0o644`; `link_rlib` emits `lib.rmeta`, `lib.rmeta-link` (listing `.rcgu.o` basenames), then `.rcgu.o` members in `compiled_modules.modules` order. | `342d74463` adds `ArchiveEntryKind` tagging (`archive.rs:396`, `link.rs:593-620`) and extends `RmetaLink` with `native_lib_filenames` (`link.rs:572`); `NewArchiveMember` zeroed header fields shift `576-584` -> `677-685`. |
| `rustc_interface/src/util.rs` | `build_output_filenames` computes `invocation_temp = sess.opts.incremental.as_ref().map(\|_\| rng().next_u32().to_base_fixed_len(CASE_INSENSITIVE).to_string())`. | Shifted `621-625` -> `686-690`; exact same 32-bit random base-36 7-character token generation. |

### Execution Environment Scope

Empirical execution findings directly apply to `rustc 1.98.0-nightly (14210df0e 2026-05-31)` on `x86_64-unknown-linux-gnu` using Rust 2024 edition (`--edition=2024`), `-C opt-level=2`, GNU/SVR4 `ar` `.rlib` format, ELF64 relocatable objects and dynamically linked Linux executables (`LC_ALL=C`, `TZ=UTC`), and single-crate / two-crate builds without procedural macros, `build.rs` scripts, or ThinLTO/FatLTO. Extending conclusions to other host OSes, archive formats (BSD/Mach-O, COFF), or non-default linker pipelines requires the checks noted under **Boundaries** and **Revalidation**.

## Findings

### 1. Path Representation, Remapping Precedence, and Metadata Erasure (`FilePathMapping` and `RealFileName`)

Basis: source + execution

#### 1.1 Internal Representation and Reverse-Precedence Prefix Stripping

`rustc` represents on-disk source paths via `RealFileName` (`compiler/rustc_span/src/lib.rs:304-324` in `14210df0e`; `308-328` in `342d74463`), which stores *two* `InnerRealFileName` triples alongside a `RemapPathScopeComponents` bitmask:

```rust
pub struct RealFileName {
    local: Option<InnerRealFileName>,
    maybe_remapped: InnerRealFileName,
    scopes: RemapPathScopeComponents,
}

struct InnerRealFileName {
    name: PathBuf,
    working_directory: PathBuf,
    embeddable_name: PathBuf,
}
```

Every `InnerRealFileName` carries three distinct `PathBuf` slots:
1. `name`: the path as passed to the compiler (absolute or relative, remapped if matched),
2. `working_directory`: the compiler working directory (remapped if matched),
3. `embeddable_name`: an absolute (or remapped) path formed by joining `working_directory` and `name` when `name` is relative.

`FilePathMapping::map_prefix` (`compiler/rustc_span/src/source_map.rs:1141-1179` in `14210df0e`) applies `--remap-path-prefix=FROM=TO` rules in **reverse command-line order** (`for (from, to) in mapping.iter().rev()` at line `1159`), stopping at the first `path.strip_prefix(from)` match. Later CLI flags therefore override earlier ones. An exact directory match (`rest.as_os_str().is_empty()`) returns `to` directly without calling `Path::join` to avoid trailing separator duplication (`source_map.rs:1163-1173`).

When `SourceMap::to_real_filename` constructs a `RealFileName` (`source_map.rs:1193-1252`), it **always** populates `local: Some(...)` with the unremapped host paths so that compiler passes reading files from disk continue to function. The active scope bitmask (`RemapPathScopeComponents`, `rustc_span/src/lib.rs:239-254`) has five bits plus one composite alias:

- `MACRO = 1 << 0` (`file!()`, `#[track_caller]` `Location::file()`),
- `DIAGNOSTICS = 1 << 1` (error/warning output),
- `DEBUGINFO = 1 << 3` (DWARF/CodeView/embedded bitcode `DIFile` & `DW_AT_comp_dir`),
- `COVERAGE = 1 << 4` (coverage maps),
- `DOCUMENTATION = 1 << 5` (rustdoc, unstable),
- `OBJECT = MACRO | DEBUGINFO | COVERAGE` (omits `DIAGNOSTICS` and `DOCUMENTATION`).

When `--remap-path-scope` is omitted, `parse_remap_path_scope` (`compiler/rustc_session/src/config.rs:1311-1340` in `14210df0e`; `1426-1455` in `342d74463`) defaults to `RemapPathScopeComponents::all()`.

#### 1.2 The Four Concrete Leak Channels and Why `update_for_crate_metadata` Traps `--remap-path-scope=object`

Source inspection identifies four distinct output sites where host checkout paths enter compiled artifacts:

1. **Crate metadata (`lib.rmeta`, 3 occurrences per unremapped `SourceFile`):** `Encoder::encode_source_map` (`compiler/rustc_metadata/src/rmeta/encoder.rs:538-578` in `14210df0e`; `570-613` in `342d74463`) clones each required `SourceFile` and calls `RealFileName::update_for_crate_metadata()` (`rustc_span/src/lib.rs:476-484` in `14210df0e`; `480-488` in `342d74463`):
   ```rust
   pub fn update_for_crate_metadata(&mut self) {
       if self.was_fully_remapped() || self.was_not_remapped() {
           self.local = None;
       }
   }
   ```
   - When unremapped (`scopes.is_empty()`), `self.local` is dropped, leaving `self.maybe_remapped.{name, working_directory, embeddable_name}` — all `3` containing the raw directory path.
   - When fully remapped (`scopes.is_all()`, the default), `self.local` is dropped and all `3` fields of `maybe_remapped` hold `/repro/...` (`0` leaks).
   - **Critical scope trap (`--remap-path-scope=object`):** When `scopes == OBJECT`, `was_fully_remapped()` is `false` and `was_not_remapped()` is `false`. Consequently, `update_for_crate_metadata()` **does not clear `self.local`**, serializing all `3` raw host paths inside `lib.rmeta` even though the `.o` object file has `0` leaks!
2. **`#[track_caller]` / `Location::file()` and `file!()` (`.rodata.str1.1`, 1 occurrence per distinct call-site file):** `TyCtxt::span_as_caller_location` (`compiler/rustc_middle/src/mir/consts.rs:515-525` in `14210df0e`; `533-543` in `342d74463`) queries `caller.file.name.display(RemapPathScopeComponents::MACRO)` (matching `expand_file` in `compiler/rustc_builtin_macros/src/source_util.rs:60-76`) and passes the resulting `Symbol` to `alloc_caller_location` (`compiler/rustc_const_eval/src/util/caller_location.rs:12-54`), which allocates `filename.to_owned() + "\0"` as a deduplicated constant in `.rodata`. Thus even at `-C debuginfo=0`, any non-inlined function invoking a `#[track_caller]` callee embeds the unremapped path directly into machine object code. (Note that trivial `pub fn` items lacking `#[inline(never)]` may be exported only as MIR in `lib.rmeta` rather than codegenned into `.o`, shifting `file!()` leaks from `.o` into `.rmeta`.)
3. **DWARF compilation-unit and file metadata (`.debug_str`, 2 occurrences at `-C debuginfo=2`):** `compile_unit_metadata` (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:865-936` in `14210df0e`; `920-990` in `342d74463`) populates `DW_AT_comp_dir` from `work_dir.path(RemapPathScopeComponents::DEBUGINFO)` and `DW_AT_name` from `local_crate_source_file().map(|src| src.path(RemapPathScopeComponents::DEBUGINFO))` (with the CGU name appended to ensure unique DWO IDs under Split DWARF, issue `#88521`). `file_metadata` (`metadata.rs:551-621` in `14210df0e`; `565-625` in `342d74463`) calls `filename.embeddable_name(RemapPathScopeComponents::DEBUGINFO)` and splits relative paths against `working_directory`.
4. **Embedded LLVM bitcode (`.llvmbc`, 2 occurrences at `-C debuginfo=2`):** Because `need_bitcode_in_object` (`compiler/rustc_codegen_ssa/src/back/write.rs:398-403`) enables embedded bitcode by default for `rlib` crates (`embed_bitcode = true`), LLVM serializes the module's IR — including its `DIFile` directory and filename strings — into the `.llvmbc` section of `.rcgu.o`. At `-C debuginfo=0`, no `DIFile` metadata is attached to the bitcode (`0` `.llvmbc` leaks); at `-C debuginfo=2`, `.llvmbc` contributes `2` additional raw path leaks on top of `.debug_str` (`2`) and `.rodata.str1.1` (`1`), explaining the exact `5`-leak total inside `.o` and `8`-leak total inside `.rlib`.

#### 1.3 Empirical 9-Mode Cross-Directory Matrix (`dir_alpha` vs. `dir_beta`)

Compiling the same `repro_lib` crate (`--edition=2024 --crate-type=rlib --emit=metadata,obj,link -C opt-level=2 -C codegen-units=1`) inside distinct directories of unequal length (`dir_alpha`, 9 chars, vs. `dir_beta`, 8 chars) on `rustc 1.98.0-nightly (14210df0e)` via `support/probe_reproducible_builds.py` yields:

| Mode | Debug | Remap Flags | Scope | Src Arg | Bit-Exact (`rmeta`/`obj`/`rlib`) | Leaks `alpha` (`rmeta`/`obj`/`rlib`) | Size `alpha` (`rmeta`/`obj`/`rlib` B) | SHA-256 Prefix `alpha` (`rmeta` / `obj` / `rlib`) |
| :--- | :---: | :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| `dbg0_no_remap` | `0` | none | `all` | abs | `F / F / F` | `3 / 1 / 4` | `6,681 / 9,368 / 18,224` | `6cd73f53` / `0cddd57f` / `8beb16fe` |
| `dbg0_remap_path` | `0` | `--remap-path-prefix=<dir>=/repro` | `all` | abs | `T / T / T` | `0 / 0 / 0` | `6,576 / 9,304 / 18,048` | `4ad70d13` / `4ba030a4` / `62a655b6` |
| `dbg0_remap_path_and_cwd` | `0` | `--remap-path-prefix` + `-Z remap-cwd-prefix=/repro` | `all` | abs | `T / T / T` | `0 / 0 / 0` | `6,576 / 9,304 / 18,048` | `f1ee8ccb` / `4ba030a4` / `9889ddf0` |
| `dbg0_remap_cwd_only_abssrc` | `0` | `-Z remap-cwd-prefix=/repro` | `all` | abs | `T / T / T` | `0 / 0 / 0` | `6,576 / 9,304 / 18,048` | `f1ee8ccb` / `4ba030a4` / `9889ddf0` |
| `dbg0_remap_cwd_only_relsrc` | `0` | `-Z remap-cwd-prefix=/repro` | `all` | rel | `T / T / T` | `0 / 0 / 0` | `6,569 / 9,280 / 18,024` | `603c1514` / `56a50986` / `29946e76` |
| `dbg2_no_remap` | `2` | none | `all` | abs | `F / F / F` | `3 / 5 / 8` | `7,210 / 32,200 / 41,584` | `d4418b56` / `0bd75e58` / `ccf65716` |
| `dbg2_remap_path_only` | `2` | `--remap-path-prefix=<dir>=/repro` | `all` | abs | `T / T / T` | `0 / 0 / 0` | `7,105 / 31,984 / 41,264` | `b51b843b` / `b0e8c4a5` / `5bf72eaa` |
| `dbg2_remap_path_and_cwd` | `2` | `--remap-path-prefix` + `-Z remap-cwd-prefix=/repro` | `all` | abs | `T / T / T` | `0 / 0 / 0` | `7,105 / 31,984 / 41,264` | `813c7339` / `b0e8c4a5` / `e342b254` |
| `dbg2_remap_scope_object` | `2` | `--remap-path-prefix=<dir>=/repro` | `object` | abs | `F / T / F` | `3 / 0 / 3` | `7,248 / 31,984 / 41,400` | `788c5044` / `b0e8c4a5` / `0011207e` |

Exact ELF section breakdown (`readelf -S -W` + byte-offset mapping) for the unremapped `.o` artifacts:
- `dbg0_no_remap` (`1` `.o` leak): `{".rodata.str1.1": 1}`, `DW_AT_comp_dir: 0`, `DW_AT_name: 0`.
- `dbg2_no_remap` (`5` `.o` leaks): `{".rodata.str1.1": 1, ".debug_str": 2, ".llvmbc": 2}`, with `readelf --debug-dump=info` showing `DW_AT_comp_dir: 1` and `DW_AT_name: 1`.

#### 1.4 Why `-Z remap-cwd-prefix` Changes `lib.rmeta` While Leaving `.o` Bit-Identical

Notice two subtle cross-mode equalities in the table above:
1. At both `-C debuginfo=0` and `-C debuginfo=2`, `--remap-path-prefix=<dir>=/repro` alone and `--remap-path-prefix=<dir>=/repro -Z remap-cwd-prefix=/repro` produce **bit-identical `.o` objects** (`4ba030a4f6140e55...` at `dbg0`; `b0e8c4a53fe033f7...` at `dbg2`), yet **distinct `lib.rmeta` and `.rlib` hashes** (`4ad70d13...` vs. `f1ee8ccb...` at `dbg0`; `b51b843b...` vs. `813c7339...` at `dbg2`).
2. Conversely, `-Z remap-cwd-prefix=/repro` alone (with absolute source path `dbg0_remap_cwd_only_abssrc`) produces the **exact same `rmeta`, `obj`, and `rlib` hashes** as `--remap-path-prefix=<dir>=/repro -Z remap-cwd-prefix=/repro` (`f1ee8ccb...` / `4ba030a4...` / `9889ddf0...`).

Source inspection of `compiler/rustc_session/src/options.rs` explains both observations directly:
- `remap_path_prefix` (`14210df0e:365`, `342d74463:478`) and `remap_path_scope` (`14210df0e:367`, `342d74463:480`) are annotated `[TRACKED_NO_CRATE_HASH]` — they are excluded from the crate's SVH (`CrateHash`) so two builds with different host `<dir>` prefixes in `--remap-path-prefix=<dir>=/repro` hash identically.
- `remap_cwd_prefix` (`14210df0e:2583`, `342d74463:2922`) is annotated `[TRACKED]` — its `Option<PathBuf>` value (`None` vs. `Some("/repro")`) IS folded into the crate hash stored in `lib.rmeta`, altering `lib.rmeta` and `.rlib` whenever toggled, while remaining identical across `dir_alpha` and `dir_beta` because the argument value `/repro` does not depend on `cwd`.
- Between `14210df0e` and `342d74463`, `rust-lang/rust#132132` (`config.rs:1495-1506`) moved the `(current_dir(), to)` expansion out of `parse_remap_path_prefix` into `file_path_mapping(...)` specifically so the raw host `cwd` is never stored inside `opts.remap_path_prefix` (where `[TRACKED_NO_CRATE_HASH]` still participates in incremental session option tracking).

#### 1.5 Cross-Directory Linked ELF Reproducibility

Compiling `repro_lib` (`-C opt-level=2 -C debuginfo=2 -C codegen-units=1 --remap-path-prefix=<dir>=/repro`) and linking `repro_bin` (`--crate-type=bin --extern repro_lib=...`) inside `elf_dir_alpha` and `elf_dir_beta` produces:
- Bit-exact `librepro_lib.rlib` (`e0083a492944aebb0ecc1f08d9261ef8a3e2a3c936d02ef3e66a6519f25a217d`),
- Bit-exact linked ELF executable `repro_bin` (`4,381,272 B`, SHA-256 `193908541773321d8ebc9fdd7cae9b87329fdcfc12285c426e7f49ef39e589df`),
- `0` raw directory leaks in both binaries,
- Identical runtime execution output: `10 30 /repro/main.rs 1729382261405277070` (proving `#[track_caller]` `Location::caller().file()` resolves cleanly to `/repro/main.rs` at runtime).

---

### 2. Parallel Multi-CGU Repeatability (`-C codegen-units=16 -Z threads=4`) and Deterministic `ar` Archive Writing

Basis: source + execution

#### 2.1 Four-Step Determinism Pipeline for Parallel Non-Incremental Codegen

Non-incremental parallel builds achieve schedule-independent bit-exactness through four consecutive canonicalization barriers verified in both `14210df0e` and `342d74463`:

1. **Deterministic intra-CGU item ordering (`compiler/rustc_middle/src/mono.rs:524-594`):** `CodegenUnit::items_in_deterministic_order` sorts all mono-items within each CGU by mangled `SymbolName` (`items.sort_by_cached_key(|&(i, _)| i.symbol_name(tcx))`, line `589`, unless `-Z codegen-source-order` is passed), eliminating `FxHashMap` iteration-order nondeterminism before LLVM IR emission.
2. **Deterministic non-incremental CGU numbering (`compiler/rustc_monomorphize/src/partitioning.rs:465-508`):** When `incremental.is_none()`, `merge_codegen_units` sorts CGUs by `cmp::Reverse(cgu.size_estimate())` and assigns zero-padded sequential names `<crate>.<16-hex-stable-crate-id>-cgu.<N>` (e.g. `repro_lib.repro_lib.6f3d9c231c4892e8-cgu.0.rcgu.o` through `cgu.5.rcgu.o`), ensuring that lexicographic order equals size-descending order.
3. **Post-parallel join canonicalization (`compiler/rustc_codegen_ssa/src/back/write.rs:2178-2181` in `14210df0e`; `2204-2207` in `342d74463`):** During parallel codegen under `-Z threads=N`, worker threads push completed `CompiledModule` values onto `compiled_modules` in arbitrary completion order (`write.rs:1670`/`1678`). Immediately after joining all workers in `OngoingCodegen::join`, `rustc` executes:
   ```rust
   // Regardless of what order these modules completed in, report them to
   // the backend in the same order every time to ensure that we're handing
   // out deterministic results.
   compiled_modules.modules.sort_by(|a, b| a.name.cmp(&b.name));
   ```
   `link_rlib` (`compiler/rustc_codegen_ssa/src/back/link.rs:555-620` in `342d74463`; `315-380` in `14210df0e`) then iterates `&compiled_modules.modules` in that sorted order to populate both `RmetaLink.rust_object_files` and `ArArchiveBuilder::add_file`.
4. **Zero-epoch deterministic archive writing (`compiler/rustc_codegen_ssa/src/back/archive.rs:576-584` in `14210df0e`; `677-685` in `342d74463`):** `ArArchiveBuilder` stores entries in an insertion-order `Vec` (explicitly rejecting `HashMap` at `archive.rs:381`/`390`) and passes every archive member to `ar_archive_writer::write_archive_to_stream` with hardcoded deterministic POSIX metadata:
   ```rust
   entries.push(NewArchiveMember {
       buf: data,
       object_reader: self.object_reader,
       member_name: String::from_utf8(entry_name).unwrap(),
       mtime: 0,
       uid: 0,
       gid: 0,
       perms: 0o644,
   })
   ```
   All timestamps (`mtime = 0`, i.e., `1970-01-01 00:00:00 UTC`), owners (`uid = 0`, `gid = 0`), and permissions (`0644`) are constant, and `write_archive_to_stream` writes to a temporary file before atomic `fs::rename`.

#### 2.2 Empirical 3-Mode × 4-Run Repeatability Sweep

Running `support/probe_reproducible_builds.py` (`probe_2_cgu_and_threads_repeatability`) over the multi-module `repro_lib` crate (`-C opt-level=2 --remap-path-prefix=<dir>=/repro`, `4` independent invocations per configuration) yields:

| Configuration | Requested CGUs | Emitted `.rcgu.o` Members | `-Z threads` | Runs | Unique `.rlib` Hashes | Unique `.rmeta` Hashes | Unique `.o` Bundle Hashes | All `ar` Headers `0/0/644/mtime=0` | `.rlib` Size (B) | `.rlib` SHA-256 Prefix |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `cgu1_t1` | `1` | `1` | `1` | `4` | `1` | `1` | `1` | `true` | `18,048` | `62a655b60fdb458e` |
| `cgu16_t1` | `16` | `6` | `1` | `4` | `1` | `1` | `1` | `true` | `37,138` | `dfa6149d41a6ae69` |
| `cgu16_t4` | `16` | `6` | `4` | `4` | `1` | `1` | `1` | `true` | `37,138` | `dfa6149d41a6ae69` |

Key empirical invariants verified:
- **Zero schedule drift:** `1 / 4` unique SHA-256 across all `4` parallel `-C codegen-units=16 -Z threads=4` runs (`all_bit_exact = true`).
- **Thread-count invariance:** `cgu16_t1` (`-Z threads=1`) and `cgu16_t4` (`-Z threads=4`) produce **bit-for-bit identical** `.rlib` archives (`dfa6149d41a6ae69...`, `37,138 B`) and `lib.rmeta` (`4ad70d132b4603dc...`).
- **Canonical archive structure:** Direct GNU/SVR4 `ar` header parsing confirms all `8` members of `cgu16_t4` (`lib.rmeta`, `lib.rmeta-link`, and `repro_lib.repro_lib.6f3d9c231c4892e8-cgu.{0..5}.rcgu.o`) carry `mtime = 0`, `uid = 0`, `gid = 0`, and `mode_octal = "644"`.

---

### 3. The `-C incremental` Bit-Identity Cliff: Dual Divergence Mechanisms

Basis: source + execution + derived

Enabling `-C incremental=<cache_dir>` breaks raw artifact bit-identity through **two completely distinct mechanisms**, one separating clean builds from incremental builds and the other separating consecutive incremental builds from each other even on a warm cache with zero source edits.

#### 3.1 Mechanism A (Clean vs. Cold Incremental): MIR `Inline` Suppression, CGU Hashing, and Partition Divergence

Three source-level branches gated on `opts.incremental` diverge between clean and incremental compilation:

1. **MIR `Inline` pass disabled (`compiler/rustc_mir_transform/src/inline.rs:45-59` in `14210df0e`; `50-58` in `342d74463`):**
   ```rust
   // 14210df0e:51-57 (identical logic via PassPolicy::optional in 342d74463:50-58)
   match sess.mir_opt_level() {
       0 | 1 => false,
       2 => {
           (sess.opts.optimize == OptLevel::More || sess.opts.optimize == OptLevel::Aggressive)
               && sess.opts.incremental == None
       }
       _ => true,
   }
   ```
   At `-C opt-level=2` or `3` (where default `mir_opt_level()` is `2`), setting `-C incremental` suppresses MIR-level inlining so that cross-function MIR edits do not invalidate wide dependency cones. This changes **both** the optimized MIR serialized in `lib.rmeta` and the LLVM IR / native code size in `.rcgu.o`.
2. **CGU naming and merging (`compiler/rustc_monomorphize/src/partitioning.rs:206, 230, 400, 423-470`):**
   - `is_volatile = is_incremental_build && mono_item.is_generic_fn()` (`partitioning.rs:230`) partitions generic items into separate volatile CGUs only when incremental mode is active.
   - `while cx.tcx.sess.opts.incremental.is_none() ...` (`partitioning.rs:400`) aggressively merges tiny CGUs only in non-incremental builds. Consequently, under `-C codegen-units=16`, our `repro_lib` crate emits **`6` CGUs** non-incrementally vs. **`7` CGUs** incrementally!
   - Instead of `-cgu.0` numbering, incremental builds retain 25-character base-36 SipHash-128 content-hashed CGU names (`CodegenUnit::mangle_name`, `compiler/rustc_middle/src/mono.rs:450-452`, e.g., `repro_lib.2ortto8p3uieo0vcykf62cozd`).
3. **Ablation proof that MIR `Inline` and incremental CGU metadata act independently:**

| Build Variant (`-C opt-level=2`, `--remap-path-prefix=<dir>=/repro`) | CGUs | `.rmeta` (B) | `.rcgu.o` (B) | `.rlib` (B) | `.rmeta` SHA-256 Prefix | `.rcgu.o[0]` SHA-256 Prefix | `.rlib` SHA-256 Prefix |
| :--- | :---: | ---: | ---: | ---: | :--- | :--- | :--- |
| `clean` (`-C cgu=1`) | `1` | `6,576` | `9,304` | `18,048` | `4ad70d132b4603dc` | `4ba030a4f6140e55` | `62a655b60fdb458e` |
| `clean_no_mir_inline` (`-C cgu=1 -Z inline-mir=no`) | `1` | `5,800` | `10,016` | `18,080` | `bbecf4904c2c0714` | `814d521d8fe07632` | `9494914b6d07b9af` |
| `incr_cold` (`-C cgu=1 -C incremental`) | `1` | `5,721` | `9,992` | `17,984` | `f1f509073e20280e` | `d99ff43ae822a39b` | `04bbc9054db4ba33` |
| `incr_force_mir_inline` (`-C cgu=1 -C incremental -Z inline-mir=yes`) | `1` | `5,717` | `9,816` | `17,800` | `539742717897986a` | `de2b83ad81f744e8` | `0da5a461f6ce9f9b` |
| `incr_warm1` (`-C cgu=1 -C incremental`, warm #1) | `1` | `5,721` | `9,992` | `17,984` | `f1f509073e20280e` | `d99ff43ae822a39b` | `6b0519e7c02419e6` |
| `incr_warm2` (`-C cgu=1 -C incremental`, warm #2) | `1` | `5,721` | `9,992` | `17,984` | `f1f509073e20280e` | `d99ff43ae822a39b` | `34a3e4417a81f12e` |
| `incr_cgu16_cold` (`-C cgu=16 -C incremental`, cold) | `7` | `5,721` | `31,808` (sum) | `40,784` | `f1f509073e20280e` | `6444af7cb9e9808d` | `42e3084c7baaf082` |
| `incr_cgu16_warm` (`-C cgu=16 -C incremental`, warm) | `7` | `5,721` | `31,808` (sum) | `40,784` | `f1f509073e20280e` | `6444af7cb9e9808d` | `7aad93994897dd97` |

Ablation isolates both effects cleanly:
- Disabling MIR `Inline` on a clean build (`clean` -> `clean_no_mir_inline`) shrinks `.rmeta` by `776 B` (`6,576 -> 5,800 B`, less inlined MIR body duplication) and grows `.rcgu.o` by `712 B` (`9,304 -> 10,016 B`).
- Conversely, forcing `-Z inline-mir=yes` on an incremental build (`incr_cold` -> `incr_force_mir_inline`) shrinks `.rcgu.o` by `176 B` (`9,992 -> 9,816 B`), yet still does NOT match `clean` (`9,304 B`) because incremental CGU naming/symbol mangling and incremental session metadata independently change `.rmeta` and `.o`.

#### 3.2 Mechanism B (Cold vs. Warm Incremental): Exact Anatomy of the `2 * M * d_H` Byte Diff (`invocation_temp` in `//` and `lib.rmeta-link`)

Source tracing pinpoints the **exact** origin of the non-deterministic 7-character base-36 token inside incremental `.rlib` archives:

1. **Per-invocation random token generation (`compiler/rustc_interface/src/util.rs:621-625` in `14210df0e`; `686-690` in `342d74463`):**
   ```rust
   let invocation_temp = sess
       .opts
       .incremental
       .as_ref()
       .map(|_| rng().next_u32().to_base_fixed_len(CASE_INSENSITIVE).to_string());
   ```
   Because `CASE_INSENSITIVE = 36` (`0-9a-z`) and `36^6 = 2,176,782,336 < 2^32 - 1 = 4,294,967,295 < 36^7 = 78,364,164,096`, `u32::to_base_fixed_len(36)` **always** emits a fixed-length **7-byte** ASCII string in `["0000000", "1z141z3"]`. Note that its leading character is always `'0'` (`~50.7%` probability) or `'1'` (`~49.3%` probability), while the remaining 6 characters vary broadly across base-36.
   *(Note also that `compiler/rustc_incremental/src/persist/fs.rs:448-455` in `14210df0e` / `382-389` in `342d74463` independently draws a separate `rng().next_u32().to_base_fixed_len(CASE_INSENSITIVE)` for the on-disk incremental session directory `s-{timestamp}-{random}-working`, which is kept out of the `.rlib`; it is specifically `OutputFilenames.invocation_temp` that enters `.rlib` member filenames.)*
2. **Injection into every `.rcgu.o` temporary filename (`compiler/rustc_session/src/config.rs:1246-1266` in `14210df0e`; `1361-1381` in `342d74463`):**
   ```rust
   pub fn temp_path_ext_for_cgu(&self, ext: &str, codegen_unit_name: &str) -> PathBuf {
       let mut extension = codegen_unit_name.to_string();
       // Append `.{invocation_temp}` to ensure temporary files are unique.
       if let Some(rng) = &self.invocation_temp {
           extension.push('.');
           extension.push_str(rng);
       }
       ...
   }
   ```
   Every CGU in an incremental invocation therefore receives the **same** 7-byte suffix: `<crate>.<25-char-base36-cgu-hash>.<7-char-invocation_temp>.rcgu.o` (length `> 15` bytes).
3. **Dual serialization into the `.rlib` archive (`compiler/rustc_codegen_ssa/src/back/link.rs:555-620` in `342d74463` and `rmeta_link.rs:14-35`):**
   `link_rlib` extracts `obj.file_name()` and embeds it in **exactly two places** per CGU inside the `.rlib`:
   - **Site 1 — GNU `ar` extended filename table (`//`):** Because the basename exceeds the 15-byte inline GNU `ar` header field, `ar_archive_writer` writes the full basename into the `//` string-table member.
   - **Site 2 — `lib.rmeta-link` (`.rmeta-link` section):** `RmetaLink { rust_object_files, ... }` (`rmeta_link.rs:17-28`) serializes the exact `Vec<String>` of `.rcgu.o` basenames into an object-file wrapper placed immediately after `lib.rmeta`.

**Derived Formula & Exact Empirical Verification:**
For two incremental builds of identical unmodified source with `M` CGUs and invocation tokens `s_1, s_2 ∈ [0-9a-z]^7` having Hamming distance `d_H(s_1, s_2) ∈ [0, 7]`, the two `.rlib` archives have **identical byte length**, **bit-identical `lib.rmeta`**, **bit-identical `.rcgu.o` object payloads**, and differ at **exactly `2 * M * d_H(s_1, s_2)` byte offsets** (bounded above by `14 * M` bytes, split 50/50 between `ar //` and `lib.rmeta-link`).

Every single pair measured by `support/probe_reproducible_builds.py` obeys this formula with zero residual bytes:

| Comparison | `M` (CGUs) | Token A | Token B | `d_H(A, B)` | Measured Diff Bytes | `ar_gnu_strtab(//)` Diff | `lib.rmeta-link` Diff | `lib.rmeta` Equal | All `.rcgu.o` Payloads Equal | `2 * M * d_H` Exact Match |
| :--- | :---: | :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `incr_cold` vs. `incr_warm1` | `1` | `09w14lc` | `0sbhbf5` | `6` | **`12`** | `6` (`869..874`) | `6` (`7427..7432`) | `true` | `true` (`d99ff43a...`) | `true` (`2*1*6 = 12`) |
| `incr_cold` vs. `incr_warm2` | `1` | `09w14lc` | `1s0llzm` | `7` | **`14`** | `7` (`868..874`) | `7` (`7426..7432`) | `true` | `true` (`d99ff43a...`) | `true` (`2*1*7 = 14`) |
| `incr_warm1` vs. `incr_warm2` | `1` | `0sbhbf5` | `1s0llzm` | `6` | **`12`** | `6` (`868,870..874`) | `6` (`7426,7428..7432`) | `true` | `true` (`d99ff43a...`) | `true` (`2*1*6 = 12`) |
| `incr_cgu16_cold` vs. `incr_cgu16_warm` | `7` | `1teft3r` (×7) | `0th4x8y` (×7) | `6` | **`84`** | `42` | `42` | `true` | `true` (`7/7` CGUs) | `true` (`2*7*6 = 84`) |

Because `s[0] ∈ {'0', '1'}` with near-50% probability, roughly half of all single-CGU cold-vs-warm comparisons exhibit `d_H = 6` (`12` bytes, matching leading digit) and roughly half exhibit `d_H = 7` (`14` bytes, differing leading digit), with occasional smaller values when another base-36 digit collides (`1/36` per position).

---

### 4. Implications for Anneal's Trusted Boundary, DDC, and Proof-Carrying Build Caches

Basis: source + derived

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three concrete operational intersections between `rustc` build determinism and Anneal's trusted computing base:

1. **Authentication of toolchain inputs and deterministic capture (`trusted/audit/src/lib.rs:108-135, 1028-1082, 1195-1240` and `trusted/rustc-capture/src/driver.rs:25-60`):**
   - `anneal-audit` (`trusted/audit/src/lib.rs`) enforces cryptographic SHA-256 authentication over `trusted/lean/foundation-lock.json` (pinning `Lean v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, distribution digests, and the allowed axiom set), `trusted/root-manifest.sha256` (covering `Cargo.toml`, `Cargo.lock`, `flake.nix`, `flake.lock`), and `Cargo.lock` v4 checksums.
   - `rustc-capture` (`trusted/rustc-capture/src/driver.rs:25-60`) pins the exact compiler version string (`rustc_interface::util::rustc_version_str()`) and overrides default `--sysroot` resolution to prevent host build paths from leaking an unauthenticated sysroot into capture runs.
   - Pairing this input-side authentication with **output-side bit-exactness** requires invoking `rustc` with (a) `-C incremental` disabled (never set on certified/CI builds), (b) `--remap-path-prefix=<checkout>=/repro` (and cargo/registry prefixes mapped to canonical virtual roots), (c) default `--remap-path-scope=all` (never `--remap-path-scope=object`, which re-introduces `3` `RealFileName.local` leaks per `SourceFile` in `lib.rmeta`), and (d) consistent `-Z remap-cwd-prefix` presence/absence across machines because `remap_cwd_prefix` is `[TRACKED]`.
2. **Diverse Double-Compiling (DDC) and proof-carrying receipt reuse:**
   - Under DDC (Wheeler's countermeasure against Thompson-style compiler trojans), compiling the same source tree `S` with an independently bootstrapped reference compiler `T_ref` and a candidate compiler `T_cand` yields a machine-checkable semantic equivalence transfer whenever `compile(T_cand, S) = compile(T_ref, S)` bit-for-bit. Any unremapped checkout path (`ce1`), partial `--remap-path-scope=object` (`ce4`), or active `-C incremental` session nonce (`ce2`) causes spurious DDC comparison failures despite semantic equivalence.
   - Similarly, a distributed remote build/proof cache (such as REAPI / content-addressed verification receipt storage) keyed by raw `.rlib` SHA-256 will experience **100% cache-key churn across warm incremental rebuilds** because `invocation_temp` rotates every invocation (`ce2`), even though `lib.rmeta` and all `.rcgu.o` payloads are bit-identical.
3. **Two sound cache-keying policies:**
   - **Policy 1 (Certified / CI / DDC builds — recommended for Anneal audit & release):** Disable `-C incremental`, pass complete `--remap-path-prefix=<dir>=/repro` with default `--remap-path-scope=all`, and permit parallel `-C codegen-units=N -Z threads=T` freely (fixing `N` across builds that share `.rlib` keys, while varying `T` freely since `cgu16_t1 == cgu16_t4`). Raw `.rmeta`, `.o`, `.rlib`, and linked ELF SHA-256 digests are then cross-directory and schedule invariant.
   - **Policy 2 (Developer-loop incremental verification caches):** If `-C incremental` must remain enabled for fast edit-compile iteration, cache verification receipts by **`normalizedArchivePayload(rlib)`** — i.e., `SHA-256(lib.rmeta || sorted_cgu_object_payloads)`, erasing `ar //` and `lib.rmeta-link` member basenames — rather than raw `.rlib` SHA-256. As proven in Theorem 3 and Theorem 4c below, `normalizedArchivePayload` is invariant across `invocation_temp` draws and determines the linked `ElfArtifact` uniquely (note, however, that an incremental build's `normalizedArchivePayload` still cannot match a clean `-C opt-level=2|3` build's cache entry unless MIR `Inline` and CGU partitioning match; see Mechanism A and `ce3`).

---

### 5. Kernel-Checked Lean `v4.34.1` Formalization (`support/ReproducibleBuildDeterminismSoundness.lean`)

Basis: derived + execution (Lean `v4.34.1` kernel check)

To give machine-checked foundations for the quotient, permutation-invariance, nonce-sensitivity, and receipt-soundness claims above, `support/ReproducibleBuildDeterminismSoundness.lean` (`1,169` lines, `35` theorems) formalizes the `rustc` build pipeline in pure core Lean `v4.34.1` (`Init` only; zero external dependencies).

#### 5.1 Formal Pipeline Model (Self-Contained Summary)

- **Constructive order & equality (`L33–L206`):** `natEqBool`, `bytesEqBool`, `natLtBool`, and lexicographic byte-string order `lexLt : List Nat → List Nat → Bool` with constructive proofs of reflexivity (`natEqBool_refl`, `bytesEqBool_refl`), irreflexivity (`lexLt_irrefl`), asymmetry (`lexLt_asym`), transitivity (`lexLt_trans`), and trichotomy (`lexLt_trichotomy`) — using `0` axioms.
- **Path remapping (`L210–L368`):** `PathSegs := List (List Nat)`, `RemapScope` (`none | objectOnly | all`), `FilePathMapping` with `mapPrefix` evaluating `rules.reverse` (reverse CLI precedence), `RealFileName` (`localPart`, `maybeRemapped`, `scopes`), `toRealFileName`, `updateForCrateMetadata` (clearing `localPart` iff `scopes = all ∨ scopes = none`), `macroScopePath`, `debuginfoPaths`, and the completeness predicate `CompleteCwdRemap m cwd vroot`.
- **Pipeline & canonical archive (`L370–L727`):** `compilePipeline (src : SourceTree) (cwd : PathSegs) (mapping : FilePathMapping) (cguPlan : List CguPlanItem) (opt : OptLevel) (dbg : DebugInfoLevel) (incr : IncrementalSession) : BuildOutput` producing `(rmeta, objs, arArchive, elf)`:
  - `mirInlineEnabled opt incr` returns `true` at `o2 | o3` iff `incr = clean`, altering `ObjectPayload.codeTag` (`1` vs. `0`) and `RmetaArtifact.mirInlined`.
  - `sortCgus` (insertion sort over `lexLt` on `cguName`) models `OngoingCodegen::join`'s canonical sort; `Perm` models arbitrary worker-thread completion permutations; `DistinctCguNames` models distinct CGU keys.
  - `assembleArtifacts` builds `ArArchive` with `gnuStrtab`, `lib.rmeta`, `lib.rmeta-link` (`RmetaLinkArtifact.rustObjectFiles`), and `objEntries` tagged with `canonicalArHeader` (`mtime = 0, uid = 0, gid = 0, perms = 0o644`), and builds `ElfArtifact` solely from the sorted `ObjectPayload`s.

#### 5.2 Proved Theorems and Exact Kernel Axiom Audit

Every theorem below was verified with:
`LEAN_SYSROOT=~/.elan/toolchains/leanprover--lean4---v4.34.1 lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`
yielding exit code `0`, `0` warnings, `0` `sorry`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, and `0` `._unsafe_rec`:

| Theorem (`ReproducibleBuildDeterminism.*`) | Location | Formal Statement / Guarantee | Kernel Axioms (`#print axioms`) |
| :--- | :---: | :--- | :--- |
| `singleRule_completeCwdRemap` | `L318` | Single `--remap-path-prefix=<cwd>=<vroot>` with scope `.all` satisfies `CompleteCwdRemap`. | `[propext]` |
| `trailingCwdRule_completeCwdRemap` | `L330` | Appending `-Z remap-cwd-prefix=<vroot>` last overrides arbitrary earlier rules and satisfies `CompleteCwdRemap`. | `[propext]` |
| `remap_eliminates_cwd_dependence` | `L352` | Under `CompleteCwdRemap` for `cwd1, cwd2 ↦ vroot`, `updateForCrateMetadata`, `macroScopePath`, and `debuginfoPaths` are equal across `cwd1` and `cwd2`. | `[propext]` |
| `remap_complete_implies_cross_dir_bit_exact` | `L765` | **Theorem 1:** Complete path remapping implies `compilePipeline ... cwd1 m1 ... = compilePipeline ... cwd2 m2 ...` across `(rmeta, objs, arArchive, elf)` at all `opt`, `dbg`, and `incr`. | `[propext]` |
| `sortCgus_eq_of_perm` | `L638` | Constructive sorting invariance: `Perm xs ys → DistinctCguNames xs → sortCgus xs = sortCgus ys` (via `insertCgu_comm`). | `[propext]` |
| `sorted_cgu_archive_invariant_under_thread_schedule` | `L783` | **Theorem 2:** Any two worker completion schedules `Perm sched1 sched2` with distinct CGU names yield bit-exact `assembleArtifacts rmeta sched1 = assembleArtifacts rmeta sched2`. | `[propext]` |
| `incremental_nonce_preserves_payload_breaks_archive_hash` | `L837` | **Theorem 3:** On any non-empty CGU plan with `n1 ≠ n2`, `b1.rmeta = b2.rmeta`, `normalizedArchivePayload b1.arArchive = normalizedArchivePayload b2.arArchive`, and `b1.elf = b2.elf`, YET `b1.arArchive ≠ b2.arArchive`. | `[propext, Quot.sound]` |
| `bit_exact_artifact_sound_receipt_reuse` | `L1010` | **Theorem 4a:** Any `VerificationReceipt spec` transfers soundly to `b2.elf` when `r.attestedElf = b2.elf`. | `[]` (no axioms) |
| `ddc_bit_exact_implies_semantic_equivalence` | `L1024` | **Theorem 4b:** If `compileRef` satisfies `spec` and `(compileCand i).elf = (compileRef i).elf`, then `spec (compileCand i).elf`. | `[]` (no axioms) |
| `normalized_payload_match_implies_elf_eq` | `L1038` | **Theorem 4c:** `normalizedArchivePayload` equality across two assembled builds implies `b1.elf = b2.elf` (sound cache reuse across warm incremental nonces). | `[propext]` |
| `ce1_unremapped_track_caller_breaks_cross_dir_repro` | `L1098` | **Counterexample 1:** Unremapped `#[track_caller]` at `debuginfo=0` breaks cross-dir `rmeta`, `arArchive`, and `elf` equality. | `[propext]` |
| `ce2_incremental_session_suffix_breaks_raw_rlib_hash_match` | `L1115` | **Counterexample 2:** Distinct 7-char nonces (`"09w14lc"` vs. `"1s0llzm"`) preserve `rmeta` and `elf` while breaking `arArchive` equality. | `[propext]` |
| `ce3_incremental_inline_suppression_changes_object_code_bytes` | `L1134` | **Counterexample 3:** At `-O2`, enabling incremental mode disables MIR `Inline`, breaking clean-vs-incremental `rmeta`, `elf`, and `arArchive` equality. | `[propext]` |
| `ce4_partial_object_scope_leaks_local_path_in_rmeta` | `L1154` | **Counterexample 4:** `--remap-path-scope=object` yields `bAlpha.elf = bBeta.elf` while breaking `rmeta` and `arArchive` cross-dir equality. | `[propext]` |

## Boundaries

To prevent over-generalization, negative space is classified using the four `reference-corpus/1` boundary categories:

### Known Not to Apply

- **Clean vs. incremental equivalence:** Findings on non-incremental bit-exactness explicitly **do not apply** when comparing a clean build against a `-C incremental` build at `-C opt-level=2|3` (MIR `Inline` suppression + CGU partitioning/naming divergence) or when comparing raw `.rlib` hashes across two incremental sessions (`invocation_temp` nonce divergence).
- **`--remap-path-scope=object` for `.rmeta`/`.rlib` reproducibility:** Established empirically (`dbg2_remap_scope_object`) and in source (`RealFileName::update_for_crate_metadata`) **not to apply** to crate metadata or `.rlib` archives: while `.o` files reach `0` leaks, `lib.rmeta` retains `3` raw paths in `RealFileName.local`.
- **Cross-`-C codegen-units=N` identity:** Fixing `N = 16` makes `cgu16_t1 == cgu16_t4`, but changing `N` (`cgu1` vs. `cgu16`) intentionally alters CGU boundaries, inlining opportunities, and `.rlib` member counts (`18,048 B` vs. `37,138 B`).
- **Toggling `-Z remap-cwd-prefix` across machines:** Because `remap_cwd_prefix` is `[TRACKED]`, a machine passing `--remap-path-prefix=<dir>=/repro` alone will NOT match a machine passing `--remap-path-prefix=<dir>=/repro -Z remap-cwd-prefix=/repro` in `lib.rmeta` or `.rlib` (even though their `.o` files match). Both builders must pass the same set of tracked flags.
- **Model vs. implementation scope of the Lean proof:** `support/ReproducibleBuildDeterminismSoundness.lean` formalizes the structural pipeline invariants (prefix-remapping quotient, permutation-invariant CGU sorting, canonical `ar` headers, dual `//` + `lib.rmeta-link` nonce injection, MIR-inline gating, and DDC/receipt transfer). It does **not** formally verify the Rust source code of `rustc`, `ar_archive_writer`, or LLVM's C++ optimizer/code generator.

### Not Examined

- **Non-ELF targets and non-GNU archive formats:** Mach-O / BSD `ar` (macOS, `ld64`, `codesign`), PE/COFF / MSVC `lib` (Windows), WebAssembly, and embedded `no_std` targets were not executed in this investigation.
- **ThinLTO (`-C lto=thin`) and FatLTO (`-C lto=fat`) parallel determinism:** Only `Lto::No` (default non-LTO `rlib` and binary linking) was executed; `do_thin_lto` parallel LTO worker scheduling and cross-crate ThinLTO summary caching were not tested.
- **Split DWARF (`.dwo` / `-C split-debuginfo=unpacked|packed`) and PGO / coverage instrumentation (`-C instrument-coverage`, `-C profile-generate`):** Although `split_dwarf_path` and `RemapPathScopeComponents::COVERAGE` were observed in source, their emitted artifacts were not empirically probed.
- **Procedural macros, `build.rs` build scripts, `OUT_DIR`, and `CARGO_HOME` registry paths:** Cargo-level environment variables, proc-macro host nondeterminism, and remapping third-party crate paths (`--remap-path-prefix=$CARGO_HOME=/cargo`) were not executed (the probe invokes `rustc` directly).
- **External linker nondeterminism (`ld.bfd` vs. `ld.lld` vs. `mold`, `--build-id`, ASLR/timestamp flags):** Probe 4 used the host default linker configuration invoked by `rustc` on `x86_64-unknown-linux-gnu`; linkers emitting random build IDs (`--build-id=uuid`), timestamps (PE headers), or multithreaded section ordering were not systematically ablated.
- **Live execution of `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:** Only `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) was executed locally; `342d74463` was verified via primary source inspection only.

### Unknown

- **Exact cross-version binary stability of `lib.rmeta-link` across future `rustc` releases:** Upstream `342d74463` already extended `RmetaLink` with `native_lib_filenames` relative to `14210df0e` (`rust-lang/rust#138243`). Whether future `rustc` releases will eventually strip `invocation_temp` from archive member names (or make `invocation_temp` deterministic/opt-out under `-C incremental`) is unresolved upstream.
- **Upper bound on multi-thread scheduling variance under heavy LLVM ThinLTO / large crate graphs (`> 100k` LOC):** While `OngoingCodegen::join` eliminates CGU-order nondeterminism for `Lto::No`, whether any LLVM pass exhibits thread-scheduling or pointer-hash nondeterminism on large real-world crates under `-Z threads=N` is not established by a 6-CGU synthetic probe.

### Unsupported

- **Bit-exact `.rlib` reproduction under `-C incremental` without archive normalization:** `rustc` exposes no stable CLI flag to disable `OutputFilenames.invocation_temp` randomization when `-C incremental` is enabled (`compiler/rustc_interface/src/util.rs:621-625` / `686-690` unconditionally calls `rng().next_u32()` whenever `sess.opts.incremental.is_some()`).
- **Direct reuse of `joshlf/anneal` Pass 1 `Trusted.MirSemantics` inside standalone proof files:** `support/ReproducibleBuildDeterminismSoundness.lean` is deliberately standalone (`Init`-only) so it checks with bare `lean` without building Anneal's Lake workspace; it does not import `Trusted.MirSemantics`.

### Stronger Conclusions Not Established by This Evidence

- Passing `--remap-path-prefix=<dir>=/repro` does **not** guarantee cross-machine reproducibility if two machines have different `rustc` sysroot paths (unless `--remap-path-prefix=<sysroot>=/rustc` or upstream `rust.remap-debuginfo` is active), different `CARGO_HOME` paths, different `-C codegen-units`, different `-Z remap-cwd-prefix` flags, or different system linkers/libc CRT objects (`crt1.o`, `libgcc`).
- Bit-exactness of `repro_lib` across `4` parallel runs of `-C codegen-units=16 -Z threads=4` verifies `rustc`'s module-collection canonicalization on `6` CGUs; it does not prove that arbitrary crates using non-deterministic procedural macros or unstable LLVM passes are deterministic.

## Evidence

### 1. Primary-Source Citations (`rust-lang/rust`)

All commit SHAs were resolved live via GitHub API on `2026-11-22` and inspected directly:

- **Executed revision:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`, `rustc 1.98.0-nightly`, `LLVM 22.1.6`).
- **Upstream cross-check revision:** `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`).

| File Path | `14210df0e` Lines | `342d74463` Lines | Symbol / Verified Mechanism |
| :--- | :---: | :---: | :--- |
| `compiler/rustc_span/src/source_map.rs` | `1121–1252` | `1123–1254` | `FilePathMapping`, `map_prefix` (`mapping.iter().rev()`), `to_real_filename` (`local: Some(...)`). |
| `compiler/rustc_span/src/lib.rs` | `239–254`, `304–324`, `348–385`, `476–484` | `243–258`, `308–328`, `352–389`, `480–488` | `RemapPathScopeComponents` (`OBJECT = MACRO \| DEBUGINFO \| COVERAGE`), `RealFileName`, `InnerRealFileName`, `update_for_crate_metadata`. |
| `compiler/rustc_session/src/options.rs` | `365–367`, `2583–2584` | `478–480`, `2922–2923` | `remap_path_prefix`/`remap_path_scope` (`[TRACKED_NO_CRATE_HASH]`) vs. `remap_cwd_prefix` (`[TRACKED]`). |
| `compiler/rustc_session/src/config.rs` | `1246–1266`, `1311–1340`, `2390–2407` | `1361–1381`, `1426–1455`, `1490–1507` | `OutputFilenames::temp_path_ext_for_cgu` (`.{invocation_temp}`), `parse_remap_path_scope`, `#132132` `remap_cwd_prefix` move into `file_path_mapping`. |
| `compiler/rustc_metadata/src/rmeta/encoder.rs` | `538–604` | `570–635` | `Encoder::encode_source_map` invoking `adapted_file_name.update_for_crate_metadata()`. |
| `compiler/rustc_middle/src/mir/consts.rs` | `515–525` | `533–543` | `TyCtxt::span_as_caller_location` using `RemapPathScopeComponents::MACRO`. |
| `compiler/rustc_const_eval/src/util/caller_location.rs` | `12–75` | `12–75` | `alloc_caller_location` emitting `filename.to_owned() + "\0"` into `.rodata`. |
| `compiler/rustc_builtin_macros/src/source_util.rs` | `60–76` | `60–76` | `expand_file` (`file!()`) using `RemapPathScopeComponents::MACRO`. |
| `compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs` | `551–621`, `865–936` | `565–625`, `920–990` | `file_metadata` (`embeddable_name(DEBUGINFO)`) and `compile_unit_metadata` (`DW_AT_comp_dir`, `DW_AT_name`). |
| `compiler/rustc_mir_transform/src/inline.rs` | `45–59` (L55) | `50–58` (L58) | `Inline` disabled at `mir_opt_level() == 2` whenever `incremental.is_some()`. |
| `compiler/rustc_middle/src/mono.rs` | `450–453`, `524–594`, `595–690` | `450–453`, `524–594`, `622–706` | `CodegenUnit::mangle_name` (base-36 SipHash-128), `items_in_deterministic_order`, `CodegenUnitNameBuilder`. |
| `compiler/rustc_monomorphize/src/partitioning.rs` | `206–245`, `385–508` | `206–245`, `385–508` | Volatile generic split (`is_incremental_build`), tiny-CGU merge guard (`incremental.is_none()`), numbered vs. hashed CGU names. |
| `compiler/rustc_interface/src/util.rs` | `621–625` | `686–690` | `invocation_temp = sess.opts.incremental.as_ref().map(\|_\| rng().next_u32().to_base_fixed_len(CASE_INSENSITIVE).to_string())`. |
| `compiler/rustc_incremental/src/persist/fs.rs` | `345–355`, `444–456` | `304–314`, `378–390` | Incremental session directory `s-{timestamp}-{random}-working` (`rng().next_u32()` base-36). |
| `compiler/rustc_codegen_ssa/src/back/write.rs` | `398–403`, `1670`, `2175–2188` | `398–403`, `1678`, `2201–2212` | `need_bitcode_in_object` (`.llvmbc`), worker completion push, `compiled_modules.modules.sort_by(\|a, b\| a.name.cmp(&b.name))`. |
| `compiler/rustc_codegen_ssa/src/back/link.rs` | `300–400` | `540–635` | `link_rlib` writing `lib.rmeta`, `lib.rmeta-link` (`RmetaLink`), and `.rcgu.o` members in sorted module order. |
| `compiler/rustc_codegen_ssa/src/back/rmeta_link.rs` | `1–56` | `1–56` | `RmetaLink` encoding `rust_object_files: Vec<String>` into `.rmeta-link` section of `lib.rmeta-link`. |
| `compiler/rustc_codegen_ssa/src/back/archive.rs` | `381–393`, `505–628` | `390–400`, `550–729` | `ArArchiveBuilder::build_inner` (`mtime: 0, uid: 0, gid: 0, perms: 0o644`) and `write_archive_to_stream`. |

### 2. Primary-Source Citations (`joshlf/anneal` and `leanprover/lean4`)

- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  - `trusted/audit/TrustedBoundary.lean:1–120` (pinned to `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, preflight allowlists, Pass 1/Pass 2 replay isolation).
  - `trusted/audit/src/lib.rs:102–135, 1028–1082, 1195–1240` (SHA-256 authentication of Lean binary, sysroot `.olean` manifest, `trusted/root-manifest.sha256`, and `Cargo.lock` v4 checksums).
  - `trusted/lean/foundation-lock.json` (distribution hashes and foundation axiom allowlist for `Lean v4.34.1`).
  - `trusted/rustc-capture/src/driver.rs:25–60` (compiler version check and default `--sysroot` hardening).
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): verified live via GitHub API on `2026-11-22`.

### 3. Preserved Package Support Artifacts

All execution and mechanization artifacts are preserved inside this report package under `support/`:

1. **`support/probe_reproducible_builds.py`:** Self-contained Python 3.10+ (stdlib-only) harness invoking real `rustc`, `readelf`, and compiled ELF executables inside isolated `tempfile.TemporaryDirectory()` sandboxes (`LC_ALL=C`, `TZ=UTC`), parsing GNU/SVR4 `ar` headers at exact byte offsets, classifying ELF section leak sites, and scrubbing all host paths from output JSON.
2. **`support/reproducible_builds_probe.json`:** Complete, unedited execution output captured on `2026-11-22` from `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` / `GNU ar 2.47`, containing every SHA-256 hash, byte size, ELF section leak map, `ar` header table, incremental byte-offset diff, and binary stdout cited in **Findings**.
3. **`support/ReproducibleBuildDeterminismSoundness.lean`:** Self-contained `1,169`-line Lean `v4.34.1` mechanization (`35` theorems) verified with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, zero warnings, zero `sorry`, zero `Classical.choice`, zero `Lean.ofReduceBool`, zero `omega`/`bv_decide`/`native_decide`/`partial`/`unsafe`).

## Revalidation

To cheaply revalidate all claims in this report against a newer `rustc` nightly/release, target architecture, or Lean version:

1. **Rerun the empirical `rustc` + `ar` probe (~5–10 seconds):**
   ```console
   python3 support/probe_reproducible_builds.py --out /tmp/repro_check.json
   ```
   Verify the following discriminating assertions on `/tmp/repro_check.json`:
   - `probe_1_cross_dir_determinism.dbg0_no_remap.bit_exact` is all `false` (`rmeta` leaks `3`, `obj` leaks `1` in `.rodata.str1.1`).
   - `probe_1_cross_dir_determinism.dbg2_no_remap.bit_exact` is all `false` (`rmeta` leaks `3`, `obj` leaks `5`: `.rodata.str1.1`, `.debug_str`, `.llvmbc`).
   - `dbg0_remap_path`, `dbg0_remap_path_and_cwd`, `dbg2_remap_path_only`, and `dbg2_remap_path_and_cwd` all report `bit_exact = {rmeta: true, obj: true, rlib: true}` and `0` leaks.
   - `dbg2_remap_scope_object` reports `bit_exact = {rmeta: false, obj: true, rlib: false}` (if upstream changes `update_for_crate_metadata`, this discriminator flips immediately).
   - `probe_2_cgu_and_threads_repeatability` reports `unique_rlib_hashes == 1` across `cgu1_t1`, `cgu16_t1`, `cgu16_t4`, `cgu16_t1_eq_cgu16_t4_rlib == true`, and `all_ar_headers_deterministic_zero_epoch == true`.
   - `probe_3_clean_vs_incremental.comparisons` reports `incr_cold_eq_incr_warm1_rmeta == true`, `incr_cold_eq_incr_warm1_obj_payload == true`, `incr_cold_eq_incr_warm1_rlib == false`, and `expected_2x_hamming_matches_diff == true` for both `M = 1` and `M = 7` CGUs. (If upstream removes `invocation_temp` from archive member names, `incr_cold_eq_incr_warm1_rlib` flips to `true` and `diff_byte_count` drops to `0`.)
   - `probe_4_linked_elf_repro.elf_bit_exact == true` with `0` leaks and matching `run_stdout`.
2. **Re-check the Lean `v4.34.1` formalization and axiom hygiene (~5 seconds):**
   ```console
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/ReproducibleBuildDeterminismSoundness.lean
   ```
   Confirm exit code `0`, and append `#print axioms` checks on a temporary copy to confirm zero `Classical.choice`, `sorryAx`, or `Lean.ofReduceBool`.
3. **Targeted upstream source diffs (when checking a newer `rust-lang/rust` commit):**
   Diff only the six load-bearing sites relative to `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:
   - `compiler/rustc_span/src/lib.rs` (`RealFileName::update_for_crate_metadata`),
   - `compiler/rustc_session/src/options.rs` (`remap_path_prefix` / `remap_cwd_prefix` tracking annotations),
   - `compiler/rustc_mir_transform/src/inline.rs` (`PassPolicy::optional` incremental check),
   - `compiler/rustc_interface/src/util.rs` (`invocation_temp` generation),
   - `compiler/rustc_codegen_ssa/src/back/write.rs` (`compiled_modules.modules.sort_by`),
   - `compiler/rustc_codegen_ssa/src/back/archive.rs` & `link.rs` (`NewArchiveMember` zeroed fields and `RmetaLink`).
   Note that passing this probe establishes determinism only for the exercised host (`x86_64-unknown-linux-gnu`), `Lto::No`, and proc-macro-free crate configurations; extending claims to ThinLTO, Split DWARF, macOS/Windows, or Cargo proc-macro workspaces requires building new probes covering those targets.
