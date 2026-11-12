# Concurrent Source File Modifications Across `rustc`, Clang, GCC, Go, `javac`, Build Orchestrators, and Hermetic `rustc_driver` Input Binding

## Summary

Production batch compilers (`rustc`, Clang, GCC, Go `cmd/compile`, and OpenJDK `javac`) do not take an atomic point-in-time snapshot of a translation unit or crate before compilation begins, nor do they place advisory or mandatory OS locks on source files. Instead, compilers discover and open files incrementally across compilation phases, exposing three distinct concurrency boundary classes:

1. **Intra-File Ingestion Mechanics (`read` Heap Snapshot vs. `mmap` Page-Cache Sharing):**
   - `rustc` (`RealFileLoader::read_file` via `read_to_string` and `read_binary_file` via `read_buf_exact`), GCC (`libcpp/files.cc` `read_file_guts` via `read`), Go `cmd/compile` (`cmd/compile/internal/syntax/source.go` streaming `Read` in $4\text{ KiB}$ chunks), and OpenJDK `javac` (`RegularFileObject` `read` into a heap buffer) copy each opened source file into private heap memory and immediately close the file descriptor. Once `read` returns, subsequent in-place overwrites or `ftruncate(0)` truncations on disk cannot mutate the already-loaded buffer or raise `SIGBUS`.
   - By contrast, standalone Clang (`llvm/lib/Support/MemoryBuffer.cpp`, `shouldUseMmap` with `IsVolatile = false`) maps regular files via `mmap(..., PROT_READ, MAP_PRIVATE | MAP_NORESERVE, fd, 0)` whenever `FileSize >= 16384` ($4 \times 4096\text{ B}$) and `(FileSize & (PageSize - 1)) != 0` (leaving at least one kernel-zeroed trailing byte on the final mapped page for `Lexer::InitLexer`'s `BufEnd[0] == '\0'` sentinel). Because `MAP_PRIVATE` mappings share clean pages with the kernel page cache and fault pages lazily—and because Clang `Token`s store only `SourceLocation` byte offsets into the `MemoryBuffer` and re-read literal/macro spellings at expansion time—concurrent edits to a $\ge 16\text{ KiB}$ non-page-multiple header in standalone `clang` cause three failure modes that never occur in `gcc` or `rustc`:
     - **Retroactive token mutation after `close(fd)`:** Overwriting bytes in place via `pwrite` after a $20{,}000\text{ B}$ header has already been `#include`d, lexed, and closed mutates the value observed when a macro from that header is expanded later in `main()` (`clang-19` compiles a binary returning the post-edit value `211`, whereas `gcc-15` returns the pre-edit value `100`).
     - **`SIGBUS` crash on truncation:** Truncating a mapped $20{,}000\text{ B}$ header via `ftruncate(0)` before a token on a higher page is expanded or diagnosed kills `clang -cc1` with `SIGBUS` (`Bus error`, exit `254`), whereas `gcc-15` exits `0`.
     - **NUL-sentinel overwrite and lexer overrun:** Appending bytes at the original $20{,}000\text{ B}$ EOF while Clang is lexing overwrites the trailing `\0` sentinel at `BufEnd[0]`, causing `clang::Lexer::LexTokenInternal` to lex past `BufferEnd` through the remainder of the $4096\text{ B}$ page and crash with `SIGBUS` on the next page boundary.
   - IDE frontends (`libclang` `CIndex.cpp` and `ASTUnit.cpp` / `clangd`) set `UserFilesAreVolatile = true`, which forces `shouldUseMmap` to return `false` (`if (IsVolatile && RequiresNullTerminator) return false;`) and falls back to `pread64` into a zero-padded heap buffer.

2. **Intra-Compilation Re-Reads and Inter-File Temporal Skew in `rustc` and GCC:**
   - **Two-phase AST fragment expansion ordering in `rustc`:** In `MacroExpander::fully_expand_fragment` (`compiler/rustc_expand/src/expand.rs:471-600`), `collect_invocations` walks each AST fragment and **immediately loads and parses all static out-of-line `mod foo;` files** (`parse_external_mod`, `expand.rs:1407-1431`) *before* expanding any macro invocations (`include!`, `include_str!`, `include_bytes!`, declarative macros, or procedural macros) in that fragment. An out-of-line `mod gate;` on line 4 of `main.rs` is therefore read from disk before `include_str!("./data.txt")` on line 3.
   - **Unconditional disk read before cache lookup in `SourceMap::load_file`:** `SourceMap::load_file` (`compiler/rustc_span/src/source_map.rs:280-284`) calls `self.file_loader.read_file(path)?` *before* `try_new_source_file` (`source_map.rs:360-383`) checks `stable_id_to_source_file`. When `StableSourceFileId` is already cached, `try_new_source_file` returns the **first** cached `Arc<SourceFile>` and silently discards the newly read `String`; however, if a cached file is unlinked on disk before a second `include!("./shared.rs")`, `load_file` fails with `error: couldn't find file` at line 281 before reaching the cache check at line 366.
   - **Divergence between `load_file` (`mod` / `include!`) and `load_binary_file` (`include_str!` / `include_bytes!`):** Both `expand_include_str` and `expand_include_bytes` (`compiler/rustc_builtin_macros/src/source_util.rs:204-313`) call `SourceMap::load_binary_file` (`source_map.rs:290-310`), which reads fresh `bytes` via `file_loader.read_binary_file(path)?`, calls `self.new_source_file(filename, text)`, and returns the **freshly read `bytes`** directly (paired with a `Span` using the cached `file.normalized_source_len`). Consequently, repeated `include_str!("./shared.rs")` or `include_bytes!("./shared.rs")` calls on the exact same path observe new on-disk edits (`V = 1` then `V = 2`), whereas repeated `include!("./shared.rs")` calls stay locked to the first cached `SourceFile.src` (`V = 1` then `V = 1`), and an early `include_bytes!("./shared.rs")` populates `SourceMap` so a later `#[path = "./shared.rs"] mod s;` or `include!("./shared.rs")` after an on-disk edit still compiles the old `V = 1` source.
   - **Single-file split-brain via non-canonical `StableSourceFileId` keys:** `StableSourceFileId` (`compiler/rustc_span/src/lib.rs:2132-2155`) hashes `(FileName, Option<StableCrateId>)` where `FilePathMapping::to_real_filename` (`source_map.rs:1229-1288`) does not call `fs::canonicalize`, collapse `..`, resolve symlinks, or strip leading `./` (`Component::CurDir`). Referencing the same physical inode via `"shared.rs"`, `"./shared.rs"`, `"./sub/../shared.rs"`, or `"./sym_shared.rs"` across a concurrent edit causes `rustc` to compile multiple temporal versions of the same file into one binary.
   - **Re-included unguarded headers in GCC vs. Clang:** Because GCC's `_cpp_clean_line` mutates buffers in place, `_cpp_stack_file` (`libcpp/files.cc:1021-1022`) sets `file->buffer_valid = false` as soon as a file is stacked. Any header lacking `#pragma once` or an active `#ifndef` guard (`cmacro`) is re-opened and re-read from disk on a second `#include` (`first_inc = 1, second_inc = 2`), whereas Clang's `ContentCache::getBufferOrNone` (`clang/lib/Basic/SourceManager.cpp:110-117`) reuses the cached `MemoryBuffer` (`first_inc = 1, second_inc = 1`).
   - **Cross-crate `src_hash` validation in `rustc` (`ensure_source_file_source_present`):** Local crate files keep `src: Some(Arc<String>)` in memory for the entire session. Imported upstream `.rmeta` `SourceFile`s have `src: None`; when a downstream diagnostic span points into an upstream `SourceFile`, `SourceMap::ensure_source_file_source_present` (`source_map.rs:1096-1121`) lazily reads the upstream `.rs` file from disk and checks `self.src_hash.matches(&src)` on the pre-normalized string (`lib.rs:2300`). If modified on disk (whether same byte length or different byte length), `add_external_src` freezes `external_src` to `ExternalSourceKind::AbsentErr` and `AnnotateSnippetEmitter` silently omits the source snippet while still printing `--> dep.rs:line:col` (`SourceFile::src_modified` at `lib.rs:2285` has zero callers in `compiler/`).

3. **Build-Orchestrator Freshness Poisoning and Hermetic `rustc_driver` Source Binding:**
   - **GNU Make (`4.4.1`) and Ninja:** Compare `mtime(input) > mtime(output)` where `mtime(output)` is written at $t_3$ when the compiler exits; any source edit at $t_2 \in (t_{\text{read}}, t_3)$ satisfies $t_2 \le t_3$ and permanently caches a stale build artifact.
   - **Cargo default `Mtime` mode (`src/compiler/mod.rs:464, 562` and `src/compiler/fingerprint/mod.rs:2208-2229`):** Cargo creates `invoked.timestamp` before spawning `rustc` ($t_0$) and rewinds `mtime(dep-lib-<pkg>)` back to $t_0$ after `rustc` exits ($t_3$), detecting edits when $t_2 > t_0$. However, `find_stale_file` uses non-strict `if path_mtime <= reference_mtime { continue; }` (`cargo#5918`), permanently caching stale binaries whenever $t_2 == t_0$ within the same OS/filesystem timestamp quantum (1–4 ms Linux coarse timer tick, 1 s HFS+/ext3, or zeroed Docker layer nanoseconds).
   - **Cargo `-Z checksum-freshness` (`--config 'build.fingerprint="content"'`) has two post-read checksum poisoning bugs:**
     1. In `compiler/rustc_interface/src/passes.rs:614-650` (`write_out_deps`), `hash_iter_files` re-opens every file in `sess.file_depinfo` (`include_str!`, `include_bytes!`, `proc_macro::tracked::path`) from disk *after* macro expansion ($t_{\text{depinfo}} > t_2$) and calls `files.extend(extra_tracked_files)`, overwriting the $t_1$ in-memory `SourceMap` checksum in `<crate>.d` with the $t_2$ post-edit disk checksum.
     2. When a file is loaded at $t_1$ (`src/main.rs`) and again at $t_2$ after an edit via a non-canonical alias (`src/./main.rs`), `rustc` emits two `# checksum:` lines in `.d`; Cargo's `translate_dep_info` (`src/compiler/fingerprint/dep_info.rs:360`) canonicalizes both to `src/main.rs`, and `parse_dep_info` (`dep_info.rs:498-506`) inserts them into a `HashMap` where the $t_2$ alias entry overwrites the $t_1$ primary entry. Both bugs cause `cargo build -Z checksum-freshness --config 'build.fingerprint="content"'` to permanently cache a stale `Version 1` binary while `Version 2` is on disk.
   - **Hermetic `rustc_driver` source binding:** External pre-hashing ($H_{\text{pre}}$), post-hashing ($H_{\text{post}}$), and $H_{\text{pre}} == H_{\text{post}}$ checks without an in-process `FileLoader` are all unsound under concurrent edits (the latter via an $A \to B \to A$ ABA race). Sound source-to-MIR binding requires either **(Pattern 4)** an in-process `Config::file_loader` (`RecordingFileLoader`) that reads once per open file descriptor, enforces a single-hash invariant keyed by both `fs::canonicalize(path)` *and* `fstat` `(st_dev, st_ino)` (to defeat hardlink aliasing), audits `source_map().files()`, `file_depinfo`, and `env_depinfo` in `after_analysis`, and verifies $H_{\text{pre}} == H_{\text{in-memory}} == H_{\text{post}}$, or **(Pattern 5)** a preloaded in-memory `VirtualFileLoader` (`BTreeMap<PathBuf, Arc<[u8]>>`) combined with a read-only private staging directory or mount namespace (`CLONE_NEWNS`) when procedural macros are enabled.

---

## Applicability

This report applies to the nine subjects recorded in `REPORT.json`, evaluated on `x86_64-unknown-linux-gnu`:

| Subject | Repository / Artifact | Version / Revision | Role in Report |
| :--- | :--- | :--- | :--- |
| **`rust-lang/rust` (source tree)** | `rust-lang/rust` | `49d734536222bf28bb6d07d885b3a81d145981da` | Primary source inspection of `rustc_span`, `rustc_expand`, `rustc_builtin_macros`, `rustc_interface`, `rustc_session`, `rustc_errors`, `rustc_metadata`, `rustc_incremental`, and `rustc_data_structures`. |
| **`rust-lang/rust` (nightly toolchain)** | `rust-lang/rust` | `19833af7224424e8b53e288097d56b6af43d5bcf` (`1.101.0-nightly`, `2026-10-20`) | Execution of all `rustc` and `rustc_driver` FIFO-synchronized concurrency probes. |
| **`rust-lang/cargo` (source pin)** | `rust-lang/cargo` | `3c0b534756e166d12eb9fd2e1abfe5b42ac6101e` | Source inspection of `src/compiler/fingerprint/` (`gitlink` in `rust-lang/rust@49d73453622`). |
| **`rust-lang/cargo` (nightly binary & source)** | `rust-lang/cargo` | `3960fa69bb617e3d93c4ddc087c1b32bf12ad907` (`1.101.0-nightly`, `2026-10-12`) | Source inspection and execution of `Mtime` and `-Z checksum-freshness` (`build.fingerprint="content"`) cache-poisoning probes. |
| **LLVM & Clang 19.1.7** | `llvm/llvm-project` | `cd708029e0b2869e80abe31ddb175f7c35361f90` (`llvmorg-19.1.7`) | Source inspection of `MemoryBuffer.cpp`, `SourceManager.cpp`, `Lexer.cpp`, `ASTReader.cpp`, `ASTUnit.cpp`, and `CIndex.cpp`; execution of `clang-19` `strace` and `mmap` mutation/truncation probes. |
| **GCC & `libcpp` 15.2.0** | `gcc-mirror/gcc` | `5115c7e447fc07457443df874bf57840e8316d5f` (`releases/gcc-15.2.0`) | Source inspection of `libcpp/files.cc` and `libcpp/lex.cc`; execution of `gcc` (`15.2.0`) `strace` and FIFO concurrency probes. |
| **Go `cmd/compile`** | `golang/go` | `2aae1000ea1d4b28923b96db28acf4e3b99d6aff` (`go1.27.3`) | Source inspection of `cmd/compile/internal/noder/noder.go` and `cmd/compile/internal/syntax/source.go`; execution of `go tool compile` `strace` probes. |
| **OpenJDK `javac`** | `javac` | `27.0.1+-google-release-sts-1005653896` | Execution of `javac` `strace` file-ingestion probes across file sizes. |
| **GNU Make** | `make` | `4.4.1` | Execution of `mtime(input) <= mtime(target)` mid-build edit cache-poisoning probe. |

### Cross-Version Notes for `rustc` and `cargo`
- Between `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` and `rust-lang/rust@19833af7224424e8b53e288097d56b6af43d5bcf` (`1.101.0-nightly`), `SourceMap`, `FileLoader`, `RealFileLoader`, `SourceFile::new`, `ensure_source_file_source_present`, and `passes::write_out_deps` are behaviorally identical; in `rustc_driver`, the public entry point `rustc_driver::run_compiler` at `49d73453622` is named `rustc_driver::compiler_entrypoint` at `19833af7224`.
- Between `rust-lang/cargo@3c0b534756e166d12eb9fd2e1abfe5b42ac6101e` and `rust-lang/cargo@3960fa69bb617e3d93c4ddc087c1b32bf12ad907`, enabling content-based checksums changed from `-Z checksum-freshness` alone (`src/compiler/mod.rs:857-859` at `3c0b53475`) to requiring both `-Z checksum-freshness` and `--config 'build.fingerprint="content"'` (`src/compiler/mod.rs:871-884` at `3960fa69b`).

---

## Findings

### 1. Cross-Compiler Source Ingestion Taxonomy and `strace` Threshold Matrix

`Basis: source + execution`

Auditing the file-ingestion implementations across `rustc`, Clang/LLVM, GCC, Go `cmd/compile`, and OpenJDK `javac` and executing the 15-run `strace` matrix in [`support/compiler_mmap_and_fifo_probes.py`](support/compiler_mmap_and_fifo_probes.py) ([`support/compiler_probe_results.json`](support/compiler_probe_results.json)) across exact file sizes of $1{,}000\text{ B}$ ($< 16\text{ KiB}$), $16{,}384\text{ B}$ ($4 \times 4096\text{ B}$ exact page multiple), and $20{,}000\text{ B}$ ($> 16\text{ KiB}$ non-page-multiple) establishes the following cross-compiler behavior:

| Compiler | $1{,}000\text{ B}$ Syscalls | $16{,}384\text{ B}$ ($4 \times 4096\text{ B}$) Syscalls | $20{,}000\text{ B}$ Syscalls | In-Place Overwrite Hazard After `close(fd)` | `ftruncate(0)` Hazard After `close(fd)` | Re-Read on Repeated Include / Load of Same Path? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Clang 19** (`clang -cc1`, `IsVolatile=false`) | `openat` $\to$ `fstat` $\to$ `pread64(fd, buf, 1000, 0)` $\to$ `close` | `openat` $\to$ `fstat` $\to$ `pread64(fd, buf, 16384, 0)` $\to$ `close` | `openat` $\to$ `fstat` $\to$ **`mmap(NULL, 20000, PROT_READ, MAP_PRIVATE\|MAP_NORESERVE, fd, 0)`** $\to$ `close` | **YES** for `mmap`ed files ($\ge 16\text{ KiB}$, `size % 4096 != 0`): mutates un-expanded macro/literal tokens live via page cache (**Exp 2a**) | **YES (`SIGBUS`)** for `mmap`ed files; appending at EOF overwrites `\0` sentinel and crashes lexer (**Exp 2b, 2c**) | **NO**: `SourceManager` `ContentCache` caches `MemoryBuffer` per `FileEntryRef` (**Exp 2d**) |
| **Clang (`libclang` / `clangd`, `IsVolatile=true`)** | `pread64` into heap buffer | `pread64` into heap buffer | `pread64` into heap buffer (`shouldUseMmap` returns `false`) | **NO** once `pread64` completes (if file shrinks before `pread64`, tail is zero-filled) | **NO** once `pread64` completes | **NO** within one `SourceManager` |
| **GCC 15** (`cc1` / `libcpp`) | `openat` $\to$ `fstat` $\to$ `read(fd, buf, 1000)` $\to$ `close` | `openat` $\to$ `fstat` $\to$ `read(fd, buf, 16384)` $\to$ `close` | `openat` $\to$ `fstat` $\to$ `read(fd, buf, 20000)` $\to$ `close` | **NO** (private heap `XNEWVEC` copy in `read_file_guts`) | **NO** (warns `%s is shorter than expected` only if truncated *before* `read()`) | **YES for unguarded headers**: `_cpp_stack_file` sets `buffer_valid = false`, re-reading on 2nd `#include` (**Exp 2d**) |
| **`rustc`** (`1.101.0-nightly`) | `openat` $\to$ `fstat` $\to$ `read(1000)` $\to$ `read(0)` $\to$ `close` | `openat` $\to$ `fstat` $\to$ `read(16384)` $\to$ `read(0)` $\to$ `close` | `openat` $\to$ `fstat` $\to$ `read(20000)` $\to$ `read(0)` $\to$ `close` | **NO** for `.rs` source files (heap `String`); **YES** for `.rmeta`/`.rlib` & incremental `.bin` (`Mmap::map`) | **NO** for `.rs` source files; **YES (`SIGBUS` / UB)** for `mmap`ed `.rmeta` & incremental cache | **`mod`/`include!`**: disk read happens, then `try_new_source_file` returns cached `SourceFile`; **`include_str!`/`include_bytes!`**: returns fresh bytes every call (**Exp 3a–3c**) |
| **Go `cmd/compile`** (`go1.27.3`) | `openat` $\to$ `read(4095)=1000` $\to$ `read(4094)=0` $\to$ `close` | `openat` $\to$ $5 \times \text{read}(4095/4093)$ $\to$ `read(0)` $\to$ `close` | `openat` $\to$ $5 \times \text{read}(4095/4093)$ $\to$ `read(0)` $\to$ `close` | **Streaming intra-file window** across $4\text{ KiB}$ `Read` chunks while file is open; **NO** after `close` | **NO** (`SIGBUS` impossible; truncation during streaming `Read` yields short read / syntax error) | **NO** (each `.go` file in package is parsed once by a goroutine in `LoadPackage`) |
| **OpenJDK `javac`** (`27.0.1`) | `statx` $\to$ `openat` $\to$ `fstat` $\to$ `read(1000)` $\to$ `read(1)=0` $\to$ `close` | `statx` $\to$ `openat` $\to$ `fstat` $\to$ `read(16384)` $\to$ `read(1)=0` $\to$ `close` | `statx` $\to$ `openat` $\to$ `fstat` $\to$ `read(20000)` $\to$ `read(1)=0` $\to$ `close` | **NO** once `read` into heap `ByteBuffer`/`CharBuffer` completes | **NO** | **NO** per compilation task |

---

### 2. `rustc` Source Ingestion, `SourceMap` Caching, and Concurrent Edit Semantics

`Basis: source + execution`

In `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` and `rustc 1.101.0-nightly (19833af7224424e8b53e288097d56b6af43d5bcf)`:

#### 2.1 `FileLoader` and `RealFileLoader` (`compiler/rustc_span/src/source_map.rs:80-165`)

`SourceMap` performs all source file reads through the `FileLoader` trait (`compiler/rustc_span/src/source_map.rs:80-96`):

```rust
pub trait FileLoader {
    fn file_exists(&self, path: &Path) -> bool;
    fn read_file(&self, path: &Path) -> io::Result<String>;
    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>>;
    fn current_directory(&self) -> io::Result<PathBuf>;
}
```

`RealFileLoader` (`source_map.rs:99-165`) implements `read_file` and `read_binary_file` with different concurrent-resize behaviors:
- **`RealFileLoader::read_file` (`source_map.rs:106-119`):** Opens `fs::File::open(path)?`, checks `file.metadata().map(|m| m.len()).ok().unwrap_or(0) > SourceFile::MAX_FILE_SIZE.into()` (`u32::MAX - 1`, `compiler/rustc_span/src/lib.rs:2158`), and calls `file.read_to_string(&mut contents)?`.
- **`RealFileLoader::read_binary_file` (`source_map.rs:121-160`):** Opens `fs::File::open(path)?`, reads `len = file.metadata()?.len()`, allocates `Arc::new_uninit_slice(len as usize)`, and calls `file.read_buf_exact(buf.unfilled())`:
  - **Concurrent truncation fallback (`source_map.rs:129-132`):** If the file shrinks between `file.metadata()` and `read_buf_exact` so `read_buf_exact` returns `io::ErrorKind::UnexpectedEof`, `read_binary_file` drops the buffer and executes `return fs::read(path).map(Vec::into);`—**re-opening `path` by name a second time**.
  - **Concurrent growth / pipe probe (`source_map.rs:135-159`):** After filling `len` bytes, `read_binary_file` issues a 32-byte probe `file.read(&mut probe)`. If `Ok(0)`, it returns `unsafe { bytes.assume_init() }`; if `Ok(n)` with $n > 0$ (the file grew after `fstat`, or `st_size == 0` on a FIFO or `/proc` file), it copies the initial `len` bytes plus `probe[..n]` into a `Vec<u8>` and calls `file.read_to_end(&mut bytes)?`.

#### 2.2 Unconditional Disk Read in `SourceMap::load_file` vs. Post-Read Cache Dedup (`source_map.rs:280-383`)

`SourceMap::load_file` (`compiler/rustc_span/src/source_map.rs:280-284`) and `try_new_source_file` (`source_map.rs:360-383`) are structured as follows:

```rust
pub fn load_file(&self, path: &Path) -> io::Result<Arc<SourceFile>> {
    let src = self.file_loader.read_file(path)?;
    let filename = FileName::Real(self.path_mapping.to_real_filename(&self.working_dir, path));
    Ok(self.new_source_file(filename, src))
}

fn try_new_source_file(
    &self,
    filename: FileName,
    src: String,
) -> Result<Arc<SourceFile>, OffsetOverflowError> {
    let stable_id = StableSourceFileId::from_filename_in_current_crate(&filename);
    match self.source_file_by_stable_id(stable_id) {
        Some(lrc_sf) => Ok(lrc_sf),
        None => {
            let source_file = SourceFile::new(
                filename,
                src,
                self.hash_kind,
                self.checksum_hash_kind,
            )?;
            debug_assert_eq!(source_file.stable_id, stable_id);
            self.register_source_file(stable_id, source_file)
        }
    }
}
```

This ordering produces three distinct consequences verified in [`support/rustc_concurrent_source_probes.py`](support/rustc_concurrent_source_probes.py) ([`support/rustc_probe_results.json`](support/rustc_probe_results.json)):
1. **Every `load_file(path)` call performs disk I/O via `FileLoader::read_file(path)` before checking `stable_id_to_source_file`.** When `stable_id` is already present in `SourceMapFiles::stable_id_to_source_file` (`source_map.rs:171-175`), `try_new_source_file` returns the **first** cached `Arc<SourceFile>` and silently drops the newly read `src: String`.
2. **Deleting an already-cached file breaks a second `include!` (`Experiment 3c`):** Because `self.file_loader.read_file(path)?` executes at line 281 before the cache lookup at line 366, unlinking `./shared.rs` on disk after an initial `include!("./shared.rs")` causes a second `include!("./shared.rs")` in the same crate to fail with `error: couldn't find file './shared.rs'` even though its `SourceFile` is already in `SourceMap`.
3. **Divergence between `load_file` (`mod` / `include!`) and `load_binary_file` (`include_str!` / `include_bytes!`) (`Experiments 3a & 3b`):**
   - Both `expand_include_str` (`compiler/rustc_builtin_macros/src/source_util.rs:204-233`) and `expand_include_bytes` (`source_util.rs:238-262`) call `source_util::load_binary_file` (`source_util.rs:264-313`) $\to$ `SourceMap::load_binary_file` (`source_map.rs:290-310`):
     ```rust
     pub fn load_binary_file(&self, path: &Path) -> io::Result<(Arc<[u8]>, Span)> {
         let bytes = self.file_loader.read_binary_file(path)?;
         let text = std::str::from_utf8(&bytes).unwrap_or("").to_string();
         let filename = FileName::Real(self.path_mapping.to_real_filename(&self.working_dir, path));
         let file = self.new_source_file(filename, text);
         Ok((
             bytes,
             Span::new(
                 file.start_pos,
                 BytePos(file.start_pos.0 + file.normalized_source_len.0),
                 SyntaxContext::root(),
                 None,
             ),
         ))
     }
     ```
   - Because `load_binary_file` returns the freshly read `bytes` directly rather than reading from `file.src`, calling `include_str!("./shared.rs")` and `include_bytes!("./shared.rs")` before and after a FIFO-synchronized on-disk edit (`pub const V: u32 = 1;` $\to$ `pub const V: u32 = 2;`) embeds **both** versions (`STR_BEFORE = "pub const V: u32 = 1;"`, `STR_AFTER = "pub const V: u32 = 2;"`), whereas calling `include!("./shared.rs")` before and after the same edit evaluates to `V = 1` both times (**Experiment 3a**).
   - Conversely, because `load_binary_file` calls `self.new_source_file(filename, text)`, calling `include_bytes!("./shared.rs")` *before* the on-disk edit populates `SourceMap` for `"./shared.rs"` with `V = 1`; a subsequent `#[path = "./shared.rs"] mod shared_same_path;` or `include!("./shared.rs")` expanded *after* the on-disk edit hits the `SourceMap` cache and compiles the stale `V = 1` code (**Experiment 3b**).

#### 2.3 Non-Canonical `StableSourceFileId` Cache Keys and Single-File Split-Brain (`Experiments 2 & 3b`)

`StableSourceFileId` (`compiler/rustc_span/src/lib.rs:2132-2155`) hashes `(filename: &FileName, stable_crate_id: Option<StableCrateId>)`. `FilePathMapping::to_real_filename` (`compiler/rustc_span/src/source_map.rs:1229-1288`) stores `local_path.to_path_buf()` directly in `InnerRealFileName::name` (`lib.rs:342-358`) without calling `std::fs::canonicalize`, without collapsing `..`, without resolving symlinks, and without stripping a leading `./` (`Component::CurDir`, which `std::path::Path::hash` preserves).

Consequently, in **Experiment 2** (`exp2_single_file_split_brain`), when `main.rs` declares:
```rust
#[path = "./shared.rs"] mod a;
mod gate; // named FIFO
#[path = "./sub/../shared.rs"] mod b;
#[path = "./sym_shared.rs"] mod c;
```
and `shared.rs` (inode `8801479`) is rewritten from `pub const V: u32 = 1;` to `pub const V: u32 = 2;` while `rustc` is blocked on `gate.rs`, `rustc` computes three distinct `StableSourceFileId`s for the same physical inode and compiles a single binary that outputs `a=1, b=2, c=2`.

#### 2.4 Two-Phase AST Expansion Ordering (`collect_invocations` Before Macro Expansion, `Experiment 3e`)

In `compiler/rustc_expand/src/expand.rs:471-600`, `MacroExpander::fully_expand_fragment` expands each AST fragment in two steps:
1. It calls `self.collect_invocations(input_fragment, &[])` (`expand.rs:476`), whose AST visitor `InvocationCollector` (`expand.rs:1393-1432`) **immediately loads and parses every static out-of-line `mod foo;` declaration** via `parse_external_mod` (`expand.rs:1407-1431` $\to$ `compiler/rustc_expand/src/module.rs:52-94`) while queuing macro invocations into a worklist.
2. Only after `collect_invocations` finishes walking the fragment does the loop at `expand.rs:492-599` pop and expand macro invocations (`include!`, `include_str!`, `include_bytes!`, `macro_rules!`, procedural macros).

In **Experiment 3e**, `main.rs` places `pub static PAYLOAD: &str = include_str!("./data.txt");` on line 3 and `mod gate;` (a FIFO) on line 4. Because `collect_invocations` loads `mod gate;` before expanding `include_str!("./data.txt")`, mutating `data.txt` while `rustc` is blocked opening `gate.rs` causes line 3's `include_str!` to read the post-gate mutation (`PAYLOAD = "T1_DURING_MOD_GATE"`).

#### 2.5 `SourceFile::new` Pre-Normalization Hashing vs. `ensure_source_file_source_present` (`Experiments 4a–4d`)

1. **Pre-normalization `src_hash` and `checksum_hash` (`compiler/rustc_span/src/lib.rs:2160-2206`):**
   `SourceFile::new` computes `src_hash = SourceFileHash::new_in_memory(hash_kind, src.as_bytes())` (default `Md5` on non-MSVC targets, `Sha256` on MSVC per `compiler/rustc_session/src/config.rs:1578-1586`), `checksum_hash`, and `unnormalized_source_len` on the **raw unnormalized `String`** *before* `normalize_src(&mut src)` (`lib.rs:2552-2626`) strips a leading UTF-8 BOM (`\u{feff}`) and converts `\r\n` to `\n`.
2. **Local vs. imported `SourceFile`s in `ensure_source_file_source_present` (`source_map.rs:1096-1121`, `lib.rs:2292-2327`):**
   - Local crate `SourceFile`s set `src: Some(Arc::new(src))` and `external_src: FreezeLock::frozen(ExternalSource::Unneeded)`. `ensure_source_file_source_present` immediately returns `true` without touching disk; diagnostics on local files always display the initial in-memory `src` even if the file on disk was overwritten before type-checking diagnostics fire (**Experiment 4d**).
   - Imported `SourceFile`s decoded from upstream `.rmeta` metadata (`compiler/rustc_metadata/src/rmeta/decoder.rs:1702-1909`) have `src: None` and `external_src: FreezeLock::new(ExternalSource::Foreign { kind: ExternalSourceKind::AbsentOk, .. })`. When a diagnostic emitter (`compiler/rustc_errors/src/emitter.rs:691`, `annotate_snippet_emitter_writer.rs:224, 292, 359`, `json.rs:556`) or `-Z embed-source` debuginfo (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:625`) calls `ensure_source_file_source_present`, `add_external_src` reads the upstream `.rs` file from disk and checks `if self.src_hash.matches(&src)` (`lib.rs:2300`) on the pre-normalized string.
   - If the upstream `.rs` file was modified on disk after `libdep.rlib` was built—whether with the exact same byte length (**Experiment 4b**) or a different byte length (**Experiment 4c**)—`self.src_hash.matches(&src)` returns `false`, `add_external_src` sets `kind = ExternalSourceKind::AbsentErr` and returns `false`, and `AnnotateSnippetEmitter` routes the span to `unannotated_messages` (`annotate_snippet_emitter_writer.rs:229-239`), printing `--> dep.rs:1:7` and silently omitting the source snippet. (`SourceFile::src_modified` at `lib.rs:2285-2290` has zero callers in `compiler/`.)

#### 2.6 `Mmap` of Binary `.rmeta`, `.rlib`, and Incremental Cache Files (`compiler/rustc_data_structures/src/memmap.rs:13-30`)

While `rustc` reads `.rs` source files into heap `String`s, it maps binary `.rmeta`/`.rlib` metadata (`compiler/rustc_metadata/src/locator.rs:944`) and incremental cache files (`dep-graph.bin`, `work-products.bin`, `query-cache.bin` in `compiler/rustc_incremental/src/persist/file_format.rs:124-130`) via `Mmap::map` (`memmap2::MmapOptions::new().map_copy_read_only(&file)`, i.e. `MAP_PRIVATE`), whose safety comment notes:

```rust
/// # Safety
///
/// The given file must not be mutated (i.e., not written, not truncated, ...) until the mapping is closed.
/// However in practice most callers do not ensure this, so uses of this function are likely unsound.
```

---

### 3. Clang/LLVM `llvm::MemoryBuffer` `mmap` Mechanics vs. GCC `libcpp`, Go `cmd/compile`, and `javac`

`Basis: source + execution`

#### 3.1 `shouldUseMmap` and `getOpenFileImpl` in LLVM 19.1.7 (`llvm/lib/Support/MemoryBuffer.cpp:358-536`)

In `llvm/llvm-project@cd708029e0b2869e80abe31ddb175f7c35361f90` (`llvm/lib/Support/MemoryBuffer.cpp:358-411`), `shouldUseMmap` governs when `MemoryBuffer::getOpenFile` maps a file via `mmap` (`MAP_PRIVATE`) versus reading it into a heap buffer via `sys::fs::readNativeFileSlice` (`pread64`):

```cpp
static bool shouldUseMmap(sys::fs::file_t FD,
                          size_t FileSize,
                          size_t MapSize,
                          off_t Offset,
                          bool RequiresNullTerminator,
                          int PageSize,
                          bool IsVolatile) {
  // mmap may leave the buffer without null terminator if the file size changed
  // by the time the last page is mapped in, so avoid it if the file size is
  // likely to change.
  if (IsVolatile && RequiresNullTerminator)
    return false;

  // We don't use mmap for small files because this can severely fragment our
  // address space.
  if (MapSize < 4 * 4096 || MapSize < (unsigned)PageSize)
    return false;

  if (!RequiresNullTerminator)
    return true;
  ...
  // Don't try to map files that are exactly a multiple of the system page size
  // if we need a null terminator.
  if ((FileSize & (PageSize -1)) == 0)
    return false;

  return true;
}
```

1. **Why Clang requires a NUL sentinel at `BufEnd[0]`:** `clang::Lexer::InitLexer` (`clang/lib/Lex/Lexer.cpp:128-136`) asserts `assert(BufEnd[0] == 0 && "We assume that the input buffer has a null character at the end to simplify lexing!");`. When `FileSize >= 16384` and `FileSize % 4096 != 0`, `mmap` relies on the OS kernel zero-filling the remainder of the last partial page so `BufEnd[0]` is `\0`. When `FileSize` is an exact multiple of $4096\text{ B}$ (such as $16{,}384\text{ B}$ in **Experiment 1**), no trailing byte exists on the mapped page, so `shouldUseMmap` returns `false` and `getOpenFileImpl` allocates a heap buffer with `Buf[Size] = 0` (`MemoryBuffer.cpp:343, 512-535`).
2. **Non-`mmap` heap read truncation handling (`MemoryBuffer.cpp:520-534`):** When `shouldUseMmap` returns `false`, `getOpenFileImpl` loops over `sys::fs::readNativeFileSlice(FD, ToRead, Offset)`; if the file shrank after `fstat` so `*ReadBytes == 0` before `ToRead` is full, line 528 zero-fills the remainder (`std::memset(ToRead.data(), 0, ToRead.size())`).Separately, `ContentCache::getBufferOrNone` (`clang/lib/Basic/SourceManager.cpp:169-175`) checks `Buffer->getBufferSize() != (size_t)ContentsEntry->getSize()` against any prior cached `stat` entry and emits `diag::err_file_modified` if the size changed before open.
3. **`UserFilesAreVolatile` in `clang` vs. `libclang`/`clangd`:** Standalone `clang -cc1` defaults `UserFilesAreVolatile` to `false` (`clang/include/clang/Lex/HeaderSearchOptions.h:204`, `clang/lib/Frontend/CompilerInvocation.cpp:3245`, overridden only by `-fsystem-headers-volatile`), whereas `libclang` (`clang/tools/libclang/CIndex.cpp:4128`) and `ASTUnit` (`clang/lib/Frontend/ASTUnit.cpp:1933`) set `UserFilesAreVolatile = true` so IDE buffers never `mmap` user source files.
4. **Empirical `mmap` concurrency failures in `clang-19` vs. `gcc-15` ([`support/compiler_mmap_and_fifo_probes.py`](support/compiler_mmap_and_fifo_probes.py)):**
   - **Experiment 2a (In-place page-cache overwrite after `close(fd)`):** `main.c` includes a $20{,}000\text{ B}$ header `large_header.h` defining `#define LATE_MACRO 100` on page 3 (offset $12{,}435$), then blocks on `#include "gate.fifo"`. While blocked at `gate.fifo` (after `large_header.h` has already been lexed and its fd closed), the harness overwrites `100` with `211` via `os.pwrite`. When `main()` expands `LATE_MACRO` after `gate.fifo`, `clang-19` reads the token spelling from its `MAP_PRIVATE` mapping (`clang/lib/Lex/Preprocessor.cpp` / `LiteralSupport.cpp`) and compiles a binary returning **`211`**, whereas `gcc-15` compiles a binary returning **`100`**.
   - **Experiment 2b (`ftruncate(0)` after `close(fd)` $\to$ `SIGBUS`):** Truncating `large_header.h` to $0\text{ B}$ while paused at `gate.fifo` causes `clang-19` to crash with **`SIGBUS` (`Bus error (core dumped)`, exit code `254`)** when expanding `LATE_MACRO` at `main.c:3:25`, whereas `gcc-15` compiles cleanly and returns **`100`**. (Without `-fno-crash-diagnostics`, the `clang` driver also spawns a second `clang -cc1 -E -frewrite-includes` crash-reproducer process that re-opens every `#include` file from scratch.)
   - **Experiment 2c (Appending past EOF on the last partial page corrupts `BufEnd[0]`):** When `large_header.h` ($20{,}000\text{ B}$) includes `gate.fifo` at line 126 and the harness appends `int appended_past_eof = 99;\n` at offset $20{,}000$ while blocked at `gate.fifo`, the non-zero `'i'` overwrites the kernel-zeroed NUL sentinel at `BufEnd[0]`. Upon resuming `large_header.h`, `clang-19`'s lexer overruns `BufferEnd`, emits 480 `warning: null character ignored [-Wnull-character]` diagnostics across the rest of the $4096\text{ B}$ page, and crashes with **`SIGBUS` (exit code `254`)** inside `clang::Lexer::LexTokenInternal` on the next page boundary, whereas `gcc-15` exits `0` with no warnings.
5. **Clang PCH / Module AST Validation (`clang/lib/Serialization/ASTReader.cpp:2533-2695`):** `ASTReader::getInputFile` checks `StoredSize != File->getSize()` and `StoredTime != File->getModificationTime()`, and when `ValidateASTInputFilesContent` is enabled, computes `xxh3_64bits(MemBuffOrError.get()->getBuffer())` against `StoredContentHash`.

#### 3.2 GCC `libcpp` (`libcpp/files.cc:725-1037`) and Re-Included Unguarded Headers (`Experiment 2d`)

In `gcc-mirror/gcc@5115c7e447fc07457443df874bf57840e8316d5f` (`libcpp/files.cc:726-834`), `read_file_guts` allocates a heap buffer `buf = XNEWVEC (uchar, size + pad)` (`pad = CPP_BUFFER_PADDING`), loops `read(file->fd, buf + total, size - total)` until `total == size` or EOF, emits a warning (`"%s is shorter than expected"`, lines 794–796) if a regular file shrank between `fstat` and `read`, and immediately closes `file->fd` (`files.cc:830`).

However, because GCC's lexer (`_cpp_clean_line` in `libcpp/lex.cc`) mutates the buffer in place while lexing, `_cpp_stack_file` (`libcpp/files.cc:1021-1022`) invalidates the cached buffer pointer immediately upon stacking:
```c
/* Clear buffer_valid since _cpp_clean_line messes it up.  */
file->buffer_valid = false;
file->stack_count++;
```
When a header is `#include`d a second time, `_cpp_stack_file` first checks `is_known_idempotent_file` (`files.cc:839-873`), which skips the file if `file->once_only` (`#pragma once` / `#import`) or `file->cmacro && cpp_macro_p(file->cmacro)` (standard `#ifndef` guard) holds. For an **unguarded header** (such as an X-macro `.def` / `.h` file included multiple times with different macro definitions), `is_known_idempotent_file` returns `false`, `read_file` sees `file->buffer_valid == false`, and GCC **re-opens and re-reads the file from disk**. In **Experiment 2d**, re-including a $1{,}000\text{ B}$ unguarded header before and after `gate.fifo` yields `(first_inc, second_inc) = (1, 2)` in `gcc-15` (exit code `12`), versus `(1, 1)` in `clang-19` (exit code `11`).

#### 3.3 Go `cmd/compile` (`go1.27.3`) and OpenJDK `javac` (`27.0.1`)

- In `golang/go@2aae1000ea1d4b28923b96db28acf4e3b99d6aff`, `LoadPackage` (`src/cmd/compile/internal/noder/noder.go:27-60`) spawns up to `runtime.GOMAXPROCS(0)+10` concurrent goroutines to open (`os.Open(filename)`) and parse all `.go` files in a package in parallel. Each goroutine streams its file through `syntax.source.fill` (`src/cmd/compile/internal/syntax/source.go:180-218`), starting with a $4\text{ KiB}$ buffer (`min = 4 << 10`, reading $4095\text{ B}$ chunks to leave 1 byte for `sentinel = utf8.RuneSelf`) and doubling up to $1\text{ MiB}$. Consequently, Go has both an inter-file concurrent open window across package goroutines and a multi-`read()` intra-file window for files $> 4095\text{ B}$.
- OpenJDK `javac` (`27.0.1`) `statx`/`fstat`s each `.java` file and reads its full `st_size` into a heap buffer in a single `read(fd, buf, st_size)` syscall followed by a 1-byte EOF check `read(fd, "", 1) = 0` and `close(fd)`.

---

### 4. Build-Orchestrator Freshness Races: Cargo (`Mtime` and `-Z checksum-freshness`), Make, Ninja, and Bazel

`Basis: source + execution`

Auditing `rust-lang/cargo` at `3c0b534756e166d12eb9fd2e1abfe5b42ac6101e` and `3960fa69bb617e3d93c4ddc087c1b32bf12ad907` alongside `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`compiler/rustc_interface/src/passes.rs:591-656`) and executing the Cargo and GNU Make probes in [`support/cargo_and_driver_toctou_probes.py`](support/cargo_and_driver_toctou_probes.py) ([`support/cargo_and_driver_probe_results.json`](support/cargo_and_driver_probe_results.json)) establishes how build systems behave when a source file is edited at $t_2$ while compilation is in flight ($t_0 \le t_{\text{read}} < t_2 < t_{\text{end}}$):

| Orchestrator & Mode | Reference Anchor | Strictness of Freshness Comparison | Mid-Build Edit Poisoning Window | Empirical Verification (`support/cargo_and_driver_probe_results.json`) |
| :--- | :--- | :--- | :--- | :--- |
| **GNU Make `4.4.1`** & **Ninja** | `mtime(output)` written when compiler exits at $t_3$ | Rebuild iff `mtime(input) > mtime(output)` | **Full $[t_{\text{read}}, t_3]$ compilation duration** | **Probe 3 (`probe_3_gnu_make`):** Editing `main.c` while `gcc` is paused on `gate.h` leaves `mtime(main.c) < mtime(app)` ($1794451115.688\text{ s} < 1794451115.717\text{ s}$); subsequent `make` prints `'app' is up to date` with `MAKE_V1` binary and `MAKE_V2` source on disk. |
| **Cargo Default (`FingerprintMethod::Mtime`)** | `invoked.timestamp` created at $t_0$ before `rustc` spawns (`src/compiler/mod.rs:464`); `dep-bin-<pkg>` rewound to $t_0$ at $t_3$ via `set_file_time_no_err` (`mod.rs:562`) | `if path_mtime <= reference_mtime { continue; }` (`src/compiler/fingerprint/mod.rs:2208-2229`, `cargo#5918`) | **Same-tick window $t_2 == t_0$** (1–4 ms Linux coarse timer tick, 1 s HFS+/ext3, 2 s FAT, or zeroed Docker layer ns) or if `set_file_time_no_err` fails | **Probe 1A ($t_2 > t_0$):** Rebuilds cleanly (`build2_rebuilt: true`).<br>**Probe 1B ($t_2 == t_0$):** Permanently caches stale `VERSION_1` binary (`build2_rebuilt: false`, `stale_binary_permanently_cached: true`). |
| **Cargo `-Z checksum-freshness` (`build.fingerprint="content"`) — Single `SourceMap` Read** | `SourceFile::new` in-memory `checksum_hash` (`blake3`) at $t_1$ (`rustc_span/src/lib.rs:2168-2174`) | `compute_file_checksum(&path) != recorded_checksum` (`fingerprint/mod.rs:2174`) | **None** for a file read once via `SourceMap` and absent from `sess.file_depinfo` | **Probe 2A (`2a_single_sourcemap_read_detects_edit`):** `.d` records `blake3(CHECKSUM_V1)`; next build detects `CHECKSUM_V2_MODIFIED` on disk and rebuilds (`build2_rebuilt: true`). |
| **Cargo `-Z checksum-freshness` — Bug #1: `sess.file_depinfo` Post-Expansion On-Disk Re-Hash** | `passes::write_out_deps` $\to$ `hash_iter_files` (`rustc_interface/src/passes.rs:614-650`) opens `sess.file_depinfo` files from disk at $t_{\text{depinfo}} > t_2$ and calls `files.extend(extra_tracked_files)` | Overwrites $t_1$ `SourceMap` checksum in `.d` with $t_{\text{depinfo}}$ on-disk checksum | **Full $[t_1, t_{\text{depinfo}}]$ window** for any file in `sess.file_depinfo` (`include_str!`, `include_bytes!`, `proc_macro::tracked::path`) | **Probe 2B (`2b_tracked_path_post_expansion_hash_poisoning`) & Track 1 Exp 3d:** Binary embeds `"MAIN_V1:DATA_V1"`, `.d` records Blake3 of `MAIN_V2` and `DATA_V2_MODIFIED`, and next `cargo build -Z checksum-freshness --config 'build.fingerprint="content"'` permanently caches the stale binary (`build2_rebuilt: false`). |
| **Cargo `-Z checksum-freshness` — Bug #2: Non-Canonical Alias Overwrite in `parse_dep_info`** | `rustc` emits two `# checksum:` lines (`src/main.rs` at $t_1$ and `src/./main.rs` at $t_2$); Cargo's `translate_dep_info` (`dep_info.rs:360`) canonicalizes both to `src/main.rs`, and `parse_dep_info` (`dep_info.rs:505`) inserts into `HashMap` | Later alias entry ($t_2$) overwrites earlier primary entry ($t_1$) in `ret.files` | **Full $[t_1, t_2]$ window** between primary module parse and alias read | **Probe 2C (`2c_non_canonical_alias_depinfo_overwrite_poisoning`):** Binary outputs `"CODE_V1"`, `src/./main.rs` read at $t_2$ overwrites `src/main.rs` checksum with `blake3(CODE_V2_UPDATED)`, and next `cargo build -Z checksum-freshness --config 'build.fingerprint="content"'` permanently caches the stale binary (`build2_rebuilt: false`). |
| **Bazel (`SkyframeActionExecutor`)** | Pre-action `FileArtifactValue` `(digest, size, mtime/ctime, inode)` $M_{\text{pre}}$ before spawning action + Linux mount sandbox | Action cache keyed by $M_{\text{pre}}$; post-action `FileSystemValueChecker` verifies $M_{\text{pre}} == M_{\text{post}}$ | **None** (aborts build with `ModifiedInputFileException` if an input changes mid-action) | Architectural reference (`SkyframeActionExecutor` / `ActionExecutionFunction`). |

*(Note: `compiler/rustc_interface/src/passes.rs:646` also contains a double-escaping defect where `.map(escape_dep_filename)` is applied to `sess.file_depinfo` paths before passing them to `hash_iter_files`, which then calls `fs::File::open(path)` on the backslash-escaped path string and calls `escape_dep_filename` a second time at line 623.)*

---

### 5. Hermetic Source-to-MIR Binding Patterns for `rustc_driver` Verifiers

`Basis: source + execution + derived`

A formal verification tool or static analyzer built on `rustc_driver` requires a stronger property than build-cache invalidation: **every byte parsed, macro-expanded, and lowered into the analyzed HIR/MIR must originate from a single immutable file snapshot $(P_i \mapsto D_i)$ whose cryptographic digests $H(D_i)$ match the emitted verification certificate.**

Evaluating the five `rustc_driver` input-binding designs in [`support/cargo_and_driver_toctou_probes.py`](support/cargo_and_driver_toctou_probes.py) (`probe_4_rustc_driver_verification_patterns` in [`support/cargo_and_driver_probe_results.json`](support/cargo_and_driver_probe_results.json)):

| Pattern | Mechanism | Vulnerable To | Empirical Probe Result (`cargo_and_driver_probe_results.json`) |
| :--- | :--- | :--- | :--- |
| **Pattern 1: External Pre-Hash Only ($H_{\text{pre}}$)** | Hash source files on disk before invoking `rustc`, then run `rustc`. | Edits in $(t_{\text{pre}}, t_{\text{read}})$ (`rustc` compiles $V_2$; certificate binds $H(V_1)$) and undeclared `#[path]` / `include!` files. | **`pattern1_pre_hash`:** `pre_hash_version = "101"`, `compiled_version = "202"`, `soundness_broken: true`. |
| **Pattern 2: External Post-Hash Only ($H_{\text{post}}$)** | Run `rustc`, then hash files listed in `SourceMap` or `.d` on disk after compilation finishes. | Edits in $(t_{\text{read}}, t_{\text{post}})$ (`rustc` compiles $V_1$; certificate binds $H(V_2)$). | **`pattern2_post_hash`:** `compiled_version = "101"`, `post_hash_matches_202: true`, `soundness_broken: true`. |
| **Pattern 3: External $H_{\text{pre}} == H_{\text{post}}$ Without In-Process `FileLoader`** | Hash files on disk before and after `rustc`, requiring $H_{\text{pre}} == H_{\text{post}}$. | **ABA race ($A \to B \to A$)** during compilation ($H_{\text{pre}} = H(A) = H_{\text{post}}$, while `rustc` compiled $B$) and undeclared mid-build files. | **`pattern3_aba`:** `pre_eq_post: true`, `verified_hash_version = "101"`, `compiled_version = "202"`, `aba_bypass_succeeded: true`. |
| **Pattern 4: In-Process `Config::file_loader` (`RecordingFileLoader`) + Canonical-Path & `(st_dev, st_ino)` Single-Hash Invariant + Session Audit** | 1. Install `interface::Config::file_loader` (`compiler/rustc_interface/src/interface.rs:63`).<br>2. In `read_file` / `read_binary_file`, open one `fs::File`, read bytes into memory, query `file.metadata()` (`fstat` on open fd), and compute `sha256(bytes)` on the exact buffer returned to `rustc`.<br>3. Enforce allowlist membership and single-hash consistency keyed by **both** `fs::canonicalize(path)` and `(meta.dev(), meta.ino())`.<br>4. In `after_analysis`, verify every local `SourceFile` in `tcx.sess.source_map().files()` and every path in `tcx.sess.file_depinfo` is recorded in `RecordingFileLoader`, `tcx.sess.env_depinfo` is empty, and $H_{\text{pre}} == H_{\text{in-memory}} == H_{\text{post}}$. | Closes all `SourceMap`, symlink/relative-path alias, hardlink alias, and ABA races.<br>**Residual boundary:** An un-sandboxed procedural macro calling `std::fs::read` directly without `proc_macro::tracked::path` bypasses both `FileLoader` and `file_depinfo`. | **`pattern4_aba_caught`:** `rejected: true` (`Pre-hash != in-memory FileLoader hash`).<br>**`pattern4_alias_caught`:** `rejected: true` (`Canonical-path hash mismatch`).<br>**`pattern4_hardlink_caught`:** `rejected: true` (`Hardlink/inode ((45, 44529424)) hash mismatch`).<br>**`pattern4_untracked_proc_macro_gap`:** `secret_file_in_rustc_dep_info: false`. |
| **Pattern 5: Preloaded In-Memory `VirtualFileLoader` + Read-Only / Sandboxed Private Staging** | Preload all declared source files into an immutable `BTreeMap<PathBuf, Arc<[u8]>>` before `compiler_entrypoint`, serve all `FileLoader` reads purely from memory, and (when proc macros are enabled) execute inside a fresh read-only staging directory or mount namespace (`CLONE_NEWNS` / `bwrap --ro-bind`). | **None** (immune to concurrent disk mutations, path/hardlink aliasing, and untracked proc-macro host reads). | **`pattern5_vfs_immune`:** Despite on-disk overwrites to `202` before compile and `303` mid-compile across `lib.rs` and `include_str!("./lib.rs")`, `compiled_version = "101"` and `all_sourcemap_entries_match_vfs_snapshot: true`. |

Why **both** `fs::canonicalize(path)` and `(meta.dev(), meta.ino())` on the open file descriptor are required in Pattern 4 when running outside a fresh staging directory:
- `SourceMap` keys its internal cache by un-canonicalized `FileName`, so `./lib.rs` and `sub/../lib.rs` both invoke `FileLoader::read_file`. Canonicalizing via `fs::canonicalize` collapses symlinks, `.`, and `..` to a single `PathBuf` key (`pattern4_alias_caught`).
- However, `fs::canonicalize` does **not** collapse POSIX hardlinks: two hardlinks `/dir/lib.rs` and `/dir/hardlink_lib.rs` resolve to two distinct canonical `PathBuf`s that share the same underlying inode `(meta.dev(), meta.ino())`. Checking `fstat` `(st_dev, st_ino)` on the open `File` handle detects any mid-compilation mutation across hardlinks (`pattern4_hardlink_caught`), while copying declared inputs into a fresh per-invocation staging directory before compilation eliminates external hardlinks altogether.

---

## Boundaries

1. **Untracked Native Execution in Procedural Macros and Build Scripts (`supported` only via OS sandboxing):**
   - Procedural macros (`#[proc_macro]`, `#[proc_macro_derive]`, `#[proc_macro_attribute]`) and Cargo build scripts (`build.rs`) execute arbitrary native host code. `Config::file_loader` intercepts only `SourceMap` operations (`rustc_parse`, `rustc_expand` module loading, `include!`, `include_str!`, `include_bytes!`, and `ensure_source_file_source_present`). A procedural macro that calls `std::fs::read` without calling `proc_macro::tracked::path` bypasses both `FileLoader` and `tcx.sess.file_depinfo`. Closing this channel when untrusted procedural macros are present requires OS-level filesystem isolation (such as a read-only `bwrap` / `CLONE_NEWNS` mount namespace or Landlock ruleset).
2. **Concurrent Mutation of Binary `.rmeta` / `.rlib` and Incremental Cache Artifacts (`unsupported` by `rustc`):**
   - `rustc` maps binary crate metadata (`.rmeta`, `.rlib`) and incremental compilation cache files (`dep-graph.bin`, `work-products.bin`, `query-cache.bin`) via `memmap2::MmapOptions::new().map_copy_read_only` (`compiler/rustc_data_structures/src/memmap.rs:13-30`) outside `FileLoader`. Concurrent truncation or in-place overwrite of these binary artifacts by another process is explicitly documented by `rustc` as unsound and can trigger `SIGBUS` or metadata decoder panics.
3. **Network and Non-POSIX Filesystems (`not examined`):**
   - All empirical `mmap`, page-cache, `inotify`/FIFO, and timestamp-granularity probes were executed on Linux (`x86_64-unknown-linux-gnu`) over local POSIX filesystems (`ext4` / `tmpfs`). Behavior on Windows (`MapViewOfFile` file-sharing locks) or network filesystems (NFS/SMB cache-coherency windows) was not empirically tested.

---

## Evidence

### 1. Primary Upstream Source Coordinates

- **`rust-lang/rust` (`49d734536222bf28bb6d07d885b3a81d145981da`):**
  - `compiler/rustc_span/src/source_map.rs:80-182, 280-426, 1096-1121, 1229-1288` (`FileLoader`, `RealFileLoader`, `SourceMap::load_file`, `load_binary_file`, `try_new_source_file`, `ensure_source_file_source_present`, `FilePathMapping::to_real_filename`).
  - `compiler/rustc_span/src/lib.rs:327-358, 2132-2327, 2552-2626` (`RealFileName::hash`, `StableSourceFileId`, `SourceFile::new`, `add_external_src`, `src_modified`, `normalize_src`).
  - `compiler/rustc_expand/src/expand.rs:471-600, 1393-1432` and `compiler/rustc_expand/src/module.rs:52-94, 159-228` (`MacroExpander::fully_expand_fragment`, `InvocationCollector`, `parse_external_mod`).
  - `compiler/rustc_builtin_macros/src/source_util.rs:98-313` (`expand_include`, `expand_include_str`, `expand_include_bytes`, `load_binary_file`).
  - `compiler/rustc_interface/src/passes.rs:55-86, 591-656` (`passes::parse`, `hash_iter_files`, `write_out_deps`).
  - `compiler/rustc_errors/src/emitter.rs:686-699` and `compiler/rustc_errors/src/annotate_snippet_emitter_writer.rs:224-308, 583-655` (`should_show_source_code`, `unannotated_messages`).
  - `compiler/rustc_data_structures/src/memmap.rs:13-30`, `compiler/rustc_metadata/src/locator.rs:944`, and `compiler/rustc_incremental/src/persist/file_format.rs:124-130` (`Mmap::map`).
- **`rust-lang/cargo` (`3c0b534756e166d12eb9fd2e1abfe5b42ac6101e` and `3960fa69bb617e3d93c4ddc087c1b32bf12ad907`):**
  - `src/compiler/mod.rs:464, 550-564, 871-884` (`set_invocation_time`, `translate_dep_info`, `set_file_time_no_err`, `FingerprintMethod::Content`).
  - `src/compiler/fingerprint/mod.rs:344-352, 896-912, 2151-2229` (`LocalFingerprint`, `find_stale_file`, `path_mtime <= reference_mtime`).
  - `src/compiler/fingerprint/dep_info.rs:319-510` (`translate_dep_info`, `try_canonicalize`, `parse_rustc_dep_info`, `parse_dep_info` `HashMap::insert` overwrite).
- **`llvm/llvm-project` (`cd708029e0b2869e80abe31ddb175f7c35361f90`, `llvmorg-19.1.7`):**
  - `llvm/lib/Support/MemoryBuffer.cpp:333-550` (`shouldUseMmap`, `getOpenFileImpl`).
  - `clang/lib/Basic/SourceManager.cpp:109-175, 318-323` (`ContentCache::getBufferOrNone`, `UserFilesAreVolatile`).
  - `clang/lib/Lex/Lexer.cpp:128-148` (`Lexer::InitLexer` `BufEnd[0] == 0`).
  - `clang/lib/Frontend/ASTUnit.cpp:1933` and `clang/tools/libclang/CIndex.cpp:4128` (`UserFilesAreVolatile = true`).
  - `clang/lib/Serialization/ASTReader.cpp:2533-2695` (`ASTReader::getInputFile`).
- **`gcc-mirror/gcc` (`5115c7e447fc07457443df874bf57840e8316d5f`, `releases/gcc-15.2.0`):**
  - `libcpp/files.cc:725-1037` (`read_file_guts`, `read_file`, `is_known_idempotent_file`, `_cpp_stack_file` `file->buffer_valid = false`).
- **`golang/go` (`2aae1000ea1d4b28923b96db28acf4e3b99d6aff`, `go1.27.3`):**
  - `src/cmd/compile/internal/noder/noder.go:27-60` (`LoadPackage`) and `src/cmd/compile/internal/syntax/source.go:40-218` (`source.fill`).

### 2. Preserved Package Support Artifacts

- [`support/rustc_concurrent_source_probes.py`](support/rustc_concurrent_source_probes.py) and [`support/rustc_probe_results.json`](support/rustc_probe_results.json): Standalone FIFO-synchronized `rustc 1.101.0-nightly` probe suite covering intra-crate temporal skew (`Exp 1`), non-canonical path and symlink split-brain (`Exp 2`), `include!` vs. `include_str!` vs. `include_bytes!` caching and deletion (`Exp 3a–3c`), `write_out_deps` `file_depinfo` post-expansion checksum mismatch (`Exp 3d`), `collect_invocations` `mod` vs. macro ordering (`Exp 3e`), and cross-crate `ensure_source_file_source_present` `src_hash` validation (`Exp 4a–4d`).
- [`support/compiler_mmap_and_fifo_probes.py`](support/compiler_mmap_and_fifo_probes.py) and [`support/compiler_probe_results.json`](support/compiler_probe_results.json): Standalone `strace` ingestion matrix across `clang-19`, `gcc-15`, `rustc`, `go tool compile`, and `javac` at $1{,}000\text{ B}$, $16{,}384\text{ B}$, and $20{,}000\text{ B}$ (`Exp 1`), plus FIFO-synchronized `clang-19` vs. `gcc-15` probes for in-place `mmap` page-cache mutation (`Exp 2a`), `ftruncate(0)` `SIGBUS` (`Exp 2b`), NUL-sentinel append overrun (`Exp 2c`), and re-included unguarded headers (`Exp 2d`).
- [`support/cargo_and_driver_toctou_probes.py`](support/cargo_and_driver_toctou_probes.py) and [`support/cargo_and_driver_probe_results.json`](support/cargo_and_driver_probe_results.json): Standalone probe suite for Cargo `Mtime` (`Probe 1A`, `Probe 1B`), Cargo `-Z checksum-freshness` (`Probe 2A`, `Probe 2B` `proc_macro::tracked::path` poisoning, `Probe 2C` non-canonical alias poisoning), GNU Make (`Probe 3`), and the five `rustc_driver` source-binding patterns (`Probe 4`, Patterns 1–5).

---

## Revalidation

Run the three self-contained probe suites from a checkout of this package:

```console
python3 reports/compiler-concurrent-source-modification-and-hermetic-input-binding/support/rustc_concurrent_source_probes.py
python3 reports/compiler-concurrent-source-modification-and-hermetic-input-binding/support/compiler_mmap_and_fifo_probes.py
python3 reports/compiler-concurrent-source-modification-and-hermetic-input-binding/support/cargo_and_driver_toctou_probes.py
```

1. **`rustc_concurrent_source_probes.py`** verifies that `Exp 1` outputs `first=10, second=20`, `Exp 2` outputs `a=1, b=2, c=2` from a single inode, `Exp 3a–3e` reproduce the `load_file` vs. `load_binary_file` and `write_out_deps` behaviors, and `Exp 4a–4d` reproduce cross-crate snippet suppression on modified `.rmeta` sources.
2. **`compiler_mmap_and_fifo_probes.py`** verifies the 15-cell `strace` syscall matrix (`clang-19` switching from `pread64` at $1{,}000\text{ B}$ and $16{,}384\text{ B}$ to `mmap` at $20{,}000\text{ B}$) and confirms `clang-19`'s live `mmap` token mutation (`211`), `SIGBUS` (`254`) on `ftruncate(0)` and EOF append, and `gcc-15`'s re-read of unguarded headers (`12` vs. `11`).
3. **`cargo_and_driver_toctou_probes.py`** verifies Cargo `Mtime` same-tick poisoning, both Cargo `-Z checksum-freshness` poisoning vectors (`tracked::path` and non-canonical path aliases), GNU Make mid-build poisoning, and `rustc_driver` Patterns 1–5.
