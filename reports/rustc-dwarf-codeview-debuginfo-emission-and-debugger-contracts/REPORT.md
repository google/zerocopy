# `rustc` 1.99.1 DWARF and CodeView Debuginfo Emission, Rust Type Conventions, and Debugger Acceptance Contracts

## Summary

`rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) emits debugging
information in two container families across the 8 Tier 1 targets:

1. **DWARF v4 (`0x0004`) by default on all 5 non-MSVC Tier 1 targets**
   (`x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`,
   `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, and
   `x86_64-pc-windows-gnu`), configurable to DWARF v2/v3/v4/v5 via
   `-Cdwarf-version=2|3|4|5` (`compiler/rustc_codegen_llvm/src/context.rs:545-580`).
2. **Microsoft CodeView (`.debug$S` symbols/lines and `.debug$T` type records in
   COFF `.obj`, linked into `.pdb` by `link.exe`/`lld-link`) on all 3 MSVC Tier
   1 targets** (`x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, and
   `aarch64-pc-windows-msvc`), paired with three in-tree Natvis visualizer files
   (`libcore.natvis`, `liballoc.natvis`, `libstd.natvis`) embedded via
   `/NATVIS:` linker arguments (`compiler/rustc_codegen_ssa/src/back/link.rs`).

`compiler/rustc_codegen_llvm/src/debuginfo/` lowers Rust's algebraic types,
generics, closures, and trait objects to two distinct representations (`enums/native.rs`
vs. `enums/cpp_like.rs` and `metadata.rs`):

- **DWARF (`enums/native.rs`)**: Emits native DWARF `DW_TAG_structure_type` with
  a nested `DW_TAG_variant_part` (`DW_AT_discr` pointing to the discriminant
  `DW_TAG_member`) and one `DW_TAG_variant` (`DW_AT_discr_value`) per active
  variant; niche-optimized enums (such as `Option<NonZeroU64>`) omit
  `DW_AT_discr_value` on the untagged data variant (`default` variant) and place
  the niche value on the empty variant.
- **CodeView (`enums/cpp_like.rs`)**: Because CodeView (`LF_STRUCTURE`,
  `LF_UNION`) lacks `DW_TAG_variant_part`, `rustc` synthesizes a C++-style
  tagged union struct (`enum$<TypeName>`) containing `Variant0`, `Variant1`, ...
  member structs and a `tag` field, decoded by `intrinsic.natvis` /
  `libcore.natvis`.
- **Debugger scripts and pretty-printers (`debuginfo/gdb.rs`)**: On ELF DWARF
  targets (when `!sess.oat_omit_gdb_pretty_printer_section()`), `rustc` emits a
  `.debug_gdb_scripts` section (`SHF_MERGE | SHF_STRINGS`) referencing
  `gdb_load_rust_pretty_printers.py`, paired with wrapper scripts `rust-gdb` and
  `rust-lldb` (`src/etc/`).
- **Acceptance test inventory and optimization quality metrics
  (`support/v9_debuginfo_inventory_and_metrics.json`)**: `rustc` 1.99.1's
  `tests/debuginfo/` suite comprises **192 test files** (`167` with `gdb-*`
  directives, `122` with `lldb-*` directives, and `69` with `cdb-*` Windows
  debugger directives). Empirical `llvm-dwarfdump --statistics` measurements
  show that `rustc_codegen_llvm` preserves **100% function location coverage
  (`5/5`) and 87.5%–100% parameter binary location coverage (`8/8` at `-O0`/`-O1`,
  `7/7` non-inlined params at `-O2`/`-O3`)**, whereas `rustc_codegen_cranelift`
  emits line tables and `DW_TAG_subprogram` entries (`5/5` functions with
  locations) **but 0% formal parameter and local variable locations (`0`
  `DW_TAG_formal_parameter` DIEs)**.

## Applicability

- **Primary baseline**: `rust-lang/rust` `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project`
  `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), cross-checked against
  `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`) and
  `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Scope**: Tier 1 debuginfo formats, split-debuginfo defaults, DWARF and
  CodeView representations for Rust constructs, Natvis and GDB/LLDB scripts,
  the 192-test `tests/debuginfo/` acceptance suite, and `llvm-dwarfdump
  --statistics` quality metrics.

## Findings

### 1. Tier 1 Debuginfo Formats, Versions, and Split-Debuginfo Defaults

`Basis: source + execution`

From `compiler/rustc_target/src/spec/` and empirical object inspection across all
8 Tier 1 targets (`support/v9_debuginfo_inventory_and_metrics.json`):

| Tier 1 Target | Format | Default DWARF / CV Version | Default `-Csplit-debuginfo` | Supported `-Csplit-debuginfo` Modes | Sections Emitted at `-Cdebuginfo=2` (`--emit=obj`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | DWARF | DWARF v4 (`0x0004`) | `off` | `off`, `packed` (`.dwp`), `unpacked` (`.dwo`) | `.debug_abbrev`, `.debug_info`, `.debug_aranges`, `.debug_str`, `.debug_pubnames`, `.debug_pubtypes`, `.debug_line`, `.debug_loc`, `.debug_ranges`, `.debug_gdb_scripts` (or `.debug_loclists`/`.debug_rnglists`/`.debug_str_offsets` at `-Cdwarf-version=5`) |
| `i686-unknown-linux-gnu` | DWARF | DWARF v4 (`0x0004`) | `off` | `off`, `packed`, `unpacked` | Same ELF DWARF v4 sections |
| `aarch64-unknown-linux-gnu` | DWARF | DWARF v4 (`0x0004`) | `off` | `off`, `packed`, `unpacked` | Same ELF DWARF v4 sections |
| `aarch64-apple-darwin` | DWARF | DWARF v4 (`0x0004`) | `unpacked` (for non-LTO) / `packed` (`.dSYM` via `dsymutil`) | `off`, `packed` (`dsymutil`), `unpacked` (`OSO` stabs in Mach-O pointing to `.o` files) | `__DWARF,__debug_abbrev`, `__debug_info`, `__debug_str`, `__debug_line`, `__debug_loc`, `__debug_ranges`, `__apple_names`, `__apple_types`, `__apple_namespac`, `__apple_objc` |
| `x86_64-pc-windows-msvc` | CodeView | CodeView C13 (`0x4`) | `packed` (`.pdb`) | `packed` (`.pdb`) | `.debug$S` (symbols, line numbers, checksums, inlinee lines) and `.debug$T` (`LF_*` type records) |
| `i686-pc-windows-msvc` | CodeView | CodeView C13 (`0x4`) | `packed` (`.pdb`) | `packed` (`.pdb`) | `.debug$S` and `.debug$T` |
| `aarch64-pc-windows-msvc` | CodeView | CodeView C13 (`0x4`) | `packed` (`.pdb`) | `packed` (`.pdb`) | `.debug$S` and `.debug$T` |
| `x86_64-pc-windows-gnu` | DWARF | DWARF v4 (`0x0004`) | `off` | `off` | PE/COFF `.debug_abbrev`, `.debug_info`, `.debug_line`, `.debug_str`, `.debug_loc`, `.debug_ranges`, `.debug_aranges` |

**Debuginfo levels (`-Cdebuginfo=`)**:
- `0` (`None`): No debuginfo sections emitted (note: `.eh_frame` / `.pdata`
  unwind tables are controlled separately by `uwtable` / `-Cforce-unwind-tables`).
- `line-directives-only`: Line tables for `#[track_caller]` / profiling only.
- `line-tables-only`: `.debug_line` and `DW_TAG_subprogram` / `DW_TAG_inlined_subroutine`
  for symbolicated backtraces without type or variable DIEs.
- `1` (`Limited`): Function signatures and type definitions for globals/functions,
  omitting local variable and parameter value locations.
- `2` (`Full`): Complete type, parameter, and local variable location tracking.

---

### 2. Rust Type Conventions in DWARF and CodeView (`debuginfo/metadata.rs`)

`Basis: source + execution`

`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs` and `metadata/enums/`
define exact structural encodings that `rust-gdb`, `rust-lldb`, and MSVC/CDB
Natvis rely on:

| Rust Construct | DWARF Encoding (`enums/native.rs`, `metadata.rs`) | CodeView Encoding (`enums/cpp_like.rs`, `metadata.rs`) |
| :--- | :--- | :--- |
| **Data Enums (`enum Shape`)** | `DW_TAG_structure_type` (`DW_AT_name = "Shape"`) containing a `DW_TAG_variant_part` whose `DW_AT_discr` references a hidden discriminant `DW_TAG_member`. Each variant is a `DW_TAG_variant` (`DW_AT_discr_value = i`) wrapping a `DW_TAG_member` of type `DW_TAG_structure_type` (`Circle`, `Rect`, `Empty`). | `LF_STRUCTURE` named `v9_specimen::Shape` (`enum2$<v9_specimen::Shape>`) containing a union of variant structs (`Variant0`, `Variant1`, ...) plus a `tag` field (`LF_ENUM`), formatted by Natvis rules. |
| **Niche-Optimized Enums (`Option<NonZeroU64>`, `Option<&T>`)** | `DW_TAG_variant_part` where the non-niche (`Some`) `DW_TAG_variant` has **no** `DW_AT_discr_value` (making it the DWARF default variant) and the niche (`None`) `DW_TAG_variant` carries `DW_AT_discr_value = 0`. | `cpp_like.rs` emits `enum2$<core::option::Option<...>>` with direct payload layout and a synthetic discriminant constant read by `libcore.natvis`. |
| **Slices (`&[T]`, `&str`) & Vec** | `DW_TAG_structure_type` named `&[T]` or `&str` with two `DW_TAG_member` fields: `data_ptr` (`DW_TAG_pointer_type` to `T` or `u8`) and `length` (`usize`). | `LF_STRUCTURE` (`slice2$<T>` / `ref$<str$>`) with `data_ptr` and `length` members (`LF_MEMBER`). |
| **Trait Objects (`&dyn Draw`)** | `DW_TAG_structure_type` named `&dyn v9_specimen::Draw` with two `DW_TAG_member` fields: `pointer` (`*mut u8`) and `vtable` (`*const [usize; N]`, aligned to pointer alignment, `metadata.rs:640-690`). | `LF_STRUCTURE` (`dyn$<v9_specimen::Draw>`) with `pointer` and `vtable` fields. |
| **Closures (`|x| ...`) & Coroutines** | `DW_TAG_structure_type` named `{closure_env#0}` inside the enclosing function's `DW_TAG_namespace`, with one `DW_TAG_member` per captured variable (named directly after the captured local!). Coroutines use `DW_TAG_variant_part` over suspension states (`Unresumed`, `Returned`, `Panicked`, `Suspend0`, ...). | `LF_STRUCTURE` (`closure_env$0`) with captured fields as `LF_MEMBER` records. |
| **Generics (`Foo<T, const N: usize>`)** | `DW_TAG_structure_type` carries both the monomorphized `DW_AT_name` (`"Foo<u32, 4>"`) and child `DW_TAG_template_type_parameter` / `DW_TAG_template_value_parameter` DIEs (`metadata.rs:1120-1190`). | `LF_STRUCTURE` with angle-bracketed type parameters in the CodeView type name. |

#### 2.1 Natvis Files and `.debug_gdb_scripts`

- **Natvis (`library/{core,alloc,std}/src/*.natvis`)**:
  - `library/core/src/libcore.natvis`: Visualizers for `Option`, `Result`,
    `NonNull`, `Cell`, `RefCell`, `UnsafeCell`, `Pin`, `Range`, `Poll`, and
    atomic types.
  - `library/alloc/src/liballoc.natvis`: Visualizers for `Vec`, `VecDeque`,
    `BTreeMap`, `BinaryHeap`, `LinkedList`, `String`, `Box`, `Rc`, and `Arc`.
  - `library/std/src/libstd.natvis`: Visualizers for `HashMap`, `HashSet`,
    `Mutex`, `RwLock`, `PathBuf`, `OsString`, and `SystemTime`.
  - Embedded into crate metadata (`lib.rmeta`) via `#[debugger_visualizer(natvis_file = "...")]`
    and passed to `link.exe`/`lld-link` via `/NATVIS:<temp_path>.natvis` (or into
    PDBs).
- **GDB/LLDB Pretty-Printers (`src/etc/`, `debuginfo/gdb.rs:1-115`)**:
  - `debuginfo/gdb.rs` emits section `.debug_gdb_scripts` containing the 1-byte
    prefix `\x01` (`SECTION_SCRIPT_ID_PYTHON_FILE`) followed by
    `"gdb_load_rust_pretty_printers.py\0"` and creates an unoptimized global
    reference `__rustc_debug_gdb_scripts_section__` so the linker does not
    garbage-collect the section.
  - `src/etc/gdb_lookup.py` and `src/etc/lldb_lookup.py` inspect `DW_TAG_variant_part`
    and slice/string/vec layouts using the exact field names (`data_ptr`,
    `length`, `pointer`, `vtable`, `__0`) documented above.

---

### 3. `tests/debuginfo/` Inventory and Quantitative Optimization Quality Metrics

`Basis: execution + source`

#### 3.1 Inventory of the 192 `tests/debuginfo/*.rs` Acceptance Tests

Scanning all **192** test files in `s1991/tests/debuginfo/`
(`support/v9_debuginfo_inventory_and_metrics.json`) shows:

- **Debugger coverage**:
  - **167 / 192 tests (`87.0%`)** execute GDB commands (`gdb-command:` /
    `gdb-check:`), with minimum GDB version guards (`//@ min-gdb-version:`)
    ranging from `8.1.1` and `8.2` to `10.1`, `13.0`, and `15.1`.
  - **122 / 192 tests (`63.5%`)** execute LLDB commands (`lldb-command:` /
    `lldb-check:`), gated on `//@ min-lldb-version: 310` (`121` tests) or `1600`
    (`1` test).
  - **69 / 192 tests (`35.9%`)** execute Windows CDB (`cdb.exe`) commands
    (`cdb-command:` / `cdb-check:`), validating CodeView + Natvis formatting on
    `*-pc-windows-msvc`.
- **Compile flags**: Almost all tests compile at `-Copt-level=0 -Cdebuginfo=2`
  unless explicitly testing optimized debuginfo (e.g., `limited-debuginfo.rs`,
  ` collapse-debuginfo-*.rs`, `unsized.rs`, `coroutine-objects.rs`).

#### 3.2 `llvm-dwarfdump --statistics` Across Optimization Levels and Cranelift

On `v9_specimen.rs` (`enum Shape`, `&dyn Draw`, and closure `clos`),
`llvm-dwarfdump --statistics` (`support/v9_debuginfo_inventory_and_metrics.json`)
measures:

| Backend & Opt Level (`-Cdebuginfo=2`) | `#functions` | `#functions with location` | `#bytes within functions` | `#params` (`DW_TAG_formal_parameter`) | `#params with binary location` (`DW_AT_location`) | `#variables` (locals) | `#variables with location` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **LLVM `-Copt-level=0`** | 5 | 5 (100%) | 509 | 8 | 8 (100%) | 15 | 14 (93.3%) |
| **LLVM `-Copt-level=1`** | 5 | 5 (100%) | 124 | 8 | 8 (100%) | 11 | 5 (45.5%) |
| **LLVM `-Copt-level=2`** | 5 | 5 (100%) | 124 | 7 | 7 (100%) | 10 | 4 (40.0%) |
| **LLVM `-Copt-level=3`** | 5 | 5 (100%) | 124 | 7 | 7 (100%) | 10 | 4 (40.0%) |
| **Cranelift (`0.134.0`) `-Copt-level=0`** | 5 | 5 (100%) | 689 | **0** | **0 (0%)** | **1** | **0 (0%)** |

**Cranelift debuginfo status (`compiler/rustc_codegen_cranelift/src/debuginfo/`)**:
Cranelift uses `gimli::write` (`debuginfo/emit.rs`, `line_info.rs`, `types.rs`)
to emit DWARF v4 `.debug_info`, `.debug_abbrev`, `.debug_str`, `.debug_line`,
and `.debug_ranges` covering compilation units, functions (`DW_TAG_subprogram`),
and basic line tables (sufficient for `addr2line` and stack backtraces), but
**does not emit `DW_TAG_formal_parameter` or `DW_AT_location` variable value
tracking** (`0` parameters with locations in `llvm-dwarfdump --statistics`).

## Boundaries

- **Live execution of `cdb.exe` and `dsymutil` (`unsupported` on Linux host)**:
  CodeView `.debug$S`/`.debug$T` and Darwin Mach-O `__DWARF` sections were
  generated via cross-compilation (`--target *-pc-windows-msvc` and
  `--target aarch64-apple-darwin`) and decoded with `llvm-readobj --codeview`
  and `llvm-dwarfdump`; running Microsoft `cdb.exe` or Apple `dsymutil` requires
  a Windows or macOS host.

## Evidence

- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_llvm/src/debuginfo/mod.rs:1-757`
  - `compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1-1841`
  - `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/{mod.rs,native.rs,cpp_like.rs}`
  - `compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs:1-115`
  - `compiler/rustc_codegen_cranelift/src/debuginfo/{mod.rs,emit.rs,line_info.rs,types.rs}`
  - `library/core/src/libcore.natvis`, `library/alloc/src/liballoc.natvis`,
    `library/std/src/libstd.natvis`
  - `tests/debuginfo/` (192 test files).
- **Support artifacts**:
  - `support/v9_debuginfo_inventory_and_metrics.json`: Complete census of the
    192 `tests/debuginfo/` files, debugger directive counts, Tier 1 DWARF/CodeView
    section and tag inventories, and `llvm-dwarfdump --statistics` quality
    metrics across `-O0..3` and Cranelift.

## Revalidation

Compile `v9_specimen.rs` across the 8 Tier 1 targets with `-Cdebuginfo=2
--emit=obj` and run `llvm-dwarfdump --statistics` (for DWARF targets) and
`llvm-readobj --codeview` (for MSVC targets) to verify tag presence and
location-coverage ratios against `support/v9_debuginfo_inventory_and_metrics.json`.
