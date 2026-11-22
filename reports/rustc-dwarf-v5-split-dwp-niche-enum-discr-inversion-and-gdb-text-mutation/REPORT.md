# `rustc` DWARF v5 Split Debuginfo (`thorin` `.dwp`), Wrapping-Niche Enum Discriminant Inversion, Coroutine `__state` Encoding, `#![debugger_visualizer]` Deduplication, and `.debug_gdb_scripts` Executable `.text` Mutation

## Summary

Direct source inspection of `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`1.102.0`), live execution on `rustc 1.98.0-nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`), normative checks against `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, cross-auditing against `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, and kernel-checked `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) proofs establish six concrete compiler-codegen and debuginfo invariants and defects:

1. **Live wrapping-niche `DISCR_BEGIN`/`DISCR_END` inversion bug in C++-like (`-windows-msvc`) debuginfo (`enums/mod.rs:420-426`) vs. native DWARF immunity (`native.rs:437`):** Both `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/cpp_like.rs` (L94, L173-179) and `src/etc/natvis/intrinsic.natvis` (L306, L335-337) explicitly specify and implement circular modular discriminant ranges (`begin > end => x >= begin || x <= end`). Yet `compute_discriminant_value` in `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs` (L420-426) unconditionally sorts `valid_range` via `min = valid_range.start.min(valid_range.end)` and `max = valid_range.start.max(valid_range.end)`. Consequently, `DISCR_BEGIN <= DISCR_END` holds universally across every emitted enum, rendering `intrinsic.natvis`'s wrapping branches (both 64-bit `in_range` and 128-bit `in_range128`) unreachable dead code. On `enum SignedWrap { Valid(std::pat::pattern_type!(i8 is -10..=10)), TagA, TagB }` (runtime bytes `Valid(-10) = 246 .. Valid(10) = 10`, `TagA = 11`, `TagB = 12`), `--target x86_64-pc-windows-msvc --emit=llvm-ir -C debuginfo=2` emits `DISCR_BEGIN = 10` and `DISCR_END = 246`. This fails (`UNMATCHED`) on **19 of the 21** valid `SignedWrap::Valid` payloads (`-9..=9`, raw bytes `{0..9} ∪ {247..255}`, including `Valid(-5) = 251` and `Valid(0) = 0`), falsely accepts **all 233** unused niche bytes (`13..=245`) as `Valid`, creates simultaneous `DISCR_EXACT` + `in_range` dual matches on `TagA (11)` and `TagB (12)` (which `cpp_like.rs:122-137`'s variant-order pseudocode misclassifies as `Valid`), and reproduces identically on 128-bit wrapping niches (`DISCR128_BEGIN = 0xa`, `DISCR128_END = 0xfffffffffffffffffffffffffffffff6`). Independently, `intrinsic.natvis` hardcodes `variant0..variant15` (16-variant cap), dropping `variant16+` emitted by `cpp_like.rs:925-949`. By contrast, Linux native DWARF (`native.rs:437`) calls `discr_value.opt_single_val()` (`None` on `DiscrResult::Range`), omitting `DW_AT_discr_value` on the untagged `Valid` `DW_TAG_variant` so DWARF's default-variant rule decodes all 21 valid payloads and both exact tags cleanly.
2. **Executable `.text` machine-code non-invariance across all non-zero `-C debuginfo` levels (`base.rs:563`, `gdb.rs:18-25`, `gdb.rs:113-115`):** On any target with `TargetOptions::emit_debug_gdb_scripts == true` (the global default in `compiler/rustc_target/src/spec/mod.rs:2829`, inherited by `x86_64-unknown-linux-gnu`), compiling an executable with **any** non-zero `-C debuginfo` level (`line-directives-only`, `line-tables-only`, `1`/`limited`, or `2`/`full`) injects `bx.volatile_load(bx.type_i8(), gdb_debug_scripts_section, Align::ONE)` inside the generated C `main` entry shim (`create_entry_fn`), emitting an executable `movzbl __rustc_debug_gdb_scripts_section__(%rip), %eax` (`0f b6 05 ...`) instruction into `.text`. Because `#![feature(omit_gdb_pretty_printer_section)]` was permanently removed in Rust `1.91.0` (PR `#144738`, `removed.rs:231`, `E0557`), no stable or unstable CLI flag or crate attribute preserves `.text` bit-invariance when enabling debuginfo on ELF executables. Crucially, even **`-C strip=debuginfo` and `-C strip=symbols` neither undo the `.text` mutation nor strip `.debug_gdb_scripts`** (`34` bytes retained) because the live `.text` relocation pins `__rustc_debug_gdb_scripts_section__`. All four non-zero `-C debuginfo` levels (and stripped variants thereof) share a single mutated `.text` SHA-256 distinct from `-C debuginfo=0`.
3. **Coroutine debuginfo divergence between native DWARF (`native.rs:199,346`) and MSVC C++-like (`cpp_like.rs:735`):** Linux native DWARF encodes coroutine discriminants as an artificial `DW_TAG_member` named `"__state"` (`DW_AT_artificial: 1`, unlike `""` for ordinary enums) and names each `DW_TAG_variant` member with bare decimal strings (`"0"`, `"1"`, `"2"`, `"3"` for a 1-yield coroutine), whereas MSVC C++-like debuginfo emits a `VariantNames` enum with symbolic `CoroutineArgs::variant_name` enumerators (`Unresumed = 0`, `Returned = 1`, `Panicked = 2`, `Suspend0 = 3`).
4. **In-process `thorin` `.dwp` packaging and path-remapped bit-identical reproducibility (`link.rs:909-1017`):** Under `-C split-debuginfo=packed` with `-Z dwarf-version=4` or `5` and `-Z split-dwarf-kind={split,single}`, `rustc` assembles `<exe>.dwp` in-process via `thorin::DwarfPackage`, deterministically sorting dependency `.rlib` inputs with `into_sorted_stable_ord()` (`link.rs:978`) and passing `MissingReferencedObjectBehaviour::Skip` (`link.rs:996`). DWARF v4 `.dwp` contains 5 debug sections (`version = 2`, `columns = 3` in `.debug_cu_index`); DWARF v5 `.dwp` adds `.debug_rnglists.dwo` (`6` debug sections, `version = 5`, `columns = 4`). Across two distinct build directories of different path lengths, `--remap-path-prefix=<dir>=/remap` produces **bit-identical** `.dwp` (`5,176` B, identical SHA-256) and executable (`4,366,168` B, identical SHA-256) outputs.
5. **`#![debugger_visualizer]` crate-type suppression, diamond deduplication, and a live local-vs-upstream `path_erased()` deduplication asymmetry (`base.rs:640-658`, `gdb.rs:41-63,90-111`):** `.rlib` and `proc-macro` crates never emit `.debug_gdb_scripts` (`needs_gdb_debug_scripts_section` returns `false`), avoiding ODR collisions. Leaf binaries emit `\x01gdb_load_rust_pretty_printers.py\0` followed by `\x04pretty-printer-<crate>-<index>\n<src>\0` entries from a `BTreeSet<DebuggerVisualizerFile>`. Because `rustc_metadata` erases `path` to `None` via `path_erased()` on upstream `.rlib`s (`encoder.rs:2065`), upstream diamond dependencies sharing identical script bytes deduplicate cleanly to `1` entry. However, `collect_debugger_visualizers_transitive` (`base.rs:644`) inserts `tcx.debugger_visualizers(LOCAL_CRATE)` **without** calling `path_erased()`, leaving `path: Some(file)` intact; when a leaf crate and an upstream `.rlib` embed byte-identical GDB scripts, `BTreeSet` treats `(src, Some(p)) != (src, None)` and emits the identical script **twice**.
6. **`#[collapse_debuginfo(yes|no|external)]` and `-C collapse-macro-debuginfo` exact 4×4 precedence (`rustc_expand/src/base.rs:844-862`, `rustc_span/src/hygiene.rs:658-678`):** Macro debuginfo collapsing obeys a 4×4 lookup table where `-C collapse-macro-debuginfo={yes,no}` unconditionally overrides all attributes, while under default/external CLI mode user `macro_rules!` default to `external` (collapse cross-crate to call site; preserve macro-body `DW_AT_decl_line` within the defining crate), built-in macros default to `yes`, and `#[collapse_debuginfo(no)]` preserves upstream macro-body file and line entries inside downstream `.debug_line` tables.

---

## Applicability

### Subjects and Relationships

The five subjects recorded in `REPORT.json` stand in an audit-and-mechanization relationship:

- **Primary source authority (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `src/version = 1.102.0`):** Every upstream file path, symbol signature, and line range cited in **Findings** was directly fetched and inspected at this commit on `2026-11-22`.
- **Executed compiler toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`):** All empirical executions in `support/probe_dwarf_dwp_niche_discr_and_gdb_text.py` (producing `support/probe_results.json`) ran live against this installed toolchain using both native `x86_64-unknown-linux-gnu` and cross-target `--target x86_64-pc-windows-msvc` LLVM IR emission plus `GNU readelf 2.47`, `GNU objdump 2.47`, and `ar`.
- **Cross-revision correspondence between `14210df0e` (executed) and `342d74463` (live upstream HEAD):** Direct diffing of the local `rustc-src` tree at `14210df0e` against the fetched `342d74463` sources confirms that every audited mechanism is **semantically identical** across both revisions, with only minor line-offset and LLVM-wrapper refactoring deltas:
  - `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs`: `compute_discriminant_value` L397-436 (buggy `min`/`max` at L420-426) is byte-for-byte identical across `14210df0e` and `342d74463`.
  - `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/cpp_like.rs` and `native.rs`: Identical logic (`cpp_like.rs` L94, L173-179, L441 vs. L443; `native.rs` L199 vs. L198, L346 vs. L345, L437 vs. L436).
  - `compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs`: Identical control flow and predicate (`L113-115` vs. `L114-116`); `14210df0e` calls `bx.volatile_load(bx.type_i8(), ...)` followed by `LLVMSetAlignment(..., 1)` (`L21-24`), whereas `342d74463` passes `Align::ONE` directly to `bx.volatile_load(bx.type_i8(), gdb_debug_scripts_section, Align::ONE)` (`L23`).
  - `compiler/rustc_codegen_ssa/src/base.rs`: `create_entry_fn` call to `bx.insert_reference_to_gdb_debug_scripts_section_global()` shifted from L542 (`14210df0e`) to L563 (`342d74463`); `collect_debugger_visualizers_transitive` shifted from L617-635 (`14210df0e`) to L640-658 (`342d74463`), still omitting `.path_erased()` on `LOCAL_CRATE` in both revisions.
  - `compiler/rustc_codegen_ssa/src/back/link.rs`: `link_dwarf_object` (`thorin::DwarfPackage`) shifted from L607-715 (`14210df0e`) to L909-1017 (`342d74463`) with identical `SplitDwarfKind`, `into_sorted_stable_ord()`, `MissingReferencedObjectBehaviour::Skip`, and `StreamingBuffer` emission logic.
  - `compiler/rustc_feature/src/removed.rs`: `(removed, omit_gdb_pretty_printer_section, "1.91.0", None, None, 144738)` at L220 (`14210df0e`) and L231 (`342d74463`).
  - `compiler/rustc_expand/src/base.rs`: `get_collapse_debuginfo` 4×4 `collapse_table` shifted from L892-910 (`14210df0e`) to L844-862 (`342d74463`), logic identical.
- **Normative specification (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Provides the normative attribute rules `r[attributes.debugger.debugger_visualizer]` and `r[attributes.debugger.collapse_debuginfo]` in `src/attributes/debugger.md`.
- **Verification boundary context (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Contextualizes how these `rustc` behaviors interact with `vendor/lean-miri/Miri/ABI/WrappingRange.lean` (circular wrapping-range semantics), `trusted/correspondence/Trusted/Correspondence.lean` (enum layout encoding), `trusted/rustc-capture/src/driver.rs` (`after_analysis` capture hook on pinned `1.98.0-nightly`), and `trusted/audit/TrustedBoundary.lean` (kernel replay rules omitting `*._unsafe_rec` helpers).
- **Formal mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `Lean v4.34.1`):** All algebraic and combinatorial claims are mechanized and kernel-checked in `support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean` (`36` user theorems, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`).

### Target, Backend, and Feature-Flag Scope

- **Backend scope:** Findings 1, 2, 3, and 5 apply specifically to the LLVM codegen backend (`rustc_codegen_llvm` + `rustc_codegen_ssa`). Cranelift (`rustc_codegen_cranelift`) and GCC (`rustc_codegen_gcc`) are outside execution scope (see **Boundaries**).
- **Target scope:**
  - The wrapping-niche `DISCR_BEGIN`/`DISCR_END` inversion affects every target selecting C++-like enum debuginfo (`type_names::cpp_like_debuginfo(tcx) == true`, i.e., `-windows-msvc` / CodeView targets), across all tag widths (8-bit through 128-bit) whenever `valid_range.start > valid_range.end`.
  - The `.debug_gdb_scripts` `.text` mutation affects every target with `TargetOptions::emit_debug_gdb_scripts == true` (ELF Linux/BSD targets by default; explicitly disabled on `msvc`, `windows_gnu`, `windows_gnullvm`, `cygwin`, `wasm`, `linux_wasm`, `arm_none`, `xtensa`, and bare-metal `riscv*`/`mips*` targets) when building `CrateType::Executable` at any `-C debuginfo != 0`.
  - `thorin` `.dwp` assembly applies on ELF targets supporting `-C split-debuginfo=packed` (e.g., `x86_64-unknown-linux-gnu`); macOS uses `dsymutil` (`.dSYM`) and MSVC uses `.pdb` via `link.exe`/`lld-link`.
- **Unstable feature gates used in minimal reproducers:** Reproducing a wrapping `WrappingRange` on a minimal 1-byte enum uses nightly `#![feature(pattern_types, pattern_type_macro)]` (`std::pat::pattern_type!(i8 is -10..=10)`), though any layout producing a wrapping `valid_range` (`start > end`) triggers the exact same `compute_discriminant_value` code path. Coroutine reproducers use `#![feature(coroutines, coroutine_trait)]`; `async fn` lowers through the same `ty::Coroutine` debuginfo path. `-Z dwarf-version` and `-Z split-dwarf-kind` require nightly `rustc`; `-C debuginfo`, `-C split-debuginfo`, `-C strip`, `-C collapse-macro-debuginfo`, `--remap-path-prefix`, `#![debugger_visualizer]`, and `#[collapse_debuginfo]` are stable flags/attributes.

---

## Findings

### 1. Live Wrapping-Niche `DISCR_BEGIN`/`DISCR_END` Inversion Bug (`enums/mod.rs` vs. `cpp_like.rs`, `intrinsic.natvis`, and `native.rs`)

Basis: source + execution + derived (Lean v4.34.1 kernel proof)

#### 1.1 Producer–Consumer Contract Mismatch in Upstream Source

In `rustc`'s ABI layout engine (`rustc_abi::WrappingRange`, mirrored in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` at `vendor/lean-miri/Miri/ABI/WrappingRange.lean:39-43`), a scalar's valid bit patterns form an inclusive circular interval `[start, end]` modulo `2^(8 * size)`:

- When `start <= end`: valid values satisfy `start <= x && x <= end` (non-wrapping).
- When `start > end`: valid values wrap around zero and satisfy `start <= x || x <= end` (wrapping).

For example, a signed subrange `i8 is -10..=10` stored as an unsigned 8-bit niche tag (`tag_base_type` normalizes all niche tags to unsigned integers in `compiler/rustc_codegen_ssa/src/debuginfo/mod.rs:71-88`) has two's-complement bit patterns `246..=255` (`-10..=-1`) followed by `0..=10` (`0..=10`), giving `valid_range = WrappingRange { start: 246, end: 10 }`. The complement gap `{11..=245}` provides `235` niche bit patterns available for other enum variants (`TagA = 11`, `TagB = 12`).

Both the C++-like debuginfo specification (`compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/cpp_like.rs` at `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) and Microsoft Visual Studio / WinDbg NatVis rules (`src/etc/natvis/intrinsic.natvis` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) explicitly adopt this circular-interval contract:

- **`cpp_like.rs` L94:**
  > `/// Note that these ranges can wrap around, so that DISCR_END < DISCR_BEGIN.`
- **`cpp_like.rs` L173-179** (decoder pseudocode):
  ```rust
  fn is_in_range(value, start, end) -> bool {
      if start < end {
          value >= start && value <= end
      } else {
          value >= start || value <= end
      }
  }
  ```
  *(Secondary documentation defect: `cpp_like.rs:174` writes strict `start < end` rather than `start <= end`; if `start == end` for a singleton range, the `else` branch `value >= start || value <= end` is tautologically `true` for all values. `intrinsic.natvis:306` avoids this by using `begin <= end`.)*
- **`intrinsic.natvis` L304-310** (64-bit `in_range` intrinsic) and **L333-344** (128-bit `in_range128` intrinsic):
  ```xml
  <!-- NOTE: That tag ranges can wrap around, in which case `end` is less than `begin` and we
             have to do a different check -->
  <Intrinsic Name="in_range" Expression="(begin &lt;= end) ? ((x &gt;= begin) &amp;&amp; (x &lt;= end)) : ((x &gt;= begin) || (x &lt;= end))">
  ```
  ```xml
  <Intrinsic Name="in_range128" Expression="(lt_or_eq128(begin_hi, begin_lo, end_hi, end_lo)) ?
                                            (lt_or_eq128(begin_hi, begin_lo, x_hi, x_lo) &amp;&amp; lt_or_eq128(x_hi, x_lo, end_hi, end_lo)) :
                                            (lt_or_eq128(begin_hi, begin_lo, x_hi, x_lo) || lt_or_eq128(x_hi, x_lo, end_hi, end_lo))">
  ```

However, the **producer** called by `cpp_like.rs:441` (`compute_discriminant_value` in `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs:397-436`) violates that contract on lines **420–426**:

```rust
if variant_index == untagged_variant {
    let valid_range = enum_type_and_layout
        .for_variant(cx, variant_index)
        .largest_niche
        .as_ref()
        .unwrap()
        .valid_range;

    let min = valid_range.start.min(valid_range.end);
    let min = tag.size(cx).truncate(min);

    let max = valid_range.start.max(valid_range.end);
    let max = tag.size(cx).truncate(max);

    DiscrResult::Range(min, max)
}
```

`build_variant_struct_wrapper_type_di_node` (`cpp_like.rs:541-550,639-687`) then emits `min` directly as `DISCR_BEGIN` (or `DISCR128_BEGIN_{HI,LO}`) and `max` as `DISCR_END` (or `DISCR128_END_{HI,LO}`). Because `tag.size(cx).truncate` is order-preserving on valid endpoints `< 2^(8 * size)`, `DISCR_BEGIN <= DISCR_END` holds unconditionally for **every** enum `rustc` emits:

1. The wrapping else-branches of both `in_range` (`intrinsic.natvis:306`) and `in_range128` (`intrinsic.natvis:335-337`) are **mathematically dead code** across all compiled Rust programs (`natvis_wrapping_branch_dead_code`).
2. Whenever `valid_range.end < valid_range.start`, sorting `(start, end)` into `(end, start)` computes the **exact Boolean negation** of the intended circular membership predicate on every tag value `x < modulus` other than the two boundary endpoints `start` and `end` (`wrapping_bug_is_exact_negation_off_endpoints`).

#### 1.2 Empirical Reproduction (`SignedWrap`, `SignedWrap128`, and `Enum17`)

Running `support/probe_dwarf_dwp_niche_discr_and_gdb_text.py` against `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)` confirms all aspects of the defect live:

- **Runtime `SignedWrap` bytes (all 23 inhabited values verified via `transmute::<SignedWrap, u8>`):**
  - `Valid(-10)..=Valid(-1)` -> raw bytes `246, 247, 248, 249, 250, 251, 252, 253, 254, 255` (specifically `Valid(-10) = 246`, `Valid(-5) = 251`, `Valid(-1) = 255`)
  - `Valid(0)..=Valid(10)` -> raw bytes `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10`
  - `TagA` -> `11`, `TagB` -> `12`
  - Unused invalid niche bytes -> `13..=245` (`233` bit patterns)
- **Emitted `--target x86_64-pc-windows-msvc --emit=llvm-ir -C debuginfo=2` metadata (`probe_results.json`):**
  ```llvm
  !194 = !DICompositeType(tag: DW_TAG_union_type, name: "enum2$<wrap_msvc::SignedWrap>", size: 8, align: 8, ...)
  !207 = !DIDerivedType(tag: DW_TAG_member, name: "DISCR_BEGIN", scope: !197, ..., extraData: i64 10)
  !208 = !DIDerivedType(tag: DW_TAG_member, name: "DISCR_END", scope: !197, ..., extraData: i64 246)
  !215 = !DIDerivedType(tag: DW_TAG_member, name: "DISCR_EXACT", scope: !210, ..., extraData: i64 11)
  !222 = !DIDerivedType(tag: DW_TAG_member, name: "DISCR_EXACT", scope: !217, ..., extraData: i64 12)
  ```
- **Exhaustive 256-byte classification matrix on `SignedWrap` (`DISCR_BEGIN = 10`, `DISCR_END = 246`, `DISCR_EXACT ∈ {11, 12}`):**

| Raw `u8` Class | Count | True Variant | `intrinsic.natvis` `<DisplayString>` (Exact-First) | `intrinsic.natvis` `<Expand>` Simultaneous Match? | `cpp_like.rs:122-137` Field-Order Scan (`variant0` First) | Corrected `(246, 10)` Unsorted | Linux Native DWARF (`native.rs:437`) |
| :--- | ---: | :--- | :--- | :--- | :--- | :--- | :--- |
| `{10, 246}` (`Valid(10)`, `Valid(-10)`) | 2 | `Valid` | `Valid` (accidental endpoint survival) | No (`in_range` only) | `Valid` | `Valid` | `Valid` (default variant) |
| `{0..9} ∪ {247..255}` (`Valid(-9)..Valid(9)`) | **19** | `Valid` | **`UNMATCHED_NATVIS_FAILURE`** | No (neither matches) | **`UNMATCHED`** | `Valid` | `Valid` (default variant) |
| `{11, 12}` (`TagA`, `TagB`) | 2 | `TagA`/`TagB` | `Exact(11)` / `Exact(12)` (rescued only by rule order) | **YES — BOTH `DISCR_EXACT` AND `in_range` true** | **Misclassified as `Valid`** | `Exact(11)` / `Exact(12)` (no dual match) | `TagA` (`0xb`) / `TagB` (`0xc`) |
| `{13..245}` (unused niche, UB) | **233** | Invalid (UB) | **False positive: `Valid`** | No (`in_range` only) | **False positive: `Valid`** | `UNMATCHED` (0 false positives) | Default fallback (`Valid`) |

- **128-bit wrapping niche confirmation (`SignedWrap128` with `std::pat::pattern_type!(i128 is -10..=10)`):**
  `--target x86_64-pc-windows-msvc --emit=llvm-ir -C debuginfo=2` emits:
  - `DISCR128_BEGIN = 0x0000000000000000_000000000000000a` (`10`)
  - `DISCR128_END = 0xffffffffffffffff_fffffffffffffff6` (`2^128 - 10`)
  - `DISCR128_EXACT ∈ {11, 12}`
  Thus the exact same inversion (`DISCR128_BEGIN <= DISCR128_END`) breaks `in_range128` across 128-bit wrapping niches as well (`signedWrap128_buggy_inversion`).
- **Secondary MSVC NatVis 16-variant hard cap (`intrinsic.natvis:346-482` vs. `cpp_like.rs:925-949`):**
  `variant_union_field_name` (`cpp_like.rs:925-949`) pre-allocates `variant0..variant15` and dynamically formats `variant16`, `variant17`, ... for larger enums. On `Enum17` (17 variants), `rustc` emits all `17` union members (`variant0` through `variant16`, verified live: `msvc_enum17_variant_field_count = 17`, `msvc_enum17_has_variant16 = true`). Yet `src/etc/natvis/intrinsic.natvis` hardcodes `<DisplayString>` and `<ExpandedItem>` clauses strictly for `variant0..variant15` (L346-361, L363-378, L380-395, L397-412, L415-481), causing any variant with index `>= 16` to fall through unmatched (`natvis_16_variant_cap_drops_variant16`).

#### 1.3 Why Linux Native DWARF Is Immune (and Its Exact Trade-off)

On ELF/DWARF targets (`compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/native.rs:430-440`), `build_enum_variant_member_di_node` calls `compute_discriminant_value`, receives `DiscrResult::Range(10, 246)` for the untagged `Valid` variant, and immediately discards both bounds via `opt_single_val()` (`enums/mod.rs:387-389`), which returns `None` for `DiscrResult::Range`. Consequently, LLVM emits:

```text
<3><4a0>: Abbrev Number: 35 (DW_TAG_variant_part)
   <4a1>   DW_AT_discr       : <0x4a5>
<4><4a5>: Abbrev Number: 36 (DW_TAG_member)     [type: u8, loc: 0, DW_AT_artificial: 1]
<4><4ac>: Abbrev Number: 37 (DW_TAG_variant)    [NO DW_AT_discr_value -> default variant]
<5><4ad>:   DW_TAG_member (DW_AT_name: Valid)
<4><4b9>: Abbrev Number: 38 (DW_TAG_variant)    [DW_AT_discr_value: 11]
<5><4bb>:   DW_TAG_member (DW_AT_name: TagA)
<4><4c7>: Abbrev Number: 38 (DW_TAG_variant)    [DW_AT_discr_value: 12]
<5><4c9>:   DW_TAG_member (DW_AT_name: TagB)
```

Under DWARF v5 §5.7.10, a `DW_TAG_variant` omitting both `DW_AT_discr_value` and `DW_AT_discr_list` is the default variant selected whenever the discriminant value matches no sibling's explicit `DW_AT_discr_value`. This makes native DWARF completely insensitive to wrapping-range endpoint ordering on all inhabited values (`native_dwarf_sound_on_inhabited`), at the cost that uninhabited (UB) unused niche bytes (`13..=245`) also fall back to `Valid` (`native_dwarf_maps_unused_niche_to_default`) rather than being flagged invalid.

#### 1.4 Minimal Upstream Fix and Connection to Anneal

Replacing lines `420-426` of `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs` with:

```rust
let start = tag.size(cx).truncate(valid_range.start);
let end = tag.size(cx).truncate(valid_range.end);
DiscrResult::Range(start, end)
```

preserves `(start, end)` unsorted, restores exact bijective decoding across both `intrinsic.natvis` and `cpp_like.rs`, eliminates all `233` false positives and both `<Expand>` dual matches, and leaves native DWARF unchanged (`unsorted_circular_range_sound_and_exact`, `signedWrap_fixed_exact_counts`).

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `vendor/lean-miri/Miri/ABI/WrappingRange.lean:39-43` already implements circular modular membership (`if range.start.toNat ≤ range.end.toNat then ... else ...`), matching the intended `WrappingRange` contract and `intrinsic.natvis:306`, while `trusted/correspondence/Trusted/Correspondence.lean:823-848` avoids computing wrapping-range hulls for fieldless enums by using `Miri.ABI.Scalar.Union` (`WrappingRange.full`). Any future verified debuginfo or CodeView emitter in Anneal must preserve `WrappingRange.{start, end}` order directly rather than mirroring `rustc_codegen_llvm`'s `.min`/`.max` clamp. (Related formalized niche invariants appear in corpus packages `enum-niche-layout-guarantees-and-validity-invariants` and `wrapping-niche-intervals-affine-tags-nested-option-capacity-and-discriminant-write-order`.)

---

### 2. `.debug_gdb_scripts` Executable `.text` Machine-Code Non-Invariance Across Non-Zero `-C debuginfo` Levels

Basis: source + execution + derived (Lean v4.34.1 kernel proof)

#### 2.1 Codegen Mechanism in `base.rs`, `gdb.rs`, `debuginfo/mod.rs`, and `removed.rs`

On ELF targets where `TargetOptions::emit_debug_gdb_scripts` is `true` (the global default in `compiler/rustc_target/src/spec/mod.rs:2829` at `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), `rustc` embeds GDB pretty-printer autoload metadata in the ELF `.debug_gdb_scripts` section via a `LinkOnceODRLinkage` constant global named `__rustc_debug_gdb_scripts_section__` (`compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs:32-82`).

Two distinct sites interact with this global:

1. **Per-CGU global emission (`compiler/rustc_codegen_llvm/src/debuginfo/mod.rs:727-741`):**
   `debuginfo_finalize` calls `gdb::get_or_insert_gdb_debug_scripts_section_global(self)` whenever `gdb::needs_gdb_debug_scripts_section(self)` holds, where (`gdb.rs:84-116`):
   ```rust
   let embed_visualizers = cx.tcx.crate_types().iter().any(|&crate_type| match crate_type {
       CrateType::Executable | CrateType::Dylib | CrateType::Cdylib
       | CrateType::StaticLib | CrateType::Sdylib => true,
       CrateType::ProcMacro | CrateType::Rlib => false,
   });
   cx.sess().opts.debuginfo != DebugInfo::None
       && cx.sess().target.emit_debug_gdb_scripts
       && embed_visualizers
   ```
2. **Executable C `main` entry-shim volatile load (`compiler/rustc_codegen_ssa/src/base.rs:563`, `gdb.rs:18-25`):**
   Inside `create_entry_fn` (which builds the native C `main(argc, argv)` trampoline for `CrateType::Executable`), `rustc` unconditionally invokes:
   ```rust
   bx.insert_reference_to_gdb_debug_scripts_section_global();
   ```
   which lowers (`gdb.rs:18-25`) to:
   ```rust
   pub(crate) fn insert_reference_to_gdb_debug_scripts_section_global(bx: &mut Builder<'_, '_, '_>) {
       if needs_gdb_debug_scripts_section(bx) {
           let gdb_debug_scripts_section = get_or_insert_gdb_debug_scripts_section_global(bx);
           bx.volatile_load(bx.type_i8(), gdb_debug_scripts_section, Align::ONE);
       }
   }
   ```
   Because the load is `volatile`, LLVM's optimizer cannot DCE it even at `-O` / `-C opt-level=3`, forcing an actual memory-load instruction into executable `.text` solely to prevent the linker (`--gc-sections`) from discarding `.debug_gdb_scripts`.

3. **Permanent removal of the opt-out attribute (`compiler/rustc_feature/src/removed.rs:231`):**
   ```rust
   /// Allows using `#[omit_gdb_pretty_printer_section]`.
   (removed, omit_gdb_pretty_printer_section, "1.91.0", None, None, 144738),
   ```
   Since Rust `1.91.0` (PR `#144738`), attempting `#![feature(omit_gdb_pretty_printer_section)]` fails with hard error `E0557`. No replacement `-C` flag, `-Z` flag, or crate attribute exists to disable `.debug_gdb_scripts` injection while keeping `debuginfo != DebugInfo::None` on targets with `emit_debug_gdb_scripts = true` (short of supplying a custom target JSON overriding `"emit-debug-gdb-scripts": false`).

#### 2.2 Empirical Verification Across All `-C debuginfo` Levels, `-C strip=*`, Targets, and Crate Types

Probe 2 (`support/probe_results.json`, compiled with `rustc 1.98.0-nightly`, `-O`, `--edition=2024`, `x86_64-unknown-linux-gnu`) measured exact `.text` SHA-256 digests, LLVM IR volatile loads, `main` disassembly, and `.debug_gdb_scripts` retention across 7 flag combinations:

| Configuration | `.text` Len (B) | `.text` SHA-256 (first 16 hex) | Identical to `debuginfo=0`? | LLVM IR `load volatile i8` | `main` Has `movzbl`? | `.debug_gdb_scripts` Present (Len) |
| :--- | ---: | :--- | :--- | :--- | :--- | :--- |
| `-C debuginfo=0` | 247,987 | `59ea39d77febc61a` | **Yes (baseline)** | `false` | `false` | `false` (`0` B) |
| `-C debuginfo=line-directives-only` | 247,987 | `34642176a6e8f479` | **NO (mutated)** | `true` | `true` | `true` (`34` B) |
| `-C debuginfo=line-tables-only` | 247,987 | `34642176a6e8f479` | **NO (mutated)** | *(not dumped)* | `true` | `true` (`34` B) |
| `-C debuginfo=1` (`limited`) | 247,987 | `34642176a6e8f479` | **NO (mutated)** | *(not dumped)* | `true` | `true` (`34` B) |
| `-C debuginfo=2` (`full`) | 247,987 | `34642176a6e8f479` | **NO (mutated)** | `true` | `true` | `true` (`34` B) |
| `-C debuginfo=2 -C strip=debuginfo` | 247,987 | `34642176a6e8f479` | **NO (mutated)** | *(not dumped)* | `true` | **`true` (`34` B — NOT stripped!)** |
| `-C debuginfo=2 -C strip=symbols` | 247,987 | `34642176a6e8f479` | **NO (mutated)** | *(not dumped)* | *(symtab stripped; `.text` SHA-256 identical)* | **`true` (`34` B — NOT stripped!)** |

Exact disassembled C `main` shim delta (from `probe_results.json`):

```asm
; -C debuginfo=0 (39 bytes: 0x13820..0x13846)
13820: 50                      push   %rax
13821: 48 89 f1                mov    %rsi,%rcx
13824: 48 63 d7                movslq %edi,%rdx
13827: 48 8d 05 c2 ff ff ff    lea    -0x3e(%rip),%rax  # <gdb_text::main>
...

; -C debuginfo=line-directives-only / line-tables-only / 1 / 2 / 2+strip=debuginfo (46 bytes: 0x13840..0x1386d)
13840: 50                      push   %rax
13841: 48 89 f1                mov    %rsi,%rcx
13844: 0f b6 05 3d 10 ff ff    movzbl -0xefc3(%rip),%eax # 4888 <__rustc_debug_gdb_scripts_section__>
1384b: 48 63 d7                movslq %edi,%rdx
1384e: 48 8d 05 bb ff ff ff    lea    -0x45(%rip),%rax  # <gdb_text::main>
...
```

Four non-obvious operational consequences emerge from these measurements:

1. **`.text` section length alone can hide the mutation:** In this binary, `main` grew from `39` to `46` bytes (+7 bytes for `0f b6 05 ...`), which fit inside existing 16-byte function alignment padding (`48` B), leaving total `.text` size unchanged at `247,987` bytes while changing the `.text` SHA-256 completely (note: depending on alignment and GOT indirection under different LLVM/linker versions, total `.text` size may grow by `0` or `16` bytes; SHA-256 hashing of `.text` is the sound discriminator).
2. **`-C strip=debuginfo` and `-C strip=symbols` fail to strip `.debug_gdb_scripts` and fail to restore `.text`:** Because the volatile `movzbl` instruction creates an active relocation from `.text` to `__rustc_debug_gdb_scripts_section__` in `.debug_gdb_scripts`, the linker cannot discard `.debug_gdb_scripts` during `--strip-debug` or `--strip-all`, and `.text` remains bit-identical to unstripped `-C debuginfo=2` (`text_mutated_for_every_nonzero_debuginfo`, `text_identical_across_all_nonzero_levels`).
3. **Crate-type asymmetry (`rlib` vs. `cdylib` vs. `staticlib` vs. `bin`):**
   - `rlib`: `needs_gdb_debug_scripts_section` returns `false` -> `0` `.o` members contain `.debug_gdb_scripts`.
   - `staticlib`: `debuginfo_finalize` (`debuginfo/mod.rs:731-737`) emits the `LinkOnceODRLinkage` global into `.o` archive members (`any_member_has_debug_gdb_scripts = true`), with no C `main` shim volatile load.
   - `cdylib`: `debuginfo_finalize` emits the global into the intermediate `.o`, **but** because a `cdylib` has no `create_entry_fn` C `main` shim, no `.text` volatile load references it, so the linker drops the unreferenced `linkonce_odr` `.debug_gdb_scripts` section (`has_debug_gdb_scripts = false` on the linked `.so`).
   - `bin` (`Executable`): `create_entry_fn` emits the volatile load, mutating `.text` and pinning `.debug_gdb_scripts` permanently.
4. **Target-spec verification and `E0557`:** `rustc -Z unstable-options --print target-spec-json` confirms `x86_64-unknown-linux-gnu` inherits the default `emit-debug-gdb-scripts: true` (key omitted from JSON diff), while `x86_64-pc-windows-msvc` and `riscv64gc-unknown-none-elf` explicitly set `"emit-debug-gdb-scripts": false`. Compiling `#![feature(omit_gdb_pretty_printer_section)]` exits with code `1` and `error[E0557]: feature has been removed ... removed in 1.91.0; see <https://github.com/rust-lang/rust/pull/144738>`.

#### 2.3 Implication for Anneal and Verified-`rustc` Trust Boundaries

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs:75-84` hooks `Callbacks::after_analysis` (pre-codegen), so `-C debuginfo` does not perturb MIR-level analysis semantics. However, any post-codegen binary-attestation or verified-backend equivalence pipeline comparing a verified `-C debuginfo=0` executable's `.text` against a debug-enabled (`-C debuginfo=1|2|line-directives-only|line-tables-only`) Linux ELF executable **will fail byte-for-byte `.text` equality on the C `main` shim** unless it either (a) compares strictly within the non-zero equivalence class (`line-directives-only == line-tables-only == 1 == 2 == 2+strip=*`), (b) normalizes/models the `create_entry_fn` volatile load, or (c) targets a spec with `emit_debug_gdb_scripts = false`.

---

### 3. Coroutine `__state` DWARF Encoding vs. MSVC `VariantNames`

Basis: source + execution

Comparing `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/native.rs` against `cpp_like.rs` at `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` exposes a sharp representational divergence for `ty::Coroutine` (covering both `#[coroutine]` and `async fn` state machines):

- **Linux native DWARF (`native.rs:175-242,344-348`):**
  1. `build_discr_member_di_node` (`native.rs:345-347`) assigns the artificial discriminant `DW_TAG_member` the name `"__state"` (`DW_AT_artificial: 1`) exclusively for `ty::Coroutine(..)`, whereas ordinary Rust enums receive `""` (anonymous artificial discriminant).
  2. `build_coroutine_di_node` (`native.rs:196-199`) names every coroutine `DW_TAG_variant`'s child `DW_TAG_member` with a bare decimal index string—despite an explicit upstream `FIXME` noting that bare numbers are invalid identifiers:
     ```rust
     // FIXME: This is problematic because just a number is not a valid identifier.
     //        CoroutineArgs::variant_name(variant_index), would be consistent with enums?
     let variant_name = format!("{}", variant_index.as_usize()).into();
     ```
- **MSVC C++-like debuginfo (`cpp_like.rs:706-795`):**
  `build_union_fields_for_direct_tag_coroutine` (`cpp_like.rs:730-735`) calls `CoroutineArgs::variant_name(variant_index)`, emitting human-readable symbolic enumerators inside `VariantNames` (`Unresumed = 0`, `Returned = 1`, `Panicked = 2`, `Suspend0 = 3`, ...).

Empirical Probe 5A on a 1-yield `#[coroutine]` confirms both outputs verbatim (`probe_results.json`):
- Linux DWARF (`readelf --debug-dump=info`): `DW_AT_name: __state`, `DW_AT_artificial: 1`, `DW_TAG_variant` member names `["0", "1", "2", "3"]`.
- MSVC LLVM IR (`--target x86_64-pc-windows-msvc --emit=llvm-ir -C debuginfo=2`): `VariantNames` `!DIEnumerator` list `[{"name": "Unresumed", "value": 0}, {"name": "Returned", "value": 1}, {"name": "Panicked", "value": 2}, {"name": "Suspend0", "value": 3}]`.

---

### 4. DWARF v4/v5 Split Debuginfo, In-Process `thorin` `.dwp` Packaging, and Path-Remapped Determinism

Basis: source + execution + derived (Lean v4.34.1 kernel proof)

#### 4.1 In-Process `thorin::DwarfPackage` Architecture (`link.rs:909-1017`)

When linking an executable with `-C split-debuginfo=packed` on ELF targets, `rustc` does not shell out to external GNU `dwp` or `llvm-dwp`. Instead, `link_dwarf_object` (`compiler/rustc_codegen_ssa/src/back/link.rs:909-1017` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) runs `thorin::DwarfPackage` in-process:

1. **Current-crate units (`link.rs:953-971`):** Under `-Z split-dwarf-kind=single`, feeds each CGU's `m.object` (and `m.global_asm_object`) directly to `package.add_input_object`; under `-Z split-dwarf-kind=split` (the default for split DWARF), feeds each CGU's separate `m.dwarf_object` (`.dwo`).
2. **Deterministic dependency ordering (`link.rs:974-983`):** Collects all dependency `.rlib`s from `crate_info.used_crate_source` and sorts them deterministically via `.into_sorted_stable_ord()` before calling `package.add_input_object(input_rlib)`.
3. **Remapped-path tolerance (`link.rs:985-997`):** Calls `package.add_executable(executable_out_filename, thorin::MissingReferencedObjectBehaviour::Skip)` because skeleton `DW_AT_dwo_name` / `DW_AT_comp_dir` paths inside the executable may point to Cargo-cleaned or `--remap-path-prefix`-rewritten locations; all required `.dwo` units were already supplied explicitly in steps 1–2.
4. **Streaming emission (`link.rs:999-1010`):** Writes `<exe>.dwp` via `thorin::object::write::StreamingBuffer` and `package.finish()?.emit(&mut output_stream)?`.

#### 4.2 Empirical 10-Cell Matrix (DWARF v4 vs. v5 × `split-debuginfo` × `split-dwarf-kind`)

Probe 4 (`support/probe_results.json`, 2-crate build `dep_krate` rlib + `app` bin, `-C debuginfo=2 -C codegen-units=1`, `rustc 1.98.0-nightly`):

| Configuration | Exe Size (B) | `.dwo` in `.rlib` | Loose `.dwo` Files | `.dwp` Size (B) | `.dwp` Debug Sections | `.debug_cu_index` Header (`ver`, `cols`, `units`, `slots`) |
| :--- | ---: | ---: | ---: | ---: | :--- | :--- |
| `dwarf4_off_single` | 4,365,928 | 0 | 0 | — (`0`) | `[]` | — |
| `dwarf4_unpacked_split` | 4,362,600 | 1 | 2 | — (`0`) | `[]` | — |
| `dwarf4_unpacked_single` | 4,362,600 | 0 | 0 | — (`0`) | `[]` | — |
| `dwarf4_packed_split` | 4,362,592 | 1 | 0 | 5,272 | 5: `.debug_str_offsets.dwo`, `.debug_abbrev.dwo`, `.debug_info.dwo`, `.debug_str.dwo`, `.debug_cu_index` | `v2`, `cols=3`, `units=2`, `slots=4` |
| `dwarf4_packed_single` | 4,362,592 | 0 | 0 | 5,272 | Same 5 sections | `v2`, `cols=3`, `units=2`, `slots=4` |
| `dwarf5_off_single` | 4,368,352 | 0 | 0 | — (`0`) | `[]` | — |
| `dwarf5_unpacked_split` | 4,366,456 | 1 | 2 | — (`0`) | `[]` | — |
| `dwarf5_unpacked_single` | 4,366,456 | 0 | 0 | — (`0`) | `[]` | — |
| `dwarf5_packed_split` | 4,366,448 | 1 | 0 | 5,360 | 6: adds **`.debug_rnglists.dwo`** | `v5`, `cols=4`, `units=2`, `slots=4` |
| `dwarf5_packed_single` | 4,366,448 | 0 | 0 | 5,360 | Same 6 sections | `v5`, `cols=4`, `units=2`, `slots=4` |

Key structural contrasts observed:
- **DWARF v4 vs. DWARF v5 `.dwp` format:** Moving from `-Z dwarf-version=4` to `-Z dwarf-version=5` upgrades `.debug_cu_index` from GNU split-DWARF v2 (`version = 2`, `columns = 3`) to standard DWARF v5 (`version = 5`, `columns = 4`) and adds `.debug_rnglists.dwo` (+88 bytes on this 2-unit binary).
- **`split` vs. `single` `.dwo` packaging:** Under `-Z split-dwarf-kind=split`, `.rlib` archives embed `1` `.dwo` member per CGU and `unpacked` leaves loose `.dwo` files in the output directory (`packed` cleans them after assembling `.dwp`). Under `-Z split-dwarf-kind=single`, split DWARF sections reside inside `.o` files directly (`0` `.dwo` members in `.rlib`, `0` loose `.dwo` files) yet `thorin` still packages an identical-size `.dwp` (`5,272` B for v4; `5,360` B for v5).

#### 4.3 Dual-Directory Bit-Identical Reproducibility Under `--remap-path-prefix`

Compiling the 2-crate DWARF v5 `-C split-debuginfo=packed -Z split-dwarf-kind=split` build inside two distinct directories of different path lengths (`repro_alpha` vs. `repro_beta_distinct_longer_dir`) with `--remap-path-prefix=<dir>=/remap` yields:

- **`.dwp` bit-identical (`true`):** Both directories produce `5,176` bytes with identical SHA-256 `20c597ba8966c268574534f4c73bf6b68f844ac883ac5a2c63c29702d9ba896b`.
- **Executable bit-identical (`true`):** Both directories produce `4,366,168` bytes with identical SHA-256 `b0f00977012c2dd308c65febc311c58a2aed3920534714c82e5c93917e76f568`.
- Adding `-Z remap-cwd-prefix=/remap` produces the exact same SHA-256 digests (`20c597ba...` and `b0f00977...`), confirming that `--remap-path-prefix` alone is sufficient when compilation runs with `cwd` inside the remapped prefix (`thorin_dwp_bit_identical_under_remap`).

---

### 5. `#![debugger_visualizer]` Binary Framing, Diamond Deduplication, and Local-vs-Upstream `path_erased()` Asymmetry

Basis: normative + source + execution + derived (Lean v4.34.1 kernel proof)

#### 5.1 Normative Contract and `.debug_gdb_scripts` Wire Format

Per `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/attributes/debugger.md` L8-167, `r[attributes.debugger.debugger_visualizer]`):
- Allowed strictly on the crate root or a module (`r[attributes.debugger.debugger_visualizer.allowed-positions]`).
- Accepts `natvis_file = "..."` (`-windows-msvc` only) or `gdb_script_file = "..."` (path relative to the declaring source file).
- May appear multiple times (`r[attributes.debugger.debugger_visualizer.duplicates]`).

In `compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs:38-63` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), `rustc` serializes `.debug_gdb_scripts` as a sequence of NUL-terminated GDB script records:
1. **Standard library external script entry (`\x01` framing, `gdb.rs:41`):**
   `0x01 || "gdb_load_rust_pretty_printers.py" || 0x00` (`34` bytes). Byte `0x01` instructs GDB to load an external Python script file by name.
2. **Transitive user `#![debugger_visualizer(gdb_script_file = ...)]` entries (`\x04` framing, `gdb.rs:45-62`):**
   For each `(index, visualizer)` in `collect_debugger_visualizers_transitive(cx.tcx, GdbPrettyPrinter)`:
   `0x04 || "pretty-printer-<local_crate_name>-<index>\n" || <raw script bytes> || 0x00`. Byte `0x04` instructs GDB that an inline named Python script follows (name terminated by `\n`, script body terminated by `\0`).

#### 5.2 Upstream Diamond Deduplication vs. Live Local-vs-Upstream `path_erased()` Duplication Defect

Inspecting `DebuggerVisualizerFile` (`compiler/rustc_middle/src/middle/debugger_visualizer.rs:10-34`), `rustc_passes/src/debugger_visualizer.rs:30-36`, `rustc_metadata/src/rmeta/encoder.rs:2065`, and `collect_debugger_visualizers_transitive` (`compiler/rustc_codegen_ssa/src/base.rs:640-658`) reveals a previously subtle deduplication asymmetry:

```rust
// rustc_middle/src/middle/debugger_visualizer.rs:10-20
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Encodable, Decodable)]
pub struct DebuggerVisualizerFile {
    pub src: Arc<[u8]>,
    pub visualizer_type: DebuggerVisualizerType,
    pub path: Option<PathBuf>,
}
```

- **Upstream `.rlib` crates:** Before serializing into crate metadata (`rmeta`), `rustc_metadata` maps every visualizer through `DebuggerVisualizerFile::path_erased()` (`path: None`) so privacy-sensitive host paths do not leak into `.rlib`s. Similarly, `hir/map.rs:1192` calls `path_erased()` when computing the crate hash.
- **Local leaf crate:** `rustc_passes/src/debugger_visualizer.rs:30-34` constructs `LOCAL_CRATE` entries via `DebuggerVisualizerFile::new(source, visualizer_type, file)`, retaining `path: Some(file)` for dep-info reporting.
- **Collection (`compiler/rustc_codegen_ssa/src/base.rs:640-658`):**
  ```rust
  pub fn collect_debugger_visualizers_transitive(
      tcx: TyCtxt<'_>,
      visualizer_type: DebuggerVisualizerType,
  ) -> BTreeSet<DebuggerVisualizerFile> {
      tcx.debugger_visualizers(LOCAL_CRATE)
          .iter()
          .chain(
              tcx.crates(()).iter()
                  .filter(|&cnum| tcx.used_crate_source_flags(*cnum)
                      .intersects(CrateSourceFlags::RMETA | CrateSourceFlags::RLIB))
                  .flat_map(|&cnum| tcx.debugger_visualizers(cnum)),
          )
          .filter(|visualizer| visualizer.visualizer_type == visualizer_type)
          .cloned()
          .collect::<BTreeSet<_>>()
  }
  ```
  Because `collect_debugger_visualizers_transitive` omits `.map(DebuggerVisualizerFile::path_erased)` on `LOCAL_CRATE`, `BTreeSet` compares `(src, ty, Some(local_path))` against `(src, ty, None)` and treats them as **distinct**!

Probe 3 (`support/probe_results.json`) empirically confirms BOTH halves of this behavior live:
1. **4-crate upstream diamond (`vis_shared` -> `{vis_left, vis_right}` -> `vis_leaf`, where both `vis_shared` and `vis_left` embed `# shared-printer-v1\n` under different filenames `shared.py` and `shared_copy.py`, and `vis_leaf` embeds `# leaf-printer-v1\n`):**
   - Zero `.rlib` `.o` members contain `.debug_gdb_scripts` (`rlib_emits_debug_gdb_scripts = false`).
   - `vis_leaf` `.debug_gdb_scripts` is `128` bytes containing `3` entries:
     - `header_byte = 1`: `"gdb_load_rust_pretty_printers.py"`
     - `header_byte = 4`: `"pretty-printer-vis_leaf-0\n# leaf-printer-v1\n"`
     - `header_byte = 4`: `"pretty-printer-vis_leaf-1\n# shared-printer-v1\n"`
   - Upstream diamond copies deduplicated cleanly (`deduplicated_shared_script_count = 1`, `upstream_diamond_deduplicates`).
2. **Local-vs-upstream identical-bytes test (`vis_leaf_local_dup` depends on `vis_shared` AND locally declares `#![debugger_visualizer(gdb_script_file = "local_shared.py")]` with byte-identical `# shared-printer-v1\n`):**
   - `vis_leaf_local_dup` `.debug_gdb_scripts` is `150` bytes with **`shared_script_occurrences = 2`** (`local_and_upstream_identical_bytes_duplicated = true`):
     - `header_byte = 4`: `"pretty-printer-vis_leaf_local_dup-0\n# shared-printer-v1\n"` (from upstream `vis_shared`, `path = None`)
     - `header_byte = 4`: `"pretty-printer-vis_leaf_local_dup-1\n# shared-printer-v1\n"` (from local `vis_leaf_local_dup`, `path = Some(...)`)
   - Note that the identical `BTreeSet` collector also feeds `info.natvis_debugger_visualizers` (`base.rs:1211-1212`), so the same local-vs-upstream non-deduplication applies to `natvis_file` on MSVC targets as well (`local_vs_upstream_fails_dedup_without_path_erase`).

---

### 6. `#[collapse_debuginfo(yes|no|external)]` and `-C collapse-macro-debuginfo` Precedence

Basis: normative + source + execution + derived (Lean v4.34.1 kernel proof)

Per `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/attributes/debugger.md` L174-228, `r[attributes.debugger.collapse_debuginfo]`) and `compiler/rustc_expand/src/base.rs:838-862` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), `SyntaxExtension::get_collapse_debuginfo(sess, attrs, ext)` evaluates an exact 4×4 lookup table (`ext = !is_local`, built-in macros default `attr` to `Yes`, user `macro_rules!` default `attr` to `Unspecified`):

| `-C collapse-macro-debuginfo` \ `#[collapse_debuginfo(...)]` | `no` | *(unspecified, user)* | `external` | `yes` / *(built-in)* |
| :--- | :--- | :--- | :--- | :--- |
| `no` | `false` | `false` | `false` | `false` |
| *(unspecified)* | `false` | `is_external` | `is_external` | `true` |
| `external` | `false` | `is_external` | `is_external` | `true` |
| `yes` | `true` | `true` | `true` | `true` |

When `expn_data.collapse_debuginfo == true`, `HygieneData::walk_chain_collapsed` (`compiler/rustc_span/src/hygiene.rs:658-678`) walks outward through macro expansion frames up to the function body and rewrites the emitted debuginfo span to the outermost collapsed macro's `call_site`.

Empirical Probe 5B (`support/probe_results.json`) verified both cross-crate (`mac_up.rs` -> `dn_*.rs`, call site line `3`) and same-crate (`mac_local.rs`, defs lines `1, 3, 5, 7`, calls lines `11, 12, 13, 14`) DWARF `.debug_line` and `DW_AT_decl_line` behavior:

| Scope | Macro / Attribute | CLI Flag | `mac_up.rs` in `.debug_line`? | Observed Local `DW_AT_decl_line` | Collapsed to Call Site? |
| :--- | :--- | :--- | :--- | ---: | :--- |
| Cross-crate | `m_default!` *(unspecified)* | *(default)* | `false` | `3` (call site) | **Yes** |
| Cross-crate | `m_yes!` (`yes`) | *(default)* | `false` | `3` (call site) | **Yes** |
| Cross-crate | `m_external!` (`external`) | *(default)* | `false` | `3` (call site) | **Yes** |
| Cross-crate | `m_no!` (`no`) | *(default)* | **`true`** | **`22`** (macro body in `mac_up.rs`) | **No** |
| Cross-crate | `m_no!` (`no`) | `-C collapse-macro-debuginfo=yes` | `false` | `3` (call site) | **Yes (CLI override)** |
| Cross-crate | `m_yes!` (`yes`) | `-C collapse-macro-debuginfo=no` | **`true`** | **`13`** (macro body in `mac_up.rs`) | **No (CLI override)** |
| Same-crate | `loc_default!` *(unspecified)* | *(default)* | *(local file)* | `1` (macro body; call at `11`) | **No (`if-ext = false`)** |
| Same-crate | `loc_yes!` (`yes`) | *(default)* | *(local file)* | **`12`** (call site; def at `3`) | **Yes** |
| Same-crate | `loc_no!` (`no`) | *(default)* | *(local file)* | `5` (macro body; call at `13`) | **No** |
| Same-crate | `loc_ext!` (`external`) | *(default)* | *(local file)* | `7` (macro body; call at `14`) | **No (`if-ext = false`)** |

---

### 7. Kernel-Checked `Lean v4.34.1` Mechanization (`support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean`)

Basis: derived (Lean v4.34.1 kernel verification)

All six mechanisms above are mechanized in `support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean` and kernel-checked under `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. To conform strictly to Anneal's kernel-replay hygiene (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/audit/TrustedBoundary.lean:2164-2167`, where compiler-generated `*._unsafe_rec` helpers are omitted during standalone kernel replay), all recursive helpers are defined via primitive `Nat.rec`/`List.rec` marked `noncomputable def` and no nested inductives use `deriving DecidableEq, Repr`. A MetaM environment inspection over all `254` module constants in `env.constants.map₁.toList` confirmed:

- **`36` named user theorems** (`67` total module theorems including generated projections/injections)
- **`0` `._unsafe_rec` constants** (`UNSAFE_REC_COUNT = 0`)
- **`0` forbidden axioms** (`0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `Lean.ofReduceNat`, `0` `Lean.trustCompiler`; complete axiom footprint across all `67` theorems is `[propext]`, with `0` uses of `Quot.sound`, `omega`, `bv_decide`, `native_decide`, or `partial def`)

Core mechanized theorems:

| Theorem (`RustcDwarfNicheGdbSoundness.*`) | Axioms | Statement Summary |
| :--- | :--- | :--- |
| `computeDiscriminantRange_sorted` | `[propext]` | `(computeDiscriminantRange start end_).1 ≤ (computeDiscriminantRange start end_).2` unconditionally. |
| `natvis_wrapping_branch_dead_code` | `[propext]` | Calling `inCircularRange` on `computeDiscriminantRange` never takes the wrapping branch. |
| `wrapping_interior_false_negative` | `[propext]` | For any wrapping range (`end_ < start`), every interior value `x < end_ ∨ start < x` is true in `inCircularRange` but `false` under `computeDiscriminantRange`. |
| `wrapping_exterior_false_positive` | `[propext]` | For any wrapping range (`end_ < start`), every exterior gap value `end_ < x ∧ x < start` is `false` in `inCircularRange` but `true` under `computeDiscriminantRange`. |
| `wrapping_bug_is_exact_negation_off_endpoints` | `[propext]` | For any `x < modulus` with `x ≠ start ∧ x ≠ end_`, `computeDiscriminantRange` computes exact `!inCircularRange modulus start end_ x`. |
| `wrapping_endpoints_survive` | `[propext]` | Both boundary endpoints `start` and `end_` survive `computeDiscriminantRange`. |
| `unsorted_circular_range_sound_and_exact` | `[]` | Preserving `(start, end_)` unsorted is sound, unambiguous, dual-match-free, and zero-false-positive under both `decodeNatvisDisplay` and `decodeCppLikeFieldOrder`. |
| `native_dwarf_sound_on_inhabited` | `[]` | Omitting `DW_AT_discr_value` on the untagged variant decodes every inhabited payload and exact tag identically, independent of wrapping. |
| `native_dwarf_maps_unused_niche_to_default` | `[]` | Documents DWARF's exact negative space: uninhabited unused niche bytes fall back to `.untagged`. |
| `signedWrap_buggy_natvis_unmatched_valid_count` | `[propext]` | Exhaustive 256-byte kernel check (`countU8`): exactly `19` of `21` valid `SignedWrap::Valid` payloads fail (`UNMATCHED`) under buggy `(10, 246)`. |
| `signedWrap_buggy_natvis_matched_valid_count` | `[propext]` | Exactly `2` of `21` valid payloads (`246`, `10`) survive. |
| `signedWrap_buggy_unused_niche_false_positive_count` | `[propext]` | All `233` unused niche bytes (`13..=245`) falsely match `Valid`. |
| `signedWrap_buggy_tagA_tagB_dual_match_and_cpplike_hijack` | `[]` | `TagA (11)` and `TagB (12)` trigger NatVis `<Expand>` dual-match AND are misclassified as `Valid` by `cpp_like.rs` field-order scan. |
| `signedWrap_fixed_exact_counts` | `[propext]` | Preserving `(246, 10)` yields `21/21` valid, `233/233` unused rejected, `0` dual matches. |
| `signedWrap_native_dwarf_counts` | `[propext]` | Native DWARF decodes `21/21` valid payloads + `TagA`/`TagB` cleanly. |
| `signedWrap128_buggy_inversion` | `[]` | Proves the identical inversion on `SignedWrap128` over `2^128` (`0` and `2^128 - 5` fail; `13` falsely matches). |
| `natvis_16_variant_cap_drops_variant16` | `[]` | Every variant with index `>= 16` returns `.unmatched` under `intrinsic.natvis`'s 16-variant cap. |
| `text_mutated_for_every_nonzero_debuginfo` | `[propext]` | Every non-zero `DebugInfoLevel` strictly mutates executable `.text` and retains `.debug_gdb_scripts` even under `StripMode.{debuginfo,symbols}`. |
| `text_identical_across_all_nonzero_levels` | `[propext]` | Entry-shim `.text` is invariant across all four non-zero levels and strip modes. |
| `text_invariant_when_disabled_or_non_executable` | `[propext]` | `targetEmitGdbScripts = false` or `ct ≠ .executable` leaves entry-shim `.text` unchanged. |
| `thorin_dwp_bit_identical_under_remap` | `[]` | Distinct build directory prefixes mapped to a shared canonical prefix yield identical `thorin` `.dwp` artifacts. |
| `upstream_diamond_deduplicates` / `local_vs_upstream_fails_dedup_without_path_erase` | `[propext]` | Upstream diamond collapses to length `1`; local `some p` vs. upstream `none` duplicates to length `2` unless `pathErased` is applied. |
| `collapse_cli_overrides_all` / `collapse_default_and_external_behavior` | `[propext]` | Formalizes the complete 4×4 `collapse_table` from `rustc_expand/src/base.rs:844-862`. |

---

## Boundaries

- **Live Windows debugger execution (`WinDbg` / Visual Studio NatVis runtime / `LLDB` on CodeView PDB): `not examined`.** Probe 1 compiled `--target x86_64-pc-windows-msvc --emit=llvm-ir -C debuginfo=2` on Linux and evaluated the exact NatVis `<Intrinsic Name="in_range">` expression (`src/etc/natvis/intrinsic.natvis:306,346-378`) programmatically and in Lean against the emitted LLVM IR `DISCR_BEGIN`/`DISCR_END`/`DISCR_EXACT` metadata. It did not link a Windows `.pdb` or drive WinDbg/Visual Studio GUI interactively; in particular, while both `tag == variant1.DISCR_EXACT` and `in_range(tag, variant0.DISCR_BEGIN, variant0.DISCR_END)` are provably `true` simultaneously on `TagA (11)` and `TagB (12)`, how a specific Visual Studio version renders duplicate `<ExpandedItem>` matches in its UI tree is **not examined**.
- **Direct execution of `rustc 1.102.0-nightly`: `not examined` on this host.** Empirical execution in `support/probe_results.json` ran on `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65, LLVM 22.1.6)`, while upstream source auditing inspected `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`1.102.0`). Extending empirical behavior to `342d74463` rests on direct line-by-line source verification showing identical implementation logic across both commits; subtle LLVM `22.1.6` vs. `23.x` codegen instruction-selection differences (such as GOT-indirect `mov ...(%rip), %rax; movzbl (%rax), %eax` vs. direct RIP-relative `movzbl __rustc_debug_gdb_scripts_section__(%rip), %eax` depending on relocation model / linker relaxation) can change exact `.text` byte counts while preserving the `.text` non-invariance property.
- **Alternative `rustc` codegen backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`): `not examined`.** Inspection confirmed `rustc_codegen_gcc` implements `insert_reference_to_gdb_debug_scripts_section_global`, but neither Cranelift nor GCC codegen was executed or audited for enum debuginfo, `.dwp`, or `.debug_gdb_scripts`.
- **Non-ELF split debuginfo (`macOS` `.dSYM` via `dsymutil`, Windows `.pdb` via `link.exe`/`lld-link`, DWARF v2/v3, and `-Z split-dwarf-inlining=false` or `rustc` LTO + split DWARF): `not examined`.** Reproducibility of `thorin` `.dwp` under ThinLTO/FatLTO, multi-CGU parallel builds (`-C codegen-units > 1`) with non-deterministic symbol hashing, or external C static libraries embedded in `.rlib`s was not tested beyond `-C codegen-units=1`.
- **GDB runtime auto-load execution and `DW_TAG_variant` consumers (`gdb`, `lldb`, `rust-gdb`): `not examined`.** Probe 1 and Probe 5 verified the emitted ELF/DWARF DIEs via `GNU readelf 2.47` (`--debug-dump=info`, `--debug-dump=decodedline`) and parsed `.debug_gdb_scripts` raw bytes directly without launching an interactive `gdb` process.
- **Does `debuginfo=0` vs. `debuginfo!=0` guarantee `.text` invariance on targets with `emit_debug_gdb_scripts = false` or on non-entry functions? `unknown` in general.** The Lean theorem `text_invariant_when_disabled_or_non_executable` proves only that `create_entry_fn` injects no `.debug_gdb_scripts` volatile load; LLVM backend passes are designed to be debuginfo-invariant (via `DbgRecord`/debug intrinsics), but empirical verification across arbitrary `-O3` programs with LLVM passes is outside the single-function `main` probe and is **not established** as a universal LLVM guarantee.
- **Unsupported / removed opt-out:** `#![feature(omit_gdb_pretty_printer_section)]` is **unsupported** (removed in `rustc 1.91.0`, `E0557`, PR `#144738`).
- **Lean formalization abstraction boundary:** `support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean` is a standalone Lean `v4.34.1` specification model over `Nat`/inductive types; it does not import `joshlf/anneal`'s `Trusted.MirSemantics` or `Miri` modules (by design for self-contained single-file kernel checking) and models `thorin` serialization and x86-64 `.text` emission abstractly rather than parsing raw ELF binary headers inside Lean.

---

## Evidence

### Primary Upstream Git Sources (Pinned 40-Hex Commits, Inspected `2026-11-22`)

| Repository & Full Commit | Path | Symbols / Line Range | Finding Supported |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `src/version` | L1 (`1.102.0`) | Upstream version identity |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs` | `DiscrResult` (L379-390), `compute_discriminant_value` (L397-436; buggy `.min`/`.max` L420-426) | Wrapping-niche inversion bug |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/cpp_like.rs` | Wrapping-range spec (L88-94), `is_in_range` pseudocode (L173-179), `compute_discriminant_value` call (L441), `DiscrKind::Range`/`Range128` emission (L541-550, L639-687), coroutine `VariantNames` (L730-735), `variant_union_field_name` (L925-949) | C++-like enum & coroutine encoding, `variant16+` emission |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `src/etc/natvis/intrinsic.natvis` | `enum2$<*>` (L303-483), `in_range` (L306-310), `in_range128` (L335-344), `variant0..variant15` `<DisplayString>` (L346-412) and `<Expand>` (L414-482) | NatVis circular-range evaluator, exact-before-range priority, 16-variant cap |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/native.rs` | Coroutine numeric variant names (L196-199), `"__state"` discriminant name (L345-348), `discr_value.opt_single_val()` (L437-440) | Native DWARF default-variant immunity & coroutine `__state` |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_ssa/src/debuginfo/mod.rs` | `tag_base_type_opt` (L57-96; unsigned niche normalization L71-88) | Unsigned tag normalization for niche enums |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_ssa/src/base.rs` | `create_entry_fn` volatile-load hook (L563), `collect_debugger_visualizers_transitive` (L640-658), NatVis transitive collection (L1210-1213) | `.text` mutation call site & `path_erased` dedup asymmetry |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs` | `insert_reference_to_gdb_debug_scripts_section_global` (L18-25), `get_or_insert_gdb_debug_scripts_section_global` (L29-82), `needs_gdb_debug_scripts_section` (L84-116, predicate L113-115) | Volatile load injection, `\x01`/`\x04` framing, crate-type gating |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_llvm/src/debuginfo/mod.rs` | `debuginfo_finalize` (L727-741) | Per-CGU `LinkOnceODRLinkage` global emission (`staticlib` vs. `cdylib`) |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_feature/src/removed.rs` | `omit_gdb_pretty_printer_section` removal (L231, `"1.91.0"`, PR `#144738`) | Absence of opt-out attribute (`E0557`) |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_target/src/spec/mod.rs` | `emit_debug_gdb_scripts: bool` field (L2497) and default `true` (L2829) | Target default governing ELF `.text` mutation |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_codegen_ssa/src/back/link.rs` | `link_dwarf_object` (`thorin::DwarfPackage`, L909-1017; `into_sorted_stable_ord` L978; `MissingReferencedObjectBehaviour::Skip` L996) | In-process `.dwp` assembly and deterministic ordering |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_middle/src/middle/debugger_visualizer.rs` & `compiler/rustc_passes/src/debugger_visualizer.rs` | `DebuggerVisualizerFile` (L10-34), `DebuggerVisualizerFile::new` (L30-34) | Local `path: Some(...)` vs. upstream `path_erased()` `None` |
| `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_expand/src/base.rs` & `compiler/rustc_span/src/hygiene.rs` | `get_collapse_debuginfo` 4×4 `collapse_table` (L838-862), `walk_chain_collapsed` (L658-678) | `#[collapse_debuginfo]` precedence and call-site rewriting |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Local installed `rustc-src` + `rustc 1.98.0-nightly` binary | Identical logic across all audited modules (line offsets noted under **Applicability**) | Executed empirical toolchain |
| `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | `src/attributes/debugger.md` | `r[attributes.debugger.debugger_visualizer]` (L8-167), `r[attributes.debugger.collapse_debuginfo]` (L174-228) | Normative attribute rules |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `vendor/lean-miri/Miri/ABI/WrappingRange.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `trusted/rustc-capture/src/driver.rs`, `trusted/audit/TrustedBoundary.lean` | `WrappingRange.contains` (L39-43), `refEnumLayoutData` (L823-848), `AnalysisCallbacks::after_analysis` (L75-84), `replayCorrAndVendor` `*._unsafe_rec` omission (L2164-2167) | Anneal trusted-boundary alignment |
| `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | `Lean v4.34.1` kernel | Direct kernel check + MetaM `env.constants.map₁` and `Lean.collectAxioms` audit | Formal soundness proofs |

### Preserved Package Support Artifacts

1. **`support/probe_dwarf_dwp_niche_discr_and_gdb_text.py`:** Standalone, zero-hardcoded-metric Python 3 reproducer executing all 5 compiler probes inside a `tempfile.TemporaryDirectory`, parsing ELF64 sections and DWARF `.debug_cu_index` headers directly, scrubbing all temporary directory paths to `<TMP>`, and writing structured JSON.
2. **`support/probe_results.json`:** Complete `28,916`-byte JSON transcript captured on `2026-11-22` from running `support/probe_dwarf_dwp_niche_discr_and_gdb_text.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / LLVM `22.1.6` / `GNU readelf 2.47` / `GNU objdump 2.47`.
3. **`support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean`:** Self-contained `Lean v4.34.1` formalization (`36` user theorems, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`, max axiom set `[propext]`).

### Verification Execution Receipts (`2026-11-22`)

- **Empirical probe run:**
  ```sh
  python3 support/probe_dwarf_dwp_niche_discr_and_gdb_text.py support/probe_results.json
  # Exit code: 0 (wrote 28,916 bytes; all 5 probes executed live)
  ```
- **Strict Lean `v4.34.1` kernel check:**
  ```sh
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean
  # Exit code: 0 (0 errors, 0 warnings)
  ```
- **Lean `v4.34.1` MetaM environment audit (`env.constants.map₁` + `Lean.collectAxioms`):**
  - `MODULE_CONSTANTS = 254`
  - `ALL_THEOREMS = 67` (`USER_THEOREMS = 36`)
  - `UNSAFE_REC_COUNT = 0`
  - `BAD_AXIOM_COUNT = 0`
  - `ALL_AXIOMS_USED = [propext]`

---

## Revalidation

Each major finding can be cheaply revalidated on a newer `rustc` nightly or upstream `rust-lang/rust` revision via targeted commands:

1. **Re-run the full empirical 5-probe suite against any nightly `rustc` (requires `x86_64-pc-windows-msvc` `rust-std` component for Probe 1B and `readelf`/`objdump`/`ar` on Linux):**
   ```sh
   RUSTC=$(which rustc) python3 support/probe_dwarf_dwp_niche_discr_and_gdb_text.py /tmp/reval_probe.json
   ```
   Check these exact discriminating keys in `/tmp/reval_probe.json`:
   - **Wrapping-niche bug fixed?** `probe_1_wrapping_niche_enum_discr_inversion.msvc_cpp_like_emitted_discr_begin_u8` changes from `10` to `246`, `..._discr_end_u8` changes from `246` to `10`, and `exhaustive_256_byte_audit.natvis_display_valid_unmatched_count` drops from `19` to `0` (and `natvis_unused_false_positive_count` drops from `233` to `0`).
   - **`.text` invariance restored or opt-out reintroduced?** `probe_2_gdb_scripts_text_mutation.text_identical_d0_vs_line_directives` becomes `true`, or `levels.debuginfo_2_strip_debuginfo.has_debug_gdb_scripts` becomes `false`.
   - **Local-vs-upstream `path_erased()` asymmetry fixed?** `probe_3_debugger_visualizer_transitive.local_vs_upstream_path_erased_asymmetry.shared_script_occurrences` drops from `2` to `1`.
   - **`thorin` `.dwp` determinism preserved?** `probe_4_split_debuginfo_and_thorin_dwp.remap_path_prefix_only.remapped_packed_dwp_bit_identical` remains `true`.
   - **Coroutine native DWARF numeric variant names updated?** `probe_5_coroutine_and_collapse_debuginfo.coroutine_linux_dwarf.numeric_variant_names` changes from `["0", "1", "2", "3"]` to symbolic names (`Unresumed`, `Returned`, `Panicked`, `Suspend0`).

2. **Diff the narrow upstream source regions in `rust-lang/rust` against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:**
   ```sh
   git diff 342d74463af7dd3018ef6aa04dd5500c2deb5bd1..HEAD -- \
     compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs \
     compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/cpp_like.rs \
     compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/native.rs \
     src/etc/natvis/intrinsic.natvis \
     compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs \
     compiler/rustc_codegen_ssa/src/base.rs \
     compiler/rustc_codegen_ssa/src/back/link.rs \
     compiler/rustc_expand/src/base.rs
   ```

3. **Re-verify the `Lean v4.34.1` kernel proofs (takes `< 3` seconds single-file):**
   ```sh
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/DwarfSplitDwpNicheEnumDiscrAndGdbTextSoundness.lean
   ```
   A passing Lean check establishes internal consistency of the mechanized theorems over the modeled predicates; it does not by itself verify that a newer `rustc` revision still matches the modeled source behavior without running checks (1) and (2).
