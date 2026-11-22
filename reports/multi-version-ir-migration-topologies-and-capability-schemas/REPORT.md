# Multi-Version IR Migration Topologies, Orthogonal Versioned Capability Schemas, and Edition-Independent Post-Cleanup MIR

## Summary

Primary-source inspection across nine multi-version compiler, bytecode, and verification ecosystems—`ocaml-ppx/ocaml-migrate-parsetree` (`v1.8.0` and post-`v2.4.0` deprecation), `ocaml-ppx/ppxlib`, `llvm/llvm-project` (LLVM `BitcodeReader`/`AutoUpgrade` and MLIR `BytecodeDialectInterface`/`DialectConversion`), `scala/scala3` (`TASTy`), `WebAssembly/spec` + `bytecodealliance/wasm-tools` (`wasmparser`), `KhronosGroup/SPIRV-Headers` + `SPIRV-Tools`, `AeneasVerif/charon` (`CrateData` / `charon-ml`), `Frama-C` (`Machdep.mach`), and `rust-lang/rust` + `rust-lang/rust-analyzer`—paired with a standalone Python 3.10+ topology probe (`support/probe_ir_migration_topologies.py` and `support/probe_ir_migration_topologies_results.json`) over the nine verified `rustc_middle::mir::syntax` mutations (`1.93.1`–`1.102.0-nightly` plus non-linear `2026-10-20` nightly `8144389c`) establishes five results:

1. **Why Pairwise Stepwise Chains (`ocaml-migrate-parsetree` v1 and `ppxlib`'s `Astlib`) and Lagging Snapshot Hubs Break Down (`source` + `derived`):**
   - `ocaml-migrate-parsetree` v1 (`1d72648812bb235d1576f483cacdf546e25c03d8`) chained adjacent deep-copy functors (`migration_compose`, `src/migrate_parsetree_versions.ml:356–379, 589–606`) across multi-version rewriter groups (`src/migrate_parsetree_driver.ml:126–170, 229–301`), allocating up to $2(v_{\text{comp}} - v_{\min})$ full intermediate ASTs per file and crashing with `Def.Migration_error` (`src/migrate_parsetree_def.mli:17–42`) whenever unrelated code in the same file used syntax newer than the oldest linked PPX.
   - `ppxlib` (`11a46ff72c2cd8bc02068654950c2573746adff5`) eliminated per-plugin version ping-ponging by registering all transforms on a single trunk AST (`module Js = Versions.OCaml_502`, `ast/import.ml:9`). Internally, however, `ast/versions.ml:517–534, 698–723` **still composes adjacent pairwise `Astlib.Migrate_<n>_<n+1>` deep-copy hops** (`4.08`..`5.06`), and because `Js = OCaml_502` lags behind OCaml `5.3`–`5.6`, `astlib/encoding_502.ml`–`encoding_506.ml` must tunnel newer constructs through **22 synthetic `"ppxlib.migration.*"` extension/attribute wrappers** (requiring `Clean.remove_migration_attributes` on pretty-print at `astlib/clean.ml:1–19`, raising `Error.invalid_encoding` if a PPX inspects tunneled code, and still raising `Error.migration_error` on unencodable `5.5`/`5.6` external types at `astlib/migrate_505_504.ml:36` and `migrate_505_506.ml:560`).

2. **Ingest Canonicalization Must Reject Codegen-Style Over-Approximation and Separate Wire Decoding From Consumer Capability Legality (`normative` + `source` + `derived`):**
   - LLVM (`2252e5dc213dd1402eb8942de5fa1608b7460d50`) keeps in-memory `llvm::Module` unversioned by canonicalizing legacy records in `BitcodeReader.cpp` and `AutoUpgrade.cpp`. Where no 1:1 equivalent exists, `AutoUpgrade.cpp` relies on **codegen-sound conservative widening** (e.g., upgrading `llvm.strip.invariant.group` to stronger `llvm.launder.invariant.group` at `L2413–2420`, widening AMDGPU sync scopes to `"agent"` at `L5586–5591`, and assuming 64-bit max pointers in `UpgradeBitCastInst` at `L6915–6949`). Silent widening or target-unaware pointer heuristics are unsound for formal verification unless explicitly modeled or rejected fail-closed.
   - MLIR (`2252e5dc213dd1402eb8942de5fa1608b7460d50`) and Scala 3 `TASTy` (`ff8f3950da9d83b44df246ad32d5882c259a28bb`) cleanly separate **wire-schema compatibility** (`BytecodeDialectInterface::readVersion` + `upgradeFromVersion` before `verify` in `BytecodeReader.cpp:2216–2225, 2586–2600`; `TastyFormat.isVersionCompatible` over `(Major, Minor, Experimental)` in `TastyFormat.scala:381–393`) from **consumer semantic legality** (`ConversionTarget::LegalizationAction::{Legal, Dynamic, Illegal}` enforced fail-closed by `applyFullConversion` in `DialectConversion.cpp:3329–3336`).
   - Across multi-producer verification and portable-IR formats, `Charon` (`b23c297f57c0`, `export.rs:42–63`, `OfJson.ml:28–35`) enforces exact producer-version lockstep (`version == "0.1.324"`), `WebAssembly` (`6fca707686ed`, `encode.ml:3`) + `wasmparser` (`97a984fd8eb5`, `WasmFeatures: u64` in `features.rs:139–275`) freeze binary `version = 1` while gating additive opcodes by proposal bitflags, `SPIR-V` (`3c8fd3529731`, `binary.cpp:48–62`, `validate_capability.cpp:355–471`) enforces two-sided preamble `OpCapability` declarations, and `Frama-C` (`189053d4a2bd`, `machdep.mli:17–98`) parameterizes one CIL AST and WP engine over a 53-field `Machdep.mach` target/dialect record.

3. **Five-Topology Evaluation (`T1`–`T5`) Over Real `rustc` `Runtime(PostCleanup)` MIR History Refutes Raw-Latest, Intersection, Pairwise-Chain, and Per-Version-Evaluator Designs (`execution` + `source` + `derived`):**
   - **`T1` (Latest-Version Canonical Raw IR, `1.102.0-nightly` `syntax.rs`):** Fails 1:1 representation on **`2 / 11` specimens** because `rustc` *deletes* operational MIR variants (`Rvalue::ShallowInitBox` in `6d4b1b38e76c`; standalone `StatementKind::Retag` in `e402c1edf047`), oscillates across non-linear release/nightly branch DAGs (`8144389c` `2026-10-20` has `Goto { target, loop_hint_attrs }` whereas `1.100.0` `0ef1bc38` `2026-11-09` does not), and destabilizes downstream operational semantics on every compiler bump.
   - **`T2` (Oldest / Common-Intersection IR):** Collapses the strict 9-pin variant intersection over mutating MIR enums to **`0` variants** (`[]`), failing or unsoundly erasing **`6 / 11` specimens** (`126 / 782` live bodies using `WithRetag::No` and `5 / 641` live `memchr` bodies using `CastKind::BoxDerefTransmute`).
   - **`T3` (Pairwise Stepwise `Migrate_k_{k+1}` Chains):** Incurs up to `7` unidirectional hops (**`21,896` extra full-body allocations** across 8 pins on a `782`-body workload in `T3a`), up to `14` bidirectional hops (**`10,948` extra allocations** on one crate in `T3b`), or **`4 / 11` unidir (`5 / 11` round-trip) tunneling/error hazards** plus **`12,512` unidir / `25,024` bidir extra allocations** when targeting a lagging `1.98.0-nightly` hub (`T3c`, breaking **`5 / 641` live `memchr` bodies** on `1.99.0+`).
   - **`T5` (Separate Per-Version IRs & Evaluators):** Multiplies TCB AST definitions, operational semantics, WP rules, and reference correspondence proofs **`9x` across 9 pins** (**`7x`** even if deduplicated by `syntax.rs` class) and prevents zero-edit cross-compiler proof reuse.
   - **`T4` (Direct Per-Spoke Lowering to a Monotonic Feature-Parameterized Superset Trunk IR):** Lowers each compiler's `TyCtxt` in **1 pass** (`0` intermediate AST copies, `0` synthetic tunnel attributes, **`0 / 11` lossy specimens**), collapses all **9 pins (including non-linear `8144389c`) into `7` `syntax.rs` equivalence classes** (`1.99.0 == 1.99.1`; `8144389c == 1.102.0-nightly`), runs on **`1` shared evaluator/proof engine**, and enforces fail-closed `SemProfile` / `CAP_*` legality (`2 / 11` admitted under minimal `CAP_CORE_SCALAR_CFG`; `9 / 11` deterministically rejected as `fail_closed_unsupported(CAP_*)` until enabled).

4. **`Runtime(PostCleanup)` MIR in `rustc` Is 100% Edition-Independent (`source` + `derived`):**
   - Both `rustc` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `rustc_span/src/hygiene.rs:526–533, 1064–1066, 1159–1160`) and `rust-analyzer` (`37721d141370e0904033f7fc3a3abe11c446c4c1`, `crates/span/src/lib.rs:122–138`, `hygiene.rs:38–46`) track `Edition` (`2015`..`2024`) per token/span to resolve mixed-edition macros in the frontend while keeping operational MIR completely edition-free (`0` `Edition` references in `rust-analyzer`'s `crates/hir-ty/src/mir.rs`; `0` `Edition` fields on `rustc_middle::mir::Body`).
   - Every edition-dependent Rust language construct—`async` (`2018`) and `gen` (`2024`) coroutine blocks (`rustc_ast_lowering/src/expr.rs:402–408, 865–875`), RFC 2229 disjoint closure field captures (`2021`, `rustc_hir_typeck/src/upvar.rs:153–157, 469–474, 2749–2755`), `!` diverging type fallback (`2024`, `rustc_hir_typeck/src/fallback.rs:55–95`), and block tail-expression / `if let` temporary drop-scope narrowing (`2024`, `rustc_hir_analysis/src/check/region.rs:146–152, 353–375`)—is fully desugared into ordinary types, captures, and `StorageDead`/`Drop` CFG edges before `Runtime(PostCleanup)`. The sole edition-referencing MIR statement, `StatementKind::BackwardIncompatibleDropHint { place, reason: BackwardIncompatibleDropReason::Edition2024 }` (`mir/syntax.rs:447–457, 977–979`), is a lint-only `Nop` **unconditionally erased by `CleanupPostBorrowck`** (`rustc_mir_transform/src/cleanup_post_borrowck.rs:33–38`) prior to `MirPhase::Runtime(RuntimePhase::PostCleanup)`.

5. **Orthogonal Three-Axis Header Contract (`derived`):**
   - A multi-compiler verification IR must separate **(1) Wire/Trunk Schema Version** (`(major, minor)` governing monotonic Trunk IR layout and epoch-boundary variant pruning), **(2) Producer Provenance** (`(rustc_commit, driver_sha256, sysroot_sha256)` checked solely by TCB receipt auditing, with zero operational branches in semantics), and **(3) Semantic Capability & Target Profile** (`SemProfile` carrying target ABI layout, `RuntimeChecks` session mode, and `required_capabilities: BitSet<Cap>` checked fail-closed against enabled verifier capabilities).

## Applicability

### Subject Roles and Relationships

This report compares multi-version IR/AST migration mechanisms across twelve upstream compiler and verification codebases and evaluates five candidate multi-compiler IR topologies (`T1`–`T5`) over nine pinned `rust-lang/rust` MIR revisions and `joshlf/anneal`:

1. **OCaml AST migration libraries (`ocaml-ppx/ocaml-migrate-parsetree` @ `1d72648812bb235d1576f483cacdf546e25c03d8` [`v1.8.0`] and `5cb1140405820b9e8c751aada2268d3585b40d25` [post-`v2.4.0` deprecation]; `ocaml-ppx/ppxlib` @ `11a46ff72c2cd8bc02068654950c2573746adff5`):** Examined directly in source to contrast bidirectional multi-version pairwise chains (`OMP` v1) against single-trunk rewriting with internal pairwise `Astlib` hops and `"ppxlib.migration.*"` tunneling (`ppxlib` over OCaml `4.08`–`5.06` with `Js = OCaml_502`).
2. **Eager ingest upgrader and two-phase dialect legality systems (`llvm/llvm-project` @ `2252e5dc213dd1402eb8942de5fa1608b7460d50`; `scala/scala3` @ `ff8f3950da9d83b44df246ad32d5882c259a28bb`):** Examined at `llvm/lib/{Bitcode/Reader,IR}`, `mlir/{include,lib}/{Bytecode,Transforms}`, and `tasty/src/dotty/tools/tasty/` (`TASTy` format `28.11-1`).
3. **Capability-gated portable bytecodes and parameterized verification IRs (`WebAssembly/spec` @ `6fca707686ed4f36a1e30ec2ae7d3dd32b276704`; `bytecodealliance/wasm-tools` @ `97a984fd8eb54c055b2516af16489cf4cbf05065`; `KhronosGroup/SPIRV-Headers` @ `fb1379425b16e58dcbdda7be0f8604a7f5cdce78` [`1.6.rev7`]; `KhronosGroup/SPIRV-Tools` @ `3c8fd35297315682906894621677f1b7003461ef`; `AeneasVerif/charon` @ `b23c297f57c0b2072de7967c7f17088db0278a8c` [`v0.1.324`, pinned to `nightly-2026-09-17`]; `Frama-C` @ `189053d4a2bd460c5c557dba8569474ff0419e73`):** Examined as comparative schema-versioning and capability-parameterization architectures.
4. **Rust edition hygiene and `Runtime(PostCleanup)` MIR evolution (`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` plus nine MIR schema pins from `1.93.1` [`01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`] through `1.102.0-nightly` [`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`] and non-linear `1.101.0-nightly` [`8144389c895da997dbdecaa635e41d6a50be6ffd`]; `rust-lang/rust-analyzer` @ `37721d141370e0904033f7fc3a3abe11c446c4c1`; `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Examined for edition desugaring invariants and empirical topology evaluation.

### Scope, Shared vs. Version-Specific Behavior, and Companion Reports

- **Shared across all examined `rust-lang/rust` revisions (`1.93.1`–`1.102.0-nightly` and `342d74463af7`):** `MirPhase::Runtime(RuntimePhase::PostCleanup)` is completely edition-free (`BackwardIncompatibleDropHint` is erased in `CleanupPostBorrowck`).
- **Version-specific across the nine `rust-lang/rust` MIR pins:** Six of ten core `rustc_middle::mir::syntax` enums undergo nine structural mutations (`10` atomic variant/field edits), including both **variant additions** (`Operand::RuntimeChecks`, `Rvalue::Reborrow`, `AssertKind::NullReferenceConstructed`, `CastKind::BoxDerefTransmute`, `ProjectionElem::PhantomDeref`), **payload widenings** (`Rvalue::Use(Operand, WithRetag)`, `TerminatorKind::Goto { target, loop_hint_attrs }`), and **variant deletions** (`Rvalue::NullaryOp`, `Rvalue::ShallowInitBox`, `StatementKind::Retag`).
- **Companion corpus relationships:** `rustc-public-stable-mir-vs-middle-mir-capture-seam-completeness` establishes why a UB-preserving verifier must extract `rustc_middle::mir` at `Runtime(PostCleanup)` with `-Zmir-preserve-ub` rather than `rustc_public` (`Runtime(Optimized)`). `rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility` measures per-crate body drift (`782` bodies across `feature_probe`, `ryu 1.0.23`, `itoa 1.0.19`, and `memchr 2.8.3`) and causal `rustc` commits. `afp-release-upgrades-mathport-adaptation-notes-coq-ci-overlays-pumpkin-patch-and-prism-repair-mining` documents downstream proof-library upgrade protocols across Lean/Mathlib, Isabelle/AFP, and Rocq. This report complements all three without duplicating their measurements by analyzing **multi-version IR migration topologies, capability-gated wire/semantic schemas, and frontend edition erasure**.

## Findings

### 1. Comparative Anatomy of Multi-Version IR and AST Systems

#### 1.1 OCaml `ocaml-migrate-parsetree` v1 to `ppxlib`: Pairwise Hop Chains, Lagging `OCaml_502` Hub, and 22 Synthetic Tunnel Attributes

`Basis: source + documentation + derived`

In `ocaml-migrate-parsetree` `v1.8.0` (`1d72648812bb235d1576f483cacdf546e25c03d8`), snapshots of `Parsetree`, `Asttypes`, `Outcometree`, `Docstrings`, and `Ast_mapper` are vendored for every major OCaml release from `4.02` through `4.12` (`src/ast_402.ml`–`src/ast_412.ml`). Cross-version migration in `src/migrate_parsetree_versions.ml:20–771` relies on three mechanisms:

1. **Extensible GADT Witnesses and Doubly-Linked Adjacency Pointers (`src/migrate_parsetree_versions.ml:20–29, 145–202`):** Each version module `OCaml_402`..`OCaml_412` extends `type _ witnesses += Version : types witnesses` (packaging 18 AST node types and mappers) and holds a mutable `migration_info` record (`next_version`, `previous_version`).
2. **Linear Functor Composition (`src/migrate_parsetree_versions.ml:356–379, 522–606`):** `Register_migration` links adjacent versions $(v_n, v_{n+1})$. Calling `migrate (module A) (module B)` walks the chain step-by-step and composes 18 deep-copy functions (`let compose f g x = f (g x)` in `migration_compose`, `L589–606`). Because OCaml does not fuse recursive algebraic datatype rebuilds across function composition, migrating across $d = |j - i|$ versions allocates **$d$ complete heap `Parsetree` copies** (`d - 1` transient intermediate trees).
3. **Multi-Version Ascending Driver Ping-Pong (`src/migrate_parsetree_driver.ml:126–170, 229–301`):** `Migrate_parsetree_driver.register` let each PPX rewriter specify its own target `ocaml_version`. `add_rewriter` (`L126–138`) sorted rewriters into `rewriter_group`s in ascending version order; `rewrite_structure` (`L229–251`) downgraded the file from `OCaml_current` ($v_{\text{comp}}$) to the oldest registered PPX $v_{k_1}$, ran its mappers, stepped upward across $v_{k_1} \to \dots \to v_{k_m}$, and upgraded back to `OCaml_current`.

Four production failure modes drove the deletion of `Migrate_parsetree_driver` in `v2.0.0` (`CHANGES.md:27–33`) and full repository deprecation at `5cb1140405820b9e8c751aada2268d3585b40d25` (`README.md:3–5`):
- **$2(v_{\text{comp}} - v_{\min})$ Full-AST Allocations From One Legacy Dependency:** Linking a single `4.02` PPX into an OCaml `4.12` build forced `10` downgrade copies + `10` upgrade copies (**`20` full-AST heap allocations per file**).
- **Whole-File Partiality Poisoning (`Def.Migration_error`):** Backward migrations $v_{n+1} \to v_n$ raised `exception Migration_error of missing_feature * Location.t` across 22 unrepresentable syntax forms (`src/migrate_parsetree_def.mli:17–42`, e.g., `Pexp_letop` `let*`, `Pcstr_record` inline records, `Pexp_unreachable`). Using `let*` (`4.08+`) anywhere in a file crashed an unrelated `4.07` `[@@deriving show]` plugin on a plain record during the initial `OCaml_current -> v_min` downgrade (`MANUAL.md:324–338`).
- **Unfusible Whole-Tree Traversals:** Rewriters targeting distinct `Ast_4xx` types could not merge context-free rules into a single top-down traversal.
- **Combinatorial Surface Churn:** Maintaining `Outcometree`, `Docstrings`, and `ppx_tools_versioned` across OCaml 5 effect syntax proved unsustainable (`CHANGES.md:4–10`).

Inspecting `ocaml-ppx/ppxlib` at `11a46ff72c2cd8bc02068654950c2573746adff5` shows both what `ppxlib` solved and what remains fragile when a trunk AST is a **lagging compiler snapshot**:
- **Single-Trunk Registration and Fused Context-Free Pass:** `ppxlib` flattens one canonical AST (`Ppxlib_ast.Ast` in `ast/ast.ml:19–120`) bound to **`module Js = Versions.OCaml_502`** (`ast/import.ml:9`). `Driver.Transform.register` (`src/driver.ml:130–223`) accepts no version parameter, and `Transform.merge_into_generic_mappers` (`L234–240`) fuses all `Context_free.Rule.t` extensions and `[@@deriving]` rules into a single `Context_free.map_top_down` pass. Binary AST I/O (`src/utils.ml:183–266`) converts once on ingest (`Convert (Input_version) (Js)`, `L201, 213`) and once on egress (`Convert (Js) (Input_version)`, `L241`).
- **Internal `Astlib` Pairwise Chains Persist (`ast/versions.ml:517–534, 698–723`; `astlib/astlib.ml:25–72`):** `Convert` still chains adjacent pairwise `Astlib.Migrate_408_409`..`Migrate_505_506` modules across 14 versions (`4.08`–`5.06`). On OCaml `5.6`, `ppxlib` still executes **4 downgrade copies** (`506 -> 505 -> 504 -> 503 -> 502`) on input and **4 upgrade copies** on output (**`8` full-AST allocations per file**).
- **22 `"ppxlib.migration.*"` Synthetic Tunnel Encodings (`astlib/encoding_502.ml`–`encoding_506.ml`):** Because `Js = OCaml_502` cannot natively represent OCaml `5.3`–`5.6` syntax (`5.3` `Ppat_effect`; `5.4` labeled tuples and bivariant parameters; `5.5` `Ptyp_functor`, `Pexp_struct_item`, external types; `5.6` `Pexp_hole`/`Pmod_hole`, primitive aliases), `astlib` wraps newer constructs into **22 synthetic extension/attribute tags** (`"ppxlib.migration.ptyp_open_502"` in `encoding_502.ml:2` plus `keep_structure`/`load_path`/`stop_taking` in `migrate_501_500.ml:799` and `migrate_502_501.ml:42, 152`; `"ppxlib.migration.ppat_effect_503"` in `encoding_503.ml:2, 8–26`; 8 tags in `encoding_504.ml:4–15`; 7 tags in `encoding_505.ml:4–10`; 6 tags in `encoding_506.ml:4–9, 58–145`).
- **Three Residual Tunneling Hazards:** (1) If a PPX inspects or rewrites tunneled nodes, `decode_*` aborts with `Error.invalid_encoding` (`astlib/error.ml:15–27`); (2) textual pretty-printing from `Js` leaks `[@@ppxlib.migration.*]` attributes into user code unless scrubbed by `Clean.remove_migration_attributes` (`astlib/clean.ml:1–19`, `src/driver.ml:1162–1165`); and (3) unencodable `5.5`/`5.6` external types and primitive aliases still abort with `Error.migration_error` (`astlib/migrate_505_504.ml:36`, `migrate_505_506.ml:560`).

#### 1.2 LLVM `BitcodeReader` and `AutoUpgrade`: Eager Ingest Canonicalization vs. Conservative Codegen Widening

`Basis: source + derived`

In `llvm/llvm-project` (`2252e5dc213dd1402eb8942de5fa1608b7460d50`), in-memory `llvm::Module`, `llvm::Function`, and `llvm::Instruction` carry **zero version fields**. Compatibility within the bitcode epoch (`LLVM 3.0+`) is enforced eagerly at parse time in `llvm/lib/Bitcode/Reader/BitcodeReader.cpp` and `llvm/lib/IR/AutoUpgrade.cpp` (`llvm/include/llvm/IR/AutoUpgrade.h:41–176`):
- **Hard Epoch Gate (`BitcodeReader.cpp:214–221`):** `readIdentificationBlock` requires `epoch == bitc::BITCODE_CURRENT_EPOCH`, failing closed immediately otherwise while keeping `ProducerIdentification` (`L212, 8936–8948`) purely diagnostic.
- **Typed-to-Opaque Pointer Canonicalization (`BitcodeReader.cpp:2756–2775, 7393–7402`):** Legacy `TYPE_CODE_POINTER` records record their pointee `TypeID` in reader-local side table `ContainedIDs` solely so untyped legacy `load`/`alloca`/`getelementptr` bitcode records can materialize explicit instruction types, while constructing an opaque `PointerType::get(Context, AddressSpace)` in the resulting IR and erasing legacy no-op `bitcast`s between `musttail call` and `ret` (`L7393–7402`).
- **Four-Class Semantic Resolution Taxonomy in `AutoUpgrade.cpp`:**

| Resolution Class | Upstream Mechanism (`llvm/llvm-project@2252e5dc213d`) | Codegen Sound? | Verification Sound? |
| :--- | :--- | :---: | :---: |
| **1. Exact Operational Desugaring** | `UpgradeAttributes` (`AutoUpgrade.cpp:8243–8277`): `"no-frame-pointer-elim"` $\mapsto$ `"frame-pointer"`; `"null-pointer-is-valid"="true"` $\mapsto$ `Attribute::NullPointerIsValid`. `UpgradeTBAANode` (`L6782–6806`): 3-op scalar TBAA $\mapsto$ 4-op struct-path TBAA at offset `0`. | Yes | **Yes** (bisimilar). |
| **2. Conservative Soundness-for-Codegen Widening** | `UpgradeIntrinsicFunction` (`L2413–2420`): maps removed `llvm.strip.invariant.group` to stronger barrier `llvm.launder.invariant.group`. AMDGPU atomic RMW (`L5586–5591`): widens broken scope to `SyncScope("agent")`. `upgradeAliasScopeDomain` (`L6860–6868`): defaults missing disjointness to `false`. `UpgradeFunctionAttributes` (`L7736–7741`): downgrades mismatched callsite `strictfp` to `nobuiltin`. | Yes (inhibits optimization safely) | **Unsound for exact equivalence / hardware-scope specs** unless modeled as explicit non-determinism. |
| **3. Target-Unaware Heuristic Lowering** | `UpgradeBitCastInst` / `UpgradeBitCastExpr` (`L6915–6949`): rewrites cross-address-space pointer `bitcast` into `ptrtoint V to i64` + `inttoptr Temp to DestTy` (*"assume that the maximum pointer size is 64bit"*). | Breaks $>64$-bit / fat pointers | **Unsound** without explicit target data-layout width/provenance check. |
| **4. Non-Operational Drop & Verifier Punt** | `UpgradeDebugInfo` (`L6967–7009`): strips mismatched debug metadata via `StripDebugInfo(M)`; aborts on broken operational IR (`report_fatal_error`, `L6992`). Malformed TBAA (`L6784–6785, 6812–6813`) is left untouched to *"punt to a verifier error"*. | Yes | **Yes** (debug drop preserves operational semantics; verifier punt fails closed). |

#### 1.3 MLIR `BytecodeDialectInterface` and `ConversionTarget`: Decoupling Wire Decoding From Fail-Closed Semantic Legality

`Basis: source + derived`

MLIR (`2252e5dc213dd1402eb8942de5fa1608b7460d50`) splits format evolution from backend capability support into two orthogonal phases:
1. **Per-Dialect Wire Versioning & Post-Parse Upgrade (`mlir/include/mlir/Bytecode/BytecodeImplementation.h:31–68`, `BytecodeDialectInterface.td:17–110`, `mlir/lib/Bytecode/Reader/BytecodeReader.cpp:2216–2226, 2586–2600`):** Alongside the global bytecode version (`getBytecodeVersion()`, `BytecodeImplementation.h:67`), each dialect section optionally encodes a custom `DialectVersion` parsed via `BytecodeDialectInterface::readVersion` (`BytecodeReader.cpp:2216–2225`, failing closed if a versioned dialect omits the interface). Custom `readType`/`readAttribute` readers query `getDialectVersion<D>()`, and after full region parsing—**strictly before `verify(*moduleOp)` (`L2598`)**—the reader runs `interface->upgradeFromVersion(*moduleOp, *loadedVersion)` (`L2586–2595`). Symmetric emission to older targets runs `verifyVersion` (`BytecodeDialectInterface.td:61–81`).
2. **Fail-Closed `ConversionTarget` Semantic Legality (`mlir/include/mlir/Transforms/DialectConversion.h:1079–1108, 1514–1553`, `mlir/lib/Transforms/Utils/DialectConversion.cpp:3316–3350`):** Syntactically valid MLIR is gated per consumer by `ConversionTarget::LegalizationAction`: `Legal`, `Dynamic` (checked per operation instance via `DynamicLegalityCallbackFn = std::function<std::optional<bool>(Operation *)>`, e.g., gating an op on operand types or flags), or `Illegal`. Whereas `applyPartialConversion` leaves uncategorized ops intact (`L3340–3345`), **`applyFullConversion` (`DialectConversion.cpp:3332–3336`) fails closed (`return failure()`) if any operation in the module is unknown or fails legalization**.

#### 1.4 Scala 3 `TASTy`: Three-Component Partial-Order Compatibility Envelopes and Experimental Quarantine

`Basis: normative + source + derived`

Scala 3 (`ff8f3950da9d83b44df246ad32d5882c259a28bb`) replaced Scala 2's $N \times M$ internal-AST compiler-plugin matrix with `TASTy` (`tasty/src/dotty/tools/tasty/TastyFormat.scala` and `TastyHeaderUnpickler.scala`). Every `.tasty` header (`TastyFormat.scala:308–345`, `TastyHeaderUnpickler.scala:96–125`) begins with magic `0x5CA1AB1F`, `majorVersion: Nat` (`28` across Scala `3.0`–`3.8+`; `<= 27` rejected at `L101–108`), `minorVersion: Nat` (`11` at `ff8f3950da9d`), `experimentalVersion: Nat` (`0` on stable releases, `> 0` on pre-release/nightly builds), diagnostic `toolingVersion: Utf8` (`L112–118`), and a 16-byte uncompressed `(Long, Long)` file identifier (`new UUID(readUncompressedLong(), readUncompressedLong())`, `L122`). Unpickling is gated upfront (`L120, 136–148`) by `TastyFormat.isVersionCompatible` (`TastyFormat.scala:381–393`):

```scala
def isVersionCompatible(
  fileMajor: Int, fileMinor: Int, fileExperimental: Int,
  compilerMajor: Int, compilerMinor: Int, compilerExperimental: Int
): Boolean = (
  fileMajor == compilerMajor &&
    (  fileMinor == compilerMinor && fileExperimental == compilerExperimental
    || fileMinor <  compilerMinor && fileExperimental == 0
  )
)
```

This partial order enforces three invariants (`Compatibility.failReason`, `TastyHeaderUnpickler.scala:202–221`): (a) **monotonic minor backward reading** (`fileMinor < compilerMinor && fileExperimental == 0`), (b) **upfront forward-incompatibility rejection** before parsing AST sections (`fileMinor > compilerMinor`), and (c) **strict experimental quarantine** (`fileExperimental > 0` requires exact `(Major, Minor, Experimental)` equality, preventing unstable nightly schemas from polluting stable readers or adjacent nightlies).

#### 1.5 WebAssembly and `wasmparser` vs. SPIR-V: Frozen Container Version and Proposal Bitflags vs. Explicit Preamble Capabilities

`Basis: normative + source`

- **WebAssembly (`WebAssembly/spec` @ `6fca707686ed4f36a1e30ec2ae7d3dd32b276704` & `bytecodealliance/wasm-tools` @ `97a984fd8eb54c055b2516af16489cf4cbf05065`):** The formal spec freezes the 8-byte binary header at `\0asm` (`0x6d736100l`) + **`version = 1l`** (`interpreter/binary/encode.ml:3`, `decode.ml:1260–1266`) across Wasm 1.0, 2.0, and 3.0. Post-MVP proposals (`SIMD`, `TAIL_CALL`, `EXCEPTIONS`, `MEMORY64`, `GC`, `WIDE_ARITHMETIC`, etc.) add section IDs and opcodes gated during single-pass decoding and validation (`interpreter/valid/valid.ml`). Production multi-version consumers such as `wasmparser` represent target support explicitly via **`pub struct WasmFeatures: u64`** (`crates/wasmparser/src/features.rs:139–275`), combining 20+ proposal bitflags with embedder capability subsets (e.g., `FLOATS` at `L211–221` and `GC_TYPES` at `L248–264` to reject float nondeterminism or runtime GC types fail-closed at validation time via `Validator::new_with_features`).
- **SPIR-V (`KhronosGroup/SPIRV-Headers` @ `fb1379425b16e58dcbdda7be0f8604a7f5cdce78` & `SPIRV-Tools` @ `3c8fd35297315682906894621677f1b7003461ef`):** Separates its 5-word header (`magic = 0x07230203`, container `version` `1.0`..`1.6` at `word[1]`, diagnostic `generator` tool ID at `word[2]`, SSA `bound` at `word[3]`, `schema = 0` at `word[4]` in `source/binary.cpp:48–62`) from **two-sided preamble `OpCapability` validation** (`source/val/validate_capability.cpp:355–471`, `validate_instruction.cpp:136–160`). Using an instruction without declaring its required `OpCapability` fails (`CheckRequiredCapabilities`), and declaring an `OpCapability` unsupported by the consumer's target environment (`SPV_ENV_VULKAN_1_0`..`1_4`) fails upfront at preamble inspection—allowing $O(1)$ header-level capability auditing without scanning every instruction body.

#### 1.6 Charon ULLBC/LLBC `CrateData` and Frama-C `Machdep`: Exact-Equality Schema Locks vs. Explicit Target/Dialect Parameterization

`Basis: source + documentation`

- **Charon (`AeneasVerif/charon` @ `b23c297f57c0b2072de7967c7f17088db0278a8c`, `v0.1.324`, pinned to `nightly-2026-09-17`):** Serializes both unstructured (`ullbc_ast`) and structured (`llbc_ast`) crates through `CrateData { charon_version: CharonVersion, translated: TranslatedCrate, has_errors: bool }` (`charon/src/export.rs:18–29`, `charon/src/lib.rs:20–23, 68–86`). Both the Rust deserializer (`export.rs:45–63`) and the OCaml `charon-ml` deserializer consumed by Aeneas (`charon-ml/src/CharonVersion.ml:3`, `charon-ml/src/OfJson.ml:21–54`) enforce **strict string equality** (`version == "0.1.324"`), rejecting any version skew immediately while carrying `target_information` and `runtime_checks` inside `TranslatedCrate` (`OfJson.ml:42–43`). This guarantees fail-closed schema safety across the Rust-to-OCaml serialization boundary, but binds each `charon` binary to a single `rust-toolchain` pin (`nightly-2026-09-17`).
- **Frama-C (`189053d4a2bd460c5c557dba8569474ff0419e73`):** Rather than duplicating CIL ASTs or WP proof engines across C compilers, Frama-C parameterizes one AST and verification engine over `Machdep.mach` (`src/kernel/internals/runtime/machdep.mli:17–98`, validated against `share/machdeps/machdep-schema.yaml`), a **53-field YAML capability record** partitioning scalar/pointer `sizeof_*` (`10` `int` fields), standard typedefs (`18` `string` fields), separate C11 `alignof_*` vs. GCC `gcc_alignof_*` tables (`25` `int` fields), endianness/char-signedness booleans, `compiler` dialect (`"gcc" | "msvc" | "generic"`), and dialect-conditional builtins (`share/machdeps/compiler_builtins.json:4–35`).

#### 1.7 Summary Comparison Across Examined Multi-Version Ecosystems

`Basis: derived (from §§1.1–1.6)`

| System | Canonical In-Memory IR | Multi-Producer Lowering Topology | Wire Version Rule | Semantic / Target Capability Gate |
| :--- | :--- | :--- | :--- | :--- |
| **`OMP` v1 (`v1.8.0`)** | None ($K$ ASTs `4.02`..`4.12`) | Bidirectional pairwise `migration_compose` chain | Exact OCaml AST magic per step | Partial downgrade raises `Def.Migration_error` |
| **`ppxlib` (`11a46ff7`)** | Lagging snapshot (`OCaml_502`) | Pairwise `Astlib.Migrate_<n>_<n+1>` + 22 `"ppxlib.migration.*"` tunnels | OCaml AST magic (`4.08`..`5.06`) | `Error.invalid_encoding` / `migration_error` |
| **LLVM (`2252e5dc`)** | Unversioned latest `llvm::Module` | Direct 1-pass `BitcodeReader` + `AutoUpgrade` | Hard `BITCODE_CURRENT_EPOCH` gate | Codegen-sound widening + `verifyModule` |
| **MLIR (`2252e5dc`)** | Unversioned current Dialect ops | `readVersion` + post-parse `upgradeFromVersion` | Global version + `DialectVersion` | `ConversionTarget` + fail-closed `applyFullConversion` |
| **Scala 3 `TASTy`** | Compiler typed tree | Monotonic tag reader over `28.0`..`28.11` | `isVersionCompatible(M, m, e)` | Upfront header gate + experimental quarantine |
| **Wasm / `wasmparser`** | Single Wasm AST | Direct 1-pass binary decode | Frozen `version == 1` | `WasmFeatures: u64` proposal/capability bitflags |
| **SPIR-V (`1.6.rev7`)** | Unified1 instruction stream | Direct 1-pass word stream parse | `1.0 <= word[1] <= 1.6` | Two-sided preamble `OpCapability` check |
| **Charon (`0.1.324`)** | `TranslatedCrate` (ULLBC/LLBC) | Single pinned `nightly-2026-09-17` driver | Exact equality (`v == "0.1.324"`) | `target_information` + `runtime_checks` + `has_errors` |
| **Frama-C (`189053d4`)** | Single CIL AST | Direct C frontend parameterized by `mach` | YAML schema (`machdep-schema.yaml`) | 53-field `Machdep.mach` + `compiler_builtins.json` |

---

### 2. Structural and Quantitative Evaluation of Five Multi-Compiler IR Topologies (`T1`–`T5`) Against Real `rustc` History

#### 2.1 Nine Verified `rustc_middle::mir::syntax` Schema Mutations and Non-Linear Release/Nightly DAG Divergence

`Basis: source + execution (support/probe_ir_migration_topologies.py, support/probe_ir_migration_topologies_results.json)`

Across eight chronological `rust-lang/rust` pins (`1.93.1` `01f6ddf7` on `2026-02-11` through `1.102.0-nightly` `3ef0c22c` on `2026-11-11`) plus the out-of-band `2026-10-20` nightly pin `8144389c895da997dbdecaa635e41d6a50be6ffd`, `compiler/rustc_middle/src/mir/syntax.rs` undergoes **nine structural enum changes** (`10` atomic variant/field edits across `Rvalue`, `Operand`, `StatementKind`, `AssertKind`, `CastKind`, `ProjectionElem`, and `TerminatorKind`):

| ID | Transition | Causal `rust-lang/rust` Commit (PR) | Structural `syntax.rs` Change | Mutation Kind & Live Impact (`782` Bodies) |
| :--- | :--- | :--- | :--- | :--- |
| `M1` | `1.93.1 -> 1.94.0` | `1a227bd47ff200975f4afb287ec725861ab8b87a` (`#148766`) | `- Rvalue::NullaryOp(NullOp)` | **Operational variant removed** (`0` live bodies) |
| `M2` | `1.93.1 -> 1.94.0` | `6319bee585561a078de4a0f8d07d567ce69cf12c` (`#148766`) | `+ Operand::RuntimeChecks(RuntimeChecks)` | **Operational variant added** (`0` live bodies) |
| `M3` | `1.94.0 -> 1.96.0` | `6d4b1b38e76c0858c8e98f89afa37535261749ca` (`#152758`) | `- Rvalue::ShallowInitBox(Operand, Ty)` | **Operational variant removed** (`0` live bodies) |
| `M4` | `1.96.0 -> 1.98-nightly` | `e402c1edf047a23b0cfef40c6097d1caa294050b` (`#154341`) | `- StatementKind::Retag(RetagKind, Box<Place>)` | **Operational variant removed** (`0` default bodies; active under `-Zmir-emit-retag`) |
| `M5` | `1.96.0 -> 1.98-nightly` | `e402c1edf047a23b0cfef40c6097d1caa294050b` (`#154341`) | `Rvalue::Use(Operand)` $\to$ `Rvalue::Use(Operand, WithRetag)` | **Operational payload widened** (**`126 / 782` bodies**: `124` `memchr` + `2` `feature_probe`) |
| `M6` | `1.96.0 -> 1.98-nightly` | `2d88ee87ddaa584a19e438528f60f825f735076a` (`#156290`) | `+ Rvalue::Reborrow(Ty, Mutability, Place)` | **Operational variant added** (`0` live bodies) |
| `M7` | `1.98-nightly -> 1.99.0` | `1a982425b6699f2b26552c6b44cc979a3d84543b` (`#158796`) | `+ AssertKind::NullReferenceConstructed` | **Operational variant added** (`0` live bodies) |
| `M8` | `1.98-nightly -> 1.99.0` | `fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f` (`#160339`) | `+ CastKind::BoxDerefTransmute` | **Operational variant added** (**`5 / 641` `memchr` bodies**) |
| `M9a` | `1.99.1 -> 1.100.0` | `5686e563774cd9e8bfba79d3ab1167fe198e9e78` (`#159103`) | `+ ProjectionElem::PhantomDeref` | **Operational variant added** (`0` live bodies) |
| `M9b` | `1.100.0 -> 1.102-nightly` (and `8144389c`) | `ec45ecffeee8ba13e42a7f45b6cdad3155ebd146` (`#163931`) | `TerminatorKind::Goto { target }` $\to$ `Goto { target, loop_hint_attrs }` | **Non-operational hint field added** (`0` live bodies) |

**Non-Linear Release/Nightly DAG Witness (`8144389c` vs. `1.100.0`):** Ordering pins by calendar date places `8144389c` (`2026-10-20` nightly) *before* `1.100.0` (`0ef1bc38`, released `2026-11-09`). Because `1.100.0` branched to `beta` before `ec45ecff` landed on `2026-10-07`, `8144389c` already carries `Goto { target, loop_hint_attrs }`, `1.100.0` reverts to `Goto { target }`, and `1.102.0-nightly` (`3ef0c22c`, `2026-11-11`) carries `Goto { target, loop_hint_attrs }` again. Real compiler pins form a **branch/cherry-pick DAG**, never a monotone calendar chain.

#### 2.2 Five-Topology Scaling, Allocation, Lossiness, and TCB Maintenance Matrix

`Basis: execution (support/probe_ir_migration_topologies.py -> support/probe_ir_migration_topologies_results.json) + derived`

`support/probe_ir_migration_topologies.py` evaluates all five topologies (`T1`–`T5`) across the 9 compiler pins (`782` baseline bodies/pin) and 11 MIR specimens (`S1`–`S11`) covering every mutation class above:

| Dimension | `T1`: Latest Raw Canonical IR (`1.102-nightly`) | `T2`: Oldest (`1.93.1`) / 9-Pin Intersection IR | `T3`: Pairwise Stepwise `Migrate_k_{k+1}` Chains (`T3a` / `T3b` / `T3c` `1.98` Hub) | `T4`: Direct Per-Spoke Lowering to Monotonic `SemProfile` Superset Trunk | `T5`: Separate Per-Version IRs, Semantics & Proof Engines |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **Canonical Evaluator & WP Proof Engines** | `1` (churns on every compiler bump) | `1` (frozen at legacy subset) | `1` | **`1` (monotonic; existing WP proofs invariant)** | **`9` stacks** (`7` if syntax-deduped; $O(N)$ TCB) |
| **Frontend Spoke / Migration Modules** | `8` (`7` classes) | `8` (`7` classes) | `7` (`T3a`/`T3c` unidir) or `14` (`T3b`/`T3c` bidir) | **`7` `syntax.rs` equivalence classes across all 9 pins** | `9` (`7` syntax-deduped) |
| **AST-to-AST Copy Hops per Body** | `0` | `0` | `0–7` (`T3a`, mean `3.5`); up to `14` (`T3b`); `0–4` / `0–8` (`T3c`) | **`0` intermediate AST copies** (`1` `TyCtxt -> TrunkIR` pass) | `0` |
| **Extra Body Allocations (`8` Pins $\times$ `782` Bodies)** | `0` | `0` | **`21,896`** (`T3a`) / **`10,948` per crate** (`T3b`) / **`12,512`–`25,024`** (`T3c`) | **`0`** | `0` |
| **Specimens Failing 1:1 / Soundness / Tunneling (`11` Total)** | **`2 / 11` fail** (`S3` `Stmt::Retag`, `S5` `ShallowInitBox`) | **`6 / 11` fail** (`0` variants in strict 9-pin intersection!) | **`2 / 11`** (`T3a`), **`9 / 11`** (`T3b`), **`4 / 11` unidir / `5 / 11` bidir** (`T3c`) | **`0 / 11` lossy** (`2` admitted in scalar v1; `9` fail-closed `CAP_*`; `11` admitted under full caps) | `0 / 11` |
| **Live `memchr 2.8.3` Bodies Broken/Tunneled (`1.99.0+`)** | `0` | **`124` (`WithRetag::No`) + `5` (`BoxDerefTransmute`)** | `0` (`T3a`) / `124` (`T3b`) / **`5 / 641` (`T3c` `BoxDerefTransmute`)** | **`0` crash** (clean `CAP_*` / `.unsupported` lowering) | `0` |
| **Handles Non-Linear Release/Beta DAG (`8144389c` vs. `1.100.0`)?** | **No** (hub oscillates) | **No** | **No** (`loop_hint_attrs` oscillation) | **Yes** (`8144389c` == `1.102-nightly` spoke class) | **Yes** |
| **Zero-Edit Proof Reuse Across Equivalent Pins?** | Broken on hub bump | Partial (legacy subset only) | Yes (where representable) | **Yes** (identical `(TrunkBody, SemProfile)` reuses proof) | **No** (separate `MirAst_v` types) |

#### 2.3 Failure Mechanics of `T1`, `T2`, `T3`, and `T5` vs. Direct Spoke-to-Superset-Trunk Lowering (`T4`)

`Basis: source + execution + derived`

1. **Why `T1` (Raw Latest `syntax.rs`) Fails 1:1 Emission and Destabilizes Proofs:**
   Compiler MIR evolution is not monotonic. Commit `6d4b1b38e76c` (`1.94.0 -> 1.96.0`) deleted `Rvalue::ShallowInitBox(Operand, Ty)` (`S5`), and commit `e402c1edf047` (`1.96.0 -> 1.98.0-nightly`) deleted `StatementKind::Retag(RetagKind, Box<Place>)` (`S3`), moving function-entry retags out of `StatementKind` and fusing assignment retags into `Rvalue::Use(Operand, WithRetag)`. Consequently, `1.102.0-nightly`'s raw `syntax.rs` **has no 1:1 representation for `1.96.0`'s `StatementKind::Retag(FnEntry, _1)`**: dropping it silently erases Stacked/Tree Borrows aliasing checks (unsound), while synthesizing `_tmp = Use(Copy(_1), WithRetag::Yes)` mutates `LocalDecls` and frame indices. Moreover, making raw `v_latest` the verification AST forces rewriting `MirSemantics` and existing weakest-precondition theorems on every destructive `rustc` refactor, and oscillates whenever a stable point release (`1.100.0`) ships after an ahead-of-branch nightly (`8144389c`).

2. **Why `T2` (Oldest / Intersection IR) Collapses Coverage or Soundness:**
   Across all 9 pins, the strict syntactic intersection over mutating MIR variants is **empty (`[]`)** because `Rvalue::Use` widened in `1.98-nightly` and `TerminatorKind::Goto` widened in `1.102-nightly`. Even pinning to `1.93.1`'s AST rejects or misrepresents **`6 / 11` specimens**: collapsing `Rvalue::Use(op, WithRetag::Yes)` (`S8`) into `1.93.1`'s non-retagging `Rvalue::Use(op)` silently drops reference retags (unsound), while `CastKind::BoxDerefTransmute` (`S9`) rejects `5 / 641` live `memchr` bodies on every `1.99.0+` toolchain.

3. **Why `T3` (Pairwise Stepwise `Migrate_k_{k+1}` Chains) Wastes $O(N)$ Allocations and Inherits Tunnel Bugs:**
   Even after `TyCtxt` extraction, `T3a` allocates up to `7` full-body copies (`21,896` extra body allocations across the 8 pins) without solving `T1`'s deleted-variant wall. Choosing an intermediate lagging snapshot hub (`T3c`, e.g., `joshlf/anneal@c131b320eeeb`'s `driver.rs` pin `1.98.0-nightly` `f8a08b688cbe`) reproduces `ppxlib`'s exact dilemma: older pins (`<= 1.96.0`) cannot represent deleted `StatementKind::Retag` or `ShallowInitBox`, while newer pins (`1.99.0`–`1.102.0-nightly`) cannot represent `CastKind::BoxDerefTransmute`, `AssertKind::NullReferenceConstructed`, or `ProjectionElem::PhantomDeref` without either failing (`5 / 641` `memchr` bodies) or inventing synthetic tunnel wrappers that break downstream semantic inspection.

4. **Why `T5` (Separate Per-Version IRs and Evaluators) Multiplies the TCB $O(N)$:**
   Giving each compiler pin its own `MirAst_v`, `MirSemantics_v`, weakest-precondition calculus `WP_v`, and Rust Reference / MiniRust correspondence proof multiplies the verified TCB **`9x` across 9 pins** (`7x` even if `1.99.0 == 1.99.1` and `8144389c == 1.102.0-nightly` share ASTs) and forces re-proving unchanged user functions (`ryu` has `0.00%` normalized MIR drift across all 9 months!) whenever the compiler pin advances.

5. **Why `T4` (1-Pass Per-Spoke Lowering to a Monotonic `SemProfile`-Parameterized Superset Trunk) Dominates:**
   Because verification is **unidirectional** (`rustc` `TyCtxt` $\to$ verifier Trunk IR, never round-tripping MIR back into `rustc`), each compiler pin lowers directly from its native `rustc_middle::mir::Body` into a **monotonic semantic superset Trunk IR** in **1 pass**:
   - **Zero lossiness on both historical deletions and newer additions:** The Trunk IR retains `TrunkStmt::Retag(kind, place)` (emitted by `<= 1.96.0` spokes) *alongside* `TrunkRvalue::Use(op, with_retag: Bool)` (mapping `<= 1.96.0` `Use(op)` to `with_retag = false` and `1.98+` `Use(op, wr)` to `wr == Yes`), sharing one underlying `retagPlace` semantic helper in `MirSemantics`.
   - **Safe erasure of strictly non-operational hints:** `TerminatorKind::Goto { target, loop_hint_attrs }` (`S11`) lowers directly to `TrunkTerm::Goto(target)`, collapsing `1.100.0`, `8144389c`, and `1.102.0-nightly` to identical Trunk CFGs.
   - **Equivalence-class deduplication and DAG independence:** All 9 pins collapse into **7 `syntax.rs` spoke classes**, and adding an out-of-order release branch never affects any other spoke.
   - **Two-tier fail-closed `.unsupported(CAP_*)` legality:** Unmodeled constructs lower to typed `.unsupported(CAP_*)` nodes rather than crashing crate-wide capture, allowing pure scalar/CFG functions (`S1`, `S11`) in the same crate to verify under `CAP_CORE_SCALAR_CFG` while deterministically rejecting any reachable execution or proof obligation touching an unenabled capability (`9 / 11` specimens under minimal scalar v1; `11 / 11` admitted once corresponding `CAP_*` capabilities are enabled).

#### 2.4 Orthogonal Three-Axis Artifact Header Contract and Epoch-Bounded Superset Pruning

`Basis: derived (synthesizing TASTy, MLIR, SPIR-V, Charon, and Frama-C)`

To prevent conflating serialization format changes, compiler binary identity, and operational semantics, captured Trunk IR artifacts should carry three strictly orthogonal header records:

1. **`schema_version: { major: u32, minor: u32 }` (TASTy / MLIR Wire Contract):** Increments `minor` monotonically when new Trunk IR variants are added; readers enforce `file.major == reader.major && file.minor <= reader.minor`. When the minimum supported `rustc` window advances past an older era (e.g., dropping `<= 1.96.0` so no active spoke emits `TrunkStmt::Retag` or `ShallowInitBox`), incrementing `major` cleanly prunes retired legacy variants at explicit epoch boundaries (matching LLVM's `BITCODE_CURRENT_EPOCH`).
2. **`producer_provenance: { rustc_commit: [u8; 20], driver_sha256: [u8; 32], sysroot_sha256: [u8; 32] }` (TCB Receipt Provenance):** Checked exclusively by the trust-boundary auditor (`PinnedVerified` vs. unverified compiler receipts) and **never read by `MirSemantics`**, so bit-identical Trunk IR bodies emitted by `1.99.0` and `1.99.1` reuse proofs with zero semantic branching.
3. **`sem_profile: { target_layout, runtime_checks_mode, aliasing_model, required_capabilities: BitSet<Cap> }` (Frama-C `Machdep` + SPIR-V `OpCapability` + MLIR `ConversionTarget`):** Parameterizes `MirSemantics` over target ABI and `-C ub-checks` / `-C overflow-checks` session modes (`S4`, `S6`) and checks `required_capabilities ⊆ verifier_supported_capabilities` in $O(1)$ before proof checking.

---

### 3. Edition-Independence Proof for `rustc` `Runtime(PostCleanup)` MIR vs. Per-Span Frontend Hygiene in `rustc` and `rust-analyzer`

#### 3.1 Per-Token `SyntaxContext` Edition Hygiene in `rustc` and `EditionedFileId` / `SyntaxContextData` in `rust-analyzer`

`Basis: source`

Rust permits a crate compiled under Edition $E_2$ to expand declarative or procedural macros defined in dependency crates compiled under Edition $E_1 \neq E_2$, and links crates across all four stable editions (`Edition2015`, `Edition2018`, `Edition2021`, `Edition2024`) plus `EditionFuture` (`compiler/rustc_span/src/edition.rs:9–37` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`). Both Rust frontends confine edition state strictly to span hygiene:
- **`rustc` (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`):** Root `SyntaxContext` (`index 0`) initializes `ExpnData::default(ExpnKind::Root, DUMMY_SP, edition, ...)` from `--edition` (`compiler/rustc_span/src/hygiene.rs:526–533`). Every macro expansion pushes an `ExpnData` carrying `pub edition: Edition` (*"Edition of the crate in which the macro is defined"*, `hygiene.rs:1159–1160`), queried per token via `span.edition()` (`SyntaxContext::edition`, `hygiene.rs:1064–1066`).
- **`rust-analyzer` (`rust-lang/rust-analyzer@37721d141370e0904033f7fc3a3abe11c446c4c1`):** Encodes file-level edition into `SpanAnchor.file_id: EditionedFileId` (`crates/span/src/lib.rs:79–88, 122–138`) and macro-hygiene edition into interned `SyntaxContextData { outer_expn, outer_transparency, edition: Edition, ... }` (`crates/span/src/hygiene.rs:38–46, 69`). Once lowered to `rust-analyzer`'s internal MIR (`crates/hir-ty/src/mir.rs`), **`Edition` appears `0` times across the entire module**.

#### 3.2 Complete Pre-MIR or Pre-`PostCleanup` Desugaring Across Editions 2015, 2018, 2021, and 2024

`Basis: source`

Every edition-gated Rust language feature in `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` resolves completely into edition-free types, places, and CFG edges before `MirPhase::Runtime(RuntimePhase::PostCleanup)`:

1. **`async` (`Edition2018+`) and `gen` (`Edition2024+`) Blocks (`compiler/rustc_ast_lowering/src/expr.rs:402–408, 865–875`):** Desugared during AST $\to$ HIR lowering via `make_desugared_coroutine_expr` into HIR coroutine closures, which `StateTransform` lowers into ordinary enum state-machine `SwitchInt` / `Aggregate` MIR before `Runtime(PostCleanup)`.
2. **RFC 2229 Disjoint Closure Field Captures (`Edition2021+`, `compiler/rustc_hir_typeck/src/upvar.rs:153–157, 469–474, 2749–2755`):** `enable_precise_capture(span)` checks `span.at_least_rust_2021()` (`L2751–2755`, explicitly honoring macro hygiene). When `< Edition2021`, `origin.1.projections.clear()` truncates captured places to the root variable during HIR typeck (`L154–156, 470–473`); MIR construction receives finalized `Place` projections in `closure_captures` regardless of edition.
3. **Diverging `!` Type Inference Fallback (`Edition2024+`, `compiler/rustc_hir_typeck/src/fallback.rs:55–95, 352–357`):** Unconstrained diverging type variables resolve during HIR type inference to `()` (`<= Edition2021`) or `tcx.types.never` (`!` in `Edition2024+`, `L88–94`), producing concrete `LocalDecl.ty` entries before THIR/MIR construction begins.
4. **Block Tail-Expression and `if let` Temporary Drop-Scope Narrowing (`Edition2024+`, RFC 3606, `compiler/rustc_hir_analysis/src/check/region.rs:146–152, 353–375`):** Region scope tree construction queries `blk.span.edition().at_least_rust_2024()` (`L147–148`) for tail expressions and selects `ScopeData::IfThenRescope` vs. `ScopeData::IfThen` (`L355–359, 370–374`) for `if let`. THIR $\to$ MIR building (`rustc_mir_build`) materializes those scopes directly as explicit `StorageDead` and `TerminatorKind::Drop` placements in the MIR CFG.

#### 3.3 Exhaustive Audit of `Edition` References in `rustc_middle::mir` and Unconditional Erasure in `CleanupPostBorrowck`

`Basis: source`

Exhaustive inspection of `compiler/rustc_middle/src/mir/mod.rs` and `compiler/rustc_middle/src/mir/syntax.rs` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` establishes that `mir::Body` has **zero `Edition` fields** and **zero operational `Edition` branches**. Only two MIR declarations mention editions or rescoping anywhere in `rustc_middle::mir`:

1. `LocalInfo::IfThenRescopeTemp { if_then: HirId }` (`compiler/rustc_middle/src/mir/mod.rs:1089–1091`), a diagnostic `LocalDecl` annotation with zero operational effect; and
2. `StatementKind::BackwardIncompatibleDropHint { place: Box<Place<'tcx>>, reason: BackwardIncompatibleDropReason::Edition2024 }` (`compiler/rustc_middle/src/mir/syntax.rs:447–457, 977–979`), emitted for migration linting during MIR build (`compiler/rustc_mir_build/src/builder/scope.rs:432–440, 1174–1182, 1922–1930`) and documented verbatim (`mir/syntax.rs:447–451`) as:

```rust
/// Marker statement indicating where `place` would be dropped.
/// This is semantically equivalent to `Nop`, so codegen and MIRI should interpret this
/// statement as such.
/// The only use case of this statement is for linting in MIR to detect temporary lifetime
/// changes.
```

During the transition from analysis MIR to runtime MIR, `CleanupPostBorrowck` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:33–38`) **unconditionally overwrites every `BackwardIncompatibleDropHint` with `StatementKind::Nop`** (`statement.make_nop(true)`):

```rust
StatementKind::AscribeUserType(..)
| StatementKind::FakeRead(..)
| StatementKind::BackwardIncompatibleDropHint { .. } => {
    statement.make_nop(true);
}
```

Consequently, at `MirPhase::Runtime(RuntimePhase::PostCleanup)`, all Rust editions (`2015`, `2018`, `2021`, `2024`, and mixed-edition macro expansions) inhabit a **100% edition-independent operational MIR**. Neither Trunk IR syntax nor `SemProfile` requires an `Edition` parameter.

## Boundaries

1. **`ppxlib` Post-`2026-11-02` Internal `Astlib` Refactoring (`not examined`):** At `ocaml-ppx/ppxlib@11a46ff72c2cd8bc02068654950c2573746adff5`, `ast/versions.ml` still composes pairwise `Astlib.Migrate_<n>_<n+1>` hops (`4.08`..`5.06`) into `Js = OCaml_502`. Whether subsequent upstream commits replace `astlib`'s internal chain with generated direct-to-trunk spoke mappers is `not examined`.
2. **Cross-Epoch LLVM Bitcode and Cross-Major Scala 3 `TASTy` Migration (`unsupported` / `known not to apply`):** LLVM `BitcodeReader` (`2252e5dc213d`) rejects `epoch != BITCODE_CURRENT_EPOCH` (`BitcodeReader.cpp:214–221`), and Scala 3 `TastyFormat.isVersionCompatible` (`ff8f3950da9d`, `TastyFormat.scala:381–393`) returns `false` whenever `fileMajor != compilerMajor` (`fileMajor <= 27` throws `UnpickleException`). In-epoch `AutoUpgrade` and minor-version `TASTy` backward compatibility are `known not to apply` across major epoch resets.
3. **Stdlib Type, Layout, and Macro-Codegen Drift Within a Single `syntax.rs` Equivalence Class (`known not to apply`):** Collapsing the 9 examined `rustc` pins into 7 `rustc_middle::mir::syntax` equivalence classes characterizes **MIR AST grammar** only. It is `known not to apply` as a sufficient condition for bit-identical `TyCtxt` output across releases: stdlib internal refactors (`AtomicU* -> Atomic<T>`, `Infallible = !`, `Box<T>.0: Unique<T> -> BoxRaw<T>`, and `#[derive(Debug)]` string concatenation, quantified in `rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility`) mutate types and bodies inside the same `syntax.rs` class unless callee contracts are verified modularly or normalized at the spoke boundary.
4. **Unstable `EditionFuture` Post-`2026-11-22` MIR Constructs (`unknown`):** Edition independence of `Runtime(PostCleanup)` MIR is established for `Edition2015` through `Edition2024` and `EditionFuture` as implemented at `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`; whether future unstable edition proposals introduce post-cleanup MIR markers not erased by `CleanupPostBorrowck` is `unknown` without re-running the revalidation check below.
5. **Single-Crate Conditional Compilation (`#[cfg]`) vs. Separate Per-Spoke Rust Crates for `T4` Emitters (`not examined` in empirical build benchmarks here):** While `T4` establishes that 9 `rustc` pins require only 7 syntactic spoke mappings (`1` pass each, `0` intermediate copies), compile-time and binary-packaging trade-offs between compiling one shared Rust emitter crate with `#[cfg(...)]` adapters vs. separate per-pin driver crates belong to host-driver engineering and are `not examined` in `support/probe_ir_migration_topologies.py`.

## Evidence

### Primary Upstream Sources Audited (`2026-11-22`)

- **`ocaml-ppx/ocaml-migrate-parsetree`:**
  - `1d72648812bb235d1576f483cacdf546e25c03d8` (`v1.8.0`): `src/migrate_parsetree_versions.ml:20–29, 145–202, 356–379, 440–460, 522–606, 745–764` (GADT witnesses, mutable `migration_info`, `migration_compose`); `src/migrate_parsetree_driver.ml:126–170, 229–301` (`rewriter_group` sorting, `rewrite_structure` ping-pong); `src/migrate_parsetree_def.mli:17–42` (`Migration_error` missing-feature enum); `MANUAL.md:33, 182–229, 324–338`.
  - `5cb1140405820b9e8c751aada2268d3585b40d25` (post-`v2.4.0` `HEAD`): `README.md:3–5`, `CHANGES.md:4–10, 27–33` (`v2.0.0` driver removal and OCaml 5 deprecation).
- **`ocaml-ppx/ppxlib` @ `11a46ff72c2cd8bc02068654950c2573746adff5`:** `ast/import.ml:9` (`module Js = Versions.OCaml_502`); `ast/ast.ml:19–120`; `ast/versions.ml:517–534, 698–723` (`Convert` over pairwise `Astlib` chain); `astlib/astlib.ml:25–72` (`Ast_408`..`Ast_506`); `astlib/encoding_502.ml:2`, `encoding_503.ml:2, 8–26`, `encoding_504.ml:4–15`, `encoding_505.ml:4–10`, `encoding_506.ml:4–9, 58–145`, `migrate_501_500.ml:799`, `migrate_502_501.ml:42, 152` (22 `"ppxlib.migration.*"` tunnel tags); `astlib/clean.ml:1–19`; `astlib/error.ml:3–27`; `astlib/migrate_505_504.ml:36`, `migrate_505_506.ml:560`; `src/driver.ml:130–240, 1162–1165`; `src/utils.ml:183–266`.
- **`llvm/llvm-project` @ `2252e5dc213dd1402eb8942de5fa1608b7460d50`:**
  - LLVM: `llvm/include/llvm/IR/AutoUpgrade.h:41–176`; `llvm/lib/Bitcode/Reader/BitcodeReader.cpp:212–221, 2632, 2756–2775, 4103–4122, 4899–4905, 7097–7099, 7386–7407, 7445–7467, 8936–8948`; `llvm/lib/IR/AutoUpgrade.cpp:2413–2420, 5586–5591, 6782–6813, 6860–6868, 6915–6949, 6967–7009, 7736–7741, 8243–8277`.
  - MLIR: `mlir/include/mlir/Bytecode/BytecodeImplementation.h:31–68`; `mlir/include/mlir/Bytecode/BytecodeDialectInterface.td:17–110`; `mlir/lib/Bytecode/Reader/BytecodeReader.cpp:2216–2226, 2586–2600`; `mlir/include/mlir/Transforms/DialectConversion.h:1079–1108, 1514–1553`; `mlir/lib/Transforms/Utils/DialectConversion.cpp:3316–3350`.
- **`scala/scala3` @ `ff8f3950da9d83b44df246ad32d5882c259a28bb`:** `tasty/src/dotty/tools/tasty/TastyFormat.scala:24–28, 308–393` (`header`, `MajorVersion = 28`, `MinorVersion = 11`, `ExperimentalVersion = 1`, `isVersionCompatible`); `tasty/src/dotty/tools/tasty/TastyHeaderUnpickler.scala:22–28, 96–196, 202–221`.
- **`WebAssembly/spec` @ `6fca707686ed4f36a1e30ec2ae7d3dd32b276704` & `bytecodealliance/wasm-tools` @ `97a984fd8eb54c055b2516af16489cf4cbf05065`:** `interpreter/binary/encode.ml:3`, `interpreter/binary/decode.ml:1260–1330`, `interpreter/valid/valid.ml`; `crates/wasmparser/src/features.rs:1–35, 139–275` (`WasmFeatures: u64`).
- **`KhronosGroup/SPIRV-Headers` @ `fb1379425b16e58dcbdda7be0f8604a7f5cdce78` & `KhronosGroup/SPIRV-Tools` @ `3c8fd35297315682906894621677f1b7003461ef`:** `include/spirv/unified1/spirv.hpp11:40–47`; `source/binary.cpp:48–62`; `source/val/validate_capability.cpp:30–471`; `source/val/validate_instruction.cpp:136–160`.
- **`AeneasVerif/charon` @ `b23c297f57c0b2072de7967c7f17088db0278a8c`:** `rust-toolchain` (`nightly-2026-09-17`); `charon/Cargo.toml:27–30` (`version = "0.1.324"`); `charon/src/lib.rs:1–24, 68–86`; `charon/src/export.rs:16–63` (`CrateData`, `CharonVersion` exact-equality `Deserialize`); `charon-ml/src/CharonVersion.ml:1–3`; `charon-ml/src/OfJson.ml:21–54` (`crate_of_json`).
- **`Frama-C` (`https://git.frama-c.com/pub/frama-c.git`) @ `189053d4a2bd460c5c557dba8569474ff0419e73`:** `src/kernel/internals/runtime/machdep.mli:17–114` (`Machdep.mach` 53-field record); `share/machdeps/machdep-schema.yaml:1–497`; `share/machdeps/machdep_x86_64.yaml:18–350`; `share/machdeps/compiler_builtins.json:4–35`.
- **`rust-lang/rust-analyzer` @ `37721d141370e0904033f7fc3a3abe11c446c4c1`:** `crates/span/src/lib.rs:79–88, 122–138` (`Span`, `SpanAnchor`, `EditionedFileId`); `crates/span/src/hygiene.rs:38–46, 65–94` (`SyntaxContextData.edition`); `crates/hir-ty/src/mir.rs:1–80` (`0` occurrences of `Edition` across entire file).
- **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` & MIR Schema Pins:**
  - Edition hygiene & erasure at `342d74463af7`: `compiler/rustc_span/src/edition.rs:9–37`; `compiler/rustc_span/src/hygiene.rs:526–533, 1064–1066, 1159–1160`; `compiler/rustc_ast_lowering/src/lib.rs:1056`, `expr.rs:402–408, 865–875`; `compiler/rustc_hir_typeck/src/upvar.rs:153–157, 469–474, 2749–2755`; `compiler/rustc_hir_typeck/src/fallback.rs:55–95, 352–357`; `compiler/rustc_hir_analysis/src/check/region.rs:146–152, 353–375`; `compiler/rustc_mir_build/src/builder/scope.rs:432–440, 1174–1182, 1922–1930`; `compiler/rustc_middle/src/mir/mod.rs:1089–1091`; `compiler/rustc_middle/src/mir/syntax.rs:447–457, 977–979`; `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:33–38`.
  - Nine `compiler/rustc_middle/src/mir/syntax.rs` pins (`2026-11-20` / `2026-11-22`): `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf` (`1.93.1`), `4a4ef493e3a1488c6e321570238084b38948f6db` (`1.94.0`), `ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96` (`1.96.0`), `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`), `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (`1.99.0`), `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`), `8144389c895da997dbdecaa635e41d6a50be6ffd` (`1.101.0-nightly`), `0ef1bc386059596dada8fb65b50425aab2ea637a` (`1.100.0`), and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`), plus causal commits listed in §2.1.
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** `trusted/rustc-capture/src/driver.rs:25` (`1.98.0-nightly (f8a08b688 2026-05-30)` pin) and `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` (`8144389c` pin and `.unsupported` sentinels).

### Preserved Package Support Material

- `support/probe_ir_migration_topologies.py`: Self-contained Python 3.10+ standard-library probe encoding all 9 `rust-lang/rust` pins, all 9 structural `syntax.rs` mutations (`10` atomic entries), all 11 MIR specimens (`S1`–`S11`), and deterministic assertions verifying `T1`–`T5` scaling, allocation, intersection, equivalence-class, and `SemProfile` capability metrics.
- `support/probe_ir_migration_topologies_results.json`: Canonical JSON output produced by `support/probe_ir_migration_topologies.py`.

## Revalidation

1. **Re-execute the standalone five-topology probe (`< 0.2s`, Python 3.10+ standard library only, zero `.pyc` bytecode written):**
   ```bash
   python3 -B reports/multi-version-ir-migration-topologies-and-capability-schemas/support/probe_ir_migration_topologies.py \
     --out /tmp/probe_ir_migration_topologies_check.json
   diff -u \
     reports/multi-version-ir-migration-topologies-and-capability-schemas/support/probe_ir_migration_topologies_results.json \
     /tmp/probe_ir_migration_topologies_check.json
   ```
   Passing (`rc=0` and empty `diff`) confirms all internal assertions (`7` `syntax.rs` equivalence classes across 9 pins, `[]` strict 9-pin variant intersection, `2/11` `T1` unrepresentable specimens, `6/11` `T2` unrepresentable specimens, `4/11` unidir and `5/11` bidir `T3c` lagging-hub hazards, and `0/11` `T4` lossiness).

2. **Revalidate `Runtime(PostCleanup)` MIR edition independence on a newer `rust-lang/rust` revision `<NEW_SHA>`:**
   - Inspect `compiler/rustc_middle/src/mir/mod.rs` and `compiler/rustc_middle/src/mir/syntax.rs` at `<NEW_SHA>` for any occurrences of `Edition` or `BackwardIncompatibleDrop`:
     ```bash
     gh api "repos/rust-lang/rust/contents/compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs?ref=<NEW_SHA>" \
       -H "Accept: application/vnd.github.raw" | grep -n -C 4 "BackwardIncompatibleDropHint"
     ```
   - Confirm `mir::Body` still contains zero `Edition` fields and `CleanupPostBorrowck` still rewrites `BackwardIncompatibleDropHint` to `Nop` before `Runtime(PostCleanup)`.

3. **Revalidate `ppxlib` trunk AST pin and tunneling encodings or `Charon` version-gate policy on newer upstream commits:**
   ```bash
   gh api "repos/ocaml-ppx/ppxlib/contents/ast/import.ml?ref=<PPXLIB_SHA>" -H "Accept: application/vnd.github.raw"
   gh api "repos/AeneasVerif/charon/contents/charon/src/export.rs?ref=<CHARON_SHA>" -H "Accept: application/vnd.github.raw" | head -n 65
   ```
   Check whether `module Js = Versions.OCaml_<NNN>` still lags the newest `Astlib.Ast_<MMM>` in `astlib/astlib.ml`, and whether `CharonVersion::deserialize` in `charon/src/export.rs` still enforces `version != crate::VERSION` exact equality or introduces minor-version range compatibility.
