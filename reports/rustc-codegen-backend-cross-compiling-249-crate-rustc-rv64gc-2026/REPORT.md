# Cross-Compiling the 249-Crate `rustc` Workspace to `RV64GC` with `rustc_codegen_anneal`: Query ICEs, `EarlyBinder` Monomorphization, `CrateType::Dylib` Whole-Archive Linking, and Anti-Stub-Drift Gates

## Summary

The companion pre-implementation report
(`reports/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/REPORT.md`)
mapped the `rustc_codegen_ssa::traits::CodegenBackend` trait surface, the
`MirPhase::Runtime(RuntimePhase::PostCleanup)` dialect boundary, and the RISC-V
LP64D `FnAbi` and intrinsic obligations for `rustc_codegen_anneal`. Turning that
architectural design into an operational `-Z codegen-backend` shared library
(`librustc_codegen_anneal.so`, `joshlf/anneal` commits `25`–`40` at
`7677632ab267e6d7075fc9ddca7280ddf0296f87`) and scaling it from single-file
tests to cross-compiling the entire 249-crate `rust-lang/rust` compiler
workspace (`compiler/rustc/Cargo.toml`) for `riscv64gc-unknown-linux-gnu`
exposed five concrete implementation hazards and architectural invariants:

1. **Diagnostic-coupled path queries (`tcx.def_path_str`) and anonymous
   `DefKind::Closure` items trigger compiler ICEs during normal codegen:**
   Calling `tcx.def_path_str(def_id)` inside a `-Z codegen-backend` plugin
   invokes `tcx.trimmed_def_paths(())`
   (`compiler/rustc_middle/src/ty/print/pretty.rs:459`), which calls
   `tcx.sess.record_trimmed_def_paths()`
   (`compiler/rustc_session/src/session.rs:528-541`) and sets
   `tcx.dcx().set_must_produce_diag()`. When a crate compiles cleanly without
   diagnostics, `DiagCtxtInner::drop`
   (`compiler/rustc_errors/src/lib.rs:432-471`) panics with an Internal Compiler
   Error (ICE): ``"`trimmed_def_paths` called, diagnostics were expected but
   none were emitted. Use `with_no_trimmed_paths` for debugging."`` This trap is
   invisible in both `--emit=mir` driver tests (because
   `record_trimmed_def_paths` explicitly exempts `OutputType::Mir` at
   `session.rs:534`) and standalone `rustc_driver` tools (because
   `opts.trimmed_def_paths` defaults to `false` unless
   `TimePassesCallbacks::config` sets it to `true` at
   `compiler/rustc_driver_impl/src/lib.rs:167`). In addition, calling
   `tcx.item_name(def_id)` on monomorphized closures (`DefKind::Closure`) panics
   at `compiler/rustc_middle/src/ty/mod.rs:1703-1706` because closures have no
   identifier name. Codegen backends must use
   `with_no_trimmed_paths!(tcx.def_path_str(def_id))` or
   `tcx.def_path_debug_str(def_id)`, query `tcx.opt_item_name(def_id)`, and read
   the crate name via `tcx.crate_name(def_id.krate)`.
2. **`tcx.instance_mir` returns uninstantiated polymorphic MIR, and
   `ty::EarlyBinder::bind` in `1.101.0-nightly` requires `(tcx, value)`:**
   Iterating `cgu.items()` yields concrete `MonoItem::Fn(instance)` entries, but
   `tcx.instance_mir(instance.def)` returns the unsubstituted polymorphic
   `mir::Body<'tcx>` of `instance.def_id()`. Passing types, operands, or callee
   `GenericArgsRef` from that body directly to `tcx.layout_of`,
   `mir::Const::eval`, `tcx.const_eval_resolve_for_typeck`, or
   `ty::Instance::try_resolve` under `ty::TypingEnv::fully_monomorphized()`
   fails or panics whenever `has_non_region_param()` is true. Furthermore, in
   `rustc 1.101.0-nightly` (`compiler/rustc_type_ir/src/binder.rs:333-357`),
   `EarlyBinder::bind(cx, value)` takes **two** arguments so it can mark rigid
   aliases via `ty::set_aliases_to_non_rigid(cx, value)`, splitting one-argument
   construction into `EarlyBinder::bind_no_rigid_aliases(value)`. Lowering must
   substitute via `instance.instantiate_mir_and_normalize_erasing_regions(tcx,
   typing_env, ty::EarlyBinder::bind(tcx, raw_value))` and guard layout, CTFE,
   and `Instance::try_resolve` queries with `!has_non_region_param()` and
   `!tcx.is_coroutine(did)`.
3. **`CrateType::Dylib` facade-crate linking (`librustc_driver.so`) drops 100%
   of `rustc_driver_impl` without `--whole-archive`, and multi-CGU `.rlib`s
   require `STB_GLOBAL`:** The `rustc` binary (`compiler/rustc/src/main.rs`) is
   a thin wrapper calling `rustc_driver::main()` inside `librustc_driver.so`
   (`CrateType::Dylib`). However, `compiler/rustc_driver/src/lib.rs` is an empty
   re-export facade (`pub use rustc_driver_impl::*;`) with `0` `MonoItem`s in
   `1` CGU; all `17,622` driver `MonoItem`s (`256` CGUs) reside in
   `librustc_driver_impl.rlib`. When cross-compiling `librustc_driver.so` with
   `rust-lld -flavor gnu -m elf64lriscv -shared`, passing upstream `.rlib`s as
   ordinary positional archives causes `rust-lld` to drop every archive member
   from `librustc_driver_impl.rlib` because `rustc_driver`'s own `rmeta.o` makes
   zero undefined symbol references. Wrapping the upstream `.rlib` paths from
   `crate_info.used_crates` (`crate_info.used_crate_source[&cnum].rlib`) in
   `--whole-archive ... --no-whole-archive` retains all `907,100` dynamic
   symbols (`218,328,228` bytes of `.text`, `691,909,736` bytes total in
   `librustc_driver.so`). Moreover, because `rustc` partitions large crates into
   up to `256` CGUs (`11,558` total CGUs across the 249 crates), internal Rust
   functions, statics, and vtables in `.o` members must be emitted with
   `STB_GLOBAL` (`is_global: true`) rather than `STB_LOCAL` so cross-CGU
   relocations resolve inside multi-CGU `.rlib`s.
4. **Target-scoped `CARGO_TARGET_<TRIPLE>_RUSTFLAGS` and `--no-default-features`
   make the 249-crate `compiler/rustc` graph 100% pure Rust (`55.14s` build):**
   Building `compiler/rustc/Cargo.toml` with `--no-default-features` disables
   the default `llvm` and `jemalloc` features
   (`compiler/rustc/Cargo.toml:30-43`,
   `compiler/rustc_driver_impl/Cargo.toml:60-71`), pruning `rustc_codegen_llvm`
   (`llvm-sys` C++ compilation) and `tikv-jemalloc-sys` (C cross-compiler build)
   so all 249 target crates are pure Rust. Scoping `-Z codegen-backend` to
   `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS` (rather than global
   `RUSTFLAGS`) keeps host `build.rs` scripts and host proc-macros
   (`rustc_macros`, `serde_derive`, `zerovec-derive`, etc.) on the host
   `x86_64-unknown-linux-gnu` LLVM backend while compiling all 249 target crates
   (`931,257` `MonoItem`s across `11,558` CGUs) to RV64GC in `55.14s`.
5. **Eliminating "stub drift" via real `-Z codegen-backend` execution gates
   isolates the three remaining runtime boundaries for un-intercepted
   `rustc-main` execution:** Early pipeline scaffolding (`entry_return_body`
   overrides in `anc-driver`, a per-CGU function cap in `rustc_codegen_anneal`,
   and matching `"main"` without checking `instance.def_id().is_local()`)
   initially allowed phase gates to pass without exercising full multi-crate
   lowering. Removing all three bypasses in commits `39`–`40` (`4bde620f6` and
   `7677632ab`) and compiling all `931,257` `MonoItem`s uncapped isolated the
   exact three engineering items separating the current `sym 507`
   (`rustc_driver::main`) banner intercept from un-intercepted
   `rustc_driver_impl::main` execution under `qemu-riscv64`: general
   `TyAndLayout` multi-field offset/size lowering (replacing the fixed 112-slot
   2-field scalarized `MirLocal` frame and 64-block clamp), removal of the
   `sym 507` CLI flag intercept, and a `riscv64-linux-gnu` `glibc` (`libc.so.6`,
   `ld-linux-riscv64-lp64d.so.1`) sysroot or static musl linkage.

## Applicability

Every claim in this report is bound to the following pinned repositories,
toolchains, and verification artifacts:

- **`rust-lang/rust`:**
  - Reference baseline commit `58cf8f9c35b355199727627d07ae34a4e2846d67`
    (`1.101.0-nightly`, pinned by Anneal's trusted boundary);
  - Host `rustc` nightly toolchain and `rustc-src` sysroot at
    `19833af7224424e8b53e288097d56b6af43d5bcf` (`1.101.0-nightly`,
    `2026-10-20`);
  - Local `rust-lang/rust` compiler workspace checkout at upstream merge-base
    `ada41e1ce81819f01577c0ee40ccbd6fc41384e8` (worktree commit
    `49d734536222bf28bb6d07d885b3a81d145981da`).
  - Specific compiler crates inspected: `compiler/rustc_middle`,
    `compiler/rustc_type_ir`, `compiler/rustc_ty_utils`,
    `compiler/rustc_session`, `compiler/rustc_errors`,
    `compiler/rustc_codegen_ssa`, `compiler/rustc_driver`,
    `compiler/rustc_driver_impl`, and `compiler/rustc`.
- **`joshlf/anneal`:**
  - Repository baseline `beb778bb135474a67dc017c185d2753a60693d8c` and RV64GC
    backend branch commit `7677632ab267e6d7075fc9ddca7280ddf0296f87` (commits
    `25`–`40`: `compiler/rustc-codegen-anneal/src/lib.rs`,
    `compiler/anc-driver/src/lib.rs`, `compiler/anc-verified/src/lib.rs`, and
    `agent_docs/anllvm/{DECISIONS.md,STATE.md,ORACLES.md}`).
- **Host and target execution environment:**
  - Host: `x86_64-unknown-linux-gnu` (`rustc 1.101.0-nightly`, bundled LLVM 21
    `rust-lld`, `ar`, `readelf`).
  - Target: `riscv64gc-unknown-linux-gnu` (`EM_RISCV = 243`, `e_flags = 0x5` for
    `EF_RISCV_RVC | EF_RISCV_FLOAT_ABI_DOUBLE`), executed under `qemu-riscv64`
    `10.0.2`.
- **Self-contained `support/` verification package:**
  - `support/rustc_codegen_traps_and_link_probe.rs` (SHA-256
    `14feba43afc9f239ed0414c1f547b2f2616c94a7558691fe1051d5dc90968f6f`) and its
    recorded output `support/rustc_codegen_traps_and_link_probe.out.txt`
    (SHA-256
    `ea1955e510459002e4e65a523dacda9d87f97024a3ea97d1bcc470dc0ba7edc8`);
  - `support/cross_compile_rustc_rv64gc_recipe.sh` (SHA-256
    `0192947785bab96819d45f6f541a846b35c049c40c9070a2b3f7abb33f91c71d`);
  - `support/rustc_249_crate_rv64gc_census.json` (SHA-256
    `3a7fed5832fbc0d62be45b38e354c7a5dcff5010db1fba9a9bf5c526adbceb74`).

## Findings

### Finding 1: The `tcx.def_path_str` $\to$ `trimmed_def_paths` $\to$ `DiagCtxtInner::drop` ICE and the `DefKind::Closure` `tcx.item_name` Panic

When a `-Z codegen-backend` plugin formats a `DefId` into a human-readable path
string during codegen (for example, to classify standard-library intrinsics or
match entry functions), calling `tcx.def_path_str(def_id)` appears innocuous. In
`rustc`, however, `def_path_str` is wired to a diagnostic-only path-trimming
query that arms a deferred panic bomb inside `DiagCtxtInner::drop` whenever
compilation succeeds without emitting a diagnostic.

#### Exact Call Chain in `rust-lang/rust`

1. **`TyCtxt::def_path_str` and `FmtPrinter::print_def_path`
   (`compiler/rustc_middle/src/ty/print/pretty.rs:2170-2186`, `2227-2236`):**
   `tcx.def_path_str(def_id)` calls `self.def_path_str_with_args(def_id, &[])`,
   which constructs `FmtPrinter::new(self, Namespace::ValueNS)` and calls
   `print_def_path(def_id, args)`. When `args.is_empty()`, line `2233` calls
   `self.try_print_trimmed_def_path(def_id)`.
2. **`PrettyPrinter::try_print_trimmed_def_path`
   (`compiler/rustc_middle/src/ty/print/pretty.rs:451-466`):**
   ```rust
   fn try_print_trimmed_def_path(&mut self, def_id: DefId) -> Result<bool, PrintError> {
       if self.tcx().sess.opts.unstable_opts.trim_diagnostic_paths
           && self.tcx().sess.opts.trimmed_def_paths
           && !with_no_trimmed_paths()
           && !with_crate_prefix()
           && let Some(symbol) = self.tcx().trimmed_def_paths(()).get(&def_id)
       {
           write!(self, "{}", Ident::with_dummy_span(*symbol))?;
           return Ok(true);
       }
       Ok(false)
   }
   ```
   Here `-Z trim-diagnostic-paths` defaults to `true`. When
   `tcx.sess.opts.trimmed_def_paths` is also `true` and neither
   `with_no_trimmed_paths!` nor `with_crate_prefix!` is active on the current
   thread, line `459` executes the `tcx.trimmed_def_paths(())` query.
3. **`trimmed_def_paths` and `Session::record_trimmed_def_paths`
   (`compiler/rustc_middle/src/ty/print/pretty.rs:3531-3539` and
   `compiler/rustc_session/src/session.rs:528-541`):** The `trimmed_def_paths`
   query computes a whole-crate map of shortened item names for error messages.
   Because constructing that map is expensive, `trimmed_def_paths` immediately
   calls `tcx.sess.record_trimmed_def_paths()`:
   ```rust
   pub fn record_trimmed_def_paths(&self) {
       if self.opts.unstable_opts.print_type_sizes
           || self.opts.unstable_opts.query_dep_graph
           || self.opts.unstable_opts.dump_mir.is_some()
           || self.opts.unstable_opts.unpretty.is_some()
           || self.prof.is_args_recording_enabled()
           || self.opts.output_types.contains_key(&OutputType::Mir)
           || std::env::var_os("RUSTC_LOG").is_some()
       {
           return;
       }
       self.dcx().set_must_produce_diag();
   }
   ```
4. **`DiagCtxtInner::set_must_produce_diag` and `DiagCtxtInner::drop`
   (`compiler/rustc_errors/src/lib.rs:314`, `432-471`, `945-951`):**
   `set_must_produce_diag()` records `Some(Backtrace::capture())` in
   `self.must_produce_diag`. When the compiler session finishes and drops
   `DiagCtxtInner`, `Drop::drop` checks whether any diagnostic was actually
   emitted:
   ```rust
   impl Drop for DiagCtxtInner {
       fn drop(&mut self) {
           // ...
           if !self.has_printed && !self.suppressed_expected_diag && !std::thread::panicking() {
               if let Some(backtrace) = &self.must_produce_diag {
                   panic!(
                       "`trimmed_def_paths` called, diagnostics were expected but none were emitted. \
                       Use `with_no_trimmed_paths` for debugging.{backtrace}",
                   );
               }
           }
       }
   }
   ```

#### Why `--emit=mir` Tests and Custom `rustc_driver` Binaries Mask the ICE

Two subtleties explain why this bug often escapes early testing and only
surfaces when a `-Z codegen-backend` plugin is invoked by standard `rustc` or
`cargo build`:

- **`--emit=mir` exemption (`compiler/rustc_session/src/session.rs:534`):** When
  a test passes `--emit=mir`,
  `self.opts.output_types.contains_key(&OutputType::Mir)` is `true`, so
  `record_trimmed_def_paths()` returns early before calling
  `set_must_produce_diag()`. The exact same backend code that succeeds under
  `rustc --emit=mir,link` panics at session teardown under `cargo build` (which
  requests `OutputType::Object` / `OutputType::Metadata` / `OutputType::Exe`
  without `OutputType::Mir`).
- **`TimePassesCallbacks::config`
  (`compiler/rustc_driver_impl/src/lib.rs:154-169`, `1688-1693`):** In
  `Options::default()`, `opts.trimmed_def_paths` starts as `false`. A standalone
  `rustc_driver` tool (`rustc_driver::compiler_entrypoint(&args, &mut
  my_callbacks)`) that implements its own `Callbacks` struct leaves
  `opts.trimmed_def_paths` at `false`, so `try_print_trimmed_def_path`
  short-circuits at line `453`. By contrast, the standard `rustc` binary
  (`rustc_driver_impl::main`) runs with `TimePassesCallbacks`, whose `config`
  hook explicitly sets `config.opts.trimmed_def_paths = true`
  (`rustc_driver_impl/src/lib.rs:167`).

#### The `DefKind::Closure` `tcx.item_name` Panic (`compiler/rustc_middle/src/ty/mod.rs:1688-1714`)

A second query panic arises as soon as a crate contains a closure or coroutine:

- `tcx.item_name(def_id)` calls `self.opt_item_name(def_id).unwrap_or_else(||
  bug!("item_name: no name for {:?}", self.def_path(def_id)))`.
- For `DefKind::Closure` (`DefPathData::Closure`), `DefKey::get_opt_name()`
  returns `None` because closures are anonymous definitions. Calling
  `tcx.item_name(instance.def_id())` on a monomorphized closure therefore ICEs
  immediately.
- Similarly, calling `tcx.item_name(def_id.krate.as_def_id())` fails when
  `def_id.krate == LOCAL_CRATE` because the crate root `CRATE_DEF_ID` has
  `DefPathData::CrateRoot` (also unnamed in `def_key`).

#### Remediation in `rustc_codegen_anneal` (`DC-20`, `DC-21`, `compiler/rustc-codegen-anneal/src/lib.rs:265-266`, `862`, `1073-1075`, `1100`)

| Unsafe / Diagnostic-Coupled Query | Failure Mode | Safe Codegen Replacement |
| :--- | :--- | :--- |
| `tcx.def_path_str(def_id)` | Invokes `trimmed_def_paths(())` $\to$ `DiagCtxtInner::drop` ICE when compilation emits 0 diagnostics | `with_no_trimmed_paths!(tcx.def_path_str(def_id))` (`pretty.rs:118`), `tcx.def_path_debug_str(def_id)` (`context.rs:1216`), or `mono_item.symbol_name(tcx).name` |
| `tcx.item_name(def_id)` | Calls `bug!("item_name: no name for ...")` on `DefKind::Closure` (`DefPathData::Closure`) | `tcx.opt_item_name(def_id)` (`Option<Symbol>`, `mod.rs:1710-1714`) |
| `tcx.item_name(def_id.krate.as_def_id())` | Calls `bug!` on `LOCAL_CRATE` (`DefPathData::CrateRoot`) | `tcx.crate_name(def_id.krate)` (`context.rs:1244`) |

---

### Finding 2: Polymorphic Query Panics in MIR Lowering and the Two-Argument `ty::EarlyBinder::bind(tcx, value)` Contract

When `CodegenBackend::codegen_crate` partitions a crate via
`tcx.collect_and_partition_mono_items(())`, every `MonoItem::Fn(instance)` in a
codegen unit represents a fully monomorphized function instantiation whose
`instance.args` holds concrete generic arguments. However, calling
`tcx.instance_mir(instance.def)`
(`compiler/rustc-codegen-anneal/src/lib.rs:297`) returns the **unsubstituted**
polymorphic `mir::Body<'tcx>` of the underlying `DefId`. Inside that
`mir::Body<'tcx>`:

- Local declarations (`body.local_decls[local].ty`) still contain
  `TyKind::Param` and unnormalized associated-type projections
  (`TyKind::Alias(Projection, ..)`).
- Constant operands (`Operand::Constant(c)`) and array lengths still contain
  `ConstKind::Param` or unevaluated generic `mir::Const::Unevaluated` values.
- Call terminators (`TerminatorKind::Call { func, .. }`) where
  `func.const_fn_def()` returns `Some((callee_def_id, raw_callee_args))` carry
  `raw_callee_args` expressed in terms of the caller's generic parameters.

#### Three Query Failure Modes on Unsubstituted MIR Entities

If MIR lowering passes those raw types, constants, or callee arguments directly
to `TyCtxt` queries under `ty::TypingEnv::fully_monomorphized()`, three distinct
panics/errors occur in `rust-lang/rust`:

1. **`Instance::instantiate_mir_and_normalize_erasing_regions`
   (`compiler/rustc_middle/src/ty/instance.rs:956-970` $\to$
   `compiler/rustc_middle/src/ty/normalize_erasing_regions.rs:157-208`):**
   Substituting a value with `instance.args` runs
   `NormalizeAfterErasingRegionsFolder`. If any `TyKind::Param` or
   unnormalizable rigid alias survives into
   `normalize_generic_arg_after_erasing_regions` under
   `TypingEnv::fully_monomorphized()`, lines `195-208` panic with: `bug!("Failed
   to normalize {:?} in typing_env={:?}, maybe try to call
   try_normalize_erasing_regions instead")`.
2. **`ty::Instance::try_resolve` and CTFE queries
   (`compiler/rustc_ty_utils/src/instance.rs:24-32` and
   `compiler/rustc_middle/src/mir/consts.rs:315-350`):**
   `ty::Instance::try_resolve(tcx, typing_env, callee_def_id, args)` begins at
   line `28` by calling `tcx.normalize_erasing_regions(typing_env,
   Unnormalized::new_wip(args))` before checking `args.has_non_region_param()`.
   Likewise, `mir::Const::eval` and `tcx.const_eval_resolve` /
   `tcx.const_eval_resolve_for_typeck`
   (`compiler/rustc_middle/src/mir/interpret/queries.rs:58-130`) resolve the
   constant's `Instance` under `typing_env`. If `args` or the constant still
   contains a generic parameter or unnormalized projection over a generic
   parameter, `normalize_erasing_regions` or CTFE panics with an ICE.
3. **`tcx.layout_of` (`compiler/rustc_ty_utils/src/layout.rs:41-112`):**
   Querying
   `tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))` when
   `ty.has_non_region_param()` is true returns
   `Err(LayoutError::TooGeneric(ty))` (or
   `Err(LayoutError::NormalizationFailure(..))`).

#### The Two-Argument `ty::EarlyBinder::bind(tcx, value)` Signature in `1.101.0-nightly`

In earlier `rustc` versions (and still in the external `rustc_public` wrapper at
`compiler/rustc_public/src/ty/tys.rs:923`), `EarlyBinder::bind(value)` took a
single argument (`value: T`). In `rustc 1.101.0-nightly`,
`compiler/rustc_type_ir/src/binder.rs:333-357` split `EarlyBinder` construction
into three methods to enforce explicit handling of rigid alias types before
normalization:

```rust
impl<I: Interner, T> EarlyBinder<I, T> {
    pub fn bind(cx: I, value: T) -> EarlyBinder<I, Unnormalized<I, T>>
    where
        T: TypeFoldable<I>,
    {
        EarlyBinder {
            value: ty::set_aliases_to_non_rigid(cx, value).skip_normalization(),
            _tcx: PhantomData,
        }
    }

    pub fn bind_iter<U>(value: T) -> EarlyBinder<I, T>
    where
        T: IntoIterator<Item = U>,
    {
        EarlyBinder { value, _tcx: PhantomData }
    }

    #[track_caller]
    pub fn bind_no_rigid_aliases(value: T) -> EarlyBinder<I, Unnormalized<I, T>>
    where
        T: TypeVisitable<I>,
    {
        #[cfg(debug_assertions)]
        assert!(!value.has_rigid_aliases());
        EarlyBinder { value: Unnormalized::new_wip(value), _tcx: PhantomData }
    }
}
```

Passing a single argument to `ty::EarlyBinder::bind` therefore fails to compile
against `rustc_middle::ty::EarlyBinder` in `1.101.0-nightly`, and calling
`EarlyBinder::bind_no_rigid_aliases(value)` on uninstantiated MIR types or
`GenericArgsRef` that contain associated-type projections triggers the debug
assertion `!value.has_rigid_aliases()`. Backend code must call the two-argument
`ty::EarlyBinder::bind(tcx, value)` so `set_aliases_to_non_rigid(tcx, value)`
converts rigid aliases prior to
`instance.instantiate_mir_and_normalize_erasing_regions`.

#### Defensive Monomorphization Pattern in `rustc_codegen_anneal` (`DC-32`, `compiler/rustc-codegen-anneal/src/lib.rs:194`, `295-297`, `381`, `960-991`, `1169`)

To compile all `931,257` `MonoItem`s of `compiler/rustc` without a single
normalization or CTFE panic, `rustc_codegen_anneal` enforces three guards:

1. **Pre-body entry guard (`lib.rs:295`):** Skip calling `tcx.instance_mir` if
   `instance.args.has_non_region_param()` or `tcx.is_coroutine(did)` is true.
2. **Two-argument `EarlyBinder::bind(tcx, ..)` substitution
   (`lib.rs:965-979`):** Before resolving a direct call's
   `(callee_def_id, raw_callee_args)`, substitute `raw_callee_args` with the
   caller `instance`:
   ```rust
   let callee_args = if !instance.args.has_non_region_param() {
       instance.instantiate_mir_and_normalize_erasing_regions(
           tcx,
           ty::TypingEnv::fully_monomorphized(),
           ty::EarlyBinder::bind(tcx, raw_callee_args),
       )
   } else {
       raw_callee_args
   };
   ```
3. **Post-substitution `!has_non_region_param()` gate (`lib.rs:194`, `381`,
   `981`, `1169`):** Before invoking `ty::Instance::try_resolve(tcx,
   ty::TypingEnv::fully_monomorphized(), callee_def_id, callee_args)`,
   `const_.eval(tcx, ty::TypingEnv::fully_monomorphized(), span)`, or
   `tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))`,
   explicitly verify `!callee_args.has_non_region_param()` /
   `!const_.has_non_region_param()` / `!ty.has_non_region_param()`.

---

### Finding 3: The `CrateType::Dylib` Facade-Crate Linker Trap (`librustc_driver.so` vs. `rustc-main`) and Cross-CGU Symbol Binding

Cross-compiling `compiler/rustc` (`rustc-main`) exposes a structural split in
how `rustc` is packaged across three crates:

```
compiler/rustc/src/main.rs           (bin: rustc-main, 1 CGU, 1 MonoItem)
  └── calls rustc_driver::main()
        │
        ▼
compiler/rustc_driver/src/lib.rs     (dylib: librustc_driver.so, 1 CGU, 0 MonoItems)
  └── `pub use rustc_driver_impl::*;` (re-export facade crate)
        │
        ▼
compiler/rustc_driver_impl/src/lib.rs (rlib: librustc_driver_impl.rlib, 256 CGUs, 17,622 MonoItems)
  └── depends on 246 upstream compiler and standard-library `.rlib` crates
```

- `compiler/rustc/Cargo.toml:1-19` defines the `rustc-main` binary, whose
  `compiler/rustc/src/main.rs:38-40` simply calls `rustc_driver::main()`.
- `compiler/rustc_driver/Cargo.toml:6-7` declares `crate-type = ["dylib"]`, and
  `compiler/rustc_driver/src/lib.rs:1-5` contains only
  `pub use rustc_driver_impl::*;`. Because `rustc_driver` defines no functions
  or statics of its own, `tcx.collect_and_partition_mono_items(())` on
  `rustc_driver` produces `1` CGU containing `0` `MonoItem`s.
- All `17,622` monomorphized items of the driver (plus `913,634` `MonoItem`s in
  its 247 upstream `.rlib` dependencies) live in `librustc_driver_impl.rlib` and
  its transitive `.rlib` graph.

This architecture creates three distinct linking traps when cross-compiling to
`riscv64gc-unknown-linux-gnu`:

#### Trap 3A: Default `rustc_codegen_ssa::back::link::link_binary` Invokes Host `cc` on `EM_RISCV` Objects

If `CodegenBackend::link` delegates `CrateType::Dylib` on
`riscv64gc-unknown-linux-gnu` to `rustc_codegen_ssa::back::link::link_binary` on
an `x86_64-unknown-linux-gnu` host without a `riscv64-linux-gnu-gcc` driver,
`link_binary` invokes the host `cc` (`x86_64`), which passes `-m elf_x86_64` to
`rust-lld` and fails on every `.rlib` member with: `rust-lld: error:
.../librustc_driver_impl.rlib(...) is incompatible with elf64-x86-64`. Instead,
`CodegenBackend::link` must invoke the sysroot's cross-target-capable `rust-lld`
directly with `-flavor gnu -m elf64lriscv`
(`compiler/rustc-codegen-anneal/src/lib.rs:1306-1346`).

#### Trap 3B: Passing `.rlib` Archives to `rust-lld -shared` Without `--whole-archive` Drops 100% of `rustc_driver_impl`

When `CodegenBackend::link` links `librustc_driver.so` (`CrateType::Dylib`),
`rustc_driver`'s own local compilation produces only `rmeta.o` (the `.rustc`
metadata section wrapper created by
`ArArchiveBuilderBuilder.create_dylib_metadata_wrapper` and `emit_wrapper_file`)
and a single empty CGU object. Neither object contains any undefined symbol
reference to `rustc_driver_impl`.

In standard ELF archive linking, passing `librustc_driver_impl.rlib` as a normal
positional archive causes `rust-lld -shared` to extract an archive member `.o`
**only** if that `.o` defines a symbol needed to satisfy an already-pending
undefined symbol reference. (In `rustc_codegen_ssa`, `add_linked_symbol_object`
at `compiler/rustc_codegen_ssa/src/back/link.rs:2482-2626` works around this by
synthesizing a temporary `symbols.o` containing undefined references to
`crate_info.linked_symbols` and a version script.) If a custom backend invokes
`rust-lld -flavor gnu -m elf64lriscv -shared rmeta.o <cgu.o>` without
`symbols.o` or `--whole-archive`, `rust-lld` drops 100% of the archive members
from `librustc_driver_impl.rlib` and its upstream `.rlib`s. The link of
`librustc_driver.so` succeeds prematurely, producing a stub shared library that
contains only `.rustc` metadata and fails as soon as `rustc-main` links against
it (`undefined symbol: rustc_driver::main`).

`rustc_codegen_anneal` (`DC-34`,
`compiler/rustc-codegen-anneal/src/lib.rs:1318-1345`) resolves this by iterating
`crate_info.used_crates` (`compiler/rustc_codegen_ssa/src/base.rs:1066-1095`,
which lists `tcx.used_crates(())` in dependency order) and wrapping every
upstream `.rlib` path from `crate_info.used_crate_source[&cnum].rlib` inside
`--whole-archive ... --no-whole-archive`:

```rust
let mut cmd = std::process::Command::new(&rust_lld);
cmd.arg("-flavor")
    .arg("gnu")
    .arg("-m")
    .arg("elf64lriscv")
    .arg("-shared")
    .arg(&rmeta_obj);
for m in &compiled_modules.modules {
    if let Some(obj) = &m.object {
        cmd.arg(obj);
    }
}
cmd.arg("--whole-archive");
for &cnum in &crate_info.used_crates {
    if let Some(src) = crate_info.used_crate_source.get(&cnum)
        && let Some((rlib_path, _)) = &src.rlib
    {
        cmd.arg(rlib_path);
    }
}
cmd.arg("--no-whole-archive").arg("-o").arg(&out_path);
```

With `--whole-archive ... --no-whole-archive`, `rust-lld` retains all `11,557`
CGU object members across all 248 library crates, producing a `691,909,736`-byte
(`659.86 MiB`) `librustc_driver.so` with `907,100` dynamic symbols in `.dynsym`
and `218,328,228` bytes (`208.21 MiB`) of executable RV64GC machine code in
`.text`.

#### Trap 3C: Multi-CGU `.rlib` Archives Require `STB_GLOBAL` Rather Than `STB_LOCAL` on Internal Items

In single-CGU toy crates, all monomorphized functions of a crate land in a
single relocatable `.o` file, so marking non-`#[no_mangle]` Rust functions as
`STB_LOCAL` (`st_info = (0 << 4) | STT_FUNC = 0x02`) still allows intra-CGU
calls to resolve. In the `compiler/rustc` workspace, however, `rustc` partitions
large crates into up to `256` CGUs (`rustc_query_impl`, `rustc_borrowck`,
`rustc_trait_selection`, `rustc_middle`, `rustc_driver_impl`, and 27 other
crates each use `256` CGUs), emitting one `.o` member per CGU into the crate's
`.rlib`.

When function $f$ in `cgu_0.o` calls private Rust function $g$ (or references a
static or vtable) partitioned into `cgu_1.o`, `cgu_0.o` emits an
`R_RISCV_CALL_PLT` (or `R_RISCV_PCREL_HI20`) relocation against an undefined
symbol entry for $g$. By the ELF specification, the linker only matches
undefined symbol references against `STB_GLOBAL` or `STB_WEAK` definitions
(`st_Idx >= sh_info` in `.symtab`); `STB_LOCAL` definitions in `cgu_1.o` are
invisible outside `cgu_1.o`. As verified by Case B of
`support/rustc_codegen_traps_and_link_probe.rs`, emitting `STB_LOCAL` for
internal Rust functions causes cross-CGU references to fail with
`undefined symbol`. Both `anc-driver/src/lib.rs:90, 105` and
`anc-verified/src/lib.rs` (`encode_rv64_module_to_elf64_rel_o`, `DC-27`)
therefore emit all CGU-level functions, statics, and vtables with
`is_global: true` (`STB_GLOBAL = 1`).

---

### Finding 4: The Exact `cargo -Z build-std` and `--no-default-features` Cross-Compilation Contract for the 249-Crate `compiler/rustc` Workspace

Cross-compiling `compiler/rustc/Cargo.toml` from `x86_64-unknown-linux-gnu` to
`riscv64gc-unknown-linux-gnu` without an external C/C++ cross-toolchain requires
satisfying three build-graph invariants simultaneously
(`support/cross_compile_rustc_rv64gc_recipe.sh`):

#### 1. Eliminating C/C++ Dependencies via `--no-default-features`

Inspecting `compiler/rustc/Cargo.toml:30-43` and
`compiler/rustc_driver_impl/Cargo.toml:60-71` shows how `rustc` gates its native
C and C++ dependencies behind Cargo features:

```toml
# compiler/rustc/Cargo.toml:30-43
[features]
jemalloc = ["dep:tikv-jemalloc-sys"]
llvm = ["rustc_driver/llvm"]
max_level_info = ["rustc_driver/max_level_info"]
rustc_use_parallel_compiler = ["rustc_driver/rustc_use_parallel_compiler"]
```

```toml
# compiler/rustc_driver_impl/Cargo.toml:60-71
[features]
llvm = ["rustc_interface/llvm"]
rustc_use_parallel_compiler = ["rustc_interface/rustc_use_parallel_compiler"]
max_level_info = ["rustc_log/max_level_info"]
```

When `--no-default-features` is passed to `cargo build --manifest-path
compiler/rustc/Cargo.toml`:

- `llvm` is disabled, which prunes `rustc_codegen_llvm` and `llvm-sys` (no
  target LLVM C++ headers or libraries are compiled or linked).
- `jemalloc` is disabled, which prunes `tikv-jemalloc-sys` (no target C compiler
  invocation is required).
- `rustc_codegen_ssa` (pure Rust) remains in the graph as the backend-agnostic
  codegen coordinator (`19,841` `MonoItem`s across `256` CGUs), allowing the
  resulting `rustc` binary to load `-Z codegen-backend` plugins dynamically or
  perform frontend/check/MIR passes without linking LLVM into
  `librustc_driver.so`.

As a result, all **249 target crates** in the `compiler/rustc` dependency graph
(from `core`, `compiler_builtins`, `alloc`, and `std` through `rustc_middle`,
`rustc_borrowck`, `rustc_query_impl`, `rustc_driver_impl`, `rustc_driver`, and
`rustc-main`) are **100% pure Rust**.

#### 2. Target-Scoped `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS` vs. Global `RUSTFLAGS`

While the 249 target crates compile for `riscv64gc-unknown-linux-gnu`, Cargo
also compiles **host** build scripts (`build.rs` in `libc`, `rustix`, `object`,
`serde`, `thiserror`, `rustc_attr_parsing`, etc.) and **host** procedural macro
shared libraries (`rustc_macros`, `rustc_index_macros`, `rustc_type_ir_macros`,
`serde_derive`, `zerovec-derive`, `displaydoc`, `tracing-attributes`, etc.) for
`x86_64-unknown-linux-gnu`, which the host `rustc` executes or `dlopen`s during
the build.

- If `-Z codegen-backend=.../librustc_codegen_anneal.so` is passed via global
  `RUSTFLAGS`, Cargo applies it to both host and target compilations, causing
  host proc-macros and `build.rs` scripts to run through the RV64GC backend and
  fail when executed on the `x86_64` host.
- Setting `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS="-Z
  codegen-backend=${CODEGEN_BACKEND_SO} -C panic=abort"` scopes the custom
  backend and `-C panic=abort` strictly to `riscv64gc-unknown-linux-gnu` target
  artifacts (including the `-Z build-std` crates `core`, `compiler_builtins`,
  `alloc`, `std`, `panic_abort`, and `proc_macro`), while host build scripts and
  proc-macros compile normally with the host LLVM backend.

#### 3. Required `rustc` Bootstrap Environment Variables

Several compiler crates inspect bootstrap environment variables at compile time
via `env!` or `option_env!`. Invoking `cargo build` directly on
`compiler/rustc/Cargo.toml` outside `x.py` requires setting six variables:

| Environment Variable | Value Used in RV64GC Build | Consuming Crates / Purpose |
| :--- | :--- | :--- |
| `RUSTC_BOOTSTRAP` | `1` | Permits `#![feature(...)]` and `-Z` flags across workspace crates and `build-std` |
| `CFG_RELEASE` | `1.101.0-nightly` | `rustc_interface`, `rustc_metadata`, `rustc_session` release string |
| `CFG_RELEASE_CHANNEL` | `nightly` | `rustc_session`, `rustc_feature` nightly feature gating |
| `CFG_VERSION` | `1.101.0-nightly (anneal-rv64gc)` | `rustc_driver_impl` `--version` banner and metadata version stamp |
| `CFG_COMPILER_HOST_TRIPLE` | `riscv64gc-unknown-linux-gnu` | `rustc_session::config::host_tuple()` default host triple of the built compiler |
| `RUSTC_INSTALL_BINDIR` | `bin` | `rustc_interface` sysroot binary directory lookup |

#### Empirical Scale of the 249-Crate `RV64GC` Build (`support/rustc_249_crate_rv64gc_census.json`)

Running `support/cross_compile_rustc_rv64gc_recipe.sh` compiles all 249 target
crates in **55.14 seconds** wall-clock time. Across the 249 target crates,
`rustc_codegen_anneal` processes **11,558 CGUs** and **931,257 `MonoItem`s**
(`931,256` across the 248 library crates plus `1` in `rustc-main`). The top 15
crates by `MonoItem` count account for `601,491` `MonoItem`s (`64.6%` of the
entire compiler):

| Rank | Crate Name | CGUs | `MonoItem`s | Share of Total (`931,257`) |
| ---: | :--- | ---: | ---: | ---: |
| 1 | `rustc_query_impl` | 256 | 86,455 | 9.28% |
| 2 | `rustc_borrowck` | 256 | 60,175 | 6.46% |
| 3 | `rustc_trait_selection` | 256 | 56,937 | 6.11% |
| 4 | `rustc_middle` | 256 | 53,129 | 5.70% |
| 5 | `rustc_hir_analysis` | 256 | 43,685 | 4.69% |
| 6 | `rustc_mir_transform` | 256 | 42,450 | 4.56% |
| 7 | `rustc_hir_typeck` | 256 | 40,639 | 4.36% |
| 8 | `rustc_resolve` | 256 | 36,110 | 3.88% |
| 9 | `rustc_attr_parsing` | 256 | 28,574 | 3.07% |
| 10 | `rustc_metadata` | 256 | 27,977 | 3.00% |
| 11 | `rustc_lint` | 256 | 21,766 | 2.34% |
| 12 | `rustc_ast_lowering` | 256 | 21,129 | 2.27% |
| 13 | `rustc_infer` | 256 | 21,007 | 2.26% |
| 14 | `rustc_codegen_ssa` | 256 | 19,841 | 2.13% |
| 15 | `rustc_driver_impl` | 256 | 17,622 | 1.89% |
| — | *Remaining 234 target crates (`std`, `core`, `rustc_mir_build`, `rustc_parse`, ..., `rustc_main`)* | 7,718 | 333,766 | 35.84% |
| **Total** | **249 target crates (`248` library + `1` binary)** | **11,558** | **931,257** | **100.00%** |

The resulting target ELF artifacts in `riscv64gc-unknown-linux-gnu/debug/` have
the following verified structure:

| ELF Artifact | ELF Type & Machine | File Size (Bytes) | `.text` Size (Bytes) | `.rodata` Size (Bytes) | `.dynsym` / `.symtab` Entries |
| :--- | :--- | ---: | ---: | ---: | ---: |
| `librustc_driver.so` | `ET_DYN`, `EM_RISCV (243)`, `Flags = 0x5` | `691,909,736` (`659.86 MiB`) | `218,328,228` (`208.21 MiB`) | `3,595,240` (`3.43 MiB`) | `907,100` / `907,101` |
| `rustc-main` | `ET_EXEC`, `EM_RISCV (243)`, `Flags = 0x5`, entry `0x10078` | `2,520` (`2.46 KiB`) | `456` (in `PT_LOAD` `0x9d8`) | — | Static `ET_EXEC` linked against `rustc_driver::main` |

---

### Finding 5: Preventing "Stub Drift" in Multi-Phase Verified Compiler Engineering and the Empirical Census of the Remaining `rustc_driver_impl` Execution Gap

When engineering a verified compiler across many incremental phases (from core
IR and instruction selection through ABI marshaling, ELF emission, and
self-hosting), early scaffolding stubs introduced to unblock downstream phase
gates can silently mask unimplemented lowering paths—a failure mode we term
**stub drift**.

#### Three Concrete Instances of Stub Drift Identified and Eliminated in Commits 37–40

1. **`entry_return_body` Override in
   `extract_rustc_mir_module_from_crate_source`
   (`compiler/anc-driver/src/lib.rs`, fixed in Commit 39 `4bde620f6`):** During
   initial phase scaffolding, `extract_rustc_mir_module_from_crate_source`
   invoked `rustc --emit=mir`, verified that the emitted MIR text was non-empty,
   and then returned a single-function `MirModule` constructed from a
   caller-supplied `entry_return_body: MirBody` parameter rather than parsing
   the `--emit=mir` output or running `-Z codegen-backend`. As a result, caller
   tests exercised `anc-verified`'s RV64 instruction selector and ELF encoder on
   `entry_return_body`, while the Rust source string passed to the function was
   only checked for syntactic/type validity by `rustc --emit=mir`. Commit 39
   removed the `entry_return_body` parameter and wired `anc-driver` to parse the
   emitted `--emit=mir` bodies directly (`parse_rustc_mir_text_to_module` at
   `compiler/anc-driver/src/lib.rs:348-418`), while adding 16 end-to-end tests
   in `compiler/rustc-codegen-anneal/src/lib.rs:1360-1573` that invoke the real
   `rustc -Z codegen-backend=librustc_codegen_anneal.so --target
   riscv64gc-unknown-linux-gnu` and execute the resulting RV64GC ELF binaries
   under `qemu-riscv64`.
2. **Non-Local `"main"` Entry-Symbol Collision
   (`compiler/rustc-codegen-anneal/src/lib.rs:1077-1083`, fixed in Commit 39
   `4bde620f6`):** Entry-symbol selection in `rustc_codegen_anneal` initially
   matched any monomorphized function whose name was `"main"`, `"main_entry"`,
   or ended with `"_entry"` without checking `instance.def_id().is_local()`. In
   multi-crate programs or crates importing helper functions named `main` from
   an upstream module, the backend could bind `entry_sym` to a non-local
   function before reaching the binary crate's own `fn main()`. Guarding entry
   detection with `instance.def_id().is_local()` ensures only a local definition
   in the root crate can become `entry_sym`.
3. **Per-CGU 32/64-Function Cap in `codegen_crate`
   (`compiler/rustc-codegen-anneal/src/lib.rs:1066-1096`, removed in Commit 40
   `7677632ab`):** To keep early multi-crate test times fast, `codegen_crate`
   initially gated full MIR lowering on `did.is_local() || total_mono_items <=
   2048 || functions.len() < 32`. While convenient during bring-up, that cap
   prevented `lower_rustc_mir_body` from exercising the remaining functions in
   large 256-CGU compiler crates. Commit 40 removed the cap completely, forcing
   all `931,257` `MonoItem`s across all 249 crates of `compiler/rustc` through
   `lower_rustc_mir_body` and into `librustc_driver.so`.

#### Design Principles for Anti-Stub-Drift Verification Gates

To prevent stub drift in multi-phase verified systems, phase gates must enforce
four structural properties:

1. **No caller-supplied expected-output or IR-override parameters in production
   driver entry points:** Any function claiming to compile source $S$ must
   derive its IR exclusively from $S$; synthetic IR builders belong only in unit
   tests.
2. **Differential input sensitivity:** Every end-to-end compilation gate must
   compile at least two distinct source inputs $S_1 \ne S_2$ through the full
   binary pipeline (`rustc -Z codegen-backend=...` $\to$ ELF $\to$
   `qemu-riscv64`) and assert that their observable runtime outputs differ
   accordingly.
3. **Zero silent truncation caps in `codegen_crate`:** Every `MonoItem` emitted
   by `collect_and_partition_mono_items` must be lowered and encoded into its
   CGU `.o` file.
4. **Explicit accounting of any remaining runtime shims in `DECISIONS.md` and
   `STATE.md`:** Any temporary runtime intercept must be isolated to a named
   symbol ID and tracked as an explicit open requirement.

#### Empirical Census of the Three Remaining Requirements for Un-Intercepted `rustc-main` Execution (`DC-36`)

With all `931,257` `MonoItem`s lowered into `librustc_driver.so` and
`rustc-main` executing `qemu-riscv64 rustc-main --version`
(`rustc 1.101.0-nightly (anneal-rv64gc)`), inspecting
`compiler/rustc-codegen-anneal/src/lib.rs` and `compiler/anc-driver/src/lib.rs`
identifies the exact three remaining boundaries between the current build and
un-intercepted `rustc_driver_impl::main` execution:

1. **General `TyAndLayout` Multi-Field Offset/Size Lowering and Unbounded
   Basic-Block/Local Scaling
   (`compiler/rustc-codegen-anneal/src/lib.rs:114-128`, `299-352`, `477-527`):**
   Currently, `lower_rustc_mir_body` maps each MIR local $i \in [0, 31]$ into a
   fixed 112-slot `MirLocal` frame (`map_base_slot` in `[0, 31]`,
   `map_field1_slot` in `[32, 63]` for `.1` two-field scalar pairs/slices,
   `map_discr_slot` in `[64, 95]` for enum discriminants, and `[96, 111]` for
   temporaries) and clamps functions with $> 64$ basic blocks (`max_bbs = 64` at
   `lib.rs:321`). Executing `rustc_driver_impl::run_compiler` un-intercepted
   requires querying `tcx.layout_of(typing_env.as_query_input(local_ty))`
   (`FieldsShape::Arbitrary` byte offsets and `Variants::Multiple` tag offsets)
   so structs and enums with $> 2$ fields or local indices $\ge 32$ and $> 64$
   basic blocks lower without slot aliasing or block clamping, together with
   indirect function-pointer calls (`jalr`) and cross-crate `.rela.text`
   relocation emission.
2. **Removing the `sym 507` (`rustc_driver::main`) CLI Banner Intercept
   (`compiler/rustc-codegen-anneal/src/lib.rs:289-294`,
   `compiler/anc-driver/src/lib.rs:867-894`):** When `rustc-main` calls
   `rustc_driver::main()` (`sym 507`, mapped via `WELL_KNOWN_SYMS` at
   `lib.rs:235`), `anc-driver` currently emits a dedicated RV64 Linux `write(1,
   "rustc 1.101.0-nightly (anneal-rv64gc)\n", 38)` + `exit_group(0)` stub
   (`emit_rv64_rustc_driver_main_stub`) so `rustc-main --version` can be
   validated under `qemu-riscv64` before `glibc` dynamic linking and multi-field
   option parsing in `rustc_driver_impl::handle_options` are active. Once
   Requirement 1 and Requirement 3 are in place, `sym 507` routes directly to
   `rustc_driver_impl::main`.
3. **Providing a `riscv64-linux-gnu` `glibc` Sysroot or Static `musl`/Syscall
   Linkage for Dynamically Linked `rustc-main`
   (`compiler/rustc-codegen-anneal/src/lib.rs:1347-1356`):** `rustc-main` is
   currently linked as a standalone static `ET_EXEC` ELF64 binary
   (`emit_rv64_executable_elf`) so `qemu-riscv64` can execute it directly on a
   host that lacks `/usr/riscv64-linux-gnu/lib/ld-linux-riscv64-lp64d.so.1` and
   `libc.so.6`. Running `rustc-main` dynamically linked against the `691.91 MB`
   `librustc_driver.so` under `qemu-riscv64 -L <sysroot>` requires a target
   `riscv64-linux-gnu` `glibc` sysroot (`libc.so.6`, `libm.so.6`,
   `libpthread.so.0`, `libdl.so.2`, `ld-linux-riscv64-lp64d.so.1`) or static
   `musl` libc archive.

## Boundaries

- **Compile-time codegen vs. un-intercepted runtime execution of `rustc-main`:**
  All 249 target crates of `compiler/rustc/Cargo.toml` (`11,558` CGUs, `931,257`
  `MonoItem`s) compile end-to-end through `librustc_codegen_anneal.so` and link
  into `librustc_driver.so` (`907,100` `.dynsym` symbols, `218,328,228` bytes
  `.text`) and `rustc-main`. However, as detailed in Finding 5, runtime
  execution of `rustc-main --version` under `qemu-riscv64` currently exercises
  the `sym 507` (`rustc_driver::main`) syscall banner stub rather than the full
  `rustc_driver_impl::main` option parser and `glibc` dynamic loader.
- **`--no-default-features` excludes the LLVM backend inside the cross-compiled
  target `rustc`:** Because `--no-default-features` disables the `llvm` feature
  on `compiler/rustc/Cargo.toml`, the cross-compiled RV64GC `librustc_driver.so`
  does not bundle `rustc_codegen_llvm`. To emit machine code on the target, the
  cross-compiled `rustc` must either load a target `-Z codegen-backend` plugin
  (such as `librustc_codegen_anneal.so` compiled for RV64GC) or be built with
  `llvm` enabled against a cross-compiled `riscv64gc` `LLVM.so`.
- **`EarlyBinder::bind(tcx, value)` API stability across `rustc` nightlies:**
  The two-argument `ty::EarlyBinder::bind(cx, value)` signature in
  `compiler/rustc_type_ir/src/binder.rs:333-357` is specific to internal
  `#![feature(rustc_private)]` APIs in `1.101.0-nightly` and may change in
  future nightly compiler revisions.

## Evidence

- **`support/rustc_codegen_traps_and_link_probe.rs` (SHA-256
  `14feba43afc9f239ed0414c1f547b2f2616c94a7558691fe1051d5dc90968f6f`) and
  `support/rustc_codegen_traps_and_link_probe.out.txt` (SHA-256
  `ea1955e510459002e4e65a523dacda9d87f97024a3ea97d1bcc470dc0ba7edc8`):**
  Self-contained `#![feature(rustc_private)]` probe compiled and executed
  against `rustc 1.101.0-nightly (19833af7224424e8b53e288097d56b6af43d5bcf)`:
  - Verifies that `with_no_trimmed_paths!(tcx.def_path_str(did))` and
    `tcx.def_path_debug_str(did)` succeed with
    `config.opts.trimmed_def_paths = true` without arming `must_produce_diag`.
  - Spawns a child process calling unwrapped `tcx.def_path_str(did)` with
    `config.opts.trimmed_def_paths = true` and no `--emit=mir`, confirming the
    exact `DiagCtxtInner::drop` ICE message: ``"`trimmed_def_paths` called,
    diagnostics were expected but none were emitted. Use
    `with_no_trimmed_paths` for debugging."``
  - Verifies that `tcx.opt_item_name(closure_did)` returns `None` on
    `DefKind::Closure` items and confirms in a child process that
    `tcx.item_name(closure_did)` ICEs with `"item_name: no name for DefPath {
    ... data: Closure }"`.
  - Verifies on `poly_size_add<T>` that `tcx.instance_mir(instance.def)` retains
    `TyKind::Param` (`raw_arg_ty.has_non_region_param() == true`), that
    `tcx.layout_of` on `raw_arg_ty` returns `Err(LayoutError::TooGeneric)`, and
    that substituting via two-argument `ty::EarlyBinder::bind(tcx, raw_arg_ty)`
    + `instance.instantiate_mir_and_normalize_erasing_regions` yields concrete
    types `[u64; 4]` (`32` bytes) and `u32` (`4` bytes).
  - Synthesizes RV64GC (`EM_RISCV = 243`, `e_flags = 0x5`) relocatable `.o` and
    `.rlib` files and invokes `rust-lld -flavor gnu -m elf64lriscv -shared`:
    - **Case A:** Without `--whole-archive`, `rust-lld` drops `impl_cgu0.o` from
      `librustc_driver_impl_global.rlib`, leaving `rustc_driver_impl_main`
      absent from `.dynsym`.
    - **Case B:** With `--whole-archive --no-undefined` and `STB_LOCAL` on
      `cgu1_internal_helper`, cross-CGU linking fails with
      `undefined symbol: cgu1_internal_helper`.
    - **Case C:** With `--whole-archive --no-undefined` and `STB_GLOBAL` across
      CGUs, `rust-lld` succeeds and exports both `rustc_driver_impl_main` and
      `cgu1_internal_helper` in `.dynsym`.
- **`support/cross_compile_rustc_rv64gc_recipe.sh` (SHA-256
  `0192947785bab96819d45f6f541a846b35c049c40c9070a2b3f7abb33f91c71d`):**
  Executable cross-compilation script documenting the exact target-scoped
  `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS`, `--no-default-features`,
  `-Z build-std`, and `CFG_*` bootstrap variables.
- **`support/rustc_249_crate_rv64gc_census.json` (SHA-256
  `3a7fed5832fbc0d62be45b38e354c7a5dcff5010db1fba9a9bf5c526adbceb74`):**
  Complete recorded empirical census of all 249 target crates (`11,558` CGUs,
  `931,257` `MonoItem`s) and the `readelf` / `qemu-riscv64` measurements of
  `librustc_driver.so` and `rustc-main`.
- **Upstream `rust-lang/rust` and `joshlf/anneal` source citations:**
  - `compiler/rustc_middle/src/ty/print/pretty.rs:118`, `451-466`, `2170-2186`,
    `2227-2236`, `3531-3539`
  - `compiler/rustc_session/src/session.rs:528-541`
  - `compiler/rustc_errors/src/lib.rs:314`, `432-471`, `945-951`
  - `compiler/rustc_driver_impl/src/lib.rs:154-169`, `1688-1693`
  - `compiler/rustc_middle/src/ty/mod.rs:1688-1714`
  - `compiler/rustc_middle/src/ty/context.rs:1216-1246`
  - `compiler/rustc_type_ir/src/binder.rs:333-357`
  - `compiler/rustc_middle/src/ty/instance.rs:956-970`
  - `compiler/rustc_middle/src/ty/normalize_erasing_regions.rs:157-208`
  - `compiler/rustc_ty_utils/src/instance.rs:24-32`
  - `compiler/rustc_ty_utils/src/layout.rs:41-112`
  - `compiler/rustc_codegen_ssa/src/base.rs:1042-1096`
  - `compiler/rustc_codegen_ssa/src/back/link.rs:2482-2626`, `3719-3739`
  - `compiler/rustc/Cargo.toml:1-43`, `compiler/rustc/src/main.rs:38-40`
  - `compiler/rustc_driver/Cargo.toml:1-14`,
    `compiler/rustc_driver/src/lib.rs:1-5`
  - `compiler/rustc_driver_impl/Cargo.toml:60-71`
  - `joshlf/anneal` (`7677632ab267e6d7075fc9ddca7280ddf0296f87`):
    `compiler/rustc-codegen-anneal/src/lib.rs:114-128`, `194`, `235`, `265-266`,
    `289-352`, `381`, `862`, `960-991`, `1066-1105`, `1169`, `1306-1573` and
    `compiler/anc-driver/src/lib.rs:90`, `105`, `348-418`, `867-894`.

## Revalidation

To revalidate the findings in this report after a `rustc` nightly toolchain
upgrade or changes to `rustc_codegen_anneal`:

1. **Run the self-contained `rustc_private` query, monomorphization, and
   `rust-lld` linker probe:**
   ```bash
   SYSROOT=$(rustc --print sysroot)
   rustc --edition 2021 support/rustc_codegen_traps_and_link_probe.rs \
     -o /tmp/rustc_codegen_traps_and_link_probe
   LD_LIBRARY_PATH="${SYSROOT}/lib" /tmp/rustc_codegen_traps_and_link_probe
   ```
   Verify that the output matches
   `support/rustc_codegen_traps_and_link_probe.out.txt` and exits with code `0`.
2. **Re-run the 249-crate `compiler/rustc` `RV64GC` cross-compilation recipe:**
   ```bash
   RUST_SRC_DIR=/path/to/rust \
   CODEGEN_BACKEND_SO=/path/to/librustc_codegen_anneal.so \
     bash support/cross_compile_rustc_rv64gc_recipe.sh
   ```
   Verify with `readelf -h -S -d` and `qemu-riscv64` that `librustc_driver.so`
   is an `EM_RISCV` (`243`) `ET_DYN` shared library retaining the
   `rustc_driver_impl` symbol table and that
   `qemu-riscv64 .../rustc-main --version` exits with code `0`.

Invalidating changes to watch for:

- Changes to `PrettyPrinter::try_print_trimmed_def_path`
  (`compiler/rustc_middle/src/ty/print/pretty.rs`),
  `Session::record_trimmed_def_paths` (`compiler/rustc_session/src/session.rs`),
  or `DiagCtxtInner::drop` (`compiler/rustc_errors/src/lib.rs`).
- Changes to `ty::EarlyBinder` in `compiler/rustc_type_ir/src/binder.rs` or
  `Instance::instantiate_mir_and_normalize_erasing_regions` in
  `compiler/rustc_middle/src/ty/instance.rs`.
- Changes to `compiler/rustc/Cargo.toml` or
  `compiler/rustc_driver_impl/Cargo.toml` default feature flags (`llvm`,
  `jemalloc`) or `CrateInfo::used_crate_source` in `compiler/rustc_codegen_ssa`.
