// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Compiler observation, complete inventory, and exact input reads. The host
//! authenticates the compiler/sysroot distribution and stages declared inputs;
//! these checks do not defend against a compromised execution environment.

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use rustc_abi::Endian;
use rustc_ast::{Attribute, Crate, MetaItem, MetaItemInner};
use rustc_data_structures::steal::Steal;
use rustc_driver::Compilation;
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::{CrateType, Options};
use rustc_span::def_id::LocalDefId;
use rustc_span::source_map::{FileLoader, RealFileLoader};
use rustc_span::{FileName, sym};

use crate::{Args, Failure, extract, identity, ir};

// rustc query providers are function pointers, so the hook cannot borrow a
// callback instance. These cells hold one process's session authority and owned
// snapshots. They are initialized once before queries and never reused for a
// second capture, avoiding stale bodies or selectors from another compilation.
type Provider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<mir::Body<'tcx>>;
static DEFAULT_PROVIDER: OnceLock<Provider> = OnceLock::new();
static SELECTION: OnceLock<ir::Scope> = OnceLock::new();
static CAPTURED: Mutex<BTreeMap<u32, extract::Result<ir::Body>>> = Mutex::new(BTreeMap::new());

/// The query returns `Steal<Body>` and later queries consume it. Call the
/// original provider, copy the admitted syntax while it is available, and
/// return the exact original result. The compiler explicitly supports this:
/// "can be overridden by custom rustc drivers".
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/lib.rs#L567-L598
///
/// Early snapshots do not decide coverage. The independent compiler census is
/// enumerated in full before selecting or assembling any output program.
fn hook<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<mir::Body<'tcx>> {
    let provider = DEFAULT_PROVIDER
        .get()
        .expect("provider installed before queries");
    let original = provider(tcx, def);
    let selection = SELECTION.get().expect("selection installed before queries");
    let matches_scope = match selection {
        ir::Scope::Crate => true,
        ir::Scope::SelectedUnit { roots } => roots.contains(&tcx.def_path_str(def)),
    };
    if callable(tcx.def_kind(def)) && matches_scope {
        let result = extract::body(tcx, def, &original.borrow());
        CAPTURED
            .lock()
            .expect("capture mutex poisoned")
            .insert(def.local_def_index.as_u32(), result);
    }
    original
}

fn override_queries(_: &rustc_session::Session, providers: &mut Providers) {
    DEFAULT_PROVIDER
        .set(providers.queries.mir_drops_elaborated_and_const_checked)
        .expect("one compiler session per capture process");
    providers.queries.mir_drops_elaborated_and_const_checked = hook;
}

#[derive(Default)]
struct Reads {
    files: BTreeMap<PathBuf, ir::SourceFile>,
    refusals: Vec<String>,
    tool_errors: Vec<String>,
}

struct RecordingLoader {
    reads: Arc<Mutex<Reads>>,
    allowed: BTreeSet<PathBuf>,
    directories: BTreeSet<PathBuf>,
}

impl RecordingLoader {
    fn new(reads: Arc<Mutex<Reads>>, allowed: BTreeSet<PathBuf>) -> Self {
        // Directories are derived authority, not another ambient inventory.
        // Requiring every original parent prefix preserves normal ../ lookup
        // through declared ancestors without admitting missing/../file when an
        // unrelated ambient directory happens to appear.
        let directories = allowed
            .iter()
            .flat_map(|path| path.ancestors().skip(1).map(Path::to_path_buf))
            .collect();
        Self {
            reads,
            allowed,
            directories,
        }
    }

    /// Resolve within the declared file-and-ancestor namespace. The standard
    /// normalizer works "without traversing the filesystem" and warns that
    /// lexical .. can differ when an intermediate component is a symlink.
    /// Check every parent prefix against derived directories, then open only
    /// the admitted normalized name. Neither missing prefixes nor undeclared
    /// aliases may acquire authority from ambient filesystem state.
    /// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/library/std/src/path.rs#L3407-L3422
    ///
    /// This is a configured source namespace, not evidence that undeclared
    /// alternatives were absent in the original tree. The CLI stages regular
    /// files; direct capture callers must keep declared canonical inputs and
    /// their ancestors unchanged throughout the compiler session. These checks
    /// do not make filesystem mutation by a compromised host atomic or safe.
    fn lookup(&self, path: &Path) -> io::Result<PathBuf> {
        let absolute = std::path::absolute(path)?;
        for parent in absolute.ancestors().skip(1) {
            let parent = parent.normalize_lexically().map_err(io::Error::other)?;
            if !self.directories.contains(&parent) {
                return Err(io::Error::other("undeclared source directory"));
            }
        }
        let path = absolute.normalize_lexically().map_err(io::Error::other)?;
        if !self.allowed.contains(&path) {
            return Err(io::Error::other("undeclared source filename"));
        }
        // Membership must precede filesystem queries: even a symlink to an
        // allowed target is invisible under an undeclared name. The canonical
        // name itself must still denote the declared regular file.
        if path.canonicalize()? != path || !path.is_file() {
            return Err(io::Error::other(
                "declared source is not a canonical regular file",
            ));
        }
        Ok(path)
    }

    fn read_path(&self, path: &Path) -> io::Result<PathBuf> {
        match self.lookup(path) {
            Ok(path) => Ok(path),
            Err(cause) => {
                let error = format!("undeclared compiler read: {}: {cause}", path.display());
                // Missing module candidates are normal negative probes. An
                // actual denied read is different: compiler recovery must not
                // publish a capture after handling this I/O error.
                let mut reads = self
                    .reads
                    .lock()
                    .map_err(|_| io::Error::other("input read mutex poisoned"))?;
                reads.refusals.push(error.clone());
                Err(io::Error::other(error))
            }
        }
    }

    fn record(&self, path: &Path, bytes: &[u8], read_kind: &'static str) -> io::Result<()> {
        let path = path.canonicalize()?;
        let mut reads = self
            .reads
            .lock()
            .map_err(|_| io::Error::other("input read mutex poisoned"))?;
        // Membership, not an empty-list convention, authorizes the read. Keep
        // refusals separately so a compiler recovery path cannot turn a denied
        // input into success merely by handling the loader's I/O error.
        if !self.allowed.contains(&path) {
            let error = format!("undeclared compiler read: {}", path.display());
            reads.refusals.push(error.clone());
            return Err(io::Error::other(error));
        }
        let sha256 = identity::sha256_bytes(bytes);
        if let Some(previous) = reads.files.get(&path) {
            if previous.sha256 != sha256 {
                let error = format!("input changed between compiler reads: {}", path.display());
                reads.refusals.push(error.clone());
                return Err(io::Error::other(error));
            }
        } else {
            reads.files.insert(
                path.clone(),
                ir::SourceFile {
                    path,
                    sha256,
                    read_kind,
                },
            );
        }
        Ok(())
    }
}

/// Hash the exact bytes returned to rustc, before SourceMap normalization.
/// `FileLoader::read_file` must "return a String because we normalize source
/// files"; binary inputs have a separate read method and are recorded too.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/source_map.rs#L81-L96
impl FileLoader for RecordingLoader {
    fn file_exists(&self, path: &Path) -> bool {
        // FileLoader asks to "Query the existence of a file." rustc probes
        // both name.rs and name/mod.rs and rejects two visible candidates.
        // Answer in the same closed namespace as reads: ambient alternatives
        // must not change module choice or ambiguity without a declaration.
        // A negative probe is not a refused read and needs no recorded input.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/source_map.rs#L81-L84
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_expand/src/module.rs#L246-L264
        self.lookup(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        let path = self.read_path(path)?;
        let text = RealFileLoader.read_file(&path)?;
        self.record(&path, text.as_bytes(), "text")?;
        Ok(text)
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        let path = self.read_path(path)?;
        let bytes = RealFileLoader.read_binary_file(&path)?;
        self.record(&path, &bytes, "binary")?;
        Ok(bytes)
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        RealFileLoader.current_directory()
    }
}

fn callable(kind: DefKind) -> bool {
    matches!(kind, DefKind::Fn | DefKind::AssocFn)
}

// Census policy is independent of successful body translation. Rust calls
// `hir_body_owners` an iterator over "all body-owners in this crate". Every
// such owner is required, including closures and anonymous/inline constants.
// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/hir/map.rs#L362-L367
//
// Functions (including declarations), statics, named constants, datatype and
// trait/impl owners, and global assembly also require explicit admission even
// without a HIR body. The initial adapter rejects unsupported owners instead
// of silently dropping their contracts or layout obligations.
//
// Other definitions describe names, parameters, or components of these owners;
// absent a body they add no separate obligation in this adapter. In particular,
// `Ctor` "Refers to the struct or enum variant's constructor", while the type
// owner is separately required. Unused `AnonConst` entries can be "unused and
// incomplete", with queries that "ICE when using this `DefId`". Use the body
// inventory rather than demanding a body query from every definition.
// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/def.rs#L99-L205
//
// Keep this match exhaustive: a compiler upgrade must classify each new kind.
fn required(kind: DefKind, has_body: bool) -> bool {
    match kind {
        DefKind::Fn
        | DefKind::AssocFn
        | DefKind::Static { .. }
        | DefKind::Const { .. }
        | DefKind::AssocConst { .. }
        | DefKind::Struct
        | DefKind::Enum
        | DefKind::Union
        | DefKind::Trait
        | DefKind::Impl { .. }
        | DefKind::GlobalAsm => true,
        DefKind::Mod
        | DefKind::Variant
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::ConstParam
        | DefKind::Ctor(..)
        | DefKind::Macro(..)
        | DefKind::ExternCrate
        | DefKind::Use
        | DefKind::ForeignMod
        | DefKind::AnonConst
        | DefKind::InlineConst
        | DefKind::OpaqueTy
        | DefKind::Field
        | DefKind::LifetimeParam
        | DefKind::Closure
        | DefKind::SyntheticCoroutineBody => has_body,
    }
}

// Required does not mean supported. Whole-crate capture must admit every
// required owner, including owners with no runtime body. A fieldless enum
// without explicit discriminant `AnonConst`s is admitted via the type adapter;
// no callable body is fabricated for it. All `AnonConst` items (including
// explicit enum discriminants) and other required owner classes remain
// explicit refusals in whole-crate scope. A callable with a body is only a
// candidate here: `collect` publishes it only if `extract::body` translates
// it, and that translation also refuses intrinsics, unsupported entry
// conditions, and unmodeled codegen attributes such as `#[linkage]`.
fn whole_crate_item(tcx: TyCtxt<'_>, def: LocalDefId, has_body: bool) -> extract::Result<()> {
    match tcx.def_kind(def) {
        DefKind::Fn | DefKind::AssocFn if has_body => Ok(()),
        // `instantiate_identity` "Makes the identity replacement
        // `T0 => T0, ..., TN => TN`", so a generic enum keeps its own
        // parameters and `extract::ty` refuses it. The enum's own type has no
        // projection for normalization to resolve.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/binder.rs#L665-L673
        DefKind::Enum => {
            extract::ty(tcx, tcx.type_of(def).instantiate_identity().skip_norm_wip()).map(|_| ())
        }
        other => Err(format!("whole-crate obligation is unsupported: {other:?}")),
    }
}

struct Callbacks<'a> {
    args: &'a Args,
    verified_sysroot: &'a Path,
    scope: &'a ir::Scope,
    reads: Arc<Mutex<Reads>>,
    result: Option<Result<ir::Manifest, Failure>>,
}

impl rustc_driver::Callbacks for Callbacks<'_> {
    fn config(&mut self, config: &mut interface::Config) {
        crate::driver::configure(config);
        if let Err(reason) = validate_compiler_options(&config.opts) {
            if let Ok(mut reads) = self.reads.lock() {
                reads.tool_errors.push(reason.clone());
            }
            EarlyDiagCtxt::new(config.opts.error_format).early_fatal(reason);
        }
        config.override_queries = Some(override_queries);
        config.file_loader = Some(Box::new(RecordingLoader::new(
            self.reads.clone(),
            self.args.source_file.iter().cloned().collect(),
        )));
    }

    fn after_crate_root_parsing(
        &mut self,
        _: &interface::Compiler,
        krate: &mut Crate,
    ) -> Compilation {
        // Reject `#![crate_type]` and `#![feature(rustc_private)]` (including
        // under `#![cfg_attr]`) before macro expansion so sysroot `rustc-dev`
        // proc-macro dylibs can never load or execute.
        if let Err(reason) = validate_crate_root_attrs(&krate.attrs) {
            if let Ok(mut reads) = self.reads.lock() {
                reads.refusals.push(reason);
            }
            return Compilation::Stop;
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some(collect(
            tcx,
            self.args,
            self.verified_sysroot,
            self.scope,
            &self.reads,
        ));
        // Continue through metadata/object emission and rustc's final check.
        // A candidate manifest is published only after the session returns
        // successfully, so errors after this callback still prohibit capture.
        // `run_compiler` finishes with "sess.dcx().abort_if_errors()".
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/interface.rs#L491-L509
        Compilation::Continue
    }
}

fn validate_crate_root_meta(meta: &MetaItem) -> Result<(), String> {
    let last_ident = meta.path.segments.last().map(|seg| seg.ident.name);
    if last_ident == Some(sym::crate_type) {
        return Err("crate-level #![crate_type] attributes are unsupported during capture".into());
    }
    if last_ident == Some(sym::feature)
        && let Some(items) = meta.meta_item_list()
    {
        for item in items {
            if item.has_name(sym::rustc_private) {
                return Err("#![feature(rustc_private)] is unsupported during capture".into());
            }
        }
    }
    if last_ident == Some(sym::cfg_attr)
        && let Some(items) = meta.meta_item_list()
    {
        for item in items.iter().skip(1) {
            if let MetaItemInner::MetaItem(nested) = item {
                validate_crate_root_meta(nested)?;
            }
        }
    }
    Ok(())
}

fn validate_crate_root_attrs(attrs: &[Attribute]) -> Result<(), String> {
    for attr in attrs {
        if let Some(meta) = attr.meta() {
            validate_crate_root_meta(&meta)?;
        } else if attr.has_name(sym::crate_type) {
            return Err(
                "crate-level #![crate_type] attributes are unsupported during capture".into(),
            );
        }
    }
    Ok(())
}

fn validate_compiler_args(compiler_args: &[String]) -> Result<(), Failure> {
    for arg in compiler_args {
        if arg.starts_with('@') {
            return Err(Failure::tool(
                "response-file arguments are forbidden during capture",
            ));
        }
        if arg == "--extern" || arg.starts_with("--extern=") || arg == "-L" || arg.starts_with("-L")
        {
            return Err(Failure::tool(format!(
                "external crate and library search arguments are forbidden: {arg}"
            )));
        }
        if arg == "--crate-type"
            || (arg.starts_with("--crate-type=")
                && !matches!(arg.as_str(), "--crate-type=lib" | "--crate-type=rlib"))
        {
            return Err(Failure::tool(format!(
                "unsupported crate type during capture: {arg}"
            )));
        }
    }
    Ok(())
}

fn validate_compiler_options(opts: &Options) -> Result<(), String> {
    if opts.externs.iter().next().is_some() {
        return Err("external crate flags (--extern) are forbidden during capture".into());
    }
    if !opts.search_paths.is_empty() {
        return Err("library search path flags (-L) are forbidden during capture".into());
    }
    if opts.crate_types.is_empty()
        || !opts
            .crate_types
            .iter()
            .all(|ct| matches!(ct, CrateType::Rlib))
    {
        return Err("proc-macro and non-library crate types are unsupported during capture".into());
    }
    Ok(())
}

fn collect_sysroot_lib_identities(
    sysroot: &Path,
    target: &str,
) -> Result<BTreeSet<(u64, u64)>, Failure> {
    let target_lib = sysroot.join("lib/rustlib").join(target).join("lib");
    if !target_lib.is_dir() {
        return Err(Failure::tool(format!(
            "target sysroot library directory missing: {}",
            target_lib.display()
        )));
    }
    let mut allowed = BTreeSet::new();
    let entries = std::fs::read_dir(&target_lib).map_err(Failure::io)?;
    for entry in entries {
        let entry = entry.map_err(Failure::io)?;
        if let Ok(dev_ino) = identity::regular_file_dev_ino(&entry.path()) {
            allowed.insert(dev_ino);
        }
    }
    if allowed.is_empty() {
        return Err(Failure::tool(format!(
            "no target libraries found in sysroot {}",
            target_lib.display()
        )));
    }
    Ok(allowed)
}

fn admit_external_crate<F>(
    crate_name: &str,
    macros_only: bool,
    has_dylib: bool,
    has_sdylib: bool,
    paths: &[&Path],
    allowed_sysroot_ids: &BTreeSet<(u64, u64)>,
    stat_dev_ino: F,
) -> Result<(), Failure>
where
    F: Fn(&Path) -> io::Result<(u64, u64)>,
{
    if macros_only || crate_name == "proc_macro" {
        return Err(Failure::unsupported(format!(
            "proc-macro or macro-only crate is unsupported: {crate_name}"
        )));
    }
    if has_dylib {
        return Err(Failure::unsupported(format!(
            "dynamic library or proc-macro crate is unsupported: {crate_name}"
        )));
    }
    if has_sdylib {
        return Err(Failure::unsupported(format!(
            "sdylib interface crate is unsupported: {crate_name}"
        )));
    }
    if paths.is_empty() {
        return Err(Failure::unsupported(format!(
            "external crate lacks a resolved artifact path: {crate_name}"
        )));
    }
    for path in paths {
        let dev_ino = stat_dev_ino(path).map_err(|error| {
            Failure::tool(format!(
                "cannot stat artifact for crate {crate_name} at {}: {error}",
                path.display()
            ))
        })?;
        if !allowed_sysroot_ids.contains(&dev_ino) {
            return Err(Failure::unsupported(format!(
                "external crate {crate_name} resolved outside target sysroot: {}",
                path.display()
            )));
        }
    }
    Ok(())
}

/// Defense-in-depth sysroot-only and no-proc-macro gate run in
/// `after_analysis`.
fn verify_sysroot_only_crates(
    tcx: TyCtxt<'_>,
    sysroot: &Path,
    target: &str,
) -> Result<(), Failure> {
    let crate_types = tcx.crate_types();
    if crate_types.is_empty() || !crate_types.iter().all(|ct| matches!(ct, CrateType::Rlib)) {
        return Err(Failure::unsupported(
            "proc-macro and non-library crates are unsupported during capture",
        ));
    }
    if tcx.hir_krate_attrs().iter().any(|attr| {
        matches!(
            attr,
            rustc_hir::Attribute::Parsed(rustc_hir::attrs::AttributeKind::CrateType(_))
        ) || attr.has_name(rustc_span::sym::crate_type)
    }) {
        return Err(Failure::unsupported(
            "crate-level #![crate_type] attributes are unsupported during capture",
        ));
    }
    if tcx.proc_macro_decls_static(()).is_some() {
        return Err(Failure::unsupported(
            "proc-macro declarations are unsupported during capture",
        ));
    }
    if tcx.sess.opts.externs.iter().next().is_some() || !tcx.sess.opts.search_paths.is_empty() {
        return Err(Failure::tool(
            "external crate flags and search paths are forbidden during capture",
        ));
    }
    let allowed_ids = collect_sysroot_lib_identities(sysroot, target)?;
    for &cnum in tcx.crates(()) {
        let crate_name = tcx.crate_name(cnum);
        let dep_kind = tcx.crate_dep_kind(cnum);
        let source = tcx.used_crate_source(cnum);
        let extern_paths = tcx.crate_extern_paths(cnum);
        let mut paths: Vec<&Path> = source.paths().map(PathBuf::as_path).collect();
        for path in extern_paths {
            if !paths.contains(&path.as_path()) {
                paths.push(path.as_path());
            }
        }
        admit_external_crate(
            crate_name.as_str(),
            dep_kind.macros_only(),
            source.dylib.is_some(),
            source.sdylib_interface.is_some(),
            &paths,
            &allowed_ids,
            identity::regular_file_dev_ino,
        )?;
    }
    Ok(())
}

fn collect(
    tcx: TyCtxt<'_>,
    args: &Args,
    verified_sysroot: &Path,
    scope: &ir::Scope,
    reads: &Arc<Mutex<Reads>>,
) -> Result<ir::Manifest, Failure> {
    // `has_errors` "excludes delayed bugs". `run_compiler` flushes those after
    // the callbacks return and panics if any exist without an emitted error;
    // `catch_fatal_errors` resumes that non-fatal unwind, so `run_capture`
    // reports a failed capture.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_errors/src/lib.rs#L723-L726
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/interface.rs#L511-L515
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_errors/src/lib.rs#L1477-L1478
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/fatal_error.rs#L33-L41
    if tcx.dcx().has_errors().is_some() {
        return Err(Failure::compiler("compiler diagnostics prohibit capture"));
    }
    // `pointer_size` is the compiler's "pointer size in the default data
    // address space". `endian` is the "Endianness of the target, which must
    // match cfg(target-endian)", set to `Endian::Little` by the data-layout
    // specification `"e"`. The owned syntax fixes both that width and
    // endianness; neither a host-width guess nor a target-name heuristic
    // supplies them.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L674-L678
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L259-L260
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L444
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L752-L756
    if tcx.data_layout.pointer_size().bits() != 64 || tcx.data_layout.endian != Endian::Little {
        return Err(Failure::unsupported(
            "only 64-bit little-endian targets are modeled",
        ));
    }
    let sysroot = tcx
        .sess
        .opts
        .sysroot
        .path()
        .canonicalize()
        .map_err(Failure::io)?;
    if sysroot != verified_sysroot {
        return Err(Failure::tool(
            "compiler session sysroot diverged from verified sysroot",
        ));
    }
    verify_sysroot_only_crates(tcx, verified_sysroot, &args.target)?;
    // "Defined lang items can come from the current crate or its dependencies."
    // Only the pinned sysroot may supply them for the scalar profile.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L24-L67
    if tcx.lang_items().iter().any(|(_, def)| def.is_local()) {
        return Err(Failure::unsupported(
            "crate-local language items are unsupported",
        ));
    }

    // `iter_local_def_id` finishes analysis and visits all definitions,
    // including definitions created during enumeration: "Recompute the number
    // of definitions each time, because our caller may be creating new ones."
    // `hir_body_owners` independently identifies bodies, including uncalled and
    // unsupported ones. Neither list comes from walking successfully translated
    // selected bodies.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/context.rs#L1353-L1371
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/hir/map.rs
    let body_owners: BTreeSet<_> = tcx
        .hir_body_owners()
        .map(|def| def.local_def_index.as_u32())
        .collect();
    let mut found = BTreeSet::new();
    let mut census = Vec::new();
    let mut selected_defs = Vec::new();
    let mut unsupported = Vec::new();
    // `extract::ty` admits only crate-local enums and keys each one by
    // `extract::enum_id`, so every emitted `EnumTy.id` belongs to a definition
    // visited here. Refusing a key shared by two local enum definitions,
    // whether or not either is captured, makes each emitted key denote one
    // enum. Distinct definitions can share a key through digest truncation or
    // an identical printed path.
    let mut enum_ids = BTreeMap::new();
    for def in tcx.iter_local_def_id() {
        let path = tcx.def_path_str(def);
        let kind = tcx.def_kind(def);
        if matches!(kind, DefKind::Enum) {
            let id = extract::enum_id(tcx, def.to_def_id());
            if let Some(previous) = enum_ids.insert(id, def) {
                return Err(Failure::unsupported(format!(
                    "enum identity collision: {} and {path} share id {id}",
                    tcx.def_path_str(previous)
                )));
            }
        }
        let has_body = body_owners.contains(&def.local_def_index.as_u32());
        let is_required = required(kind, has_body);
        // Selected-unit claims cover only the requested callable bodies. Keep
        // every other item visible in the census without pretending to verify
        // it. Whole-crate mode instead requires admission of every required
        // item, so an unsupported owner cannot disappear with its body.
        let selected = match scope {
            ir::Scope::Crate => is_required,
            ir::Scope::SelectedUnit { roots } => {
                let matched = roots.contains(&path);
                if matched {
                    found.insert(path.clone());
                }
                matched
            }
        };
        census.push(ir::CensusItem {
            def_id: def.local_def_index.as_u32(),
            path: path.clone(),
            kind: format!("{kind:?}"),
            has_body,
            selected,
            required: is_required,
        });
        if !selected {
            continue;
        }
        let admission = match scope {
            ir::Scope::Crate => whole_crate_item(tcx, def, has_body),
            ir::Scope::SelectedUnit { .. } if callable(kind) && has_body => Ok(()),
            ir::Scope::SelectedUnit { .. } => {
                Err("selected roots must be callable definitions with bodies".into())
            }
        };
        match admission {
            Ok(()) if callable(kind) => selected_defs.push(def),
            Ok(()) => {}
            Err(reason) => unsupported.push(ir::Unsupported {
                def_id: def.local_def_index.as_u32(),
                path,
                reason,
            }),
        }
    }
    if let ir::Scope::SelectedUnit { roots } = scope
        && &found != roots
    {
        return Err(Failure::unsupported(format!(
            "selected definitions not found: {:?}",
            roots.difference(&found).collect::<Vec<_>>()
        )));
    }
    // A provider is only called when a query is demanded. Force every selected
    // body before code generation, with no incremental cache or fallback to
    // optimized MIR. The hook records bodies before later stealing. The query
    // is declared `no_hash` without `cache_on_disk_if`, and capture passes no
    // `-Cincremental`, so no stored result can stand in for the provider call.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/queries.rs#L638-L641
    let mut bodies = Vec::new();
    let mut selected = Vec::new();
    for def in selected_defs {
        let key = def.local_def_index.as_u32();
        let _ = tcx.mir_drops_elaborated_and_const_checked(def);
        let result = CAPTURED
            .lock()
            .map_err(|_| Failure::tool("capture mutex poisoned"))?
            .get(&key)
            .cloned()
            .unwrap_or_else(|| Err("compiler did not provide Runtime(PostCleanup) MIR".into()));
        match result {
            Ok(body) => {
                selected.push(ir::SelectedBody {
                    def_id: key,
                    path: tcx.def_path_str(def),
                    body_index: bodies.len(),
                });
                bodies.push(body);
            }
            Err(reason) => unsupported.push(ir::Unsupported {
                def_id: key,
                path: tcx.def_path_str(def),
                reason,
            }),
        }
    }
    if tcx.dcx().has_errors().is_some() {
        return Err(Failure::compiler(
            "late compiler diagnostics prohibit capture",
        ));
    }
    if !unsupported.is_empty() {
        return Err(Failure::unsupported_items(unsupported));
    }
    // The manifest binds file bytes and explicit flags, not ambient environment
    // values. rustc records "Environment variables accessed during the build
    // and their values when they exist"; accepting these would leave part of
    // the compilation subject outside the input binding. `env!` and
    // `option_env!` both insert `(var, value.as_ref().ok().copied())`, so an
    // absent variable is recorded too: setting it would change the expansion.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L155-L159
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_builtin_macros/src/env.rs#L54-L55
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_builtin_macros/src/env.rs#L133-L134
    if !tcx.sess.env_depinfo.borrow().is_empty() {
        return Err(Failure::unsupported(
            "environment-dependent source inputs are unsupported",
        ));
    }
    let reads = reads
        .lock()
        .map_err(|_| Failure::tool("input read mutex poisoned"))?;
    // Cross-check rustc's input inventories against the loader instead of
    // assuming that installing a loader intercepted every source dependency.
    // Imported source-map entries describe precompiled dependency source;
    // authenticating that distribution belongs to the host, while local source
    // reads must all have records here. `is_imported` is
    // `self.src.is_none()`, and external crates "will have a `None` value as
    // `self.src`". `FileName` "Differentiates between real files and common
    // virtual files"; `local_path` returns "the path suitable for reading from
    // the file system on the local host, if this information exists."
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/lib.rs#L2358-L2361
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/lib.rs#L1934-L1936
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/lib.rs#L505-L508
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_span/src/lib.rs#L387-L394
    for file in tcx.sess.source_map().files().iter() {
        if file.is_imported() {
            continue;
        }
        let FileName::Real(real) = &file.name else {
            return Err(Failure::unsupported(
                "non-file compiler source input is unsupported",
            ));
        };
        let path = real
            .local_path()
            .ok_or_else(|| Failure::unsupported("source input lacks a local path"))?
            .canonicalize()
            .map_err(Failure::io)?;
        if !reads.files.contains_key(&path) {
            return Err(Failure::unsupported(format!(
                "source input bypassed read recording: {}",
                path.display()
            )));
        }
    }
    // SourceMap alone is insufficient: rustc also records "File paths accessed
    // during the build". Binary include inputs must have the same byte binding
    // as textual source, even when they have no source-map entry.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L158-L159
    for file in tcx.sess.file_depinfo.borrow().iter() {
        let path = Path::new(file.as_str())
            .canonicalize()
            .map_err(Failure::io)?;
        if !reads.files.contains_key(&path) {
            return Err(Failure::unsupported(format!(
                "dependency input bypassed read recording: {}",
                path.display()
            )));
        }
    }
    check_current_inputs(&reads)?;
    let program = ir::Program::try_new(scope.clone(), bodies).map_err(Failure::unsupported)?;
    Ok(ir::Manifest {
        schema_version: ir::SCHEMA_VERSION,
        compiler: ir::Compiler {
            commit: ir::COMPILER_COMMIT,
            version: ir::COMPILER_VERSION,
            sysroot,
        },
        configuration: ir::Configuration {
            crate_root: args.crate_root.clone(),
            crate_name: args.crate_name.clone(),
            edition: args.edition.clone(),
            target: args.target.clone(),
            cfg: args.cfg.clone(),
            opt_level: 0,
            debug_assertions: false,
            overflow_checks: false,
            pointer_bits: 64,
            endian: "little",
            declared_source_files: args.source_file.clone(),
        },
        source_files: reads.files.values().cloned().collect(),
        census,
        selected,
        unsupported,
        program,
    })
}

// The compiler continues through object emission after analysis. Recheck the
// observed bytes after that work as well as when constructing the manifest.
fn check_current_inputs(reads: &Reads) -> Result<(), Failure> {
    for file in reads.files.values() {
        let current = std::fs::read(&file.path).map_err(Failure::io)?;
        if identity::sha256_bytes(&current) != file.sha256 {
            return Err(Failure::unsupported(format!(
                "compiler input changed after reading: {}",
                file.path.display()
            )));
        }
    }
    Ok(())
}

pub fn run(args: &Args, verified_sysroot: &Path) -> Result<ir::Manifest, Failure> {
    let scope = args.resolved_scope()?;
    SELECTION
        .set(scope.clone())
        .map_err(|_| Failure::tool("one capture invocation per process is required"))?;
    let mut compiler_args = vec![
        "anneal-rustc-capture".into(),
        compiler_path(&args.crate_root)?.to_string(),
        "--crate-type=lib".into(),
        format!("--crate-name={}", args.crate_name),
        format!("--edition={}", args.edition),
        format!("--target={}", args.target),
        // Metadata alone skips monomorphization and can miss a failing generic
        // inline constant. rustc skips crate items when `should_codegen` is
        // false: "Skip crate items and just output metadata in -Z no-codegen
        // mode." Request object output to reach normal code generation without
        // a linker; these outputs stay in the private publication staging area.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/passes.rs#L1308-L1318
        //
        // The collector says: "Always visit all `required_consts`, so that we
        // evaluate them and abort compilation if any of them errors."
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_monomorphize/src/collector.rs#L1347-L1353
        "--emit=metadata,obj".into(),
        // This explicit profile belongs to the captured configuration, rather
        // than inheriting Cargo or host defaults. rustc says debug-assertions
        // controls "cfg(debug_assertions)" and overflow-checks controls
        // "runtime integer overflow". This subject uses both disabled; explicit
        // MIR checks are still translated or refused, never silently removed.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/src/doc/rustc/src/codegen-options/index.md#L65-L76
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/src/doc/rustc/src/codegen-options/index.md#L463-L474
        "-Copt-level=0".into(),
        "-Cdebug-assertions=no".into(),
        "-Coverflow-checks=no".into(),
        format!("--out-dir={}", compiler_path(&args.out_dir)?),
    ];
    if let Some(sysroot) = &args.sysroot {
        compiler_args.push(format!("--sysroot={}", compiler_path(sysroot)?));
    }
    // The pinned driver expands argument files before parsing compiler options:
    // "Replaces any `@file` arguments with the contents of `file`, with each
    // line of `file` as a separate argument." Keep cfg text attached to its
    // option so a leading @ stays literal instead of reading unauthenticated
    // bytes or introducing compiler flags. Expander::arg checks the argv
    // prefix; rustc itself parses the complete cfg grammar.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/lib.rs#L171-L187
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L14-L32
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L94-L108
    for cfg in &args.cfg {
        compiler_args.push(format!("--cfg={cfg}"));
    }
    validate_compiler_args(&compiler_args)?;
    let reads = Arc::new(Mutex::new(Reads::default()));
    let mut callbacks = Callbacks {
        args,
        verified_sysroot,
        scope: &scope,
        reads: reads.clone(),
        result: None,
    };
    let compiler_result = rustc_driver::catch_fatal_errors(|| {
        crate::driver::install_ice_hook();
        rustc_driver::run_compiler(&compiler_args, &mut callbacks);
    });
    let reads = reads
        .lock()
        .map_err(|_| Failure::tool("input read mutex poisoned"))?;
    if !reads.tool_errors.is_empty() {
        return Err(Failure::tool(reads.tool_errors.join("; ")));
    }
    if !reads.refusals.is_empty() {
        return Err(Failure::unsupported(reads.refusals.join("; ")));
    }
    if compiler_result.is_err() {
        return Err(Failure::compiler(
            "rustc rejected the compilation; see stderr diagnostics",
        ));
    }
    let manifest = callbacks
        .result
        .unwrap_or_else(|| Err(Failure::compiler("rustc did not reach after_analysis")))?;
    // Continuing after analysis must not leave later compiler reads out of
    // the source binding. Reject a changed read set rather than completing
    // an earlier snapshot with inputs that its compiler census never checked.
    if manifest.source_files.len() != reads.files.len()
        || !manifest
            .source_files
            .iter()
            .zip(reads.files.values())
            .all(|(captured, final_read)| {
                captured.path == final_read.path
                    && captured.sha256 == final_read.sha256
                    && captured.read_kind == final_read.read_kind
            })
    {
        return Err(Failure::unsupported(
            "compiler inputs changed after the analysis snapshot",
        ));
    }
    check_current_inputs(&reads)?;
    Ok(manifest)
}

fn compiler_path(path: &Path) -> Result<&str, Failure> {
    path.to_str().ok_or_else(|| {
        Failure::unsupported("non-UTF-8 paths cannot be passed to the compiler driver")
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compiler_args_gate_rejects_extern_search_paths_response_files_and_proc_macro() {
        let valid = vec![
            "anneal-rustc-capture".to_owned(),
            "lib.rs".to_owned(),
            "--crate-type=lib".to_owned(),
            "--crate-name=demo".to_owned(),
        ];
        assert!(validate_compiler_args(&valid).is_ok());

        for bad in [
            vec!["@args.rsp".to_owned()],
            vec!["--extern".to_owned(), "foo=libfoo.rlib".to_owned()],
            vec!["--extern=foo=libfoo.rlib".to_owned()],
            vec!["-L".to_owned(), "/tmp/deps".to_owned()],
            vec!["-L/tmp/deps".to_owned()],
            vec!["--crate-type=proc-macro".to_owned()],
            vec!["--crate-type=dylib".to_owned()],
            vec!["--crate-type".to_owned(), "proc-macro".to_owned()],
        ] {
            assert!(
                validate_compiler_args(&bad).is_err(),
                "expected {bad:?} to fail"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn sysroot_only_crate_admission_enforces_sysroot_dev_ino_and_no_proc_macro() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let sysroot = dir.path().join("sysroot");
        let target_lib = sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib");
        let host_lib = sysroot.join("lib");
        let cas = dir.path().join("cas");
        let outside = dir.path().join("outside");
        std::fs::create_dir_all(&target_lib).unwrap();
        std::fs::create_dir_all(&host_lib).unwrap();
        std::fs::create_dir_all(&cas).unwrap();
        std::fs::create_dir_all(&outside).unwrap();

        let core_real = cas.join("libcore-123.rmeta");
        std::fs::write(&core_real, b"core").unwrap();
        let core_link = target_lib.join("libcore-123.rmeta");
        symlink(&core_real, &core_link).unwrap();

        let host_only = host_lib.join("libhost_only.rlib");
        std::fs::write(&host_only, b"host").unwrap();

        let outside_rlib = outside.join("libevil.rlib");
        std::fs::write(&outside_rlib, b"evil").unwrap();

        let allowed = collect_sysroot_lib_identities(&sysroot, "x86_64-unknown-linux-gnu").unwrap();
        assert!(
            admit_external_crate(
                "core",
                false,
                false,
                false,
                &[core_link.as_path()],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_ok()
        );
        assert!(
            admit_external_crate(
                "host_only",
                false,
                false,
                false,
                &[host_only.as_path()],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                "evil",
                false,
                false,
                false,
                &[outside_rlib.as_path()],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                "my_macro",
                true,
                false,
                false,
                &[core_link.as_path()],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                "my_macro",
                false,
                true,
                false,
                &[core_link.as_path()],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                "proc_macro",
                false,
                false,
                false,
                &[core_link.as_path()],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                "core",
                false,
                false,
                false,
                &[],
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
    }
}
