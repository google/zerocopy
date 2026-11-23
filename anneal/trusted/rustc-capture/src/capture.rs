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

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use std::ops::ControlFlow;

use rustc_abi::{Endian, ExternAbi, Size};
use rustc_ast::{Attribute, Crate, MetaItem, MetaItemInner, Mutability};
use rustc_data_structures::steal::Steal;
use rustc_driver::Compilation;
use rustc_hir as hir;
use rustc_hir::LangItem;
use rustc_hir::attrs::AttributeKind;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::intravisit;
use rustc_interface::interface;
use rustc_middle::mir;
use rustc_middle::mir::interpret::{AllocRange, GlobalAlloc};
use rustc_middle::ty::trait_def::{ImplRestrictionKind, TraitSpecializationKind};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt, TypingEnv};
use rustc_middle::util::Providers;
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::{CrateType, OptLevel, Options};
use rustc_span::def_id::{LOCAL_CRATE, LocalDefId};
use rustc_span::source_map::{FileLoader, RealFileLoader};
use rustc_span::{FileName, sym};
use rustc_target::spec::PanicStrategy as RustcPanicStrategy;

use crate::{Args, Failure, extract, identity, ir, mono};

// rustc query providers are function pointers, so the hook cannot borrow a
// callback instance. These cells hold one process's session authority and owned
// snapshots. They are initialized once before queries and never reused for a
// second capture, avoiding stale bodies or selectors from another compilation.
type Provider = for<'tcx> fn(TyCtxt<'tcx>, LocalDefId) -> &'tcx Steal<mir::Body<'tcx>>;
static DEFAULT_PROVIDER: OnceLock<Provider> = OnceLock::new();
static CAPTURE_STARTED: OnceLock<()> = OnceLock::new();
static OBSERVED_HOOK: Mutex<BTreeSet<u32>> = Mutex::new(BTreeSet::new());

/// The query returns `Steal<Body>` and later codegen queries consume it. Call
/// the original provider, record that it ran for this callable `LocalDefId`,
/// and return the exact original result without running CTFE inside the active
/// query frame (evaluating a self-referential `const fn`'s `const { ... }`
/// inside the hook would trigger a `rustc` query cycle `E0391`). Extraction
/// runs immediately after the query returns in `collect`, before codegen can
/// steal the body; `mir_for_ctfe` clones `ConstFn` bodies without stealing.
/// The compiler explicitly supports overriding this query: "can be overridden
/// by custom rustc drivers".
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/lib.rs#L495-L503
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/lib.rs#L567-L598
///
/// Early hook observation does not decide coverage. The independent compiler
/// census is enumerated in full before selecting or assembling any output.
fn hook<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> &'tcx Steal<mir::Body<'tcx>> {
    let provider = DEFAULT_PROVIDER
        .get()
        .expect("provider installed before queries");
    let original = provider(tcx, def);
    if callable(tcx.def_kind(def)) {
        OBSERVED_HOOK
            .lock()
            .expect("capture hook mutex poisoned")
            .insert(def.local_def_index.as_u32());
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
//
// `DefKind::ForeignMod` and `DefKind::ForeignTy` are unconditionally required
// even without child items or HIR bodies: an item-less
// `#[link(name = "...")] unsafe extern "C" {}` block embeds link-time
// native-library obligations into crate metadata, and foreign types introduce
// unmodeled FFI invariants.
//
// Externally visible `DefKind::Macro(..)` items (`#[macro_export]`,
// `pub macro`, or `pub use`-reexported macros) are required in whole-crate
// scope because they expand into downstream crates (where `rustc`'s
// `unsafe_code` lint exempts tokens originating from external macro spans).
// Crate-private helper `macro_rules!` remain non-required when bodyless
// because every crate-local expansion is already captured in caller MIR.
fn required(tcx: TyCtxt<'_>, def: LocalDefId, kind: DefKind, has_body: bool) -> bool {
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
        | DefKind::GlobalAsm
        | DefKind::ForeignMod
        | DefKind::ForeignTy => true,
        DefKind::Macro(..) => {
            has_body
                || tcx.effective_visibilities(()).is_exported(def)
                || tcx.visibility(def).is_public()
        }
        DefKind::Mod
        | DefKind::Variant
        | DefKind::TyAlias
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::ConstParam
        | DefKind::Ctor(..)
        | DefKind::ExternCrate
        | DefKind::Use
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
// required owner, including owners with no runtime body:
// - Fieldless enums without explicit discriminant `AnonConst`s are admitted
//   via the type adapter.
// - Pure array-length, repeat-count, and discriminant `AnonConst`s,
//   non-generic pure-value `Const`/`AssocConst` items, safe `Trait`
//   declarations (plus their bodyless safe Rust-ABI `AssocFn` and
//   `AssocConst` items), and safe `Impl` blocks whose child items are
//   checked separately are admitted fail-closed below with no fabricated body.
// - `Struct` (pending struct capture/verification), `InlineConst`, `Static`,
//   `Union`, `ForeignMod`, `ForeignTy`, `GlobalAsm`, and bodyless free `Fn`
//   items remain explicit refusals in whole-crate scope.
// - Callables with bodies are only candidates here: `collect` publishes one
//   only if `extract::body` translates it, refusing intrinsics, generics,
//   unsupported entry conditions, and unmodeled codegen attributes.

/// Reject attributes on non-callable items whose semantic effect the scalar
/// model does not capture (`#[linkage]`, `#[no_mangle]`, `#[export_name]`,
/// `#[rustc_*]`, etc.). When `allow_repr` is true (for `Struct` constants
/// whose `adt.repr()` options are validated separately), `AttributeKind::Repr`
/// is permitted.
fn check_non_callable_attrs(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    allow_repr: bool,
    context: &str,
) -> extract::Result<()> {
    for attr in tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)) {
        match attr {
            hir::Attribute::Parsed(AttributeKind::Repr { .. }) if allow_repr => {}
            hir::Attribute::Parsed(kind) => match kind {
                AttributeKind::AutomaticallyDerived
                | AttributeKind::CfgAttrTrace
                | AttributeKind::CfgTrace(_)
                | AttributeKind::Deprecated { .. }
                | AttributeKind::Doc(_)
                | AttributeKind::DocComment { .. }
                | AttributeKind::DoNotRecommend
                | AttributeKind::MustUse { .. }
                | AttributeKind::OnConst { .. }
                | AttributeKind::OnMove { .. }
                | AttributeKind::OnUnimplemented { .. }
                | AttributeKind::OnUnknown { .. }
                | AttributeKind::OnUnmatchArgs { .. } => {}
                other => {
                    return Err(format!("{context}: unmodeled attribute {other:?} is unsupported"));
                }
            },
            hir::Attribute::Unparsed(item) => {
                let segments = item.path.segments.as_ref();
                let is_lint_attr = segments.len() == 1
                    && matches!(
                        segments[0],
                        sym::allow | sym::warn | sym::deny | sym::forbid | sym::expect
                    );
                let is_tool_attr =
                    segments.len() >= 2 && matches!(segments[0].as_str(), "clippy" | "rustfmt");
                if !is_lint_attr && !is_tool_attr {
                    return Err(format!(
                        "{context}: unmodeled attribute `{}` is unsupported",
                        item.path
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Admit only safe, ordinary Rust trait declarations (not `unsafe trait`,
/// `const trait`, `auto trait`, `#[marker]`, `#[fundamental]`, coinductive,
/// specialization, or `#[rustc_*]`-attributed traits).
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/trait_def.rs#L19-L84
fn admit_safe_trait(tcx: TyCtxt<'_>, def: LocalDefId) -> extract::Result<()> {
    let ty::TraitDef {
        def_id: _,
        impl_restriction,
        safety,
        constness,
        paren_sugar,
        has_auto_impl,
        is_marker,
        is_coinductive,
        is_fundamental,
        skip_array_during_method_dispatch,
        skip_boxed_slice_during_method_dispatch,
        specialization_kind,
        must_implement_one_of,
        force_dyn_incompatible,
        deny_explicit_impl,
    } = tcx.trait_def(def);
    if *safety != hir::Safety::Safe {
        return Err("whole-crate obligation is unsupported: Trait (unsafe trait)".into());
    }
    if *constness != hir::Constness::NotConst {
        return Err("whole-crate obligation is unsupported: Trait (const trait)".into());
    }
    if *has_auto_impl {
        return Err("whole-crate obligation is unsupported: Trait (auto trait)".into());
    }
    if *is_marker
        || *is_coinductive
        || *is_fundamental
        || *paren_sugar
        || *skip_array_during_method_dispatch
        || *skip_boxed_slice_during_method_dispatch
        || *deny_explicit_impl
        || must_implement_one_of.is_some()
        || force_dyn_incompatible.is_some()
        || !matches!(impl_restriction, ImplRestrictionKind::Unrestricted)
        || !matches!(specialization_kind, TraitSpecializationKind::None)
    {
        return Err(
            "whole-crate obligation is unsupported: Trait (unmodeled trait modifier)".into()
        );
    }
    check_non_callable_attrs(tcx, def, false, "whole-crate obligation is unsupported: Trait")
}

/// Admit safe inherent or trait `Impl` blocks whose associated items are
/// separately checked by `collect` / `whole_crate_item`. Reject `unsafe impl`
/// (except builtin `#[derive(Clone, Copy)]`'s `core::clone::TrivialClone`
/// marker impl, where `rustc` checks `self.is_automatically_derived(def_id)`
/// and `RustcBuiltinMacro` on the derive expansion), negative/reservation
/// impls (`ImplPolarity::{Negative, Reservation}`), `default impl`, `const
/// impl`, and unmodeled attributes.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/mod.rs#L288-L294
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/predicate.rs#L272-L284
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_builtin_macros/src/deriving/clone.rs#L71-L92
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/mod.rs#L2047-L2060
fn admit_safe_impl(tcx: TyCtxt<'_>, def: LocalDefId, of_trait: bool) -> extract::Result<()> {
    let impl_ = tcx.hir_expect_item(def).expect_impl();
    if impl_.constness != hir::Constness::NotConst {
        return Err(format!(
            "whole-crate obligation is unsupported: Impl {{ of_trait: {of_trait} }} (const impl)"
        ));
    }
    if of_trait {
        let Some(hir_header) = impl_.of_trait else {
            return Err(
                "whole-crate obligation is unsupported: Impl { of_trait: true } (missing header)"
                    .into(),
            );
        };
        if !matches!(hir_header.defaultness, hir::Defaultness::Final) {
            return Err(
                "whole-crate obligation is unsupported: Impl { of_trait: true } (default impl)"
                    .into(),
            );
        }
        let ty::ImplTraitHeader { trait_ref, polarity, safety, constness } =
            tcx.impl_trait_header(def);
        if constness != hir::Constness::NotConst {
            return Err(
                "whole-crate obligation is unsupported: Impl { of_trait: true } (const impl)"
                    .into(),
            );
        }
        if !matches!(polarity, ty::ImplPolarity::Positive) {
            return Err(format!(
                "whole-crate obligation is unsupported: Impl {{ of_trait: true }} \
                 ({polarity} polarity)"
            ));
        }
        if safety != hir::Safety::Safe {
            let trait_def_id = trait_ref.instantiate_identity().skip_norm_wip().def_id;
            let is_builtin_trivial_clone = !trait_def_id.is_local()
                && tcx.is_lang_item(trait_def_id, LangItem::TrivialClone)
                && tcx.is_builtin_derived(def.to_def_id());
            if !is_builtin_trivial_clone {
                return Err(
                    "whole-crate obligation is unsupported: Impl { of_trait: true } (unsafe impl)"
                        .into(),
                );
            }
        }
    }
    check_non_callable_attrs(
        tcx,
        def,
        false,
        &format!("whole-crate obligation is unsupported: Impl {{ of_trait: {of_trait} }}"),
    )
}

/// Check that a non-generic `Const`/`AssocConst` type contains only pure
/// immutable value data (scalars, fieldless enums, `Ordering`, tuples, arrays,
/// or local plain structs without `Drop`, `UnsafeCell`, unsafe fields, or
/// unmodeled representations/attributes).
fn const_ty_is_pure_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    context: &str,
) -> extract::Result<()> {
    match *ty.kind() {
        ty::Bool | ty::Char | ty::Never | ty::Int(_) | ty::Uint(_) => Ok(()),
        ty::Tuple(elems) => {
            for elem in elems {
                const_ty_is_pure_value(tcx, elem, context)?;
            }
            Ok(())
        }
        ty::Array(elem, _) => const_ty_is_pure_value(tcx, elem, context),
        ty::Adt(adt, args)
            if args.is_empty() && tcx.is_lang_item(adt.did(), LangItem::OrderingEnum) =>
        {
            Ok(())
        }
        ty::Adt(adt, args) if adt.did().is_local() && adt.is_enum() && args.is_empty() => {
            if adt.has_dtor(tcx) {
                return Err(format!("{context}: Drop enum constant type {ty:?} is unsupported"));
            }
            extract::ty(tcx, ty).map(|_| ())
        }
        ty::Adt(adt, args) if adt.did().is_local() && adt.is_struct() && args.is_empty() => {
            let Some(local_def) = adt.did().as_local() else {
                return Err(format!("{context}: non-local struct constant type {ty:?}"));
            };
            if adt.has_dtor(tcx) {
                return Err(format!("{context}: Drop struct constant type {ty:?} is unsupported"));
            }
            if ty.has_unsafe_fields() || !ty.is_freeze(tcx, TypingEnv::fully_monomorphized()) {
                return Err(format!(
                    "{context}: interior-mutable or unsafe-field constant type {ty:?} is unsupported"
                ));
            }
            let repr = adt.repr();
            if repr.simd() || repr.scalable() || repr.packed() {
                return Err(format!("{context}: unmodeled repr on struct constant type {ty:?}"));
            }
            // Reject any `#[rustc_*]` or unmodeled attribute on the struct
            // (allowing benign attributes plus `#[repr(..)]`, whose fields are
            // checked above).
            check_non_callable_attrs(tcx, local_def, true, context)?;
            let typing_env = TypingEnv::fully_monomorphized();
            for field in &adt.non_enum_variant().fields {
                let field_ty = field.ty(tcx, args);
                let normalized = tcx
                    .try_normalize_erasing_regions(typing_env, field_ty)
                    .map_err(|_| format!("{context}: unnormalizable field type {field_ty:?}"))?;
                if normalized.has_non_region_param()
                    || normalized.has_non_region_infer()
                    || normalized.references_error()
                {
                    return Err(format!(
                        "{context}: generic or erroneous field type {normalized:?}"
                    ));
                }
                const_ty_is_pure_value(tcx, normalized, context)?;
            }
            Ok(())
        }
        _ => Err(format!("{context}: unsupported constant type {ty:?}")),
    }
}

fn check_const_value_pure<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    value: mir::ConstValue,
    context: &str,
) -> extract::Result<()> {
    let typing_env = TypingEnv::fully_monomorphized();
    match value {
        mir::ConstValue::ZeroSized => {
            let layout = tcx
                .layout_of(typing_env.as_query_input(ty))
                .map_err(|err| format!("{context}: failed to compute layout for {ty:?}: {err}"))?;
            if layout.is_zst() {
                Ok(())
            } else {
                Err(format!(
                    "{context}: zero-sized constant value disagrees with non-ZST type {ty:?}"
                ))
            }
        }
        mir::ConstValue::Scalar(scalar) => {
            if scalar.try_to_scalar_int().is_ok() {
                Ok(())
            } else {
                Err(format!("{context}: provenance-bearing scalar constant is unsupported"))
            }
        }
        mir::ConstValue::Indirect { alloc_id, offset: _ } => match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Memory(const_alloc) => {
                let alloc = const_alloc.inner();
                if alloc.mutability != Mutability::Not {
                    return Err(format!(
                        "{context}: mutable global allocations are unsupported in constants"
                    ));
                }
                let range = AllocRange { start: Size::ZERO, size: alloc.size() };
                if !alloc.provenance().range_empty(range, &tcx) {
                    return Err(format!(
                        "{context}: provenance-bearing constant allocation is unsupported"
                    ));
                }
                Ok(())
            }
            GlobalAlloc::Static(_)
            | GlobalAlloc::Function { .. }
            | GlobalAlloc::VTable(..)
            | GlobalAlloc::TypeId { .. } => {
                Err(format!("{context}: non-memory global allocation in constant is unsupported"))
            }
        },
        mir::ConstValue::Slice { .. } => {
            Err(format!("{context}: slice constant values are unsupported"))
        }
    }
}

struct ConstHirSafetyVisitor<'tcx> {
    reject_calls_and_items: bool,
    typeck: Option<&'tcx ty::TypeckResults<'tcx>>,
}

impl<'v, 'tcx> intravisit::Visitor<'v> for ConstHirSafetyVisitor<'tcx> {
    type Result = ControlFlow<String>;

    fn visit_block(&mut self, b: &'v hir::Block<'v>) -> Self::Result {
        if matches!(b.rules, hir::BlockCheckMode::UnsafeBlock(_)) {
            return ControlFlow::Break("unsafe blocks are unsupported in constants".into());
        }
        intravisit::walk_block(self, b)
    }

    fn visit_stmt(&mut self, s: &'v hir::Stmt<'v>) -> Self::Result {
        if self.reject_calls_and_items && matches!(s.kind, hir::StmtKind::Item(_)) {
            return ControlFlow::Break(
                "nested items are unsupported in anonymous constants".into(),
            );
        }
        intravisit::walk_stmt(self, s)
    }

    fn visit_expr(&mut self, ex: &'v hir::Expr<'v>) -> Self::Result {
        match ex.kind {
            hir::ExprKind::InlineAsm(_) => {
                return ControlFlow::Break("inline assembly is unsupported in constants".into());
            }
            hir::ExprKind::Call(..) | hir::ExprKind::MethodCall(..)
                if self.reject_calls_and_items =>
            {
                return ControlFlow::Break(
                    "function and method calls are unsupported in anonymous constants".into(),
                );
            }
            hir::ExprKind::ConstBlock(_)
            | hir::ExprKind::Closure(_)
            | hir::ExprKind::AddrOf(..)
                if self.reject_calls_and_items =>
            {
                return ControlFlow::Break(
                    "const blocks, closures, and references are unsupported in anonymous constants"
                        .into(),
                );
            }
            hir::ExprKind::Path(ref qpath) if self.reject_calls_and_items => {
                if let Some(typeck) = self.typeck
                    && let Res::Def(_, did) = typeck.qpath_res(qpath, ex.hir_id)
                    && !did.is_local()
                {
                    return ControlFlow::Break(
                        "external definitions are unsupported in anonymous constants".into(),
                    );
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, ex)
    }

    fn visit_path(&mut self, path: &hir::Path<'v>, _id: hir::HirId) -> Self::Result {
        if self.reject_calls_and_items
            && let Res::Def(_, did) = path.res
            && !did.is_local()
        {
            return ControlFlow::Break(
                "external definitions are unsupported in anonymous constants".into(),
            );
        }
        intravisit::walk_path(self, path)
    }
}

fn check_const_hir_safety(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    reject_calls_and_items: bool,
    context: &str,
) -> extract::Result<()> {
    let body = tcx.hir_body_owned_by(def);
    let typeck = reject_calls_and_items.then(|| tcx.typeck(tcx.typeck_root_def_id_local(def)));
    let mut visitor = ConstHirSafetyVisitor { reject_calls_and_items, typeck };
    if let ControlFlow::Break(reason) = intravisit::Visitor::visit_body(&mut visitor, body) {
        return Err(format!("{context}: {reason}"));
    }
    Ok(())
}

fn admit_const_item(
    tcx: TyCtxt<'_>,
    def: LocalDefId,
    is_assoc: bool,
    is_type_const: bool,
    has_body: bool,
) -> extract::Result<()> {
    let kind_label = if is_assoc { "AssocConst" } else { "Const" };
    let context = format!(
        "whole-crate obligation is unsupported: {kind_label} {{ is_type_const: {is_type_const} }}"
    );
    if is_type_const {
        return Err(context);
    }
    check_non_callable_attrs(tcx, def, false, &context)?;
    if !has_body {
        if is_assoc && tcx.def_kind(tcx.local_parent(def)) == DefKind::Trait {
            return admit_safe_trait(tcx, tcx.local_parent(def));
        }
        return Err(format!("{context} (missing constant body)"));
    }
    if tcx.generics_of(def).count() != 0 {
        return Err(format!(
            "{context} (generic constants require quantified instantiation obligations)"
        ));
    }
    let raw_ty = tcx.type_of(def).instantiate_identity();
    let ty = tcx
        .try_normalize_erasing_regions(TypingEnv::fully_monomorphized(), raw_ty)
        .map_err(|_| format!("{context}: failed to normalize constant type"))?;
    if ty.has_non_region_param() || ty.has_non_region_infer() || ty.references_error() {
        return Err(format!("{context}: generic or erroneous constant type {ty:?}"));
    }
    const_ty_is_pure_value(tcx, ty, &context)?;
    check_const_hir_safety(tcx, def, false, &context)?;
    let ctfe_mir = tcx.mir_for_ctfe(def.to_def_id());
    if ctfe_mir.tainted_by_errors.is_some() {
        return Err(format!("{context}: constant MIR tainted by compiler errors"));
    }
    let val = tcx
        .const_eval_poly(def.to_def_id())
        .map_err(|err| format!("{context}: constant failed CTFE: {err:?}"))?;
    check_const_value_pure(tcx, ty, val, &context)
}

/// Admit pure scalar `AnonConst` items (literal/arithmetic array lengths,
/// repeat counts, and explicit enum discriminants) while rejecting `GCE`/`GCA`
/// const-generics, `unsafe` blocks, calls, nested items, external references,
/// and generic-dependent constants.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_analysis/src/collect/generics_of.rs#L97-L104
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/interpret/queries.rs#L15-L29
fn admit_anon_const(tcx: TyCtxt<'_>, def: LocalDefId, has_body: bool) -> extract::Result<()> {
    let context = "whole-crate obligation is unsupported: AnonConst";
    if !has_body {
        return Err(format!("{context} (missing body)"));
    }
    if matches!(
        tcx.anon_const_kind(def.to_def_id()),
        ty::AnonConstKind::GCE | ty::AnonConstKind::GCA
    ) {
        return Err(format!("{context} (generic const expr/arg)"));
    }
    check_non_callable_attrs(tcx, def, false, context)?;
    check_const_hir_safety(tcx, def, true, context)?;
    let raw_ty = tcx.type_of(def).instantiate_identity();
    let ty = tcx
        .try_normalize_erasing_regions(TypingEnv::fully_monomorphized(), raw_ty)
        .map_err(|_| format!("{context}: failed to normalize type"))?;
    if !matches!(ty.kind(), ty::Int(_) | ty::Uint(_) | ty::Bool | ty::Char) {
        return Err(format!("{context}: unsupported scalar type {ty:?}"));
    }
    let ctfe_mir = tcx.mir_for_ctfe(def.to_def_id());
    if ctfe_mir.tainted_by_errors.is_some() {
        return Err(format!("{context}: MIR tainted by compiler errors"));
    }
    for block in ctfe_mir.basic_blocks.iter() {
        let Some(term) = &block.terminator else {
            return Err(format!("{context}: missing terminator in CTFE MIR"));
        };
        if matches!(
            term.kind,
            mir::TerminatorKind::Call { .. }
                | mir::TerminatorKind::TailCall { .. }
                | mir::TerminatorKind::Drop { .. }
                | mir::TerminatorKind::InlineAsm { .. }
                | mir::TerminatorKind::Yield { .. }
                | mir::TerminatorKind::CoroutineDrop
        ) {
            return Err(format!("{context}: unsupported CTFE MIR terminator {:?}", term.kind));
        }
    }
    let val = tcx
        .const_eval_poly(def.to_def_id())
        .map_err(|err| format!("{context}: failed CTFE: {err:?}"))?;
    if val.try_to_scalar_int().is_none() {
        return Err(format!("{context}: expected concrete scalar integer constant"));
    }
    Ok(())
}

fn whole_crate_item(tcx: TyCtxt<'_>, def: LocalDefId, has_body: bool) -> extract::Result<()> {
    match tcx.def_kind(def) {
        DefKind::Fn | DefKind::AssocFn if has_body => Ok(()),
        DefKind::AssocFn => {
            let parent = tcx.local_parent(def);
            if tcx.def_kind(parent) != DefKind::Trait {
                return Err("whole-crate obligation is unsupported: AssocFn".into());
            }
            admit_safe_trait(tcx, parent)?;
            if let Some(intrinsic) = tcx.intrinsic(def) {
                return Err(format!(
                    "intrinsic `{}` is unsupported in trait declaration",
                    intrinsic.name
                ));
            }
            let sig = tcx.fn_sig(def).instantiate_identity().skip_binder();
            if sig.safety().is_unsafe() {
                return Err("unsafe trait method declarations are unsupported".into());
            }
            if sig.abi() != ExternAbi::Rust || sig.c_variadic() {
                return Err("only non-variadic Rust ABI functions are admitted".into());
            }
            extract::codegen_attrs(tcx, def)?;
            check_non_callable_attrs(
                tcx,
                def,
                false,
                "whole-crate obligation is unsupported: AssocFn",
            )
        }
        DefKind::Trait => admit_safe_trait(tcx, def),
        DefKind::Impl { of_trait } => admit_safe_impl(tcx, def, of_trait),
        DefKind::Const { is_type_const } => {
            admit_const_item(tcx, def, false, is_type_const, has_body)
        }
        DefKind::AssocConst { is_type_const } => {
            admit_const_item(tcx, def, true, is_type_const, has_body)
        }
        DefKind::AnonConst => admit_anon_const(tcx, def, has_body),
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
    declared_env: &'a BTreeMap<String, String>,
    verified_sysroot: &'a Path,
    verified_compiler: &'a identity::VerifiedCompiler,
    scope: &'a ir::Scope,
    reads: Arc<Mutex<Reads>>,
    result: Option<Result<ir::Manifest, Failure>>,
}

impl rustc_driver::Callbacks for Callbacks<'_> {
    fn config(&mut self, config: &mut interface::Config) {
        crate::driver::configure(config);
        // Pin both explicit and default sysroot unconditionally to the
        // pre-verified logical sysroot so `rustc_session::filesearch` can
        // never fall back to `AT_FDCWD` `./lib/rustlib`.
        config.opts.sysroot.explicit = Some(self.verified_sysroot.to_path_buf());
        config.opts.sysroot.default = self.verified_sysroot.to_path_buf();
        if let Err(reason) = validate_compiler_options(
            &config.opts,
            self.args.crate_type.into(),
            self.args.panic.into(),
        ) {
            if let Ok(mut reads) = self.reads.lock() {
                reads.tool_errors.push(reason.clone());
            }
            EarlyDiagCtxt::new(config.opts.error_format).early_fatal(reason);
        }
        // Populate `rustc`'s logical compile-time environment directly instead
        // of mutating process environment variables or passing `--env-set`
        // through argv. `lookup_env` checks `cx.sess.opts.logical_env.get(var)`
        // before falling back to `std::env::var(var)`, so explicit `--env`
        // bindings override ambient values without exposing them to the
        // compiler process environment or response-file expansion.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_builtin_macros/src/env.rs#L21-L29
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/config.rs#L1436
        for (key, value) in self.declared_env {
            config.opts.logical_env.insert(key.clone(), value.clone());
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
            self.declared_env,
            self.verified_sysroot,
            self.verified_compiler,
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
        if arg == "--env-set" || arg.starts_with("--env-set=") {
            return Err(Failure::tool(format!(
                "raw compiler --env-set arguments are forbidden: {arg}"
            )));
        }
        if arg == "--crate-type"
            || (arg.starts_with("--crate-type=")
                && !matches!(
                    arg.as_str(),
                    "--crate-type=lib" | "--crate-type=rlib" | "--crate-type=bin"
                ))
        {
            return Err(Failure::tool(format!(
                "unsupported crate type during capture: {arg}"
            )));
        }
        if arg == "-C"
            || arg == "-Cpanic"
            || (arg.starts_with("-Cpanic=")
                && !matches!(arg.as_str(), "-Cpanic=unwind" | "-Cpanic=abort"))
        {
            return Err(Failure::tool(format!(
                "unsupported panic or split -C compiler option during capture: {arg}"
            )));
        }
    }
    Ok(())
}

fn rustc_crate_type(crate_type: ir::CrateType) -> CrateType {
    match crate_type {
        ir::CrateType::Lib => CrateType::Rlib,
        ir::CrateType::Bin => CrateType::Executable,
    }
}

/// Validate the captured compilation's optimization, debug-assertion,
/// overflow-check, and UB-preservation flags, returning the numeric
/// optimization level encoded in `ir::Configuration`.
///
/// `rustc` defines `OptLevel::No` as `"-Copt-level=0"`, computes
/// `"let debug_assertions = cg.debug_assertions.unwrap_or(opt_level ==`
/// `OptLevel::No);"`, and computes `Session::overflow_checks` as
/// `"self.opts.cg.overflow_checks.unwrap_or(self.opts.debug_assertions)"`.
/// Require explicit `-Coverflow-checks=no` (`Some(false)`) here so missing
/// flags cannot pass silently by defaulting through `debug_assertions`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/config.rs#L91-L105
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/config.rs#L2629-L2634
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L724-L726
fn validate_profile_options(opts: &Options) -> Result<u8, String> {
    let opt_level = match opts.optimize {
        OptLevel::No => 0,
        other @ (OptLevel::Less
        | OptLevel::More
        | OptLevel::Aggressive
        | OptLevel::Size
        | OptLevel::SizeMin) => {
            return Err(format!("-Copt-level=0 is required during capture (got {other:?})"));
        }
    };
    if opts.debug_assertions {
        return Err("-Cdebug-assertions=no is required during capture".into());
    }
    if opts.cg.overflow_checks != Some(false) {
        return Err(format!(
            "-Coverflow-checks=no is required during capture (got {:?})",
            opts.cg.overflow_checks
        ));
    }
    if !opts.unstable_opts.mir_preserve_ub {
        return Err("-Zmir-preserve-ub must be enabled during capture".into());
    }
    Ok(opt_level)
}

fn validate_compiler_options(
    opts: &Options,
    expected_crate_type: ir::CrateType,
    expected_panic: ir::PanicStrategy,
) -> Result<(), String> {
    if opts.sysroot.explicit.is_none() {
        return Err("explicit --sysroot is required during capture".into());
    }
    if opts.externs.iter().next().is_some() {
        return Err("external crate flags (--extern) are forbidden during capture".into());
    }
    if !opts.search_paths.is_empty() {
        return Err("library search path flags (-L) are forbidden during capture".into());
    }
    let expected_rustc_ct = rustc_crate_type(expected_crate_type);
    if opts.crate_types.as_slice() != [expected_rustc_ct] {
        return Err(format!(
            "unsupported or mismatched crate types during capture: {:?}",
            opts.crate_types
        ));
    }
    let panic_ok = match expected_panic {
        ir::PanicStrategy::Unwind => {
            matches!(opts.cg.panic, None | Some(RustcPanicStrategy::Unwind))
        }
        ir::PanicStrategy::Abort => matches!(opts.cg.panic, Some(RustcPanicStrategy::Abort)),
    };
    if !panic_ok {
        return Err(format!(
            "panic strategy {:?} disagreed with configured strategy `{}`",
            opts.cg.panic,
            expected_panic.as_str()
        ));
    }
    let _ = validate_profile_options(opts)?;
    if !opts.logical_env.is_empty() {
        return Err("raw compiler --env-set flags are forbidden during capture".into());
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

struct ExternalCrate<'a> {
    name: &'a str,
    macros_only: bool,
    has_rlib: bool,
    has_dylib: bool,
    has_sdylib: bool,
    paths: &'a [&'a Path],
}

/// When `allow_dual_rlib_dylib` is true (specifically `CrateType::Bin`, where
/// `rustc_metadata::locator::Context::needs_crate_flavor` probes all flavors and
/// sysroot `std` carries both `.rlib` and `.so`), a sysroot crate with both
/// `rlib` and `dylib` artifacts is admitted provided every resolved artifact
/// resides inside `allowed_sysroot_ids`. Pure dynamic/proc-macro crates
/// (`!has_rlib`) and `CrateType::Lib` dylibs remain refused.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_metadata/src/locator.rs#L550-L561
fn admit_external_crate<F>(
    krate: &ExternalCrate<'_>,
    allow_dual_rlib_dylib: bool,
    allowed_sysroot_ids: &BTreeSet<(u64, u64)>,
    stat_dev_ino: F,
) -> Result<(), Failure>
where
    F: Fn(&Path) -> io::Result<(u64, u64)>,
{
    if krate.macros_only || krate.name == "proc_macro" {
        return Err(Failure::unsupported(format!(
            "proc-macro or macro-only crate is unsupported: {}",
            krate.name
        )));
    }
    if krate.has_dylib && !(allow_dual_rlib_dylib && krate.has_rlib) {
        return Err(Failure::unsupported(format!(
            "dynamic library or proc-macro crate is unsupported: {}",
            krate.name
        )));
    }
    if krate.has_sdylib {
        return Err(Failure::unsupported(format!(
            "sdylib interface crate is unsupported: {}",
            krate.name
        )));
    }
    if krate.paths.is_empty() {
        return Err(Failure::unsupported(format!(
            "external crate lacks a resolved artifact path: {}",
            krate.name
        )));
    }
    for path in krate.paths {
        let dev_ino = stat_dev_ino(path).map_err(|error| {
            Failure::tool(format!(
                "cannot stat artifact for crate {} at {}: {error}",
                krate.name,
                path.display()
            ))
        })?;
        if !allowed_sysroot_ids.contains(&dev_ino) {
            return Err(Failure::unsupported(format!(
                "external crate {} resolved outside target sysroot: {}",
                krate.name,
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
    expected_crate_type: ir::CrateType,
) -> Result<(), Failure> {
    let crate_types = tcx.crate_types();
    let expected_rustc_ct = rustc_crate_type(expected_crate_type);
    if crate_types != [expected_rustc_ct] {
        return Err(Failure::unsupported(format!(
            "unsupported or mismatched crate types during capture: {crate_types:?}"
        )));
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
            &ExternalCrate {
                name: crate_name.as_str(),
                macros_only: dep_kind.macros_only(),
                has_rlib: source.rlib.is_some(),
                has_dylib: source.dylib.is_some(),
                has_sdylib: source.sdylib_interface.is_some(),
                paths: &paths,
            },
            expected_crate_type == ir::CrateType::Bin,
            &allowed_ids,
            identity::regular_file_dev_ino,
        )?;
    }
    Ok(())
}

/// Verify that the active compiler session's logical sysroot matches the
/// pre-verified logical path and still resolves to the directory `(st_dev,
/// st_ino)` recorded before `identity::verify_compiler` ran.
fn verify_session_sysroot(
    session_sysroot: &Path,
    verified_sysroot: &Path,
    verified_sysroot_id: identity::DevIno,
) -> Result<PathBuf, Failure> {
    let sysroot = identity::normalize_logical_sysroot(session_sysroot)?;
    let session_sysroot_id = identity::dir_dev_ino(&sysroot).map_err(Failure::io)?;
    if sysroot != verified_sysroot || session_sysroot_id != verified_sysroot_id {
        return Err(Failure::tool(
            "compiler session sysroot diverged from verified sysroot",
        ));
    }
    Ok(sysroot)
}

/// Verify that every compile-time environment variable read recorded in
/// `tcx.sess.env_depinfo` matches an explicitly declared `--env KEY=VALUE`
/// binding.
///
/// `rustc` records `(var, value.as_ref().ok().copied())` for both `env!` and
/// `option_env!`, including absent variables (`None`). Requiring every
/// observed key to exist in `declared` with an exact `Some(expected)` match
/// keeps undeclared reads—whether present or absent in the ambient
/// environment—fail-closed while permitting explicitly bound values.
fn check_env_depinfo<'a>(
    declared: &BTreeMap<String, String>,
    observed: impl IntoIterator<Item = (&'a str, Option<&'a str>)>,
) -> Result<(), Failure> {
    let mut entries: Vec<(&'a str, Option<&'a str>)> = observed.into_iter().collect();
    entries.sort_unstable();
    for (name, value) in entries {
        let Some(expected) = declared.get(name) else {
            return Err(Failure::unsupported(format!(
                "environment-dependent source inputs are unsupported: undeclared variable {name}"
            )));
        };
        if value != Some(expected.as_str()) {
            return Err(Failure::unsupported(format!(
                "environment-dependent source inputs are unsupported: observed value for {name} \
                 disagreed with declared --env binding"
            )));
        }
    }
    Ok(())
}

/// Verify that every emitted or whole-crate-admitted `EnumTy.id` maps to a
/// unique local enum definition in the compiled crate.
fn check_admitted_enum_collisions(
    tcx: TyCtxt<'_>,
    all_local_enums: &BTreeMap<u32, Vec<LocalDefId>>,
    admitted_enum_ids: &BTreeSet<u32>,
) -> Result<(), Failure> {
    for &id in admitted_enum_ids {
        let Some(defs) = all_local_enums.get(&id) else {
            return Err(Failure::tool(format!(
                "captured enum id {id} has no matching local enum definition"
            )));
        };
        if defs.len() > 1 {
            return Err(Failure::unsupported(format!(
                "enum identity collision: {} and {} share id {id}",
                tcx.def_path_str(defs[0]),
                tcx.def_path_str(defs[1]),
            )));
        }
    }
    Ok(())
}

struct CheckedProfileConfig {
    opt_level: u8,
    debug_assertions: bool,
    overflow_checks: bool,
    mir_preserve_ub: bool,
    pointer_bits: u64,
    endian: &'static str,
}

fn checked_target_profile(
    pointer_bits: u64,
    endian: Endian,
) -> Result<(u64, &'static str), Failure> {
    match endian {
        Endian::Little if pointer_bits == 64 => Ok((pointer_bits, "little")),
        Endian::Little | Endian::Big => {
            Err(Failure::unsupported("only 64-bit little-endian targets are modeled"))
        }
    }
}

/// Validate and derive the captured target and compiler-flag profile from
/// the active `TyCtxt` rather than hardcoding literals in `ir::Configuration`.
///
/// Check `tcx.sess.overflow_checks()` directly alongside `tcx.sess.opts`
/// because MIR building (`"check_overflow |= tcx.sess.overflow_checks();"`)
/// and `cfg(overflow_checks)` read that resolved session predicate.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_build/src/builder/mod.rs#L759-L760
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/config/cfg.rs#L194-L214
fn verified_profile_config(tcx: TyCtxt<'_>) -> Result<CheckedProfileConfig, Failure> {
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
    let (pointer_bits, endian) =
        checked_target_profile(tcx.data_layout.pointer_size().bits(), tcx.data_layout.endian)?;
    let opt_level = validate_profile_options(&tcx.sess.opts).map_err(Failure::tool)?;
    let debug_assertions = tcx.sess.opts.debug_assertions;
    let overflow_checks = tcx.sess.overflow_checks();
    if overflow_checks {
        return Err(Failure::tool("-Coverflow-checks=no is required during capture"));
    }
    let mir_preserve_ub = tcx.sess.opts.unstable_opts.mir_preserve_ub;
    Ok(CheckedProfileConfig {
        opt_level,
        debug_assertions,
        overflow_checks,
        mir_preserve_ub,
        pointer_bits,
        endian,
    })
}

fn collect(
    tcx: TyCtxt<'_>,
    args: &Args,
    declared_env: &BTreeMap<String, String>,
    verified_sysroot: &Path,
    verified_compiler: &identity::VerifiedCompiler,
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
    let profile = verified_profile_config(tcx)?;
    let sysroot = verify_session_sysroot(
        tcx.sess.opts.sysroot.path(),
        verified_sysroot,
        verified_compiler.sysroot_id,
    )?;
    let requested_crate_type: ir::CrateType = args.crate_type.into();
    let requested_panic: ir::PanicStrategy = args.panic.into();
    if (requested_panic == ir::PanicStrategy::Abort)
        != (tcx.sess.panic_strategy() == RustcPanicStrategy::Abort)
    {
        return Err(Failure::unsupported(format!(
            "session panic strategy {:?} disagreed with configured strategy `{}`",
            tcx.sess.panic_strategy(),
            requested_panic.as_str()
        )));
    }
    verify_sysroot_only_crates(tcx, verified_sysroot, &args.target, requested_crate_type)?;
    // "Defined lang items can come from the current crate or its dependencies."
    // Admit crate-local `#[panic_handler]` (`LangItem::PanicImpl`) only in
    // `SelectedUnit` scope on binary crates (`CrateType::Executable`); every
    // other crate-local lang item (and any `PanicImpl` in `Scope::Crate` or
    // `CrateType::Lib`) stays refused.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L24-L67
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/lang_items.rs#L289
    if let Some((lang_item, _)) = tcx.lang_items().iter().find(|(lang_item, def)| {
        def.is_local()
            && !(requested_crate_type == ir::CrateType::Bin
                && matches!(scope, ir::Scope::SelectedUnit { .. })
                && matches!(lang_item, LangItem::PanicImpl))
    }) {
        return Err(Failure::unsupported(format!(
            "crate-local language item {lang_item:?} is unsupported"
        )));
    }
    // During codegen after `Runtime(PostCleanup)`, `rustc_codegen_ssa` runs
    // `optimize_use_clone` ("Replace `clone` calls that come from `use`
    // statements with direct copies if possible") whenever
    // `tcx.features().ergonomic_clones()` holds (`if
    // tcx.features().ergonomic_clones()`), rewriting `CallSource::Use` calls
    // on `&T` (`T: Copy`) into bitwise copies even when `<T as Clone>::clone`
    // is non-trivial. Enforce this at crate level too so bodyless
    // `--scope=crate` captures fail closed before per-body extraction.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L217-L224
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/mod.rs#L350-L407
    if tcx.features().ergonomic_clones() {
        return Err(Failure::unsupported(
            "#![feature(ergonomic_clones)] is unsupported during capture: \
             post-capture optimize_use_clone can diverge from captured MIR",
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
    // visited here. Record all local enum definitions by key, then after
    // admission refuse any emitted (or whole-crate-admitted) key shared by two
    // local definitions. That preserves global uniqueness for every key that
    // enters `ir::Program` without letting unreferenced colliding enums (such
    // as macro-expanded `const _: () = { enum ... }` blocks) abort unrelated
    // selected-unit captures.
    let mut enum_ids: BTreeMap<u32, Vec<LocalDefId>> = BTreeMap::new();
    let mut admitted_enum_ids = BTreeSet::new();
    for def in tcx.iter_local_def_id() {
        let path = tcx.def_path_str(def);
        let kind = tcx.def_kind(def);
        let enum_key = if matches!(kind, DefKind::Enum) {
            let id = extract::enum_id(tcx, def.to_def_id());
            enum_ids.entry(id).or_default().push(def);
            Some(id)
        } else {
            None
        };
        let has_body = body_owners.contains(&def.local_def_index.as_u32());
        let is_required = required(tcx, def, kind, has_body);
        // Selected-unit claims cover only the requested callable bodies. Keep
        // every other item visible in the census without pretending to verify
        // it. Whole-crate mode instead requires admission of every required
        // item, so an unsupported owner cannot disappear with its body.
        let selected = match scope {
            ir::Scope::Crate => is_required,
            ir::Scope::SelectedUnit { roots, .. } => {
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
            Ok(()) if callable(kind) && has_body => selected_defs.push(def),
            Ok(()) => {
                if let Some(id) = enum_key {
                    admitted_enum_ids.insert(id);
                }
            }
            Err(reason) => unsupported.push(ir::Unsupported {
                def_id: def.local_def_index.as_u32(),
                path,
                reason,
            }),
        }
    }
    if let ir::Scope::SelectedUnit { roots, .. } = scope
        && &found != roots
    {
        return Err(Failure::unsupported(format!(
            "selected definitions not found: {:?}",
            roots.difference(&found).collect::<Vec<_>>()
        )));
    }
    // A provider is only called when a query is demanded. Force every selected
    // body before code generation, with no incremental cache or fallback to
    // optimized MIR. Confirm the provider hook fired and the body is unstolen,
    // then extract outside the query frame so CTFE cannot cycle on self-calls.
    // The query is declared `no_hash` without `cache_on_disk_if`, and capture
    // passes no `-Cincremental`, so no stored result can stand in for the
    // provider call.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/queries.rs#L638-L641
    let mut bodies = Vec::new();
    let mut selected = Vec::new();
    let mut seen_instances = HashSet::new();
    for &def in &selected_defs {
        let key = def.local_def_index.as_u32();
        let steal = tcx.mir_drops_elaborated_and_const_checked(def);
        let observed = OBSERVED_HOOK
            .lock()
            .map_err(|_| Failure::tool("capture hook mutex poisoned"))?
            .contains(&key);
        let result = if !observed {
            Err("compiler did not provide Runtime(PostCleanup) MIR".into())
        } else if steal.is_stolen() {
            Err("Runtime(PostCleanup) MIR was already stolen before capture".into())
        } else {
            extract::body(tcx, def, &steal.borrow())
        };
        match result {
            Ok(body) => {
                seen_instances.insert(ty::Instance::mono(tcx, def.to_def_id()));
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
    if let ir::Scope::SelectedUnit { instantiations, .. } = scope {
        for inst in instantiations {
            match mono::instantiate_body(tcx, &inst.path, &inst.args) {
                Ok(resolved) => {
                    if !seen_instances.insert(resolved.instance) {
                        continue;
                    }
                    let inst_path = extract::instance_path(tcx, resolved.instance);
                    let key = resolved.resolved_local.local_def_index.as_u32();
                    let observed = OBSERVED_HOOK
                        .lock()
                        .map_err(|_| Failure::tool("capture hook mutex poisoned"))?
                        .contains(&key);
                    let extracted = if !observed {
                        Err("compiler did not provide Runtime(PostCleanup) MIR".into())
                    } else {
                        extract::instantiated_body(tcx, &resolved)
                    };
                    match extracted {
                        Ok(body) => {
                            selected.push(ir::SelectedBody {
                                def_id: key,
                                path: inst_path,
                                body_index: bodies.len(),
                            });
                            bodies.push(body);
                        }
                        Err(reason) => unsupported.push(ir::Unsupported {
                            def_id: key,
                            path: inst_path,
                            reason,
                        }),
                    }
                }
                Err(reason) => unsupported.push(ir::Unsupported {
                    def_id: 0,
                    path: format!("{}<{}>", inst.path, inst.args.join(", ")),
                    reason,
                }),
            }
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
    // Belt-and-suspenders guard complementing `DefKind::ForeignMod`: refuse
    // any crate carrying native-library link directives in crate metadata
    // (such as item-less `#[link(name = ...)]` blocks or `-l` flags), since
    // link-time native-library obligations are unmodeled in the scalar profile.
    if !tcx.native_libraries(LOCAL_CRATE).is_empty() {
        return Err(Failure::unsupported(
            "crate-local native libraries are unsupported",
        ));
    }
    for body in &bodies {
        body.collect_enum_ids(&mut admitted_enum_ids);
    }
    check_admitted_enum_collisions(tcx, &enum_ids, &admitted_enum_ids)?;
    // Defense in depth: confirm `rustc`'s logical environment still matches the
    // explicit `--env` map installed in `Callbacks::config`.
    if tcx.sess.opts.logical_env.len() != declared_env.len()
        || !declared_env
            .iter()
            .all(|(k, v)| tcx.sess.opts.logical_env.get(k) == Some(v))
    {
        return Err(Failure::tool(
            "compiler logical environment diverged from declared --env bindings",
        ));
    }
    // The manifest binds file bytes, explicit flags, and explicitly declared
    // `--env KEY=VALUE` bindings, never ambient environment values. rustc
    // records "Environment variables accessed during the build and their values
    // when they exist"; `env!` and `option_env!` both insert
    // `(var, value.as_ref().ok().copied())`, so undeclared variables—present or
    // absent—are refused here while declared bindings are checked against the
    // exact value rustc observed.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L155-L159
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_builtin_macros/src/env.rs#L54-L55
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_builtin_macros/src/env.rs#L133-L134
    {
        let env_depinfo = tcx.sess.env_depinfo.borrow();
        check_env_depinfo(
            declared_env,
            env_depinfo
                .iter()
                .map(|(var, value)| (var.as_str(), value.as_ref().map(rustc_span::Symbol::as_str))),
        )?;
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
            rustc_sha256: verified_compiler.rustc_sha256.clone(),
            driver: verified_compiler.driver.clone(),
        },
        configuration: ir::Configuration {
            crate_root: args.crate_root.clone(),
            crate_name: args.crate_name.clone(),
            crate_type: requested_crate_type,
            panic: requested_panic,
            edition: args.edition.clone(),
            target: args.target.clone(),
            cfg: args.cfg.clone(),
            env: declared_env.clone(),
            opt_level: profile.opt_level,
            debug_assertions: profile.debug_assertions,
            overflow_checks: profile.overflow_checks,
            mir_preserve_ub: profile.mir_preserve_ub,
            pointer_bits: profile.pointer_bits,
            endian: profile.endian,
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

pub(crate) fn run(
    args: &Args,
    declared_env: &BTreeMap<String, String>,
    verified_sysroot: &Path,
    verified_compiler: &identity::VerifiedCompiler,
) -> Result<ir::Manifest, Failure> {
    let scope = args.resolved_scope()?;
    CAPTURE_STARTED
        .set(())
        .map_err(|_| Failure::tool("one capture invocation per process is required"))?;
    let requested_crate_type: ir::CrateType = args.crate_type.into();
    let requested_panic: ir::PanicStrategy = args.panic.into();
    let mut compiler_args = vec![
        "anneal-rustc-capture".into(),
        compiler_path(&args.crate_root)?.to_string(),
        format!("--crate-type={}", requested_crate_type.as_str()),
        format!("--crate-name={}", args.crate_name),
        format!("--edition={}", args.edition),
        format!("--target={}", args.target),
        format!("-Cpanic={}", requested_panic.as_str()),
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
        // Preserve `StatementKind::PlaceMention` (`RemovePlaceMention` checks
        // `!sess.opts.unstable_opts.mir_preserve_ub`) and `SwitchInt` reads
        // (`SimplifyCfg` checks
        // `|| tcx.sess.opts.unstable_opts.mir_preserve_ub`), matching Miri's
        // UB-preservation flag. Note that despite `options.rs`'s help text
        // ("implies -Zmir-opt-level=0"), `Session::mir_opt_level` inspects
        // only `mir_opt_level` and `optimize`, so `-Zmir-preserve-ub` does not
        // force `-Zmir-opt-level=0` (Miri passes both flags separately).
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/remove_place_mention.rs#L10-L12
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/simplify.rs#L128-L130
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_mir_transform/src/simplify.rs#L304-L312
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L617-L622
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/src/tools/miri/src/lib.rs#L183-L188
        "-Zmir-preserve-ub".into(),
        format!("--out-dir={}", compiler_path(&args.out_dir)?),
    ];
    compiler_args.push(format!("--sysroot={}", compiler_path(verified_sysroot)?));
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
        declared_env,
        verified_sysroot,
        verified_compiler,
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
    let _ = verify_session_sysroot(
        verified_sysroot,
        verified_sysroot,
        verified_compiler.sysroot_id,
    )?;
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
            "--crate-type=bin".to_owned(),
            "-Cpanic=unwind".to_owned(),
            "-Cpanic=abort".to_owned(),
            "--crate-name=demo".to_owned(),
        ];
        assert!(validate_compiler_args(&valid).is_ok());

        for bad in [
            vec!["@args.rsp".to_owned()],
            vec!["--extern".to_owned(), "foo=libfoo.rlib".to_owned()],
            vec!["--extern=foo=libfoo.rlib".to_owned()],
            vec!["-L".to_owned(), "/tmp/deps".to_owned()],
            vec!["-L/tmp/deps".to_owned()],
            vec!["--env-set".to_owned(), "FOO=bar".to_owned()],
            vec!["--env-set=FOO=bar".to_owned()],
            vec!["--crate-type=proc-macro".to_owned()],
            vec!["--crate-type=dylib".to_owned()],
            vec!["--crate-type".to_owned(), "proc-macro".to_owned()],
            vec!["-Cpanic=immediate-abort".to_owned()],
            vec!["-Cpanic".to_owned(), "abort".to_owned()],
            vec!["-C".to_owned(), "panic=abort".to_owned()],
        ] {
            assert!(
                validate_compiler_args(&bad).is_err(),
                "expected {bad:?} to fail"
            );
        }
    }

    fn valid_capture_options(crate_type: CrateType) -> Options {
        let mut opts = Options { crate_types: vec![crate_type], ..Options::default() };
        opts.sysroot.explicit = Some(PathBuf::from("/sysroot"));
        opts.optimize = OptLevel::No;
        opts.debug_assertions = false;
        opts.cg.overflow_checks = Some(false);
        opts.unstable_opts.mir_preserve_ub = true;
        opts
    }

    #[test]
    fn compiler_options_gate_requires_mir_preserve_ub_and_matching_crate_type_and_panic() {
        let mut opts = valid_capture_options(CrateType::Rlib);
        opts.unstable_opts.mir_preserve_ub = false;
        let err = validate_compiler_options(
            &opts,
            ir::CrateType::Lib,
            ir::PanicStrategy::Unwind,
        )
        .unwrap_err();
        assert!(err.contains("-Zmir-preserve-ub"), "{err}");

        opts.unstable_opts.mir_preserve_ub = true;
        assert!(
            validate_compiler_options(&opts, ir::CrateType::Lib, ir::PanicStrategy::Unwind)
                .is_ok()
        );
        assert!(
            validate_compiler_options(&opts, ir::CrateType::Bin, ir::PanicStrategy::Unwind)
                .is_err()
        );

        let mut bin_opts = valid_capture_options(CrateType::Executable);
        bin_opts.cg.panic = Some(RustcPanicStrategy::Abort);
        assert!(
            validate_compiler_options(&bin_opts, ir::CrateType::Bin, ir::PanicStrategy::Abort)
                .is_ok()
        );
        assert!(
            validate_compiler_options(&bin_opts, ir::CrateType::Bin, ir::PanicStrategy::Unwind)
                .is_err()
        );

        opts.logical_env.insert("FOO".to_owned(), "bar".to_owned());
        let err = validate_compiler_options(
            &opts,
            ir::CrateType::Lib,
            ir::PanicStrategy::Unwind,
        )
        .unwrap_err();
        assert!(err.contains("--env-set"), "{err}");
    }

    #[test]
    fn compiler_options_gate_enforces_opt_level_debug_assertions_and_overflow_checks() {
        let base = valid_capture_options(CrateType::Rlib);
        assert_eq!(validate_profile_options(&base).unwrap(), 0);
        assert!(
            validate_compiler_options(&base, ir::CrateType::Lib, ir::PanicStrategy::Unwind).is_ok()
        );

        for level in [
            OptLevel::Less,
            OptLevel::More,
            OptLevel::Aggressive,
            OptLevel::Size,
            OptLevel::SizeMin,
        ] {
            let mut opts = valid_capture_options(CrateType::Rlib);
            opts.optimize = level;
            let err =
                validate_compiler_options(&opts, ir::CrateType::Lib, ir::PanicStrategy::Unwind)
                    .unwrap_err();
            assert!(err.contains("-Copt-level=0"), "{level:?}: {err}");
        }

        let mut debug_opts = valid_capture_options(CrateType::Rlib);
        debug_opts.debug_assertions = true;
        let err =
            validate_compiler_options(&debug_opts, ir::CrateType::Lib, ir::PanicStrategy::Unwind)
                .unwrap_err();
        assert!(err.contains("-Cdebug-assertions=no"), "{err}");

        for overflow in [None, Some(true)] {
            let mut overflow_opts = valid_capture_options(CrateType::Rlib);
            overflow_opts.cg.overflow_checks = overflow;
            let err = validate_compiler_options(
                &overflow_opts,
                ir::CrateType::Lib,
                ir::PanicStrategy::Unwind,
            )
            .unwrap_err();
            assert!(err.contains("-Coverflow-checks=no"), "{overflow:?}: {err}");
        }
    }

    #[test]
    fn target_profile_gate_requires_64_bit_little_endian() {
        assert_eq!(checked_target_profile(64, Endian::Little).unwrap(), (64, "little"));
        for (bits, endian) in [(32, Endian::Little), (64, Endian::Big), (32, Endian::Big)] {
            let err = checked_target_profile(bits, endian).unwrap_err();
            assert_eq!(err.status, "unsupported");
            assert!(
                err.diagnostics[0].contains("64-bit little-endian"),
                "{bits}, {endian:?}: {err:?}"
            );
        }
    }

    #[test]
    fn env_depinfo_gate_requires_exact_declared_bindings() {
        let empty = BTreeMap::new();
        assert!(check_env_depinfo(&empty, []).is_ok());

        let declared = BTreeMap::from([
            ("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned()),
            ("UNUSED".to_owned(), "val".to_owned()),
        ]);
        assert!(check_env_depinfo(&declared, []).is_ok());
        assert!(check_env_depinfo(&declared, [("CARGO_PKG_VERSION", Some("0.8.64"))]).is_ok());

        let undeclared_present =
            check_env_depinfo(&declared, [("AMBIENT", Some("secret"))]).unwrap_err();
        assert_eq!(undeclared_present.status, "unsupported");
        assert!(
            undeclared_present.diagnostics[0]
                .contains("environment-dependent source inputs are unsupported")
                && undeclared_present.diagnostics[0].contains("AMBIENT"),
            "{undeclared_present:?}"
        );

        let undeclared_absent = check_env_depinfo(&declared, [("MISSING", None)]).unwrap_err();
        assert_eq!(undeclared_absent.status, "unsupported");
        assert!(
            undeclared_absent.diagnostics[0]
                .contains("environment-dependent source inputs are unsupported")
                && undeclared_absent.diagnostics[0].contains("MISSING"),
            "{undeclared_absent:?}"
        );

        let mismatched =
            check_env_depinfo(&declared, [("CARGO_PKG_VERSION", Some("0.8.65"))]).unwrap_err();
        assert_eq!(mismatched.status, "unsupported");
        assert!(
            mismatched.diagnostics[0].contains("disagreed with declared --env binding"),
            "{mismatched:?}"
        );

        let observed_none =
            check_env_depinfo(&declared, [("CARGO_PKG_VERSION", None)]).unwrap_err();
        assert_eq!(observed_none.status, "unsupported");
        assert!(
            observed_none.diagnostics[0].contains("disagreed with declared --env binding"),
            "{observed_none:?}"
        );
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
                &ExternalCrate {
                    name: "core",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: false,
                    has_sdylib: false,
                    paths: &[core_link.as_path()],
                },
                false,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_ok()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "host_only",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: false,
                    has_sdylib: false,
                    paths: &[host_only.as_path()],
                },
                false,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "evil",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: false,
                    has_sdylib: false,
                    paths: &[outside_rlib.as_path()],
                },
                false,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "my_macro",
                    macros_only: true,
                    has_rlib: false,
                    has_dylib: false,
                    has_sdylib: false,
                    paths: &[core_link.as_path()],
                },
                false,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "my_macro",
                    macros_only: false,
                    has_rlib: false,
                    has_dylib: true,
                    has_sdylib: false,
                    paths: &[core_link.as_path()],
                },
                true,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "std",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: true,
                    has_sdylib: false,
                    paths: &[core_link.as_path()],
                },
                false,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "std",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: true,
                    has_sdylib: false,
                    paths: &[core_link.as_path()],
                },
                true,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_ok()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "proc_macro",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: false,
                    has_sdylib: false,
                    paths: &[core_link.as_path()],
                },
                true,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
        assert!(
            admit_external_crate(
                &ExternalCrate {
                    name: "core",
                    macros_only: false,
                    has_rlib: true,
                    has_dylib: false,
                    has_sdylib: false,
                    paths: &[],
                },
                false,
                &allowed,
                identity::regular_file_dev_ino,
            )
            .is_err()
        );
    }

    #[cfg(unix)]
    #[test]
    fn session_sysroot_check_detects_symlink_retargeting_toctou() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let sysroot_a = dir.path().join("sysroot-a");
        let sysroot_b = dir.path().join("sysroot-b");
        std::fs::create_dir_all(&sysroot_a).unwrap();
        std::fs::create_dir_all(&sysroot_b).unwrap();

        let logical_link = dir.path().join("logical-sysroot");
        symlink(&sysroot_a, &logical_link).unwrap();
        let verified_logical = identity::normalize_logical_sysroot(&logical_link).unwrap();
        let pinned_id = identity::dir_dev_ino(&verified_logical).unwrap();

        assert_eq!(
            verify_session_sysroot(&logical_link, &verified_logical, pinned_id).unwrap(),
            verified_logical
        );

        // Retarget the symlink to a different directory inode while preserving
        // the logical path: checking against `pinned_id` must fail closed.
        std::fs::remove_file(&logical_link).unwrap();
        symlink(&sysroot_b, &logical_link).unwrap();
        let err = verify_session_sysroot(&logical_link, &verified_logical, pinned_id).unwrap_err();
        assert!(
            err.diagnostics[0].contains("compiler session sysroot diverged from verified sysroot"),
            "{err:?}"
        );
    }
}
