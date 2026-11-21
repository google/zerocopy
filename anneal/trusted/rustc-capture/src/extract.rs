// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Direct translation of the admitted pointer-free Tier 2 MIR syntax.
//! Unsupported variants remain errors; this adapter performs no control-flow
//! or expression simplification.

use std::collections::BTreeMap;
use std::sync::Mutex;

use rustc_abi::{ExternAbi, Integer, Primitive, Scalar, TagEncoding, Variants};
use rustc_hir::attrs::{InlineAttr, OptimizeAttr};
use rustc_middle::middle::codegen_fn_attrs::{
    CodegenFnAttrFlags, CodegenFnAttrs, SanitizerFnAttrs,
};
use rustc_middle::mir::{self, MirPhase, RuntimePhase};
use rustc_middle::ty::{self, TyCtxt, TypingEnv};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::sym;
use sha2::{Digest, Sha256};

use crate::ir::{self, ConstLit, IntTy, IntWidth};

pub type Result<T> = std::result::Result<T, String>;

/// Session-wide collision guard for monomorphized struct and enum nominal keys
/// (`(is_struct, id) -> canonical_key`).
static OBSERVED_ADT_IDS: Mutex<BTreeMap<(bool, u32), String>> = Mutex::new(BTreeMap::new());

/// Pre-remapping terminator produced by [`body`] before `capture.rs` assigns
/// deterministic `Program.bodies` indices to the transitive call closure.
#[derive(Clone, Debug)]
pub enum RawTerminator {
    Goto {
        block: u32,
    },
    SwitchInt {
        operand: ir::Operand,
        targets: Vec<ir::SwitchTarget>,
        otherwise: u32,
    },
    Ret,
    Unreachable,
    UnwindResume,
    Assert {
        cond: ir::Operand,
        expected: bool,
        msg: ir::AssertKind,
        target: u32,
        unwind: ir::UnwindAction,
    },
    Call {
        callee: LocalDefId,
        args: Vec<ir::Operand>,
        destination: ir::Place,
        target: Option<u32>,
        unwind: ir::UnwindAction,
    },
    CallBuiltin {
        builtin: ir::CoreBuiltin,
        args: Vec<ir::Operand>,
        destination: ir::Place,
        target: Option<u32>,
        unwind: ir::UnwindAction,
    },
}

#[derive(Clone, Debug)]
pub struct RawBlock {
    pub statements: Vec<ir::Statement>,
    pub terminator: RawTerminator,
    pub cleanup: bool,
}

#[derive(Clone, Debug)]
pub struct RawBody {
    arg_count: usize,
    is_unsafe: bool,
    local_tys: Vec<ir::Ty>,
    blocks: Vec<RawBlock>,
    identity: String,
}

impl RawBody {
    /// Collect every distinct direct crate-local callee in deterministic
    /// `LocalDefId` order so `capture.rs` can resolve the transitive closure.
    pub fn local_callees(&self) -> Vec<LocalDefId> {
        let mut callees = BTreeMap::new();
        for block in &self.blocks {
            if let RawTerminator::Call { callee, .. } = block.terminator {
                callees.insert(callee.local_def_index.as_u32(), callee);
            }
        }
        callees.into_values().collect()
    }

    /// Remap direct crate-local call targets to `Program.bodies` indices and
    /// validate all [`ir::Body`] invariants.
    pub fn into_body(self, def_to_body_index: &BTreeMap<u32, u32>) -> Result<ir::Body> {
        let blocks = self
            .blocks
            .into_iter()
            .map(|block| {
                let terminator = match block.terminator {
                    RawTerminator::Goto { block } => ir::Terminator::Goto { block },
                    RawTerminator::SwitchInt {
                        operand,
                        targets,
                        otherwise,
                    } => ir::Terminator::SwitchInt {
                        operand,
                        targets,
                        otherwise,
                    },
                    RawTerminator::Ret => ir::Terminator::Ret,
                    RawTerminator::Unreachable => ir::Terminator::Unreachable,
                    RawTerminator::UnwindResume => ir::Terminator::UnwindResume,
                    RawTerminator::Assert {
                        cond,
                        expected,
                        msg,
                        target,
                        unwind,
                    } => ir::Terminator::Assert {
                        cond,
                        expected,
                        msg,
                        target,
                        unwind,
                    },
                    RawTerminator::Call {
                        callee,
                        args,
                        destination,
                        target,
                        unwind,
                    } => {
                        let key = callee.local_def_index.as_u32();
                        let callee_idx = *def_to_body_index.get(&key).ok_or_else(|| {
                            format!("missing body index for local callee def {key}")
                        })?;
                        ir::Terminator::Call {
                            callee: callee_idx,
                            args,
                            destination,
                            target,
                            unwind,
                        }
                    }
                    RawTerminator::CallBuiltin {
                        builtin,
                        args,
                        destination,
                        target,
                        unwind,
                    } => ir::Terminator::CallBuiltin {
                        builtin,
                        args,
                        destination,
                        target,
                        unwind,
                    },
                };
                Ok(ir::Block {
                    statements: block.statements,
                    terminator,
                    cleanup: block.cleanup,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        ir::Body::try_new(
            self.arg_count,
            self.is_unsafe,
            self.local_tys,
            blocks,
            self.identity,
        )
    }
}

/// Decode a `TyKind::Int` or `TyKind::Uint` into [`IntTy`], preserving pointer-
/// sized `isize`/`usize` (`bit_width() == None`) as [`IntWidth::Isize`] on the
/// separately checked 64-bit target.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ast_ir/src/lib.rs#L58-L67
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_ast_ir/src/lib.rs#L134-L143
fn int_ty(t: ty::Ty<'_>) -> Result<IntTy> {
    let (bit_width, signed) = match *t.kind() {
        ty::Uint(u) => (u.bit_width(), false),
        ty::Int(i) => (i.bit_width(), true),
        _ => return Err(format!("expected integer type, got {t:?}")),
    };
    let width = match bit_width {
        None => IntWidth::Isize,
        Some(8) => IntWidth::I8,
        Some(16) => IntWidth::I16,
        Some(32) => IntWidth::I32,
        Some(64) => IntWidth::I64,
        Some(128) => IntWidth::I128,
        Some(bits) => {
            return Err(format!("unsupported integer width {bits}"));
        }
    };
    Ok(IntTy { width, signed })
}

/// Parse the primitive integer name printed by `rustc` inside
/// `core::num::<impl {name}>::...`.
fn parse_primitive_int_name(name: &str) -> Option<IntTy> {
    let (width, signed) = match name {
        "u8" => (IntWidth::I8, false),
        "u16" => (IntWidth::I16, false),
        "u32" => (IntWidth::I32, false),
        "u64" => (IntWidth::I64, false),
        "u128" => (IntWidth::I128, false),
        "usize" => (IntWidth::Isize, false),
        "i8" => (IntWidth::I8, true),
        "i16" => (IntWidth::I16, true),
        "i32" => (IntWidth::I32, true),
        "i64" => (IntWidth::I64, true),
        "i128" => (IntWidth::I128, true),
        "isize" => (IntWidth::Isize, true),
        _ => return None,
    };
    Some(IntTy { width, signed })
}

fn int_ty_from_abi(integer: Integer, signed: bool) -> IntTy {
    let width = match integer {
        Integer::I8 => IntWidth::I8,
        Integer::I16 => IntWidth::I16,
        Integer::I32 => IntWidth::I32,
        Integer::I64 => IntWidth::I64,
        Integer::I128 => IntWidth::I128,
    };
    IntTy { width, signed }
}

/// Canonical injective string key for an admitted `ir::Ty`, used when deriving
/// nominal ADT IDs for monomorphized generic structs and enums.
fn canonical_ty_key(ty: &ir::Ty) -> String {
    match ty {
        ir::Ty::Bool => "bool".into(),
        ir::Ty::Unit => "unit".into(),
        ir::Ty::Never => "never".into(),
        ir::Ty::Int(ity) => format!(
            "{}{}",
            if ity.signed { "s" } else { "u" },
            ity.width.lean_name()
        ),
        ir::Ty::Struct(sty) => format!("struct#{}", sty.id()),
        ir::Ty::Enum(ety) => format!("enum#{}", ety.id()),
        ir::Ty::Tuple { fields } => format!(
            "tuple({})",
            fields
                .iter()
                .map(canonical_ty_key)
                .collect::<Vec<_>>()
                .join(",")
        ),
        ir::Ty::Array { elem, len } => format!("array({};{})", canonical_ty_key(elem), len),
    }
}

/// Register a derived ADT nominal key and fail closed if two distinct
/// monomorphized ADT definitions ever hash to the same 32-bit key.
fn register_adt_id(is_struct: bool, key: String, id: u32) -> Result<u32> {
    let mut table = OBSERVED_ADT_IDS
        .lock()
        .map_err(|_| "ADT identity table mutex poisoned".to_string())?;
    if let Some(prev) = table.get(&(is_struct, id)) {
        if *prev != key {
            return Err(format!(
                "ADT identity collision: `{prev}` and `{key}` share id {id}"
            ));
        }
    } else {
        table.insert((is_struct, id), key);
    }
    Ok(id)
}

/// Derive a deterministic nominal `u32` ID for a monomorphized struct or enum.
/// Non-generic local enums keep the exact `anneal:enum:v1:<item_identity>` hash
/// input so existing fieldless enum IDs remain bit-for-bit identical.
fn monomorphized_adt_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    args: ty::GenericArgsRef<'tcx>,
    is_struct: bool,
    depth: usize,
) -> Result<u32> {
    let prefix = if is_struct {
        "anneal:struct:v1:"
    } else {
        "anneal:enum:v1:"
    };
    let mut type_arg_keys = Vec::new();
    for arg in args.iter() {
        if arg.as_region().is_some() {
            continue;
        }
        let Some(arg_ty) = arg.as_type() else {
            return Err(format!(
                "unsupported non-type generic argument `{arg:?}` on ADT `{}`",
                canonical_def_path(tcx, def)
            ));
        };
        let lowered = ty_inner(tcx, arg_ty, depth + 1)?;
        type_arg_keys.push(canonical_ty_key(&lowered));
    }
    let key = if type_arg_keys.is_empty() {
        format!("{prefix}{}", item_identity(tcx, def))
    } else {
        format!(
            "{prefix}{}<{}>",
            item_identity(tcx, def),
            type_arg_keys.join(",")
        )
    };
    let digest = Sha256::digest(key.as_bytes());
    let id = u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]]);
    register_adt_id(is_struct, key, id)
}

#[derive(Clone, Copy)]
struct NicheTarget {
    tag_size: u64,
    tag_ty: IntTy,
}

/// Recursively locate the unique field/element index path inside a compound
/// value type reaching a niche leaf scalar at byte offset `rel_offset`.
fn descend_niche_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    rust_ty: ty::Ty<'tcx>,
    ir_ty: &ir::Ty,
    rel_offset: u64,
    target: NicheTarget,
    path: &mut Vec<u32>,
    depth: usize,
) -> Result<()> {
    if depth > 64 {
        return Err("niche path recursion limit exceeded".into());
    }
    let layout = tcx
        .layout_of(TypingEnv::fully_monomorphized().as_query_input(rust_ty))
        .map_err(|err| format!("failed to compute niche field layout for {rust_ty:?}: {err}"))?;
    if ir::niche_leaf_matches_tag(target.tag_ty, ir_ty) {
        if rel_offset == 0 && layout.size.bytes() == target.tag_size {
            return Ok(());
        }
        return Err(format!(
            "niche leaf {rust_ty:?} offset/size mismatch (rel_offset={rel_offset}, size={}, tag_size={})",
            layout.size.bytes(),
            target.tag_size
        ));
    }
    match (*rust_ty.kind(), ir_ty) {
        (ty::Tuple(elems), ir::Ty::Tuple { fields }) if elems.len() == fields.len() => {
            let mut found: Option<(usize, u64)> = None;
            for (idx, elem_ty) in elems.iter().enumerate() {
                let field_offset = layout.fields.offset(idx).bytes();
                let field_layout = tcx
                    .layout_of(TypingEnv::fully_monomorphized().as_query_input(elem_ty))
                    .map_err(|err| format!("failed to compute tuple niche field layout: {err}"))?;
                let field_size = field_layout.size.bytes();
                if field_size > 0
                    && field_offset <= rel_offset
                    && rel_offset + target.tag_size <= field_offset + field_size
                {
                    if found.is_some() {
                        return Err("ambiguous overlapping niche field in tuple".into());
                    }
                    found = Some((idx, rel_offset - field_offset));
                }
            }
            let Some((idx, next_offset)) = found else {
                return Err(format!("could not locate niche inside tuple {rust_ty:?}"));
            };
            path.push(u32::try_from(idx).map_err(|_| "niche path index overflow".to_string())?);
            descend_niche_path(
                tcx,
                elems[idx],
                &fields[idx],
                next_offset,
                target,
                path,
                depth + 1,
            )
        }
        (ty::Adt(adt, args), ir::Ty::Struct(sty)) if adt.is_struct() => {
            let variant = adt.non_enum_variant();
            if variant.fields.len() != sty.fields().len() {
                return Err("struct niche field count mismatch".into());
            }
            let mut found: Option<(usize, ty::Ty<'tcx>, u64)> = None;
            for (idx, field_def) in variant.fields.iter().enumerate() {
                let field_offset = layout.fields.offset(idx).bytes();
                let fty = tcx.normalize_erasing_regions(
                    TypingEnv::fully_monomorphized(),
                    field_def.ty(tcx, args),
                );
                let field_layout = tcx
                    .layout_of(TypingEnv::fully_monomorphized().as_query_input(fty))
                    .map_err(|err| format!("failed to compute struct niche field layout: {err}"))?;
                let field_size = field_layout.size.bytes();
                if field_size > 0
                    && field_offset <= rel_offset
                    && rel_offset + target.tag_size <= field_offset + field_size
                {
                    if found.is_some() {
                        return Err("ambiguous overlapping niche field in struct".into());
                    }
                    found = Some((idx, fty, rel_offset - field_offset));
                }
            }
            let Some((idx, fty, next_offset)) = found else {
                return Err(format!("could not locate niche inside struct {rust_ty:?}"));
            };
            path.push(u32::try_from(idx).map_err(|_| "niche path index overflow".to_string())?);
            descend_niche_path(
                tcx,
                fty,
                &sty.fields()[idx],
                next_offset,
                target,
                path,
                depth + 1,
            )
        }
        (ty::Array(elem_rust_ty, _), ir::Ty::Array { elem, len }) => {
            let elem_layout = tcx
                .layout_of(TypingEnv::fully_monomorphized().as_query_input(elem_rust_ty))
                .map_err(|err| format!("failed to compute array niche element layout: {err}"))?;
            let elem_size = elem_layout.size.bytes();
            if elem_size == 0 {
                return Err("cannot locate niche inside zero-sized array element".into());
            }
            let elem_idx = rel_offset / elem_size;
            let inner_offset = rel_offset % elem_size;
            if elem_idx >= *len || inner_offset + target.tag_size > elem_size {
                return Err(format!("niche offset out of bounds in array {rust_ty:?}"));
            }
            let idx_u32 =
                u32::try_from(elem_idx).map_err(|_| "array niche index exceeds u32".to_string())?;
            path.push(idx_u32);
            descend_niche_path(
                tcx,
                elem_rust_ty,
                elem,
                inner_offset,
                target,
                path,
                depth + 1,
            )
        }
        _ => Err(format!(
            "unsupported niche container type {rust_ty:?} (ir {ir_ty:?})"
        )),
    }
}

/// Extract the in-memory tag representation of an enum from `rustc`'s
/// monomorphized `Variants` layout (`Empty`, `Single { index }`, `Multiple`
/// with `TagEncoding::Direct` or `TagEncoding::Niche`).
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_abi/src/lib.rs#L1937-L1952
fn enum_tag_repr<'tcx>(
    tcx: TyCtxt<'tcx>,
    t: ty::Ty<'tcx>,
    adt: ty::AdtDef<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    variant_fields: &[Vec<ir::Ty>],
) -> Result<ir::EnumTagRepr> {
    let layout = tcx
        .layout_of(TypingEnv::fully_monomorphized().as_query_input(t))
        .map_err(|err| format!("failed to compute enum layout for {t:?}: {err}"))?;
    let variant_count = adt.variants().len();
    let has_payload = variant_fields.iter().any(|fs| !fs.is_empty());
    match &layout.variants {
        Variants::Empty => Err(format!(
            "uninhabited zero-variant enums are unsupported: {t:?}"
        )),
        Variants::Single { index } => {
            if index.as_usize() == 0
                && layout.size.bytes() == 0
                && variant_count == 1
                && !has_payload
            {
                Ok(ir::EnumTagRepr::ZeroSized)
            } else {
                Ok(ir::EnumTagRepr::Single {
                    variant: index.as_u32(),
                })
            }
        }
        Variants::Multiple {
            tag,
            tag_encoding: TagEncoding::Direct,
            tag_field,
            ..
        } if tag_field.as_usize() == 0 => match tag.primitive() {
            Primitive::Int(integer, signed) => {
                Ok(ir::EnumTagRepr::Scalar(int_ty_from_abi(integer, signed)))
            }
            other => Err(format!("non-integer enum tag primitive {other:?}: {t:?}")),
        },
        Variants::Multiple {
            tag,
            tag_encoding:
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                },
            tag_field,
            variants,
        } => {
            let Scalar::Initialized {
                value: Primitive::Int(integer, signed),
                valid_range,
            } = *tag
            else {
                return Err(format!("unsupported niche tag scalar {tag:?}: {t:?}"));
            };
            let tag_ty = int_ty_from_abi(integer, signed);
            let tag_size = tag.size(&tcx.data_layout).bytes();
            let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
            let untagged_idx = untagged_variant.as_usize();
            let untagged_layout = &variants[*untagged_variant];
            let untagged_def = adt.variant(*untagged_variant);
            let untagged_ir_fields = variant_fields
                .get(untagged_idx)
                .ok_or_else(|| format!("untagged variant {untagged_idx} out of bounds"))?;
            if untagged_def.fields.len() != untagged_ir_fields.len() {
                return Err("untagged variant field count mismatch".into());
            }
            let mut found: Option<(usize, ty::Ty<'tcx>, u64)> = None;
            for (idx, field_def) in untagged_def.fields.iter().enumerate() {
                let field_offset =
                    untagged_layout.field_offsets[rustc_abi::FieldIdx::from_usize(idx)].bytes();
                let fty = tcx.normalize_erasing_regions(
                    TypingEnv::fully_monomorphized(),
                    field_def.ty(tcx, args),
                );
                let field_layout = tcx
                    .layout_of(TypingEnv::fully_monomorphized().as_query_input(fty))
                    .map_err(|err| {
                        format!("failed to compute untagged variant field layout: {err}")
                    })?;
                let field_size = field_layout.size.bytes();
                if field_size > 0
                    && field_offset <= tag_offset
                    && tag_offset + tag_size <= field_offset + field_size
                {
                    if found.is_some() {
                        return Err(format!(
                            "ambiguous overlapping niche field in untagged variant of {t:?}"
                        ));
                    }
                    found = Some((idx, fty, tag_offset - field_offset));
                }
            }
            let Some((first_idx, first_fty, rel_offset)) = found else {
                return Err(format!(
                    "could not locate niche field at offset {tag_offset} in {t:?}"
                ));
            };
            let mut niche_path = vec![
                u32::try_from(first_idx).map_err(|_| "niche path index overflow".to_string())?,
            ];
            descend_niche_path(
                tcx,
                first_fty,
                &untagged_ir_fields[first_idx],
                rel_offset,
                NicheTarget { tag_size, tag_ty },
                &mut niche_path,
                0,
            )?;
            Ok(ir::EnumTagRepr::Niche {
                tag: tag_ty,
                valid_start: valid_range.start,
                valid_end: valid_range.end,
                niche_path,
                untagged: untagged_variant.as_u32(),
                start: niche_variants.start.as_u32(),
                last: niche_variants.last.as_u32(),
                niche_start: *niche_start,
            })
        }
        other => Err(format!("unsupported enum variant layout {other:?}: {t:?}")),
    }
}

/// Check whether an external ADT is one of the audited `core` ADTs admitted in
/// Tier 2 (`core::option::Option` or `core::result::Result`).
fn is_admitted_external_adt(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if def.is_local() || tcx.crate_name(def.krate) != sym::core {
        return false;
    }
    matches!(
        canonical_def_path(tcx, def).as_str(),
        "core::option::Option" | "core::result::Result"
    )
}

/// The type grammar is `TyKind` at the pinned compiler revision:
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/ty_kind.rs
pub fn ty<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Result<ir::Ty> {
    ty_inner(tcx, t, 0)
}

fn ty_inner<'tcx>(tcx: TyCtxt<'tcx>, raw_t: ty::Ty<'tcx>, depth: usize) -> Result<ir::Ty> {
    if depth > 64 {
        return Err(format!("type recursion limit exceeded for {raw_t:?}"));
    }
    let t = tcx.normalize_erasing_regions(
        TypingEnv::fully_monomorphized(),
        ty::Unnormalized::new_wip(raw_t),
    );
    match *t.kind() {
        ty::Bool => Ok(ir::Ty::Bool),
        ty::Never => Ok(ir::Ty::Never),
        ty::Tuple(elements) if elements.is_empty() => Ok(ir::Ty::Unit),
        ty::Tuple(elements) => {
            let fields = elements
                .iter()
                .map(|elem| ty_inner(tcx, elem, depth + 1))
                .collect::<Result<Vec<_>>>()?;
            Ok(ir::Ty::Tuple { fields })
        }
        ty::Uint(_) | ty::Int(_) => Ok(ir::Ty::Int(int_ty(t)?)),
        ty::Array(elem, len_const) => {
            let norm_len = tcx.normalize_erasing_regions(
                TypingEnv::fully_monomorphized(),
                ty::Unnormalized::new_wip(len_const),
            );
            let len = norm_len
                .try_to_target_usize(tcx)
                .ok_or_else(|| format!("unevaluated array length constant in {t:?}"))?;
            let elem_ty = ty_inner(tcx, elem, depth + 1)?;
            Ok(ir::Ty::Array {
                elem: Box::new(elem_ty),
                len,
            })
        }
        ty::Adt(adt, args)
            if (adt.did().is_local() || is_admitted_external_adt(tcx, adt.did())) =>
        {
            if adt.is_union() {
                return Err(format!("union types are unsupported: {t:?}"));
            }
            if adt.repr().simd() {
                return Err(format!("SIMD struct types are unsupported: {t:?}"));
            }
            if adt.is_struct() {
                let id = monomorphized_adt_id(tcx, adt.did(), args, true, depth)?;
                let fields = adt
                    .non_enum_variant()
                    .fields
                    .iter()
                    .map(|field| ty_inner(tcx, field.ty(tcx, args).skip_norm_wip(), depth + 1))
                    .collect::<Result<Vec<_>>>()?;
                let sty = ir::StructTy::try_new(id, fields)
                    .map_err(|reason| format!("{reason}: {t:?}"))?;
                return Ok(ir::Ty::Struct(sty));
            }
            if !adt.is_enum() {
                return Err(format!("unsupported ADT type: {t:?}"));
            }
            if adt.variants().is_empty() {
                return Err(format!(
                    "uninhabited zero-variant enums are unsupported: {t:?}"
                ));
            }
            let id = monomorphized_adt_id(tcx, adt.did(), args, false, depth)?;
            let variant_fields = adt
                .variants()
                .iter()
                .map(|variant| {
                    variant
                        .fields
                        .iter()
                        .map(|field| ty_inner(tcx, field.ty(tcx, args).skip_norm_wip(), depth + 1))
                        .collect::<Result<Vec<_>>>()
                })
                .collect::<Result<Vec<_>>>()?;
            let discr = int_ty(t.discriminant_ty(tcx))
                .map_err(|err| format!("unsupported enum discriminant type for {t:?}: {err}"))?;
            let tag_repr = enum_tag_repr(tcx, t, adt, args, &variant_fields)?;
            let discriminants = adt
                .discriminants(tcx)
                .map(|(_, entry)| {
                    if int_ty(entry.ty)? != discr {
                        return Err("enum discriminant type disagrees with discriminant_ty".into());
                    }
                    Ok(entry.val)
                })
                .collect::<Result<Vec<_>>>()?;
            let ety = ir::EnumTy::try_new(id, discr, tag_repr, discriminants, variant_fields)
                .map_err(|reason| format!("{reason}: {t:?}"))?;
            Ok(ir::Ty::Enum(ety))
        }
        _ => Err(format!("unsupported type: {t:?}")),
    }
}

/// `Place` has a local plus left-to-right projections. Tier 2 admits `Field`,
/// `Downcast`, `Index`, and `ConstantIndex`, preserving compiler local indices
/// without renumbering.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1182-L1188
fn place<'tcx>(tcx: TyCtxt<'tcx>, p: &mir::Place<'tcx>) -> Result<ir::Place> {
    let mut projection = Vec::with_capacity(p.projection.len());
    for elem in p.projection.iter() {
        match elem {
            mir::ProjectionElem::Field(field_idx, field_ty) => {
                projection.push(ir::ProjectionElem::Field {
                    index: field_idx.as_u32(),
                    ty: ty(tcx, field_ty)?,
                });
            }
            mir::ProjectionElem::Downcast(_, variant_idx) => {
                projection.push(ir::ProjectionElem::Downcast {
                    variant_idx: variant_idx.as_u32(),
                });
            }
            mir::ProjectionElem::Index(local) => {
                projection.push(ir::ProjectionElem::Index {
                    local: local.as_u32(),
                });
            }
            mir::ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                projection.push(ir::ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                });
            }
            other => {
                return Err(format!("unsupported place projection {other:?}: {p:?}"));
            }
        }
    }
    Ok(ir::Place {
        local: p.local.as_u32(),
        projection,
    })
}

/// Copy and move are distinct constructors. The source says a move "may
/// additionally overwrite the place with `uninit` bytes"; the model owns that
/// operational choice rather than having the adapter erase the distinction.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1303-L1330
fn operand<'tcx>(tcx: TyCtxt<'tcx>, op: &mir::Operand<'tcx>) -> Result<ir::Operand> {
    match op {
        mir::Operand::Copy(p) => Ok(ir::Operand::Copy {
            place: place(tcx, p)?,
        }),
        mir::Operand::Move(p) => Ok(ir::Operand::Move {
            place: place(tcx, p)?,
        }),
        mir::Operand::Constant(constant) => {
            let t = ty(tcx, constant.const_.ty())?;
            let width = match &t {
                ir::Ty::Bool => 8,
                ir::Ty::Unit => {
                    if matches!(
                        constant.const_,
                        mir::Const::Val(mir::ConstValue::ZeroSized, _)
                    ) {
                        return Ok(ir::Operand::Constant {
                            ty: t,
                            lit: ConstLit::ZeroSized,
                        });
                    }
                    return Err("unit constant lacks the compiler ZeroSized representation".into());
                }
                ir::Ty::Never => {
                    return Err("the never type has no scalar constants".into());
                }
                ir::Ty::Int(ity) => ity.width.bits(),
                ir::Ty::Tuple { .. } => {
                    return Err("tuple constants are unsupported".into());
                }
                ir::Ty::Struct(_) => {
                    if matches!(
                        constant.const_,
                        mir::Const::Val(mir::ConstValue::ZeroSized, _)
                    ) {
                        ir::validate_constant(&t, ConstLit::ZeroSized)?;
                        return Ok(ir::Operand::Constant {
                            ty: t,
                            lit: ConstLit::ZeroSized,
                        });
                    }
                    return Err("non-ZST struct constants are unsupported".into());
                }
                ir::Ty::Array { len: 0, .. } => {
                    if matches!(
                        constant.const_,
                        mir::Const::Val(mir::ConstValue::ZeroSized, _)
                    ) {
                        return Ok(ir::Operand::Constant {
                            ty: t,
                            lit: ConstLit::ZeroSized,
                        });
                    }
                    return Err(
                        "zero-length array constant lacks the compiler ZeroSized representation"
                            .into(),
                    );
                }
                ir::Ty::Array { .. } => {
                    return Err("non-empty array constants are unsupported".into());
                }
                ir::Ty::Enum(ety) => match ety.tag_repr() {
                    ir::EnumTagRepr::ZeroSized | ir::EnumTagRepr::Single { .. } => {
                        if matches!(
                            constant.const_,
                            mir::Const::Val(mir::ConstValue::ZeroSized, _)
                        ) {
                            ir::validate_constant(&t, ConstLit::ZeroSized)?;
                            return Ok(ir::Operand::Constant {
                                ty: t,
                                lit: ConstLit::ZeroSized,
                            });
                        }
                        return Err(
                            "zero-sized enum constant lacks the compiler ZeroSized representation"
                                .into(),
                        );
                    }
                    ir::EnumTagRepr::Scalar(tag) => tag.width.bits(),
                    ir::EnumTagRepr::Niche { tag, .. } => tag.width.bits(),
                },
            };
            // Admit already-valued integer scalars (including evaluated
            // type-level `ValTreeKind::Leaf` constants emitted for fixed-array
            // `BoundsCheck` lengths) and the closed allowlist of pure sysroot
            // `core` primitive integer constants (`MIN`, `MAX`, `BITS`). Refuse
            // all crate-local and other `Unevaluated` constants fail-closed.
            let value = match constant.const_ {
                mir::Const::Val(value, _) => value
                    .try_to_scalar_int()
                    .ok_or("only integer scalar constants are modeled")?,
                mir::Const::Ty(_, c) => match c.kind() {
                    ty::ConstKind::Value(cv) => match *cv.valtree {
                        ty::ValTreeKind::Leaf(scalar_int) => *scalar_int,
                        _ => return Err(format!("unsupported constant: {:?}", constant.const_)),
                    },
                    _ => return Err(format!("unsupported constant: {:?}", constant.const_)),
                },
                mir::Const::Unevaluated(uneval, const_ty) => {
                    eval_admitted_core_scalar_const(tcx, uneval, const_ty, constant.span)
                        .ok_or_else(|| format!("unsupported constant: {:?}", constant.const_))?
                }
            };
            if value.size().bits() != u64::from(width) {
                return Err("scalar constant width disagrees with its type".into());
            }
            let lit = ConstLit::Scalar {
                bits: value.to_bits_unchecked(),
            };
            ir::validate_constant(&t, lit)?;
            Ok(ir::Operand::Constant { ty: t, lit })
        }
        other => Err(format!("unsupported operand: {other:?}")),
    }
}

/// Preserve the MIR unary and binary operators modeled in
/// `Trusted.MirSemantics.evalUnOp` and `Trusted.MirSemantics.evalBinOp`
/// (`compiler/rustc_middle/src/mir/syntax.rs` in `rust-lang/rust`
/// `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
///
/// > "pub enum UnOp { Not, Neg, PtrMetadata }"
/// > "pub enum BinOp { Add, AddUnchecked, AddWithOverflow, Sub, SubUnchecked,
/// >  SubWithOverflow, Mul, MulUnchecked, MulWithOverflow, Div, Rem, BitXor,
/// >  BitAnd, BitOr, Shl, ShlUnchecked, Shr, ShrUnchecked, Eq, Lt, Le, Ne,
/// >  Ge, Gt, Cmp, Offset }"
///
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1621-L1708
fn un_op(op: mir::UnOp) -> Result<ir::UnOp> {
    Ok(match op {
        mir::UnOp::Not => ir::UnOp::Not,
        mir::UnOp::Neg => ir::UnOp::Neg,
        other => return Err(format!("unsupported unary operator: {other:?}")),
    })
}

fn bin_op(op: mir::BinOp) -> Result<ir::BinOp> {
    Ok(match op {
        mir::BinOp::BitAnd => ir::BinOp::BitAnd,
        mir::BinOp::BitOr => ir::BinOp::BitOr,
        mir::BinOp::BitXor => ir::BinOp::BitXor,
        mir::BinOp::Shl => ir::BinOp::Shl,
        mir::BinOp::ShlUnchecked => ir::BinOp::ShlUnchecked,
        mir::BinOp::Shr => ir::BinOp::Shr,
        mir::BinOp::ShrUnchecked => ir::BinOp::ShrUnchecked,
        mir::BinOp::Add => ir::BinOp::Add,
        mir::BinOp::AddUnchecked => ir::BinOp::AddUnchecked,
        mir::BinOp::AddWithOverflow => ir::BinOp::AddWithOverflow,
        mir::BinOp::Sub => ir::BinOp::Sub,
        mir::BinOp::SubUnchecked => ir::BinOp::SubUnchecked,
        mir::BinOp::SubWithOverflow => ir::BinOp::SubWithOverflow,
        mir::BinOp::Mul => ir::BinOp::Mul,
        mir::BinOp::MulUnchecked => ir::BinOp::MulUnchecked,
        mir::BinOp::MulWithOverflow => ir::BinOp::MulWithOverflow,
        mir::BinOp::Div => ir::BinOp::Div,
        mir::BinOp::Rem => ir::BinOp::Rem,
        mir::BinOp::Eq => ir::BinOp::Eq,
        mir::BinOp::Ne => ir::BinOp::Ne,
        mir::BinOp::Lt => ir::BinOp::Lt,
        mir::BinOp::Le => ir::BinOp::Le,
        mir::BinOp::Gt => ir::BinOp::Gt,
        mir::BinOp::Ge => ir::BinOp::Ge,
        other => return Err(format!("unsupported binary operator: {other:?}")),
    })
}

/// `Use` "yields the operand unchanged, except for a potential retag."
/// `rustc` lowers ordinary assignments to `Rvalue::Use(_, WithRetag::Yes)`,
/// which in Miri (`Miri/Interpreter/Rvalue.lean` + `ValidityVisitor.lean`)
/// invokes `retagSafePointer` only on safe-pointer types (`&T`, `&mut T`,
/// `Box<T>`). `ir::Body::try_new` admits `with_retag == true` only when
/// `dst_ty.is_retag_noop()`, so future pointer/reference extensions fail
/// closed until retagging is modeled. Binary operands may have different types
/// for shifts; no casts are inserted.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1363-L1365
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L1410-L1443
fn rvalue<'tcx>(tcx: TyCtxt<'tcx>, value: &mir::Rvalue<'tcx>) -> Result<ir::Rvalue> {
    Ok(match value {
        mir::Rvalue::Aggregate(kind, operands) => {
            let translated = operands
                .iter()
                .map(|op| operand(tcx, op))
                .collect::<Result<Vec<_>>>()?;
            match &**kind {
                mir::AggregateKind::Tuple => {
                    if translated.is_empty() {
                        ir::Rvalue::Unit
                    } else {
                        ir::Rvalue::Aggregate {
                            aggregate_kind: ir::AggregateKind::Tuple,
                            operands: translated,
                        }
                    }
                }
                mir::AggregateKind::Adt(adt_def_id, variant_idx, generic_args, _, active_field) => {
                    if active_field.is_some() {
                        return Err("union aggregates are unsupported".into());
                    }
                    let adt_def = tcx.adt_def(*adt_def_id);
                    let adt_ty = ty::Ty::new_adt(tcx, adt_def, generic_args);
                    match ty(tcx, adt_ty)? {
                        ir::Ty::Struct(sty) => {
                            if variant_idx.as_u32() != 0 {
                                return Err("non-zero struct variant index".into());
                            }
                            ir::Rvalue::Aggregate {
                                aggregate_kind: ir::AggregateKind::AdtStruct { sty },
                                operands: translated,
                            }
                        }
                        ir::Ty::Enum(ety) => ir::Rvalue::Aggregate {
                            aggregate_kind: ir::AggregateKind::AdtEnum {
                                ety,
                                variant_idx: variant_idx.as_u32(),
                            },
                            operands: translated,
                        },
                        other => {
                            return Err(format!("unexpected ADT aggregate type: {other:?}"));
                        }
                    }
                }
                mir::AggregateKind::Array(elem_ty) => ir::Rvalue::Aggregate {
                    aggregate_kind: ir::AggregateKind::Array {
                        elem_ty: ty(tcx, *elem_ty)?,
                    },
                    operands: translated,
                },
                other => return Err(format!("unsupported aggregate kind: {other:?}")),
            }
        }
        mir::Rvalue::Repeat(op, count_const) => {
            let norm_count = tcx.normalize_erasing_regions(
                TypingEnv::fully_monomorphized(),
                ty::Unnormalized::new_wip(*count_const),
            );
            let count = norm_count
                .try_to_target_usize(tcx)
                .ok_or_else(|| format!("unevaluated repeat count: {count_const:?}"))?;
            ir::Rvalue::Repeat {
                operand: operand(tcx, op)?,
                count,
            }
        }
        mir::Rvalue::Use(op, with_retag) => ir::Rvalue::Use {
            operand: operand(tcx, op)?,
            with_retag: with_retag.yes(),
        },
        mir::Rvalue::UnaryOp(op, opnd) => ir::Rvalue::Unary {
            op: un_op(*op)?,
            operand: operand(tcx, opnd)?,
        },
        mir::Rvalue::BinaryOp(op, values) => ir::Rvalue::Binary {
            op: bin_op(*op)?,
            left: operand(tcx, &values.0)?,
            right: operand(tcx, &values.1)?,
        },
        mir::Rvalue::Cast(mir::CastKind::IntToInt, op, target_ty) => ir::Rvalue::Cast {
            cast_kind: ir::CastKind::IntToInt,
            operand: operand(tcx, op)?,
            ty: ty(tcx, *target_ty)?,
        },
        mir::Rvalue::Discriminant(p) => ir::Rvalue::Discriminant {
            place: place(tcx, p)?,
        },
        other => return Err(format!("unsupported rvalue: {other:?}")),
    })
}

/// Storage markers survive capture. Their documented effect is that
/// "Using a local ... while it is unallocated is UB."
/// `Nop` alone has no effect.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L364-L385
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L442-L443
fn statement<'tcx>(tcx: TyCtxt<'tcx>, stmt: &mir::StatementKind<'tcx>) -> Result<ir::Statement> {
    Ok(match stmt {
        mir::StatementKind::Assign(value) => ir::Statement::Assign {
            place: place(tcx, &value.0)?,
            value: Box::new(rvalue(tcx, &value.1)?),
        },
        mir::StatementKind::SetDiscriminant {
            place: p,
            variant_index,
        } => ir::Statement::SetDiscriminant {
            place: place(tcx, p)?,
            variant_idx: variant_index.as_u32(),
        },
        mir::StatementKind::StorageLive(local) => ir::Statement::StorageLive {
            local: local.as_u32(),
        },
        mir::StatementKind::StorageDead(local) => ir::Statement::StorageDead {
            local: local.as_u32(),
        },
        mir::StatementKind::Nop => ir::Statement::Nop,
        other => return Err(format!("unsupported statement: {other:?}")),
    })
}

fn unwind_action(unwind: mir::UnwindAction) -> ir::UnwindAction {
    match unwind {
        mir::UnwindAction::Continue => ir::UnwindAction::Continue,
        mir::UnwindAction::Unreachable => ir::UnwindAction::Unreachable,
        mir::UnwindAction::Terminate(_) => ir::UnwindAction::Terminate,
        mir::UnwindAction::Cleanup(bb) => ir::UnwindAction::Cleanup { block: bb.as_u32() },
    }
}

/// Validate the implicit panic-handling path invoked when a MIR `Assert`
/// fails at runtime:
/// 1. `msg.panic_function()` must resolve to a non-local `core` lang item
///    (blocking `#![no_core]` crates that define local `panic_*` lang items
///    outside the verified call closure).
/// 2. For operand-free asserts (where `Trusted.MirSemantics` models failure by
///    unwinding to `.unwound`), `LangItem::PanicImpl` (`#[panic_handler]`)
///    must resolve to sysroot `std`. For `BoundsCheck`, `Trusted.MirSemantics`
///    fails closed with `.fault .unsupported` on failure rather than modeling
///    unwinding, so every verified execution must prove bounds checks never
///    fail and `#![no_std]` crates without `std::panic_impl` are sound to
///    admit.
///
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/terminator.rs#L948-L1005
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/mir/block.rs#L1294-L1330
fn validate_assert_panic_path<'tcx, O: std::fmt::Debug>(
    tcx: TyCtxt<'tcx>,
    msg: &mir::AssertKind<O>,
) -> Result<()> {
    let panic_lang_item = match msg {
        mir::AssertKind::BoundsCheck { .. } => rustc_hir::LangItem::PanicBoundsCheck,
        _ => msg.panic_function(),
    };
    let Some(panic_fn) = tcx.lang_items().get(panic_lang_item) else {
        return Err(format!(
            "missing panic lang item {panic_lang_item:?} for assert {msg:?}"
        ));
    };
    if panic_fn.is_local() || tcx.crate_name(panic_fn.krate) != sym::core {
        return Err(format!(
            "assert panic lang item `{}` must resolve to sysroot `core`",
            canonical_def_path(tcx, panic_fn)
        ));
    }
    if matches!(msg, mir::AssertKind::BoundsCheck { .. }) {
        return Ok(());
    }
    let Some(panic_impl) = tcx.lang_items().panic_impl() else {
        return Err(
            "panic asserts require sysroot `std` unwinding panic handler; \
             `#![no_std]` libraries without `std` are unsupported for bodies \
             containing asserts"
                .into(),
        );
    };
    if panic_impl.is_local() || tcx.crate_name(panic_impl.krate) != sym::std {
        return Err(format!(
            "assert panic handler `{}` must resolve to sysroot `std` \
             (crate-local or non-std `#[panic_handler]` is unsupported)",
            canonical_def_path(tcx, panic_impl)
        ));
    }
    Ok(())
}

/// Translate an admitted `mir::AssertKind` using `rustc`'s own
/// `is_optional_overflow_check` predicate so `-Coverflow-checks=no` never
/// disagrees with codegen.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/terminator.rs#L938-L946
fn assert_kind<O: std::fmt::Debug>(
    overflow_checks: bool,
    msg: &mir::AssertKind<O>,
) -> Result<ir::AssertKind> {
    if !overflow_checks && msg.is_optional_overflow_check() {
        return Err(format!(
            "optional overflow assert {msg:?} is ignored by rustc when overflow checks are disabled; enable --overflow-checks"
        ));
    }
    match msg {
        mir::AssertKind::Overflow(op, _, _) => {
            let op = bin_op(*op)?;
            if !op.is_admitted_assert_overflow_op() {
                return Err(format!("unsupported assert overflow operator: {op:?}"));
            }
            Ok(ir::AssertKind::Overflow { op })
        }
        mir::AssertKind::OverflowNeg(_) => Ok(ir::AssertKind::OverflowNeg),
        mir::AssertKind::DivisionByZero(_) => Ok(ir::AssertKind::DivisionByZero),
        mir::AssertKind::RemainderByZero(_) => Ok(ir::AssertKind::RemainderByZero),
        mir::AssertKind::BoundsCheck { .. } => Ok(ir::AssertKind::BoundsCheck),
        mir::AssertKind::NullPointerDereference => Ok(ir::AssertKind::NullPointerDereference),
        other => Err(format!("unsupported assert kind: {other:?}")),
    }
}

/// Canonical crate-qualified definition path with trimming and visible
/// re-export paths disabled, so re-exports under `std::` resolve back to their
/// defining `core::` path.
fn canonical_def_path(tcx: TyCtxt<'_>, def: DefId) -> String {
    rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(tcx.def_path_str(def))
    )
}

/// Recognize an audited `core::num` or `core::cmp` builtin call and validate
/// its exact monomorphized type arguments and argument/destination signature.
fn recognize_core_builtin<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    generic_args: ty::GenericArgsRef<'tcx>,
    arg_tys: &[&ir::Ty],
    dst_ty: &ir::Ty,
) -> Result<ir::CoreBuiltin> {
    if tcx.crate_name(callee_def_id.krate) != sym::core {
        return Err(format!(
            "unsupported external call outside `core`: {}",
            canonical_def_path(tcx, callee_def_id)
        ));
    }
    if tcx
        .codegen_fn_attrs(callee_def_id)
        .flags
        .contains(CodegenFnAttrFlags::TRACK_CALLER)
    {
        return Err(format!(
            "external `#[track_caller]` call is unsupported: {}",
            canonical_def_path(tcx, callee_def_id)
        ));
    }
    let path = canonical_def_path(tcx, callee_def_id);
    let builtin = if let Some(rest) = path.strip_prefix("core::num::<impl ") {
        if !generic_args.is_empty() {
            return Err(format!(
                "unexpected generic arguments on core::num builtin `{path}`: {generic_args:?}"
            ));
        }
        let Some((ty_name, method)) = rest.split_once(">::") else {
            return Err(format!("unsupported core::num call `{path}`"));
        };
        let Some(self_int_ty) = parse_primitive_int_name(ty_name) else {
            return Err(format!("unsupported core::num receiver type `{path}`"));
        };
        let builtin = match method {
            "wrapping_add" => ir::CoreBuiltin::WrappingAdd,
            "wrapping_sub" => ir::CoreBuiltin::WrappingSub,
            "wrapping_mul" => ir::CoreBuiltin::WrappingMul,
            "wrapping_shl" => ir::CoreBuiltin::WrappingShl,
            "wrapping_shr" => ir::CoreBuiltin::WrappingShr,
            "overflowing_add" => ir::CoreBuiltin::OverflowingAdd,
            "overflowing_sub" => ir::CoreBuiltin::OverflowingSub,
            "overflowing_mul" => ir::CoreBuiltin::OverflowingMul,
            "saturating_add" => ir::CoreBuiltin::SaturatingAdd,
            "saturating_sub" => ir::CoreBuiltin::SaturatingSub,
            "checked_add" => ir::CoreBuiltin::CheckedAdd,
            "checked_sub" => ir::CoreBuiltin::CheckedSub,
            "checked_mul" => ir::CoreBuiltin::CheckedMul,
            "leading_zeros" => ir::CoreBuiltin::LeadingZeros,
            "trailing_zeros" => ir::CoreBuiltin::TrailingZeros,
            "is_multiple_of" if !self_int_ty.signed => ir::CoreBuiltin::IsMultipleOf,
            "to_le_bytes" => ir::CoreBuiltin::ToLeBytes,
            "from_le_bytes" => ir::CoreBuiltin::FromLeBytes,
            _ => return Err(format!("unsupported core::num call `{path}`")),
        };
        let expected_self = ir::Ty::Int(self_int_ty);
        if builtin == ir::CoreBuiltin::FromLeBytes {
            if dst_ty != &expected_self {
                return Err(format!(
                    "core::num builtin `{path}` return type disagrees with destination"
                ));
            }
        } else if arg_tys.first().copied() != Some(&expected_self) {
            return Err(format!(
                "core::num builtin `{path}` receiver type disagrees with argument 0"
            ));
        }
        builtin
    } else if path == "core::cmp::min" || path == "core::cmp::max" {
        if generic_args.len() != 1 {
            return Err(format!(
                "expected 1 generic type argument on `{path}`, got {generic_args:?}"
            ));
        }
        let Some(raw_ty) = generic_args[0].as_type() else {
            return Err(format!(
                "expected type generic argument on `{path}`, got {generic_args:?}"
            ));
        };
        let inst_ty = ty(tcx, raw_ty)?;
        if !matches!(inst_ty, ir::Ty::Int(_)) {
            return Err(format!(
                "`{path}` is only admitted for integer types, got {inst_ty:?}"
            ));
        }
        if arg_tys.first().copied() != Some(&inst_ty) {
            return Err(format!(
                "`{path}` generic argument {inst_ty:?} disagrees with argument 0"
            ));
        }
        if path == "core::cmp::min" {
            ir::CoreBuiltin::CmpMin
        } else {
            ir::CoreBuiltin::CmpMax
        }
    } else {
        return Err(format!("unsupported external `core` call: `{path}`"));
    };
    ir::validate_core_builtin_signature(builtin, arg_tys, dst_ty)?;
    Ok(builtin)
}

fn operand_ty<'a>(local_tys: &'a [ir::Ty], op: &'a ir::Operand) -> Result<&'a ir::Ty> {
    match op {
        ir::Operand::Copy { place } | ir::Operand::Move { place } => {
            ir::project_place_ty(local_tys, place, "call argument")
        }
        ir::Operand::Constant { ty, lit } => {
            ir::validate_constant(ty, *lit)?;
            Ok(ty)
        }
    }
}

/// Translate admitted Tier 1 terminators (`Goto`, `SwitchInt`, `Return`,
/// `Unreachable`, `UnwindResume`, operand-free `Assert`, direct monomorphic
/// crate-local `Call`, and audited `CoreBuiltin` `Call`).
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/syntax.rs#L692-L740
fn terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_tys: &[ir::Ty],
    term: &mir::TerminatorKind<'tcx>,
) -> Result<RawTerminator> {
    Ok(match term {
        mir::TerminatorKind::Goto { target } => RawTerminator::Goto {
            block: target.as_u32(),
        },
        mir::TerminatorKind::SwitchInt { discr, targets } => RawTerminator::SwitchInt {
            operand: operand(tcx, discr)?,
            targets: targets
                .iter()
                .map(|(value, block)| ir::SwitchTarget {
                    value,
                    block: block.as_u32(),
                })
                .collect(),
            otherwise: targets.otherwise().as_u32(),
        },
        mir::TerminatorKind::Return => RawTerminator::Ret,
        mir::TerminatorKind::Unreachable => RawTerminator::Unreachable,
        mir::TerminatorKind::UnwindResume => RawTerminator::UnwindResume,
        mir::TerminatorKind::Assert {
            cond,
            expected,
            msg,
            target,
            unwind,
        } => {
            validate_assert_panic_path(tcx, msg)?;
            RawTerminator::Assert {
                cond: operand(tcx, cond)?,
                expected: *expected,
                msg: assert_kind(tcx.sess.overflow_checks(), msg)?,
                target: target.as_u32(),
                unwind: unwind_action(*unwind),
            }
        }
        mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } => {
            let mir::Operand::Constant(func_const) = func else {
                return Err(format!(
                    "indirect or non-constant call is unsupported: {func:?}"
                ));
            };
            let ty::FnDef(callee_def_id, generic_args) = *func_const.const_.ty().kind() else {
                return Err(format!(
                    "non-FnDef call target is unsupported: {:?}",
                    func_const.const_.ty()
                ));
            };
            let translated_args = args
                .iter()
                .map(|arg| operand(tcx, &arg.node))
                .collect::<Result<Vec<_>>>()?;
            let translated_dst = place(tcx, destination)?;
            let translated_target = target.map(|bb| bb.as_u32());
            let translated_unwind = unwind_action(*unwind);
            if let Some(local_callee) = callee_def_id.as_local() {
                if !generic_args.is_empty() {
                    return Err(format!(
                        "generic crate-local call is unsupported: {}<{generic_args:?}>",
                        canonical_def_path(tcx, callee_def_id)
                    ));
                }
                if let Some(intrinsic) = tcx.intrinsic(callee_def_id) {
                    return Err(format!(
                        "call to local intrinsic `{}` is unsupported",
                        intrinsic.name
                    ));
                }
                RawTerminator::Call {
                    callee: local_callee,
                    args: translated_args,
                    destination: translated_dst,
                    target: translated_target,
                    unwind: translated_unwind,
                }
            } else {
                let arg_tys = translated_args
                    .iter()
                    .map(|arg| operand_ty(local_tys, arg))
                    .collect::<Result<Vec<_>>>()?;
                let dst_ty =
                    ir::project_place_ty(local_tys, &translated_dst, "builtin destination")?;
                let builtin =
                    recognize_core_builtin(tcx, callee_def_id, generic_args, &arg_tys, dst_ty)?;
                RawTerminator::CallBuiltin {
                    builtin,
                    args: translated_args,
                    destination: translated_dst,
                    target: translated_target,
                    unwind: translated_unwind,
                }
            }
        }
        other => return Err(format!("unsupported terminator: {other:?}")),
    })
}

/// Bind an item to an owned, versioned source identity for this compiler.
///
/// The pinned compiler calls `def_path_str` a string "suitable for user
/// output"; it is not a stable identifier contract. Anneal's v1 scheme fixes
/// that pinned semantic path printer with trimming and visible reexports
/// disabled. Thus a public alias cannot replace the defining path. In this
/// phase impl paths use their self/trait types rather than file positions.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L115-L124
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2191-L2210
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/print/pretty.rs#L2266-L2306
///
/// Raw compiler indices cannot identify a contract across source edits. Even a
/// raw DefPath disambiguator has "some artificial ordering dependency", notably
/// for impl blocks, so v1 uses the pinned semantic owner/type path instead.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/definitions.rs#L103-L109
///
/// Identities are crate-relative and tied to this scheme and compiler pin.
/// Item renames and owner changes change the key. Toolchain changes require
/// reviewing the scheme and its specifications; this is an Anneal format, not
/// an assumption that Rust's diagnostic formatter remains stable forever.
///
/// Anonymous-owner components can still depend on source order. Such functions
/// are admitted only through selected scope today, whose reviewed roots already
/// expose selectors such as `outer::{closure#0}::inner`. This v1 key exposes
/// the same selector; persistent identity across anonymous-owner edits needs a
/// reviewed stable anchor or a separate binding protocol. It is not established
/// by prefixing a diagnostic path with a version number.
///
/// `ir::Program::try_new` separately refuses duplicate function identities
/// before publishing a subject, so a printer collision cannot share one
/// contract between distinct functions. `capture.rs` performs the
/// corresponding check for the enum keys that [`enum_id`] derives from this
/// identity.
fn item_identity(tcx: TyCtxt<'_>, def: DefId) -> String {
    format!("rust-path-v1::{}", canonical_def_path(tcx, def))
}

/// Key a crate-local enum for `Trusted.MirAst.EnumTy.id`.
///
/// Lean compares this key when deciding enum type equality, and a reviewed
/// specification may name it as a literal. A `DefIndex` would silently select
/// another type once unrelated items are inserted before the enum. The key is
/// instead the first four bytes, read big-endian, of the SHA-256 digest of
/// `anneal:enum:v1:` followed by the enum's `item_identity`. The key thus
/// follows that identity, including its anonymous-owner caveat: renaming or
/// moving the enum changes the key, while inserting or reordering unrelated
/// items does not.
///
/// Truncation to the `u32` width of `ir::EnumTy`'s key can collide, and
/// distinct definitions can print the same path (for example, same-named enums
/// in sibling blocks of one function). `capture.rs` therefore refuses a crate
/// in which two local enum definitions share a key.
pub fn enum_id(tcx: TyCtxt<'_>, def: DefId) -> u32 {
    let digest = Sha256::digest(format!("anneal:enum:v1:{}", item_identity(tcx, def)));
    u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]])
}

/// Key a crate-local struct for `Trusted.MirAst.StructTy.id`, paralleling
/// [`enum_id`] with domain separation prefix `anneal:struct:v1:`.
pub fn struct_id(tcx: TyCtxt<'_>, def: DefId) -> u32 {
    let digest = Sha256::digest(format!("anneal:struct:v1:{}", item_identity(tcx, def)));
    u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]])
}

/// The only codegen flags admitted: hints that change neither the captured
/// body nor its entry contract.
///
/// `#[cold]` "suggests that the attributed function is unlikely to be called
/// which may help the compiler produce better code."
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L91-L92
///
/// `#[track_caller]` appends an implicit caller-location ABI parameter outside
/// MIR locals and affects call/panic semantics; now that `Call` and `Assert`
/// are admitted (and
/// `Trusted.Correspondence.refCallHooks.requiresCallerLocation`
/// returns `false`), `TRACK_CALLER` is refused fail-closed.
/// https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/attributes/codegen.md?plain=1#L763-L779
///
/// Every other flag at the pinned revision is refused; see [`codegen_attrs`].
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L156-L214
const ADMITTED_CODEGEN_FLAGS: CodegenFnAttrFlags = CodegenFnAttrFlags::COLD;

/// Refuse code-generation attributes whose effect the model does not state.
///
/// `codegen_fn_attrs` combines an item's codegen attributes with the settings
/// that the compiler implies for it. Destructuring every field of
/// `CodegenFnAttrs` makes a compiler upgrade that adds a field fail to compile
/// here until the field is classified. Only settings that cannot change what
/// a call executes or what the body may assume are admitted: inlining hints,
/// `#[optimize]` goals, and [`ADMITTED_CODEGEN_FLAGS`]. Everything else is a
/// refusal, including attributes that are rare or impossible on an admitted
/// function, so an unclassified case cannot pass silently.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L60-L112
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L551-L577
fn codegen_attrs(tcx: TyCtxt<'_>, def: LocalDefId) -> Result<()> {
    let CodegenFnAttrs {
        flags,
        inline,
        optimize,
        symbol_name,
        foreign_item_symbol_aliases,
        link_ordinal,
        target_features,
        safe_target_features,
        linkage,
        import_linkage,
        link_section,
        sanitizers,
        instruction_set,
        alignment,
        patchable_function_entry,
        objc_class,
        objc_selector,
    } = tcx.codegen_fn_attrs(def);
    // Refuse `#[target_feature]` functions. `target_features` records "The
    // `#[target_feature(enable = "...")]` attribute and the enabled
    // features", and `safe_target_features` records "Whether the function was
    // declared safe, but has target features". A safe function with target
    // features has `HeaderSafety::SafeTargetFeatures`; the type system "treats
    // this function as an unsafe function", and `FnHeader::safety` maps it to
    // `Safety::Unsafe`. The signature safety read in [`body`] would therefore
    // report `Unsafe`, capture would emit `isUnsafe := true`, and verification
    // would assume `specs.safety` without modeling the hardware-feature entry
    // obligation.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L82-L87
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4668-L4673
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/hir.rs#L4708-L4713
    if !target_features.is_empty() || *safe_target_features {
        return Err("target-feature entry obligations are unsupported".into());
    }
    // `linkage` holds "The `#[linkage = "..."]` attribute on Rust-defined
    // items", whose values are LLVM linkage types. The LLVM that the pinned
    // compiler builds against (its `src/llvm-project` submodule) never emits
    // an `available_externally` definition: "From the linker's perspective,
    // an `available_externally` global is equivalent to an external
    // declaration." `linkonce` globals "are merged with other globals of the
    // same name when linkage occurs", so "the body may be overridden with a
    // more definitive definition later", and `weak` "has the same merging
    // semantics". As with the intrinsics refused in [`body`], calls need not
    // execute the captured body. `import_linkage` is the same attribute on a
    // foreign item, which has no body to capture; refuse it too.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L88-L91
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir/src/attrs/data_structures.rs#L282-L298
    // https://github.com/rust-lang/llvm-project/blob/08c84e69a84d95936296dfcab0e38b34100725d5/llvm/docs/LangRef.rst?plain=1#L237-L264
    if let Some(linkage) = linkage.or(*import_linkage) {
        return Err(format!(
            "linkage attribute {linkage:?} is unsupported: calls need not execute the captured body"
        ));
    }
    // Symbol and section attributes impose link-time obligations that neither
    // the captured body nor `isUnsafe`, which [`body`] reads from the
    // signature alone, records. The Reference requires `unsafe` on each:
    // `export_name` because "a symbol with a custom name may collide with
    // another symbol with the same name (or with a well-known symbol),
    // leading to undefined behavior", `no_mangle` (the `NO_MANGLE` flag
    // below) for the same collision, and `link_section` because "it allows
    // users to place data and code into sections of memory not expecting
    // them". `symbol_name` is "The name this function will be
    // imported/exported under"; weak lang items also receive one.
    // `foreign_item_symbol_aliases` additionally exports this function under
    // the symbol of a foreign item that it should "satisfy", binding calls to
    // that item, whose contract the model does not state, to this body.
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/abi.md?plain=1#L114-L115
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/abi.md?plain=1#L145-L146
    // https://github.com/rust-lang/reference/blob/a286e1ecb8ce193d50056e4bb042eea9b23876ef/src/abi.md?plain=1#L172-L173
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L67-L76
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L92-L94
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L518-L523
    if let Some(name) = symbol_name {
        return Err(format!(
            "exported symbol name `{name}` is unsupported: symbol obligations are unmodeled"
        ));
    }
    if let Some(section) = link_section {
        return Err(format!(
            "link section `{section}` is unsupported: section obligations are unmodeled"
        ));
    }
    if !foreign_item_symbol_aliases.is_empty() {
        return Err("foreign-item symbol aliases are unsupported".into());
    }
    // Refuse every flag outside [`ADMITTED_CODEGEN_FLAGS`].
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/middle/codegen_fn_attrs.rs#L156-L214
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_codegen_ssa/src/codegen_attrs.rs#L348-L353
    let unmodeled = flags.difference(ADMITTED_CODEGEN_FLAGS);
    if !unmodeled.is_empty() {
        return Err(format!(
            "codegen attribute flags {unmodeled:?} are unsupported"
        ));
    }
    match inline {
        InlineAttr::None | InlineAttr::Hint | InlineAttr::Always | InlineAttr::Never => {}
        InlineAttr::Force { .. } => {
            return Err("forced inlining is unsupported".into());
        }
    }
    match optimize {
        OptimizeAttr::Default
        | OptimizeAttr::DoNotOptimize
        | OptimizeAttr::Speed
        | OptimizeAttr::Size => {}
    }
    if *sanitizers != SanitizerFnAttrs::default() {
        return Err(format!("sanitizer settings {sanitizers:?} are unsupported"));
    }
    if let Some(set) = instruction_set {
        return Err(format!("instruction set {set:?} is unsupported"));
    }
    if let Some(align) = alignment {
        return Err(format!("function alignment {align:?} is unsupported"));
    }
    if patchable_function_entry.is_some() {
        return Err("patchable function entries are unsupported".into());
    }
    if link_ordinal.is_some() || objc_class.is_some() || objc_selector.is_some() {
        return Err("link ordinals and Objective-C names are unsupported".into());
    }
    Ok(())
}

/// Recognize and evaluate pure sysroot `core` primitive integer associated
/// constants (`{u,i}{8,16,32,64,128,size}::{MIN,MAX,BITS}`). These constants
/// are part of trusted `core`, contain no crate-local code, and cannot fail
/// post-monomorphization evaluation.
fn eval_admitted_core_scalar_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    uneval: mir::UnevaluatedConst<'tcx>,
    const_ty: ty::Ty<'tcx>,
    span: rustc_span::Span,
) -> Option<ty::ScalarInt> {
    if uneval.promoted.is_some() || !uneval.args.is_empty() || uneval.def.is_local() {
        return None;
    }
    if tcx.crate_name(uneval.def.krate) != sym::core {
        return None;
    }
    if !matches!(ty(tcx, const_ty), Ok(ir::Ty::Int(_))) {
        return None;
    }
    let path = canonical_def_path(tcx, uneval.def);
    let rest = path.strip_prefix("core::num::<impl ")?;
    let (int_name, const_name) = rest.split_once(">::")?;
    let is_prim_int = matches!(
        int_name,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
    );
    let is_const = matches!(const_name, "MIN" | "MAX" | "BITS");
    if !(is_prim_int && is_const) {
        return None;
    }
    tcx.const_eval_resolve(TypingEnv::fully_monomorphized(), uneval, span)
        .ok()
        .and_then(|val| val.try_to_scalar_int())
}

fn is_admitted_core_scalar_required_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    req: &mir::ConstOperand<'tcx>,
) -> bool {
    let mir::Const::Unevaluated(uneval, const_ty) = req.const_ else {
        return false;
    };
    eval_admitted_core_scalar_const(tcx, uneval, const_ty, req.span).is_some()
}

/// Translate the provider's exact body. `required_consts` is explicitly
/// "soundness-critical"; an unrepresented required constant is a refusal,
/// independent of runtime preconditions or whether any return is reachable.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/mir/mod.rs#L265-L271
pub fn body<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId, body: &mir::Body<'tcx>) -> Result<RawBody> {
    if let Some(intrinsic) = tcx.intrinsic(def) {
        return Err(format!(
            "intrinsic `{}` is unsupported: calls need not execute its fallback body",
            intrinsic.name
        ));
    }
    if body.phase != MirPhase::Runtime(RuntimePhase::PostCleanup) {
        return Err(format!("unexpected MIR phase: {:?}", body.phase));
    }
    if body.tainted_by_errors.is_some() || body.coroutine.is_some() || body.spread_arg.is_some() {
        return Err("tainted, coroutine or spread-argument body is unsupported".into());
    }
    let Some(required_consts) = body.required_consts.as_deref() else {
        return Err("required constants are unavailable in the scalar model".into());
    };
    for req in required_consts {
        if !is_admitted_core_scalar_required_const(tcx, req) {
            return Err("required constants are unavailable in the scalar model".into());
        }
    }
    if tcx.generics_of(def).count() != 0 {
        return Err("generic functions require quantified instantiation obligations".into());
    }
    let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
    if signature.abi() != ExternAbi::Rust || signature.c_variadic() {
        return Err("only non-variadic Rust ABI functions are admitted".into());
    }
    codegen_attrs(tcx, def)?;
    let local_tys = body
        .local_decls
        .iter()
        .map(|decl| ty(tcx, decl.ty))
        .collect::<Result<Vec<_>>>()?;
    let blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(id, block)| {
            let statements = block
                .statements
                .iter()
                .enumerate()
                .map(|(index, stmt)| {
                    statement(tcx, &stmt.kind)
                        .map_err(|error| format!("{id:?} statement {index}: {error}"))
                })
                .collect::<Result<Vec<_>>>()?;
            let term = block.terminator.as_ref().ok_or("missing terminator")?;
            let terminator = terminator(tcx, &local_tys, &term.kind)
                .map_err(|error| format!("{id:?} terminator: {error}"))?;
            Ok(RawBlock {
                statements,
                terminator,
                cleanup: block.is_cleanup,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(RawBody {
        arg_count: body.arg_count,
        is_unsafe: signature.safety().is_unsafe(),
        local_tys,
        blocks,
        identity: item_identity(tcx, def.to_def_id()),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn use_retag_is_admitted_only_for_retag_noop_types() {
        let u64_ty = ir::Ty::Int(IntTy {
            width: IntWidth::I64,
            signed: false,
        });
        assert!(ir::check_use_retag(&u64_ty, false).is_ok());
        assert!(ir::check_use_retag(&u64_ty, true).is_ok());
        assert!(ir::check_use_retag(&ir::Ty::Bool, true).is_ok());
        assert!(ir::check_use_retag(&ir::Ty::Unit, true).is_ok());
        assert!(
            ir::check_use_retag(
                &ir::Ty::Tuple {
                    fields: vec![u64_ty, ir::Ty::Bool]
                },
                true
            )
            .is_ok()
        );
        let ety = ir::EnumTy::try_new(
            1,
            IntTy {
                width: IntWidth::Isize,
                signed: true,
            },
            ir::EnumTagRepr::Scalar(IntTy {
                width: IntWidth::I8,
                signed: false,
            }),
            vec![0, 1],
            vec![vec![], vec![]],
        )
        .unwrap();
        assert!(ir::check_use_retag(&ir::Ty::Enum(ety), true).is_ok());
    }

    #[test]
    fn enum_ty_constructor_enforces_discriminant_and_tag_invariants() {
        let isize_discr = IntTy {
            width: IntWidth::Isize,
            signed: true,
        };
        assert!(
            ir::EnumTy::try_new(
                1,
                isize_discr,
                ir::EnumTagRepr::ZeroSized,
                vec![0],
                vec![vec![]]
            )
            .is_ok()
        );
        assert!(
            ir::EnumTy::try_new(1, isize_discr, ir::EnumTagRepr::ZeroSized, vec![], vec![])
                .is_err()
        );
        assert!(
            ir::EnumTy::try_new(
                1,
                isize_discr,
                ir::EnumTagRepr::ZeroSized,
                vec![0, 1],
                vec![vec![], vec![]]
            )
            .is_err()
        );
        let i8_signed = ir::EnumTagRepr::Scalar(IntTy {
            width: IntWidth::I8,
            signed: true,
        });
        let u8_unsigned = ir::EnumTagRepr::Scalar(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        assert!(
            ir::EnumTy::try_new(
                2,
                isize_discr,
                i8_signed.clone(),
                vec![u128::from(u64::MAX), 0, 1],
                vec![vec![], vec![], vec![]],
            )
            .is_ok()
        );
        assert!(
            ir::EnumTy::try_new(2, isize_discr, i8_signed, vec![7, 7], vec![vec![], vec![]])
                .is_err()
        );
        assert!(
            ir::EnumTy::try_new(
                2,
                isize_discr,
                u8_unsigned.clone(),
                vec![u128::from(u64::MAX), 0, 1],
                vec![vec![], vec![], vec![]],
            )
            .is_err()
        );
        assert!(
            ir::EnumTy::try_new(
                3,
                IntTy {
                    width: IntWidth::I8,
                    signed: false,
                },
                u8_unsigned,
                vec![256],
                vec![vec![]],
            )
            .is_err()
        );
    }

    #[test]
    fn body_and_program_constructors_enforce_static_admission_and_unique_identities() {
        let block = ir::Block {
            statements: vec![],
            terminator: ir::Terminator::Ret,
            cleanup: false,
        };
        assert!(
            ir::Body::try_new(
                0,
                false,
                vec![ir::Ty::Unit],
                vec![],
                "rust-path-v1::empty".into(),
            )
            .is_err()
        );
        assert!(
            ir::Body::try_new(
                1,
                false,
                vec![ir::Ty::Unit],
                vec![block.clone()],
                "rust-path-v1::bad_args".into(),
            )
            .is_err()
        );
        assert!(
            ir::Body::try_new(
                0,
                false,
                vec![ir::Ty::Unit],
                vec![ir::Block {
                    statements: vec![ir::Statement::StorageLive { local: 3 }],
                    terminator: ir::Terminator::Ret,
                    cleanup: false,
                }],
                "rust-path-v1::oob_storage".into(),
            )
            .is_err()
        );

        let valid = ir::Body::try_new(
            0,
            false,
            vec![ir::Ty::Unit],
            vec![block],
            "rust-path-v1::entry".into(),
        )
        .unwrap();
        assert!(ir::Program::try_new(ir::Scope::Crate, vec![]).is_err());
        assert!(
            ir::Program::try_new(
                ir::Scope::SelectedUnit {
                    roots: std::collections::BTreeSet::new(),
                },
                vec![valid.clone()],
            )
            .is_err()
        );
        let duplicate =
            ir::Program::try_new(ir::Scope::Crate, vec![valid.clone(), valid]).unwrap_err();
        assert!(duplicate.contains("ambiguous captured function identity"));
    }

    #[test]
    fn body_constructor_rejects_storage_dead_return_place_and_invalid_constants() {
        let u8_ty = ir::Ty::Int(IntTy {
            width: IntWidth::I8,
            signed: false,
        });
        let storage_dead_ret = ir::Body::try_new(
            0,
            false,
            vec![u8_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::StorageDead { local: 0 }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::dead_ret".into(),
        )
        .unwrap_err();
        assert!(storage_dead_ret.contains("StorageDead on return place _0"));

        let u8_overflow = ir::Body::try_new(
            0,
            false,
            vec![u8_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    place: ir::Place::local(0),
                    value: Box::new(ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: u8_ty.clone(),
                            lit: ConstLit::Scalar { bits: 300 },
                        },
                        with_retag: false,
                    }),
                }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::u8_overflow".into(),
        )
        .unwrap_err();
        assert!(u8_overflow.contains("exceeds 8-bit width"));

        let signed_enum = ir::EnumTy::try_new(
            7,
            IntTy {
                width: IntWidth::Isize,
                signed: true,
            },
            ir::EnumTagRepr::Scalar(IntTy {
                width: IntWidth::I8,
                signed: true,
            }),
            vec![u128::from(u64::MAX), 0, 1],
            vec![vec![], vec![], vec![]],
        )
        .unwrap();
        let enum_ty = ir::Ty::Enum(signed_enum);
        let enum_tag_overflow = ir::Body::try_new(
            0,
            false,
            vec![enum_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    place: ir::Place::local(0),
                    value: Box::new(ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: enum_ty.clone(),
                            lit: ConstLit::Scalar { bits: 256 },
                        },
                        with_retag: false,
                    }),
                }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::enum_overflow".into(),
        )
        .unwrap_err();
        assert!(enum_tag_overflow.contains("exceeds 8-bit tag width"));

        let enum_bad_variant = ir::Body::try_new(
            0,
            false,
            vec![enum_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    place: ir::Place::local(0),
                    value: Box::new(ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: enum_ty.clone(),
                            lit: ConstLit::Scalar { bits: 5 },
                        },
                        with_retag: false,
                    }),
                }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::enum_bad_variant".into(),
        )
        .unwrap_err();
        assert!(enum_bad_variant.contains("does not match any declared variant"));

        let valid_neg = ir::Body::try_new(
            0,
            false,
            vec![enum_ty.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    place: ir::Place::local(0),
                    value: Box::new(ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: enum_ty,
                            lit: ConstLit::Scalar { bits: 0xff },
                        },
                        with_retag: false,
                    }),
                }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::enum_neg_tag".into(),
        )
        .unwrap();
        let zst_enum = ir::Ty::Enum(
            ir::EnumTy::try_new(
                8,
                IntTy {
                    width: IntWidth::Isize,
                    signed: true,
                },
                ir::EnumTagRepr::ZeroSized,
                vec![42],
                vec![vec![]],
            )
            .unwrap(),
        );
        let valid_zst = ir::Body::try_new(
            0,
            false,
            vec![zst_enum.clone()],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    place: ir::Place::local(0),
                    value: Box::new(ir::Rvalue::Use {
                        operand: ir::Operand::Constant {
                            ty: zst_enum,
                            lit: ConstLit::ZeroSized,
                        },
                        with_retag: false,
                    }),
                }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::enum_zst".into(),
        )
        .unwrap();
        let prog = ir::Program::try_new(
            ir::Scope::SelectedUnit {
                roots: std::collections::BTreeSet::from(["enum_neg_tag".into(), "enum_zst".into()]),
            },
            vec![valid_neg, valid_zst],
        )
        .unwrap();
        let rendered = crate::lean::render(&prog);
        assert!(
            rendered.contains("ConstLit.scalar (BitVec.ofNat 128 255)"),
            "{rendered}"
        );
        assert!(rendered.contains("ConstLit.zeroSized"), "{rendered}");

        let non_enum_discr = ir::Body::try_new(
            1,
            false,
            vec![u8_ty.clone(), u8_ty],
            vec![ir::Block {
                statements: vec![ir::Statement::Assign {
                    place: ir::Place::local(0),
                    value: Box::new(ir::Rvalue::Discriminant {
                        place: ir::Place::local(1),
                    }),
                }],
                terminator: ir::Terminator::Ret,
                cleanup: false,
            }],
            "rust-path-v1::non_enum_discr".into(),
        )
        .unwrap_err();
        assert!(non_enum_discr.contains("requires an enum place"));
    }

    #[test]
    fn assert_kind_rejects_optional_overflow_asserts_when_overflow_checks_disabled() {
        let add_ov: mir::AssertKind<()> = mir::AssertKind::Overflow(mir::BinOp::Add, (), ());
        let neg_ov: mir::AssertKind<()> = mir::AssertKind::OverflowNeg(());
        let div_ov: mir::AssertKind<()> = mir::AssertKind::Overflow(mir::BinOp::Div, (), ());
        let div_zero: mir::AssertKind<()> = mir::AssertKind::DivisionByZero(());
        let bounds: mir::AssertKind<()> = mir::AssertKind::BoundsCheck { len: (), index: () };

        assert!(assert_kind(false, &add_ov).is_err());
        assert!(assert_kind(false, &neg_ov).is_err());
        assert_eq!(
            assert_kind(true, &add_ov).unwrap(),
            ir::AssertKind::Overflow { op: ir::BinOp::Add }
        );
        assert_eq!(
            assert_kind(true, &neg_ov).unwrap(),
            ir::AssertKind::OverflowNeg
        );
        assert_eq!(
            assert_kind(false, &div_ov).unwrap(),
            ir::AssertKind::Overflow { op: ir::BinOp::Div }
        );
        assert_eq!(
            assert_kind(false, &div_zero).unwrap(),
            ir::AssertKind::DivisionByZero
        );
        assert_eq!(
            assert_kind(true, &bounds).unwrap(),
            ir::AssertKind::BoundsCheck
        );
        assert_eq!(
            assert_kind(false, &bounds).unwrap(),
            ir::AssertKind::BoundsCheck
        );
    }
}
