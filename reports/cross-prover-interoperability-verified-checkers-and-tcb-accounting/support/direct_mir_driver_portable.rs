#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_abi::FieldsShape;
use rustc_data_structures::steal::Steal;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_index::IndexVec;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::mir::{
    AggregateKind, BinOp, Body, BorrowKind, ClearCrossCrate, Const, ConstValue, LocalInfo,
    MirPhase, Operand, Place, ProjectionElem, Promoted, RawPtrKind, RuntimePhase,
    Rvalue, StatementKind, TerminatorKind, UnOp, UnwindAction, UnwindTerminateReason,
    VarDebugInfoContents,
};
#[cfg(rustc_1_98)]
use rustc_middle::mir::WithRetag;
#[cfg(not(rustc_1_98))]
use rustc_middle::mir::RetagKind;
use rustc_middle::ty::{
    EarlyBinder, GenericArgsRef, Instance, InstanceKind, Ty, TyCtxt, TyKind, TypingEnv,
};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::{FileName, DUMMY_SP};
use std::collections::BTreeMap;
use std::sync::Mutex;

static HOOK_LOG: Mutex<Vec<String>> = Mutex::new(Vec::new());
static HOOK_BODIES: Mutex<Vec<String>> = Mutex::new(Vec::new());
static BUILT_LOCAL_SNAPSHOTS: Mutex<Option<BTreeMap<String, BuiltBodySnapshot>>> =
    Mutex::new(None);
static AMIR_EXPORT_FAILED: Mutex<bool> = Mutex::new(false);

#[derive(Clone, Debug)]
struct BuiltVarDebugEntry {
    name: String,
    span: String,
    #[allow(dead_code)]
    scope: usize,
    local_idx: Option<usize>,
    proj_repr: String,
    is_const: bool,
}

#[derive(Clone, Debug)]
struct BuiltBodySnapshot {
    local_count: usize,
    local_infos: Vec<String>,
    var_debug_entries: Vec<BuiltVarDebugEntry>,
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn classify_local_info<'tcx>(info: &ClearCrossCrate<Box<LocalInfo<'tcx>>>) -> &'static str {
    match info {
        ClearCrossCrate::Clear => "Cleared",
        ClearCrossCrate::Set(box_info) => match &**box_info {
            LocalInfo::User(_) => "User",
            LocalInfo::Boring => "Boring",
            LocalInfo::DerefTemp => "DerefTemp",
            LocalInfo::FakeBorrow => "FakeBorrow",
            LocalInfo::StaticRef { .. } => "StaticRef",
            LocalInfo::ConstRef { .. } => "ConstRef",
            LocalInfo::AggregateTemp => "AggregateTemp",
            _ => "OtherLocalInfo",
        },
    }
}

fn extract_var_debug_entries<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<BuiltVarDebugEntry> {
    let sm = tcx.sess.source_map();
    let mut entries = Vec::new();
    for vdi in &body.var_debug_info {
        let name = vdi.name.as_str().to_string();
        let span = sm.span_to_diagnostic_string(vdi.source_info.span);
        let scope = vdi.source_info.scope.index();
        match &vdi.value {
            VarDebugInfoContents::Place(p) => {
                let proj_repr = if p.projection.is_empty() {
                    String::new()
                } else {
                    format!("{:?}", p.projection)
                };
                entries.push(BuiltVarDebugEntry {
                    name,
                    span,
                    scope,
                    local_idx: Some(p.local.index()),
                    proj_repr,
                    is_const: false,
                });
            }
            VarDebugInfoContents::Const(c) => {
                entries.push(BuiltVarDebugEntry {
                    name,
                    span,
                    scope,
                    local_idx: None,
                    proj_repr: format!("{:?}", c),
                    is_const: true,
                });
            }
        }
    }
    entries
}

fn build_var_debug_join_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_path: &str,
    body: &Body<'tcx>,
) -> String {
    let built_map = BUILT_LOCAL_SNAPSHOTS.lock().unwrap();
    let built_snap = built_map.as_ref().and_then(|m| m.get(owner_path));
    let post_vdi = extract_var_debug_entries(tcx, body);
    let vdi_source = if let Some(bs) = built_snap {
        &bs.var_debug_entries
    } else {
        &post_vdi
    };

    let mut joined_locals = Vec::new();
    for (idx, decl) in body.local_decls.iter_enumerated() {
        let l_idx = idx.index();
        let post_info = classify_local_info(&decl.local_info);
        let built_info = built_snap
            .and_then(|bs| bs.local_infos.get(l_idx).map(|s| s.as_str()))
            .unwrap_or("PostBuiltSynthesized");

        let direct_matches: Vec<&BuiltVarDebugEntry> = vdi_source
            .iter()
            .filter(|e| !e.is_const && e.local_idx == Some(l_idx) && e.proj_repr.is_empty())
            .collect();
        let projected_matches: Vec<&BuiltVarDebugEntry> = vdi_source
            .iter()
            .filter(|e| !e.is_const && e.local_idx == Some(l_idx) && !e.proj_repr.is_empty())
            .collect();

        let (binding_kind, var_name, var_span) = if l_idx == 0 {
            ("ReturnPlace", "_0".to_string(), String::new())
        } else if direct_matches.len() == 1 {
            (
                "UniqueUserVar",
                direct_matches[0].name.clone(),
                direct_matches[0].span.clone(),
            )
        } else if direct_matches.len() > 1 {
            let names: Vec<String> = direct_matches.iter().map(|e| e.name.clone()).collect();
            let spans: Vec<String> = direct_matches.iter().map(|e| e.span.clone()).collect();
            (
                "AmbiguousUserVar",
                names.join("|"),
                spans.join("|"),
            )
        } else if !projected_matches.is_empty() {
            let names: Vec<String> = projected_matches
                .iter()
                .map(|e| format!("{}{}", e.name, e.proj_repr))
                .collect();
            (
                "ProjectedCaptureVar",
                names.join("|"),
                projected_matches[0].span.clone(),
            )
        } else if built_snap.map(|bs| l_idx >= bs.local_count).unwrap_or(false) {
            if format!("{:?}", decl.ty) == "bool" {
                (
                    "SynthesizedDropFlag",
                    format!("_drop_flag_{}", l_idx),
                    String::new(),
                )
            } else {
                (
                    "SynthesizedPassTemp",
                    format!("_pass_temp_{}", l_idx),
                    String::new(),
                )
            }
        } else {
            ("CompilerTemp", format!("_{}", l_idx), String::new())
        };

        joined_locals.push(format!(
            "{{\"local\":\"_{}\",\"ty\":\"{}\",\"built_local_info\":\"{}\",\"post_cleanup_local_info\":\"{}\",\"binding_kind\":\"{}\",\"source_name\":\"{}\",\"source_span\":\"{}\"}}",
            l_idx,
            json_escape(&format!("{:?}", decl.ty)),
            built_info,
            post_info,
            binding_kind,
            json_escape(&var_name),
            json_escape(&var_span)
        ));
    }
    format!("[{}]", joined_locals.join(","))
}

fn classify_phase_byte(phase: MirPhase) -> u8 {
    match phase {
        MirPhase::Built => 0x01,
        MirPhase::Analysis(_) => 0x02,
        MirPhase::Runtime(RuntimePhase::Initial) | MirPhase::Runtime(RuntimePhase::PostCleanup) => {
            0x03
        }
        MirPhase::Runtime(RuntimePhase::Optimized) => 0x04,
    }
}

fn resolve_owner_symbol_id(path: &str) -> Result<u8, String> {
    if path == "EffectLog::record" || path.ends_with("::EffectLog::record") {
        Ok(1)
    } else if (path == "<Guard<'a> as core::ops::Drop>::drop"
        || path == "<Guard<'_> as core::ops::Drop>::drop"
        || path == "<Guard<'a> as core::ops::drop::Drop>::drop"
        || path == "<Guard<'_> as core::ops::drop::Drop>::drop")
        && !path.contains("fake")
        && !path.contains("Fake")
    {
        Ok(2)
    } else if path == "may_unwind_op" || path.ends_with("::may_unwind_op") {
        Ok(3)
    } else if path == "partial_init_move_cleanup" || path.ends_with("::partial_init_move_cleanup") {
        Ok(4)
    } else if path == "partial_field_reinit_cleanup"
        || path.ends_with("::partial_field_reinit_cleanup")
    {
        Ok(5)
    } else if path == "ub_boundary_probe" || path.ends_with("::ub_boundary_probe") {
        Ok(6)
    } else if path == "DropGlue<Guard>" || path.ends_with("::DropGlue<Guard>") {
        Ok(7)
    } else if path == "DropGlue<PairGuards>" || path.ends_with("::DropGlue<PairGuards>") {
        Ok(8)
    } else if path == "match_wildcard_probe" || path.ends_with("::match_wildcard_probe") {
        Ok(9)
    } else if path == "assign_underscore_probe" || path.ends_with("::assign_underscore_probe") {
        Ok(10)
    } else if path == "align_to" || path.ends_with("::align_to") {
        Ok(11)
    } else if path == "DstLayout::extend" || path.ends_with("::DstLayout::extend") {
        Ok(12)
    } else if path == "DstLayout::validate_cast_and_convert_metadata"
        || path.ends_with("::DstLayout::validate_cast_and_convert_metadata")
    {
        Ok(13)
    } else if path == "count_valid_prefixes" || path.ends_with("::count_valid_prefixes") {
        Ok(14)
    } else if path.contains("DstLayout") && path.ends_with("::clone") {
        Ok(15)
    } else if path.contains("DstLayout") && path.ends_with("::eq") {
        Ok(16)
    } else if path.contains("DstLayout")
        && (path.ends_with("::assert_fields_are_eq")
            || path.ends_with("::assert_receiver_is_total_eq"))
    {
        Ok(17)
    } else if path.contains("SizeError") && path.ends_with("::clone") {
        Ok(18)
    } else if path.contains("SizeError") && path.ends_with("::eq") {
        Ok(19)
    } else if path == "core::mem::drop::<Guard>" {
        Ok(24)
    } else if path == "unbounded_period4_probe" || path.ends_with("::unbounded_period4_probe") {
        Ok(43)
    } else if path.contains("SizeError")
        && (path.ends_with("::assert_fields_are_eq")
            || path.ends_with("::assert_receiver_is_total_eq"))
    {
        Ok(44)
    } else if path.ends_with("GENERATED_ARCH_ALIGN") {
        Ok(50)
    } else if path.ends_with("STRICT_ALIGN_BONUS") {
        Ok(51)
    } else if path.ends_with("dep_inline_align") {
        Ok(52)
    } else if path.ends_with("dep_non_inline_check") {
        Ok(53)
    } else if path.ends_with("dep_non_inline_check::{closure#0}") {
        Ok(54)
    } else if path.ends_with("macro_generated_probe") {
        Ok(55)
    } else if path.ends_with("verify_cross_crate_entry") {
        Ok(56)
    } else if path == "alpha" || path.ends_with("::alpha") {
        Ok(57)
    } else if path == "beta" || path.ends_with("::beta") {
        Ok(58)
    } else if path.starts_with("synthetic_limit_body_") {
        Ok(60)
    } else {
        Err(format!("UnsupportedOwnerSymbol({})", path))
    }
}

fn resolve_callee_symbol_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: rustc_span::def_id::DefId,
    substs_repr: &str,
) -> Result<u8, String> {
    let path = tcx.def_path_str(callee_def_id);
    if (path == "EffectLog::record" || path.ends_with("::EffectLog::record")) && substs_repr == "[]"
    {
        Ok(1)
    } else if (path == "core::mem::drop" || path == "std::mem::drop")
        && substs_repr.starts_with("[Guard<")
        && !substs_repr.contains("fake")
        && !substs_repr.contains("Fake")
        && !substs_repr.contains('&')
    {
        Ok(24)
    } else if (path == "core::mem::forget" || path == "std::mem::forget")
        && substs_repr.starts_with("[Guard<")
        && !substs_repr.contains("fake")
        && !substs_repr.contains("Fake")
        && !substs_repr.contains('&')
    {
        Ok(25)
    } else if (path == "<Guard<'a> as core::ops::Drop>::drop"
        || path == "<Guard<'_> as core::ops::Drop>::drop"
        || path == "<Guard<'a> as core::ops::drop::Drop>::drop"
        || path == "<Guard<'_> as core::ops::drop::Drop>::drop"
        || ((path == "core::ops::Drop::drop" || path == "core::ops::drop::Drop::drop")
            && substs_repr.starts_with("[Guard<")))
        && !path.contains("fake")
        && !path.contains("Fake")
        && !substs_repr.contains("fake")
        && !substs_repr.contains("Fake")
    {
        Ok(2)
    } else if (path == "may_unwind_op" || path.ends_with("::may_unwind_op")) && substs_repr == "[]"
    {
        Ok(3)
    } else if (path == "partial_init_move_cleanup" || path.ends_with("::partial_init_move_cleanup"))
        && substs_repr == "[]"
    {
        Ok(4)
    } else if (path == "partial_field_reinit_cleanup"
        || path.ends_with("::partial_field_reinit_cleanup"))
        && substs_repr == "[]"
    {
        Ok(5)
    } else if (path == "align_to" || path.ends_with("::align_to")) && substs_repr == "[]" {
        Ok(11)
    } else if (path == "DstLayout::extend" || path.ends_with("::DstLayout::extend"))
        && substs_repr == "[]"
    {
        Ok(12)
    } else if (path == "DstLayout::validate_cast_and_convert_metadata"
        || path.ends_with("::DstLayout::validate_cast_and_convert_metadata"))
        && substs_repr == "[]"
    {
        Ok(13)
    } else if (path == "count_valid_prefixes" || path.ends_with("::count_valid_prefixes"))
        && substs_repr == "[]"
    {
        Ok(14)
    } else if path == "core::num::<impl u32>::wrapping_add" && substs_repr == "[]" {
        Ok(20)
    } else if path == "core::num::<impl u32>::wrapping_mul" && substs_repr == "[]" {
        Ok(21)
    } else if path == "core::num::<impl usize>::checked_add" && substs_repr == "[]" {
        Ok(23)
    } else if path == "core::num::<impl usize>::wrapping_add" && substs_repr == "[]" {
        Ok(40)
    } else if path == "core::num::<impl usize>::wrapping_mul" && substs_repr == "[]" {
        Ok(41)
    } else if path == "core::num::<impl u32>::checked_add" && substs_repr == "[]" {
        Ok(42)
    } else if (path == "unbounded_period4_probe" || path.ends_with("::unbounded_period4_probe"))
        && substs_repr == "[]"
    {
        Ok(43)
    } else if path == "core::fmt::Arguments::<'a>::from_str"
        || path == "core::fmt::Arguments::<'_>::from_str"
    {
        Ok(26)
    } else if path == "core::panicking::panic_fmt" && substs_repr == "[]" {
        Ok(27)
    } else if path == "core::option::Option::<T>::ok_or"
        && substs_repr.contains("usize")
        && substs_repr.contains("SizeError")
    {
        Ok(28)
    } else if path.ends_with("::branch") && substs_repr.contains("SizeError") {
        Ok(29)
    } else if path.ends_with("::from_residual") && substs_repr.contains("SizeError") {
        Ok(30)
    } else if path == "core::option::Option::<T>::is_some" && substs_repr == "[(usize, usize)]" {
        Ok(31)
    } else if path == "dep_inline_align" || path.ends_with("::dep_inline_align") {
        if substs_repr == "[u32]" {
            Ok(32)
        } else if substs_repr == "[]" || substs_repr == "[T]" || substs_repr == "[T/#0]" {
            Ok(52)
        } else {
            Err(format!("UnsupportedCallee({} with substs {})", path, substs_repr))
        }
    } else if (path == "dep_non_inline_check" || path.ends_with("::dep_non_inline_check"))
        && substs_repr == "[]"
    {
        Ok(33)
    } else if (path == "macro_generated_probe" || path.ends_with("::macro_generated_probe"))
        && substs_repr == "[]"
    {
        Ok(34)
    } else if (path == "alpha" || path.ends_with("::alpha")) && substs_repr == "[]" {
        Ok(35)
    } else if (path == "beta" || path.ends_with("::beta")) && substs_repr == "[]" {
        Ok(36)
    } else if path == "core::option::Option::<T>::map"
        && substs_repr.contains("usize")
        && substs_repr.contains("dep_non_inline_check")
    {
        Ok(37)
    } else if path == "core::mem::align_of" || path == "std::mem::align_of" {
        if substs_repr == "[u32]" {
            Ok(39)
        } else if substs_repr == "[T]" || substs_repr == "[T/#0]" {
            Ok(38)
        } else {
            Err(format!("UnsupportedCallee({} with substs {})", path, substs_repr))
        }
    } else {
        Err(format!("UnsupportedCallee({} with substs {})", path, substs_repr))
    }
}

fn encode_type_tag<'tcx>(ty: Ty<'tcx>) -> Result<u8, String> {
    let s = format!("{:?}", ty);
    if s == "()" {
        Ok(1)
    } else if s == "bool" {
        Ok(2)
    } else if s == "u32" {
        Ok(3)
    } else if s == "usize" || s == "isize" {
        Ok(4)
    } else if s == "*const u32" || s == "*mut u32" {
        Ok(5)
    } else if s.contains("EffectLog") && (s.starts_with('&') || s.starts_with('*')) {
        Ok(6)
    } else if s == "EffectLog" {
        Ok(7)
    } else if s.contains("Guard<")
        && !s.contains("PairGuards")
        && !s.contains("fake")
        && !s.contains("Fake")
    {
        if s.starts_with('&') || s.starts_with('*') {
            Ok(22)
        } else {
            Ok(8)
        }
    } else if s.contains("PairGuards") && !s.contains("fake") && !s.contains("Fake") {
        if s.starts_with('&') || s.starts_with('*') {
            Ok(23)
        } else {
            Ok(9)
        }
    } else if s == "DstLayout" || s.ends_with(" DstLayout") {
        Ok(10)
    } else if s == "SizeError" || s.ends_with(" SizeError") {
        Ok(11)
    } else if s.contains("Option<usize>") {
        Ok(12)
    } else if s.contains("Option<(usize, usize)>") {
        Ok(13)
    } else if (s.contains("Result<usize, SizeError>")
        || s.contains("ControlFlow<core::result::Result<core::convert::Infallible, SizeError>, usize>")
        || s.contains("Result<core::convert::Infallible, SizeError>"))
        && !s.contains("DstLayout")
    {
        Ok(14)
    } else if s.contains("DstLayout") && (s.contains("Result<") || s.contains("ControlFlow<")) {
        Ok(15)
    } else if s == "(usize, bool)" {
        Ok(16)
    } else if s == "(usize, usize)" {
        Ok(17)
    } else if s == "(DstLayout, usize)" {
        Ok(18)
    } else if s == "!" || s.contains("Arguments<") {
        Ok(19)
    } else if (s.starts_with('&') && s.ends_with(" usize"))
        || s.contains("dep_non_inline_check::{closure#0}")
    {
        Ok(20)
    } else if s == "(u32, bool)" {
        Ok(21)
    } else {
        Err(format!("UnsupportedLocalType({})", s))
    }
}

fn encode_place_v3<'tcx>(place: &Place<'tcx>, local_count: usize) -> Result<[u8; 2], String> {
    let l_idx = place.local.index();
    if l_idx >= local_count || l_idx >= 64 {
        return Err(format!(
            "LocalIndexOutOfBounds(local={}, local_count={})",
            l_idx, local_count
        ));
    }
    let elems: Vec<_> = place.projection.iter().collect();
    let proj_code: u8 = match elems.as_slice() {
        [] => 0,
        [ProjectionElem::Field(f, _)] => match f.index() {
            0 => 1,
            1 => 2,
            2 => 3,
            other => {
                return Err(format!("UnsupportedFieldIndex({})", other));
            }
        },
        [ProjectionElem::Deref] => 4,
        [ProjectionElem::Deref, ProjectionElem::Field(f, _)] => match f.index() {
            0 => 5,
            1 => 6,
            2 => 7,
            other => {
                return Err(format!("UnsupportedDerefFieldIndex({})", other));
            }
        },
        [ProjectionElem::Downcast(_, v), ProjectionElem::Field(f, _)] => {
            if f.index() != 0 {
                return Err(format!(
                    "UnsupportedDowncastField(variant={}, field={})",
                    v.index(),
                    f.index()
                ));
            }
            match v.index() {
                0 => 8,
                1 => 9,
                other => {
                    return Err(format!("UnsupportedDowncastVariant({})", other));
                }
            }
        }
        _ => {
            return Err(format!("UnsupportedProjectionChain({:?})", place.projection));
        }
    };
    Ok([l_idx as u8, proj_code])
}

fn eval_const_operand_v3<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    c: &Const<'tcx>,
) -> Result<[u8; 2], String> {
    let ty = c.ty();
    let ty_str = format!("{:?}", ty);
    if ty_str == "()" {
        return Ok([131, 0]);
    }
    if ty_str == "SizeError" {
        return Ok([131, 1]);
    }
    if ty_str.contains("str") {
        return Ok([131, 2]);
    }
    let val = match c {
        Const::Val(v, _) => *v,
        Const::Unevaluated(uv, _) => match tcx.const_eval_resolve(typing_env, *uv, DUMMY_SP) {
            Ok(v) => v,
            Err(e) => {
                return Err(format!("ConstEvalFailed({:?}: {:?})", c, e));
            }
        },
        Const::Ty(_, ct) => {
            return Err(format!("UnsupportedTypeConst({:?})", ct));
        }
    };
    match val {
        ConstValue::ZeroSized => {
            if ty_str == "()" {
                Ok([131, 0])
            } else if ty_str == "SizeError" {
                Ok([131, 1])
            } else {
                Err(format!("UnsupportedZeroSizedConst({})", ty_str))
            }
        }
        ConstValue::Scalar(rustc_middle::mir::interpret::Scalar::Int(si)) => {
            let bits = si.to_bits_unchecked();
            match ty.kind() {
                TyKind::Bool => Ok([128, if bits != 0 { 1 } else { 0 }]),
                TyKind::Uint(rustc_middle::ty::UintTy::U32) => {
                    if bits <= 255 {
                        Ok([129, bits as u8])
                    } else {
                        Err(format!("ConstU32ExceedsByteRange({})", bits))
                    }
                }
                TyKind::Uint(rustc_middle::ty::UintTy::Usize) => {
                    if bits <= 255 {
                        Ok([130, bits as u8])
                    } else {
                        Err(format!("ConstUsizeExceedsByteRange({})", bits))
                    }
                }
                _ => Err(format!("UnsupportedScalarConstType({:?}, bits={})", ty, bits)),
            }
        }
        ConstValue::Slice { .. } | ConstValue::Indirect { .. } => {
            if ty_str.contains("str") {
                Ok([131, 2])
            } else {
                Err(format!("UnsupportedNonScalarConst({:?})", c))
            }
        }
        _ => Err(format!("UnsupportedConstValue({:?})", c)),
    }
}

fn encode_operand_v3<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    op: &Operand<'tcx>,
    local_count: usize,
) -> Result<[u8; 2], String> {
    match op {
        Operand::Copy(p) => {
            let [l, pr] = encode_place_v3(p, local_count)?;
            Ok([l, pr])
        }
        Operand::Move(p) => {
            let [l, pr] = encode_place_v3(p, local_count)?;
            Ok([l + 64, pr])
        }
        Operand::Constant(box_c) => eval_const_operand_v3(tcx, typing_env, &box_c.const_),
        Operand::RuntimeChecks(rc) => Err(format!("UnsupportedRuntimeChecksOperand({:?})", rc)),
    }
}

fn encode_binop_v3(op: BinOp) -> Result<u8, String> {
    match op {
        BinOp::Eq => Ok(1),
        BinOp::Ne => Ok(2),
        BinOp::Lt => Ok(3),
        BinOp::Le => Ok(4),
        BinOp::Gt => Ok(5),
        BinOp::Ge => Ok(6),
        BinOp::Add => Ok(7),
        BinOp::Sub => Ok(8),
        BinOp::Mul => Ok(9),
        BinOp::Div => Ok(10),
        BinOp::Rem => Ok(11),
        BinOp::BitAnd => Ok(12),
        BinOp::AddWithOverflow => Ok(13),
        BinOp::SubWithOverflow => Ok(14),
        BinOp::MulWithOverflow => Ok(15),
        other => Err(format!("UnsupportedBinOp({:?})", other)),
    }
}

fn encode_unwind_v3(uw: &UnwindAction, block_count: usize) -> Result<u8, String> {
    match uw {
        UnwindAction::Cleanup(b) => {
            let idx = b.index();
            if idx >= block_count || idx >= 32 {
                Err(format!(
                    "UnwindCleanupTargetOutOfBounds(bb={}, block_count={})",
                    idx, block_count
                ))
            } else {
                Ok(idx as u8)
            }
        }
        UnwindAction::Continue => Ok(252),
        UnwindAction::Unreachable => Ok(253),
        UnwindAction::Terminate(UnwindTerminateReason::Abi) => Ok(254),
        UnwindAction::Terminate(UnwindTerminateReason::InCleanup) => Ok(255),
    }
}

fn resolve_drop_glue_sym_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Result<u8, String> {
    let s = format!("{:?}", ty);
    if s.contains("Guard<") && !s.contains("PairGuards") {
        Ok(7)
    } else if s.contains("PairGuards") {
        Ok(8)
    } else if !ty.needs_drop(tcx, typing_env) {
        Ok(0)
    } else {
        Err(format!("UnsupportedDropGlueType({})", s))
    }
}

fn encode_body_amir_v3<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner_path: &str,
    body_id: u8,
    origin_kind: u8,
    body: &Body<'tcx>,
    simulate_drift: Option<&str>,
) -> Result<Vec<u8>, String> {
    let sym_id = resolve_owner_symbol_id(owner_path)?;
    let phase_byte = classify_phase_byte(body.phase);
    let local_count = body.local_decls.len();
    if local_count == 0 || local_count > 64 {
        return Err(format!(
            "ExceedsLocalLimit(owner={}, locals={}, max=64)",
            owner_path, local_count
        ));
    }
    let arg_count = body.arg_count;
    if arg_count >= local_count {
        return Err(format!(
            "InvalidArgCount(owner={}, args={}, locals={})",
            owner_path, arg_count, local_count
        ));
    }
    let block_count = body.basic_blocks.len();
    if block_count == 0 || block_count > 32 {
        return Err(format!(
            "ExceedsBlockLimit(owner={}, blocks={}, max=32)",
            owner_path, block_count
        ));
    }

    let typing_env = body.typing_env(tcx);
    let mut local_type_bytes = Vec::with_capacity(local_count);
    for decl in body.local_decls.iter() {
        local_type_bytes.push(encode_type_tag(decl.ty)?);
    }

    let mut out = Vec::new();
    out.push(body_id);
    out.push(sym_id);
    out.push(origin_kind);
    out.push(phase_byte);
    out.push(local_count as u8);
    out.push(arg_count as u8);
    out.push(block_count as u8);
    out.extend_from_slice(&local_type_bytes);

    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        let is_cleanup: u8 = if bb_data.is_cleanup { 1 } else { 0 };
        if bb_data.statements.len() > 64 {
            return Err(format!(
                "ExceedsStmtLimit(owner={}, bb={}, stmts={}, max=64)",
                owner_path,
                bb_idx.index(),
                bb_data.statements.len()
            ));
        }
        let mut encoded_stmts: Vec<Vec<u8>> = Vec::new();
        for stmt in &bb_data.statements {
            let st_bytes: Vec<u8> = match &stmt.kind {
                StatementKind::Assign(assign_box) => {
                    let (lhs, rval) = &**assign_box;
                    let [dst_l, dst_p] = encode_place_v3(lhs, local_count)?;
                    match rval {
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(op, WithRetag::No) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x10, dst_l, dst_p, b0, b1]
                        }
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(op, WithRetag::Yes) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x11, dst_l, dst_p, b0, b1]
                        }
                        #[cfg(not(rustc_1_98))]
                        Rvalue::Use(op) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x10, dst_l, dst_p, b0, b1]
                        }
                        Rvalue::CopyForDeref(src_p) => {
                            let [src_l, src_pr] = encode_place_v3(src_p, local_count)?;
                            vec![0x12, dst_l, dst_p, src_l, src_pr]
                        }
                        Rvalue::Ref(_, bkind, src_p) => {
                            let [src_l, src_pr] = encode_place_v3(src_p, local_count)?;
                            let rk: u8 = match bkind {
                                BorrowKind::Shared => 0,
                                BorrowKind::Mut { .. } => 1,
                                BorrowKind::Fake(_) => {
                                    return Err(format!("UnsupportedFakeBorrow({:?})", stmt));
                                }
                            };
                            vec![0x13, dst_l, dst_p, rk, src_l, src_pr]
                        }
                        Rvalue::RawPtr(ptr_kind, src_p) => {
                            let [src_l, src_pr] = encode_place_v3(src_p, local_count)?;
                            let rk: u8 = match ptr_kind {
                                RawPtrKind::Const => 2,
                                RawPtrKind::Mut => 3,
                                RawPtrKind::FakeForPtrMetadata => 2,
                            };
                            vec![0x13, dst_l, dst_p, rk, src_l, src_pr]
                        }
                        Rvalue::Discriminant(src_p) => {
                            let [src_l, src_pr] = encode_place_v3(src_p, local_count)?;
                            vec![0x14, dst_l, dst_p, src_l, src_pr]
                        }
                        Rvalue::BinaryOp(bop, box_ops) => {
                            let btag = encode_binop_v3(*bop)?;
                            let [l0, l1] =
                                encode_operand_v3(tcx, typing_env, &box_ops.0, local_count)?;
                            let [r0, r1] =
                                encode_operand_v3(tcx, typing_env, &box_ops.1, local_count)?;
                            vec![0x15, dst_l, dst_p, btag, l0, l1, r0, r1]
                        }
                        Rvalue::UnaryOp(uop, src_op) => {
                            let utag: u8 = match uop {
                                UnOp::Not => 1,
                                other => {
                                    return Err(format!("UnsupportedUnOp({:?})", other));
                                }
                            };
                            let [s0, s1] =
                                encode_operand_v3(tcx, typing_env, src_op, local_count)?;
                            vec![0x16, dst_l, dst_p, utag, s0, s1]
                        }
                        Rvalue::Aggregate(agg_box, fields) => {
                            let mut op_bytes: Vec<[u8; 2]> = Vec::with_capacity(fields.len());
                            for f_op in fields.iter() {
                                op_bytes.push(encode_operand_v3(
                                    tcx,
                                    typing_env,
                                    f_op,
                                    local_count,
                                )?);
                            }
                            match (&**agg_box, op_bytes.as_slice()) {
                                (AggregateKind::Adt(did, v_idx, _, _, _), []) => {
                                    let adt_path = tcx.def_path_str(*did);
                                    let agg0_tag: u8 = if adt_path.ends_with("SizeError") {
                                        1
                                    } else if adt_path.ends_with("Option") && v_idx.index() == 0 {
                                        2
                                    } else {
                                        return Err(format!(
                                            "UnsupportedZeroFieldAdt({}, variant={})",
                                            adt_path,
                                            v_idx.index()
                                        ));
                                    };
                                    vec![0x17, dst_l, dst_p, agg0_tag]
                                }
                                (AggregateKind::Adt(did, v_idx, _, _, _), [[a0, a1]]) => {
                                    let adt_path = tcx.def_path_str(*did);
                                    let agg1_tag: u8 = if (adt_path.ends_with("Result")
                                        && v_idx.index() == 0)
                                        || (adt_path.ends_with("Option") && v_idx.index() == 1)
                                    {
                                        1
                                    } else if adt_path.ends_with("Result") && v_idx.index() == 1 {
                                        2
                                    } else {
                                        return Err(format!(
                                            "UnsupportedOneFieldAdt({}, variant={})",
                                            adt_path,
                                            v_idx.index()
                                        ));
                                    };
                                    vec![0x18, dst_l, dst_p, agg1_tag, *a0, *a1]
                                }
                                (AggregateKind::Closure(did, _), [[a0, a1]]) => {
                                    let c_path = tcx.def_path_str(*did);
                                    if c_path.contains("dep_non_inline_check") {
                                        vec![0x18, dst_l, dst_p, 3, *a0, *a1]
                                    } else {
                                        return Err(format!("UnsupportedClosureAggregate({})", c_path));
                                    }
                                }
                                (AggregateKind::Adt(did, _, _, _, _), [[a0, a1], [b0, b1]]) => {
                                    let adt_path = tcx.def_path_str(*did);
                                    let agg2_tag: u8 = if adt_path.ends_with("Guard") {
                                        1
                                    } else if adt_path.ends_with("PairGuards") {
                                        2
                                    } else if adt_path.ends_with("EffectLog") {
                                        3
                                    } else {
                                        return Err(format!(
                                            "UnsupportedTwoFieldAdt({})",
                                            adt_path
                                        ));
                                    };
                                    let f0_val = if simulate_drift == Some("alter_reinit_constant")
                                        && sym_id == 5
                                        && agg2_tag == 1
                                        && *a0 == 129
                                        && *a1 == 3
                                    {
                                        4u8
                                    } else {
                                        *a1
                                    };
                                    vec![0x19, dst_l, dst_p, agg2_tag, *a0, f0_val, *b0, *b1]
                                }
                                (AggregateKind::Tuple, [[a0, a1], [b0, b1]]) => {
                                    vec![0x19, dst_l, dst_p, 4, *a0, *a1, *b0, *b1]
                                }
                                (
                                    AggregateKind::Adt(did, _, _, _, _),
                                    [[a0, a1], [b0, b1], [c0, c1]],
                                ) => {
                                    let adt_path = tcx.def_path_str(*did);
                                    if adt_path.ends_with("DstLayout") {
                                        vec![
                                            0x1A, dst_l, dst_p, 1, *a0, *a1, *b0, *b1, *c0, *c1,
                                        ]
                                    } else {
                                        return Err(format!(
                                            "UnsupportedThreeFieldAdt({})",
                                            adt_path
                                        ));
                                    }
                                }
                                _ => {
                                    return Err(format!(
                                        "UnsupportedAggregate({:?}, arity={})",
                                        agg_box,
                                        fields.len()
                                    ));
                                }
                            }
                        }
                        other => {
                            return Err(format!(
                                "UnsupportedRvalue(owner={}, bb={}, rval={:?})",
                                owner_path,
                                bb_idx.index(),
                                other
                            ));
                        }
                    }
                }
                StatementKind::StorageLive(l) => {
                    let idx = l.index();
                    if idx >= local_count || idx >= 64 {
                        return Err(format!("StorageLiveOutOfBounds({})", idx));
                    }
                    vec![0x20, idx as u8]
                }
                StatementKind::StorageDead(l) => {
                    let idx = l.index();
                    if idx >= local_count || idx >= 64 {
                        return Err(format!("StorageDeadOutOfBounds({})", idx));
                    }
                    vec![0x21, idx as u8]
                }
                StatementKind::Nop => vec![0x22],
                StatementKind::PlaceMention(p) => {
                    if simulate_drift == Some("strip_place_mention") {
                        vec![0x22]
                    } else {
                        let [src_l, src_pr] = encode_place_v3(p, local_count)?;
                        vec![0x30, src_l, src_pr]
                    }
                }
                #[cfg(not(rustc_1_98))]
                StatementKind::Retag(rk, box_p) => {
                    let rk_byte: u8 = match rk {
                        RetagKind::Default => 0,
                        RetagKind::FnEntry => 1,
                        RetagKind::TwoPhase => 2,
                        RetagKind::Raw => 3,
                    };
                    let [src_l, src_pr] = encode_place_v3(box_p, local_count)?;
                    vec![0x31, rk_byte, src_l, src_pr]
                }
                other => {
                    return Err(format!(
                        "UnsupportedStatement(owner={}, bb={}, stmt={:?})",
                        owner_path,
                        bb_idx.index(),
                        other
                    ));
                }
            };
            encoded_stmts.push(st_bytes);
        }

        let term = bb_data.terminator.as_ref().ok_or_else(|| {
            format!(
                "MissingTerminator(owner={}, bb={})",
                owner_path,
                bb_idx.index()
            )
        })?;

        let check_target = |b: rustc_middle::mir::BasicBlock| -> Result<u8, String> {
            let idx = b.index();
            if idx >= block_count || idx >= 32 {
                Err(format!(
                    "BranchTargetOutOfBounds(owner={}, bb={}, target={}, block_count={})",
                    owner_path,
                    bb_idx.index(),
                    idx,
                    block_count
                ))
            } else {
                Ok(idx as u8)
            }
        };

        let term_bytes: Vec<u8> = match &term.kind {
            TerminatorKind::Return => vec![0x40],
            TerminatorKind::UnwindResume => vec![0x41],
            TerminatorKind::UnwindTerminate(reason) => {
                let r_byte: u8 = match reason {
                    UnwindTerminateReason::Abi => 1,
                    UnwindTerminateReason::InCleanup => 2,
                };
                vec![0x42, r_byte]
            }
            TerminatorKind::Unreachable => vec![0x43],
            TerminatorKind::Goto { target } => {
                let t = check_target(*target)?;
                vec![0x44, t]
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let [d0, d1] = encode_operand_v3(tcx, typing_env, discr, local_count)?;
                let branches: Vec<(u128, rustc_middle::mir::BasicBlock)> =
                    targets.iter().collect();
                let other_bb = check_target(targets.otherwise())?;
                match branches.as_slice() {
                    [(v0, b0)] => {
                        if *v0 > 255 {
                            return Err(format!("SwitchIntValueExceedsByteRange({})", v0));
                        }
                        let tb0 = check_target(*b0)?;
                        let (arm_bb, oth_bb) =
                            if simulate_drift == Some("swap_extend_slice_branch")
                                && sym_id == 12
                                && bb_idx.index() == 11
                            {
                                (other_bb, tb0)
                            } else {
                                (tb0, other_bb)
                            };
                        vec![0x45, d0, d1, *v0 as u8, arm_bb, oth_bb]
                    }
                    [(v0, b0), (v1, b1)] => {
                        if *v0 > 255 || *v1 > 255 {
                            return Err(format!(
                                "SwitchIntValueExceedsByteRange({}, {})",
                                v0, v1
                            ));
                        }
                        let tb0 = check_target(*b0)?;
                        let tb1 = check_target(*b1)?;
                        vec![0x46, d0, d1, *v0 as u8, tb0, *v1 as u8, tb1, other_bb]
                    }
                    _ => {
                        return Err(format!(
                            "UnsupportedSwitchIntArity(owner={}, bb={}, arms={})",
                            owner_path,
                            bb_idx.index(),
                            branches.len()
                        ));
                    }
                }
            }
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                ..
            } => {
                let t_bb = check_target(*target)?;
                if simulate_drift == Some("strip_cleanup_drop") && bb_data.is_cleanup {
                    vec![0x44, t_bb]
                } else {
                    let [pl_l, pl_p] = encode_place_v3(place, local_count)?;
                    let place_ty = place.ty(&body.local_decls, tcx).ty;
                    let glue_sym = resolve_drop_glue_sym_id(tcx, typing_env, place_ty)?;
                    let uw_b = encode_unwind_v3(unwind, block_count)?;
                    vec![0x47, pl_l, pl_p, glue_sym, t_bb, uw_b]
                }
            }
            TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => {
                let [c0, c1] = encode_operand_v3(tcx, typing_env, cond, local_count)?;
                let exp_b: u8 = if *expected { 1 } else { 0 };
                let t_bb = check_target(*target)?;
                let uw_b = encode_unwind_v3(unwind, block_count)?;
                vec![0x48, c0, c1, exp_b, t_bb, uw_b]
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                let (callee_def_id, substs) = func.const_fn_def().ok_or_else(|| {
                    format!(
                        "UnsupportedIndirectCall(owner={}, bb={}, func={:?})",
                        owner_path,
                        bb_idx.index(),
                        func
                    )
                })?;
                let substs_repr = format!("{:?}", substs);
                let callee_sym = resolve_callee_symbol_id(tcx, callee_def_id, &substs_repr)?;
                let [dst_l, dst_p] = encode_place_v3(destination, local_count)?;
                let t_opt: u8 = match target {
                    Some(b) => check_target(*b)?,
                    None => 255,
                };
                let uw_b = encode_unwind_v3(unwind, block_count)?;
                if args.len() > 4 {
                    return Err(format!(
                        "UnsupportedCallArity(owner={}, bb={}, args={})",
                        owner_path,
                        bb_idx.index(),
                        args.len()
                    ));
                }
                let op_byte: u8 = 0x49 + (args.len() as u8);
                let mut v = vec![op_byte, callee_sym, dst_l, dst_p, t_opt, uw_b];
                for a in args.iter() {
                    let [a0, a1] = encode_operand_v3(tcx, typing_env, &a.node, local_count)?;
                    v.push(a0);
                    v.push(a1);
                }
                v
            }
            other => {
                return Err(format!(
                    "UnsupportedTerminator(owner={}, bb={}, term={:?})",
                    owner_path,
                    bb_idx.index(),
                    other
                ));
            }
        };

        out.push(is_cleanup);
        out.push(encoded_stmts.len() as u8);
        for st_b in encoded_stmts {
            out.extend_from_slice(&st_b);
        }
        out.extend_from_slice(&term_bytes);
    }

    Ok(out)
}

fn export_full_body_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: &str,
    origin_kind: &str,
    stage: &str,
    body: &Body<'tcx>,
) -> String {
    let mut locals_json = Vec::new();
    for (idx, decl) in body.local_decls.iter_enumerated() {
        locals_json.push(format!(
            "{{\"local\":\"_{}\",\"mutability\":\"{:?}\",\"local_info\":\"{}\",\"ty\":\"{}\"}}",
            idx.index(),
            decl.mutability,
            classify_local_info(&decl.local_info),
            json_escape(&format!("{:?}", decl.ty))
        ));
    }

    let mut blocks_json = Vec::new();
    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        let mut stmts_json = Vec::new();
        for stmt in &bb_data.statements {
            let kind_tag = match &stmt.kind {
                StatementKind::Assign(assign_box) => {
                    let (_, rval) = &**assign_box;
                    match rval {
                        Rvalue::CopyForDeref(_) => "Assign(CopyForDeref)",
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::Yes) => "Assign(Use,WithRetag::Yes)",
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::No) => "Assign(Use,WithRetag::No)",
                        #[cfg(not(rustc_1_98))]
                        Rvalue::Use(_) => "Assign(Use,Pre198)",
                        _ => "Assign(Other)",
                    }
                }
                StatementKind::StorageLive(_) => "StorageLive",
                StatementKind::StorageDead(_) => "StorageDead",
                StatementKind::FakeRead(_) => "FakeRead",
                StatementKind::PlaceMention(_) => "PlaceMention",
                _ => "Other",
            };
            stmts_json.push(format!(
                "{{\"kind\":\"{}\",\"repr\":\"{}\"}}",
                kind_tag,
                json_escape(&format!("{:?}", stmt))
            ));
        }

        let term_json = if let Some(term) = &bb_data.terminator {
            let term_tag = match &term.kind {
                TerminatorKind::Goto { .. } => "Goto",
                TerminatorKind::SwitchInt { .. } => "SwitchInt",
                TerminatorKind::UnwindResume => "UnwindResume",
                TerminatorKind::UnwindTerminate(_) => "UnwindTerminate",
                TerminatorKind::Return => "Return",
                TerminatorKind::Unreachable => "Unreachable",
                TerminatorKind::Drop { .. } => "Drop",
                TerminatorKind::Call { .. } => "Call",
                TerminatorKind::TailCall { .. } => "TailCall",
                TerminatorKind::Assert { .. } => "Assert",
                TerminatorKind::Yield { .. } => "Yield",
                TerminatorKind::CoroutineDrop => "CoroutineDrop",
                TerminatorKind::FalseEdge { .. } => "FalseEdge",
                TerminatorKind::FalseUnwind { .. } => "FalseUnwind",
                TerminatorKind::InlineAsm { .. } => "InlineAsm",
            };
            let succs: Vec<String> = term
                .successors()
                .map(|b| format!("\"bb{}\"", b.index()))
                .collect();
            format!(
                "{{\"kind\":\"{}\",\"repr\":\"{}\",\"successors\":[{}]}}",
                term_tag,
                json_escape(&format!("{:?}", term.kind)),
                succs.join(",")
            )
        } else {
            "null".to_string()
        };

        blocks_json.push(format!(
            "{{\"block\":\"bb{}\",\"is_cleanup\":{},\"statements\":[{}],\"terminator\":{}}}",
            bb_idx.index(),
            bb_data.is_cleanup,
            stmts_json.join(","),
            term_json
        ));
    }

    let var_debug_join = build_var_debug_join_json(tcx, owner, body);

    format!(
        "{{\"owner\":\"{}\",\"origin_kind\":\"{}\",\"stage\":\"{}\",\"phase\":\"{:?}\",\"locals\":[{}],\"var_debug_join\":{},\"basic_blocks\":[{}]}}",
        json_escape(owner),
        json_escape(origin_kind),
        json_escape(stage),
        body.phase,
        locals_json.join(","),
        var_debug_join,
        blocks_json.join(",")
    )
}

fn summarize_body<'tcx>(
    _tcx: TyCtxt<'tcx>,
    name: &str,
    origin_kind: &str,
    stage: &str,
    body: &Body<'tcx>,
) -> String {
    let mut drop_count = 0usize;
    let mut call_count = 0usize;
    let mut switch_count = 0usize;
    let mut resume_count = 0usize;
    let mut abort_count = 0usize;
    let mut return_count = 0usize;
    let mut goto_count = 0usize;
    let mut assign_count = 0usize;
    let mut storage_live_count = 0usize;
    let mut storage_dead_count = 0usize;
    let mut fake_read_count = 0usize;
    let mut place_mention_count = 0usize;
    let retag_stmt_count = 0usize;
    let mut copy_for_deref_count = 0usize;
    #[allow(unused_mut)]
    let mut use_retag_yes_count = 0usize;
    let mut use_retag_no_count = 0usize;
    let mut local_info_set_count = 0usize;
    let mut local_info_cleared_count = 0usize;

    for decl in body.local_decls.iter() {
        match &decl.local_info {
            ClearCrossCrate::Clear => local_info_cleared_count += 1,
            ClearCrossCrate::Set(_) => local_info_set_count += 1,
        }
    }

    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign(assign_box) => {
                    let (_, rval) = &**assign_box;
                    assign_count += 1;
                    match rval {
                        Rvalue::CopyForDeref(_) => copy_for_deref_count += 1,
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::Yes) => use_retag_yes_count += 1,
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::No) => use_retag_no_count += 1,
                        #[cfg(not(rustc_1_98))]
                        Rvalue::Use(_) => use_retag_no_count += 1,
                        _ => {}
                    }
                }
                StatementKind::StorageLive(_) => storage_live_count += 1,
                StatementKind::StorageDead(_) => storage_dead_count += 1,
                StatementKind::FakeRead(_) => fake_read_count += 1,
                StatementKind::PlaceMention(_) => place_mention_count += 1,
                _ => {}
            }
        }
        if let Some(term) = &bb_data.terminator {
            match &term.kind {
                TerminatorKind::Drop { .. } => drop_count += 1,
                TerminatorKind::Call { .. } => call_count += 1,
                TerminatorKind::SwitchInt { .. } => switch_count += 1,
                TerminatorKind::UnwindResume => resume_count += 1,
                TerminatorKind::UnwindTerminate(_) => abort_count += 1,
                TerminatorKind::Return => return_count += 1,
                TerminatorKind::Goto { .. } => goto_count += 1,
                _ => {}
            }
        }
    }

    format!(
        "{{\"owner\":\"{}\",\"origin_kind\":\"{}\",\"stage\":\"{}\",\"phase\":\"{:?}\",\"blocks\":{},\"locals\":{},\"var_debug_count\":{},\"local_info_set\":{},\"local_info_cleared\":{},\"assigns\":{},\"storage_live\":{},\"storage_dead\":{},\"fake_reads\":{},\"place_mentions\":{},\"retag_stmts\":{},\"copy_for_deref\":{},\"use_retag_yes\":{},\"use_retag_no\":{},\"drops\":{},\"calls\":{},\"switches\":{},\"returns\":{},\"resumes\":{},\"terminates\":{},\"gotos\":{},\"required_consts\":{}}}",
        json_escape(name),
        json_escape(origin_kind),
        json_escape(stage),
        body.phase,
        body.basic_blocks.len(),
        body.local_decls.len(),
        body.var_debug_info.len(),
        local_info_set_count,
        local_info_cleared_count,
        assign_count,
        storage_live_count,
        storage_dead_count,
        fake_read_count,
        place_mention_count,
        retag_stmt_count,
        copy_for_deref_count,
        use_retag_yes_count,
        use_retag_no_count,
        drop_count,
        call_count,
        switch_count,
        return_count,
        resume_count,
        abort_count,
        goto_count,
        body.required_consts.as_ref().map(|v| v.len()).unwrap_or(0)
    )
}

fn hook_mir_built<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> &'tcx Steal<Body<'tcx>> {
    let stolen_res = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_built)(tcx, def_id);
    if !stolen_res.is_stolen() {
        let body = stolen_res.borrow();
        let path = tcx.def_path_str(def_id);
        let snap = BuiltBodySnapshot {
            local_count: body.local_decls.len(),
            local_infos: body
                .local_decls
                .iter()
                .map(|d| classify_local_info(&d.local_info).to_string())
                .collect(),
            var_debug_entries: extract_var_debug_entries(tcx, &body),
        };
        let mut guard = BUILT_LOCAL_SNAPSHOTS.lock().unwrap();
        let map = guard.get_or_insert_with(BTreeMap::new);
        map.insert(path.clone(), snap);
        drop(guard);

        let summary = summarize_body(tcx, &path, "LocalOwner", "hook_mir_built", &body);
        HOOK_LOG.lock().unwrap().push(summary);
        let full = export_full_body_json(tcx, &path, "LocalOwner", "hook_mir_built", &body);
        HOOK_BODIES.lock().unwrap().push(full);
    }
    stolen_res
}

fn hook_mir_promoted<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> (
    &'tcx Steal<Body<'tcx>>,
    &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>,
) {
    let (body_steal, promoted_steal) =
        (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_promoted)(tcx, def_id);
    if !promoted_steal.is_stolen() {
        let promoted_vec = promoted_steal.borrow();
        let path = tcx.def_path_str(def_id);
        for (p_idx, p_body) in promoted_vec.iter_enumerated() {
            let p_name = format!("{}::promoted[{}]", path, p_idx.index());
            let summary = summarize_body(
                tcx,
                &p_name,
                "PromotedConst",
                "hook_mir_promoted",
                p_body,
            );
            HOOK_LOG.lock().unwrap().push(summary);
            let full = export_full_body_json(
                tcx,
                &p_name,
                "PromotedConst",
                "hook_mir_promoted",
                p_body,
            );
            HOOK_BODIES.lock().unwrap().push(full);
        }
    }
    (body_steal, promoted_steal)
}

fn hook_mir_drops_elaborated<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> &'tcx Steal<Body<'tcx>> {
    let stolen_res = (rustc_interface::DEFAULT_QUERY_PROVIDERS
        .queries
        .mir_drops_elaborated_and_const_checked)(tcx, def_id);
    if !stolen_res.is_stolen() {
        let body = stolen_res.borrow();
        let path = tcx.def_path_str(def_id);
        let summary = summarize_body(tcx, &path, "LocalOwner", "hook_mir_drops_elaborated", &body);
        HOOK_LOG.lock().unwrap().push(summary);
        let full = export_full_body_json(
            tcx,
            &path,
            "LocalOwner",
            "hook_mir_drops_elaborated",
            &body,
        );
        HOOK_BODIES.lock().unwrap().push(full);
    }
    stolen_res
}

struct DirectMirCallbacks {
    stop_after_analysis: bool,
    run_mono_collector: bool,
    force_opt_before_elab_read: bool,
    passive_hooks_only: bool,
    include_const_owners_in_amir: bool,
    out_json_path: Option<String>,
    dump_bodies_path: Option<String>,
    emit_amir_v3_path: Option<String>,
    simulate_drift: Option<String>,
}

impl Callbacks for DirectMirCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers| {
            providers.queries.mir_built = hook_mir_built;
            providers.queries.mir_promoted = hook_mir_promoted;
            providers.queries.mir_drops_elaborated_and_const_checked = hook_mir_drops_elaborated;
        });
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut after_records: Vec<String> = Vec::new();
        let mut dumped_bodies: Vec<String> = HOOK_BODIES.lock().unwrap().clone();
        let mut amir_encoded_bodies: Vec<Vec<u8>> = Vec::new();
        let mut amir_export_errors: Vec<String> = Vec::new();
        let mut computed_layouts: Vec<String> = Vec::new();
        let mut required_external_bodies: Vec<(u8, String, DefId, GenericArgsRef<'tcx>)> =
            Vec::new();
        let mut next_body_id: u8 = 1;

        if !self.passive_hooks_only {
            for def_id in tcx.hir_body_owners() {
                let kind = tcx.def_kind(def_id);
                if !matches!(
                    kind,
                    DefKind::Fn
                        | DefKind::AssocFn
                        | DefKind::Closure
                        | DefKind::Const { .. }
                        | DefKind::AssocConst { .. }
                        | DefKind::InlineConst
                ) {
                    continue;
                }
                let path = tcx.def_path_str(def_id);
                let def_path_hash = format!("{:?}", tcx.def_path_hash(def_id.to_def_id()));
                let built_stolen = tcx.mir_built(def_id).is_stolen();
                let promoted_stolen = tcx.mir_promoted(def_id).1.is_stolen();

                if self.force_opt_before_elab_read
                    && matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
                {
                    let _ = tcx.optimized_mir(def_id.to_def_id());
                }

                let elab_steal = tcx.mir_drops_elaborated_and_const_checked(def_id);
                let elab_stolen_before = elab_steal.is_stolen();
                let elab_summary = if !elab_stolen_before {
                    let body = elab_steal.borrow();
                    if self.dump_bodies_path.is_some() {
                        dumped_bodies.push(export_full_body_json(
                            tcx,
                            &path,
                            "LocalOwner",
                            "after_analysis_elaborated",
                            &body,
                        ));
                    }
                    let should_emit = matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
                        || (self.include_const_owners_in_amir
                            && matches!(kind, DefKind::Const { .. } | DefKind::AssocConst { .. }));
                    if self.emit_amir_v3_path.is_some() && should_emit {
                        let orig_byte = if matches!(kind, DefKind::Const { .. } | DefKind::AssocConst { .. }) {
                            0x04
                        } else {
                            0x01
                        };
                        match encode_body_amir_v3(tcx, &path, next_body_id, orig_byte, &body, self.simulate_drift.as_deref()) {
                            Ok(bytes) => {
                                amir_encoded_bodies.push(bytes);
                                next_body_id = next_body_id.saturating_add(1);
                            }
                            Err(err) => {
                                amir_export_errors.push(err);
                            }
                        }
                    }
                    summarize_body(tcx, &path, "LocalOwner", "after_analysis_elaborated", &body)
                } else {
                    if self.emit_amir_v3_path.is_some()
                        && matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
                    {
                        amir_export_errors.push(format!("ElaboratedBodyStolenBeforeAfterAnalysis({})", path));
                    }
                    format!(
                        "{{\"owner\":\"{}\",\"stage\":\"after_analysis_elaborated\",\"stolen\":true}}",
                        json_escape(&path)
                    )
                };

                let promoted_count =
                    if matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                        tcx.promoted_mir(def_id.to_def_id()).len()
                    } else {
                        0
                    };

                let opt_summary =
                    if matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                        let opt_body = tcx.optimized_mir(def_id.to_def_id());
                        if self.dump_bodies_path.is_some() {
                            dumped_bodies.push(export_full_body_json(
                                tcx,
                                &path,
                                "LocalOwner",
                                "after_analysis_optimized",
                                opt_body,
                            ));
                        }
                        summarize_body(
                            tcx,
                            &path,
                            "LocalOwner",
                            "after_analysis_optimized",
                            opt_body,
                        )
                    } else {
                        "null".to_string()
                    };
                let elab_stolen_after_opt =
                    tcx.mir_drops_elaborated_and_const_checked(def_id).is_stolen();

                let mut ext_calls: Vec<String> = Vec::new();
                if matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                    let opt_body = tcx.optimized_mir(def_id.to_def_id());
                    for bb in opt_body.basic_blocks.iter() {
                        if let Some(term) = &bb.terminator {
                            if let TerminatorKind::Call { func, .. } = &term.kind {
                                if let Some((callee_def_id, substs)) = func.const_fn_def() {
                                    let callee_path = tcx.def_path_str(callee_def_id);
                                    let callee_hash =
                                        format!("{:?}", tcx.def_path_hash(callee_def_id));
                                    let is_local = callee_def_id.is_local();
                                    let mir_avail = tcx.is_mir_available(callee_def_id);
                                    let substs_str = format!("{:?}", substs);
                                    if !is_local
                                        && resolve_callee_symbol_id(tcx, callee_def_id, &substs_str)
                                            == Ok(24)
                                        && !required_external_bodies
                                            .iter()
                                            .any(|(s, _, _, _)| *s == 24)
                                    {
                                        required_external_bodies.push((
                                            24,
                                            "core::mem::drop::<Guard>".to_string(),
                                            callee_def_id,
                                            substs,
                                        ));
                                    }
                                    ext_calls.push(format!(
                                        "{{\"callee\":\"{}\",\"def_path_hash\":\"{}\",\"args\":\"{}\",\"is_local\":{},\"is_mir_available\":{}}}",
                                        json_escape(&callee_path),
                                        json_escape(&callee_hash),
                                        json_escape(&substs_str),
                                        is_local,
                                        mir_avail
                                    ));
                                }
                            }
                        }
                    }
                }

                after_records.push(format!(
                    "{{\"owner\":\"{}\",\"def_path_hash\":\"{}\",\"def_kind\":\"{:?}\",\"promoted_count\":{},\"built_stolen\":{},\"promoted_stolen\":{},\"elab_stolen_before_opt\":{},\"elab_stolen_after_opt\":{},\"elaborated\":{},\"optimized\":{},\"calls\":[{}]}}",
                    json_escape(&path),
                    json_escape(&def_path_hash),
                    kind,
                    promoted_count,
                    built_stolen,
                    promoted_stolen,
                    elab_stolen_before,
                    elab_stolen_after_opt,
                    elab_summary,
                    opt_summary,
                    ext_calls.join(",")
                ));
            }

            for item_id in tcx.hir_crate_items(()).free_items() {
                let def_id = item_id.owner_id.def_id;
                if matches!(
                    tcx.def_kind(def_id),
                    DefKind::Struct | DefKind::Enum | DefKind::Union
                ) {
                    let path = tcx.def_path_str(def_id);
                    let generics = tcx.generics_of(def_id);
                    if !generics.requires_monomorphization(tcx) {
                        let ty = tcx.erase_and_anonymize_regions(tcx.type_of(def_id).skip_binder());
                        let typing_env = TypingEnv::post_analysis(tcx, def_id);
                        if let Ok(ty_and_layout) =
                            tcx.layout_of(typing_env.as_query_input(ty))
                        {
                            let sz = ty_and_layout.size.bytes();
                            let al = ty_and_layout.align.abi.bytes();
                            let offsets: Vec<String> = match &ty_and_layout.fields {
                                FieldsShape::Arbitrary { offsets, .. } => offsets
                                    .iter()
                                    .map(|o| format!("{}", o.bytes()))
                                    .collect(),
                                _ => Vec::new(),
                            };
                            computed_layouts.push(format!(
                                "{{\"adt\":\"{}\",\"size_bytes\":{},\"align_bytes\":{},\"field_offsets_bytes\":[{}]}}",
                                json_escape(&path),
                                sz,
                                al,
                                offsets.join(",")
                            ));
                        }
                    }
                    if matches!(tcx.def_kind(def_id), DefKind::Struct) {
                        let ty = tcx.type_of(def_id).skip_binder();
                        #[cfg(not(rustc_1_98))]
                        let drop_inst = Instance::resolve_drop_in_place(tcx, ty);
                        #[cfg(rustc_1_98)]
                        let drop_inst = Instance::resolve_drop_glue(tcx, ty);
                        if let InstanceKind::DropGlue(_, Some(_)) = drop_inst.def {
                            let shim_body = tcx.mir_shims(drop_inst.def);
                            let shim_owner = format!("DropGlue<{}>", path);
                            if self.dump_bodies_path.is_some() {
                                dumped_bodies.push(export_full_body_json(
                                    tcx,
                                    &shim_owner,
                                    "CompilerShim",
                                    "mir_shims_drop_glue",
                                    shim_body,
                                ));
                            }
                            if self.emit_amir_v3_path.is_some() {
                                match encode_body_amir_v3(
                                    tcx,
                                    &shim_owner,
                                    next_body_id,
                                    0x02,
                                    shim_body,
                                    self.simulate_drift.as_deref(),
                                ) {
                                    Ok(bytes) => {
                                        amir_encoded_bodies.push(bytes);
                                        next_body_id = next_body_id.saturating_add(1);
                                    }
                                    Err(err) => {
                                        amir_export_errors.push(err);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            for (_ext_sym_id, ext_owner, ext_def_id, ext_substs) in &required_external_bodies {
                if tcx.is_mir_available(*ext_def_id) {
                    let raw_ext_body = tcx.optimized_mir(*ext_def_id);
                    let erased_substs = tcx.erase_and_anonymize_regions(*ext_substs);
                    let inst_body = tcx.instantiate_and_normalize_erasing_regions(
                        erased_substs,
                        TypingEnv::fully_monomorphized(),
                        EarlyBinder::bind(raw_ext_body.clone()),
                    );
                    if self.dump_bodies_path.is_some() {
                        dumped_bodies.push(export_full_body_json(
                            tcx,
                            ext_owner,
                            "ExternalRlib",
                            "optimized_mir_instantiated",
                            &inst_body,
                        ));
                    }
                    if self.emit_amir_v3_path.is_some() {
                        match encode_body_amir_v3(
                            tcx,
                            ext_owner,
                            next_body_id,
                            0x03,
                            &inst_body,
                            self.simulate_drift.as_deref(),
                        ) {
                            Ok(bytes) => {
                                amir_encoded_bodies.push(bytes);
                                next_body_id = next_body_id.saturating_add(1);
                            }
                            Err(err) => {
                                amir_export_errors.push(err);
                            }
                        }
                    }
                } else {
                    amir_export_errors.push(format!("ExternalBodyUnavailable({})", ext_owner));
                }
            }
        }

        if let Some(dump_p) = &self.dump_bodies_path {
            let dump_json = format!("[\n  {}\n]\n", dumped_bodies.join(",\n  "));
            let _ = std::fs::write(dump_p, &dump_json);
        }

        let mut ext_crates: Vec<String> = Vec::new();
        for &cnum in tcx.crates(()) {
            let cname = tcx.crate_name(cnum).to_string();
            let svh = format!("{:?}", tcx.crate_hash(cnum));
            ext_crates.push(format!("{{\"crate_name\":\"{}\",\"svh\":\"{}\"}}", cname, svh));
        }

        let has_errors_in_after = tcx.dcx().has_errors().is_some();
        let hooks_before_mono = HOOK_LOG.lock().unwrap().clone();

        let provisional_json = format!(
            "{{\n  \"provisional_hook_written\": true,\n  \"mono_collection_completed\": false,\n  \"stop_after_analysis\": {},\n  \"run_mono_collector\": {},\n  \"force_opt_before_elab_read\": {},\n  \"passive_hooks_only\": {},\n  \"has_errors_at_after_analysis\": {},\n  \"amir_v3_status\": \"provisional_incomplete\",\n  \"amir_v3_errors\": [],\n  \"computed_layouts\": [{}],\n  \"external_crates\": [{}],\n  \"hook_events\": [\n    {}\n  ],\n  \"after_analysis_owners\": [\n    {}\n  ],\n  \"collected_mono_items\": []\n}}\n",
            self.stop_after_analysis,
            self.run_mono_collector,
            self.force_opt_before_elab_read,
            self.passive_hooks_only,
            has_errors_in_after,
            computed_layouts.join(", "),
            ext_crates.join(", "),
            hooks_before_mono.join(",\n    "),
            after_records.join(",\n    ")
        );
        if let Some(p) = &self.out_json_path {
            let _ = std::fs::write(p, &provisional_json);
        }

        let mut mono_items_list: Vec<String> = Vec::new();
        if self.run_mono_collector {
            let partitions = tcx.collect_and_partition_mono_items(());
            for cgu in partitions.codegen_units {
                for (mono_item, _) in cgu.items() {
                    mono_items_list
                        .push(format!("\"{}\"", json_escape(&format!("{:?}", mono_item))));
                }
            }
        }

        let has_errors_after_mono = tcx.dcx().has_errors().is_some();
        let mono_complete = self.run_mono_collector && !has_errors_after_mono && !self.stop_after_analysis;

        // Compute deterministic 16-bit crate/config fingerprint from crate name + body bytes
        let crate_name_sym = tcx.crate_name(rustc_span::def_id::LOCAL_CRATE);
        let crate_name_str = crate_name_sym.as_str();
        let mut fp_acc: u16 = 0x5A3C;
        for b in crate_name_str.as_bytes() {
            fp_acc = fp_acc.wrapping_mul(31).wrapping_add(*b as u16);
        }
        for body_vec in &amir_encoded_bodies {
            for b in body_vec {
                fp_acc = fp_acc.wrapping_mul(131).wrapping_add(*b as u16);
            }
        }
        let fp_hi: u8 = ((fp_acc >> 8) & 0xFF) as u8;
        let fp_lo: u8 = (fp_acc & 0xFF) as u8;

        let amir_v3_status = if let Some(amir_p) = &self.emit_amir_v3_path {
            if !amir_export_errors.is_empty() {
                "rejected_fail_closed"
            } else if has_errors_after_mono || !mono_complete {
                "rejected_incomplete_compilation"
            } else if amir_encoded_bodies.is_empty() || amir_encoded_bodies.len() > 64 {
                amir_export_errors.push(format!(
                    "InvalidPackageBodyCount({})",
                    amir_encoded_bodies.len()
                ));
                "rejected_fail_closed"
            } else {
                let preserve_ub = tcx.sess.opts.unstable_opts.mir_preserve_ub;
                let ub_checks = tcx.sess.opts.unstable_opts.ub_checks.unwrap_or(true);
                let mut flags_byte: u8 = 0;
                if mono_complete {
                    flags_byte |= 0x01;
                }
                if preserve_ub {
                    flags_byte |= 0x02;
                }
                if ub_checks {
                    flags_byte |= 0x08;
                }
                let mut pkg_bytes: Vec<u8> = vec![
                    0x41,
                    0x4D,
                    0x49,
                    0x52, // "AMIR"
                    0x03, // version 3
                    0x03, // default local phase = Runtime(PostCleanup)
                    flags_byte,
                    fp_hi,
                    fp_lo,
                    amir_encoded_bodies.len() as u8,
                ];
                for b in &amir_encoded_bodies {
                    pkg_bytes.extend_from_slice(b);
                }
                match std::fs::write(amir_p, &pkg_bytes) {
                    Ok(()) => "accepted_complete",
                    Err(io_err) => {
                        amir_export_errors.push(format!(
                            "OutputWriteFailed(path={}, error={})",
                            amir_p, io_err
                        ));
                        "rejected_output_write_error"
                    }
                }
            }
        } else {
            "not_requested"
        };

        if self.emit_amir_v3_path.is_some() && amir_v3_status != "accepted_complete" {
            *AMIR_EXPORT_FAILED.lock().unwrap() = true;
        }

        let err_json: Vec<String> = amir_export_errors
            .iter()
            .map(|e| format!("\"{}\"", json_escape(e)))
            .collect();

        let hooks = HOOK_LOG.lock().unwrap().clone();
        let json_out = format!(
            "{{\n  \"provisional_hook_written\": true,\n  \"mono_collection_completed\": {},\n  \"stop_after_analysis\": {},\n  \"run_mono_collector\": {},\n  \"force_opt_before_elab_read\": {},\n  \"passive_hooks_only\": {},\n  \"has_errors_at_after_analysis\": {},\n  \"amir_v3_status\": \"{}\",\n  \"amir_v3_fp16\": [{}, {}],\n  \"amir_v3_errors\": [{}],\n  \"computed_layouts\": [{}],\n  \"external_crates\": [{}],\n  \"hook_events\": [\n    {}\n  ],\n  \"after_analysis_owners\": [\n    {}\n  ],\n  \"collected_mono_items\": [{}]\n}}\n",
            mono_complete,
            self.stop_after_analysis,
            self.run_mono_collector,
            self.force_opt_before_elab_read,
            self.passive_hooks_only,
            has_errors_after_mono,
            amir_v3_status,
            fp_hi,
            fp_lo,
            err_json.join(", "),
            computed_layouts.join(", "),
            ext_crates.join(", "),
            hooks.join(",\n    "),
            after_records.join(",\n    "),
            mono_items_list.join(", ")
        );

        if let Some(p) = &self.out_json_path {
            let _ = std::fs::write(p, &json_out);
        } else {
            println!("{}", json_out);
        }

        if self.stop_after_analysis {
            Compilation::Stop
        } else {
            Compilation::Continue
        }
    }
}

fn main() {
    let raw_args: Vec<String> = std::env::args().collect();
    let mut rustc_args: Vec<String> = Vec::new();
    let mut stop_after_analysis = false;
    let mut run_mono_collector = false;
    let mut force_opt_before_elab_read = false;
    let mut passive_hooks_only = false;
    let mut include_const_owners_in_amir = false;
    let mut out_json_path: Option<String> = None;
    let mut dump_bodies_path: Option<String> = None;
    let mut emit_amir_v3_path: Option<String> = None;
    let mut simulate_drift: Option<String> = None;

    let mut i = 0;
    while i < raw_args.len() {
        match raw_args[i].as_str() {
            "--driver-stop-after-analysis" => stop_after_analysis = true,
            "--driver-run-mono-collector" => run_mono_collector = true,
            "--driver-force-opt-before-elab" => force_opt_before_elab_read = true,
            "--driver-passive-hooks-only" => passive_hooks_only = true,
            "--driver-include-const-owners" => include_const_owners_in_amir = true,
            "--driver-out-json" => {
                i += 1;
                if i < raw_args.len() {
                    out_json_path = Some(raw_args[i].clone());
                }
            }
            "--driver-dump-bodies" => {
                i += 1;
                if i < raw_args.len() {
                    dump_bodies_path = Some(raw_args[i].clone());
                }
            }
            "--driver-emit-amir-v3" => {
                i += 1;
                if i < raw_args.len() {
                    emit_amir_v3_path = Some(raw_args[i].clone());
                }
            }
            "--driver-simulate-drift" => {
                i += 1;
                if i < raw_args.len() {
                    simulate_drift = Some(raw_args[i].clone());
                }
            }
            other => rustc_args.push(other.to_string()),
        }
        i += 1;
    }

    if let Some(amir_p) = &emit_amir_v3_path {
        let _ = std::fs::remove_file(amir_p);
    }

    let mut cb = DirectMirCallbacks {
        stop_after_analysis,
        run_mono_collector,
        force_opt_before_elab_read,
        passive_hooks_only,
        include_const_owners_in_amir,
        out_json_path,
        dump_bodies_path,
        emit_amir_v3_path,
        simulate_drift,
    };

    let res =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&rustc_args, &mut cb));
    match res {
        Ok(()) => {
            if *AMIR_EXPORT_FAILED.lock().unwrap() {
                std::process::exit(2);
            }
        }
        Err(_) => {
            std::process::exit(1);
        }
    }
}
