// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone CLI over `anneal-mir-eval` for inspecting captured MIR JSON
//! manifests, stepping concrete inputs, and probing for pre-proof UB
//! counterexamples.

#![forbid(unsafe_code)]

use std::{env, fs, process::ExitCode};

use anneal_mir_eval::{
    CaptureInput, EnumTy, EvalConfig, FaultKind, IntTy, IntWidth, OrderingVal, Outcome,
    ProbeConfig, ProbeReport, Program, ScalarVal, TargetEndian, TerminalOut, Ty, Val,
    eval_body_with_config, probe_body_with_policy, validate_program_config,
};

fn usage() -> &'static str {
    "Usage:
  anneal-mir-eval list <capture.json> [--json]
  anneal-mir-eval eval <capture.json> [--body <idx|identity>] [--arg <val>]...
                       [--fuel <n>] [--endian big|little] [--profile-v2]
                       [--trace] [--json]
  anneal-mir-eval probe <capture.json> [--body <idx|identity> | --all]
                        [--cases <n>] [--fuel <n>] [--seed <n>]
                        [--endian big|little] [--profile-v2]
                        [--include-unsafe] [--json]"
}

fn format_ty(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".into(),
        Ty::Char => "char".into(),
        Ty::Ordering => "Ordering".into(),
        Ty::Unit => "()".into(),
        Ty::Never => "!".into(),
        Ty::Int(ity) => ity.width.rust_name(ity.signed).into(),
        Ty::Enum(ety) => format!("enum#{}", ety.id),
        Ty::OverflowPair(ity) => format!("({}, bool)", ity.width.rust_name(ity.signed)),
        Ty::Tuple { fields } => {
            let inner: Vec<String> = fields.iter().map(format_ty).collect();
            format!("({})", inner.join(", "))
        }
        Ty::Ref { mutability, pointee } => {
            let prefix = match mutability {
                anneal_mir_eval::Mutability::Shared => "&",
                anneal_mir_eval::Mutability::Mut => "&mut ",
            };
            format!("{prefix}{}", format_ty(pointee))
        }
        Ty::RawPtr { mutability, pointee } => {
            let prefix = match mutability {
                anneal_mir_eval::Mutability::Shared => "*const ",
                anneal_mir_eval::Mutability::Mut => "*mut ",
            };
            format!("{prefix}{}", format_ty(pointee))
        }
        Ty::Array { elem, len } => format!("[{}; {len}]", format_ty(elem)),
        Ty::Unsupported => "<unsupported>".into(),
    }
}

fn format_val(val: &Val) -> String {
    match val {
        Val::Scalar(sv) => {
            if sv.signed {
                format!("{}{}", sv.to_signed_i128(), sv.width.rust_name(true))
            } else {
                format!("{}{}", sv.truncated_bits(), sv.width.rust_name(false))
            }
        }
        Val::Ptr(p) => format!("{p:?}"),
        Val::Bool(b) => b.to_string(),
        Val::Char(c) => format!("{c:?}"),
        Val::Ordering(OrderingVal::Less) => "Ordering::Less".into(),
        Val::Ordering(OrderingVal::Equal) => "Ordering::Equal".into(),
        Val::Ordering(OrderingVal::Greater) => "Ordering::Greater".into(),
        Val::Unit => "()".into(),
        Val::EnumVal { ty, variant } => {
            let discr = ty.discriminants.get(*variant).copied().unwrap_or(0);
            format!("enum#{}::v{}(discr={discr})", ty.id, variant)
        }
        Val::Tuple(fields) => {
            let parts: Vec<String> = fields.iter().map(format_val).collect();
            format!("({})", parts.join(", "))
        }
        Val::Bytes(bs) => format!("[{} bytes]", bs.len()),
    }
}

struct LoadedCapture {
    program: Program,
    manifest_endian: Option<TargetEndian>,
    from_manifest: bool,
}

fn load_capture(path: &str) -> Result<LoadedCapture, String> {
    let raw = fs::read_to_string(path).map_err(|err| format!("failed to read '{path}': {err}"))?;
    let input = CaptureInput::from_json_str(&raw)?;
    let (manifest_endian, from_manifest) = match input.manifest() {
        Some(m) => {
            let endian =
                TargetEndian::from_manifest_str(&m.configuration.endian).ok_or_else(|| {
                    format!(
                        "unsupported manifest configuration.endian '{}'",
                        m.configuration.endian
                    )
                })?;
            (Some(endian), true)
        }
        None => (None, false),
    };
    Ok(LoadedCapture { program: input.into_program(), manifest_endian, from_manifest })
}

fn resolve_body_id(
    program: &Program,
    from_manifest: bool,
    selector: Option<&str>,
) -> Result<usize, String> {
    match selector {
        None => {
            if from_manifest && program.bodies.len() != 1 {
                return Err(format!(
                    "capture manifest contains {} bodies; pass --body <idx|identity>",
                    program.bodies.len()
                ));
            }
            let idx = program.entry_def_id as usize;
            if idx < program.bodies.len() {
                Ok(idx)
            } else {
                Err(format!("default entry_def_id {idx} out of bounds"))
            }
        }
        Some(sel) => {
            if let Ok(idx) = sel.parse::<usize>() {
                if idx < program.bodies.len() {
                    return Ok(idx);
                }
                return Err(format!(
                    "body index {idx} out of bounds (len={})",
                    program.bodies.len()
                ));
            }
            if let Some(exact) = program.bodies.iter().position(|b| b.identity == sel) {
                return Ok(exact);
            }
            let suffix_matches: Vec<usize> = program
                .bodies
                .iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    (b.identity.strip_prefix("rust-path-v1::") == Some(sel)).then_some(i)
                })
                .collect();
            match suffix_matches.as_slice() {
                [only] => Ok(*only),
                [] => Err(format!("no body matching '{sel}'")),
                _ => Err(format!("ambiguous body selector '{sel}'")),
            }
        }
    }
}

fn parse_int_bits(raw: &str, ity: IntTy) -> Result<ScalarVal, String> {
    let s = raw.trim();
    if ity.signed {
        if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            let bits = u128::from_str_radix(hex, 16)
                .map_err(|e| format!("invalid signed hex '{raw}': {e}"))?;
            if bits > ity.width.mask() {
                return Err(format!("value {raw} out of range for {}", ity.width.rust_name(true)));
            }
            return Ok(ScalarVal::new(ity.width, true, bits));
        }
        let parsed =
            s.parse::<i128>().map_err(|e| format!("invalid signed integer '{raw}': {e}"))?;
        let sv = ScalarVal::new(ity.width, true, parsed as u128);
        if sv.to_signed_i128() != parsed {
            return Err(format!("value {parsed} out of range for {}", ity.width.rust_name(true)));
        }
        Ok(sv)
    } else {
        let parsed = if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            u128::from_str_radix(hex, 16)
                .map_err(|e| format!("invalid unsigned hex '{raw}': {e}"))?
        } else {
            s.parse::<u128>().map_err(|e| format!("invalid unsigned integer '{raw}': {e}"))?
        };
        if parsed > ity.width.mask() {
            return Err(format!("value {parsed} out of range for {}", ity.width.rust_name(false)));
        }
        Ok(ScalarVal::new(ity.width, false, parsed))
    }
}

fn parse_enum_arg(raw: &str, ety: &EnumTy) -> Result<Val, String> {
    if let Some(v_str) = raw.strip_prefix("variant:").or_else(|| raw.strip_prefix('v')) {
        let variant =
            v_str.parse::<usize>().map_err(|e| format!("invalid enum variant '{raw}': {e}"))?;
        if variant >= ety.discriminants.len() {
            return Err(format!(
                "variant index {variant} out of bounds (len={})",
                ety.discriminants.len()
            ));
        }
        return Ok(Val::EnumVal { ty: ety.clone(), variant });
    }
    let sv = parse_int_bits(raw, ety.discr())?;
    let variant = ety
        .discriminants
        .iter()
        .position(|&d| d == sv.bits)
        .ok_or_else(|| format!("discriminant '{raw}' not declared in enum#{}", ety.id))?;
    Ok(Val::EnumVal { ty: ety.clone(), variant })
}

fn parse_arg_spec(raw: &str, expected_ty: Option<&Ty>) -> Result<Val, String> {
    if let Some((prefix, rest)) = raw.split_once(':') {
        let typed = match prefix {
            "u8" => Some(Ty::Int(IntTy { width: IntWidth::I8, signed: false })),
            "u16" => Some(Ty::Int(IntTy { width: IntWidth::I16, signed: false })),
            "u32" => Some(Ty::Int(IntTy { width: IntWidth::I32, signed: false })),
            "u64" => Some(Ty::Int(IntTy { width: IntWidth::I64, signed: false })),
            "u128" => Some(Ty::Int(IntTy { width: IntWidth::I128, signed: false })),
            "usize" => Some(Ty::Int(IntTy { width: IntWidth::Isize, signed: false })),
            "i8" => Some(Ty::Int(IntTy { width: IntWidth::I8, signed: true })),
            "i16" => Some(Ty::Int(IntTy { width: IntWidth::I16, signed: true })),
            "i32" => Some(Ty::Int(IntTy { width: IntWidth::I32, signed: true })),
            "i64" => Some(Ty::Int(IntTy { width: IntWidth::I64, signed: true })),
            "i128" => Some(Ty::Int(IntTy { width: IntWidth::I128, signed: true })),
            "isize" => Some(Ty::Int(IntTy { width: IntWidth::Isize, signed: true })),
            "bool" => Some(Ty::Bool),
            "char" => Some(Ty::Char),
            "ordering" => Some(Ty::Ordering),
            "unit" => Some(Ty::Unit),
            _ => None,
        };
        if let Some(ty) = typed {
            return parse_arg_for_ty(rest, &ty);
        }
    }
    let Some(ty) = expected_ty else {
        if raw == "()" || raw == "unit" {
            return Ok(Val::Unit);
        }
        return Err(format!("cannot infer type for argument '{raw}'; add a prefix like u32:{raw}"));
    };
    parse_arg_for_ty(raw, ty)
}

fn parse_arg_for_ty(raw: &str, ty: &Ty) -> Result<Val, String> {
    match ty {
        Ty::Unit => {
            if raw.is_empty() || raw == "()" || raw == "unit" {
                Ok(Val::Unit)
            } else {
                Err(format!("expected unit argument, got '{raw}'"))
            }
        }
        Ty::Bool => match raw {
            "true" | "1" => Ok(Val::Bool(true)),
            "false" | "0" => Ok(Val::Bool(false)),
            _ => Err(format!("expected bool, got '{raw}'")),
        },
        Ty::Char => {
            let mut chars = raw.chars();
            if let (Some(c), None) = (chars.next(), chars.next()) {
                return Ok(Val::Char(c));
            }
            if let Some(hex) = raw.strip_prefix("U+").or_else(|| raw.strip_prefix("0x")) {
                let cp = u32::from_str_radix(hex, 16)
                    .map_err(|e| format!("invalid char scalar '{raw}': {e}"))?;
                let c = char::from_u32(cp)
                    .ok_or_else(|| format!("'{raw}' is not a Unicode scalar value"))?;
                return Ok(Val::Char(c));
            }
            Err(format!("expected single char or U+XXXX, got '{raw}'"))
        }
        Ty::Ordering => match raw {
            "less" | "Less" | "-1" => Ok(Val::Ordering(OrderingVal::Less)),
            "equal" | "Equal" | "0" => Ok(Val::Ordering(OrderingVal::Equal)),
            "greater" | "Greater" | "1" => Ok(Val::Ordering(OrderingVal::Greater)),
            _ => Err(format!("expected Ordering (less|equal|greater), got '{raw}'")),
        },
        Ty::Int(ity) => Ok(Val::Scalar(parse_int_bits(raw, *ity)?)),
        Ty::Enum(ety) => parse_enum_arg(raw, ety),
        other => Err(format!("CLI parsing unsupported for parameter type {}", format_ty(other))),
    }
}

fn build_config(
    endian_override: Option<TargetEndian>,
    manifest_endian: Option<TargetEndian>,
    profile_v2: bool,
) -> EvalConfig {
    let mut cfg = if profile_v2 {
        EvalConfig::profile_v2(endian_override.or(manifest_endian).unwrap_or(TargetEndian::Little))
    } else {
        EvalConfig::profile_v1()
    };
    if let Some(endian) = endian_override {
        cfg.endian = endian;
    }
    cfg
}

fn cmd_list(args: &[String]) -> Result<ExitCode, String> {
    let mut path: Option<&str> = None;
    let mut json_out = false;
    for arg in args {
        if arg == "--json" {
            json_out = true;
        } else if path.is_none() && !arg.starts_with('-') {
            path = Some(arg);
        } else {
            return Err(format!("unexpected flag '{arg}'"));
        }
    }
    let path = path.ok_or_else(|| "missing <capture.json> argument".to_string())?;
    let LoadedCapture { program, .. } = load_capture(path)?;
    if json_out {
        println!(
            "{}",
            serde_json::to_string_pretty(&program.bodies)
                .map_err(|e| format!("failed to serialize bodies: {e}"))?
        );
        return Ok(ExitCode::SUCCESS);
    }
    println!(
        "bodies: {} (pointer_width_bits={}, mir_profile_version={})",
        program.bodies.len(),
        program.pointer_width_bits,
        program.mir_profile_version
    );
    for (idx, body) in program.bodies.iter().enumerate() {
        let params: Vec<String> = body.param_tys().unwrap_or(&[]).iter().map(format_ty).collect();
        let ret = body.return_ty().map(format_ty).unwrap_or_else(|| "?".into());
        println!(
            "  [{idx}] {}({}) -> {} [unsafe={}, blocks={}]",
            body.identity,
            params.join(", "),
            ret,
            body.is_unsafe,
            body.blocks.len()
        );
    }
    Ok(ExitCode::SUCCESS)
}

fn next_flag_val<'a>(args: &'a [String], idx: &mut usize, flag: &str) -> Result<&'a str, String> {
    *idx += 1;
    args.get(*idx).map(String::as_str).ok_or_else(|| format!("missing value after '{flag}'"))
}

fn parse_endian(raw: &str) -> Result<TargetEndian, String> {
    TargetEndian::from_manifest_str(raw)
        .ok_or_else(|| format!("expected 'big' or 'little' for --endian, got '{raw}'"))
}

fn cmd_eval(args: &[String]) -> Result<ExitCode, String> {
    let mut path: Option<String> = None;
    let mut body_sel: Option<String> = None;
    let mut raw_args: Vec<String> = Vec::new();
    let mut fuel = 100_000usize;
    let mut endian_override: Option<TargetEndian> = None;
    let mut profile_v2 = false;
    let mut show_trace = false;
    let mut json_out = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--body" => body_sel = Some(next_flag_val(args, &mut i, "--body")?.into()),
            "--arg" => raw_args.push(next_flag_val(args, &mut i, "--arg")?.into()),
            "--fuel" => {
                let raw = next_flag_val(args, &mut i, "--fuel")?;
                fuel = raw.parse::<usize>().map_err(|e| format!("invalid --fuel '{raw}': {e}"))?;
            }
            "--endian" => {
                endian_override = Some(parse_endian(next_flag_val(args, &mut i, "--endian")?)?)
            }
            "--profile-v2" => profile_v2 = true,
            "--trace" => show_trace = true,
            "--json" => json_out = true,
            flag if flag.starts_with('-') => return Err(format!("unknown flag '{flag}'")),
            pos if path.is_none() => path = Some(pos.into()),
            extra => return Err(format!("unexpected positional argument '{extra}'")),
        }
        i += 1;
    }

    let path = path.ok_or_else(|| "missing <capture.json> argument".to_string())?;
    let LoadedCapture { program, manifest_endian, from_manifest } = load_capture(&path)?;
    let body_id = resolve_body_id(&program, from_manifest, body_sel.as_deref())?;
    let body = &program.bodies[body_id];
    let param_tys = body.param_tys().unwrap_or(&[]);

    let mut parsed_args = Vec::with_capacity(raw_args.len());
    for (idx, spec) in raw_args.iter().enumerate() {
        parsed_args.push(parse_arg_spec(spec, param_tys.get(idx))?);
    }

    let config = build_config(endian_override, manifest_endian, profile_v2);
    let trace = eval_body_with_config(&program, body_id, &parsed_args, fuel, &config);

    if json_out {
        println!(
            "{}",
            serde_json::to_string_pretty(&trace)
                .map_err(|e| format!("failed to serialize trace: {e}"))?
        );
    } else {
        println!(
            "body [{body_id}] {} (steps={}/{}):",
            trace.identity, trace.steps_executed, trace.fuel_limit
        );
        match &trace.outcome {
            Outcome::Returned(TerminalOut::Returned { ret, .. }) => {
                println!("  RETURNED {}", format_val(ret));
            }
            Outcome::Returned(TerminalOut::Unwound { .. }) => {
                println!("  UNWOUND (panic)");
            }
            Outcome::Aborted { .. } => {
                println!("  ABORTED (UnwindAction::Terminate)");
            }
            Outcome::Fault(err) => {
                println!("  FAULT {err}");
            }
            Outcome::OutOfFuel => {
                println!("  OUT OF FUEL");
            }
        }
        if show_trace {
            for ev in &trace.events {
                if let Some(fault) = &ev.fault {
                    println!(
                        "    step {:>3}: body={} bb{} stmt{} {} -> fault({})",
                        ev.step, ev.def_id, ev.block_idx, ev.stmt_idx, ev.kind, fault
                    );
                } else {
                    println!(
                        "    step {:>3}: body={} bb{} stmt{} {}",
                        ev.step, ev.def_id, ev.block_idx, ev.stmt_idx, ev.kind
                    );
                }
            }
        }
    }

    Ok(match &trace.outcome {
        Outcome::Returned(_) => ExitCode::SUCCESS,
        Outcome::Fault(f) if f.kind == FaultKind::Undefined => ExitCode::from(2),
        Outcome::Fault(_) | Outcome::OutOfFuel => ExitCode::from(3),
        Outcome::Aborted { .. } => ExitCode::from(4),
    })
}

fn cmd_probe(args: &[String]) -> Result<ExitCode, String> {
    let mut path: Option<String> = None;
    let mut body_sel: Option<String> = None;
    let mut all_bodies = false;
    let mut probe = ProbeConfig::default();
    let mut endian_override: Option<TargetEndian> = None;
    let mut profile_v2 = false;
    let mut include_unsafe = false;
    let mut json_out = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--body" => body_sel = Some(next_flag_val(args, &mut i, "--body")?.into()),
            "--all" => all_bodies = true,
            "--cases" => {
                let raw = next_flag_val(args, &mut i, "--cases")?;
                probe.max_cases =
                    raw.parse::<usize>().map_err(|e| format!("invalid --cases '{raw}': {e}"))?;
            }
            "--fuel" => {
                let raw = next_flag_val(args, &mut i, "--fuel")?;
                probe.fuel =
                    raw.parse::<usize>().map_err(|e| format!("invalid --fuel '{raw}': {e}"))?;
            }
            "--seed" => {
                let raw = next_flag_val(args, &mut i, "--seed")?;
                probe.seed =
                    raw.parse::<u64>().map_err(|e| format!("invalid --seed '{raw}': {e}"))?;
            }
            "--endian" => {
                endian_override = Some(parse_endian(next_flag_val(args, &mut i, "--endian")?)?)
            }
            "--profile-v2" => profile_v2 = true,
            "--include-unsafe" => include_unsafe = true,
            "--json" => json_out = true,
            flag if flag.starts_with('-') => return Err(format!("unknown flag '{flag}'")),
            pos if path.is_none() => path = Some(pos.into()),
            extra => return Err(format!("unexpected positional argument '{extra}'")),
        }
        i += 1;
    }

    if all_bodies && body_sel.is_some() {
        return Err("cannot combine --all with --body".to_string());
    }
    let path = path.ok_or_else(|| "missing <capture.json> argument".to_string())?;
    let LoadedCapture { program, manifest_endian, from_manifest } = load_capture(&path)?;
    let config = build_config(endian_override, manifest_endian, profile_v2);
    if let Err(fault) = validate_program_config(&program, &config) {
        eprintln!("unsupported program: {}", fault.reason);
        return Ok(ExitCode::from(3));
    }

    let body_ids: Vec<usize> = if all_bodies || body_sel.is_none() {
        (0..program.bodies.len()).collect()
    } else {
        vec![resolve_body_id(&program, from_manifest, body_sel.as_deref())?]
    };

    let reports: Vec<ProbeReport> = body_ids
        .into_iter()
        .map(|id| probe_body_with_policy(&program, id, &probe, &config, !include_unsafe))
        .collect();
    let any_ub = reports.iter().any(|r| r.undefined_count > 0);
    let any_incomplete = reports
        .iter()
        .any(|r| r.unsupported_count > 0 || r.out_of_fuel_count > 0 || r.unsupported_param_shape);

    if json_out {
        println!(
            "{}",
            serde_json::to_string_pretty(&reports)
                .map_err(|e| format!("failed to serialize probe reports: {e}"))?
        );
    } else {
        for r in &reports {
            if r.skipped_unsafe {
                println!(
                    "[{}] {}: skipped_unsafe=true (pass --include-unsafe to probe preconditions manually)",
                    r.body_id, r.identity
                );
                continue;
            }
            println!(
                "[{}] {}: cases={} ok={} unwound={} aborted={} ub={} unsupported={} oom_fuel={} uninhabited={} unsupported_param_shape={}",
                r.body_id,
                r.identity,
                r.cases_run,
                r.returned_count,
                r.unwound_count,
                r.aborted_count,
                r.undefined_count,
                r.unsupported_count,
                r.out_of_fuel_count,
                r.uninhabited_params,
                r.unsupported_param_shape
            );
            if let Some(cex) = &r.first_undefined {
                let formatted_args: Vec<String> = cex.args.iter().map(format_val).collect();
                let reason = match &cex.trace.outcome {
                    Outcome::Fault(f) => f.reason.as_str(),
                    _ => "",
                };
                println!("  COUNTEREXAMPLE args=({}) -> {}", formatted_args.join(", "), reason);
            }
        }
    }

    Ok(if any_ub {
        ExitCode::from(2)
    } else if any_incomplete {
        ExitCode::from(3)
    } else {
        ExitCode::SUCCESS
    })
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() || matches!(args[0].as_str(), "-h" | "--help" | "help") {
        println!("{}", usage());
        return ExitCode::SUCCESS;
    }
    let res = match args[0].as_str() {
        "list" => cmd_list(&args[1..]),
        "eval" => cmd_eval(&args[1..]),
        "probe" => cmd_probe(&args[1..]),
        other => Err(format!("unknown subcommand '{other}'\n\n{}", usage())),
    };
    match res {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_endian_and_body_selection_contracts() {
        let cfg_big = build_config(None, Some(TargetEndian::Big), true);
        assert_eq!(cfg_big.endian, TargetEndian::Big);
        let cfg_override = build_config(Some(TargetEndian::Little), Some(TargetEndian::Big), true);
        assert_eq!(cfg_override.endian, TargetEndian::Little);
        let cfg_v1 = build_config(None, Some(TargetEndian::Little), false);
        assert_eq!(cfg_v1.endian, TargetEndian::Big);

        let dir =
            std::env::temp_dir().join(format!("anneal-mir-eval-main-unit-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let manifest_path = dir.join("manifest.json");
        let body_json = |id: &str| {
            format!(
                r#"{{
                    "arg_count": 0,
                    "is_unsafe": false,
                    "identity": "{id}",
                    "local_tys": [{{ "kind": "unit" }}],
                    "blocks": [{{ "statements": [], "terminator": {{ "kind": "ret" }} }}]
                }}"#
            )
        };
        let manifest_json = |endian: &str, two_bodies: bool| {
            let bodies = if two_bodies {
                format!("{}, {}", body_json("demo::one"), body_json("demo::two"))
            } else {
                body_json("demo::one")
            };
            format!(
                r#"{{
                    "schema_version": 4,
                    "compiler": {{
                        "commit": "deadbeef",
                        "version": "1.100.0",
                        "sysroot": "/sysroot",
                        "rustc_sha256": "{h}",
                        "driver": {{
                            "linkage": "dynamic_dso",
                            "driver_sha256": "{h}",
                            "dso_digests": {{}}
                        }}
                    }},
                    "configuration": {{
                        "crate_root": "src/lib.rs",
                        "crate_name": "demo",
                        "crate_type": "lib",
                        "panic": "unwind",
                        "edition": "2024",
                        "target": "x86_64-unknown-linux-gnu",
                        "cfg": [],
                        "env": {{}},
                        "opt_level": 0,
                        "debug_assertions": false,
                        "overflow_checks": true,
                        "mir_preserve_ub": true,
                        "pointer_bits": 64,
                        "endian": "{endian}",
                        "declared_source_files": ["src/lib.rs"]
                    }},
                    "source_files": [],
                    "census": [],
                    "selected": [],
                    "unsupported": [],
                    "program": {{
                        "scope": {{ "kind": "crate" }},
                        "bodies": [{bodies}]
                    }}
                }}"#,
                h = "a".repeat(64)
            )
        };

        fs::write(&manifest_path, manifest_json("big", true)).unwrap();
        let loaded = load_capture(manifest_path.to_str().unwrap()).unwrap();
        assert_eq!(loaded.manifest_endian, Some(TargetEndian::Big));
        assert!(loaded.from_manifest);
        assert!(resolve_body_id(&loaded.program, loaded.from_manifest, None).is_err());
        assert_eq!(
            resolve_body_id(&loaded.program, loaded.from_manifest, Some("demo::two")).unwrap(),
            1
        );

        fs::write(&manifest_path, manifest_json("pdp", false)).unwrap();
        assert!(load_capture(manifest_path.to_str().unwrap()).is_err());

        let _ = fs::remove_dir_all(&dir);
    }
}
