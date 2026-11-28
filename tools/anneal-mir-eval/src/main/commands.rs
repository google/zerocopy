// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The `list`, `eval`, and `probe` subcommands.

use std::{fs, process::ExitCode};

use anneal_mir_eval::{
    CallerMemory, Counterexample, FaultKind, Outcome, ProbeConfig, ProbeReport, Query,
    TargetEndian, TerminalOut, eval_body_with_caller_mem, probe_body_with_policy, trace_location,
    validate_program_config,
};

use super::{
    ProfileOverride,
    args::{next_flag_val, parse_arg_spec, parse_endian},
    capture::{LoadedCapture, build_config, load_capture, resolve_body_id},
    format::{format_ty, format_val},
};

pub(super) fn cmd_list(args: &[String]) -> Result<ExitCode, String> {
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
        "bodies: {} (pointer_width_bits={}, mir_profile_version={}, overflow_checks={})",
        program.bodies.len(),
        program.pointer_width_bits,
        program.mir_profile_version,
        program.overflow_checks
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

pub(super) fn cmd_eval(args: &[String]) -> Result<ExitCode, String> {
    let mut path: Option<String> = None;
    let mut body_sel: Option<String> = None;
    let mut raw_args: Vec<String> = Vec::new();
    let mut query_path: Option<String> = None;
    let mut fuel = 100_000usize;
    let mut endian_override: Option<TargetEndian> = None;
    let mut profile_override = ProfileOverride::Auto;
    let mut show_trace = false;
    let mut json_out = false;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--body" => body_sel = Some(next_flag_val(args, &mut i, "--body")?.into()),
            "--arg" => raw_args.push(next_flag_val(args, &mut i, "--arg")?.into()),
            "--query" => query_path = Some(next_flag_val(args, &mut i, "--query")?.into()),
            "--fuel" => {
                let raw = next_flag_val(args, &mut i, "--fuel")?;
                fuel = raw.parse::<usize>().map_err(|e| format!("invalid --fuel '{raw}': {e}"))?;
            }
            "--endian" => {
                endian_override = Some(parse_endian(next_flag_val(args, &mut i, "--endian")?)?)
            }
            "--strict-v1" => {
                if profile_override == ProfileOverride::ProfileV2 {
                    return Err("cannot combine --strict-v1 with --profile-v2".into());
                }
                profile_override = ProfileOverride::StrictV1;
            }
            "--profile-v2" => {
                if profile_override == ProfileOverride::StrictV1 {
                    return Err("cannot combine --strict-v1 with --profile-v2".into());
                }
                profile_override = ProfileOverride::ProfileV2;
            }
            "--trace" => show_trace = true,
            "--json" => json_out = true,
            flag if flag.starts_with('-') => return Err(format!("unknown flag '{flag}'")),
            pos if path.is_none() => path = Some(pos.into()),
            extra => return Err(format!("unexpected positional argument '{extra}'")),
        }
        i += 1;
    }

    if query_path.is_some() && !raw_args.is_empty() {
        return Err("cannot combine --query with --arg".into());
    }
    let path = path.ok_or_else(|| "missing <capture.json> argument".to_string())?;
    let LoadedCapture { program, manifest_endian, from_manifest } = load_capture(&path)?;
    let body_id = resolve_body_id(&program, from_manifest, body_sel.as_deref())?;
    let body = &program.bodies[body_id];
    let param_tys = body.param_tys().unwrap_or(&[]);

    let (parsed_args, caller_mem) = if let Some(qpath) = query_path {
        let raw_q = fs::read_to_string(&qpath)
            .map_err(|e| format!("failed to read query '{qpath}': {e}"))?;
        let query: Query = serde_json::from_str(&raw_q)
            .map_err(|e| format!("invalid query JSON '{qpath}': {e}"))?;
        (query.args, query.caller_mem)
    } else {
        let mut parsed_args = Vec::with_capacity(raw_args.len());
        let mut allocations = Vec::new();
        let mut next_alloc_id = 2u64;
        for (idx, spec) in raw_args.iter().enumerate() {
            parsed_args.push(parse_arg_spec(
                spec,
                param_tys.get(idx),
                &mut allocations,
                &mut next_alloc_id,
            )?);
        }
        (parsed_args, CallerMemory { allocations })
    };

    let config = match build_config(&program, endian_override, manifest_endian, profile_override) {
        Ok(cfg) => cfg,
        Err(fault) => {
            eprintln!("unsupported program: {}", fault.reason);
            return Ok(ExitCode::from(3));
        }
    };
    let trace =
        eval_body_with_caller_mem(&program, body_id, &parsed_args, caller_mem, fuel, &config);

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
        let site_tag = trace_location(&program, &trace)
            .map(|loc| format!(" @ {}", loc.format_site(Some(body_id))))
            .unwrap_or_default();
        match &trace.outcome {
            Outcome::Returned(TerminalOut::Returned { ret, .. }) => {
                println!("  RETURNED {}", format_val(ret));
            }
            Outcome::Returned(TerminalOut::Unwound { .. }) => {
                println!("  UNWOUND (panic){site_tag}");
            }
            Outcome::Aborted { .. } => {
                println!("  ABORTED (panic abort){site_tag}");
            }
            Outcome::Fault(err) => {
                if let Some(class) = err.witness_class() {
                    println!("  FAULT {err} [witness_class={class}]{site_tag}");
                } else {
                    println!("  FAULT {err}{site_tag}");
                }
            }
            Outcome::OutOfFuel => {
                println!("  OUT OF FUEL{site_tag}");
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

fn print_probe_site(label: &str, cex: &Counterexample, suffix: &str) {
    let args: Vec<String> = cex.args.iter().map(format_val).collect();
    let n = cex.caller_mem.allocations.len();
    let mem = if n == 0 { String::new() } else { format!(" caller_allocs={n}") };
    let site = cex
        .fault_location
        .as_ref()
        .map_or_else(String::new, |l| format!(" @ {}", l.format_site(Some(cex.trace.body_id))));
    println!("  {label} args=({}){mem}{site}{suffix}", args.join(", "));
}

pub(super) fn cmd_probe(args: &[String]) -> Result<ExitCode, String> {
    let mut path: Option<String> = None;
    let mut body_sel: Option<String> = None;
    let mut all_bodies = false;
    let mut probe = ProbeConfig::default();
    let mut endian_override: Option<TargetEndian> = None;
    let mut profile_override = ProfileOverride::Auto;
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
            "--strict-v1" => {
                if profile_override == ProfileOverride::ProfileV2 {
                    return Err("cannot combine --strict-v1 with --profile-v2".into());
                }
                profile_override = ProfileOverride::StrictV1;
            }
            "--profile-v2" => {
                if profile_override == ProfileOverride::StrictV1 {
                    return Err("cannot combine --strict-v1 with --profile-v2".into());
                }
                profile_override = ProfileOverride::ProfileV2;
            }
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
    let config = match build_config(&program, endian_override, manifest_endian, profile_override) {
        Ok(cfg) => cfg,
        Err(fault) => {
            eprintln!("unsupported program: {}", fault.reason);
            return Ok(ExitCode::from(3));
        }
    };
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
                "[{}] {}: cases={} ok={} unwound={} aborted={} ub={} (replayable={}, model_only_unreplayed={}) unsupported={} oom_fuel={} uninhabited={} unsupported_param_shape={}",
                r.body_id,
                r.identity,
                r.cases_run,
                r.returned_count,
                r.unwound_count,
                r.aborted_count,
                r.undefined_count,
                r.replayable_ub_count,
                r.model_only_unreplayed_ub_count,
                r.unsupported_count,
                r.out_of_fuel_count,
                r.uninhabited_params,
                r.unsupported_param_shape
            );
            if let Some(cex) = &r.first_undefined {
                let (ub_tag, reason) = match &cex.trace.outcome {
                    Outcome::Fault(f) => {
                        let ub = f.ub_class.map_or_else(String::new, |c| {
                            let s = serde_json::to_string(&c).unwrap_or_else(|_| format!("{c:?}"));
                            format!(", ub_class={}", s.trim_matches('"'))
                        });
                        (ub, f.reason.as_str())
                    }
                    _ => (String::new(), ""),
                };
                let class = cex
                    .witness_class
                    .map(|c| c.to_string())
                    .unwrap_or_else(|| "model_only_unreplayed".into());
                print_probe_site(
                    &format!("COUNTEREXAMPLE [class={class}{ub_tag}]"),
                    cex,
                    &format!(" -> {reason}"),
                );
                if let Some(note) = &cex.witness_note {
                    println!("    note: {note}");
                }
            }
            for (lbl, opt) in [
                ("UNWOUND", &r.first_unwound),
                ("ABORTED", &r.first_aborted),
                ("OUT_OF_FUEL", &r.first_out_of_fuel),
                ("UNSUPPORTED", &r.first_unsupported),
            ] {
                if let Some(cex) = opt {
                    let sfx = match (&cex.trace.outcome, lbl) {
                        (Outcome::Fault(f), "UNSUPPORTED") => format!(" -> {}", f.reason),
                        _ => String::new(),
                    };
                    print_probe_site(lbl, cex, &sfx);
                }
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
