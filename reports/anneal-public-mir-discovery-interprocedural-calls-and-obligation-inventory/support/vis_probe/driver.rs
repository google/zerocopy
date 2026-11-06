// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::middle::privacy::Level;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{TyCtxt, Visibility};
use rustc_span::def_id::LocalDefId;
use std::collections::HashSet;

struct VisProbeCallbacks;

fn fmt_vis(vis: Option<Visibility<LocalDefId>>) -> String {
    match vis {
        None => "-".to_string(),
        Some(Visibility::Public) => "Pub".to_string(),
        Some(Visibility::Restricted(mod_id)) => format!("Restr({:?})", mod_id),
    }
}

impl Callbacks for VisProbeCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let eff_vis = tcx.effective_visibilities(());
        let reachable = tcx.reachable_set(());
        let mir_keys = tcx.mir_keys(());
        let body_owners: HashSet<LocalDefId> = tcx.hir_body_owners().collect();
        let entry_fn = tcx.entry_fn(()).and_then(|(def_id, _)| def_id.as_local());

        let partitions = tcx.collect_and_partition_mono_items(());
        let mut mono_def_ids: HashSet<LocalDefId> = HashSet::new();
        for cgu in partitions.codegen_units {
            for item in cgu.items().keys() {
                if let MonoItem::Fn(instance) = item {
                    if let Some(local_id) = instance.def_id().as_local() {
                        mono_def_ids.insert(local_id);
                    }
                }
            }
        }

        println!("=== ENTRY_FN: {:?} ===", entry_fn.map(|id| tcx.def_path_str(id)));
        println!(
            "{:<52} | {:<12} | {:<5} | {:<5} | {:<12} | {:<12} | {:<12} | {:<12} | {:<12} | {:<5} | {:<6} | {:<4}",
            "def_path_str",
            "DefKind",
            "in_bo",
            "in_mk",
            "nom_vis",
            "Direct",
            "Reexported",
            "Reachable",
            "ReachImplT",
            "reach",
            "extern",
            "mono"
        );
        println!("{}", "-".repeat(175));

        let mut all_ids: Vec<LocalDefId> = mir_keys.iter().copied().collect();
        for id in &body_owners {
            if !mir_keys.contains(id) {
                all_ids.push(*id);
            }
        }
        all_ids.sort_by_key(|id| tcx.def_path_str(*id));

        for local_id in all_ids {
            let def_id = local_id.to_def_id();
            let path = tcx.def_path_str(def_id);
            let kind = tcx.def_kind(def_id);
            let in_bo = body_owners.contains(&local_id);
            let in_mk = mir_keys.contains(&local_id);

            let nom_vis = match kind {
                DefKind::AssocConst { .. }
                | DefKind::AssocFn
                | DefKind::Const { .. }
                | DefKind::Enum
                | DefKind::Fn
                | DefKind::ForeignTy
                | DefKind::Macro(..)
                | DefKind::Mod
                | DefKind::Static { .. }
                | DefKind::Struct
                | DefKind::Trait
                | DefKind::TraitAlias
                | DefKind::TyAlias { .. }
                | DefKind::Union
                | DefKind::Use
                | DefKind::Variant
                | DefKind::Ctor(..)
                | DefKind::Field => Some(tcx.local_visibility(local_id)),
                _ => None,
            };

            let ev = eff_vis.effective_vis(local_id);
            let d_vis = ev.map(|v| *v.at_level(Level::Direct));
            let re_vis = ev.map(|v| *v.at_level(Level::Reexported));
            let r_vis = ev.map(|v| *v.at_level(Level::Reachable));
            let rit_vis = ev.map(|v| *v.at_level(Level::ReachableThroughImplTrait));

            let is_reach = reachable.contains(&local_id);
            let is_extern = match kind {
                DefKind::Fn | DefKind::AssocFn => {
                    tcx.codegen_fn_attrs(def_id).contains_extern_indicator()
                }
                _ => false,
            };
            let in_mono = mono_def_ids.contains(&local_id);

            println!(
                "{:<52} | {:<12} | {:<5} | {:<5} | {:<12} | {:<12} | {:<12} | {:<12} | {:<12} | {:<5} | {:<6} | {:<4}",
                path,
                format!("{:?}", kind),
                in_bo,
                in_mk,
                fmt_vis(nom_vis),
                fmt_vis(d_vis),
                fmt_vis(re_vis),
                fmt_vis(r_vis),
                fmt_vis(rit_vis),
                is_reach,
                is_extern,
                in_mono
            );
        }

        // Also inspect parent impls and opaque types for extra detail
        println!("\n=== IMPL & OPAQUE EFFECTIVE VISIBILITIES ===");
        for impl_id in tcx.hir_crate_items(()).free_items() {
            let local_id = impl_id.owner_id.def_id;
            let kind = tcx.def_kind(local_id);
            if matches!(kind, DefKind::Impl { .. } | DefKind::OpaqueTy) {
                let ev = eff_vis.effective_vis(local_id);
                println!(
                    "{:<52} | {:?} | Direct={} Reexp={} Reach={} ReachImplT={}",
                    tcx.def_path_str(local_id),
                    kind,
                    fmt_vis(ev.map(|v| *v.at_level(Level::Direct))),
                    fmt_vis(ev.map(|v| *v.at_level(Level::Reexported))),
                    fmt_vis(ev.map(|v| *v.at_level(Level::Reachable))),
                    fmt_vis(ev.map(|v| *v.at_level(Level::ReachableThroughImplTrait))),
                );
            }
        }
        for op_id in tcx.hir_crate_items(()).opaques() {
            let ev = eff_vis.effective_vis(op_id);
            let parent = tcx.local_parent(op_id);
            println!(
                "OpaqueTy {:<43} | parent={:<30} | Direct={} Reexp={} Reach={} ReachImplT={}",
                tcx.def_path_str(op_id),
                tcx.def_path_str(parent),
                fmt_vis(ev.map(|v| *v.at_level(Level::Direct))),
                fmt_vis(ev.map(|v| *v.at_level(Level::Reexported))),
                fmt_vis(ev.map(|v| *v.at_level(Level::Reachable))),
                fmt_vis(ev.map(|v| *v.at_level(Level::ReachableThroughImplTrait))),
            );
        }

        Compilation::Stop
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut callbacks = VisProbeCallbacks;
    rustc_driver::run_compiler(&args, &mut callbacks);
}
