// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The private interface to Anneal's pinned compiler libraries.

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use std::ffi::OsString;
use std::process::ExitCode;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::ErrorOutputType;

struct AnalysisCallbacks {
    error_format: ErrorOutputType,
    analysis_reached: bool,
}

impl Callbacks for AnalysisCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        self.error_format = config.opts.error_format;
        configure(config);
    }

    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        // rustc documents this hook as "Called after analysis" and invokes it
        // after its analysis query. Record only clean analysis, then continue
        // the requested compilation so later diagnostics prohibit success.
        // No compiler data or verification obligation is extracted here.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/lib.rs#L141-L150
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/lib.rs#L326-L353
        self.analysis_reached = tcx.dcx().has_errors().is_none();
        Compilation::Continue
    }
}

pub(super) fn resolve_packaged_sysroot() -> Result<std::path::PathBuf, String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("cannot resolve capture executable: {error}"))?;
    let install_root = executable
        .parent()
        .and_then(|bin| bin.parent())
        .ok_or_else(|| "capture executable has no installation root".to_owned())?;
    let packaged_sysroot = install_root.join("rust");
    if !packaged_sysroot.join("lib/rustlib").is_dir() {
        return Err(format!(
            "packaged Rust sysroot is missing at {}; pass --sysroot for an unbundled binary",
            packaged_sysroot.display()
        ));
    }
    Ok(packaged_sysroot)
}

/// Apply the pinned compiler version and packaged-sysroot policy.
///
/// Both compiler modes call this after rustc has parsed its options, so an
/// explicit sysroot takes precedence over the adjacent distribution.
pub(super) fn configure(config: &mut interface::Config) {
    // EarlyDiagCtxt supports the user's "preference on error emission
    // format". Use that format once compiler options are available,
    // including for failures before a compiler session exists.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L1412-L1446
    let early_dcx = EarlyDiagCtxt::new(config.opts.error_format);

    // The distribution hashes in flake.nix authenticate the complete
    // compiler. This check catches builds against another nightly.
    // rustc_version_str returns the "version string for `rustc` itself".
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/util.rs#L688-L691
    if rustc_interface::util::rustc_version_str() != Some(crate::ir::COMPILER_VERSION) {
        early_dcx.early_fatal("driver was built with an unexpected compiler version");
    }

    // Let rustc parse --sysroot, including options in response files.
    // Sysroot::path selects the "explicit sysroot if it was passed with
    // `--sysroot`, or default sysroot otherwise". Replace only the default
    // so the compiler's build path cannot rescue an incomplete archive.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/config.rs#L1343-L1356
    if config.opts.sysroot.explicit.is_none() {
        config.opts.sysroot.default =
            resolve_packaged_sysroot().unwrap_or_else(|message| early_dcx.early_fatal(message));
    }
}

/// Reject non-Unicode process arguments before rustc's hook inspects them.
///
/// Typed capture builds its own compiler argument list, but the hook still
/// reads the original process arguments, including its program name.
pub(super) fn install_ice_hook() {
    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    for (index, argument) in std::env::args_os().enumerate() {
        if argument.to_str().is_none() {
            let subject = if index == 0 {
                "program name"
            } else {
                "argument"
            };
            early_dcx.early_fatal(format!("compiler {subject} is not UTF-8: {argument:?}"));
        }
    }
    // The hook will "print the ICE message on unexpected panics" and is
    // "useable even by external tools". It scans `std::env::args()` for
    // "-Zui-testing" when RUST_BACKTRACE is unset, including the program name.
    // Compiler panics retain rustc's context and bug-report guidance.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/lib.rs#L1434-L1461
    rustc_driver::install_ice_hook(
        "https://github.com/google/zerocopy/issues/new?template=anneal.yml",
        |_| (),
    );
}

/// Run one compiler session and require a clean analysis callback.
///
/// Diagnostics, including callback evidence, use rustc's chosen stderr format.
/// Argument errors before options are parsed use rustc's default format.
/// Evidence appears only after the entire requested compilation succeeds. A
/// compiler information request that returns without analysis fails this check.
pub(super) fn run(args: Vec<OsString>) -> ExitCode {
    // catch_with_exit_code "also computes the exit code" for caught fatal
    // errors. Keep already-reported diagnostics without a wrapper error; other
    // panics unwind without callback evidence.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/lib.rs#L1375-L1381
    rustc_driver::catch_with_exit_code(|| {
        // Like rustc's raw_args, reject non-Unicode arguments before parsing
        // compiler options, using the default early diagnostic format.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L114-L134
        let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
        let mut compiler_args = vec!["anneal-rustc-capture".into()];
        compiler_args.extend(args.into_iter().map(|arg| {
            arg.into_string().unwrap_or_else(|arg| {
                early_dcx.early_fatal(format!("compiler argument is not UTF-8: {arg:?}"))
            })
        }));

        install_ice_hook();

        let mut callbacks = AnalysisCallbacks {
            error_format: ErrorOutputType::default(),
            analysis_reached: false,
        };

        // run_compiler discards argv[0] before expanding response files and
        // parsing compiler options. Supply that slot without parsing flags.
        // Its normal return includes the final abort_if_errors check, so even
        // errors after analysis prohibit callback evidence.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/lib.rs#L171-L187
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_interface/src/interface.rs#L491-L509
        rustc_driver::run_compiler(&compiler_args, &mut callbacks);

        // early_note uses rustc's diagnostic emitter, whose destinations are
        // stderr for both human and JSON formats. Keep stdout exclusively for
        // requested compiler output, which may include binary artifacts.
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L1432-L1434
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_session/src/session.rs#L1462-L1478
        let early_dcx = EarlyDiagCtxt::new(callbacks.error_format);
        if !callbacks.analysis_reached {
            early_dcx.early_fatal("compiler returned without reaching a clean analysis callback");
        }
        early_dcx.early_note(
            "anneal-rustc-capture: compiler analysis callback reached; verification not performed",
        );
    })
}
