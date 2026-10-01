//! Run the rustc compiler with our custom options and hooks.
use crate::CharonFailure;
use crate::toolchain::toolchain_version;
use crate::translate::translate_crate;
use charon_lib::errors::ErrorCtx;
use charon_lib::options::{self, CliOpts};
use charon_lib::transform::TransformCtx;
use charon_lib::utils::arg_value;
use itertools::Itertools;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::Config;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{InstanceKind, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::config::{OutputType, OutputTypes};
use rustc_span::ErrorGuaranteed;
use std::num::NonZero;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::{env, fmt};

/// Helper that runs the compiler and catches its fatal errors.
fn run_compiler_with_callbacks(
    args: Vec<String>,
    callbacks: &mut (dyn Callbacks + Send),
) -> Result<(), CharonFailure> {
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, callbacks))
        .map_err(|_| CharonFailure::RustcError)
}

/// Tweak options to get usable MIR even for foreign crates.
fn set_mir_options(config: &mut Config) {
    config.opts.unstable_opts.always_encode_mir = true;
    config.opts.unstable_opts.mir_opt_level = Some(0);
    config.opts.unstable_opts.mir_preserve_ub = true;
    let disabled_mir_passes = ["CheckAlignment", "CheckNull"];
    for pass in disabled_mir_passes {
        config
            .opts
            .unstable_opts
            .mir_enable_passes
            .push((pass.to_owned(), false));
    }
}

/// Enable rustc's parallel front-end.
fn set_parallel_frontend(config: &mut Config) {
    if config.opts.jobs.frontend.is_none() {
        // Match rustc's `--jobs-frontend=0` behavior.
        const RUSTC_MAX_THREADS_CAP: usize = u8::MAX as usize;
        let threads = std::thread::available_parallelism()
            .map_or(1, |n| n.get())
            .min(RUSTC_MAX_THREADS_CAP);
        config.opts.jobs.frontend = NonZero::new(threads).filter(|n| n.get() > 1);
    }
}

// We use a static to be able to pass data to `override_queries`.
static SKIP_BORROWCK: AtomicBool = AtomicBool::new(false);
fn set_skip_borrowck() {
    SKIP_BORROWCK.store(true, Ordering::SeqCst);
}
fn skip_borrowck_if_set(providers: &mut Providers) {
    if SKIP_BORROWCK.load(Ordering::SeqCst) {
        providers.queries.mir_borrowck = |tcx, _def_id| {
            // Empty result, which is what is used for custom_mir bodies.
            Ok(tcx.arena.alloc(Default::default()))
        }
    }
}

fn setup_compiler(
    config: &mut Config,
    options: &CliOpts,
    do_translate: bool,
    emit_artifacts: bool,
    codegen: bool,
) {
    if do_translate {
        if options.skip_borrowck {
            // We use a static to be able to pass data to `override_queries`.
            set_skip_borrowck();
        }

        config.override_queries = Some(|_sess, providers| {
            skip_borrowck_if_set(providers);

            // TODO: catch the MIR in-flight to avoid stealing issues?
            // providers.mir_built = |tcx, def_id| {
            //     let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
            //     let mut mir = mir.steal();
            //     // use the mir
            //     tcx.alloc_steal_mir(mir)
            // };
        });

        config.opts.unstable_opts.no_codegen = !codegen;
        if !emit_artifacts {
            config.opts.output_types = OutputTypes::new(&[(OutputType::Object, None)]);
        }
        set_parallel_frontend(config);
    }
    set_mir_options(config);
}

/// Run a couple of rustc queries that don't involve MIR (so that they don't steal it). Returns
/// whether rustc reported errors. This lets us avoid running Charon translation on crates rustc
/// already rejects.
fn precheck_rustc_errors(tcx: TyCtxt<'_>) -> bool {
    type QueryResult = Result<(), ErrorGuaranteed>;

    tcx.par_hir_for_each_module(|module| {
        tcx.ensure_ok().check_mod_attrs(module);
        tcx.ensure_ok().check_mod_unstable_api_usage(module);
    });

    let _: QueryResult = tcx.ensure_result().check_type_wf(());
    for &trait_def_id in tcx.all_local_trait_impls(()).keys() {
        let _: QueryResult = tcx.ensure_result().coherent_trait(trait_def_id);
    }
    let _: QueryResult = tcx.ensure_result().crate_inherent_impls_validity_check(());
    let _: QueryResult = tcx.ensure_result().crate_inherent_impls_overlap_check(());

    tcx.par_hir_body_owners(|def_id| {
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, rustc_hir::def::DefKind::AnonConst)
            && !tcx.is_typeck_child(def_id.to_def_id())
        {
            tcx.ensure_ok().typeck(def_id);
        }
    });

    tcx.dcx().has_errors().is_some()
}

/// Run rustc checks that normally happen close to codegen, so that we get all the post-mono errors
/// etc.
fn check_late_rustc_errors(tcx: TyCtxt<'_>) {
    tcx.par_hir_body_owners(|def_id| {
        let _ = tcx.instance_mir(InstanceKind::Item(def_id.to_def_id()));
    });

    if tcx.dcx().err_count() == 0 {
        let _ = tcx.collect_and_partition_mono_items(());
    }
}

/// Whether this sysroot provides libraries for the given target.
fn sysroot_has_target(sysroot: &std::path::Path, target: &str) -> bool {
    sysroot.join("lib").join("rustlib").join(target).is_dir()
}

/// Where we tell `cargo miri setup` to build the sysroot for the current toolchain.
/// We use a per-toolchain directory because Miri's default cache directory (`~/.cache/miri`) is
/// shared across all toolchains and gets overwritten when switching between Charon versions.
fn miri_sysroot_cache_dir() -> Option<PathBuf> {
    let toolchain = toolchain_version();
    let cache_dir = match env::var_os("CHARON_CACHE_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => env::home_dir()?.join(".cache").join("charon"),
    };
    Some(cache_dir.join("miri-sysroot").join(toolchain))
}

/// `cargo miri setup` sets up a sysroot containing a standard library built with
/// `-Zalways-encode-mir`.
fn setup_miri_sysroot(target: &str) -> Option<PathBuf> {
    if let Some(root) = env::var_os("CHARON_MIRI_SYSROOTS")
        && let sysroot = PathBuf::from(root)
        && sysroot_has_target(&sysroot, target)
    {
        return Some(sysroot);
    }

    let cache_sysroot = miri_sysroot_cache_dir();
    if let Some(sysroot) = &cache_sysroot
        && sysroot_has_target(sysroot, target)
    {
        return Some(sysroot.clone());
    }

    let mut cmd = Command::new("cargo");
    cmd.arg("miri")
        .arg("setup")
        .arg(format!("--target={target}"))
        .arg("--print-sysroot")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("RUSTC_WRAPPER");
    if let Some(sysroot) = &cache_sysroot {
        cmd.env("MIRI_SYSROOT", sysroot);
    }

    let output = match cmd.output() {
        Ok(output) => output,
        Err(err) => {
            eprintln!(
                "warning: failed to run `cargo miri setup` for target `{target}`; \
                falling back to rustc's default sysroot: {err}"
            );
            return None;
        }
    };

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprintln!(
            "warning: `cargo miri setup` failed for target `{target}`; \
            falling back to rustc's default sysroot: {}",
            stderr.trim()
        );
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let sysroot = stdout.lines().map(str::trim).find(|line| !line.is_empty());
    match sysroot {
        Some(sysroot) => Some(PathBuf::from(sysroot)),
        None => {
            eprintln!(
                "warning: `cargo miri setup --print-sysroot` printed no sysroot for target \
                `{target}`; falling back to rustc's default sysroot"
            );
            None
        }
    }
}

/// Run the rustc driver with our custom hooks. Returns `None` if the crate was not compiled with
/// charon (e.g. because it was a dependency). Otherwise returns the translated crate, ready for
/// post-processing transformations.
pub fn run_rustc_driver() -> Result<Option<(TransformCtx, CliOpts)>, CharonFailure> {
    // Retreive the command-line arguments pased to `charon_driver`. The first arg is the path to
    // the current executable, we skip it.
    let mut compiler_args: Vec<String> = env::args().skip(1).collect();
    // We use `RUSTC_WORKSPACE_WRAPPER` to break cargo's caching; that value ends up as our first
    // argument.
    if compiler_args
        .first()
        .is_some_and(|arg| arg.starts_with("charon-dont-cache-this-"))
    {
        compiler_args.remove(0);
    }
    trace!(
        "charon-driver called with args: {}",
        compiler_args.iter().format(" ")
    );

    // When called using cargo, we tell cargo to use `charon-driver` by setting the `RUSTC_WRAPPER`
    // env var. This uses `charon-driver` for all the crates being compiled.
    // We may however not want to be calling charon on all crates; `CARGO_PRIMARY_PACKAGE` tells us
    // whether the crate was specifically selected or is a dependency.
    let is_workspace_dependency =
        env::var("CHARON_USING_CARGO").is_ok() && env::var("CARGO_PRIMARY_PACKAGE").is_err();
    // Let rustc emit artifacts (metadata, binaries) normally if invoked by `cargo` or when
    // explicitly requested.
    let emit_artifacts =
        env::var("CHARON_USING_CARGO").is_ok() || env::var("CHARON_EMIT_ARTIFACTS").is_ok();
    // Let rustc emit codegen artifacts, more specifically.
    let mut codegen = emit_artifacts;
    // Determines if we are being invoked to build a crate for the "target" architecture, in
    // contrast to the "host" architecture. Host crates are for build scripts and proc macros and
    // still need to be built like normal; target crates need to be processed by Charon.
    //
    // Currently, we detect this by checking for "--target=", which is never set for host crates.
    // This matches what Miri does, which hopefully makes it reliable enough. This relies on us
    // always invoking cargo itself with `--target`, which `charon` ensures.
    let target = arg_value(&compiler_args, "--target");
    // Whether this is the crate we want to translate.
    let is_selected_crate = !is_workspace_dependency && target.is_some();

    let mut error_ctx = ErrorCtx::new();

    // Retrieve the Charon options by deserializing them from the environment variable
    // (cargo-charon serialized the arguments and stored them in a specific environment
    // variable before calling cargo with `RUSTC_WRAPPER=charon-driver`).
    let mut options = match env::var(options::CHARON_ARGS)
        .ok()
        .map(|opts| serde_json::from_str::<options::CliOpts>(&opts).unwrap())
    {
        Some(options) => options,
        None if !is_selected_crate => Default::default(),
        None => {
            register_error!(
                error_ctx,
                no_crate,
                "environment variable `CHARON_ARGS` not set; \
                don't call `charon-driver` directly, call `charon rustc` instead"
            );
            return Err(CharonFailure::CharonError(1));
        }
    };

    if options.sysroot.as_deref() == Some("default") {
        // Do nothing
    } else if let Some(sysroot) = options.sysroot.as_ref()
        && sysroot != "miri"
    {
        compiler_args.push(format!("--sysroot={sysroot}"));
    } else if let Some(target) = target
        && let Some(sysroot) = setup_miri_sysroot(target)
    {
        // In the default case, or `--sysroot=miri`, we ask Miri to build a full-mir syroot for us.
        compiler_args.push(format!("--sysroot={}", sysroot.display()));
        // The Miri sysroot doesn't support codegen.
        codegen = false;
    }

    let output = if !is_selected_crate {
        trace!("Skipping charon; running compiler normally instead.");
        // Run the compiler normally.
        run_compiler_with_callbacks(compiler_args, &mut RunCompilerNormallyCallbacks)?;
        None
    } else {
        options.apply_preset();

        error_ctx.continue_on_failure = !options.abort_on_error;
        error_ctx.error_on_warnings = options.error_on_warnings;

        for extra_flag in options.rustc_args.iter().cloned() {
            compiler_args.push(extra_flag);
        }

        // Call the Rust compiler with our custom callback.
        let mut callback = CharonCallbacks {
            options: &options,
            emit_artifacts,
            codegen,
            error_ctx: Some(error_ctx),
            transform_ctx: None,
        };
        charon_lib::timing::time("rustc-driver", || {
            run_compiler_with_callbacks(compiler_args, &mut callback)
        })?;
        // If `transform_ctx` is not set here, there was a fatal error.
        let ctx = callback.transform_ctx.ok_or(CharonFailure::RustcError)?;
        Some((ctx, options))
    };
    Ok(output)
}

/// The callbacks for Charon
pub struct CharonCallbacks<'a> {
    options: &'a CliOpts,
    /// Whether rustc should emit the artifacts (metadata, binaries) it normally would. This is
    /// needed under cargo so later crate invocations can consume earlier selected crates.
    emit_artifacts: bool,
    /// Whether to let rustc run codegen as it normally would.
    codegen: bool,
    /// Context for errors; `take()`n by translation.
    error_ctx: Option<ErrorCtx>,
    /// This is to be filled during the extraction; it contains the translated crate. `None` at the
    /// start or if we couldn't translate anything.
    transform_ctx: Option<TransformCtx>,
}
impl<'a> Callbacks for CharonCallbacks<'a> {
    fn config(&mut self, config: &mut Config) {
        setup_compiler(
            config,
            self.options,
            true,
            self.emit_artifacts,
            self.codegen,
        );
    }

    /// The MIR is modified in place: borrow-checking requires the "promoted" MIR, which causes the
    /// "built" MIR (which results from the conversion to HIR to MIR) to become unaccessible.
    /// Because we require built MIR at the moment, we hook ourselves before MIR-based analysis
    /// passes.
    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        // Set up our own `DefId` debug routine.
        rustc_hir::def_id::DEF_ID_DEBUG
            .swap(&(def_id_debug as fn(_, &mut fmt::Formatter<'_>) -> _));

        if charon_lib::timing::time("rustc-precheck-errors", || precheck_rustc_errors(tcx)) {
            return Compilation::Continue;
        }

        self.transform_ctx = charon_lib::timing::time("translate-crate", || {
            translate_crate::translate(
                tcx,
                self.options,
                self.error_ctx.take().unwrap(),
                compiler.sess.opts.sysroot.path().to_owned(),
            )
        })
        .ok();

        Compilation::Continue
    }
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if !self.emit_artifacts {
            charon_lib::timing::time("rustc-late-checks", || check_late_rustc_errors(tcx));
        }
        Compilation::Continue
    }
}

/// Dummy callbacks used to run the compiler normally when we shouldn't be analyzing the crate.
pub struct RunCompilerNormallyCallbacks;

impl Callbacks for RunCompilerNormallyCallbacks {
    fn config(&mut self, config: &mut Config) {
        setup_compiler(config, &Default::default(), false, true, true);
    }
}

/// Custom `DefId` debug routine that doesn't print unstable values like ids and hashes.
fn def_id_debug(def_id: rustc_hir::def_id::DefId, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    rustc_middle::ty::tls::with_opt(|opt_tcx| {
        if let Some(tcx) = opt_tcx {
            let crate_name = if def_id.is_local() {
                tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE)
            } else {
                tcx.cstore_untracked().crate_name(def_id.krate)
            };
            write!(
                f,
                "{}{}",
                crate_name,
                tcx.def_path(def_id).to_string_no_crate_verbose()
            )?;
        } else {
            write!(f, "<can't access `tcx` to print `DefId` path>")?;
        }
        Ok(())
    })
}
