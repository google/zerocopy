use futures::{future::BoxFuture, stream::BoxStream, Future, FutureExt, Stream, StreamExt};
use serde::Deserialize;
use snafu::prelude::*;
use std::{
    collections::{BTreeSet, HashMap},
    fmt, mem, ops,
    pin::{self, pin},
    process::Stdio,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc, LazyLock, Mutex,
    },
    task,
    time::Duration,
};
use tokio::{
    process::{Child, ChildStdin, ChildStdout, Command},
    select,
    sync::{mpsc, oneshot, OnceCell},
    task::{JoinHandle, JoinSet},
    time::{self, MissedTickBehavior},
    try_join,
};
use tokio_stream::wrappers::ReceiverStream;
use tokio_util::{io::SyncIoBridge, sync::CancellationToken, task::AbortOnDropHandle};
use tracing::{error, info, info_span, instrument, trace, trace_span, warn, Instrument};

use crate::{
    bincode_input_closed,
    message::{
        CommandStatistics, CoordinatorMessage, DeleteFileRequest, ExecuteCommandRequest,
        ExecuteCommandResponse, JobId, Multiplexed, OneToOneResponse, ReadFileRequest,
        ReadFileResponse, SerializedError2, WorkerMessage, WriteFileRequest,
    },
    DropErrorDetailsExt, TaskAbortExt as _,
};

macro_rules! kvs {
    ($($k:expr => $v:expr),+$(,)?) => {
        [
            $((Into::into($k), Into::into($v)),)+
        ].into_iter()
    };
}

pub mod limits;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Versions {
    pub stable: ChannelVersions,
    pub beta: ChannelVersions,
    pub nightly: ChannelVersions,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChannelVersions {
    pub rustc: Version,
    pub rustfmt: Version,
    pub clippy: Version,
    pub miri: Option<Version>,
}

/// Parsing this struct is very lenient — we'd rather return some
/// partial data instead of absolutely nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Version {
    pub release: String,
    pub commit_hash: String,
    pub commit_date: String,
}

impl Version {
    fn parse_rustc_version_verbose(rustc_version: &str) -> Self {
        let mut release = "";
        let mut commit_hash = "";
        let mut commit_date = "";

        let fields = rustc_version.lines().skip(1).filter_map(|line| {
            let mut pieces = line.splitn(2, ':');
            let key = pieces.next()?.trim();
            let value = pieces.next()?.trim();
            Some((key, value))
        });

        for (k, v) in fields {
            match k {
                "release" => release = v,
                "commit-hash" => commit_hash = v,
                "commit-date" => commit_date = v,
                _ => {}
            }
        }

        Self {
            release: release.into(),
            commit_hash: commit_hash.into(),
            commit_date: commit_date.into(),
        }
    }

    // Parses versions of the shape `toolname 0.0.0 (0000000 0000-00-00)`
    fn parse_tool_version(tool_version: &str) -> Self {
        let mut parts = tool_version.split_whitespace().fuse().skip(1);

        let release = parts.next().unwrap_or("").into();
        let commit_hash = parts.next().unwrap_or("").trim_start_matches('(').into();
        let commit_date = parts.next().unwrap_or("").trim_end_matches(')').into();

        Self {
            release,
            commit_hash,
            commit_date,
        }
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum VersionsError {
    #[snafu(display("Unable to determine versions for the stable channel"))]
    Stable { source: VersionsChannelError },

    #[snafu(display("Unable to determine versions for the beta channel"))]
    Beta { source: VersionsChannelError },

    #[snafu(display("Unable to determine versions for the nightly channel"))]
    Nightly { source: VersionsChannelError },
}

#[derive(Debug, Snafu)]
pub enum VersionsChannelError {
    #[snafu(transparent)]
    Channel { source: Error },

    #[snafu(transparent)]
    Versions { source: ContainerVersionsError },
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum ContainerVersionsError {
    #[snafu(display("Failed to get `rustc` version"))]
    Rustc { source: VersionError },

    #[snafu(display("`rustc` not executable"))]
    RustcMissing,

    #[snafu(display("Failed to get `rustfmt` version"))]
    Rustfmt { source: VersionError },

    #[snafu(display("`cargo fmt` not executable"))]
    RustfmtMissing,

    #[snafu(display("Failed to get clippy version"))]
    Clippy { source: VersionError },

    #[snafu(display("`cargo clippy` not executable"))]
    ClippyMissing,

    #[snafu(display("Failed to get miri version"))]
    Miri { source: VersionError },
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum VersionError {
    #[snafu(display("Could not start the process"))]
    #[snafu(context(false))]
    SpawnProcess { source: SpawnCargoError },

    #[snafu(display("The task panicked"))]
    #[snafu(context(false))]
    TaskPanic { source: tokio::task::JoinError },
}

#[derive(Debug, Clone)]
pub struct Crate {
    pub name: String,
    pub version: String,
    pub id: String,
}

#[derive(Deserialize)]
struct InternalCrate {
    name: String,
    version: String,
    id: String,
}

impl From<InternalCrate> for Crate {
    fn from(other: InternalCrate) -> Self {
        let InternalCrate { name, version, id } = other;
        Self { name, version, id }
    }
}

#[derive(Debug, Snafu)]
pub enum CratesError {
    #[snafu(display("Could not start the container"))]
    #[snafu(context(false))]
    Start { source: Error },

    #[snafu(transparent)]
    Container { source: ContainerCratesError },
}

#[derive(Debug, Snafu)]
pub enum ContainerCratesError {
    #[snafu(display("Could not read the crate information file"))]
    #[snafu(context(false))]
    Read { source: CommanderError },

    #[snafu(display("Could not parse the crate information file"))]
    #[snafu(context(false))]
    Deserialization { source: serde_json::Error },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AssemblyFlavor {
    Att,
    Intel,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DemangleAssembly {
    Demangle,
    Mangle,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ProcessAssembly {
    Filter,
    Raw,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CompileTarget {
    Assembly(AssemblyFlavor, DemangleAssembly, ProcessAssembly),
    Hir,
    LlvmIr,
    Mir,
    Wasm,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Channel {
    Stable,
    Beta,
    Nightly,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AliasingModel {
    Stacked,
    Tree,
}

impl Channel {
    #[cfg(test)]
    pub(crate) const ALL: [Self; 3] = [Self::Stable, Self::Beta, Self::Nightly];

    #[cfg(test)]
    pub(crate) fn to_str(self) -> &'static str {
        match self {
            Channel::Stable => "stable",
            Channel::Beta => "beta",
            Channel::Nightly => "nightly",
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Mode {
    Debug,
    Release,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Edition {
    Rust2015,
    Rust2018,
    Rust2021,
    Rust2024,
}

impl Edition {
    #[cfg(test)]
    pub(crate) const ALL: [Self; 4] = [
        Self::Rust2015,
        Self::Rust2018,
        Self::Rust2021,
        Self::Rust2024,
    ];

    pub(crate) fn to_str(self) -> &'static str {
        match self {
            Edition::Rust2015 => "2015",
            Edition::Rust2018 => "2018",
            Edition::Rust2021 => "2021",
            Edition::Rust2024 => "2024",
        }
    }

    pub(crate) fn to_cargo_toml_key(self) -> &'static str {
        self.to_str()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CrateType {
    Binary,
    Library(LibraryType),
}

impl CrateType {
    const MAIN_RS: &'static str = "src/main.rs";
    const LIB_RS: &'static str = "src/lib.rs";

    pub(crate) fn is_binary(self) -> bool {
        self == CrateType::Binary
    }

    pub(crate) fn primary_path(self) -> &'static str {
        match self {
            CrateType::Binary => Self::MAIN_RS,
            CrateType::Library(_) => Self::LIB_RS,
        }
    }

    pub(crate) fn other_path(self) -> &'static str {
        match self {
            CrateType::Binary => Self::LIB_RS,
            CrateType::Library(_) => Self::MAIN_RS,
        }
    }

    pub(crate) fn to_cargo_toml_key(self) -> &'static str {
        use {CrateType::*, LibraryType::*};

        match self {
            Binary => "bin",
            Library(Lib) => "lib",
            Library(Dylib) => "dylib",
            Library(Rlib) => "rlib",
            Library(Staticlib) => "staticlib",
            Library(Cdylib) => "cdylib",
            Library(ProcMacro) => "proc-macro",
        }
    }

    pub(crate) fn to_library_cargo_toml_key(self) -> Option<&'static str> {
        if self == Self::Binary {
            None
        } else {
            Some(self.to_cargo_toml_key())
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LibraryType {
    Lib,
    Dylib,
    Rlib,
    Staticlib,
    Cdylib,
    ProcMacro,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecutionTool {
    Cargo, 
    AnnealVerify,
}

#[derive(Debug, Clone)]
pub struct ExecuteRequest {
    pub channel: Channel,
    pub mode: Mode,
    pub edition: Edition,
    pub crate_type: CrateType,
    pub tests: bool,
    pub backtrace: bool,
    pub code: String,
    pub execution_tool: ExecutionTool,
}

impl LowerRequest for ExecuteRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        delete_previous_primary_file_request(self.crate_type)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        write_primary_file_request(self.crate_type, &self.code)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        let args = match self.execution_tool {
            ExecutionTool::Cargo => {
                let cmd = match (self.tests, self.crate_type.is_binary()) {
                    (true, _) => "test",
                    (_, true) => "run",
                    (_, _) => "build",
                };

                let mut args = vec![cmd];

                if let Mode::Release = self.mode {
                    args.push("--release");
                }

                args
            }

            ExecutionTool::AnnealVerify => vec!["anneal", "verify"],
        };

        let mut envs = HashMap::new();
        if self.backtrace {
            envs.extend(kvs!("RUST_BACKTRACE" => "1"));
        }

        ExecuteCommandRequest {
            cmd: "cargo".to_owned(),
            args: args.into_iter().map(|s| s.to_owned()).collect(),
            envs,
            cwd: None,
        }
    }
}

impl CargoTomlModifier for ExecuteRequest {
    fn modify_cargo_toml(&self, mut cargo_toml: toml::Value) -> toml::Value {
        cargo_toml = modify_cargo_toml::set_edition(cargo_toml, self.edition.to_cargo_toml_key());

        if let Some(crate_type) = self.crate_type.to_library_cargo_toml_key() {
            cargo_toml = modify_cargo_toml::set_crate_type(cargo_toml, crate_type);
        }
        cargo_toml
    }
}

#[derive(Debug, Clone)]
pub struct ExecuteStatus {
    pub resident_set_size_bytes: u64,
    pub total_time_secs: f64,
}

impl From<CommandStatistics> for ExecuteStatus {
    fn from(value: CommandStatistics) -> Self {
        let CommandStatistics {
            total_time_secs,
            resident_set_size_bytes,
        } = value;
        Self {
            resident_set_size_bytes,
            total_time_secs,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ExecuteResponse {
    pub success: bool,
    pub exit_detail: String,
}

#[derive(Debug, Clone)]
pub struct CompileRequest {
    pub target: CompileTarget,
    pub channel: Channel,
    pub crate_type: CrateType,
    pub mode: Mode,
    pub edition: Edition,
    // TODO: Remove `tests` and `backtrace` -- don't make sense for compiling.
    pub tests: bool,
    pub backtrace: bool,
    pub code: String,
}

impl CompileRequest {
    const OUTPUT_PATH: &str = "compilation";

    fn read_output_request(&self) -> ReadFileRequest {
        ReadFileRequest {
            path: Self::OUTPUT_PATH.to_owned(),
        }
    }

    pub(crate) fn postprocess_result(&self, mut code: String) -> String {
        if let CompileTarget::Assembly(_, demangle, process) = self.target {
            if demangle == DemangleAssembly::Demangle {
                code = asm_cleanup::demangle_asm(&code);
            }

            if process == ProcessAssembly::Filter {
                code = asm_cleanup::filter_asm(&code);
            }
        }

        code
    }
}

impl LowerRequest for CompileRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        delete_previous_primary_file_request(self.crate_type)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        write_primary_file_request(self.crate_type, &self.code)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        use CompileTarget::*;

        let mut args = if let Wasm = self.target {
            vec!["wasm"]
        } else {
            vec!["rustc"]
        };
        if let Mode::Release = self.mode {
            args.push("--release");
        }

        match self.target {
            Assembly(flavor, _, _) => {
                args.extend(&["--", "--emit", "asm=compilation"]);

                // Enable extra assembly comments for nightly builds
                if let Channel::Nightly = self.channel {
                    args.push("-Z");
                    args.push("verbose-asm");
                }

                args.push("-C");
                match flavor {
                    AssemblyFlavor::Att => args.push("llvm-args=-x86-asm-syntax=att"),
                    AssemblyFlavor::Intel => args.push("llvm-args=-x86-asm-syntax=intel"),
                }
            }
            LlvmIr => args.extend(&["--", "--emit", "llvm-ir=compilation"]),
            Mir => args.extend(&["--", "--emit", "mir=compilation"]),
            Hir => args.extend(&["--", "-Zunpretty=hir", "-o", Self::OUTPUT_PATH]),
            Wasm => args.extend(&["-o", Self::OUTPUT_PATH]),
        }
        let mut envs = HashMap::new();
        if self.backtrace {
            envs.extend(kvs!("RUST_BACKTRACE" => "1"));
        }

        ExecuteCommandRequest {
            cmd: "cargo".to_owned(),
            args: args.into_iter().map(|s| s.to_owned()).collect(),
            envs,
            cwd: None,
        }
    }
}

impl CargoTomlModifier for CompileRequest {
    fn modify_cargo_toml(&self, mut cargo_toml: toml::Value) -> toml::Value {
        cargo_toml = modify_cargo_toml::set_edition(cargo_toml, self.edition.to_cargo_toml_key());

        if let Some(crate_type) = self.crate_type.to_library_cargo_toml_key() {
            cargo_toml = modify_cargo_toml::set_crate_type(cargo_toml, crate_type);
        }

        if CompileTarget::Wasm == self.target {
            cargo_toml = modify_cargo_toml::remove_dependencies(cargo_toml);
            cargo_toml = modify_cargo_toml::set_release_lto(cargo_toml, true);
        }

        cargo_toml
    }
}

#[derive(Debug, Clone)]
pub struct CompileResponse {
    pub success: bool,
    pub exit_detail: String,
    pub code: String,
}

#[derive(Debug, Clone)]
pub struct FormatRequest {
    pub channel: Channel,
    pub crate_type: CrateType,
    pub edition: Edition,
    pub code: String,
}

impl FormatRequest {
    fn read_output_request(&self) -> ReadFileRequest {
        ReadFileRequest {
            path: self.crate_type.primary_path().to_owned(),
        }
    }
}

impl LowerRequest for FormatRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        delete_previous_primary_file_request(self.crate_type)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        write_primary_file_request(self.crate_type, &self.code)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        ExecuteCommandRequest {
            cmd: "cargo".to_owned(),
            args: vec!["fmt".to_owned()],
            envs: Default::default(),
            cwd: None,
        }
    }
}

impl CargoTomlModifier for FormatRequest {
    fn modify_cargo_toml(&self, mut cargo_toml: toml::Value) -> toml::Value {
        cargo_toml = modify_cargo_toml::set_edition(cargo_toml, self.edition.to_cargo_toml_key());

        if let Some(crate_type) = self.crate_type.to_library_cargo_toml_key() {
            cargo_toml = modify_cargo_toml::set_crate_type(cargo_toml, crate_type);
        }
        cargo_toml
    }
}

#[derive(Debug, Clone)]
pub struct FormatResponse {
    pub success: bool,
    pub exit_detail: String,
    pub code: String,
}

#[derive(Debug, Clone)]
pub struct ClippyRequest {
    pub channel: Channel,
    pub crate_type: CrateType,
    pub edition: Edition,
    pub code: String,
}

impl LowerRequest for ClippyRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        delete_previous_primary_file_request(self.crate_type)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        write_primary_file_request(self.crate_type, &self.code)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        ExecuteCommandRequest {
            cmd: "cargo".to_owned(),
            args: vec!["clippy".to_owned()],
            envs: Default::default(),
            cwd: None,
        }
    }
}

impl CargoTomlModifier for ClippyRequest {
    fn modify_cargo_toml(&self, mut cargo_toml: toml::Value) -> toml::Value {
        cargo_toml = modify_cargo_toml::set_edition(cargo_toml, self.edition.to_cargo_toml_key());

        if let Some(crate_type) = self.crate_type.to_library_cargo_toml_key() {
            cargo_toml = modify_cargo_toml::set_crate_type(cargo_toml, crate_type);
        }
        cargo_toml
    }
}

#[derive(Debug, Clone)]
pub struct ClippyResponse {
    pub success: bool,
    pub exit_detail: String,
}

#[derive(Debug, Clone)]
pub struct MiriRequest {
    pub channel: Channel,
    pub crate_type: CrateType,
    pub edition: Edition,
    pub tests: bool,
    pub aliasing_model: AliasingModel,
    pub code: String,
}

impl LowerRequest for MiriRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        delete_previous_primary_file_request(self.crate_type)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        write_primary_file_request(self.crate_type, &self.code)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        let mut miriflags = Vec::new();

        if matches!(self.aliasing_model, AliasingModel::Tree) {
            miriflags.push("-Zmiri-tree-borrows");
        }

        miriflags.push("-Zmiri-disable-isolation");

        let miriflags = miriflags.join(" ");

        let subcommand = if self.tests { "test" } else { "run" };

        ExecuteCommandRequest {
            cmd: "cargo".to_owned(),
            args: ["miri", subcommand].map(Into::into).into(),
            envs: kvs! {
                "MIRIFLAGS" => miriflags,
                // Be sure that `cargo miri` will not build a new
                // sysroot. Creating a sysroot takes a while and Miri
                // will build one by default if it's missing. If
                // `MIRI_SYSROOT` is set and the sysroot is missing,
                // it will error instead.
                "MIRI_SYSROOT" => "/playground/.cache/miri",
            }
            .collect(),
            cwd: None,
        }
    }
}

impl CargoTomlModifier for MiriRequest {
    fn modify_cargo_toml(&self, mut cargo_toml: toml::Value) -> toml::Value {
        cargo_toml = modify_cargo_toml::set_edition(cargo_toml, self.edition.to_cargo_toml_key());

        if let Some(crate_type) = self.crate_type.to_library_cargo_toml_key() {
            cargo_toml = modify_cargo_toml::set_crate_type(cargo_toml, crate_type);
        }
        cargo_toml
    }
}

#[derive(Debug, Clone)]
pub struct MiriResponse {
    pub success: bool,
    pub exit_detail: String,
}

#[derive(Debug, Clone)]
pub struct MacroExpansionRequest {
    pub channel: Channel,
    pub crate_type: CrateType,
    pub edition: Edition,
    pub code: String,
}

impl LowerRequest for MacroExpansionRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        delete_previous_primary_file_request(self.crate_type)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        write_primary_file_request(self.crate_type, &self.code)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        ExecuteCommandRequest {
            cmd: "cargo".to_owned(),
            args: ["rustc", "--", "-Zunpretty=expanded"]
                .map(str::to_owned)
                .to_vec(),
            envs: Default::default(),
            cwd: None,
        }
    }
}

impl CargoTomlModifier for MacroExpansionRequest {
    fn modify_cargo_toml(&self, mut cargo_toml: toml::Value) -> toml::Value {
        cargo_toml = modify_cargo_toml::set_edition(cargo_toml, self.edition.to_cargo_toml_key());

        if let Some(crate_type) = self.crate_type.to_library_cargo_toml_key() {
            cargo_toml = modify_cargo_toml::set_crate_type(cargo_toml, crate_type);
        }
        cargo_toml
    }
}

#[derive(Debug, Clone)]
pub struct MacroExpansionResponse {
    pub success: bool,
    pub exit_detail: String,
}

#[derive(Debug, Clone)]
pub struct WithOutput<T> {
    pub response: T,
    pub stdout: String,
    pub stderr: String,
}

impl<T> WithOutput<T> {
    async fn try_absorb<F, E>(
        task: F,
        stdout_rx: mpsc::Receiver<String>,
        stderr_rx: mpsc::Receiver<String>,
    ) -> Result<WithOutput<T>, E>
    where
        F: Future<Output = Result<T, E>>,
    {
        Self::try_absorb_stream(
            task,
            ReceiverStream::new(stdout_rx),
            ReceiverStream::new(stderr_rx),
        )
        .await
    }

    async fn try_absorb_stream<F, E>(
        task: F,
        stdout_rx: impl Stream<Item = String>,
        stderr_rx: impl Stream<Item = String>,
    ) -> Result<WithOutput<T>, E>
    where
        F: Future<Output = Result<T, E>>,
    {
        let stdout = stdout_rx.collect().map(Ok);
        let stderr = stderr_rx.collect().map(Ok);

        let (response, stdout, stderr) = try_join!(task, stdout, stderr)?;

        Ok(WithOutput {
            response,
            stdout,
            stderr,
        })
    }
}

impl<T> ops::Deref for WithOutput<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.response
    }
}

fn write_primary_file_request(crate_type: CrateType, code: &str) -> WriteFileRequest {
    WriteFileRequest {
        path: crate_type.primary_path().to_owned(),
        content: code.into(),
    }
}

fn delete_previous_primary_file_request(crate_type: CrateType) -> DeleteFileRequest {
    DeleteFileRequest {
        path: crate_type.other_path().to_owned(),
    }
}

#[derive(Debug)]
enum DemultiplexCommand {
    Listen(JobId, mpsc::Sender<WorkerMessage>),
    ListenOnce(JobId, oneshot::Sender<WorkerMessage>),
}

type ResourceError = Box<dyn snafu::Error + Send + Sync + 'static>;
type ResourceResult<T, E = ResourceError> = std::result::Result<T, E>;

/// Mediate resource limits and names for created objects.
///
/// The [`Coordinator`][] requires mostly-global resources, such as
/// Docker containers or running processes. This trait covers two cases:
///
/// 1. To avoid conflicts, each container must have a unique name.
/// 2. Containers and processes compete for CPU / memory.
///
/// Only a global view guarantees the unique names and resource
/// allocation, so whoever creates [`Coordinator`][]s via the
/// [`CoordinatorFactory`][] is responsible.
pub trait ResourceLimits: Send + Sync + fmt::Debug + 'static {
    /// Block until resources for a container are available.
    fn next_container(&self) -> BoxFuture<'static, ResourceResult<Box<dyn ContainerPermit>>>;

    /// Block until someone reqeusts that you return an in-use container.
    fn container_requested(&self) -> BoxFuture<'static, ()>;
}

/// Represents one allowed Docker container (or equivalent).
pub trait ContainerPermit: Send + Sync + fmt::Debug + fmt::Display + 'static {
    /// Block until resources for a process are available.
    fn next_process(&self) -> BoxFuture<'static, ResourceResult<Box<dyn ProcessPermit>>>;
}

/// Represents one allowed process.
pub trait ProcessPermit: Send + Sync + fmt::Debug + 'static {}

/// Enforces a limited number of concurrent `Coordinator`s.
#[derive(Debug)]
pub struct CoordinatorFactory {
    limits: Arc<dyn ResourceLimits>,
}

impl CoordinatorFactory {
    pub fn new(limits: Arc<dyn ResourceLimits>) -> Self {
        Self { limits }
    }

    pub fn build<B>(&self) -> Coordinator<B>
    where
        B: Backend + Default,
    {
        let limits = self.limits.clone();

        let backend = B::default();

        Coordinator::new(limits, backend)
    }

    pub async fn container_requested(&self) {
        self.limits.container_requested().await
    }
}

#[derive(Debug)]
pub struct Coordinator<B> {
    limits: Arc<dyn ResourceLimits>,
    backend: B,
    stable: OnceCell<Container>,
    beta: OnceCell<Container>,
    nightly: OnceCell<Container>,
    token: CancelOnDrop,
}

/// Runs things.
///
/// # Liveness concerns
///
/// If you use one of the streaming versions (e.g. `begin_execute`),
/// you need to make sure that the stdout / stderr / status channels
/// are continuously read from or dropped completely. If not, one
/// channel can fill up, preventing the other channels from receiving
/// data as well.
impl<B> Coordinator<B>
where
    B: Backend,
{
    fn new(limits: Arc<dyn ResourceLimits>, backend: B) -> Self {
        Self {
            limits,
            backend,
            stable: OnceCell::new(),
            beta: OnceCell::new(),
            nightly: OnceCell::new(),
            token: CancelOnDrop::default(),
        }
    }

    pub async fn versions(&self) -> Result<Versions, VersionsError> {
        use versions_error::*;

        let [stable, beta, nightly] =
            [Channel::Stable, Channel::Beta, Channel::Nightly].map(async |c| {
                let c = self.select_channel(c).await?;
                c.versions().await.map_err(VersionsChannelError::from)
            });

        let stable = async { stable.await.context(StableSnafu) };
        let beta = async { beta.await.context(BetaSnafu) };
        let nightly = async { nightly.await.context(NightlySnafu) };

        let (stable, beta, nightly) = try_join!(stable, beta, nightly)?;

        Ok(Versions {
            stable,
            beta,
            nightly,
        })
    }

    pub async fn crates(&self) -> Result<Vec<Crate>, CratesError> {
        self.select_channel(Channel::Stable)
            .await?
            .crates()
            .await
            .map_err(Into::into)
    }

    pub async fn execute(
        &self,
        request: ExecuteRequest,
    ) -> Result<WithOutput<ExecuteResponse>, ExecuteError> {
        use execute_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .execute(request)
            .await
    }

    pub async fn begin_execute(
        &self,
        token: CancellationToken,
        request: ExecuteRequest,
    ) -> Result<ActiveExecution, ExecuteError> {
        use execute_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .begin_execute(token, request)
            .await
    }

    pub async fn compile(
        &self,
        request: CompileRequest,
    ) -> Result<WithOutput<CompileResponse>, CompileError> {
        use compile_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .compile(request)
            .await
    }

    pub async fn begin_compile(
        &self,
        token: CancellationToken,
        request: CompileRequest,
    ) -> Result<ActiveCompilation, CompileError> {
        use compile_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .begin_compile(token, request)
            .await
    }

    pub async fn format(
        &self,
        request: FormatRequest,
    ) -> Result<WithOutput<FormatResponse>, FormatError> {
        use format_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .format(request)
            .await
    }

    pub async fn begin_format(
        &self,
        token: CancellationToken,
        request: FormatRequest,
    ) -> Result<ActiveFormatting, FormatError> {
        use format_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .begin_format(token, request)
            .await
    }

    pub async fn clippy(
        &self,
        request: ClippyRequest,
    ) -> Result<WithOutput<ClippyResponse>, ClippyError> {
        use clippy_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .clippy(request)
            .await
    }

    pub async fn begin_clippy(
        &self,
        token: CancellationToken,
        request: ClippyRequest,
    ) -> Result<ActiveClippy, ClippyError> {
        use clippy_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .begin_clippy(token, request)
            .await
    }

    pub async fn miri(&self, request: MiriRequest) -> Result<WithOutput<MiriResponse>, MiriError> {
        use miri_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .miri(request)
            .await
    }

    pub async fn begin_miri(
        &self,
        token: CancellationToken,
        request: MiriRequest,
    ) -> Result<ActiveMiri, MiriError> {
        use miri_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .begin_miri(token, request)
            .await
    }

    pub async fn macro_expansion(
        &self,
        request: MacroExpansionRequest,
    ) -> Result<WithOutput<MacroExpansionResponse>, MacroExpansionError> {
        use macro_expansion_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .macro_expansion(request)
            .await
    }

    pub async fn begin_macro_expansion(
        &self,
        token: CancellationToken,
        request: MacroExpansionRequest,
    ) -> Result<ActiveMacroExpansion, MacroExpansionError> {
        use macro_expansion_error::*;

        self.select_channel(request.channel)
            .await
            .context(CouldNotStartContainerSnafu)?
            .begin_macro_expansion(token, request)
            .await
    }

    pub async fn idle(&mut self) -> Result<()> {
        let Self {
            stable,
            beta,
            nightly,
            token,
            ..
        } = self;

        let token = mem::take(token);
        token.cancel();

        let channels = [stable, beta, nightly].map(async |c| match c.take() {
            Some(c) => c.shutdown().await,
            _ => Ok(()),
        });

        let [stable, beta, nightly] = channels;

        let (stable, beta, nightly) = try_join!(stable, beta, nightly)?;
        let _: [(); 3] = [stable, beta, nightly];

        Ok(())
    }

    pub async fn shutdown(mut self) -> Result<B> {
        self.idle().await?;
        Ok(self.backend)
    }

    async fn select_channel(&self, channel: Channel) -> Result<&Container, Error> {
        let container = match channel {
            Channel::Stable => &self.stable,
            Channel::Beta => &self.beta,
            Channel::Nightly => &self.nightly,
        };

        container
            .get_or_try_init(|| {
                let limits = self.limits.clone();
                let token = self.token.0.clone();
                Container::new(channel, limits, token, &self.backend)
            })
            .await
    }
}

#[derive(Debug, Default)]
struct CancelOnDrop(CancellationToken);

impl CancelOnDrop {
    fn cancel(&self) {
        self.0.cancel();
    }
}

impl Drop for CancelOnDrop {
    fn drop(&mut self) {
        self.0.cancel();
    }
}

#[derive(Debug)]
struct Container {
    permit: Box<dyn ContainerPermit>,
    task: AbortOnDropHandle<Result<()>>,
    kill_child: TerminateContainer,
    modify_cargo_toml: ModifyCargoToml,
    commander: Commander,
}

impl Container {
    async fn new(
        channel: Channel,
        limits: Arc<dyn ResourceLimits>,
        token: CancellationToken,
        backend: &impl Backend,
    ) -> Result<Self> {
        let permit = limits.next_container().await.context(AcquirePermitSnafu)?;

        let (mut child, kill_child, stdin, stdout) =
            backend.run_worker_in_background(channel, &permit)?;
        let IoQueue {
            mut tasks,
            to_worker_tx,
            from_worker_rx,
        } = spawn_io_queue(stdin, stdout, token);

        let (command_tx, command_rx) = mpsc::channel(8);
        let demultiplex = Commander::demultiplex(command_rx, from_worker_rx);
        let demultiplex_task = tokio::spawn(demultiplex.in_current_span()).abort_on_drop();

        let task = tokio::spawn(
            async move {
                let child = async {
                    let _: std::process::ExitStatus =
                        child.wait().await.context(JoinWorkerSnafu)?;
                    Ok(())
                };

                let demultiplex_task = async {
                    demultiplex_task
                        .await
                        .context(DemultiplexerTaskPanickedSnafu)?
                        .context(DemultiplexerTaskFailedSnafu)
                };

                let task = async {
                    if let Some(t) = tasks.join_next().await {
                        t.context(IoQueuePanickedSnafu)??;
                    }
                    Ok(())
                };

                let (c, d, t) = try_join!(child, demultiplex_task, task)?;
                let _: [(); 3] = [c, d, t];

                Ok(())
            }
            .in_current_span(),
        )
        .abort_on_drop();

        let commander = Commander {
            to_worker_tx,
            to_demultiplexer_tx: command_tx,
            id: Default::default(),
        };

        let modify_cargo_toml = ModifyCargoToml::new(commander.clone())
            .await
            .context(CouldNotLoadCargoTomlSnafu)?;

        Ok(Container {
            permit,
            task,
            kill_child,
            modify_cargo_toml,
            commander,
        })
    }

    async fn versions(&self) -> Result<ChannelVersions, ContainerVersionsError> {
        use container_versions_error::*;

        let token = CancellationToken::new();

        let rustc = {
            let token = token.clone();
            async {
                self.rustc_version(token)
                    .await
                    .context(RustcSnafu)?
                    .context(RustcMissingSnafu)
            }
        };
        let rustfmt = {
            let token = token.clone();
            async {
                self.tool_version(token, "fmt")
                    .await
                    .context(RustfmtSnafu)?
                    .context(RustfmtMissingSnafu)
            }
        };
        let clippy = {
            let token = token.clone();
            async {
                self.tool_version(token, "clippy")
                    .await
                    .context(ClippySnafu)?
                    .context(ClippyMissingSnafu)
            }
        };
        let miri = {
            let token = token.clone();
            async { self.tool_version(token, "miri").await.context(MiriSnafu) }
        };

        let _token = token.drop_guard();

        let (rustc, rustfmt, clippy, miri) = try_join!(rustc, rustfmt, clippy, miri)?;

        Ok(ChannelVersions {
            rustc,
            rustfmt,
            clippy,
            miri,
        })
    }

    async fn rustc_version(
        &self,
        token: CancellationToken,
    ) -> Result<Option<Version>, VersionError> {
        let rustc_cmd = ExecuteCommandRequest::simple("rustc", ["--version", "--verbose"]);
        let output = self.version_output(token, rustc_cmd).await?;

        Ok(output.map(|o| Version::parse_rustc_version_verbose(&o)))
    }

    async fn tool_version(
        &self,
        token: CancellationToken,
        subcommand_name: &str,
    ) -> Result<Option<Version>, VersionError> {
        let tool_cmd = ExecuteCommandRequest::simple("cargo", [subcommand_name, "--version"]);
        let output = self.version_output(token, tool_cmd).await?;

        Ok(output.map(|o| Version::parse_tool_version(&o)))
    }

    async fn version_output(
        &self,
        token: CancellationToken,
        cmd: ExecuteCommandRequest,
    ) -> Result<Option<String>, VersionError> {
        let SpawnCargo {
            permit: _permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.spawn_cargo_task(token, cmd).await?;

        drop(stdin_tx);
        drop(status_rx);

        let task = async { task.await?.map_err(VersionError::from) };
        let o = WithOutput::try_absorb(task, stdout_rx, stderr_rx).await?;
        Ok(if o.success { Some(o.stdout) } else { None })
    }

    async fn crates(&self) -> Result<Vec<Crate>, ContainerCratesError> {
        let read = ReadFileRequest {
            path: "crate-information.json".into(),
        };
        let read = self.commander.one(read).await?;
        let crates = serde_json::from_slice::<Vec<InternalCrate>>(&read.0)?;
        Ok(crates.into_iter().map(Into::into).collect())
    }

    async fn execute(
        &self,
        request: ExecuteRequest,
    ) -> Result<WithOutput<ExecuteResponse>, ExecuteError> {
        let token = Default::default();

        let ActiveExecution {
            permit: _permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.begin_execute(token, request).await?;

        drop(stdin_tx);
        drop(status_rx);

        WithOutput::try_absorb(task, stdout_rx, stderr_rx).await
    }

    #[instrument(skip_all)]
    async fn begin_execute(
        &self,
        token: CancellationToken,
        request: ExecuteRequest,
    ) -> Result<ActiveExecution, ExecuteError> {
        use execute_error::*;

        let SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.do_request(request, token).await?;

        let task = async move {
            let ExecuteCommandResponse {
                success,
                exit_detail,
            } = task
                .await
                .context(CargoTaskPanickedSnafu)?
                .context(CargoFailedSnafu)?;
            Ok(ExecuteResponse {
                success,
                exit_detail,
            })
        }
        .boxed();

        let status_rx = tokio_stream::wrappers::ReceiverStream::new(status_rx)
            .map(|s| {
                let CommandStatistics {
                    total_time_secs,
                    resident_set_size_bytes,
                } = s;
                ExecuteStatus {
                    resident_set_size_bytes,
                    total_time_secs,
                }
            })
            .boxed();

        Ok(ActiveExecution {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        })
    }

    async fn compile(
        &self,
        request: CompileRequest,
    ) -> Result<WithOutput<CompileResponse>, CompileError> {
        let token = Default::default();

        let ActiveCompilation {
            permit: _permit,
            task,
            stdout_rx,
            stderr_rx,
        } = self.begin_compile(token, request).await?;

        WithOutput::try_absorb(task, stdout_rx, stderr_rx).await
    }

    #[instrument(skip_all)]
    async fn begin_compile(
        &self,
        token: CancellationToken,
        request: CompileRequest,
    ) -> Result<ActiveCompilation, CompileError> {
        use compile_error::*;

        let SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.do_request(&request, token).await?;

        drop(stdin_tx);
        drop(status_rx);

        let commander = self.commander.clone();
        let task = async move {
            let ExecuteCommandResponse {
                success,
                exit_detail,
            } = task
                .await
                .context(CargoTaskPanickedSnafu)?
                .context(CargoFailedSnafu)?;

            let code = if success {
                let read_output = request.read_output_request();

                let file: ReadFileResponse = commander
                    .one(read_output)
                    .await
                    .context(CouldNotReadCodeSnafu)?;
                String::from_utf8(file.0).context(CodeNotUtf8Snafu)?
            } else {
                String::new()
            };

            // TODO: This is synchronous...
            let code = request.postprocess_result(code);

            Ok(CompileResponse {
                success,
                exit_detail,
                code,
            })
        }
        .boxed();

        Ok(ActiveCompilation {
            permit,
            task,
            stdout_rx,
            stderr_rx,
        })
    }

    async fn format(
        &self,
        request: FormatRequest,
    ) -> Result<WithOutput<FormatResponse>, FormatError> {
        let token = Default::default();

        let ActiveFormatting {
            permit: _permit,
            task,
            stdout_rx,
            stderr_rx,
        } = self.begin_format(token, request).await?;

        WithOutput::try_absorb(task, stdout_rx, stderr_rx).await
    }

    async fn begin_format(
        &self,
        token: CancellationToken,
        request: FormatRequest,
    ) -> Result<ActiveFormatting, FormatError> {
        use format_error::*;

        let SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.do_request(&request, token).await?;

        drop(stdin_tx);
        drop(status_rx);

        let commander = self.commander.clone();
        let task = async move {
            let ExecuteCommandResponse {
                success,
                exit_detail,
            } = task
                .await
                .context(CargoTaskPanickedSnafu)?
                .context(CargoFailedSnafu)?;

            let read_output = request.read_output_request();
            let file = commander
                .one(read_output)
                .await
                .context(CouldNotReadCodeSnafu)?;
            let code = String::from_utf8(file.0).context(CodeNotUtf8Snafu)?;

            Ok(FormatResponse {
                success,
                exit_detail,
                code,
            })
        }
        .boxed();

        Ok(ActiveFormatting {
            permit,
            task,
            stdout_rx,
            stderr_rx,
        })
    }

    async fn clippy(
        &self,
        request: ClippyRequest,
    ) -> Result<WithOutput<ClippyResponse>, ClippyError> {
        let token = Default::default();

        let ActiveClippy {
            permit: _permit,
            task,
            stdout_rx,
            stderr_rx,
        } = self.begin_clippy(token, request).await?;

        WithOutput::try_absorb(task, stdout_rx, stderr_rx).await
    }

    async fn begin_clippy(
        &self,
        token: CancellationToken,
        request: ClippyRequest,
    ) -> Result<ActiveClippy, ClippyError> {
        use clippy_error::*;

        let SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.do_request(request, token).await?;

        drop(stdin_tx);
        drop(status_rx);

        let task = async move {
            let ExecuteCommandResponse {
                success,
                exit_detail,
            } = task
                .await
                .context(CargoTaskPanickedSnafu)?
                .context(CargoFailedSnafu)?;

            Ok(ClippyResponse {
                success,
                exit_detail,
            })
        }
        .boxed();

        Ok(ActiveClippy {
            permit,
            task,
            stdout_rx,
            stderr_rx,
        })
    }

    async fn miri(&self, request: MiriRequest) -> Result<WithOutput<MiriResponse>, MiriError> {
        let token = Default::default();

        let ActiveMiri {
            permit: _permit,
            task,
            stdout_rx,
            stderr_rx,
        } = self.begin_miri(token, request).await?;

        WithOutput::try_absorb(task, stdout_rx, stderr_rx).await
    }

    async fn begin_miri(
        &self,
        token: CancellationToken,
        request: MiriRequest,
    ) -> Result<ActiveMiri, MiriError> {
        use miri_error::*;

        let SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.do_request(request, token).await?;

        drop(stdin_tx);
        drop(status_rx);

        let task = async move {
            let ExecuteCommandResponse {
                success,
                exit_detail,
            } = task
                .await
                .context(CargoTaskPanickedSnafu)?
                .context(CargoFailedSnafu)?;

            Ok(MiriResponse {
                success,
                exit_detail,
            })
        }
        .boxed();

        Ok(ActiveMiri {
            permit,
            task,
            stdout_rx,
            stderr_rx,
        })
    }

    async fn macro_expansion(
        &self,
        request: MacroExpansionRequest,
    ) -> Result<WithOutput<MacroExpansionResponse>, MacroExpansionError> {
        let token = Default::default();

        let ActiveMacroExpansion {
            permit: _permit,
            task,
            stdout_rx,
            stderr_rx,
        } = self.begin_macro_expansion(token, request).await?;

        WithOutput::try_absorb(task, stdout_rx, stderr_rx).await
    }

    async fn begin_macro_expansion(
        &self,
        token: CancellationToken,
        request: MacroExpansionRequest,
    ) -> Result<ActiveMacroExpansion, MacroExpansionError> {
        use macro_expansion_error::*;

        let SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = self.do_request(request, token).await?;

        drop(stdin_tx);
        drop(status_rx);

        let task = async move {
            let ExecuteCommandResponse {
                success,
                exit_detail,
            } = task
                .await
                .context(CargoTaskPanickedSnafu)?
                .context(CargoFailedSnafu)?;

            Ok(MacroExpansionResponse {
                success,
                exit_detail,
            })
        }
        .boxed();

        Ok(ActiveMacroExpansion {
            permit,
            task,
            stdout_rx,
            stderr_rx,
        })
    }

    async fn do_request(
        &self,
        request: impl LowerRequest + CargoTomlModifier,
        token: CancellationToken,
    ) -> Result<SpawnCargo, DoRequestError> {
        use do_request_error::*;

        let delete_previous_main = async {
            self.commander
                .one(request.delete_previous_main_request())
                .await
                .context(CouldNotDeletePreviousCodeSnafu)
                .map(drop::<crate::message::DeleteFileResponse>)
        };

        let write_main = async {
            self.commander
                .one(request.write_main_request())
                .await
                .context(CouldNotWriteCodeSnafu)
                .map(drop::<crate::message::WriteFileResponse>)
        };

        let modify_cargo_toml = async {
            self.modify_cargo_toml
                .modify_for(&request)
                .await
                .context(CouldNotModifyCargoTomlSnafu)
        };

        let (d, w, m) = try_join!(delete_previous_main, write_main, modify_cargo_toml)?;
        let _: [(); 3] = [d, w, m];

        let execute_cargo = request.execute_cargo_request();
        self.spawn_cargo_task(token, execute_cargo)
            .await
            .context(CouldNotStartCargoSnafu)
    }

    async fn spawn_cargo_task(
        &self,
        token: CancellationToken,
        execute_cargo: ExecuteCommandRequest,
    ) -> Result<SpawnCargo, SpawnCargoError> {
        use spawn_cargo_error::*;

        let permit = self
            .permit
            .next_process()
            .await
            .context(AcquirePermitSnafu)?;

        trace!(?execute_cargo, "starting cargo task");

        let (stdin_tx, mut stdin_rx) = mpsc::channel(8);
        let (stdout_tx, stdout_rx) = mpsc::channel(8);
        let (stderr_tx, stderr_rx) = mpsc::channel(8);
        let (status_tx, status_rx) = mpsc::channel(8);

        let (to_worker_tx, mut from_worker_rx) = self
            .commander
            .many(execute_cargo)
            .await
            .context(CouldNotStartCargoSnafu)?;

        let token = token.child_token();
        let drop_token = token.clone();

        let task = tokio::spawn({
            async move {
                let mut cancelled = pin!(token.cancelled().fuse());
                let mut stdin_open = true;

                loop {
                    enum Event {
                        Cancelled,
                        Stdin(Option<String>),
                        FromWorker(WorkerMessage),
                    }
                    use Event::*;

                    let event = select! {
                        () = &mut cancelled => Cancelled,

                        stdin = stdin_rx.recv(), if stdin_open => Stdin(stdin),

                        Some(container_msg) = from_worker_rx.recv() => FromWorker(container_msg),

                        else => return UnexpectedEndOfMessagesSnafu.fail(),
                    };

                    match event {
                        Cancelled => {
                            let msg = CoordinatorMessage::Kill;
                            trace!(msg_name = msg.as_ref(), "processing");
                            to_worker_tx.send(msg).await.context(KillSnafu)?;
                        }

                        Stdin(stdin) => {
                            let msg = match stdin {
                                Some(stdin) => CoordinatorMessage::StdinPacket(stdin),

                                None => {
                                    stdin_open = false;
                                    CoordinatorMessage::StdinClose
                                }
                            };

                            trace!(msg_name = msg.as_ref(), "processing");
                            to_worker_tx.send(msg).await.context(StdinSnafu)?;
                        }

                        FromWorker(container_msg) => {
                            trace!(msg_name = container_msg.as_ref(), "processing");

                            match container_msg {
                                WorkerMessage::ExecuteCommand(resp) => {
                                    return Ok(resp);
                                }

                                WorkerMessage::StdoutPacket(packet) => {
                                    stdout_tx.send(packet).await.ok(/* Receiver gone, that's OK */);
                                }

                                WorkerMessage::StderrPacket(packet) => {
                                    stderr_tx.send(packet).await.ok(/* Receiver gone, that's OK */);
                                }

                                WorkerMessage::CommandStatistics(stats) => {
                                    status_tx.send(stats).await.ok(/* Receiver gone, that's OK */);
                                }

                                WorkerMessage::Error(e) => {
                                    return Err(SerializedError2::adapt(e)).context(WorkerSnafu);
                                }

                                WorkerMessage::Error2(e) => return Err(e).context(WorkerSnafu),

                                _ => {
                                    let message = container_msg.as_ref();
                                    return UnexpectedMessageSnafu { message }.fail();
                                }
                            }
                        }
                    }
                }
            }
            .instrument(trace_span!("cargo task").or_current())
        })
        .cancel_on_drop(drop_token);

        Ok(SpawnCargo {
            permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx,
        })
    }

    async fn shutdown(self) -> Result<()> {
        let Self {
            permit,
            task,
            mut kill_child,
            modify_cargo_toml,
            commander,
        } = self;
        drop(commander);
        drop(modify_cargo_toml);

        kill_child.terminate_now().await?;

        let r = task.await;
        drop(permit);

        r.context(ContainerTaskPanickedSnafu)?
    }
}

pub struct ActiveExecution {
    pub permit: Box<dyn ProcessPermit>,
    pub task: BoxFuture<'static, Result<ExecuteResponse, ExecuteError>>,
    pub stdin_tx: mpsc::Sender<String>,
    pub stdout_rx: mpsc::Receiver<String>,
    pub stderr_rx: mpsc::Receiver<String>,
    pub status_rx: BoxStream<'static, ExecuteStatus>,
}

impl fmt::Debug for ActiveExecution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActiveExecution")
            .field("task", &"<future>")
            .field("stdin_tx", &self.stdin_tx)
            .field("stdout_rx", &self.stdout_rx)
            .field("stderr_rx", &self.stderr_rx)
            .finish()
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum ExecuteError {
    #[snafu(display("Could not start the container"))]
    CouldNotStartContainer { source: Error },

    #[snafu(transparent)]
    DoRequest { source: DoRequestError },

    #[snafu(display("The Cargo task panicked"))]
    CargoTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Cargo task failed"))]
    CargoFailed { source: SpawnCargoError },
}

pub struct ActiveCompilation {
    pub permit: Box<dyn ProcessPermit>,
    pub task: BoxFuture<'static, Result<CompileResponse, CompileError>>,
    pub stdout_rx: mpsc::Receiver<String>,
    pub stderr_rx: mpsc::Receiver<String>,
}

impl fmt::Debug for ActiveCompilation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActiveCompilation")
            .field("task", &"<future>")
            .field("stdout_rx", &self.stdout_rx)
            .field("stderr_rx", &self.stderr_rx)
            .finish()
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum CompileError {
    #[snafu(display("Could not start the container"))]
    CouldNotStartContainer { source: Error },

    #[snafu(transparent)]
    DoRequest { source: DoRequestError },

    #[snafu(display("The Cargo task panicked"))]
    CargoTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Cargo task failed"))]
    CargoFailed { source: SpawnCargoError },

    #[snafu(display("Could not read the compilation output"))]
    CouldNotReadCode { source: CommanderError },

    #[snafu(display("The compilation output was not UTF-8"))]
    CodeNotUtf8 { source: std::string::FromUtf8Error },
}

pub struct ActiveFormatting {
    pub permit: Box<dyn ProcessPermit>,
    pub task: BoxFuture<'static, Result<FormatResponse, FormatError>>,
    pub stdout_rx: mpsc::Receiver<String>,
    pub stderr_rx: mpsc::Receiver<String>,
}

impl fmt::Debug for ActiveFormatting {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActiveFormatting")
            .field("task", &"<future>")
            .field("stdout_rx", &self.stdout_rx)
            .field("stderr_rx", &self.stderr_rx)
            .finish()
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum FormatError {
    #[snafu(display("Could not start the container"))]
    CouldNotStartContainer { source: Error },

    #[snafu(transparent)]
    DoRequest { source: DoRequestError },

    #[snafu(display("The Cargo task panicked"))]
    CargoTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Cargo task failed"))]
    CargoFailed { source: SpawnCargoError },

    #[snafu(display("Could not read the compilation output"))]
    CouldNotReadCode { source: CommanderError },

    #[snafu(display("The compilation output was not UTF-8"))]
    CodeNotUtf8 { source: std::string::FromUtf8Error },
}

pub struct ActiveClippy {
    pub permit: Box<dyn ProcessPermit>,
    pub task: BoxFuture<'static, Result<ClippyResponse, ClippyError>>,
    pub stdout_rx: mpsc::Receiver<String>,
    pub stderr_rx: mpsc::Receiver<String>,
}

impl fmt::Debug for ActiveClippy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActiveClippy")
            .field("task", &"<future>")
            .field("stdout_rx", &self.stdout_rx)
            .field("stderr_rx", &self.stderr_rx)
            .finish()
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum ClippyError {
    #[snafu(display("Could not start the container"))]
    CouldNotStartContainer { source: Error },

    #[snafu(transparent)]
    DoRequest { source: DoRequestError },

    #[snafu(display("The Cargo task panicked"))]
    CargoTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Cargo task failed"))]
    CargoFailed { source: SpawnCargoError },
}

pub struct ActiveMiri {
    pub permit: Box<dyn ProcessPermit>,
    pub task: BoxFuture<'static, Result<MiriResponse, MiriError>>,
    pub stdout_rx: mpsc::Receiver<String>,
    pub stderr_rx: mpsc::Receiver<String>,
}

impl fmt::Debug for ActiveMiri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActiveMiri")
            .field("task", &"<future>")
            .field("stdout_rx", &self.stdout_rx)
            .field("stderr_rx", &self.stderr_rx)
            .finish()
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum MiriError {
    #[snafu(display("Could not start the container"))]
    CouldNotStartContainer { source: Error },

    #[snafu(transparent)]
    DoRequest { source: DoRequestError },

    #[snafu(display("The Cargo task panicked"))]
    CargoTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Cargo task failed"))]
    CargoFailed { source: SpawnCargoError },
}

pub struct ActiveMacroExpansion {
    pub permit: Box<dyn ProcessPermit>,
    pub task: BoxFuture<'static, Result<MacroExpansionResponse, MacroExpansionError>>,
    pub stdout_rx: mpsc::Receiver<String>,
    pub stderr_rx: mpsc::Receiver<String>,
}

impl fmt::Debug for ActiveMacroExpansion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ActiveMacroExpansion")
            .field("task", &"<future>")
            .field("stdout_rx", &self.stdout_rx)
            .field("stderr_rx", &self.stderr_rx)
            .finish()
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum MacroExpansionError {
    #[snafu(display("Could not start the container"))]
    CouldNotStartContainer { source: Error },

    #[snafu(transparent)]
    DoRequest { source: DoRequestError },

    #[snafu(display("The Cargo task panicked"))]
    CargoTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Cargo task failed"))]
    CargoFailed { source: SpawnCargoError },
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum DoRequestError {
    #[snafu(display("Could not modify Cargo.toml"))]
    CouldNotModifyCargoToml { source: ModifyCargoTomlError },

    #[snafu(display("Could not delete previous source code"))]
    CouldNotDeletePreviousCode { source: CommanderError },

    #[snafu(display("Could not write source code"))]
    CouldNotWriteCode { source: CommanderError },

    #[snafu(display("Could not start Cargo task"))]
    CouldNotStartCargo { source: SpawnCargoError },
}

/// Triggers `CancellationToken::cancel` when dropped, wrapping
/// another future (which should make use of the token) to keep this
/// guard paired with it.
#[derive(Debug, Default)]
struct CancelOnDropFuture<F> {
    token: CancellationToken,
    fut: F,
}

impl<F> Drop for CancelOnDropFuture<F> {
    fn drop(&mut self) {
        self.token.cancel();
    }
}

impl<F> Future for CancelOnDropFuture<F>
where
    F: Future + Unpin,
{
    type Output = F::Output;

    fn poll(mut self: pin::Pin<&mut Self>, cx: &mut task::Context<'_>) -> task::Poll<Self::Output> {
        pin::Pin::new(&mut self.fut).poll(cx)
    }
}

trait CancelOnDropFutureExt {
    fn cancel_on_drop(self, token: CancellationToken) -> CancelOnDropFuture<Self>
    where
        Self: Sized;
}

impl<T> CancelOnDropFutureExt for T {
    fn cancel_on_drop(self, token: CancellationToken) -> CancelOnDropFuture<Self>
    where
        Self: Sized,
    {
        CancelOnDropFuture { token, fut: self }
    }
}

struct SpawnCargo {
    permit: Box<dyn ProcessPermit>,
    task: CancelOnDropFuture<JoinHandle<Result<ExecuteCommandResponse, SpawnCargoError>>>,
    stdin_tx: mpsc::Sender<String>,
    stdout_rx: mpsc::Receiver<String>,
    stderr_rx: mpsc::Receiver<String>,
    status_rx: mpsc::Receiver<CommandStatistics>,
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum SpawnCargoError {
    #[snafu(display("Could not start Cargo"))]
    CouldNotStartCargo { source: CommanderError },

    #[snafu(display("The worker operation failed"))]
    Worker { source: SerializedError2 },

    #[snafu(display("Received the unexpected message `{message}`"))]
    UnexpectedMessage { message: String },

    #[snafu(display("There are no more messages"))]
    UnexpectedEndOfMessages,

    #[snafu(display("Unable to send stdin message"))]
    Stdin { source: MultiplexedSenderError },

    #[snafu(display("Unable to send kill message"))]
    Kill { source: MultiplexedSenderError },

    #[snafu(display("Could not acquire a process permit"))]
    AcquirePermit { source: ResourceError },
}

#[derive(Debug, Clone)]
struct Commander {
    to_worker_tx: mpsc::Sender<Multiplexed<CoordinatorMessage>>,
    to_demultiplexer_tx: mpsc::Sender<(oneshot::Sender<()>, DemultiplexCommand)>,
    id: Arc<AtomicU64>,
}

trait LowerRequest {
    fn delete_previous_main_request(&self) -> DeleteFileRequest;

    fn write_main_request(&self) -> WriteFileRequest;

    fn execute_cargo_request(&self) -> ExecuteCommandRequest;
}

impl<S> LowerRequest for &S
where
    S: LowerRequest,
{
    fn delete_previous_main_request(&self) -> DeleteFileRequest {
        S::delete_previous_main_request(self)
    }

    fn write_main_request(&self) -> WriteFileRequest {
        S::write_main_request(self)
    }

    fn execute_cargo_request(&self) -> ExecuteCommandRequest {
        S::execute_cargo_request(self)
    }
}

trait CargoTomlModifier {
    fn modify_cargo_toml(&self, cargo_toml: toml::Value) -> toml::Value;
}

impl<C> CargoTomlModifier for &C
where
    C: CargoTomlModifier,
{
    fn modify_cargo_toml(&self, cargo_toml: toml::Value) -> toml::Value {
        C::modify_cargo_toml(self, cargo_toml)
    }
}

#[derive(Debug)]
struct ModifyCargoToml {
    commander: Commander,
    cargo_toml: toml::Value,
}

impl ModifyCargoToml {
    const PATH: &'static str = "Cargo.toml";

    async fn new(commander: Commander) -> Result<Self, ModifyCargoTomlError> {
        let cargo_toml = Self::read(&commander).await?;
        Ok(Self {
            commander,
            cargo_toml,
        })
    }

    async fn modify_for(
        &self,
        request: &impl CargoTomlModifier,
    ) -> Result<(), ModifyCargoTomlError> {
        let cargo_toml = self.cargo_toml.clone();
        let cargo_toml = request.modify_cargo_toml(cargo_toml);
        Self::write(&self.commander, cargo_toml).await
    }

    async fn read(commander: &Commander) -> Result<toml::Value, ModifyCargoTomlError> {
        use modify_cargo_toml_error::*;

        let path = Self::PATH.to_owned();
        let cargo_toml = commander
            .one(ReadFileRequest { path })
            .await
            .context(CouldNotReadSnafu)?;

        let cargo_toml = String::from_utf8(cargo_toml.0)?;
        let cargo_toml = toml::from_str(&cargo_toml)?;

        Ok(cargo_toml)
    }

    async fn write(
        commander: &Commander,
        cargo_toml: toml::Value,
    ) -> Result<(), ModifyCargoTomlError> {
        use modify_cargo_toml_error::*;

        let cargo_toml = toml::to_string(&cargo_toml)?;
        let content = cargo_toml.into_bytes();

        let path = Self::PATH.to_owned();
        commander
            .one(WriteFileRequest { path, content })
            .await
            .context(CouldNotWriteSnafu)?;

        Ok(())
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum ModifyCargoTomlError {
    #[snafu(display("Could not read the file"))]
    CouldNotRead { source: CommanderError },

    #[snafu(display("Could not parse the file as UTF-8"))]
    #[snafu(context(false))]
    InvalidUtf8 { source: std::string::FromUtf8Error },

    #[snafu(display("Could not deserialize the file as TOML"))]
    #[snafu(context(false))]
    CouldNotDeserialize { source: toml::de::Error },

    #[snafu(display("Could not serialize the file as TOML"))]
    #[snafu(context(false))]
    CouldNotSerialize { source: toml::ser::Error },

    #[snafu(display("Could not write the file"))]
    CouldNotWrite { source: CommanderError },
}

struct MultiplexedSender {
    job_id: JobId,
    to_worker_tx: mpsc::Sender<Multiplexed<CoordinatorMessage>>,
}

impl MultiplexedSender {
    async fn send(
        &self,
        message: impl Into<CoordinatorMessage>,
    ) -> Result<(), MultiplexedSenderError> {
        use multiplexed_sender_error::*;

        let message = message.into();
        let message = Multiplexed(self.job_id, message);

        self.to_worker_tx
            .send(message)
            .await
            .drop_error_details()
            .context(MultiplexedSenderSnafu)
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
#[snafu(display("Could not send a message to the worker"))]
pub struct MultiplexedSenderError {
    source: mpsc::error::SendError<()>,
}

impl Commander {
    const GC_PERIOD: Duration = Duration::from_secs(30);

    #[instrument(skip_all)]
    async fn demultiplex(
        mut command_rx: mpsc::Receiver<(oneshot::Sender<()>, DemultiplexCommand)>,
        mut from_worker_rx: mpsc::Receiver<Multiplexed<WorkerMessage>>,
    ) -> Result<(), CommanderError> {
        use commander_error::*;

        let mut waiting = HashMap::new();
        let mut waiting_once = HashMap::new();

        let mut gc_interval = time::interval(Self::GC_PERIOD);
        gc_interval.set_missed_tick_behavior(MissedTickBehavior::Delay);

        loop {
            enum Event {
                Command(Option<(oneshot::Sender<()>, DemultiplexCommand)>),

                FromWorker(Option<Multiplexed<WorkerMessage>>),

                // Find any channels where the receivers have been
                // dropped and clear out the sending halves.
                Gc,
            }
            use Event::*;

            let event = select! {
                command = command_rx.recv() => Command(command),

                msg = from_worker_rx.recv() => FromWorker(msg),

                _ = gc_interval.tick() => Gc,
            };

            match event {
                Command(None) => break,
                Command(Some((ack_tx, command))) => {
                    match command {
                        DemultiplexCommand::Listen(job_id, waiter) => {
                            trace!(job_id, "adding listener (many)");
                            let old = waiting.insert(job_id, waiter);
                            ensure!(old.is_none(), DuplicateDemultiplexerClientSnafu { job_id });
                        }

                        DemultiplexCommand::ListenOnce(job_id, waiter) => {
                            trace!(job_id, "adding listener (once)");
                            let old = waiting_once.insert(job_id, waiter);
                            ensure!(old.is_none(), DuplicateDemultiplexerClientSnafu { job_id });
                        }
                    }

                    ack_tx.send(()).ok(/* Don't care about it */);
                }

                FromWorker(None) => break,
                FromWorker(Some(Multiplexed(job_id, msg))) => {
                    if let Some(waiter) = waiting_once.remove(&job_id) {
                        trace!(job_id, "notifying listener (once)");
                        waiter.send(msg).ok(/* Don't care about it */);
                        continue;
                    }

                    if let Some(waiter) = waiting.get(&job_id) {
                        trace!(job_id, "notifying listener (many)");
                        waiter.send(msg).await.ok(/* Don't care about it */);
                        continue;
                    }

                    warn!(job_id, msg_name = msg.as_ref(), "no listener to notify");
                }

                Gc => {
                    waiting.retain(|_job_id, tx| !tx.is_closed());
                    waiting_once.retain(|_job_id, tx| !tx.is_closed());
                }
            }
        }

        Ok(())
    }

    fn next_id(&self) -> JobId {
        self.id.fetch_add(1, Ordering::SeqCst)
    }

    async fn send_to_demultiplexer(
        &self,
        command: DemultiplexCommand,
    ) -> Result<(), CommanderError> {
        use commander_error::*;

        let (ack_tx, ack_rx) = oneshot::channel();

        self.to_demultiplexer_tx
            .send((ack_tx, command))
            .await
            .drop_error_details()
            .context(UnableToSendToDemultiplexerSnafu)?;

        ack_rx.await.context(DemultiplexerDidNotRespondSnafu)
    }

    fn build_multiplexed_sender(&self, job_id: JobId) -> MultiplexedSender {
        let to_worker_tx = self.to_worker_tx.clone();
        MultiplexedSender {
            job_id,
            to_worker_tx,
        }
    }

    async fn one<M>(&self, message: M) -> Result<M::Response, CommanderError>
    where
        M: Into<CoordinatorMessage>,
        M: OneToOneResponse,
        Result<M::Response, SerializedError2>: TryFrom<WorkerMessage>,
    {
        use commander_error::*;

        let id = self.next_id();
        let to_worker_tx = self.build_multiplexed_sender(id);
        let (from_demultiplexer_tx, from_demultiplexer_rx) = oneshot::channel();

        self.send_to_demultiplexer(DemultiplexCommand::ListenOnce(id, from_demultiplexer_tx))
            .await?;
        to_worker_tx
            .send(message)
            .await
            .context(UnableToStartOneSnafu)?;
        let msg = from_demultiplexer_rx
            .await
            .context(UnableToReceiveFromDemultiplexerSnafu)?;

        match <Result<_, _>>::try_from(msg) {
            Ok(v) => v.context(WorkerOperationFailedSnafu),
            Err(_) => UnexpectedResponseTypeSnafu.fail(),
        }
    }

    async fn many<M>(
        &self,
        message: M,
    ) -> Result<(MultiplexedSender, mpsc::Receiver<WorkerMessage>), CommanderError>
    where
        M: Into<CoordinatorMessage>,
    {
        use commander_error::*;

        let id = self.next_id();
        let to_worker_tx = self.build_multiplexed_sender(id);
        let (from_worker_tx, from_worker_rx) = mpsc::channel(8);

        self.send_to_demultiplexer(DemultiplexCommand::Listen(id, from_worker_tx))
            .await?;
        to_worker_tx
            .send(message)
            .await
            .context(UnableToStartManySnafu)?;

        Ok((to_worker_tx, from_worker_rx))
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum CommanderError {
    #[snafu(display("Two listeners subscribed to job {job_id}"))]
    DuplicateDemultiplexerClient { job_id: JobId },

    #[snafu(display("Could not send a message to the demultiplexer"))]
    UnableToSendToDemultiplexer { source: mpsc::error::SendError<()> },

    #[snafu(display("Could not send a message to the demultiplexer"))]
    DemultiplexerDidNotRespond { source: oneshot::error::RecvError },

    #[snafu(display("Did not receive a response from the demultiplexer"))]
    UnableToReceiveFromDemultiplexer { source: oneshot::error::RecvError },

    #[snafu(display("Could not start single request/response interaction"))]
    UnableToStartOne { source: MultiplexedSenderError },

    #[snafu(display("Could not start continuous interaction"))]
    UnableToStartMany { source: MultiplexedSenderError },

    #[snafu(display("Did not receive the expected response type from the worker"))]
    UnexpectedResponseType,

    #[snafu(display("The worker operation failed"))]
    WorkerOperationFailed { source: SerializedError2 },
}

pub static TRACKED_CONTAINERS: LazyLock<Mutex<BTreeSet<Arc<str>>>> =
    LazyLock::new(Default::default);

#[derive(Debug)]
pub struct TerminateContainer(Option<(String, Command)>);

impl TerminateContainer {
    pub fn new(name: String, command: Command) -> Self {
        Self::start_tracking(&name);

        Self(Some((name, command)))
    }

    pub fn none() -> Self {
        Self(None)
    }

    async fn terminate_now(&mut self) -> Result<(), TerminateContainerError> {
        use terminate_container_error::*;

        if let Some((name, mut kill_child)) = self.0.take() {
            Self::stop_tracking(&name, false);
            let o = kill_child
                .output()
                .await
                .context(TerminateContainerSnafu { name: &name })?;
            Self::report_failure(name, o);
        } else {
            warn!("Would have stopped tracking in `terminate_now`, but found `None`");
        }

        Ok(())
    }

    #[instrument]
    fn start_tracking(name: &str) {
        let was_inserted = TRACKED_CONTAINERS
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(name.into());

        if was_inserted {
            info!("Started tracking container");
        } else {
            error!("Started tracking container, but it was already tracked");
        }
    }

    #[instrument]
    fn stop_tracking(name: &str, from_drop: bool) {
        let was_tracked = TRACKED_CONTAINERS
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .remove(name);

        if was_tracked {
            info!(from_drop, "Stopped tracking container");
        } else {
            error!("Stopped tracking container, but it was not in the tracking set");
        }
    }

    fn report_failure(name: String, s: std::process::Output) {
        // We generally don't care if the command itself succeeds or
        // not; the container may already be dead! However, let's log
        // it in an attempt to debug cases where there are more
        // containers running than we expect.

        if !s.status.success() {
            let code = s.status.code();
            // FUTURE: use `_owned`
            let stdout = String::from_utf8_lossy(&s.stdout);
            let stderr = String::from_utf8_lossy(&s.stderr);

            let stdout = stdout.trim();
            let stderr = stderr.trim();

            error!(?code, %stdout, %stderr, %name, "Killing the container failed");
        }
    }
}

impl Drop for TerminateContainer {
    fn drop(&mut self) {
        if let Some((name, mut kill_child)) = self.0.take() {
            Self::stop_tracking(&name, true);
            match kill_child.as_std_mut().output() {
                Ok(o) => Self::report_failure(name, o),
                Err(e) => error!("Unable to kill container {name} while dropping: {e}"),
            }
        }
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
#[snafu(display("Unable to kill the Docker container {name}"))]
pub struct TerminateContainerError {
    name: String,
    source: std::io::Error,
}

pub trait Backend {
    fn run_worker_in_background(
        &self,
        channel: Channel,
        id: impl fmt::Display,
    ) -> Result<(Child, TerminateContainer, ChildStdin, ChildStdout)> {
        let (mut start, kill) = self.prepare_worker_command(channel, id);

        let mut child = start
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .context(SpawnWorkerSnafu)?;
        let stdin = child.stdin.take().context(WorkerStdinCaptureSnafu)?;
        let stdout = child.stdout.take().context(WorkerStdoutCaptureSnafu)?;
        Ok((child, kill, stdin, stdout))
    }

    fn prepare_worker_command(
        &self,
        channel: Channel,
        id: impl fmt::Display,
    ) -> (Command, TerminateContainer);
}

impl<B> Backend for &B
where
    B: Backend,
{
    fn prepare_worker_command(
        &self,
        channel: Channel,
        id: impl fmt::Display,
    ) -> (Command, TerminateContainer) {
        B::prepare_worker_command(self, channel, id)
    }
}

macro_rules! docker_command {
    ($($arg:expr),* $(,)?) => ({
        let mut cmd = Command::new("docker");
        $( cmd.arg($arg); )*
        cmd
    });
}

macro_rules! docker_target_arch {
    (x86_64: $x:expr, aarch64: $a:expr $(,)?) => {{
        #[cfg(target_arch = "x86_64")]
        {
            $x
        }

        #[cfg(target_arch = "aarch64")]
        {
            $a
        }
    }};
}

const DOCKER_ARCH: &str = docker_target_arch! {
    x86_64: "linux/amd64",
    aarch64: "linux/arm64",
};

fn basic_secure_docker_command() -> Command {
    docker_command!(
        "run",
        "--platform",
        DOCKER_ARCH,
        "--cap-drop=ALL",
        "--net",
        "none",
        "--memory",
        "512m",
        "--memory-swap",
        "640m",
        "--pids-limit",
        "512",
        "--oom-score-adj",
        "1000",
    )
}

#[derive(Default)]
pub struct DockerBackend(());

impl Backend for DockerBackend {
    fn prepare_worker_command(
        &self,
        channel: Channel,
        id: impl fmt::Display,
    ) -> (Command, TerminateContainer) {
        let name = format!("playground-{id}");

        let mut command = basic_secure_docker_command();
        command
            .args(["--name", &name])
            .arg("-i")
            .args(["-a", "stdin", "-a", "stdout", "-a", "stderr"])
            .arg("--rm")
            .arg(channel.to_container_name())
            .arg("worker")
            .arg("/playground");

        let mut kill = Command::new("docker");
        kill.arg("kill").args(["--signal", "KILL"]).arg(&name);
        let kill = TerminateContainer::new(name, kill);

        (command, kill)
    }
}

impl Channel {
    fn to_container_name(self) -> &'static str {
        match self {
            Channel::Stable => "rust-stable",
            Channel::Beta => "rust-beta",
            Channel::Nightly => "rust-nightly",
        }
    }
}

pub type Result<T, E = Error> = ::std::result::Result<T, E>;

#[derive(Debug, Snafu)]
pub enum Error {
    #[snafu(display("Reached system process limit"))]
    SpawnWorker { source: std::io::Error },

    #[snafu(display("Unable to join child process"))]
    JoinWorker { source: std::io::Error },

    #[snafu(display("The demultiplexer task panicked"))]
    DemultiplexerTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("The demultiplexer task failed"))]
    DemultiplexerTaskFailed { source: CommanderError },

    #[snafu(display("The IO queue task panicked"))]
    IoQueuePanicked { source: tokio::task::JoinError },

    #[snafu(transparent)]
    KillWorker { source: TerminateContainerError },

    #[snafu(display("The container task panicked"))]
    ContainerTaskPanicked { source: tokio::task::JoinError },

    #[snafu(display("Worker process's stdin not captured"))]
    WorkerStdinCapture,

    #[snafu(display("Worker process's stdout not captured"))]
    WorkerStdoutCapture,

    #[snafu(display("Failed to flush child stdin"))]
    WorkerStdinFlush { source: std::io::Error },

    #[snafu(display("Failed to deserialize worker message"))]
    WorkerMessageDeserialization { source: bincode::Error },

    #[snafu(display("Failed to serialize coordinator message"))]
    CoordinatorMessageSerialization { source: bincode::Error },

    #[snafu(display("Failed to send worker message through channel"))]
    UnableToSendWorkerMessage { source: mpsc::error::SendError<()> },

    #[snafu(display("Unable to load original Cargo.toml"))]
    CouldNotLoadCargoToml { source: ModifyCargoTomlError },

    #[snafu(display("Could not acquire a container permit"))]
    AcquirePermit { source: ResourceError },
}

struct IoQueue {
    tasks: JoinSet<Result<()>>,
    to_worker_tx: mpsc::Sender<Multiplexed<CoordinatorMessage>>,
    from_worker_rx: mpsc::Receiver<Multiplexed<WorkerMessage>>,
}

// Child stdin/out <--> messages.
fn spawn_io_queue(stdin: ChildStdin, stdout: ChildStdout, token: CancellationToken) -> IoQueue {
    use std::io::{prelude::*, BufReader, BufWriter};

    let mut tasks = JoinSet::new();

    let (tx, from_worker_rx) = mpsc::channel(8);
    tasks.spawn_blocking(move || {
        let span = info_span!("child_io_queue::input");
        let _span = span.enter();

        let stdout = SyncIoBridge::new(stdout);
        let mut stdout = BufReader::new(stdout);

        loop {
            let worker_msg = bincode::deserialize_from(&mut stdout);

            if bincode_input_closed(&worker_msg) {
                break;
            };

            let worker_msg = worker_msg.context(WorkerMessageDeserializationSnafu)?;

            tx.blocking_send(worker_msg)
                .drop_error_details()
                .context(UnableToSendWorkerMessageSnafu)?;
        }

        Ok(())
    });

    let (to_worker_tx, mut rx) = mpsc::channel(8);
    tasks.spawn_blocking(move || {
        let span = info_span!("child_io_queue::output");
        let _span = span.enter();

        let stdin = SyncIoBridge::new(stdin);
        let mut stdin = BufWriter::new(stdin);

        let handle = tokio::runtime::Handle::current();

        loop {
            let coordinator_msg = handle.block_on(token.run_until_cancelled(rx.recv()));

            let Some(Some(coordinator_msg)) = coordinator_msg else {
                break;
            };

            bincode::serialize_into(&mut stdin, &coordinator_msg)
                .context(CoordinatorMessageSerializationSnafu)?;

            stdin.flush().context(WorkerStdinFlushSnafu)?;
        }

        Ok(())
    });

    IoQueue {
        tasks,
        to_worker_tx,
        from_worker_rx,
    }
}

#[cfg(test)]
mod tests {
    use assertables::*;
    use futures::future::{join, try_join_all};
    use std::{
        env,
        sync::{LazyLock, Once},
    };
    use tempfile::TempDir;

    use super::*;

    #[allow(dead_code)]
    fn setup_tracing() {
        use tracing::Level;
        use tracing_subscriber::fmt::TestWriter;

        tracing_subscriber::fmt()
            .with_ansi(false)
            .with_max_level(Level::TRACE)
            .with_writer(TestWriter::new())
            .try_init()
            .ok();
    }

    #[derive(Debug)]
    struct TestBackend {
        project_dir: TempDir,
    }

    impl Default for TestBackend {
        fn default() -> Self {
            static COMPILE_WORKER_ONCE: Once = Once::new();

            COMPILE_WORKER_ONCE.call_once(|| {
                let output = std::process::Command::new("cargo")
                    .arg("build")
                    .output()
                    .expect("Build failed");
                assert!(output.status.success(), "Build failed");
            });

            let project_dir = TempDir::with_prefix("playground")
                .expect("Failed to create temporary project directory");

            for channel in Channel::ALL {
                let channel = channel.to_str();
                let channel_dir = project_dir.path().join(channel);

                let output = std::process::Command::new("cargo")
                    .arg(format!("+{channel}"))
                    .arg("new")
                    .args(["--name", "playground"])
                    .arg(&channel_dir)
                    .output()
                    .expect("Cargo new failed");
                assert!(output.status.success(), "Cargo new failed");

                let main = channel_dir.join("src").join("main.rs");
                std::fs::remove_file(main).expect("Could not delete main.rs");
            }

            Self { project_dir }
        }
    }

    impl Backend for TestBackend {
        fn prepare_worker_command(
            &self,
            channel: Channel,
            _id: impl fmt::Display,
        ) -> (Command, TerminateContainer) {
            let channel_dir = self.project_dir.path().join(channel.to_str());

            let mut command = Command::new("./target/debug/worker");
            command.env("RUSTUP_TOOLCHAIN", channel.to_str());
            command.arg(channel_dir);

            (command, TerminateContainer::none())
        }
    }

    static MAX_CONCURRENT_TESTS: LazyLock<usize> = LazyLock::new(|| {
        env::var("TESTS_MAX_CONCURRENCY")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(5)
    });

    static TEST_COORDINATOR_ID_PROVIDER: LazyLock<Arc<limits::Global>> =
        LazyLock::new(|| Arc::new(limits::Global::new(100, *MAX_CONCURRENT_TESTS)));

    static TEST_COORDINATOR_FACTORY: LazyLock<CoordinatorFactory> =
        LazyLock::new(|| CoordinatorFactory::new(TEST_COORDINATOR_ID_PROVIDER.clone()));

    fn new_coordinator_test() -> Coordinator<TestBackend> {
        TEST_COORDINATOR_FACTORY.build()
    }

    fn new_coordinator_docker() -> Coordinator<DockerBackend> {
        TEST_COORDINATOR_FACTORY.build()
    }

    fn new_coordinator() -> Coordinator<impl Backend> {
        #[cfg(not(force_docker))]
        {
            new_coordinator_test()
        }

        #[cfg(force_docker)]
        {
            new_coordinator_docker()
        }
    }

    #[tokio::test]
    #[snafu::report]
    async fn versions() -> Result<()> {
        let coordinator = new_coordinator();

        let versions = coordinator.versions().with_timeout().await.unwrap();

        assert_starts_with!(versions.stable.rustc.release, "1.");

        coordinator.shutdown().await?;

        Ok(())
    }

    const ARBITRARY_EXECUTE_REQUEST: ExecuteRequest = ExecuteRequest {
        channel: Channel::Stable,
        mode: Mode::Debug,
        edition: Edition::Rust2021,
        crate_type: CrateType::Binary,
        tests: false,
        backtrace: false,
        code: String::new(),
    };

    fn new_execute_request() -> ExecuteRequest {
        ExecuteRequest {
            code: r#"fn main() { println!("Hello, coordinator!"); }"#.into(),
            ..ARBITRARY_EXECUTE_REQUEST
        }
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_response() -> Result<()> {
        let coordinator = new_coordinator();

        let response = coordinator
            .execute(new_execute_request())
            .with_timeout()
            .await
            .unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(response.stderr, "Compiling");
        assert_contains!(response.stderr, "Finished");
        assert_contains!(response.stderr, "Running");
        assert_contains!(response.stdout, "Hello, coordinator!");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_mode() -> Result<()> {
        let params = [
            (Mode::Debug, "[unoptimized + debuginfo]"),
            (Mode::Release, "[optimized]"),
        ];

        let tests = params.into_iter().map(async |(mode, expected)| {
            let coordinator = new_coordinator();

            let request = ExecuteRequest {
                mode,
                ..new_execute_request()
            };
            let response = coordinator.execute(request).await.unwrap();

            assert!(response.success, "({mode:?}) stderr: {}", response.stderr);
            assert_contains!(response.stderr, expected);

            coordinator.shutdown().await?;

            Ok::<_, Error>(())
        });

        try_join_all(tests).with_timeout().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_edition() -> Result<()> {
        let params = [
            (r#"fn x() { let dyn = true; }"#, [true, false, false, false]),
            (
                r#"fn x() { u16::try_from(1u8); }"#,
                [false, false, true, true],
            ),
            (r#"fn x() { let gen = true; }"#, [true, true, true, false]),
        ];

        let tests = params.into_iter().flat_map(|(code, works_in)| {
            Edition::ALL
                .into_iter()
                .zip(works_in)
                .map(async |(edition, expected_to_work)| {
                    let coordinator = new_coordinator();

                    let request = ExecuteRequest {
                        code: code.into(),
                        edition,
                        crate_type: CrateType::Library(LibraryType::Lib),
                        ..ARBITRARY_EXECUTE_REQUEST
                    };
                    let response = coordinator.execute(request).await.unwrap();

                    assert_eq!(
                        response.success, expected_to_work,
                        "({edition:?}), stderr: {}",
                        response.stderr,
                    );

                    coordinator.shutdown().await?;

                    Ok::<_, Error>(())
                })
        });

        try_join_all(tests).with_timeout().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_crate_type() -> Result<()> {
        let params = [
            (CrateType::Binary, "Running `target"),
            (
                CrateType::Library(LibraryType::Cdylib),
                "function `main` is never used",
            ),
        ];

        let tests = params.into_iter().map(async |(crate_type, expected)| {
            let coordinator = new_coordinator();

            let request = ExecuteRequest {
                crate_type,
                ..new_execute_request()
            };
            let response = coordinator.execute(request).await.unwrap();

            assert!(
                response.success,
                "({crate_type:?}), stderr: {}",
                response.stderr,
            );
            assert_contains!(response.stderr, expected);

            coordinator.shutdown().await?;

            Ok::<_, Error>(())
        });

        try_join_all(tests).with_timeout().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_tests() -> Result<()> {
        let code = r#"fn main() {} #[test] fn test() {}"#;

        let params = [(false, "Running `"), (true, "Running unittests")];

        let tests = params.into_iter().map(async |(tests, expected)| {
            let coordinator = new_coordinator();

            let request = ExecuteRequest {
                code: code.into(),
                tests,
                ..new_execute_request()
            };
            let response = coordinator.execute(request).await.unwrap();

            assert!(response.success, "({tests:?}), stderr: {}", response.stderr);
            assert_contains!(response.stderr, expected);

            coordinator.shutdown().await?;

            Ok::<_, Error>(())
        });

        try_join_all(tests).with_timeout().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_backtrace() -> Result<()> {
        let code = r#"fn main() { panic!("Disco"); }"#;

        let params = [
            (false, "note: run with `RUST_BACKTRACE=1`"),
            (true, "stack backtrace:"),
        ];

        let tests = params.into_iter().map(async |(backtrace, expected)| {
            let coordinator = new_coordinator();

            let request = ExecuteRequest {
                code: code.into(),
                backtrace,
                ..new_execute_request()
            };
            let response = coordinator.execute(request).await.unwrap();

            assert!(
                !response.success,
                "({backtrace:?}), stderr: {}",
                response.stderr,
            );
            assert_contains!(response.stderr, expected);

            coordinator.shutdown().await?;

            Ok::<_, Error>(())
        });

        try_join_all(tests).with_timeout().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_stdin() -> Result<()> {
        let coordinator = new_coordinator();

        let request = ExecuteRequest {
            code: r#"
                fn main() {
                    let mut input = String::new();
                    if std::io::stdin().read_line(&mut input).is_ok() {
                        println!("You entered >>>{input:?}<<<");
                    }
                }
            "#
            .into(),
            ..ARBITRARY_EXECUTE_REQUEST
        };

        let token = Default::default();
        let ActiveExecution {
            permit: _permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx: _status_rx,
        } = coordinator.begin_execute(token, request).await.unwrap();

        stdin_tx.send("this is stdin\n".into()).await.unwrap();
        // Purposefully not dropping stdin_tx / status_rx early --
        // real users might forget.

        let WithOutput {
            response,
            stdout,
            stderr,
        } = WithOutput::try_absorb(task, stdout_rx, stderr_rx)
            .with_timeout()
            .await
            .unwrap();

        assert!(response.success, "{stderr}");
        assert_contains!(stdout, r#">>>"this is stdin\n"<<<"#);

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_stdin_close() -> Result<()> {
        let coordinator = new_coordinator();

        let request = ExecuteRequest {
            code: r#"
                fn main() {
                    let mut input = String::new();
                    while let Ok(n) = std::io::stdin().read_line(&mut input) {
                        if n == 0 {
                            break;
                        }
                        println!("You entered >>>{input:?}<<<");
                        input.clear();
                    }
                }
            "#
            .into(),
            ..ARBITRARY_EXECUTE_REQUEST
        };

        let token = Default::default();
        let ActiveExecution {
            permit: _permit,
            task,
            stdin_tx,
            stdout_rx,
            stderr_rx,
            status_rx: _,
        } = coordinator.begin_execute(token, request).await.unwrap();

        for i in 0..3 {
            stdin_tx.send(format!("line {i}\n")).await.unwrap();
        }

        stdin_tx.send("no newline".into()).await.unwrap();
        drop(stdin_tx); // Close the stdin handle

        let WithOutput {
            response,
            stdout,
            stderr,
        } = WithOutput::try_absorb(task, stdout_rx, stderr_rx)
            .with_timeout()
            .await
            .unwrap();

        assert!(response.success, "{stderr}");
        assert_contains!(stdout, r#">>>"line 0\n"<<<"#);
        assert_contains!(stdout, r#">>>"line 1\n"<<<"#);
        assert_contains!(stdout, r#">>>"line 2\n"<<<"#);
        assert_contains!(stdout, r#">>>"no newline"<<<"#);

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_kill() -> Result<()> {
        let coordinator = new_coordinator();

        let request = ExecuteRequest {
            code: r#"
                fn main() {
                    println!("Before");
                    loop {
                        std::thread::sleep(std::time::Duration::from_secs(1));
                    }
                    println!("After");
                }
            "#
            .into(),
            ..ARBITRARY_EXECUTE_REQUEST
        };

        let token = CancellationToken::new();
        let ActiveExecution {
            permit: _permit,
            task,
            stdin_tx: _,
            stdout_rx,
            stderr_rx,
            status_rx: _,
        } = coordinator
            .begin_execute(token.clone(), request)
            .await
            .unwrap();

        let stdout_rx = ReceiverStream::new(stdout_rx);
        let stderr_rx = ReceiverStream::new(stderr_rx);

        // We (a) want to wait for some output before we try to
        // kill the process and (b) need to keep pumping stdout /
        // stderr / status to avoid locking up the output.
        let stdout_rx = stdout_rx.inspect(|_| token.cancel());

        let WithOutput {
            response,
            stdout,
            stderr,
        } = WithOutput::try_absorb_stream(task, stdout_rx, stderr_rx)
            .with_timeout()
            .await
            .unwrap();

        assert!(!response.success, "{stderr}");
        assert_contains!(response.exit_detail, "kill");

        assert_contains!(stdout, "Before");
        assert_not_contains!(stdout, "After");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn execute_status() -> Result<()> {
        let coordinator = new_coordinator();

        let request = ExecuteRequest {
            code: r#"
                use std::{time::{Instant, Duration}, thread};

                const MORE_THAN_STATUS_INTERVAL: Duration = Duration::from_millis(1100);

                fn main() {
                    let start = Instant::now();
                    while start.elapsed() < MORE_THAN_STATUS_INTERVAL {
                        // Busy loop
                    }
                    thread::sleep(MORE_THAN_STATUS_INTERVAL);
                }
            "#
            .into(),
            ..ARBITRARY_EXECUTE_REQUEST
        };

        let token = CancellationToken::new();
        let ActiveExecution {
            permit: _permit,
            task,
            stdin_tx: _,
            stdout_rx,
            stderr_rx,
            status_rx,
        } = coordinator
            .begin_execute(token.clone(), request)
            .await
            .unwrap();

        let statuses = status_rx.collect::<Vec<_>>();

        let output = WithOutput::try_absorb(task, stdout_rx, stderr_rx);

        let (statuses, output) = join(statuses, output).with_timeout().await;

        let WithOutput {
            response, stderr, ..
        } = output.unwrap();

        assert!(response.success, "{stderr}");

        let [first, last] = [statuses.first(), statuses.last()].map(|s| s.unwrap().total_time_secs);

        let cpu_time_used = last - first;
        assert!(
            cpu_time_used > 1.0,
            "CPU usage did not increase enough ({first} -> {last})"
        );

        coordinator.shutdown().await?;

        Ok(())
    }

    const HELLO_WORLD_CODE: &str = r#"fn main() { println!("Hello World!"); }"#;

    const ARBITRARY_COMPILE_REQUEST: CompileRequest = CompileRequest {
        target: CompileTarget::Mir,
        channel: Channel::Stable,
        crate_type: CrateType::Binary,
        mode: Mode::Release,
        edition: Edition::Rust2021,
        tests: false,
        backtrace: false,
        code: String::new(),
    };

    #[tokio::test]
    #[snafu::report]
    async fn compile_response() -> Result<()> {
        let coordinator = new_coordinator();

        let req = CompileRequest {
            code: HELLO_WORLD_CODE.into(),
            ..ARBITRARY_COMPILE_REQUEST
        };

        let response = coordinator.compile(req).with_timeout().await.unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(response.stderr, "Compiling");
        assert_contains!(response.stderr, "Finished");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn compile_streaming() -> Result<()> {
        let coordinator = new_coordinator();

        let req = CompileRequest {
            code: HELLO_WORLD_CODE.into(),
            ..ARBITRARY_COMPILE_REQUEST
        };

        let token = Default::default();
        let ActiveCompilation {
            permit: _permit,
            task,
            stdout_rx,
            stderr_rx,
        } = coordinator.begin_compile(token, req).await.unwrap();

        let WithOutput {
            response,
            stdout: _,
            stderr,
        } = WithOutput::try_absorb(task, stdout_rx, stderr_rx)
            .await
            .unwrap();

        assert!(response.success, "stderr: {stderr}");
        assert_contains!(stderr, "Compiling");
        assert_contains!(stderr, "Finished");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn compile_edition() -> Result<()> {
        for edition in Edition::ALL {
            let coordinator = new_coordinator();

            let req = CompileRequest {
                edition,
                code: SUBTRACT_CODE.into(),
                ..ARBITRARY_HIR_REQUEST
            };

            let response = coordinator.compile(req).with_timeout().await.unwrap();

            let prelude = format!("std::prelude::rust_{}", edition.to_str());

            assert!(response.success, "stderr: {}", response.stderr);
            assert_contains!(response.code, &prelude);

            coordinator.shutdown().await?;
        }

        Ok(())
    }

    const ADD_CODE: &str = r#"#[inline(never)] pub fn add(a: u8, b: u8) -> u8 { a + b }"#;

    const ARBITRARY_ASSEMBLY_REQUEST: CompileRequest = CompileRequest {
        target: CompileTarget::Assembly(
            DEFAULT_ASSEMBLY_FLAVOR,
            DEFAULT_ASSEMBLY_DEMANGLE,
            DEFAULT_ASSEMBLY_PROCESS,
        ),
        channel: Channel::Beta,
        crate_type: CrateType::Library(LibraryType::Lib),
        mode: Mode::Release,
        edition: Edition::Rust2018,
        tests: false,
        backtrace: false,
        code: String::new(),
    };

    const DEFAULT_ASSEMBLY_FLAVOR: AssemblyFlavor = AssemblyFlavor::Intel;
    const DEFAULT_ASSEMBLY_DEMANGLE: DemangleAssembly = DemangleAssembly::Demangle;
    const DEFAULT_ASSEMBLY_PROCESS: ProcessAssembly = ProcessAssembly::Filter;

    #[tokio::test]
    #[snafu::report]
    async fn compile_assembly() -> Result<()> {
        let coordinator = new_coordinator();

        let req = CompileRequest {
            code: ADD_CODE.into(),
            ..ARBITRARY_ASSEMBLY_REQUEST
        };

        let response = coordinator.compile(req).with_timeout().await.unwrap();

        let asm = docker_target_arch! {
            x86_64: "eax, [rsi + rdi]",
            aarch64: "w0, w1, w0",
        };

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(response.code, asm);

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    // Assembly flavor only makes sense when targeting x86(_64): this
    // test will always fail on aarch64.
    async fn compile_assembly_flavor() -> Result<()> {
        let cases = [
            (AssemblyFlavor::Att, "(%rsi,%rdi), %eax"),
            (AssemblyFlavor::Intel, "eax, [rsi + rdi]"),
        ];

        for (flavor, expected) in cases {
            let coordinator = new_coordinator();

            let req = CompileRequest {
                target: CompileTarget::Assembly(
                    flavor,
                    DEFAULT_ASSEMBLY_DEMANGLE,
                    DEFAULT_ASSEMBLY_PROCESS,
                ),
                code: ADD_CODE.into(),
                ..ARBITRARY_ASSEMBLY_REQUEST
            };

            let response = coordinator.compile(req).with_timeout().await.unwrap();

            assert!(response.success, "stderr: {}", response.stderr);
            assert_contains!(response.code, expected);

            coordinator.shutdown().await?;
        }

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    // The demangling expects Linux-style symbols, not macOS: this
    // test will always fail on macOS.
    async fn compile_assembly_demangle() -> Result<()> {
        let cases = [
            (DemangleAssembly::Mangle, "10playground3add"),
            (DemangleAssembly::Demangle, "playground::add"),
        ];

        for (mangle, expected) in cases {
            let coordinator = new_coordinator();

            let req = CompileRequest {
                target: CompileTarget::Assembly(
                    DEFAULT_ASSEMBLY_FLAVOR,
                    mangle,
                    DEFAULT_ASSEMBLY_PROCESS,
                ),
                code: ADD_CODE.into(),
                ..ARBITRARY_ASSEMBLY_REQUEST
            };

            let response = coordinator.compile(req).with_timeout().await.unwrap();

            assert!(response.success, "stderr: {}", response.stderr);
            assert_contains!(response.code, expected);

            coordinator.shutdown().await?;
        }

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn compile_assembly_process() -> Result<()> {
        let cases = [
            (ProcessAssembly::Raw, true),
            (ProcessAssembly::Filter, false),
        ];

        for (process, expected) in cases {
            let coordinator = new_coordinator();

            let req = CompileRequest {
                target: CompileTarget::Assembly(
                    DEFAULT_ASSEMBLY_FLAVOR,
                    DEFAULT_ASSEMBLY_DEMANGLE,
                    process,
                ),
                code: ADD_CODE.into(),
                ..ARBITRARY_ASSEMBLY_REQUEST
            };

            let response = coordinator.compile(req).with_timeout().await.unwrap();

            assert!(response.success, "stderr: {}", response.stderr);
            if expected {
                assert_contains!(response.code, ".cfi_startproc");
            } else {
                assert_not_contains!(response.code, ".cfi_startproc");
            }

            coordinator.shutdown().await?;
        }

        Ok(())
    }

    const SUBTRACT_CODE: &str = r#"pub fn sub(a: u8, b: u8) -> u8 { a - b }"#;

    const ARBITRARY_HIR_REQUEST: CompileRequest = CompileRequest {
        target: CompileTarget::Hir,
        channel: Channel::Nightly,
        crate_type: CrateType::Library(LibraryType::Lib),
        mode: Mode::Release,
        edition: Edition::Rust2021,
        tests: false,
        backtrace: false,
        code: String::new(),
    };

    #[tokio::test]
    #[snafu::report]
    async fn compile_hir() -> Result<()> {
        let coordinator = new_coordinator();

        let req = CompileRequest {
            code: SUBTRACT_CODE.into(),
            ..ARBITRARY_HIR_REQUEST
        };

        let response = coordinator.compile(req).with_timeout().await.unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(response.code, "extern crate std");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn compile_llvm_ir() -> Result<()> {
        let coordinator = new_coordinator();

        let req = CompileRequest {
            target: CompileTarget::LlvmIr,
            channel: Channel::Stable,
            crate_type: CrateType::Library(LibraryType::Lib),
            mode: Mode::Debug,
            edition: Edition::Rust2015,
            tests: false,
            backtrace: false,
            code: r#"pub fn mul(a: u8, b: u8) -> u8 { a * b }"#.into(),
        };

        let response = coordinator.compile(req).with_timeout().await.unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(response.code, "@llvm.umul.with.overflow.i8(i8, i8)");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn compile_wasm() -> Result<()> {
        // cargo-wasm only exists inside the container
        let coordinator = new_coordinator_docker();

        let req = CompileRequest {
            target: CompileTarget::Wasm,
            channel: Channel::Nightly,
            crate_type: CrateType::Library(LibraryType::Cdylib),
            mode: Mode::Release,
            edition: Edition::Rust2021,
            tests: false,
            backtrace: false,
            code: r#"#[export_name = "inc"] pub fn inc(a: u8) -> u8 { a + 1 }"#.into(),
        };

        let response = coordinator.compile(req).with_timeout().await.unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(
            response.code,
            r#"(func $inc (;0;) (type 0) (param i32) (result i32)"#
        );

        coordinator.shutdown().await?;

        Ok(())
    }

    const ARBITRARY_FORMAT_REQUEST: FormatRequest = FormatRequest {
        channel: Channel::Stable,
        crate_type: CrateType::Binary,
        edition: Edition::Rust2015,
        code: String::new(),
    };

    const ARBITRARY_FORMAT_INPUT: &str = "fn main(){1+1;}";
    #[rustfmt::skip]
    const ARBITRARY_FORMAT_OUTPUT: &[&str] = &[
        "fn main() {",
        "    1 + 1;",
        "}"
    ];

    #[tokio::test]
    #[snafu::report]
    async fn format() -> Result<()> {
        let coordinator = new_coordinator();

        let req = FormatRequest {
            code: ARBITRARY_FORMAT_INPUT.into(),
            ..ARBITRARY_FORMAT_REQUEST
        };

        let response = coordinator.format(req).with_timeout().await.unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        let lines = response.code.lines().collect::<Vec<_>>();
        assert_eq!(ARBITRARY_FORMAT_OUTPUT, lines);

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn format_channel() -> Result<()> {
        for channel in Channel::ALL {
            let coordinator = new_coordinator();

            let req = FormatRequest {
                channel,
                code: ARBITRARY_FORMAT_INPUT.into(),
                ..ARBITRARY_FORMAT_REQUEST
            };

            let response = coordinator.format(req).with_timeout().await.unwrap();

            assert!(response.success, "stderr: {}", response.stderr);
            let lines = response.code.lines().collect::<Vec<_>>();
            assert_eq!(ARBITRARY_FORMAT_OUTPUT, lines);

            coordinator.shutdown().await?;
        }

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn format_edition() -> Result<()> {
        let cases = [
            ("fn main() { async { 1 } }", [false, true, true, true]),
            ("fn main() { gen { 1 } }", [false, false, false, true]),
        ];

        for (code, works_in) in cases {
            let coordinator = new_coordinator();

            for (edition, works) in Edition::ALL.into_iter().zip(works_in) {
                let req = FormatRequest {
                    edition,
                    code: code.into(),
                    ..ARBITRARY_FORMAT_REQUEST
                };

                let response = coordinator.format(req).with_timeout().await.unwrap();

                assert_eq!(response.success, works, "{code} in {edition:?}");
            }
        }

        Ok(())
    }

    const ARBITRARY_CLIPPY_REQUEST: ClippyRequest = ClippyRequest {
        channel: Channel::Stable,
        crate_type: CrateType::Library(LibraryType::Rlib),
        edition: Edition::Rust2021,
        code: String::new(),
    };

    #[tokio::test]
    #[snafu::report]
    async fn clippy() -> Result<()> {
        let coordinator = new_coordinator();

        let req = ClippyRequest {
            code: r#"
                fn main() {
                    let a = 0.0 / 0.0;
                    println!("NaN is {}", a);
                }
                "#
            .into(),
            ..ARBITRARY_CLIPPY_REQUEST
        };

        let response = coordinator.clippy(req).with_timeout().await.unwrap();

        assert!(!response.success, "stderr: {}", response.stderr);
        assert_contains!(response.stderr, "deny(clippy::eq_op)");
        assert_contains!(response.stderr, "warn(clippy::zero_divided_by_zero)");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn clippy_edition() -> Result<()> {
        let cases = [(
            "#![deny(clippy::single_element_loop)]
              fn a() { for i in [1] { dbg!(i); } }",
            [true, true, false, false],
        )];

        let tests = cases.into_iter().flat_map(|(code, expected_to_be_clean)| {
            Edition::ALL.into_iter().zip(expected_to_be_clean).map(
                move |(edition, expected_to_be_clean)| async move {
                    let coordinator = new_coordinator();

                    let req = ClippyRequest {
                        edition,
                        code: code.into(),
                        ..ARBITRARY_CLIPPY_REQUEST
                    };

                    let response = coordinator.clippy(req).with_timeout().await.unwrap();

                    assert_eq!(
                        response.success, expected_to_be_clean,
                        "{code:?} in {edition:?}, {}",
                        response.stderr
                    );

                    coordinator.shutdown().await?;

                    Ok::<_, Error>(())
                },
            )
        });

        try_join_all(tests).with_timeout().await?;

        Ok(())
    }

    const ARBITRARY_MIRI_REQUEST: MiriRequest = MiriRequest {
        channel: Channel::Nightly,
        crate_type: CrateType::Binary,
        edition: Edition::Rust2021,
        tests: false,
        aliasing_model: AliasingModel::Stacked,
        code: String::new(),
    };

    #[tokio::test]
    #[snafu::report]
    async fn miri() -> Result<()> {
        // We set the `MIRI_SYSROOT` variable to something that's only
        // valid on Linux.
        let coordinator = new_coordinator_docker();

        let req = MiriRequest {
            code: r#"
                fn main() {
                    unsafe { core::mem::MaybeUninit::<u8>::uninit().assume_init() };
                }
                "#
            .into(),
            ..ARBITRARY_MIRI_REQUEST
        };

        let response = coordinator.miri(req).with_timeout().await.unwrap();

        assert!(!response.success, "stderr: {}", response.stderr);

        assert_contains!(response.stderr, "Undefined Behavior");
        assert_contains!(response.stderr, "memory is uninitialized");
        assert_contains!(response.stderr, "operation requires initialized memory");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn miri_tests() -> Result<()> {
        let coordinator = new_coordinator_docker();

        let req = MiriRequest {
            tests: true,
            code: r#"
                #[test]
                fn oops() {
                    unsafe { core::mem::MaybeUninit::<u8>::uninit().assume_init() };
                }
                "#
            .into(),
            ..ARBITRARY_MIRI_REQUEST
        };

        let response = coordinator.miri(req).with_timeout().await.unwrap();

        assert!(!response.success, "stderr: {}", response.stderr);

        assert_contains!(response.stderr, "Undefined Behavior");
        assert_contains!(response.stderr, "memory is uninitialized");
        assert_contains!(response.stderr, "operation requires initialized memory");

        coordinator.shutdown().await?;

        Ok(())
    }

    const ARBITRARY_MACRO_EXPANSION_REQUEST: MacroExpansionRequest = MacroExpansionRequest {
        channel: Channel::Nightly,
        crate_type: CrateType::Library(LibraryType::Cdylib),
        edition: Edition::Rust2018,
        code: String::new(),
    };

    #[tokio::test]
    #[snafu::report]
    async fn macro_expansion() -> Result<()> {
        let coordinator = new_coordinator();

        let req = MacroExpansionRequest {
            code: r#"
                #[derive(Debug)]
                struct Dummy;

                fn main() { println!("Hello!"); }
                "#
            .into(),
            ..ARBITRARY_MACRO_EXPANSION_REQUEST
        };

        let response = coordinator
            .macro_expansion(req)
            .with_timeout()
            .await
            .unwrap();

        assert!(response.success, "stderr: {}", response.stderr);
        assert_contains!(response.stdout, "impl ::core::fmt::Debug for Dummy");
        assert_contains!(response.stdout, "Formatter::write_str");

        coordinator.shutdown().await?;

        Ok(())
    }

    // The next set of tests are broader than the functionality of a
    // single operation.

    #[tokio::test]
    #[snafu::report]
    async fn compile_clears_old_main_rs() -> Result<()> {
        let coordinator = new_coordinator();

        // Create a main.rs file
        let req = ExecuteRequest {
            channel: Channel::Stable,
            crate_type: CrateType::Binary,
            mode: Mode::Debug,
            edition: Edition::Rust2021,
            tests: false,
            backtrace: false,
            code: "pub fn alpha() {}".into(),
        };

        let response = coordinator
            .execute(req.clone())
            .with_timeout()
            .await
            .unwrap();
        assert!(!response.success, "stderr: {}", response.stderr);
        assert_contains!(response.stderr, "`main` function not found");

        // Create a lib.rs file
        let req = CompileRequest {
            target: CompileTarget::LlvmIr,
            channel: req.channel,
            mode: req.mode,
            edition: req.edition,
            crate_type: CrateType::Library(LibraryType::Rlib),
            tests: req.tests,
            backtrace: req.backtrace,
            code: "pub fn beta() {}".into(),
        };

        let response = coordinator
            .compile(req.clone())
            .with_timeout()
            .await
            .unwrap();
        assert!(response.success, "stderr: {}", response.stderr);

        assert_not_contains!(response.code, "alpha");
        assert_contains!(response.code, "beta");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn still_usable_after_idle() -> Result<()> {
        let mut coordinator = new_coordinator();

        let req = ExecuteRequest {
            channel: Channel::Stable,
            mode: Mode::Debug,
            edition: Edition::Rust2021,
            crate_type: CrateType::Binary,
            tests: false,
            backtrace: false,
            code: r#"fn main() { println!("hello") }"#.into(),
        };

        let res = coordinator.execute(req.clone()).await.unwrap();
        assert_eq!(res.stdout, "hello\n");

        coordinator.idle().await.unwrap();

        let res = coordinator.execute(req).await.unwrap();
        assert_eq!(res.stdout, "hello\n");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn exit_due_to_signal_is_reported() -> Result<()> {
        let coordinator = new_coordinator();

        let req = ExecuteRequest {
            channel: Channel::Stable,
            mode: Mode::Release,
            edition: Edition::Rust2021,
            crate_type: CrateType::Binary,
            tests: false,
            backtrace: false,
            code: r#"fn main() { std::process::abort(); }"#.into(),
        };

        let res = coordinator.execute(req.clone()).await.unwrap();

        assert!(!res.success);
        assert_contains!(res.exit_detail, "abort");

        coordinator.shutdown().await?;

        Ok(())
    }

    fn new_execution_limited_request() -> ExecuteRequest {
        ExecuteRequest {
            channel: Channel::Stable,
            mode: Mode::Debug,
            edition: Edition::Rust2021,
            crate_type: CrateType::Binary,
            tests: false,
            backtrace: false,
            code: Default::default(),
            execution_tool: ExecutionTool::Cargo,
        }
    }

    #[tokio::test]
    #[snafu::report]
    async fn network_connections_are_disabled() -> Result<()> {
        // The limits are only applied to the container
        let coordinator = new_coordinator_docker();

        let req = ExecuteRequest {
            code: r#"
                fn main() {
                    match ::std::net::TcpStream::connect("google.com:80") {
                        Ok(_) => println!("Able to connect to the outside world"),
                        Err(e) => println!("Failed to connect {}, {:?}", e, e),
                    }
                }
            "#
            .into(),
            ..new_execution_limited_request()
        };

        let res = coordinator.execute(req).with_timeout().await.unwrap();

        assert_contains!(res.stdout, "Failed to connect");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn memory_usage_is_limited() -> Result<()> {
        // The limits are only applied to the container
        let coordinator = new_coordinator_docker();

        let req = ExecuteRequest {
            code: r#"
                fn main() {
                    let gigabyte = 1024 * 1024 * 1024;
                    let mut big = vec![0u8; 1 * gigabyte];
                    for i in &mut big { *i += 1; }
                }
            "#
            .into(),
            ..new_execution_limited_request()
        };

        let res = coordinator.execute(req).with_timeout().await.unwrap();

        assert!(!res.success);
        // TODO: We need to actually inform the user about this somehow. The UI is blank.
        // assert_contains!(res.stdout, "Killed");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn number_of_pids_is_limited() -> Result<()> {
        // The limits are only applied to the container
        let coordinator = new_coordinator_docker();

        let req = ExecuteRequest {
            code: r##"
                fn main() {
                    ::std::process::Command::new("sh").arg("-c").arg(r#"
                        z() {
                            z&
                            z
                        }
                        z
                    "#).status().unwrap();
                }
            "##
            .into(),
            ..new_execution_limited_request()
        };

        let res = coordinator.execute(req).with_timeout().await.unwrap();

        assert_contains!(res.stderr, "Cannot fork");

        coordinator.shutdown().await?;

        Ok(())
    }

    #[tokio::test]
    #[snafu::report]
    async fn amount_of_output_is_limited() -> Result<()> {
        // The limits are only applied to the container
        let coordinator = new_coordinator_docker();

        let req = ExecuteRequest {
            code: r##"
                use std::io::Write;

                fn main() {
                    let a = "a".repeat(1024);
                    let out = std::io::stdout();
                    let mut out = out.lock();
                    loop {//for _ in 0..1_000_000 {
                        let _ = out.write_all(a.as_bytes());
                        let _ = out.write_all(b"\n");
                    }
                }
            "##
            .into(),
            ..new_execution_limited_request()
        };

        let err = coordinator.execute(req).with_timeout().await.unwrap_err();
        let err = snafu::ChainCompat::new(&err).last().unwrap();
        assert_contains!(err.to_string(), "bytes of output, exiting");

        coordinator.shutdown().await?;

        Ok(())
    }

    static TIMEOUT: LazyLock<Duration> = LazyLock::new(|| {
        let millis = env::var("TESTS_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(5000);
        Duration::from_millis(millis)
    });

    trait TimeoutExt: Future + Sized {
        async fn with_timeout(self) -> Self::Output {
            tokio::time::timeout(*TIMEOUT, self)
                .await
                .expect("The operation timed out")
        }
    }

    impl<F: Future> TimeoutExt for F {}
}
