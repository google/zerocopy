use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, VecDeque},
    fmt,
};

pub type JobId = u64;
pub type Path = String;

macro_rules! impl_narrow_to_broad {
    ($enum_type:ident, $($variant_name:ident => $variant_type:ident),* $(,)?) => {
        $(
            impl From<$variant_type> for $enum_type {
                fn from(other: $variant_type) -> Self {
                    $enum_type::$variant_name(other)
                }
            }
        )*
    };
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Multiplexed<T>(pub JobId, pub T);

#[derive(Debug, Serialize, Deserialize, strum_macros::AsRefStr)]
pub enum CoordinatorMessage {
    WriteFile(WriteFileRequest),
    DeleteFile(DeleteFileRequest),
    ReadFile(ReadFileRequest),
    ExecuteCommand(ExecuteCommandRequest),
    StdinPacket(String),
    StdinClose,
    Kill,
}

impl_narrow_to_broad!(
    CoordinatorMessage,
    WriteFile => WriteFileRequest,
    DeleteFile => DeleteFileRequest,
    ReadFile => ReadFileRequest,
    ExecuteCommand => ExecuteCommandRequest,
);

#[derive(Debug, Serialize, Deserialize, strum_macros::AsRefStr)]
pub enum WorkerMessage {
    WriteFile(WriteFileResponse),
    DeleteFile(DeleteFileResponse),
    ReadFile(ReadFileResponse),
    ExecuteCommand(ExecuteCommandResponse),
    StdoutPacket(String),
    StderrPacket(String),
    CommandStatistics(CommandStatistics),
    /// Vestigial; remove after a while
    Error(SerializedError),
    Error2(SerializedError2),
}

macro_rules! impl_broad_to_narrow_with_error {
    ($enum_type:ident, $($variant_name:ident => $variant_type:ty),* $(,)?) => {
        $(
            impl TryFrom<$enum_type> for Result<$variant_type, SerializedError2> {
                type Error = $enum_type;

                fn try_from(other: $enum_type) -> Result<Self, Self::Error> {
                    match other {
                        $enum_type::$variant_name(x) => Ok(Ok(x)),
                        $enum_type::Error(e) => Ok(Err(SerializedError2::adapt(e))),
                        $enum_type::Error2(e) => Ok(Err(e)),
                        o => Err(o)
                    }
                }
            }
        )*
    };
}

impl_narrow_to_broad!(
    WorkerMessage,
    WriteFile => WriteFileResponse,
    DeleteFile => DeleteFileResponse,
    ReadFile => ReadFileResponse,
    ExecuteCommand => ExecuteCommandResponse,
    CommandStatistics => CommandStatistics,
);

impl_broad_to_narrow_with_error!(
    WorkerMessage,
    WriteFile => WriteFileResponse,
    DeleteFile => DeleteFileResponse,
    ReadFile => ReadFileResponse,
    ExecuteCommand => ExecuteCommandResponse,
);

#[derive(Debug, Serialize, Deserialize)]
pub struct WriteFileRequest {
    pub path: Path,
    pub content: Vec<u8>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct WriteFileResponse(pub ());

#[derive(Debug, Serialize, Deserialize)]
pub struct DeleteFileRequest {
    pub path: Path,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DeleteFileResponse(pub ());

#[derive(Debug, Serialize, Deserialize)]
pub struct ReadFileRequest {
    pub path: Path,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ReadFileResponse(pub Vec<u8>);

#[derive(Debug, Serialize, Deserialize)]
pub struct ExecuteCommandRequest {
    pub cmd: String,
    pub args: Vec<String>,
    pub envs: HashMap<String, String>,
    pub cwd: Option<String>, // None means in project direcotry.
}

impl ExecuteCommandRequest {
    pub fn simple(
        cmd: impl Into<String>,
        args: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self {
            cmd: cmd.into(),
            args: args.into_iter().map(Into::into).collect(),
            envs: Default::default(),
            cwd: None,
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ExecuteCommandResponse {
    pub success: bool,
    pub exit_detail: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CommandStatistics {
    pub total_time_secs: f64,
    pub resident_set_size_bytes: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SerializedError(pub String);

impl SerializedError {
    pub fn new(e: impl snafu::Error) -> Self {
        Self(snafu::Report::from_error(e).to_string())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SerializedError2 {
    pub message: String,
    pub source: Option<Box<Self>>,
}

impl SerializedError2 {
    pub fn new(e: impl snafu::Error) -> Self {
        let mut messages = snafu::CleanedErrorText::new(&e)
            .map(|(_, t, _)| t)
            .filter(|t| !t.is_empty())
            .collect::<VecDeque<_>>();

        let message = messages
            .pop_front()
            .unwrap_or_else(|| "No error message".into());
        let source = messages.into_iter().rev().fold(None, |source, message| {
            Some(Box::new(Self { source, message }))
        });

        Self { message, source }
    }

    pub fn adapt(other: SerializedError) -> Self {
        Self {
            message: other.0,
            source: None,
        }
    }
}

impl snafu::Error for SerializedError2 {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.as_ref().map(|x| &**x as &dyn snafu::Error)
    }
}

impl fmt::Display for SerializedError2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.message.fmt(f)
    }
}

pub trait OneToOneResponse {
    type Response;
}

impl OneToOneResponse for WriteFileRequest {
    type Response = WriteFileResponse;
}

impl OneToOneResponse for DeleteFileRequest {
    type Response = DeleteFileResponse;
}

impl OneToOneResponse for ReadFileRequest {
    type Response = ReadFileResponse;
}

impl OneToOneResponse for ExecuteCommandRequest {
    type Response = ExecuteCommandResponse;
}
