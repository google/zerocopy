use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ErrorJson {
    pub(crate) error: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CompileRequest {
    pub(crate) target: String,
    #[serde(rename = "assemblyFlavor")]
    pub(crate) assembly_flavor: Option<String>,
    #[serde(rename = "demangleAssembly")]
    pub(crate) demangle_assembly: Option<String>,
    #[serde(rename = "processAssembly")]
    pub(crate) process_assembly: Option<String>,
    pub(crate) channel: String,
    pub(crate) mode: String,
    #[serde(default)]
    pub(crate) edition: String,
    #[serde(rename = "crateType")]
    pub(crate) crate_type: String,
    pub(crate) tests: bool,
    #[serde(default)]
    pub(crate) backtrace: bool,
    pub(crate) code: String,
}

pub(crate) fn default_execution_tool() -> String {
    "cargo".to_owned()
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct CompileResponse {
    pub(crate) success: bool,
    #[serde(rename = "exitDetail")]
    pub(crate) exit_detail: String,
    pub(crate) code: String,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ExecuteRequest {
    pub(crate) channel: String,
    pub(crate) mode: String,
    #[serde(default)]
    pub(crate) edition: String,
    #[serde(rename = "crateType")]
    pub(crate) crate_type: String,
    pub(crate) tests: bool,
    #[serde(default)]
    pub(crate) backtrace: bool,
    pub(crate) code: String,
    #[serde(default = "default_execution_tool", rename = "executionTool")]
    pub(crate) execution_tool: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ExecuteResponse {
    pub(crate) success: bool,
    #[serde(rename = "exitDetail")]
    pub(crate) exit_detail: String,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct FormatRequest {
    #[serde(default)]
    pub(crate) channel: Option<String>,
    #[serde(default)]
    pub(crate) edition: String,
    pub(crate) code: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct FormatResponse {
    pub(crate) success: bool,
    #[serde(rename = "exitDetail")]
    pub(crate) exit_detail: String,
    pub(crate) code: String,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct ClippyRequest {
    #[serde(default)]
    pub(crate) channel: Option<String>,
    #[serde(default = "default_crate_type", rename = "crateType")]
    pub(crate) crate_type: String,
    #[serde(default)]
    pub(crate) edition: String,
    pub(crate) code: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ClippyResponse {
    pub(crate) success: bool,
    pub(crate) exit_detail: String,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct MiriRequest {
    pub(crate) code: String,
    #[serde(default)]
    pub(crate) edition: String,
    #[serde(default)]
    pub(crate) tests: bool,
    #[serde(default, rename = "aliasingModel")]
    pub(crate) aliasing_model: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct MiriResponse {
    pub(crate) success: bool,
    pub(crate) exit_detail: String,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct MacroExpansionRequest {
    pub(crate) code: String,
    #[serde(default)]
    pub(crate) edition: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct MacroExpansionResponse {
    pub(crate) success: bool,
    pub(crate) exit_detail: String,
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct CrateInformation {
    pub(crate) name: String,
    pub(crate) version: String,
    pub(crate) id: String,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MetaCratesResponse {
    pub(crate) crates: Arc<[CrateInformation]>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MetaVersionsResponse {
    pub(crate) stable: MetaChannelVersionResponse,
    pub(crate) beta: MetaChannelVersionResponse,
    pub(crate) nightly: MetaChannelVersionResponse,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MetaChannelVersionResponse {
    pub(crate) rustc: MetaVersionResponse,
    pub(crate) rustfmt: MetaVersionResponse,
    pub(crate) clippy: MetaVersionResponse,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) miri: Option<MetaVersionResponse>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MetaVersionResponse {
    pub(crate) version: Arc<str>,
    pub(crate) hash: Arc<str>,
    pub(crate) date: Arc<str>,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct MetaGistCreateRequest {
    pub(crate) code: String,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct MetaGistResponse {
    pub(crate) id: String,
    pub(crate) url: String,
    pub(crate) code: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct EvaluateRequest {
    pub(crate) version: String,
    pub(crate) optimize: String,
    pub(crate) code: String,
    #[serde(default)]
    pub(crate) edition: String,
    #[serde(default)]
    pub(crate) tests: bool,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct EvaluateResponse {
    pub(crate) result: String,
    pub(crate) error: Option<String>,
}

fn default_crate_type() -> String {
    "bin".into()
}
