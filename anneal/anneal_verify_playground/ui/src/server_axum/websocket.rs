use crate::public_http_api::default_execution_tool;
use crate::{
    metrics::{self, record_metric, Endpoint, HasLabelsCore, Outcome},
    request_database::Handle,
    server_axum::api_orchestrator_integration_impls::*,
    WebSocketConfig,
};

use axum::extract::ws::{Message, WebSocket};
use futures::{future::Fuse, Future, FutureExt, StreamExt, TryFutureExt};
use orchestrator::{
    coordinator::{self, Coordinator, CoordinatorFactory, DockerBackend},
    DropErrorDetailsExt,
};
use snafu::prelude::*;
use std::{
    collections::BTreeMap,
    convert::TryFrom,
    pin::pin,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};
use tokio::{
    sync::{mpsc, Semaphore},
    task::{AbortHandle, JoinSet},
    time,
};
use tokio_util::{
    sync::{CancellationToken, DropGuard},
    time::FutureExt as _,
};
use tracing::{error, info, instrument, warn, Instrument};

#[derive(Debug, serde::Deserialize, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct MetaInner {
    sequence_number: i64,
}

type Meta = Arc<MetaInner>;

#[derive(serde::Deserialize)]
#[serde(tag = "type")]
enum HandshakeMessage {
    #[serde(rename = "websocket/connected")]
    Connected {
        payload: Connected,
        #[allow(unused)]
        meta: Meta,
    },
}

#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct Connected {
    i_accept_this_is_an_unsupported_api: bool,
}

#[derive(serde::Deserialize)]
#[serde(tag = "type")]
enum WSMessageRequest {
    #[serde(rename = "output/execute/wsExecuteRequest")]
    ExecuteRequest { payload: ExecuteRequest, meta: Meta },

    #[serde(rename = "output/execute/wsExecuteStdin")]
    ExecuteStdin { payload: String, meta: Meta },

    #[serde(rename = "output/execute/wsExecuteStdinClose")]
    ExecuteStdinClose { meta: Meta },

    #[serde(rename = "output/execute/wsExecuteKill")]
    ExecuteKill { meta: Meta },
}

#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase")]
struct ExecuteRequest {
    channel: String,
    mode: String,
    edition: String,
    crate_type: String,
    tests: bool,
    code: String,
    backtrace: bool,
    #[serde(default = "default_execution_tool")]
    execution_tool: String,
}

impl TryFrom<ExecuteRequest> for coordinator::ExecuteRequest {
    type Error = ExecuteRequestParseError;

    fn try_from(value: ExecuteRequest) -> Result<Self, Self::Error> {
        let ExecuteRequest {
            channel,
            mode,
            edition,
            crate_type,
            tests,
            code,
            backtrace,
            execution_tool,
        } = value;

        Ok(coordinator::ExecuteRequest {
            channel: parse_channel(&channel)?,
            mode: parse_mode(&mode)?,
            edition: parse_edition(&edition)?,
            crate_type: parse_crate_type(&crate_type)?,
            tests,
            backtrace,
            code,
            execution_tool: parse_execution_tool(&execution_tool)?,
        })
    }
}

#[derive(Debug, Snafu)]
pub(crate) enum ExecuteRequestParseError {
    #[snafu(transparent)]
    Channel { source: ParseChannelError },

    #[snafu(transparent)]
    CrateType { source: ParseCrateTypeError },

    #[snafu(transparent)]
    Mode { source: ParseModeError },

    #[snafu(transparent)]
    Edition { source: ParseEditionError },

    #[snafu(transparent)]
    ExecutionTool { source: ParseExecutionToolError },
}

#[derive(Debug, serde::Serialize)]
#[serde(tag = "type")]
enum MessageResponse {
    #[serde(rename = "websocket/error")]
    Error { payload: WSError, meta: Meta },

    #[serde(rename = "featureFlags")]
    FeatureFlags { payload: FeatureFlags, meta: Meta },

    #[serde(rename = "output/execute/wsExecuteBegin")]
    ExecuteBegin { meta: Meta },

    #[serde(rename = "output/execute/wsExecuteStdout")]
    ExecuteStdout { payload: String, meta: Meta },

    #[serde(rename = "output/execute/wsExecuteStderr")]
    ExecuteStderr { payload: String, meta: Meta },

    #[serde(rename = "output/execute/wsExecuteStatus")]
    ExecuteStatus { payload: ExecuteStatus, meta: Meta },

    #[serde(rename = "output/execute/wsExecuteEnd")]
    ExecuteEnd {
        payload: ExecuteResponse,
        meta: Meta,
    },
}

#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct WSError {
    error: String,
}

#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct FeatureFlags {}

impl From<crate::FeatureFlags> for FeatureFlags {
    fn from(_value: crate::FeatureFlags) -> Self {
        Self {}
    }
}

#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ExecuteStatus {
    resident_set_size_bytes: u64,
    total_time_secs: f64,
}

impl From<orchestrator::coordinator::ExecuteStatus> for ExecuteStatus {
    fn from(value: orchestrator::coordinator::ExecuteStatus) -> Self {
        let coordinator::ExecuteStatus {
            resident_set_size_bytes,
            total_time_secs,
        } = value;

        Self {
            resident_set_size_bytes,
            total_time_secs,
        }
    }
}

#[derive(Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct ExecuteResponse {
    success: bool,
    exit_detail: String,
}

#[instrument(skip_all, fields(ws_id))]
pub(crate) async fn handle(
    socket: WebSocket,
    config: WebSocketConfig,
    factory: Arc<CoordinatorFactory>,
    feature_flags: FeatureFlags,
    db: Handle,
) {
    struct MetricGuard {
        clean: bool,
        start: Instant,
    }

    impl MetricGuard {
        fn new() -> Self {
            static WEBSOCKET_ID: AtomicU64 = AtomicU64::new(0);

            metrics::LIVE_WS.inc();
            let start = Instant::now();

            let id = WEBSOCKET_ID.fetch_add(1, Ordering::SeqCst);
            tracing::Span::current().record("ws_id", id);
            info!("WebSocket started");

            Self {
                clean: false,
                start,
            }
        }
    }

    impl Drop for MetricGuard {
        fn drop(&mut self) {
            info!(clean = self.clean, "WebSocket ending");
            metrics::LIVE_WS.dec();
            let elapsed = self.start.elapsed();
            metrics::DURATION_WS.observe(elapsed.as_secs_f64());
        }
    }

    let mut mg = MetricGuard::new();

    let hc = handle_core(socket, config, factory, feature_flags, db)
        .timeout(config.overall_timeout())
        .await;

    if hc.is_err() {
        error!("`handle_core` exceeded the overall timeout");
    }

    mg.clean = true;
}

type TaggedError = (Error, Option<Meta>);
type ResponseTx = mpsc::Sender<Result<MessageResponse, TaggedError>>;
type SharedCoordinator = Arc<Coordinator<DockerBackend>>;

/// Manages a limited amount of access to the `Coordinator`.
///
/// Has a number of responsibilities:
///
/// - Constructs the `Coordinator` on demand.
///
/// - Only allows one job of a certain kind at a time (e.g. executing
///   vs formatting). Older jobs will be cancelled.
///
/// - Allows limited parallelism between jobs of different types.
struct CoordinatorManager {
    coordinator: SharedCoordinator,
    tasks: JoinSet<Result<(), TaggedError>>,
    semaphore: Arc<Semaphore>,
    abort_handles: [Option<AbortHandle>; Self::N_KINDS],
}

impl CoordinatorManager {
    const N_PARALLEL: usize = 2;

    const N_KINDS: usize = 1;
    const KIND_EXECUTE: usize = 0;

    fn new(factory: &CoordinatorFactory) -> Self {
        Self {
            coordinator: Arc::new(factory.build()),
            tasks: Default::default(),
            semaphore: Arc::new(Semaphore::new(Self::N_PARALLEL)),
            abort_handles: Default::default(),
        }
    }

    fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    async fn join_next(
        &mut self,
    ) -> Option<Result<Result<(), TaggedError>, tokio::task::JoinError>> {
        self.tasks.join_next().await
    }

    async fn spawn<F, Fut>(&mut self, handler: F) -> CoordinatorManagerResult<()>
    where
        F: FnOnce(SharedCoordinator) -> Fut,
        F: 'static + Send,
        Fut: Future<Output = Result<(), TaggedError>>,
        Fut: 'static + Send,
    {
        let coordinator = self.coordinator.clone();
        let semaphore = self.semaphore.clone();

        let new_abort_handle = self.tasks.spawn(
            async move {
                let _permit = semaphore.acquire().await;
                handler(coordinator).await
            }
            .in_current_span(),
        );

        let kind = Self::KIND_EXECUTE; // TODO: parameterize when we get a second kind
        let old_abort_handle = self.abort_handles[kind].replace(new_abort_handle);

        if let Some(abort_handle) = old_abort_handle {
            abort_handle.abort();
        }

        Ok(())
    }

    async fn idle(&mut self) -> CoordinatorManagerResult<()> {
        use coordinator_manager_error::*;

        Arc::get_mut(&mut self.coordinator)
            .context(OutstandingCoordinatorIdleSnafu)?
            .idle()
            .await
            .context(IdleSnafu)?;

        Ok(())
    }

    async fn shutdown(mut self) -> CoordinatorManagerResult<()> {
        use coordinator_manager_error::*;

        self.tasks.shutdown().await;
        Arc::into_inner(self.coordinator)
            .context(OutstandingCoordinatorShutdownSnafu)?
            .shutdown()
            .await
            .context(ShutdownSnafu)?;

        Ok(())
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum CoordinatorManagerError {
    #[snafu(display("The coordinator is still referenced and cannot be idled"))]
    OutstandingCoordinatorIdle,

    #[snafu(display("Could not idle the coordinator"))]
    Idle { source: coordinator::Error },

    #[snafu(display("The coordinator is still referenced and cannot be shut down"))]
    OutstandingCoordinatorShutdown,

    #[snafu(display("Could not shut down the coordinator"))]
    Shutdown { source: coordinator::Error },
}

type CoordinatorManagerResult<T, E = CoordinatorManagerError> = std::result::Result<T, E>;

async fn handle_core(
    mut socket: WebSocket,
    config: WebSocketConfig,
    factory: Arc<CoordinatorFactory>,
    feature_flags: FeatureFlags,
    db: Handle,
) {
    let accepted_handshake = connect_handshake(&mut socket)
        .timeout(config.handshake_timeout)
        .await
        .unwrap_or(false);

    if !accepted_handshake {
        return;
    }

    let (tx, mut rx) = mpsc::channel(3);

    let ff = MessageResponse::FeatureFlags {
        payload: feature_flags,
        meta: create_server_meta(),
    };

    if tx.send(Ok(ff)).await.is_err() {
        return;
    }

    let mut manager = CoordinatorManager::new(&factory);
    let mut session_timeout = pin!(time::sleep(config.session_timeout));
    let mut idle_timeout = pin!(Fuse::terminated());

    let mut active_executions = BTreeMap::new();
    let mut active_execution_gc_interval = time::interval(Duration::from_secs(30));

    loop {
        use Event::*;

        enum Event {
            Request(Option<Result<Message, axum::Error>>),
            Response(Option<Result<MessageResponse, TaggedError>>),
            Task(Result<Result<(), TaggedError>, tokio::task::JoinError>),
            GarbageCollection,
            IdleTimeout,
            IdleRequest,
            SessionTimeout,
        }

        let event = tokio::select! {
            request = socket.recv() => Request(request),

            resp = rx.recv() => Response(resp),

            // We don't care if there are no running tasks
            Some(task) = manager.join_next() => Task(task),

            _ = active_execution_gc_interval.tick() => GarbageCollection,

            _ = &mut idle_timeout, if manager.is_empty() => IdleTimeout,

            _ = factory.container_requested(), if manager.is_empty() => IdleRequest,

            _ = &mut session_timeout => SessionTimeout,
        };

        match event {
            Request(request) => {
                metrics::WS_INCOMING.inc();

                match request {
                    // browser disconnected
                    None => break,

                    Some(Ok(Message::Text(txt))) => {
                        handle_msg(&txt, &tx, &mut manager, &mut active_executions, &db).await
                    }

                    // unknown message type
                    Some(Ok(_)) => continue,

                    Some(Err(e)) => super::record_websocket_error(e.to_string()),
                }
            }

            Response(resp) => {
                let resp = resp.expect("The rx should never close as we have a tx");

                let success = resp.is_ok();
                let resp = resp.unwrap_or_else(error_to_response);
                let resp = response_to_message(resp);

                if socket.send(resp).await.is_err() {
                    // We can't send a response
                    break;
                }

                let success = if success { "true" } else { "false" };
                metrics::WS_OUTGOING.with_label_values(&[success]).inc();
            }

            Task(task) => {
                // The last task has completed which means we are a
                // candidate for idling in a little while.
                if manager.is_empty() {
                    idle_timeout.set(time::sleep(config.idle_timeout).fuse());
                }

                let (error, meta) = match task {
                    Ok(Ok(())) => continue,

                    Ok(Err(error)) => error,

                    Err(error) => {
                        // The task was cancelled; no need to report
                        let Ok(panic) = error.try_into_panic() else {
                            continue;
                        };

                        let text = match panic.downcast::<String>() {
                            Ok(text) => *text,
                            Err(panic) => match panic.downcast::<&str>() {
                                Ok(text) => text.to_string(),
                                _ => "An unknown panic occurred".into(),
                            },
                        };
                        (WebSocketTaskPanicSnafu { text }.build(), None)
                    }
                };

                if tx.send(Err((error, meta))).await.is_err() {
                    // We can't send a response
                    break;
                }
            }

            GarbageCollection => {
                active_executions
                    .retain(|_id, (_, tx)| tx.as_ref().is_some_and(|tx| !tx.is_closed()));
            }

            IdleTimeout | IdleRequest => {
                if matches!(event, IdleRequest) {
                    info!("Container requested to idle");
                }

                match manager.idle().timeout(config.idle_shutdown_timeout).await {
                    Ok(idled) => {
                        let idled = idled.context(StreamingCoordinatorIdleSnafu);
                        let Err(error) = idled else { continue };

                        if tx.send(Err((error, None))).await.is_err() {
                            // We can't send a response
                            break;
                        }
                    }

                    Err(_) => {
                        error!("Timed out idling the Coordinator");
                        break;
                    }
                }
            }

            SessionTimeout => break,
        }
    }

    drop((tx, rx, socket));
    let shutdown = manager.shutdown().timeout(config.shutdown_timeout).await;

    match shutdown {
        Ok(Ok(())) => {}
        Ok(Err(e)) => error!("Could not shut down the Coordinator: {e:?}"),
        Err(_) => error!("Timed out shutting down the Coordinator"),
    }
}

async fn connect_handshake(socket: &mut WebSocket) -> bool {
    let Some(Ok(Message::Text(txt))) = socket.recv().await else {
        return false;
    };
    let Ok(HandshakeMessage::Connected { payload, .. }) = serde_json::from_str(&txt) else {
        return false;
    };
    if !payload.i_accept_this_is_an_unsupported_api {
        return false;
    }
    socket.send(Message::Text(txt)).await.is_ok()
}

fn create_server_meta() -> Meta {
    Arc::new(MetaInner {
        sequence_number: -1,
    })
}

fn error_to_response((error, meta): TaggedError) -> MessageResponse {
    let error = snafu::CleanedErrorText::new(&error)
        .map(|(_, t, _)| t)
        .reduce(|e, t| e + ": " + &t)
        .unwrap_or_default();
    let payload = WSError { error };

    let meta = meta.unwrap_or_else(create_server_meta);

    MessageResponse::Error { payload, meta }
}

fn response_to_message(response: MessageResponse) -> Message {
    const LAST_CHANCE_ERROR: &str =
        r#"{ "type": "WEBSOCKET_ERROR", "error": "Unable to serialize JSON" }"#;
    let resp = serde_json::to_string(&response).unwrap_or_else(|_| LAST_CHANCE_ERROR.into());
    Message::Text(resp.into())
}

type ActiveExecutionInfo = (DropGuard, Option<mpsc::Sender<String>>);

async fn handle_msg(
    txt: &str,
    tx: &ResponseTx,
    manager: &mut CoordinatorManager,
    active_executions: &mut BTreeMap<i64, ActiveExecutionInfo>,
    db: &Handle,
) {
    use WSMessageRequest::*;

    let msg = serde_json::from_str(txt).context(DeserializationSnafu);

    match msg {
        Ok(ExecuteRequest { payload, meta }) => {
            let token = CancellationToken::new();
            let (execution_tx, execution_rx) = mpsc::channel(8);

            let guard = db.clone().start_with_guard("ws.Execute", txt).await;

            active_executions.insert(
                meta.sequence_number,
                (token.clone().drop_guard(), Some(execution_tx)),
            );

            // TODO: Should a single execute / build / etc. session have a timeout of some kind?
            let spawned = manager
                .spawn({
                    let tx = tx.clone();
                    let meta = meta.clone();
                    async |coordinator| {
                        let r = handle_execute(
                            token,
                            execution_rx,
                            tx,
                            coordinator,
                            payload,
                            meta.clone(),
                        )
                        .context(StreamingExecuteSnafu)
                        .map_err(|e| (e, Some(meta)))
                        .await;

                        guard.complete_now(r)
                    }
                })
                .await
                .context(StreamingCoordinatorSpawnSnafu);

            if let Err(e) = spawned {
                tx.send(Err((e, Some(meta)))).await.ok(/* We don't care if the channel is closed */);
            }
        }

        Ok(ExecuteStdin { payload, meta }) => {
            let Some((_, Some(execution_tx))) = active_executions.get(&meta.sequence_number) else {
                warn!("Received stdin for an execution that is no longer active");
                return;
            };
            let sent = execution_tx
                .send(payload)
                .await
                .drop_error_details()
                .context(StreamingCoordinatorExecuteStdinSnafu);

            if let Err(e) = sent {
                tx.send(Err((e, Some(meta)))).await.ok(/* We don't care if the channel is closed */);
            }
        }

        Ok(ExecuteStdinClose { meta }) => {
            let Some((_, execution_tx)) = active_executions.get_mut(&meta.sequence_number) else {
                warn!("Received stdin close for an execution that is no longer active");
                return;
            };

            *execution_tx = None; // Drop to signal closed
        }

        Ok(ExecuteKill { meta }) => {
            let Some((token, _)) = active_executions.remove(&meta.sequence_number) else {
                warn!("Received kill for an execution that is no longer active");
                return;
            };
            drop(token);
        }

        Err(e) => {
            tx.send(Err((e, None))).await.ok(/* We don't care if the channel is closed */);
        }
    }
}

#[derive(Debug)]
enum CompletedOrAbandoned<T> {
    Abandoned,
    Completed(T),
}

macro_rules! abandon_if_closed {
    ($sent:expr) => {
        if $sent.is_err() {
            return Ok(CompletedOrAbandoned::Abandoned);
        }
    };
}

async fn handle_execute(
    token: CancellationToken,
    rx: mpsc::Receiver<String>,
    tx: ResponseTx,
    coordinator: SharedCoordinator,
    req: ExecuteRequest,
    meta: Meta,
) -> ExecuteResult<()> {
    use execute_error::*;
    use CompletedOrAbandoned::*;

    let req = coordinator::ExecuteRequest::try_from(req).context(BadRequestSnafu)?;

    let labels_core = req.labels_core();

    let start = Instant::now();
    let v = handle_execute_inner(token, rx, tx, coordinator, req, meta).await;
    let elapsed = start.elapsed();

    let outcome = match &v {
        Ok(Abandoned) => Outcome::Abandoned,
        Ok(Completed(v)) => *v,
        Err(_) => Outcome::ErrorServer,
    };

    record_metric(Endpoint::Execute, labels_core, outcome, elapsed);

    v?;
    Ok(())
}

async fn handle_execute_inner(
    token: CancellationToken,
    mut rx: mpsc::Receiver<String>,
    tx: ResponseTx,
    coordinator: SharedCoordinator,
    req: coordinator::ExecuteRequest,
    meta: Meta,
) -> ExecuteResult<CompletedOrAbandoned<Outcome>> {
    use execute_error::*;
    use CompletedOrAbandoned::*;

    let coordinator::ActiveExecution {
        permit: _permit,
        mut task,
        stdin_tx,
        mut stdout_rx,
        mut stderr_rx,
        mut status_rx,
    } = coordinator
        .begin_execute(token, req.clone())
        .await
        .context(BeginSnafu)?;

    let sent = tx
        .send(Ok(MessageResponse::ExecuteBegin { meta: meta.clone() }))
        .await;
    abandon_if_closed!(sent);

    let mut stdin_tx = Some(stdin_tx);

    let send_stdout = async |payload| {
        let meta = meta.clone();
        tx.send(Ok(MessageResponse::ExecuteStdout { payload, meta }))
            .await
    };

    let send_stderr = async |payload| {
        let meta = meta.clone();
        tx.send(Ok(MessageResponse::ExecuteStderr { payload, meta }))
            .await
    };

    let mut reported = false;

    let status = loop {
        enum Event {
            Stdin(Option<String>),
            Stdout(String),
            Stderr(String),
            Status(coordinator::ExecuteStatus),
        }
        use Event::*;

        let event = tokio::select! {
            response = &mut task => break response,

            stdin = rx.recv(), if stdin_tx.is_some() => Stdin(stdin),

            Some(stdout) = stdout_rx.recv() => Stdout(stdout),

            Some(stderr) = stderr_rx.recv() => Stderr(stderr),

            Some(status) = status_rx.next() => Status(status)
        };

        match event {
            Stdin(Some(stdin)) => {
                stdin_tx
                    .as_ref()
                    .unwrap(/* This is a precondition */)
                    .send(stdin)
                    .await
                    .drop_error_details()
                    .context(StdinSnafu)?;
            }
            Stdin(None) => {
                let stdin_tx = stdin_tx.take();
                drop(stdin_tx); // Signal closed
            }

            Stdout(stdout) => {
                let sent = send_stdout(stdout).await;
                abandon_if_closed!(sent);
            }

            Stderr(stderr) => {
                let sent = send_stderr(stderr).await;
                abandon_if_closed!(sent);
            }

            Status(status) => {
                if !reported && status.total_time_secs > 60.0 {
                    error!("Request consumed more than 60s of CPU time: {req:?}");
                    reported = true;
                }

                let payload = status.into();
                let meta = meta.clone();
                let sent = tx
                    .send(Ok(MessageResponse::ExecuteStatus { payload, meta }))
                    .await;
                abandon_if_closed!(sent);
            }
        }
    };

    // Drain any remaining output
    while let Some(Some(stdout)) = stdout_rx.recv().now_or_never() {
        let sent = send_stdout(stdout).await;
        abandon_if_closed!(sent);
    }

    while let Some(Some(stderr)) = stderr_rx.recv().now_or_never() {
        let sent = send_stderr(stderr).await;
        abandon_if_closed!(sent);
    }

    let status = status.context(EndSnafu)?;
    let outcome = Outcome::from_success(&status);

    let coordinator::ExecuteResponse {
        success,
        exit_detail,
    } = status;

    let sent = tx
        .send(Ok(MessageResponse::ExecuteEnd {
            payload: ExecuteResponse {
                success,
                exit_detail,
            },
            meta,
        }))
        .await;
    abandon_if_closed!(sent);

    Ok(Completed(outcome))
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub(crate) enum ExecuteError {
    #[snafu(display("The request could not be parsed"))]
    BadRequest { source: ExecuteRequestParseError },

    #[snafu(display("Could not begin the execution session"))]
    Begin { source: coordinator::ExecuteError },

    #[snafu(display("Could not end the execution session"))]
    End { source: coordinator::ExecuteError },

    #[snafu(display("Could not send stdin to the coordinator"))]
    Stdin {
        source: tokio::sync::mpsc::error::SendError<()>,
    },
}

type ExecuteResult<T, E = ExecuteError> = std::result::Result<T, E>;

#[derive(Debug, Snafu)]
enum Error {
    #[snafu(display("Unable to deserialize request"))]
    Deserialization { source: serde_json::Error },

    #[snafu(display("The WebSocket worker panicked: {}", text))]
    WebSocketTaskPanic { text: String },

    #[snafu(display("Unable to spawn a coordinator task"))]
    StreamingCoordinatorSpawn { source: CoordinatorManagerError },

    #[snafu(display("Unable to idle the coordinator"))]
    StreamingCoordinatorIdle { source: CoordinatorManagerError },

    #[snafu(display("Unable to perform a streaming execute"))]
    StreamingExecute { source: ExecuteError },

    #[snafu(display("Unable to pass stdin to the active execution"))]
    StreamingCoordinatorExecuteStdin {
        source: tokio::sync::mpsc::error::SendError<()>,
    },
}
