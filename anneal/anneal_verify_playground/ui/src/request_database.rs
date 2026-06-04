use orchestrator::DropErrorDetailsExt;
use rusqlite::Connection;
use snafu::prelude::*;
use std::path::Path;
use tokio::{
    sync::{mpsc, oneshot},
    task,
};
use tracing::{info, warn, Instrument as _};

pub struct Database {
    db: Connection,
}

#[derive(Debug, Copy, Clone)]
pub struct Id(i64);

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum How {
    Complete = 0,
    Abandoned = 1,
    Error = 2,
}

impl Database {
    fn new(path: impl AsRef<Path>) -> Result<Self> {
        let db = Connection::open(path).context(CreateSnafu)?;
        Ok(Self { db })
    }

    fn new_memory() -> Result<Self> {
        let db = Connection::open_in_memory().context(CreateMemorySnafu)?;
        Ok(Self { db })
    }

    pub fn initialize(path: impl AsRef<Path>) -> Result<Self> {
        let this = Self::new(path)?;
        this.ensure_tables()?;
        Ok(this)
    }

    pub fn initialize_memory() -> Result<Self> {
        let this = Self::new_memory()?;
        this.ensure_tables()?;
        Ok(this)
    }

    fn ensure_tables(&self) -> Result<()> {
        let sql = r#"
            CREATE TABLE IF NOT EXISTS requests (
                id INTEGER PRIMARY KEY,
                started_at INTEGER DEFAULT (unixepoch()) NOT NULL,
                ended_at INTEGER,
                how INTEGER,
                category TEXT NOT NULL,
                payload TEXT NOT NULL
            ) STRICT
        "#;
        self.db.execute_batch(sql).context(InitializeSnafu)
    }

    pub fn start_request(&self, category: &str, payload: &str) -> Result<Id> {
        let sql = r#"
            INSERT INTO requests (category, payload)
            VALUES (?1, ?2)
            RETURNING id
        "#;
        let id = self
            .db
            .query_row(sql, (category, payload), |r| r.get(0))
            .context(StartRequestSnafu)?;

        Ok(Id(id))
    }

    pub fn end_request(&self, id: Id, how: How) -> Result<()> {
        let sql = r#"
            UPDATE requests
            SET
                ended_at = unixepoch(),
                how = ?2
            WHERE id = ?1
        "#;
        self.db
            .execute(sql, (id.0, how as u8))
            .map(drop)
            .context(EndRequestSnafu)
    }

    pub fn spawn(self) -> (task::JoinHandle<()>, Handle) {
        let (tx, rx) = mpsc::channel(10);
        let task = task::spawn_blocking(|| self.task(rx));
        let handle = Handle { tx };

        (task, handle)
    }

    fn task(self, mut rx: mpsc::Receiver<Message>) {
        while let Some(msg) = rx.blocking_recv() {
            match msg {
                Message::StartRequest {
                    category,
                    payload,
                    tx,
                } => {
                    let r = self.start_request(&category, &payload);
                    tx.send(r).ok(/* Don't care if caller is gone */);
                }

                Message::EndRequest { id, how, tx } => {
                    let r = self.end_request(id, how);
                    tx.send(r).ok(/* Don't care if caller is gone */);
                }
            }
        }
    }
}

#[derive(Debug, Snafu)]
pub enum Error {
    Create { source: rusqlite::Error },

    CreateMemory { source: rusqlite::Error },

    Initialize { source: rusqlite::Error },

    StartRequest { source: rusqlite::Error },

    EndRequest { source: rusqlite::Error },
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Debug)]
enum Message {
    StartRequest {
        category: String,
        payload: String,
        tx: oneshot::Sender<Result<Id>>,
    },

    EndRequest {
        id: Id,
        how: How,
        tx: oneshot::Sender<Result<()>>,
    },
}

#[derive(Clone)]
pub struct Handle {
    tx: mpsc::Sender<Message>,
}

impl Handle {
    async fn start_request(
        &self,
        category: impl Into<String>,
        payload: impl Into<String>,
    ) -> HandleResult<Id> {
        let category = category.into();
        let payload = payload.into();
        let (tx, rx) = oneshot::channel();

        self.tx
            .send(Message::StartRequest {
                category,
                payload,
                tx,
            })
            .await
            .drop_error_details()
            .context(SendStartRequestSnafu)?;

        let id = rx.await.context(RecvStartRequestSnafu)??;

        info!(request_id = id.0, "Started request");

        Ok(id)
    }

    async fn attempt_start_request(
        &self,
        category: impl Into<String>,
        payload: impl Into<String>,
    ) -> Option<Id> {
        match self.start_request(category, payload).await {
            Ok(id) => Some(id),
            Err(err) => {
                warn!(?err, "Unable to record start request");
                None
            }
        }
    }

    async fn end_request(&self, id: Id, how: How) -> HandleResult<()> {
        let (tx, rx) = oneshot::channel();

        self.tx
            .send(Message::EndRequest { id, how, tx })
            .await
            .drop_error_details()
            .context(SendEndRequestSnafu)?;

        rx.await.context(RecvEndRequestSnafu)??;

        info!(request_id = id.0, "Ended request");

        Ok(())
    }

    async fn attempt_end_request(&self, id: Id, how: How) {
        if let Err(err) = self.end_request(id, how).await {
            warn!(?err, "Unable to record end request");
        }
    }

    pub async fn start_with_guard(
        self,
        category: impl Into<String>,
        payload: impl Into<String>,
    ) -> EndGuard {
        let g = self
            .attempt_start_request(category, payload)
            .await
            .map(|id| EndGuardInner(id, How::Abandoned, Some(self)));
        EndGuard(g)
    }
}

pub struct EndGuard(Option<EndGuardInner>);

impl EndGuard {
    pub fn complete_now<T, E>(mut self, result: Result<T, E>) -> Result<T, E> {
        if let Some(mut inner) = self.0.take() {
            inner.1 = if result.is_err() {
                How::Error
            } else {
                How::Complete
            };

            drop(inner);
        }

        result
    }
}

struct EndGuardInner(Id, How, Option<Handle>);

impl Drop for EndGuardInner {
    fn drop(&mut self) {
        let Self(id, how, ref mut handle) = *self;
        if let Ok(h) = tokio::runtime::Handle::try_current() {
            if let Some(handle) = handle.take() {
                h.spawn(async move { handle.attempt_end_request(id, how).await }.in_current_span());
            }
        }
    }
}

#[derive(Debug, Snafu)]
pub enum HandleError {
    #[snafu(transparent)]
    Database {
        source: Error,
    },

    SendStartRequest {
        source: mpsc::error::SendError<()>,
    },

    RecvStartRequest {
        source: oneshot::error::RecvError,
    },

    SendEndRequest {
        source: mpsc::error::SendError<()>,
    },

    RecvEndRequest {
        source: oneshot::error::RecvError,
    },
}

pub type HandleResult<T, E = HandleError> = std::result::Result<T, E>;
