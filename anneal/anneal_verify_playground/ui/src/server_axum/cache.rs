use futures::{
    future::{Fuse, FusedFuture as _},
    FutureExt as _,
};
use orchestrator::{DropErrorDetailsExt as _, TaskAbortExt as _};
use snafu::prelude::*;
use std::{
    future::Future,
    pin::pin,
    sync::Arc,
    time::{Duration, Instant, SystemTime},
};
use tokio::{
    select,
    sync::{mpsc, oneshot},
    time,
};
use tokio_util::task::AbortOnDropHandle;
use tracing::warn;

const ONE_HUNDRED_MILLISECONDS: Duration = Duration::from_millis(100);
const TEN_SECONDS: Duration = Duration::from_secs(10);
const TEN_MINUTES: Duration = Duration::from_secs(10 * 60);

pub const SANDBOX_CACHE_TIME_TO_LIVE: Duration = TEN_MINUTES;
const SANDBOX_CACHE_ERROR_TIME_TO_LIVE: Duration = TEN_SECONDS;
const SANDBOX_CACHE_INITIAL_DELAY: Duration = ONE_HUNDRED_MILLISECONDS;

pub type Stamped<T> = (T, SystemTime);

#[derive(Debug)]
pub struct CacheTx<T, E>(mpsc::Sender<CacheTaskItem<T, E>>)
where
    E: snafu::Error + 'static;

impl<T, E> Clone for CacheTx<T, E>
where
    E: snafu::Error + 'static,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T, E> CacheTx<T, E>
where
    E: snafu::Error + 'static,
{
    pub fn spawn<Fut>(
        f: impl FnOnce(mpsc::Receiver<CacheTaskItem<T, E>>) -> Fut,
    ) -> (AbortOnDropHandle<()>, Self)
    where
        Fut: Future<Output = ()> + Send + 'static,
    {
        let (tx, rx) = mpsc::channel(8);
        let task = tokio::spawn(f(rx)).abort_on_drop();
        let cache_tx = CacheTx(tx);
        (task, cache_tx)
    }

    pub async fn get(&self) -> Result<Stamped<T>, CacheTxError<E>> {
        use cache_tx_error::*;

        let (tx, rx) = oneshot::channel();
        self.0
            .send(tx)
            .await
            .drop_error_details()
            .context(SendToTaskSnafu)?;
        let value = rx.await.context(RecvFromTaskSnafu)?;
        Ok((value.0?, value.1))
    }
}

#[derive(Debug, Snafu)]
#[snafu(module)]
pub enum CacheTxError<E: snafu::Error + 'static> {
    #[snafu(display("Could not contact the cache"))]
    SendToTask { source: mpsc::error::SendError<()> },

    #[snafu(display("Did not receive a response from the cache"))]
    RecvFromTask { source: oneshot::error::RecvError },

    #[snafu(transparent)]
    Inner { source: CacheError<E> },
}

pub type CacheTaskItem<T, E> = oneshot::Sender<CacheResponse<T, E>>;
pub type CacheResponse<T, E> = Stamped<Result<T, CacheError<E>>>;

pub async fn cache_task<T, E, G, Fut>(mut rx: mpsc::Receiver<CacheTaskItem<T, E>>, generator: G)
where
    T: Clone + PartialEq,
    T: Send + 'static,
    E: snafu::Error,
    E: Send + Sync,
    G: FnMut() -> Fut,
    G: Clone + Send + 'static,
    Fut: Future<Output = Result<T, E>>,
    Fut: Send,
{
    let mut cached_value = CacheInfo::build(Err(CacheError::Empty));
    // Sleep is fused so that it resolves exactly once
    let mut cache_expired = pin!(time::sleep(SANDBOX_CACHE_INITIAL_DELAY).fuse());
    let mut new_value = pin!(Fuse::terminated());

    loop {
        enum Event<T, E>
        where
            E: snafu::Error + 'static,
        {
            Rx(Option<CacheTaskItem<T, E>>),

            Expired,

            New(Result<CacheInfo<Result<T, CacheError<E>>>, tokio::task::JoinError>),
        }
        use Event::*;

        let event = select! {
            rx = rx.recv() => Rx(rx),

            _ = &mut cache_expired => Expired,

            new = &mut new_value => New(new),
        };

        match event {
            // All senders dropped, indicating shutdown
            Rx(None) => break,

            // Someone wants the cached value
            Rx(Some(resp_tx)) => {
                resp_tx.send(cached_value.stamped_value()).ok(/* Don't care if they received it */);
            }

            // The cached value has expired, start working on a new one
            Expired => {
                assert!(
                    new_value.is_terminated(),
                    "The previous cache task has not completed",
                );

                let new_value_task = tokio::spawn({
                    let mut generator = generator.clone();

                    async move {
                        let new_value = generator().await.map_err(CacheError::from);
                        CacheInfo::build(new_value)
                    }
                })
                .abort_on_drop();

                new_value.set(new_value_task.fuse());
            }

            // A new value is ready to be stored in the cache
            New(new_value) => {
                assert!(
                    cache_expired.is_terminated(),
                    "The previous cache timer has not completed",
                );

                let new_value = new_value.unwrap_or_else(|e| {
                    warn!(?e, "The cache task exited abnormally");
                    CacheInfo::build(Err(CacheError::Empty))
                });

                cached_value = new_value.try_combine_with_previous(cached_value);

                let cache_ttl = if cached_value.value.is_ok() {
                    SANDBOX_CACHE_TIME_TO_LIVE
                } else {
                    SANDBOX_CACHE_ERROR_TIME_TO_LIVE
                };

                cache_expired.set(time::sleep(cache_ttl).fuse());
            }
        }
    }
}

#[derive(Debug)]
struct CacheInfo<T> {
    value: T,
    creation_time: SystemTime,
    validation_time: Instant,
}

impl<T> CacheInfo<T> {
    fn build(value: T) -> Self {
        let creation_time = SystemTime::now();
        let validation_time = Instant::now();

        Self {
            value,
            creation_time,
            validation_time,
        }
    }

    fn stamped_value(&self) -> Stamped<T>
    where
        T: Clone,
    {
        (self.value.clone(), self.creation_time)
    }
}

impl<T, E> CacheInfo<Result<T, E>> {
    fn try_combine_with_previous(self, mut old_value: Self) -> Self
    where
        T: PartialEq,
    {
        match (&old_value.value, &self.value) {
            // Always take the successful value
            (Err(_), Ok(_)) => self,

            // It doesn't really matter which error we keep, so pick the newer one
            (Err(_), Err(_)) => self,

            // Keep the stale version instead of the broken version
            (Ok(_), Err(_)) => old_value,

            (Ok(old), Ok(new)) => {
                if old == new {
                    // The value hasn't changed; record that we have
                    // checked recently, but keep the creation time to
                    // preserve caching.
                    old_value.validation_time = self.validation_time;
                    old_value
                } else {
                    self
                }
            }
        }
    }
}

#[derive(Debug, Snafu)]
pub enum CacheError<E>
where
    E: snafu::Error + 'static,
{
    #[snafu(display("No value has been cached yet"))]
    Empty,

    #[snafu(transparent)]
    Real {
        #[snafu(source(from(E, Arc::new)))]
        source: Arc<E>,
    },
}

impl<E> Clone for CacheError<E>
where
    E: snafu::Error + 'static,
{
    fn clone(&self) -> Self {
        match self {
            CacheError::Empty => CacheError::Empty,
            CacheError::Real { source } => CacheError::Real {
                source: source.clone(),
            },
        }
    }
}
