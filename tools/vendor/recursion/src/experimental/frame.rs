use std::sync::Arc;

use crate::frame::MappableFrame;

use futures::{future::BoxFuture, stream::FuturesUnordered, FutureExt, StreamExt};
use tokio::sync::{mpsc, oneshot};

pub mod compose;

pub(crate) type Frame<F, X> = <F as MappableFrame>::Frame<X>;

// mostly just used for Compact (defined over frame, needs to collapse_ref via ref frame)
pub trait MappableFrameRef: MappableFrame {
    type RefFrameToken<'a>: MappableFrame;

    fn as_ref<X>(input: &Self::Frame<X>) -> <Self::RefFrameToken<'_> as MappableFrame>::Frame<&X>;
}

pub trait AsyncMappableFrame: MappableFrame {
    // NOTE: what does having 'a here mean/imply? should 'a bound be on A/B/E?
    fn map_frame_async<'a, A, B, E>(
        input: Self::Frame<A>,
        f: impl Fn(A) -> BoxFuture<'a, Result<B, E>> + Send + Sync + 'a,
    ) -> BoxFuture<'a, Result<Self::Frame<B>, E>>
    where
        E: Send + 'a,
        A: Send + 'a,
        B: Send + 'a;
}

pub async fn expand_and_collapse_async<'a, Seed, Out, E, F>(
    seed: Seed,
    expand_frame: impl Fn(Seed) -> BoxFuture<'a, Result<Frame<F, Seed>, E>> + Send + Sync + 'a,
    collapse_frame: impl Fn(Frame<F, Out>) -> BoxFuture<'a, Result<Out, E>> + Send + Sync + 'a,
) -> Result<Out, E>
where
    E: Send + Sync + 'a,
    F: AsyncMappableFrame + 'a,
    Seed: Send + Sync + 'a,
    Out: Send + Sync + 'a,
    Frame<F, Seed>: Send + Sync + 'a,
    Frame<F, Out>: Send + Sync + 'a,
{
    let expand_frame = Arc::new(expand_frame);
    let collapse_frame = Arc::new(collapse_frame);

    let mut work_pool: FuturesUnordered<BoxFuture<'a, Result<(), E>>> = FuturesUnordered::new();
    let (work_sender, mut work_receiver) = mpsc::channel(1024); // idk what size is right here

    let (root_step, root_receiver) = Step::new(seed, work_sender);

    work_pool.push(
        root_step
            .run::<'a, F, E>(expand_frame.clone(), collapse_frame.clone())
            .boxed(),
    );

    loop {
        tokio::select! {
            // enqueue more work if we have it (bias should be here)
            Some(work) = work_receiver.recv() => work_pool.push(work.run::<F, E>(expand_frame.clone(), collapse_frame.clone()).boxed()),

            // push existing work to completion and short circuit if err
            Some(completion) = work_pool.next() => match completion{
                                Ok(_) => continue,
                                Err(e) => return Err(e),
                            },
            else => break,
        }
    }

    Ok(root_receiver.await.unwrap()) // will always terminate
}

struct Step<Seed, Out> {
    seed: Seed,
    completion_sender: oneshot::Sender<Out>,
    work_queue: mpsc::Sender<Self>,
}

// NOTE[future work]: I could build in visualization via an mpsc channel of events just like in Viz (woah, nice, etc)
impl<Seed: Sync + Send, Out: Sync + Send> Step<Seed, Out> {
    fn new(seed: Seed, work_queue: mpsc::Sender<Self>) -> (Self, oneshot::Receiver<Out>) {
        let (sender, receiver) = oneshot::channel();

        let item = Step {
            seed,
            completion_sender: sender,
            work_queue,
        };

        (item, receiver)
    }

    async fn run<'a, F: AsyncMappableFrame, E: Send + Sync + 'a>(
        self,
        expand_frame: Arc<
            dyn Fn(Seed) -> BoxFuture<'a, Result<Frame<F, Seed>, E>> + Send + Sync + 'a,
        >,
        collapse_frame: Arc<
            dyn Fn(Frame<F, Out>) -> BoxFuture<'a, Result<Out, E>> + Send + Sync + 'a,
        >,
    ) -> Result<(), E> {
        // first we expand the seed to a frame of seeds
        let frame = expand_frame(self.seed).await?;

        // enqueue work to expand each seed in the frame
        let node = F::map_frame_async(frame, |seed| {
            async {
                // for each seed in the frame, enqueue a 'Step' while hanging on to that step's receiver
                let (step, receiver) = Step::new(seed, self.work_queue.clone());
                self.work_queue.send(step).await.ok().expect("mpsc error");

                // wait on that step's receiver, at which point we have an 'Out' value to complete with
                let recvd: Out = receiver.await.expect("oneshot recv error");
                Ok(recvd)
            }
            .boxed()
        })
        .await?;

        // collapse the resulting 'Frame<F, Out>' into an 'Out'
        let collapsed = collapse_frame(node).await?;

        // pass the resulting 'Out' to this step's parent
        self.completion_sender
            .send(collapsed)
            .ok()
            .expect("oneshot send failure");

        Ok(())
    }
}
