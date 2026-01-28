use futures::{future::BoxFuture, FutureExt};

use crate::{
    experimental::frame::{expand_and_collapse_async, AsyncMappableFrame, Frame},
    recursive::expand::Expandable,
};

pub trait ExpandableAsync: Expandable<FrameToken = Self::AsyncFrameToken>
where
    Self: Sized,
{
    type AsyncFrameToken: AsyncMappableFrame;

    /// defined on trait for convenience and to allow for optimized impls
    fn expand_frames_async<'a, In, E>(
        seed: In,
        expand_frame: impl Fn(In) -> BoxFuture<'a, Result<Frame<Self::AsyncFrameToken, In>, E>>
            + Send
            + Sync
            + 'a,
    ) -> BoxFuture<'a, Result<Self, E>>
    where
        Self: Send + Sync + 'a,
        In: Send + Sync + 'a,
        Frame<Self::AsyncFrameToken, Self>: Send + Sync + 'a,
        Frame<Self::AsyncFrameToken, In>: Send + Sync + 'a,
        E: Send + Sync + 'a,
    {
        expand_and_collapse_async::<In, Self, E, Self::AsyncFrameToken>(
            seed,
            expand_frame,
            |frame| std::future::ready(Ok(Self::from_frame(frame))).boxed(),
        )
        .boxed()
    }
}
