use futures::{future::BoxFuture, FutureExt};

use crate::{
    experimental::frame::{expand_and_collapse_async, AsyncMappableFrame, Frame},
    recursive::collapse::Collapsible,
};

/// The ability to collapse a value into some output type, frame by frame
pub trait CollapsibleAsync: Collapsible<FrameToken = Self::AsyncFrameToken>
where
    Self: Sized,
{
    type AsyncFrameToken: AsyncMappableFrame;

    /// defined on trait for convenience and to allow for optimized impls
    fn collapse_frames_async<'a, Out, E>(
        self,
        collapse_frame: impl Fn(Frame<Self::AsyncFrameToken, Out>) -> BoxFuture<'a, Result<Out, E>>
            + Send
            + Sync
            + 'a,
    ) -> BoxFuture<'a, Result<Out, E>>
    where
        Self: Send + Sync + 'a,
        Out: Send + Sync + 'a,
        Frame<Self::AsyncFrameToken, Self>: Send + Sync + 'a,
        Frame<Self::AsyncFrameToken, Out>: Send + Sync + 'a,
        E: Send + Sync + 'a,
    {
        expand_and_collapse_async::<Self, Out, E, Self::AsyncFrameToken>(
            self,
            |seed| std::future::ready(Ok(Self::into_frame(seed))).boxed(),
            collapse_frame,
        )
        .boxed()
    }
}
