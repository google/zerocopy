pub mod compact;
pub mod fix;
pub mod frame;
pub mod recursive;

use futures::{future, FutureExt, TryFutureExt};

use crate::{frame::MappableFrame, recursive::collapse::Collapsible};

use self::{
    frame::{compose::PartiallyApplied, AsyncMappableFrame},
    recursive::collapse::CollapsibleAsync,
};

// TODO: move to tests
pub enum Peano<Next> {
    Succ(Next),
    Zero,
}

impl MappableFrame for Peano<PartiallyApplied> {
    type Frame<Next> = Peano<Next>;

    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
        match input {
            Peano::Succ(x) => Peano::Succ(f(x)),
            Peano::Zero => Peano::Zero,
        }
    }
}

impl AsyncMappableFrame for Peano<PartiallyApplied> {
    fn map_frame_async<'a, A, B, E>(
        input: Self::Frame<A>,
        f: impl Fn(A) -> futures::future::BoxFuture<'a, Result<B, E>> + Send + Sync + 'a,
    ) -> futures::future::BoxFuture<'a, Result<Self::Frame<B>, E>>
    where
        E: Send + 'a,
        A: Send + 'a,
        B: Send + 'a,
    {
        match input {
            Peano::Succ(x) => f(x).map_ok(Peano::Succ).boxed(),
            Peano::Zero => future::ready(Ok(Peano::Zero)).boxed(),
        }
    }
}

impl Collapsible for usize {
    type FrameToken = Peano<PartiallyApplied>;

    fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self> {
        if self == 0 {
            Peano::Zero
        } else {
            Peano::Succ(self - 1)
        }
    }
}

impl CollapsibleAsync for usize {
    type AsyncFrameToken = Peano<PartiallyApplied>;
}

#[test]
fn peano_numbers() {
    use crate::recursive::CollapsibleExt;
    let x: usize = 3;

    let peano_repr: String = x.collapse_frames(|frame: Peano<String>| match frame {
        Peano::Succ(mut acc) => {
            acc.push_str(" + 1");
            acc
        }
        Peano::Zero => "0".to_string(),
    });

    assert_eq!("0 + 1 + 1 + 1", &peano_repr);
}

#[tokio::test]
async fn peano_numbers_async() {
    let x: usize = 3;

    let peano_repr: Result<String, String> = x
        .collapse_frames_async(|frame: Peano<String>| {
            async {
                match frame {
                    Peano::Succ(mut acc) => {
                        acc.push_str(" + 1");
                        Ok(acc)
                    }
                    Peano::Zero => Ok("0".to_string()),
                }
            }
            .boxed()
        })
        .await;

    assert_eq!("0 + 1 + 1 + 1", &peano_repr.unwrap());
}
