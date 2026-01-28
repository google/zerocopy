use crate::frame::{expand_and_collapse, MappableFrame};

/// The ability to recursively collapse some type into some output type, frame by frame.
///
/// # Example: A tree of integers
///
/// Here's an example showing how to use [`Collapsible`] to collapse a binary tree of integers,
/// where nodes hold two subnodes and no data and leaves hold a single `usize` value
///
/// ```rust
/// # use recursion::*;
/// enum IntTree {
///     Leaf { value: usize },
///     Node { left: Box<Self>, right: Box<Self> },
/// }
///
/// # impl IntTree {
/// #     fn node(left: Self, right: Self) -> Self {
/// #         Self::Node {
/// #             left: Box::new(left),
/// #             right: Box::new(right),
/// #         }
/// #     }
/// #     fn leaf(value: usize) -> Self {
/// #         Self::Leaf { value }
/// #     }
/// # }
/// ```
///
/// ## Defining a frame type
///
/// For working with values of type `IntTree`, we'll define an `IntTreeFrame<A>` frame type
/// that represents a single layer of the `IntTree` structure, with `A` subbed in for `Box<Self>`
///
/// ```rust
/// # use recursion::*;
/// enum IntTreeFrame<A> {
///     Leaf { value: usize },
///     Node { left: A, right: A },
/// }
/// impl MappableFrame for IntTreeFrame<PartiallyApplied> { /*...*/
/// #    type Frame<X> = IntTreeFrame<X>;
/// #
/// #    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
/// #         match input {
/// #             IntTreeFrame::Leaf { value } => IntTreeFrame::Leaf { value },
/// #             IntTreeFrame::Node { left, right } => IntTreeFrame::Node {
/// #                 left: f(left),
/// #                 right: f(right),
/// #             },
/// #         }
/// #     }
/// }
/// ```
///
/// ## Implementing Collapsible
///
/// Then we can define a collapse instance for `IntTree`
///
/// ```rust
/// # use recursion::*;
/// # enum IntTree {
/// #     Leaf { value: usize },
/// #     Node { left: Box<Self>, right: Box<Self> },
/// # }
/// # impl IntTree {
/// #   fn node(left: Self, right: Self) -> Self { Self::Node{left: Box::new(left), right: Box::new(right)}}
/// #   fn leaf(value: usize) -> Self { Self::Leaf{value}}
/// # }
/// # enum IntTreeFrame<A> {
/// #     Leaf { value: usize },
/// #     Node { left: A, right: A },
/// # }
/// # impl MappableFrame for IntTreeFrame<PartiallyApplied> {
/// #    type Frame<X> = IntTreeFrame<X>;
/// #
/// #    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
/// #         match input {
/// #             IntTreeFrame::Leaf { value } => IntTreeFrame::Leaf { value },
/// #             IntTreeFrame::Node { left, right } => IntTreeFrame::Node {
/// #                 left: f(left),
/// #                 right: f(right),
/// #             },
/// #         }
/// #     }
/// # }
/// impl<'a> Collapsible for &'a IntTree {
///     type FrameToken = IntTreeFrame<PartiallyApplied>;
///
///     fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self> {
///         match self {
///             IntTree::Leaf { value } => IntTreeFrame::Leaf { value: *value },
///             IntTree::Node { left, right } => IntTreeFrame::Node {
///                 left: left.as_ref(),
///                 right: right.as_ref(),
///             },
///         }
///     }
/// }
/// ```
///
/// ## Collapsing a tree into a value
///
/// Finally, we can use our [`Collapsible`] instance to collapse an example tree into a single value.
/// In this case, we're just doing something simple - counting the number of leaves in the structure
///
/// ```rust
/// # use recursion::*;
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum IntTree {
/// #     Leaf { value: usize },
/// #     Node { left: Box<Self>, right: Box<Self> },
/// # }
/// # impl IntTree {
/// #   fn node(left: Self, right: Self) -> Self { Self::Node{left: Box::new(left), right: Box::new(right)}}
/// #   fn leaf(value: usize) -> Self { Self::Leaf{value}}
/// # }
///
/// # enum IntTreeFrame<A> {
/// #     Leaf { value: usize },
/// #     Node { left: A, right: A },
/// # }
/// # impl MappableFrame for IntTreeFrame<PartiallyApplied> {
/// #    type Frame<X> = IntTreeFrame<X>;
/// #
/// #    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
/// #         match input {
/// #             IntTreeFrame::Leaf { value } => IntTreeFrame::Leaf { value },
/// #             IntTreeFrame::Node { left, right } => IntTreeFrame::Node {
/// #                 left: f(left),
/// #                 right: f(right),
/// #             },
/// #         }
/// #     }
/// # }
/// # impl<'a> Collapsible for &'a IntTree {
/// #     type FrameToken = IntTreeFrame<PartiallyApplied>;
/// #
/// #     fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self> {
/// #         match self {
/// #             IntTree::Leaf { value } => IntTreeFrame::Leaf { value: *value },
/// #             IntTree::Node { left, right } => IntTreeFrame::Node {
/// #                 left: left.as_ref(),
/// #                 right: right.as_ref(),
/// #             },
/// #         }
/// #     }
/// # }
/// let tree = IntTree::node(
///     IntTree::node(IntTree::leaf(0), IntTree::leaf(0)),
///     IntTree::node(IntTree::leaf(0), IntTree::leaf(0)),
/// );
///
/// let leaf_count = tree.collapse_frames(|frame| match frame {
///     IntTreeFrame::Leaf { value } => 1,
///     IntTreeFrame::Node { left, right } => left + right,
/// });
///
/// assert_eq!(leaf_count, 4)
/// ```

pub trait Collapsible
where
    Self: Sized,
{
    type FrameToken: MappableFrame;

    /// Given an instance of this type, generate a frame holding the data owned by it,
    /// with any recursive instances of `Self` owned by this node as the frame elements
    fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self>;
}

pub trait CollapsibleExt: Collapsible
where
    Self: Sized,
{
    /// Given an instance of this type, collapse it into a single value of type `Out` by
    /// traversing the recursive structure of `self`, generating frames, and collapsing
    /// those frames using some function from `Frame<Out> -> Out`
    fn collapse_frames<Out>(
        self,
        collapse_frame: impl FnMut(<Self::FrameToken as MappableFrame>::Frame<Out>) -> Out,
    ) -> Out;

    /// Given an instance of this type, collapse it into a single value of type `Result<Out, E>` by
    /// traversing the recursive structure of `self`, generating frames, and collapsing
    /// those frames using some function from `Frame<Out> -> Result<Out, E>`
    fn try_collapse_frames<Out, E>(
        self,
        collapse_frame: impl FnMut(<Self::FrameToken as MappableFrame>::Frame<Out>) -> Result<Out, E>,
    ) -> Result<Out, E>;
}

impl<X> CollapsibleExt for X
where
    X: Collapsible,
{
    fn collapse_frames<Out>(
        self,
        collapse_frame: impl FnMut(<Self::FrameToken as MappableFrame>::Frame<Out>) -> Out,
    ) -> Out {
        expand_and_collapse::<Self::FrameToken, Self, Out>(self, Self::into_frame, collapse_frame)
    }

    // TODO: add example here in this file
    fn try_collapse_frames<Out, E>(
        self,
        collapse_frame: impl FnMut(<Self::FrameToken as MappableFrame>::Frame<Out>) -> Result<Out, E>,
    ) -> Result<Out, E> {
        crate::frame::try_expand_and_collapse::<Self::FrameToken, Self, Out, E>(
            self,
            |seed| Ok(Self::into_frame(seed)),
            collapse_frame,
        )
    }
}
