/// A single 'frame' containing values that can be mapped over via `map_frame`.
///
/// # Motivation
///
/// Generally speaking, you won't use this trait yourself. It's used by the internal plumbing of
/// [`crate::Collapsible`] and [`crate::Expandable`] to implement recursive traversals.
///
/// # Implementing this trait
///
/// This trait is usually implemented for some marker token, because rust does not
/// allow for implementing a trait for a partially applied type. That is, we can implement
/// a trait for `Option<usize>` but we can't implement a trait for just `Option`, because
/// `Option` is a partially applied type.
///
/// For this reason, a common convention is to implement this trait using the uninhabited
///  [`PartiallyApplied`] enum marker, eg
///
/// ```rust
/// # use recursion::{MappableFrame, PartiallyApplied};
/// # #[derive(Debug, PartialEq, Eq)]
/// enum MyOption<A> {
///     Some(A),
///     None,
/// }
///
/// impl MappableFrame for MyOption<PartiallyApplied> {
///     type Frame<X> = MyOption<X>;
///
///     fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
///         match input {
///             MyOption::Some(x) => MyOption::Some(f(x)),
///             MyOption::None => MyOption::None,
///         }
///     }
/// }
/// ```
///
/// # Use
///
/// Here's what mapping over a `MyOption` frame looks like in action:
/// ```rust
/// # use recursion::{MappableFrame, PartiallyApplied};
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum MyOption<A> {
/// #     Some(A),
/// #     None,
/// # }
/// #
/// # impl MappableFrame for MyOption<PartiallyApplied> {
/// #     type Frame<X> = MyOption<X>;
/// #
/// #     fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
/// #         match input {
/// #             MyOption::Some(x) => MyOption::Some(f(x)),
/// #             MyOption::None => MyOption::None,
/// #         }
/// #     }
/// # }
/// let frame = MyOption::Some(1);
/// let mapped_frame = MyOption::<PartiallyApplied>::map_frame(frame, |n| n + 10);
///
/// assert_eq!(mapped_frame, MyOption::Some(11));
/// ```
pub trait MappableFrame {
    /// the frame type that is mapped over by `map_frame`
    type Frame<X>;

    /// Apply some function `f` to each element inside a frame
    fn map_frame<A, B>(input: Self::Frame<A>, f: impl FnMut(A) -> B) -> Self::Frame<B>;
}

/// "An uninhabited type used to define [`MappableFrame`] instances for partially-applied types."
///
/// For example: the MappableFrame instance for `MyFrame<A>` cannot be written over the
/// partially-applied type `MyFrame`, so instead we write it over `MyFrame<PartiallyApplied>`
#[derive(Debug)]
pub enum PartiallyApplied {}

/// This function generates a stack machine for some frame `F::Frame`,
/// expanding some seed value `Seed` into frames via a function `Seed -> Frame<Seed>`
/// and collapsing those values via a function `Frame<Out> -> Out`.
///
/// This function performs a depth-first traversal, expanding and collapsing each branch in turn
///
/// This function is stack safe (it does not use the call stack), but it
/// does use an internal stack data structure and is thus, technically,
/// susceptible to stack overflows if said stack expands
pub fn expand_and_collapse<F: MappableFrame, Seed, Out>(
    seed: Seed,
    mut expand_frame: impl FnMut(Seed) -> F::Frame<Seed>,
    mut collapse_frame: impl FnMut(F::Frame<Out>) -> Out,
) -> Out {
    enum State<Seed, CollapsibleInternal> {
        Expand(usize, Seed),
        Collapse(usize, CollapsibleInternal),
    }

    let mut vals: Vec<Option<Out>> = vec![None];
    let mut stack = vec![State::Expand(0, seed)];

    while let Some(item) = stack.pop() {
        match item {
            State::Expand(val_idx, seed) => {
                let node = expand_frame(seed);
                let mut seeds = Vec::new();
                let node = F::map_frame(node, |seed| {
                    vals.push(None);
                    let idx = vals.len() - 1;
                    seeds.push(State::Expand(idx, seed));
                    idx
                });

                stack.push(State::Collapse(val_idx, node));
                stack.extend(seeds);
            }
            State::Collapse(val_idx, node) => {
                let node = F::map_frame(node, |k| vals[k].take().unwrap());
                vals[val_idx] = Some(collapse_frame(node));
            }
        };
    }
    vals[0].take().unwrap()
}

/// This function generates a fallible stack machine for some frame `F::Frame`,
/// expanding some seed value `Seed` into frames via a function `Seed -> Result<Frame<Seed>, E>`
/// and collapsing those values via a function `Frame<Out> -> Result<Out, E>`.
///
/// This function performs a depth-first traversal, expanding and collapsing each branch in turn
///
/// This function is stack safe (it does not use the call stack), but it
/// does use an internal stack data structure and is thus, technically,
/// susceptible to stack overflows if said stack expands
pub fn try_expand_and_collapse<F: MappableFrame, Seed, Out, E>(
    seed: Seed,
    mut expand_frame: impl FnMut(Seed) -> Result<F::Frame<Seed>, E>,
    mut collapse_frame: impl FnMut(F::Frame<Out>) -> Result<Out, E>,
) -> Result<Out, E> {
    enum State<Seed, CollapsibleInternal> {
        Expand(usize, Seed),
        Collapse(usize, CollapsibleInternal),
    }

    let mut vals: Vec<Option<Out>> = vec![None];
    let mut stack = vec![State::Expand(0, seed)];

    while let Some(item) = stack.pop() {
        match item {
            State::Expand(val_idx, seed) => {
                let node = expand_frame(seed)?;
                let mut seeds = Vec::new();
                let node = F::map_frame(node, |seed| {
                    vals.push(None);
                    let idx = vals.len() - 1;
                    seeds.push(State::Expand(idx, seed));
                    idx
                });

                stack.push(State::Collapse(val_idx, node));
                stack.extend(seeds);
            }
            State::Collapse(val_idx, node) => {
                let node = F::map_frame(node, |k| vals[k].take().unwrap());
                vals[val_idx] = Some(collapse_frame(node)?);
            }
        };
    }
    Ok(vals[0].take().unwrap())
}
