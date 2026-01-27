use crate::frame::MappableFrame;

// mostly just used for Compact (defined over frame, needs to collapse_ref via ref frame)
pub trait MappableFrameRef: MappableFrame {
    type RefFrameToken<'a>: MappableFrame;

    fn as_ref<X>(input: &Self::Frame<X>) -> <Self::RefFrameToken<'_> as MappableFrame>::Frame<&X>;
}

pub struct Compose<F1, F2>(std::marker::PhantomData<F1>, std::marker::PhantomData<F2>);

impl<F1: MappableFrame, F2: MappableFrame> MappableFrame for Compose<F1, F2> {
    type Frame<X> = F1::Frame<F2::Frame<X>>;

    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
        F1::map_frame(input, move |x| F2::map_frame(x, &mut f))
    }
}

#[derive(Debug)]
pub enum PartiallyApplied {}

impl MappableFrame for Option<PartiallyApplied> {
    type Frame<X> = Option<X>;

    fn map_frame<A, B>(input: Self::Frame<A>, f: impl FnMut(A) -> B) -> Self::Frame<B> {
        input.map(f)
    }
}

impl<Fst> MappableFrame for (Fst, PartiallyApplied) {
    type Frame<X> = (Fst, X);

    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
        (input.0, f(input.1))
    }
}

pub struct PairMappableFrame;

pub type Paired<F> = Compose<PairMappableFrame, F>;

impl MappableFrame for PairMappableFrame {
    type Frame<X> = (X, X);

    fn map_frame<A, B>(input: Self::Frame<A>, mut f: impl FnMut(A) -> B) -> Self::Frame<B> {
        (f(input.0), f(input.1))
    }
}

pub trait TryMappableFrame: MappableFrame {
    // NOTE: can I do anything about implicit ordering requirement here?
    fn try_map_frame<A, B, E>(
        input: Self::Frame<A>,
        f: impl FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Frame<B>, E>;
}

pub fn try_expand_and_collapse<F: TryMappableFrame, Seed, Out, E>(
    seed: Seed,
    mut expand_frame: impl FnMut(Seed) -> Result<F::Frame<Seed>, E>,
    mut collapse_frame: impl FnMut(F::Frame<Out>) -> Result<Out, E>,
) -> Result<Out, E> {
    enum State<Seed, CollapsibleInternal> {
        Expand(Seed),
        Collapse(CollapsibleInternal),
    }

    let mut vals: Vec<Out> = vec![];
    let mut stack = vec![State::Expand(seed)];

    while let Some(item) = stack.pop() {
        match item {
            State::Expand(seed) => {
                let node = expand_frame(seed)?;
                let mut seeds = Vec::new();
                let node = F::map_frame(node, |seed| seeds.push(seed));

                stack.push(State::Collapse(node));
                stack.extend(seeds.into_iter().map(State::Expand));
            }
            State::Collapse(node) => {
                let node = F::map_frame(node, |_: ()| vals.pop().unwrap());
                vals.push(collapse_frame(node)?)
            }
        };
    }
    Ok(vals.pop().unwrap())
}
