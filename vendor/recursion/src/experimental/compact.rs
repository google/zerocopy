use crate::{frame::MappableFrame, recursive::collapse::Collapsible};

use super::frame::MappableFrameRef;

pub struct Compact<F: MappableFrame>(pub Vec<F::Frame<()>>);

#[repr(transparent)]
pub struct CompactRef<F: MappableFrame>(pub [F::Frame<()>]);

impl<F: MappableFrame> Compact<F> {
    // the idea here is to have 'compact' as a transparent wrapper around collapsible structures,
    // such that they can be pre-compacted and we don't need to run the expand step each time

    // ALSO, this makes it so we can just remove the expandable/collapsible defn's and can
    // just have a method 'collapse_frames' on Compact
    pub fn new<E: Collapsible<FrameToken = F>>(e: E) -> Self {
        expand_compact(e, E::into_frame)
    }

    pub fn collapse_frames<Out>(
        self,
        collapse_frame: impl FnMut(<F as MappableFrame>::Frame<Out>) -> Out,
    ) -> Out {
        collapse_compact::<F, Out>(self, collapse_frame)
    }
}

impl<F: MappableFrame + MappableFrameRef> Compact<F> {
    pub fn collapse_frames_ref<'a, 'c: 'a, Out>(
        &'c self,
        collapse_frame: impl FnMut(<F::RefFrameToken<'a> as MappableFrame>::Frame<Out>) -> Out,
    ) -> Out {
        collapse_compact_ref::<'a, 'c, F, Out>(self, collapse_frame)
    }
}

pub fn collapse_compact<F: MappableFrame, Out>(
    c: Compact<F>,
    mut collapse_frame: impl FnMut(F::Frame<Out>) -> Out,
) -> Out {
    let mut vals: Vec<Out> = vec![];

    for item in c.0.into_iter() {
        let node = F::map_frame(item, |_: ()| vals.pop().unwrap());
        vals.push(collapse_frame(node))
    }
    vals.pop().unwrap()
}

pub fn collapse_compact_ref<'a, 'c: 'a, F: MappableFrameRef, Out>(
    c: &'c Compact<F>,
    mut collapse_frame: impl FnMut(<F::RefFrameToken<'a> as MappableFrame>::Frame<Out>) -> Out,
) -> Out {
    let mut vals: Vec<Out> = vec![];

    for item in c.0.iter() {
        let node = <F::RefFrameToken<'a>>::map_frame(F::as_ref(item), |_: &()| vals.pop().unwrap());
        vals.push(collapse_frame(node))
    }
    vals.pop().unwrap()
}

// important note: I don't really want to do this, let's elide perf data for the GAT impl and center ergonomics
pub fn expand_compact<F: MappableFrame, Seed>(
    seed: Seed,
    mut expand_frame: impl FnMut(Seed) -> F::Frame<Seed>,
) -> Compact<F> {
    let mut frontier = Vec::from([seed]);
    let mut elems = vec![];

    // expand to build a vec of elems while preserving topo order
    while let Some(seed) = frontier.pop() {
        let frame = expand_frame(seed);

        let mut topush = Vec::new();
        let frame = F::map_frame(frame, |aa| {
            topush.push(aa);
        });
        frontier.extend(topush.into_iter().rev());

        elems.push(frame);
    }

    elems.reverse();

    Compact(elems)
}
