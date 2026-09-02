# Prior design note

The project previously approved a conditional design sketch: a private raw
pointer plus `PhantomData<&mut T>` would represent a uniquely borrowed view.
That review explicitly required a fresh source audit after implementation.

