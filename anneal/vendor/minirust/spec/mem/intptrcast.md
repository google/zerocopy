# MiniRust integer-pointer cast model

This file defines the approach MiniRust takes to integer-pointer casts.
It is basically exactly what was outlined [in this blog post](https://www.ralfj.de/blog/2022/04/11/provenance-exposed.html).
The brief summary is that we treat pointer-to-integer casts as having the side-effect of recording, in a piece of global state, that the provenance of this pointer has been exposed.
An integer-to-pointer cast then non-deterministically guesses a suitable provenance for the new pointer.
Using the `predict` function means that this guess will be made maximally in the programmer's favor: if there *exists* a choice for the guess that makes program behavior well-defined, then that is the choice that will be made.

Note that this is entirely independent of how the actual memory model works.
We are just parameterized by its type of `Provenance`.

```rust
pub struct IntPtrCast<Provenance> {
    /// The set of exposed provenance.
    exposed: Set<Provenance>,
}

impl<Provenance> IntPtrCast<Provenance> {
    pub fn new() -> Self {
        Self { exposed: Set::new() }
    }

    pub fn expose(&mut self, ptr: ThinPointer<Provenance>) {
        if let Some(provenance) = ptr.provenance {
            // Remember this provenance as having been exposed.
            self.exposed.insert(provenance);
        }
    }

    pub fn int2ptr(&self, addr: Int) -> NdResult<ThinPointer<Provenance>> {
        // Predict a suitable provenance. It must be either `None` or already exposed.
        let provenance = predict(|prov: Option<Provenance>| {
            prov.map_or(
                true, // `None` is always an option
                |p| self.exposed.contains(p),
            )
        })?;

        // Construct a pointer with that provenance.
        ret(ThinPointer { addr, provenance })
    }
}
```
