# Anneal

<img src="docs/images/logo.svg" width="100%">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

Anneal is an experimental Rust verifier that uses Lean 4 to check proofs
about Rust programs. It aims to extend Rust's type checking to safety
obligations in `unsafe` code.

> [!NOTE]
> The current MIR-based implementation can install a locally built toolchain
> archive and includes kernel-checked proofs for selected MIR programs.
> End-to-end Rust crate verification is under development.

For example, [`usize::unchecked_div_exact`][unchecked-div] requires a nonzero
divisor and exact divisibility. An annotation could state these requirements
so Anneal can check that callers satisfy them.

```rust
impl usize {
    /// # Safety
    ///
    /// ```anneal
    /// requires(nonzero): rhs != 0
    /// requires(divides): self % rhs == 0
    /// ```
    pub unsafe fn unchecked_div_exact(self, rhs: usize) -> usize;
}

let res: usize = unsafe { 1usize.unchecked_div_exact(0) }; // ERROR: Cannot prove `rhs != 0`
```

*Support for this example is in development. The annotation syntax may change.*

Read the [project principles](PRINCIPLES.md) for Anneal's correctness
promise and the [developer guide](docs/README.md) to build and test the
current verifier. The guide also links to the [historical V1 and V2
workspaces](docs/README.md#historical-workspaces).

[unchecked-div]: https://doc.rust-lang.org/std/primitive.usize.html#method.unchecked_div_exact
