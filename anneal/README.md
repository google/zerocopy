<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

<img src="v1/docs/images/logo.svg" width="100%" alt="Anneal logo">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

Rust lets you express many safety requirements in types. When you write
`unsafe` code, some requirements live in safety comments. Anneal aims to make
those requirements explicit and use Lean 4 to check that your code meets them.

> [!NOTE]
> The current MIR-based implementation can install a locally built toolchain
> archive and includes kernel-checked proofs for selected MIR programs.
> End-to-end Rust crate verification is under development.

## From safety comments to proof obligations

Consider [`usize::strict_div`][strict-div]. Its safe interface can accept any
pair of `usize` values. If the divisor is zero, the function panics.

Now consider [`usize::unchecked_div_exact`][unchecked-div-exact]. The caller
must ensure that the divisor is nonzero and that it divides the dividend
exactly. Both operands can have type `usize` even when, as in this call,
they violate the safety contract.

```rust
let res: usize = unsafe { 1usize.unchecked_div_exact(0) }; // Undefined behavior
```

Anneal's goal is to let developers state such preconditions as annotations and
prove that verified calls satisfy them. The example below states both
preconditions.

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

let res: usize = unsafe { 1usize.unchecked_div_exact(0) }; // Cannot prove `rhs != 0`
```

*Support for this example is in development. The annotation syntax may change.*

| | Rust | Anneal's design |
| --- | --- | --- |
| **Developer checks** | `cargo check` | Rust checks and verification of the covered code |
| **Requirements** | Rust types and the contracts of unsafe operations | Rust types, baseline soundness, and stated specifications |
| **Guarantee** | Sound safe interfaces prevent callers from triggering undefined behavior through safe code | Successful verification establishes that the covered code is free of undefined behavior and meets its stated specifications, provided the trusted code is correct and the logged assumptions are valid |
| **Trusted base** | The compiler, platform, and unsafe code behind safe interfaces | The Rust and Anneal toolchains, the Lean kernel, and any additional trusted code or assumptions recorded in the TCB audit log |

External code, such as a C function called through FFI, may require trusted
assumptions about its behavior. Anneal's design calls for recording these in
the TCB audit log so callers can be verified under explicit assumptions. See
the [correctness promise](PRINCIPLES.md#anneals-promise-to-its-users) and
[threat model](THREAT_MODEL.md) for what a verification result covers and what
maintainers review.

## Development philosophy

Verification should fit into the normal Rust development loop. When you write
an unsafe operation, you already need to explain why its safety contract holds.
Anneal aims to let you express that reasoning as a specification and check it
as the code changes, locally and in CI.

## Try Anneal

Start with [Developing Anneal](docs/README.md) to build the current verifier's
toolchain and run its repository checks. The runnable [V1 prototype](v1/)
includes a verification walkthrough. The historical [V2 workspace](v2/)
builds the Aeneas toolchain used by V1.

[strict-div]: https://doc.rust-lang.org/std/primitive.usize.html#method.strict_div
[unchecked-div-exact]: https://doc.rust-lang.org/std/primitive.usize.html#method.unchecked_div_exact
