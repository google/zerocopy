# Anneal

<img src="docs/images/logo.svg" width="100%">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

> **Note:** Anneal is currently in pre-alpha. You're welcome to use it, but many things
> are broken or unsound, and we will change APIs frequently.

Anneal enables "literate verification" of safe and `unsafe` code. It allows you to write specifications and proofs of correctness and soundness directly within your Rust source files using standard documentation comments.

Anneal is designed for use by both human engineers and AI coding agents. By providing machine-checked guarantees for safe and `unsafe` code, Anneal eliminates the cognitive burden of manual review and enables the safe acceleration of systems software development. We have [demonstrated](https://drive.google.com/file/d/1areyf438L0izETTHj7PRMnoSHSX4kM29/view?usp=sharing) that Antigravity can author `unsafe` Rust code and prove its soundness using Anneal.

Without Anneal:

```rust
struct PositiveUsize {
    // INVARIANT: x > 0
    x: usize,
}

impl PositiveUsize {
    /// Creates a new `PositiveUsize` if `x > 0`.
    pub fn new(x: usize) -> Option<Self> {
        if x > 0 {
            // SAFETY: We checked that x > 0.
            Some(Self { x })
        } else {
            None
        }
    }
}

impl std::ops::Div<PositiveUsize> for usize {
    type Output = usize;

    fn div(self, rhs: PositiveUsize) -> Self::Output {
        // SAFETY: The type invariant of `PositiveUsize` guarantees that
        // `rhs.x > 0`. This makes division by zero impossible.
        unsafe { std::intrinsics::unchecked_div(self, rhs.x) }
    }
}
```

With Anneal:

```rust
/// ```anneal
/// isValid self := self.val.val > 0
/// ```
pub struct PositiveUsize {
    pub val: usize,
}

impl PositiveUsize {
    /// Creates a new `PositiveUsize` if `x > 0`.
    ///
    /// ```anneal
    /// ensures:
    ///   match ret with
    ///   | none => x.val = 0
    ///   | some r => r.val.val = x.val
    /// ```
    pub fn new(x: usize) -> Option<PositiveUsize> {
        if x > 0 {
            Some(Self { val: x })
        } else {
            None
        }
    }
}

/// ```anneal
/// proof (h_progress):
///   unfold div_positive
///   rcases h_req with ⟨h_self_val_is_valid, h_rhs_is_valid⟩
///   have ho := unchecked_div.spec self_val rhs.val {
///     h_a_is_valid := h_self_val_is_valid
///     h_b_is_valid := by verify_is_valid h_b_is_valid _root_.positive_usize.div_positive
///     h_anon := by simp_all [Anneal.IsValid.isValid]
///   }
///   rcases Aeneas.Std.WP.spec_imp_exists ho with ⟨y, h_eq, _⟩
///   exact ⟨y, h_eq⟩
/// ```
fn div_positive(self_val: usize, rhs: PositiveUsize) -> usize {
    unsafe { self_val.unchecked_div(rhs.val) }
}

impl std::ops::Div<PositiveUsize> for usize {
    type Output = usize;

    fn div(self, rhs: PositiveUsize) -> usize {
        unsafe { unchecked_div(self_val, rhs.val) }
    }
}
```

## Installation

Install Anneal and its required toolchains (Charon and Aeneas):

```bash
cargo install cargo-anneal@0.1.0-alpha.17
cargo anneal setup
```

## Quick Start

Write a specification for your function using Anneal annotations in a doc comment:

```rust
/// ```anneal
/// requires: x.val < Usize.max
/// ensures: ret.val = x.val + 1
/// proof:
///   scalar_tac
/// ```
pub fn add_one(x: usize) -> usize {
    x + 1
}
```

Verify your crate:

```bash
cargo anneal verify
```

## Usage & Commands

Anneal wraps the underlying tools to provide a seamless experience:

- **`cargo anneal verify`**: Verifies the target crate.
- **`cargo anneal expand`**: Outputs the generated Lean code without running full verification (useful for debugging).
- **`cargo anneal generate`**: Generates the `.lean` files on disk, allowing you to iterate on proofs using standard Lean tooling before copying them back to Rust source.
