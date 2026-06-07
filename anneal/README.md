# Anneal

<img src="docs/images/logo.svg" width="100%">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

> **Note:** Anneal is currently in pre-alpha. You're welcome to use it, but many things
> are broken or unsound, and we will change APIs frequently.

For safe code, Rust promises that "if it compiles, then it is memory-safe." Anneal promises the same for unsafe code.

Rust promises that all safe Rust code is free of memory safety bugs. It does this by encoding the requirements for memory safety in the type system, ensuring that if a program type checks, then it is free of memory safety bugs. The lifetime system prevents use-after-free bugs, the ownership system prevents double-free bugs, and so on. **There do not exist type-checked safe Rust programs with memory safety bugs.**[^1] The same is not true of unsafe Rust code. **There do exist type-checked unsafe Rust programs with memory safety bugs.**

[^1]: Barring compiler and platform bugs, which do exist.

One way to understand this distinction is that a safe Rust function must be free of memory safety bugs *no matter what value is passed in*. Consider [`usize::strict_div`](https://doc.rust-lang.org/std/primitive.usize.html#method.strict_div):

```rust
impl usize {
    /// # Panics
    /// 
    /// This function will panic if `rhs` is zero.
    pub fn strict_div(self, rhs: usize) -> usize;
}
```

A safe implementation of `strict_div` would be forced to handle *all possible values* of `self` and `rhs`. `strict_div` must handle the case where `rhs == 0` (division by zero). It could choose to return an arbitrary `usize` or, as it does in practice, panic. But it cannot exhibit a memory safety bug – Rust would prevent such a program from compiling.

By contrast, consider the unsafe [`usize::unchecked_div_exact`](https://doc.rust-lang.org/std/primitive.usize.html#method.unchecked_div_exact):

```rust
impl usize {
    /// # Safety
    /// 
    /// This results in undefined behavior when `rhs == 0` or `self % rhs != 0`.
    pub unsafe fn unchecked_div_exact(self, rhs: usize) -> usize;
}
```

Rust doesn't have any way to epxress "a pair of `usize`s such `rhs != 0` and `self % rhs == 0`". Thus, the type signature of `unchecked_div_exact` is *too permissive*. While it prevents some illegal values statically (e.g., the type system will not permit you to pass `-1`), some illegal values will compile just fine, and will result in memory safety bugs at runtime:

```rust
let res: usize = unsafe { 1usize.unchecked_div_exact(0) };
```

In this view, unsafe Rust differs from safe Rust in that **some type-safe values are still illegal**, while in safe Rust, **all type-safe values are legal** (where "illegal" means "will result in a memory safety bug").

As we saw before, Rust ensures that **no type-checked safe Rust programs contain memory safety bugs.** Anneal provides the same promise, but for unsafe Rust code. Just as Rust encodes memory safety requirements in its types, Anneal encodes memory safety requirements in its annotations. Unlike Rust types, Anneal annotations are powerful enough to prevent *any* illegal values from compiling, even in unsafe code. In this sense, Anneal annotations are an *extension* to Rust's type system.

For example, here's how Anneal would encode the safety precondition of `unchecked_div_exact`, preventing buggy programs from compiling:

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

Anneal removes most `unsafe` code from your [trusted computing base](https://en.wikipedia.org/wiki/Trusted_computing_base) (TCB).*

| | Rust | Anneal |
|-| ---- | ------ |
| | `cargo check` | `cargo anneal verify` |
| **Types** | Rust types | Rust types + Anneal annotations |
| **Guarantee** | Safe code is free of memory safety bugs | Safe and unsafe code is free of memory safety bugs* |
| **Caveat** | Unsafe code is unchecked | Code outside of the Rust Abstract Machine (AM) is unchecked* |
| **TCB** | Rust toolchain, unsafe code | Rust + Anneal toolchains, code outside of the Rust AM* |

\* *Anneal cannot verify the soundness of code constructs which exist outside of the Rust Abstract Machine (AM), such as FFI or inline assembly. The programmer must axiomatically assert the behavior of this code, and it remains in the TCB. Note that Rust code which **calls** these constructs (e.g., code which calls a function implemented in C) **can** be verified – Anneal removes this code from the TCB.*

### Development Philosophy

Anneal is a [formal verification](https://en.wikipedia.org/wiki/Formal_verification) tool. However, it diverges from many formal verification tools in its philosophy for how it should be used by end users.

While exceptions exist, the most common form of formal verification has historically been *post-hoc verification*, in which verification is applied to a software artifact which already exists and which was not specifically written with verification in mind. This approach comes with a number of assumptions and limitations which we aim to sidestep:
1. Assumes that verification requires distinct expertise which developers lack
2. Verification is applied to a codebase whose structure may not be amenable to verification
3. Results in long iteration cycles, in which feedback from verification is obtained long after a line of code is written
4. Without extra infrastructure (e.g. in CI), software codebase and verification artifacts (specifications and proofs) can drift, requiring periodic efforts to update the verification to "catch up" with recent code changes

We believe that all of these can be addressed by thinking of specifications as merely an extension to the type system rather than a parallel artifact. In particular:
1. Developers already have justifications – albeit undocumented – for their belief that their code is correct. Type annotations simply ask them to make these justifications explicit
2. As with any form of static typing, Anneal annotations will shape the codebase and nudge developers towards certain patterns for code organization which are more amenable to verification. This nudging will happen in the developer's inner loop and so will be much more effective than feedback from post-hoc verification
3. We expect `cargo anneal verify` to be just as frequent as `cargo check`, and so iteration cycles are extremely short
4. CI can simply run `cargo anneal verify` to ensure that specifications and proofs never drift or bit rot

### Human and Agentic Development

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
cargo install cargo-anneal@0.1.0-alpha.24
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

- **`cargo anneal verify`**: Verifies the target crate.
- **`cargo anneal expand`**: Outputs the generated Lean code without running full verification (useful for debugging).
- **`cargo anneal generate`**: Generates the `.lean` files on disk, allowing you to iterate on proofs using standard Lean tooling before copying them back to Rust source.
