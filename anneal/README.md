# Anneal

<img src="https://raw.githubusercontent.com/google/zerocopy/main/anneal/docs/images/logo.svg" alt="Anneal logo" width="100%">

<p align="center"><em>logo by <a href="https://www.instagram.com/tinyneonspark">tinyneonspark</a></em></p>

> **Note:** Anneal is in alpha. You're welcome to use it, but many things
> are broken or unsound, and we will change APIs frequently.

> [!NOTE]
> The MIR-based alpha installs a toolchain from a published or locally built
> archive and uses Lean's kernel to check proofs for selected Rust functions or
> scalar library crates. General crate verification is under development. The
> design discussion and examples below describe Anneal's goals. Verification
> guarantees depend on trusted code being correct and the assumptions in the
> verification receipt being valid.

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

*Support for this example is in development. The annotation syntax may change.*

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

Anneal is designed for use by both human engineers and AI coding agents.
Machine-checked proofs reduce the amount of code reviewers check by hand.
Human reviewers assess specifications and trusted assumptions. We have
[demonstrated](https://drive.google.com/file/d/1areyf438L0izETTHj7PRMnoSHSX4kM29/view?usp=sharing)
that Antigravity can author `unsafe` Rust code and prove its soundness using
Anneal.

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

## Try the alpha

The alpha verifies selected Rust functions or dependency-free scalar library
crates on x86-64 Linux with glibc. Follow the [alpha guide][alpha-guide] to
install it and check a runnable proof.

[alpha-guide]: https://github.com/google/zerocopy/blob/main/anneal/docs/alpha.md

## Agent skill

Run `cargo anneal skill` to print the bundled `SKILL.md` without setting up
the Anneal toolchain.

To make the skill discoverable before an agent runs `cargo anneal`, install it
with [GitHub CLI][gh-skill]. Set `ANNEAL_REV` to the release tag or source
commit for your `cargo-anneal` build and run this from your project's Git
repository.

```sh
gh skill install google/zerocopy \
  anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md \
  --agent codex --scope project --pin "${ANNEAL_REV:?set the source revision}"
```

Choose the `--agent` value for your host. Commit the installed skill to share
it with teammates and agents working in fresh checkouts.

[gh-skill]: https://cli.github.com/manual/gh_skill_install

## Repository checks

See the [contributor guide][developing-anneal] to build the local toolchain
archive and audit the trust boundary, the [scaffold guide][scaffold-guide] to
run installed smoke cases and reproduce retained failures, and the
[Codex review guide][codex-review] for required merge checks.

[developing-anneal]: https://github.com/google/zerocopy/blob/main/anneal/docs/README.md
[scaffold-guide]: https://github.com/google/zerocopy/blob/main/anneal/docs/scaffolding.md
[codex-review]: https://github.com/google/zerocopy/blob/main/anneal/docs/codex-review.md

## Acknowledgments

Anneal builds on decades of work and research in formal verification and the
study of programming languages, among other fields. It is only possible thanks
to the work of countless researchers and software engineers. Some of the most
significant influences are listed here, but this list is far from exhaustive.

- Son Ho and Jonathan Protzenko's [Aeneas] inspired PureLift's translation of
  Rust borrows and updates into pure computations. Early Anneal used Aeneas
  to translate Rust into Lean and [Charon] to extract Rust programs for
  analysis. Charon is by Son Ho, Guillaume Boisseau, Lucas Franceschino, Yoann
  Prak, Aymeric Fromherz, and Jonathan Protzenko. Son Ho, Aymeric Fromherz, and
  Jonathan Protzenko's [work on symbolic borrow checking][symbolic-borrows]
  informed Anneal's study of the semantics behind this translation.
- PureLift uses lawful bidirectional lenses. J. Nathan Foster, Michael B.
  Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt developed
  these foundations in [Combinators for Bidirectional Tree
  Transformations][tree-lenses].
- Anneal's tristate-number (`tnum`) bitwise and carry-propagation transfer
  functions adapt the `tnum` abstract domain formalized by Harishankar
  Vishwanathan, Matan Shachnai, Srinivas Narayana, and Santosh Nagarakatte in
  [Sound, Precise, and Fast Abstract Interpretation with Tristate
  Numbers][tnum-paper] and used in the Linux kernel's eBPF verifier.
- Anneal's proof-lifting experiments drew on Magnus O. Myreen, Michael J. C.
  Gordon, and Konrad Slind's [decompilation into logic][decompilation] to
  reason about one basic block at a time. [Tree Borrows][tree-borrows] by
  Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung guided
  experiments on how to account for mutable borrow permissions.
- Anneal's MIR correspondence proofs use a pinned, patched copy of
  [lean-miri]. Yuichi Nishiwaki's port builds on the Rust compiler's MIR
  interpreter and the work of the [Miri developers and contributors][Miri].
  Ralf Jung's [MiniRust] and the Rust Unsafe Code
  Guidelines contributors' [discussion of moved values][ucg-moves] helped
  inform Anneal's treatment of moves. Xavier Leroy and the [CompCert]
  contributors' work on simulation proofs provided a comparison for how
  Anneal relates its model to its reference semantics.
- [Lean 4], by Leonardo de Moura, Sebastian Ullrich, and the Lean
  contributors, checks Anneal's proofs. Lean's
  [declaration replay][lean-replay], [environment importer][lean-env],
  compiler-attribute handling, and kernel reduction behavior guided Anneal's
  auditor and PureLift's combinators.
- The Rust contributors' [compiler source][rustc] (including
  [`rustc_const_eval`][rustc-const-eval] and [a padding-clearing
  issue][rust-148470]) and [Rust Reference] guided Anneal's MIR capture and
  model of Rust behavior. The earlier memory model also drew on the
  [standard library documentation][rust-std]. The LLVM contributors'
  [language reference][llvm-linkage] guided Anneal's treatment of Rust's
  linkage attributes.
- Early design work drew on
  [research into security risks in Rust][rust-security] by Xiaoye Zheng,
  Zhiyuan Wan, Yun Zhang, Rui Chang, and David Lo. Lars Bergstrom's
  [Rust Nation UK talk][rust-nation], Jeff Vander Stoep's
  [Android delivery data][android-rust], and Hongliang Tian's
  [account of the Asterinas kernel][asterinas] gave the early design concrete
  examples of Rust development and the work involved in writing unsafe code.
- The [Fuchsia] and [Starnix eBPF][starnix-ebpf] contributors' production Rust
  crates and build integration shaped Anneal's out-of-tree verification
  interface and end-to-end verification tests.

[Aeneas]: https://arxiv.org/abs/2206.07185
[Charon]: https://link.springer.com/chapter/10.1007/978-3-031-98685-7_18
[symbolic-borrows]: https://arxiv.org/abs/2404.02680
[tree-lenses]: https://doi.org/10.1145/1232420.1232424
[tnum-paper]: https://arxiv.org/abs/2105.05398
[decompilation]: https://www.cl.cam.ac.uk/~mom22/decompilation/fmcad12.pdf
[tree-borrows]: https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf
[lean-miri]: https://github.com/proofs-rs/lean-miri
[Miri]: https://github.com/rust-lang/miri
[MiniRust]: https://github.com/minirust/minirust
[ucg-moves]: https://github.com/rust-lang/unsafe-code-guidelines/issues/188
[CompCert]: https://compcert.org/
[Lean 4]: https://lean-lang.org/papers/lean4.pdf
[lean-replay]: https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Replay.lean
[lean-env]: https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean
[rustc]: https://github.com/rust-lang/rust/tree/main/compiler
[rustc-const-eval]: https://github.com/rust-lang/rust/tree/main/compiler/rustc_const_eval/src/interpret
[rust-148470]: https://github.com/rust-lang/rust/issues/148470
[Rust Reference]: https://doc.rust-lang.org/reference/
[rust-std]: https://doc.rust-lang.org/std/
[llvm-linkage]: https://llvm.org/docs/LangRef.html#linkage-types
[rust-security]: https://arxiv.org/abs/2308.15046
[rust-nation]: https://www.youtube.com/watch?v=QrrH2lcl9ew
[android-rust]: https://blog.google/security/rust-in-android-move-fast-fix-things/
[asterinas]: https://asterinas.github.io/2025/06/04/kernel-memory-safety-mission-accomplished.html
[Fuchsia]: https://fuchsia.dev/
[starnix-ebpf]: https://fuchsia.googlesource.com/fuchsia/+/823a15538f191b9dbd9ebafaa6ba23220b87d2e1/src/starnix/lib/ebpf/core/src
