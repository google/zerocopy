<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal

Anneal is a verification framework for proving the correctness of Rust programs in Lean 4. It emphasizes proof that programs do not exhibit *undefined behavior* (i.e., programs are "UB-free"), and empowers developers to assert and prove other properties they consider to be part of program correctness without obliging Rust developers to learn Lean 4.

# Some things we believe

Rust developers deserve programs that are correct. As the Rust aphorism goes, *if it compiles, it works*. Anneal is built to extend this aphorism beyond safe Rust (to unsafe Rust) and beyond memory safety (to other safety or correctness properties). Anneal's approach to this extension is built on several hypotheses about Rust development.

## Well-defined behavior is non-negotiable

Almost nothing can be proven about programs that may exhibit UB.[^1] Although Anneal may support ways of disabling other obligations, UB-freedom is a feature that is *always on*.[^2]

## If a programmer can write a Rust program that is correct, then–given the right tools–they can also prove it is correct

Every programmer has a theory of why they *think* their program is correct; that theory is the reason they wrote it in the first place! Anneal aims to build on developers' existing intuitions about the Rust type system; unsatisfied proof obligations are surfaced using language and presentation that resemble Rust compiler errors to explain why a program fails to uphold a property Anneal has been asked to prove. In this way, Anneal's interface is like an extension of the Rust type system for statements like "behavior is well-defined", and "satisfies developer-defined requirements".

### Given the right tools, Rust programmers can write `unsafe` programs with confidence

This claim is a corollary of the above two hypotheses. If Anneal emits compiler errors for programs that may exhibit UB, and those errors explain how to fix the problem, then Rust developers should be just as confident and productive using Anneal to write `unsafe` Rust as they are using `rustc` to write safe Rust.

# Anneal's promise to its users

One of Anneal's outputs is a *TCB audit log*, a list of code and assumptions Anneal trusts (including itself) to compile your code and prove it correct. Anneal's promise is this:

***If** the code in your TCB audit log is correct, its assumptions are valid, **and** Anneal emits no errors, **then** your code is correct.*

This commitment means that if you write code that Anneal cannot reason about, *it will not compile*. Anneal will never “fail open.” It also means that if Anneal emits no errors, then either:

1. There is a bug or invalid assumption in the TCB (Anneal, Lean, etc.), or  
2. The program behaves as promised.[^3]

# How we make decisions about Anneal

The team behind Anneal strives to uphold a handful of principles that govern its development:

1. **First support all Rust *programmers*; then support all program *behaviors*[^4]**. Rust developers will only be interested in, confident with, and productive using Anneal if it works for them. This principle represents our preference to prefer usability above completeness.  
2. **Don't break promises**. As Anneal evolves, it should not violate its "If ... and ... then ..." promise.  
3. **Don't foreclose increasing expressive power**. Of course, Anneal does not support specifying and proving all possible properties of Rust programs. That said, we will always want to add more. That's why we prefer specification and proof designs that are open to future extension.  
4. **Prefer depth of understanding over point solutions**. Though feature development is rooted in practical examples, we prefer to identify the broader pattern "known use cases" represent. Our experience in other projects suggests this approach often reveals unexpected insights that benefit our users.

[^1]: &nbsp;One might expect that useful properties can be proven about the behavior of such programs during the window before UB is triggered, but unfortunately the definition of UB and methods applied by compilers is even worse: compilers that perform aggressive optimizations under the assumption that UB cannot occur may disrupt the behavior of a program before the offending instruction is executed. This means that, if a particular execution exhibits UB, the semantics of the *entire* execution is not well-defined.

[^2]: &nbsp;Anneal may support *development-only* options that bypass UB checks or turn them into warnings, but such features will clearly label the results and TCB log as tainted or irreparably untrustworthy.

[^3]: &nbsp;Of course, "as promised" is not guaranteed to mean "as the programmer expects" in the face of user error that misconstrued developer-defined requirements.

[^4]: &nbsp;It is a *non-goal* for Anneal to support all Rust *programs*. Technically, Anneal aims to support all program *behaviors*: there may be certain dark corners of rust operational semantics or ways of combining rust features that Anneal never intends to support. In such cases, though, Anneal should give actionable guidance on strategies that can achieve the same behavior by different (and less risky) means.
