# MiniRust

**If you prefer video to text, I recently [presented MiniRust at RustWeek 2025](https://www.youtube.com/watch?v=yoeuW_dSe0o).**
Furthermore, you can check out this [older, but more in-depth presentation of MiniRust for the RFMIG](https://www.youtube.com/watch?v=eFpHadbv34I).

MiniRust is the cornerstone of my vision for a normative specification of Rust semantics.
It is an idealized MIR-like language with the purpose of serving as a "core language" of Rust.
This is part of a larger story whose goal is to precisely specify the operational behavior of Rust, i.e., the possible behaviors that a Rust program might have when being executed:
the behavior of a Rust program is defined by first translating it to MiniRust (which is outside the scope of this repository), and then considering the possible behaviors of the MiniRust program as specified in this document.
That translation does a *lot* of work; for example, traits and pattern matching are basically gone on the level of MiniRust.
On the other hand, MiniRust is concerned a lot with details such as the exact evaluation order, data representations, and precisely what is and is not Undefined Behavior.

To separate the complexities of memory from the semantics of MiniRust statements and expressions, we introduce the MiniRust *memory interface*:
think of memory as implementing some trait; MiniRust semantics is generic over the actual implementation of that trait.
The interface between the MiniRust language (specified in `lang`) and its memory model (specified in `mem`) is *untyped and byte-oriented* (but "bytes" are a bit more complex than you might expect).
For now, we only define the memory interface, but do not give an implementation.
Even without deciding what exactly the final memory model will look like, we can answer a surprising amount of interesting questions about Rust semantics!

On the MiniRust language side, the most important concept to understand is that of a *value* and how it relates to *types*.
Values form a high-level, structural view of data (e.g. mathematical integers); types serve to relate values with their low-level byte-oriented representation.
Types are essentially just parameters attached to certain operations to define the (de)serialization format.
Well-formedness of a MiniRust program ensures that expressions and statements satisfy some basic typing discipline, but MiniRust is by design *not* type-safe.

## specr lang: the language used to define MiniRust

The most precise way to write down the MiniRust spec would be with mathematical notation.
However, without LaTeX this is a pain, and it also involves a lot of jargon which hurts accessibility of the spec.
That's why the MiniRust spec is written as an *interpreter*, so the spec itself is code.
That begs the question, which language do we write that code in?
We are using a kind of "Rust-like pseudo-code" called *specr lang*:
imagine Rust without all the restrictions about sizedness and pointer indirections for recursive types (we could implicitly insert `Arc` where needed).
We use generic type names like `List`, `Map`, `Set` rather than concrete implementations like `Vec`, `HashMap`, `HashSet`, since the implementation details do not matter.
We also assume some "obvious" language extensions -- basically, it should always be clear what is meant to anyone with some Rust experience, even if this is not actually legal Rust.

All types except for mutable references are `Copy` (let's just imagine we implicitly `Clone` where needed), and we use `fn(T) -> U` notation even for closures that can capture arbitrarily.

We use `panic!` (and `unwrap` and slice indexing and similar standard Rust operations) to indicate conditions that should always hold; if execution ever panics, that is a bug in the specification.

Our functions are generally pure; they can write to mutable references, but we can consider this to be implemented via explicit state passing.
When we do need other effects, we make them explicit in the return type.
The next sections describe the effects used in the MiniRust interpreter.

### Fallible operations

We use `Result` to make operations fallible (where failure indicates UB or machine termination).
We use a `throw_ub!` macro to make the current function return a UB error value, and `throw_machine_stop!` to indicate that and how the machine has stopped.
Similarly, we use `throw!()` inside `Option`-returning functions to return `None`.
In order to wrap a value `t: T` as `Result<T>`, `Option<T>` or `NdResult<T>` (see next subchapter), we use the function `ret(t)`.
See [the prelude](spec/prelude/main.md) for details.

### Non-determinism

We also need one language feature that Rust does not have direct support for: non-determinism.
The return type `Nondet<T>` indicates that this function picks the returned `T` (and also its effect on `&mut` it has access to) *non-deterministically*
This is only used in the memory model; the expression language is perfectly deterministic (but of course it has to propagate the memory model's non-determinism).
In a function returning `Nondet`, we use `?` for monadic bind (this is more general than its usual role for short-circuiting), and the return value is implicitly wrapped in monadic return.

The function `pick<T>(impl Distribution<T>, fn(T) -> bool) -> Nondet<T>` will return a value of type `T` such that the given closure returns `true` for this value.
This non-determinism is interpreted *daemonically*, which means that the program has to be correct for every possible choice.
In particular, if the closure is `|_| false` or `T` is uninhabited, then this corresponds to "no behavior" (which is basically the perfect opposite of Undefined Behavior, and also very confusing).
For the purpose of making the spec executable, `pick` also receives a `Distribution` argument.
This argument does not affect the set of possible program behaviors, it is purely a hint for the interpreter to sample suitable candidates.

Similar to `pick`, the function `predict<T>(fn(T) -> bool) -> Nondet<T>` also returns a `T` satisfying the closure, but this non-determinism is interpreted *angelically*, which means there has to *exist* a possible choice that makes the program behave as intended.
In particular, if the closure is `|_| false` or `T` is uninhabited, then this operation is exactly the same as `hint::unreachable_unchecked()`: no possible choice exists, and hence ever reaching this operation is Undefined Behavior.

The combined monad `Nondet<Result<T>>` is abbreviated `NdResult<T>`, and in such a function `?` can also be used on computations that only need one of the monads, applying suitable lifting:
`Result<U> -> NdResult<U>` is trivial (just use monadic return of `Nondet`); `Nondet<U>` -> `NdResult<U>` simply maps `Ok` over the inner computation.

### MiniRust vs specr lang

So just to be clear, there are *two* Rust dialects at play here:

- *MiniRust* is the "Rust core language", the main subject of this project.
  In logician's terms, this is the "object language".
  It has all the nasty features of unsafe Rust and comes with an interpreter that describes what exactly happens when a program is executed, but it would be awful to program in as it lacks any convenience.
  It doesn't even have concrete syntax; all we really care about is the abstract syntax (the data structure that represents a MiniRust program: statements, expressions, ...).
- *specr lang* is the programming language that the MiniRust interpreter itself is written in.
  In logician's terms, this is the "meta language".
  It is a fully safe Rust-style language, and the intention is that the meaning of a specr lang program is "obvious" to any Rust programmer.
  The tool `specr-transpile` can translate specr lang into Rust, so that we can run and test the MiniRust interpreter.
  In the future, we'll hopefully have tools that can translate specr lang into the formal language of a theorem prover like Coq, so that we can establish formal proofs about the MiniRust specification.

## Status

MiniRust is extremely incomplete!
Some features are entirely missing (e.g. floats).
There are lots of TODOs.
The language syntax is also missing many of the Rust operators and casts.
I hope to slowly chip away at all this over time.
If you want to help, please talk to me -- PRs to add missing features are very welcome. :)
But we also need to ensure the entire document stays coherent, and I already have vague ideas for many of these things.

- TODO: establish global variable name conventions. Do we use `v: Value`, `val: Value`, `value: Value`?
  What do we use for `ValueExpr`? Similar questions exist around `Place`/`PlaceExpr` and `ty: Type`/`type: Type`.

## Table of Contents

* [Prelude](spec/prelude/main.md): common definitions shared by everything
  * [Target Parameterization](spec/prelude/target.md): defines which parameters are controlled by the target
* MiniRust memory
  * [Pointer](spec/mem/pointer.md): the definition of what even is a pointer in MiniRust
  * [Memory interface](spec/mem/interface.md): the API via which the MiniRust Abstract Machine interacts with memory
  * [Basic memory model](spec/mem/basic.md): an implementation of the memory interface that ignores aliasing concerns
  * [Tree Borrows memory model](spec/mem/tree_borrows/memory.md): an alternative implementation of the memory interface that abstracts reborrowings as a *tree*.
  * [Integer-pointer cast model](spec/mem/intptrcast.md): a memory-model independent way of defining integer-pointer casts
* MiniRust language
  * [Prelude](spec/lang/prelude.md): common definitions and parameters of the language
  * [Values](spec/lang/values.md): the domain of high-level MiniRust values
  * [Types](spec/lang/types.md): the set of MiniRust types
  * [Representation relation](spec/lang/representation.md): how types (de)serialize values into/from memory
  * [Syntax](spec/lang/syntax.md): the abstract syntax of MiniRust programs
  * [Well-formedness](spec/lang/well-formed.md): the requirements for well-formed types and programs
  * [Abstract Machine](spec/lang/machine.md): the state that makes up a MiniRust Abstract Machine as well as the definitions of the initial state and the non-deterministic state transition function
  * The definition of how to evaluate a single machine step is the heart of MiniRust, and spread across multiple files
    * [Statement evaluation](spec/lang/step/statements.md)
    * [Terminator evaluation](spec/lang/step/terminators.md)
    * [Expression evaluation](spec/lang/step/expressions.md)
    * [Operator evaluation](spec/lang/step/operators.md)
    * [General intrinsics](spec/lang/step/intrinsics.md)
    * [Lock intrinsics](spec/lang/step/locks.md)

## Relation to other efforts

### What about a-mir-formality?

You might wonder how this project compares to Niko's [a-mir-formality](https://github.com/nikomatsakis/a-mir-formality/).
The obvious answer is that Niko is much better at picking names. ;)

On a more serious note, these projects have very a different scope: MiniRust is *only* about the operational semantics.
a-mir-formality is a lot more ambitious; as the [inaugural blog post](https://nikomatsakis.github.io/a-mir-formality/blog/2022/05/12/) explains, it aims to also formalize traits, type checking, and borrow checking -- all of which I consider out-of-scope for MiniRust.
a-mir-formality is machine-readable and written in PLT redex; MiniRust uses pseudo-code that is not currently machine-readable (but I have ideas :).
The primary goals of MiniRust are to be precise and human-readable; I would argue that while PLT redex is more precise than the style I use, it does lack in readability when compared with Rust-style pseudo-code.
I am willing to sacrifice some precision for the significant gain in readability, in particular since I think we can recover this precision with some amount of work.
And finally, the "operational semantics" layer in a-mir-formality is "not even sketched out yet", so as of now, the projects are actually disjoint.
If and when a-mir-formality obtains an operational semantics, my hope is that it will be basically the same as MiniRust, just translated into PLT redex.
(Niko writes this layer of a-mir-formality is "basically equivalent to Miri"; MiniRust is basically an idealized Miri, so I think this would work well.)

### What about the Ferrocene Language Specification?

Recently, Ferrocene announced a first draft of their [Ferrocene Language Specification](https://github.com/ferrocene/specification).
Aiming to make Rust viable in safety-critical domains, their specification is intended as a document to validate an implementation against.

It is very different in style and scope from MiniRust:
it aims at describing the *surface language* Rust, not just a core language, and also covers things like syntax and borrow checking; all of these are out of scope for MiniRust.
Furthermore it is written in English, in an axiomatic style, somewhat akin to the C/C++ specifications.
English is notoriously ambiguous, but they are working with the folks from AdaCore, so they have a lot of experience in "how to write a precise spec".
And I have to say, their document is quite impressive!
In terms of consistent use of terminology and ease of navigation, MiniRust has a lot of catching up to do.
Still, from my experience doing research in formal methods and programming languages, there's a big gap between even a well-made English-language specification like theirs and an unambiguous formal specification in the mathematical sense.
Furthermore, the style of specification used by C/C++ and also Ferrocene is *axiomatic*, meaning it states a whole bunch of rules that all should be true about each program execution.
It's basically a long wishlist.
The big problem with that style is that it is very easy to specify rules that contradict each other, to forget to specify some rules, or to introduce effects in your semantics that you don't even realize are there.
(Wishes gone wrong is a fantasy trope for a reason...)
For example, C/C++ have a notion of "pointer provenance", but the specification does not even mention this crucial fact, and completely fails to say how pointer provenance interacts with many other features of the language.
Yet, without pointer provenance, one simply [cannot explain](https://www.ralfj.de/blog/2020/12/14/provenance.html) some aspects of these languages.
That's why I strongly prefer an *operational* semantics, which describes the behavior of a program in a [step-by-step process](spec/lang/step).
Operational semantics *have to* make things like pointer provenance explicit, they cannot cheat and entirely omit crucial parts of what is needed to describe program behavior.
One of the biggest things missing from the C/C++ specification, in my opinion, is the equivalent of the [MiniRust Machine declaration](spec/lang/machine.md): an exhaustive list that makes up everything needed to describe the state of the Abstract Machine.

But of course, it is perfectly possible to have *both* an operational and an axiomatic specification.
And ideally they will say the same thing. :)
Right now, to my knowledge the Ferrocene Spec does not go into a lot of detail on the questions MiniRust is most interested in exploring (the interplay of places and values, value representations, padding and uninitialized memory, pointer provenance); once they start exploring that, I am curious what they will propose and how it relates to the answers MiniRust is giving to these questions.

### What about Miri?

MiniRust is, at least conceptually, very similar to [Miri](https://github.com/rust-lang/miri).
You can think of it as an "idealized Miri": if Miri didn't have to care about working with all the rustc data structures that represent MIR and types, and cared about neither performance nor diagnostics, then it would be implemented like this specification.
There are some [differences between Miri and MiniRust](https://github.com/rust-lang/miri/issues/2159); these are generally Miri bugs and I intend to slowly chip away at the remaining (tricky) ones.

### How does this relate to the reference?

The Rust Reference contains a [list of Undefined Behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
The intention is that MiniRust has no more UB than that, but it *does* have less UB in some situations:

- It is *not* UB to dereference a null, unaligned, or dangling raw pointer. In other words, `addr_of!(*ptr)` is always defined.
  However, if the `*ptr` place expression is being offset, that still needs to happen in-bounds, and actual loads/stores need to be sufficiently aligned.
- It is *not* always UB to create a reference or `Box` to an invalid value.
  However, it *is* UB to create a reference or `Box` to an *uninhabited type*, or one that is dangling or unaligned.
  Moreover, when evaluating an `&[mut]` value expression, dangling references are UB.
  (Dangling references nested in fields will likely also become UB when the aliasing model is added.)

To my knowledge, rustc does not currently exploit those cases of UB, so changing the reference to match MiniRust would be a specification-only change.
Miri matches MiniRust on the second point, but enforces the stricter rules of the reference for the first point.
