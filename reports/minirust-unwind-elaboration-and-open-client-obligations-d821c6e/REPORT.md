# Unwinding, elaboration and open-library obligations around MiniRust

## Summary

The examined MiniRust core implements unwind payload stacks and Start/Stop/ResumeUnwind. Its Rust translator nevertheless contains a narrower destructor-call seam: the MIR Drop branch emits a call with no unwind continuation. Core unwind support therefore cannot establish safety-reflecting source drop elaboration.

A safe native probe preserves actual partial-move and destructor-unwind cleanup traces plus MIR. Static elaboration and safe-client linking need explicit proofs that bind resolved operations, generated cleanup, implementation dictionaries and every relevant exit to the selected dynamic semantics.

## Applicability

Source-inspected MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`; a-mir-formality README at `71dc31c1b186df1f0a64d8464b8103195902a5a5`; Rust Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`; and archived RustBelt POPL 2018 source identified by SHA-256 in metadata. The Fukala thesis identifies commit `120d9b3d1e868ddd00ce9163b2bb53d099154247`; its GitLab source was inaccessible, so theorem completeness is reported from the thesis, not a fresh assumption audit.

Native execution used rustc 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, aarch64-apple-darwin, edition 2021, opt-level 0 and panic=unwind. It is a safe Rust specimen compiled by that toolchain, not the older toolchain requested by minimize. No minimize execution or end-to-end equivalence is claimed.

## Findings

### F1. Core unwind control is present and affects alias restoration

Basis: **source**.

StartUnwind evaluates a thin raw payload pointer, pushes it onto the current thread's payload stack and enters cleanup. StopUnwind pops one payload, rejects an empty stack and enters a regular block. ResumeUnwind pops the frame, deallocates its locals, invokes `mem.end_call(frame.extra)`, then follows the caller's unwind continuation. Unwinding out of the bottom frame or through a call without an unwind block is UB. Return likewise deallocates locals and ends the memory-model call before passing its return value back. [Terminators](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/terminators.md#L405), [thread payload state](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/machine.md#L109).

Well-formed block kinds distinguish regular, cleanup, catch and terminate regions. StorageDead deallocates a local's backing storage; it is not itself source destructor invocation. Tree Borrows `end_call` releases every frame protector and can fail. Thus “callee unwinds” is not an unconditional rule that the caller regains all old permissions. The exceptional contract must account for cleanup effects and the same alias exit hook as normal return. [Block kinds](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/syntax.md#L503), [storage operations](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/statements.md#L160).

### F2. The translator's destructor-unwind boundary is concrete

Basis: **source** + **execution** of a source specimen.

The minimize branch `TerminatorKind::Drop { place, target, .. }` selects either static drop glue or a trait-object drop function and emits a MiniRust Call with `unwind_block: None`. It does not preserve the matched MIR Drop unwind action. Ordinary calls and Assert have translated unwind actions; `translate_panic` creates StartUnwind for unwind strategy, but substitutes a null/unit payload and documents bypass of the actual panic runtime. Catch-unwind lowering exists. UnwindTerminate, Yield and CoroutineDrop terminators are explicitly rejected. [Drop branch](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#L220), [panic lowering](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#L619).

The safe native probe deliberately catches two expected panics and emits:

```text
partial_caught=true;drops=["left", "right", "outer"]
destructor_caught=true;drops=["body", "bomb", "outer"]
binding_drop_order=["wildcard", "after_wildcard", "after_binding", "binding"]
callback_fields=7,9
selected_impls=1,2
```

The first case moves and explicitly drops one tuple field, then unwinds; only the remaining field and outer token are cleaned up. The second implicitly drops Bomb, whose destructor panics; the enclosing catch still observes the outer token's cleanup. Preserved MIR `main::{closure#2}`, bb7, has `drop(_5) -> [return: bb8, unwind: bb12]`; bb12 drops the outer token then resumes. This is exactly the kind of edge discarded by the inspected minimize branch.

This establishes a meaningful unsupported correspondence boundary at the source branch, not a tested minimize misexecution: the Rust compiler and minimize toolchains differ, and other unsupported constructs in the specimen could stop translation first. No invalid Rust was run. A second panic during destruction was not executed.

### F3. The drop-elaboration thesis has two different proof scopes

Basis: **documentation** of a formal development.

Fukala's thesis §5.3 states equivalence of terminating pre-/post-elaboration body executions for arbitrary heaps and arguments, given well-typed body, global call context and argument assignment. Its tuple-support version has a proof skeleton relying on unproved lemmas; an earlier scalar-only version has a complete proof. The model abstracts the heap and calls, omits enums and unwinding, and does not verify rustc. Whole-program composition is future work. These are not equivalent to preservation of every unsafe or exceptional execution prefix. [Thesis §§3, 5.3–5.4, 6.1, Appendix A](https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Viktor-Thesis.pdf).

A future safety-reflecting elaboration theorem must additionally preserve the observations used to detect invalid cleanup, including partial initialization/moves, destructor side effects, alias permissions, abort/double-panic outcomes and reentrant calls. Equivalence restricted to completed runs cannot independently rule out a source UB prefix that prevents completion. This is a **derived** requirement, not a criticism of the thesis's stated scope.

### F4. Static semantics chooses the program whose execution is being proved

Basis: **source/documentation** and **execution**.

The inspected a-mir-formality README calls the project experimental; it separates grammar, semantic checking (`check_all_crates`) and proving/trait normalization. It is not evidence that a complete Rust-to-MiniRust bridge or static soundness theorem is available. [Pinned README](https://github.com/rust-lang/a-mir-formality/blob/71dc31c1b186df1f0a64d8464b8103195902a5a5/README.md).

The accepted executable-spec goal proposes parsing, desugarings, a-mir-formality and MiniRust integration; method resolution/autoderef need type information. It distinguishes intended authoritative sections from reasonable experimental choices and excludes most standard-library and low-level FFI details. This is a plan, not a transfer theorem for today's implementation. [Goal](https://goals.rust-lang.org/2026/executable-spec.html).

The native feature pair `Select.pick()` versus `(&Select).pick()` resolves to distinct trait implementations and returns 1 versus 2. The wildcard binding `let _ = Token(...)` drops before the next log event, whereas a named underscore binding survives to scope exit. Preserved MIR exposes the selected implementations and generated cleanup. Thus preserving surface text or a value-only call graph can omit behavior relevant to proof binding.

| Static/elaboration input | Fact the dynamic theorem must receive |
|---|---|
| Trait solving, method resolution, autoderef | Exact impl/method body, substitutions, associated-item/law dictionary and receiver adjustment |
| Patterns, temporary scopes, partial moves | Evaluations, moves and cleanup edges with correct drop flags/order |
| Generics and const evaluation | Actual monomorphic layouts/constants or a theorem quantified over all admitted instantiations |
| Macros and generated code | Expanded item identity and all reachable generated operations, not only handwritten bodies |
| Closures | Environment layout, captures, call mode, generated drop code and callback contract |
| Pin/async/generators | Hidden state, suspension/drop states and pinning invariants; rejected generator terminators remain outside the examined importer |

The table gives **derived obligations**. This wave executes only the first two simple feature pairs and closure cleanup. It does not establish whole-item coverage for the other features.

### F5. Existing safe-client adequacy states the right quantifiers for its own language

Basis: **source** from a rehashed preserved archive.

In RustBelt `programs.v`, `typed_body` quantifies over thread identifiers and requires lifetime context, external/local lifetime interpretation, non-atomic token, continuation context and owned type context before WP. In `soundness.v`, `type_soundness` assumes semantic typing of main for every typeG instance and a finite reduction from the empty state; it concludes a nonracing pool and that each thread is a value or reducible. The closed wrapper fixes the resource functors. These exact premises and conclusion are preserved in report-owned excerpts. They provide neither arbitrary initial-state safety nor a MiniRust theorem.

The paper's fundamental theorem composes syntactically justified code with semantically proved exceptional components; adequacy then excludes stuck executions of the resulting closed λRust program. Traits and automatic source destruction are outside that subject. [RustBelt §7](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf).

For a proposed MiniRust library theorem, a useful explicit target is: for every admitted target/layout/environment, every library instance satisfying its unsafe-trait/dictionary premises, and every linked client satisfying the chosen safe typing relation, the linked program satisfies the selected model's safety judgment and preserves the abstraction. That judgment must retain the distinct demonic and angelic choice meanings; it cannot simply quantify universally over every raw provenance-prediction path. Each quantifier needs a bridge: MiniRust well-formedness alone is not safe Rust typing; its Type definitions expressly describe representation formats, not a type-safe language. The choice distinction is explicit in the [integer-pointer cast model](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/intptrcast.md). This is a **derived theorem proposal**, not an established result.

### F6. Callback and unsafe-trait premises cannot be supplied by a closed demo

Basis: **execution** + **derived** obligations.

The safe callback specimen passes only a shared Cell field to a callback, returns a mutable reference to a separate u8 field, and produces (7,9). This demonstrates an admitted client behavior that a range-only immutability contract would reject. It does not prove arbitrary callback soundness under Tree Borrows. Reentrant callbacks may retain permitted aliases, invoke other exports, return references, mutate allowed shared state or unwind; the abstraction must hold whenever control is handed out and on every reentry.

A Vec-like contract needs capacity/layout, allocation liveness, initialized prefix, element invariants and normal/unwind/abort effects. A zerocopy trait contract also needs exact representation and physical-access hypotheses, tied to the selected implementation and generic substitution. An unsafe caller violating an explicit precondition is outside that theorem's client domain; a safe caller choosing an allowed callback or safe trait implementation remains inside it. “The type checker accepted this demo” does not prove a universal value law or an unsafe-trait premise.

A future linking record should bind target, exact source/expanded item, lowering, impl/dictionary, runtime leaf contracts, public ownership/sharing predicates and exceptional exits. Mutating a proof-relevant impl or monomorphization must invalidate the binding even if the numerical example result stays equal. This wave specifies that negative-control obligation; it does not implement a new certificate checker.

## Boundaries

- **Established:** current unwind control and Drop importer seam, actual safe native traces/MIR, thesis proof-scope distinctions, and named RustBelt source theorem premises.
- **Not established:** full Rust-to-MiniRust elaboration adequacy, a MiniRust fundamental/linking theorem, zerocopy or Vec API soundness, source unwind payload fidelity or protected-reference restoration on every exceptional path.
- **Unknown:** complete axiom closure of the inaccessible thesis developments; the source RustBelt endpoint was inspected but not kernel-rebuilt.
- **Not examined:** actual double-panic termination, FFI/reentrant foreign clients, all trait/dictionary forms, macro/const evaluation, generated async state machines, or a complete surface feature inventory.
- **Unsupported at inspected importer branches:** Yield, CoroutineDrop and listed terminators; this is not a claim that Rust lacks those features.

## Evidence

Observed/revalidated 2026-10-14. `source-evidence.json` records immutable code coordinates and excerpts, thesis reported identities and unavailable-source outcomes. The preserved RustBelt archive was rehashed as `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`; exact member hashes and excerpts are retained under `evidence/`. No reliance on an unpublished external scratch file is necessary.

`probe.rs`, `probe-bin.mir`, `results.txt` and `execution.json` preserve source execution, full compiler identity, commands and statuses. Compilation emitted one expected warning that multiple output types adapt the output name. Runtime exit was 0 and stderr empty; the two deliberate caught panics were expected. No dependency installation or upstream build occurred.

## Revalidation

Inspect the Drop branch before importing any unwind claim; require it to preserve the MIR cleanup target and verify the panic strategy/payload path. Recompile the safe specimen with a pinned compiler, inspect its MIR cleanup and compare expected output. For the thesis, obtain the exact scalar/tuple artifacts and audit assumptions separately. For open APIs, choose the safe-client relation and discharge every resolved implementation, generated body, callback and exit against semantic type/ownership predicates before claiming contextual safety.

*Authored by an AI agent acting on joshlf's behalf.*
