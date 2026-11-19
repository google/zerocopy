# Algebraic effects, handlers, coeffects and capability tracking: typing disciplines, runtime models and the linearity collision

## Summary

- An effect handler receives the delimited continuation of the operation it handles and may resume it zero times (abort), once, or many times. Every other property in this report follows from how a language types, dispatches and represents that continuation.
- Three typing disciplines are in production use. Koka infers row-polymorphic effect types and compiles them with evidence passing; Effekt binds handlers lexically as second-class capabilities and needs no effect variables on higher-order functions; Scala 3 records the capabilities a value may retain in its type (`A^{c}`) and rejects values that outlive a locally bound capability. OCaml 5 has no effect typing at all: an unhandled effect is a runtime exception.
- Three runtime representations exist. OCaml 5 links heap-allocated fiber stacks and never copies frames, at the price of one-shot continuations. Koka unwinds to the handler by returning through every frame ("yield bubbling") while accumulating the continuation as composed heap closures, so multi-shot resumption is a second call of a reference-counted closure. Effekt's LLVM runtime keeps a meta-stack of reference-counted stack segments and copies a captured segment on resume only when it is shared.
- Value linearity is unsound in the presence of handlers unless resumption multiplicity is also controlled. A dropped continuation never runs the code that would release a captured resource; a continuation resumed twice runs that code twice. OCaml answers with a dynamic one-shot check plus `discontinue`; Koka with `finally`/`initially` and implicit finalization of unresumed clauses; Tang et al. with a static "control-flow linearity" on operations. Koka's own documentation states that double resumption still closes a file handle twice.
- Handler nesting order is semantically significant and invisible in an unordered effect row: state outside exceptions keeps writes made before the raise, exceptions outside state discard them; the same holds for state against nondeterminism.
- Effects cannot cross an opaque foreign frame in OCaml 5: the runtime clears the fiber's parent pointer around a C-to-OCaml callback, so a `perform` inside the callback raises `Effect.Unhandled`.
- The package's probe is a small-step machine and a checker for a model calculus. Over 924 enumerated programs, a checker that grades each operation's resumptions in {0, 1, ω} accepted 176 programs, all of which ran without leak, double-free or use-after-free; the same checker with only value linearity accepted 330 programs that went wrong. This is evidence about the model, not about any of the compilers above.
- Several widely repeated details are wrong or outdated and are corrected under Findings: OCaml fibers start at 64 words, not tens of bytes; a second resume raises `Continuation_already_resumed`, not `Invalid_argument`; continuation cloning was removed from Multicore OCaml, not deprecated in OCaml; the linear-base control hierarchy lives in `Control.Functor.Linear`.

## Applicability

The findings concern four language implementations at pinned revisions and seven publications. The implementations were read as source and in-tree documentation; nothing was compiled or executed from them. The only execution evidence in this report is the Python probe under `support/`, which runs a model calculus defined in that file.

| Subject | Role in this report | Depth of examination |
| --- | --- | --- |
| `ocaml/ocaml` at `d921d1e8…` | one-shot fiber runtime, effect API, manual | runtime C and assembly, stdlib interface, manual chapter |
| `koka-lang/koka` at `b66091b2…` | row-typed effects, evidence passing, finalization | handler library, C primitives, parser, language tour |
| `effekt-lang/effekt` at `6976c794…` | lexical capabilities, stack-copying runtime | LLVM and JavaScript runtimes, CPS tree, well-formedness checker |
| `scala/scala3` at `90f3daf0…` | capture checking, separation checking | reference documentation in tree, `CanThrow` library class |
| `tweag/linear-base` at `bb5182a7…` | linear control monads, resource release on exception | two modules |
| `ocaml-multicore/ocaml-multicore` at `ee7b692e…` | removal of continuation cloning | merge description |
| Plotkin and Pretnar; Petricek, Orchard and Mycroft; Tang et al.; Sivaramakrishnan et al.; Boruch-Gruszecki et al. | definitions, theorems, design rationale | full text (see Evidence for which copy) |
| Xie and Leijen; Brachthäuser, Schuster and Ostermann | published accounts of Koka's and Effekt's compilation | abstract and bibliographic record only |

Scope limits that change how the findings may be reused:

- Scala 3 capture checking and separation checking are experimental and enabled per file by `import language.experimental.captureChecking` and `import language.experimental.separationChecking`. The surface syntax at the pinned revision (`A^{c}`, universal capability `any`) differs from the published calculus, which writes `{c} A` and `*`. Statements about syntax apply to the pinned revision only.
- OCaml statements apply to the native-code runtime on 64-bit targets unless noted; the bytecode runtime shares the fiber allocator but not the assembly paths.
- Koka runtime statements apply to its C backend. The JavaScript backend shares the handler library but not the C primitives.
- Performance numbers are quoted from one paper with its hardware. No benchmark was run here.

Rust-specific material is deliberately absent. Borrow-checking, drop elaboration and the coroutine state-machine transform are covered by other packages in this corpus; the adjacent ones are `anneal-deductive-logics-types-and-abstract-interp-survey` (typestate and effect systems in deductive Rust verifiers), `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic` (the Iris base logic on which the separation logic for effect handlers cited below is built), `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics` (stackless coroutines) and `functional-core-effect-boundaries-reconciliation-and-netstack3-architecture` (effects as an architectural boundary). Where this report says "linear resource" it means a value that must be consumed exactly once; an exclusive mutable borrow behaves like one for the purposes of the duplication argument in the linearity section, but no claim is made here about Rust's rules.

## Findings

### 1. Vocabulary

| Term | Meaning used here |
| --- | --- |
| operation, `perform` | a call that transfers control to the nearest applicable handler together with the continuation up to that handler |
| resumption `k` | that delimited continuation, reified for the handler clause |
| deep handler | the resumption includes the handler, so it is reinstalled on resume; shallow handlers are not |
| shot count | how many times a clause resumes `k` normally: 0 (abort), 1, or more |
| tail-resumptive | the clause resumes exactly once, as its last action; needs no capture |
| dynamic binding | an operation reaches the innermost handler for its label on the stack |
| lexical binding | an operation reaches the handler instance its capability was bound to |
| evidence | a runtime value that identifies the handler for a label without a stack search |
| coeffect | a description of what a computation requires from its context, as opposed to what it does to it |

Basis: derived, as a normalisation of terms used across the sources below.

### 2. What the algebraic account fixes and what it leaves open

Plotkin and Pretnar treat a handler as an interpretation of an effect's operations: handling a computation applies the homomorphism induced by the universal property of the free model. Their calculus extends call-by-push-value with operations, handler definitions and a handling construct. Two consequences matter operationally.

First, the paper permits arbitrary handler definitions and therefore distinguishes correct handlers, those that respect the effect theory's equations, from the rest; a handling construct with an incorrect handler has no meaning in the semantics. Correctness is undecidable in general, and the paper shows that deciding it for very simple handlers is already Π2-complete. Languages built on handlers sidestep this by giving effects the empty theory, in which every handler is correct. The price is that no equation between operations, such as "two reads without a write return the same value", is available to a compiler or a proof unless it is established for a specific handler.

Second, the paper's examples already contain the ordering phenomenon of the non-commutativity section. Its rollback handler handles `raise` by resetting a memory location to the value it held on entry, so that modifications made before the exception are reverted; the alternative it gives is a parameter-passing handler that never writes memory and instead threads the changes as a parameter.

The conference version is titled "Handlers of Algebraic Effects" (ESOP 2009); the journal version is "Handling Algebraic Effects" (2013). They are frequently cited interchangeably under either title.

Basis: normative (the journal paper is the defining account of the construct).

### 3. Three static disciplines and one absence

| | Koka | Effekt | Scala 3 capture checking | OCaml 5 |
| --- | --- | --- | --- | --- |
| What a type records | an effect row of the operations a function may perform | the capabilities a function requires from its context | the capabilities a value may retain | nothing about effects |
| Higher-order functions | row variable shared between argument and result | no annotation; blocks are second-class | no annotation; impure arrow `=>` admits any capability | no annotation |
| Handler binding | dynamic, innermost handler of the label | lexical, explicit prompt per handler | not a handler mechanism; capabilities are ordinary values | dynamic |
| Unhandled operation | type error | type error | missing-capability error for `CanThrow` | runtime `Effect.Unhandled` |
| Escape of a handler's capability | ordinary handlers bind no first-class capability; named handlers not examined | type error on the handled statement's return type | type error on the capture set | not checked |
| Status at the pinned revision | stable | stable | experimental language imports | effect API marked unstable |

Koka. The handler library describes the internal typing directly: an effect row has kind `E`, an atomic effect is a type constructor from an answer context to a value type, and evidence for a handler is an existential package of a marker and the handler for some answer context. Operation declarations carry a sort that fixes the clause's shot count by construction: `val` and `fun` are tail-resumptive, `final ctl` never resumes, `ctl` is general, and `raw ctl` is general without automatic finalization. A `linear effect` may contain only tail-resumptive operations; the parser rejects `ctl` and `final ctl` inside one with the messages "'ctl' operations are invalid for a linear effect" and "'final ctl' operations are invalid for a linear effect". The tour says such effects remove the need for the monadic translation; that paragraph of the tour is marked as unfinished.

Effekt. The published abstract states the design position: effect types express which capabilities a computation requires from its context rather than which side effects it has, all functions are second-class to guarantee effect safety, and the semantics is a translation into a calculus in explicit capability-passing style. The pinned compiler shows the same structure. Its continuation-passing intermediate language has `Reset`, `Shift(prompt, body, ...)` and `Resume(resumption, body, ...)`; `Shift` names its prompt explicitly, which is what makes binding lexical. The well-formedness pass rejects a handled statement whose inferred type mentions a capability the handler binds, with the message "The return type … of the handled statement is not allowed to refer to any of the bound capabilities", and applies the same rule to regions and to mutable local variables that would escape through a returned value.

Scala 3. A capturing type `A^{c₁, …, cₙ}` describes values of `A` that retain the listed capabilities; a bare `A` is pure for classes that do not extend `Capability`; `A^` abbreviates `A^{any}`. `A -> B` is the pure function type and `A => B` abbreviates `A ->{any} B`. Capture sets are ordered by inclusion, and a capability whose own type captures a set refines that set. Escape checking follows from scoping: a capture set can mention only capabilities visible where the set is defined, so a closure that captures a locally bound capability cannot be returned through a type variable instantiated outside that scope. Checked exceptions are encoded on top: `T throws E` expands to a context function taking `CanThrow[E]`, and a `try` that catches `E` provides an erased instance. In the library, `CanThrow[-E <: Exception]` extends `caps.Control` and `compiletime.Erased`.

Separation checking is a further experimental layer that treats each occurrence of the universal capability as a distinct, unaliased capability and adds a `consume` modifier whose argument may not be used after the call. The in-tree documentation describes it as less mature than capture checking proper. It is the only one of the four systems at these revisions with a use-once discipline on ordinary values, and it says nothing about continuations, which Scala does not expose.

OCaml 5. The manual states that effect handlers do not provide effect safety, in contrast to Eff and Koka, and that an effect without a matching handler raises `Effect.Unhandled` at the `perform`. The `Effect` module carries an alert that its interface may change incompatibly.

Basis: source + documentation for the four implementations; documentation for the two abstracts quoted.

### 4. Dispatch: stack search, evidence vectors and lexical capabilities

Dynamic binding can be implemented by walking handler frames, as OCaml does, or by passing evidence. In Koka, installing a handler allocates a fresh marker, builds evidence from the handler's tag, the marker, the handler and the current evidence vector, inserts it into the vector and runs the action under a prompt. Performing an operation selects the evidence, selects the clause from the handler and calls it with the marker. The clause, not the call site, decides what happens next:

| Clause constructor | Behaviour | Capture |
| --- | --- | --- |
| `clause-tail-noop1` | calls the operation body in place | none |
| `clause-tail1` | swaps to the evidence vector stored in the evidence, calls the body, swaps back | none |
| `clause-never1` | yields to the marker in final mode | none; the continuation is discarded as it unwinds |
| `clause-control1` | yields to the marker; the prompt builds the resumption and runs the clause under a protection wrapper | yes |

The evidence vector is a dynamically scoped register, not a closure-captured value, so evidence passing preserves dynamic binding. A resumption is only valid in the handler context it was captured in: the prompt compares evidence vectors on return, and the C runtime aborts with "trying to resume outside the (handler) scope of the original handler" when they differ.

Lexical binding changes the meaning of programs, not only their cost. If a higher-order function privately installs a handler for a label and then calls a callback that performs the same label, dynamic binding delivers the callback's operation to the private handler. Zhang and Myers name this accidental handling and give a semantics in which effects tunnel through code that is polymorphic in them; Biernacki et al. obtain a similar guarantee with lexically scoped handler instances. Koka's remedy within dynamic binding is `mask<l>`, which skips the innermost handler for `l` and whose type adds a second occurrence of `l` to the row.

The converse failure belongs to lexical binding: a closure that captured a capability may be called after its handler has returned. Effekt and Scala 3 reject this statically, as described above.

The probe exercises all three behaviours in its model. With a callee that privately handles `ask` by answering 100 around a callback closed over an outer handler answering 1, stack search and evidence-vector dispatch both return 100 and lexical dispatch returns 1. A closure that outlives its handler fails under lexical dispatch even when an outer handler for the same label exists, while dynamic dispatch silently rebinds it to that outer handler. Across all 924 family programs and the three ordering examples, evidence-vector dispatch produced the same outcome as stack search and never selected a different handler frame.

Basis: source (Koka handler library and C primitives) + documentation (Koka tour; abstracts of the tunneling and lexical-instances papers) + execution (probe checks e1 to e8).

### 5. Runtime representations

| | OCaml 5 | Koka (C backend) | Effekt (LLVM backend) |
| --- | --- | --- | --- |
| Unit captured | a chain of fiber stacks, by pointer | closures registered by each frame as it returns | a cyclic list of stack segments, by pointer |
| Cost of capture | constant per fiber; no frame is copied | every frame between the operation and the handler returns once | constant per segment |
| Resume | relink the chain under the current stack | call the composed closure | relink; copy first if the resumption is shared |
| Multi-shot | unsupported | supported; second call takes a reference-count-aware slow path | supported; copy on shared resume |
| Abort | drop, or `discontinue` to unwind | final yield; continuations are dropped as they are offered | drop; frames are erased by reference counting |
| Foreign frames | effects cannot cross a C callback | not examined | not examined |

OCaml 5. A continuation is a one-word heap object pointing to a fiber, and each fiber points to its parent through its handler record:

```c
struct stack_handler {
  value handle_value;
  value handle_exn;
  value handle_effect;
  struct stack_info* parent; /* parent OCaml stack if any */
};
```

`perform` stores the current stack in a fresh continuation, then walks parents: if the parent is null it switches back to the performer and raises the unhandled-effect exception; otherwise it switches stacks, appends the fiber it left to the continuation and calls the parent's effect handler with the effect and the continuation. Because handler closures are tried in turn, the paper notes that handling cost is linear in the number of handlers between the operation and its handler. Resumption takes the stack out of the continuation, links the current stack as the parent of the continuation's last fiber and switches.

Sizes at the pinned revision, which differ from the paper:

| Quantity | Paper (Multicore OCaml on 4.10) | Pinned source |
| --- | --- | --- |
| initial fiber frame area | 16 words | `caml_fiber_wsz = (Stack_threshold * 2) / sizeof(value)`, that is 64 words (512 bytes on 64-bit) |
| red zone below which leaf functions skip the overflow check | 16 words | `Stack_threshold_words 32` |
| growth | copy to a region of double size | `caml_try_realloc_stack` doubles until the request fits, copies the used part, rewrites the exception-pointer chain and every C-stack link that refers to the old stack |
| main stack | not stated | 4096 words initially (64 in debug builds) |
| limit | not stated | `Max_stack_def`, 128 Mi words |
| allocation | `malloc`, with a cache of freed stacks | `mmap` with `MAP_STACK` when configured, else the runtime allocator; five pooled size classes |

Growth by copying is sound only because, as the paper observes, OCaml creates no pointers into its own frames; the two saved pointers per fiber and the exception chain are the only things relocated.

The one-shot rule is enforced where the stack is taken out of the continuation:

```c
CAMLprim value caml_continuation_use (value cont)
{
  value v = caml_continuation_use_noexc(cont);
  if (v == Val_ptr(NULL))
    caml_raise_continuation_already_resumed();
  return v;
}
```

`caml_continuation_use_noexc` replaces the continuation's field with a null stack, by plain store when the domain runs alone and by atomic compare-and-exchange otherwise. It follows (derived, not tested here) that of two domains racing to resume one continuation at most one obtains the stack. The native `caml_resume` path tests the stack pointer it is handed for null and raises the same exception.

The paper reports, for one handler installed, one effect performed and resumed, and return, on a Xeon Gold 5120: 23 ns to install the handler and allocate the fiber, 5 ns to perform and reach the handler, 11 ns to resume, 7 ns to return and free the fiber, against a measured local memory-load latency of 93.2 ns. It reports that the multicore variants were on average less than 1% slower than stock OCaml on 54 programs that do not use effects, and micro-benchmark time differences of +17% for an external call and +65% for a callback; the paper explains that C functions have no overflow checks and must therefore run on the system stack.

Koka. An operation that needs its continuation sets a thread-local yield record (marker, clause, and an array of at most eight continuation closures) and returns. The handler library, which by its own header is compiled without the monadic translation and written in that style by hand, shows the protocol: after an effectful call the caller tests the yielding flag and, if set, registers the rest of its own body and returns as well (`yield-bind`, `yield-extend`). When the array is full the entries are folded into one composed closure. The code the compiler generates for user functions was not inspected. The prompt whose marker matches composes the array into the resumption and runs the clause. Capture therefore costs one return per intervening frame and no stack copy. The composed closure distinguishes two cases when called:

```c
if kk_likely(kk_datatype_ptr_is_unique(fself, ctx)) {
  // Special handling for unique continuation function to avoid dup/drop
  // overhead for the continuation and captured variables.
```

A uniquely referenced resumption is consumed in place and freed; a shared one duplicates each stored continuation before calling it. Multi-shot resumption is thus an ordinary second call under reference counting. A final yield never builds the continuation: extensions offered while yielding in final mode are dropped immediately, and resuming such a resumption aborts with "trying to resume a finalized resumption".

Effekt. The LLVM runtime represents a resumption as a pointer into a cyclic list of stack values, each carrying a reference count, stack pointer, limit, prompt and link. `shift` detaches the segments above a prompt; `resume` first calls `uniqueStack`, which returns the resumption unchanged when its reference count is zero and otherwise decrements the count and copies every segment with `copyStack`. Copying a segment is a `memcpy` of the used part followed by sharing every frame's contents and the prompt. Mutable variables are addressed as a prompt and an offset, so they live in the segment and are copied with it; the JavaScript runtime obtains the same semantics with a snapshottable arena whose state is captured in constant time and restored in time proportional to the writes since capture. It follows (derived) that a mutable local variable is duplicated together with the segment that holds it when a shared resumption is resumed.

Basis: source for all three runtimes + documentation (OCaml manual; Koka tour) + normative for the figures attributed to the OCaml paper. The cost characterisations in the comparison table are derived from the control flow of the cited functions; none was measured here.

### 6. Foreign frames

OCaml 5 refuses to capture a continuation that would contain a C frame. The mechanism is not a check at `perform` but a change to the fiber made when C calls back into OCaml. The callback runs on the current fiber, and the runtime detaches that fiber from its parent for the duration:

```c
/*
 * These functions are to ensure effects are handled correctly inside
 * callbacks. There are two aspects:
 *  - we clear the stack parent for a callback to force an Effect.Unhandled
 *  exception rather than effects being passed over the callback
 *  - we register the stack parent as a local root while the callback
 * is executing to ensure that the garbage collector follows the
 * stack parent
 */
```

`alloc_and_clear_stack_parent` wraps the parent stack in a continuation object and nulls the parent field; `restore_stack_parent` takes it back out afterwards. Since `perform` raises the unhandled-effect exception exactly when it reaches a fiber with no parent, an effect performed inside the callback and not handled inside it is reported as unhandled even though a handler exists further out. A handler installed inside the callback is unaffected (derived: its fiber has a parent). The manual states the limitation for `caml_callback` and warns about mixing libraries that use C-to-OCaml callbacks with libraries that use effects; separately it states that effects are synchronous, so one performed from a signal handler, finaliser, memprof callback or GC alarm cannot be caught by the main code and is likewise unhandled.

The paper gives the reason: OCaml lets exceptions cross C frames, but an effect crossing one would make the C frames part of the captured continuation, and managing them was judged not worth the complexity. External calls themselves run on the system stack because C code has no stack-overflow checks. The fiber is not pinned by an outstanding C call (derived): stack reallocation walks the list of C-stack links and repoints those that refer to the moved stack.

The probe models the barrier with an opaque frame that dispatch may not pass. In its evidence-vector mode the frame is implemented by emptying the vector on entry, which reproduces the OCaml mechanism: the operation is simply not found.

Basis: source + documentation + execution (probe checks f1 to f3, model only).

### 7. Linear resources against shot counts

The collision can be stated without reference to any one language. Let a computation hold a resource that must be released exactly once, and let it perform an operation while holding it. The code that releases the resource is then inside the resumption.

- If the handler never resumes and simply returns, that code never runs: the resource leaks. A `finally` block around the computation does not help by itself, because nothing unwinds the abandoned continuation.
- If the handler resumes twice, that code runs twice: the resource is released twice, or used after release, depending on what the continuation does first.
- If the handler resumes exactly once, nothing goes wrong.

A type system that counts how often a variable is used, and assumes each program point is passed once, accepts all three programs. The remedies differ by system.

| System | At most once | At least once | Mechanism |
| --- | --- | --- | --- |
| OCaml 5 | dynamic check | not checked | `Continuation_already_resumed`; `discontinue` raises an exception inside the continuation so that its handlers and cleanup run |
| Koka | not enforced for `ctl` | automatic for `ctl`, `final ctl` | `finally` runs on normal return and on unwinding; an unresumed `ctl` clause has its resumption finalized; `initially` reruns setup on later resumes |
| Tang et al. calculi | static | static | operations are control-flow linear or unlimited; a linear resource may be live only across linear operations |
| Linear Haskell with linear-base | by type | by type on the normal path; a release map on exceptions | the bind of a control monad consumes its continuation linearly |
| Scala 3 separation checking | by `consume` on values | not applicable | no first-class continuations |

OCaml. The manual's rule is that every captured continuation must be resumed with `continue` or `discontinue` exactly once. It is explicit that only half of this is checked: the at-most-once property by a dynamic check, the at-least-once property not at all, and that an unresumed continuation leaks the fiber's memory and any resource the suspended computation holds. The suggested backstop is a finaliser that discontinues the continuation with a private exception, with the caveat that finalisers cost far more than capturing a continuation. The manual's stated reasons for not supporting multi-shot continuations are that one-shot suffices for concurrency, avoids copying frames, and that resuming twice would break the linear use of resources such as sockets with no static check to diagnose it.

Two version details. The paper describes the second-resume failure as an `Invalid_argument` exception; the pinned standard library declares a dedicated `Continuation_already_resumed` and documents it on `continue`, `discontinue` and their shallow counterparts. And Multicore OCaml once had a primitive to clone a continuation, which made multi-shot handlers possible by copying fibers. It was removed before effects reached mainline OCaml; the description of the removing merge says that cloning breaks compiler optimisations and is hard to use correctly in the presence of resources. No such primitive is declared in the `Obj` interface at the pinned revision.

Koka. `finally(fin, action)` distinguishes three states after `action` returns: not yielding, in which case `fin` runs; yielding to a resuming operation, in which case the finalizer is re-registered around the rest of the continuation; and yielding in final mode, in which case the yield is captured, `fin` runs, and the yield is re-raised. A general `ctl` clause is wrapped so that returning without resuming is not a silent drop:

```koka
fun protect( x : a, clause : (x:a, k: b -> e r) -> e r, k : resume-result<b,r> -> e r ) : e r
  val resumed = (unsafe-st{ref(NeedsFinalization(k))})()
  fun kprotect(ret)
    (unsafe-st{resumed := NoFinalization})()
    k(Deep(ret))
  val res = clause(x,kprotect)
  protect-prompt(resumed,res)
```

If the clause did not call `kprotect`, `protect-prompt` resumes the continuation in `Finalize` mode, which re-enters it only to yield finally from the operation's call site and so runs every enclosing `finally`. A `raw ctl` clause opts out and receives a resumption context with explicit `resume` and `finalize`. This covers the zero-shot case. For the multi-shot case the tour is candid: its file-handle example is "robust for operations that never resume, or operations that resume once -- but there is still trouble when resuming more than once", the handle "will be closed again", and "there is active research into using the type system to statically prevent this". The handler library documents a lattice of control-flow contexts (none; except, never resumes; linear, exactly once; affine, never or once; multi) next to a query for whether the current evidence vector is affine, but in the C backend that query unconditionally returns false and the bookkeeping for it is commented out, so nothing at run time currently depends on the classification there.

Tang et al. introduce control-flow linearity: a control-flow-linear context is entered exactly once and may capture linear resources; a control-flow-unlimited context may be entered any number of times and may not. Operations carry the distinction, effect rows lift it, and the resumption of a linear operation has a linear function type, so a handler that invokes it twice or drops it is ill-typed. The paper's motivating program writes to a file handle after a nondeterministic choice and is rejected once the choice operation is declared control-flow linear. Besides progress and subject reduction, the paper proves that unlimited values, unlimited continuations and deep handlers capture no linear variables, and gives a linearity-aware semantics in which no linear value is discarded or duplicated during evaluation. It reports that the Links language, which combines session-typed linear channels with handlers, had a long-standing soundness bug of exactly this kind, fixed by adopting the design. A second calculus based on qualified types infers the annotations.

Linear Haskell. In linear-base the bind of the control-monad hierarchy is

```haskell
(>>=) :: m a %1 -> (a %1 -> m b) %1 -> m b
```

so the continuation of every monadic step is consumed exactly once by type. Exceptions are outside that guarantee: the resource-aware IO monad keeps a map of release actions and runs the remaining ones only when the computation exits by exception, with the in-source remark that resources are guaranteed released on non-exceptional return. This is the same split as OCaml's and Koka's: linearity covers the normal path, and abortion needs a registry of finalizers.

A separation logic for effect handlers by de Vilhena and Pottier, built on Iris, is the proof-side counterpart, and it is the first reference given by the Multicore OCaml merge that removed cloning. Only its abstract was read here.

Basis: documentation + source (OCaml manual and runtime, Koka library and tour, linear-base) + normative (Tang et al. for their calculi) + derived (the three-case argument and the comparison table).

### 8. A graded discipline, checked on a model

The probe implements one way to make the three-case argument a checkable rule, using the multiplicities 0, 1 and ω. It is a model built for this report, not a description of any cited system, though each rule has a counterpart above.

Each operation label is declared with a grade. For every handler clause the checker computes, per control-flow path, how the clause uses its resumption: dropped, unwound once, resumed once, or anything else (two or more uses, or the resumption escapes into a closure or value). The declared grade restricts the clause:

| Grade | Clause must | Counterpart |
| --- | --- | --- |
| 1 | resume exactly once on every path | Koka `fun`; a control-flow-linear operation |
| 0 | unwind exactly once on every path and never resume | Koka `final ctl`; OCaml `discontinue` |
| ω | anything | Koka `ctl`; a control-flow-unlimited operation |

and restricts every point where the operation may be performed. Let C be the linear handles that are live at that point and are opened or closed inside the body of the handler that will receive the operation (all live handles, if that handler is not lexically visible):

| Grade | Requirement on C |
| --- | --- |
| 1 | none |
| 0 | every handle in C is closed by the cleanup of a `finally` that encloses the point inside that handler |
| ω | C is empty |

A point where the operation "may be performed" is a perform of that label, a call (which may perform any label that occurs under a lambda), or a resume inside a clause (which may perform any label that the clause's own handler forwards). Grade 0 demands unwinding rather than dropping because, as in OCaml's rule, unwinding is a linear use of the continuation through its exceptional entry.

Results over the enumerated family (11 placements of one handle relative to one perform, 7 clause behaviours, 3 declared grades, 2 arguments, 2 nesting shapes; 924 programs), each also run on the machine with unrestricted multi-shot resumption and no automatic finalization:

| | ran safely | leak, double-free or use-after-free |
| --- | --- | --- |
| accepted by the graded checker | 176 | 0 |
| rejected by the graded checker | 418 | 330 |
| accepted with value linearity only | 594 | 330 (234 leak, 60 double-free, 36 use-after-free) |

Of the 418 safe programs rejected, 332 have a clause that does not match its declared grade and 86 are rejected at a perform point because the declared grade permits a behaviour the actual handler happens not to exhibit. Disabling any single graded rule admits unsafe programs: 110 without the ω requirement, 24 without the grade-0 requirement, 124 without the clause restriction, 20 without the resume-point rule and 20 without the call-point rule.

Individual cases recorded by the probe: resuming twice across an open handle is a double-free when the continuation closes first and a use-after-free when it writes first; the same program under a one-shot check stops at the second resume with one close performed; dropping the resumption leaks even when the handle is guarded by `finally`; unwinding the resumption, or finalizing an unresumed clause automatically, closes a guarded handle exactly once; unwinding does not help an unguarded handle.

Limits. The family is finite and hand-enumerated; acceptance implying safety is observed on it, not proved. The checker is conservative by construction, treats handles as second-class names, has no grade for "never or once", and grades a resumption used under a lambda as ω, which is why the state-passing handlers of the next section would be rejected around any open handle although they resume once per operation.

Basis: execution (probe checks b1 to b5, c1 to c8, d1 to d6) + derived (the rules themselves).

### 9. Handler order is observable

With state implemented as a parameter-passing handler and exceptions as a handler that discards its resumption, the program "write 1, then raise" started from state 0 gives:

| Nesting | Result | Reading |
| --- | --- | --- |
| state outside exception | `(("err", "boom"), 1)` | the write survives the raise |
| exception outside state | `("err", "boom")` | the state is discarded with the continuation |

With nondeterministic choice implemented by resuming twice and concatenating results, and a body that chooses, increments the state and returns it:

| Nesting | Result | Reading |
| --- | --- | --- |
| state outside choice | `((1, 2), 2)` | one state threaded through both branches |
| choice outside state | `((1, 1), (1, 1))` | each branch starts from the captured state |

Both pairs of programs have the same set of effect labels. An effect row that is a set or multiset of labels therefore cannot express which behaviour a polymorphic function relies on. Which semantics a mutable cell gets also depends on where the runtime keeps it: a heap reference shared by both resumptions persists across branches regardless of nesting, whereas state held in the captured frames, as with Effekt's local variables, is duplicated with them.

The algebraic treatment of combining effect theories by sum and tensor is due to Hyland, Plotkin and Power; that paper was identified but not read for this report.

Basis: execution (probe checks a1 to a5, e2) + derived.

### 10. Coeffects and where grades come from

Petricek, Orchard and Mycroft define a coeffect calculus whose typing judgment annotates the context, written Γ@R ⊢ e : τ, and whose function types carry a scalar annotation for their one parameter. The algebra has three layers. A coeffect scalar is a structure (C, ⊛, ⊕, use, ign, ≤) in which (C, ⊛, use) and (C, ⊕, ign) are monoids, ≤ is a preorder, and ⊛ distributes over ⊕ on both sides; ⊛ models sequential composition with variable access as its identity, ⊕ combines the uses of a context shared between subterms, and `ign` marks an unused variable. A shape determines how scalars are attached to a context: one annotation for the whole context in a flat system, a vector with one entry per variable in a structural system. The coeffect algebra then says how annotations split and merge at abstraction and application.

Instances given in the paper include bounded reuse, with scalars (ℕ, ∗, +, 1, 0, ≤) counting variable uses as in bounded linear logic, dataflow caching depth, liveness, and implicit parameters as a flat system. The paper shows that structural systems preserve types under β-reduction and η-expansion, which it notes distinguishes them from both effect systems and flat coeffects, and gives a semantics using indexed comonads.

The relevance here is twofold. Capabilities and lexically bound handlers are context requirements, so Effekt's reading of effect types as "capabilities required from the context" is a coeffect reading in this vocabulary; that identification is this report's, and neither the Effekt abstract nor the coeffect paper makes it in those words. And the multiplicities {0, 1, ω} form a coeffect scalar: the probe checks all 27 triples for associativity and distributivity, the units, and the preorder with 0 ≤ ω and 1 ≤ ω. Grading a resumption by how often a clause uses it is then the bounded-reuse analysis collapsed to three values and applied to one distinguished variable.

Basis: normative (the coeffect paper, for its definitions and stated properties) + execution (probe check g1) + derived (the two identifications).

### 11. Corrections to commonly repeated details

| Often stated | What the examined sources show |
| --- | --- |
| OCaml fibers start at a few dozen bytes | 64 words of frame area at the pinned revision, plus a header and a handler record; the paper's figure is 16 words |
| a second resume raises `Invalid_argument` | true of the paper's implementation; the pinned runtime raises `Effect.Continuation_already_resumed` |
| OCaml deprecated `Obj.clone_continuation` | cloning was removed in Multicore OCaml before effects were merged into OCaml; the pinned `Obj` interface has no such value |
| C frames are pinned, so effects fail | the callback detaches the fiber from its parent; `perform` then finds no handler |
| Koka and Effekt implement multi-shot by cloning the stack | Koka's C backend composes heap closures and copies no stack; Effekt's LLVM runtime copies segments, and only when the resumption is shared |
| linear control monads live in `Control.Monad.Linear` | the module at the pinned linear-base revision is `Control.Functor.Linear` |
| the Scala capture-checking syntax is `{c} T` with universal capability `*` | that is the published calculus; the pinned compiler documents `T^{c}` and `any` |

Basis: source + documentation, as cited in the sections above.

## Boundaries

Not examined:

- Any execution of OCaml, Koka, Effekt or Scala programs. Every statement about those systems rests on reading source and in-tree documentation at the pinned revisions.
- The full text of Xie and Leijen and of Brachthäuser, Schuster and Ostermann. Their abstracts and bibliographic records were read; the mechanisms attributed to Koka and Effekt come from the pinned implementations, which may differ from the papers.
- The code the Koka compiler generates for user functions (its monadic translation pass), Koka's named handlers, and Koka's non-C backends beyond noting that they share the handler library.
- Effekt's type checker beyond the well-formedness pass, its Chez Scheme backend, and how Effekt or Koka interact with foreign code.
- The Scala 3 capture checker's implementation; only its documentation and one library class were read.
- The WebAssembly stack-switching proposal, the C++ effects library and Project Loom, which Tang et al. list alongside OCaml as dynamically checked one-shot designs.
- Shallow handlers, beyond noting that OCaml and Koka provide them.
- Bytecode OCaml and 32-bit targets.

Unknown:

- Whether a publication titled "Qualified Effect Handlers" exists. None was found; the calculus with that flavour is the qualified-types calculus in Tang et al.
- Whether the graded rules of the probe are sound beyond the enumerated family. No proof was attempted.
- Current performance of any of the three runtimes. The only figures quoted are from the 2021 OCaml paper on its hardware.
- Whether Koka's control-flow-context classification is used by backends other than C.

Known not to apply:

- The one-shot restriction does not make OCaml programs resource-safe: an unresumed continuation leaks, by the manual's own statement.
- Koka's `finally` does not make multi-shot resumption safe for a held resource, by the tour's own statement.
- Evidence passing does not change which handler an operation reaches; it is an implementation of dynamic binding. Lexical capability passing does change it.
- Capture checking in Scala 3 is not a linearity or multiplicity discipline; the `consume` modifier belongs to the separate separation-checking extension.

Unsupported:

- OCaml does not support multi-shot continuations, performing an effect across a C-to-OCaml callback, or performing one asynchronously from a signal handler, finaliser, memprof callback or GC alarm.
- A Koka `linear effect` does not admit `ctl` or `final ctl` operations.

Stronger conclusions the evidence does not establish: that any of these systems is sound for linear resources; that the probe's discipline could be added to one of them unchanged; that exclusive borrows in Rust interact with handlers as the model's handles do.

## Evidence

All evidence was acquired on 2026-11-19. Line numbers refer to the files at the pinned revisions.

`ocaml/ocaml` at `d921d1e86c56baa7b30e890ced455c12255793f5`:

- `runtime/caml/fiber.h` 31–36 (`struct stack_handler`), 43–62 (`struct stack_info`), 108–121 (`struct c_stack_link`).
- `runtime/caml/config.h` 168–189 (`Stack_init_bsize`, `Stack_threshold_words`, `Max_stack_def`); `runtime/gc_ctrl.c` 345 (`caml_fiber_wsz`).
- `runtime/fiber.c` 95 (size classes), 111–146 (allocation), 537–602 (`caml_try_realloc_stack`), 688–724 (`caml_continuation_use_noexc`, `caml_continuation_use`), 771–794 (the two exceptions).
- `runtime/amd64.S` 1127–1207 (`caml_perform`), 1227–1277 (`caml_resume`).
- `runtime/callback.c` 46–75 (parent clearing), 186–203 (use in `caml_callback_exn`).
- `stdlib/effect.mli` 21–34 (alert, `Unhandled`, `Continuation_already_resumed`), 48–59; `stdlib/obj.mli` (no clone primitive).
- `manual/src/refman/extensions/effects.etex` 535–619 (no copying; unhandled effects; linear continuations; limitations).

`koka-lang/koka` at `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`:

- `lib/std/core/hnd.kk` 9–103 (design notes), 226–237 (control-flow contexts), 365–428 (`resume-result`, `yld`, `prompt`, handler installation), 485–499 (`finally`), 525–542 (`initially`), 551–560, 614–672 (`protect`, clause constructors).
- `lib/std/core/inline/hnd.c` 22 and 122–125 (`kk_evv_is_affine`), 266–306 (`kcompose`), 324–340 (`kk_yield_extend`), 381–400 (yield and final yield), 431–439 (`kk_evv_guard`).
- `kklib/include/kklib.h` 416–433 (yield record).
- `src/Syntax/Parse.hs` 1199–1219 (linear-effect restrictions); `src/Common/Syntax.hs` 353–363 (operation sorts).
- `doc/spec/tour.kk.md` 1104–1166 (tail-resumptive operations, evidence passing), 1547–1597 (`mask`), 1798–1900 (`initially`, `finally`, `raw ctl`, linear effects).

`effekt-lang/effekt` at `6976c7947eac26bc1203bcd48892702ce6d3cf21`:

- `libraries/llvm/rts.ll` 64–91 (types), 579–609 (`resume`, `shift`), 663–745 (`copyStack`, `uniqueStack`), 747–800 (sharing and erasing resumptions).
- `libraries/js/effekt_runtime.js` 36–67 (arena, snapshot).
- `effekt/shared/src/main/scala/effekt/cps/Tree.scala` 120–126; `effekt/shared/src/main/scala/effekt/typer/Wellformedness.scala` 100–161.

`scala/scala3` at `90f3daf0a4795308d9c0e1b8f2265aeaecae8aa2`, under `docs/_docs/reference/experimental/capture-checking/`: `overview.md` 63–148, `basics.md` 40–72 and 335–366, `scoped-capabilities.md` 8–20, `separation-checking.md` 35–46 and 234–314, `checked-exceptions.md` 7–70, `how-to-use.md` 7–22; and `library/src/scala/CanThrow.scala` 13.

`tweag/linear-base` at `bb5182a76c84eedcf78536c9ce24cb900882b2f3`: `src/Control/Functor/Linear/Internal/Class.hs` 176–186; `src/System/IO/Resource/Linear/Internal.hs` 49–84. The repository tree at that revision contains no `Control/Monad/Linear.hs`.

`ocaml-multicore/ocaml-multicore` at `ee7b692e49d87cc59381b1c1a643e6d66563cddb`: the merge of pull request 651, "Expose deep and shallow handlers as functions", merged 2021-09-22; its description states the removal of continuation cloning and the two reasons quoted.

Publications, with the copy read:

- Plotkin and Pretnar, "Handling Algebraic Effects", Logical Methods in Computer Science 9(4), 2013, DOI 10.2168/LMCS-9(4:23)2013; arXiv 1312.1399v2, full text. Preliminary version "Handlers of Algebraic Effects", ESOP 2009, LNCS 5502, pages 80–94, DOI 10.1007/978-3-642-00590-9_7; record and abstract.
- Sivaramakrishnan, Dolan, White, Kelly, Jaffer and Madhavapeddy, "Retrofitting Effect Handlers onto OCaml", PLDI 2021, pages 206–221, DOI 10.1145/3453483.3454039; arXiv 2104.00250v1. Full text read from the first author's hosted copy carrying the PLDI '21 running head.
- Xie and Leijen, "Generalized Evidence Passing for Effect Handlers: Efficient Compilation of Effect Handlers to C", Proc. ACM Program. Lang. 5(ICFP), 2021, DOI 10.1145/3473576; extended version MSR-TR-2021-5, v4 of 2021-06-07. Abstract only.
- Brachthäuser, Schuster and Ostermann, "Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism", Proc. ACM Program. Lang. 4(OOPSLA), 2020, DOI 10.1145/3428194. Abstract only.
- Boruch-Gruszecki, Odersky, Lee, Lhoták and Brachthäuser, "Capturing Types", ACM TOPLAS 45(4), 2023, pages 1–52, DOI 10.1145/3618003. Full text read as the preprint "Scoped Capabilities for Polymorphic Effects", arXiv 2207.03402v2, which uses the older syntax.
- Petricek, Orchard and Mycroft, "Coeffects: A Calculus of Context-Dependent Computation", ICFP 2014, pages 123–135, DOI 10.1145/2628136.2628160. Full text read from the first author's hosted copy.
- Tang, Hillerström, Lindley and Morris, "Soundly Handling Linearity", Proc. ACM Program. Lang. 8(POPL), article 54, 2024, DOI 10.1145/3632896; arXiv 2307.09383v2, full text.
- Abstract or record only, cited for context: de Vilhena and Pottier, "A Separation Logic for Effect Handlers", DOI 10.1145/3434314; Zhang and Myers, "Abstraction-Safe Effect Handlers via Tunneling", DOI 10.1145/3290318; Biernacki, Piróg, Polesiuk and Sieczkowski, "Binders by Day, Labels by Night", DOI 10.1145/3371116; Hyland, Plotkin and Power, "Combining Effects: Sum and Tensor", DOI 10.1016/j.tcs.2006.03.013.

Execution. `support/verify_effect_linearity_and_evidence.py` is self-contained Python (3.10 or newer, standard library only) and writes nothing but standard output:

```console
$ python3 -B support/verify_effect_linearity_and_evidence.py
...
RESULT: PASS (45/45 checks)
```

It was run with Python 3.13 and completes in about one second. `--json` prints the facts quoted in sections 4, 8 and 9; `--list` prints the verdict and outcome of each of the 924 family programs. The report's synthesis, as distinct from source facts, is confined to passages marked derived, to the comparison tables, and to sections 8 and 10.

## Revalidation

- OCaml one-shot rule and exception name: read `caml_continuation_use` in `runtime/fiber.c` and the declarations at the top of `stdlib/effect.mli`. If continuations can be reused or cloned, the linearity row for OCaml and the first runtime table change.
- OCaml fiber sizes: read `Stack_threshold_words` in `runtime/caml/config.h` and the assignment to `caml_fiber_wsz` in `runtime/gc_ctrl.c`.
- OCaml foreign-frame barrier: search `runtime/callback.c` for the function that clears the stack parent, and the limitations subsection of the effects chapter of the manual.
- Koka shot classification and finalization: in `lib/std/core/hnd.kk` check that a general control clause still goes through `protect`, that the never-resuming clause still uses a final yield, and whether `kk_evv_is_affine` in `lib/std/core/inline/hnd.c` still returns false. Check the paragraph on resuming more than once in the resource section of `doc/spec/tour.kk.md`; if it no longer admits the double close, Koka may have gained a static discipline and section 7 needs rework.
- Effekt copy-on-shared-resume: read `resume` and `uniqueStack` in `libraries/llvm/rts.ll`.
- Scala syntax and status: read the first screen of `overview.md` and `how-to-use.md` in the capture-checking reference; if the language imports are no longer under `experimental`, update Applicability.
- Model claims: rerun the probe. A failing check d1 means the graded rules admit an unsafe program in the family; a failing e1 means the evidence-vector model diverged from stack search. A passing run establishes only what those checks cover: the model calculus and the enumerated family.
- No cheap check exists for the claims taken from full-text papers; they must be reread if a corrected or extended version is to be relied on.
