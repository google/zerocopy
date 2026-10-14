<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Admitting Rust executions before Aeneas lowering

This document records the correspondence design and its implementation boundary.
The current checker implements the restricted value-and-borrow fragment below.
The broader storage and handler rules remain requirements for future extensions,
not a claim that today's CI certifies arbitrary unsafe Rust. The
[lowering audit](LOWERING_AUDIT.md) records the remaining translator premises.

## Implemented fragment

`run.sh` requests promoted MIR from the pinned compiler. A checked-in Charon
patch saves its imported unstructured AST *before any Charon transformations*.
`admission.py` inspects that snapshot and final LLBC. It follows every function
binding and executable dependency, including original unwind and dead blocks.
A stock driver cannot silently skip the check: the missing snapshot rejects the
run. Drop terminators are rejected before drop elaboration or cleanup can erase
them. During admission, the driver refuses to fall back to optimized MIR for
local bodies if their requested MIR was stolen. We deliberately use promoted MIR
rather than drop-elaborated MIR; no supported execution relies on a destructor's
effects.

The allowed operations are logical integers, booleans, field records, ordinary
arrays/slices, supported borrows, checked indexing/arithmetic, branching, and
loops. Unknown AST constructors and extraction options reject the run. Escaping
borrows, callbacks, raw pointers, foreign ABIs, statics, assembly, drops, union
storage, and general memory observations remain unsupported. Valid incoming
references and Aeneas's reviewed borrow translation are explicit premises.

`external.json` supplies exact reviewed leaves, including standard-library
builtins and two local unsafe helpers. Local opaque body hashes are checked
against Rust-parser body boundaries. The only admitted generic transmutation
instantiation is `u8 -> bool`; its interpretation rejects all other bytes and
instantiations. Byte copying has explicit input and updated-output slices and
rejects oversized sources. Complete-definition checks in `Check.lean` compare
these interpretations and unchecked arithmetic independently, including bad
inputs. Generated external templates must retain failure-capable signatures;
normalization must not lose a guarded call. Pinned builtin mapping and backend
semantics remain trusted correspondence premises, rather than a translation
certificate established by the report.

The report lives in the existing `bindings.json`. It includes both AST digests,
root coverage, visited executions, call boundaries, registry digest, source
identity, Cargo configuration hashes, and patched-runtime provenance. Compiler
overrides are rejected before compilation. A pre-compilation identity must match
at binding time and again after proof checking. Golden and live definitions
remain independent and receive the same complete proof and dependency audits.

Current specifications permit no failure. Source UB aborts may still lower to
panic, but neither outcome is admitted by total or partial contracts. Unwind
paths can contain only non-executing cleanup bookkeeping and terminal failure;
any effectful cleanup rejects admission. There are no supported failure
handlers, spawned threads, or callbacks. A future recovery model must preserve
UB separately; do not infer that every generated panic is catchable Rust panic.

`SafetyTests.lean` proves that sequencing preserves `.undef` and both execution
judgments reject it for arbitrary postconditions. It also checks invalid Boolean
production before discarding or divergence, and every oversized byte copy.
`tests/test_admission.py` mutates a real original extraction to challenge missing
registration, unsupported instantiation, annotated callees, drops, raw storage,
unknown effects/attributes/options, and failure-erasing signatures. Shell
controls challenge well-formed semantic mutations in both proof projects.
These tests establish sensitivity of the checks, not exhaustive rustc semantics.

## Correspondence requirements for the fragment and future extensions

The goal is to accept an extraction only when every operation in the executions
it describes has an adequate interpretation. Finding every annotation, preserving
every explicit call, or rejecting unsupported syntax is individually
insufficient. An implicit destructor can have an effect; a builtin can replace
a call incorrectly; a compiler pass can remove an operation before we inspect it.

The design retains one checking path for every discovered specification. It
does not introduce special root declarations, a second roster of functions, or
per-function options to skip the safety checks. Unsupported cases fail the run.
It also retains ordinary mathematical decoders: no encoder, injectivity law,
or separate representation theorem becomes mandatory for each annotated type.

The core rule is small: follow every executable dependency, and require either
an analyzed body from the controlled compilation or an explicitly reviewed
interpretation of that exact operation. Both must preserve failures as well as
successful behavior. Unknown origins or unsupported effects reject the run.
The rules below explain how to apply this rule before information disappears;
they do not add another specification language or another result type.

## What a successful run would establish

For a discovered function, begin with concrete Rust arguments represented by
the extracted arguments. The mathematical decoders must accept the arguments,
and the written requirements must hold. The caller must also supply the
well-formed Rust state required at the function boundary: valid input values
and, where references are present, the necessary ownership, allocation,
alignment, and interference conditions. A logical referent value alone is not
evidence for those conditions.

Those boundary premises must not assume that the function being proved avoids
UB. In particular, an unsafe operation's guard must appear in its interpretation
and be established by the caller's proof. A general premise saying that every
internal access is valid would merely assume the desired conclusion. When the
current model cannot express the needed guard or frame, exclude the operation.

Subject to the execution correspondence described below, a proved contract
then establishes the following for that invocation:

- A total contract permits only successful termination, with the specified
  postconditions and accepted output decoding.
- A partial contract also permits divergence. Every finite execution prefix
  must still be free of UB. Panic and forbidden execution remain unacceptable.
- Neither contract permits UB before a result is discarded, before divergence,
  or while executing a callee or implicit operation within the invocation.

This is conditional safety, not proof that all safe Rust callers establish the
requirements. It does not certify a whole program, its unrelated threads, or a
value's later destruction by its caller. Native-process termination also needs
the runtime/resource premises of the chosen Rust execution model; an abstract
termination proof does not establish sufficient stack space on every machine.

Bit-validity checks concern producing Rust values, including intermediate
ones. Library-model admission concerns which already-valid values a contract
describes. Failing the former must be an execution failure. Failing the latter
can exclude an input from a conditional contract. These cannot share a rule
that silently treats an invalidly produced Rust value as an excluded input.

## The correspondence rule

Use one relation between concrete Rust execution states and abstract states.
It records the observations and safety conditions needed by the admitted
operations. It can forget details, such as padding contents, if no admitted
operation relies on them.

The required correspondence has three parts:

1. Every concrete execution is covered, not merely the executions that happen
   to return a value. A concrete prefix reaching UB must be incompatible with
   the abstract contract. It cannot disappear into abstract success or
   divergence. Ordinary failure is also incompatible with today's contracts.
2. Every concrete successful result is related to a modeled successful result,
   with the observations needed for the written postconditions. If several
   concrete results share one abstract value, the postcondition must apply to
   all of them. Choosing one convenient result is not an abstraction argument.
3. For total contracts, concrete divergence cannot become abstract success.
   Erased steps must not hide an infinite computation. A proof of progress, or
   an explicitly trusted progress correspondence, is necessary as well as
   preservation of successful values.

To justify these properties compositionally, start from related entry states
without assuming the function's own safety. For each admitted operation,
establish that a permitted concrete step preserves the relation, or that its
bad case produces a failure before execution continues. Compose these local
rules through calls and control flow, including the progress rule for erased
steps. Together with the Lean contract's rejection of failure, they exclude
the first bad concrete step. Do not begin a simulation by assuming that the
entire concrete execution is already UB-free.

This is a stronger requirement than an ordinary compiler correctness theorem
about preserving executions that were already defined. Rust optimizers may
assume UB never occurs and remove branches leading to it; the
[documentation for `unreachable_unchecked`](https://doc.rust-lang.org/std/hint/fn.unreachable_unchecked.html)
gives an explicit example. A correct optimizer is therefore not automatically
a suitable front end for proving absence of source-level UB.

For example, consider this design witness:

```rust
unsafe fn require_nonzero(x: usize) -> usize {
    if x == 0 {
        core::hint::unreachable_unchecked();
    }
    1
}
```

Inspecting an optimized body that only returns `1` cannot justify a source
contract with no requirement on `x`. The admission mechanism must reject that
input body or rely on a separate interpretation of the original operation that
retains its requirement. A sound implementation must not assume the missing
requirement as part of its correspondence premise.

The practical implementation will still trust pinned compiler/importer passes,
Aeneas's supported value-and-borrow semantics, selected backend definitions,
and reviewed external interpretations. These are named correspondence premises,
not Lean theorems supplied by the admission report. The checker is itself part
of the trusted infrastructure until its acceptance rule is formally verified.
No successful test suite makes those premises unconditional.

## The pipeline and its single source of identity

The existing annotation scan supplies the roots and Rust owners. Charon supplies
the final LLBC. A mandatory check runs on that LLBC before Aeneas can consume it.
The existing source-binding checks, conservative golden comparison, two proof
builds, required-contract checks, and compiled dependency audits then run.

Extend the existing binding manifest with the admission result and the inputs
it actually checked:

- Source/configuration identity and discovered Rust owners, including dependency
  sources, the lockfile, target, Cargo features, effective `cfg` values, panic
  strategy, overflow settings, and enabled target features.
- Toolchain pins, applied patches, extraction options, backend identity, and
  the support-policy version. Anneal remains the source of truth for pins.
- The exact LLBC digest, extraction provenance, visited declarations and calls,
  admitted external interpretations, and rejection reasons with source locations.

The claim applies to that exact Rust configuration. A verification-only `cfg`
that substitutes a simpler function body cannot certify the production body.
Additional harnesses may be enabled for extraction, but any change to the
implementation or its dependencies is a different subject. Do not summarize
one verified target/feature selection as coverage of every build configuration.

The manifest remains the one record connecting Rust owners, admission, and
generated declarations. Do not construct another root map or a separately
maintained roster of approved functions. The driver must check and lower the
same immutable LLBC snapshot. The proof builds must use the corresponding
generated modules and source bindings. The final completion record is written
only after all checks finish, and identifies both proof builds and their inputs.

A report is evidence of running a trusted checker, not a translation certificate
checked by Lean. A cached report is reusable only for the same complete input
identity. Missing reports, changed inputs, stale compiled modules, skipped
audits, and development-only extraction are not successful CI verification.
The CI aggregate must require the completed run, rather than interpreting a
skipped job or `--extract-only` exit status as a proof result.

Goldens retain their own definitions throughout checking. Admission of the fresh
LLBC concerns the live extraction; it does not establish a separate Rust
correspondence for an old golden. Both model builds independently pass proofs
and dependency checks. The application of those proofs to current Rust relies
on the live extraction's correspondence, not fuzzy text comparison.

## Admit bodies by their origin

There are two ways to justify an executable dependency:

- Analyze its body, produced by the controlled compiler/importer pipeline, and
  inspect its dependencies using the same rule.
- Select an exact external interpretation, with the guards, behavior, and
  correspondence premises described below. A compiler builtin is such an
  interpretation too; its familiar name does not exempt it from review.

This is an evidence distinction, not a user choice between stronger and weaker
contracts. A body being present in LLBC does not establish its origin. A body
being absent does not establish that the function is harmless. Stop traversal
at a reviewed interpretation because that interpretation covers the operation,
not simply because the declaration is opaque or comes from the standard library.

Choose evidence for the interpretation Aeneas actually uses. If a builtin
replaces a function whose body is present in LLBC, inspecting that Rust body
does not justify the replacement. The builtin needs the external-interpretation
case, with its replacement mapping and failure classification checked. An
analyzed body is admitted only when the reviewed translation uses that body.

Start with freshly compiled local bodies and explicitly modeled external leaves.
An imported dependency body needs evidence that its MIR was produced by the
controlled pipeline. Otherwise give it an external interpretation or reject it.
Keep the existing default sysroot: rebuilding the entire standard library is
unnecessary when its admitted operations have reviewed external interpretations.
If a future proof needs a standard-library body, establish its build origin then.

## Reuse Charon's MIR preservation configuration

Most operation checks use information already present in final LLBC: calls,
operands, projections, residual drops, abort kinds, unwind blocks, function
attributes, types, constants, and trait evidence. Do not add a general earlier
AST export merely because Aeneas later erases some of that information.

The pinned
[Charon MIR selector](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/get_mir.rs#L60)
can silently fall back to optimized MIR when a requested local body has been
consumed. Non-local functions may also arrive as optimized MIR. The inspected
LLBC schema does not attest to the actual stage selected for each body. However,
the query name alone does not tell us which optional optimizations ran.

The pinned [Charon driver already sets](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/driver.rs#L33)
`always_encode_mir = true`, `mir_opt_level = Some(0)`, and
`mir_preserve_ub = true`. Both selected-crate and normal dependency compilation
use this setup. Charon's Cargo command installs the driver as `RUSTC_WRAPPER`
for every crate it compiles. Reuse and validate that implementation rather than
adding duplicate command-line flags or an independently maintained compiler
preset. The existing toolchain provenance record already hashes the driver
and compiler binaries; Anneal remains the source of their pins.

`-Copt-level=0` alone is insufficient: the compiler separately controls MIR
optimization, whose documented default in unoptimized builds is level 1.
The equivalent command-line settings are
`-Zmir-opt-level=0 -Zmir-preserve-ub`. The latter also implies level 0 and keeps
place mentions and reads in trivial switches that could expose UB. These are
[Miri's own defaults](https://github.com/rust-lang/miri/blob/master/src/lib.rs).
Their presence in our driver is established by source inspection. Their adequacy
for our supported fragment still needs the pinned-path review and source-level
negative controls; they are not a formal source-to-MIR correspondence theorem.

The name `optimized_mir` describes a query/stage, not proof that optional
optimizations ran. A body obtained through that query under the reviewed
preservation configuration may be admissible. Require the reviewed production
pipeline instead of banning the query. Reject unreviewed pass overrides,
borrow-checker bypasses, custom MIR, or extraction settings that circumvent that
pipeline. Validate effective inputs, including environment, Cargo/Charon
configuration files, and build-script output; checking our shell arguments
alone is insufficient. Record permitted semantic variations such as overflow
checking as part of the verified Rust configuration.

Preservation is not instrumentation that proves access safety. The same driver
explicitly disables rustc's `CheckAlignment` and `CheckNull` MIR passes.
Supported access operations must have their own modeled guards; do not expect
the compiler to insert all the checks needed by a safety proof.

The configuration must apply when each analyzed crate's MIR is produced.
Current flags cannot undo transformations in precompiled dependency or sysroot
MIR. Charon forces Cargo to rerun workspace extraction, but this does not attest
to every cached dependency's build history. Use a dedicated dependency cache
whose identity includes the controlled pipeline and relevant build inputs,
and whose entries originate from that pipeline. Reuse it only under that
identity. Unknown or externally supplied entries must be rebuilt or rejected.
Directory names and current compiler flags are not evidence of an old entry's
origin. Global initializers, promoted bodies, and CTFE inputs follow the same
origin rule; being called a constant supplies no exemption.

Do not require a new per-body stage export when the reviewed configuration and
artifact origin cover both the requested query and its fallback. If review
finds a relevant erasure that distinguishes those paths, reject that case or
preserve that specific distinction in Charon. A provenance sidecar, if needed,
must be bound to the exact artifact and incorporated into the same manifest.
This conditional extension does not require another complete AST export.

Selecting an earlier stage or using the preservation flags does not prove that
all preceding passes preserved UB-producing prefixes. Review the pinned path
and retain that specific correspondence premise. Any newly discovered erasure
requires rejection, a suitable earlier observation, or a justified replacement.

Charon's existing normalizations remain trusted, with their exact options
recorded. Initially exclude whole features whose normalization hides effects
we cannot justify, especially allocation and custom allocators. If later support
needs information removed by allocator/trait normalization, preserve that
specific information or change that option. Do not guess the original meaning
from the lowered type or a missing field.

## One exhaustive admission traversal

Parse the pinned schema strictly. Require the successful extraction marker,
resolve every referenced ID, and reject missing/error bodies, unknown operation
forms, semantic flags, and unsupported declaration metadata. Known diagnostic
metadata may be ignored. A schema or pin change requires explicit review;
warnings and partial extraction cannot yield admission.

Traverse all discovered roots to a fixed point. Cycles are ordinary recursion,
not a reason to stop examining a body. Inspect a generic body under its declared
parameters; preserve concrete Rust instantiations at call and external-model
boundaries. An erased Lean type or a visited function name alone is not the
identity of an instantiated Rust primitive.

For each body, visit nested blocks, both branch arms, loop bodies, operands,
places and all projections, embedded constants, normal calls, and every unwind
block. Do not rely on source-level `unsafe` markers or prove reachability to
skip unsupported syntax in the first implementation. A conservative rejection
is easier to review than a second optimizer in the checker.

The closure includes callable dependencies, globals and their initializers,
promoted computations, and destruction. Referenced type declarations supply
fields, representation/layout metadata, and implicit-effect information. A
reference to a trait dictionary is not itself execution of every dictionary
method; resolve the method at each possible invocation. Dictionary construction
must nevertheless be checked for any actual construction effects.

Initially permit only calls with a known implementation or an exactly registered
external interpretation. Reject unresolved generic trait calls, function-pointer
calls, unknown callbacks, dynamic dispatch, and escaping borrow reconstruction.
An unannotated ordinary callee can be analyzed; it need not gain a separate
specification. A spec proves its root's behavior through the complete model.

The mathematical `RustModel` dictionaries are interpretations of values. They
are not contracts for arbitrary Rust trait methods and do not establish that
a Rust type has no destructor. Keep these two uses of dictionaries distinct.

## Operation rules for the first supported subset

Start with deterministic integer and initialized-byte computations, ordinary
logical data, and the existing reviewed value-and-borrow subset. The following
rules are release conditions, not exemptions that are already implemented.

| Operation or feature | Admission rule |
| --- | --- |
| Scalar arithmetic, casts, bounds checks, and byte order | Admit only reviewed type/width/mode combinations and their actual backend implementations. A UB overflow mode cannot silently become wrapping arithmetic. |
| Copy, move, assignment, arguments, and returns | Interpret logical values only when the state relation justifies erasing physical transfer effects. Exact general typed storage is excluded. |
| Creation of values from storage or unchecked construction | Require a guarded producer interpretation before the typed carrier is entered. Invalid production remains forbidden even if its value is unused. |
| `PlaceMention` and projected place formation | Reject unless a reviewed rule proves the projections valid in related states. A count of reference/field projections or absence of raw pointers is insufficient. |
| Residual `Drop`, including conditional and unwind drops | Reject initially. `-eval-drops` does not execute the destructor. Enabling it is not admission. |
| `#[target_feature]`, dispatch variants, unsupported ABIs | Reject initially. Later support must require the real platform/ABI conditions at the call boundary. |
| Raw pointers, unions, raw-memory constants, transmutation, FFI, assembly | Reject unless a specifically admitted primitive completely interprets the operation; no generic successful placeholder. |
| Allocation, allocator parameters, interior mutation, atomics, concurrency | Exclude initially; logical return values alone do not describe their effects. |
| Borrow reconstruction that returns hidden state transformers | Reject until the transformer semantics and state validity are checked. |
| Error or unsupported syntax, missing dependencies | Reject extraction. Never turn a failed analysis into a successful model. |

Existing value proofs need not be false when these rules reject their extraction
for a stronger claim. In particular, the preserved extraction contains projected
place mentions and numerous opaque dependencies. Each needs a justification;
their presence does not warrant a blanket allowlist. Do not advertise this
design as already admitting all current roots for source-level UB-freedom.

Charon removes some proven-trivial drops. That removal is part of the reviewed
normalization premise. Do not infer that every generic or opaque type has a
trivial destructor just because no destructor body was imported. A future drop
implementation must extract precise drop glue, inspect its callees and unwind
paths, and preserve conditional/uninitialized/packed-place semantics.

The source state relation must justify ordinary reference dereferences,
reborrows, retagging, and field projections. For the restricted safe-borrow
subset, this can use the existing borrow semantics and explicit caller frame
premises. Introducing a pointer-producing primitive expands that obligation;
it must not inherit approval just because its output lowers to the same logical
referent type. Unsupported reference validity or interference rules remain
rejections rather than implicit assumptions that every access is safe.

## Failure, unwind, and divergence

The existing total and partial contract predicates reject every failure. The
downstream `.fail .undef` marker additionally records forbidden or unsupported
execution. Sequencing preserves failure even when a continuation discards its
argument or diverges; the current Lean tests establish this fact.

The pinned translator collapses some source UB and panic branches into the
same failure. That is conservative for today's failure-rejecting contracts,
provided the branch is retained. It does not justify panic-tolerant contracts.
Keep panic catching, failure recovery, thread spawning, callbacks with unknown
effects, and panic-tolerant specifications unsupported in this policy.

Inspect unwind blocks even though Aeneas ignores them. A structural rule can
admit a simple exceptional suffix only when it is entered exclusively after an
already-modeled failure, cannot reenter normal execution, and contains no
unclassified effects. Existing proofs exclude that failure on admitted inputs.
`UnwindResume` in such a suffix is not the same as permitting it on a normal
execution path. Residual destruction remains rejected there as elsewhere.
If the rule cannot establish the connection to modeled failure, reject it.

An external interpretation cannot return `.div` as a placeholder for unsupported
behavior. A partial contract would then accept it. Its correspondence must
establish that divergence represents only safe infinite execution prefixes.
For example, UB followed by an infinite loop is forbidden, not divergence.
Returning `.undef` for a known unsupported case fails closed; classifying that
case as divergence does not.

Follow complete compiled execution dependencies, including opaque helper bodies.
Retain the existing rejection of downstream `Option.ofResult` and other
unapproved recovery definitions. Stop only at the actual pinned backend modules,
whose implementations have been reviewed for the admitted operations. Namespace
spelling must not let downstream code impersonate those modules.

The current backend-boundary audit alone is insufficient for broader safety
claims: review the specific builtins reached by admitted operations, including
their failure conversions and extraction metadata. Calling a builtin
infallible can cause Aeneas to erase it before any Lean dependency audit. The
input admission rules must exclude that builtin or justify the classification.

The adapter blacklist is a regression check, not a complete proof that failure
cannot be erased. An author could write the same recovery with a direct match
on `Result`. Close that gap through ownership and complete primitive laws:
application execution definitions must come from the unchanged admitted
extraction or a registered interpretation with its checked whole-domain law.
The pinned execution combinators they use also require review, including their
failure behavior; a backend namespace alone supplies no exemption. Arbitrary
handwritten execution helpers do not gain admission merely by passing the axiom
audit. Helpers inside a registered interpretation are covered by that
interpretation's complete law.
Do not attempt to recognize every possible failure-erasing program by name.

Apply this ownership rule to definitions that determine the executable model.
Ordinary proof lemmas remain ordinary Lean code, subject to the existing proof
and axiom checks. Mathematical decoders also retain their existing role of
defining a contract's domain and observations. Neither a proof helper nor a
decoder may replace the generated execution or turn an unsafe primitive's guard
into an optional library-admission check.

## External interpretations are explicit trust boundaries

For each admitted primitive, record its Rust definition identity, crate/source
identity, complete signature and generic arguments, supported instantiations,
target/ABI assumptions, Lean implementation, and relevant extraction settings.
Specify its successful behavior, its safety guard, its failure behavior, and
whether it can affect state. Bind it through the existing ownership manifest.

An unsupported callee can become such a boundary; it need not remain rejected
forever. Register the exact Rust item and the Lean interpretation, then derive
the precise Charon `--opaque` selection from that registration. Opaqueness
retains the callable declaration and its signature while omitting the body.
Do not exclude the call or turn it into a successful placeholder. An opaque
declaration without an approved interpretation remains an error. This applies
to locally defined unsafe helpers as well as standard-library operations.

The registration must identify the actual replacement selected by Aeneas,
including its failure classification. A guarded unsafe operation must remain
capable of failure, even when its result is unused. Keep argument evaluation,
original parameters, returned values, and explicit updated states. The chosen
signature and carriers must contain enough information to state its safety
conditions and effects. Opaqueness does not repair a carrier that has already
forgotten a pointer's address, provenance, or relevant storage state. If that
information cannot be supplied by the admitted interface, reject the boundary
until its interface has an adequate interpretation.

Prefer an ordinary Lean definition with an explicit guard and forbidden branch.
It is axiomatic with respect to Rust: correspondence to the omitted Rust body
is a trusted premise, even though Lean can prove facts about the supplied
definition without adding a logical axiom. The existing unchecked-arithmetic
models use this form. Supporting a literal Lean axiom or an axiomatized behavior
law would additionally require an exact, reviewed extension of the compiled
axiom policy. Never admit arbitrary axioms or a blanket axiom asserting an
inline specification. An inconsistent logical axiom can prove anything; the
guard mechanism cannot repair that inconsistency.

Report a substituted Rust item as a trusted interpretation, including when it
also owns an inline specification. Proving that specification about the Lean
interpretation does not prove correspondence to the omitted body. A local
substitution should also be visible at its Rust declaration so a source reader
can distinguish an assumed boundary from an analyzed implementation; its exact
annotation syntax remains to be designed. As support grows, the same boundary
can be replaced by an analyzed body without changing callers' contracts.

For example, admitting `usize::unchecked_add` requires the selected Rust
definition and word width, the exact Lean external definition, the guard
`left.val + right.val ≤ Usize.max`, the exact sum on the good branch, and
`.fail .undef` on the bad branch. Its extraction classification must permit
failure and preserve argument evaluation. It cannot be classified as infallible
merely because a caller is supposed to establish the guard: doing that could
erase an unused call before the caller's proof ever sees its obligation.

Do not register by an unqualified name, broad path wildcard, or Lean signature
alone. Distinct Rust types can erase to the same Lean type, particularly around
ABI reads. Trait implementation identity and Rust type instantiation remain
relevant even when the emitted function signature looks identical.

Recording the identities is necessary but not sufficient. If two Rust
instantiations need different ABI or safety observations but the model maps
both to one indistinguishable observation, reject that combination or supply
separately justified data parameters. The existing `Type → Usize` layout input
must not silently identify incompatible Rust instantiations merely because
their Lean carriers coincide. Documented correspondence premises must be
realizable for the claimed instantiations, rather than contradictory premises
that make a contract vacuously true.

Use the existing complete-definition check for simple guarded primitives such
as unchecked addition and multiplication. A theorem about successful inputs
alone cannot detect a changed implementation on bad inputs. Check the complete
guarded definition, including its failure tag, against an independently stated
expected interpretation. A more complex primitive needs an appropriate checked
semantic law over its whole modeled domain, not just its useful branch.

Such a check proves that the supplied Lean interpretation is the one intended
by the policy. It does not prove that Rust implements it. That correspondence
remains reviewed and documented. Primitive code, correspondence premises, and
policy changes therefore require review as verification infrastructure, even
when application reviewers primarily read `.rs` specifications.

Do not import stateful or nondeterministic operations into deterministic pure
models. Aeneas can merge repeated calls and eliminate computations classified
as infallible. Future stateful support must make state/effects explicit and
justify the applicable transformations before being admitted. A hidden global
effect is not made harmless by returning `()`.

## Bit validity and padding

For a byte-producing pilot, the storage carrier records initialized payload
bytes. An operation that produces a Rust `T` first checks access conditions
and decodes storage according to `T`'s bit-validity rules. Only success may
produce a value in the extracted typed carrier. A decoder for `bool`, for
example, rejects bytes other than `0` and `1` before creating Lean `Bool`.

That guard must be part of the primitive's execution, not a `requires` clause
silently added after the invalid production has happened. The caller's proof
must establish it or the primitive fails. Check the result even when discarded,
before a mathematical projection, or before divergence. Later library-model
decoding can impose further requirements on an already-bit-valid value.

Until typed-copy effects are supported, forget all padding contents and
initializedness. A padding write still evaluates its arguments and satisfies
write-access conditions; it cannot establish retained storage information.
Reject later reads, wider reinterpretations, hashing, byte comparison, and
other observations that rely on forgotten bytes. Mask padding at every boundary
that could expose it, not just typed copies. Initially prefer padding-free
storage such as `MaybeUninit<[u8; N]>`; its eventual interpretation still needs
initialization and access guards.

<!-- FIXME: Support for general typed copies is tracked by
https://github.com/AeneasVerif/aeneas/issues/1405. Do not model arbitrary
MaybeUninit<T> as exact persistent bytes while physical transfers are erased. -->

The mathematical field decoder remains free to choose a coarse abstraction.
The execution state relation, storage primitives, and operation contracts must
retain whatever information safety and the written observations require. This
does not require mathematical models to have canonical raw representatives.

## Tests that must fail for the right reason

The following are design witnesses for future controls, not tests already run.
Use real source-to-LLBC-to-Lean examples as well as small checker fixtures.
Separate admission rejection, extraction rejection, and proof rejection in
diagnostics; only an elaborating bad model challenges a Lean proof boundary.

| Deliberate violation | Required result |
| --- | --- |
| UB-producing call whose result is discarded | Failure remains; `ensures _ => True` cannot be proved. |
| UB-producing call followed by an infinite loop | Partial correctness cannot classify the execution as acceptable divergence. |
| Invalid boolean/nonzero production, followed by dropping the value | Producer guard rejects before entering the typed carrier. |
| Destructor containing a forbidden operation, including generic or unwind drop | Admission rejects residual drop; eventual supported drop exposes the failure. |
| Invalid projected place with otherwise constant return | Admission rejects the unproved projection rule. |
| Unsafe callee hidden by trait dispatch or a callback | Resolve and inspect the real callee, or reject the call. |
| CPU-feature-dependent callee with an innocuous body | Admission rejects missing platform support. |
| Changed Rust type instantiation with the same Lean carrier | Primitive identity/instantiation check rejects mismatched interpretation. |
| Unapproved MIR configuration or a precompiled body that hides an unsafe branch | Configuration/body provenance rejects it; a final AST scan alone must not count as success. |
| Pass override, custom MIR, or borrow-checker bypass supplied through another configuration input | Effective-input policy rejects it even though the driver still sets MIR optimization level 0. |
| Old dependency artifact placed in an otherwise correctly named build cache | Unknown production origin prevents admission until rebuilt or justified. |
| Unsafe access with no alignment/null guard in the model | Admission rejects it; preservation settings and compiler check insertion cannot supply the missing guard. |
| Local opaque helper wrapping failure erasure | Compiled dependency audit rejects it. |
| Handwritten recovery that matches on `Result` without using a blacklisted adapter | Closed execution ownership or the complete primitive law rejects it. |
| Stateful primitive modeled as an infallible pure unit result | Input policy rejects the interpretation before optimizer erasure. |
| Builtin replaces an inspected Rust body with a different execution | Admission checks the actual replacement and its failure classification; inspecting the unused body supplies no approval. |
| Read relying on a previously written padding byte | Storage policy rejects the observation instead of supplying convenient initialized bytes. |
| Missing root, missing dependency, unknown semantic flag, changed LLBC, or stale report | Whole verification run fails. |
| Golden proof passes while live proof fails, or vice versa | Whole verification run fails. |
| Byte/ABI interpretation changed for another target | Configuration identity prevents reuse; new target needs its own correspondence. |

## Implementation order and remaining obligations

1. Extend the existing LLBC preflight with one strict traversal, closed schema
   handling, root/dependency resolution, source diagnostics, and an admission
   report. Add rejection fixtures from the operation inventory. This improves
   coverage without yet asserting source-level memory safety.
2. Validate Charon's existing MIR preservation setup and enforce controlled
   build origins and effective inputs. Use reviewed interpretations for external
   leaves; add earlier-stage evidence only for a concrete unresolved erasure.
   Close the compiler/importer correspondence for the restricted fragment.
   Review normalization and the reached backend mappings. Resolve projected-place and reference rules before
   accepting them; reject unresolved cases, even in current roots.
3. Integrate the mandatory report with the existing two proof builds and final
   completion path. Add freshness and skip controls. Maintain a single policy
   for all discovered roots in that run.
4. Add guarded bit-validity producers for a small padding-free byte subset,
   with complete-definition checks and source-level negative controls. Expand
   storage, destruction, state, or concurrency only with their missing semantics.

Release of a source-level safety claim is blocked until the MIR provenance,
restricted correspondence, operation rules, primitive interpretations, and
mandatory CI path are all supplied. A checker prototype that merely scans
final LLBC must continue to report the existing conditional functional claim.

This design narrows the accepted language to avoid known gaps; it does not
formally verify rustc, Charon, Aeneas, or the checker. Removing those trusted
premises would require verified translations or kernel-checked certificates.
The practical guarantee is conditional on a finite, explicit trusted boundary,
with no known unsupported operation silently accepted within that boundary.
