# Proposed E33 compiler-bound ABI witness experiment

*Authored by an AI agent acting on joshlf's behalf.*

This is a preparation checkpoint. No compiler, observer, native subject, target
query, linker or container was invoked. The new observer and fixtures have not
been compiled. E33 is not marked complete by this plan.

The first useful experiment is an actual structured export from the retained
May 1 compiler (`f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`), paired with its
LLVM IR and caller/callee assembly for the same independently chosen source,
target, instance and options. A small consumer then compares artifact data with
an independently generated observation under its fixed request. This supplies a
bounded trusted-compiler witness prototype; it is not a proof of rustc's ABI
classification or Rust-to-machine correspondence.

## Subject and acceptance authority

`requests.json` fixes four proposed native-host profiles: ordinary subjects and
fixed-width vectors, each at optimization0 and2. Each profile binds source and
selector bytes, actual compiler/runtime identities, built-in target triple,
edition, crate name, panic mode, CPU, target features and incremental setting.
The consumer's request selection must come from an independently fixed catalog
or explicit consumer authority. A producer cannot supply a new request/root/hash
and have that redefine the requested claim. Producer input consists only of
candidate witness bytes. A stronger or weaker-looking root is still rejected
if it differs from the consumer's choice.

Before any future compiler launch, validate the caller request and all selected
bytes, reject duplicate JSON keys/unknown fields and arbitrary flags, require a
fresh owned output directory, and check the tool/runtime closure available here.
Run one compiler at a time, cap each process's address space and time under the
parent's reviewed harness, retain all streams/statuses and hash tools before and
after. A fresh request-source copy must preserve the same source bytes. Read
compiler-loaded local sources back from the observation and compare them to the
request. Compare the complete structured observation; do not exempt provenance,
attributes, instances, hidden operands or configuration fields. Public path
projection, if later needed, belongs to a display copy with raw/restoration
receipts, not to the acceptance predicate.

`proposed_observer.rs` reads selectors supplied by that future validated consumer
and stops after `after_analysis`. It is not itself a complete request checker or
producer-input acceptor. No executed schema/consumer is claimed yet. The planned
acceptor must distinguish malformed input, unsupported selection, compiler query
error, operational failure and semantic mismatch. An unexpected panic or assert
stops dependent work for diagnosis; an output file or exit0 alone is insufficient.

## Source-backed mechanism

The inspected implementation defines `FnAbi` as argument/return `ArgAbi`s,
canonical convention, variadic/fixed count and unwind permission. Each `ArgAbi`
contains a layout and `PassMode`: ignored, direct, pair, cast or indirect. Export
all attributes (raw bitset, extension, pointee size/alignment) and every cast
component, not only a debug rendering or a count of source arguments. The
proposed layout export includes size/alignment, field offsets, scalar ranges,
backend representation and complete supplemental compiler debug layout. These
scalar ranges are compiler layout facts, not a complete source validity or
aliasing semantics. Supplemental type/variant renderings remain opaque compiler
output; no verified general decoder is asserted.

The source deliberately makes `ArgAttributes::eq_abi` compare only `InReg` and
extension while ignoring noalias, nonnull and pointee properties. It is therefore
too weak for this witness's complete semantic-attribute comparison. Likewise,
printing a `NoAlias` attribute is not a proof that the caller owns the required
Rust resource or that a chosen machine proof satisfies it.

`TyCtxt::fn_abi_of_instance` chooses body-derived attributes only when optimizing
and incremental compilation is absent. LLVM emission separately suppresses many
optimization attributes at optimization0. Query output and emitted IR need not
have identical visible attribute lists. Record both layers and interpret their
relationship using the source, rather than declaring a mismatch or silently
dropping attributes. Body-derived deduction here further applies to Rust-ABI
indirect parameters, not every C or direct scalar argument.

Instance and function-pointer queries are separate. The instance construction
can append a `#[track_caller]` location argument; the function-pointer construction
sets caller location and determined body to none. A tracked function coerced to a
function pointer may involve a compiler shim; this plan does not conflate the
selected direct instance with that shim or prove a coercion theorem. Generic
`generic_id::<u8>` and `generic_id::<u64>` are explicitly distinct selections.

The source sanity checks contain assertions for inappropriate query shapes. The
proposed finite observer rejects extras on nonvariadic signatures before querying,
rejects arbitrary generic argument kinds, and excludes scalable vectors and
virtual/TLS/closure shims. Future requests must remain inside the reviewed source
and query table; this is not a panic-finding or arbitrary compiler-input experiment.

## Planned subjects and discriminating checks

| Subject | Planned observation and its limit |
|---|---|
| C/system/Rust narrow integers and bool | Extension, scalar valid ranges, convention identity; same host system/C result would not imply portability. |
| C/system `repr(C)` pair and Rust tuple | Equal sizes do not determine passing shape; export field offsets and cast/pair representation. |
| C/system/Rust three-word aggregate | Return indirection and argument mode; hidden result is represented by `ret.mode`, not necessarily an extra `FnAbi.args` element. |
| HFA and fixed-width vector | Distinguish homogeneous aggregate casts, vector representation and target feature/configuration. No scalable-vector or universal SIMD claim. |
| Raw pointer, shared reference, mutable reference, `UnsafeCell` reference | Compare actual full attributes without inferring ownership from their names or absence. Raw pointer is only returned, never dereferenced. |
| Rust slice/unit/track_caller | Wide metadata, ignored ZST, hidden caller location; no synthetic vtable-layout claim. |
| Generic scalar instances | Bind complete selected type arguments and reject stale instance reuse. |
| Variadic pointer types plus compile-only caller | Fixed-count and promoted i32/f64/raw-pointer extras; no variadic definition, foreign execution or assumed ABI-invariant extra allocation. |
| Twelve-scalar foreign call | Inspect actual caller and callee placement to expose register exhaustion and stack slots. No native call to the unresolved foreign symbol. |

These are planned observations, not outcomes. Darwin source predicts extension
of small C integers to32 bits, ordinary <=128-bit aggregates cast to integer
units, eligible HFAs cast consecutively, and larger aggregates returned
indirectly. These predictions need the actual query/IR/assembly check; exact
attribute lists and concrete outputs remain unknown.

The defined bodies operate only on typed initialized values. They never read
padding or forge references. Mutable references require ordinary exclusive,
aligned, initialized access; shared and slice references require their ordinary
validity/lifetime premises. Foreign call wrappers and vectors are compile-only.
No runtime validation, foreign implementation, alias-violating control, invalid
representation or target-specific native execution is authorized by this plan.

## Physical placement and missing target dependencies

`PassMode::Indirect.on_stack` specifically means byval/fixed stack-offset passing;
it does not enumerate the stack placement of otherwise-direct scalar arguments
after registers run out. `FnAbi` also does not contain a general register map or
Windows shadow-space ledger. Use emitted caller/callee code for those concrete
observations and keep LLVM lowering trusted. For an indirect result, the inspected
LLVM code adds a pointer parameter and returns void. Physical placement, including
AArch64 x8, still needs the selected emitted code's actual evidence.

Only `aarch64-apple-darwin` target libraries are installed in this May1 toolchain.
The local channel manifest advertises exact matching x86_64 MSVC, x86_64 Linux
and AArch64 Linux std archives; their URLs/hashes are recorded in
`source-identities.json`. No download, install or target query occurred. The
separate Rust1.89 E08 Linux target libraries are incompatible with this compiler
and cannot fill that prerequisite.

The smallest useful later extension is x86_64-pc-windows-msvc compile-only output
for a caller with six/twelve scalar arguments plus the aggregate cases. It needs
matching May1 target core/alloc/std components (the rust-std archive supplies
them) and confirmation that this retained compiler's backend supports that
target. Empty standalone codegen-backend directory entries do not establish
missing LLVM support; support remains unqueried here. No Windows SDK, linker or
runtime is needed for the proposed library IR/asm/obj output. Executing or linking
Windows code would require separate resources and authorization.

A Windows observation must establish actual caller shadow-space/stack accesses,
not infer a 32-byte reservation solely from `FnAbi`. The previous four-target C
report is a useful comparison lead, not an actual May1 Rust cross-target result.
Windows target setup is optional until explicitly authorized; report a missing
resource as such, not target unsupportedness. Source-level Microsoft dispatch
and aggregate rules alone do not complete the machine-placement observation.

## Minimal execution sequence proposed for review

1. Parent authorizes one host observer build and inspects actual linkage/load
   commands and runtime hashes before running it. The historical copied-observer
   loader failure is a reason to validate the new binary's actual dependencies,
   not to patch an old binary or assume relocation safety.
2. In fresh owned outputs, run the four fixed host profiles serially (two
   subjects/two optimization levels), with each valid source/query reviewed
   first. Obtain full structured witnesses, raw streams and statuses.
3. Emit matching IR/asm/obj separately under exactly those profiles; bind all
   outputs and actual codegen configuration. Inspect the named signature,
   hidden-result and argument placements, including caller/callee stack evidence.
4. Implement and review the small strict consumer, then accept exact candidate
   observations and reject every negative in `controls.json`. These controls
   modify data only. Candidate source/target/flags never replace the fixed
   consumer request, and no malformed candidate is executed.
5. Only after a separate grant/setup, repeat the selected compile-only Windows
   cases. Native host tests, if later requested, need a separate safe wrapper
   avoiding unresolved foreign calls; they are not necessary to export FnAbi.

`commands.json` contains nonexecuted argv templates, not completed commands or a
runner. Material prerequisites remain observer compilation, loader validation,
strict consumer implementation, actual captures/controls and placement inspection.
No experiment result or E33 completion is recorded at this checkpoint. A verified
classification checker or a Rust/resource-to-machine theorem is a stronger,
separate future goal; the bounded trusted-compiler witness must name that frontier.

## Primary bindings and previous evidence

`source-identities.json` records hashes and line coordinates for the directly
inspected installed compiler sources. Those source copies and retained binary
identities are read-only inputs; no upstream source mirrors are included here.
The installed channel manifest is the local distribution authority for optional
target archive identities. No remote URL was fetched during this preparation.

The earlier canonical `rust-function-abi-witnesses-b940084` report has actual
Rust LLVM/assembly observations from a different compiler and four-target C
compiler outputs. Its report body hash is recorded for comparison, without
substituting its compiler or C results for the proposed f53 Rust observations.
This preparation leaves E10/P127/P131 source-capture/meaning frontiers and E41
universal unwinder/resource proof unchanged.
