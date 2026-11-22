# Ownership and Borrowing Across Moving-GC Foreign Interfaces: Root Registration, Pinning, Safepoint Tokens, Finalizers, and Reentrancy

## Summary

Native code that holds a name for a managed object must keep that name meaningful while a
collector relocates or reclaims objects. Four widely used interfaces (JNI, the OCaml C
interface, PyO3 over CPython, and WebAssembly GC) and the verified-collector literature all
resolve this with the same three ingredients, and differ only in where each ingredient
lives:

1. **Identity is separated from address, and the address map is replaced at safepoints.**
   Every formal treatment of a moving collector examined makes the map from object identity
   to address a parameter that a collection may replace (JNI Light names it and abstracts
   it away): the concrete-to-abstract map `$toAbs` of
   Hawblitzel and Petrank (allocation "modifies `$toAbs`, which potentially invalidates any
   pointers that the mutator possesses"), the `repr` predicate of McCreight et al., the
   injective map `f` of CakeML's `gc_related`, the "flatten function" of JNI Light, the
   resource `GC(θ)` of Melocoton, and VeriFFI's graph predicates "preserved under
   g.c.-isomorphism". A flat machine address is a fact *relative to the current map*; a
   registered root or handle is a name that survives the replacement.
2. **The interfaces place the surviving name in four different carriers.** JNI hands out
   opaque references into a per-call registry and offers flat addresses only inside
   pin-or-copy windows. The OCaml C interface hands out *transparent* flat words (`value`)
   and obliges the callee to register the C variables holding them so the collector can
   rewrite them. PyO3 hands out reference-counted pointers branded with a copyable scope
   token, which suffices only because CPython object addresses are constant for an
   object's lifetime. WebAssembly GC makes references opaque in the type system
   ("neither their size nor their bit pattern can be observed", storable "in tables but not
   in memories"), so relocation is unobservable by construction and byte-addressed
   linear-memory data can refer to a managed object only through a table index.
3. **Relocation points, reentrancy points, and thread-release points are three different
   sets, and exclusivity follows none of them automatically.** In OCaml since 4.10 an
   allocation may collect but is "guaranteed not to run any OCaml code, including
   finalisers"; polling pending actions, calling back, and releasing or re-acquiring the
   domain lock may. JNI states that pinning an array does not lock it. PyO3 documents that
   the `'py` brand proves attachment, not exclusion, and enforces `&mut` access to
   Rust-backed objects with a run-time borrow flag. A name that stays *valid* across a
   safepoint is therefore not a name that stays *exclusive*, and finalizers are reentrant
   code that no frame called.

A Rust-side static discipline matching ingredient 1 is documented for OCaml (Boxroot;
`ocaml-interop`) and SpiderMonkey (Josephine): unrooted values are copyable borrows of a
runtime token, and every operation that may collect takes the token by unique borrow, so
the borrow checker rejects use of an unrooted value after a safepoint ("garbage collection
as iterator invalidation"). Josephine states its memory safety "is conjectured, but not
proved formally".

A Mathlib-free Lean 4 toy model accompanies the report `[kernel-checked proof]`
`[toy model]`. It proves, over an abstract heap with a root table, a pin set, and an
arbitrary relocation map: (a) for every live unpinned object and every free address there
is a legal collection after which the object's old flat address is empty, and for every
two live unpinned rooted objects one after which the first object's old flat address
silently reads the *other* object; given a free address, a flat address is stable under
all collections exactly when the object is pinned; (b) handle dereference and handle
identity are invariant under every collection, and every program accepted by an epoch-branded token discipline never
dereferences a stale flat address, for all relocations and all reentrant writes; (c) an
unchecked reentrant callback or synchronously run finalizer changes the value under an
outstanding exclusive borrow, while a dynamic borrow check preserves it for every
reentrant action list; plus resurrection and ordering results for finalizers.

**Model–system relation: none proved.** The Lean development is a finite abstract model
written for this report. No theorem in it is connected by proof to HotSpot, the OCaml
runtime, CPython, PyO3, any WebAssembly engine, or any cited formalization.

## Applicability

**What the findings apply to.** The findings describe the *documented contract* between
native code and a managed runtime at four interfaces, and how published formal work models
that contract. They are statements about specifications, upstream documentation, and
papers, read on 2026-11-22. No runtime, compiler, or library source was inspected, and
nothing was executed against any runtime; the only execution evidence is the Lean kernel
check of the toy model.

**How the subjects in `REPORT.json` relate.** This is a comparison, organised in three
groups:

- *Interface descriptions compared side by side.* The Java Native Interface Specification
  for Java SE 25 (normative); the OCaml 5.4 manual chapter "Interfacing C with OCaml" and
  the `Gc` library and parallelism chapters (upstream documentation; there is no separate
  standard); PyO3 0.30.1 API documentation and the PyO3 user guide on its `main` branch,
  read together with PEP 703 for the thread-state model PyO3 wraps; the WebAssembly
  Specification release 3.0 (draft dated 2026-11-20), the WebAssembly JavaScript Interface
  source, and the GC proposal's design documents.
- *Formal and semi-formal literature through which those contracts are interpreted.*
  Verified collectors and their mutator interfaces (McCreight, Shao, Lin and Li; Hawblitzel
  and Petrank; Sandberg Ericsson, Myreen and Åman Pohjola, with the CakeML backend paper
  for its foreign-function oracle; Gammie, Hosking and Engelhardt), foreign-interface
  semantics and checkers (Tan; Furr and Foster; Lee et al.; Guéneau et al.; Korkut, Stark
  and Appel), and ownership-typed interfaces to collected heaps (Jeffrey; Munch-Maccagnoni
  and Scherer; the `ocaml-interop` crate documentation; Hughes and Tratt).
- *The toolchain on which the toy model was checked.* Lean 4 `v4.34.1`. The model
  characterises no subject; it makes the report's derived claims checkable.

**Version scope.** JNI statements are those of the Java SE 25 edition; the passages quoted
on references and critical regions were not compared with earlier editions. OCaml
statements are those of the 5.4 manual; the allocation guarantee is dated by the manual
itself ("Since 4.10"), and domain-related statements apply to OCaml 5. PyO3 statements use
the 0.30.1 names `Python::attach` and `Python::detach`; the guide was read from the moving
`main` branch (repository head `be9e428ab7573552c65aa9e7a7a0c6d14b06fd5d` on the
observation date), so guide wording is not pinned to 0.30.1. CPython statements cover the
default and free-threaded builds as PEP 703 describes them; PEP 779 (status Final, Python
3.14) records the free-threaded build's supported status. WebAssembly statements are
those of release 3.0, which incorporates the garbage collection extension; the proposal's
`Overview.md` is described by its own repository as out of date in its concrete details
and is used here only through `MVP.md` and `Post-MVP.md`.

**Scope of the claims.** "Moving" covers any collector that may change an object's address
or reuse its storage while native code is live. CPython is included as the contrasting
non-moving case, because the adequacy of PyO3's token design depends on exactly that.
Statements about what a carrier *permits* are statements about the documented contract; an
implementation may be stricter (for example by checking) or may happen not to move a given
object.

**Cross-references to adjacent packages of this corpus (material not duplicated here).**

- `multi-runtime-ffi-gc-interop-handles-and-shared-address-clashes` holds the runtime
  overview this report builds on: collector-specific implementations of JNI critical
  pinning, CPython free-threaded reference counting, cross-heap reference cycles,
  process-global signal and lock collisions, and bridge generators. None of that is
  repeated; this report adds the formal reading of roots, pins, safepoints, and borrows.
- `semantic-multi-language-interop-dimsum-melocoton-and-linking-types` covers Melocoton's
  wrapper semantics and address map at the level of its Coq definitions, VeriFFI's
  architecture, and the multi-language semantics landscape. Here Melocoton and VeriFFI
  appear only as two rows of the address-map comparison.
- `handle-tables-scoped-arenas-and-cross-runtime-ffi-pinning-protocols` covers handle-table
  and scoped-arena implementations; `garbage-collection-barriers-safepoints-and-runtime-invariants`
  and `colored-pointer-load-barriers-zgc-immix-lines-and-mmtk-collectors` cover the
  compiler and collector side (stack maps, derived pointers, barriers, safepoint polls).
- `cross-heap-cycle-collection-external-accounting-and-linear-finalization` and
  `jls-finalization-reachability-fences-go-keepalive-agesen-detlefs-moss-stack-liveness-shaham-heap-liveness-hirzel-type-accuracy-and-rojemo-runciman-lag-drag-void`
  cover finalization timing, reachability fences, and cleanup APIs in Java and Go.
- `reentrant-ffi-mixed-mir-isa-call-stacks-tree-borrows-and-oracle-composition`,
  `rust-drop-reentrancy-interior-mutability-and-arena-borrowing-invariants`, and
  `rust-c-ffi-tbaa-noalias-dead-store-hazards-and-tls-destructor-reentrancy` cover
  Rust-side aliasing models and reentrancy without a collector.
- `python-cpython-object-protocol-free-threading-jit-and-c-api-ffi`,
  `jvm-bytecode-verification-jmm-causality-valhalla-loom-and-panama-ffi`,
  `wasm-component-model-truffle-graal-and-polyglot-interop-platforms`, and
  `mswasm-colored-memory-safety-van-strydonck-linear-capabilities-georges-uninitialized-capabilities-skorstengaard-local-capabilities-richwasm-and-cherivoke-sweeping-revocation`
  cover the individual runtimes and typed WebAssembly variants in depth.

**Model–system relation: none proved.** The toy model's vocabulary (heap, root slot, pin,
safepoint, brand, borrow flag) is chosen to mirror the documented contracts, but the
correspondence is an interpretation stated in prose, not a theorem.

## Findings

### 1. One contract, stated once

Basis: derived (from the normative and documentation sources quoted in Findings 2 to 6)

Write `ι` for an object identity, `θ` for the current partial map from identities to
machine addresses, `R` for the set of root cells the runtime knows about, and `P` for the
set of pinned identities. A *safepoint* is a program point at which the runtime may replace
`θ` by some `θ'`. Every interface examined documents the same four obligations:

- **Root.** At a safepoint the runtime preserves the objects reachable from `R` (and from
  `P`) and rewrites the cells of `R` to hold addresses under `θ'`. It rewrites nothing
  else. An object reachable only from native locals may be absent from `θ'`.
- **Brand.** A flat address `θ(ι)` held by native code is meaningful only under the `θ` it
  was read from. After a safepoint it must be re-read from a root cell.
- **Pin.** For `ι ∈ P`, `θ'(ι) = θ(ι)`.
- **Handle.** A handle names a root cell rather than an address, so it is meaningful under
  every `θ'`. Identity comparison must go through handles (`IsSameObject`, `ref.eq`), not
  through flat addresses read under different maps.

The interfaces differ in three choices, tabulated below and substantiated in the following
findings: whether native code is given `θ(ι)` at all; which program points are safepoints;
and what bounds the validity of a handle.

| Interface | What native code holds | Flat address exposed? | Points at which `θ` may change, as documented | Bound on validity of the name | Pin primitive |
|---|---|---|---|---|---|
| JNI | opaque local, global, or weak global reference | only inside `Get…ArrayElements`, `Get…Critical` windows, which may return a copy | any time ("garbage collection may occur while native methods are running") | local: the native call and the creating thread; global: explicit delete; weak global: until cleared | `GetPrimitiveArrayCritical`, `GetStringCritical`; `Get…ArrayElements` ("If the VM supports pinning, the pointer to the original data is returned; otherwise, a copy is made") |
| OCaml C interface | the flat word itself (`value`) in a C variable registered with `CAMLparam`, `CAMLlocal`, or a global root | yes, always | allocation and any runtime call that may allocate | registration: the C function activation (`CAMLreturn`) or explicit removal | none in the examined chapter; avoid collection or copy out |
| PyO3 over CPython | `Bound<'py, T>` or `Py<T>`, each owning a reference count | yes (`Bound::as_ptr` returns `*mut PyObject`), but the address is constant for the object's lifetime | none (non-moving); reclamation is by reference count | `Bound`: the `'py` attachment scope; `Py`: until dropped | not needed |
| WebAssembly GC | a value of reference type; in linear-memory code, a table index | no ("neither their size nor their bit pattern can be observed") | not observable ("not semantically observable, and hence outside the scope of this specification") | reachability; a table slot until overwritten | not expressible |

### 2. JNI: opaque references, pin-or-copy windows, and a per-thread environment

Basis: normative (JNI Specification, Java SE 25, chapters 2, 4, 5) + documentation (Tan;
Furr and Foster; Lee et al.) + derived

**Design premise.** The specification states the moving-collector requirement directly:
"the garbage collector must be able to move an object referred to by the native code", and
the VM "must keep track of all objects that have been passed to the native code".

**Local references are slots in a per-call registry.** "Local references are valid for the
duration of a native method call, and are automatically freed after the native method
returns"; they "are only valid in the thread in which they are created". The
implementation note describes exactly a handle table: "the Java VM creates a registry for
each transition of control from Java to a native method. A registry maps nonmovable local
references to Java objects, and keeps the objects from being garbage collected." It also
rules out the transparent alternative: "local references cannot be faithfully implemented
by conservatively scanning the native stack. The native code may store local references
into global or heap data structures."

Two further rules make the registry a resource with a frame condition. JNI functions "are
not allowed to create extra local references, except for references they return as the
result". Capacity is explicit: "the VM automatically ensures that at least 16 local
references can be created" on entry, `EnsureLocalCapacity` extends it, and `PushLocalFrame`
nests frames in which "local references already created in previous local frames are still
valid".

**Global and weak global references.** Global references "remain valid until they are
explicitly freed". A weak global reference "is treated as a phantom reference referring to
that object when determining whether the object is phantom reachable" and "will become
functionally equivalent to `NULL` at the same time as a `PhantomReference` referring to that
same object would be cleared". The specification rejects check-then-use: comparing with
`NULL` through `IsSameObject` is possible, but "programmers should not rely on this check
to determine whether a weak global reference may be used ... since an intervening garbage
collection could change the weak global reference"; instead a strong reference is acquired
with `NewLocalRef` or `NewGlobalRef`, which "will return `NULL` if the object has been
freed". The upgrade is the atomic operation; the test is not.

**Flat addresses exist only inside release-bracketed windows, and may be copies.** For
primitive arrays the specification adopts "a compromise": region copy functions, and
functions returning "a pinned-down version of array elements" that "may require the Java VM
to perform storage allocation and copying". If the collector supports pinning and the
layout matches, "no copying is needed"; "otherwise, the array is copied to a nonmovable
memory block"; the release functions either unpin or reconcile "the original array with its
non-movable copy". A collector "can make separate decisions about copying or pinning for
each given array".

`GetPrimitiveArrayCritical` strengthens the window so that an uncopied pointer is more
likely: "Inside a critical region, native code must not call other JNI functions, or any
system call that may cause the current thread to block and wait for another Java thread";
the stated reason is that "a VM may temporarily disable garbage collection when the native
code is holding a pointer to an array". Pairs "may be nested", and the function "might
still make a copy", so the result must still be checked against `NULL`.

**Pinning is not exclusion (normative).** "A JNI implementation must ensure that native
methods running in multiple threads can simultaneously access the same array", for example
by keeping "an internal counter for each pinned array"; and "the JNI does not need to lock
primitive arrays for exclusive access by a native method. Simultaneously updating a Java
array from different threads leads to nondeterministic results."

**Thread state.** "The JNI interface pointer (`JNIEnv`) is valid only in the current
thread." `AttachCurrentThread` "attaches the current thread to a Java VM" and returns that
pointer; attaching an attached thread returns the existing one. "A thread cannot detach
itself if there are Java methods on the call stack."

**Derived state machine.** Reading these rules as typestate: a local reference is
`valid(frame, thread)` until `DeleteLocalRef`, `PopLocalFrame`, or return from the native
method; a thread is `detached`, `attached`, or `attached, critical depth n > 0`; in the last
state the only permitted JNI calls are further `Get…Critical` and `Release…Critical`
calls. No transition gives a thread exclusive access to an array.

**Formal models.** Tan's JNI Light models a heap as "a map from labels to blocks", a block
as "a map from addresses (natural numbers) to primitive values", and a reference as
`ℓ[i]`, with address arithmetic "allowed within one block". The stated benefit is that
"there is no need to worry about whether GC moves objects because the resulting heap after
moving is equivalent to the previous heap"; a footnote names the hidden parameter: "a
moving GC will change only the flatten function". The collection rule removes any set of
unreachable Java blocks disjoint from the stack's roots, where the roots of a native frame
include "the set of labels registered with GC"; the rule "is nondeterministic" and the
removed set "can be as small as the empty set". Theorem 3 (GC Safety) states that a
collection step preserves state well-typedness. The paper states that it "models only
local references" (not global or weak global ones) and omits concurrency. Because native
code receives `ℓ[i]` rather than a flat address, a stale flat address cannot be written in
the model (derived); the pin-or-copy windows are thereby abstracted rather than modelled.

Furr and Foster state the contrast with OCaml that the table in Finding 1 records: "Java
does not require the C programmer to register all local C references to Java objects.
Instead, since all such references are returned from JNI function calls, they are
automatically registered until the C code returns execution to the JVM."

Lee, Wiedermann, Hirzel, Grimm and McKinley (Jinn) specify foreign-interface constraints
as state machines: per their abstract, "three classes of FFI constraints encoded by eleven
state machines that capture thousands of JNI and Python/C FFI rules", with a mapping
function selecting "which state machines, transitions, and program entities (threads,
objects, references) to check at each FFI call and return". Only the abstract was read;
the individual machines are not described here.

### 3. OCaml C interface: transparent words, callee-registered roots, and three kinds of safepoint

Basis: documentation (OCaml 5.4 manual, chapter 23; `Gc` module; parallelism chapter) +
documentation (Furr and Foster; Guéneau et al.; Korkut, Stark and Appel; Munch-Maccagnoni
and Scherer; `ocaml-interop` 0.12.0) + derived

**The carrier is the flat word.** C code holds OCaml values in C variables of type `value`.
The manual's rules make the C function responsible for registering those variables:

- Rule 1: a function with `value` parameters or locals "must begin with a call to one of
  the `CAMLparam` macros and return with `CAMLreturn`, `CAMLreturn0`, or `CAMLreturnT`".
- Rule 2: locals "must be declared with one of the `CAMLlocal` macros"; and, for what
  cannot be registered, "a temporary of type `value` must not be live when a garbage
  collection may occur".
- Rule 4: a global variable (or any location outside the heap) containing a value must be
  registered with `caml_register_global_root`, and "the registration causes the contents of
  the variable or memory location to be updated by the garbage collector whenever the value
  in such variable or location is moved within the OCaml heap". Between registering and
  storing the value "you must not call any of the OCaml runtime functions or macros".
  Generational global roots trade scanning for a barrier on the root itself: "you must not
  modify the value of `v` directly, but you must use
  `caml_modify_generational_global_root(&v,x)`".

The evaluation-order hazard is called out for `Store_field`: its first argument "must be a
variable declared by `CAMLparam*` or a parameter declared by `CAMLlocal*` to ensure that a
garbage collection triggered by the evaluation of the other arguments will not invalidate
the first argument after it is computed". Derived pointers are excluded from registration
altogether: `Caml_ba_array_val(v)` "resolves to a derived pointer: it is not a valid OCaml
value but points to a memory region managed by the GC", so it "must always be dereferenced
immediately and not stored anywhere, including local variables".

Munch-Maccagnoni and Scherer name this protocol and its alternative: the OCaml C interface
is *callee-roots* ("functions receive GC-allocated values as arguments and have to ensure
that they are registered with the GC at their own allocation points"), against a
*caller-roots* protocol in which "functions are passed pointers that guarantee that the
values they contain is registered with the GC". They also name the transparency axis:
"Like the OCaml FFI, and unlike the Java Native Interface, our roots are transparent.
Borrowing a root exposes a reference to its value; these values can be accessed directly."

**What moves.** Per the parallelism chapter, each domain "has its own domain-local minor
heap arena"; when one is exhausted the domain "calls for a stop-the-world collection of the
minor heaps", in which "all the domains collect their minor heap arenas in parallel
evacuating the survivors to the major heap"; the major heap "is collected by a concurrent
mark-and-sweep algorithm that involves a few short stop-the-world pauses". `Gc.compact`
performs "a full major collection and compact[s] the heap".

**Three nested classes of safepoint (derived from the manual's section on pending
actions and on multithreading).**

| Program point | May relocate or reclaim | May run OCaml code on this thread | May let other threads of the domain run |
|---|---|---|---|
| allocation functions | yes | no: "Since 4.10, allocation functions are guaranteed not to run any OCaml code, including finalisers, signal handlers and other threads running on the same domain. Instead, their execution is delayed to a later safe point." | no |
| `caml_process_pending_actions` | yes ("requested minor and major garbage collections") | yes: it "executes any pending signal handlers and finalisers, Memprof callbacks, preemptive systhread switching"; it "can raise asynchronous exceptions and cause mutations on the OCaml heap from the same domain" | yes (systhread switching) |
| callbacks into OCaml | yes | yes | as the callee decides |
| `caml_release_runtime_system` … `caml_acquire_runtime_system` | yes | yes: they "poll for pending signals by calling asynchronous callbacks ... before releasing and after acquiring the lock. They can therefore execute arbitrary OCaml code" | yes |

Between release and acquire "the C code must not access any OCaml data, nor call any
function of the run-time system, nor call back into OCaml code", so arguments "must be
copied into C data structures before" releasing. The manual gives `caml_enter_blocking_section`
and `caml_leave_blocking_section` as the historical names of the same two functions.
Callbacks "must be performed while holding the domain lock", and a thread created from C
must first be registered with `caml_c_thread_register`.

The first row is the notable one: relocation points strictly contain reentrancy points.
A C function that only allocates must re-read its registered roots, but its heap
invariants cannot be disturbed by finalizers or signal handlers until it reaches a point
of the other three kinds.

**Static checking of the registration rules.** Furr and Foster give a type system for C
glue code in which every function type carries "a garbage collection effect `GC`", either
`gc` ("the function may invoke the OCaml runtime (and thus the garbage collector)") or
`nogc`, ordered `nogc ⊑ gc`, and typing judgments carry "a protection set `P`, which
contains those variables that have been registered with the garbage collector". The
application rule "requires that if this function may call the garbage collector, then
every variable that points into the OCaml heap and is still live must have been registered".
The published soundness argument does not cover that rule: it is sketched "for a slightly
simplified version of our multilingual type checking system that omits function calls, and
`CAMLprotect` and `CAMLreturn`".

**Program logics.** Melocoton gives the same obligation as a separation-logic resource:
`GC(θ)` "asserts that the current map from runtime locations to λC addresses is `θ`"; the
specification of allocation consumes `GC(θ)` and returns `GC(θ')` for an existentially
quantified `θ'`;
a registered root is owned as `a ↦root γ`, which mentions no `θ`. The paper states its
omissions: "we also do not currently model features like exceptions or multithreading",
and it models "the primitives for registering roots with a more elementary API than the
one provided by the OCaml FFI". VeriFFI states the invariant as a type-class field,
`gc_preserved`, glossed "`graph_predicate` preserved under g.c.-isomorphism", and its glue
code shows the brand discipline operationally: push a frame holding the live local, call
`garbage_collect(tinfo)`, then re-read (`temp=roots[0]; tinfo->fp=fr.prev;`). Both are
treated at length in the adjacent package named under Applicability.

**The same contract as Rust lifetimes.** Munch-Maccagnoni and Scherer summarise "the basic
common idea in Jeffrey (2018) and Dolan (2018)" as "garbage collection as iterator
invalidation": the collector heap plays the vector, an unrooted value the iterator,
allocation the append that can invalidate pointers, and a root the index, the "invariant
name for the elements". Concretely, "we pass around a linear capability ... `gc`,
representing the permission to access the GC heap (in our case in the form of a mutable or
immutable borrow of a token ...)", unrooted values are "copiable borrows of `gc`", and

```rust
pub fn caml_alloc<'a>(gc: &'a mut Runtime, size: usize, tag: u8) -> Value<'a>
```

"requires a mutable borrow of the capability, and returns a value with the same lifetime.
Therefore calling `caml_alloc` invalidates existing non-rooted pointers into the OCaml
heap". Functions fall into three classes by what they take: no runtime access, `&Runtime`
("can call runtime functions which do not trigger a GC"), and `&mut Runtime` ("can call
allocation functions as well as release and re-acquire the runtime lock"). The
`ocaml-interop` 0.12.0 documentation presents the same design as an API: "most interop
operations require an OCaml runtime handle (`cr: &mut OCamlRuntime`)"; `OCaml<'gc, T>`
values "should be regarded as potentially invalid subsequent to any invocation into the
OCaml runtime, unless explicitly rooted"; `BoxRoot<T>` roots a value so that the collector
"does not deallocate or move it".

*Disagreement preserved.* The Boxroot paper says of its roots: "They can also be sent or
shared across threads." The `ocaml-interop` 0.12.0 guide says `BoxRoot<T>` "is `!Send` and
`!Sync` due to its direct interaction with OCaml's domain-specific GC state". The two
statements concern different layers (the C library's roots; one Rust wrapper type four
years later) and were not reconciled here.

### 4. PyO3 over CPython: a copyable scope token is enough only because nothing moves

Basis: documentation (PyO3 0.30.1 API documentation; PyO3 guide, `main`; PEP 703; PEP 779;
Python library reference) + derived

**The brand.** `Python<'py>` is "a marker token"; "its lifetime represents the scope of
holding the GIL which can be used to create Rust references that are bound to it, such as
`Bound<'py, PyAny>`". It is `Copy` and `Clone`, and neither `Send` nor `Sync`.
`Bound<'py, T>` "can be thought of as equivalent to the tuple `(Py<T>, Python<'py>)`" and
"engages in Python reference counting. This means that `Bound<'py, T>` owns a Python
object." `Py<T>` has no lifetime; "almost all methods on `Py<T>` require a `Python<'py>`
token as the first argument", and dropping one while detached "registers the underlying
pointer to have its reference count decremented the next time PyO3 attaches".

**Why a copyable token suffices (derived).** The unique-borrow discipline of Finding 3
exists to invalidate flat addresses at safepoints. Under CPython the address of an object
is constant: the library reference defines `id()` as "an integer which is guaranteed to be
unique and constant for this object during its lifetime" and notes as a CPython
implementation detail "this is the address of the object in memory". With no relocation,
and with each `Bound` and `Py` owning a count, the Root and Brand obligations of Finding 1
reduce to *the thread is attached when the count is manipulated*, which a shared,
copyable scope token expresses. The same design would not be adequate over a runtime that
moves objects; that case needs either opaque handles or the unique-borrow token.

**The brand is wider than the lock.** The API documentation draws the scopes explicitly:
"the GIL can be temporarily released by the Python interpreter during a function call",
with a timeline in which "`Python` exists" spans an interval during which "GIL actually
held" is interrupted. Every call into the interpreter under a live `'py` is therefore a
point where other threads' code and arbitrary Python code may run.

**Detaching.** `Python::detach` has the signature
`fn detach<T, F>(self, f: F) -> T where F: Ungil + FnOnce() -> T, T: Ungil`, and "only
types that implement `Ungil` can cross the closure". On stable Rust `Ungil` is implemented
for every `Send` type; the module documentation records the consequence as a known
limitation of the encoding: a wrapper that is `Send` while containing a
`Bound<'_, PyString>` "will 'work' to smuggle Python references across the closure", an
example it labels unsound and answers with "don't do that", and it gives the intended
definition as an auto trait with `impl !Ungil for Python<'_> {}` on nightly Rust. On
stable Rust the separation of attached-only data from the detached region is therefore
enforced through a proxy trait (`Send`) rather than a dedicated one.

**Free-threaded builds.** The guide states: "In the GIL-enabled build, PyO3 uses the
`Python<'py>` type and the `'py` lifetime to signify that the global interpreter lock is
held. In the freethreaded build, holding a `'py` lifetime means only that the thread is
currently attached to the Python interpreter – other threads can be simultaneously
interacting with the interpreter." PEP 703 gives the state machine being wrapped: thread
states `ATTACHED`, `DETACHED`, and `GC`; "the `ATTACHED` and `DETACHED` states correspond
closely to acquiring and releasing the global interpreter lock", with the difference that
"multiple threads can be in the attached state simultaneously"; during a
stop-the-world pause the collecting thread "can transition other threads from the
`DETACHED` state to the `GC` state using an atomic compare-and-swap operation", and
threads in `ATTACHED` "are requested to pause themselves". A thread that transitions to
`DETACHED` "should suspend any active critical sections". The guide accordingly
requires that `#[pyclass]` types be `Send` and `Sync`.

**Exclusivity is dynamic.** "The Rust borrow checker cannot reason about `&mut` references
once an object's ownership has been passed to the Python interpreter. To solve this, PyO3
does borrow checking at runtime using a scheme very similar to `std::cell::RefCell<T>`."
A class may opt out with `frozen`, which "removes the borrow checker overhead when
retrieving a shared reference to the Rust struct, but disables the ability to get a
mutable reference". Read as an interpretation, this corresponds to the checked discipline
of the toy model's part (c), in which a reentrant access to an exclusively borrowed object
is refused rather than aliased.

**Collector hooks restrict reentrancy.** `Python::attach` panics "if the current thread is
currently in the middle of a GC traversal (i.e. called from within a `__traverse__`
method)": traversal is a context in which acquiring the brand is refused.

### 5. WebAssembly GC: opacity in the type system, and what linear memory may hold

Basis: normative (WebAssembly Specification 3.0; WebAssembly JavaScript Interface) +
documentation (GC proposal `MVP.md`, `Post-MVP.md`) + derived

**References are opaque.** "Reference types are opaque, meaning that neither their size
nor their bit pattern can be observed. Values of reference type can be stored in tables
but not in memories." Heap types form "three disjoint hierarchies": function types;
"aggregate types [which] classify dynamically allocated managed data, such as structures,
arrays, or unboxed scalars"; and "external types [which] classify external references
possibly owned by the embedder". The last two are "interconvertible by ways of the
`extern.convert_any` and `any.convert_extern` instructions"; "both type hierarchies are
inhabited by an isomorphic set of values, but may have different, incompatible
representations in practice". Identity is available only for the `eq` hierarchy, "all
types for which references can be compared"; `i31` values "are not actually allocated in
the store".

**Addresses in the semantics are indices, and collection is outside it.** Structure,
array, and exception instances "are referenced with abstract addresses. These are simply
indices into the respective store component." And: "In practice, implementations may apply
techniques like garbage collection or reference counting to remove objects from the store
that are no longer referenced. However, such techniques are not semantically observable,
and hence outside the scope of this specification." Host references point "to an
uninterpreted form of host address defined by the embedder".

**Consequences (derived).**

- There is no flat address of a managed object for code to hold, so the Brand obligation
  is vacuous and no Pin primitive is expressible. Relocation is unobservable by
  construction, which is the JNI Light move ("a moving GC will change only the flatten
  function") made normative.
- Code whose data structures live in linear memory (the byte-addressed `memory`) cannot
  store a reference in them. To retain a managed object from such a data structure it must
  place the reference in a table and keep the integer index. The table is then a root
  table and the index a handle in exactly the sense of Finding 1, with the same manual
  lifetime (the slot roots the object until overwritten).
- Interior pointers are absent from the first version. `Post-MVP.md` lists "field
  references" that "can also be used to implement *interior pointers* as *fat pointers*",
  deferred "for the sake of simplicity".
- Per `Post-MVP.md`, the first version has no weak references and no finalizers: "Binding to
  external libraries sometimes requires the use of *weak references* or *finalizers*";
  they are deferred because "it is not clear at this point what a sufficiently simple and
  efficient set of primitives for weak references and finalisation could be". Reentrancy
  into a module from collector-scheduled code therefore cannot originate inside the
  language; it can come only from the embedder.

**Host and JavaScript sides are kept apart by caches keyed on abstract addresses.** In the
JavaScript interface a struct or array is surfaced as an "Exported GC Object", "an exotic
object that wraps a garbage collected WebAssembly reference value", on which "most
JavaScript operations ... will throw an exception or return undefined"; it carries an
`[[ObjectAddress]]` internal slot. The agent keeps an "Exported GC Object cache, mapping
struct addresses and array addresses to Exported GC Object objects" (so the same address
yields the same wrapper) and a "Host value cache, mapping host addresses to values" (so a
JavaScript value passed as `externref` receives a host address, the "smallest host address"
not yet in the map when it is new). Neither side sees the other's representation.

**Type soundness is stated with an explicit obligation on host code.** The specification's
appendix states Preservation and Progress theorems and notes that "host functions do not
automatically adhere to" the invariants; "consequently, the required invariants must be
stated as explicit constraints on the invocation of host functions", "codified by the
notion of store extension". Embedder code thus carries a proof obligation of the same
shape as foreign glue code elsewhere in this report (derived).

### 6. The address-map device in verified collectors and interface semantics

Basis: documentation (the cited papers and formal developments, read as primary
literature) + derived

| Work | Abstract side | The map | What replaces it | How a mutator-held pointer is re-validated | Stated limits relevant here |
|---|---|---|---|---|---|
| McCreight, Shao, Lin, Li (2007) | "an abstract state seen by the mutator" | representation predicate `repr` relating it "to its concrete binary representation seen by the collector" | a collector behaviour relation `gcStep` | roots are registers in the abstract state's domain; the collector guarantee says "the roots are the same after the GC runs" at the abstract level | Coq proofs for mark-sweep, Cheney copying, and Baker incremental copying collectors with sample mutators on a MIPS-like machine |
| Hawblitzel, Petrank (2009; journal version 2010) | "an abstract graph of abstract nodes" defined by the mutator | `$toAbs`, mapping "each concrete memory address ... to an abstract node, or to `NO_ABS`"; well-formedness is injectivity | `Alloc` "modifies `$toAbs`" | "the mutator may pass in a root pointer, and the `Alloc` procedure returns a new root pointer that points to the same abstract node"; an old pointer "won't satisfy the preconditions for `ReadField` and `WriteField`, which are in terms of the current `$toAbs`" | no multithreaded mutators |
| Sandberg Ericsson, Myreen, Åman Pohjola (2019) | DataLang values related to heaps by `v_inv` | `gc_related f heap₁ heap₂` with `f` "an injective map into the set of valid addresses in" the new heap whose domain is closed under reachability | each collection | roots are rewritten by `addr_apply f`; "`v_inv` properties can be transported from one heap to another if they are `gc_related`" | generational copying collector for CakeML |
| Tan (JNI Light, 2010; journal version 2014) | heap as a map from labels to blocks | the unformalised "flatten function" | a moving collection "will change only the flatten function" | not needed: references are label-plus-offset | local references only; no concurrency |
| Guéneau et al. (Melocoton, 2023) | block store by logical location | `θ`, carried by the resource `GC(θ)` | allocation and other collection points return `GC(θ')` | store in a registered root (`a ↦root γ`), re-read after | no exceptions, no multithreading; elementary root API |
| Korkut, Stark, Appel (VeriFFI, 2025) | Coq values | graph predicates over a heap graph, with `gc_preserved` | calls to the collector (`garbage_collect`) | push a root frame, collect, re-read | stated for Coq programs compiled by CertiCoq, with C functions specified in VST; "composes with the CompCert verified C compiler and the CertiGC verified garbage collector" |
| Gammie, Hosking, Engelhardt (2015) | reachability from mutator roots | none: the modelled collector has phases `ph-Idle`, `ph-Init`, `ph-Mark`, `ph-Sweep` and does not relocate | n/a | n/a | x86-TSO; an unbounded number of mutators |

Three observations (derived).

- *Direction and ownership of the map vary; its role does not.* Hawblitzel and Petrank map
  concrete to abstract "because our invariants quantify over concrete addresses";
  Melocoton and CakeML map abstract to concrete. In every case the new map is chosen by
  the collector, constrained only by roots, and a pointer fact stated against the old map
  is unusable afterwards.
- *Re-validation has exactly three forms*: pass the pointer through the collecting
  primitive and receive the new one (Hawblitzel and Petrank's `Alloc`); park it in a
  registered root and re-read (OCaml C, Melocoton, VeriFFI, CakeML's stack roots); or never
  hold a flat pointer (JNI references, JNI Light labels, WebAssembly references). The Rust
  token discipline of Finding 3 is a static enforcement of the second form.
- *Safepoints in a concurrent collector are a protocol, not a point.* Gammie, Hosking and
  Engelhardt model "handshakes" of types `ht-NOOP`, `ht-GetRoots`, `ht-GetWork` in which
  "the garbage collector instructs mutators to perform certain actions, and blocks until
  the mutators signal these actions are done", and state the key property as "it does not
  free objects that are reachable from mutator roots". In their model "the handshake type
  and handshake pending bit are not subject to TSO", an explicit modelling assumption. This is the formal counterpart
  of the attach and detach state machines of Findings 2 and 4, for a non-moving collector.

**Foreign calls in a verified compiler.** CakeML's semantics parameterise foreign calls by
an oracle: `semantics : ϕ ffi_state → program → behaviour set`, where "the FFI state ...
includes an oracle specifying how foreign function calls behave". In the Isabelle export
of the Lem source `semantics/ffi/ffi.lem` an individual oracle function has type
`'ffi oracle_function = 'ffi ⇒ 8 word list ⇒ 8 word list ⇒ 'ffi oracle_result` (dispatched
by function name via `oracle0 = string ⇒ 'ffi oracle_function`), and an I/O event "represents the
call of FFI function `s` with immutable input bytes and mutable input ..., returning ... in
the mutable array". Only byte sequences cross, and the oracle's type gives it no way to
invoke CakeML code; relocation and reentrancy are both excluded from the foreign interface
by its type (derived).

### 7. Ownership-typed interfaces to collected heaps: three token designs

Basis: documentation + derived

| Design | Token | What a safepoint does to it | What an unrooted value is | Exclusivity of managed data | Stated status of the safety argument |
|---|---|---|---|---|---|
| Scope token (PyO3) | `Python<'py>`, copyable | nothing; there are no relocation safepoints | not applicable; every handle owns a count | run-time borrow flag for Rust-backed classes; none for other objects | documentation states the `Ungil`-via-`Send` limitation on stable Rust |
| Unique-borrow token (Boxroot paper; `ocaml-interop`) | `&mut Runtime` / `&mut OCamlRuntime` | reborrows it uniquely, ending every borrow derived from the previous one | `Value<'a>` / `OCaml<'gc, T>`, a copyable borrow of the token | not addressed by the token | design described; no formal proof cited in the paper passages read |
| Unique-borrow token with compartments (Josephine) | `&mut JSContext<S>` | "any action that can trigger garbage collection ... requires mutable access to the JavaScript context" | `JSManaged<'a, C, T>`; roots via `in_root` | "mutable access to JavaScript-managed data requires mutable access to the JavaScript context" | "memory safety is conjectured, but not proved formally" |

Josephine is the one design in which the token also governs *exclusivity of the data*:
because "access to the JavaScript context does respect Rust's affine types, mutation or
garbage collection cannot occur simultaneously with accessing JavaScript-managed data".
The Boxroot design uses the token for validity only, and PyO3 uses neither the token nor
the type system for exclusivity of object contents.

### 8. Finalizers: resurrection, ordering, and reentrancy that nobody called

Basis: documentation + normative (JNI) + derived

| Mechanism | Receives the object? | May resurrect? | Ordering statement | What the body may do |
|---|---|---|---|---|
| OCaml custom-block `finalize` | yes | no heap access permitted | none given | "finalizers must not access the OCaml heap, or mutate the OCaml heap or any memory reachable from OCaml GC roots"; no allocation, no callback, no `CAMLparam`; "if a custom block finalizer does anything with the value it receives other than call `Data_custom_val` on it, then it is probably unsafe" |
| OCaml `Gc.finalise` | yes | yes: it "can use all features of OCaml, including assignments that make the value reachable again" | called "at some point between the first time `v` becomes unreachable ... and the time `v` is collected"; within one cycle "in the reverse order of the corresponding calls to `finalise`", so that "each value is finalised before the values it depends upon" when registration follows allocation order | anything; "any particular finaliser may be executed in any of the threads" |
| OCaml `Gc.finalise_last` | no | no: "the value will never be reachable again or used again" | run "after the value is unreachable for the last time"; weak pointers and ephemerons to it are unset first; `finalise` functions "are always called before" `finalise_last` ones | anything not mentioning the value |
| JNI weak global reference | n/a (a reference, not a callback) | not once cleared (derived from the phantom-reference equivalence) | becomes `NULL`-equivalent "at the same time as a `PhantomReference` referring to that same object would be cleared" | upgrade with `NewLocalRef` / `NewGlobalRef`, test the result |
| WebAssembly GC | none in the language | n/a | n/a | deferred to a later version |
| Rust destructors as finalizers (Hughes and Tratt) | yes | "finalizers can resurrect values by copying the reference passed to the finalizer and storing it somewhere" | "finalizers can reference other GCed values that are partly, or wholly, 'finalized' and may have had their backing memory reused" | restricted by a static finalizer safety analysis so that finalizers are "memory safe, cycle safe (i.e. do not access already finalized objects), and thread safe" |

Two points bear on borrowing.

- *Where finalizers run decides whether they are reentrancy.* Hughes and Tratt: "running
  finalizers in the same thread as the last owner of the value can lead to race conditions
  and deadlocks if a finalizer tries to access a resource that the mutator expects to have
  exclusive access too […] since finalizers do not have a predictable execution point, there
  is no way to safely access shared resources if they are run on the same thread. The only
  way to avoid this is to run finalizers on a non-mutator thread — but not all Rust types /
  destructors are safe to run on another thread." Their worked case is a mutator that
  holds a lock when a collection runs a finalizer that takes the same lock: on the same
  thread "it will fail to grab the lock ... and cause a deadlock". OCaml's rule that
  allocation does not run finalisers (Finding 3) is the other resolution: keep finalizers
  on the mutator thread but confine them to declared poll points.
- *Resurrection is prevented either by restricting the body or by withholding the object.*
  OCaml's custom-block rule and Hughes and Tratt's analysis restrict the body;
  `Gc.finalise_last`, phantom-strength weak references, and (as Hughes and Tratt note of
  Java's replacement for per-type finalizers) "per-object 'cleaners', whose API prevents
  problems such as object resurrection" withhold the object.

### 9. Toy model `[kernel-checked proof]` `[toy model]`

Basis: execution (Lean 4 `v4.34.1` kernel check of `lean/`, no Mathlib) + derived (the
reading of each theorem against Findings 1 to 8). **Model–system relation: none proved.**

**Model.** `lean/Toy/Relocation.lean` defines a heap as a flat store
`mem : Addr → Option Val`, a root table `roots : Slot → Option Addr`, and a pin set
`pin : Addr → Bool`. A collector step `Moves f h h'` relocates along an arbitrary address
map `f` subject to six clauses: `f` is injective on live addresses; every rooted address
`a` satisfies `h'.mem (f a) = h.mem a`; every root slot is rewritten through `f`; pinned
addresses are fixed points of `f` and keep their contents; the pin set is unchanged.
Nothing is promised for addresses that are neither rooted nor pinned. `readRaw` reads a
flat address; `readHandle` looks a slot up and then reads.

`lean/Toy/Token.lean` adds straight-line native programs over six operations (`load`,
`pinLoad`, `unpinAll`, `use`, `useH`, `safepoint`). At a `safepoint` the runtime performs
any finite sequence of `RtStep`s: collections with arbitrary legal relocation maps, and
payload overwrites of live objects by reentrant code. The predicate `Stale h env ops`
holds when some execution dereferences a local flat address that is no longer the address
its handle designates; the semantics itself performs no check. The static discipline
`check` brands each raw view with the epoch of the token it was read under, increments the
epoch at each `safepoint`, and accepts `use x` only for a view of the current epoch or a
pinned view.

`lean/Toy/Reentrancy.lean` names objects by identity and gives each a payload and an
exclusive-borrow flag. An outer frame (`holder`) takes an exclusive borrow, stores `v`,
enters the runtime, and loads again through the borrow. Reentrant code is a list of read
and write attempts through its own handles, run unchecked (`stepU`) or under a dynamic
borrow check (`stepC`); it arrives either as a callback or as finalizers queued by the
collector and run synchronously at an allocation (`allocSync`) or deferred to an explicit
poll (`allocDeferred`, `poll`).

`lean/Toy/Finalizer.lean` models finalizer bodies as arbitrary functions on a root list,
with and without access to the dying object, and two collector policies (free after the
finalizer; free only if still unrooted), plus one-at-a-time versus two-phase finalization
over a dependency relation.

**Results.** Exact statements are in the sources; the table gives each theorem's content.

| Theorem | Content |
|---|---|
| `unpinned_raw_can_dangle` | (a) For every heap, every live unpinned object at `a`, and every free unpinned address `b`, some legal collector step leaves `readRaw a = none`, puts the object at `b`, forwards every root slot that designated `a` to `b`, and leaves every handle read unchanged. |
| `unpinned_raw_can_alias` | (a) For two live unpinned rooted objects with payloads `v` and `w`, some legal collector step makes the first object's old flat address read `w`, while both handles still read their own payloads and the second handle now designates that address. A stale flat address can silently denote another live object. |
| `unrooted_can_be_collected` | A live object that no slot designates and that is not pinned can be reclaimed by a legal step that moves nothing, with every handle read unchanged. |
| `pinned_raw_gc_stable`, `pinned_raw_gc_stable_star` | A pinned object's flat address reads the same after one, and after any number of, collector steps. |
| `raw_stable_iff_pinned` | Given a free unpinned address to move into, a live object's flat address reads the same after *every* legal collector step if and only if the object is pinned. |
| `handle_read_gc_stable`, `handle_read_gc_stable_star` | (b) `readHandle` returns the same payload after one, and after any number of, collector steps, for every relocation map. |
| `handle_identity_gc_stable` | (b) Two root slots designate the same live object after a collector step exactly when they did before. |
| `branded_tokens_sound`, `branded_tokens_sound_closed` | (b) If `check` accepts a program, no execution of it is `Stale`, for every relocation chosen and every reentrant write made at each safepoint. |
| `current_view_reads_as_handle`, `rt_keeps_pinned_view` | A view that is not stale reads exactly what its handle reads; a pinned view stays current, and its object pinned, across any finite sequence of runtime steps. |
| `staleProgram_rejected`, `unbranded_use_is_stale` | The program `load; safepoint; use` is rejected by `check`, and it does have a `Stale` execution: the discipline is not vacuous. |
| `reloadProgram_accepted`, `pinnedProgram_accepted`, `afterUnpinProgram_rejected` | Re-reading after the safepoint and using a pinned view across it are accepted; using a pinned view after `unpinAll` and a safepoint is rejected. |
| `pinned_view_valid_not_exclusive` | A pinned view stays current across a safepoint and yet reads a different payload afterwards, because reentrant code wrote through its own handle. Validity is not exclusivity. |
| `unchecked_reentrancy_breaks_exclusive`, `unchecked_reentrant_read_observes` | (c) With unchecked reentrancy, one reentrant write makes the outer frame's later load return `w ≠ v`, and the event log records a successful access to an exclusively borrowed object; an unchecked reentrant read likewise succeeds. |
| `checked_reentrancy_preserves_exclusive`, `holder_checked` | (c) Under the dynamic borrow check, for every list of reentrant actions the exclusively borrowed object is unchanged, the log records no successful access to it, and the outer frame's later load returns `v`. |
| `sync_unchecked_finalizer_breaks_exclusive` | (c) The same violation occurs when the outer frame makes no call back at all and merely allocates, if finalizers run synchronously and unchecked. |
| `sync_checked_finalizer_preserves_exclusive`, `deferred_finalizer_preserves_exclusive`, `deferred_then_poll_breaks_exclusive` | The borrow check protects against synchronous finalizers; deferral protects at the allocation (by definition of the policy) but polling while the borrow is outstanding reintroduces the violation. |
| `resurrection_dangles` | A finalizer that stores the object it receives, followed by an unconditional free, leaves a registered root designating freed storage. |
| `retrace_sound`, `objectless_finalizer_sound` | Freeing only if the object is still unrooted preserves the root invariant when a body can add at most its own object; a body that can only keep or drop existing roots cannot break the invariant even with an unconditional free. |
| `interleaved_order_sensitive`, `two_phase_order_insensitive` | Freeing each object right after its finalizer is order-sensitive (one order reads freed storage, the other does not); running all finalizers before freeing anything is safe for every order. |

**Reading against the interfaces (interpretation, not proof).** `load` followed by
`safepoint` and `use` is the unregistered `value` temporary of OCaml's Rule 2 and the
unrooted `Value<'a>` used after `caml_alloc`; the epoch is the lifetime of one unique
borrow of the runtime token; a slot is a registered root, a JNI local reference, or a
table index holding a WebAssembly reference; `pinLoad` … `unpinAll` is a critical-style
window on a collector that pins rather than copies; `stepC` is a `RefCell`-style borrow
flag; `allocDeferred` is the rule that allocation runs no finalisers; `finalizeFree` with an
objectless body is `Gc.finalise_last` or a phantom-strength reference. The model has no
copy-on-pin branch, no threads, no object graph, no borrow counts for shared borrows, and
no type structure on payloads.

## Boundaries

**Model–system relation: none proved.** Every Lean theorem is about the definitions in
`lean/Toy/`. In particular:

- `branded_tokens_sound` is *not* a soundness theorem for Rust's borrow checker, for
  `ocaml-interop`, for the Boxroot interface, or for Josephine. The epoch counter is a
  model of unique reborrowing; no theorem relates it to Rust lifetimes.
- `handle_read_gc_stable` is *not* a correctness theorem for any collector. `Moves` is an
  axiomatic description of what a correct moving collector may do, with rooted-object
  preservation assumed as a clause.
- `checked_reentrancy_preserves_exclusive` is *not* a proof about PyO3's borrow checking or
  about any aliasing model of Rust. It shows that a refuse-on-conflict flag preserves one
  cell's contents in a sequential model.

**Not examined.**

- Source code of any runtime, compiler, or binding library, and any executed behaviour of
  them. Statements such as *CPython does not move objects* rest on the library reference's
  description of `id()`, not on inspection.
- JNI editions other than Java SE 25; OCaml manuals other than 5.4; PyO3 releases other
  than 0.30.1; alternative Python implementations with moving collectors and their
  emulations of the C API.
- The WebAssembly instruction set in full. The opacity claim rests on the specification's
  own sentence about reference types, not on an instruction-by-instruction audit.
- The body of the Jinn paper (only the abstract was read) and the talk "Safely Mixing OCaml
  and Rust" (only its programme listing was found; its content is reported through the
  Boxroot paper's summary).
- .NET, Go, Haskell, Erlang, Ruby, and Lua foreign interfaces; conservative stack scanning
  as an alternative to registration, beyond JNI's statement excluding it and Hughes and
  Tratt's remark that it is "formally speaking, unsound" in most language semantics.
- Write barriers, remembered sets, and concurrent marking invariants as they bear on
  native writes into managed objects (OCaml Rules 3, 5, 6 are noted but not analysed).
- Exceptions and non-local exits across native frames, and their interaction with root
  registration.

**Unknown.**

- Whether any mechanised result connects a Rust-lifetime token discipline for a moving
  collector to an operational semantics. The passages read give designs and, in one case, an
  explicit statement that safety is conjectured; a search for such a proof was not part of
  this work.
- Whether the Furr and Foster soundness argument extends to the garbage-collection effect
  and protection-set rules. The paper says the omitted features "can be added without
  difficulty, though with more tedium"; no such extension was found in the text read.
- How the Boxroot paper's statement that roots may be sent or shared across threads and
  `ocaml-interop` 0.12.0's `!Send`/`!Sync` `BoxRoot<T>` relate.
- Which OCaml runtime entry points other than those the manual lists can run pending
  actions.

**Known not to apply.**

- The unique-borrow token argument does not apply to PyO3: `Python<'py>` is `Copy`, and a
  call into the interpreter does not end the validity of any `Bound<'py, T>`. PyO3's design
  is justified by non-relocation plus owned counts, not by safepoint invalidation.
- *Pinned implies exclusive* does not hold in JNI: the specification states that the JNI
  "does not need to lock primitive arrays for exclusive access".
- *`'py` implies mutual exclusion* does not hold in free-threaded builds (PyO3 guide), and
  *`'py` implies the lock is continuously held* does not hold even in the default build
  (PyO3 API documentation's timeline).
- *An OCaml allocation may run a finaliser* does not hold from 4.10 on, per the manual; the
  relocation hazard at allocations remains.
- *JNI's `IsSameObject(weak, NULL)` establishes that the weak reference is usable* does not
  hold; the specification says not to rely on it.
- The CakeML foreign-function oracle does not model callbacks or shared heap references;
  conclusions about reentrancy cannot be drawn from it.

**Unsupported (by the interface, per its own documentation).**

- Calling JNI functions other than the critical pair, or blocking on another Java thread,
  inside a JNI critical region.
- Using a JNI local reference in another thread, or after the native method returns.
- Accessing OCaml data, calling the runtime, or calling back between
  `caml_release_runtime_system` and `caml_acquire_runtime_system`; allocating, calling
  back, or touching the OCaml heap inside a custom-block finalizer; storing
  `Caml_ba_array_val(v)` anywhere.
- Storing a WebAssembly reference in linear memory; observing its bit pattern; weak
  references and finalizers in WebAssembly 3.0.
- Calling `Python::attach` from within a `__traverse__` method (panics).

**Stronger readings the evidence does not establish.**

- That opaque handles are *sufficient* for memory safety. They remove the stale-address
  hazard; scope violations (a JNI local reference used after return or on another thread)
  remain unchecked in C, and exclusivity is untouched.
- That the three safepoint classes of Finding 3 are disjoint or exhaustive in other
  runtimes. The table is the OCaml manual's; JNI and PyO3 document different partitions.
- That a design which is sound over a non-moving runtime remains sound when the runtime
  begins to move objects. The PyO3 analysis shows the opposite dependence.
- That the toy model's `Moves` relation captures generational, concurrent, or incremental
  collectors. It describes a single atomic relocation step between two heaps.

## Evidence

All sources were acquired and read on 2026-11-22. Bibliographic metadata (title, authors,
venue, pages, year) for every DOI below — including the journal DOI of Hawblitzel and
Petrank's Logical Methods in Computer Science article (`10.2168/LMCS-6(3:6)2010`) — was
checked against the Crossref record for that DOI on the same date. arXiv identifiers and versions were checked
against the arXiv abstract pages, and the HAL identifier against the HAL record;
quotations are from the full texts named.

### Specifications and upstream documentation

| Source | Identity | Passages used |
|---|---|---|
| Java Native Interface Specification, Java SE 25 & JDK 25 | `https://docs.oracle.com/en/java/javase/25/docs/specs/jni/design.html`, `.../functions.html`, `.../invocation.html` | Ch. 2 "Referencing Java Objects", "Global and Local References", "Implementing Local References", "Accessing Primitive Arrays"; Ch. 4 `EnsureLocalCapacity`, `PushLocalFrame`, "Weak Global References", `Get/ReleasePrimitiveArrayCritical`; Ch. 5 `AttachCurrentThread`, `DetachCurrentThread`, validity of `JNIEnv` |
| The OCaml Manual, version 5.4, Chapter 23 "Interfacing C with OCaml" | `https://ocaml.org/manual/5.4/intfc.html` | §5.1 Rules 1 to 4; §5.2 Rules 5, 6; §5.3 "Pending actions and asynchronous exceptions"; §9.1 custom operations and the caution on `finalize`; §9.6; §10.2 warning on `Caml_ba_array_val`; §12.1, §12.2 |
| OCaml 5.4 `Gc` module documentation | `https://ocaml.org/manual/5.4/api/Gc.html` | `finalise`, `finalise_last`, `compact` |
| The OCaml Manual, version 5.4, "Parallel programming" | `https://ocaml.org/manual/5.4/parallelism.html` | description of domain-local minor heaps and the major collector |
| PyO3 0.30.1 API documentation | `https://docs.rs/pyo3/0.30.1/pyo3/marker/index.html`, `.../marker/struct.Python.html`, `.../struct.Bound.html`, `.../struct.Py.html` (reached through the `latest` alias, which resolved to 0.30.1; crates.io reported 0.30.1 as newest and maximum stable version) | module `marker` (`Ungil`, drawbacks, auto-trait definition); `Python` (purposes, "Deadlocks" timeline, `attach` panics, `detach` signature, `assume_attached`, `Copy`, `!Send`, `!Sync`); `Bound`; `Py` (reference counts, `Drop`) |
| PyO3 user guide, branch `main` | `https://pyo3.rs/main/types.html`, `.../free-threading.html`, `.../class.html`; repository `PyO3/pyo3` head `be9e428ab7573552c65aa9e7a7a0c6d14b06fd5d` on the observation date | smart pointer overview; meaning of `'py` in free-threaded builds; `#[pyclass]` thread-safety requirements; run-time borrow checking; `frozen` |
| PEP 703, "Making the Global Interpreter Lock Optional in CPython" | `https://peps.python.org/pep-0703/` | "Thread States", "Stop-the-World", "Borrowed References", critical-section suspension on detach |
| PEP 779, "Criteria for supported status for free-threaded Python" (Thomas Wouters, Matt Page, Sam Gross; status Final; Python 3.14) | `https://peps.python.org/pep-0779/` | header fields only |
| Python library reference, built-in `id()` | `https://docs.python.org/3/library/functions.html#id` | definition and CPython implementation detail |
| WebAssembly Specification, Release 3.0 (draft dated 2026-11-20), editor Andreas Rossberg | `https://webassembly.github.io/spec/core/` (`syntax/types.html`, `exec/runtime.html`, `appendix/properties.html`, `appendix/changes.html`) | "Heap Types", "Reference Types"; store note on garbage collection; abstract and host addresses; "Type Soundness" (host function instances, store extension, Preservation, Progress); change history entry "Garbage Collection" |
| WebAssembly JavaScript Interface, source | repository `WebAssembly/spec`, branch `main` at `6fca707686ed4f36a1e30ec2ae7d3dd32b276704`, `document/js-api/index.bs` | agent caches; `ToJSValue`, `ToWebAssemblyValue`; "Exported GC Object" |
| WebAssembly GC proposal documents | repository `WebAssembly/gc`, branch `main` at `756060f5816c7e2159f4817fbdee76cf52f9c923`, `proposals/gc/MVP.md`, `proposals/gc/Post-MVP.md`, `README.md` | type hierarchy and external conversion; "Field References"; "Weak References"; the README's statement that `Overview.md` is out of date in its concrete details |
| `ocaml-interop` 0.12.0 crate documentation | `https://docs.rs/ocaml-interop/0.12.0/ocaml_interop/` and `.../user_guides/part2_fundamental_concepts/index.html` | runtime handle; `OCaml<'gc, T>`; `BoxRoot<T>`; caller-rooted convention |

Limitations of identity: the JNI and OCaml documents are identified by edition and URL
only (no content hash was recorded); the WebAssembly core specification is a draft
identified by its self-declared release line; the PyO3 guide is on a moving branch.

### Papers and formal developments

- Armaël Guéneau, Johannes Hostert, Simon Spies, Michael Sammler, Lars Birkedal, Derek
  Dreyer. *Melocoton: A Program Logic for Verified Interoperability Between OCaml and C.*
  Proc. ACM Program. Lang. 7 (OOPSLA2), pp. 716–744, 2023. DOI `10.1145/3622823`. Full
  text read from an author-hosted copy.
- Joomy Korkut, Kathrin Stark, Andrew W. Appel. *A Verified Foreign Function Interface
  between Coq and C.* Proc. ACM Program. Lang. 9 (POPL), pp. 687–717, 2025. DOI
  `10.1145/3704860`. Full text read from an author-hosted copy.
- Adam Sandberg Ericsson, Magnus O. Myreen, Johannes Åman Pohjola. *A Verified Generational
  Garbage Collector for CakeML.* Journal of Automated Reasoning 63(2), pp. 463–488
  (published online 2018). DOI `10.1007/s10817-018-9487-z`. Full text read from the
  publisher's open-access page. (Extends the ITP 2017 paper of the same title, LNCS 10499,
  pp. 444–461, as the article's own reference list records.)
- Yong Kiam Tan, Magnus O. Myreen, Ramana Kumar, Anthony Fox, Scott Owens, Michael Norrish.
  *The verified CakeML compiler backend.* Journal of Functional Programming 29, e2, 2019.
  DOI `10.1017/S0956796818000229`. Full text read from the project-hosted copy. The oracle
  type is quoted from the theory `Ffi` of the Archive of Formal Proofs entry `CakeML`
  ("Generated by Lem from `semantics/ffi/ffi.lem`"), `https://isa-afp.org/browser_info/current/AFP/CakeML/Ffi.html`,
  a moving URL.
- Andrew McCreight, Zhong Shao, Chunxiao Lin, Long Li. *A general framework for certifying
  garbage collectors and their mutators.* PLDI 2007, pp. 468–479. DOI
  `10.1145/1250734.1250788`. Full text read from an author-hosted copy.
- Chris Hawblitzel, Erez Petrank. *Automated verification of practical garbage collectors.*
  POPL 2009, pp. 441–453. DOI `10.1145/1480881.1480935`. The text read and quoted is the
  journal version: Logical Methods in Computer Science 6(3), 2010, DOI
  `10.2168/LMCS-6(3:6)2010`, arXiv `1004.3808v3`.
- Peter Gammie, Antony L. Hosking, Kai Engelhardt. *Relaxing safely: verified on-the-fly
  garbage collection for x86-TSO.* PLDI 2015, pp. 99–109. DOI `10.1145/2737924.2738006`.
  The text read and quoted is the accompanying Isabelle development, Archive of Formal
  Proofs entry `ConcurrentGC` (dated April 13, 2015), `https://www.isa-afp.org/entries/ConcurrentGC.html`.
- Gang Tan. *JNI Light: An Operational Model for the Core JNI.* APLAS 2010, LNCS 6461,
  pp. 114–130. DOI `10.1007/978-3-642-17164-2_9`. The text read and quoted is the journal
  version: Mathematical Structures in Computer Science 25(4), pp. 805–840 (published online
  2014), DOI `10.1017/S0960129513000042`, from an author-hosted copy.
- Michael Furr, Jeffrey S. Foster. *Checking type safety of foreign function calls.* ACM
  Transactions on Programming Languages and Systems 30(4), pp. 1–63, 2008. DOI
  `10.1145/1377492.1377493`. Full text read from an author-hosted copy. (Journal version
  of the PLDI 2005 paper of the same title, DOI `10.1145/1065010.1065019`.)
- Byeongcheol Lee, Ben Wiedermann, Martin Hirzel, Robert Grimm, Kathryn S. McKinley. *Jinn:
  synthesizing dynamic bug detectors for foreign language interfaces.* PLDI 2010,
  pp. 36–49. DOI `10.1145/1806596.1806601`. Abstract only, from the publication page of
  one author's institution.
- Alan Jeffrey. *Josephine: Using JavaScript to safely manage the lifetimes of Rust data.*
  arXiv `1807.00067v1`, 29 June 2018. Full text read.
- Guillaume Munch-Maccagnoni, Gabriel Scherer. *Boxroot, fast movable GC roots for a better
  FFI.* ML Family Workshop, September 2022, Ljubljana. HAL `hal-03910313v1`. Full text
  read.
- Jacob Hughes, Laurence Tratt. *Garbage Collection for Rust: The Finalizer Frontier.*
  Proc. ACM Program. Lang. 9 (OOPSLA2), pp. 3588–3614, 2025. DOI `10.1145/3763179`. Text
  read: arXiv `2504.01841v4`.
- Stephen Dolan. *Safely Mixing OCaml and Rust.* Talk, ML Family Workshop 2018 (programme
  listing at `https://icfp18.sigplan.org/track/mlfamilyworkshop-2018-papers`). Not read;
  cited only as the origin the Boxroot paper and the `ocaml-interop` documentation name.

### Lean kernel audit

Toolchain `leanprover/lean4:v4.34.1` (tag commit
`5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib and no other dependency. The
library `Toy` (`lean/Toy.lean` importing `Toy/Relocation.lean`, `Toy/Token.lean`,
`Toy/Reentrancy.lean`, `Toy/Finalizer.lean`) builds with `lake build` without errors or
warnings. The sources contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or
`partial`. `lean/Audit.lean` runs `#print axioms` on every theorem named in Finding 9; its
output is preserved verbatim in `audit/axioms.txt`.

| Theorem | Source file | `#print axioms` result |
|---|---|---|
| `Toy.handle_read_gc_stable` | `lean/Toy/Relocation.lean` | `does not depend on any axioms` |
| `Toy.handle_read_gc_stable_star` | `lean/Toy/Relocation.lean` | `does not depend on any axioms` |
| `Toy.handle_identity_gc_stable` | `lean/Toy/Relocation.lean` | `depends on axioms: [propext]` |
| `Toy.pinned_raw_gc_stable` | `lean/Toy/Relocation.lean` | `does not depend on any axioms` |
| `Toy.pinned_raw_gc_stable_star` | `lean/Toy/Relocation.lean` | `does not depend on any axioms` |
| `Toy.unpinned_raw_can_dangle` | `lean/Toy/Relocation.lean` | `depends on axioms: [propext]` |
| `Toy.unpinned_raw_can_alias` | `lean/Toy/Relocation.lean` | `depends on axioms: [propext]` |
| `Toy.unrooted_can_be_collected` | `lean/Toy/Relocation.lean` | `depends on axioms: [propext]` |
| `Toy.raw_stable_iff_pinned` | `lean/Toy/Relocation.lean` | `depends on axioms: [propext]` |
| `Toy.current_view_reads_as_handle` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.rt_keeps_pinned_view` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.branded_tokens_sound` | `lean/Toy/Token.lean` | `depends on axioms: [propext, Quot.sound]` |
| `Toy.branded_tokens_sound_closed` | `lean/Toy/Token.lean` | `depends on axioms: [propext, Quot.sound]` |
| `Toy.staleProgram_rejected` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.reloadProgram_accepted` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.pinnedProgram_accepted` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.afterUnpinProgram_rejected` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.unbranded_use_is_stale` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.pinned_view_valid_not_exclusive` | `lean/Toy/Token.lean` | `depends on axioms: [propext]` |
| `Toy.checked_reentrancy_preserves_exclusive` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.holder_checked` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.unchecked_reentrancy_breaks_exclusive` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.unchecked_reentrant_read_observes` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.sync_unchecked_finalizer_breaks_exclusive` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.sync_checked_finalizer_preserves_exclusive` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.deferred_finalizer_preserves_exclusive` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.deferred_then_poll_breaks_exclusive` | `lean/Toy/Reentrancy.lean` | `depends on axioms: [propext]` |
| `Toy.resurrection_dangles` | `lean/Toy/Finalizer.lean` | `depends on axioms: [propext]` |
| `Toy.retrace_sound` | `lean/Toy/Finalizer.lean` | `depends on axioms: [propext, Quot.sound]` |
| `Toy.objectless_finalizer_sound` | `lean/Toy/Finalizer.lean` | `depends on axioms: [propext]` |
| `Toy.interleaved_order_sensitive` | `lean/Toy/Finalizer.lean` | `does not depend on any axioms` |
| `Toy.two_phase_order_insensitive` | `lean/Toy/Finalizer.lean` | `depends on axioms: [propext, Quot.sound]` |

Of the 32 audited theorems, 5 depend on no axiom, 23 on `propext` only, and 4 on `propext` and `Quot.sound`; none depends on `Classical.choice`.

## Revalidation

1. **Rebuild and axiom-check the toy model.** From a copy of this package's `lean/`
   directory (so that no build output is written into the corpus tree):

   ```console
   cp -r reports/ownership-to-moving-gc-ffi-root-pinning-safepoints-and-reentrancy/lean /tmp/gcffi-lean
   cd /tmp/gcffi-lean && lake build && lake env lean Audit.lean
   ```

   `support/check_lean.sh` performs the same steps, additionally rejects forbidden tokens
   in the sources, and compares the audit output with `audit/axioms.txt`. A pass shows that
   the definitions and theorems still check on the pinned toolchain and depend on no axiom
   beyond `propext`, `Classical.choice`, `Quot.sound`. It shows nothing about any runtime.
2. **JNI.** In the current edition of the specification, re-read three passages: "Weak
   Global References" (phantom-reference equivalence and the advice against the `NULL`
   test), `GetPrimitiveArrayCritical` (the prohibition on other JNI calls and on blocking),
   and "Accessing Primitive Arrays" (no exclusive locking). A change to any of them changes
   Finding 2.
3. **OCaml.** In the manual for the version of interest, re-read §5.3 of the C interface
   chapter. If the sentence guaranteeing that allocation functions run no OCaml code is
   absent or qualified, the first row of the safepoint table in Finding 3 no longer holds.
   Re-read the caution on custom-block finalizers and the `Gc.finalise` /
   `Gc.finalise_last` entries for Finding 8.
4. **PyO3.** Check three items of the API documentation for the release of interest:
   whether `Python<'py>` is still `Copy`; the bounds on `Python::detach`; and the stable
   definition of `Ungil`. If the token becomes non-copyable or `Ungil` becomes a true auto
   trait on stable Rust, Finding 4 and the first row of Finding 7 need revision. Check the
   free-threading guide's sentence on what `'py` means.
5. **WebAssembly.** In the core specification, check that the "Reference Types" section
   still says references are opaque and storable in tables but not memories, and whether a
   later release adds weak references, finalization, field references, or shared
   references; any of these changes the consequences listed in Finding 5.
6. **Literature.** The address-map table (Finding 6) is a reading of fixed publications
   and needs no revalidation unless a cited development is revised; the row most likely to
   change is the statement of limits for a living mechanisation.
