# Reentrant FFI, Mixed MIR-ISA Call Stacks, Tree Borrows Protectors, and Two-Oracle Pass-2 Correspondence

## Summary

Modeling mixed Rust MIR and foreign C/assembly (`asm!` and `extern`) execution
across reentrant call chains (`Rust -> Foreign/Asm -> Rust callback -> Foreign/Asm`),
Rust exports invoked from foreign code, and cross-ABI unwinding cannot be
accomplished with a single big-step `BridgeTransition` that runs foreign code
atomically to completion before returning to MIR. Even Miri's own `-Zmiri-native-lib`
executor implements a single big-step `call_native_raw` boundary and aborts with
an unsupported error on reentrant callbacks into Rust.

Key verified findings across multi-language semantics, Tree Borrows, provenance
exposure, allocator coexistence, and `vendor/lean-miri` Pass-2 correspondence:

1. **Lean 4 heterogeneous call stacks do not require Iris COFEs or step-indexing
   for verified or first-order/stratified FFI contracts.** A CompCertO/CompCertM-style
   heterogeneous call stack (`List (LinkFrame SM SI M Q R)`) combined with
   DimSum-style external event traces and a first-order Kripke address valuation
   $\alpha$ plus exposed-allocation set handles arbitrary reentrant `MIR <-> ISA`
   callback nesting and unwinding in pure Lean 4 (`Init`-only, standard
   `{propext, Classical.choice}` axioms). Iris COFEs, guarded recursion (`▷`),
   and impredicative invariants (as in Melocoton and Cerise) become mathematically
   necessary only when untrusted foreign code can store arbitrary self-referential
   higher-order closures or capabilities in mutable shared heap (Landin's knot
   across FFI).
2. **Outer Rust Tree Borrows `FnEntry` protectors remain live across foreign
   calls and reentrant Rust callbacks, while foreign callees install no callee
   `FnEntry` protector.** In both `rustc` (`interpret/call.rs`) and `lean-miri`
   (`Call.lean`), calling a foreign item returns `none` from `findMirOrEvalFn`
   and bypasses `initStackFrame`, whereas every suspended outer Rust frame keeps
   its `StrongProtector` active in `global.protectedTags`. Live Miri execution
   under `-Zmiri-tree-borrows` confirms all four reentrant callback aliasing
   cases: child writes via `user_data` derived from `&mut T` validly activate
   `ReservedFrz false -> Unique`; sibling writes trigger immediate protector UB;
   sibling reads conflict `ReservedFrz false -> ReservedFrz true`, causing UB if
   and only if the outer Rust function subsequently writes before returning.
3. **Exposed provenance protects Rust stack locals against `sp`-arithmetic
   scanning in abstract semantics, but flat ISA verification requires explicit
   memory-footprint containment.** Under PNVI-ae-udi and Miri's `exposed` set,
   an unexposed stack local cannot be recovered via `with_exposed_provenance`
   even if its raw integer address is obtained via `.addr()`. In contrast,
   Miri's `-Zmiri-native-lib` eagerly exposes every pointer crossing FFI and
   bypasses Tree Borrows `perform_access` during C execution. For verified
   `asm!`/FFI, preserving an explicit valuation bijection $\alpha$ avoids
   unnecessary wildcard over-approximation (such as Tree Borrows' optimistic
   `EitherAccess` no-op when both root and child are exposed), while flat ISA
   semantics (`I_ref`) must independently prove that foreign instructions do not
   access addresses outside caller-exposed ranges and the callee's own stack frame.
4. **Foreign `malloc`/`free`/`realloc` and Rust `GlobalAlloc` share one flat
   address space but strictly disjoint deallocation domains.** `MiriMemoryKind`
   partitions `.rust` and `.c` allocations; `__rust_dealloc` enforces both kind
   and exact `(size, align)` layout, C `malloc(0)` creates a real 0-byte `.c`
   allocation distinct from Rust's `NonNull::dangling()` (which has no
   provenance), `free(NULL)` is a legal no-op, `realloc(p, 0)` is UB (C23 /
   WG14 N2464), and cross-allocator deallocation fails closed with
   `memoryKindMismatch`.
5. **`vendor/lean-miri` (`c92d1d97`) already includes foreign-call, unwind,
   Tree Borrows, exposed-set, and allocator-kind modules inside its 160-module
   `execution_machine_closure`, but lacks an `inlineAsm` hook in
   `TerminatorHooks` (`ControlFlow.lean:151` hardcodes `.unsupported`).**
   Satisfying Anneal's Pass-2 correspondence strategy (`docs/mir-correspondence-strategy.md`
   §4.2 and §4.4) without bloating `vendor/lean-miri` with ISA decoders requires:
   (a) a minimal audited patch adding `inlineAsm` to `TerminatorHooks` and routing
   foreign calls through `CallDispatchMachine.Hooks.foreign`, (b) two-oracle
   horizontal composition combining MIR correspondence ($M_{\text{anneal}} \sim M_{\text{ref}}$)
   with an independent golden ISA/FFI reference ($I_{\text{anneal}} \sim I_{\text{ref}}$)
   over a shared call/return/memory interface (mechanized in Lean 4.34.1 for both
   leaf oracles and arbitrarily reentrant heterogeneous stacks), and (c) upgrading
   `CorrespondenceClaim` from closed `TerminalOut` to trace-indexed
   `BehaviorTrace` / `FaultTrace` / `DivergesTrace`.

## Applicability

This report characterizes the exact interactions among the subjects in
`REPORT.json`:

- **Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)** and its
  vendored **`lean-miri` (`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`)**,
  which pins upstream `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`
  and `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` in
  `vendor/lean-miri/UPSTREAM_PIN.json`. Findings about `TerminatorHooks`,
  `execution_machine_closure`, `Trusted.Correspondence`, and `TrustedBoundary`
  apply specifically to these pinned revisions and any successor sharing those
  module interfaces.
- **Miri execution evidence** was obtained on `x86_64-unknown-linux-gnu` using
  `rustc 1.102.0-nightly` / `miri 0.1.0` at commit
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (2026-11-11) with
  `MIRIFLAGS="-Zmiri-tree-borrows"` under Rust edition 2024. The Tree Borrows
  protector, wildcard `ExposedCache`, unexposed `.addr()` forging, and
  `MiriMemoryKind::C` vs. `Rust` deallocation semantics verified by execution
  agree with the pinned `7fa591d7` source and `lean-miri@c92d1d97` Lean
  implementation.
- **Unwinding rules** apply to Rust targets compiled with `panic=unwind` under
  `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`extern "C"` vs.
  `extern "C-unwind"`). They do not apply to `panic=abort` configurations or
  forced unwinding (`longjmp`, `pthread_exit`), which the Rust Reference
  explicitly excludes.
- **Multi-language semantics comparison** synthesizes exact primary Coq/Iris
  mechanizations (`CertiKOS/compcert@87a62d95`, `snu-sf/CompCertM@1bf2113b`,
  `logsem/cerise@9eb72e67`, `logsem/melocoton@039dae32`) and peer-reviewed
  specifications (DimSum POPL 2023, Simuliris POPL 2022, Tree Borrows PLDI 2025,
  PNVI-ae-udi POPL 2019 / ISO/IEC TS 6010).
- **Mechanized Lean 4 proofs** in
  `support/ReentrantInterleavedBridgeAndOracleComposition.lean` were kernel-checked
  by `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
  with `-DElab.async=false -Ddebug.skipKernelTC=false` using only Lean's
  built-in `Init` library (zero external dependencies, zero `sorryAx`). The
  mechanized theorems establish structural properties of the modeled interfaces
  (labeled `derived` + `execution`); applying them to full `Trusted.MirSemantics`
  requires instantiating the `OpenComponent` / `OpenMirMachine` adapters on
  concrete MIR and ISA states.

## Findings

### 1. Why Single Big-Step Bridges Break on Reentrant FFI and Foreign Unwinding

Basis: normative + source + derived + execution

A single big-step `BridgeTransition` models an external boundary as a closed
relation or function $\text{runISA} : \text{IsaProg} \times \sigma_{\text{MIR}} \to \sigma_{\text{MIR}}'$
that marshals MIR values into an ISA state, runs the foreign code to completion,
and unmarshals the final result back into the suspended MIR frame. That model
breaks structurally on three standard FFI patterns:

1. **Reentrant FFI callbacks (`Rust_0 -> Foreign/Asm_1 -> Rust_2 -> Foreign/Asm_3`):**
   C APIs routinely accept a function pointer `extern "C" fn(*mut c_void)` plus
   an opaque `user_data` context (e.g., `qsort`, event loops, visitor hooks,
   custom allocator wrappers). During `Foreign/Asm_1`, control re-enters Rust
   MIR (`Rust_2`), which mutates Rust memory, triggers Tree Borrows transitions
   against `Rust_0`'s still-live protectors, may allocate/deallocate heap blocks,
   and may invoke further foreign calls (`Foreign/Asm_3`) before returning to
   `Foreign/Asm_1`. Any single-frame big-step bridge that takes only the foreign
   program and entry MIR state without suspending `Foreign/Asm_1` on a shared
   heterogeneous call stack and dispatching the MIR evaluator on `Rust_2` cannot
   distinguish semantically different callback bodies (mechanized in
   `big_step_bridge_blind_to_callback_semantics`,
   `support/ReentrantInterleavedBridgeAndOracleComposition.lean:258-272`).
2. **Foreign-initiated Rust exports (`Foreign_0 -> #[unsafe(no_mangle)] extern "C" fn rust_export`):**
   When C or assembly owns `main` or drives a library entry point, execution
   starts in an ISA frame and pushes a MIR frame on top. There is no enclosing
   MIR caller frame (`callerSentinelFrame`) to anchor a MIR-driven big-step
   bridge.
3. **Cross-boundary unwinding through interleaved frames:**
   Under `panic=unwind`, unwinding can originate in an inner Rust callback
   (`Rust_2`) or inside a foreign C++ frame (`Foreign_1`), pass through foreign
   stack frames with C++ destructors and Rust frames with `Drop` impls and
   `FnEntry` protectors, and terminate in a `catch_unwind` or C++ `catch` block
   or abort at a non-unwinding ABI boundary. A single big-step entry-to-exit
   bridge cannot observe intermediate frame unwinding, release frame-local
   protectors in exact unwind order, or distinguish `"C"` from `"C-unwind"`
   crossing points.

**Concrete upstream confirmation in Miri and `lean-miri`:**
Miri's own native FFI runner (`rust-lang/miri@7fa591d7`,
`src/shims/native_lib/mod.rs:488-516`) executes foreign calls as a single
big-step `call_native_raw` through `libffi`. When foreign code tries to invoke a
Rust function pointer passed across FFI, `libffi_closure_callback` (lines
490-514) explicitly emits `err_unsup_format!("calling a function pointer through the FFI boundary")`
and calls `std::process::exit(1)`. Correspondingly, `proofs-rs/lean-miri@c92d1d97`
mirrors this limitation in `Miri/Interpreter/Native/Supervisor.lean:91`, where
the ptrace supervisor aborts with
`"native code segfaulted when re-trying memory access; native callback into Rust?"`.

**Normative Rust FFI unwinding matrix (`panic=unwind`):**
From `rust-lang/reference@c9cc3282`, `src/items/functions.md:245-263`
(`r[items.fn.extern.unwind.behavior]`, `r[items.fn.extern.abort]`) and
`src/panic.md:118-141` (`r[panic.unwind.ffi.*]`):

| Unwind origin | ABI boundary | Normative outcome (`panic=unwind`) | Formal model requirement |
|---|---|---|---|
| Rust panic | `extern "C"` (non-unwinding) | Deterministic process abort (`r[items.fn.extern.abort]`); unspecified whether inner Rust `Drop`s run before abort | Must model nondeterminism of cleanup before abort, or restrict verified code to no-panic across `"C"` |
| Foreign exception (e.g. C++ `throw`) | `extern "C"` (non-unwinding) | **Undefined Behavior** (`r[items.fn.extern.unwind.behavior]`) | Must transition directly to `.fault .ub` |
| Rust panic | `extern "C-unwind"` | Propagates through foreign frames; foreign runtime behavior upon catching/disposing payload is unspecified | Requires unwind-aware stack frames releasing each popped MIR frame's protectors |
| Foreign exception | `extern "C-unwind"` | Propagates through Rust frames running `Drop`s; `std::panic::catch_unwind` has unspecified outcome (either process abort OR `Err(opaque)`) | Cannot assume `catch_unwind` catches foreign exceptions cleanly |
| Forced unwinding (`longjmp`, `pthread_exit`) | Any Rust frame | **Undefined Behavior** / excluded from `C-unwind` guarantees (`r[panic.unwind.ffi.forced]`) | Out of scope for normal stack-unwinding frames; fails closed as UB |

### 2. Formal Comparison of Multi-Language Semantics for Mixed MIR-ISA Call Stacks in Lean 4

Basis: normative + source + derived + execution

Five canonical verification frameworks address cross-language linking and
reentrant calls. Direct source inspection reveals the exact mathematical
boundary where Iris COFEs and step-indexing become necessary versus avoidable
in Lean 4.

| Framework | Primary mechanization | Heterogeneous stack representation | Reentrant callbacks | Distinct memory models | Unwinding / non-local control | Requires Iris COFEs / step-indexing? |
|---|---|---|---|---|---|---|
| **CompCertO** (PLDI 2021) | `CertiKOS/compcert@87a62d95` (`common/SmallstepLinking.v:31-46`, `LanguageInterface.v:11-64`, `CallconvAlgebra.v`) | `Variant frame := st (i : I) (s : state (L i))` with `list frame`; `step_internal`, `step_push`, `step_pop` | Yes (arbitrary depth) | Via Kripke `callconv` (`ccworld`, `match_senv`, `match_query`, `match_reply`); base linking assumes shared CompCert `mem` unless bridged in `callconv` | Well-bracketed call/return only; unwinding needs explicit unwind reply tag | **No** (first-order Coq inductive/coinductive simulations; Kripke worlds are plain types) |
| **CompCertM** (POPL 2020) | `snu-sf/CompCertM@1bf2113b` (`compose/Sem.v:26-90`, `compose/ModSem.v:19-26`) | `Frame.t := mk ms st`; `state := Callstate args frs \| State frs`; `Args.Cstyle \| Args.Asmstyle` | Yes (arbitrary depth) | Shared CompCert `mem` + RUSC memory-injection worlds | Well-bracketed call/return only | **No** (uses `paco` coinduction; zero COFEs/step-indexing) |
| **DimSum** (POPL 2023) | DOI `10.1145/3571220` / Zenodo `10.5281/zenodo.7306312` | Decentralized LTS `S × (E + {τ}) × P(S)` with dual nondeterminism (`exists` demonic, `forall` angelic); `link_mod`, `prepost_mod` wrappers (`rec_to_asm`) | Yes (arbitrary depth) | Yes (`Rec` block-offset heap vs. `Asm` flat word memory via wrapper state & address bijection) | Yes (event traces naturally express unwinding, coroutines, and non-bracketed jumps) | **Core LTS / `trefines`: No.** High-level `rec_to_asm` proof automation uses Iris Kripke worlds/step-indexing |
| **Melocoton** (OOPSLA 2023) | `logsem/melocoton@039dae32` (DOI `10.1145/3622823`) | Wrapper `link (wrap e) p` with opposite dual-nondeterminism polarity (`umrel`) and `GC(θ)` heap-abstraction token | Yes (including Landin's knot across ML-C FFI) | Yes (ML abstract GC heap vs. C flat memory via `θ` bijection) | Partial (GC roots/callbacks modeled; C++ unwinding not modeled) | **Yes — Transfinite Iris** (`oofe`/`oupred` + `siProp_witness` classical choice) because angelic choice is embedded inside step-indexed WP |
| **Simuliris** (POPL 2022; Tree Borrows PLDI 2025) | DOIs `10.1145/3498689`, `10.1145/3735592` | Intra-language concurrent thread pool (no heterogeneous MIR+ISA linker) | Intra-language only | Single language heap (`Tree Borrows` ghost state) | Intra-language only | **Yes** (full Iris COFEs, `▷`, `ghost_map`, impredicative invariants) |
| **Cerise** (JACM 2024) | `logsem/cerise@9eb72e67` (`theories/logrel.v:54-160, 218-230`, DOI `10.1145/3623510`) | Flat capability-machine registers + `WCap E` sentry capabilities (no abstract call stack) | Yes (arbitrary untrusted assembly calling capabilities) | Single flat capability machine memory | Arbitrary jumps via capabilities | **Yes** (contravariant guarded recursive domain equation `fixpoint interp1`, `Contractive interp1`, `▷`, `inv (logN .@ a)`) |

**The exact COFE / step-indexing necessity line for Lean 4:**
Why do Melocoton and Cerise require Iris COFEs and step-indexing while CompCertO,
CompCertM, and DimSum's semantic core do not?

- **When COFEs/step-indexing ARE mathematically forced:** Whenever the verification
  target universally quantifies over *unverified/arbitrary* foreign code that can
  store arbitrary **higher-order closures or callable function pointers inside
  mutable shared memory** (Landin's knot across the FFI boundary). Defining the
  logical-relation value interpretation $\mathcal{V}(v)$ requires referring to
  the invariant of heap cells that themselves hold values satisfying $\mathcal{V}$,
  creating a contravariant recursive domain equation
  $\text{World} \cong \text{Addr} \rightharpoonup_{\text{fin}} (\text{World} \to \text{Prop})$
  (explicitly visible in Cerise `theories/logrel.v:54-160`, where `interp1` is
  constructed via Banach's fixed-point theorem on a COFE using `Contractive`).
- **When COFEs/step-indexing are NOT needed (Lean 4 Pass-1 sweet spot):** When
  interleaved MIR and ISA components are either (a) *both verified* (Rust MIR +
  verified `asm!`/external assembly) or (b) foreign code is governed by
  *first-order or stratified function-pointer contracts* (e.g., a fixed callback
  signature `extern "C" fn(*mut c_void)` whose pre/postcondition quantifies over
  first-order memory invariants and Tree Borrows permissions, without storing
  self-referential higher-order predicates in heap cells). Under this regime:
  - A **CompCertO/CompCertM heterogeneous call stack** (`List (LinkFrame SM SI M Q R)`)
    models arbitrary depth `MIR -> ISA -> MIR -> ISA` reentrancy directly via
    ordinary inductive types.
  - A **DimSum-style external event trace** (`StepOut.ext ev next`, `TraceReaches`,
    `DivergesTrace`) records externally visible foreign calls/syscalls and
    supports non-local unwinding transitions without changing the kernel logic.
  - A **first-order Kripke address valuation $\alpha$** (monotone map from
    `AllocId` to disjoint `[base, base + size)` ranges) plus `exposed : Set AllocId`
    bridges MIR's block-offset memory to ISA's flat byte memory.
  - Part C of `support/ReentrantInterleavedBridgeAndOracleComposition.lean`
    mechanizes this exact heterogeneous reentrant linking architecture in pure
    Lean 4.34.1 (`Init`-only) and proves `reentrant_heterogeneous_stack_composition`
    preserving `BehaviorTrace`, `FaultTrace`, and `DivergesTrace` using only
    `[propext, Classical.choice]`.

### 3. Tree Borrows Protectors, Provenance Exposure, and Local-State Encapsulation Across Reentrant FFI and Inline Assembly

Basis: normative + source + execution + derived

#### 3.1 `FnEntry` Protectors Across FFI Calls and Reentrant Callbacks

In `rustc`'s Miri interpreter (`rust-lang/rust@8144389c`,
`compiler/rustc_const_eval/src/interpret/call.rs:599, 840-878`) and its Lean
port (`proofs-rs/lean-miri@c92d1d97`, `Miri/Interpreter/Call.lean:392, 571-601`,
`CallDispatchMachine.lean:33-40`):

- On a normal Rust MIR call, `init_stack_frame` pushes a new stack frame (giving
  it a fresh `CallId` / protector slot) and invokes `with_retag_mode(RetagMode::FnEntry)`
  on every function argument, installing a `StrongProtector` in
  `global.protectedTags` for every `&T` and `&mut T` parameter (and `WeakProtector`
  for `Box<T>`). That protector stays live until that exact Rust frame pops (on
  normal return or unwind).
- On a foreign `extern` call, `findMirOrEvalFn` dispatches to
  `ForeignItems.emulate` (returning `none` for a MIR body) and **skips
  `initStackFrame`**—unless the foreign symbol resolves to a Rust-defined
  `#[no_mangle] extern "C" fn` body via `lookupFunction`, in which case it enters
  `initStackFrame` like a normal Rust function. Consequently:
  1. A pure C or assembly callee installs **no callee-side `FnEntry` protector**
     on pointer parameters (`*const T` / `*mut T` receive no `FnEntry` retag).
  2. Every **suspended outer Rust frame** remains on the call stack with its
     `FnEntry` `StrongProtector` active throughout both foreign execution and
     any reentrant Rust callback (`Rust_0 -> Foreign_1 -> Rust_2`).
  3. When the reentrant callback `Rust_2` exits, only `Rust_2`'s frame protectors
     are retired (`releaseFrameProtectors`, mechanized in
     `reentrant_stack_preserves_outer_protector`); `Rust_0`'s outer protectors
     remain enforced until `Rust_0` itself returns or unwinds.

Live execution under Miri (`MIRIFLAGS="-Zmiri-tree-borrows"`,
`support/miri_reentrant_tb_and_alloc_probe.rs`) confirms all four reentrant
aliasing scenarios while an outer `fn outer(x: &mut u32)` holds a live
`StrongProtector` on `x` (initially `ReservedFrz false`):

| Scenario during reentrant callback `cb` | Tree Borrows transition on outer `x: &mut u32` | Live Miri result (`-Zmiri-tree-borrows`) | Mechanized Lean theorem |
|---|---|---|---|
| `cb` writes via `user_data` derived from `x` (`LocalAccess` write) | `ReservedFrz false -> Unique` (valid activation) | **OK** (`ok_reentrant_callback_child_write_activates_outer_protector`) | `reentrant_callback_child_write_activates_outer` |
| `cb` writes via global/sibling root pointer (`ForeignAccess` write) | Protected `ReservedFrz false` foreign write -> `Disabled` forbidden -> **UB** | **UB**: `write access through <tag> (root of the allocation) ... is forbidden` | `reentrant_callback_sibling_write_triggers_outer_protector_ub` |
| `cb` reads via global/sibling root pointer (`ForeignAccess` read), then `outer` writes `*x = 123` | `ReservedFrz false -> ReservedFrz true` (conflicted); subsequent `outer` local write on protected conflicted tag -> **UB** | **UB**: `write access through <tag> ... is forbidden` | `reentrant_callback_foreign_read_then_outer_write_ub` |
| `cb` reads via global/sibling root pointer (`ForeignAccess` read), and `outer` only reads `*x` (never writes) | `ReservedFrz false -> ReservedFrz true`; local read allowed; frame exits cleanly | **OK** (`ok_reentrant_callback_foreign_read_if_outer_mut_never_writes`) | Follows from `tbStep .read .local_ (.reservedFrz true) true true = .ok (.reservedFrz true)` |

The third and fourth rows highlight a critical compositional subtlety for FFI
callback specifications: under Tree Borrows (unlike Stacked Borrows, which
rejects the sibling read immediately on `&mut T` entry), a reentrant callback
reading through a sibling alias *silently taints* an unactivated outer `&mut T`
into `ReservedFrz true`. Whether UB occurs depends on whether the outer Rust
function later writes through `x` after the foreign call returns! Any
compositional FFI contract therefore cannot treat an outer `&mut T`'s Tree
Borrows state as invariant across a foreign call unless the contract forbids
foreign reads of aliased ancestors or tracks the `conflicted` bit explicitly.

#### 3.2 Exposed Provenance, Wildcard Tracking, and Local-State Encapsulation

Under PNVI-ae-udi (Memarian et al., POPL 2019; WG14 N2676 / N3005 / ISO/IEC
TS 6010), MiniRust (`minirust/minirust@063d7841`, `spec/mem/intptrcast.md`),
Miri (`rust-lang/miri@7fa591d7`, `src/borrow_tracker/tree_borrows/wildcard.rs:85-182`),
and `lean-miri` (`Miri/Memory/AllocAddresses/GlobalState.lean:324-375`,
`Miri/Interpreter/PointerMachine.lean:78-103`,
`Miri/TreeBorrows/TreeState.lean:78-97, 413-504, 576-615`):

1. **Concrete exposure vs. `.addr()` inspection:**
   - Calling `ptr.expose_provenance()` (or `ptr as usize`) marks both the
     allocation (`allocId ∈ state.exposed`) and, in Tree Borrows, the borrow
     tag's subtree exposure counters (`ExposedCache`).
   - Calling `ptr.addr()` (strict provenance) yields the integer address
     *without* adding `allocId` to `state.exposed`.
   - Calling `std::ptr::with_exposed_provenance(addr)` creates a `Wildcard`
     pointer; resolving it via `allocIdFromAddr` (`GlobalState.lean:347`) filters
     strictly to live allocations where `id ∈ state.exposed`.
2. **Tree Borrows `ExposedCache` wildcard relatedness (`wildcard.rs:85-182`):**
   When a wildcard pointer accesses a byte in an exposed allocation, Tree Borrows
   compares the number of exposed tags inside node `n`'s subtree (`local_count`)
   against the total exposed tags in the tree (`total_count`):
   - `local_count == total_count` (all exposed tags are inside `n`'s subtree) ->
     `LocalAccess` (e.g., child exposed, root unexposed -> **OK** under outer
     `&mut` protector; verified by `ok_exposed_child_wildcard_write_preserves_outer_protector`).
   - `local_count == 0` (no exposed tag inside `n`'s subtree) -> `ForeignAccess`
     (e.g., root exposed, child unexposed -> **UB** protector violation;
     verified by `ub_exposed_root_unexposed_child_wildcard_write_violates_protector`).
   - `0 < local_count < total_count` (both an ancestor/sibling and a child tag
     are exposed) -> `EitherAccess`, which Tree Borrows resolves *optimistically*
     as a no-op on `n` (verified by
     `ok_both_root_and_child_exposed_wildcard_write_either_access_optimistic`).
3. **Eager exposure vs. explicit bijection $\alpha$ across `asm!` / FFI:**
   - **When exposure IS required:** If foreign C or assembly code strips
     provenance into untyped integers (e.g., low-bit pointer tagging, XOR linked
     lists, storing pointers in integer registers/structs across opaque ABI
     boundaries without tracked provenance) and later passes an integer back to
     Rust via `with_exposed_provenance`, the Rust boundary *must* expose the
     pointer's provenance on exit.
   - **Why eager exposure is undesirable when avoidable:** Miri's
     `-Zmiri-native-lib` (`src/shims/native_lib/mod.rs:344-404`) eagerly exposes
     every pointer passed to C (and transitively reachable pointers in
     non-tracing mode) and notably **skips Tree Borrows `perform_access` during
     native C execution**, invoking only `expose_provenance` on reads and
     `Allocation.processNativeWrite` (byte initialization + wildcard fragments)
     on writes. For a sound formal verifier, eagerly exposing pointers degrades
     precision because any simultaneously exposed ancestor creates `EitherAccess`
     aliasing ambiguity. Instead, when verifying structured `asm!` or verified
     external assembly, keeping an **explicit monotone address valuation $\alpha : \text{AllocId} \rightharpoonup_{\text{fin}} \text{Addr}$**
     (preserving concrete `(AllocId, BorTag)` metadata alongside each ISA
     register/memory word for structured pointer-passing operands, and falling
     back to `exposed` / `Wildcard` only when the assembly actually performs
     provenance-destroying integer arithmetic) maintains full Tree Borrows
     precision.
4. **Defeating foreign stack scanning (`sp` arithmetic) and the flat-ISA proof
   obligation:**
   - In abstract MIR/PNVI-ae-udi semantics, private Rust stack locals are never
     added to `state.exposed` unless their address escapes via `expose_provenance`
     or an explicit pointer-to-foreign pass. Live Miri execution
     (`ub_unexposed_stack_local_addr_guess_fails`) confirms that forging a
     pointer to a live stack local via `with_exposed_provenance((&raw const secret).addr())`
     and executing `std::ptr::read` fails immediately with
     `attempting to access 4 bytes, but got 0x...[noalloc] which is a dangling pointer (it has no provenance)`
     (mechanized in `unexposed_stack_local_guess_is_ub`). Note that Rust's
     `let _ = *forged;` is a MIR `PlaceMention` rather than a memory load and
     does not trigger the access check; an actual read (`std::ptr::read` or
     value copy) is required.
   - **Crucial boundary for real ISA verification:** A real CPU (`x86_64` /
     `AArch64` / `RISC-V`) has no hardware provenance tag blocking `ld x0, [sp, #offset]`
     from reading a caller's unexposed Rust stack frame! Therefore, when linking
     MIR ($M_{\text{ref}}$) with a flat ISA oracle ($I_{\text{ref}}$), local-state
     encapsulation holds **only if** the ISA-side verification obligation proves
     **spatial memory-footprint containment**: every load/store executed by the
     foreign assembly falls inside either (a) the callee's own freshly allocated
     stack frame or (b) the byte intervals `[α(aid), α(aid) + size)` of
     allocations explicitly passed or exposed to the foreign call. Without that
     ISA footprint side-condition (or hardware capabilities / SFI), flat ISA
     execution can violate abstract MIR stack encapsulation.

### 4. Foreign vs. Rust Heap Allocator Coexistence in a Shared Flat ISA Address Space

Basis: normative + source + execution + derived

When C `malloc`/`calloc`/`realloc`/`free` and Rust's `GlobalAlloc`
(`__rust_alloc`, `__rust_alloc_zeroed`, `__rust_realloc`, `__rust_dealloc`)
coexist in the same flat virtual address space, their allocations occupy
disjoint address intervals under $\alpha$ **and** strictly disjoint deallocation
domains. Direct inspection of `rust-lang/miri@7fa591d7` (`src/shims/alloc.rs:80-275`),
`proofs-rs/lean-miri@c92d1d97` (`Miri/Memory/MiriMemoryKind.lean:8-11`,
`Miri/Memory/MemoryState.lean:1127-1134`, `Miri/Interpreter/ForeignItems.lean:180-325`),
and live Miri execution (`support/miri_reentrant_tb_and_alloc_probe.rs`) establish
the exact cross-allocator contract:

| Operation | `MiriMemoryKind` / layout rule | Live Miri result (`-Zmiri-tree-borrows`) | `lean-miri@c92d1d97` behavior |
|---|---|---|---|
| `malloc(0)` then `free(p)` | Allocates a live 0-byte `MiriMemoryKind.c` block (distinct non-null address); `free` succeeds once | **OK** (`ok_c_malloc_zero_allocates_and_frees_once`) | `ForeignItems.lean:212-239`: allocates 0-byte `.c` block; `free` deallocates with `oldSizeAndAlign := none` |
| `malloc(0)` then `free(p); free(p)` | Second `free` hits freed allocation | **UB**: `alloc... has been freed, so this pointer is dangling` | `MemoryState.lean`: deallocated entry -> UB |
| `free(NULL)` | Special-cased legal no-op (`addr == 0`) | **OK** (`ok_c_malloc_zero_allocates_and_frees_once`) | `ForeignItems.lean:231`: returns unit on `addr == 0` |
| `free(NonNull::<u64>::dangling())` | Non-null dangling pointer (`prov = none`, e.g. `0x8`) is NOT a valid `.c` allocation | **UB**: `pointer must point to some allocation, but got 0x8[noalloc]` | Fails `checkPtr` / `allocId` lookup -> UB |
| `realloc(p, 0)` | C23 §7.24.3.5 / WG14 N2464: `realloc` with size 0 is UB | **UB**: `` `realloc` with a size of zero `` | `ForeignItems.lean:259`: `throw (.undefinedBehavior "realloc with size zero")` |
| `__rust_alloc(0, align)` | Rust `GlobalAlloc::alloc` precondition requires `layout.size() > 0` (safe `Global::allocate` returns `NonNull::dangling()` without calling `__rust_alloc`) | N/A (blocked at `GlobalAlloc` contract; Miri checks size > 0) | `ForeignItems.lean:287`: `throw (.undefinedBehavior "creating allocation with size 0")` |
| Rust `alloc(L)` freed by C `free(p)` | `entry.kind == .rust ≠ .c` | **UB**: `deallocating alloc..., which is Rust heap memory, using C heap deallocation operation` | `MemoryState.lean:1128`: `.error (.memoryKindMismatch allocId)` |
| C `malloc(n)` freed by Rust `dealloc(p, L)` | `entry.kind == .c ≠ .rust` | **UB**: `deallocating alloc..., which is C heap memory, using Rust heap deallocation operation` | `MemoryState.lean:1128`: `.error (.memoryKindMismatch allocId)` |
| Rust `alloc(L1)` freed by Rust `dealloc(p, L2)` (`L1 ≠ L2`) | `oldSizeAndAlign = some (size, align)` mismatch | UB (`incorrect layout on deallocation`) | `MemoryState.lean:1132`: `.error (.layoutMismatch allocId ...)` |

**Formal heap-ownership transfer invariant across FFI:**
In a mixed MIR-ISA heap (`MixedHeap`), every live allocation carries an immutable
`AllocDomain` tag (`rustGlobal size align | foreignC size | rustStack frameId`).
Passing a pointer across FFI can transfer *read/write/aliasing ownership* (via
Tree Borrows permissions and separation-logic points-to resources), but **never
mutates `AllocDomain`**. A foreign component that takes ownership of a
Rust-allocated buffer cannot call C `free` on it; it must release the buffer by
invoking a Rust-exported destructor (`extern "C" fn(*mut T)`) carrying the exact
`Layout`, and symmetrically Rust taking ownership of a `malloc`'d buffer must
reclaim it via C `free` (never `Box::from_raw` / `Global::deallocate`).

### 5. `vendor/lean-miri` (`M_ref`) Hook Inventory and Pass-2 Correspondence Composition Architecture

Basis: source + execution + derived

#### 5.1 Direct Hook Audit of `joshlf/anneal@c131b320` and `proofs-rs/lean-miri@c92d1d97`

Static verification via `support/audit_lean_miri_ffi_hooks.py` against
`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` and its vendored
`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` yields the exact
inventory:

- **Vendored footprint (`vendor/lean-miri/UPSTREAM_PIN.json`):**
  608 total vendored `.lean` files, of which **160 modules** comprise
  `execution_machine_closure` (10 patched files). Exactly **22 `Native*` modules**
  (including `NativeMachine.lean` and `Native/Supervisor.lean`) and **23 platform
  `Foreign*` modules** (`UnixForeign`, `LinuxForeign`, `WindowsForeign`, etc.)
  reside in the vendor tree **outside** the 160-module closure.
- **`TerminatorKind.InlineAsm` gap:**
  `Miri/MIR/Syntax.lean:470-523, 560` **already defines** the complete
  `InlineAsmTerminator` AST (`asmMacro`, `template`, `operands`, `options`,
  `targets`, `unwind`) and `TerminatorKind.InlineAsm`. However,
  `Miri/Interpreter/ControlFlow.lean:116-131` defines `TerminatorHooks` with
  fields `{call, drop, unwind, checkBool, evalOperand, readInt}` and **NO
  `inlineAsm` field**, and line 151 hardcodes:
  `| .InlineAsm _ => return (state, .error (.unsupported "inline assembly"))`.
- **Foreign `Call` hooks already inside the 160-module closure:**
  `Miri.Interpreter.Call`, `CallDispatchMachine`, `ForeignItems` (including
  `Core.callNative`, `ForeignItems.emulate`, `lookupFunction`, `specialAllocator`,
  `malloc`/`free`/`realloc`), `Unwind`, `TreeState`,
  `AllocAddresses.GlobalState`, `MiriMemoryKind`, and `RunLoop` are **all already
  inside** the 160-module `execution_machine_closure`.
- **Current `Trusted/Correspondence.lean@c131b320` and `TrustedBoundary.lean` locks:**
  1. `Trusted/MirSemantics.lean` fails closed on both `.call` and `.unsupported`
     (where `InlineAsm` currently lowers).
  2. `Trusted/Correspondence.lean` pins `evalRefStep` to single-frame execution
     (`rs.frames = [callerSentinelFrame retTy, rf]`), calls `Step.step` directly
     with `refStepHooksFor` (bypassing `ExecutionMachine.step` and
     `CallDispatchMachine`), and defines closed `CorrespondenceClaim` and
     `FaultEquivalenceClaim` over `TerminalOut` and `Diverges` with no external
     event trace.
  3. `TrustedBoundary.lean:2030-2088` (`verifyRefEvaluatorIndependence`) locks
     **21 required `Miri.*` primitives** and **25 forbidden `Trusted.MirSemantics.*`
     evaluators** in `Correspondence.lean`'s transitive cone.

#### 5.2 Satisfying `docs/mir-correspondence-strategy.md` §4.2 and §4.4 via Two-Oracle Horizontal Composition

`docs/mir-correspondence-strategy.md` §4.2 requires that every construct modeled
by `M_anneal` be modeled by `M_ref` (never weakening correspondence to an
unsupported escape hatch), and §4.4 notes that closed `TerminalOut` suffices
only while external I/O and FFI side effects are excluded. Adding `InlineAsm`
and FFI cleanly under Pass-2 auditability splits into three orthogonal
mechanisms—all mechanized in `support/ReentrantInterleavedBridgeAndOracleComposition.lean`:

1. **Minimal audited hook patch in `vendor/lean-miri`:**
   Do **not** embed an ISA decoder or Sail interpreter inside `vendor/lean-miri`.
   Instead, add a single optional `inlineAsm` callback field to `TerminatorHooks`
   in `Miri/Interpreter/ControlFlow.lean` (defaulting to
   `.error (.unsupported "inline assembly")` when omitted, preserving exact
   upstream behavior for pure-MIR callers) and route foreign `Call` terminators
   through the existing `CallDispatchMachine.Hooks.foreign` boundary. This keeps
   `vendor/lean-miri` focused on Rust MIR operational semantics (1 patched file
   in `LOCKED_PATCHED_MIRI_FILES`) and preserves Pass-2 separation between the
   Rust MIR reference (`vendor/lean-miri`) and ISA references (e.g. Sail / LNSym).
2. **Parameterized external oracle $\mathcal{O}$ and two-oracle horizontal composition:**
   - **Leaf `InlineAsm` / non-reentrant leaf FFI (`Part B`):** Parameterize both
     $M_{\text{anneal}}(\mathcal{O})$ and $M_{\text{ref}}(\mathcal{O})$ by a
     shared `ExternalOracle Q R E M`. Proving `OpenMirSim mA mR Rel` once proves
     correspondence universally for **all** instantiations of $\mathcal{O}$
     (`parametric_oracle_correspondence`), and combining it with oracle
     equivalence `OracleEquiv oA oR` (between Anneal's ISA/FFI semantics
     `I_anneal` and a golden ISA reference `I_ref`) yields full
     `BehaviorTrace`, `FaultTrace`, and `DivergesTrace` equivalence
     (`horizontal_two_oracle_composition`).
   - **Arbitrarily reentrant `MIR <-> ISA` FFI (`Part C`):** Model MIR and ISA
     as symmetric `OpenComponent`s linked by a CompCertO/CompCertM heterogeneous
     call stack `LinkedState` (`linkStep`), exchanging `(CallQuery, RetReply, SharedMem)`
     across the bridge relation (which carries allocations, Tree Borrows trees,
     per-frame active protectors, `exposed` set, and `AllocDomain` tags).
     Theorem `reentrant_heterogeneous_stack_composition` proves that proving
     open MIR correspondence (`OpenCompSim mA mR RelM`) and open ISA
     correspondence (`OpenCompSim iA iR RelI`) separately composes horizontally
     to exact `BehaviorTrace`, `FaultTrace`, and `DivergesTrace` equivalence of
     `M_anneal ⊕_stack I_anneal` and `M_ref ⊕_stack I_ref` across arbitrary
     reentrant callback depth—with zero Iris COFEs and zero step-indexing.
3. **Mandatory trace-indexed correspondence once external effects enter:**
   Closed `TerminalOut`-only correspondence is strictly unsound once `InlineAsm`
   or FFI emits observable external events (syscalls, MMIO, foreign I/O).
   Theorem `closed_terminal_out_insufficient_for_effectful_ffi` constructs two
   concrete machines (`stepA`, `stepB`) with identical terminal value `()` and
   identical non-faulting behavior, yet conflicting external traces `[1]` vs.
   `[2]`. Extending `Trusted.Correspondence` to `BehaviorTrace`, `FaultTrace`,
   and `DivergesTrace` is therefore mandatory before admitting effectful
   `InlineAsm` or foreign calls into the correspondence claim.

## Boundaries

- **Weak memory / cross-thread FFI concurrency (`not examined`):** All Tree
  Borrows, provenance, and two-oracle composition results here assume
  single-threaded sequential interleaving (`Rust -> Foreign -> Rust`). Relaxed
  atomics, C11/C++20 memory-model interaction with Rust atomics across FFI, and
  concurrent foreign threads invoking Rust callbacks simultaneously were not
  examined.
- **Concrete Sail / LNSym ISA decoder integration (`not examined`):** This
  report establishes the abstract `OpenComponent` / `ExternalOracle` composition
  interface and `vendor/lean-miri` hook surface; it does not inspect concrete
  Sail/LNSym AST encodings, ABI calling-convention register marshaling details,
  or DWARF CFI unwinding tables for specific ISAs (`x86_64`, `AArch64`, `RISC-V`).
- **Higher-order untrusted foreign code with Landin's knot (`known not to apply`):**
  The COFE-free heterogeneous stack composition in Part C applies to verified
  MIR+ISA components and first-order/stratified FFI callback contracts. It is
  known *not* to suffice for universally quantifying over arbitrary unverified
  foreign assembly that stores self-referential higher-order closures or
  capabilities in mutable shared heap (which requires guarded recursive worlds /
  COFEs as in Melocoton and Cerise).
- **Exact Rust semantics of `catch_unwind` on foreign exceptions and `Drop`
  execution before `"C"` panic abort (`unknown` / unspecified by Rust
  Reference):** Per `rust-lang/reference@c9cc3282`, whether inner `Drop`s run
  before aborting at a non-unwinding `extern "C"` boundary and whether
  `catch_unwind` aborts or returns `Err(opaque)` on a foreign exception are
  explicitly unspecified; formal models must treat both outcomes as admissible
  nondeterministic behaviors.
- **Miri `-Zmiri-native-lib` reentrant callbacks and Tree Borrows checking
  during native execution (`unsupported`):** `rust-lang/miri@7fa591d7`
  explicitly rejects reentrant callbacks from native libraries into Rust and
  does not run Tree Borrows `perform_access` on individual C memory operations.
  Do not treat passing `-Zmiri-native-lib` runs as evidence of Tree Borrows
  soundness inside C code.
- **Miri `TerminatorKind::InlineAsm` execution (`unsupported`):** Both
  `rust-lang/miri@7fa591d7` and `proofs-rs/lean-miri@c92d1d97`
  (`ControlFlow.lean:151`) reject `InlineAsm` as `.unsupported`.
- **Single-frame `Trusted.Correspondence` lockstep assumption (`known not to
  apply` to multi-frame calls):** `Trusted/Correspondence.lean@c131b320`
  hardcodes `rs.frames = [callerSentinelFrame retTy, rf]`; lifting
  correspondence to reentrant `Call` / `InlineAsm` requires generalizing the
  state relation to arbitrary stacks (`StackRel`) and relaxing the fixed-length
  frame invariant in `evalRefStep`.

## Evidence

### 1. Primary Source Inspections (Observed 2026-11-20)

- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
  - `docs/mir-correspondence-strategy.md` (§4.2, §4.4 lines 552-561): requirement
    that `M_ref` model every construct in `M_anneal`, and deferral of
    `BehaviorTrace` until external effects are added.
  - `trusted/lean/Trusted/MirAst.lean` & `trusted/lean/Trusted/MirSemantics.lean`:
    `.call _ _ _ _ _` and `.unsupported` (including `InlineAsm`) fail closed.
  - `trusted/correspondence/Trusted/Correspondence.lean`: `evalRefStep`
    requires `rs.frames = [callerSentinelFrame retTy, rf]`, invokes `Step.step`
    with `refStepHooksFor`, and defines closed `CorrespondenceClaim` /
    `FaultEquivalenceClaim` over `TerminalOut` and `Diverges`.
  - `trusted/audit/TrustedBoundary.lean:2030-2088`: `verifyRefEvaluatorIndependence`
    pins 21 required `Miri.*` constants and 25 forbidden `Trusted.MirSemantics.*`
    evaluators.
- **`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (vendored in
  `joshlf/anneal@c131b320` under `vendor/lean-miri/`):**
  - `UPSTREAM_PIN.json`: 608 vendor files, 160 `execution_machine_closure`
    modules, 10 patched files; pins `rust-lang/miri@7fa591d7` and
    `rust-lang/rust@8144389c`.
  - `Miri/MIR/Syntax.lean:470-523, 560`: complete `InlineAsmTerminator` AST and
    `TerminatorKind.InlineAsm`.
  - `Miri/Interpreter/ControlFlow.lean:116-131, 151`: `TerminatorHooks` omits
    `inlineAsm`; line 151 returns `.error (.unsupported "inline assembly")`.
  - `Miri/Interpreter/Call.lean:392, 571-601` and `CallDispatchMachine.lean:33-40`:
    foreign call dispatch via `findMirOrEvalFn` / `ForeignItems.emulate`,
    bypassing `initStackFrame` unless resolved to an exported Rust MIR body.
  - `Miri/Interpreter/ForeignItems.lean:180-325`: `malloc(0)` allocates 0-byte
    `.c` block, `free(NULL)` no-ops (`line 231`), `realloc(p, 0)` throws UB
    (`line 259`), `__rust_alloc(0, _)` throws UB (`line 287`).
  - `Miri/Memory/MiriMemoryKind.lean:8-11` & `MemoryState.lean:1127-1134`:
    `.rust` vs. `.c` deallocation `memoryKindMismatch` and `layoutMismatch`.
  - `Miri/Memory/AllocAddresses/GlobalState.lean:324-375`,
    `PointerMachine.lean:78-103`, `TreeBorrows/TreeState.lean:78-97, 413-504, 576-615`:
    `exposed` set, `allocIdFromAddr`, and Tree Borrows `ExposedCache`.
  - `Miri/Interpreter/NativeMachine.lean` & `Native/Supervisor.lean:91`: outside
    the 160-module closure; single big-step `host.execute` rejecting native
    callbacks into Rust.
- **Upstream specifications and mechanizations:**
  - `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`:
    `src/shims/native_lib/mod.rs:344-404, 488-516`, `src/shims/alloc.rs:80-275`,
    `src/borrow_tracker/tree_borrows/wildcard.rs:85-182`.
  - `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`:
    `compiler/rustc_const_eval/src/interpret/call.rs:599, 840-878`.
  - `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:
    `src/items/external-blocks.md`, `src/items/functions.md:245-263`,
    `src/panic.md:118-141`.
  - `minirust/minirust@063d784186d3252bee242217f218223205c0b568`:
    `spec/mem/intptrcast.md`, `spec/mem/tree_borrows/memory.md`.
  - `CertiKOS/compcert@87a62d95cd24a44e3ecd5fefddc70a969a881bcb` (`compcerto`):
    `common/LanguageInterface.v:11-64`, `common/CallconvAlgebra.v`,
    `common/SmallstepLinking.v:31-46`.
  - `snu-sf/CompCertM@1bf2113b2381df604a3abcce7711af1f154d1620`:
    `compose/Sem.v:26-90`, `compose/ModSem.v:19-26`.
  - `logsem/cerise@9eb72e675216d7c5473499f392b18049364db03a`:
    `theories/logrel.v:54-160, 218-230`.
  - `logsem/melocoton@039dae32893a33bc70d668a7abcd25d54587dc3c` (OOPSLA 2023,
    DOI `10.1145/3622823`); DimSum (POPL 2023, DOI `10.1145/3571220`, Zenodo
    `10.5281/zenodo.7306312`); Simuliris (POPL 2022, DOI `10.1145/3498689`);
    Tree Borrows (PLDI 2025, DOI `10.1145/3735592`); PNVI-ae-udi (POPL 2019,
    DOI `10.1145/3290380`).

### 2. Executable Probes Preserved in `support/` (Observed 2026-11-20)

1. **`support/miri_reentrant_tb_and_alloc_probe.rs`** — 14 standalone unit tests
   executed under `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` /
   `miri 0.1.0 (3ef0c22cdb 2026-11-11)` with `MIRIFLAGS="-Zmiri-tree-borrows"`
   (edition 2024, `x86_64-unknown-linux-gnu`): **14/14 matched** expected
   OK/UB outcomes, including exact Miri diagnostics for:
   - `ub_reentrant_callback_sibling_write_violates_outer_protector`:
     `write access through <tag> (root of the allocation) ... is forbidden`
   - `ub_reentrant_callback_foreign_read_conflicts_outer_reserved_mut`:
     `write access through <tag> ... is forbidden`
   - `ub_exposed_root_unexposed_child_wildcard_write_violates_protector`:
     `write access through <wildcard> ... is forbidden`
   - `ub_unexposed_stack_local_addr_guess_fails`:
     `memory access failed: attempting to access 4 bytes, but got 0x...[noalloc] which is a dangling pointer (it has no provenance)`
   - `ub_c_malloc_zero_double_free`:
     `alloc... has been freed, so this pointer is dangling`
   - `ub_cross_allocator_rust_alloc_freed_by_c_free` &
     `ub_cross_allocator_c_malloc_freed_by_rust_dealloc`:
     `deallocating alloc..., which is Rust/C heap memory, using C/Rust heap deallocation operation`
   - `ub_c_free_on_rust_dangling_zst_ptr`:
     `pointer must point to some allocation, but got 0x8[noalloc]`
   - `ub_c_realloc_size_zero`:
     `` `realloc` with a size of zero ``
2. **`support/audit_lean_miri_ffi_hooks.py`** — Read-only static audit executed
   against `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: exited `0`
   confirming `vendor_lean_files: 608`, `execution_machine_closure_modules: 160`,
   `native_modules_outside_closure: 22`, `foreign_modules_outside_closure: 23`,
   `required_miri_primitives: 21`, `forbidden_anneal_evaluators: 25`, and
   `inline_asm_hook_present: false`.
3. **`support/ReentrantInterleavedBridgeAndOracleComposition.lean`** — Pure
   Lean 4 (`Init`-only) formalization kernel-checked with `leanprover/lean4`
   `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using
   `lean -DElab.async=false -Ddebug.skipKernelTC=false`: exited `0` with all 12
   theorems verified (`big_step_bridge_blind_to_callback_semantics`,
   `reentrant_stack_preserves_outer_protector`,
   `reentrant_callback_child_write_activates_outer`,
   `reentrant_callback_sibling_write_triggers_outer_protector_ub`,
   `reentrant_callback_foreign_read_then_outer_write_ub`,
   `unexposed_stack_local_guess_is_ub`, `cross_allocator_and_malloc_zero_laws`,
   `ffi_unwind_abi_laws`, `horizontal_two_oracle_composition`,
   `parametric_oracle_correspondence`,
   `closed_terminal_out_insufficient_for_effectful_ffi`, and
   `reentrant_heterogeneous_stack_composition`). `#print axioms` confirmed zero
   `sorryAx`, zero `Lean.ofReduceBool`, and axioms restricted strictly to Lean's
   standard `{propext, Classical.choice, Quot.sound}` (with
   `reentrant_heterogeneous_stack_composition` using only `[propext, Classical.choice]`).

## Revalidation

1. **Re-run Miri Tree Borrows / exposed provenance / allocator probe:**
   Copy `support/miri_reentrant_tb_and_alloc_probe.rs` into a temporary Rust
   crate (`edition = "2024"`) and run each test individually under
   `MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test --lib -- --exact <test_name>`.
   Confirm all `ok_*` tests exit `0` and all `ub_*` tests exit non-zero with
   `error: Undefined Behavior:`. Re-check if Miri changes wildcard
   `EitherAccess` optimism, Tree Borrows `ReservedFrz` conflict rules, or
   `malloc(0)` / `realloc(p, 0)` shims.
2. **Re-run static `lean-miri` / Anneal hook audit:**
   Run `python3 support/audit_lean_miri_ffi_hooks.py <path-to-anneal-checkout>`
   after any `vendor/lean-miri` upgrade or `Trusted.Correspondence` /
   `TrustedBoundary` change. A failing assertion pinpoints the exact hook,
   closure boundary, or evaluator-independence list that shifted (for example,
   when `inlineAsm` is added to `TerminatorHooks` or `evalRefStep` is lifted to
   multi-frame stacks).
3. **Re-check Lean 4 composition proofs:**
   Run `lean -DElab.async=false -Ddebug.skipKernelTC=false support/ReentrantInterleavedBridgeAndOracleComposition.lean`
   under the pinned Lean 4 toolchain (`v4.34.1` or newer) and verify exit code
   `0` and clean `#print axioms` output.
4. **Upstream normative drift checks:**
   Diff `rust-lang/reference` (`src/items/functions.md`, `src/panic.md`) for
   changes to `C-unwind` or `catch_unwind` on foreign exceptions, and diff
   `rust-lang/miri` (`src/shims/native_lib/mod.rs`) if native FFI gains
   reentrant callback support or per-access Tree Borrows instrumentation.
