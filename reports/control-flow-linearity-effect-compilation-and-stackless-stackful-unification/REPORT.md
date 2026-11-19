# Control-Flow Linearity, Algebraic Effect Compilation, Stackless/Stackful Unification, and Register Error Channels

## Summary

Modern systems and managed runtimes face four tightly intertwined control-flow design tensions: (1) combining linear/affine ownership (file handles, session channels, DMA tokens, RAII guards) with algebraic effect handlers without duplicating or leaking linear resources; (2) compiling algebraic effects to native code without paying coroutine/continuation allocation overhead on common tail-resumptive operations; (3) unifying stackless state-machine async code (`Rust`/`JS`/`C#`) and stackful fiber/green-thread runtimes (`Go`/`JVM`/`OCaml`) across one FFI boundary without carrier-thread pinning or double-colored APIs; and (4) propagating typed errors across mixed-language call graphs without paying DWARF `.eh_frame` metadata bloat or optimization barriers.

Key established findings from primary compiler sources, W3C/Wasm specifications, peer-reviewed papers, and executable probes:

1. **Value linearity is unsound in the presence of general effect handlers unless paired with control-flow linearity ($F^\circ_{\text{eff}}$ / $Q^\circ_{\text{eff}}$, POPL 2024).** Standard linear type systems implicitly assume continuations execute exactly once. As formalized by Tang, Hillerström, Lindley & Morris (`10.1145/3632896`, `arXiv:2307.09383v2`) and reproduced operationally in `p3_qeff_linearity_and_abi_probe.py`, invoking a non-linear effect while a linear resource (`DmaToken`) is live in the continuation causes double-consumption (use-after-free, `consumes=2`) under multi-shot backtracking handlers and linear resource leaks (`consumes=0`) under abortive exception handlers. $Q^\circ_{\text{eff}}$ closes this soundness hole with zero programmer annotations via qualified types tracking effect-row control-flow linearity (`Lin` vs. `Unr`), rejecting any non-linear operation whenever a linear binding spans the suspension point while permitting abortive/multi-shot effects whenever no linear resource is live across them.
2. **Evidence passing (`Koka`) and lexical capability passing (`Effekt`) compile effect handlers without global dynamic stack search—specializing tail-resumptive clauses to direct calls.** Koka (`koka-lang/koka` `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`, ICFP 2021 `10.1145/3473576`) passes an explicit evidence vector (`evv`) and statically classifies every clause via `Core.AnalysisResume.analyzeResume` into `ResumeTail` (`clause-tail{0..4}` / `clause-tail-noop{0..4}`), `ResumeNever` (`clause-never{0..2}`), `ResumeOnce`/`ResumeScopedOnce`, or `ResumeNormal` (`clause-control{0..4}`). Tail-resumptive operations execute as direct calls with zero continuation capture; non-tail operations bubble through `yield-bind` (`if yielding() then kk_yield_extend(next) else next(x)` in `lib/std/core/hnd.kk` L288–296). Effekt (`effekt-lang/effekt` `6976c7947eac26bc1203bcd48892702ce6d3cf21`, OOPSLA 2020 `10.1145/3428194`, OOPSLA 2022 `10.1145/3527320`) goes further by passing handlers as **second-class lexical capabilities** (`CapabilityScope.scala`: `BindSome`/`BindAll` lexical tunneling preventing accidental dynamic capture as in Zhang & Myers POPL 2019 `10.1145/3290318`), lowering to a continuation machine IR (`effekt/machine/Tree.scala`: `PushFrame`, `Return`, `Reset`, `Shift`, `Resume`).
3. **WebAssembly Stack Switching and the Component Model Async Canonical ABI provide a concrete blueprint for unifying stackful and stackless concurrency across languages—while OpenJDK JEP 491 shows exactly what remains pinned on native stacks.** Core WebAssembly Stack Switching (`WebAssembly/stack-switching` `f0b43efd4952e6520592e4d601f2c271ea6cd659`, `Explainer.md` L178–211, L694–700) enforces **one-shot affine continuations** dynamically: `resume`, `resume_throw`, `resume_throw_ref`, `switch`, and `cont.bind` destructively invalidate the suspended `(ref $ct)` so any second invocation traps. Above it, the Component Model Async Canonical ABI (`WebAssembly/component-model` `585526aa1f2c7f76f07557d16e265dede38b3acb`, `Concurrency.md`) defines a single language-agnostic `async` ABI supporting **both** stackful blocking (`waitable-set.wait`, `stream.read`) and stackless event-loop callbacks (`CALLBACK_CODE` `EXIT`/`YIELD`/`WAIT`), composing sync-calls-async and async-calls-sync via component-level `backpressure` and preserving single-threaded run-to-completion (Component Invariant #2, verified in `p3_qeff_linearity_and_abi_probe.py`). On JVM green stacks, OpenJDK JEP 491 (`openjdk/jdk` `4f33273115381cd7697082fcb1bb2642dae19043`) eliminates `synchronized`-block carrier pinning by changing `ObjectMonitor::_owner` (`objectMonitor.hpp` L150–165) from a carrier `JavaThread*` to a 64-bit virtual-thread `owner_id` (plus sentinels `NO_OWNER=0`, `ANONYMOUS_OWNER=1`, `DEFLATER_MARKER=2`), yet `continuationFreezeThaw.cpp` L935–950 proves that **native/JNI frames without oop maps (`f.oop_map() == nullptr`, `call_stub`/`upcall_stub`) still force `freeze_pinned_native`**.
4. **Callee-saved register error channels (`LLVM swifterror`, Midori) eliminate DWARF `.eh_frame` unwinding tables and hot-path ABI distortion on checked errors, at the cost of one conditional check per throwing callsite.** Inspection of `llvm/llvm-project` (`c078d7b6876e6f21c0162671374939016b174c94`) confirms that LLVM dedicates a **callee-saved register** to `swifterror`—**`R12`** on x86-64 (`X86CallingConv.td` L376, L538, L627; alongside `SwiftSelf=R13`, `SwiftAsync=R14`), **`X21`** on standard AArch64 (`AArch64CallingConvention.td` L75, L135; alongside `SwiftSelf=X20`), and **`X19`** on ARM64EC (`L259, L337`)—promoted to virtual registers via `SwiftErrorValueTracking.cpp` (L9–38). Because the register is callee-saved, calls to ordinary C/non-throwing functions preserve it without spilling, and returning an error requires zero `.eh_frame` lookup or stack-unwinder metadata—matching Midori's separation of fast register-carried typed errors from non-recoverable domain abandonment.

## Applicability

This report examines primary compiler implementations, runtime sources, formal calculi, and ABI specifications across six domains:

- **Control-flow linearity and effect soundness:** Tang et al. (POPL 2024, `10.1145/3632896`, `arXiv:2307.09383v2`), formalizing $F^\circ_{\text{eff}}$ (System F-style) and $Q^\circ_{\text{eff}}$ (ML-style qualified-type inference) and fixing soundness bugs in Links.
- **Evidence-passing and capability-passing effect compilation:** `koka-lang/koka` (`b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`, `src/Core/AnalysisResume.hs`, `src/Core/Monadic.hs`, `src/Core/MonadicLift.hs`, `lib/std/core/hnd.kk`) and Xie & Leijen (ICFP 2021, `10.1145/3473576`); `effekt-lang/effekt` (`6976c7947eac26bc1203bcd48892702ce6d3cf21`, `effekt/typer/CapabilityScope.scala`, `effekt/machine/Tree.scala`, `effekt/machine/Transformer.scala`), Brachthäuser et al. (OOPSLA 2020 `10.1145/3428194`, OOPSLA 2022 `10.1145/3527320`), Zhang & Myers (POPL 2019 `10.1145/3290318`), and Biernacki et al. (POPL 2020 `10.1145/3371116`).
- **Typed continuations and unified async FFI ABIs:** `WebAssembly/stack-switching` (`f0b43efd4952e6520592e4d601f2c271ea6cd659`, `proposals/stack-switching/Explainer.md`) and `WebAssembly/component-model` (`585526aa1f2c7f76f07557d16e265dede38b3acb`, `design/mvp/Concurrency.md` and `design/mvp/CanonicalABI.md` targeting WASI Preview 3). Note that both Wasm proposals are active W3C Community Group specifications whose instruction encodings may evolve prior to final W3C standardization.
- **Virtual-thread unpinning on native stacks:** `openjdk/jdk` (`4f33273115381cd7697082fcb1bb2642dae19043`, `src/hotspot/share/runtime/objectMonitor.hpp`, `objectMonitor.cpp`, `continuationFreezeThaw.cpp`), reflecting post-JEP 491 HotSpot (JDK 24+ mainline).
- **Register-based error ABIs vs. table-driven unwinding:** `llvm/llvm-project` (`c078d7b6876e6f21c0162671374939016b174c94`, `llvm/lib/CodeGen/SwiftErrorValueTracking.cpp`, `X86CallingConv.td`, `AArch64CallingConvention.td`), `swiftlang/swift` (`3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f`, `docs/ABI/CallingConvention.rst`), and Joe Duffy's Midori error model design notes (2016).

The executable probe (`p3_qeff_linearity_and_abi_probe.py`) runs on Python 3 on Linux x86-64 and verifies the linear-resource operational failure modes, the $Q^\circ_{\text{eff}}$ multiplicity check, and the Component Model async backpressure/reentrancy state machine; it does not benchmark native assembly throughput or `.eh_frame` binary sizes across compilers.

## Findings

### 1. Control-Flow Linearity for Linear Resources Under Effect Handlers ($F^\circ_{\text{eff}}$ and $Q^\circ_{\text{eff}}$)

Basis: normative (`10.1145/3632896`, `arXiv:2307.09383v2`) + execution (`p3_qeff_linearity_and_abi_probe.py`) + derived

#### 1.1 The Value-Linearity vs. Delimited-Continuation Soundness Hole

In a linear or affine systems language (e.g., Rust `&mut` / `!Drop` DMA tokens, Links linear session channels, or OxCaml `Unique` values), a linear value `tok : DmaToken` must be consumed **exact count = 1** (or at most once for affine values). Suppose a function acquires `tok`, suspends on an effect operation `do op()`, and consumes `tok` after resumption:

```text
let tok = acquire_dma_token() in
let x   = do op() in          -- captures continuation k = \x. consume(tok, x)
consume(tok, x)
```

In a naive linear + effect type system, the source code syntactically uses `tok` once, so value-linearity checking succeeds. Yet the captured continuation `k` closes over `tok`. Direct execution in `p3_qeff_linearity_and_abi_probe.py` demonstrates three outcomes depending on how the enclosing handler invokes `k`:
1. **One-shot linear handler (`resume` called once):** `tok.consumes == 1` (**sound**).
2. **Multi-shot backtracking handler (`resume` called twice):** `tok.consumes == 2` (**unsound: double-consume / use-after-free**).
3. **Abortive exception handler (`resume` called zero times):** `tok.consumes == 0` (**unsound: linear resource leak**—fatal for `!Drop` DMA tokens, session-type protocol completion, or lock guards).

This exact mismatch produced long-standing soundness bugs in `links-lang/links` when linear session channels interacted with algebraic effect handlers (`arXiv:2307.09383v2`).

#### 1.2 Control-Flow Linearity Typing Discipline ($F^\circ_{\text{eff}}$ / $Q^\circ_{\text{eff}}$)

Tang et al. (POPL 2024) resolve the hole by introducing **control-flow linearity** as the dual of value linearity:

- **Effect-row linearity annotations:** Every effect operation / effect row carries a control-flow linearity qualifier $Y \in \{\text{Lin}, \text{Unr}\}$ (ordered $\text{Lin} \le \text{Unr}$, generalized in $Q^\circ_{\text{eff}}$ via qualified type predicates over linearity variables and effect rows).
  - An operation with qualifier `Lin` guarantees its handler invokes the captured continuation **linearly (exactly once)**—e.g., cooperative async yield without cancellation, reader/state effects, or scoped one-shot resumes.
  - An operation with qualifier `Unr` permits **arbitrary control flow** (zero resumptions as in exceptions/cancellation, or $\ge 2$ resumptions as in nondeterminism/backtracking).
- **The Continuation-Capture Guard Rule:** Whenever a subexpression $e_1$ performs effects $E$ while the evaluation context $E_{\text{ctx}}[\cdot]$ (everything live after $e_1$) closes over **any linear binding** in $\Gamma_{\text{lin}} \neq \emptyset$, the typing rule constrains every effect in $E$ to satisfy **control-flow linearity $E \le \text{Lin}$** (equivalently, the continuation $k$ captured by `do op` inherits the linearity of its free variables, so an `Unr` handler that discards or duplicates $k$ is statically rejected).
- **Refinement for affine systems ownership & async cancellation (`derived`):** Mapping $Q^\circ_{\text{eff}}$ onto Rust-style systems ownership distinguishes two distinct non-linear risks:
  - **Multi-shot duplication** violates **both** affine (`&mut`, `Box<T>`, `Drop`) and strictly linear (`!Drop` `DmaToken`) types; therefore multi-shot handlers must be forbidden whenever *any* affine or linear value spans the suspension point.
  - **Zero-shot abortion (exceptions / async `Cancel`)** is safe for **affine** values with synchronous `Drop` destructors *provided* the runtime unwinds/drops the suspended frame deterministically (turning zero-shot discard into a structured unwind), but remains **unsound** for strictly linear `!Drop` obligations (active hardware DMA descriptors, session-typed channel protocols, unmasked critical sections)—requiring either a `Lin` (`CancelMask` / uncancellable) region around the live linear token or explicit handler-enforced finalization clauses.
- **Full type inference via qualified types ($Q^\circ_{\text{eff}}$):** Rather than requiring manual linearity annotations on every higher-order function (`map`, `bind`), $Q^\circ_{\text{eff}}$ captures both value linearity and control-flow linearity as qualified type constraints (`Lin(a) => ...`), supporting **linearity polymorphism** and **linearity dependencies between type variables** with zero programmer annotations (`arXiv:2307.09383v2`).

---

### 2. Compiling Algebraic Effects: Generalized Evidence Passing (`Koka`) vs. Capability Passing & Tunneling (`Effekt`)

#### 2.1 Koka Generalized Evidence Passing and Resume-Kind Specialization

Basis: source (`koka-lang/koka@b66091b2`, `src/Core/AnalysisResume.hs` L35–65, `lib/std/core/hnd.kk` L288–304, L605–808) + normative (`10.1145/3473576`)

Compiling algebraic effects to standard C without segmented stacks or OS threads requires avoiding dynamic stack walking on effect invocation. Xie & Leijen (ICFP 2021) and `koka-lang/koka@b66091b2` achieve this via **Generalized Evidence Passing**:

1. **Evidence Vector (`evv`) passed as an implicit parameter:** Every effectful function receives an immutable, small, flat vector `evv` mapping each handled effect label to its active handler evidence record `(marker, handler_clause_table, parent_evv)`. Because effect rows are statically known (or polymorphic via evidence offset indices), locating the handler for `do op()` is an **$O(1)$ indexed load** from `evv`—zero dynamic handler-stack search.
2. **Static `ResumeKind` classification (`src/Core/AnalysisResume.hs` L35–65, `lib/std/core/hnd.kk` L605–808):** Koka analyzes each handler clause body via `analyzeResume` into distinct compilation tiers:
   - **`ResumeTail` (`clause-tail{0..4}`, `clause-tail-noop{0..4}`, `clause-value`):** The handler resumes in tail position (e.g., `state.get`, `state.put`, `reader.ask`, `logger.emit`). Koka executes the clause **in-place as a direct C function call** under the handler's parent evidence vector (`evv`), with **zero continuation allocation, zero bubbling, and zero stack unwinding**!
   - **`ResumeNever` (`clause-never{0..2}`):** The handler never invokes `resume` (exceptions / early exit). Bubbles up to the matching prompt marker and discards intermediate frames without building a heap continuation closure.
   - **`ResumeOnce` / `ResumeScopedOnce` (`resumeShallowName`):** Single resumption, avoiding multi-shot environment cloning.
   - **`ResumeNormal` / `ResumeNormalRaw` (`clause-control{0..4}`, `clause-control-raw{0..3}`):** General multi-shot or first-class delimited continuations.
3. **Monadic bubbling fast path (`lib/std/core/hnd.kk` L288–296):** Every effectful call site in monadic C lowering checks a single thread-local yielding flag (`yielding()`):
   ```koka
   pub inline fun yield-bind( x : a, next : a -> e b ) : e b
     if yielding() then yield-extend(next) else next(x)
   ```
   On the common non-yielding path (including all `ResumeTail` calls), `yielding()` is false (highly branch-predicted), executing straight-line native C frames at near-C speed. Only when a non-tail operation actually yields does each unwinding frame register its continuation closure via `kk_yield_extend`, assembling a linked composition of frames up to the target `marker` prompt.

#### 2.2 Effekt Capability Passing, Lexical Tunneling, and Second-Class Blocks

Basis: source (`effekt-lang/effekt@6976c794`, `effekt/typer/CapabilityScope.scala` L15–90, `effekt/machine/Tree.scala` L54–130) + normative (`10.1145/3428194`, `10.1145/3527320`, `10.1145/3290318`, `10.1145/3371116`)

Dynamic effect-name dispatch suffers from **accidental handler capture** when higher-order functions (e.g., `map` invoking a user callback) install internal handlers of the same effect type. Zhang & Myers (*Abstraction-Safe Effect Handlers via Tunneling*, POPL 2019, `10.1145/3290318`) and Biernacki et al. (*Binders by Day, Labels by Night*, POPL 2020, `10.1145/3371116`) establish that **lexically scoped effect instances/capabilities** preserve parametricity and abstraction safety by binding each effect operation directly to a statically resolved handler instance ("tunneling" transparently past intermediate handlers of the same type).

Effekt (`effekt-lang/effekt@6976c794`) operationalizes this via **Effects as Capabilities** (OOPSLA 2020) and **System C Boxes** (OOPSLA 2022):
- **Lexical `CapabilityScope` (`CapabilityScope.scala` L17–90):** During type checking, handlers bind named capability block parameters inside lexical scopes (`BindSome`, `BindAll`, terminating at `GlobalCapabilityScope`, which aborts on unhandled effects). Functions declare required capabilities implicitly as **second-class block parameters**—which cannot escape their defining handler scope—yielding **lightweight effect polymorphism** without explicit effect-row variables on higher-order combinators (`map` simply forwards any capabilities captured in its second-class block argument).
- **First-class escape via `Box` (OOPSLA 2022):** When a function *must* be stored in a heap data structure or returned from a scope, it is explicitly wrapped in a **boxed** value whose type records its captured capability set (`Captures`), enforcing that it cannot outlive the handlers of those capabilities (`requireSubregion` in `CapabilityScope.scala` L43).
- **Continuation machine lowering (`effekt/machine/Tree.scala` L77–130):** Effekt lowers capability-passing core IR to a compact abstract machine whose statements explicitly separate ordinary stack frames (`PushFrame`, `Return`, `Jump`), object/capability dispatch (`New`, `Invoke`), mutable regions (`Var`, `LoadVar`, `StoreVar`), foreign boundaries (`ForeignCall`, `ForeignJump`), and multi-prompt delimited control (`Reset`, `Shift`, `Resume`)—targeting LLVM native stacks, Chez Scheme, or JS CPS cleanly.

---

### 3. Unifying Stackless and Stackful Concurrency Across Languages (`Wasm`, `WASI Preview 3`, and `OpenJDK JEP 491`)

#### 3.1 Core WebAssembly Stack Switching: One-Shot Affine Typed Continuations

Basis: source (`WebAssembly/stack-switching@f0b43efd`, `proposals/stack-switching/Explainer.md` L1–10, L178–211, L484–496, L694–700)

Core WebAssembly Stack Switching adds first-class typed continuations `(ref $ct)` to Wasm without exposing raw linear-memory stack pointers or C ABI frames:
- **Instruction set (`Explainer.md` L178–211, L484–496):**
  - `cont.new $ct`: allocates a fresh suspended continuation from a typed function reference; execution begins only on first resumption.
  - `cont.bind`: partially applies arguments to a suspended continuation.
  - `resume $ct (on $tag $label)`: resumes continuation `$c`, branching to `$label` with payload + remaining continuation `(ref $ct)` if `$c` suspends on tag `$tag`.
  - `suspend $tag`: suspends up to the nearest enclosing `resume` handler matching `$tag`.
  - `resume_throw` / `resume_throw_ref`: injects a Wasm exception directly into a suspended continuation to perform structured **cancellation/unwinding** without resuming normal execution.
  - `switch`: symmetric transfer directly between two continuations without bouncing through a central scheduler frame.
- **One-shot affine invariant (`Explainer.md` L696–700):** *"In order to ensure that continuations are one-shot, `resume`, `resume_throw`, `resume_throw_ref`, `switch`, and `cont.bind` destructively modify the suspended continuation such that any subsequent use of the same suspended continuation will result in a trap."* Because continuations are strictly one-shot, runtimes implement them as **zero-copy mutable OS/fiber stack segments** (never needing stack copying for multi-shot cloning), while preventing double-resumption UB dynamically.

#### 3.2 Component Model Async Canonical ABI (WASI Preview 3): Unifying Stackful and Stackless Guests

Basis: source (`WebAssembly/component-model@585526aa`, `design/mvp/Concurrency.md` L22–92, L176–187, L489–563) + execution (`p3_qeff_linearity_and_abi_probe.py`)

A major obstacle in polyglot async FFI is the **"function coloring" split** between stackless state-machine languages (Rust `async fn` / `Future`, JS `Promise`, C# `Task`) and stackful fiber/sync languages (Go goroutines, Java virtual threads, C/POSIX blocking I/O). The WebAssembly Component Model Async Canonical ABI (`Concurrency.md`) dissolves this split at the binary interface:

1. **Single WIT interface, dual Core Wasm lowerings (`Concurrency.md` L22–92, L489–502):**
   - A WIT `async func` can be lifted/lowered by a **stackful guest** (or traditional synchronous C code calling `read()`/`write()`) using blocking Canonical ABI built-ins (`waitable-set.wait`, `stream.read`, `future.read`, `subtask.cancel`), which suspend the guest thread via the `$block` effect (implemented atop Wasm Stack Switching or polyfilled in browsers via JSPI).
   - The **exact same** WIT `async func` can be lifted/lowered by a **stackless guest** (Rust/JS) using the **`callback` ABI**: the export function runs one non-blocking turn and returns an integer callback code (`EXIT = 0`, `YIELD = 1`, `WAIT = 2` + `waitable-set` handle) to the host event loop, which later invokes a registered `callback(event)` function when the waitable completes—requiring **zero per-task native stacks**!
   - Both `sync-ABI-calls-async-ABI` and `async-ABI-calls-sync-ABI` compose transparently across component boundaries.
2. **Uniform heterogeneous waitables (`Concurrency.md` L550–563):** Subtasks, `stream<T>` ends, and `future<T>` ends are all **waitables** managed uniformly via `waitable-set.new`, `waitable.join`, `waitable-set.wait`, and `waitable-set.poll`—giving polyglot runtimes an epoll/kqueue-like readiness multiplexer directly in the ABI.
3. **Backpressure and Run-to-Completion (`Concurrency.md` L35–36, L178–187; verified in `p3_qeff_linearity_and_abi_probe.py` Part B):** Components expose explicit `backpressure` gating so an overloaded component stalls new incoming async calls in `STARTING` state before entering guest memory, and `may_enter` enforces Component Invariant #2 (single-threaded run-to-completion between yield/wait boundaries so non-thread-safe linear memory is never re-entered mid-mutation).

#### 3.3 OpenJDK JEP 491: Virtual-Thread Unpinning and the Residual Native-Frame Pinning Boundary

Basis: source (`openjdk/jdk@4f332731`, `src/hotspot/share/runtime/objectMonitor.hpp` L149–165, `src/hotspot/share/runtime/continuationFreezeThaw.cpp` L935–950, L1376–1389)

Prior to JDK 24 (JEP 491), entering a Java `synchronized` block pinned a virtual thread to its OS carrier thread because HotSpot's `ObjectMonitor` recorded ownership as the OS carrier's `JavaThread*` pointer. Inspection of `openjdk/jdk@4f332731` shows exactly how JEP 491 removed monitor pinning—and where pinning **still** remains unavoidable on shared native stacks:

1. **Virtual-thread-ID monitor ownership (`objectMonitor.hpp` L150–165):**
   ```cpp
   static const int64_t NO_OWNER = 0;
   static const int64_t ANONYMOUS_OWNER = 1;
   static const int64_t DEFLATER_MARKER = 2;
   int64_t volatile _owner; // Either owner_id of owner, NO_OWNER, ANONYMOUS_OWNER or DEFLATER_MARKER.
   volatile uint64_t _previous_owner_tid;
   DEFINE_PAD_MINUS_SIZE(0, OM_CACHE_LINE_SIZE, sizeof(int64_t volatile) + sizeof(volatile uint64_t));
   ```
   By decoupling `_owner` from the OS carrier `JavaThread*` and keying it by the virtual thread's logical `owner_id`, a virtual thread can safely unmount from its carrier while holding an inflated `ObjectMonitor` (or waiting in `Object.wait()` / monitor entry) and later remount on a completely different OS carrier thread without breaking monitor reentrancy or release checks.
2. **Residual native-frame pinning (`continuationFreezeThaw.cpp` L935–950, L1376–1389):** When freezing a virtual-thread stack chunk onto the heap, `FreezeBase` checks every frame on the carrier stack:
   - If `f.oop_map() == nullptr` (special native frame, L935–938), or if the frame is a `call_stub`/`upcall_stub` indicating native C/JNI frames further up the stack (L947–950), freezing aborts with **`freeze_pinned_native`**, pinning the virtual thread to its carrier OS thread.
   - Only a native/runtime frame sitting at the very top during preemption (`top && _preempt`, L943–946) can be frozen via `recurse_freeze_native_frame`, and even then frames requiring oop-fixup across native conventions fall back to `freeze_pinned_native` (L1376–1379).
3. **Implication for leaf native FFI on green stacks (`derived`):** Eliminating stack-switch trampolines (like Go's `cgo` `g0` switch or JVM JNI pinning) by running leaf native functions directly on small green stacks requires **two strict conditions** beyond JEP 491: (a) a statically verified worst-case stack-frame bound `LeafBound(K)` smaller than the remaining green-stack headroom (obtainable via compiler `-Z emit-stack-sizes` / call-graph static analysis for non-recursive leaf graphs with no `alloca`/VLAs), AND (b) guaranteeing that **no asynchronous trap, lazy dynamic-linker PLT resolver, or hardware shadow-stack (Intel CET) push** can silently execute on that green stack (requiring eager `-Wl,-z,now` binding and hardware-routed alternate signal/trap stacks `sigaltstack` / IST).

---

### 4. Register Error Channels (`swifterror` & Midori) vs. Table-Driven Unwinding (DWARF `.eh_frame`)

Basis: source (`llvm/llvm-project@c078d7b6`, `SwiftErrorValueTracking.cpp` L9–38, `X86CallingConv.td` L376, L413, L537–542, L626–631, `AArch64CallingConvention.td` L72–76, L134–136, L258–261, L337; `swiftlang/swift@3be0cf4b`, `docs/ABI/CallingConvention.rst` L620–635) + documentation (Midori Error Model) + derived

#### 4.1 Exact LLVM `swifterror` Lowering and Target Register Assignments

LLVM implements Swift's zero-unwinding typed error propagation by tagging an error pointer parameter or `alloca` with the `swifterror` IR attribute and lowering it through `SwiftErrorValueTracking` (`llvm/lib/CodeGen/SwiftErrorValueTracking.cpp` L9–38):
- **Limited `mem2reg` promotion to virtual registers:** Rather than keeping the error slot on the stack, `SwiftErrorValueTracking` promotes `swifterror` uses inside each `MachineBasicBlock` into per-block virtual registers (`VRegDefMap` / `VRegUpwardsUse`), inserting copies/PHIs only at block joins.
- **Exact callee-saved register bindings verified from LLVM TableGen targets:**

| Target Architecture / ABI | `SwiftError` Register | Companion Special Registers | Why Callee-Saved Matters |
| :--- | :--- | :--- | :--- |
| **x86-64** (`X86CallingConv.td` L376, L538, L627) | **`R12`** | `SwiftSelf = R13`, `SwiftAsync = R14` | Unmodified C/non-throwing callees automatically preserve `R12` across calls with **zero caller spill/reload** |
| **AArch64 AAPCS** (`AArch64CallingConvention.td` L75, L135) | **`X21`** | `SwiftSelf = X20` | Preserved across standard AAPCS C calls; zero conflict with `X0..X7` normal return registers |
| **ARM64EC** (`AArch64CallingConvention.td` L259, L337) | **`X19`** | `SwiftSelf = X20` | Matches x86-64 `R12` emulation mapping cleanly |

On the happy path, the caller initializes `R12`/`X21 = 0` once per scope; the callee leaves `R12`/`X21` untouched if no error occurs (zero extra write on return!), and the caller checks `test %r12, %r12; jnz error_path` (a single 1-cycle macro-fused test+branch predicted not-taken, leaving `RAX`/`RDX` or `X0`/`X1` completely unencumbered for normal multi-register return values).

#### 4.2 Midori Error Model vs. DWARF `.eh_frame` Unwinding Trade-Off Matrix

Joe Duffy's Midori OS engineering retrospective (*The Error Model*, 2016) draws a sharp bifurcation that directly reinforces `swifterror` and Wasm multi-value error returns:
- **Recoverable errors (typed checked exceptions / `Result`):** Lowered to explicit return-value / register error channels (avoiding `.eh_frame` tables entirely). Deterministic, predictable latency even under high error rates (e.g., network/parser errors), no hidden unwind-table `.eh_frame` / LSDA binary bloat, and no opaque `invoke` landing-pad edges blocking LLVM register allocation or loop vectorization.
- **Unrecoverable bugs (contract violations, out-of-bounds, invariant corruption):** Never caught by local `try/catch` (which risks executing destructors over corrupt state); instead triggers immediate **fail-fast domain/process abandonment**, reclaiming all domain memory in bulk without running corrupt cleanups.

| Error Mechanism | Happy-Path Cost | Error-Path Cost | Binary Metadata Overhead | Optimizer Impact | Mixed-Language FFI & Linear-Resource Safety |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **LLVM `swifterror` (`R12`/`X21`)** | 1 predicted `test+jnz` per throwing callsite; normal return regs untouched | **O(1) register store + normal `ret`** (nanoseconds) | **Zero** `.eh_frame` / LSDA needed for throws | Local explicit CFG branch; full inlining & DCE | Preserved across standard C callees; explicit linear cleanup edges in CFG |
| **Struct / Wasm Multi-Value `Result<T, E>`** | Tag test per call; may spill large `T` to stack (`sret`) if `sizeof(T+E)` exceeds reg ABI | **O(1) normal `ret`** | **Zero** unwind metadata | Full SSA optimization | Universally portable across C / Wasm / Rust without custom register reservation |
| **Itanium DWARF `.eh_frame` Unwinding** | Zero instructions on happy path (table-driven PC lookup) | **Microseconds** (table binary search, DWARF CFA bytecode eval, global lock/dl_iterate_phdr) | Substantial (`.eh_frame` + `.gcc_except_table` LSDA per function) | Every `invoke` breaks basic blocks, inhibits code motion & register pinning | **Hazardous across FFI** (unwinding across `extern "C"` is UB; personality-routine mismatch across runtimes) |
| **Midori Fail-Fast Abandonment** | Zero (only bug-check traps) | Bulk domain teardown (no stack unwinding) | Zero for local recovery | Minimal | Eliminates corrupt destructor execution; requires external reclamation for hardware DMA |

## Boundaries

- **Not examined:** Empirical wall-clock throughput, I-cache footprint, and binary-size measurements comparing `swifterror`, Rust `Result` multi-value returns, and Itanium DWARF `.eh_frame` across concrete polyglot benchmarks were not executed; the comparison table derives from verified LLVM lowering mechanics and published design analyses.
- **Not examined:** Hardware Intel CET shadow-stack (`SHSTK`) frame accounting interactions with green-stack switching (`Go` / `OCaml 5` / `JVM Loom`) and Rust `-Z emit-stack-sizes` / CompCert static stack-bound verification toolchains were not directly run on binaries in this study.
- **Not examined:** The exact `links-lang/links` compiler patch committing $F^\circ_{\text{eff}}$ control-flow linearity (beyond confirming the `links-lang/links` revision and `arXiv:2307.09383v2` report of the bug fix) was not diffed line-by-line.
- **Unknown:** Final standardized binary opcodes and browser-engine adoption timelines for both `WebAssembly/stack-switching` and the Component Model Async Canonical ABI (WASI Preview 3) remain subject to W3C CG standardization changes past the pinned revisions.
- **Known not to apply:** OpenJDK JEP 491 (`openjdk/jdk@4f332731`) does **not** eliminate carrier-thread pinning when native JNI frames or frames lacking oop maps (`f.oop_map() == nullptr`) sit on the call stack (`continuationFreezeThaw.cpp` L935–950 still returns `freeze_pinned_native`).
- **Known not to apply:** `swiftlang/swift` `docs/ABI/CallingConvention.rst` (`3be0cf4b`, L620–635) is an older design document stating error calling conventions *"aren't yet settled"* and does **not** reflect the authoritative production register bindings (`R12`/`X21`/`X19`), which live normatively in LLVM's target TableGen files (`X86CallingConv.td`, `AArch64CallingConvention.td`).
- **Unsupported:** Core WebAssembly Stack Switching (`WebAssembly/stack-switching@f0b43efd`) explicitly does **not** support multi-shot continuations (`Explainer.md` L696–700 specifies destructive invalidation and trapping on second resumption); languages requiring multi-shot backtracking on Wasm must compile via CPS/evidence-passing (`Koka`/`Effekt`-style) or heap-copied state machines rather than raw `cont` references.
- **Stronger conclusion avoided:** While $Q^\circ_{\text{eff}}$ control-flow linearity prevents linear resource duplication/leaks under arbitrary effect handlers, proving end-to-end memory safety for a native FFI async runtime also requires preventing native/C frames from capturing raw stack pointers across suspension points—which static effect linearity alone does not check inside opaque C code.

## Evidence

### Primary Git Source References (Observed 2026-11-19)

1. **`koka-lang/koka` @ `b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`**
   - `src/Core/AnalysisResume.hs` L35–65: `analyzeResume` classifying handler clauses into `ResumeTail`, `ResumeScopedOnce`, `ResumeOnce`, `ResumeNever`, `ResumeNormal`, `ResumeNormalRaw`.
   - `lib/std/core/hnd.kk` L288–304, L605–808: `yield-extend` (`kk_yield_extend`), `yield-bind` (`if yielding() then yield-extend(next) else next(x)`), `clause-tail{0..4}`, `clause-tail-noop{0..4}`, `clause-never{0..2}`, `clause-control{0..4}`, `clause-control-raw{0..3}`.
2. **`effekt-lang/effekt` @ `6976c7947eac26bc1203bcd48892702ce6d3cf21`**
   - `effekt/shared/src/main/scala/effekt/typer/CapabilityScope.scala` L15–90: `GlobalCapabilityScope`, `BindSome`, `BindAll`, lexical `capabilityFor`, `requireSubregion`.
   - `effekt/shared/src/main/scala/effekt/machine/Tree.scala` L54–130: `Clause`, `Statement` enum (`Jump`, `Construct`, `Switch`, `New`, `Invoke`, `Var`, `LoadVar`, `StoreVar`, `PushFrame`, `Return`, `Reset`, `Resume`, `Shift`, `ForeignCall`, `ForeignJump`).
3. **`WebAssembly/stack-switching` @ `f0b43efd4952e6520592e4d601f2c271ea6cd659`**
   - `proposals/stack-switching/Explainer.md` L1–10, L178–211, L484–496, L694–700: `cont.new`, `cont.bind`, `resume`, `resume_throw`, `resume_throw_ref`, `suspend`, `switch`, and destructive one-shot continuation trap rule.
4. **`WebAssembly/component-model` @ `585526aa1f2c7f76f07557d16e265dede38b3acb`**
   - `design/mvp/Concurrency.md` L22–92, L176–187, L489–563: Stackful vs. stackless `callback` ABI (`EXIT`/`YIELD`/`WAIT`), sync/async interop, `backpressure`, Component Invariant #2 run-to-completion, `waitable-set.{new,wait,poll}`, `waitable.join`, `subtask.cancel`, `stream`/`future` waitables, JSPI polyfill.
   - `design/mvp/CanonicalABI.md`: Formal Canonical ABI lowering rules.
5. **`openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043`**
   - `src/hotspot/share/runtime/objectMonitor.hpp` L149–165: `int64_t volatile _owner` (`NO_OWNER=0`, `ANONYMOUS_OWNER=1`, `DEFLATER_MARKER=2`), `_previous_owner_tid`, `OM_CACHE_LINE_SIZE` padding.
   - `src/hotspot/share/runtime/continuationFreezeThaw.cpp` L935–950, L1376–1389: `freeze_pinned_native` on `f.oop_map() == nullptr`, `call_stub`/`upcall_stub`, and non-preemptable native frames.
6. **`llvm/llvm-project` @ `c078d7b6876e6f21c0162671374939016b174c94`**
   - `llvm/lib/CodeGen/SwiftErrorValueTracking.cpp` L9–38: `SwiftErrorValueTracking::getOrCreateVReg` promoting `swifterror` args/allocas to per-MBB virtual registers.
   - `llvm/lib/Target/X86/X86CallingConv.td` L376, L413, L537–542, L626–631: `CCIfSwiftError -> R12`, `CCIfSwiftSelf -> R13`, `CCIfSwiftAsync -> R14`.
   - `llvm/lib/Target/AArch64/AArch64CallingConvention.td` L72–76, L134–136, L258–261, L337: `CCIfSwiftError -> X21` (AAPCS) and `X19` (ARM64EC), `CCIfSwiftSelf -> X20`.
7. **`swiftlang/swift` @ `3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f`**
   - `docs/ABI/CallingConvention.rst` L620–635: Historical Swift calling-convention rationale on register error checks vs. indirect result contortion.

### Published Literature & Specifications

- Wenhao Tang, Daniel Hillerström, Sam Lindley, J. Garrett Morris. *Soundly Handling Linearity*. PACMPL 8 (POPL 2024). DOI: `10.1145/3632896`, `arXiv:2307.09383v2` (2024-01-02).
- Ningning Xie, Daan Leijen. *Generalized Evidence Passing for Effect Handlers: Efficient Compilation of Effect Handlers to C*. PACMPL 5 (ICFP 2021). DOI: `10.1145/3473576`.
- Jonathan Immanuel Brachthäuser, Philipp Schuster, Klaus Ostermann. *Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism*. PACMPL 4 (OOPSLA 2020). DOI: `10.1145/3428194`.
- Jonathan Immanuel Brachthäuser, Philipp Schuster, Edward Lee, Aleksander Boruch-Gruszecki. *Effects, Capabilities, and Boxes: From Scope-Based Reasoning to Type-Based Reasoning and Back*. PACMPL 6 (OOPSLA 2022). DOI: `10.1145/3527320`.
- Yizhou Zhang, Andrew C. Myers. *Abstraction-Safe Effect Handlers via Tunneling*. PACMPL 3 (POPL 2019). DOI: `10.1145/3290318`.
- Dariusz Biernacki, Maciej Piróg, Piotr Polesiuk, Filip Sieczkowski. *Binders by Day, Labels by Night: Effect Instances via Lexically Scoped Handlers*. PACMPL 4 (POPL 2020). DOI: `10.1145/3371116`.
- OpenJDK *JEP 491: Synchronize Virtual Threads without Pinning* (JDK 24).
- Joe Duffy. *The Error Model* (Midori engineering blog series, 2016).

### Executable Probe and Recorded Output (`Basis: execution`, 2026-11-19)

Command: `python3 /tmp/p3_qeff_linearity_and_abi_probe.py` (Python 3, Linux x86-64). Standalone probe source:

```python
from dataclasses import dataclass

@dataclass
class DmaToken:
    token_id: int
    consumes: int = 0

def run_with_handler(handler_kind: str):
    tok = DmaToken(token_id=42)
    def body_after_suspend(val: int):
        tok.consumes += 1
        return val + tok.token_id
    if handler_kind == "one_shot_linear": res = [body_after_suspend(10)]
    elif handler_kind == "multi_shot_backtrack": res = [body_after_suspend(10), body_after_suspend(20)]
    elif handler_kind == "abortive_exception": res = []
    status = "SOUND (exact=1)" if tok.consumes == 1 else (
        "UNSOUND: DOUBLE-CONSUME / UAF" if tok.consumes > 1 else "UNSOUND: LINEAR RESOURCE LEAK")
    return tok.consumes, status, res

def qeff_typecheck(linear_live_across_op: bool, handler_resumes: str) -> bool:
    op_mult = "Lin" if handler_resumes == "exact_1" else "Unr"
    return not (linear_live_across_op and op_mult != "Lin")

for kind, resumes in [("one_shot_linear", "exact_1"), ("multi_shot_backtrack", "many_multishot"), ("abortive_exception", "zero_abort")]:
    cnt, status, _ = run_with_handler(kind)
    print(f"  {kind:22s}: consumes={cnt} ({status:30s}) | Q_eff(lin_live=True) admits={qeff_typecheck(True, resumes)}")
print(f"  {'abortive_no_live_lin':22s}: Q_eff(lin_live=False) admits={qeff_typecheck(False, 'zero_abort')} (safe when no linear var spans op)")

EXIT, YIELD, WAIT = 0, 1, 2
class ComponentInstance:
    def __init__(self):
        self.may_enter, self.backpressure, self.active_tasks = True, False, 0
    def enter_async_export(self, task_id: str):
        if self.backpressure or not self.may_enter: return ("QUEUED_BACKPRESSURE", "STARTING")
        self.may_enter = False; self.active_tasks += 1; return ("RUNNING", "STARTED")
    def callback_step(self, code: int):
        assert not self.may_enter
        self.may_enter = True
        if code == EXIT: self.active_tasks -= 1; return "RETURNED"
        return "STARTED"

inst = ComponentInstance()
st1 = inst.enter_async_export("t1")
inst.backpressure = True
st2_blocked = inst.enter_async_export("t2")
cb1 = inst.callback_step(WAIT)
st2_still_bp = inst.enter_async_export("t2")
inst.backpressure = False
st2_admitted = inst.enter_async_export("t2")
cb2 = inst.callback_step(EXIT)
assert inst.may_enter; inst.may_enter = False
cb1_done = inst.callback_step(EXIT)
print(f"  t1 enter={st1}, t2(bp+busy)={st2_blocked}, t1 WAIT->{cb1}, t2(bp)={st2_still_bp}, t2(bp_off)={st2_admitted}, t2 EXIT->{cb2}, t1 EXIT->{cb1_done}, active_tasks={inst.active_tasks}")
```

Observed stdout:

```text
  one_shot_linear       : consumes=1 (SOUND (exact=1)               ) | Q_eff(lin_live=True) admits=True
  multi_shot_backtrack  : consumes=2 (UNSOUND: DOUBLE-CONSUME / UAF ) | Q_eff(lin_live=True) admits=False
  abortive_exception    : consumes=0 (UNSOUND: LINEAR RESOURCE LEAK ) | Q_eff(lin_live=True) admits=False
  abortive_no_live_lin  : Q_eff(lin_live=False) admits=True (safe when no linear var spans op)
  t1 enter=('RUNNING', 'STARTED'), t2(bp+busy)=('QUEUED_BACKPRESSURE', 'STARTING'), t1 WAIT->STARTED, t2(bp)=('QUEUED_BACKPRESSURE', 'STARTING'), t2(bp_off)=('RUNNING', 'STARTED'), t2 EXIT->RETURNED, t1 EXIT->RETURNED, active_tasks=0
```

## Revalidation

1. **Koka evidence passing and Effekt capability lowering:** Diff `src/Core/AnalysisResume.hs` and `lib/std/core/hnd.kk` (`yield-bind`, `clause-tail*`) against `koka-lang/koka@b66091b2a5a7ea20c5ed9498ad1e1f03caee9589`, and `effekt/typer/CapabilityScope.scala` / `effekt/machine/Tree.scala` against `effekt-lang/effekt@6976c7947eac26bc1203bcd48892702ce6d3cf21`.
2. **WebAssembly Stack Switching and Component Model Async ABI:** Diff `proposals/stack-switching/Explainer.md` (specifically checking whether one-shot trapping semantics or `resume_throw` change) against `f0b43efd4952e6520592e4d601f2c271ea6cd659`, and `design/mvp/Concurrency.md` (`callback` codes, `waitable-set`, `backpressure`) against `585526aa1f2c7f76f07557d16e265dede38b3acb`.
3. **OpenJDK JEP 491 monitor ownership and native pinning:** Diff `src/hotspot/share/runtime/objectMonitor.hpp` (`_owner`) and `src/hotspot/share/runtime/continuationFreezeThaw.cpp` (`freeze_pinned_native`) against `openjdk/jdk@4f33273115381cd7697082fcb1bb2642dae19043`.
4. **LLVM `swifterror` ABI bindings:** Diff `llvm/lib/Target/X86/X86CallingConv.td`, `llvm/lib/Target/AArch64/AArch64CallingConvention.td`, and `llvm/lib/CodeGen/SwiftErrorValueTracking.cpp` against `llvm/llvm-project@c078d7b6876e6f21c0162671374939016b174c94`.
5. **Control-flow linearity and ABI state-machine probe:** Re-run the embedded Python probe whenever modifying linear-effect typing rules or Component Model callback transitions to verify exact resource-consumption counts and reentrancy exclusion.
