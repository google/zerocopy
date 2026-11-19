# CRuby YARV/YJIT Dynamic Semantics, Conservative C-Extension GC, ECMA-262 Proxies and Memory Model, V8 Speculative Deoptimization, and TypeScript Structural Unsoundness

## Summary

Modern dynamic-language virtual machines (CRuby/YJIT and V8) achieve near-native throughput only by speculating aggressively against highly reflective, open-world language semantics—then guaranteeing observational equivalence via runtime invariant tracking, code patching, and frame-reconstructing deoptimization:

1. **CRuby YARV, YJIT Lazy Basic Block Versioning (LBBV), and open-world invalidation**: YJIT compiles specialized basic-block versions indexed by a compact 4-bit `Type` lattice (16 variants in `yjit/src/core.rs`) capped by `max_versions`, emitting direct machine code guarded by seven global invariant tables (`yjit/src/invariants.rs`): callable method entry (`cme_validity`) stability against open-class monkey-patching, basic operator redefinition (`BOP`), constant path mutations, singleton-class creation on core containers (`Array`/`Hash`/`String`), environment-pointer non-escape (`no_ep_escape_iseqs`, invalidated when `Binding`/`Proc`/`eval` promotes stack locals to heap frames), single-Ractor execution, and global `TracePoint` invalidation (`rb_yjit_tracing_invalidate_all`). Lexical `Refinements` (`refine`/`using`) scope method overrides statically to lexical call sites—including `send` inside the lexical scope and self-invocation inside the `refine` block—without propagating dynamically to unrefined callees, forbidding refinement call caches from sharing unrefined YARV call-cache entries.
2. **CRuby conservative C-extension GC and compaction pinning hazards**: Because CRuby C extensions hold raw `VALUE` handles in C local variables and registers without a shadow root stack, `rb_gc_mark_locations` / `rb_gc_impl_mark_maybe` conservatively scans C machine stacks (and `Fiber` stacks) and **pins** every heap-pointing word (`gc_mark_and_pin`). Optimizing C compilers routinely drop a dead `VALUE` from stack/registers before the final dereference of an interior C pointer (`RSTRING_PTR(s)`), causing premature collection unless `RB_GC_GUARD(v)` (a `volatile` pointer + empty inline asm memory barrier) is placed *after* the last interior dereference. `RTypedData` extensions face additional soundness hazards across `RUBY_TYPED_FREE_IMMEDIATELY` (GVL unlock during sweep), `RUBY_TYPED_EMBEDDABLE` (interior pointers invalidated by `GC.compact`), `RUBY_TYPED_WB_PROTECTED` (missed generational write barriers), and `rb_gc_mark` vs. `rb_gc_mark_movable` + `rb_gc_location`.
3. **ECMA-262 `Proxy`/`Reflect` invariants and `SharedArrayBuffer` tearing**: ECMA-262 enforces hard non-configurable / non-extensible target invariants on every Proxy trap (`[[Get]]`, `[[Set]]`, `[[Delete]]`, `[[OwnPropertyKeys]]`, `[[GetPrototypeOf]]`), throwing `TypeError` whenever a handler lies about frozen/sealed target semantics. Concurrently, the ECMAScript relaxed memory model guarantees sequential consistency for data-race-free programs (DRF-SC) and tear-free reads *only* for aligned integer `TypedArray` accesses over **equal** byte ranges (`sec-tear-free-aligned-reads`). Mixed-width overlapping races on a `SharedArrayBuffer` (e.g., 64-bit `BigUint64Array` reads against paired 32-bit `Uint32Array` writes) are explicitly permitted to tear and deterministically produce torn values (`0x2222222211111111`) even on x86-64 TSO.
4. **V8 hidden classes (`Map`), `DependentCode`, and Maglev/TurboFan deoptimization**: V8 compiles dynamic property layouts into `Map` transition trees and monotonic `ElementsKind` lattices, tracking speculative assumptions via a 10-group `DependentCode` bitset and global `Protectors` (`NoElementsProtector`, `ArraySpeciesProtector`, `ArrayBufferDetachingProtector`). Speculation failures trigger either **eager deoptimization** (inline guard bailout, observed live in both `<Code MAGLEV>` and `<Code TURBOFAN_JS>`) or **lazy deoptimization** (marking live on-stack optimized code for bailout upon callee return when a dependency such as `kFieldConstGroup` or `kPrototypeCheckGroup` breaks), using `TranslatedState` / `TranslatedValue` to un-inline frames and materialize escape-analyzed objects (`kCapturedObject` / `kDuplicatedObject`) back into Ignition bytecode frames.
5. **TypeScript intentional structural unsoundness**: Direct inspection of Microsoft's TypeScript `7.1.0-dev` native Go typechecker (`tsc/internal/checker/relater.go`) confirms that TypeScript deliberately sacrifices soundness for JavaScript compatibility and zero-overhead type erasure: method declarations, method signatures, and constructors remain **bivariant** even with `strictFunctionTypes` enabled (`relater.go:1538`); writable object properties and arrays are checked **covariantly** (`relater.go:4361-4404`); `readonly` does not affect assignability (`relater.go:4365-4369`); `any` acts simultaneously as top and bottom (`relater.go:212, 265`); and excess-property checks vanish once an object literal is aliased through a variable.

## Applicability

This report synthesizes four pinned upstream specifications/implementations alongside live execution probes on two local runtimes:

- **CRuby implementation (`source`)**: Inspected at `ruby/ruby` commit `2e6b197f6849401b2c25894b5b8ac39ac3c2558e` (`RUBY_API_VERSION = 4.1.0`), covering YJIT (`yjit/src/{core,invariants,codegen,stats}.rs`), YARV method dispatch (`vm_insnhelper.c`, `vm_method.c`, `class.c`), `Binding`/`Fiber` (`proc.c`, `cont.c`), and the modular default GC and C-extension headers (`gc.c`, `gc/default/default.c`, `include/ruby/internal/{memory,gc,core/rtypeddata}.h`).
- **CRuby execution (`execution`)**: Executed on `ruby 3.3.8 (2025-04-09 revision b200bad6cd) [x86_64-linux-gnu]`. Because this local binary was built *without* YJIT (`ruby --yjit` warns that Ruby was built without YJIT support), execution observations verify YARV disassembly, lexical `Refinements` vs. `send`, `method_missing` / `respond_to_missing?`, `Binding` live local mutation, and `Fiber` coroutines; YJIT LBBV codegen and invalidation mechanics are grounded in `source` inspection of `ruby/ruby@2e6b197f...` and Chevalier-Boisvert et al. (ECOOP 2015, MPLR 2023).
- **ECMA-262 specification (`normative`)**: Inspected at `tc39/ecma262` commit `b1eaed82fc5e8a511c5b2007f194b16c8f7e5ea6` (`spec.html`), covering Proxy internal methods (`sec-proxy-object-internal-methods-and-internal-slots`) and the shared memory model (`sec-memory-model`).
- **V8 engine (`source` + `execution`)**: Source architecture inspected at `v8/v8` commit `e88118f63dd96f24a9acb8bd0665e7880063f5c0` (`V8 16.0.0` candidate: `src/objects/{map,transitions,dependent-code,elements-kind}.h`, `src/deoptimizer/{deoptimizer,deoptimize-reason,translated-state}.h`, `src/compiler/compilation-dependencies.h`, `src/execution/protectors.h`). Live execution probes ran on `Node.js v24.21.0` embedding `V8 13.6.233.17-node.53` on Linux x86_64 with `--allow-natives-syntax --trace-deopt` and `node:worker_threads`. Exact internal flags and deopt log formatting can shift between V8 13.6 and V8 16.0; the architectural `Map`/`DependentCode`/`TranslatedState` model is shared across both.
- **TypeScript typechecker (`source`)**: Inspected at `microsoft/TypeScript` commit `9c4ad5cbc5a24f3e8893c6e395ac8981c1154c16` (`version = "7.1.0-dev"`, native Go compiler port at `tsc/internal/checker/relater.go` and `checker.go`), cross-checked against Bierman, Abadi, and Torgersen (ECOOP 2014) and Rastogi et al. (POPL 2015). Because `tsc` is not installed locally, TypeScript findings rely strictly on `source` and `documentation`, not local `tsc` execution.

## Findings

### 1. CRuby YARV, YJIT Lazy Basic Block Versioning, Open-World Semantics, and Conservative GC

#### 1.1 YARV Dispatch, Open Classes, Lexical `Refinements`, `method_missing`, `Binding`, and `Fiber`

Basis: source (`ruby/ruby@2e6b197f...`) + execution (`ruby 3.3.8`)

CRuby compiles Ruby source to stack-based YARV instruction sequences (`rb_iseq_t`) that embed inline call-site descriptors (`struct rb_callinfo` + `struct rb_callcache`). Disassembling `def f(a, b); a + b; end; def g(o); o.foo; end` on Ruby 3.3.8 emits specialized operator and send instructions:

```text
0004 opt_plus                  <calldata!mid:+, argc:1, ARGS_SIMPLE>[CcCr]
0002 opt_send_without_block    <calldata!mid:foo, argc:0, ARGS_SIMPLE>
```

Five dynamic language features continuously threaten inline caches and ahead-of-time/JIT assumptions:

1. **Open classes and Basic Operator (BOP) redefinition**: Any Ruby class—including `Integer`, `String`, `Array`, and `BasicObject`—can be reopened at runtime (`class Integer; def +(x); ...; end; end`). `rb_method_entry_make` (`vm_method.c:1393-1411`) acquires the VM lock, walks the entire subclass tree to invalidate cached `rb_callable_method_entry_t` (`cme`) entries, updates `ruby_vm_redefined_flag` when a BOP is overridden, and collects warning metadata to emit *only after releasing the VM lock* (because formatting anonymous class names can invoke `#to_s` and trigger interrupts!).
2. **Lexical `Refinements` (`refine` / `using`)**: Unlike global monkey-patching, a refinement is lexically scoped to the file, class, or module body containing `using M`. Three subtle semantic properties—verified in both `vm_insnhelper.c` and our Ruby 3.3.8 execution probe—govern refinements:
   - **Lexical boundary vs. dynamic call stack**: Inside `RefinedCaller` (`using R`, where `R` refines `Integer#+` to `super(other * 10)`), both direct `2 + 3` and dynamic `2.send(:+, 3)` evaluate to `32`, whereas calling `unrefined_caller(2, 3)` (defined outside `using R`) evaluates to `5` (`2 + 3`).
   - **Self-activation inside `refine` blocks**: The refinement is lexically active inside its own `refine Integer do ... end` body; calling `self * 100 + other` without `super` triggers infinite recursion (`SystemStackError: stack level too deep`, observed directly on Ruby 3.3.8!), whereas `super(other * 10)` dispatches to the unrefined `Integer#+`.
   - **Cache separation invariant**: `vm_insnhelper.c:2064` asserts `VM_ASSERT(!vm_cc_refinement_p(cc))` on standard non-refined call-cache entries so refinement method entries never leak into globally shared call caches.
3. **`method_missing` and `respond_to_missing?`**: When `vm_search_method_slowpath0` fails to locate a callable method entry (or when `vm_call_symbol` encounters a non-existent symbol ID, `vm_insnhelper.c:4417-4430`), YARV records `ec->method_missing_reason` (`MISSING_NOENTRY`, `MISSING_PRIVATE`, `MISSING_VCALL`, etc.) and dispatches `idMethodMissing`. Crucially, if the receiver retains `BasicObject`'s default `method_missing` (`rb_method_basic_definition_p(klass, idMethodMissing)`), CRuby short-circuits directly to `rb_make_no_method_exception` without interning the unknown symbol (preventing symbol-table DoS). Defining `method_missing` without a matching `respond_to_missing?` breaks reflective protocols (`respond_to?`, `method(:name)`).
4. **`Binding` live-frame escape (`EP != BP`)**: Normally, YARV stores local variables on the contiguous VM stack where the environment pointer (`EP`) equals the base pointer (`BP`). Calling `binding` (or capturing a closure `Proc` / calling `eval`) escapes the environment onto the heap so `b.local_variable_set(:x, 777)` can mutate a live method's local variable `x` after the fact (verified on Ruby 3.3.8: `live_frame` returns `777`), breaking any JIT assumption that `EP == BP` or that unaliased locals live strictly in CPU registers.
5. **`Fiber` cooperative stack switching**: Each `Fiber` (`cont.c`) owns an independent YARV VM stack and native C machine stack, yielding and resuming across arbitrary C call frames (`Fiber.yield` / `f.resume`). Garbage collection must scan *every* live fiber's machine stack conservatively.

#### 1.2 YJIT Lazy Basic Block Versioning (LBBV) and Global Invariant Tracking

Basis: source (`ruby/ruby@2e6b197f...`, `yjit/src/{core,invariants}.rs`) + documentation (Chevalier-Boisvert & Feeley ECOOP 2015; Chevalier-Boisvert et al. MPLR 2023)

Unlike method-based tracing or SSA optimizing compilers, YJIT compiles individual YARV basic blocks lazily on demand, specializing each block for the concrete abstract `Context` observed at runtime entry:

- **4-bit `Type` lattice (`yjit/src/core.rs:46-69`)**: YJIT encodes every tracked temporary stack slot and local variable type in at most 4 bits (`max value 15`) inside `Context`:
  `Unknown`, `UnknownImm`, `UnknownHeap`, `Nil`, `True`, `False`, `Fixnum`, `Flonum`, `ImmSymbol`, `TString`/`CString`, `TArray`/`CArray`, `THash`/`CHash`, and `BlockParamProxy`. Notice the distinction between `TString` (C-level `T_STRING` struct layout) and `CString` (exact class `rb_cString`, invalidated if a singleton class is attached to the object!).
- **Version bounding (`yjit/src/core.rs:471, 1222, 2302-2309`)**: Each block version is keyed by `(BlockId, Context)` where `Context` captures `stack_size`, `sp_offset` (deferred SP delta between JIT and interpreter), register mappings, and slot types. To prevent exponential code explosion on polymorphic branches, YJIT caps compiled versions per `BlockId` at `get_option!(max_versions)`, falling back to generalized (`Type::Unknown`) block versions when `next_versions >= max_versions`.
- **Zero-overhead assumption tracking & code patching (`yjit/src/invariants.rs:24-67, 263-647`)**: Rather than emitting repeated runtime checks for rare open-world mutations, YJIT registers compiled `BlockRef`s in global `Invariants` maps and patches invalidated block entries into side exits under `with_vm_lock`:

| YJIT Invariant Table (`invariants.rs`) | C Trigger Callback | Open-World Mutation Invalidated |
| --- | --- | --- |
| `cme_validity` | `rb_yjit_cme_invalidate(callee_cme)` | Open-class method redefinition, `prepend`/`include`, `undef_method`, `alias` |
| `basic_operator_blocks` | `rb_yjit_bop_redefined(klass, bop)` | Redefining `Integer#+`, `Array#[]`, `String#<<`, etc. |
| `constant_state_blocks` | `rb_yjit_constant_state_changed(id)` | Reassigning/removing any segment `A` or `B` in constant path `A::B` |
| `no_singleton_classes` | `rb_yjit_invalidate_no_singleton_class(klass)` | Attaching first singleton class to `Array`, `Hash`, or `String` |
| `no_ep_escape_iseqs` | `rb_yjit_invalidate_ep_is_bp(iseq)` | First `Binding`/`Proc`/`eval` environment escape (`EP != BP`) in an ISEQ |
| `single_ractor` | `rb_yjit_invalidate_single_ractor()` | Spawning a second `Ractor` (changes constant & global access semantics) |
| All ISEQs (`payload.take_all_blocks`) | `rb_yjit_tracing_invalidate_all()` | Enabling `TracePoint` hooks; defers freeing on-stack blocks via `delayed_deallocation` and patches C-return stubs |

- **GC interaction inside YJIT (`invariants.rs:347-390`)**: `rb_yjit_root_mark` calls `rb_gc_mark(cme)` (pinning CME `IMEMO` keys in `cme_validity` because rehashing a moving key during GC could allocate and re-enter GC), whereas `rb_yjit_root_update_references` allows `no_ep_escape_iseqs` ISEQ keys to move during compaction by rebuilding the Rust `HashMap` via `rb_gc_location(iseq)`.

#### 1.3 Conservative C-Extension Stack Scanning, `RB_GC_GUARD`, and `RTypedData` Hazards

Basis: source (`ruby/ruby@2e6b197f...`, `gc.c`, `gc/default/default.c`, `include/ruby/internal/{memory,gc,core/rtypeddata}.h`)

CRuby's C-extension ABI passes raw `VALUE` words without explicit handle registration. Consequently, CRuby's GC uses **conservative stack scanning** (`rb_gc_mark_locations`, `gc.c:3175-3182` -> `rb_gc_impl_mark_maybe`, `gc/default/default.c:6643-6664`): every word on the C stack and spilled registers is tested via `is_pointer_to_heap`; valid non-`T_ZOMBIE`/non-`T_NONE` objects are marked via `gc_mark_and_pin(objspace, obj)`, which both marks the object live *and pins its heap slot* so `GC.compact` cannot relocate it while C code might hold its address.

This hybrid conservative-marking + moving-compaction design introduces **five critical FFI soundness hazards**:

1. **Compiler dead-value elimination breaking stack liveness (`RB_GC_GUARD`, `include/ruby/internal/memory.h:132-181`)**:
   If a C extension writes `char *sptr = RSTRING_PTR(s); ... /* allocations that may trigger GC */ ... use(sptr);`, an optimizing compiler observes that `s` is never read after `RSTRING_PTR(s)` and reuses `s`'s register/stack slot for another value before `use(sptr)`. Because `sptr` points to an external `malloc` buffer (not the `RString` heap slot itself), conservative scanning no longer sees `s`, sweeps `s`, frees `sptr`, and triggers a use-after-free SEGV. `RB_GC_GUARD(s)` MUST be placed **after** the last dereference of `sptr`; on GCC/Clang it expands to:
   ```c
   #define RB_GC_GUARD(v) (*__extension__ ({ \
       volatile VALUE *rb_gc_guarded_ptr = &(v); \
       __asm__("" : : "m"(rb_gc_guarded_ptr)); \
       rb_gc_guarded_ptr; \
   }))
   ```
2. **`GC.compact` pointer invalidation on movable/embedded objects (`rtypeddata.h:165-183`, `gc.h:200-215`)**:
   Objects marked via `rb_gc_mark` are pinned; objects marked via `rb_gc_mark_movable` *can move* during compaction, requiring the extension's `dcompact` callback to rewrite stored `VALUE` fields with `field = rb_gc_location(field)`. For `RUBY_TYPED_EMBEDDABLE` `RTypedData` structs (embedded directly inside the Ruby heap slot rather than `malloc`'d), any interior pointer into the C struct becomes dangling as soon as the enclosing Ruby `VALUE` leaves the C stack and GC compacts the slot (`rtypeddata.h:175-177`).
3. **Sweep-phase GVL/re-entrancy hazard (`RUBY_TYPED_FREE_IMMEDIATELY` & `RUBY_TYPED_THREAD_SAFE_FREE`, `rtypeddata.h:150-163`)**:
   By default, CRuby defers `dfree` callbacks until safe execution outside GC. Setting `RUBY_TYPED_FREE_IMMEDIATELY` runs `dfree` synchronously during sweep while the VM is locked—if `dfree` unlocks the GVL (e.g., flushing I/O) or calls Ruby APIs, threads run concurrently with GC state corruption. Setting `RUBY_TYPED_THREAD_SAFE_FREE` permits parallel `dfree` on *any* native or Ruby thread concurrently with running Ruby code.
4. **Generational GC missing write barriers (`RUBY_TYPED_WB_PROTECTED`, `rtypeddata.h:206-224`)**:
   Third-party `RTypedData` objects are excluded from old-generation promotion by default because failing to emit `RB_OBJ_WRITE(parent, &field, child)` when storing a young `VALUE` inside an old `RUBY_TYPED_WB_PROTECTED` object causes minor GC to miss the young object and free it prematurely.
5. **Ractor data-race bypass (`RUBY_TYPED_FROZEN_SHAREABLE`, `rtypeddata.h:186-197`)**:
   Allows frozen `RTypedData` instances passed through `rb_ractor_make_shareable()` to be accessed across parallel Ractors without the GVL, placing full data-race synchronization responsibility on the C extension.

---

### 2. ECMA-262 `Proxy`/`Reflect` Exotic Object Invariants

Basis: normative (`tc39/ecma262@b1eaed82...`, `spec.html:2907, 15568-16190`) + documentation (Van Cutsem & Miller ECOOP 2013) + execution (`Node.js v24.21.0` / `V8 13.6`)

ECMAScript `Proxy` objects virtualize all 13 essential internal methods (`[[GetPrototypeOf]]`, `[[SetPrototypeOf]]`, `[[IsExtensible]]`, `[[PreventExtensions]]`, `[[GetOwnProperty]]`, `[[DefineOwnProperty]]`, `[[HasProperty]]`, `[[Get]]`, `[[Set]]`, `[[Delete]]`, `[[OwnPropertyKeys]]`, plus `[[Call]]` and `[[Construct]]` for callable targets) via a `handler` object and a `target` object, paired symmetrically with the `Reflect` namespace (`spec.html:52459`).

To preserve **non-configurability** and **non-extensibility** as unforgeable security/integrity primitives (e.g., frozen capability objects, Van Cutsem & Miller ECOOP 2013), ECMA-262 mandates post-trap runtime validation against `[[ProxyTarget]]` (`spec.html:16004-16190`). Every invariant violation MUST throw `TypeError`:

| Internal Method (Trap) | Normative Target Condition (`spec.html`) | Required Post-Trap Validation (`TypeError` on Failure) | Verified V8 13.6 Execution |
| --- | --- | --- | --- |
| `[[Get]]` (`get`, L16004-16042) | Target has own non-configurable, non-writable data prop `P` | `SameValue(trapResult, targetDesc.[[Value]])` must be `true` | `TypeError: ... expected '1' but got '2'` |
| `[[Get]]` (`get`, L16028-16029) | Target has own non-configurable accessor `P` with `[[Get]] === undefined` | `trapResult` must be `undefined` | `TypeError: ... did not return 'undefined' (got '123')` |
| `[[Set]]` (`set`, L16045-16089) | Trap returns truthy; target has own non-configurable, non-writable data prop `P` (or accessor with `[[Set]] === undefined`) | For data prop, `SameValue(value, targetDesc.[[Value]])` must be `true`; for setter-less accessor, unconditionally throws `TypeError` | `TypeError: trap returned truish for property 'x' ...` |
| `[[Delete]]` (`deleteProperty`, L16091-16132) | Trap returns truthy; `P` exists on target and is non-configurable *or* target is non-extensible | Unconditionally throws `TypeError` | `TypeError: trap returned truish for property 'x' which is non-configurable` |
| `[[OwnPropertyKeys]]` (`ownKeys`, L16134-16190) | Any target / non-extensible target | Result must be a duplicate-free list of string/symbol keys containing *all* non-configurable own target keys; if target is non-extensible, result must contain *every* target own key and **no extra keys** | Both omission (`did not include 'x'`) and extra key (`returned extra keys`) throw `TypeError` |
| `[[GetPrototypeOf]]` (`getPrototypeOf`) | Target is non-extensible | `SameValue(trapResult, target.[[GetPrototypeOf]]())` must be `true` | `TypeError: proxy target is non-extensible ...` |

**Subtle engine and verification consequences**:
- **Double-interception re-entrancy**: Notice in `spec.html:16023-16024` that after calling `trap`, the runtime invokes `target.[[GetOwnProperty]](propertyKey)` (`<emu-meta effects="user-code">`). If `target` is itself a nested `Proxy`, invariant checking executes arbitrary user JavaScript *inside* the invariant check—creating re-entrant side effects that optimizing compilers cannot hoist or eliminate.
- **Prototype-chain poisoning**: Placing a `Proxy` anywhere on `Object.prototype` or an object's prototype chain converts ordinary property lookups (`obj.foo`) and `for..in` enumeration into arbitrary trap invocations, forcing V8 to abort fast prototype-chain property loads and invalidate `kPrototypeCheckGroup` dependencies.

---

### 3. V8 Hidden Classes (`Map`), `DependentCode`, Protectors, and Speculative Deoptimization

Basis: source (`v8/v8@e88118f6...`) + execution (`Node.js v24.21.0` / `V8 13.6`) + documentation (Flückiger et al. POPL 2018)

#### 3.1 Hidden Classes (`Map`), Transition Trees, and `ElementsKind` Lattice

V8 represents the structural shape of every JS heap object via an immutable hidden class (`Map`, `src/objects/map.h:221-417`):

- **Transition trees and property order**: Adding properties to an object walks a shared transition tree (`TransitionArray`, `src/objects/transitions.h`). As verified live via `%HaveSameMap`, `{ x: 1, y: 2 }` and `{ x: 10, y: 20 }` share the exact same `Map` (`true`), whereas `{ y: 2, x: 1 }` follows a different branch (`false`), turning monomorphic inline caches polymorphic.
- **Dictionary-mode degradation**: Deleting a non-last property (`delete a.x` on `{ x: 1, y: 2 }`) cannot simply rewind the transition tree; V8 normalizes the object into slow hash-table dictionary mode (`%HasFastProperties(a)` transitions `true` -> `false`, verified live).
- **Monotonic `ElementsKind` lattice (`src/objects/elements-kind.h:93-120`)**: Indexed array storage transitions monotonically downward in specificity: `PACKED_SMI_ELEMENTS` -> `HOLEY_SMI_ELEMENTS` -> `PACKED_DOUBLE_ELEMENTS` -> `HOLEY_DOUBLE_ELEMENTS` -> `PACKED_ELEMENTS` -> `HOLEY_ELEMENTS` (plus non-extensible, sealed, frozen, and resizable `RAB_GSAB_*` typed-array kinds). Reading out-of-bounds or an uninitialized hole triggers `DeoptimizeReason::kHole` / `kOutOfBounds` and walks the prototype chain unless guarded by `NoElementsProtector`.

#### 3.2 `DependentCode`, `CompilationDependencies`, and Global Protectors

V8's tiered pipeline (`Ignition` bytecode interpreter -> `Sparkplug` baseline -> `Maglev` mid-tier SSA JIT -> `TurboFan`/`Turboshaft` optimizing JIT) relies on `CompilationDependencies` (`src/compiler/compilation-dependencies.h:49-94`) installed as weak entries inside `DependentCode` (`src/objects/dependent-code.h:37-72`):

- **10 `DependentCode::DependencyGroup` bitflags**: `kTransitionGroup` (map stability), `kPrototypeCheckGroup` (fast/dictionary prototype chain stability), `kPropertyCellChangedGroup` (global variable cell type/constness), `kFieldTypeGroup`, `kFieldConstGroup` (property never overwritten), `kFieldRepresentationGroup` (Smi/Double/HeapObject representation), `kInitialMapChangedGroup`, `kAllocationSiteTransitionChangedGroup`, `kContextCellChangedGroup`, and `kEmptyContextExtensionGroup` (no `eval`/`with` context extension).
- **Global `Protectors` (`src/execution/protectors.h:19-58`)**: Fast global sentinel cells invalidating optimized code when rare JS invariants break—including `NoElementsProtector` (no indexed elements on `Array.prototype`/`Object.prototype`), `ArraySpeciesProtector` (`Symbol.species` untouched), `ArrayIteratorProtector`, `ArrayBufferDetachingProtector`, `ArrayBufferMutableProtector`, and `NoUndetectableObjectsProtector`.

#### 3.3 Eager vs. Lazy Deoptimization and `TranslatedState` Frame Materialization

Basis: source (`v8/v8@e88118f6...`, `src/deoptimizer/{deoptimizer.h,deoptimize-reason.h,translated-state.h}`) + execution (`V8 13.6`) + documentation (Flückiger et al. POPL 2018)

When a speculative assumption fails, V8 must seamlessly transition mid-execution from optimized machine code back to Ignition interpreter bytecode frames without losing any observable side effects (the exact semantic-preservation property formalized by Flückiger et al., POPL 2018):

1. **Eager deoptimization (`deopt-eager`)**: Triggered synchronously at an inline speculation guard (`CheckMaps`, `CheckSmi`, `CheckBounds`, `CheckNotHole`; full taxonomy in `DEOPTIMIZE_REASON_LIST`, `src/deoptimizer/deoptimize-reason.h:20-95`). Observed live in V8 13.6 on both tiers when calling `sumX({ y: 1, x: 1.5 })`:
   - Maglev: `[bailout (kind: deopt-eager, reason: wrong map): begin. deoptimizing ... <Code MAGLEV> ... FP to SP delta 24]`
   - TurboFan: `[bailout (kind: deopt-eager, reason: wrong map): begin. deoptimizing ... <Code TURBOFAN_JS> ... FP to SP delta 32]`
2. **Lazy deoptimization (`deopt-lazy`)**: Triggered asynchronously while an optimized function is *suspended on the call stack* awaiting a callee. When the callee mutates a prototype property (`Base.prototype.k = 99`), `DependentCode::DeoptimizeDependencyGroups` marks the live `Code` object invalid (`reason: dependent field type constness changed`, observed live!). V8 patches the return address of the suspended frame to a lazy-deopt trampoline; the instant `hook(true)` returns, V8 executes `[bailout (kind: deopt-lazy, ...): begin. deoptimizing ... bytecode offset 8]` and resumes `readProto` in Ignition to re-read `o.k == 99`, returning `42 + 99 = 141` instead of the stale constant-folded `84`.
3. **Escape-analysis object materialization (`TranslatedState` / `TranslatedValue`, `src/deoptimizer/translated-state.h:57-215`)**:
   TurboFan aggressively inlines callees and scalar-replaces non-escaping heap allocations (`kCapturedObject`, `kUniqueCapturedObject`, `kDuplicatedObject`, `kCapturedStringConcat`) and unboxed numbers (`kInt32`, `kFloat`, `kDouble`, `kHoleyDouble`, `kInt64ToBigInt`, `kSimd128`). During `Deoptimizer::DoComputeOutputFrames`, V8 decodes the compact frame-translation table into `TranslatedFrame`s—expanding one physical optimized frame into $k \ge 1$ Ignition frames—and materializes virtual objects through a strict 3-state machine (`kUninitialized` -> `kAllocated` byte-array placeholder -> `kFinished` morphed heap object, `translated-state.h:109-115, 175-177`) so cyclic references among scalar-replaced objects are resolved safely without invoking user JS or triggering re-entrant GC corruption.

---

### 4. ECMA-262 `SharedArrayBuffer` Weak Memory Model and Mixed-Width Tearing

Basis: normative (`tc39/ecma262@b1eaed82...`, `spec.html:52686-53285`) + documentation (Watt et al. PLDI 2020) + execution (`Node.js v24.21.0`)

ECMAScript defines a formal axiomatic relaxed memory model over byte-indexed `Shared Data Block` events (`ReadSharedMemory`, `WriteSharedMemory`, `ReadModifyWriteSharedMemory`) with two orderings: `~unordered~` (normal `TypedArray` loads/stores) and `~seq-cst~` (`Atomics.*`) (`spec.html:53189-53266`).

Unlike C++11/Rust (where *any* data race triggers full Undefined Behavior), ECMAScript defines **bounded, safe semantics even for racy programs** (since browsers execute untrusted JavaScript):

- **Valid Executions (`sec-valid-executions`, `spec.html:53219-53231`)**: Every program has at least one valid execution satisfying: strict partial-order `happens-before`, valid chosen reads, coherent reads, tear-free reads, and sequentially consistent atomics (`is-memory-order-before`).
- **Data Race Freedom -> SC (`sec-data-races`, `sec-data-race-freedom`, `spec.html:53248-53266`)**: Two non-happens-before racing events on non-disjoint byte ranges form a *data race* if either event is not `~seq-cst~` **or** their byte ranges overlap without being equal (mixed-size atomic race!). Every data-race-free program executes sequentially consistently.
- **Exact Tear-Free Boundary (`sec-tear-free-aligned-reads`, `spec.html:53171-53187`)**:
  The normative algorithm guarantees that an aligned `[[NoTear]] = true` integer `TypedArray` read cannot mix bytes from two distinct `[[NoTear]] = true` writes **only when the read and both writes have equal memory ranges** (same byte index and element size). The specification explicitly warns (`spec.html:53185`): *"It is possible, however, for an aligned read event to read from multiple write events with overlapping ranges."*
  - **Live x86-64 tearing verification**: In our Node.js v24 `worker_threads` probe, a worker loops writing two 32-bit halves (`u32[0] = pat; u32[1] = pat;`, alternating `0x11111111` and `0x22222222`) into a `SharedArrayBuffer` while the main thread reads via an overlapping 64-bit `BigUint64Array` (`u64[0]`). Even on x86-64 TSO, the probe deterministically observes torn mixed words (`tornCount=5, sampleTorn=0x2222222211111111`) in milliseconds.
- **Compiler constraint (`sec-shared-memory-guidelines`, `spec.html:53283-53285`)**: *"Atomics are carved in stone"*—JIT compilers must never remove `~seq-cst~` events or reorder them with respect to each other or `~unordered~` events in an agent-order slice, and must treat unknown calls as potential `~seq-cst~` barriers.
- **Historical soundness repairs (Watt et al., PLDI 2020)**: Mechanizing the ES2017 memory model in Coq/Isabelle revealed that the original specification accidentally forbade valid ARMv8 compilation schemes for mixed-size `seq-cst` accesses and lacked adequate SC constraints on mixed atomic/non-atomic races; TC39 adopted Watt et al.'s strengthened `is-memory-order-before` formulation (now codified in `spec.html:53189-53216`).

---

### 5. TypeScript Intentional Structural Unsoundness

Basis: source (`microsoft/TypeScript@9c4ad5cb...`, `tsc/internal/checker/relater.go`) + documentation (Bierman et al. ECOOP 2014; Rastogi et al. POPL 2015)

TypeScript adds erased static structural types over JavaScript without emitting runtime type checks. Direct inspection of TypeScript `7.1.0-dev`'s type-relation engine (`tsc/internal/checker/relater.go`) verifies five **intentional soundness holes** baked directly into the assignability relation:

1. **Bivariant methods and constructors under `strictFunctionTypes` (`relater.go:1538, 1587-1615`)**:
   ```go
   strictVariance := checkMode&SignatureCheckModeCallback == 0 && c.strictFunctionTypes &&
       kind != ast.KindMethodDeclaration && kind != ast.KindMethodSignature && kind != ast.KindConstructor
   ```
   When `!strictVariance`, `compareSignaturesRelated` tests covariant parameter assignability (`compareTypes(sourceType, targetType)`) *before* contravariant assignability (`compareTypes(targetType, sourceType)`, `relater.go:1609-1614`). The checker's own comment (`relater.go:1587-1594`) explains that bivariant methods exist specifically so generic types like `Array<T>` (whose `.push(item: T)` uses method syntax) remain covariant in `T`—meaning `Dog[]` is assignable to `Animal[]`, after which `animals.push(new Cat())` silently corrupts a `Dog[]` at runtime!
2. **Covariant mutable properties and `readonly` erasure (`relater.go:4361-4404`)**:
   `isPropertySymbolTypeRelated` (`relater.go:4395-4404`) checks *only* `r.isRelatedToEx(effectiveSource, effectiveTarget, ...)`—never invariance—even for writable object properties. Moreover, lines 4361-4369 explicitly note that `{ readonly a: T }` and `{ a: T }` are mutually assignable under `assignableRelation` (`readonly` rejection applies *only* during `strictSubtypeRelation` for union subtype reduction). Aliasing a `{ readonly x: number }` as `{ x: number }` lets safe TypeScript mutate `readonly` fields without any cast.
3. **`any` as simultaneous top and bottom (`relater.go:212-216, 264-266`)**:
   In `isSimpleTypeRelatedTo`, `target.flags&TypeFlagsAny != 0` unconditionally returns `true` (top), and in `assignableRelation`/`comparableRelation`, `source.flags&TypeFlagsAny != 0` also returns `true` (bottom, assigning `any` to `number`, `string`, or arbitrary interfaces with zero runtime checks—unlike `unknown`, which permits top-assignment only).
4. **Excess-property check bypass via variable aliasing (`relater.go:2754`)**:
   `hasExcessProperties` enforces closed-record checking only on fresh object literals (`ObjectFlagsFreshLiteral`). Assigning `const obj = { x: 1, extra: "oops" }; const t: { x: number } = obj;` strips freshness and bypasses excess-property rejection, breaking assumptions about `Object.keys(t)` or prototype/dictionary merging.
5. **Unchecked indexed access and zero-overhead erasure**:
   Without `noUncheckedIndexedAccess`, indexing `arr[999]` or `record[key]` types as `T` rather than `T | undefined`; and unlike Safe TypeScript (Rastogi et al., POPL 2015), TypeScript performs no runtime wrapper/cast insertion. Consequently, TypeScript static types provide **zero runtime memory-safety, type-safety, or capability-isolation guarantees** against untrusted JS callers, JSON deserialization, `Proxy` traps, or `SharedArrayBuffer` races.

---

### 6. Cross-Runtime Speculative Execution and Invalidation Matrix

Basis: source + execution + derived

| Architectural Axis | CRuby YARV + YJIT (`ruby/ruby@2e6b197f`) | V8 Ignition + Maglev/TurboFan (`v8/v8@e88118f6`) | CPython Tier-1 + Tier-2 JIT (`python/cpython@441c010f`) |
| --- | --- | --- | --- |
| Primary specialization unit | Basic block version `(BlockId, Context)` via LBBV (capped by `max_versions`) | Whole function / OSR loop with feedback vectors (`Maglev` SSA, `TurboFan` Sea-of-Nodes/Turboshaft) | Inline-cached bytecode (Tier-1) -> linear micro-op traces (`_PyExecutorObject`, Tier-2 copy-and-patch) |
| Object shape / type model | 4-bit `Type` lattice (`Fixnum`, `CString`, `TString`, etc.) + `rb_callable_method_entry_t` | `Map` transition trees + monotonic `ElementsKind` lattice + `FieldRepresentation` | `tp_version_tag` + split/inline-values `keys_version` + descriptor kind analysis |
| Global assumption invalidation | 7 `Invariants` tables (`cme`, `BOP`, constants, no-singleton, `ep_is_bp`, single-ractor, tracing) | `DependentCode` (10 bitflags) + global `Protectors` (`NoElements`, `ArraySpecies`, etc.) | `PyType_Modified` (subclass tree) + `_Py_Executors_InvalidateDependency` (incl. `FrameLocalsProxy`) |
| Frame reconstruction on bailout | Side-exit stub restores YARV `sp_offset` / PC directly into YARV interpreter | `Deoptimizer` + `TranslatedState` un-inlines frames and materializes `kCapturedObject`s into Ignition | `_COLD_EXIT` stub syncs Tier-1 stack/IP; `MAX_CHAIN_DEPTH` bounds side-exit chains |
| Live frame mutation / debugging | `Binding` triggers `rb_yjit_invalidate_ep_is_bp`; `TracePoint` triggers `rb_yjit_tracing_invalidate_all` | Debugger triggers `DeoptimizeTopmostFrame` / `DebuggerInspectableFrame` materialization | `FrameLocalsProxy` invalidates executors and pins overwritten values in `f_overwritten_fast_locals` |
| Native FFI / GC safety seam | Conservative C-stack scan (`gc_mark_and_pin`), `RB_GC_GUARD`, `RTypedData` compaction/WB flags | V8 `HandleScope` / `Local<T>` / `Global<T>` explicit handle table (precise moving GC) | `PyObject*` manual refcount (borrowed/stolen hazards) vs. `HPy` handles / `PyO3` `Bound<'py, T>` |

## Boundaries

- **Live YJIT machine-code execution (`not examined`)**: The local `ruby 3.3.8` binary was built without YJIT (`ruby --yjit` prints a build warning and leaves `RubyVM::YJIT` undefined). Therefore, YJIT LBBV block versioning, side-exit counts, and `rb_yjit_*` invalidation callbacks are verified strictly by `source` inspection of `ruby/ruby@2e6b197f...` (API 4.1.0) and Chevalier-Boisvert et al. (MPLR 2023), not live YJIT execution.
- **V8 version skew between source and execution (`known not to apply` to byte-level ABI details)**: Source inspection pinned `v8/v8` at `e88118f6...` (`V8 16.0.0-candidate`), whereas local execution ran `Node.js v24.21.0` (`V8 13.6.233.17-node.53`). Architectural mechanisms (`Map`, `DependentCode`, `TranslatedState`, `MAGLEV`/`TURBOFAN_JS` eager and lazy deopt) match across both, but exact bit positions in `Map::bit_field3`, `DeoptimizeReason` enum ordinals, and FP-to-SP deltas are revision-specific.
- **Local `tsc` execution (`not examined`)**: No TypeScript compiler binary (`tsc`) is installed on the host; TypeScript soundness findings are grounded directly in `source` inspection of `microsoft/TypeScript@9c4ad5cb...` (`tsc/internal/checker/relater.go`) and peer-reviewed formalizations (ECOOP 2014, POPL 2015).
- **Non-x86-64 memory ordering (`not examined`)**: The `SharedArrayBuffer` tearing probe executed on x86-64 TSO, which exhibits mixed-width tearing (`u32` vs. `u64`) but does not exhibit ARMv8/POWER store-buffering or load-load reordering anomalies on equal-width `~unordered~` accesses (those are established normatively from `tc39/ecma262` and Watt et al. PLDI 2020).
- **V8 Turboshaft vs. TurboFan internal IR pipeline & Ruby Prism/RJIT (`not examined`)**: Internal Turboshaft graph lowering and Ruby's pure-Ruby experimental RJIT were outside scope.
- **Attractive stronger conclusions NOT established**:
  - *Does ECMA-262 `Proxy` guarantee complete behavioral transparency for frozen targets?* **Known not to apply.** Proxy invariants lock down non-configurable and non-extensible *structural* properties (`[[Get]]`/`[[Set]]`/`[[Delete]]`/`[[OwnPropertyKeys]]`/`[[GetPrototypeOf]]`), but traps can still introduce arbitrary observable side effects, latency, re-entrancy, or non-deterministic return values on configurable properties and function calls.
  - *Does ECMA-262 forbid all tearing on `SharedArrayBuffer` integer `TypedArray`s?* **Known not to apply.** `sec-tear-free-aligned-reads` (`spec.html:53171-53187`) prevents tearing *only* among aligned integer accesses with **equal** byte ranges; overlapping mixed-width views (`Uint32Array` + `BigUint64Array`) are explicitly allowed to tear and do tear on x86-64.
  - *Does enabling TypeScript's `"strict": true` (including `strictFunctionTypes` and `strictNullChecks`) make TypeScript type-sound?* **Known not to apply.** Verified directly at `tsc/internal/checker/relater.go:1538, 4361-4404` that method/constructor bivariance, covariant writable properties/arrays, `readonly` assignability erasure, `any` top+bottom escape, and aliased excess properties remain enabled even under `"strict": true`.
  - *Does CRuby's conservative stack scanner make C extensions safe without GC annotations?* **Known not to apply.** Compiler dead-value elimination drops unguarded `VALUE` variables before interior `RSTRING_PTR` dereferences (`include/ruby/internal/memory.h:135-143`), requiring `RB_GC_GUARD`, `RB_OBJ_WRITE`, and `rb_gc_location` for compaction-safe C extensions.

## Evidence

### Primary Git Repositories and Source Locations (observed 2026-11-19)

1. **`ruby/ruby` @ `2e6b197f6849401b2c25894b5b8ac39ac3c2558e` (`RUBY_API_VERSION = 4.1.0`)**:
   - `include/ruby/version.h` & `version.h:10-16` — API version `4.1.0`.
   - `yjit/src/core.rs:46-69, 471-480, 1222, 2302-2309` — 16-variant 4-bit `Type` lattice, `Context`, `BlockId`, `max_versions` cap.
   - `yjit/src/invariants.rs:24-67, 98-440, 543-647` — `Invariants` struct (`cme_validity`, `basic_operator_blocks`, `single_ractor`, `constant_state_blocks`, `no_singleton_classes`, `no_ep_escape_iseqs`), all `rb_yjit_*` invalidation callbacks, `rb_yjit_root_mark` pinning CMEs vs. `rb_yjit_root_update_references` relocating ISEQs, `rb_yjit_tracing_invalidate_all` delayed deallocation.
   - `vm_insnhelper.c:1087-1091, 2064, 2273-2320, 4402-4430` — refinement checks (`VM_ASSERT(!vm_cc_refinement_p(cc))`), `vm_search_method_slowpath0`, `vm_call_symbol` / `vm_call_method_missing`.
   - `vm_method.c:1393-1411` — `rb_method_entry_make` VM lock discipline and subclass-tree redefinition walk.
   - `gc.c:3175-3188` & `gc/default/default.c:6643-6672` — `rb_gc_mark_locations` conservative stack scan and `rb_gc_impl_mark_maybe` -> `gc_mark_and_pin`.
   - `include/ruby/internal/memory.h:132-181` — `RB_GC_GUARD` rationale and GCC/Clang inline-asm implementation.
   - `include/ruby/internal/gc.h:200-215` — `rb_gc_mark_movable` and `rb_gc_location`.
   - `include/ruby/internal/core/rtypeddata.h:134-230` — `RUBY_TYPED_FREE_IMMEDIATELY`, `RUBY_TYPED_THREAD_SAFE_FREE`, `RUBY_TYPED_EMBEDDABLE`, `RUBY_TYPED_FROZEN_SHAREABLE`, `RUBY_TYPED_WB_PROTECTED`.
2. **`tc39/ecma262` @ `b1eaed82fc5e8a511c5b2007f194b16c8f7e5ea6`**:
   - `spec.html:2907` — `sec-invariants-of-the-essential-internal-methods`.
   - `spec.html:15568-16190` — `Proxy` exotic object internal methods (`[[Get]]` L16004, `[[Set]]` L16045, `[[Delete]]` L16091, `[[OwnPropertyKeys]]` L16134).
   - `spec.html:52459` — `sec-reflect-object`.
   - `spec.html:52686-53285` — `sec-memory-model`, `sec-tear-free-aligned-reads` (L53171-53187), `sec-memory-order` (L53189-53216), `sec-valid-executions` (L53219-53231), `sec-data-races` (L53248-53259), `sec-shared-memory-guidelines` (L53268-53285).
3. **`v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0` (`V8 16.0.0-candidate`)**:
   - `include/v8-version.h:11-18` — version `16.0.0` candidate.
   - `src/objects/map.h:221-417` & `src/objects/elements-kind.h:93-120` — `Map` bitfields (`is_prototype_map`, `is_deprecated`, `is_extensible`, `ElementsKind`), `PACKED_*`/`HOLEY_*` and `RAB_GSAB_*` kinds.
   - `src/objects/dependent-code.h:37-108` — 10 `DependencyGroup` bitflags and weak `{InstructionStream, Smi}` storage.
   - `src/compiler/compilation-dependencies.h:49-94` & `src/execution/protectors.h:19-58` — `DependOn*` assumptions and global protectors.
   - `src/deoptimizer/deoptimizer.h:37-120`, `src/deoptimizer/deoptimize-reason.h:16-95`, `src/deoptimizer/translated-state.h:57-215` — `Deoptimizer`, `DEOPTIMIZE_REASON_LIST`, `TranslatedValue::Kind` (`kCapturedObject`, `kUniqueCapturedObject`, `kDuplicatedObject`, `kCapturedStringConcat`) and 3-state materialization.
4. **`microsoft/TypeScript` @ `9c4ad5cbc5a24f3e8893c6e395ac8981c1154c16` (`version = "7.1.0-dev"`)**:
   - `tsc/internal/core/version.go:8` — `"7.1.0-dev"`.
   - `tsc/internal/checker/relater.go:209-266` — `isSimpleTypeRelatedTo` (`TypeFlagsAny` top and bottom).
   - `tsc/internal/checker/relater.go:1538, 1587-1625` — `compareSignaturesRelated` (`strictVariance` excluding `KindMethodDeclaration`, `KindMethodSignature`, `KindConstructor`).
   - `tsc/internal/checker/relater.go:2754` — `hasExcessProperties`.
   - `tsc/internal/checker/relater.go:4331-4404` — `propertyRelatedTo` (`readonly` mutual assignability at L4361-4369) and `isPropertySymbolTypeRelated` (covariant property check at L4403).

### Peer-Reviewed Literature (verified 2026-11-19)

- M. Chevalier-Boisvert, M. Feeley, *"Simple and Effective Type Check Removal through Lazy Basic Block Versioning"*, ECOOP 2015, LIPIcs vol. 37, pp. 101–123, DOI `10.4230/LIPIcs.ECOOP.2015.101`.
- M. Chevalier-Boisvert, T. Kokubun, N. Gibbs, S. X. Wu, A. Patterson, J. Issroff, *"Evaluating YJIT's Performance in a Production Context: A Pragmatic Approach"*, MPLR 2023, pp. 20–33, DOI `10.1145/3617651.3622982`.
- T. Van Cutsem, M. S. Miller, *"Trustworthy Proxies: Virtualizing Objects with Invariants"*, ECOOP 2013, LNCS, DOI `10.1007/978-3-642-39038-8_7`.
- O. Flückiger, G. Scherer, M.-H. Yee, A. Goel, A. Ahmed, J. Vitek, *"Correctness of Speculative Optimizations with Dynamic Deoptimization"*, POPL 2018 (PACMPL), DOI `10.1145/3158137`.
- C. Watt, C. Pulte, A. Podkopaev, G. Barbier, S. Dolan, S. Flur, J. Pichon-Pharabod, S. Guo, *"Repairing and Mechanising the JavaScript Relaxed Memory Model"*, PLDI 2020, DOI `10.1145/3385412.3385973`.
- G. M. Bierman, M. Abadi, M. Torgersen, *"Understanding TypeScript"*, ECOOP 2014, LNCS vol. 8586, pp. 257–281, DOI `10.1007/978-3-662-44202-9_11`.
- A. Rastogi, N. Swamy, C. Fournet, G. Bierman, P. Vekris, *"Safe & Efficient Gradual Typing for TypeScript"*, POPL 2015, DOI `10.1145/2676726.2676971`.

### Execution Probes and Recorded Outputs (observed 2026-11-19)

#### Probe A: CRuby 3.3.8 YARV, Lexical `Refinements`, `method_missing`, `Binding`, and `Fiber`

```ruby
# Run with: ruby probe_ruby.rb
iseq = RubyVM::InstructionSequence.compile("def f(a, b); a + b; end; def g(o); o.foo; end")
puts iseq.disasm.lines.select { |l| l =~ /opt_plus|opt_send_without_block/ }.join

module R
  refine Integer do
    def +(other); super(other * 10); end
  end
end
def unrefined_caller(x, y); x + y; end
class RefinedCaller
  using R
  def self.direct(x, y); x + y; end
  def self.via_send(x, y); x.send(:+, y); end
  def self.indirect(x, y); unrefined_caller(x, y); end
end
puts [RefinedCaller.direct(2, 3), RefinedCaller.via_send(2, 3), RefinedCaller.indirect(2, 3), 2 + 3].inspect

def live_frame; x = 10; b = binding; b.local_variable_set(:x, 777); x; end
f = Fiber.new { |v| v2 = Fiber.yield(v + 1); v2 * 10 }
puts "binding=#{live_frame} fiber=[#{f.resume(5)}, #{f.resume(9)}, alive=#{f.alive?}]"
```

Observed output (`ruby 3.3.8`, exit code `0`):

```text
0004 opt_plus                               <calldata!mid:+, argc:1, ARGS_SIMPLE>[CcCr]
0002 opt_send_without_block                 <calldata!mid:foo, argc:0, ARGS_SIMPLE>
[32, 32, 5, 5]
binding=777 fiber=[6, 90, alive=false]
```

#### Probe B: ECMA-262 `Proxy` Invariants & V8 13.6 Map/Maglev/TurboFan Eager and Lazy Deoptimization

```bash
# Run with: node --allow-natives-syntax --trace-deopt probe_v8.mjs
```

```javascript
// 1. Hidden-class map sensitivity and dictionary fallback
const a = { x: 1, y: 2 }, b = { x: 10, y: 20 }, c = { y: 2, x: 1 };
console.log("maps:", %HaveSameMap(a, b), %HaveSameMap(a, c), %HasFastProperties(a));
delete a.x;
console.log("after delete a.x fast?:", %HasFastProperties(a));

// 2. Maglev eager deopt (wrong map)
function sumM(o) { return o.x + 1; }
%PrepareFunctionForOptimization(sumM); sumM({ x: 1 }); sumM({ x: 2 });
%OptimizeMaglevOnNextCall(sumM); sumM({ x: 3 });
console.log("maglev deopt:", sumM({ y: 1, x: 1.5 }));

// 3. TurboFan lazy deopt via DependentCode kFieldConstGroup prototype mutation
function Base() {}
Base.prototype.k = 42;
function hook(m) { if (m) Base.prototype.k = 99; }
%NeverOptimizeFunction(hook);
function readProto(o, m) { const v1 = o.k; hook(m); return v1 + o.k; }
const inst = new Base();
%PrepareFunctionForOptimization(readProto); readProto(inst, false); readProto(inst, false);
%OptimizeFunctionOnNextCall(readProto);
console.log("opt:", readProto(inst, false), "lazyDeopt:", readProto(inst, true));
```

Observed output (`Node.js v24.21.0` / `V8 13.6.233.17-node.53`, exit code `0`, pointer addresses omitted for stability):

```text
maps: true false true
after delete a.x fast?: false
[bailout (kind: deopt-eager, reason: wrong map): begin. deoptimizing <JSFunction sumM>, <Code MAGLEV>, opt id 1, bytecode offset 0, deopt exit 0, FP to SP delta 24]
maglev deopt: 2.5
[marking dependent code <Code TURBOFAN_JS> (<SharedFunctionInfo readProto>) (opt id 2) for deoptimization, reason: dependent field type constness changed]
[bailout (kind: deopt-lazy, reason: (unknown)): begin. deoptimizing <JSFunction readProto>, <Code TURBOFAN_JS>, opt id 2, bytecode offset 8, deopt exit 4, FP to SP delta 32]
opt: 84 lazyDeopt: 141
```

#### Probe C: ECMA-262 `Proxy` Invariant Enforcement Matrix

```javascript
// Run with: node probe_proxy.mjs
const t1 = Object.defineProperty({}, "x", { value: 1, writable: false, configurable: false });
const t2 = Object.defineProperty({}, "y", { get: undefined, set() {}, configurable: false });
const t6 = Object.preventExtensions({ a: 1 });
const cases = [
  ["get_nonwritable_nonconfig", () => new Proxy(t1, { get: () => 2 }).x],
  ["get_undefined_getter_nonconfig", () => new Proxy(t2, { get: () => 123 }).y],
  ["set_nonwritable_nonconfig", () => { new Proxy(t1, { set: () => true }).x = 99; }],
  ["delete_nonconfig", () => delete new Proxy(t1, { deleteProperty: () => true }).x],
  ["ownKeys_omit_nonconfig", () => Object.keys(new Proxy(t1, { ownKeys: () => [] }))],
  ["ownKeys_extra_nonextensible", () => Reflect.ownKeys(new Proxy(t6, { ownKeys: () => ["a", "b"] }))],
  ["getPrototypeOf_nonextensible", () => Object.getPrototypeOf(new Proxy(t6, { getPrototypeOf: () => null }))],
];
for (const [label, fn] of cases) {
  try { fn(); console.log("FAIL", label); }
  catch (e) { console.log("OK", label, e.name); }
}
```

Observed output (`Node.js v24.21.0` / `V8 13.6.233.17-node.53`, exit code `0`):

```text
OK get_nonwritable_nonconfig TypeError
OK get_undefined_getter_nonconfig TypeError
OK set_nonwritable_nonconfig TypeError
OK delete_nonconfig TypeError
OK ownKeys_omit_nonconfig TypeError
OK ownKeys_extra_nonextensible TypeError
OK getPrototypeOf_nonextensible TypeError
```

#### Probe D: `SharedArrayBuffer` Mixed-Width Tearing on x86-64

```javascript
// Run with: node probe_sab.mjs
import { Worker, isMainThread, workerData } from "node:worker_threads";
if (isMainThread) {
  const sab = new SharedArrayBuffer(16);
  const u32 = new Uint32Array(sab), u64 = new BigUint64Array(sab, 0, 1);
  const worker = new Worker(new URL(import.meta.url), { workerData: sab });
  const A = 0x1111111111111111n, B = 0x2222222222222222n;
  let torn = 0n, tornCount = 0, deadline = Date.now() + 800;
  while (Atomics.load(u32, 2) === 0) {}
  while (Date.now() < deadline && tornCount < 5) {
    const v = u64[0];
    if (v !== 0n && v !== A && v !== B) { torn = v; tornCount++; }
  }
  Atomics.store(u32, 2, 2);
  await worker.terminate();
  console.log(`Mixed-width SAB race: tornCount=${tornCount}, sampleTorn=0x${torn.toString(16)}`);
} else {
  const u32 = new Uint32Array(workerData);
  Atomics.store(u32, 2, 1);
  for (let toggle = false; Atomics.load(u32, 2) === 1; toggle = !toggle) {
    const pat = toggle ? 0x11111111 : 0x22222222;
    u32[0] = pat; u32[1] = pat;
  }
}
```

Observed output (`Node.js v24.21.0`, Linux x86_64, exit code `0`):

```text
Mixed-width SAB race: tornCount=5, sampleTorn=0x2222222211111111
```

## Revalidation

1. **Revalidate CRuby YJIT invariants & GC flags**: On a newer `ruby/ruby` commit, diff `yjit/src/core.rs` (`enum Type`), `yjit/src/invariants.rs` (`struct Invariants`, `rb_yjit_*`), and `include/ruby/internal/core/rtypeddata.h` (`rbimpl_typeddata_flags`). On any Ruby binary built with `--enable-yjit`, rerun Probe A with `ruby --yjit --yjit-stats` to observe live `invalidate_ep_escape` and `invalidate_bop_redefined` counters directly.
2. **Revalidate V8 deoptimization and `DependentCode`**: Rerun Probe B under `node --allow-natives-syntax --trace-deopt` on any target Node.js/V8 release to verify `<Code MAGLEV>` / `<Code TURBOFAN_JS>` eager and lazy deoptimization frames, and diff `src/objects/dependent-code.h` and `src/deoptimizer/translated-state.h` for new dependency groups or virtual-object kinds.
3. **Revalidate ECMA-262 Proxy invariants & `SharedArrayBuffer` tearing**: Run Probe C (`node probe_proxy.mjs`) and Probe D (`node probe_sab.mjs`) on target JS engines (V8, SpiderMonkey, JavaScriptCore); any change in Proxy `TypeError` behavior signals a normative regression against `tc39/ecma262`.
4. **Revalidate TypeScript unsoundness rules**: Diff `tsc/internal/checker/relater.go` (around `strictVariance` in `compareSignaturesRelated`, `isSimpleTypeRelatedTo`, and `propertyRelatedTo`) in newer `microsoft/TypeScript` revisions, or compile minimal counterexample files with `tsc --strict --noEmit` to check whether a new opt-in compiler flag tightens method variance or `readonly` assignability.
