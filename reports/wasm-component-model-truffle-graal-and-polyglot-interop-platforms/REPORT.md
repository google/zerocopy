# N-to-N Polyglot Interoperability Platforms: WebAssembly Component Model, GraalVM Truffle, ECMA-335 CLI, and Zero-Copy Capability Wire Protocols

## Summary

Industrial platforms that collapse $O(N \times M)$ pairwise FFI bridges into $O(N + M)$ polyglot substrates occupy four distinct architectural vertices, trading off memory encapsulation, copy amplification, cross-language JIT specialization, and type-system expressiveness:

1. **Shared-nothing component ABIs (WebAssembly Component Model: `WIT`, Canonical ABI, `wasmtime`)** eliminate ambient raw-pointer aliasing across untrusted languages by isolating each component in a disjoint linear memory and mediating cross-boundary state via `lift`/`lower` value copies (`cabi_realloc`) and capability handle tables (`own<T>` / `borrow<T>`). Dynamic borrow tracking enforces temporal safety across non-lifetime-checked guests (`Task.num_borrows == 0` on return; `ResourceHandle.num_lends == 0` on drop/transfer), while WASI 0.3 adds non-coloring `async` effect typing (`stream<T>`/`future<T>`). Its primary wall is an **$O(N)$ deep-copy and string-transcoding cliff** (verified at **2.703x write / 3.703x read+write amplification** and **3 `cabi_realloc` calls** in a single mixed Latin-1/CJK `utf8 -> latin1+utf16` crossing, and **12.0x traffic** across 4 alternating hops); even `stream<T>` and `WasmGC` v1 MVP do not provide zero-copy shared cross-component views until a Component Model GC ABI option and `shared-everything-threads` stabilize.
2. **Shared-AST / shared-JIT polyglot VMs (GraalVM `Truffle` + `InteropLibrary`)** compile multiple guest interpreters (`JS`, `Python`, `Ruby`, `R`, `Sulong` LLVM bitcode, `Espresso`) into one managed heap and JIT compilation unit via partial evaluation over polymorphic `@CachedLibrary` inline caches. Their walls are **semantic and isolation limits**: foreign proxy object-identity splits requiring symmetric `TriState` double dispatch (`isIdenticalOrUndefined`), collapsed `isNull`/numeric/meta-object semantics, single-threaded language defaults (`TruffleLanguage.isThreadAccessAllowed`) serializing an entire polyglot `Context`, `libffi` boundary reversion in Truffle NFI, and re-introduction of isolation boundaries whenever untrusted sandboxing demands Native Image **Polyglot Isolates**.
3. **Common Intermediate Language runtimes (`ECMA-335` CLI / .NET `CoreCLR`)** unify statically typed managed languages (`C#`, `F#`, `VB.NET`) around a single Common Type System (CTS) with unboxed value types, reified generics (value-type specialization + shared reference-type code via hidden generic dictionaries), and the CLS boundary subset. Languages with non-CLR semantics hit structural walls: affine/unmanaged lifetimes (`C++/CLI` mixed-mode binaries, Rust-to-CIL losing verifiability), 11-step per-call P/Invoke GC-transition frames, post-standard augmentations (`Ref Fields`, `ByRefLike` generics, `Extended Layout`) required even for safe `Span<T>`, and strict `tail.` restrictions (`§III.2.4`; CoreCLR `fgCanFastTailCall` rejecting `byref` parameters, `localloc`, and mismatched return buffers).
4. **Zero-copy wire schemas and capability IPC bridges (`Cap'n Proto` and Fuchsia `FIDL`)** avoid native-heap sharing and parse/serialize copies by accessing 64-bit word-aligned arena buffers in place and transporting capabilities out of band. Cap'n Proto achieves **0 payload copies and 0 heap allocations** on read while defending against adversarial pointer graphs via `nestingLimit = 64`, relaxed-atomic `ReadLimiter` (`8 * 1024 * 1024` words = 64 MiB default), and `amplifiedRead` on zero-sized `INLINE_COMPOSITE` lists—at the cost of abandoning native language layouts. Fuchsia FIDL enforces single-pass canonical validation (zeroed padding, depth limit 32, 8-byte v2 envelopes) with kernel-enforced Zircon handle rights, and RFC-0126 exposes the sharp trade-off: skipping linearization via per-request `fdf::Arena` achieves in-process zero-copy only by introducing a **leaked-handles hazard** on unknown fields unless handles are still partially extracted.

| Dimension | WebAssembly Component Model (`WIT` / Canonical ABI) | GraalVM `Truffle` (`InteropLibrary`) | `ECMA-335` CLI (`.NET` CoreCLR) | `Cap'n Proto` / Fuchsia `FIDL` |
| --- | --- | --- | --- | --- |
| **Memory & Isolation** | Shared-nothing disjoint linear memories; SFI bounds; per-instance handle tables | Shared GC heap & JIT (fault isolation requires Polyglot Isolates) | Shared GC heap + CTS verification; P/Invoke exits to unmanaged heap | Segmented arenas (`Cap'n Proto`); `Zircon` channels or in-process `fdf::Arena` (`FIDL`) |
| **Boundary Protocol** | `WIT` algebraic values + `cabi_realloc` `lift`/`lower`; `own<T>`/`borrow<T>` u32 handles | Polymorphic `InteropLibrary` messages over `Object` + `@CachedLibrary` | Shared CTS types, CLS metadata subset, CIL bytecode | 64-bit word-aligned offsets + out-of-band capability/handle tables |
| **Bulk Transfer Cost** | $O(N)$ copy + UTF-8/UTF-16/`latin1+utf16` transcode (`1.0x–3.7x` R+W per hop) | $O(1)$ reference pass + JIT-inlined access (copy/pin on NFI) | $O(1)$ in CTS; copy/pin + 11-step GC frame on P/Invoke | $O(1)$ in-place (`Cap'n Proto`, `0` copies); linearized copy in `FIDL` channels (`0` in RFC-0126 arena) |
| **Lifetime & Capabilities** | Dynamic borrow counts (`num_lends`, `num_borrows`) trapping on escape/early drop | Tracing GC; no borrow revocation; manual `toNative` pinning | Tracing GC + post-ECMA-335 stack-only `ByRefLike` escape rules | `Cap'n Proto` RPC capability table; `FIDL` kernel `zx_obj_type_t` / `zx_rights_t` |
| **Primary Wall** | $O(N)$ copy/transcode cliff; no shared views in MVP; `WasmGC`/threads separate | Identity/null/numeric/thread clashes; warmup; isolates kill shared JIT | Affine lifetimes, HKT, dynamic prototypes, `tail.`/`byref` downgrades | Rigid wire layouts; DoS budgets (`ReadLimiter`) or handle-leak vs. zero-copy trade-off |

## Applicability

This report covers and cross-compares the 11 primary subjects recorded in `REPORT.json`:

- **WebAssembly Component Model stack**: normative `WIT`, `CanonicalABI`, `Binary`, `Concurrency`, and executable Python reference semantics in `WebAssembly/component-model` (`585526aa1f2c7f76f07557d16e265dede38b3acb`); `WasmGC` v1/Post-MVP in `WebAssembly/gc` (`756060f5816c7e2159f4817fbdee76cf52f9c923`); `WebAssembly/shared-everything-threads` (`de560922268ca89fd3303776c5c1b8f123da2aec`); and production runtime enforcement in `bytecodealliance/wasmtime` (`3ce2209872ccf1ea115914a81e020aef66a10c51`).
- **Shared-JIT polyglot VM stack**: Grimmer et al. (DLS 2015, `10.1145/2816707.2816714`; ACM TOPLAS 2018, `10.1145/3201898`) paired with `oracle/graal` (`3fd1dcaa85129cc6df8232487f9506d73787a755`: `InteropLibrary.java`, `TruffleLanguage.java`, `TruffleLibraries.md`, `NFI.md`, `Optimizing.md`, `llvm/Interoperability.md`, `embedding/embed-languages.md`).
- **Common Intermediate Language stack**: `ECMA-335` 6th Edition (June 2012, ISO/IEC 23271) paired with `dotnet/runtime` (`db341b0b461356d954079d27e86cb47c929e7e8a`: `Ecma-335-Augments.md`, `clr-abi.md`, `type-system.md`, and `src/coreclr/jit/morph.cpp`).
- **Zero-copy wire & capability IPC stack**: `capnproto/capnproto` (`20fe8fd325bf3825d6cdc3cf16bb263a4c142326`: `doc/encoding.md`, `c++/src/capnp/{layout.c++,arena.h,message.h}`) contrasted against Fuchsia's `FIDL` wire format specification (v2 envelopes), `RFC-0131`, and `RFC-0126`.

**Relationship to adjacent corpus packages**: Low-level SFI/LFI instruction sandboxing, `WaVe`, `Nebulet`, and ring-0 Wasm kernel isolation are documented in `modern-sfi-lfi-and-ring0-wasm-kernels-2020-2026`. This report complements that package without duplicating SFI/LFI codegen or Rust-specific native ABI tables, focusing strictly on N-to-N polyglot interop platforms above the sandbox/ISA boundary.

**Observation vs. broader generalization**: Normative rules, source invariants, and executable probe metrics hold verbatim for the pinned revisions above. Architectural trade-offs and contingency classifications are explicitly tagged `derived` with their supporting evidence.

## Findings

### 1. Structural Taxonomy: Four Vertices of the $O(N + M)$ Interop Space

Basis: normative + source + derived

Pairwise language bridges scale quadratically ($O(N \times M)$) in glue maintenance and semantic mismatch bugs. Each of the four industrial platforms reduces integration to $O(N + M)$ by standardizing a different boundary contract, exposing three irreducible design triangles (`derived` from Sections 2–5):

1. **Zero-Copy Shared Views vs. Relocating GC vs. Exclusive Aliasing**: In-place mutable sharing (`Truffle`, `CLR` CTS, `FIDL` `fdf::Arena`) collides with compacting GC (requiring pinning/write barriers as in CoreCLR P/Invoke and Truffle NFI `toNative`), exclusive linear aliasing (`WIT` `own<T>`, Rust `&mut T`), or cross-trust spatial isolation (disjoint Wasm linear memories).
2. **Cross-Boundary Optimization vs. Fault & Abstraction Isolation**: Eliminating call overhead requires exposing callee internals to the caller's optimizer (`Truffle` partial evaluation across `InteropLibrary`, `CLR` JIT inlining). Reclaiming strong fault isolation (`Wasm` components, `GraalVM` Polyglot Isolates, `Zircon` processes) breaks cross-boundary inlining and re-introduces value copying or handle indirection.
3. **Expressive Source Semantics vs. Universal ABI**: Rich shared type systems (`ECMA-335` CTS) excel for co-designed languages (`C#`, `F#`) but inflict impedance mismatches on orthogonal paradigms (affine lifetimes, dynamic prototypes, higher-kinded types). Minimal algebraic/wire interfaces (`WIT`, `Cap'n Proto`, `FIDL`) accept any language cleanly but force every language to abandon or copy out of its idiomatic in-memory representations.

**Historical contingencies vs. irreducible constraints (`derived`)**:
- *Historical contingencies* (refuted by contrasting precedents): NUL-terminated untyped `char*` C strings (refuted by length-prefixed UTF-8/UTF-16/compact strings in `WIT`, `FIDL`, and `TruffleString`); ambient pointer aliasing as the default FFI convention (refuted by `WIT` shared-nothing linear memories and `Zircon` out-of-band handle arrays); monolithic function-coloring async ABIs (refuted by the Component Model's decoupled `async` effect typing vs. sync/async lowering in `Concurrency.md`).
- *Irreducible constraints*: validating untrusted pointer-offset graphs in $O(1)$ per dereference without linearizing requires explicit depth and traversal budgets (`Cap'n Proto` `nestingLimit` + `ReadLimiter`) because relative offsets can encode cycles or $2^k$-amplified DAGs in $O(k)$ wire bytes; enforcing scoped borrow safety against untrusted guests lacking static lifetime checking requires dynamic tracking and trapping (`WIT` `num_lends`/`num_borrows`) because cross-boundary escape analysis is undecidable.

---

### 2. WebAssembly Component Model: Shared-Nothing Encapsulation, `WIT`, Canonical ABI, and Resource Handles

Basis: normative + source + execution

#### 2.1 Shared-Nothing Linear-Memory Encapsulation and `WIT` Algebraic Types

In `WebAssembly/component-model` (`WIT.md` L762–822, L1774–2008; `Explainer.md`), each `ComponentInstance` (`definitions.py` L190–206) encapsulates its own Core Wasm linear memory, handle table, and thread table. Components never pass raw linear-memory pointers across boundaries; instead, **WIT** defines a closed algebraic value universe:
- Primitives: `bool`, `s8`..`s64`, `u8`..`u64`, `f32`, `f64`, `char` (Unicode scalar value), `string`, and `error-context`.
- Named composites: `record`, `variant`, `enum`, `flags` (bit-packed integer words).
- Anonymous constructors: `tuple<...>`, `option<T>`, `result<T, E>`, `list<T>`, `stream<T>`, `future<T>`.
- Abstract capability types: `resource` items desugaring constructors (`%[constructor]R`), statics (`%[static]R.f`), methods (`%[method]R.m` taking implicit `self: borrow<R>`), and getters/setters (`WIT.md` L1808–1839), passed solely as owned (`R` / `own<R>`) or borrowed (`borrow<R>`) 32-bit handle indices.

#### 2.2 The Canonical ABI `lift`/`lower` and `cabi_realloc` Protocol

Core WebAssembly functions only accept scalar parameters and results; the Canonical ABI (`CanonicalABI.md`; `definitions.py`) mediates WIT values via `canon lift` and `canon lower`:
- **Flat spilling limits** (`definitions.py` L1767–1769; `CanonicalABI.md` L2880–2908): `MAX_FLAT_PARAMS = 16` (sync), `MAX_FLAT_ASYNC_PARAMS = 4` (async lower), and `MAX_FLAT_RESULTS = 1`. Exceeding these limits spills values into linear memory via an extra pointer argument or caller-allocated retptr.
- **Length caps** (`definitions.py` L645, L870, L1349, L1387): `Table.MAX_LENGTH = Buffer.MAX_LENGTH = MAX_STRING_BYTE_LENGTH = MAX_LIST_BYTE_LENGTH = (1 << 28) - 1` (~256 MiB), guaranteeing `2 * MAX_STRING_BYTE_LENGTH < REALLOC_I32_MAX` (`2**32 - 1`) so UTF-8-to-UTF-16 over-allocation cannot overflow 32-bit `realloc` sizes.
- **`cabi_realloc` and the `may_leave` reentrancy guard** (`definitions.py` L614–635, L2110–2113): Lowering dynamic payloads (`string`, `list<T>`) invokes the target's `cabi_realloc(old, old_byte_length, alignment, new_byte_length) -> ptr` while setting `self.inst.may_leave = False` (also cleared across `post-return`). Every canonical built-in (`canon_lower`, `canon_resource_{new,drop}`, `canon_task_return`, `canon_stream_*`, `canon_waitable_*`) executes `trap_if(not inst.may_leave)`, preventing a guest allocator from reentrantly calling imports or mutating handle tables mid-marshaling. Misaligned or out-of-bounds return pointers trap immediately (`L630–631`).
- **Value canonicalization** (`definitions.py` L1299–1338): `char` traps on surrogate range `0xD800..0xDFFF` or `> 0x10FFFF`; floats canonicalize NaN payloads (`canonicalize_nan32`/`64`), stripping NaN-boxing tags at component boundaries.

#### 2.3 Dynamic Capability Resource Handle Tables (`own<T>` / `borrow<T>`)

To guarantee temporal safety for stateful capabilities across untrusted guests without static borrow checkers, the Component Model combines static binary validation (`Binary.md` L255–263) with per-instance runtime handle tables (`definitions.py` L641–703, L809–865, L1440–1454, L1731–1748, L2254–2293). Slot `0` of every `Table` is permanently `None`; each live entry holds `ResourceHandle(rt, rep_val, own, borrow_scope, num_lends)`:

| Operation | Normative Rule (`definitions.py` / `Binary.md`) | Wasmtime Enforcement (`handle_table.rs` / `resources.rs`) | Trap / Validation Failure |
| --- | --- | --- | --- |
| **Static type check** | `Binary.md` L257–263: `contains_borrow(t)` forbidden in function results, exported value types, `stream<T>`, `future<T>` | Component validation (`crates/environ/src/component/translate.rs`) | Static binary validation error |
| **`canon resource.new`** | `inst.may_leave == True`; defining instance `rt.impl_inst` only | `ResourceTables::resource_new` (`resources.rs` L195) | Traps if `may_leave == False` or table full |
| **`lift_own(i)`** | `handles.remove(i)`; `h.rt is ownt.rt`; `h.own == True`; `h.num_lends == 0` (`L1440–1446`) | `resource_lift_own` (`resources.rs` L252–256); `remove_resource` (`handle_table.rs` L298–323) | `"cannot lift own resource from a borrow"` / `"cannot remove owned resource while borrowed"` |
| **`lift_borrow(i)`** | `handles.get(i)` (`own` or `borrow`); `subtask.add_lender(h)` increments `h.num_lends += 1` (`L1448–1454`, L841–844) | `resource_lift_borrow` (`resources.rs` L309–321); `resource_lend` (`handle_table.rs` L224–273) | Traps on `lend_count` overflow (`checked_add(1)`) or store handle cap |
| **`lower_borrow(rep)`** | If `cx.inst is rt.impl_inst` (`pass_rep_not_handle`, `L1202`), pass raw `rep_val`; else allocate borrow entry & `task.num_borrows += 1` (`L1738–1748`) | `resource_transfer_borrow_to_owner` (`libcalls.rs` L671) vs. `resource_lower_borrow` (`resources.rs` L410) | Zero table overhead for calls targeting the defining component |
| **`canon resource.drop`** | `inst.may_leave == True`; `h.num_lends == 0`; if `own`, run `rt.dtor` in `rt.impl_inst`; if borrow, `borrow_scope.num_borrows -= 1` (`L2263–2283`) | `HandleTable::remove_resource` (`handle_table.rs` L298–323) | `"cannot remove owned resource while borrowed"` / `"cannot remove borrowed resource while it is lent out"` |
| **`Task.return_` / `cancel`** | `task.num_borrows == 0` (`L476–487`); caller's `Subtask.deliver_resolve()` decrements `h.num_lends -= 1` (`L853–857`) | `ResourceTables::validate_scope_exit` (`resources.rs` L424–435) | `"borrow handles still remain at the end of the call"` |

**Wasmtime runtime optimizations (`source`)**: In `handle_table.rs` (L23–38), `VMHandleTableSlot::ResourceOwn` and `ResourceBorrow` place `lend_count` at an identical struct offset (verified by `lend_count_offset_is_variant_agnostic`). For `component-model-async` deferred threads, `resources.rs` (L326–395) buffers lends in `lazy_lenders` via `resource_lift_borrow_lazy`, deferring `lend_count` mutations unless thread suspension invokes atomic `promote_lazy_lends`.

**Executable verification (`support/verify_wit_canonical_abi_and_resources.py`)**: All 10 state-machine checks passed deterministically: static rejection of `borrow<T>` in return types and `stream<borrow<T>>` (`A1`/`A1b`), `UNRELEASED_BORROW` trap on undropped borrow at return (`A2`), `OWN_STILL_BORROWED` trap on drop (`A3`) or ownership transfer (`A4a`) while lent, `LIFT_OWN_FROM_BORROW` (`A4b`), `BORROW_STILL_LENT` on intermediate drop of a re-lent borrow (`A5`), zero-handle `pass_rep_not_handle` delivery (`A6`, `rep=0xcafe, num_borrows=0`), exact single destructor + double-drop trap (`A7`), `CANNOT_LEAVE` trap inside reentrant `cabi_realloc` (`A8`), and `INVALID_UNICODE` trap on lone UTF-16 surrogates (`A9`).

#### 2.4 The $O(N)$ String Transcoding and Byte-Copy Amplification Cliff

Every `string` and `list<T>` crossing disjoint linear memories incurs full $O(N)$ validation and copying (`definitions.py` L1352–1408, L1548–1696; `wasmtime` `func/typed.rs` L1371–1424, `libcalls.rs` L186–555). To bridge UTF-8, UTF-16, and compact Latin-1/UTF-16 runtimes, components select `utf8`, `utf16`, or `latin1+utf16` (using `UTF16_TAG = 1 << 31` on memory32 / `1 << 63` on memory64, `definitions.py` L1345–1370).

Because `cabi_realloc` must allocate guest memory *before* transcoding in a single source pass, mismatched encodings trigger optimistic-alloc + grow + shrink churn (`definitions.py` L1598–1671):
- `utf8 -> utf16` (`store_utf8_to_utf16`): allocates worst-case `2 * src_bytes`, writes UTF-16LE, then shrinks via a 2nd `cabi_realloc` whenever multi-byte UTF-8 characters occurred.
- `utf16 -> utf8` (`store_utf16_to_utf8`): allocates `src_code_units` optimistically; on the first non-ASCII scalar (`>= 0x80`), grows via a 2nd `cabi_realloc` to worst-case `3 * src_code_units` (copying the ASCII prefix), writes the remainder, and shrinks via a 3rd `cabi_realloc`.
- `utf8 -> latin1+utf16` (`store_string_to_latin1_or_utf16`): allocates `src_code_units` (align 2), writes Latin-1 bytes until hitting any scalar `>= 0x100`, grows via a 2nd `cabi_realloc` to `2 * src_code_units`, widens the Latin-1 prefix **backward in place** to UTF-16LE, writes the tail, sets `UTF16_TAG`, and shrinks via a 3rd `cabi_realloc`.

Observed copy and allocation amplification from executing `support/verify_wit_canonical_abi_and_resources.py`:

| Workload | Crossing | Src (B) | Dst Written (B) | Peak Alloc (B) | Final Alloc (B) | `realloc` Calls | Write Amp | Total R+W Amp | Peak/Final |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ascii_4096B` (`"A"*4096`) | `utf8 -> utf8` | 4,096 | 4,096 | 4,096 | 4,096 | 1 | 1.000x | 2.000x | 1.000x |
| `ascii_4096B` | `utf8 -> utf16` | 4,096 | 8,192 | 8,192 | 8,192 | 1 | 2.000x | 3.000x | 1.000x |
| `ascii_4096B` | `utf16 -> utf8` | 8,192 | 4,096 | 4,096 | 4,096 | 1 | 0.500x | 1.500x | 1.000x |
| `ascii_4096B` | `utf8 -> latin1+utf16` | 4,096 | 4,096 | 4,096 | 4,096 | 1 | 1.000x | 2.000x | 1.000x |
| `mixed_latin1_plus_cjk_1024cp` (`"café"*200+"漢"*224`) | `utf8 -> utf8` | 1,672 | 1,672 | 1,672 | 1,672 | 1 | 1.000x | 2.000x | 1.000x |
| `mixed_latin1_plus_cjk_1024cp` | `utf8 -> utf16` | 1,672 | 2,048 | 3,344 | 2,048 | 2 | 1.225x | 2.225x | 1.633x |
| `mixed_latin1_plus_cjk_1024cp` | `utf16 -> utf8` | 2,048 | 2,696 | 3,072 | 1,672 | 3 | 1.316x | 2.316x | 1.837x |
| `mixed_latin1_plus_cjk_1024cp` | `utf8 -> latin1+utf16` | 1,672 | 4,520 | 3,344 | 2,048 | 3 | **2.703x** | **3.703x** | 1.633x |
| `emoji_4byte_512cp` (`"🚀"*512`) | `utf16 -> utf8` | 2,048 | 3,072 | 3,072 | 2,048 | 3 | 1.500x | 2.500x | 1.500x |
| `emoji_4byte_512cp` | `utf8 -> latin1+utf16` | 2,048 | 4,096 | 4,096 | 2,048 | 3 | 2.000x | 3.000x | 2.000x |
| **4-hop alternating pipeline** (4,096 B ASCII) | `u8->u16->u8->u16->u8` | 4,096 | — | — | — | 4 | — | **12.000x** (49,152 B) | — |

In addition, WIT `string` requires valid Unicode scalar values (`load_string_from_range` traps on `UnicodeError`, `definitions.py` L1375–1378), so WTF-16 strings with lone surrogates from JS/Java/Win32 cannot pass through `string` without lossy replacement or `list<u16>` tunneling. Even when `wasmtime` uses `encoding_rs` SIMD helpers for host-to-guest `latin1+utf16` (`func/typed.rs` L1381–1386), guest linear-memory allocation and byte copying remain mandatory.

#### 2.5 Interaction with `WasmGC`, `shared-everything-threads`, and WASI 0.3 Async Concurrency

- **`WasmGC` (`WebAssembly/gc` `MVP.md` L26–145, L230–360)**: Defines three disjoint reference hierarchies (*Internal* `any` > `eq` > `{struct, array, i31}` > `none`; *External* `extern` > `noextern`; *Functions* `func` > `nofunc`) and higher-kinded iso-recursive `rec` groups whose tied back-edges (`rec.i`) admit $O(1)$ canonicalized equivalence and nominal-modulo-canonicalization `sub final?` single inheritance (`L241–322`). However, the Component Model Canonical ABI currently operates strictly on 32/64-bit linear memory (`CanonicalABI.md` L1431, L4936, L5029); zero-copy `WasmGC` struct/array interop awaits a future GC ABI canonical option (`WebAssembly/component-model` issue `#525`).
- **`shared-everything-threads` (`WebAssembly/shared-everything-threads` `Overview.md` L39–112)**: Standard Wasm threads allow only `shared` linear memory, leaving `WasmGC` strictly single-threaded (`L41–42`). This proposal adds `shared` annotations to tables, globals, functions, and GC heap types under an asymmetric rule: **non-shared items may reference `shared` items, but `shared` items can never reference non-shared items** (`L98–106`).
- **WASI 0.3 Async `stream<T>`, `future<T>`, and Stack Switching (`Concurrency.md` L9–119; `definitions.py` L869–1019, L2093–2251)**: Decoupling the WIT `async` effect from the Core Wasm lift/lower ABI avoids function coloring: an `async` export can be lowered synchronously, via `async + callback` (`CallbackCode::{EXIT=0, YIELD=1, WAIT=2}` packed with a 28-bit `WaitableSet` handle at `definitions.py` L2164–2176, releasing `exclusive_thread` while suspended), or stackfully. Crucially, `ReadableGuestBuffer.read`, `WritableGuestBuffer.write`, and `End.copy` (`definitions.py` L901–964) show that **`stream<T>` and `future<T>` still perform element-wise `load_list_from_valid_range` / `store_list_into_valid_range` copies between disjoint linear memories**—eliminating whole-message buffering and enabling backpressure, cancellation, and zero-copy relay splicing via `End.forward` (`L984–1000`), but **not** eliminating endpoint-to-endpoint linear memory copies.

---

### 3. GraalVM Truffle Polyglot VM: Partial Evaluation, `InteropLibrary`, and Shared-Heap Walls

Basis: documentation + source + derived

#### 3.1 Shared-JIT Compilation via Partial Evaluation and `InteropLibrary`

Grimmer et al. (DLS 2015; ACM TOPLAS 2018) and `oracle/graal` run multiple guest interpreters (`GraalJS`, `GraalPy`, `TruffleRuby`, `FastR`, `Sulong` LLVM bitcode, `Espresso`) on one shared JVM/Native Image heap compiled by one Graal JIT. Cross-language operations dispatch through **Truffle Libraries** (`truffle/docs/TruffleLibraries.md`; `InteropLibrary.java`), specializing polymorphic inline caches (`@CachedLibrary(limit = "...")`) on concrete receiver classes for uniform messages (`readMember`, `invokeMember`, `execute`, `readArrayElement`, `readBuffer*`, `asTruffleString`, `asPointer`). When Graal partially evaluates a hot caller loop, it folds caller AST, cached `InteropLibrary` dispatch, and foreign callee AST into **one native JIT compilation unit**, letting escape analysis eliminate transient wrappers and achieve zero-copy cross-language inlining.

**Compilation walls (`Optimizing.md`, `embed-languages.md`)**: Exceeding `@CachedLibrary` specialization limits falls back to uncached megamorphic dispatch (`InteropLibrary.getUncached`), breaking inlining; unstable receiver profiles induce deoptimization cycles (`Optimizing.md` L684–862); `@TruffleBoundary` annotations block partial evaluation (`L874–920`); and running on vanilla Oracle JDK / OpenJDK without Graal's JVMCI optimizing runtime silently degrades to **interpreter-only fallback** (`embed-languages.md` L407–465) unless guest languages execute inside Native Image Polyglot Isolates.

#### 3.2 Object-Identity Schizophrenia and Symmetric Double-Dispatch `isIdentical`

Even on a shared heap, language wrappers, `HostObject` membranes, and polyglot `Value` proxies create **object-identity schizophrenia**: if the same entity crosses into a foreign language under two wrapper allocations, raw Java `==` breaks `===`/`is`/`WeakMap` invariants. `InteropLibrary.java` (L2912–3045) mitigates this via symmetric double dispatch over `TriState`:

```java
public boolean isIdentical(Object receiver, Object other, InteropLibrary otherInterop) {
    TriState result = this.isIdenticalOrUndefined(receiver, other);
    if (result == TriState.UNDEFINED) {
        result = otherInterop.isIdenticalOrUndefined(other, receiver);
    }
    return result == TriState.TRUE;
}
```

As `InteropLibrary.java` L2926–2959 explicitly cautions, two fractures persist: (1) interop identity is **non-reflexive** for primitive/value types (Java `Integer` cannot expose interop identity against boxed guest numbers without violating symmetry), forcing every guest language to combine custom language-level equality with `isIdentical`; and (2) any forwarding proxy that fails to override `isIdentical` (delegating to its target) and keep `identityHashCode` consistent re-introduces identity splits in cross-language sets and maps.

#### 3.3 Semantic Collisions Across Null, Numerics, Meta-Objects, and Thread Safety

| Semantic Axis | `InteropLibrary` / Truffle Mechanism | Structural Clash Across Languages |
| --- | --- | --- |
| **Null / Bottom** | Single `isNull(Object)` (`InteropLibrary.java` L206–215) | Collapses JS `null` and `undefined`, Python `None`, Ruby `nil`, and Java `null` into one predicate, erasing distinct falsiness and `typeof` semantics. |
| **Numeric Tower** | `isNumber` + `fitsIn{Byte,Short,Int,Long,BigInteger,Float,Double}` (`L429–670`) | Forces dynamic range/precision probing across JS `f64` ($2^{53}-1$ integer ceiling), Java signed fixed-width primitives, and Python/Ruby arbitrary-precision integers. |
| **Meta-Objects** | `hasMetaObject`, `getMetaObject`, `isMetaInstance` (`L5339–5533`) | Nominal JVM `Class<?>` hierarchies clash with mutable JS prototypes and Python/Ruby metaclasses; `isMetaInstance` is purely dynamic. |
| **Thread Safety** | `TruffleLanguage.isThreadAccessAllowed(Thread, boolean singleThreaded)` (`TruffleLanguage.java` L1318–1327) | Defaults to `return singleThreaded`, and requires **every** initialized language in a `Context` to allow multi-threading before `initializeMultiThreading` is invoked. Including a single-threaded language (e.g., JS) serializes concurrent access across the entire shared polyglot `Context`. |

#### 3.4 Native C Extensions (`Sulong` vs. Truffle NFI) and the Polyglot Isolate Reversal

- **`Sulong` LLVM Runtime (`docs/reference-manual/llvm/Interoperability.md`)**: Compiles C/C++ into LLVM bitcode with mandatory DWARF debug info (`clang -shared ... -lgraalvm-llvm`) and `<graalvm/llvm/polyglot.h>` (`POLYGLOT_DECLARE_STRUCT`), allowing JS/Ruby/Python to access C struct fields (`point.x = 5`) and pass JS objects directly to C functions (`cpart.printPoint({x: 17, y: 42})`) inside the same JIT unit. Costs: mandatory bitcode recompilation, restricted inline assembly/raw syscalls, and JIT warmup/memory footprint.
- **Truffle NFI (`truffle/docs/NFI.md`)**: Bridges pre-compiled native libraries via `libffi` (JNI on HotSpot, system Java on Native Image, or Panama), typing signatures with `POINTER`, `STRING`, `OBJECT`, `[UINT8]`, and `ENV`. Managed objects must transition through `InteropLibrary.toNative` / `asPointer` (`InteropLibrary.java` L1864–1879), restoring opaque FFI marshaling/pinning and forfeiting cross-language inlining.
- **Polyglot Isolates (`embed-languages.md` L503–565)**: Available in Oracle GraalVM 23.1+ and GraalVM CE 25.1+, Polyglot Isolates run each guest engine in a separate Native Image VM fault domain with its own GC and JIT for sandboxing—demonstrating (`derived`) that reclaiming untrusted isolation from a shared-heap VM forces re-erecting a heap/serialization boundary and giving up direct shared-heap inlining.

---

### 4. Common Intermediate Language Platforms (`ECMA-335` CLI / .NET CoreCLR)

Basis: normative + documentation + source + derived

#### 4.1 Architectural Successes: CTS, Value Types, Reified Generics, and CLS Subsetting

`ECMA-335` 6th Edition (June 2012, ISO/IEC 23271) delivered zero-marshaling interop among CLR-native languages (`C#`, `F#`, `VB.NET`) through four design pillars:
- **Unboxed value types alongside self-typing objects** (`§I.8`, p. 16): Distinguishes identity-bearing heap objects from flat bit-pattern values (`struct`), avoiding mandatory heap boxing for composites.
- **Reified generics with dual compilation** (`§I.8`, pp. 16–17; `clr-abi.md` L88–100): Statically verifiable at definition time; CoreCLR specializes native code per value-type argument (unboxed, cast-free) while sharing code across reference-type arguments via a hidden generic dictionary parameter.
- **Safe declaration-site variance** (`§I.8`, p. 17): Restricted to generic interfaces and delegates, avoiding covariant mutable array soundness holes.
- **Boundary-only CLS subsetting** (`§I.7.3`, Rules 1–2, pp. 14–15): Constrains only externally visible assembly APIs (unless marked `[CLSCompliant(false)]`), leaving internal implementation unconstrained.

#### 4.2 Impedance Mismatches for Non-CLR Languages

Languages whose semantics diverge from traced, nominal, single-inheritance OOP encounter four hard CLI boundaries:

1. **Unmanaged & Affine Lifetimes vs. Managed Pointers (`Ecma-335-Augments.md` L991–1088, L1183–1223)**: Normative `ECMA-335 §I.8.2.1.1` forbade `byref` (`T&`) managed pointers in struct fields, array elements, and generic arguments. Supporting safe zero-copy `Span<T>` required major CoreCLR post-standard addenda—**Ref Fields** (stack-only `ByRefLike` structs with `III.1.7.7.1` escape rules), **ByRefLike types in generics** (`gpAllowByRefLike`), and **Extended Layout**. Even with these augments, the VES lacks affine ownership and deterministic destruction: `C++/CLI` bridges native RAII and managed code only via mixed-mode "It Just Works" (IJW) assemblies embedding native machine instructions alongside CIL (tying binaries to Windows/platform ABIs), while Rust-to-CIL backends (`rustc_codegen_clr`) must lower Rust borrows into unsafe unmanaged pointers, forfeiting CIL verification.
2. **P/Invoke GC-Transition Cost (`clr-abi.md` L177–230)**: Unless explicitly opted out (`SuppressGCTransition`), every native P/Invoke call executes an **11-step transition**: pushing an `InlinedCallFrame` onto `Thread->m_pFrame`, setting `m_pCallerReturnAddress`, clearing `Thread->m_fPreemptiveGCDisabled = 0`, killing all live GC refs in registers (`RefTypeKillGCRefs`), calling native code, restoring `m_fPreemptiveGCDisabled = 1`, polling `g_TrapReturningThreads` (`CORINFO_HELP_STOP_FOR_GC`), and popping the frame chain—plus IL-stub marshaling copies for non-blittable types and UTF-16/UTF-8 strings.
3. **Tail-Call Exclusions (`ECMA-335 §III.2.4`; CoreCLR `src/coreclr/jit/morph.cpp` L4112–4317)**: Although CIL specifies the `tail.` prefix, `§III.2.4` prohibits verifiable `tail.` calls inside `try`/`catch`/`filter`/`finally` regions or with escaping local managed pointers. In CoreCLR RyuJIT, `Compiler::fgCanFastTailCall` (`morph.cpp` L4112–4317) rejects fast native `jmp` tail calls whenever `"Callee has a byref parameter"` (`L4308`), `"Localloc used"` (`L4266`), `"Callee has RetBuf but caller does not."` (`L4283`), `"Not enough incoming arg space"` (`L4298`), `"Not enough registers available due to the GS security cookie check"` (`L4220`), or Windows ARM/ARM64 varargs (`L4260`) apply—downgrading functional languages (`F#`, Scheme, ML) to slower helper trampolines (`fgMorphTailCallViaHelpers` / `fgMorphTailCallViaJitHelper`, `L4927–5928`), while P/Invoke IL stubs do not support tail calls at all (`clr-abi.md` L229).
4. **Dynamic Prototypes and Higher-Kinded Polymorphism**: Dynamic languages (`IronPython`) must layer a secondary DLR (`CallSite` dynamic IL codegen) over rigid nominal `MethodDesc` dispatch (`method-descriptor.md`), and CTS generics only quantify over kind `*`, forcing Haskell/Scala higher-kinded type constructors (`F<_>`) into boxed defunctionalized witness encodings.

---

### 5. Zero-Copy Wire Schemas and Capability IPC Bridges: Cap'n Proto and Fuchsia FIDL

Basis: normative + documentation + source + execution

#### 5.1 Cap'n Proto In-Place Word-Offset Wire Format and Capability Tables

Cap'n Proto (`capnproto/capnproto`, `doc/encoding.md` L10–277) makes the 64-bit little-endian word-aligned wire format identical to the reader's in-memory layout:
- **Split-section structs & segmented arenas**: Messages span one or more flat segments; word 0 of segment 0 is the root struct pointer. Every struct stores its naturally aligned **data section** (with 1-bit packed `Bool`s and 16-bit enums) directly before its **pointer section**, enabling schema-agnostic traversal (`encoding.md` L89–91).
- **Four 64-bit pointer words** (`encoding.md` L93–270): `Struct` (`A=0`, 30-bit signed word offset `B`, 16-bit `dataSize`, 16-bit `ptrCount`); `List` (`A=1`, 30-bit offset `B`, 3-bit `elementSize` including `INLINE_COMPOSITE=7` with a leading `Struct` tag word, 29-bit count/words); `Far` (`A=2`, 1-bit `doubleFar`, 29-bit landing-pad offset, 32-bit `segmentId`, `layout.c++` L584–616); and `Capability` (`A=3, B=0`, 32-bit index `C` into an out-of-band per-message capability table, `layout.c++` L2118–2139).
- **Zero-copy verification (`support/verify_wit_canonical_abi_and_resources.py`)**: Reading a root struct plus 4,096-byte list from a segment arena performed **0 payload bytes copied** and **0 heap allocations** (`514` words billed to `ReadLimiter`), vs. `8,192–12,288` R+W bytes per single hop and `49,152` R+W bytes across 4 hops in the Component Model Canonical ABI. The price is **native layout lock-in** (abandoning idiomatic `Vec`/GC layouts or paying a builder copy) plus NUL-terminated `Text` caveats (`encoding.md` L79–85).

#### 5.2 Cap'n Proto Adversarial DoS Invariants (`nestingLimit`, `ReadLimiter`, `amplifiedRead`)

Untrusted relative word offsets can violate Cap'n Proto's tree invariant via cycles, overlapping exponential DAGs, or zero-sized lists. Cap'n Proto defends readers in $O(1)$ per dereference without visited-set allocation (`message.h` L51–75; `arena.h` L62–96, L416–429; `layout.c++` L455–464, L2075–2270):
1. **Segment bounds (`SegmentReader::checkObject`, `arena.h` L416–425)**: Verifies `startOffset + size <= segment_words` and deducts `size` from `readLimiter->canRead(size, arena)`.
2. **Cycle cutoff (`nestingLimit = 64`, `message.h` L75; `layout.c++` L2091, L2167)**: Every pointer dereference requires `nestingLimit > 0` and passes `nestingLimit - 1`.
3. **DAG amplification cutoff (`ReadLimiter`, default `traversalLimitInWords = 8 * 1024 * 1024` = 64 MiB, `message.h` L54; `arena.h` L62–96)**: Relaxed-atomic cumulative word counter aborts overlapping DAG expansion deterministically, intentionally trading exactness (repeated benign getter calls double-count unless callers invoke `unread()`) for zero per-read allocation.
4. **Zero-sized list defense (`amplifiedRead`, `layout.c++` L2203–2208, L2268; `arena.h` L427–429)**: Whenever an `INLINE_COMPOSITE` list has `wordsPerElement == 0` (or `elementSize == VOID`), `amplifiedRead` bills 1 virtual word per claimed element, defeating 16-byte lists claiming $10^7$ zero-sized structs.

Verified execution receipts from `support/verify_wit_canonical_abi_and_resources.py`:

| Adversarial Probe | Wire Size | Logical Expansion / Target | Triggered Defense | Verified Error |
| --- | ---: | --- | --- | --- |
| `B1` Self-referential struct cycle (`offset = -1`) | 16 B | $\infty$ depth | `nestingLimit = 64` | `[NESTING_LIMIT_EXCEEDED]` |
| `B2` 24-level overlapping binary DAG bomb | 400 B | $2^{24} = 16,777,216$ leaves | `ReadLimiter` (16,384-word test budget) | `[TRAVERSAL_LIMIT_EXCEEDED]` at 16,384 words |
| `B3` Zero-sized `INLINE_COMPOSITE` struct list | 16 B | `10,000,000` elements | `amplifiedRead` vs. 8,388,608-word default | `[TRAVERSAL_LIMIT_EXCEEDED]` immediately |
| `B4a` / `B4b` OOB struct / unknown `Far` seg `99` | 8 B | Out-of-bounds / missing segment | `boundsCheck` / `tryGetSegment` | `[OUT_OF_BOUNDS]` / `[UNKNOWN_SEGMENT]` |

#### 5.3 Fuchsia FIDL: Linearized Canonical Wire Format, Zircon Handle Rights, and RFC-0126

Fuchsia's **FIDL** (`wire-format` spec, `RFC-0131`, `RFC-0126`) combines strict canonical validation with OS-kernel capability transport:
- **Canonical depth-first linearization (`wire-format` §Core Concepts / §Details; `RFC-0131` §Design)**: An 8-byte-aligned primary object followed by 8-byte-aligned secondary objects in fixed depth-first traversal order enables single-pass, zero-allocation validation that rules out cycles, pointer aliasing bombs, and trailing junk by construction. All padding bytes **must be zero**, UTF-8 is strictly validated, and **maximum recursion depth is capped at 32 indirections** (1 inline object + 32 out-of-line levels = 33 total, `wire-format` §Maximum Recursion Depth).
- **8-byte v2 envelopes & out-of-band Zircon handles (`wire-format` §Handles / §Envelopes)**: Tables and unions use 8-byte envelopes (bit 0 flags inline payloads $\le 4$ bytes vs. out-of-line payloads carrying 8-byte-aligned `num_bytes` and `num_handles` so receivers can skip unknown fields and close unknown handles). On the wire, 32-bit handle slots hold only `0` or `UINT32_MAX` (`0xFFFFFFFF`); actual handles travel out of band via `zx_channel_write()`, with Zircon enforcing unforgeable `zx_obj_type_t` and monotonic `zx_rights_t` attenuation in the kernel.
- **The RFC-0126 Driver Runtime zero-copy dilemma (`RFC-0126` §Per Request arena / §Linearization)**: Channel IPC incurs linearization plus two kernel copies. RFC-0126 introduces in-process per-request **`fdf::Arena`** ownership transfer to skip linearization—but explicitly identifies three walls: (1) **leaked handles** inside unknown union/table fields when encode no longer extracts handles into a flat handle array (requiring "partial encode/decode" handle extraction to mitigate); (2) extra transformer burden across wire-format migrations; and (3) **binding asymmetry**, where only wire-layout-native `LLCPP` bindings avoid copying while higher-level bindings still linearize.

---

### 6. Comparative Synthesis and Architectural Design Rules

Basis: derived (from Sections 2–5)

| Target Workload & Trust Model | Best-Fit Paradigm | Why Alternatives Fail |
| --- | --- | --- |
| **Untrusted multi-language plugins, sandboxed cloud/edge composition, deterministic teardown** | **WebAssembly Component Model (`WIT` + Canonical ABI)** | Truffle shared heap lacks fault isolation (Isolates restore copy boundaries); CLR CTS lacks affine borrow revocation; Cap'n Proto has no dynamic `borrow<T>` traps. |
| **High-frequency fine-grained polyglot compute in one trusted fault domain** | **GraalVM `Truffle` (`InteropLibrary`)** | Component Model hits $O(N)$ `cabi_realloc` copy/transcode cliffs; Cap'n Proto/FIDL enforce rigid wire layouts and prevent cross-language inlining. |
| **Tightly coupled statically typed managed ecosystem sharing one GC and generics** | **`ECMA-335` CLI / CoreCLR (with `ByRefLike` augments)** | Component Model lacks generics and shared GC graphs in MVP; Truffle forfeits static metadata verification. |
| **Bulk structured payloads, cross-process capability IPC, driver zero-copy transport** | **`Cap'n Proto` arenas or `FIDL` channels + RFC-0126 arenas** | Component Model streams still copy element-wise across linear memories; Truffle/CLR cannot span OS address spaces without serialization. |

**Convergence frontier (`derived`)**: Across all four stacks, three architectural principles emerge: (1) treat **trust and memory domains as first-class boundary tiers** (inlining across mutually trusted/verified modules; synthesizing capability handle tables or arena views at untrusted edges); (2) close WebAssembly's copy cliff by composing `WasmGC`, `shared-everything-threads`, and the future Component Model GC ABI so immutable graphs cross boundaries by unforgeable reference; and (3) **separate unforgeable capabilities from mutable payload bytes** (`WIT` handle tables, `Cap'n Proto` capability tables, `FIDL` out-of-band Zircon handle arrays and RFC-0126 partial handle extraction all converge on this invariant).

## Boundaries

- **not examined**:
  - Wall-clock CPU microbenchmarks on compiled `wasmtime`, `GraalVM`, `CoreCLR`, `capnp`, or Zircon binaries; quantitative copy-amplification and DoS-rejection figures come from deterministic execution of the spec-faithful Python model in `support/verify_wit_canonical_abi_and_resources.py`.
  - Pairwise or single-ecosystem FFI bridges outside the four N-to-N platforms examined here (`JNI`, `Java FFM`, `PyO3`, `Swift` Value Witness Tables, `Apache Arrow`, `FlatBuffers`, `COM`/`WinRT`, `GObject`, `D-Bus`).
  - Low-level SFI/LFI instruction sandboxing and ring-0 Wasm kernel isolation (covered in `modern-sfi-lfi-and-ring0-wasm-kernels-2020-2026`).
  - Non-C++ Cap'n Proto runtimes (`capnproto-rust`) and non-CoreCLR CLI backends (Mono, NativeAOT tail-call codegen).
- **unknown**:
  - Final normative semantics and zero-copy scope of the WebAssembly Component Model **GC ABI canonical option** (`WebAssembly/component-model` issue `#525`) and its composition with `shared-everything-threads` (both unstandardized at the examined commits).
  - Production deployment status of Fuchsia RFC-0126's non-linearized arena path and partial handle extraction in Rust FIDL driver bindings beyond LLCPP.
  - Comparative warmup and memory-footprint curves of GraalVM 25 CE vs. Oracle GraalVM 25 Polyglot Isolates across multi-language workloads.
- **known not to apply**:
  - Component Model linear-memory `cabi_realloc` copy/transcode amplification does **not** apply to host-virtualized intrinsics or same-defining-instance `borrow<T>` dispatch (`pass_rep_not_handle` passes the raw representation integer with zero handle-table entry).
  - Truffle cross-language JIT inlining does **not** apply under the fallback interpreter runtime (vanilla JDK without JVMCI) or across separate **Polyglot Isolate** boundaries (`embed-languages.md` L407–564).
  - Cap'n Proto's `ReadLimiter` does **not** perform exact graph-overlap detection; repeated benign getter calls on one sub-struct double-count against `traversalLimitInWords` unless callers call `unread()` (`arena.h` L72–91).
- **unsupported**:
  - Component Model binary validation **statically forbids** transitive `borrow<T>` in function results, exported value types, `stream<T>`, and `future<T>` (`Binary.md` L257–263).
  - `WasmGC` v1 MVP does **not** allow sharing GC references across threads (`shared-everything-threads/Overview.md` L41–42).
  - Normative `ECMA-335` 6th Edition (without CoreCLR `Ecma-335-Augments.md`) does **not** allow `byref` struct fields or `ByRefLike` generic arguments (`§I.8.2.1.1`).
  - Truffle does **not** permit concurrent multi-threaded execution inside a `Context` if any initialized language returns `false` from `TruffleLanguage.isThreadAccessAllowed(thread, /*singleThreaded=*/false)` (`TruffleLanguage.java` L1318–1327).

## Evidence

### 1. Primary Specifications, Source Revisions, and Papers (Observed 2026-11-19)

1. **`WebAssembly/component-model`** @ `585526aa1f2c7f76f07557d16e265dede38b3acb`:
   - `design/mvp/WIT.md` (L762–822, L1774–1839, L1976–2008); `design/mvp/Binary.md` (L212, L255–263); `design/mvp/CanonicalABI.md` (L71–80, L999–1015, L1431, L2200–2687, L2880–2908, L4936, L5029); `design/mvp/Concurrency.md` (L9–119).
   - `design/mvp/canonical-abi/definitions.py`: L190–206 (`ComponentInstance`), L392–487 (`Task`), L598–635 (`LiftLowerContext.reallocate`, `may_leave`), L641–703 (`Table`, `ResourceHandle`), L809–865 (`Subtask`), L869–1019 (`GuestBuffer`, `End.{copy,forward}`), L1106–1129 (`contains_borrow`), L1202–1203 (`pass_rep_not_handle`), L1345–1388 (`load_string_from_range`), L1440–1454 (`lift_{own,borrow}`), L1548–1671 (`store_string_*`), L1731–1748 (`store_{own,borrow}`), L1767–1769 (`MAX_FLAT_*`), L2093–2293 (`canon_{lift,lower,resource_*}`).
2. **`WebAssembly/gc`** @ `756060f5816c7e2159f4817fbdee76cf52f9c923`: `proposals/gc/MVP.md` (L26–145, L230–360).
3. **`WebAssembly/shared-everything-threads`** @ `de560922268ca89fd3303776c5c1b8f123da2aec`: `proposals/shared-everything-threads/Overview.md` (L35–112).
4. **`bytecodealliance/wasmtime`** @ `3ce2209872ccf1ea115914a81e020aef66a10c51`: `crates/wasmtime/src/runtime/vm/component/{handle_table.rs (L23–38, L224–323), resources.rs (L143–154, L252–256, L309–395, L424–435), libcalls.rs (L186–555, L599–689)}`; `crates/wasmtime/src/runtime/component/func/typed.rs` (L1344–1424).
5. **`oracle/graal`** @ `3fd1dcaa85129cc6df8232487f9506d73787a755` & Grimmer et al.:
   - Grimmer, Seaton, Schatz, Würthinger, Mössenböck, DLS 2015, DOI `10.1145/2816707.2816714`; Grimmer, Schatz, Seaton, Würthinger, Luján, Mössenböck, ACM TOPLAS 40(2), Art. 8, 2018, DOI `10.1145/3201898`.
   - `InteropLibrary.java` (L206–215, L429–670, L1864–1879, L2912–3045, L5339–5533); `TruffleLanguage.java` (L1301–1327); `truffle/docs/{TruffleLibraries.md, NFI.md, Optimizing.md (L684–920)}`; `docs/reference-manual/{llvm/Interoperability.md, embedding/embed-languages.md (L407–565)}`.
6. **`ECMA-335` 6th Edition (June 2012)** & **`dotnet/runtime`** @ `db341b0b461356d954079d27e86cb47c929e7e8a`:
   - `ECMA-335_6th_edition_june_2012.pdf`: Partition I `§I.7.3` (pp. 14–15), `§I.8` (pp. 16–18); Partition III `§III.2.4` (p. 320).
   - `docs/design/specs/Ecma-335-Augments.md` (L991–1088, L1183–1223); `docs/design/coreclr/botr/clr-abi.md` (L88–100, L177–230, L961–985); `src/coreclr/jit/morph.cpp` (`Compiler::fgCanFastTailCall` L4112–4317, `fgMorphTailCallVia{Helpers,JitHelper}` L4927–5928).
7. **`capnproto/capnproto`** @ `20fe8fd325bf3825d6cdc3cf16bb263a4c142326`: `doc/encoding.md` (L10–277); `c++/src/capnp/{message.h (L51–75), arena.h (L62–96, L416–429), layout.c++ (L455–464, L578–619, L2075–2270)}`.
8. **Fuchsia `FIDL`** (fetched 2026-11-19): `wire-format` (§Core Concepts, §Handles, §Envelopes, §Details, §Maximum Recursion Depth), `RFC-0131` (§Design), and `RFC-0126` (§Per Request arena, §Linearization / Leaked Handles / Non-LLCPP Bindings).

### 2. Executable Support Probe Receipt

- **Script**: `support/verify_wit_canonical_abi_and_resources.py` (Python 3.10+ stdlib only).
- **Command**: `python3 -B reports/wasm-component-model-truffle-graal-and-polyglot-interop-platforms/support/verify_wit_canonical_abi_and_resources.py`
- **Observed Result (exit code 0, 2026-11-19)**: `"status": "PASS"` across resource/reentrancy/Unicode checks `A1`–`A9`, 12 single-hop transcoding crossings + 4-hop alternating pipeline (`49,152 B` = `12.0x`), zero-copy Cap'n Proto 4,096 B read (`0` copies, `0` allocs, `514` words billed), and adversarial DoS rejections `B1`–`B4b`.

## Revalidation

1. **Re-run the executable probe**: Execute `python3 -B reports/wasm-component-model-truffle-graal-and-polyglot-interop-platforms/support/verify_wit_canonical_abi_and_resources.py` and confirm exit code `0` with `"status": "PASS"`. (Validates the encoded algorithms; upstream specification drift requires the targeted diffs below.)
2. **WebAssembly Component Model & Wasmtime**: Diff `WebAssembly/component-model` `definitions.py` (`MAX_FLAT_*`, `store_string_into_range`, `ResourceHandle`, `End.copy`, `reallocate`) and `Binary.md` (`contains_borrow`) against `585526aa1f2c7f76f07557d16e265dede38b3acb`; check stabilization of the GC ABI option (issue `#525`), Phase 4 status of `WebAssembly/shared-everything-threads` (`de560922...`), and `wasmtime` `handle_table.rs`/`resources.rs` (`3ce22098...`).
3. **GraalVM Truffle**: Diff `oracle/graal` `InteropLibrary.java` (`isIdentical`, `isNull`, `fitsIn*`, `toNative`), `TruffleLanguage.java` (`isThreadAccessAllowed`), and `embed-languages.md` (runtime optimization matrix & Polyglot Isolates) against `3fd1dcaa85129cc6df8232487f9506d73787a755`.
4. **ECMA-335 & CoreCLR**: Diff `dotnet/runtime` `Ecma-335-Augments.md` and `src/coreclr/jit/morph.cpp` (`fgCanFastTailCall`) against `db341b0b461356d954079d27e86cb47c929e7e8a`; check whether Ecma International publishes a 7th Edition incorporating `Ref Fields` / `ByRefLike` generics or whether RyuJIT lifts the `byref` fast-tail-call restriction.
5. **Cap'n Proto & Fuchsia FIDL**: Diff `capnproto/capnproto` `c++/src/capnp/{message.h,arena.h,layout.c++}` (`ReaderOptions`, `checkObject`, `amplifiedRead`) against `20fe8fd325bf3825d6cdc3cf16bb263a4c142326`, and check Fuchsia's FIDL wire-format specification and RFC index for wire-format v3 or non-LLCPP adoption of RFC-0126 partial handle extraction.
