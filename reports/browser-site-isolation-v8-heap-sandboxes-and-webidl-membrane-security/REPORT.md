# Browser Site Isolation, V8 Heap Sandboxes, RLBox, and WebIDL Membrane Security

## Summary

Modern web browsers enforce defense-in-depth across four nested isolation tiers—OS processes, in-process VM heap cages, fine-grained native-library sandboxes, and JavaScript/DOM object membranes—each addressing a distinct fault model where lower-level memory or language invariants are assumed broken:

1. **OS-Level Site Isolation (`Chromium` `ProcessLock`, OOPIFs, and CORB/ORB):** Site Isolation (Reis, Moshchuk, Oskov, USENIX Security 2019; `chromium/chromium` @ `6105bc803f9c448b923d10464fee38644066cc2a`) locks each renderer process to a single site (`ProcessLock`), renders cross-site iframes in Out-of-Process Iframes (OOPIFs), and filters cross-origin network payloads in the browser/network process via Opaque Response Blocking (`services/network/public/cpp/orb/orb_api.h`, successor to CORB) before untrusted bytes ever enter a renderer's address space.
2. **In-Process VM Heap Containment (`V8 Sandbox` / "Ubercage"):** At `v8/v8` `e88118f63dd96f24a9acb8bd0665e7880063f5c0`, the V8 Sandbox assumes arbitrary concurrent read/write inside a contiguous virtual address cage (typically **1 TiB** = `2^40` bytes flanked by **32 GiB** front and back guard regions, *not* 4 TiB—with 128 GiB / 16 GiB variants on constrained targets) and prevents writes from corrupting out-of-sandbox process memory. It replaces raw 64-bit pointers inside the cage with: (a) 40-bit shifted offsets (`SandboxedPointer_t`, `raw >> 24`) paired with 35-bit `BoundedSize` (`raw >> 29`, guaranteed to land inside the 32 GiB guard region with 2 bytes of headroom even on `UINT64_MAX`), (b) out-of-sandbox `TrustedSpace` accessed via `TrustedPointerTable`, (c) type-tagged `ExternalPointerTable` (7-bit tag + mark bit) and `CppHeapPointerTable` (15-bit hierarchical tag ranges for Blink Oilpan C++ objects), and (d) write-protected `JSDispatchTable` (coupling `Code`, entrypoint, and 16-bit parameter count) plus `WasmCodePointerTable` and 7-bit XORed `CodeEntrypointTag` CFI—superseding the historical standalone `CodePointerTable` still named in `src/sandbox/GLOSSARY.md`. Optional hardware support (`src/sandbox/hardware-support.h`) layers Memory Protection Keys (PKU/PKEY) to make out-of-sandbox memory hardware-unwritable during sandboxed execution.
3. **Type-Enforced Native Library Sandboxing (`RLBox`):** `PLSysSec/rlbox_sandboxing_api` (`b0157dc84f86ffbe4549e32ed5cbdfad79c17f43`; Narayan et al., USENIX Security 2020) embeds information-flow and TOCTOU-free boundary crossing into the C++ type system via `tainted<T, T_Sbx>` (app-memory tainted values) and `tainted_volatile<T, T_Sbx>` (sandbox-memory references produced by pointer dereference), enforcing single-copy linear extraction (`copy_and_verify`, `copy_and_verify_range`, `copy_and_verify_string`) into host-private storage before validation predicates execute.
4. **JavaScript/DOM Membranes (`WebIDL`, `WindowProxy`, Blink `DOMWrapperWorld`, and `Trusted Types`):** Cross-world DOM isolation in Blink (`DOMWrapperWorld` + `DOMDataStore`) gives each extension or inspector world distinct JS wrapper graphs over shared Oilpan C++ DOM nodes; WHATWG `WindowProxy` enforces dynamic cross-origin property access checks (`IsPlatformObjectSameOrigin` / `CrossOriginGetOwnPropertyHelper`, explicitly documenting a willful violation of ECMAScript's essential internal-method invariants for web compatibility); WebIDL `[LegacyUnforgeable]` and `[CrossOriginIsolated]` gate property stability and high-privilege APIs; and W3C Trusted Types (`w3c/trusted-types` @ `afcdd4634f6c85056e9c5f39fc1fe75486ea2bc5`) converts DOM injection sinks into capability-checked typed operations (`TrustedHTML`, `TrustedScript`, `TrustedScriptURL`, plus `TrustedHTMLParserOptions`).

## Applicability

This report documents primary-source specifications, concrete bit-level layouts, and formal boundary invariants for four coupled browser-isolation mechanisms:

- **Process-Level Isolation & Blink Bindings:** `chromium/chromium` @ `6105bc803f9c448b923d10464fee38644066cc2a` (`content/browser/process_lock.h`, `content/browser/site_info.h`, `content/public/browser/site_isolation_policy.h`, `services/network/public/cpp/orb/orb_api.h`, `third_party/blink/renderer/platform/bindings/{dom_wrapper_world,dom_data_store}.h`) and Reis, Moshchuk, Oskov (USENIX Security 2019).
- **V8 In-Process Heap Sandbox:** `v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0` (`include/v8-internal.h`, `src/sandbox/{README.md,GLOSSARY.md,sandbox.h,sandboxed-pointer-inl.h,bounded-size-inl.h,tagged-payload.h,external-pointer-table.h,trusted-pointer-table.h,cppheap-pointer-table.h,js-dispatch-table.h,js-dispatch-table-inl.h,code-entrypoint-tag.h,hardware-support.h,bytecode-verifier.h,generated-code-validator.h}`). Constants apply to 64-bit sandbox-enabled builds (`V8_ENABLE_SANDBOX`, `V8_COMPRESS_POINTERS`); 32-bit targets do not support the V8 Sandbox.
- **Fine-Grained Library Sandboxing:** `PLSysSec/rlbox_sandboxing_api` @ `b0157dc84f86ffbe4549e32ed5cbdfad79c17f43` (`code/include/{rlbox.hpp,rlbox_types.hpp,rlbox_wrapper_traits.hpp}`) and Narayan et al. (USENIX Security 2020). Applies to C++ host applications isolating untrusted C/C++ libraries via Wasm/SFI or process backends.
- **Web Platform Membranes:** `whatwg/webidl` @ `54a5f2de6a34e27a517a49370bc07d8943b0be11`, `whatwg/html` @ `94e4f346fdb450f5088da17ec5fe995e8860cf35`, and `w3c/trusted-types` @ `afcdd4634f6c85056e9c5f39fc1fe75486ea2bc5`.

Where documentation and source code have evolved (specifically V8's transition from standalone `CodePointerTable` to `JSDispatchTable` + `WasmCodePointerTable`, and Chromium's transition from CORB to ORB), both the historical design terminology and the exact pinned-revision implementation are preserved explicitly.

## Findings

### 1. Chromium Site Isolation, `ProcessLock`, OOPIFs, and ORB

`Basis: documentation + source`

Chromium's multi-process architecture historically separated renderer processes from the privileged browser process, yet co-located cross-site documents (especially cross-site `<iframe>` subdocuments) in the same renderer address space. Under either a compromised renderer or microarchitectural transient-execution disclosure (Spectre), any sensitive cross-site resource resident in the renderer's address space is exposed.

**Core Architectural Pillars (Reis, Moshchuk, Oskov, USENIX Security 2019; `chromium/chromium` @ `6105bc803f9c448b923d10464fee38644066cc2a`):**

1. **Site-Locked Renderer Processes (`content/browser/process_lock.h`, `content/browser/site_info.h`):**
   - `ProcessLock` binds a renderer process to a site principal (scheme + registrable domain, or finer-grained origin isolation when `Origin-Agent-Cluster` / cross-origin isolation applies).
   - The browser process enforces `ChildProcessSecurityPolicy` checks against a process's `ProcessLock` on every IPC boundary (cookies, storage, `postMessage` origin claims, file access), preventing a compromised renderer locked to `https://untrusted.example` from requesting credentials or storage belonging to `https://bank.example`.
2. **Out-of-Process Iframes (OOPIFs):**
   - Cross-site subframes execute in separate renderer processes with distinct `ProcessLock` instances; the parent renderer holds only a lightweight proxy frame (`RenderFrameProxy`), while the compositor stitches visual surfaces from isolated processes.
   - Cross-origin `WindowProxy` calls traverse IPC through the browser process rather than touching remote DOM memory directly.
3. **Cross-Origin Read Blocking (CORB) -> Opaque Response Blocking (ORB) (`services/network/public/cpp/orb/orb_api.h`):**
   - Even when a renderer is locked to one site, web compatibility allows `<script>`, `<img>`, and `<link>` tags to issue cross-origin no-CORS fetches. Without filtering, a renderer could request cross-origin JSON, HTML, or XML and read its bytes into renderer RAM before parsing fails.
   - Chromium's `network::orb::ResponseAnalyzer` (`orb_api.h:25-95`) inspects HTTP headers and incremental body prefixes *in the network service* before forwarding bytes to a renderer, returning `Decision::{kAllow, kBlock, kSniffMore}` and finalizing via `HandleEndOfSniffableResponseBody()`. Blocked responses are replaced with empty/network-error bodies so sensitive cross-origin bytes never cross into the untrusted renderer process.
4. **Cross-Origin Isolation (`COOP` + `COEP`):**
   - APIs exposing high-resolution timers or `SharedArrayBuffer` (annotated `[CrossOriginIsolated]` in `whatwg/webidl` `index.bs:9728-9753`) require both `Cross-Origin-Opener-Policy: same-origin` and `Cross-Origin-Embedder-Policy: require-corp` (or `credentialless`), guaranteeing that *every* resource mapped into the browsing context group explicitly opted into sharing.

---

### 2. V8 Heap Sandbox ("Ubercage"): Threat Model, Virtual Layout, and Tagged Pointer Tables

`Basis: documentation + source + execution`

#### 2.1 Threat Model and Violation Criterion

From `v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0` (`src/sandbox/README.md:1-29`, `src/sandbox/sandbox.h:26-62`):

- **Assumed Adversary Capability:** The attacker has **arbitrary concurrent read and write access to all memory inside the sandbox address space**, plus the ability to read out-of-sandbox memory (e.g., via hardware side channels).
- **Security Invariant:** No corruption of in-sandbox memory may cause a write outside the sandbox address space that corrupts unguarded host process state or diverts control flow to unintended native code.
- **Explicit Non-Violations (`README.md:22-29`):** Access violations inside the sandbox or guard regions (safe traps), writes trapped inside segmented table guard pages, or GC reclamation induced by corrupted in-sandbox pointers so long as out-of-sandbox metadata remains consistent.

#### 2.2 Virtual Address Space Geometry and Zero-Branch Bounds Guarantees

Direct inspection of `src/sandbox/sandbox.h:51-61` and `include/v8-internal.h:225-305` pins the exact address-space layout:

```text
+---------------+--------------------------------------------------+---------------+
|  32 GiB Guard |                  1 TiB Sandbox                   |  32 GiB Guard |
|    (front)    |  4 GiB V8 Heap Cage  : ArrayBuffers, Wasm, etc.  |     (back)    |
+---------------+----------------------+---------------------------+---------------+
                ^                                                  ^
                sandbox_base                                       sandbox_end
```

Exact compile-time constants (`include/v8-internal.h:225-301`, `src/sandbox/sandboxed-pointer-inl.h:18-46`, `src/sandbox/bounded-size-inl.h:18-35`):

| Constant / Mechanism | 64-Bit Desktop Value (`v8/v8` @ `e88118f6`) | Formula / Encoding | Security Guarantee |
| --- | --- | --- | --- |
| `kSandboxSizeLog2` / `kSandboxSize` | `40` / `1 TiB` (`2^40` B; `128 GiB` or `16 GiB` on constrained configs) | Contiguous virtual reservation | All untrusted V8 heap, `ArrayBuffer` backing stores, and Wasm linear memories reside here |
| `kSandboxGuardRegionSize` | `32 GiB` (`2^35` B) front & back | Unmapped `PROT_NONE` guard pages | Traps any bounded offset overrun past `sandbox_end` |
| `SandboxedPointer_t` | 40-bit offset shifted left by `kSandboxedPointerShift = 64 - 40 = 24` | Decode: `cage_base + (raw >> 24)` | Branchlessly guarantees `ptr ∈ [base, base + 2^40 - 1]` for *every* 64-bit bit pattern |
| `BoundedSize` | 35-bit length shifted left by `kBoundedSizeShift = 29` | Decode: `raw >> 29` (`max = 2^35 - 1`) | Even with corrupted `ptr = base + 2^40 - 1` and `size = 2^35 - 1`, `ptr + size` lands strictly inside the 32 GiB trailing guard region (`2` bytes of headroom) |
| Compressed V8 Pointer | 32-bit offset inside the initial `4 GiB` heap cage | `cage_base + (uint32_t)offset` | Confined strictly to first 4 GiB of sandbox |

Execution of `test_v8_sandbox_bounds` (`Basis: execution`) across adversarial 64-bit boundary values (`0`, `2^24 - 1`, `0xFFFF_FFFF_FFFF_FFFF`) confirms `max_offset = 0xffffffffff`, `max_bounded_size = 0x7ffffffff`, and `limit - (max_ptr + max_sz) == 2` bytes—mathematically demonstrating why `kSandboxSizeLog2 = 40`, `kBoundedSizeShift = 29`, and `kSandboxGuardRegionSize = 32 GiB` are co-designed as a single arithmetic containment invariant.

#### 2.3 Out-of-Sandbox Pointer Tables, `TrustedSpace`, and `CodePointerTable` Evolution

Because in-sandbox objects must still reference native embedder objects, Blink C++ Oilpan objects, privileged V8 bytecode/JIT metadata, and executable code, V8 stores **32-bit opaque handles (indices)** inside the sandbox and resolves them through **out-of-sandbox segmented tables** (`src/sandbox/segmented-table.h`, `external-entity-table.h`):

| Pointer Class / Table | Target Space | Entry Layout (`v8/v8` @ `e88118f6`) | Type / CFI Check Mechanism | Residual In-Sandbox Hazard |
| --- | --- | --- | --- | --- |
| **External Pointer (`ExternalPointerTable`, EPT)** | Native non-V8 C++ objects | 8 B entry: pointer + mark bit (`1<<48`, or `1<<56` on LA57/TBI) + 7-bit tag (`shift 49` / `57`, mask `0x00fe...`) | `TaggedPayload::CheckTag(content, tag_range)` + `SBXCHECK` (or null return if nullable); free/evacuation entries carry reserved tags | Attacker can swap two live handles carrying the **same** `ExternalPointerTag` ("pointer swap attack") |
| **CppHeap Pointer (`CppHeapPointerTable`)** | Blink Oilpan (`cppgc`) C++ DOM objects | 8 B entry: mark bit (bit 0) + **15-bit tag** (`bits [15:1]`) + pointer shifted left 16 (`kCppHeapPointerPayloadShift = 16`) | Constant-time contiguous `TagRange` inclusion check supporting C++ inheritance hierarchies (`Node` range enclosing `Element` sub-range) | Same-tag-range wrapper confusion within a single Blink class family |
| **Trusted Pointer (`TrustedPointerTable`, TPT)** | `TrustedSpace` (separate pointer-compression cage *outside* sandbox) | 8 B entry (64 MB table reservation, handle shift `9`), tagged with `IndirectPointerTag` | `ExposedTrustedObject` owns TPT entry; pointers *between* trusted objects use `ProtectedPointer` (immutable from sandbox) | Swapping two live `ExposedTrustedObject` handles of the same `TrustedPointerTag` |
| **JS Call Dispatch (`JSDispatchTable`, JSDT)** | `Code` object in TrustedSpace + executable entrypoint | 16 B entry (`code_object` + **16-bit `parameter_count`** + `entrypoint`, write-protected where supported, acquire/release publication in `js-dispatch-table-inl.h:28-95`) | Enforces JS calling-convention **arity agreement** between caller and callee; replaces standalone `CodePointerTable` for JS calls | Swapping dispatch handles between distinct JS functions still respects signature/parameter-count integrity |
| **Non-JS / Wasm Code (`WasmCodePointerTable` + `CodeEntrypointTag`)** | Wasm / RegExp / IC / Bytecode handlers | `WasmCodePointerTable` (128 MB reservation) + 7-bit `CodeEntrypointTag` (`src/sandbox/code-entrypoint-tag.h:35-69`, XORed at shift `48` or `57` on LA57) | Callsite hardcodes expected `CodeEntrypointTag` and XOR-untags entrypoint; mismatch yields non-canonical faulting address | Prevents cross-convention jumps (e.g., jumping to a RegExp or IC handler from a Wasm callsite) |

**Source-vs-Documentation Discrepancy Preserved (`Basis: documentation + source`):** `src/sandbox/GLOSSARY.md:132-140` and `src/sandbox/README.md:118-121` still describe a standalone `CodePointerTable` (CPT) for `Code` entrypoints. Direct source inspection of `v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0` confirms `src/sandbox/code-pointer-table.h` no longer exists at HEAD: JavaScript call dispatch has migrated to **`JSDispatchTable`** (`src/sandbox/js-dispatch-table.h`, adding parameter-count signature enforcement and fast tiering), Wasm uses **`WasmCodePointerTable`** (`include/v8-internal.h:929`), and `CodeEntrypointTag` (`src/sandbox/code-entrypoint-tag.h`) provides fine-grained calling-convention CFI.

#### 2.4 Hardware Sandbox Support, Bytecode Verification, and Generated-Code Validation

At `e88118f63dd96f24a9acb8bd0665e7880063f5c0`, V8 layers three additional defenses atop software pointer tables:

- **Hardware Support (`src/sandbox/hardware-support.h:80-110`):** Uses Memory Protection Keys (`EnterSandboxedExecutionModeForCurrentThread` / `ExitSandboxedExecutionModeForCurrentThread`) so threads in `CodeSandboxingMode::kSandboxed` lose hardware write permission to out-of-sandbox memory keys (with explicit `RegisterUnsafeSandboxExtensionMemory` debt tracking for legacy out-of-sandbox writes).
- **Bytecode Verifier (`src/sandbox/bytecode-verifier.h`) & Generated-Code Validator (`src/sandbox/generated-code-validator.h`):** Verify Ignition bytecode invariants and validate emitted x64/arm64 machine code against sandbox constraints (e.g., disallowing raw out-of-sandbox memory stores in sandboxed code).

Execution of `test_pointer_tables` (`Basis: execution`) verifies `ExternalPointerTable` round-trip untagging, rejection of all `127` mismatched 7-bit tags (including freelist and evacuation tags), and `CppHeapPointerTable` hierarchical sub-range acceptance vs. disjoint-range rejection.

---

### 3. RLBox: Type-System Information Flow and Anti-TOCTOU Extraction for Sandboxed Libraries

`Basis: source + documentation`

While Site Isolation isolates origins at OS-process granularity and the V8 Sandbox isolates JS/Wasm heaps, browsers still link dozens of memory-unsafe C/C++ media, font, and parser libraries (`libGraphite`, `Expat`, `hunspell`, `libjpeg`, `libvpx`) directly into the renderer. **RLBox** (Narayan et al., USENIX Security 2020; `PLSysSec/rlbox_sandboxing_api` @ `b0157dc84f86ffbe4549e32ed5cbdfad79c17f43`) isolates these libraries behind Wasm/SFI or process backends and prevents host-side validation mistakes using C++ wrapper types:

#### 3.1 Core Type Algebra (`code/include/rlbox_types.hpp`, `code/include/rlbox.hpp`)

| RLBox C++ Type | Memory Residence | Permitted Host Operations | Boundary Enforcement Purpose |
| --- | --- | --- | --- |
| `tainted<T, T_Sbx>` (`rlbox.hpp:878`) | Host (application) memory | Arithmetic/comparisons stay tainted (`tainted<U>` or `tainted_boolean_hint`); cannot directly control host branches or raw pointer dereferences without explicit verification | Prevents untrusted values from silently flowing into host array indices, allocations, or control flow |
| `tainted_volatile<T, T_Sbx>` (`rlbox.hpp:1121`) | **Inside sandbox memory** (result of dereferencing `tainted<T*, T_Sbx>`) | Cannot be verified in place; `copy_and_verify` copies into host-private storage first; unary `&` yields `tainted<T*, T_Sbx>` | **Structurally prevents double-fetch TOCTOU** when another sandbox thread or callback mutates sandbox memory |
| `tainted_opaque<T, T_Sbx>` (`rlbox_types.hpp:8`) | Sandbox-encoded representation (opaque to host) | Zeroing (`set_zero`) or conversion via sandbox-aware wrappers | Prevents host code from misinterpreting LP32 Wasm pointer/type layouts inside a 64-bit host |
| `tainted_boolean_hint` / `tainted_int_hint` | Host memory | Explicit developer acknowledgment before branching on a tainted boolean comparison | Makes tainted control-flow dependencies auditable in code review |
| `app_pointer<T, T_Sbx>` / `sandbox_callback<T, T_Sbx>` | Host capability tokens | Registers host pointers/callbacks in sandbox-opaque indirection tables | Prevents sandboxed code from forging host function pointers or raw application addresses |

#### 3.2 Linear Single-Copy Verification (`code/include/rlbox.hpp:487-562`, `74-97`)

Direct inspection of `copy_and_verify` (`rlbox.hpp:525-535`) proves that RLBox explicitly implements the same linear copy-in-once defense analyzed in hypervisor shared-ring backends:

```cpp
// PLSysSec/rlbox_sandboxing_api @ b0157dc84f86ffbe4549e32ed5cbdfad79c17f43
// code/include/rlbox.hpp:529-534
// Important to assign to a local variable (i.e. make a copy)
// Else, for tainted_volatile, this will allow a
// time-of-check-time-of-use attack
auto val_copy = std::make_unique<T_Deref>();
*val_copy = *val;
return verifier(std::move(val_copy));
```

Additional static and dynamic boundary guards verified in `rlbox.hpp`:
- `copy_and_verify` statically rejects `void*` (`L502-L511`) and function pointers (`L514-L521`), and restricts array `copy_and_verify` to fundamental/enum element types (`L544-L554`).
- `unverified_safe_pointer_because(count, reason)` (`L74-L97`) statically forbids pointers-to-pointers (`static_assert` / `rlbox_detail_static_fail_because` on `std::is_pointer_v<T_Pointed>`) and dynamically enforces `detail::check_sandbox_pointer_range_is_contained<T_Sbx>(ret, sizeof(T_Pointed) * count)` so a tainted pointer cannot alias host memory outside the sandbox's linear memory bounds.
- Unchecked escape hatches (`UNSAFE_unverified()`, `unverified_safe_because`) carry explicit grep-auditable names so security review concentrates on a tiny surface.

---

### 4. WebIDL, Blink Isolated Worlds, `WindowProxy`, and W3C Trusted Types Membranes

`Basis: normative + source + execution`

Even when OS processes, V8 heaps, and native libraries are memory-safe and compartmentalized, JavaScript code from distinct trust realms (cross-origin frames, browser extensions, and untrusted web strings) interacts across object membranes defined by WebIDL, HTML, Blink, and Trusted Types.

#### 4.1 Blink `DOMWrapperWorld` and `DOMDataStore` (JS <-> Oilpan C++ Membrane)

In Chromium Blink (`third_party/blink/renderer/platform/bindings/dom_wrapper_world.h:56-116`, `dom_data_store.h:99-145`), a single C++ DOM node (`ScriptWrappable`, managed by Oilpan `cppgc`) may be observed simultaneously by the web page (`WorldType::kMain`, `kMainWorldId = 0`), browser-extension content scripts (`WorldType::kIsolated`, IDs in `[1, 1<<29)`), DevTools (`WorldType::kInspectorIsolated`), or ShadowRealms (`WorldType::kShadowRealm`):

- Each `DOMWrapperWorld` maintains an isolated `DOMDataStore` mapping `ScriptWrappable* -> v8::Object` (with fast inline wrapper storage for the main world and per-world maps for isolated worlds).
- Consequently, the main page and an extension content script share the underlying C++ DOM tree, **never** share JS wrapper objects or prototype chains (`Object.prototype`, `Element.prototype`, getters/setters), preventing page-script prototype tampering from hijacking privileged extension execution.
- Across the C++/V8 boundary, the V8 wrapper references its C++ `ScriptWrappable` through V8's `CppHeapPointerTable` with hierarchical `CppHeapPointerTagRange` type checks (Section 2.3), pairing JS-level world isolation with sandbox-level C++ type integrity.

#### 4.2 WHATWG `WindowProxy` Exotic Object and Cross-Origin Invariants

In `whatwg/html` (`94e4f346fdb450f5088da17ec5fe995e8860cf35`, `source:99318-99452`), every browsing context exposes a `WindowProxy` exotic object whose internal `[[Window]]` slot dynamically retargets on navigation. Its `[[GetOwnProperty]](P)` and `[[DefineOwnProperty]](P, Desc)` algorithms enforce the Same-Origin Policy dynamically:

1. Check `IsPlatformObjectSameOrigin(W)`.
   - **If same-origin:** Delegate to `OrdinaryGetOwnProperty(W, P)` / `OrdinaryDefineOwnProperty(W, P, Desc)`. The specification explicitly records (`L99379-L99382`, `L99435-L99438`) that this is a **willful violation of ECMAScript's invariants of the essential internal methods**: because `WindowProxy`'s `[[Window]]` target changes on cross-document navigation, a property previously observed as `non-configurable` (`[LegacyUnforgeable]`, such as `window.location` or `window.document`) can later disappear or change value across navigations—violating ECMA-262's immutability invariant for non-configurable properties.
   - **If cross-origin:** Permit only the fixed `CrossOriginProperties` allowlist (`window`, `self`, `location`, `close`, `closed`, `focus`, `blur`, `frames`, `length`, `top`, `opener`, `parent`, `postMessage` on `Window`; `href` setter and `replace` on `Location`), plus child navigable indices/names and neutral `undefined` fallback for `then` / well-known symbols (`Symbol.toStringTag`, `Symbol.hasInstance`, `Symbol.isConcatSpreadable`, preventing cross-origin `Promise.resolve(otherWindow)` crashes). Any other access throws a `SecurityError` `DOMException`.

#### 4.3 WebIDL Conversion Re-Entrancy and `[LegacyUnforgeable]`

In `whatwg/webidl` (`54a5f2de6a34e27a517a49370bc07d8943b0be11`):
- **`[LegacyUnforgeable]` (`index.bs:11352-11377`):** Forces security-sensitive attributes/operations (e.g., `Window.location`, `Window.document`, `Document.location`) to be installed as non-configurable own properties on the instance rather than on the prototype, preventing prototype shadowing.
- **Observable Conversion Re-Entrancy (`es-DOMString`, `es-dictionary`):** Converting JS arguments to WebIDL types (`DOMString`, dictionaries, sequences, unions) invokes user-defined JavaScript (`toString()`, `valueOf()`, `Symbol.iterator`, Proxy traps, property getters) *before* invoking the underlying C++ DOM method. Sound C++ bindings must therefore complete all WebIDL conversions (copying primitives/strings) before taking raw references into mutable DOM structures, or revalidate DOM state after every conversion step to prevent JS-callback mutation (use-after-free or state-machine desynchronization during argument marshaling).

#### 4.4 W3C Trusted Types: Capability-Typed DOM Sinks and Parser Options

In `w3c/trusted-types` (`afcdd4634f6c85056e9c5f39fc1fe75486ea2bc5`), DOM XSS defenses shift from ad-hoc string sanitization to **nominal capability types** (`TrustedHTML`, `TrustedScript`, `TrustedScriptURL`, `spec/index.bs:515-547`) created exclusively by CSP-allowlisted `TrustedTypePolicy` factories (`trusted-types` CSP directive) and enforced at sinks via `require-trusted-types-for 'script'` (`L1770-L1865`).

The normative **`get trusted type compliant string`** algorithm (`spec/index.bs:1472-1496`) executes strictly in this order:
1. If `input` is already an instance of `expectedType` (e.g., `TrustedHTML` for `Element.innerHTML`), return its immutable internal `[[data]]` string.
2. Query `Does sink type require trusted types?(global, sinkGroup, true)`. If `false`, stringify and allow.
3. Otherwise invoke the realm's `default` policy (`Process value with a default policy`), rethrowing any exception it raises.
4. If the `default` policy is absent or returns `null`/`undefined`, query CSP (`should sink type mismatch violation be blocked by content security policy?`): allow (with violation report) in report-only mode, or throw a `TypeError` in enforce mode.

**Parser-Options Hardening (`spec/index.bs:586-593`, `1498-1525`):** Modern HTML parsing sinks (`setHTMLUnsafe`, `Document.parseHTMLUnsafe`) accept sanitizer/parser options dicts. As the specification notes (`L1515`), markup already vetted as `TrustedHTML` can still become unsafe if parsed with an unvetted sanitizer transform or script execution enabled; `TrustedHTMLParserOptions` and `get trusted type compliant parser options` close this gap by requiring unvetted author-supplied options to pass through a vetted `TrustedHTMLParserOptions` instance or the `default` policy's `createParserOptions` hook (while XML fragment sinks always require compliant strings).

Execution of `test_membranes` (`Basis: execution`) validates all decision branches of both `WindowProxy`'s cross-origin access predicate and Trusted Types' `get trusted type compliant string` state machine.

---

### 5. Cross-Layer Browser Isolation Trade-Off Matrix

`Basis: derived`

| Isolation Tier | Threat Model / Assumed Fault | Enforcing Mechanism | Cross-Boundary Transfer Pattern | Key Bypass / Residual Constraint |
| --- | --- | --- | --- | --- |
| **OS Process (`Site Isolation` + `ORB`)** | Compromised renderer (native RCE) or Spectre cross-site reads | OS virtual memory + `ProcessLock` + network-process `ResponseAnalyzer` | Structured IPC (Mojo) checked by `ChildProcessSecurityPolicy` | Cross-origin subresources allowed by web semantics (e.g., valid images/scripts) still enter renderer memory unless COEP/CORP restricts them |
| **In-Process VM Cage (`V8 Sandbox`)** | Arbitrary concurrent read/write inside 1 TiB JS/Wasm heap | 40-bit `SandboxedPointer` + 35-bit `BoundedSize` + 32 GiB guards + out-of-sandbox EPT/TPT/CppHeapPT/JSDT + optional PKU | Handle indices resolved via tagged tables; `ProtectedPointer` inside `TrustedSpace` | Same-tag pointer swaps inside EPT/TPT/CppHeapPT; read-only confidentiality out of scope (delegated to Site Isolation) |
| **Fine-Grained Library (`RLBox`)** | Memory corruption inside sandboxed C/C++ library (codec/font/XML) | Wasm/SFI or process memory isolation + C++ `tainted<T>` / `tainted_volatile<T>` types | Linear `copy_and_verify` into host-private memory before host predicates | Security relies on correctness of developer-supplied verifier lambdas and minimization of `UNSAFE_unverified` sites |
| **JS/DOM Membrane (`WebIDL` / `WindowProxy` / `DOMWrapperWorld` / `Trusted Types`)** | Malicious web script, cross-origin frame, or untrusted DOM string | Per-world `DOMDataStore` wrappers; dynamic `IsPlatformObjectSameOrigin`; nominal `Trusted*` capability objects + CSP | WebIDL conversions; `postMessage`; `TrustedTypePolicy` factories | Re-entrant JS callbacks during WebIDL conversion; `WindowProxy` willful violation of ECMA-262 non-configurable invariants; `default` policy over-permissiveness |

## Boundaries

- **V8 `CodePointerTable` Historical vs. Current Tree (`known not to apply` to `e88118f6`):** Claims assuming a standalone `src/sandbox/code-pointer-table.h` file at `v8/v8` `e88118f63dd96f24a9acb8bd0665e7880063f5c0` do not apply; JS call dispatch uses `JSDispatchTable` (`src/sandbox/js-dispatch-table.h`) and Wasm uses `WasmCodePointerTable`.
- **V8 Sandbox Confidentiality Against Out-of-Sandbox Reads (`unsupported`):** As explicitly stated in `src/sandbox/README.md:17-20` and `89-93`, the V8 Sandbox does *not* attempt to prevent out-of-sandbox reads (such as hardware side channels); confidentiality across origins is delegated to OS-level Site Isolation.
- **V8 Sandbox on 32-Bit Architectures (`unsupported`):** `src/sandbox/README.md:33-34` states the V8 Sandbox is only available on 64-bit configurations due to its large virtual address space reservation.
- **Site Isolation Memory Overhead & Mobile Partial Isolation Policies (`not examined`):** This report verified Chromium's `ProcessLock` and `ORB` mechanisms in source (`6105bc803f9c448b923d10464fee38644066cc2a`) and Reis et al. (2019), but did not benchmark process-count memory overhead or Android-specific partial Site Isolation heuristics (`SiteIsolationPolicy` memory thresholds).
- **Wasm2c / Lucet / Process Backend Internals for RLBox (`not examined`):** We verified the host-side `rlbox_sandboxing_api` header invariants (`b0157dc84f86ffbe4549e32ed5cbdfad79c17f43`), not the SFI compiler codegen inside specific RLBox backend plugins (e.g., `rlbox_wasm2c_sandbox`).
- **Hardware PKU Coverage Across All V8 Out-of-Sandbox Writes (`unknown`):** `src/sandbox/hardware-support.h:75-80` documents `RegisterUnsafeSandboxExtensionMemory` as a temporary mechanism for legacy code paths still writing out-of-sandbox memory from sandboxed code; exact remaining callsite count across all architectures was not audited.

## Evidence

### Primary Specifications & Upstream Source Revisions (Observed `2026-11-19`)

- **V8 (`v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0`):**
  - `src/sandbox/README.md:1-136` (attacker model, violation criteria, `--sandbox-testing`/`--sandbox-fuzzing`, design doc index).
  - `src/sandbox/GLOSSARY.md:8-140` (1 TB sandbox summary, `TrustedObject`, `ExposedTrustedObject`, `SandboxedPointer`, `ProtectedPointer`, `ExternalPointer`, `TrustedPointer`, historical `CodePointer`).
  - `src/sandbox/sandbox.h:26-95` (32 GB guard + 1 TB sandbox + 32 GB guard ASCII layout, `kMaxVirtualAddressBitsForCrashFilter`).
  - `include/v8-internal.h:225-305` (`kSandboxSizeLog2 = 40`, `kSandboxedPointerShift = 64 - kSandboxSizeLog2`, `kBoundedSizeShift = 29`, `kSandboxGuardRegionSize`), `341-452` (`ExternalPointerTable` & `CppHeapPointerTable` shifts/masks), `907-929` (`kTrustedPointerTableReservationSize = 64 * MB`, `kWasmCodePointerTableReservationSize = 128 * MB`).
  - `src/sandbox/sandboxed-pointer-inl.h:18-46` (`ReadSandboxedPointerField`, `WriteSandboxedPointerField`).
  - `src/sandbox/bounded-size-inl.h:18-35` (`ReadBoundedSizeField`, `WriteBoundedSizeField`).
  - `src/sandbox/tagged-payload.h:21-130` (`TaggedPayload::Tag`, `CheckTag`, `UntagAllowNullHandle`, `UntagDisallowNullHandle` with `SBXCHECK`, freelist/evacuation tag extraction).
  - `src/sandbox/external-pointer-table.h:25-96` (`ExternalPointerTableEntry` regular/freelist/evacuation states).
  - `src/sandbox/js-dispatch-table.h:26-233` & `src/sandbox/js-dispatch-table-inl.h:28-95` (`JSDispatchEntry::MakeJSDispatchEntry`, 16-bit `parameter_count`, release/acquire ordering on `code_object_`/`entrypoint_`).
  - `src/sandbox/code-entrypoint-tag.h:17-74` (7-bit XOR `CodeEntrypointTag` fine-grained CFI tags at shift 48 or 57 on LA57).
  - `src/sandbox/hardware-support.h:75-110` (`RegisterUnsafeSandboxExtensionMemory`, `EnterSandboxedExecutionModeForCurrentThread`, `CodeSandboxingMode`).
  - `src/sandbox/bytecode-verifier.h`, `src/sandbox/generated-code-validator.h`.
- **Chromium & Blink (`chromium/chromium` @ `6105bc803f9c448b923d10464fee38644066cc2a`):**
  - `content/browser/process_lock.h:25-115` (`ProcessLock`), `content/browser/site_info.h`, `content/public/browser/site_isolation_policy.h`.
  - `services/network/public/cpp/orb/orb_api.h:25-95` (`network::orb::ResponseAnalyzer`, `HandleEndOfSniffableResponseBody`).
  - `third_party/blink/renderer/platform/bindings/dom_wrapper_world.h:56-120` (`IsolatedWorldId`, `DOMWrapperWorld::WorldType::{kMain,kIsolated,kInspectorIsolated,kWorkerOrWorklet,kShadowRealm}`).
  - `third_party/blink/renderer/platform/bindings/dom_data_store.h:99-145` (`DOMDataStore::GetWrapper`, `SetWrapper`, inline main-world storage).
  - Reis, Moshchuk, Oskov, *"Site Isolation: Process Separation for Web Sites within the Browser"*, USENIX Security 2019 (`https://www.usenix.org/conference/usenixsecurity19/presentation/reis`).
- **RLBox (`PLSysSec/rlbox_sandboxing_api` @ `b0157dc84f86ffbe4549e32ed5cbdfad79c17f43`):**
  - `code/include/rlbox_types.hpp:7-87` (`tainted_opaque`, `tainted`, `tainted_volatile`, `tainted_boolean_hint`, `sandbox_callback`, `app_pointer`).
  - `code/include/rlbox.hpp:43-97` (`UNSAFE_unverified`, `unverified_safe_pointer_because` rejecting pointers-to-pointers + `check_sandbox_pointer_range_is_contained`), `487-562` (`copy_and_verify` single-copy anti-TOCTOU pattern), `878` (`class tainted`), `1121-1210` (`class tainted_volatile`).
  - Narayan et al., *"Retrofitting Fine Grain Isolation in the Firefox Renderer"*, USENIX Security 2020 (`https://www.usenix.org/conference/usenixsecurity20/presentation/narayan`).
- **Web Platform Specifications:**
  - `whatwg/webidl` @ `54a5f2de6a34e27a517a49370bc07d8943b0be11`: `index.bs:9728-9753` (`[CrossOriginIsolated]`), `11352-11377` (`[LegacyUnforgeable]`).
  - `whatwg/html` @ `94e4f346fdb450f5088da17ec5fe995e8860cf35`: `source:99318-99452` (`WindowProxy::[[GetOwnProperty]]`, `[[DefineOwnProperty]]`, `IsPlatformObjectSameOrigin`, `CrossOriginGetOwnPropertyHelper`, willful violation of ECMA-262 internal-method invariants).
  - `w3c/trusted-types` @ `afcdd4634f6c85056e9c5f39fc1fe75486ea2bc5`: `spec/index.bs:515-547` (`TrustedHTML`, `TrustedScript`), `586-593` (`TrustedHTMLParserOptions`), `1472-1525` (`get trusted type compliant string`, `get trusted type compliant parser options`), `1770-1865` (`require-trusted-types-for` CSP directive).

### Execution Probe Record (Observed `2026-11-19`)

A standalone Python 3 defensive invariant probe (`probe_v8_sandbox_membranes.py`, standard library only) verified V8 bit-level containment, EPT/CppHeapPT tag isolation, `WindowProxy` access gating, and Trusted Types sink evaluation:

```json
{
  "v8_bounds": {
    "sandbox_size_gib": 1024,
    "guard_size_gib": 32,
    "max_offset_hex": "0xffffffffff",
    "max_bounded_size_hex": "0x7ffffffff",
    "all_ptrs_in_sandbox": true,
    "ptr_plus_bounded_size_within_guard": true,
    "headroom_bytes": 2
  },
  "v8_pointer_tables": {
    "ept_roundtrip_exact": true,
    "ept_all_127_other_tags_rejected": true,
    "ept_freelist_and_evac_rejected": true,
    "cppheap_hierarchy_accept": true,
    "cppheap_disjoint_rejected": true
  },
  "web_membranes": {
    "windowproxy": {
      "same_origin_document": "OrdinaryGetOwnProperty",
      "cross_origin_document": "ThrowSecurityError",
      "cross_origin_postMessage": "CrossOriginAllowedDescriptor",
      "cross_origin_then": "UndefinedFallback"
    },
    "trusted_types": {
      "trusted_html_instance": "ALLOW_TRUSTED_INSTANCE",
      "raw_string_enforced_no_default": "BLOCK_TYPE_ERROR",
      "raw_string_enforced_with_default": "ALLOW_VIA_DEFAULT_POLICY",
      "raw_string_enforced_default_null": "BLOCK_TYPE_ERROR_AFTER_DEFAULT_NULL",
      "wrong_trusted_type": "BLOCK_TYPE_ERROR"
    }
  }
}
```

## Revalidation

1. **Check V8 Sandbox bit-layout constants & table architecture:** Diff `include/v8-internal.h` (`kSandboxSizeLog2`, `kBoundedSizeShift`, `kSandboxGuardRegionSize`, EPT/CppHeapPT/TPT shifts) and `src/sandbox/{tagged-payload.h,js-dispatch-table.h,hardware-support.h}` against `e88118f63dd96f24a9acb8bd0665e7880063f5c0`. Verify that `2^kSandboxSizeLog2 + (2^(64 - kBoundedSizeShift) - 1) <= 2^kSandboxSizeLog2 + kSandboxGuardRegionSize` continues to hold.
2. **Check V8 hardware sandbox completion:** Inspect `RegisterUnsafeSandboxExtensionMemory` references in `src/sandbox/hardware-support.h` to determine whether PKU/PKEY enforcement has eliminated remaining out-of-sandbox extension exemptions.
3. **Check RLBox `copy_and_verify` TOCTOU invariant:** Diff `code/include/rlbox.hpp` (`copy_and_verify` and `unverified_safe_pointer_because`) against `b0157dc84f86ffbe4549e32ed5cbdfad79c17f43` to confirm `tainted_volatile` values remain copied into host-private storage prior to verifier invocation.
4. **Check Chromium ORB & Blink Isolated World storage:** Diff `services/network/public/cpp/orb/orb_api.h` and `third_party/blink/renderer/platform/bindings/{dom_wrapper_world,dom_data_store}.h` against `6105bc803f9c448b923d10464fee38644066cc2a`.
5. **Check Trusted Types & `WindowProxy` normative deltas:** Diff `spec/index.bs` (`get trusted type compliant string` and `get trusted type compliant parser options`) in `w3c/trusted-types` and `windowproxy-getownproperty` in `whatwg/html`, then re-run the Python invariant probe against any updated constants or allowlists.
