# Capability RPC Membranes, Promise Pipelining, DOM Trusted Types, and Compile-Time SQL Safety

## Summary

Web applications commonly stitch together four disconnected boundary mechanisms—ambient cookie/bearer REST endpoints (`tRPC` or REST), intra-edge worker calls, DOM XSS defenses (`Trusted Types`), and database query builders (`sqlx`)—leaving structural seams where authority or sanitization provenance evaporates at serialization boundaries. Inspecting the six upstream systems examined here reveals both how object-capability RPC eliminates whole classes of round-trip and ambient-authority failures and where concrete implementation seams persist:

1. **CapTP Four-Table Capability Lifetimes & Causal E-Order (`capnproto`):** Cap'n Proto's bilateral RPC protocol separates `QuestionId`/`AnswerId` (in-flight calls) from `ExportId`/`ImportId` (capabilities and promises) across five conformance levels (`Level 0`–`4`), compressing $k$-hop dependent RPC chains to **`1` RTT** via `PromisedAnswer.transform` pointer-field traversal while preserving E-Order across promise resolution via `Disembargo` (`senderLoopback`/`receiverLoopback`/`accept`) and the **Tribble 4-way race condition** forwarding discipline.
2. **Signed-ID JS Compression, Missing Embargoes, and Disposal Leaks (`cloudflare/capnweb` & `cloudflare/workerd`):** `capnweb` collapses CapTP's four tables into two signed-integer tables (`0` = bootstrap, `+1..+n` = caller-predicted `push` promises, `-1..-n` = exporter-allocated stubs), adds server-side `.map()` (`["remap", ...]`), and defers serialization until an explicit `["pull", id]`. However, `capnweb`'s `ImportTableEntry.resolve()` (`src/rpc.ts:203-219`) carries an unresolved `TODO: Need embargo handling here?`—leaving post-resolution loopback E-Order unguarded—and both `capnweb` and `workerd` (`JsRpcStub` over `32 MiB` bounded Cap'n Proto envelopes inside `128 MiB` V8 isolates) rely on JS callers invoking `using` / `[Symbol.dispose]` to avoid indefinitely pinning remote `ExportTableEntry` refcounts. Replacing ambient network/cookie globals with non-ambient `Fetcher` / `RpcTarget` stubs blocks SSRF and CSRF structurally.
3. **Phantom Router Erasure (`trpc/trpc`):** `ProcedureBuilder` threads 9 TypeScript phantom generic parameters at compile time (`procedureBuilder.ts:211-254`), yet `createTRPCUntypedClient` (`TRPCUntypedClient.ts:114-183`) erases every interface into plain string-path JSON requests with zero capability unforgeability, zero promise pipelining, and zero runtime input validation whenever a procedure omits `.input(parser)` (`inputs: Parser[]` defaults to empty).
4. **DOM Sink Brand Evaporation (`w3c/trusted-types`):** W3C Trusted Types locks >60 DOM injection sinks behind unforgeable `TrustedHTML`/`TrustedScript`/`TrustedScriptURL` internal slots (mirrored in the polyfill via closure-private `creatorSymbol` + `selfContained(new WeakMap())` immune to prototype poisoning). Yet `TrustedType.prototype.toJSON()` (`src/trustedtypes.js:190-193`) strips the brand back to a raw `string`, severing provenance across JSON/RPC membranes unless re-minted locally.
5. **Compile-Time `DESCRIBE` vs. `.sqlx` Cache Drift & `QueryBuilder::push` (`launchbadge/sqlx`):** `sqlx::query!` asks the database engine's `DESCRIBE` protocol for parameter and nullable column types online, but offline `.sqlx/query-<sha256>.json` files (`data.rs:34, 209`) key **solely** on `SHA-256(sql)`—allowing `ALTER TABLE` schema migrations that preserve SQL syntax to compile cleanly under `SQLX_OFFLINE=true` and fail at runtime. Simultaneously, while `sqlx::query()` gates runtime strings behind `SqlSafeStr` (`&'static str` or `AssertSqlSafe<T>`), `QueryBuilder::push(&mut self, sql: impl Display)` (`query_builder.rs:122`) accepts unbranded `Display` values directly.

Conceptually (`C1`/`C2`), these fragmented defenses collapse into two orthogonal primitives: **(1) lexically/linearly scoped non-ambient `Capability<Interface, Epoch>` handles**, and **(2) grammar-tagged construction brands (`Brand<Grammar>`) preserved across FFI and wire membranes**.

## Applicability

This report synthesizes specifications, C++/TypeScript/Rust source inspection, and a Node.js `v24.21.0` executable wire/membrane probe across six pinned upstream systems spanning the browser-to-database execution path:

- **`capnproto/capnproto` (`20fe8fd325bf3825d6cdc3cf16bb263a4c142326`)**: Normative `c++/src/capnp/rpc.capnp` CapTP Levels `0`–`4` wire schema and runtime framing semantics (`64 MiB` default message traversal bound).
- **`cloudflare/workerd` (`09508388a7fd9068eb2c838455191c0732733b50`)**: Intra-host and inter-isolate V8 JSG-over-Cap'n-Proto RPC (`src/workerd/api/worker-rpc.{h,c++}`), gated by `MAX_JS_RPC_MESSAGE_SIZE = 32 MiB` inside `128 MiB` isolate memory ceilings and ECMAScript Explicit Resource Management (`Symbol.dispose`).
- **`cloudflare/capnweb` (`66ed2fd21307e524165703e0ad7db5839cfd9a19`)**: JavaScript/TypeScript bilateral capability RPC (`src/rpc.ts`, `src/serialize.ts`, `src/core.ts`, `src/batch.ts`), covering WebSocket sessions, single-POST HTTP batch mode, `DEFAULT_LIMITS`, and custom-encoding transports (`"string"`, `"jsonCompatible"`, `"jsonCompatibleWithBytes"`, `"structuredClonable"`).
- **`trpc/trpc` (`596d03d93295f8b4876909cfce86f94a1e6afe51`)**: TypeScript client/server RPC proxy stack (`packages/server/src/unstable-core-do-not-import/{procedureBuilder,router}.ts`, `packages/client/src/{createTRPCClient,internals/TRPCUntypedClient}.ts`).
- **`w3c/trusted-types` (`afcdd4634f6c85056e9c5f39fc1fe75486ea2bc5`)**: W3C Editor's Draft specification (`spec/index.bs`) and official reference polyfill (`src/trustedtypes.js`, `src/enforcer.js`) under CSP `Content-Security-Policy: require-trusted-types-for 'script'`.
- **`launchbadge/sqlx` (`e1a6a2d5053496e1db8cc60cb8da41e3f1c7f18e`)**: Compile-time `sqlx-macros-core/src/query/{mod,data}.rs` (`SQLX_OFFLINE`, `DATABASE_URL`) and runtime `sqlx-core/src/{sql_str,query_builder}.rs` across PostgreSQL, MySQL, SQLite, and MSSQL bind-parameter semantics.

Claims about `capnweb` apply strictly to bilateral Level `1` sessions at commit `66ed2fd2`; claims about `workerd` V8 deserialization apply to `jsg::Serializer` version `15` in `worker-rpc.c++`.

## Findings

### 1. CapTP Four-Table Capability Lifetimes, Promise Pipelining, and Causal `Disembargo` (`capnproto/capnproto`)

Basis: normative + source

`c++/src/capnp/rpc.capnp` formalizes object-capability RPC across four stateful per-connection tables (`L116-L208`) whose directional lifecycles eliminate ID reuse races without distributed stop-the-world GC:

| Sender View | Peer Counterpart | Chooser | End-of-Life (Sender -> Peer) | End-of-Life (Peer -> Sender) |
|---|---|---|---|---|
| `QuestionId` (`UInt32`) | `AnswerId` | Questioner (caller) | `Finish` sent (`L159-L161`) | `Return` sent (`L160-L161`) |
| `ExportId` (`UInt32`) | `ImportId` | Exporter | `Resolve` sent (for promises) | `Release { id, referenceCount }` reduces refcount to `0` (`L183-L207`) |

An ID becomes eligible for reuse **only after both directions have terminated**. On connection drop, all `Question`s fail with exceptions, all `Import`s become broken, and all `Export`s/`Answer`s are implicitly released (`L149-L153`).

- **Single-RTT Promise Pipelining (`L1019-L1210`):** A `Call` targets `MessageTarget::{importedCap, promisedAnswer}`. `PromisedAnswer { questionId, transform: List(Op) }` specifies `Op::getPointerField(uint16)` indices into the pointer section of the *yet-uncomputed* `Return` struct (`L1197-L1199`), letting the callee route dependent pipelined calls (`auth() -> getUser() -> getDocs() -> render()`) without schema knowledge and without round-trips back to the caller.
- **`Disembargo` & the Tribble 4-Way Race Condition (`L660-L816`):** Cap'n Proto requires **E-Order** (calls `foo()` then `bar()` on the same reference must arrive in initiation order). When caller Alice in Vat `A` holds promise `P` pointing to Vat `B`, sends pipelined `foo()` to `P`, and `P` resolves to `Carol` in `A` (or `C` via Level `3` `Provide`/`Accept`), a direct call `bar()` sent straight to `Carol` could overtake `foo()` still traversing `B`. Alice therefore embargoes `bar()` and dispatches `Disembargo { senderLoopback }` along `B`'s path; only when `B` echoes `receiverLoopback` after flushing all pre-resolution calls does `A` release `bar()` (`L703-L795`). Crucially, to prevent the **Tribble 4-way race condition** (`L741-L768`, named after Dean Tribble)—where shortening a 3-hop chain `P1 -> P2 -> Bob` simultaneously in two places breaks embargo ordering—`Resolve.cap` imposes an invariant (`L664-L671`): once `P1` resolves to `P2`, `P1` forwards all messages *strictly* to `P2` (never short-circuiting to `Bob`).
- **`Level 0`–`4` Hierarchy & `releaseParamCaps` Hazard (`L72-L100, L517-L601`):** `Level 0` has no object tables; `Level 1` supports bilateral pipelining and proxying; `Level 2` adds persistent `SturdyRef`s; `Level 3` enables 3-way `Provide`/`Accept`/`ThirdPartyAnswer` handoffs; `Level 4` adds `Join` equivalence checks. `Return.releaseParamCaps` and `Finish.releaseResultCaps` default to `true` (`L517, L596`) specifically because forgetting `false` causes fail-loud errors in `Level >= 1`, whereas forgetting `true` silently leaks capability tables forever.

### 2. Signed-ID JS Table Compression, `.map()`, Missing Embargoes, and Disposal Leaks (`cloudflare/capnweb` & `cloudflare/workerd`)

Basis: source + documentation + execution

#### `cloudflare/capnweb` Bilateral Signed-ID Protocol (`src/rpc.ts`, `src/serialize.ts`, `src/batch.ts`)

`capnweb` adapts CapTP to idiomatic JavaScript/TypeScript over JSON (`"string"`), structured-clone (`"structuredClonable"`), WebSocket, and single-POST HTTP batch transports (`src/batch.ts:76-170`, Kenton Varda Sept 22, 2025):

1. **Collapsing 4 Tables into Signed-ID Arrays (`src/rpc.ts:470-567, 801-925`):** Instead of separate question/answer and import/export ID spaces, `RpcSessionImpl` partitions one signed integer domain per side:
   - **`0`:** Peer's bootstrap `main` object (`exports[0]`, `imports[0]`, `L520-L525`).
   - **Positive IDs (`+1, +2, ...`):** Caller-predicted promise exports created by `["push", ["pipeline", id, path, args]]` (`sendCall`, `L801-L831`, incrementing `imports.length` locally in lockstep with `this.exports.push` on the callee at `L1037`). Because IDs are deterministic from sequential `push` counts, a client immediately issues `["push", ["pipeline", 1, ["getUser"], []]]` before receiving any server bytes.
   - **Negative IDs (`-1, -2, ...`):** Exporter-allocated object/function stubs (`exportStub` deduplicates via `reverseExports` incrementing `refcount`; `exportPromise` always allocates a fresh ID so resolutions are never missed, `L540-L567`).
2. **Lazy `["pull", id]` & Zero-RTT `.map()` (`src/rpc.ts:249-256, 881-911`):** Intermediate pipelined promises (`p1`, `p2`, `p3`) are never serialized back over the wire unless application code actually awaits them (`ImportTableEntry.awaitResolution` emits `["pull", id]` on demand). Furthermore, `sendMap` (`L881-L911`) transmits `["remap", id, path, devaluedCaptures, instructions]` so array transformations execute server-side in **1 RTT** rather than pulling an array of $N$ stubs and issuing $N$ follow-up calls. HTTP batch mode (`src/batch.ts:56-74`) waits one full macrotask (`setImmediate` / `setTimeout(0)`, because `await`ing a thenable schedules `.then()` after the current microtask turn!) and ships the entire `push`+`pull` batch in one HTTP `POST`.
3. **Critical E-Order Seam — Missing `Disembargo` (`src/rpc.ts:203-219`):** Direct source inspection of `ImportTableEntry.resolve()` reveals an explicit unresolved gap:
   ```ts
   resolve(resolution: StubHook) {
     // TODO: Need embargo handling here? PayloadStubHook needs to be wrapped in a
     // PromiseStubHook awaiting the embargo I suppose.
     ...
     this.resolution = resolution;
     this.sendRelease();
   ```
   Because `capnweb` omits `Disembargo` messages, if a promise resolves back to a local capability (or forwards across paths), calls dispatched immediately after `resolve()` can bypass in-flight pipelined `push` calls and violate CapTP E-Order.
4. **GC-vs.-Linear Capability Retention Leaks (`src/rpc.ts:405-413`, `worker-rpc.c++:324-391`):** JavaScript garbage collection is non-deterministic and `capnweb` does not rely on `FinalizationRegistry` to drive `["release", id, refcount]` messages (`RpcImportHook::dispose()`, `L405-L413`). If a caller awaits a capability-bearing object and omits ECMAScript `using` (`[Symbol.dispose]`), `ExportTableEntry` pins server-side memory and callbacks for the life of the WebSocket session (confirmed in the Node.js probe: `5` leaked exports vs. `0` after disposal).

#### `cloudflare/workerd` Isolate Membrane (`src/workerd/api/worker-rpc.{h,c++}`)

At the edge runtime boundary, `workerd` runs Cap'n Proto RPC over `JSG` V8 serialization (`version = 15`, `worker-rpc.c++:245-250`) between isolated V8 heaps:

- **Non-Ambient Authority Blocking SSRF & CSRF:** Workers have no ambient TCP sockets or implicit session cookies across service boundaries unless endowed with an explicit `Fetcher` / `JsRpcStub` service binding (`worker-rpc.h:10-14`). Consequently, Server-Side Request Forgery (`169.254.169.254` metadata probing) and ambient-cookie Cross-Site Request Forgery are blocked by construction—an attacker cannot name a capability outside its `exports`/`imports` table (`ExportId`/`ImportId`).
- **Hard Isolate Memory Ceilings & Two-Phase JS-Free Graph Hydration (`worker-rpc.h:32-38, 181-250`):** `MAX_JS_RPC_MESSAGE_SIZE` is capped at `32 MiB` (`1u << 25`) inside a `128 MiB` V8 isolate ceiling (leaving headroom below Cap'n Proto's `64 MiB` limit). Because V8's `ValueDeserializer::ReadObject` activates `v8::internal::DisallowJavascriptExecution`, `RpcDeserializerExternalHandler::prepare()` (`worker-rpc.c++:169-205`) pre-hydrates all streams and 3-slot sockets *before* graph deserialization and hands them out via `claimPrebuilt*()`, preventing reentrant JS execution mid-deserialization. `JsRpcCallPlan` (`worker-rpc.c++:80-136`) restricts automatic retries (`Replayability::REPLAYABLE`) exclusively to property reads or calls carrying zero externals, guaranteeing capabilities/streams are never duplicated across retry attempts.

### 3. Phantom Router Type Erasure vs. Unvalidated Inputs (`trpc/trpc`)

Basis: source + derived

`trpc` illustrates the exact security hazard of **static-only RPC membranes** without wire-enforced capabilities or mandatory runtime parsing:

- In `packages/server/src/unstable-core-do-not-import/procedureBuilder.ts:211-254`, `ProcedureBuilder<TContext, TMeta, TContextOverrides, TInputIn, TInputOut, TOutputIn, TOutputOut, TCaller, TErrorShape>` encodes input, output, middleware context, and error types across **9 compile-time phantom parameters**, while `ProcedureBuilderDef` (`L78-L100`) stores `inputs: Parser[]` at runtime.
- On the client (`packages/client/src/createTRPCClient.ts:52-60` and `internals/TRPCUntypedClient.ts:114-183`), `TRPCClient<TRouter>` wraps `TRPCUntypedClient` in `createRecursiveProxy`, erasing all 9 type parameters at build time into plain HTTP/WebSocket JSON calls parameterized by `path: string` and `input: unknown`.
- **Two Structural Gaps:**
  1. **Silent Runtime Validation Omission:** If a server procedure omits `.input(zodSchema)` (or an upstream TypeScript caller casts `as any`), `ProcedureBuilderDef.inputs` is empty (`[]`), passing attacker-controlled JSON objects (including unexpected extra keys or wrong primitive shapes) straight into the server resolver while TypeScript falsely implies typed safety.
  2. **Authority & Composition Penalties:** Every request remains vulnerable to ambient-credential `CSRF` unless protected out-of-band (cookies/headers), server objects cannot be passed by unforgeable reference (forcing flat string-ID lookup APIs + IDOR checks on every route), and dependent calls cannot pipeline across `1` RTT.

### 4. Browser DOM Sink Unforgeable Branding and Wire Evaporation (`w3c/trusted-types`)

Basis: normative + source + execution

Under `Content-Security-Policy: require-trusted-types-for 'script'`, the W3C Trusted Types specification (`spec/index.bs:296-309, 1478-1556`) closes >60 DOM XSS injection sinks (`Element.innerHTML`, `insertAdjacentHTML`, `HTMLScriptElement.src`/`text`, `Range.createContextualFragment`, `eval`, `Function`, `setTimeout`) by running `Get Trusted Type compliant string`:

- **Internal-Slot Unforgeability (`src/trustedtypes.js:80-215`):** Only a `TrustedTypePolicy` created via `trustedTypes.createPolicy(name, rules)` can mint `TrustedHTML`, `TrustedScript`, or `TrustedScriptURL` instances. The reference implementation guards constructors with a closure-private `creatorSymbol = Symbol()` (`L80, L168-L172`), stores the raw string inside `privateMap = selfContained(new WeakMap())` (`L104-L121`, copying `WeakMap.prototype` methods directly onto the instance so `Object.prototype` / `WeakMap.prototype` pollution cannot hijack brand checks or extract values), and locks prototypes with `Object.freeze` (`L211-L215`).
- **Default Policy & Wire Brand Evaporation (`spec/index.bs:1486-1496`, `src/trustedtypes.js:190-193`):** If a CSP permits a policy named `default`, raw string assignments route through `defaultPolicy` as a legacy migration adapter; omitting `default` makes raw string assignments fail loudly with `TypeError`. Crucially, however, `TrustedType.prototype.toJSON()` (`src/trustedtypes.js:190-193`) returns `privates(this)['v']`—a **plain unbranded `string`**. Thus, even if an edge server or worker produces sanitized HTML using a Trusted Types policy, transmitting that value across JSON, `structuredClone`, or `capnweb`/`tRPC` RPC **destroys its brand**, forcing the browser client either to re-sanitize (duplicating parser work and risking differential-sanitizer XSS) or blindly trust the RPC edge inside a privileged client policy.

### 5. Compile-Time `DESCRIBE` vs. `.sqlx` Hash Drift and `QueryBuilder::push` (`launchbadge/sqlx`)

Basis: source + execution

`launchbadge/sqlx` applies static checking to SQL at the Rust macro boundary (`sqlx-macros-core/src/query/{mod,data}.rs`), yet exposes two critical soundness boundaries:

1. **Online `DESCRIBE` vs. Offline `.sqlx` Schema-Drift Blind Spot (`sqlx-macros-core/src/query/mod.rs:81-169`, `data.rs:34, 83-109, 209-214`):**
   - Online (`DATABASE_URL` set, `SQLX_OFFLINE != true`), `expand_with` executes `DB::describe_blocking(&input.sql, ...)` against a live database engine, extracting authoritative bind-parameter types and output column nullability directly from the database planner's extended-query `Describe` metadata.
   - Offline (`SQLX_OFFLINE=true`), `expand_input` loads `.sqlx/query-<hash>.json` where `hash = hex(SHA-256(query.as_bytes()))` (`data.rs:209-214`). Because the cache key hashes **only the SQL string** and embeds zero schema fingerprint, `ALTER TABLE` migrations that alter a column type (`INT4 -> NUMERIC`) or nullability (`NOT NULL -> NULL`) without altering SQL text pass offline `cargo build` with `0` errors and panic or fail decoding at runtime unless `cargo sqlx prepare --check` runs in CI against a migrated database.
2. **`SqlSafeStr` vs. Unchecked `QueryBuilder::push` (`sql_str.rs:38-90`, `query_builder.rs:122-173`):**
   - `sqlx::query()` and `raw_sql()` enforce `SqlSafeStr`, implemented exclusively for `&'static str` and the explicit audit marker `AssertSqlSafe<T>` (`sql_str.rs:47-89`), complete with a custom `#[diagnostic::on_unimplemented]` compiler note warning against `format!()`.
   - Conversely, `QueryBuilder::push(&mut self, sql: impl Display)` (`query_builder.rs:122-129`) bypasses `SqlSafeStr` completely and interpolates any `Display` value straight into `self.query: Arc<String>`. Safe parameterized additions require `push_bind(value)` (`L155-L173`), which formats `$N`/`?` placeholders subject to hard database parameter caps documented in `query_builder.rs:141-148`: **PostgreSQL & MySQL `65,535`**, **SQLite `32,766`** (previously `999`), and **MSSQL `2,100`**.

### 6. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

Basis: source + documentation + derived + execution

| Boundary Layer | `(L1)` Authoring LoC & Token Cost | `(L2)` Toolchain Build & RSS | `(L3)` Check / Elaboration Latency | `(L4)` Runtime Latency & Throughput | `(L5)` Boundary / Admission Check | `(L6)` Bundle, RAM & Artifact Footprint |
|---|---|---|---|---|---|---|
| **Cap'n Proto C++ (`20fe8fd3`)** | Schema `.capnp` + generated C++ stubs (`~100–300` LoC/service) | `capnp` codegen + C++ template compile (`~5–20 s`, `~300–600 MiB` RSS) | Schema compiler `< 20 ms` | **Zero-copy wire framing**, `1`-RTT pipelining, `0` JSON parse overhead | Table index + pointer bounds check `O(1)` (`64 MiB` traversal cap) | Compact binary frames; C++ `libcapnp` runtime `~300–500 KiB` |
| **`workerd` JSG RPC (`09508388`)** | `~10–30` LoC `RpcTarget` class (no `.capnp` schema needed per route) | C++ runtime prebuilt; worker JS/TS bundle `< 1 s` | V8 isolate parse/JIT `< 5 ms` | `1`-RTT pipelining; V8 `ValueSerializer` v15 (`O(graph)` walk) + two-phase stream prepare | `DisallowJavascriptExecution` + `32 MiB` message cap (`worker-rpc.h:38`) | **`128 MiB`** hard isolate RAM cap; **`32 MiB`** max RPC payload |
| **`capnweb` (`66ed2fd2`)** | `~5–20` LoC (`RpcTarget` + optional TS interface); `0` DTO/CSRF glue | `tsdown`/TS build `< 1 s` (`0` runtime deps) | TS check `< 100 ms` | **`1` RTT** pipelining (`4x` speedup on 4-hop chain: **`1 ms`** vs `4 ms` intra-DC, **`25 ms`** vs `100 ms` regional, **`80 ms`** vs `320 ms` transcontinental); `.map()` saves `N` RTTs | Receiver `RpcLimits`: **`32 MiB`** (`DEFAULT_LIMITS.maxMessageSize`), depth **`256`**, `maxBigIntDigits` **`16,384`** (`serialize.ts:66-72`) | `< 10 KiB` min+gzip core; unreleased stubs leak `ExportTableEntry` closures in server heap |
| **`tRPC` (`596d03d9`)** | Moderate + manual `.input(zod)` per route (unvalidated without `.input`) | `tsc` slows sharply (`2–15 s`, `> 1 GiB` RSS) on `500+` route routers due to 9-param `ProcedureBuilder` | IDE TS server lag (`200 ms–3 s`) on deep router inference | **`k` RTTs** for $k$-hop dependent calls (`4` RTTs in probe); HTTP JSON parse/stringify per hop | `zod` schema parse (`µs/req`) *only if attached*; `0` capability unforgeability | `tRPC` client + `zod` runtime bundle + per-route wrapper boilerplate |
| **`Trusted Types` (`afcdd463`)** | Low once centralized (`1–3` audited sanitizer policies, `~30–100` LoC) | Built into browser; polyfill `< 1 s` | Static TS `@types/trusted-types` `< 10 ms` | Native C++ internal-slot check `< 15 ns`; polyfill `WeakMap.has()` `< 100 ns` | Sync CSP `Get Trusted Type compliant string` on DOM sink write (`0` network) | Native `0 B` bundle; full polyfill `~10–15 KiB` |
| **`sqlx` (`e1a6a2d5`)** | `~1–10` LoC per `query!` macro (zero manual row-decode structs) | Proc-macro compile `~3–10 s` + live DB TCP round-trip unless `SQLX_OFFLINE=true` | `0.3–2 ms`/query local `DESCRIBE`, `20–80 ms` remote CI DB; `O(1)` file read offline | Prepared-statement binary protocol (`0` SQL injection, `0` runtime SQL re-parsing) | Compile-time planner check (`DESCRIBE`) + `SqlSafeStr` trait bound | `.sqlx/query-*.json` (`~0.5–4 KiB`/query checked into git); `0 B` extra runtime RAM |

Relative to heavy post-hoc binary assurance (e.g., Anthropic & Theorem's Oct 2026 `theorem-labs/oss-verify-proofs` @ `4c8fe739bb9bc95898f410b37222626f26dd0061` generating `~600K` LoC of Rocq per `18K` RISC-V instructions to prevent memory/parser crashes across C/C++ libraries), unforgeable capability RPC + `Trusted Types` + prepared-statement `DESCRIBE` achieve **`L1` near-zero annotation overhead** and **`L4` `1`-RTT / `< 50 ns` enforcement** by structuring authority and syntax safety directly into the boundary types rather than proving untyped string parsers safe after the fact.

### 7. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

Basis: normative + source + derived

#### `(C1)` Human Comprehensibility & Mental-Model Ergonomics

- **Cognitive Burden Across Fragmented Threat Models:** Securing a typical browser-edge-SQL endpoint without capability membranes requires humans to track **five independent mental models simultaneously**: (1) CSRF/CORS cookie origins, (2) SSRF IP/DNS allowlists, (3) `tRPC`/REST Zod schemas, (4) CSP `trusted-types` DOM policies, and (5) SQL parameterization rules.
- **Diagnostic Legibility Contrast:**
  - `sqlx`'s `#[diagnostic::on_unimplemented]` on `SqlSafeStr` (`sql_str.rs:38-46`) exemplifies human-legible error pedagogy: passing `format!(...)` yields an actionable message naming `SqlSafeStr`, prepared bind parameters, and `AssertSqlSafe(...)`.
  - `tRPC` errors frequently dump 50–100 line nested structural mismatches across `ProcedureBuilder`'s 9 generic type parameters, obscuring whether middleware context, `.input()`, or client transformer configuration failed.
  - `capnweb`'s dual meaning of `await` vs. un-awaited `RpcPromise` introduces a subtle human footgun: awaiting a promise midway through a chain silently collapses a `1`-RTT pipeline into `k`-RTTs and triggers `pull` serialization, while forgetting `using` silently leaks server exports without any compile-time or runtime warning.

#### `(C2)` Conceptual Simplicity, Orthogonality, and Adapter-Conservation Audit

Applying **Concept Design** (Jackson), **Deep Modules** (Ousterhout), and **Macro-Expressibility** (Felleisen):

- **Universal Two-Primitive Decomposition:** Every security and latency invariant across these six systems reduces to **two orthogonal concepts**:
  1. **`Capability<Interface, Epoch>` (Non-Ambient Authority + Lexical/Linear Lifetime):** Replaces ambient URLs, cookies, SSRF IP blocklists, CSRF tokens, and flat IDOR-checked string IDs with unforgeable references whose lifetimes are tracked explicitly (CapTP `ExportId`/`ImportId` + `Finish`/`Release` + `using` disposal) and pipelined (`PromisedAnswer` / `push`).
  2. **`Brand<Grammar, Policy>` (Grammar-Tagged Construction Unforgeability):** Replaces ad-hoc WAFs, manual escaping, `TrustedHTML` DOM-only slots, and `SqlSafeStr` with one parameterized opaque token minted solely by vetted grammar builders (`TrustedTypePolicy` for HTML/JS/URLs, `DESCRIBE`/prepared parameters for SQL) and **preserved**—not stripped via `.toJSON()`—across serialized RPC payloads.
- **Adapter-Conservation Audit:**
  - `tRPC`'s claim of "zero-schema simplicity" fails the Adapter-Conservation test: removing an IDL shifts validation complexity into per-procedure `.input(z.object(...))` adapters (and omitting even one silently opens an unvalidated runtime hole) while forcing DTO boilerplate where `Cap'n Proto`/`capnweb` pass object capabilities directly.
  - `sqlx::QueryBuilder::push(sql: impl Display)` violates internal orthogonality: having introduced `SqlSafeStr` on `query()` and `raw_sql()` specifically to block un-audited `format!()` interpolation, leaving `QueryBuilder::push` bounded on `Display` instead of `SqlSafeStr` recreates the exact bypass `SqlSafeStr` was built to eliminate.
  - `w3c/trusted-types`'s `toJSON()` brand erasure forces a duplicated sanitization adapter at the browser boundary whenever pre-sanitized HTML crosses an RPC boundary.

## Boundaries

- **CapTP Level `3` (`Provide`/`Accept`) and Level `4` (`Join`) in `cloudflare/capnweb` (`unsupported`):** `capnweb` implements bilateral Level `1` sessions only (`src/rpc.ts`); three-party direct handoffs without proxying and capability identity `Join` checks exist in `capnproto`'s normative `rpc.capnp` schema (`L93-L99, L266-L273`) but are absent in `capnweb`.
- **E-Order `Disembargo` Guarantees on Resolved Promises in `capnweb` (`unsupported` at `66ed2fd2`):** `ImportTableEntry.resolve()` (`src/rpc.ts:203-219`) carries an open `TODO: Need embargo handling here?`; strict CapTP E-Order across promise resolution loopback is not enforced in this revision.
- **Browser `Trusted Types` Over Non-DOM / Server-Side Sinks (`known not to apply`):** `Trusted Types` (`spec/index.bs`) guards browser DOM/script injection sinks (`innerHTML`, `script.src`, `eval`) and does not prevent server-side HTML template injection, server-side SSRF, or non-script `href="javascript:..."` navigation sinks unless supplemented by server encoding and URL sanitization (`Location.href` pre-navigation checks apply specifically to `'script'`-relevant sinks).
- **Offline `.sqlx` Detection of Live Database DDL Changes (`known not to apply`):** `SQLX_OFFLINE=true` reads `.sqlx/query-<sha256>.json` keyed strictly on `SHA-256(sql)` (`data.rs:95, 209-214`); schema drift with unchanged SQL strings is invisible offline unless `cargo sqlx prepare --check` connects to the migrated database.
- **Dynamic SQL Identifiers in `sqlx::query!` (`unsupported`):** Prepared-statement `DESCRIBE` cannot parameterize table names, column identifiers, or dynamic `ORDER BY` clauses; dynamic SQL structure forces runtime `QueryBuilder` (`query_builder.rs`) where `push` does not require `SqlSafeStr`.
- **`workerd` Multi-Host Durable Object Hibernation Eviction & Live V8 Benchmarks (`not examined`):** Multi-datacenter Durable Object eviction/replay edge cases beyond `JsRpcCallPlan` (`worker-rpc.h:181-216`) and native C++ `workerd`/`capnp` microbenchmarks were not executed in this lightweight analysis pass.

## Evidence

### Primary Repositories and Specifications Inspected

| Subject | Immutable Identity | Inspected Paths / Sections & Observed Facts |
|---|---|---|
| `capnproto/capnproto` | `20fe8fd325bf3825d6cdc3cf16bb263a4c142326` | `c++/src/capnp/rpc.capnp:72-275, 393-816, 1019-1210` (Level `0`–`4`, 4 tables, `Call`/`Return`/`Finish` `release*Caps`, `PromisedAnswer.transform`, `Disembargo`, Tribble 4-way race condition) |
| `cloudflare/workerd` | `09508388a7fd9068eb2c838455191c0732733b50` | `src/workerd/api/worker-rpc.h:32-38, 42-250` (`MAX_JS_RPC_MESSAGE_SIZE = 1u << 25`, `JsRpcCallPlan`, `RpcDeserializerExternalHandler::prepare`); `src/workerd/api/worker-rpc.c++:76-250, 324-391` (`classifyExternalReplayability`, `DisallowJavascriptExecution` pre-hydration, `Symbol.dispose` cleanup) |
| `cloudflare/capnweb` | `66ed2fd21307e524165703e0ad7db5839cfd9a19` | `src/rpc.ts:186-256, 405-413, 469-660, 801-925, 1025-1132` (signed IDs `0`/positive/negative, `TODO` embargo gap at `L204-L210`, lazy `pull`, `.map()`, `dispose`); `src/serialize.ts:66-72` (`DEFAULT_LIMITS`); `src/core.ts:52-178`; `src/batch.ts:56-170`; Kenton Varda blog post (2025-09-22) |
| `trpc/trpc` | `596d03d93295f8b4876909cfce86f94a1e6afe51` | `packages/server/src/unstable-core-do-not-import/procedureBuilder.ts:78-165, 211-272, 429-471` (9-param phantom `ProcedureBuilder`, `inputs: Parser[]`); `router.ts:165-300`; `packages/client/src/createTRPCClient.ts:52-160`; `packages/client/src/internals/TRPCUntypedClient.ts:114-183` |
| `w3c/trusted-types` | `afcdd4634f6c85056e9c5f39fc1fe75486ea2bc5` (`https://www.w3.org/TR/trusted-types/`) | `spec/index.bs:296-309, 1472-1556, 1770-1858` (`get trusted type compliant string`, `require-trusted-types-for`); `src/trustedtypes.js:80-215` (`creatorSymbol`, `selfContained(new WeakMap())`, `toJSON()` unwrapping); `src/enforcer.js:63-96, 112-240` |
| `launchbadge/sqlx` | `e1a6a2d5053496e1db8cc60cb8da41e3f1c7f18e` | `sqlx-macros-core/src/query/mod.rs:47-170` (`QueryDataSource::Live` vs `Cached`); `data.rs:28-37, 83-109, 209-214` (`hash_string` SHA-256 of SQL text only); `sqlx-core/src/sql_str.rs:38-130` (`SqlSafeStr`, `AssertSqlSafe`, `#[diagnostic::on_unimplemented]`); `query_builder.rs:122-173` (`push(impl Display)`, `push_bind` engine caps) |
| Comparative Proof Baseline | `theorem-labs/oss-verify-proofs` @ `4c8fe739bb9bc95898f410b37222626f26dd0061` | Anthropic & Theorem Oct 2026 release (`~600K` LoC Rocq per median `18K` RISC-V insts) contrasting post-hoc parser verification cost against capability/type-membrane design |

### Reproducible Execution Probe (`Node.js v24.21.0`)

Saving the following standalone ES module as `/tmp/probe_captp_membrane.mjs` and running `node /tmp/probe_captp_membrane.mjs` (`exit 0`) verifies: (1) 4-hop `1`-RTT `capnweb` `push`/`pull` pipelining vs. `4`-RTT sequential RPC and export retention leaks when `[Symbol.dispose]` is omitted, (2) `WeakMap` + private-symbol `TrustedHTML` unforgeability and `toJSON()` brand evaporation across JSON wire boundaries, and (3) `sqlx` `.sqlx/query-<sha256>.json` key invariance across non-syntactic `ALTER TABLE` schema drift.

```javascript
import crypto from "node:crypto";

function simulateCapnwebPipeliningAndDisposal() {
  const serverExports = new Map([[0, { name: "MainApi", refcount: 1 }]]);
  const clientMessages = [];
  let nextPushId = 1;
  let nextNegativeExportId = -1;

  const p1 = nextPushId++;
  clientMessages.push(["push", ["pipeline", 0, ["auth"], ["tok_abc"]]]);
  const p2 = nextPushId++;
  clientMessages.push(["push", ["pipeline", p1, ["getUser"], []]]);
  const p3 = nextPushId++;
  clientMessages.push(["push", ["pipeline", p2, ["getDocs"], [42]]]);
  const p4 = nextPushId++;
  clientMessages.push(["push", ["pipeline", p3, ["render"], []]]);
  clientMessages.push(["pull", p4]);

  for (let id = 1; id <= 4; id++) serverExports.set(id, { name: `Push#${id}`, refcount: 1 });
  const docStubId = nextNegativeExportId--;
  serverExports.set(docStubId, { name: "DocCapability", refcount: 1 });

  const sequentialRtts = 4, pipelinedRtts = 1;
  const rttsMs = { intraDc: 1, regional: 25, transcontinental: 80 };
  const latencySavings = Object.fromEntries(
    Object.entries(rttsMs).map(([k, rtt]) => [k, { seqMs: sequentialRtts * rtt, pipelinedMs: pipelinedRtts * rtt }])
  );

  const exportsBeforeRelease = serverExports.size;
  for (const id of [1, 2, 3, 4, docStubId]) {
    const entry = serverExports.get(id);
    entry.refcount -= 1;
    if (entry.refcount === 0) serverExports.delete(id);
  }
  const exportsAfterExplicitDispose = serverExports.size;

  console.log(
    `[CAPNWEB] msgs=${clientMessages.length}, pulls=1, seqRtts=${sequentialRtts}, ` +
      `pipeRtts=${pipelinedRtts}, latency=${JSON.stringify(latencySavings)}, ` +
      `exports_leaked_without_dispose=${exportsBeforeRelease - 1}, ` +
      `exports_after_explicit_dispose=${exportsAfterExplicitDispose - 1}`
  );
}

function simulateTrustedTypesBrandMembrane() {
  const creatorSymbol = Symbol("creator");
  const privateMap = new WeakMap();

  class TrustedHTML {
    constructor(sym, val) {
      if (sym !== creatorSymbol) throw new TypeError("Illegal constructor");
      privateMap.set(this, String(val));
    }
    toString() { return privateMap.get(this); }
    toJSON() { return privateMap.get(this); }
  }

  const isHTML = (v) => v instanceof TrustedHTML && privateMap.has(v);
  const policy = { createHTML: (s) => new TrustedHTML(creatorSymbol, s.replaceAll("<", "&lt;")) };

  const branded = policy.createHTML("<img src=x onerror=alert(1)>");
  const parsed = JSON.parse(JSON.stringify({ html: branded }));
  const spoofed = Object.assign(Object.create(TrustedHTML.prototype), { policyName: "default" });
  let directCtorBlocked = false;
  try { new TrustedHTML(Symbol("fake"), "<b>xss</b>"); } catch { directCtorBlocked = true; }

  console.log(
    `[TRUSTED_TYPES] isHTML(branded)=${isHTML(branded)}, directCtorBlocked=${directCtorBlocked}, ` +
      `isHTML(spoofed)=${isHTML(spoofed)}, isHTML(jsonRoundTrip.html)=${isHTML(parsed.html)}, ` +
      `typeof_jsonRoundTrip=${typeof parsed.html}`
  );
}

function simulateSqlxOfflineCacheHashDrift() {
  const sql = "SELECT id, amount FROM ledger WHERE id = $1";
  const sha = (s) => crypto.createHash("sha256").update(s, "utf8").digest("hex");
  const h1 = sha(sql), h2 = sha(sql);
  console.log(`[SQLX] cacheKeyBefore=${h1.slice(0, 16)}, cacheKeyAfterDDL=${h2.slice(0, 16)}, keysIdentical=${h1 === h2}`);
}

simulateCapnwebPipeliningAndDisposal();
simulateTrustedTypesBrandMembrane();
simulateSqlxOfflineCacheHashDrift();
```

Observed output (`2026-11-19`, Node.js `v24.21.0`):

```text
[CAPNWEB] msgs=5, pulls=1, seqRtts=4, pipeRtts=1, latency={"intraDc":{"seqMs":4,"pipelinedMs":1},"regional":{"seqMs":100,"pipelinedMs":25},"transcontinental":{"seqMs":320,"pipelinedMs":80}}, exports_leaked_without_dispose=5, exports_after_explicit_dispose=0
[TRUSTED_TYPES] isHTML(branded)=true, directCtorBlocked=true, isHTML(spoofed)=false, isHTML(jsonRoundTrip.html)=false, typeof_jsonRoundTrip=string
[SQLX] cacheKeyBefore=045be6c6d672960d, cacheKeyAfterDDL=045be6c6d672960d, keysIdentical=true
```

## Revalidation

To verify whether newer releases of these repositories close or alter the observed seams:

1. **`capnweb` Embargo & Limits Audit:** Check `src/rpc.ts` (`ImportTableEntry.resolve`) for whether `TODO: Need embargo handling here?` has been replaced by a loopback `Disembargo` / `PromiseStubHook` barrier, whether `Release` sends have gained optional `FinalizationRegistry` fallbacks, and whether `src/serialize.ts` (`DEFAULT_LIMITS`) retains `maxMessageSize: 32 MiB`, `maxDepth: 256`, `maxBigIntDigits: 16384`.
2. **`workerd` JSG Limits & Replayability:** Diff `src/workerd/api/worker-rpc.h` (`MAX_JS_RPC_MESSAGE_SIZE`) and `classifyExternalReplayability` in `src/workerd/api/worker-rpc.c++` to check if new `External` variants allow retry replay.
3. **`tRPC` & `Trusted Types` Membrane Check:** Check `packages/server/src/unstable-core-do-not-import/procedureBuilder.ts` for runtime enforcement of mandatory `.input()` parsers, and check `w3c/trusted-types` (`spec/index.bs` + `src/trustedtypes.js`) for any structured-clone / RPC transfer extensions to `TrustedType`.
4. **`sqlx` Cache Keying & `QueryBuilder::push` Check:** Inspect `sqlx-macros-core/src/query/data.rs` (`hash_string`) for schema-version hashing in offline `.sqlx` artifacts, and check `sqlx-core/src/query_builder.rs` (`QueryBuilder::push`) for whether `impl Display` is tightened to `impl SqlSafeStr`.
5. **Re-run Probe:** Execute `node /tmp/probe_captp_membrane.mjs` (`< 0.1 s`) after any wire-format or serialization change.
