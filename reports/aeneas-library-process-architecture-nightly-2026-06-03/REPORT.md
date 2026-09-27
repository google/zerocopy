# Aeneas library and process architecture at nightly-2026.06.03

## Summary

Aeneas `nightly-2026.06.03` is both an installable OCaml library and a one-shot command-line program. Its Dune package exposes a public library named `aeneas` containing the parser, pre-passes, symbolic interpreter, pure translation, extraction machinery, configuration, error handling, and parallel helpers. The public `aeneas` executable is a single `Main` module linked against that library.

This makes in-process integration materially more direct than wrapping a command that hides all translation internals. A library caller can parse LLBC, run `PrePasses.apply_passes`, call `Translate.translate_crate_to_pure` to obtain an in-memory translation context and pure translated crate, and call extraction separately. The higher-level `Translate.translate_crate` combines pure translation with file extraction.

The pinned library is not, however, a ready-made long-lived multi-request service. Much of its run configuration lives in process-global mutable `ref`s in `Config.ml`. Error accumulation lives in process-global mutable `Errors.error_list` and `Errors.unique_errors`; the pinned `Errors.ml` contains no reset helper. The CLI mutates configuration according to command-line/backend choices, processes exactly one LLBC file, checks the global error accumulator, and then exits. Reusing the same OCaml process across requests therefore requires an embedding layer to define request boundaries, reset or snapshot mutable state, and prevent overlapping requests from racing through shared configuration.

There is one intentional reusable runtime resource: `Parallel.ml` owns a lazy Domainslib pool that is created once and reused until process exit. This is process reuse, not semantic incremental translation. The inspected pinned entrypoints do not define a server/daemon protocol, request IDs, per-workspace sessions, incremental LLBC patches, cancellation, or an invalidation model.

For an interactive Anneal architecture, the important result is therefore not “Aeneas must be a subprocess” or “Aeneas already is a server.” The pinned release supports a genuine in-process OCaml library boundary, including an in-memory pure-translation boundary, but a long-lived service would need an explicit lifecycle around mutable global state. A separate process per translation naturally restores the clean-process assumptions of the current CLI; a persistent host can reuse process resources and in-memory values only after it supplies isolation and invalidation semantics that Aeneas itself does not currently provide.

No Aeneas, OCaml, Charon, or Lean execution was performed for this report. The conclusions are from the exact pinned build files and source.

## Applicability

The primary subject is `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`, selected by current Anneal.

This report is specifically about the software boundary available to a caller:

- whether Aeneas is only a command or also a linkable library;
- which translation stages are callable in-process;
- what state is process-global;
- what process lifetime currently provides implicitly;
- whether the pinned program already exposes a long-lived server/session protocol; and
- what source-level constraints matter to an interactive host.

The existing `aeneas-architecture-translation-pipeline-nightly-2026-06-03` report describes the semantic pipeline from LLBC through pre-passes, symbolic execution, pure translation, micro-passes, and backend extraction. This report does not repeat that pipeline inventory. It focuses on the boundary around that pipeline.

“Library” here means the public OCaml Dune library `aeneas`, not the generated Lean standard library under `backends/lean`. “Server” means a long-lived request-driven Aeneas service, not an external process supervisor that repeatedly invokes the CLI.

## Findings

### The package exposes both a public OCaml library and a public executable

The pinned `src/dune` contains two distinct public build products.

The executable stanza names module `Main`, publishes it as `aeneas`, and links the `aeneas` library:

```text
(executable
 (name main)
 (public_name aeneas)
 (package aeneas)
 (libraries aeneas)
 ...
 (modules Main))
```

The following library stanza also publishes `aeneas` and explicitly includes the implementation modules used by translation: `Config`, `Errors`, `LlbcOfJson`, `Parallel`, `PrePasses`, `Translate`, the interpreter modules, the symbolic-to-pure modules, extraction modules, and the LLBC/pure AST modules.

This is a real installed library boundary, not merely source files that happen to be reusable. The generated `aeneas.opam` package builds Dune's `@install` target, and the Dune file declares package documentation as well.

Basis: pinned **build source**.

### The CLI is a thin process boundary around the public library

`Main.ml` opens modules through the `Aeneas` library namespace and delegates the substantive stages to library functions. After parsing and checking the one input file, it calls:

```text
Aeneas.PrePasses.apply_passes m
Aeneas.BorrowCheck.borrow_check_crate ...
Aeneas.Translate.translate_crate ...
```

The executable stanza itself contains only module `Main`. The translation machinery is therefore not trapped inside an executable-only module.

This matters for an interactive host: embedding Aeneas does not require parsing CLI output or reimplementing its translator. A host written in OCaml can link the same modules the CLI uses.

Basis: pinned **build source** + pinned **source**.

### The library exposes a useful in-memory boundary before backend file extraction

`Translate.translate_crate_to_pure` takes an LLBC `crate` and marked IDs and returns:

```text
trans_ctx * translated_crate
```

The `translated_crate` contains translated types, builtin signatures, functions, globals, traits, and trait implementations. `extract_translated_crate` is a later function that consumes that result and writes backend output. `Translate.translate_crate` is only a convenience composition: it calls `translate_crate_to_pure` and then `extract_translated_crate`.

An in-process caller can therefore stop between translation and file extraction and retain the pure translation in memory. That is a stronger integration surface than the CLI's file-in/file-out presentation.

The source does not make that retained value incremental. `translate_crate_to_pure` still consumes a whole crate and computes a fresh translation context. This report found no patch/update operation that mutates a previous translated crate in response to an LLBC edit.

Basis: pinned **source** + **derived** interface distinction.

### Exact CLI behavior consists of more than calling `Translate.translate_crate`

A caller that wants behavior equivalent to the CLI must reproduce setup performed in `Main.ml`.

The pinned CLI:

- parses global `Config` options;
- derives additional option changes from the selected backend;
- precomputes several builtin maps before parallel work;
- accepts exactly one filename;
- loads one serialized LLBC crate;
- clears Charon `short_names` to improve printing determinism;
- rejects LLBC that was not produced with Charon's Aeneas preset;
- applies `PrePasses.apply_passes`;
- then runs borrow checking or translation; and
- treats any entry left in `Errors.error_list` as a failed run.

`Translate.translate_crate` itself starts at the pure-translation stage after those earlier obligations. Linking the public library therefore gives access to the pieces but does not define one high-level “request” API with all CLI preconditions encoded in its type.

Basis: pinned **source**.

### The command-line program intentionally handles one LLBC file and terminates

`Main.ml` collects positional filenames and accepts the input only when the list contains exactly one file. Its comment is explicit: “For now, we only process one file at a time.”

After that one crate is processed, the program prints final diagnostics/timing and exits with status 1 when the global error list is nonempty. There is no top-level loop waiting for another request.

This source shape establishes the normal process lifecycle at the pin: one configured invocation, one LLBC input, one translation/borrow-check result, then process termination.

Basis: pinned **source**.

### The pinned entrypoint does not expose a server or daemon mode

The public Aeneas entrypoint is the `Main` executable above. Its option parser chooses translation backend or borrow-check mode and a single LLBC input; it does not define a server, daemon, RPC, LSP, or request-loop mode.

The complete pinned `src` tree contains the public library, the one `Main` executable module, and the PPX package, but no source subtree or Dune target representing an Aeneas server. This is not evidence that an external program cannot host the library. It means the pinned Aeneas package does not itself provide the long-lived service protocol Anneal would need to call.

Basis: pinned **build/source inventory** + pinned **source**.

### Configuration is process-global mutable state

`Config.ml` begins by describing itself as defining “global configuration options.” The backend is stored in:

```text
let opt_backend : backend option ref = ref None
```

and the module contains many additional mutable refs, including namespace/subdirectory, borrow-check mode, warning/error behavior, backend representation choices, loop translation choices, parallelism, diagnostics, Lean limits, and drop treatment.

`Main.ml` mutates some of these refs based on the selected backend. For example, selecting Lean changes record-field naming, variant naming, tuple/let handling, and pure-call lifting; other backends change different refs.

A process that serves multiple requests cannot assume the next request starts from the module's source defaults. If request A changes a global ref and request B does not explicitly restore it, B can inherit A's setting. An embedding layer therefore needs a complete configuration initialization/reset discipline or a more explicit per-request configuration representation.

Basis: pinned **source** + **derived** lifecycle consequence.

### Error state also survives inside a reused process unless the host clears it

`Errors.ml` defines:

```text
let error_list = ref []
let unique_errors = ref FileLineMap.empty
```

`push_error` appends to those process-global accumulators. In the exact pinned `Errors.ml`, the only assignment to `error_list` after initialization is the append in `push_error`; the module contains no reset helper. The corresponding `unique_errors` map is likewise initialized once and then updated.

The CLI reads these refs after its one translation and exits. Process termination therefore provides error-state cleanup for free.

Because there is no `.mli` hiding these values, a linked caller can technically mutate the refs directly. That is different from Aeneas providing a request-scoped error object or a supported reset protocol. A persistent host must deliberately clear/replace the accumulators at the right boundary and must account for any other process-global state as well.

Basis: pinned **source** + complete mention scan of the pinned `Errors.ml`.

### Concurrent requests cannot safely vary the global configuration without added isolation

Aeneas uses internal parallelism within one translation, but its configuration is shared at module scope. The translation code reads `Config` refs while work is running. Two independent requests in one process that mutate those refs for different backends or options would share the same cells.

The pinned library does not provide a request/session object that owns a configuration snapshot. Therefore a multi-request host needs to serialize configuration-sensitive work, isolate requests into processes, or refactor/fence the global state before allowing overlapping requests.

This is a source-level state-ownership conclusion, not an empirical race report. No concurrent embedding was executed.

Basis: pinned **source** + **derived** concurrency requirement.

### Aeneas deliberately reuses one process-local Domainslib worker pool

`Parallel.ml` contains a lazy persistent `Domainslib.Task` pool. Its comment says the pool is “created once and reused for all parallel operations” to avoid repeated setup/teardown. It is torn down with `at_exit`.

The default `Parallel.parallel_map` and `parallel_filter_map` aliases use this pool when `Config.parallel` is enabled.

A long-lived in-process host can therefore reuse at least this runtime resource across translation operations. A CLI invocation receives the same reuse only within that one process. This is process-lifetime reuse, not semantic incremental compilation: the pool does not identify source snapshots, cache translated declarations, or decide what an edit invalidates.

Basis: pinned **source**.

### The library boundary does not define interactive identity, invalidation, or cancellation

The callable translation boundary accepts an LLBC crate, computes a translation context, produces pure declarations, and optionally writes backend files. The inspected public entry/build surfaces define no:

- workspace or session identity;
- document/source generation number;
- request correlation ID;
- incremental LLBC edit operation;
- declaration-level invalidation API;
- translation cancellation token; or
- protocol for retaining and updating a prior translation.

A long-lived Anneal adapter can add those concepts around Aeneas, but they are adapter semantics rather than capabilities supplied by this pinned Aeneas interface.

Basis: pinned **source/build interface** + **derived** boundary.

### Process isolation and in-process reuse preserve different properties

The current executable model gives each invocation newly initialized OCaml globals and eventually tears down process-local state. It also means any in-memory LLBC, translation context, pure AST, memoized values, and Domainslib pool die with the process.

The public library makes the opposite trade available: a host can keep the process, parsed LLBC, pure translation objects, and reusable runtime resources alive. But the host then owns the lifecycle that process termination previously supplied, especially configuration/error reset and exclusion of conflicting requests.

The pinned source does not choose between these architectures for Anneal. It supplies enough structure for either a subprocess adapter or an in-process Aeneas service, while leaving long-lived request semantics to the caller.

Basis: pinned **source** + **derived** architectural comparison.

## Boundaries

- No Aeneas, OCaml, Charon, Lean, Dune, or Opam execution was performed.
- This report does not prove that an external project can compile against every listed `Aeneas` module without additional package/toolchain configuration; the Dune public-library declaration establishes the intended build surface, not a fresh consumer build.
- The report does not claim that the public library API is stable across Aeneas releases. The inspected revision is the Anneal pin.
- It does not claim that every mutable/global value in Aeneas has been inventoried. `Config` and `Errors` are sufficient to show that request state is not fully encapsulated; a production server should audit all other global caches/loggers/ID generators before relying on process reuse.
- It does not claim that direct assignment to `Errors.error_list` and `unique_errors` is a sufficient reset protocol.
- It does not establish whether two sequential translations in one process produce the same results as two fresh CLI processes. That requires execution and is a separate long-lived-server/batch-equivalence question.
- It does not establish whether concurrent translations would produce an incorrect result. It establishes that differing requests share mutable configuration unless an adapter prevents that overlap.
- It does not characterize Aeneas incremental translation feasibility, declaration-level recomputation cost, or cacheability. Those are separate #3720 subjects.
- The persistent Domainslib pool is a runtime scheduling optimization. It is not evidence of incremental semantic state.
- The report does not prescribe Anneal's final process architecture. That design decision belongs on `main`, not in this reference corpus.

## Evidence

Primary subject:

```text
AeneasVerif/aeneas
ac9f1bc5262a5e4ff1e24ca78617121382202727
release nightly-2026.06.03
```

Pinned build/package source:

- `src/dune`, blob `4152c9de6d84484bf501da543553f3e6af324f9a`: public `aeneas` executable; public `aeneas` library; explicit module list including `Config`, `Errors`, `LlbcOfJson`, `Parallel`, `PrePasses`, `Translate`, symbolic/interpreter/extraction modules; dependency on `charon` and Domainslib.
- `src/dune-project`, blob `4656b7396dc213ebfef5c351986e9d89645078cd`: Dune package/project identity.
- `src/aeneas.opam`, blob `70ea2f7050a98a598b85f982d1e65259c6a66b0a`: generated installable package build through Dune `@install`.

Pinned executable/library source:

- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: command-line parsing; backend-dependent global configuration; exact-one-file input rule; LLBC load; `short_names` clearing; Aeneas-preset check; pre-pass call; translation/borrow-check dispatch; global-error exit policy.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: `translate_crate_to_pure`, `translated_crate`, `extract_translated_crate`, and `translate_crate` composition.
- `src/PrePasses.ml`, blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`: public `apply_passes` stage used by the CLI before translation.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: process-global mutable configuration refs, including backend, borrow-check, output/representation settings, parallelism, diagnostics, and Lean-specific values.
- `src/Errors.ml`, blob `c135674b8601786616c6c20ad81ec388bb8cbfea`: global `error_list` and `unique_errors` refs plus mutation path; no reset helper in the pinned file.
- `src/Parallel.ml`, blob `08f055cf2e87e0164bb3d02dc9f8dde2fc84034c`: lazy persistent Domainslib pool reused across parallel operations and torn down at process exit.
- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: documented Charon → LLBC → `aeneas` command workflow.

Related corpus evidence:

- `aeneas-architecture-translation-pipeline-nightly-2026-06-03` records the internal translation stages and per-declaration failure behavior. This report narrows the question to public build boundaries and process/request lifetime.
- The Charon-side report `charon-library-process-server-0-1-210`, if later adopted, is complementary: Charon's `charon_lib` does not expose its rustc extraction driver through the same kind of public library boundary, while Aeneas's Dune library explicitly contains its translation pipeline.

No evidence above is fresh **execution**.

## Revalidation

For a later Aeneas pin, begin with the build boundary:

1. Inspect `src/dune` and record the public executable/library stanzas, module list, and library dependencies.
2. Inspect the package metadata/Opam generation to confirm that the library remains part of the installed package.
3. Inspect `Main.ml` for the input cardinality, setup done outside library calls, backend-specific configuration mutation, error handling, and any new request/server mode.
4. Inspect `Translate.ml` to see whether `translate_crate_to_pure`, extraction, and the whole-crate input boundary still exist.
5. Inventory mutable process-global state, beginning with `Config.ml`, `Errors.ml`, `Parallel.ml`, builtin caches, logging state, and any ID generators. Look specifically for a newly introduced session/request object or reset API.
6. Search the pinned build/source tree for server, RPC, LSP, daemon, cancellation, incremental-update, and workspace/session entrypoints before carrying forward the “no service protocol” conclusion.

On an execution-capable surface, test the process-lifetime boundary directly.

- Build a tiny external OCaml program against the installed `aeneas` library and confirm it can parse LLBC, apply pre-passes, and obtain `Translate.translate_crate_to_pure`.
- Run two different translations sequentially in one process, deliberately changing backend-sensitive `Config` values between requests. Compare each result with a fresh-process CLI run and preserve all configuration/error state before and after each request.
- Trigger one recoverable Aeneas error, then run a clean translation in the same process. Verify whether stale `Errors.error_list` affects the second request until explicitly cleared.
- Exercise the in-process path both sequentially and with attempted overlapping requests; treat any concurrency experiment as invalid unless the host records exactly how it fences global configuration.
- Measure startup and steady-state cost separately. In particular, distinguish reuse of the persistent Domainslib pool from reuse of semantic translation results.

Those probes would establish what a production interactive adapter must reset or isolate. They still would not establish an incremental invalidation algorithm; that remains a separate research subject.
