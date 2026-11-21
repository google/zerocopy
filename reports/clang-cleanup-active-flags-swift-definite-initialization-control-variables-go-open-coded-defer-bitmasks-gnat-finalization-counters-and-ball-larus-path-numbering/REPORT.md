# Run-time state for conditionally owed destruction and deferred calls: Clang cleanup active flags, Swift definite-initialization control variables, Go open-coded defer bitmasks, GNAT finalization counters and master nodes, and the path-numbering bound

## Summary

When a destructor, finalizer or deferred call is owed on some paths to a release point but not others, a compiler either duplicates code until each copy knows its obligations or keeps run-time state recording which remain. At pinned revisions, with released toolchains probed:

- **Clang:** one `i1` slot per conditional cleanup (`cleanup.cond`; `cleanup.isactive` for out-of-order (de)activation), set `false` before the outermost conditional and `true` at creation, tested separately on the normal and EH paths. From `-O1` it becomes an SSA value (usually the original condition); duplication removes the re-test only when no `invoke` intervenes. With `-fexceptions` the re-test survived every jump-threading threshold tried (0–1000, Clang 19.1.7) and cost 0.3–1.1 ns/call at `-O2`, including a lost tail call.
- **Swift DI:** a static `No`/`Yes`/`Partial` lattice per element; only if some store or destroy is path-dependent does it allocate one `Builtin.IntN` control variable (N tracked elements, +1 for conditional `self` initialization), and only `Partial` elements get bit tests.
- **Go:** one `uint8` `deferBits` per function, one bit per `defer` site, only if ≤8 defers, none in a loop, `returns × defers ≤ 15`, no `-N`/race instrumentation; else stack/heap defer records. Bit stores survive even when exit tests fold, because panics read the byte via funcdata. go1.27.3: 8 open-coded defers 26 ns/call vs 88–103 ns for 9 records; 4 defers × 3 returns 13 ns vs 46 ns at 4 returns.
- **GNAT:** a 24-byte `Master_Node` per scope object whose `Object_Address` doubles as the active flag; one `Integer` counter per record component list driving `case C is when n => goto Ln`; one `Integer` count per array. On GNAT FSF 16.1.0, the 4th of 6 element `Initialize` calls raising produced 9 `Finalize` calls where 3 `Initialize` calls had completed: the array's counter cleanup ran, then an enclosing handler finalized the whole array (claim strength under Boundaries).
- **Rust RFC 320:** one stack-local boolean per *dynamic drop obligation*, i.e. union minus intersection of predecessor obligation sets at a merge; the exact flag set is left unspecified; "static drop semantics" (early drops equalizing sets) was rejected as non-intuitive.
- **Minimum information:** ⌈log₂ s⌉ bits at a release point, s = reachable obligation sets; a Ball–Larus path number (⌈log₂ P⌉ bits, P acyclic paths) always suffices since the set is a function of the path. Flags use k bits; prefix counters ⌈log₂(k+1)⌉. No examined compiler sizes its state by s.

## Applicability

Subjects and their relationship (all identities are in `REPORT.json`):

| Role | Subject | What was done |
| :--- | :--- | :--- |
| C++ front end source | `llvm/llvm-project` @ `d71d3a9b75d9b21fc8fc8069cce2de71023b5b41` (`clang/lib/CodeGen`) | source read |
| C++ toolchain probed | Debian clang 19.1.7 (`1:19.1.7-10.1+build1`, x86-64) | executed |
| Swift DI source | `swiftlang/swift` @ `df95e655b44760b7d16a7da561cbedb3f4294fed` | source read only (no Swift toolchain run) |
| Go source | `golang/go` @ `2dbf8b413af37486224cd62bae53dafc516ce875` | source read |
| Go design document | `golang/proposal` @ `83ee2aaf9fdcc1a1cf4bb4d20216fc979635cf04`, `design/34481-opencoded-defers.md` | documentation read |
| Go toolchain probed | go1.27.3 linux/amd64 (Debian `golang-1.27-go 1.27.3-1`) | executed |
| Ada front end source | `gcc-mirror/gcc` @ `88f95ebe13064c5745d2571bf19b09ba641bf6fe` (`gcc/ada`) | source read |
| Ada toolchain probed | GNAT FSF build `gnat-x86_64-linux-16.1.0-1` from `alire-project/GNAT-FSF-builds`, archive sha256 `9f74f58a827a2ad40dd84c72a413e75ea52888e0d8f7e252fba4d26762402703`, reporting `gcc (GNAT-FSF-builds) 16.1.0` | executed |
| Drop-flag proposal | `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/0320-nonzeroing-dynamic-drop.md` | normative text of the proposal |
| Normative languages | ISO/IEC 14882 ([except.ctor], read in the public working draft at eel.is); Ada 2022 RM 7.6.1 (ada-auth.org HTML) | normative |
| Theory | Knuth–Stevenson 1973; Ball–Larus 1994, 1996 | literature |

Source pins and probed binaries differ: execution results describe the released toolchains, source findings the pinned trees. The probes' IR value names and flag-slot shapes match what the pinned source emits, which is the evidence that they illustrate the same mechanism. Probes ran on x86-64 Linux (Xeon @ 2.60 GHz, shared host), one CPU for timing, under a 4 GiB cap and a 60 s timeout. Timings are three-repetition magnitudes with visible noise, not portable constants.

## Findings

### 1. A common model

An *obligation* is a pending release action: a destructor, a `Finalize`, or a deferred call. At a program point p, let **O(p)** be the set of obligations pending on a given path. A *conditional* obligation is one that is in O(p) on some paths reaching a release point r and not on others. At r, the compiler must distinguish the **s(r)** distinct sets reachable there. The examined systems use four encodings:

| Encoding | Bits at r | Who uses it | Requirement |
| :--- | :--- | :--- | :--- |
| One flag per conditional obligation | k (number of conditional obligations) | Clang, Swift DI (per element), Go (per defer site), RFC 320 | none |
| Counter of completed prefix | ⌈log₂(k+1)⌉ | GNAT records and arrays; Clang partial arrays (end-of-prefix pointer) | obligations are created in a fixed order, so the sets are prefixes |
| PC or sentinel encodes state | 0 extra bits: state from the PC, or a null sentinel in a field stored anyway | Clang landing pads at `-O2`; GNAT `Master_Node.Object_Address` | a distinct PC per state (unwinder tables), or a sentinel value |
| Duplication | 0 | jump threading and tail duplication when the budget allows | code grows with s(r) |

Basis: derived. Necessity follows by counting: two paths reaching r with different sets need different stored states, unless the PC already differs. Sufficiency of a path number: O(r) is a function of the path, so any injective path encoding (Finding 7) determines it.

### 2. Clang: cleanup active flags

Mechanism. Basis: source, `clang/lib/CodeGen` at the pinned commit.

- `pushFullExprCleanup` (`CodeGenFunction.h:961`) pushes a plain cleanup unless `isInConditionalBranch()` (`:1426`, i.e. `OutermostConditional != nullptr`, maintained by the RAII class `ConditionalEvaluation`, `:1400`); otherwise it saves arguments via `saveValueInCond`, pushes `EHScopeStack::ConditionalCleanup<T>` and calls `initFullExprCleanup()`.
- `createCleanupActiveFlag()` (`CGCleanup.cpp:282`–`295`) allocates an `i1` named `"cleanup.cond"`, stores `false` via `setBeforeOutermostConditional` (end of the block that starts the outermost conditional, `CodeGenFunction.h:1428`), and stores `true` at the creation point. `initFullExprCleanupWithFlag` (`:297`) records it in `Address ActiveFlag` (`CGCleanup.h:267`) and sets the 1-bit `TestFlagInNormalCleanup`/`TestFlagInEHCleanup` (`CGCleanup.h:97`, `:101`).
- `EmitCleanup` (`CGCleanup.cpp:568`–`591`) loads `"cleanup.is_active"` and branches around the cleanup; normal and EH emission each test the flag.
- `SetupCleanupBlockActivation` (`:1228`–`1285`, used by `ActivateCleanupBlock` `:1288` and `DeactivateCleanupBlock` `:1300`) creates `"cleanup.isactive"` only for a normal cleanup or an EH cleanup activated in a conditional or already used; its comment: "It would be good if we had some way of determining if there were extra uses *after* the change-over point." Conditional lifetime-extended temporaries use `pushCleanupAfterFullExpr` (`CodeGenFunction.h:979`).
- Partial arrays use a counter: `CGExprAgg.cpp:623` allocates `"arrayinit.endOfInit"` (one past the last constructed element) and `pushIrregularPartialArrayCleanup` (`CGDecl.cpp:2669`) destroys `[begin, *endOfInit)`.

Measured state. Basis: execution, Clang 19.1.7, `support/clang/cond_cleanup.cpp`: `t_cond` = `use(c ? S(x).v : x)`; `t_two` = two independent conditional temporaries; `t_ext2` = `const R &r = c ? R{S(x)} : R{g}` (lifetime-extended in one arm); `t_ext` = `c ? S(x) : S(x+1)` bound to a reference; `t_arr` = `S a[4] = {...}`; `t_new` = `new S(x)`; `t_cond_dup` = hand-duplicated `t_cond`. `S` has out-of-line constructor and destructor. In the table, "slot/st/ld" counts the named flag allocas, flag stores and flag loads in IR emitted with `-fno-discard-value-names`, `jcc` counts conditional jumps in the object code, and "bytes" is the `.text` size of the function.

| Function | `-fexceptions -O0` slot/st/ld, jcc, bytes | `-fexceptions -O2` jcc, bytes | `-fno-exceptions -O0` slot/st/ld | `-fno-exceptions -O2` jcc, bytes |
| :--- | :--- | :--- | :--- | :--- |
| `t_cond` | 1/2/2, 3, 145 | 3, 82 | 1/2/1 | 1, 55 |
| `t_two` | 2/4/4, 6, 262 | 8, 196 | 2/4/2 | 4, 121 |
| `t_ext2` | 1/2/2, 3, 167 | 3, 85 | 1/2/1 | 1, 55 |
| `t_ext` | 0/0/0, 1, 126 | 0, 75 | 0/0/0 | 0, 54 |
| `t_new` | 0/0/0, 0, 86 | 0, 61 | 0/0/0 | 0, 40 |
| `t_arr` | 0 flags, 1 `endOfInit` slot, 4, 317 | 1, 233 | 0 flags | 0, 145 |
| `t_cond_dup` | 0/0/0, 1, 125 | 1, 81 | 0/0/0 | 1, 55 |

Observations. Basis: execution plus derived.

- At `-O0` each conditional cleanup costs one byte slot, two stores (`false` before the conditional, `true` in the arm) and one load per use (normal path; plus the EH path with `-fexceptions`). `t_ext` needs no flag (both arms yield one prvalue materialized once); `t_new` needs none (deactivation point dominates the uses).
- From `-O1` no flag slot survives anywhere; the flag is the original condition held in a callee-saved register. With `-fexceptions`, `-O2` `t_cond` keeps `c` in `%bl`, calls `use`, and re-tests (`test %bl,%bl; je`) before the destructor and again in the landing pad. With `-fno-exceptions` the join is threaded into the shape of `t_cond_dup` (one branch, tail call on the false path).
- Jump-threading sweep (`support/clang/jt_sweep.sh`, `-O2 -mllvm -jump-threading-threshold=N`): without EH, `t_cond` keeps the re-test (2 jcc, 56 bytes) for N ≤ 3 and is threaded (1 jcc, 55 bytes) for N ≥ 4; with `-fexceptions` it stays at 3 jcc, 82 bytes for every N in {0, 3, 4, 5, 6, 50, 1000} — the `invoke` of `use` separates the flag's producer and consumer across an EH edge.
- `t_two` without EH at `-O2`: the second condition is removed by duplicating the tail (`use` + one destructor) and the first stays a register re-test in both copies — 2 copies, not 2² = 4.
- `t_arr` with EH at `-O2`: the end-of-prefix pointer survives as the bound of one shared partial-destroy loop in one landing pad. The landing pad reached when `use` throws destroys all 4 elements in straight-line code, so its state is implied by which landing pad runs.

Run time. Basis: execution, `support/clang/bench.cpp` (5×10⁷ calls from a separate translation unit, `-fexceptions`, three repetitions).

| Pattern of `c` | `-O2` flag (`t_cond`) ns/call | `-O2` duplicated ns/call | `-O0` flag | `-O0` duplicated |
| :--- | :--- | :--- | :--- | :--- |
| alternating | 4.02–4.19 | 3.00–3.07 | 7.26–8.96 | 6.70–10.06 |
| always true | 3.28–3.49 | 2.97–3.04 | 8.02–11.05 | 8.26–8.48 |
| always false | 2.67–2.71 | 1.78–1.79 | 4.89–6.80 | 4.65–6.21 |

At `-O2` the flag version is 0.3–1.1 ns/call slower; in the always-false case the cause is not a branch but the lost tail call and frame needed to keep `c` live across `use`. At `-O0` noise exceeds the difference.

### 3. Swift: definite-initialization control variable

Basis: source, `lib/SILOptimizer/Mandatory/` at the pinned commit; not executed.

- **Elements.** `DIMemoryObjectInfo` flattens the memory object into elements: tuple leaves, or stored properties of `self` in an initializer, plus one extra element for derived classes, which models whether `super.init` ran (`DIMemoryUseCollector.h:40`–`66`, `getNumMemoryElements()` at `:108`).
- **Static lattice.** `enum class DIKind : uint8_t { No, Yes, Partial }` (`DefiniteInitialization.cpp:104`). The availability sets store 2 bits per element at compile time (`:173`–`177`), and the dataflow merges predecessors with `Partial` for disagreement.
- **Dynamic state only on demand.** After liveness is computed, the pass sets `ControlVariable = handleConditionalInitAssign()` only if `HasConditionalInitAssign || HasConditionalDestroy || HasConditionalSelfInitialized` (`:1267`). The allocation is then marked `setDynamicLifetime()`. For a noncopyable type, the pass diagnoses `noncopyable_dynamic_lifetime_unsupported`: dynamic lifetime is rejected rather than tracked.
- **Width.** `handleConditionalInitAssign` (`:3070`) creates `alloc_stack` of `SILType::getBuiltinIntegerType(NumMemoryElements, ...)` (`:3083`) at function entry. `NumMemoryElements` is the element count, incremented by one if `HasConditionalSelfInitialized`. The pass stores zero right after the memory allocation and ORs in `Use.getElementBitmask(...)` at each full initialization.
- **Untracked bits.** Elements touched only by trivial stores are skipped (`onlyTouchesTrivialElements`, `:3130`) except for root-class `self`, whose trivial fields must be tracked to choose `partial_dealloc_ref`. Their bits are allocated but never maintained.
- **Conditional destroys.** `handleConditionalDestroys` (`:3336`) handles each element at a release: `No` means skip, `Yes` means destroy unconditionally, and `Partial` means `testControlVariableBit` followed by `InsertCFGDiamond` around the destroy (`:3383`–`3418`).
- **Conditional assignments.** A path-dependent init-or-assign store becomes a CFG diamond that destroys the old value only when the bit says it is live.

Consequence. Basis: derived. Swift's allocated width is N bits per memory object even if only one element is `Partial`. Tests are emitted only for `Partial` elements, so the dynamic cost scales with the number of `Partial` elements and the footprint with N. Any later lowering of the control variable (promotion of the `alloc_stack` by mem2reg, folding of known bits) was not examined.

### 4. Go: open-coded defers and the `deferBits` mask

Eligibility. Basis: source, at the pinned commit.

| Rule | Location | Effect when violated |
| :--- | :--- | :--- |
| `NumDefers > maxOpenDefers` with `const maxOpenDefers = 8`, or `n.DeferAt != nil` | `walk/stmt.go:110`, `walk/walk.go:308` | `SetOpenCodedDeferDisallowed(true)`. The comment says: "we use a single byte to record active defers" |
| `n.Esc() != ir.EscNever` ("this defer occurs in a loop") | `walk/stmt.go:117` | disallowed |
| `base.Flag.N == 0` (no `-N`), `Debug.NoOpenDefer == 0`, not 386 shared/dynlink, no race enter/exit instrumentation, every result parameter on the stack | `ssagen/ssa.go:407`–`433` | `hasOpenDefers = false` |
| `NumReturns*NumDefers > 15` | `ssagen/ssa.go:436` | disallowed. The comment says: "we are generating defer calls at every exit" |
| a call to `runtime.deferrangefunc` (range-over-func body sharing the frame) | `walk/expr.go:625`–`630` | disallowed |

Fallback records are stack-allocated (`callDeferStack`) when `EscNever` and `DeferAt == nil`, else heap-allocated (`ssa.go:1741`–`1745`). `test/defererrcheck.go` pins the outcomes, including a defer after a backward `goto` being "considered to be inside a loop" (f6) and f7 (4 defers × 3 returns, open-coded) vs f8 (4 × 4, stack records).

Code generation. Basis: source. `deferBitsTemp` is a `TUINT8` autotmp (`ssa.go:454`) zeroed in the entry block and kept alive by `OpVarLive` so that "stores to deferBits are not eliminated, even if all checking code on deferBits in the function exit can be eliminated" (`:462`–`467`). `openDeferRecord` (`:4868`) saves the closure to a stack slot, then ORs `1<<index` into the mask and stores it (`:4892`–`4894`). `openDeferExit` (`:4951`) tests bits in reverse, clearing and storing each "so we will not try to re-run this defer call if this defer call panics", then calls the closure. `emitOpenDeferInfo` (`:279`) emits funcdata of two varints (offset of `deferBits`, offset of the first closure slot). At panic, `initOpenCodedDefers` (`runtime/panic.go:1068`) finds the byte (zero = nothing pending) and `nextDefer` (`:937`) repeatedly takes the top set bit (`i := 7 - uintptr(sys.LeadingZeros8(bits))`, `:969`), clears and stores it, and returns that closure.

Design document. Basis: documentation, `34481-opencoded-defers.md` (2019-09-23): Go 1.13 `defer` took "about 35ns (reduced from about 50ns in Go 1.12)" vs "about 6ns" for a direct call (`:14`–`16`); stack-allocated records "applies to 363 out of the 370 static defer sites in the `cmd/go` binary and speeds up this case by 30%" (`:69`–`70`); "the compiler assigns a bit for every `defer` site" (`:147`); "To minimize code size, we currently make deferBits to be 8 bits" (`:325`); pointer-containing argument slots are zeroed at entry for the GC. It reports no code- or frame-size measurement, and the `returns × defers ≤ 15` rule is only in the source.

Measured. Basis: execution, go1.27.3 amd64, `support/go/`. Frame and code sizes come from `-gcflags=-S` (`locals=`, `size=`). Kinds come from `-gcflags=-d=defer`. Times are `go test -bench`, 5×10⁶ iterations, three counts, one CPU.

| Function | Kind (optimized) | Frame bytes | Code bytes | ns/op | Kind / frame / code at `-N -l` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `NoDefer` (explicit release) | – | 24 | 67 | 4.56–4.63 | – / 32 / 85 |
| `DeferUncond` | open-coded | 56 | 143 | 4.36–4.39 | stack / 112 / 165 |
| `DeferCond`, c=true | open-coded | 56 | 173 | 4.67–4.84 | stack / 112 / 197 |
| `DeferCond`, c=false | open-coded | 56 | 173 | 2.41–2.43 | – |
| `ManualCond` (hand duplication) | – | 24 | 101 | 4.47–4.49 | – / 40 / 127 |
| `Defer8` | open-coded ×8 | 96 | 329 | 25.9–26.2 | stack / 416 / 380 |
| `Defer9` | stack ×9 | 456 | 369 | 87.7–103.3 | stack / 464 / 414 |
| `DeferLoop` (n=1) | heap | 56 | 206 | 48.8–53.7 | heap / 80 / 221 |
| `Defer4Ret3` (12 ≤ 15) | open-coded ×4 | 64 | 374 | 12.9–13.1 | stack / 232 / 405 |
| `Defer4Ret4` (16 > 15) | stack ×4 | 216 | 404 | 45.7–47.6 | stack / 232 / 471 |
| `PanicOpen` (panic + recover) | open-coded | 56 | 165 | 242–268 | – |
| `PanicLoop` (panic + recover) | heap | 56 | 233 | 304–326 | – |

Derived from the table: crossing the 8-defer limit raised time 3.4–4.0× (26 → 88–103 ns) and frame 4.75× (96 → 456 bytes); crossing `returns × defers` raised time ≈3.6× (13 → 46 ns). The `DeferCond` listing realizes the mask as `MOVB $0, autotmp+15(SP)` at entry, `MOVB $1` in the arm, and at exit a re-test of the spilled `c` (not the byte) followed by `MOVB $0` and an indirect `CALL AX` — the test folded to the condition but all three byte stores survived, as `OpVarLive` requires; closure, captured argument and closure pointer take three 8-byte slots. Versus hand duplication: +32 frame bytes, +72 code bytes, +0.2–0.4 ns/call.

### 5. GNAT: master nodes, record state counters, array counters

Basis: source at the pinned commit, plus execution on GNAT FSF 16.1.0 (`support/gnat/`).

- **Scope objects.** `exp_ch7.adb:100`–`270`: each controlled `X` gets `XMN : aliased System.Finalization_Primitives.Master_Node`, attached after successful initialization by `Attach_To_Master (X'address, CtrlFD'unrestricted_access, XMN'unrestricted_access, Mnn)` (a single object "degenerates into a single master node", `Attach_To_Node`). The node is `record Finalize_Address; Object_Address : System.Address; Next : Master_Node_Ptr; end record` (`libgnat/s-finpri.ads:185`); `Finalize_Object` does `if Addr /= Null_Address then Node.Object_Address := Null_Address; ... Finalize_Address (Addr)` (`s-finpri.adb:362`–`374`), so the address is both active flag and second-call guard. Measured `Master_Node'Size` = 192 bits (24 bytes). The probe's `Pick` (`return (if Flag then Make (3).V else 0)`) gets one node declared before the `if`, attached only in the then-arm, finalized unconditionally at block end.
- **Record init procedures.** `Build_Record_Init_Proc` creates `Cnn : Integer := 0` per component list with controlled parts (`Make_Counter`, `exp_ch3.adb:3826`), increments it after each controlled component ("Preserve initialization state in the current counter", `:4248`, `:4422`), and declares a local `_Finalizer` from `Make_Local_Deep_Finalize` (`:3718`–`3726`; `exp_ch7.adb:8573`), i.e. `Make_Deep_Record_Body (..., Is_Local => True)` whose logic is "dictated by state counters" (`exp_ch7.adb:666`–`674`). Observed `-gnatG` for a 3-component record: `case C1 is when 3 => goto L3; when 2 => goto L2; when 1 => goto L1; when others => goto L0; end case; <<L3>> Finalize (v.c); <<L2>> Finalize (v.b); <<L1>> Finalize (v.a); <<L0>>`. With the 2nd `Initialize` raising, exactly 1 `Finalize` ran.
- **Arrays.** `Build_Initialize_Statements` (`exp_ch7.adb:5682`–`5740`) wraps each `[Deep_]Initialize (V (J))` in a handler: `Counter := Counter + 1` on success; on exception `Counter := V'Length - Counter`, then a reverse walk skipping (decrementing) while `Counter > 0` and finalizing the rest — seen verbatim in `-gnatG` (`C63s := v'length(1) - C63s`).
- **Observed over-finalization.** Basis: execution plus source. For `A : Arr (1 .. 6)` with the 4th element's `Initialize` raising, the trace was `fin(V=3) fin(V=2) fin(V=1) fin(V=0) fin(V=0) fin(V=0) fin(V=3) fin(V=2) fin(V=1)`, which is 9 calls. `V` records the completion order of `Initialize`, and 0 means it never completed. The first three calls come from the array's own counter-driven handler.
  - The other six come from an enclosing block emitted by `Build_Default_Initialization`, `exp_ch3.adb:1103`–`1154` at the pinned commit:

    ```ada
          --  Build a special finalization block when both the object and its
          --  controlled components are to be initialized. The block finalizes
          --  the components if the object initialization fails. Generate:
          ...
          if Has_Controlled_Component (Typ)
            and then Present (Comp_Init)
            and then Present (Obj_Init)
            and then Exceptions_OK
          then
             Init_Stmts := Comp_Init;

             Fin_Call :=
               Make_Final_Call
                 (Obj_Ref   => New_Object_Reference,
                  Typ       => Typ,
                  Skip_Self => True);
    ```

    and lines 1145–1154 place `Obj_Init` in that block with an `others` handler holding `Fin_Call, Make_Raise_Statement (Loc)`.
  - For an array, `Obj_Init` is `Deep_Initialize`, which already finalized its prefix; the handler's `Deep_Finalize (A, False)` then finalizes all six elements (`F` is ignored for arrays): expansion `arrDI (a); ... exception when others => arrDF (a, false); raise;`. RM 7.6.1(4) finalizes an object "if the object was successfully initialized"; NOTE 4 asks `Finalize` to tolerate "a second time"; elements 4–6 never completed `Initialize`.
- **Code size** (`-O2`, bytes, body + `.cold`): `rec3IP` 307+236, `arrDI` 171+223, `use_arr` 396+254, `Pick` 260+36; all levels in `support/gnat/out_gnat.txt`.

### 6. Rust RFC 320: stack-local drop flags

Basis: normative text of the proposal at the pinned commit.

- "No struct or enum has an implicit drop-flag" (`### Drop obligations`, line 99).
- At a merge point with predecessor sets S₁…S_k, the dynamic drop obligations are `(S_1 | … | S_k) \ (S_1 & … & S_k)` (lines 117–126).
- For each, "If necessary, it will inject and maintain boolean flag", and "we do not specify the precise set of boolean flags that are injected" (`### Stack-local drop flags`, lines 144–156).
- The analysis is control-flow-based, not lexical. Arms that never meet may have unrelated sets.
- Rejected alternatives:
  - The withdrawn static drop semantics (RFC PR #210, which drops values early so that sets agree at every merge) was rejected because "its policy for inserting early drops into the code is non-intuitive". Its `NoisyDrop`/`QuietDrop` mitigations "were deemed unacceptable" (lines 50–68).
  - Eager drops (RFC PR #239) "would probably invalidate a number of RAII style coding patterns" (`## Alternatives`, line 494).
- The proposal's stated motivation was the cost of the per-value hidden flag plus memory zeroing: for example, `struct Foo { x: u32, y: u32 }` doubles from 8 to 16 bytes, and the waste is "strewn throughout the heap".
- An optional lint would report dynamic drop obligations so that developers can see "how many boolean dynamic drop flags are potentially being injected".

### 7. Minimum information: optimal counter placement and path numbering

Literature. Basis: documentation (access level noted in Evidence).

- Knuth–Stevenson 1973: "A procedure recently devised by A. Nahapetian, for reducing the number of measurements needed to determine all the execution frequencies in a computer program, is shown to be optimal"; Ball–Larus 1994 credit it with "the minimum number of vertex counters necessary and sufficient for vertex profiling".
- Ball–Larus 1994: an edge-counter placement works "iff (E – Ecnt) contains no (undirected) cycle", so the minimum is "|E| − (|V| − 1)" (the uncounted edges form a spanning tree, chosen by expected or measured frequency so counters land on cold chords); optimal placement cut overhead "from 10-225 percent to 5-91 percent"; optimal vertex profiling with edge counters "seems to be a hard problem ... We believe the problem is NP-complete".
- Ball–Larus 1996: edge increments sum to a path value with "the maximum value for any path is the number of unique paths through a CFG (minus one)"; the count is "in the worst case ... still exponential"; 32-bit states, hash tables beyond "4000–6000 paths" on SPARC, truncation past "100,000,000"; overhead "averaged 31% (6–97%)" vs 16% for edge profiling on SPEC95.
- Vaswani–Nori–Chilimbi 2007: compact numbers for "interesting paths" only, "an optimality result for the compactness of path numbering", overhead "from 50% on average ... to 15% on average".

Relation to obligation state. Basis: derived; no published result connecting the two problems was found.

1. **Upper bound.** O(r) is a function of the acyclic path to r, so s(r) ≤ P(r) and a Ball–Larus path register (⌈log₂ P(r)⌉ bits) always determines the owed releases. It can be far from tight. Diamonds that create no obligation multiply P but not s, and every examined compiler ignores them.
2. **Lower bound.** Fewer than ⌈log₂ s(r)⌉ stored bits cannot work unless the PC distinguishes the states. This is how Clang's EH landing pads and full duplication escape the bound.
3. **Placement analogy.** Ball–Larus instrument only the chords of a spanning tree and infer the rest. The compilers' flag stores occur only on acquisition edges, with initialization hoisted to a dominator: before the outermost conditional (Clang), at entry (Go), or after the allocation (Swift). RFC 320 restricts flags to obligations whose membership differs at some merge, which plays the role of chords. A frequency-weighted *minimum-store* placement of obligation flags, analogous to optimal counter placement, was not found in the literature or in these compilers.
4. **Readability mid-path.** Go needs the state at any panic point. Per-site bits are monotone (set at `defer`, cleared at the call), so any prefix is meaningful. A Ball–Larus partial sum also identifies the path prefix, but no compiler uses one for release state.

Bits used and bits needed by the probes. s(r) counts the sets reachable at the release point. Basis: derived from Findings 2–5.

| Probe | Conditional obligations k | s(r) | ⌈log₂ s(r)⌉ | State used |
| :--- | :--- | :--- | :--- | :--- |
| Clang `t_cond` | 1 | 2 | 1 | 1-byte slot at `-O0`; 0 stored bits at `-O2` (the condition stays live in a register) |
| Clang `t_two` | 2 independent | 4 | 2 | 2 slots at `-O0`; 1 register re-test + 1 duplication at `-O2` without EH |
| Clang `t_arr` (4 elements, EH) | 4, ordered | 5 | 3 | 64-bit end-of-prefix pointer |
| Go `DeferCond` | 1 | 2 | 1 | 8-bit `deferBits`, 1 bit live |
| Go `Defer8` at a panic point | 0 conditional at exit; the pending set varies by PC inside the body | 1 per PC | 0 given the PC | 8 bits |
| GNAT `Rec3` init | 3, ordered | 4 | 2 | 32-bit counter |
| GNAT `Arr (1..6)` init | 6, ordered | 7 | 3 | 32-bit counter |
| GNAT `Pick` | 1 | 2 | 1 | 64-bit address field of a 24-byte node |
| Swift, N tracked elements, initialized in any order | N | up to 2^N | up to N | N-bit integer |

### 8. Cross-system comparison

| Aspect | Clang | Swift DI | Go open-coded | GNAT | RFC 320 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Unit tracked | each conditional cleanup | each memory element | each `defer` site | each object (node); each component list (counter); each array (counter) | each dynamic drop obligation |
| Representation | `i1` alloca | `Builtin.IntN`, one allocation | `uint8` + closure slots + funcdata | 24-byte node; `Integer` counters | boolean |
| Static elimination | the slot is promoted at ≥ `-O1`; duplication removes the re-test if no `invoke` intervenes | lattice `No`/`Yes` per element; no variable unless some use is `Partial`/conditional | tests may fold to the condition; stores kept (`OpVarLive`) | none observed (counters and nodes are unconditional) | "some compiler analysis may be able to identify" flags not needed |
| Hard limits | none found | noncopyable types with dynamic lifetime rejected | ≤ 8 defers, no loops, returns × defers ≤ 15 | none found | n/a |
| EH or panic path | the same flag is tested in the EH cleanup | n/a (no unwinding through initializers examined) | the runtime reads the byte via funcdata | `Finalize_Object` checks the address; the counter drives `case`/`goto` | n/a |

### 9. Performance and footprint by level

| Level | Clang | Swift DI | Go | GNAT |
| :--- | :--- | :--- | :--- | :--- |
| L1 authoring/maintenance | not measured | not measured | not measured | not measured |
| L2 toolchain build | not measured | not measured | not measured | not measured |
| L3 compile latency | whole probe matrix (20 compiler invocations: 10 configurations × IR + object, 9 functions): 2.09 s wall, peak RSS of the largest child 110,428 KB (measured with `/usr/bin/time -v`) | not measured | static probe (4 builds) finished inside the 60 s cap; per-compile time not measured | not measured |
| L4 generated code | +0.3 to +1.1 ns/call at `-O2` (Finding 2) | not measured | Finding 4 table | not measured (correctness probe only) |
| L5 certificate checking | not applicable (no certificates) | not applicable | not applicable | not applicable |
| L6 footprint | 1 byte per flag at `-O0`; 0 bytes at ≥ `-O1` in all probes; a callee-saved register across calls | N bits per tracked object (source) | 1-byte mask + one 8-byte closure-pointer slot per defer (plus closure storage); frames 24 → 56 (1 defer), 96 (8 open) vs 456 (9 records) | 24 bytes per controlled object (node), 32-bit `Integer` per counter (`Integer'Size` = 32 measured, GNAT 16.1.0 x86-64) |

### 10. Comprehensibility and model refinement (C1, C2)

- **C1.** The per-obligation flag is the easiest scheme to audit locally: each flag maps one-to-one to a source construct. Go's `-d=defer` diagnostic names the mechanism chosen per site, and Swift's DI has a debug printer of the lattice (`n`/`y`/`p` per element, `DefiniteInitialization.cpp:237`–`241`).
  - Counters require nonlocal reasoning: the GNAT finalizer's `case` jumps into the middle of a straight-line sequence, and correctness depends on the init order matching the finalization labels.
  - The GNAT array over-finalization (Finding 5) shows the cost. Two mechanisms, a counter inside `Deep_Initialize` and a whole-object handler around it, each locally plausible, compose into double finalization.
  - Clang's EH-path re-test cannot be diagnosed from source. It is visible only in assembly.
- **C2.** One invariant ("run each pending release exactly once, in reverse creation order") is enforced by five realizations. Some differences are essential:
  - Go must make the state readable by a runtime unwinder from a frame alone, which forces memory-resident bits.
  - Ada must survive exceptions raised by `Initialize` itself.

  Others are incidental: Clang's choice between `cleanup.cond` and `cleanup.isactive` names one concept twice. A single abstraction would make the special cases ordinary: an obligation set per release point, represented by the cheapest injective encoding of its reachable values (flags, prefix counter, PC, or duplication), chosen by s(r), k, and whether the state must be read without the PC. No examined compiler implements that selection. It is a design hypothesis, not a finding.

### 11. How these mechanisms are validated (V1–V4)

- **V1.** Go pins the eligibility rules with `test/defererrcheck.go`, which is an errorcheck test on `-d=defer` diagnostics. Its f6 case also pins a known over-approximation: a backward `goto` is treated as a loop. The probes here are differential non-vacuity checks: the duplicated twin must yield identical results (the timing driver accumulates and prints `acc`), and the GNAT trace counts `Finalize` calls against completed `Initialize` calls.
- **V2.** No differential or metamorphic fuzzing of cleanup-flag lowering across compilers was found or run. The GNAT observation suggests that a cheap oracle exists: count `Initialize` and `Finalize` calls under injected exceptions at every index.
- **V3.** Concurrency is not relevant to these single-frame mechanisms. Unwinding is relevant, and the probes exercised it only for Go panics and Ada exceptions.
- **V4.** not examined.

## Boundaries

- **Not examined:** Swift execution and Swift's post-DI lowering of the control variable; builds of the pinned trunks (only released binaries ran); MSVC, GCC's C++ front end, non-x86 targets; C++ unwinding cost; whether the GNAT over-finalization is reported upstream or considered conforming by GCC maintainers.
- **Unknown:** whether the pinned GCC trunk reproduces the 9-call trace (the quoted generating block and the array counter expansion exist at the pin, so likely, but not executed); whether RM 7.6.1 intends "successfully initialized" per component during default initialization of a composite (NOTE 4 tolerates repeated `Finalize` but does not address components that never completed `Initialize`).
- **Known not to apply:** Clang's flag is absent for unconditional temporaries (`t_base`) and for a conditional between prvalues materialized once (`t_ext`); Go's `deferBits` is absent under `-N`.
- **Unsupported:** Swift rejects dynamic lifetimes for noncopyable types (`noncopyable_dynamic_lifetime_unsupported`); Go has no open-coded defers in loops or beyond 8 sites.
- **Stronger conclusions not established:** that the ≈1 ns Clang cost generalizes beyond this probe and host; that jump threading never removes EH-crossing flag tests (only thresholds ≤ 1000 on Clang 19.1.7 tried); that any compiler is bit-optimal (none sizes state by s(r)); no published bound on s(r) for cleanup obligations was found — the path-count bound is derived.
- **Not measured:** all L1, L2, L5 cells; Swift L3/L4/L6; GNAT run time; energy.

## Evidence

All source, documentation and probe observations: 2026-11-21 (UTC); pins resolved via the GitHub commits API that day.

- Clang `llvm/llvm-project` @ `d71d3a9b75d9b21fc8fc8069cce2de71023b5b41`: `clang/lib/CodeGen/CGCleanup.cpp:282`–`305`, `:568`–`591`, `:1218`–`1320`; `CGCleanup.h:97`, `:101`, `:267`, `:414`–`435`; `CodeGenFunction.h:961`–`1037`, `:1400`–`1435`; `CGExprAgg.cpp:605`–`632`; `CGDecl.cpp:2655`–`2695`.
- Swift `swiftlang/swift` @ `df95e655b44760b7d16a7da561cbedb3f4294fed`: `lib/SILOptimizer/Mandatory/DefiniteInitialization.cpp:104`–`245`, `:1255`–`1290`, `:3064`–`3160`, `:3330`–`3420`; `DIMemoryUseCollector.h:40`–`117`.
- Go `golang/go` @ `2dbf8b413af37486224cd62bae53dafc516ce875`: `src/cmd/compile/internal/ssagen/ssa.go:265`–`298`, `:400`–`468`, `:1722`–`1745`, `:4862`–`4995`; `walk/stmt.go:106`–`121`; `walk/walk.go:308`; `walk/expr.go:624`–`631`; `src/runtime/panic.go:937`–`975`, `:1068`–`1090`; `test/defererrcheck.go`. Design: `golang/proposal` @ `83ee2aaf9fdcc1a1cf4bb4d20216fc979635cf04`, `design/34481-opencoded-defers.md:12`–`27`, `:60`–`72`, `:142`–`222`, `:315`–`349`.
- GNAT `gcc-mirror/gcc` @ `88f95ebe13064c5745d2571bf19b09ba641bf6fe`: `gcc/ada/exp_ch7.adb:100`–`270`, `:664`–`674`, `:5682`–`5740`, `:6560`–`6650`, `:7225`–`7260`, `:8573`–`8615`; `exp_ch3.adb:1094`–`1160`, `:3700`–`3730`, `:3781`–`3848`, `:4248`–`4255`; `libgnat/s-finpri.ads:60`–`200`; `libgnat/s-finpri.adb:362`–`375`.
- RFC: `rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/0320-nonzeroing-dynamic-drop.md:6`–`156`, `:368`–`380`, `:473`–`516`.
- Normative: ISO/IEC 14882 [except.ctor] p2–p3 (public working draft, eel.is/c++draft/except.ctor): objects "constructed, but not yet destroyed" are destroyed "in the reverse order of the completion of their construction"; subobjects "whose initialization has completed" are destroyed when initialization exits by exception. Ada 2022 RM 7.6.1 paras 4, 9, 11, 14–20, 20.1, NOTE 4 (ada-auth.org/standards/22rm/html/RM-7-6-1.html).
- Literature; every DOI checked against Crossref metadata (`api.crossref.org/works/<doi>`) on 2026-11-21, title/authors/venue/volume/pages matching:
  - D. E. Knuth, F. R. Stevenson, "Optimal measurement points for program frequency counts", BIT 13(3):313–322, 1973, DOI 10.1007/BF01951942. Abstract only.
  - T. Ball, J. R. Larus, "Optimally profiling and tracing programs", ACM TOPLAS 16(4):1319–1360, 1994, DOI 10.1145/183432.183527. Full text read in a scanned copy.
  - T. Ball, J. R. Larus, "Efficient path profiling", MICRO-29, pp. 46–57, DOI 10.1109/MICRO.1996.566449. Crossref records no date (year from the proceedings record). Full text read.
  - Vaswani, Nori, Chilimbi, "Preferential path profiling: compactly numbering interesting paths", POPL 2007, pp. 351–362, DOI 10.1145/1190216.1190268. Abstract only.
- Probes (`support/`, commands in each script header): `clang/measure_clang.py <clang++> <dir>` → `clang/out/measure.tsv`; `clang/jt_sweep.sh` → `clang/out/jt_sweep.tsv`; `clang++ -std=c++17 -O{0,2} bench.cpp cond_cleanup.cpp support.cpp && taskset -c 4 ./bench 50000000 {0,1,2}` → `clang/out/bench.txt`; `go/run_go.sh <dir> static|bench` → `go/out_static.txt`, `go/out_bench.txt`; `gnat/run_gnat.sh <gnat-root> <dir>` → `gnat/out_gnat.txt`, `gnat/expanded_fin_probe.txt`; `gnat/node_size.adb`. Binary sha256: `clang-19` `652e82bfb8c2b0881693501a9643e3106d5f22aa18da3b0697888c2d0fc995ae`; `go` `bed03ff113340190c4ebf8c6dcf1c1ad90d302c759a43fee4564ae24aa3b896e`.

## Revalidation

- **Clang:** `support/clang/jt_sweep.sh <clang++> <dir>`; discriminating rows are `-fexceptions` N=1000 (`t_cond_jcc` = 3: EH-crossing re-test persists) and `-fno-exceptions` N=3 vs N=4 (threading threshold). For source, diff `CGCleanup.cpp` around `createCleanupActiveFlag`/`SetupCleanupBlockActivation`.
- **Go:** `go build -gcflags=-d=defer` on `support/go/deferprobe`; the kinds of `Defer8`/`Defer9` and `Defer4Ret3`/`Defer4Ret4` discriminate the 8-site and 15-product limits. Check `walk/walk.go` (`maxOpenDefers`) and `ssagen/ssa.go` (`> 15`, `OpVarLive`).
- **Swift:** grep `DefiniteInitialization.cpp` for `getBuiltinIntegerType(NumMemoryElements` and the `HasConditional*` gate; `-emit-sil` on an initializer that throws after a conditional store would settle the lowering question.
- **GNAT:** build `support/gnat/trace_main.adb`; more `fin(...)` calls than 3, or any `fin(V= 0)`, reproduces the over-finalization. Check `exp_ch3.adb` for the `Skip_Self => True` block in `Build_Default_Initialization`.
- **RFC 320:** immutable at the pin.
