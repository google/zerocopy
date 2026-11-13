# Lean 4 Native Compilation Pipeline, Runtime Semantics, Code-Substitution Attributes, and Trust Surface

## Summary

Executing a Lean 4 checker or compiler pass as a native binary—or invoking it inside proofs via `native_decide` (`Lean.Meta.nativeEqTrue`) or `Lean.ofReduceBool`—expands the Trusted Computing Base (TCB) far beyond the **8,091-LOC** C++ kernel (`src/kernel/`, 37 files). Direct source inspection and execution probes against **Lean 4 v4.34.1** (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`) and its bundled **LLVM/Clang 22.1.4** toolchain (`llvm/llvm-project` commit `35990504507d79e0b9deb809c8ee5e1b34ceef20`) establish six governing invariants:

1. **Four-stage unverified compiler pipeline (`26,759 LOC` in `src/Lean/Compiler/`):** Native code generation lowers kernel `Expr` definitions through four untrusted intermediate phases orchestrated by `Lean.Compiler.LCNF.PassManager.run` (`src/Lean/Compiler/LCNF/Main.lean:105-193`) and `builtinPassManager` (`src/Lean/Compiler/LCNF/Passes.lean:119-185`):
   - **Pre-LCNF `toDecl` & `toLCNF` (`ToDecl.lean`, `ToLCNF.lean`, 1,105 LOC):** Selects `_unsafe_rec` recursive definitions over well-founded kernel encodings (`getDeclInfo?`, `ToDecl.lean:101-103`), rewrites `@[csimp]` constants (`replaceLogicConstants`, `ToDecl.lean:90-98`), inlines `[macro_inline]` and auxiliary matchers, erases proofs to `lcProof`/`lcErased` and irrelevant types to `lcAny`, lowers `Quot.mk` to identity and `Quot.lift` to `Quot.lcInv` (`ToLCNF.lean:697-714`), and converts to A-normal form (`LCNF .pure`).
   - **Phase 1 — `.base` LCNF (17 passes):** Runs `init`, `pullInstances`, `cse`, `simp`, `floatLetIn`, `findJoinPoints`, `pullFunDecls`, `reduceJpArity`, `simp { etaPoly := true, inlinePartial := true, implementedBy := true }` (which substitutes `@[implemented_by]` targets before specialization), `eagerLambdaLifting`, `checkTemplateVisibility`, `specialize`, `findJoinPoints`, `simp`, `cse`, `saveBase`, `inferVisibility`, and `toMono`.
   - **Phase 2 — `.mono` LCNF (10 + 8 passes across SCCs):** Erases type parameters, maps `Nat`/`Int` operations to runtime primitives (`lean_nat_*`, `lean_int_*`), lowers `UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize`/`Float`/`Float32` and trivial single-field structures, splits strongly connected components (`splitScc`), runs `elimDeadBranches`, `cse`, `saveMono`, `extractClosed`, and lowers to `.impure` (`toImpure`).
   - **Phase 3 — `.impure` LCNF (14 passes) & Direct C Emission (`EmitC.lean`, 1,189 LOC):** Computes constructor memory layouts (`setCtorLayout` in `ToImpureType.lean:212-298`), inserts destructive-update `reset`/`reuse` pairs (`insertResetReuse`), infers borrowed parameters (`inferBorrow`), inserts explicit `box`/`unbox` conversions (`explicitBoxing`), inserts reference-count increments and decrements (`explicitRc`), expands `reset`/`reuse` into runtime `lean_is_exclusive` branches (`expandResetReuse`), coalesces adjacent RC operations (`coalesceRC`), detects compile-time static ground constants (`detectSimpleGround`), and emits C directly from `.impure` LCNF via `LCNF.emitC` (`src/Lean/Compiler/LCNF/EmitC.lean:1185-1187`). Separately, `IR.toIR` (`src/Lean/Compiler/IR/ToIR.lean:206-211`) lowers `.impure` LCNF to `Lean.IR.Decl` for the C++ bytecode/IR interpreter (`src/library/ir_interpreter.cpp`, 1,240 LOC) and the optional experimental LLVM bitcode backend (`src/Lean/Compiler/IR/EmitLLVM.lean`, 1,678 LOC).

2. **Bundled C compiler, linker, and runtime library chain:** `leanc` (`src/Leanc.lean:1-67`) wraps bundled **Clang 22.1.4** (`bin/clang`, SHA-256 `9fcd5fc4...`) and **LLD 22.1.4** (`bin/ld.lld`, SHA-256 `d32d5121...`) with `--sysroot ROOT -nostdinc -isystem ROOT/include/clang -fstack-clash-protection -ffp-contract=off -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden -fuse-ld=lld`. By default (`linkStatic := true`), `leanc` links against the **17,654-LOC** C++ runtime (`src/runtime/`, 79 files; `lib/lean/libleanrt.a`, 1,265,008 B), `libleancpp.a`, `libInit.a`, `libStd.a`, `libLean.a`, static `libc++.a` / `libc++abi.a` / `libunwind.a`, static **GMP 6.3.0** (`lib/libgmp.a`, 1,668,288 B), static **mimalloc v3.4.4** (compiled into `libleanrt.a` under `#define LEAN_MIMALLOC` in `include/lean/config.h:9`), static **libuv v1.48.0** (`lib/libuv.a`), static **OpenSSL 3.6.0** (`lib/libssl.a`, `lib/libcrypto.a`), and stub **glibc 2.26** shared objects (`lib/glibc/{libc.so,libm.so,libdl.so,librt.so,libpthread.so,ld.so}`) so the resulting ELF binary dynamically depends only on the host OS kernel and host `libc.so.6` / `ld-linux-x86-64.so.2`.

3. **Runtime object representation, sticky reference counting, and in-place mutation (`include/lean/lean.h`, `src/runtime/object.cpp`):** Every heap object starts with an 8-byte `lean_object` header (`int m_rc; unsigned m_cs_sz:16; unsigned m_other:8; unsigned m_tag:8`, `lean.h:151-156`), while unboxed scalars (`Nat` $\le 2^{63}-1$, `Bool`, enum tags, small `Int`) are tagged pointers with bit 0 set (`lean_box(n) = (n << 1) | 1`, `lean.h:334-336`). Single-threaded objects have `m_rc > 0` (`lean_is_exclusive(o)` tests `o->m_rc == 1`, `lean.h:729-735`); thread-shared objects have `m_rc < 0` adjusted atomically (`std::memory_order_relaxed` on increment, `acq_rel` on decrement); persistent and compacted `.olean` objects have `m_rc == 0`. Following the discovery that 32-bit `m_rc` overflow could trigger use-after-free in the kernel and prove `False` (`#14838`), Lean `v4.34.1` reserves a sticky negative band (`LEAN_RC_STICKY = INT_MIN + 0x10000000`, `LEAN_RC_STICKY_DROP = INT_MIN + 0x20000000`, `LEAN_RC_STUCK_ST = INT_MIN + 0x10000`, `lean.h:621-658`) that permanently freezes overflowing or underflowing objects.

4. **Silent code-substitution attributes (`@[implemented_by]`, `@[extern]`, `@[csimp]`) and a critical `@[csimp]` axiom-masking hazard:**
   - `@[implemented_by impl]` (`ImplementedByAttr.lean:51-72`) and `@[extern "sym"]` (`ExternAttr.lean:1-136`) replace a safe definition's compiled code without leaving any trace in the definition's kernel `ConstantInfo` or `#print axioms`.
   - `@[csimp]` (`CSimpAttr.lean:60-134`) requires a theorem `thmName` of type `@f = @g`, which `ToDecl.replaceLogicConstants` (`ToDecl.lean:90-98`) and `ToLCNF` (`ToLCNF.lean:547,685,818`) apply to rewrite `f` to `g` in compiled code. Crucially, `CSimp.replaceConstant` (`CSimpAttr.lean:128-134`) records `thmName` only in `extraModUses` (`recordExtraModUseFromDecl`) and **does not** reference `thmName` or `g` inside the caller's kernel `Expr`. Consequently, if `thmName` is an axiom or proved via `sorryAx`, `#print axioms` on any function calling `f` (or any theorem proved about `f` via `Lean.ofReduceBool`) reports **zero** dependency on `thmName` or `sorryAx`, as demonstrated in [`support/LeanNativeCompilationAndTrustProbe.lean`](support/LeanNativeCompilationAndTrustProbe.lean).

5. **Two distinct native-reflection handles (`Lean.ofReduceBool` vs. `Lean.Meta.nativeEqTrue`) and module-system interpreter dispatch:**
   - Legacy `Lean.ofReduceBool` (`src/Init/Core.lean:2396`) triggers the C++ kernel hook `reduce_native` (`src/kernel/type_checker.cpp:614-635`), which invokes `ir::run_boxed_kernel` and leaves `[Lean.ofReduceBool, Lean.trustCompiler]` in `#print axioms`.
   - In Lean `v4.34.1`, `native_decide` and `bv_decide` instead call `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean:29-78`), which compiles a temporary `meta` declaration under `Elab.async=false`, evaluates it via `unsafe evalConst Bool`, and injects a fresh per-goal custom axiom `_native.<tacticName>.ax_* : e = true` into the environment—bypassing `reduce_native` and never referencing `Lean.ofReduceBool` or `Lean.trustCompiler`.
   - Furthermore, under the `module` system (`src/Lean/Compiler/IR/CompilerM.lean:96-111`), `.olean` exports strip non-`meta` IR function bodies into `.extern f xs ty { entries := [.opaque] }`. Because `ir_interpreter.cpp:848` checks `if (m_prefer_native || decl_tag(e_new.m_decl) == decl_kind::Extern ...)`, the interpreter **always** dispatches imported `module` functions to native machine code via `dlsym(RTLD_DEFAULT, ...)` even when `set_option interpreter.prefer_native false` is set.

6. **Determinism, host support, and historical compiler/runtime soundness bugs:** `lean --c` is bit-for-bit deterministic (`SHA-256: 0f9dfb23...`), and `leanc -O3` produces bit-for-bit identical 4,476,960-byte ELF executables (`SHA-256: 83b23bad...`) when compiled from the same relative source filename (differing by 1 byte in `.strtab`'s `STT_FILE` entry when the input `.c` filename differs). However, recent Lean 4 commit history documents multiple bugs where native execution or runtime memory management diverged from the logic—including 32-bit `m_rc` overflow use-after-free (`#14838`, `#15241`, `#15288`, `#15307`), `String.Pos.Raw.extract` model/runtime mismatch and use-after-free on non-scalar positions (`#14717`, `#14687`), `Bool` 0-ary constant-folding miscompilation (`#13989`), `IntX.ofIntClamp` clamping to `minValue` instead of `maxValue` (`#14078`), `ExpandResetReuse` double-`oproj` corruption (`#13421`), `EmitC` greedy hex escape corruption (`#13435`), `InferBorrow` `export` parameter ownership loss (`#13052`), and GMP `< 6.3.0` arithmetic bugs (`flake.nix:60-63`).

## Applicability

These findings govern:

- **Lean 4 v4.34.1** (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`), specifically the `Lean.Compiler.LCNF` compiler pipeline, `Lean.Compiler.IR` interpreter bridge, C++ runtime (`src/runtime/`, `include/lean/lean.h`), C++ kernel (`src/kernel/type_checker.cpp`), and `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean`).
- **Lean 4 v4.34.1 official Linux `x86_64` toolchain archive** (`lean-4.34.1-linux.tar.zst`), including bundled `clang` and `ld.lld` `22.1.4` (`llvm/llvm-project` commit `35990504507d79e0b9deb809c8ee5e1b34ceef20`), `mimalloc v3.4.4`, `GMP 6.3.0`, `libuv v1.48.0`, `OpenSSL 3.6.0`, `CaDiCaL rel-2.1.2`, `leantar v0.1.20`, and the NixOS 18.03 glibc `2.26` stub sysroot.
- **Anneal (`joshlf/anneal` commit `7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) and verified Rust compiler architectures** that either:
  1. check proofs inside the Lean kernel (`Trusted.CrateTheorem`) while auditing `.olean` files with `trusted/audit`, or
  2. compile a verified translation-validation / proof-checking function (`check : Cert → Input → Bool`) to a standalone native binary via `lean --c` and `leanc`.

## Findings

### 1. The Lean 4.34.1 Native Compilation Pipeline (`Expr` $\to$ `LCNF` $\to$ `.c` $\to$ ELF)

#### 1.1 Subsystem Size Breakdown (`src/Lean/Compiler/` vs. `src/kernel/`)

Basis: source (`src/kernel/`, `src/runtime/`, `src/Lean/Compiler/`, `src/library/` at `5045d0056413266e57c625dcd7c365b10e377c52`).

In Lean `v4.34.1`, the LCNF compiler has completely replaced the legacy C++ compiler and emits C directly from `.impure` LCNF (`src/Lean/Compiler/LCNF/EmitC.lean`), while retaining `Lean.Compiler.IR` as a lightweight lowering target for the C++ bytecode interpreter and optional LLVM bitcode emission:

| Subsystem | Source Path | Files | Lines of Code (LOC) | Size (Bytes) | Role in Execution Mode |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **Lean C++ Kernel** | `src/kernel/` | 37 | 8,091 | 344,132 | Trusted in all modes (`type_checker.cpp`: 1,373 LOC; `inductive.cpp`: 1,417 LOC) |
| **LCNF Compiler Core & Passes** | `src/Lean/Compiler/LCNF/` | 84 | 21,046 | 797,295 | Trusted for native binaries, `native_decide`, `ofReduceBool`, and `#eval` |
| **Compiler Attributes & FFI** | `src/Lean/Compiler/*.lean` | 21 | 1,945 | 71,861 | `@[implemented_by]`, `@[extern]`, `@[csimp]`, `@[export]`, `@[init]`, name mangling |
| **Legacy IR & LLVM Backend** | `src/Lean/Compiler/IR/` | 12 | 3,768 | 155,702 | `ToIR.lean` (213 LOC) lowers `.impure` LCNF for `ir_interpreter.cpp`; `EmitLLVM.lean` (1,678 LOC) |
| **Separate Codegen Driver** | `src/LeanIR.lean` + `src/Leanc.lean` | 2 | 242 | 8,042 | `leanir` separate-process `.ir`/`.c` generator; `leanc` C compiler wrapper |
| **C++ IR Interpreter** | `src/library/ir_interpreter.cpp` | 2 | 1,259 | 67,454 | Executes `IR.Decl` bytecode and dispatches `dlsym` native calls for `evalConst`/`reduce_native` |
| **C++ Runtime (`libleanrt.a`)** | `src/runtime/` + `include/lean/` | 85 | 21,885 | 833,497 | Object header, sticky RC, closures, arrays, strings, GMP `mpz`, `mimalloc`, task manager, libuv |
| **Total Non-Kernel Native Pipeline** | Compiler + Interpreter + Runtime | **206** | **50,145** | **1,933,851** | **6.20$\times$ larger in LOC than the C++ kernel** (excluding Clang/LLD, GMP, mimalloc, libc) |

#### 1.2 Exact Four-Stage Pass Pipeline (`src/Lean/Compiler/LCNF/Passes.lean:119-185`)

Basis: source (`src/Lean/Compiler/LCNF/Main.lean:105-193`, `src/Lean/Compiler/LCNF/Passes.lean:119-185`, `src/Lean/Compiler/LCNF/ToDecl.lean:100-181`, `src/Lean/Compiler/LCNF/ToLCNF.lean:435-860`).

When `compileDecls` (`src/Lean/Compiler/LCNF/Main.lean:105`) compiles a declaration block, it transforms definitions through four representations:

1. **Stage 0 — `toDecl` and `toLCNF` (`Expr` $\to$ `Decl .pure`):**
   - **Well-founded vs. `_unsafe_rec` replacement (`ToDecl.lean:101-103`):** `getDeclInfo? declName` checks `env.find? (mkUnsafeRecName declName) <|> env.find? declName`. For any recursive function compiled via structural or well-founded recursion, the kernel environment stores a well-founded `WellFounded.fix` / `.brecOn` definition under `declName`, alongside an `unsafe` direct-recursion auxiliary `declName._unsafe_rec`. The compiler **discards** the kernel's well-founded proof term and compiles `declName._unsafe_rec` instead!
   - **Pre-LCNF rewrites (`ToDecl.lean:152-161`):** Eta-expands the body, runs `replaceLogicConstants` (which rewrites nested `_unsafe_rec` references back to `declName` and applies `@[csimp]` constant replacements via `CSimp.replaceConstant`), expands `[macro_inline]`, inlines auxiliary `matcher` and `match_on_same_ctor.het` declarations (`inlineMatchers`), and runs `macroInline` a second time to expand exposed `ite`/`dite` macros.
   - **Quotient, proof, and recursor erasure (`ToLCNF.lean:697-850`):** Replaces proof arguments (`Meta.isProp`) with `lcProof` / `.erased`; lowers `Quot.mk α r a` to `a` and `Quot.lift α r β f h q` to `f (Quot.lcInv α r q)`; lowers `Eq.rec`, `Eq.ndrec`, `HEq.rec`, and `HEq.ndrec` directly to their minor premise; and lowers `False.rec` / `Empty.rec` to `mkUnreachable` (which emits `lean_internal_panic_unreachable()` in C).

2. **Stage 1 — `.base` Phase (`Passes.lean:120-146`, polymorphic `LCNF .pure`):**
   - Runs `init`, `pullInstances` (hoisting typeclass instances), `cse (shouldElimFunDecls := false)`, `simp`, `floatLetIn`, `findJoinPoints`, `pullFunDecls`, `reduceJpArity`.
   - Runs `simp { etaPoly := true, inlinePartial := true, implementedBy := true } (occurrence := 1)`: **`applyImplementedBy?` (`src/Lean/Compiler/LCNF/Simp/SimpValue.lean:65-69`) replaces every constant `declName` carrying `@[implemented_by declNameNew]` with `declNameNew` here**, prior to `specialize`, so that the replacement function is what gets monomorphized and specialized.
   - Runs `eagerLambdaLifting`, `checkTemplateVisibility`, `specialize`, `findJoinPoints (occurrence := 1)`, `simp (occurrence := 2)`, `cse (occurrence := 1)`, `saveBase`, `inferVisibility (phase := .base)`, and `toMono`.

3. **Stage 2 — `.mono` Phase (`Passes.lean:147-168`, monomorphic `LCNF .pure`):**
   - `toMono` (`src/Lean/Compiler/LCNF/ToMono.lean`) erases universe levels and type parameters (`lcErased`), eliminates trivial single-field wrapper structures (`hasTrivialStructure?`), lowers primitive inductive representations (`Nat`, `Int`, `Bool`, `UInt8..64`, `USize`, `Float`, `Float32`, `Array`, `ByteArray`, `FloatArray`, `String`, `Thunk`, `Task`), and rewrites `casesOn` for types with `@[implemented_by]` computed fields (`_impl`).
   - Runs `simp (occurrence := 3)`, `reduceJpArity`, `structProjCases`, `extendJoinPointContext`, `floatLetIn`, `reduceArity`, `commonJoinPointArgs`, `simp (occurrence := 4)`, `floatLetIn`, `lambdaLifting`.
   - Splits declarations into strongly connected components (`splitScc`) and runs `monoPassesNoLambda`: `extendJoinPointContext`, `simp (occurrence := 5)`, `elimDeadBranches` (abstract-interpretation dead branch elimination), `cse (occurrence := 2)`, `saveMono`, `inferVisibility`, `extractClosed` (hoisting closed terms into module-level `___closed__*` globals initialized once at startup), and `toImpure`.

4. **Stage 3 — `.impure` Phase (`Passes.lean:169-184`, `LCNF .impure`) and `EmitC` (`EmitC.lean:1-1189`):**
   - `toImpure` (`src/Lean/Compiler/LCNF/ToImpure.lean`) lowers constructor applications and pattern matching using `getCtorLayout` (`ToImpureType.lean:212-298`), which orders constructor fields in memory as: (1) boxed object pointers (`lean_object*`), (2) `USize` fields, and (3) scalar fields sorted descending by alignment size (`8B`, `4B`, `2B`, `1B`).
   - Runs the 14 impure passes:
     1. `pushProj (occurrence := 0)` — pushes projections inward toward uses to shorten live ranges.
     2. `insertResetReuse` (`ResetReuse.lean`, 333 LOC) — pairs dead pattern-matched constructors with subsequent constructor allocations of matching size (`Reset` + `Reuse`).
     3. `elimDeadVars` — removes dead bindings exposed by projection pushing.
     4. `simpCase` (`SimpCase.lean`, 134 LOC) — merges identical case branches.
     5. `inferBorrow` (`InferBorrow.lean`, 454 LOC) — fixed-point dataflow analysis inferring which parameters can be passed borrowed (`@&` / `b_lean_obj_arg`) without being consumed or escaping into closures/constructors/reset-reuse.
     6. `explicitBoxing` (`ExplicitBoxing.lean`, 378 LOC) — inserts `.box` and `.unbox` conversions at boundaries between unboxed scalars (`uint8_t`, `uint64_t`, `size_t`, `double`) and polymorphic/closure contexts, and generates `___boxed` wrapper functions.
     7. `explicitRc` (`ExplicitRC.lean`, 704 LOC) — backward liveness pass inserting explicit `.inc` (`lean_inc` / `lean_inc_ref_n`), `.dec` (`lean_dec` / `lean_dec_ref`), and `.del` (`lean_del_object`) instructions according to owned vs. borrowed parameter conventions.
     8. `expandResetReuse` (`ExpandResetReuse.lean`, 385 LOC) — lowers abstract `reset`/`reuse` into runtime `!lean_is_exclusive(x)` branches: when exclusive (`m_rc == 1`), mutates fields in-place and skips `lean_alloc_ctor`; when shared (`m_rc != 1`), increments surviving fields, decrements `x`, and allocates a fresh constructor.
     9. `coalesceRC` (`CoalesceRC.lean`, 104 LOC) — merges multiple `.inc x 1` into `.inc x k`.
     10. `pushProj (occurrence := 1)` — second projection push after `expandResetReuse`.
     11. `detectSimpleGround` (`SimpleGroundExpr.lean`, 427 LOC) — identifies closed constant object graphs that can be emitted as C `static const` structs (`m_rc = 0`, `.m_header = {.m_rc = 0, ...}`) in `.rodata` without runtime initialization.
     12. `inferVisibility (phase := .impure)`.
     13. `toposortPass` (`Toposort.lean`) — topologically orders declarations for C emission.
     14. `saveImpure` — persists `.impure` declarations into environment extensions (`impureDecls`) for `EmitC.emitC` (`src/Lean/Compiler/LCNF/EmitC.lean:1185`) and lowers via `IR.toIR` (`src/Lean/Compiler/LCNF/Main.lean:174`) for the interpreter.

#### 1.3 Separate-Process Codegen (`leanir`) and C Compilation (`leanc`, Clang 22.1.4, LLD 22.1.4)

Basis: source + execution (`src/LeanIR.lean:1-175`, `src/Leanc.lean:1-67`, `script/prepare-llvm-linux.sh:1-106`, `leanc --print-cflags`, `leanc --print-ldflags`).

Under Lake's multi-part module build system (`src/LeanIR.lean:59-175`), `lean` elaborates and kernel-checks a module to produce `.olean`, `.olean.server`, `.olean.private`, and `.ir.sig` while postponing code generation (`compiler.postponeCompile = true`, `LCNF/Main.lean:128`). A separate process (`bin/leanir <setup.json> <output.ir> <output.c>`) then loads `.olean.private` and imported `.ir.sig` files, runs the LCNF pipeline, writes `<output.ir>`, and emits `<output.c>` via `LCNF.emitC`.

`bin/leanc` (`src/Leanc.lean:1-67`) invokes the bundled Clang `22.1.4` and LLD `22.1.4` with the following exact flags on `x86_64-unknown-linux-gnu`:

- **C compiler flags (`getCFlags` + `getInternalCFlags`):**
  ```text
  -I <sysroot>/include -fstack-clash-protection -ffp-contract=off
  -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden
  --sysroot <sysroot> -nostdinc -isystem <sysroot>/include/clang
  ```
  Note `-ffp-contract=off` and the compile-time guard `#if !defined(FLT_EVAL_METHOD) || (FLT_EVAL_METHOD != 0)` in `include/lean/lean.h:86-88`, which forbid fused multiply-add contraction and extended-precision `x87` evaluation so C floating-point operations match IEEE 754 binary64/binary32.
- **Linker flags (`getInternalLinkerFlags` + `getLinkerFlags` with `linkStatic = true`):**
  ```text
  --sysroot <sysroot> -L <sysroot>/lib -L <sysroot>/lib/glibc
  -lc -lc_nonshared -Wl,--as-needed -l:ld.so -Wl,--no-as-needed -lpthread_nonshared
  -Wl,--as-needed -Wl,-Bstatic -lgmp -lunwind -luv -lssl -lcrypto -Wl,-Bdynamic -Wl,--no-as-needed
  -fuse-ld=lld -L <sysroot>/lib/lean
  -Wl,--start-group -lleancpp -lLean -Wl,--end-group -lStd
  -Wl,--start-group -lInit -lleanrt -Wl,--end-group
  -Wl,-Bstatic -lc++ -lc++abi -Wl,-Bdynamic -lLake
  -Wl,--as-needed -lgmp -luv -lssl -lcrypto -lpthread -ldl -lrt -Wl,--no-as-needed
  -Wl,--gc-sections -lm -ldl -pthread
  ```

### 2. Runtime Semantics: Reference Counting, In-Place Updates, Arrays, GMP, Tasks, and FFI

Basis: source (`include/lean/lean.h:90-1850`, `include/lean/config.h:1-12`, `src/runtime/object.cpp`, `src/runtime/memory.cpp`, `src/runtime/mpz.cpp`, `src/runtime/thread.cpp`).

1. **Object Header and Tagged Pointers (`lean.h:92-156, 334-336`):**
   - Every heap-allocated value has an 8-byte `lean_object` header: `int m_rc` (32-bit signed reference count), `unsigned m_cs_sz : 16` (object byte size for `mimalloc` / compact regions), `unsigned m_other : 8` (number of pointer fields for constructors, or element byte size for `LeanScalarArray`), and `unsigned m_tag : 8` (`0..243` for constructor tags; `244` `LeanPromise`, `245` `LeanClosure`, `246` `LeanArray`, `247` `LeanStructArray`, `248` `LeanScalarArray`, `249` `LeanString`, `250` `LeanMPZ`, `251` `LeanThunk`, `252` `LeanTask`, `253` `LeanRef`, `254` `LeanExternal`, `255` `LeanReserved`).
   - Any pointer with bit 0 set (`((size_t)o & 1) == 1`) is an unboxed scalar (`lean_box(n)` / `lean_unbox(o)`), requiring zero heap allocation or reference counting.
   - During deallocation (`lean_dec_ref_cold` in `src/runtime/object.cpp`), the runtime reuses the 48 bits of `m_rc` (32 bits) + `m_cs_sz` (16 bits) to thread an intrusive deletion worklist without stack recursion (`lean.h:142-146`). Consequently, Lean's runtime is incompatible with 64-bit pointer-tagging hardware extensions such as ARM MTE or HWASAN that set upper pointer bits (`lean.h:145-146`).

2. **Three-State Reference Counter and Sticky Overflow Protection (`lean.h:124-135, 588-701`):**
   - `m_rc > 0` (**Single-Threaded, `lean_is_st`**): Incremented and decremented with non-atomic integer arithmetic (`lean_internal_add_rc`, `lean_internal_sub_rc`). `lean_is_exclusive(o)` (`lean.h:729-735`) returns `true` if and only if `o->m_rc == 1`.
   - `m_rc < 0` (**Multi-Threaded, `lean_is_mt`**): Triggered when an object graph is passed to `Task.spawn` / `IO.asTask` (`lean_mark_mt`). A reference count of $N$ is stored as $-N$ and adjusted via `std::atomic_fetch_sub_explicit(..., std::memory_order_relaxed)` on increment and `atomic_fetch_add_explicit(..., std::memory_order_acq_rel)` in `lean_dec_ref_cold`. `lean_is_exclusive(o)` is **always `false`** for `m_rc <= 0`.
   - `m_rc == 0` (**Persistent / Compacted, `lean_is_persistent`**): Used for module-initialization globals (`lean_mark_persistent`), compile-time static ground structs in `.rodata`, and mmap'd `.olean` compact regions (`src/runtime/compact.cpp`). Never freed or mutated in place.
   - **Sticky Overflow Band (`lean.h:609-682`):** To prevent 32-bit signed `m_rc` wrap-around from causing use-after-free, Lean `v4.34.1` defines `LEAN_RC_INC_MAX = 0x10000`, `LEAN_RC_STUCK_ST = INT_MIN + 0x10000`, `LEAN_RC_STICKY = INT_MIN + 0x10000000`, and `LEAN_RC_STICKY_DROP = INT_MIN + 0x20000000`. Single-threaded counts overflowing `INT_MAX` wrap into `[INT_MIN, LEAN_RC_STUCK_ST)`, and multi-threaded counts descending below `LEAN_RC_STICKY` freeze permanently: `lean_is_never_freed(o)` (`(unsigned)rc <= (unsigned)LEAN_RC_STICKY_DROP`) prevents both top-level `lean_dec_ref` and deletion cascades from ever freeing a sticky object.

3. **In-Place Constructor Reuse and Copy-on-Write Arrays (`lean.h:830-839, 964-1311`):**
   - When `expandResetReuse` lowers a pattern match followed by a constructor allocation, the generated C code checks `!lean_is_exclusive(x)` (see lines 120-210 of the emitted C in [`support/LeanNativeCompilationAndTrustProbe.lean`](support/LeanNativeCompilationAndTrustProbe.lean)). If `x` is exclusive (`m_rc == 1`), it overwrites `x`'s fields in-place without calling `lean_alloc_ctor`. If `lean_ctor_release(o, i)` is used on a partially reset object, it writes `objs[i] = lean_box(0)` after `lean_dec(objs[i])` (`lean.h:830-839`) so that a fallback `lean_dec(o)` on a non-reused branch cannot double-free `objs[i]`.
   - `Array α` (`lean_array_object`: `m_header`, `size_t m_size`, `size_t m_capacity`, `lean_object * m_data[]`), `ByteArray`, and `FloatArray` (`lean_sarray_object`) check `lean_is_exclusive(a)` on every `uset` / `fset` / `push` / `pop` (`lean.h:1085-1155, 1287-1294`). When `m_rc == 1`, updates mutate `m_data[i]` in place in $O(1)$ time; when `m_rc != 1`, `lean_copy_expand_array` allocates a copy before mutating.

4. **Arbitrary-Precision Arithmetic (`GMP 6.3.0`, `lean.h:1500-1850`, `src/runtime/mpz.cpp`):**
   - Small `Nat` values $\le \text{LEAN\_MAX\_SMALL\_NAT} = \text{SIZE\_MAX} \gg 1 = 2^{63}-1$ (on 64-bit hosts) and small `Int` values in $[-2^{31}, 2^{31}-1]$ (`LEAN_MIN_SMALL_INT..LEAN_MAX_SMALL_INT`) are stored unboxed as tagged pointers (`lean_is_scalar`).
   - Values exceeding those bounds allocate a `LeanMPZ` heap object (`m_tag = 250`) backed by **GNU MP (GMP) 6.3.0** (`lib/libgmp.a`, `src/runtime/mpz.h`). Both the C++ kernel (`reduce_bin_nat_op` in `src/kernel/type_checker.cpp:644-658`) and compiled native code call the exact same `mpz` wrapper (`lean_nat_big_add`, `lean_nat_big_mul`, `lean_nat_big_div`, etc.). As documented in `flake.nix:60-63` and `doc/dev/index.md`, Lean requires **GMP $\ge$ 6.3.0** because earlier GMP releases contain arithmetic bugs that can make Lean produce unsound results.

5. **Allocator (`mimalloc v3.4.4`), Task Manager (`src/runtime/thread.cpp`), and FFI (`lean.h:159-189, 317-332`):**
   - `include/lean/config.h:9` enables `#define LEAN_MIMALLOC` (`microsoft/mimalloc` `v3.4.4`). Small objects ($\le \text{MI\_SMALL\_SIZE\_MAX}$) call `mi_malloc_small(sz)` and record their aligned size in `o->m_cs_sz` (`lean.h:482-493`) after calling `lean_inc_heartbeat()`, and `lean_alloc_ctor_memory` zeroes the trailing padding word (`end[-1] = 0`, `lean.h:505-517`) so `compact.cpp` and `maxsharing.cpp` never read uninitialized padding bytes.
   - `Task α` (`lean_task_object`, `lean.h:254-310`) implements a 6-state atomic state machine (`Queued`, `Waiting`, `Promised`, `Running`, `Deactivated`, `Finished`) scheduled on `task_manager`'s work-stealing `std::thread` pool (`src/runtime/thread.cpp`).
   - Lean's C FFI (`@[extern "c_name"]` and `@[export c_name]`) passes owned arguments as `lean_obj_arg` (callee must consume `m_rc`) and `@&` borrowed arguments as `b_lean_obj_arg` (callee must **not** decrement `m_rc`, and must `lean_inc` if storing or returning the reference). Any mismatch between the Lean declaration's `@&` annotations and the C function's RC behavior causes immediate memory corruption or use-after-free (as in `#14687` and `#13052`).

### 3. Code-Substitution Attributes (`@[implemented_by]`, `@[extern]`, `@[csimp]`) and Native Evaluation Handles

Basis: source + execution (`src/Lean/Compiler/ImplementedByAttr.lean:1-81`, `src/Lean/Compiler/ExternAttr.lean:1-136`, `src/Lean/Compiler/CSimpAttr.lean:1-145`, `src/Lean/Meta/Native.lean:1-78`, `src/kernel/type_checker.cpp:604-635`, `src/library/ir_interpreter.cpp:846-960`, [`support/LeanNativeCompilationAndTrustProbe.lean`](support/LeanNativeCompilationAndTrustProbe.lean)).

| Mechanism | Where Applied in Compiler / Kernel | Checked by Kernel? | Visible in `#print axioms` (`CollectAxioms`)? | Trust & Auditing Implication |
| :--- | :--- | :--- | :--- | :--- |
| `@[implemented_by g] def f` | `.base` LCNF pass `simp (occurrence := 1)` (`SimpValue.lean:65-69`) and `ToMono.lean:160` (`casesOn`) | **No** (only checks type equality `declType == fnType` in `ImplementedByAttr.lean:65`) | **No** (`f`'s kernel `defnInfo.value` never mentions `g`) | Native binary and `native_decide`/`ofReduceBool` run `g`; kernel `rfl` reduces `f`. Unsound `g` proves `False` via `native_decide`/`ofReduceBool` or silently corrupts a standalone native checker. |
| `@[extern "sym"] def/opaque f` | `ToDecl.toDecl` (`ToDecl.lean:138-142`) emits `Decl.value := .extern`; `ir_interpreter.cpp:848` calls `dlsym` | **No** (kernel sees `f`'s logical body or `opaque`/`axiom` stub) | **No** (if `def` or `opaque` with default value; only `axiom` is listed) | Arbitrary C/Rust/assembly code executes at runtime and during `evalConst` / `native_decide` / `ofReduceBool`. |
| `@[csimp] theorem thm : @f = @g` | `ToDecl.replaceLogicConstants` (`ToDecl.lean:90-98`) and `ToLCNF.lean:547,685,818` | Kernel checks `thm : @f = @g`, **but `CSimp.add` does NOT check `thm`'s axioms!** | **No!** Caller `h` of `f` has only `f` in its kernel `Expr`; `thm` and `g` are **invisible** to `CollectAxioms` on `h`! | **Critical audit finding:** If `thm : @f = @g` is an axiom or proved via `sorryAx`, `#print axioms h` (and `#print axioms` on a `Lean.ofReduceBool` proof using `h`) does **not** report `thm` or `sorryAx`! |
| `Lean.ofReduceBool` / `Lean.reduceBool` | C++ kernel `reduce_native` (`src/kernel/type_checker.cpp:614-635`) calls `ir::run_boxed_kernel` | Kernel trusts interpreter/native return value as `Bool.true` / `Bool.false` | **Yes:** `[Lean.ofReduceBool, Lean.trustCompiler]` (`Init/Core.lean:2361-2396`) | Deprecated since `2026-02-01` (`Init/Core.lean:2395`), but **still active in `type_checker.cpp:618`**! Must be explicitly forbidden in axiom auditors. |
| `native_decide` / `bv_decide` (`Lean.Meta.nativeEqTrue`) | Elaborator (`src/Lean/Meta/Native.lean:29-78`) runs `evalConst Bool` on temp `meta` decl, then calls `addDecl axDecl` | Kernel sees a fresh custom axiom `_native.<tac>.ax_* : e = true` | **Yes:** `[<thm>._native.<tac>.ax_*]` (does **not** mention `ofReduceBool` or `trustCompiler`) | An auditor that only blacklists `Lean.ofReduceBool` and `Lean.trustCompiler` without enforcing an axiom **allowlist** (`allowedAxioms ⊆ {propext, Classical.choice, Quot.sound}`) will miss `native_decide` in Lean `v4.34.1`! |
| Standalone Native Binary (`lean --c` + `leanc`) | `LCNF.emitC` $\to$ `clang 22.1.4` $\to$ `ld.lld 22.1.4` $\to$ `main` | **No** (kernel does not check compiled machine code) | **None** (`main` is executed directly by the OS, not via a kernel axiom) | Trusts the entire 50,145-LOC Lean compiler/runtime, all active `@[implemented_by]`/`@[extern]`/`@[csimp]` attributes in transitive imports, Clang/LLD `22.1.4`, GMP `6.3.0`, mimalloc `v3.4.4`, host OS/libc, and CPU. |

Executing [`support/LeanNativeCompilationAndTrustProbe.lean`](support/LeanNativeCompilationAndTrustProbe.lean) with `lean -DElab.async=false` confirms all five behaviors simultaneously:
- `kernel_sees_safeSpec0 : safeSpec0 = false := rfl` and `kernel_sees_callerOfCsimp0 : callerOfCsimp0 = false := rfl` both succeed in the kernel with **zero** axioms (`'does not depend on any axioms'`).
- `false_from_implemented_by_and_ofReduceBool : False` and `false_from_csimp_and_ofReduceBool : False` both type-check in the kernel with axiom footprint `[Lean.ofReduceBool, Lean.trustCompiler]`—note that `unsound_csimp_ax` is **completely absent** from `#print axioms false_from_csimp_and_ofReduceBool`!
- When compiled via `lean --c` and `leanc -O3`, the native executable prints `safeSpec0 (compiled): true` and `callerOfCsimp0 (compiled): true`.

### 4. Native Build Determinism, Supported Hosts, and Historical Miscompilation Catalog

#### 4.1 Determinism of `lean --c` and `leanc`

Basis: execution ([`support/verify_lean_native_pipeline.py`](support/verify_lean_native_pipeline.py)).

Running `lean -DElab.async=false --root=<dir> --c=<out.c> LeanNativeCompilationAndTrustProbe.lean` across separate directories produces bit-for-bit identical 14,691-byte C files (`SHA-256: 0f9dfb232c132e289548eae65838e2415997be112de3277894830522eda2e226`) because `LCNF.emitC` (`src/Lean/Compiler/LCNF/EmitC.lean:1174-1183`) sorts local declarations by `getImpureDeclIndices` and formats deterministic `v_<name>_<idx>_` C identifiers.

Compiling that C file with `leanc -O3 probe.c -o probe_bin` in two distinct directories (`d1/probe.c` and `d2/probe.c`) produces bit-for-bit identical 4,476,960-byte ELF executables (`SHA-256: 83b23bad0352f21137ec297b9e403c07c8e90fc6731e7c33aba179cedaf7600b`). If the input `.c` filenames themselves differ (`probe1.c` vs. `probe2.c`), the resulting 4,476,960-byte ELF binaries differ at **exactly 1 byte** (`offset 0x33d8c3`: `'1'` vs. `'2'`) in the `.strtab` `STT_FILE` symbol entry emitted by Clang.

#### 4.2 Official Supported Host Platforms in Lean `v4.34.1`

Basis: source (`.github/workflows/ci.yml:290-441`, `flake.nix:1-106`, `script/prepare-llvm-{linux,macos,mingw}.sh`).

| Host Target Triple | Release Archive | Bundled LLVM / Linker | Bundled C / System Runtime | Tier / CI Status in `ci.yml` |
| :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `lean-4.34.1-linux.tar.zst` | `clang` + `ld.lld` `22.1.4` | Stub `glibc 2.26` (`nixos-18.03`), static `gmp 6.3.0`, `libuv 1.48.0`, `openssl 3.6.0`, `libc++`, `libunwind` | Tier 1 (`test: true`, `check-rebootstrap: true`) |
| `aarch64-unknown-linux-gnu` | `lean-4.34.1-linux_aarch64.tar.zst` | `clang` + `ld.lld` `22.1.4` | Stub `glibc 2.27` (`nixos-19.03`), static `gmp 6.3.0`, `libuv 1.48.0`, `openssl 3.6.0`, `libc++`, `libunwind` | Tier 1 (`test: true`) |
| `aarch64-apple-darwin` | `lean-4.34.1-darwin_aarch64.tar.zst` | `clang` + `ld64.lld` `22.1.4` | `libSystem.tbd`, `libc++.dylib`, static `gmp`, `libuv`, `openssl` | Tier 1 (`test: true` at `level >= 2`) |
| `x86_64-apple-darwin` | `lean-4.34.1-darwin.tar.zst` | `clang` + `ld64.lld` `22.1.4` | `libSystem.tbd`, `libc++.dylib`, static `gmp`, `libuv`, `openssl` | Tier 2 (`test: false // Tier 2 platform`, `ci.yml:370`) |
| `x86_64-w64-windows-gnu` | `lean-4.34.1-windows.zip` | `clang` + `ld.lld` `22.1.4` | MSYS2 `clang64` MinGW-w64 import libs + `libgmp-10.dll`, `libuv-1.dll`, `libc++.dll`, `libunwind.dll` | Tier 1 (`test: true`) |
| `i686-unknown-linux-gnu` (`-m32`) | *(Disabled in `ci.yml:415-426`)* | — | Built with `-DUSE_GMP=OFF -DMMAP=OFF` when enabled | Disabled (`"a 2GB heap is just not that much"`) |
| `wasm32-unknown-emscripten` | *(Disabled in `ci.yml:427-440`)* | Emscripten | Built with `-DUSE_GMP=OFF -DMMAP=OFF` | Disabled in release matrix |

#### 4.3 Concrete Catalog of Lean 4 Compiler and Runtime Bugs Causing Kernel/Native Divergence

Basis: source (`git log` in `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`).

Even when a program uses **zero** `@[implemented_by]`, `@[extern]`, or `@[csimp]` attributes of its own, bugs in Lean's LCNF passes, C emission, standard-library `@[extern]` functions, or C++ runtime can cause native execution to disagree with the kernel:

| Commit (`leanprover/lean4`) | PR / Issue | Subsystem | Mechanism of Kernel vs. Native Divergence or Memory Corruption |
| :--- | :--- | :--- | :--- |
| `992fdd2d47a6` ( plus `27e473f2866e`, `e71b3cccb4b3`, `846ad6cd66e5`) | `#14838`, `#15241`, `#15288`, `#15307` | Runtime RC (`lean.h`, `object.cpp`, `sharecommon.cpp`) | **32-bit `m_rc` overflow $\to$ use-after-free $\to$ proof of `False`:** Allocating $> 2^{31}$ references to a single object on a machine with $\ge 18\text{ GiB}$ RAM wrapped `m_rc` into negative/zero values, freeing a live object and allowing type confusion inside the official kernel and native code. Fixed by the sticky-RC band (`LEAN_RC_STICKY`). |
| `f7f5b4cda9b3` & `4c29de6f2cb9` | `#14717`, `#14687` (`#14684`) | Runtime `@[extern]` (`object.cpp:2380`, `String.Pos.Raw.extract`) | **Model/runtime mismatch + use-after-free on non-scalar `Nat` positions:** When `b0` or `e0` exceeded `LEAN_MAX_SMALL_NAT` (e.g. `2^100`), `lean_string_utf8_extract` returned the input string `s` (without `lean_inc(s)` before `#14687`, causing UAF!) instead of clamping to `SIZE_MAX`, whereas the logical definition returned `""` for `String.Pos.Raw.extract "abc" ⟨2^100⟩ ⟨1⟩`. |
| `ccfc89f86787` | `#13989` | LCNF `Simp/ConstantFold.lean` | **`Bool` constant-folding miscompilation:** `getBoolLit` checked `return ctor == ``Bool.true` on any 0-ary `.const name [] #[]`, silently folding **any** non-inlined 0-ary `Bool` function (`@[noinline] def myBool := true`) to `false` because its constant name was `myBool` $\ne$ `Bool.true`! |
| `28de11f21b60` | `#14078` | `Init/Data/Int/Bitwise.lean` (`IntX.ofIntClamp`) | **Signed clamping inversion:** `Int8/16/32/64/ISize.ofIntClamp` returned `IntX.minValue` instead of `IntX.maxValue` when `i > IntX.maxValue.toInt`. |
| `5949ae86a2a0` | `#13421` | LCNF `ExpandResetReuse.lean` | **`Reset`/`Reuse` double-projection corruption:** When expanding `reset`/`reuse` in the presence of two projections (`oproj`) of the same field from the reset object, the second projection read overwritten/released memory. |
| `f180c9ce1796` | `#13435` | LCNF `EmitC.lean` (`quoteString`) | **Greedy C hex escape in `EmitC`:** Control characters $\le 31$ were emitted as `\xNN` instead of 3-digit octal `\NNN`, so a Lean string literal `"\x01abc"` emitted `"\x01abc"` in C, where C parsed `\x01abc` as a single out-of-range hex escape. |
| `8dc4c16fce95` | `#13242` | LCNF `ToMono.lean` | **`String` pattern-matching lowering bug:** Pattern matching on `String.mk` in `ToMono` had not been updated from `String.data` (`List Char`) to `String.toByteArray` (`ByteArray`), miscompiling `cases` on `String`. |
| `08595c5f8fde` & `90b5e3185b3b` | `#13052`, `#13022` | LCNF `InferBorrow.lean` & `IR/CompilerM.lean` | **Borrow inference & `@[export]` ABI mismatch:** Parameters of `@[export]` functions were not added to the owned parameter set during `InferBorrow`, causing values they flowed into to be wrongly inferred as borrowed and freed prematurely. |
| `flake.nix:60-63` | GMP `< 6.3.0` | `libgmp` (`mpz.cpp`) | **Upstream GMP arithmetic bug:** `flake.nix` explicitly overrides `nixpkgs-older`'s GMP 6.1.2 to GMP 6.3.0 because earlier GMP versions contain bugs that can produce unsound results in Lean. |

## Boundaries

- **Verified extraction for Lean 4 (`Not Supported / Absent in Lean v4.34.1`):** Unlike Rocq (`MetaRocq` verified erasure + `CertiCoq` verified C/Clight codegen) or HOL4 (`CakeML` verified in-logic bootstrapping to machine code), Lean `v4.34.1` has **no** mechanically verified compiler or verified extraction pipeline from `Expr` or `LCNF` to C or machine code. `Lean4Lean` (`digama0/lean4lean`) verifies the Lean typechecker in Lean, not the LCNF compiler (`ToLCNF`, `ToMono`, `InferBorrow`, `ExplicitRC`, `ExpandResetReuse`, `EmitC`) or the C++ runtime (`libleanrt.a`).
- **32-bit Linux and WebAssembly native targets (`Unsupported in official v4.34.1 releases`):** Although `CMakeLists.txt` and `ci.yml:415-440` retain commented-out build configurations for `-linux_x86` (`-m32 -DUSE_GMP=OFF -DMMAP=OFF`) and `-linux_wasm32`, both are disabled in official releases due to 2 GiB address-space exhaustion during module builds.
- **ARM MTE / HWASAN incompatibility (`Known Not to Apply`):** Because `lean_dec_ref_cold` packs a 48-bit pointer into `m_rc` (32 bits) + `m_cs_sz` (16 bits) during deallocation (`include/lean/lean.h:142-146`), native Lean binaries cannot run under ARM Memory Tagging Extension (MTE) or Hardware-Assisted AddressSanitizer (HWASAN).

## Evidence

- **Primary upstream sources (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`):**
  - Compiler pipeline and passes: `src/Lean/Compiler/LCNF/Main.lean:105-193`, `src/Lean/Compiler/LCNF/Passes.lean:119-185`, `src/Lean/Compiler/LCNF/ToDecl.lean:85-181`, `src/Lean/Compiler/LCNF/ToLCNF.lean:435-850`, `src/Lean/Compiler/LCNF/ToMono.lean:1-215`, `src/Lean/Compiler/LCNF/ToImpure.lean:1-338`, `src/Lean/Compiler/LCNF/ToImpureType.lean:212-298`, `src/Lean/Compiler/LCNF/InferBorrow.lean:1-454`, `src/Lean/Compiler/LCNF/ExplicitBoxing.lean:1-378`, `src/Lean/Compiler/LCNF/ExplicitRC.lean:1-704`, `src/Lean/Compiler/LCNF/ResetReuse.lean:1-333`, `src/Lean/Compiler/LCNF/ExpandResetReuse.lean:1-385`, `src/Lean/Compiler/LCNF/EmitC.lean:1-1189`, `src/Lean/Compiler/IR/CompilerM.lean:85-115`, `src/Lean/Compiler/IR/ToIR.lean:1-213`, `src/LeanIR.lean:1-175`, `src/Leanc.lean:1-67`.
  - Code-substitution attributes and native evaluation hooks: `src/Lean/Compiler/ImplementedByAttr.lean:51-81`, `src/Lean/Compiler/ExternAttr.lean:1-136`, `src/Lean/Compiler/CSimpAttr.lean:60-144`, `src/Lean/Compiler/LCNF/Simp/SimpValue.lean:65-75`, `src/Lean/Meta/Native.lean:29-78`, `src/Lean/Elab/Tactic/Decide.lean:1-195`, `src/Init/Core.lean:2340-2415`, `src/Lean/Util/CollectAxioms.lean:35-95`, `src/kernel/type_checker.cpp:604-635`, `src/library/ir_interpreter.cpp:341-412, 826-965, 1157-1240`.
  - Runtime and build configuration: `include/lean/lean.h:1-1850`, `include/lean/config.h:1-12`, `src/runtime/object.cpp`, `src/runtime/mpz.h`, `src/runtime/mpz.cpp`, `src/runtime/sharecommon.cpp`, `CMakeLists.txt:1-204`, `src/CMakeLists.txt:1-900`, `script/prepare-llvm-{linux,macos,mingw}.sh`, `flake.nix:1-106`, `.github/workflows/ci.yml:275-450`.
- **Preserved executable probes in `support/`:**
  - [`support/LeanNativeCompilationAndTrustProbe.lean`](support/LeanNativeCompilationAndTrustProbe.lean): Mechanized Lean `v4.34.1` file demonstrating `@[implemented_by]`, `@[csimp]` (including axiom-hiding of `unsound_csimp_ax`), `Lean.ofReduceBool`, `native_decide` (`Lean.Meta.nativeEqTrue`), kernel proofs of `False`, and native binary divergence.
  - [`support/verify_lean_native_pipeline.py`](support/verify_lean_native_pipeline.py): Standalone revalidation script verifying the axiom footprints, C emission determinism (`SHA-256: 0f9dfb23...`), `leanc -O3` ELF determinism (`SHA-256: 83b23bad...`), and runtime behavior of the compiled binary.

## Revalidation

Run the self-contained verification script from a machine with Lean `v4.34.1` installed:

```bash
python3 reports/lean-native-compilation-pipeline-runtime-and-trust-surface/support/verify_lean_native_pipeline.py
```

The script elaborates `LeanNativeCompilationAndTrustProbe.lean` with `-DElab.async=false`, asserts that `#print axioms` reports zero axioms for the kernel `rfl` proofs, `[Lean.ofReduceBool, Lean.trustCompiler]` for the `ofReduceBool` proofs (with `unsound_csimp_ax` absent), and `_native.native_decide.ax_1` for `native_decide`, verifies that two independent `lean --c` and `leanc -O3` builds produce identical SHA-256 digests, and confirms that the compiled binary prints `true` for the functions that the kernel proves equal to `false`.
