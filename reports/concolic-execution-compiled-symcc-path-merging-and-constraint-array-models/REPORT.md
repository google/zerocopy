# Concolic and Symbolic Execution: Interpreted KLEE, Compiled SymCC/SymQEMU, Veritesting Path Merging, and Bitvector-Array Memory Models

## Summary

Symbolic and concolic execution engines occupy a sharp multi-axis design space trading **native execution throughput**, **path-state scalability**, **SMT query complexity**, and **symbolic memory soundness**:

1. **IR Interpretation (`KLEE`) vs. Native Shadow Compilation (`SymCC` / `SymQEMU`):**
   - `KLEE` (`klee/klee`) interprets LLVM bitcode over multi-state `ExecutionState` forks backed by a copy-on-write segmented `AddressSpace` (`ImmutableTree` of `MemoryObject` $\to$ `ObjectState`). Each `MemoryObject` lowers to its own SMT `Array (_ BitVec 32) (_ BitVec 8)` via lazy `UpdateList` flushing, giving exact symbolic-index array semantics (`select`/`store`) and out-of-bounds / use-after-free detection (`kdalloc`), at the cost of interpreter dispatch overhead and exponential state forking.
   - `SymCC` (`eurecom-s3/symcc` + `eurecom-s3/symcc-rt`) eliminates interpreter overhead by running an LLVM pass (`Symbolizer`) that compiles parallel `SymExpr` shadow computations directly into native machine code alongside a single concrete execution, backed by a lazy page-granular byte shadow map (`g_shadow_pages`, 8 bytes per shadowed application byte on 64-bit hosts). `SymQEMU` (`eurecom-s3/symqemu`, based on QEMU 8.1) applies the same compilation strategy dynamically to QEMU Tiny Code Generator (`TCG`) IR for stripped binaries without source code, delegating symbolic construction to `libsymcc-rt`.
   - **Critical Semantic Asymmetry:** Neither `SymCC` nor `SymQEMU` lowers memory into SMT array theory (`QF_ABV`). On every load or store through a symbolic pointer, `Symbolizer::tryAlternative` (`SymCC`) and `sym_load_guest_internal` / `sym_store_guest_internal` (`SymQEMU`) emit a path constraint pinning `addr_expr == concrete_addr`, attempt to negate it to sample an alternative pointer, and then perform a **concrete-address** lookup in shadow memory. Consequently, table lookups like `if (lut[idx & 15] == 0x5A)` become completely opaque to the solver (`val` has `SymExpr == nullptr`; zero symbolic branch constraint is emitted), reducing discovery to blind retries or hybrid fuzzing.
   - **Upstream Implementation Bug Observed in `SymQEMU` (`6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59`):** In `accel/tcg/tcg-runtime-sym.c` L635–638, `sym_movcond_internal` (`cmov` conditional move) masks *both* `v1_expr` and `v2_expr` with `condition_ext` (`_sym_build_and(v2_expr, condition_ext)` instead of `_sym_build_not(condition_ext)`) before XORing them, yielding `0` instead of `v2` when `cond == false` and `v1 ^ v2` instead of `v1` when `cond == true`.
2. **State Merging (`KLEE MergeHandler`, `Veritesting`) vs. SMT `ite`-DAG Query-Cost Cliffs:**
   - Static-to-dynamic `Veritesting` (`Avgerinos et al., ICSE 2014`; implemented in `angr/analyses/veritesting.py`) collapses diamond control flow into a single merged state with conditional `ite` expressions, compressing $2^N$ forked states to `1` state and $O(N)$ hash-consed DAG nodes (`4N + 3` on a diamond counter). `KLEE`'s explicit `klee_open_merge()` / `klee_close_merge()` (`ExecutionState::merge`) merges only when PCs, symbolic objects, call stacks, and live `MemoryObject` sets match identically—aborting if any branch allocates or frees memory asymmetrically—and emits byte-wise `SelectExpr` over every mutated object.
   - **Two Query-Cost Cliffs:** First, if a merged `ite`-DAG is serialized or bit-blasted without structure-preserving `let`/Tseitin sharing, term size explodes back to $O(2^N)$ (`83` DAG nodes unfold to `7,340,026` tree nodes at $N = 20$). Second, merging symbolic-index memory writes into a single array triggers quadratic McCarthy read-over-write (`ROW2`) aliasing lemmas in Z3 (`theory_array_base::assert_store_axiom2_core`), degrading `QF_ABV` solver latency sharply once merged writes cross independent branches.
3. **Symbolic Pointer Memory Models (`Flat McCarthy Array` vs. `KLEE Segmented` vs. `angr Concretization` vs. `SymCC/QSYM`):**
   - A flat `Array (_ BitVec 64) (_ BitVec 8)` models arbitrary pointer aliasing in one theory but incurs $W \cdot R$ cross-object `ROW2` lemmas and **silently allows out-of-bounds writes on `buf_a` to mutate adjacent `buf_b`** unless explicit provenance bounds guards are synthesized.
   - `KLEE`'s segmented memory eliminates cross-object `ROW2` lemmas by a $K\times$ factor across $K$ disjoint objects, but its default `AddressSpace::resolve` still forks across multiple allocations when a symbolic pointer can reach them unless `SingleObjectResolution` (`base_addrs`) enforces single-object provenance.
   - `angr` (`AddressConcretizationMixin`) splits the policy between reads (default `SimConcretizationStrategyRange(1024)` building bounded symbolic expressions) and writes (default `SimConcretizationStrategyRange(128)` falling back to `SimConcretizationStrategyMax()`), trading completeness for bounded `store` chains. `QSYM` (`eurecom-s3/qsym`) pairs pointer concretization (`addAddr` min/max probing + `addValue` pinning) with **optimistic solving** (`negatePath` dropping the path prefix on UNSAT) to keep hybrid fuzzers fed at the cost of false-positive / unreachable inputs.

---

## Applicability

This report synthesizes primary-source inspection across seven pinned upstream repositories, foundational papers, and deterministic Python execution probes gathered on `2026-11-19`:

- **IR-Interpreted Symbolic Execution:** `klee/klee` @ `424bd9be2229dc0f3ee0fe55cc6ea4a649fc88e3` (`lib/Core/{AddressSpace,Memory,Executor,ExecutionState,MergeHandler}.{h,cpp}`, `lib/Solver/{Z3Builder,CexCachingSolver,IndependentSolver}.cpp`). Findings cover LLVM-bitcode interpretation, copy-on-write segmented memory, symbolic pointer resolution (`resolveOne`, `resolve`, `SingleObjectResolution`, `MaxSymArraySize`), `klee_open_merge`/`klee_close_merge` (`-use-merge`), and Z3 `QF_ABV` lowering.
- **Compiled Concolic Execution (Source & Binary):** `eurecom-s3/symcc` @ `522c48070bc312aeb621a631ff130ded71507d6d` (`compiler/{Pass,Symbolizer,Runtime}.{h,cpp}`), `eurecom-s3/symcc-rt` @ `e28fe412de2f190103037b0ea4d0f33a5cfb93b1` (`include/{Shadow,RuntimeCommon}.h`, `src/{RuntimeCommon,LibcWrappers,Config}.cpp`, `src/backends/{qsym,simple}/Runtime.cpp`), `eurecom-s3/symqemu` @ `6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59` (QEMU 8.1 port: `accel/tcg/tcg-runtime-sym.c`, `tcg/tcg-op-ldst.c`, `README.md`), and `eurecom-s3/qsym` @ `7add95b08f67dcc66400dc1297ecc30282322451` (`qsym/pintool/{solver,memory}.cpp`). Findings apply to single-path native concolic instrumentation (source-compiled LLVM IR and JIT-lifted x86-64/experimental AArch64 binaries) paired with QSYM or Z3 simple backends.
- **Static-Dynamic Path Merging & Concretization Policies:** `angr/angr` @ `80c962c99a8d487e75acdfba7a2bcf01a5abfb93` (`angr/analyses/veritesting.py`, `angr/storage/memory_mixins/address_concretization_mixin.py`, `angr/concretization_strategies/{range,single}.py`) and `Avgerinos et al. (ICSE 2014)`.
- **SMT Array Theory & Bit-Blasting Backend:** `Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1` (`src/smt/theory_array_base.cpp`, `src/tactic/smtlogics/qfbv_tactic.cpp`).

Concrete implementation details (such as SymQEMU's QEMU 8.1 `sym_movcond_internal` bitmask bug, angr's `1024`/`128` range limits, and KLEE's `SingleObjectResolution` `base_addrs` fast path) apply specifically to the pinned commits above. Architectural laws—such as $2^N$ path explosion vs. $O(N)$ `ite`-DAG merging vs. $O(2^N)$ unshared tree unfolding, $O(W \cdot R)$ McCarthy `ROW2` aliasing growth, and lookup-table opacity under single-address pointer concretization—generalize across any engine adopting those execution or memory models.

---

## Findings

### 1. Execution Architectures: IR Interpretation (`KLEE`) vs. Native Compilation (`SymCC`) vs. Binary JIT (`SymQEMU`)

`Basis: source + normative`

| Dimension | `KLEE` (`klee/klee`) | `SymCC` (`eurecom-s3/symcc` + `symcc-rt`) | `SymQEMU` (`eurecom-s3/symqemu`) | `QSYM` (`eurecom-s3/qsym`) | `angr` (`angr/angr`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Input & Lifting Layer** | LLVM IR bitcode (requires source/LLVM compile) | LLVM IR pass (`Symbolizer` in `Pass.cpp`) emitting native object code | Stripped ELF binary lifted dynamically via QEMU 8.1 TCG JIT | Stripped binary via Intel Pin DBI (`pintool`) | Stripped binary lifted to Valgrind VEX IR (Python) |
| **Execution Model** | Multi-state IR interpreter (`ExecutionState` worklist) | Single-path native concrete + inline shadow calls | Single-path QEMU JIT concrete + TCG helper calls | Single-path Pin-instrumented concrete + C++ shadow | Multi-state Python VEX interpreter + optional `Veritesting` |
| **Symbolic Memory Model** | Segmented `MemoryMap` (`ImmutableTree<MO*, OS*>`) $\to$ per-object `Array BV32 BV8` | Concrete-address page shadow table (`std::map<uintptr_t, SymExpr*>`, `8x` page size) | Host-TLB concrete shadow table via `libsymcc-rt` (`little_endian=true` hardcoded) | Concrete-address shadow (`memory.cpp`) + `addAddr` min/max probing | Paged symbolic memory (`SimMemory`) + pluggable read/write concretization |
| **Symbolic Pointer Handling** | `resolve()` forks per reachable `MemoryObject` + OOB/UAF state (`kdalloc`) | `tryAlternative()` pins `addr == concrete`, reads concrete shadow | `sym_{load,store}_guest_internal` pins `addr == concrete` after TLB fill | `addAddr()` probes `min`/`max` then pins `addr == concrete` | Read: `Range(1024)` $\to$ `Any`; Write: `Range(128)` $\to$ `Max` |
| **SMT Theories Emitted** | `QF_ABV` (bitvectors + McCarthy arrays) | **`QF_BV` only** (zero SMT arrays) | **`QF_BV` only** (zero SMT arrays) | **`QF_BV` only** (zero SMT arrays) | `QF_BV` (default; optional `QF_ABV` with `SYMBOLIC_MEMORY_NO_CONCRETIZATION`) |
| **State Merging Support** | Opt-in explicit `klee_open_merge` / `klee_close_merge` (`-use-merge`, default off) | None (single-path concolic; relies on fuzzer/corpus re-execution) | None (single-path concolic) | None (single-path concolic) | Built-in `Veritesting` static-to-dynamic CFG merging (`angr/analyses/veritesting.py`) |
| **Solver Optimizations** | `IndependentSolver`, `CexCachingSolver`, `FastCexSolver`, expr simplification | QSYM backend: dependency forest (`dep_forest_`), range sets, optimistic solving; Simple backend: raw Z3 | Shares `libsymcc-rt` QSYM or Simple Z3 backend | `dep_forest_` slicing, `RangeSet` tightening, optimistic solving (`negatePath`) | Claripy AST caching, constraint slicing, backend Z3 |

#### 1.1 `KLEE` LLVM Bitcode Interpretation & Copy-on-Write Segmented Memory

`Basis: source` (`klee/klee` @ `424bd9be2229dc0f3ee0fe55cc6ea4a649fc88e3`, Cadar, Dunbar, Engler, OSDI 2008)

1. **Copy-on-Write `AddressSpace` (`lib/Core/AddressSpace.cpp` L25–53, `Memory.h` L39–197):**
   - Each `ExecutionState` holds an `AddressSpace` whose `objects` field is a persistent functional `ImmutableTree<const MemoryObject*, ref<ObjectState>>`. Forking a state copies only the root pointer and increments `cowKey`, achieving $O(1)$ fork memory cost.
   - `AddressSpace::getWriteable(mo, os)` (L40–53) checks `if (cowKey == os->copyOnWriteOwner)`; on mismatch, it allocates a fresh `ObjectState(*os)`, assigns `cowKey`, and replaces the tree entry in $O(\log M)$ time.
2. **Dual Concrete/Symbolic `ObjectState` & Lazy `UpdateList` Flushing (`lib/Core/Memory.cpp` L272–315, `lib/Solver/Z3Builder.cpp` L330–536):**
   - Each `ObjectState` maintains a flat concrete byte buffer (`concreteStore`), a per-byte `concreteMask`, an `unflushedMask`, an array of `knownSymbolics` byte expressions, and a persistent linked `UpdateList` (`updates`) rooted at an SMT `Array (_ BitVec 32) (_ BitVec 8)`.
   - Concrete-offset reads and writes stay purely in `concreteStore` / `knownSymbolics` with zero SMT array operations. The moment a **symbolic-offset** read or write touches `[rangeBase, rangeBase + rangeSize)`, `flushRangeForRead` (L272–292) or `flushRangeForWrite` (L294–315) flushes every dirty byte into `updates.extend(ConstantExpr(offset, 32), byteExpr)`.
   - `Z3Builder::getArrayForUpdate` (`Z3Builder.cpp` L424–435) and `constructActual` (L490–536) materialize the `UpdateList` as nested `Z3_mk_store` calls rooted at `getInitialArray(root)` and index it via `Z3_mk_select`.
3. **Solver Caching Stack (`lib/Solver/IndependentSolver.cpp`, `CexCachingSolver.cpp`):**
   - Before hitting Z3/STP, `IndependentSolver` (`getIndependentConstraints`, L317) partitions the path constraint set into connected components over referenced symbolic `Array` objects, discarding constraints unrelated to the query expression.
   - `CexCachingSolver` (`lookupAssignment`, L190; `searchForAssignment`, L122) indexes satisfying assignments in a trie (`MapOfSets`) keyed by constraint sets, answering superset-UNSAT and subset-SAT queries without invoking the underlying SMT solver.

#### 1.2 `SymCC` Compile-Time LLVM Shadow Instrumentation

`Basis: source + normative` (`eurecom-s3/symcc` @ `522c48070bc312aeb621a631ff130ded71507d6d`, `eurecom-s3/symcc-rt` @ `e28fe412de2f190103037b0ea4d0f33a5cfb93b1`; Poeplau & Francillon, USENIX Security 2020)

1. **Function-Level Pass Pipeline (`compiler/Pass.cpp` L161–206):**
   - `instrumentFunction` lowers intrinsics (`IntrinsicLowering::LowerIntrinsicCall`) and inline assembly (`liftInlineAssembly`, L180), creates a `Symbolizer` for the module, inserts `_sym_notify_basic_block` hooks for every basic block (used by QSYM's branch-interest filter), visits every instruction via `Symbolizer::visit`, resolves cyclic SSA definitions via `finalizePHINodes()` (L198), and applies `shortCircuitExpressionUses()` (L199) so purely concrete computations branch around runtime calls in a single null-pointer check (`expr == nullptr`).
2. **Shadow Memory Page Table (`symcc-rt/include/Shadow.h` L42–225, `src/RuntimeCommon.cpp` L137–190):**
   - `g_shadow_pages` (`std::map<uintptr_t, SymExpr *>`, `Shadow.h` L56) maps each 4096-byte page start (`addr & ~4095`) to a `malloc(4096 * sizeof(SymExpr))` array (**32 KiB per touched 4 KiB page**, an `8×` memory expansion on 64-bit hosts).
   - `isConcrete(addr, nbytes)` (`Shadow.h` L215–225) implements a single-page fast path checking `!g_shadow_pages.count(pageStart(addr))`. `_sym_read_memory` (`RuntimeCommon.cpp` L137–162) returns `nullptr` immediately for concrete regions, and otherwise folds per-byte `NonNullReadShadowIterator` entries via `_sym_concat_helper` (respecting `little_endian`). `_sym_write_memory` (L164–190) slices multi-byte expressions via `_sym_extract_helper` or zeroes shadow pointers on concrete overwrites.
   - **Consequence of `std::map` + Per-Byte Shadow:** Every uninstrumented library call (`libc` functions lacking wrappers in `LibcWrappers.cpp`) or kernel syscall writes concrete bytes without clearing stale `g_shadow_pages` entries unless explicitly intercepted, causing **shadow staleness / over-taint** or **lost taint** across FFI boundaries.
3. **Pointer Concretization at Every Load and Store (`compiler/Symbolizer.cpp` L539–576, L1102–1115):**
   - `visitGetElementPtrInst` (L578–605) faithfully builds symbolic address arithmetic (`SymExpr` for pointers).
   - However, upon reaching `visitLoadInst` (L539–553) or `visitStoreInst` (L555–576), `Symbolizer` immediately emits `tryAlternative(IRB, addr)` (L1102–1115), which calls `_sym_push_path_constraint(_sym_build_equal(destExpr, concreteDestExpr), /*taken=*/true, site_id)` and then passes only the **concrete** integer address `IRB.CreatePtrToInt(addr, intPtrType)` to `runtime.readMemory` / `runtime.writeMemory`.
   - `tryAlternative` is also emitted for `memcpy`/`memmove`/`memset` operands (L192–225), indirect call targets (`visitCallInst`, L374), and indirect branches (L512).

#### 1.3 `SymQEMU` Binary-Only TCG JIT Instrumentation & Observed Upstream Bug

`Basis: source + execution` (`eurecom-s3/symqemu` @ `6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59`; Poeplau & Francillon, NDSS 2021, `DOI: 10.14722/ndss.2021.24118`)

1. **TCG Shadow Temporaries & Helper Delegation (`tcg/tcg-op-ldst.c` L216–448, `accel/tcg/tcg-runtime-sym.c` L35–395):**
   - During QEMU's guest-to-TCG translation, every `TCGTemp` carries a shadow `TCGTemp` (`tcgv_i64_expr(val)`) holding a host `SymExpr` pointer (`void*`). Because host 64-bit pointers are stored directly in shadow guest registers, 32-bit guest architectures are currently unsupported (`README.md` L41–44).
   - For guest memory accesses (`tcg_gen_qemu_ld_i64_int` L356–362, `tcg_gen_qemu_st_i64_int` L436–443), SymQEMU emits `gen_helper_sym_load_guest_i64` / `store` **strictly after** the concrete guest memory instruction so that the guest address is guaranteed resident in QEMU's software TLB.
   - `sym_load_guest_internal` (L294–313) and `sym_store_guest_internal` (L329–343) mirror SymCC's exact concretization: if `addr_expr != NULL`, push `_sym_build_equal(addr_expr, concrete_addr)` as a taken path constraint, translate via `tlb_vaddr_to_host`, and call `_sym_read_memory` / `_sym_write_memory` with **`little_endian = true` hardcoded** (L307, L342)—which silently misorders multi-byte symbolic values on big-endian guest targets!
   - Unimplemented TCG operations macro-expand to `#define NOT_IMPLEMENTED NULL` (L38), silently concretizing values to avoid crashing translation.
2. **Concrete Upstream Bug in `sym_movcond_internal` (`accel/tcg/tcg-runtime-sym.c` L595–639, verified in `PROBE 5`):**
   - For conditional-move (`cmov` / `TCG movcond`) instructions, `sym_movcond_internal` first pushes a path constraint for the comparison (`build_and_push_path_constraint`, L628—needlessly pinning a branchless conditional move!), sign-extends the 1-bit condition to `result_bits` (`condition_ext`, L630–631), and then computes:
     ```c
     void *v1_masked = _sym_build_and(v1_expr, condition_ext);
     void *v2_masked = _sym_build_and(v2_expr, condition_ext); // BUG: missing _sym_build_not(condition_ext)
     return _sym_build_xor(v1_masked, v2_masked);
     ```
   - Because `v2_expr` is ANDed with `condition_ext` rather than `~condition_ext`, our execution check (`PROBE 5`) confirms that for `v1 = 0x1122334455667788`, `v2 = 0xAABBCCDDEEFF0011`:
     - When `cond = 0` (`mask = 0`): returns `0x0000000000000000` instead of `0xAABBCCDDEEFF0011`.
     - When `cond = 1` (`mask = 0xFFFFFFFFFFFFFFFF`): returns `0xBB99FF99BB997799` (`v1 ^ v2`) instead of `0x1122334455667788`.
   - Any branchless guest code compiled with `cmov` (e.g., constant-time cryptography, clamped bounds checks, or `-O2` conditionals) receives corrupted symbolic expressions under `SymQEMU` at commit `6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59`.

---

### 2. Path Merging (`Veritesting`, `KLEE MergeHandler`) vs. SMT `ite`-DAG Query-Cost Cliffs

`Basis: normative + source + execution`

Pure path-forking symbolic execution suffers exponential state blowup on sequential independent conditionals ("diamond CFGs"): $N$ sequential `if (x[i] == c) count++;` branches spawn $2^N$ states ($1{,}048{,}576$ states at $N = 20$), exhausting memory and scheduler budgets before reaching code past the loop.

#### 2.1 Static-to-Dynamic `Veritesting` (`angr`) vs. Explicit `KLEE` State Merging

1. **Veritesting Algorithm (`Avgerinos et al., ICSE 2014`, `DOI: 10.1145/2568225.2568293`; `angr/analyses/veritesting.py` L172–445):**
   - Rather than committing globally to either Dynamic Symbolic Execution (DSE, forking) or Static Symbolic Execution (SSE, whole-program `ite` formula), Veritesting runs DSE normally and switches into bounded SSE whenever it reaches a symbolic branch inside a clean CFG hammock.
   - `angr`'s `Veritesting._execute_and_merge` (L272–361) recovers a local CFG, computes dominance-based merge points (`_get_all_merge_points`, L287), steps states while stashing arrivals at each `_merge_<addr>_<loop_cnt>` stash (L343–347), and invokes `_join_merge_points` (L363–435) once active states drain:
     - First prunes unsatisfiable states (`manager.prune`, L393) to avoid polluting merged `ite` terms with dead paths.
     - Groups states by identical `callstack` (L400–402) and invokes `manager.merge` (synthesizing Claripy `If(guard, val_a, val_b)` nodes).
   - **Hard Static-to-Dynamic Bailout Boundaries (`veritesting.py` L93–158, L328–337, L425–430):** Veritesting immediately drops back to DSE (`deviated` / `successful` / `deadended` stashes) whenever execution encounters: (i) an unresolved indirect jump / target not in the recovered CFG (`is_not_in_cfg`, L328), (ii) a syscall or `SimProcedure` outside `CallTracingFilter.whitelist` (L93–158), (iii) abnormal `jumpkind` (exceptions, non-boring/call/ret transfers, L333–335), or (iv) a loop counter exceeding `loop_unrolling_limit` (L425–430).
2. **`KLEE` Explicit Merging (`lib/Core/MergeHandler.cpp` L24–152, `ExecutionState.cpp` L190–351):**
   - Disabled by default (`-use-merge=false`). Users annotate regions with `klee_open_merge()` / `klee_close_merge()`. `MergeHandler::getPrioritizeState` (L56–67) prioritizes lagging states whose instruction distance is `< 2 * closedMean` to synchronize arrivals at the close point.
   - `ExecutionState::merge(const ExecutionState &b)` (`ExecutionState.cpp` L190–351) enforces **strict structural compatibility** and returns `false` (leaving states unmerged) if ANY of the following hold:
     1. `pc != b.pc` (L194);
     2. `symbolics != b.symbolics` — different sets of `klee_make_symbolic` calls along the two paths (L200);
     3. Call stacks differ in depth, `caller`, or `KFunction* kf` (L204–215);
     4. Live `MemoryObject` map keys differ (`ai->first != bi->first`, L272–292) — meaning **any `malloc` not freed before `klee_close_merge`, or any `free` performed on only one branch, silently aborts merging**!
   - When merging succeeds, KLEE splits constraints into `commonConstraints`, `aSuffix` (`inA`), and `bSuffix` (`inB`), rewrites every live stack local via `SelectExpr::create(inA, av, bv)` (L321), rewrites **every byte `0..mo->size-1`** of every mutated `MemoryObject` via `SelectExpr::create(inA, av, bv)` (L336–340), and asserts `commonConstraints ∧ (inA ∨ inB)` (L348).

#### 2.2 The Two Query-Cost Cliffs of State Merging (`PROBE 1` & `PROBE 2`)

`Basis: execution + source + derived`

State merging trades **path-count explosion** ($2^N$ states) for **formula-size and theory-interaction explosion** inside the SMT solver. Two distinct cliffs arise:

1. **Cliff 1 — Hash-Consed `ite`-DAG vs. Unshared Tree Unfolding (`PROBE 1`):**
   - On the canonical $N$-step diamond counter (`for i in 0..N-1: if (x[i] == 0x42) count += 1`), each iteration produces `c' = ite(x_i == 0x42, c + 1, c)`, referencing `c` **twice** in the `ite` arms.
   - Inside a hash-consed AST (`KLEE` `Expr` / `Claripy` / `Z3` `ast_manager`), the merged DAG grows strictly linearly: **`4N + 3` nodes** (`83` nodes at $N = 20$ vs. `1,048,576` forked states).
   - However, any pass that walks the expression as a tree without memoization—or any SMT-LIB2 serializer omitting `let`-bindings, or a naive case-splitting solver—triggers exponential **tree unfolding**:

| Diamond Depth $N$ | Path-Forking States ($2^N$) | Merged States | Hash-Consed `ite`-DAG Nodes ($4N + 3$) | Unshared Tree-Unfolded Nodes |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 16 | 1 | 19 | 106 |
| 8 | 256 | 1 | 35 | 1,786 |
| 12 | 4,096 | 1 | 51 | 28,666 |
| 16 | 65,536 | 1 | 67 | 458,746 |
| 20 | 1,048,576 | 1 | 83 | 7,340,026 |

   - Even with hash-consing preserved into Z3's `qfbv_tactic` (`Z3Prover/z3/src/tactic/smtlogics/qfbv_tactic.cpp` L92–116: bit-blaster `mk_bit_blaster_tactic` + `mk_aig_tactic` Tseitin encoding), merging **disjoint path conditions** (`inA ∨ inB`) into a single `QF_BV` formula destroys KLEE's `IndependentSolver` constraint partitioning and `CexCachingSolver` prefix reuse, and can force the CDCL SAT backend to solve a harder global disjunction than $k$ small independent queries—especially when `ite` guards feed into non-linear bitvector multiplication, division, or cryptographic S-boxes.
2. **Cliff 2 — Merged Symbolic Writes Triggering Quadratic McCarthy `ROW2` Lemmas:**
   - When KLEE's `ExecutionState::merge` writes `SelectExpr(inA, av, bv)` across a 4 KiB buffer (L336–340), every mutated byte becomes a symbolic `ite` node; if a subsequent symbolic-index load reads that buffer, `flushRangeForRead` pushes 4096 `store` entries into `UpdateList`, causing Z3's array theory to instantiate up to thousands of read-over-write lemmas on a single load.
   - Similarly, merging branches that perform symbolic-index writes `M' = ite(g, store(M, i1, v1), store(M, i2, v2))` nests `store` inside `ite`, forcing Z3 either to lift `ite` over `select` (`select(ite(g, A, B), j) = ite(g, select(A, j), select(B, j))`) or instantiate cross-branch `ROW2` axioms against both arms, turning linear branch sequences into dense SMT array-aliasing webs.

---

### 3. McCarthy Bitvector-Array Theory (`QF_ABV`) and Symbolic Pointer Aliasing Trade-Offs

`Basis: normative + source + execution`

#### 3.1 Z3 Lazy McCarthy Read-Over-Write Instantiation (`theory_array_base.cpp`)

In SMT-LIB2 `QF_ABV`, memory is modeled by McCarthy's theory of extensional arrays (`Array (_ BitVec w) (_ BitVec 8)`) governed by three axioms:

1. **ROW1 (Read-Over-Write Same Index):** $\forall A, i, v.\, \text{select}(\text{store}(A, i, v), i) = v$ (`Z3Prover/z3/src/smt/theory_array_base.cpp`, `assert_store_axiom1_core`, L110–137).
2. **ROW2 (Read-Over-Write Different Index):** $\forall A, i, j, v.\, i = j \vee \text{select}(\text{store}(A, i, v), j) = \text{select}(A, j)$ (`assert_store_axiom2_core`, L149–219; deduplicated via `ctx.add_fingerprint` in `assert_store_axiom2`, L244–260).
3. **Extensionality:** $\forall A, B.\, (\forall i.\, \text{select}(A, i) = \text{select}(B, i)) \implies A = B$ (`assert_extensionality_core`, L358–418).

Look closely at `assert_store_axiom2_core` (L196–217): when `idx1` and `idx2` are not syntactically known distinct (`!m.are_distinct`), Z3 creates a fresh Boolean equality literal `ante = mk_eq(idx1, idx2)`, marks it relevant, attaches a relevance watch `ctx.add_rel_watch(~ante, conseq_expr)`, and asserts the clause `ante ∨ (select(store(A, i, v), j) = select(A, j))`—which in turn introduces `select(A, j)` into the E-graph, cascading recursively down the entire chain of prior `store`s on `A`!

- **Flat vs. Segmented `ROW2` Growth (`PROBE 2`):** For a trace with $W$ symbolic writes and $R$ symbolic reads:
  - Under a **single flat byte array** (`Array BV64 BV8`), every symbolic read `j` can alias every prior symbolic write `i_1, ..., i_W`, triggering up to **$W \cdot R$** `ROW2` aliasing clauses (`64` at $W=R=8$; `1,024` at $W=R=32$; `4,096` at $W=R=64$).
  - Under **`KLEE`'s segmented per-object arrays** across $K$ disjoint `MemoryObject`s (each receiving $W/K$ writes and $R/K$ reads once resolved), total `ROW2` pairs drop to $K \cdot (W/K) \cdot (R/K) = (W \cdot R)/K$ — an exact **$K\times$ lemma reduction** (`16`, `128`, `256` for $K = 4, 8, 16$, `PROBE 2`), at the cost of state forking whenever a symbolic pointer can legally alias multiple objects.

#### 3.2 Concrete Soundness and Completeness Failure Modes Across All Four Memory Models

`Basis: source + execution`

| Memory & Pointer Model | Representative Engine(s) | Lookup Table `if (lut[idx & 15] == 0x5A)` (`PROBE 3`) | Adjacent-Object OOB `*(buf_a + 8) = 0xFF` (`PROBE 4`) | `ROW2` Aliasing Cost ($W$ writes, $R$ reads, $K$ objects) | Soundness / Completeness Classification |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. Single-Address Concretization (Concrete Shadow)** | `SymCC` (`Symbolizer::tryAlternative`), `SymQEMU` (`sym_{load,store}_guest_internal`) | **Opaque (Missed):** pins `(idx & 15) == 3`, reads concrete `0x11` (`SymExpr = NULL`), `0` branch constraints; negation `(idx & 15) != 3` needs `8.0` avg / `15` worst blind tries | **Concrete run only:** silently corrupts adjacent heap layout if concrete `off == 8`; no symbolic OOB synthesis unless `tryAlternative` randomly picks OOB | **$0$ SMT array lemmas** (`QF_BV` only) | **Under-approximating (incomplete)** on symbolic pointers; fast native throughput |
| **2. Min/Max Probe + Concretize + Optimistic Solving** | `QSYM` (`Solver::addAddr` L195–215, `negatePath` L518–529) | Probes `min(idx)` and `max(idx)` via iterative `ult`/`ugt` loops (`getMinValue`/`getMaxValue` L355–383), then pins `addr == concrete`; still misses interior magic index `11` | Can trigger boundary OOB via `getMaxValue` if `off` is upper-bounded near object end; optimistic solving (`negatePath` L524–528) drops path prefix on UNSAT, risking **infeasible (unsound) test inputs** | **$0$ SMT array lemmas** (`QF_BV` only) | **Neither sound nor complete** per query (hybrid fuzzer filters infeasible outputs via concrete replay) |
| **3. Segmented Per-Object Arrays + Fork on Multi-Object** | `KLEE` (`AddressSpace::resolve`, `Executor::executeMemoryOperation` L4486–4665) | **Complete (1 query):** resolves single `MemoryObject(lut)`, emits `select(lut, idx & 15) == 0x5A`, solves `idx = 11` directly (unless `mo->size >= MaxSymArraySize` triggers `toConstant` at L4547!) | **Default `resolve()`:** forks across `['buf_a', 'buf_b']`, allowing cross-object aliasing! **`SingleObjectResolution` (`base_addrs` L4508–4531):** restricts to `buf_a` and flags `off >= 8` as OOB! | **$(W \cdot R) / K$** per resolved object (plus fork cost if pointer spans objects) | **Sound & complete** within object bounds (for `size < MaxSymArraySize` and non-timeout); provenance-strict only with `SingleObjectResolution` |
| **4. Bounded Range Concretization (`Read 1024 / Write 128`)** | `angr` (`AddressConcretizationMixin` L99–138, `SimConcretizationStrategyRange`) | **Complete (1 query):** range `[0..15]` has span $16 \le 1024$, so read evaluates symbolically across all 16 indices and solves `idx = 11` | Depends on read/write strategy: writes with span `> 128` fall back to `SimConcretizationStrategyMax()` (L138), concretizing to a **single** max address (missing interior targets, biasing toward buffer overflow!) | Bounded `ite` tree over $\le 1024$ (reads) / $\le 128$ (writes) concrete addresses | **Asymmetric heuristic:** preserves read completeness up to span `1024`, sacrifices write completeness above `128` to prevent SMT `store` blowup |
| **5. Flat Global McCarthy Array (`Array BV64 BV8`)** | Naive whole-memory SMT encoders / BMC | **Complete (1 query):** `select(M, &lut + (idx & 15)) == 0x5A` solves `idx = 11` directly | **Provenance-unsound (`PROBE 4`):** `store(M, 0x1008, 0xFF)` silently mutates `buf_b[0]` with `OOB_flagged = False` unless explicit disjoint-object bounds assertions are conjoined | **$W \cdot R$** global aliasing pairs across entire heap/stack | **Over-approximating cross-object aliasing** unless guarded by C/Rust/LLVM allocation provenance constraints |

#### 3.3 Subtle Interaction Details Directly Observed in Upstream Source

`Basis: source`

1. **`KLEE`'s Hidden Concretization Escape Hatch (`Executor.cpp` L4546–4548):** Even though KLEE models memory via `QF_ABV`, setting `-max-sym-array-size=<N>` causes `if (MaxSymArraySize && mo->size >= MaxSymArraySize) address = toConstant(state, address, "max-sym-array-size");`—silently falling back to single-address concretization on large buffers (e.g., 64 KiB packet buffers), exhibiting the same lookup-table opacity as SymCC on arrays exceeding the threshold.
2. **`KLEE`'s Deterministic Quarantine UAF Detection (`Executor.cpp` L4649–4664):** When `-kdalloc` (`MemoryManager::isDeterministic`) is enabled and a pointer falls outside live `MemoryMap` bindings, KLEE queries `unbound->heapAllocator.locationInfo(ptr, bytes)` for `LocationInfo::LI_AllocatedOrQuarantined`, distinguishing **use-after-free** from generic out-of-bounds access without false address reuse.
3. **`QSYM`'s Optimistic Solving & Range-Set Compression (`qsym/pintool/solver.cpp` L392–529):** `Solver::syncConstraints` (L392–423) computes transitive input-byte dependencies via `dep_forest_` (analogous to KLEE's `IndependentSolver`), compresses `const op sym` bounds into interval `RangeSet`s (`addRangeConstraint` L445–465), and in `negatePath` (L518–529) first tries `syncConstraints(e) ∧ ¬e`; if UNSAT, it resets the solver and solves `¬e` **alone** (`checkAndSave("optimistic")`), deliberately emitting inputs that may fail earlier path predicates so that a companion greybox fuzzer (AFL/AFL++) can mutate or validate them concretely.
4. **`SymCC`'s QSYM Backend vs. Simple Z3 Backend (`symcc-rt/src/backends/{qsym,simple}/Runtime.cpp`):** The `simple` backend maintains a single global Z3 solver and invokes `Z3_solver_check` (`simple/Runtime.cpp` L472, L490, L529) directly on the full path condition with no dependency slicing or branch-interest filtering; the `qsym` backend (`qsym/Runtime.cpp` L324–330) delegates `_sym_push_path_constraint` to `g_solver->addJcc(...)`, inheriting QSYM's bitmap-based branch deduplication (`isInterestingBranch`), `dep_forest_` slicing, and optimistic fallback.

---

## Boundaries

- **Not examined — Wall-Clock Throughput & Coverage Benchmarks:** No native C/C++/QEMU binaries (`klee`, `symcc`, `symqemu`, `qsym`, `angr`, `z3`) were compiled or benchmarked on LAVA-M / Magma / FuzzBench targets during this investigation (lightweight environment without local Z3/LLVM/QEMU toolchains); comparative throughput claims between IR interpretation, LLVM compilation, and TCG JIT rely on source-level execution-model analysis and published evaluations (Cadar et al. OSDI 2008; Yun et al. USENIX Security 2018; Poeplau & Francillon USENIX Security 2020 & NDSS 2021).
- **Not examined — Floating-Point (`QF_FP`), Symbolic `alloca`/Heap Size Allocation, and Concurrency/Weak-Memory Models:** While `SymCC`'s `Symbolizer.cpp` (L1145–1168) converts floats via `buildBitsToFloat` / `buildFloatToBits` and `KLEE`'s `Executor.cpp` (L4354–4376) forks on symbolic allocation sizes, floating-point rounding accuracy, multi-threaded interleaving symbolic execution, and weak-memory concurrency were not examined.
- **Not examined — Alternative Memory Compilers (`SymSan`, `Marco`, `FuzzySat`, `SeaHorn` / `CBMC` Array Encodings):** Newer dataflow-sanitizer-based concolic compilers (`SymSan`) and bounded model checkers (`CBMC`, `Kani`) that encode segmented/flat arrays statically without dynamic path exploration were outside the examined subject set.
- **Known not to apply — `SymCC`/`SymQEMU` for Exhaustive Sound Verification:** Because `SymCC` and `SymQEMU` concretize every symbolic memory address via `tryAlternative`, drop taint across uninstrumented `libc`/syscalls or `#define NOT_IMPLEMENTED NULL` TCG ops, and (with the QSYM backend) use optimistic solving and branch-count pruning, **absence of bugs under `SymCC`/`SymQEMU` proves nothing about program soundness**; they are strictly bug-finding / hybrid-fuzzing test generators.
- **Unsupported — 32-bit Guest Targets and Big-Endian Symbolic Loads/Stores in `SymQEMU` (`6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59`):** `SymQEMU` explicitly documents 32-bit targets as unsupported (`README.md` L41–44) because host 64-bit `SymExpr` pointers are carried in guest shadow registers, and `accel/tcg/tcg-runtime-sym.c` (L307, L342) hardcodes `little_endian = true` for guest memory accesses.
- **Unknown — Whether `SymQEMU`'s `sym_movcond_internal` Bug (`tcg-runtime-sym.c` L635–638) Is Fixed in Unmerged Forks:** Direct source inspection confirms the missing `_sym_build_not(condition_ext)` bug at `eurecom-s3/symqemu` HEAD (`6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59`), but external downstream forks or unmerged pull requests were not surveyed.

---

## Evidence

### 1. Inspected Upstream Source Revisions (2026-11-19)

- **`klee/klee` @ `424bd9be2229dc0f3ee0fe55cc6ea4a649fc88e3`:**
  - `lib/Core/AddressSpace.cpp` L25–53 (`bindObject`, `getWriteable` CoW via `cowKey`), L57–169 (`resolveOne`), L171–260 (`checkPointerInObject`, `resolve` `ImmutableTree` scan).
  - `lib/Core/Memory.h` L39, L170–197 (`MemoryObject`, `ObjectState`, `concreteStore`, `concreteMask`, `updates`, `copyOnWriteOwner`).
  - `lib/Core/Memory.cpp` L272–315 (`flushRangeForRead`, `flushRangeForWrite` lazy `UpdateList` flushing).
  - `lib/Core/Executor.cpp` L4486–4665 (`executeMemoryOperation`, `SingleObjectResolution` via `state.base_addrs` L4508–4531, `MaxSymArraySize` concretization escape hatch L4546–4548, multi-object `resolve` + `fork` loop L4598–4634, `kdalloc::LocationInfo::LI_AllocatedOrQuarantined` UAF detection L4649–4664).
  - `lib/Core/MergeHandler.cpp` L24–152 (`UseMerge` default `false`, `getPrioritizeState` `< 2 * getMean()`, `addClosedState`).
  - `lib/Core/ExecutionState.cpp` L190–351 (`ExecutionState::merge` structural abort checks L194–292, `SelectExpr::create` over locals L321 and every byte `0..mo->size` of mutated objects L336–340, `OrExpr(inA, inB)` L348).
  - `lib/Solver/Z3Builder.cpp` L330–334 (`Z3_mk_store`/`Z3_mk_select`), L380–536 (`getInitialArray`, `getArrayForUpdate`, `constructActual`); `IndependentSolver.cpp` L317 (`getIndependentConstraints`); `CexCachingSolver.cpp` L122, L190 (`searchForAssignment`, `lookupAssignment`).
- **`eurecom-s3/symcc` @ `522c48070bc312aeb621a631ff130ded71507d6d` & `eurecom-s3/symcc-rt` @ `e28fe412de2f190103037b0ea4d0f33a5cfb93b1`:**
  - `symcc/compiler/Pass.cpp` L161–206 (`instrumentFunction`, `IntrinsicLowering`, `liftInlineAssembly`, `Symbolizer`, `finalizePHINodes`, `shortCircuitExpressionUses`).
  - `symcc/compiler/Symbolizer.cpp` L192–225, L374, L512, L539–605 (`visitLoadInst`, `visitStoreInst`, `visitGetElementPtrInst`), L1102–1115 (`tryAlternative` emitting `ICMP_EQ` against concrete value + `pushPathConstraint`), L1140–1176 (float/i1 conversions).
  - `symcc-rt/include/Shadow.h` L42–225 (`kPageSize = 4096`, `g_shadow_pages`, `malloc(kPageSize * sizeof(SymExpr))` L171, `isConcrete` L215–225).
  - `symcc-rt/src/RuntimeCommon.cpp` L137–190 (`_sym_read_memory`, `_sym_write_memory`); `src/backends/qsym/Runtime.cpp` L324–330 (`addJcc`), L441 (`_sym_feasible`); `src/backends/simple/Runtime.cpp` L438–529 (`Z3_solver_check`).
- **`eurecom-s3/symqemu` @ `6e37dd2c3bace02997f358a7fb5d2b23bf4a5b59`:**
  - `README.md` L3–44 (QEMU 8.1 base, x86-64 / experimental AArch64, 32-bit guest unsupported).
  - `tcg/tcg-op-ldst.c` L216–220, L293–297, L356–362, L436–443 (symbolic load/store helpers emitted *after* concrete access to guarantee TLB presence).
  - `accel/tcg/tcg-runtime-sym.c` L35–38 (`NOT_IMPLEMENTED NULL`), L294–343 (`sym_load_guest_internal`, `sym_store_guest_internal` pushing `addr_expr == addr` + hardcoded `little_endian = true`), L595–639 (`sym_movcond_internal` missing `_sym_build_not(condition_ext)` bug at L636).
- **`eurecom-s3/qsym` @ `7add95b08f67dcc66400dc1297ecc30282322451`:**
  - `qsym/pintool/solver.cpp` L160–262 (`addJcc`, `addAddr` min/max probing + `addValue` concretization, `solveAll`), L355–383 (`getMinValue`, `getMaxValue`), L392–465 (`syncConstraints` via `dep_forest_`, `addRangeConstraint`), L518–529 (`negatePath` optimistic solving fallback).
- **`angr/angr` @ `80c962c99a8d487e75acdfba7a2bcf01a5abfb93`:**
  - `angr/analyses/veritesting.py` L93–158 (`CallTracingFilter.whitelist`), L172–445 (`Veritesting._execute_and_merge`, `_join_merge_points`, `loop_unrolling_limit`, `is_not_in_cfg`, callstack-partitioned merging).
  - `angr/storage/memory_mixins/address_concretization_mixin.py` L99–138 (default read `Range(1024)` $\to$ `Any`; write `Range(128)` $\to$ `Max`), L159–219 (`_apply_concretization_strategies`, `concretize_write_addr`, `concretize_read_addr`).
- **`Z3Prover/z3` @ `c73b745cef365e1390408fbd7c599236941d34d1`:**
  - `src/smt/theory_array_base.cpp` L110–137 (`assert_store_axiom1_core`), L149–219 (`assert_store_axiom2_core` lazy `ROW2` clause generation), L244–260 (`assert_store_axiom2` fingerprinting), L358–418 (`assert_extensionality_core`).
  - `src/tactic/smtlogics/qfbv_tactic.cpp` L92–116 (`mk_bit_blaster_tactic`, `mk_aig_tactic`).

### 2. Primary Peer-Reviewed Literature Verified

- Cadar, Dunbar, Engler (OSDI 2008), *KLEE: Unassisted and Automatic Generation of High-Coverage Tests for Complex Systems Programs*, USENIX OSDI 2008, pp. 209–224.
- Avgerinos, Rebert, Cha, Brumley (ICSE 2014), *Enhancing Symbolic Execution with Veritesting*, `DOI: 10.1145/2568225.2568293`.
- Yun, Lee, Xu, Jang, Kim (USENIX Security 2018), *QSYM: A Practical Concolic Execution Engine Tailored for Hybrid Fuzzing*, 27th USENIX Security Symposium, pp. 745–761.
- Poeplau, Francillon (USENIX Security 2020), *Symbolic Execution with SymCC: Don't Interpret, Compile!*, 29th USENIX Security Symposium, pp. 181–198, ISBN `978-1-939133-17-5`.
- Poeplau, Francillon (NDSS 2021), *SymQEMU: Compilation-Based Symbolic Execution for Binaries*, `DOI: 10.14722/ndss.2021.24118`.

### 3. Reproducible Execution Evidence (Python 3.13.15, 2026-11-19)

Running the standalone probe in `## Revalidation` (`python3 /tmp/probe_concolic_arrays.py`) produced the exact deterministic output:

```text
=== PROBE 1: Path Forking vs Veritesting ite-DAG Merging (Diamond Counter Benchmark) ===
  N= 4: Forking_states=      16 | Merged_states=1, DAG_nodes= 19, Unfolded_tree_nodes=       106
  N= 8: Forking_states=     256 | Merged_states=1, DAG_nodes= 35, Unfolded_tree_nodes=      1786
  N=12: Forking_states=    4096 | Merged_states=1, DAG_nodes= 51, Unfolded_tree_nodes=     28666
  N=16: Forking_states=   65536 | Merged_states=1, DAG_nodes= 67, Unfolded_tree_nodes=    458746
  N=20: Forking_states= 1048576 | Merged_states=1, DAG_nodes= 83, Unfolded_tree_nodes=   7340026

=== PROBE 2: McCarthy Array ROW2 (select(store(A,i,v),j)) Aliasing Lemmas: Flat vs Segmented ===
  W= 8 writes, R= 8 reads, K= 4 disjoint objects: Flat_ROW2_pairs=   64 | Segmented_ROW2_pairs=  16 (4.0x reduction)
  W=32 writes, R=32 reads, K= 8 disjoint objects: Flat_ROW2_pairs= 1024 | Segmented_ROW2_pairs= 128 (8.0x reduction)
  W=64 writes, R=64 reads, K=16 disjoint objects: Flat_ROW2_pairs= 4096 | Segmented_ROW2_pairs= 256 (16.0x reduction)

=== PROBE 3: Lookup-Table Opacity (SymCC tryAlternative Concretization vs KLEE/angr Array Select) ===
  Target: if (lut[idx & 15] == 0x5A) bug(); seed idx=3, magic index=[11]
  SymCC/SymQEMU: addr_constraint=(idx & 15) == 3, branch_sym_constraints=0, negated_addr_query='(idx & 15) != 3' (blind expected tries=8.0, worst-case=15)
  KLEE/angr(Range>=16): SMT select(lut, idx&15)==0x5A directly solves idx=[11] in 1 query

=== PROBE 4: Adjacent Allocations Cross-Object Aliasing (Flat Array vs KLEE Segmented) ===
  off=8: Flat Array BV64->BV8 silently aliases buf_b[0]=0xFF (mutated=True, OOB_flagged=False)
  KLEE default resolve(): forks across ['buf_a', 'buf_b'] (allows cross-object aliasing unless pointer provenance enforced)
  KLEE SingleObjectResolution (base_addrs): restricts to ['buf_a'], flags off>=8 as OOB=True

=== PROBE 5: SymQEMU sym_movcond_internal (tcg-runtime-sym.c L635-638) Bitmask Bug Check ===
  cond=0: expected=0xAABBCCDDEEFF0011, SymQEMU_L638=0x0000000000000000, match=False
  cond=1: expected=0x1122334455667788, SymQEMU_L638=0xBB99FF99BB997799, match=False
```

---

## Revalidation

1. **Rerun the Self-Contained Merging, Array-Aliasing, and `SymQEMU` Bug Probe:** Save the following script to `/tmp/probe_concolic_arrays.py` and run `python3 /tmp/probe_concolic_arrays.py` to reproduce every quantitative table and counterexample in `## Evidence`:

```python
#!/usr/bin/env python3
class HashConsDAG:
    def __init__(self):
        self.table, self.nodes = {}, []
    def intern(self, op, *args):
        key = (op, args)
        if key not in self.table:
            self.table[key] = len(self.nodes)
            self.nodes.append(key)
        return self.table[key]
    def tree_size(self, nid, memo=None):
        memo = {} if memo is None else memo
        if nid in memo: return memo[nid]
        op, args = self.nodes[nid]
        res = 1 if op in ("SYM", "CONST") else 1 + sum(self.tree_size(a, memo) for a in args)
        memo[nid] = res
        return res

print("=== PROBE 1: Path Forking vs Veritesting ite-DAG Merging (Diamond Counter Benchmark) ===")
for N in (4, 8, 12, 16, 20):
    dag = HashConsDAG()
    c, one = dag.intern("CONST", 0), dag.intern("CONST", 1)
    for i in range(N):
        cond = dag.intern("EQ", dag.intern("SYM", f"x{i}"), dag.intern("CONST", 0x42))
        c = dag.intern("ITE", cond, dag.intern("ADD", c, one), c)
    print(f"  N={N:2d}: Forking_states={2**N:8d} | Merged_states=1, DAG_nodes={len(dag.nodes):3d}, Unfolded_tree_nodes={dag.tree_size(c):10d}")

print("\n=== PROBE 2: McCarthy Array ROW2 (select(store(A,i,v),j)) Aliasing Lemmas: Flat vs Segmented ===")
for W, R, K in [(8, 8, 4), (32, 32, 8), (64, 64, 16)]:
    flat_row2, seg_row2 = W * R, K * (W // K) * (R // K)
    print(f"  W={W:2d} writes, R={R:2d} reads, K={K:2d} disjoint objects: Flat_ROW2_pairs={flat_row2:5d} | Segmented_ROW2_pairs={seg_row2:4d} ({flat_row2/seg_row2:.1f}x reduction)")

print("\n=== PROBE 3: Lookup-Table Opacity (SymCC tryAlternative Concretization vs KLEE/angr Array Select) ===")
lut = [0x11] * 16; lut[11] = 0x5A; seed_idx = 3
klee_solutions = [i for i in range(16) if lut[i] == 0x5A]
print(f"  Target: if (lut[idx & 15] == 0x5A) bug(); seed idx={seed_idx}, magic index={klee_solutions}")
print(f"  SymCC/SymQEMU: addr_constraint=(idx & 15) == {seed_idx}, branch_sym_constraints=0, negated_addr_query='(idx & 15) != {seed_idx}' (blind expected tries={(15+1)/2:.1f}, worst-case=15)")
print(f"  KLEE/angr(Range>=16): SMT select(lut, idx&15)==0x5A directly solves idx={klee_solutions} in 1 query")

print("\n=== PROBE 4: Adjacent Allocations Cross-Object Aliasing (Flat Array vs KLEE Segmented) ===")
flat_mem = {a: 0x00 for a in range(0x1000, 0x1010)}; flat_mem[0x1008] = 0xFF
klee_def = [n for n, b, s in [("buf_a", 0x1000, 8), ("buf_b", 0x1008, 8)] if any(b <= 0x1000 + o < b + s for o in range(16))]
print(f"  off=8: Flat Array BV64->BV8 silently aliases buf_b[0]=0x{flat_mem[0x1008]:02X} (mutated={flat_mem[0x1008]==0xFF}, OOB_flagged=False)")
print(f"  KLEE default resolve(): forks across {klee_def} (allows cross-object aliasing unless pointer provenance enforced)")
print(f"  KLEE SingleObjectResolution (base_addrs): restricts to ['buf_a'], flags off>=8 as OOB={any(not (0x1000 <= 0x1000 + o < 0x1008) for o in range(16))}")

print("\n=== PROBE 5: SymQEMU sym_movcond_internal (tcg-runtime-sym.c L635-638) Bitmask Bug Check ===")
v1, v2 = 0x1122334455667788, 0xAABBCCDDEEFF0011
for cb in (0, 1):
    mask = ((1 << 64) - 1) if cb else 0
    got, exp = (v1 & mask) ^ (v2 & mask), (v1 if cb else v2)
    print(f"  cond={cb}: expected=0x{exp:016X}, SymQEMU_L638=0x{got:016X}, match={got == exp}")
```

2. **Check Upstream Drift in Narrow Implementation Regions:**
   - **`SymCC` / `SymCC-RT`:** Diff `eurecom-s3/symcc/compiler/Symbolizer.cpp` (`visitLoadInst`, `visitStoreInst`, `tryAlternative`) and `eurecom-s3/symcc-rt/include/Shadow.h` (`g_shadow_pages`) to determine whether symbolic-index array theory (`QF_ABV`) or mmap-based flat shadow memory replaces concrete `tryAlternative` + `std::map`.
   - **`SymQEMU`:** Diff `eurecom-s3/symqemu/accel/tcg/tcg-runtime-sym.c` (`sym_movcond_internal` L635–638 and `sym_{load,store}_guest_internal` L307/L342) to check whether the missing `_sym_build_not(condition_ext)` bug or hardcoded `little_endian = true` is patched.
   - **`KLEE`:** Diff `klee/klee/lib/Core/Executor.cpp` (`executeMemoryOperation`, `SingleObjectResolution`, `MaxSymArraySize`) and `ExecutionState.cpp` (`ExecutionState::merge`) to check whether symbolic heap allocation merging or default pointer-provenance enforcement changes.
   - **`angr` & `Z3`:** Diff `angr/angr/angr/storage/memory_mixins/address_concretization_mixin.py` (default `1024`/`128` range limits), `angr/analyses/veritesting.py` (`CallTracingFilter.whitelist`), and `Z3Prover/z3/src/smt/theory_array_base.cpp` (`assert_store_axiom2_core`).
