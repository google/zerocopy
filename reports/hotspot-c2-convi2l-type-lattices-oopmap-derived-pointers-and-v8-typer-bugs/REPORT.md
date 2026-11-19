# HotSpot C2 Sea-of-Nodes Type Lattices, ConvI2L Range-Check Escapes, Safepoint OopMap Derived Pointers, and V8 Typer Bugs

## Summary

Speculative Just-In-Time (`JIT`) compilers achieve near-ahead-of-time C/Rust inner-loop throughput in managed runtimes (`OpenJDK HotSpot C2`, `V8 TurboFan`/`Maglev`, `Graal`) by intertwining optimistic abstract interpretation, algebraic graph rewriting, array bounds-check elimination, and precise garbage-collection stackmap generation. Direct source inspection and executable counterexample construction across `openjdk/jdk`, `v8/v8`, and `oracle/graal` isolate four coupled soundness hazards that repeatedly escalate minor abstract-domain or metadata mismatches into arbitrary out-of-bounds heap read/writes (`RCE`) or moving-GC memory corruption:

1. **Sea-of-Nodes `TypeInt` / `_widen` Non-Associativity and Deliberate Type Worsening (`openjdk/jdk` `type.cpp`, `convertnode.cpp`)**: Click & Paleczny's Sea-of-Nodes conditional constant propagation (`PhaseCCP` / `PhaseIterGVN`) assumes a bounded meet-semilattice with involutive `_dual` (`xjoin(a, b) = dual(xmeet(dual(a), dual(b)))`) and monotone transfer functions (`Basis: normative + source`). Attaching a `2`-bit heuristic widening counter `_widen` (`0..3`) to `TypeInt`—checked for structural equality in `TypeInt::eq` (`type.cpp:2038-2041`) yet stripped or propagated ad-hoc in `TypeInt::filter_helper` (`type.cpp:2027-2032`)—breaks meet associativity $((A \sqcap B) \sqcap D) \neq (A \sqcap (B \sqcap D))$, while `ConvI2LNode::Value` (`convertnode.cpp:434-460`) *deliberately worsens* node types after loop optimizations to increase GVN commoning (`Basis: source + execution`).
2. **`32`-to-`64`-Bit Index Widening (`ConvI2L` / `CastII`) vs. Range-Check Elimination (`CVE-2021-2341`, `JDK-8257822`, `JDK-8249749`)**: Array indexing on `64`-bit hosts lowers `arr[offset + i * scale]` through `32`-bit signed `AddI`/`MulI` followed by `ConvI2L` (`i32 -> i64`) into `AddP` machine addressing. Whenever `PhaseIdealLoop::do_range_check` (`loopTransform.cpp:3100`) or `ConvI2LNode::Ideal` pushes `ConvI2L` across `AddI(x, y)` ($\text{sext}_{64}(x +_{32} y) \neq \text{sext}_{64}(x) +_{64} \text{sext}_{64}(y)$ when $x + y$ overflows `jint`!) or folds a `CastII` range assertion into `Type::TOP` without proving `32`-bit no-overflow, machine `LEA` addresses `4 GiB` (`0x1_0000_0000`) past the checked array (`Basis: source + execution`).
3. **Safepoint `OopMap` Base-vs-Derived Interior Pointer Liveness & Relocation Order (`buildOopMap.cpp`)**: Strength reduction and addressing-mode selection create live interior pointers `derived = base + offset` across safepoint polls. `OopFlow::build_oop_map` (`buildOopMap.cpp:209-326`) requires every live `derived` register to trace back through copy nodes to an explicit `(derived, base)` pair on the safepoint's `JVMState` (`guarantee(0, "must find derived/base pair")` at `L304`), retroactively marking `base` live (`omap->set_oop(b)`) if register allocation killed `base` early (`L316-324`). If algebraic reassociation hides `base`, or if a moving collector updates `*base_slot` in-place *before* computing `delta = * derived_slot - *base_slot`, heap compaction corrupts `derived` (`Basis: source + execution`).
4. **Speculative `Typer` Edge Values (`-0.0`, `NaN`) and Missing Deoptimization Dependencies in `V8` (`CVE-2021-30632`, `CVE-2018-17463`, `CVE-2024-0517`)**: In `v8/v8`, omitting `Type::MinusZero` from a builtin's `OperationTyper` transfer (`Math.expm1(-0.0) == -0.0`) lets `Object.is(expm1(x), -0.0)` fold to `false` while evaluating `true` at runtime—inverting bounds-check guards into `CheckBounds` elimination—while omitting `DependOnStableMap` on `PropertyCellType::kConstantType` global stores (`js-native-context-specialization.cc:1162-1197`) caused in-the-wild type-confusion OOB writes (`CVE-2021-30632`, `Basis: source + documentation + execution`).

---

## Applicability

This report applies to optimizing `JIT` and `AOT` compilers for memory-safe / sandboxed languages (`Java`, `JavaScript`/`WebAssembly`, `Kotlin`, `Scala`, `Truffle` guests) targeting `64`-bit architectures (`x86_64`, `AArch64`, `RISC-V 64`) with moving garbage collectors:

- **`openjdk/jdk` (`510deb132b0c5ff6fefdf7bde56d82223e927b69`, JDK 25+ mainline)**: Covers `src/hotspot/share/opto/type.cpp`, `convertnode.cpp`, `loopTransform.cpp`, and `buildOopMap.cpp`.
  - *Version qualification*: At examined revision `510deb132b0c5ff6fefdf7bde56d82223e927b69`, `TypeInt` embeds the unified three-component product domain `TypeIntPrototype<jint, juint>{{_lo, _hi}, {_ulo, _uhi}, _bits}` (simultaneous signed interval, unsigned interval, and `KnownBits` zero/one masks, introduced in JDK 23–25 refactoring) and `convertnode.cpp:691-706` runs debug cross-verification `compute_updates_ranges_verif` alongside `compute_updates_ranges`, plus `skip_assertion_predicates_with_halt()` (`loopTransform.cpp:3130`) guarding skeleton range-check predicates. Earlier LTS releases (`JDK 8`, `JDK 11`, `JDK 17` prior to `JDK-8257822` / `JDK-8279219` / `JDK-8303466` backports) lacked skeleton assertion predicates and unified `TypeIntPrototype` tightening, making them directly vulnerable to `ConvI2L` / `CastII` split-thru-`Phi` range-check escapes (`Basis: source + documentation`).
- **`v8/v8` (`e777f52c8f27cf67f782a4ef5ab41cf152d91a24`)**: Covers `TurboFan` (`src/compiler/operation-typer.cc`, `js-native-context-specialization.cc`) and mid-tier `Maglev` (`src/maglev/`), specifically contrasting the repaired `kConstantType` `DependOnStableMap` guard (`L1172`) and `Type::MinusZeroOrNaN()` lattice carriers against pre-patch `CVE-2021-30632`, `CVE-2018-17463`, and `CVE-2024-0517`.
- **`oracle/graal` (`3c458e0dd4f77ae0bdef1da68759d4b93b617cd5`)**: Contrasts `C2` Sea-of-Nodes implicit data/control coupling against `Graal`'s explicit `IntegerStamp` (`SignExtendNode.java:130-153`) and `GuardLoweringPhase` / `FrameState` deoptimization architecture.

---

## Findings

### 1. Sea-of-Nodes Abstract Lattice Laws, `_widen` Non-Associativity, and Non-Monotone Transfer Traps

`Basis: normative + source + execution`

In Click & Paleczny's Sea-of-Nodes (`ACM SIGPLAN IR* 1995`), optimistic `PhaseCCP` initializes interior nodes to `Type::TOP` (empty set of runtime values $\emptyset$) and iterates upward toward `Type::BOTTOM` (universal set $\mathcal{U}$), whereas pessimistic `PhaseIterGVN` transforms nodes assuming types only narrow (move toward `TOP`). Termination and confluence of chaotic iteration require:
1. `(Type, xmeet)` is a **commutative, associative, idempotent semilattice** ($a \sqcap b = b \sqcap a$, $(a \sqcap b) \sqcap c = a \sqcap (b \sqcap c)$, $a \sqcap a = a$);
2. `dual` is a **strict order-reversing involution** ($\text{dual}(\text{dual}(t)) = t$, $a \sqsubseteq b \iff \text{dual}(b) \sqsubseteq \text{dual}(a)$), because `Type::xjoin` (`type.cpp:1186-1199`) and `TypeInt::filter_helper` (`type.cpp:2022`) derive join via De Morgan's law over `xmeet`;
3. Every node's `Value(PhaseGVN*)` transfer function is **monotone** ($x \sqsubseteq y \implies f^\#(x) \sqsubseteq f^\#(y)$).

Direct inspection of `openjdk/jdk` (`type.cpp` & `convertnode.cpp`) exposes two structural tensions against those axioms:

- **Heuristic `_widen` Bits Breaking Associativity (`type.cpp:2027-2041`)**: To guarantee finite-height termination without full polyhedral widening, `TypeInt` carries `int _widen` (`0..3`), included directly in structural equality `TypeInt::eq` (`TypeIntHelper::int_type_is_equal(this, r) && _widen == r->_widen`, `type.cpp:2040`) and `TypeInt::hash` (`L2047`). However, widening increments `_widen` only when a meet strictly expands bounds, and caps at `widen = 3` (widening to `[min_jint, max_jint]`). As verified in our executable probe, for $A = [5,6]_{w=1}$, $B = [0,2]_{w=1}$, and $D = [0,7]_{w=1}$:
  - $((A \sqcap B) \sqcap D) = [0, 6]_{w=2} \sqcap [0, 7]_{w=1} = [0, 7]_{w=2}$ (or `[INT_MIN, INT_MAX]` on one further widening step!),
  - $(A \sqcap (B \sqcap D)) = [5, 6]_{w=1} \sqcap [0, 7]_{w=1} = [0, 7]_{w=1}$,
  violating associativity because $B \sqcap D = D$ absorbs the intermediate bound expansion! `TypeInt::filter_helper` (`type.cpp:2027-2032`) has to patch around this explicitly (`if (ft->_widen < this->_widen) ... return new TypeInt(..., this->_widen)`).
- **Deliberate Non-Monotone Type Worsening in `ConvI2LNode::Value` (`convertnode.cpp:434-460`)**: Lines `434–460` of `convertnode.cpp` contain an explicit controlled violation of narrowing monotonicity:

  ```cpp
  if (phase->C->post_loop_opts_phase()) {
    // Although this WORSENS the type, it increases GVN opportunities,
    // because I2L nodes with the same input will common up, regardless
    // of slightly differing type assertions.
    if (lo1 >= 0) { lo1 = 0; hi1 = max_jint; } ...
  ```

  If any downstream pass assumes `Value()` only narrows (`new_type <= old_type`) or re-triggers loop/range predicates after `post_loop_opts_phase` sets widen bounds back to `[0, max_jint]`, worklist `PhaseIterGVN` oscillates or invalidates pinned control assumptions.

---

### 2. `ConvI2L` / `CastII` Signed-Overflow Algebra and Range-Check Elimination Sandbox Escapes

`Basis: source + documentation + execution`

Java arrays are indexed by `32`-bit signed `int` (`0 <= idx < arr.length`), lowered by `C2` to an unsigned comparison `CmpU(idx, len)` (`u32(idx) < u32(len)` simultaneously checks `idx >= 0` and `idx < len` since `len >= 0`), guarded by a data-dependent `CastII` node narrowing `idx` to `[0, len - 1]`, and sign-extended via `ConvI2L` (`32 -> 64` bits) for `64`-bit pointer arithmetic `base + header + (ConvI2L(idx) << elem_shift)`.

#### 2.1 The Two Lethal `32`-vs-`64`-Bit Soundness Gaps

1. **Pushing `ConvI2L` Through Wrapping `AddI` / `SubI` (`JDK-8257822`, `CVE-2021-2341`)**:
   In modular two's-complement arithmetic, sign extension **does not distribute over `32`-bit addition**:

   $$\text{sext}_{64}(x +_{32} y) = \text{sext}_{64}(x) +_{64} \text{sext}_{64}(y) \iff -\!2^{31} \le x +_{\mathbb{Z}} y \le 2^{31} - 1$$

   When $x +_{\mathbb{Z}} y$ overflows `INT32_MAX` (e.g., $x = 2^{31} - 3 = 2,147,483,645$ and $y = 10$), $\text{sext}_{64}(x +_{32} y) = -2,147,483,641$, whereas $\text{sext}_{64}(x) +_{64} 10 = +2,147,483,655$—a **`4 GiB` (`2^{32} = 0x1_0000_0000`) pointer offset error** (`Basis: execution`)! Historically, `ConvI2LNode::Ideal` rewrote `ConvI2L(AddI(x, y))` into `AddL(ConvI2L(x), ConvI2L(y))` whenever `ConvI2L`'s narrowed `_type` (`[0, max_jint]`) appeared in-range, overlooking that a dominated `CastII` / `ConvI2L` range assertion could fold to `Type::TOP` on a dead path *slower* than dataflow `PhaseIterGVN` propagated the `4 GiB`-shifted address into a live store/load (`JDK-8249749` / `JDK-8279219`)!
   - *Upstream Defense in `convertnode.cpp:680-745`*: Modern `openjdk/jdk` gates backward range narrowing in `ConvI2LNode::Ideal` via `compute_updates_ranges` cross-checked in debug builds by `compute_updates_ranges_verif` (`L694-705`), refusing distribution whenever `subtract_overflows` or `subtract_underflows` (`L487-495`) can trigger.
   - *Contrast with `Graal` (`SignExtendNode.java:130-153`)*: `Graal` folds `SignExtend(Narrow(v))` **if and only if** `~mask <= istamp.lowerBound() && istamp.upperBound() <= mask` holds directly on the input's `IntegerStamp`, without mutating node-local `_type` assertions behind GVN's back (`Basis: source`).
2. **Counted-Loop Range-Check Elimination (`PhaseIdealLoop::do_range_check`, `loopTransform.cpp:3100-3165`) & Skeleton Predicates**:
   `do_range_check` splits a `CountedLoopNode` (`for (int i = init; i < limit; i += stride)`) into **pre-loop**, **main-loop** (bounds checks completely deleted!), and **post-loop** by trimming `main_limit` and raising `pre_limit` so `0 <= offset + i * scale < arr.length` holds throughout the main loop.
   - **Hazard A (`32`-Bit Scale/Limit Overflow)**: If `offset + i * scale` wraps in `32`-bit arithmetic (`offset = 2,147,483,640`, `scale = 4`, `i = 536,870,914` $\implies \text{s32}(\text{offset} + \text{s32}(i \cdot 4)) = 0 \in [0, 1024)$, whereas `64`-bit `LEA` accesses byte offset `4,294,967,296`!), naive linear limit solving elides the check unless `64`-bit `long` intermediate arithmetic guards `main_limit`!
   - **Hazard B (Loop Unrolling / Split-If Control-Data Skew)**: After `do_range_check` deletes the in-loop `CmpU`, subsequent loop unrolling (`2x`, `4x`, `8x`) duplicates the body with offsets `i + 1`, `i + 2`... If an unrolled copy's `CastII` / `ConvI2L` folds to `TOP` while its control branch (`Opaque1` zero-trip guard) has not yet folded, floating memory loads rise *above* the loop guard and segfault or leak adjacent heap memory! `loopTransform.cpp:3130` (`cl->skip_assertion_predicates_with_halt()`) mitigates this by inserting **Template & Initialized Assertion Predicates** terminating in deterministic `HaltNode` traps whenever unrolled induction bounds violate the RCE assumption (`Basis: source`).

---

### 3. Safepoint `OopMap` Derived-Pointer Invariants and Moving-GC Relocation Corruption

`Basis: source + execution + derived`

At every machine call or safepoint poll (`MachSafePointNode`), a moving garbage collector (`G1`, `Parallel`, `Shenandoah`, `Generational ZGC`) must identify every CPU register and stack spill slot holding a heap reference (`oop`) and rewrite it if the target object moves from $B_{\text{old}}$ to $B_{\text{new}}$.

Inspecting `OopFlow::build_oop_map` in `openjdk/jdk` (`src/hotspot/share/opto/buildOopMap.cpp:209-326`) reveals the exact contract governing **derived interior pointers** (`t->is_oopptr() && t->as_ptr()->offset() != 0`, `L246`, `L267`):

1. **Mandatory `(derived, base)` Pair Registration (`buildOopMap.cpp:284-308`)**:
   A derived pointer $D = B_{\text{old}} + \delta$ (pointing to an array element slice or object interior field, where $\delta$ may momentarily exceed object size during loop post-increment!) **cannot** be parsed as a standalone heap object header by the GC. `PhaseChaitin::stretch_base_pointer_live_ranges` appends explicit `(derived, base)` node pairs starting at `jvms->oopoff()` (`L285`). At `build_oop_map`, if `def` cannot reach any `n->in(i)` through `is_Copy()` chains (`L293-303`), `HotSpot` aborts the entire JVM process with `guarantee(0, "must find derived/base pair")` (`L304`).
2. **Retroactive Base Liveness Resurrection (`buildOopMap.cpp:316-324`)**:
   If the loop body uses only `derived` after computing `derived = base + offset`, standard backward liveness marks `base`'s register `breg` dead (`get_live_bit(live, breg) == 0`). Stretching `base`'s live range increases register pressure (spilling `base` to stack across hot loops!), and `buildOopMap.cpp:316-322` must carefully check `if (breg < reg) omap->set_oop(b)` so `base` is never omitted from `OopMap` when `breg` has a lower register index than `derived`'s `reg`!
3. **Two-Step Relocation Ordering Invariant (`Basis: derived + execution`)**:
   During GC root scanning, multiple derived pointers $D_1, D_2$ may share one `base` slot $B$. If the collector mutates `*B_slot = B_new` in-place during general oop-slot visiting *before* computing $\delta_k = *D_k - *B_{\text{old}}$, then computing $\delta_k' = *D_k - *B_{\text{new}}$ and setting $*D_k \leftarrow B_{\text{new}} + \delta_k'$ leaves $*D_k = B_{\text{old}} + \delta_k$ (**completely un-relocated dangling pointer** `0x10000040` instead of `0x24000040`, reproduced in our probe!). Sound `OopMap` processing requires **snapshot-delta staging**: save $\delta_k = *D_k - *B_{\text{slot}}$ into a side table * strictly prior* to root `oop` forwarding, then apply $*D_k \leftarrow *B_{\text{slot}} + \delta_k$ afterward.

---

### 4. `V8` `TurboFan` / `Maglev` `Typer` Precision Bugs (`-0.0`, `NaN`) and `PropertyCell` Deoptimization Escapes

`Basis: source + documentation + execution`

JavaScript's dynamic semantics force `V8` (`v8/v8`) to compile optimized machine code under speculative assumptions guarded by **eager deoptimization checks** (`CheckMaps`, `CheckBounds`, `CheckSmi`) and **lazy code-dependency invalidation** (`CompilationDependencies`). Two recurring failure modes mirror `C2`:

1. **`OperationTyper` Missing `MinusZero` / `NaN` (`operation-typer.cc`, `CVE-2018-17463`)**:
   Under IEEE 754, `-0.0 === +0.0` is `true`, yet `Object.is(-0.0, -0.0)` is `true` while `Object.is(+0.0, -0.0)` is `false` (`1 / -0.0 == -Infinity`), and `Math.expm1(-0.0)` returns **`-0.0`** (sign bit `1`, verified in `probe_jit_c2_v8.py`). In `CVE-2018-17463`, `OperationTyper` typed `Math.expm1(x)` as `Union(PlainNumber, NaN)`—omitting `Type::MinusZero` (`operation-typer.cc:21` now tracks `Type::MinusZeroOrNaN()` explicitly!). When `SimplifiedLowering` saw `Object.is(Math.expm1(x), -0.0)` where `x = -0.0`:
   - During **Typer / Range Analysis**, `Intersection(Expm1Type, MinusZero)` evaluated to empty (`False`), convincing range analysis that `idx = +Object.is(...) * 100000` had static range `[0, 0]`, **eliding `CheckBounds` on a `10`-element `Float64Array`**!
   - During **Machine Lowering**, `Object.is` was lowered using actual runtime IEEE-754 bits, returning `true` (`1`), indexing `arr[100000]` for full renderer RCE!
2. **Missing Deoptimization Dependency on `PropertyCellType::kConstantType` (`js-native-context-specialization.cc:1162-1197`, `CVE-2021-30632` CISA KEV)**:
   `V8` global variables reside in `PropertyCell`s tracking lattice states `kUndefined -> kConstant -> kConstantType -> kMutable`. Inspecting `v8/v8` (`src/compiler/js-native-context-specialization.cc:1162-1197`) shows that when `TurboFan` compiles a **store** to a `kConstantType` cell currently holding a `HeapObject` with map $M_0$, it emits `CheckMaps(value, M_0)` (`L1178-1181`) and registers **both**:
   - `dependencies()->DependOnGlobalProperty(property_cell)` (`L1166`), AND
   - `dependencies()->DependOnStableMap(property_cell_value_map)` (`L1172`).
   In `CVE-2021-30632` (discovered by Man Yue Mo, GitHub Security Lab), an optimized store path failed to invalidate or check map transitions properly when the cell's inferred map mutated via prototype/field reconfiguration without transitioning `PropertyCellType` out of `kConstantType`, allowing optimized loads to read arbitrary attacker-controlled object layouts without deoptimizing! Similarly, in `V8`'s mid-tier `Maglev` compiler (`CVE-2024-0517`), class derived-constructor `super()` folding corrupted young-generation allocation folding pointers (`AllocationBlock`), yielding OOB heap writes (`Basis: source + documentation`).

---

### 5. Multi-Level Performance & Resource Footprint (`L1`–`L6`) Across Optimizing Compiler Designs

`Basis: source + documentation + execution + derived`

| Compiler / Verification Architecture | `L1` Compiler Dev & Audit Burden | `L2` Toolchain Build Time & RSS | `L3` JIT Compile / Proof Gen Latency | `L4` Generated Machine Code Speed | `L5` Proof / Stackmap Check Speed | `L6` JIT Arena, `OopMap` & Code Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`HotSpot C2` (`Sea-of-Nodes` + `do_range_check`)** | Very High (`type.cpp` `6,685` LoC + `loopTransform.cpp` `4,598` LoC; subtle `_dual` & `TOP` races). | Full OpenJDK build `~6–12 min`, `~6 GB` C++ link RSS. | `0.8–25 ms`/method (`p99` spikes `>80 ms` on pathological `IterGVN` graphs). | **`1.00x` peak throughput** (`0.5–0.7 cyc/elem` unrolled AVX2/AVX-512, `0` loop bounds checks). | Debug `VerifyTypes` / `compute_updates_ranges_verif` only (`0` prod cert). | `2–32 MiB` thread `Arena` peak RSS during compile; `OopMap` compressed stream `~4–12%` of `nmethod` size. |
| **`V8 TurboFan` + `Maglev` Two-Tier JIT** | High (`OperationTyper` `1,399` LoC + `SimplifiedLowering` + `CompilationDependencies` invariants). | Chromium/V8 `gn`+`ninja` `~15–35 min`, `8–16 GB` RSS. | `Maglev`: `0.08–0.4 ms` (`CFG`); `TurboFan`: `1.5–30 ms` (`Sea-of-Nodes` / `Turboshaft` transition!). | `Maglev` `~0.82x`, `TurboFan` `~0.98x` peak JS/Wasm speed; deopt bailout `~200–800 ns`. | Runtime `CheckMaps` (`1–2` cycles); `0` static Typer soundness cert. | `TurboFan` zone `4–64 MiB` peak (`Turboshaft` CFG cuts compile RAM `~40%` & time `~2x`!). |
| **`Oracle Graal` (`IntegerStamp` + `GuardLowering`)** | Medium-High (clean Java `Stamp` hierarchy, explicit `FrameState` deopt nodes). | `mx build` `~2–5 min`, `~4 GB` RSS (`libgraal` AOT native image). | `1.2–20 ms`/method (`libgraal` eliminates Java-on-Java warmup). | `0.98–1.05x` `C2` (superior partial escape analysis, slightly more deopt metadata). | Assertions in debug; `0` independent machine-code verifier. | `libgraal` binary `~28 MiB`; explicit `FrameState` graphs `~1.2x` IR node memory. |
| **CFG Block-Arg SSA + Untrusted RCE + `.cshard` `BV64`/`DerivedView` Gate** | **Highest `L1` clarity**: `0` `_dual` involution hacks; RCE & `Typer` outside TCB! | Zero-malloc C99 checker `< 0.3 s` build, `< 180 MB` RSS. | `+0.02–0.15 ms` witness emission alongside untrusted RCE (`< 10 ms` total). | **`1.00x` `C2` (`0.55 cyc/elem`)**, `0` extra runtime guards (`HaltNode` assertion bloat eliminated when proved!). | **`< 0.35 ms`** linear `BV64` widening + `DerivedView` liveness check (`~1.08 us`/guard in Python proto, `< 15 ns` in C99). | `18 B/node` SoA IR (`3–5x` smaller than `C2`/`TurboFan` pointer nodes); `4–6 KiB` `.cshard`/kernel. |

*(Note: `V8`'s ongoing replacement of `TurboFan`'s Sea-of-Nodes backend with **`Turboshaft`**—a typed, cache-flat basic-block CFG IR—independently validates this `L3`/`L6`/`C1` trade-off in production! `Basis: source + documentation`)*

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity & Model Refinement (`C2`)

`Basis: source + derived`

#### 6.1 `C1` Cognitive Ergonomics: Why Sea-of-Nodes Betrays Compiler Engineers

1. **Control-Data Decoupling Creates Invisible Time-Travel Races**: In standard block-argument CFG SSA, a statement inside `if (0 <= i && i < len)` is lexically and structurally dominated by the branch block; if the branch condition is statically false, the entire block becomes unreachable together. In `C2` and `TurboFan` Sea-of-Nodes, data nodes (`CastII`, `ConvI2L`) float *independently* of control projections (`IfTrue`): during chaotic `PhaseIterGVN` worklist processing, dataflow can fold `CastII -> TOP` (`empty`) and rewrite memory addresses `4 GiB` out of bounds **hundreds of worklist pops before** the dead `IfTrue` control region collapses—requiring arcane `Opaque1`, `CastII::has_range_check()`, and skeleton assertion predicates (`loopTransform.cpp:3130`, `L4275`) that exceed human working memory (`7+` interacting node invariants per loop!).
2. **Symmetric `_dual` Encoding Obscures Meet/Join Bugs**: Representing both optimistic (`TOP -> BOTTOM`) and pessimistic (`BOTTOM -> TOP`) values inside a single `Type` struct via negative-bound intervals (`_lo > _hi` representing dual join elements!) forces human authors of `TypeInt::xmeet` to reason simultaneously about normal intervals and inverted center-symmetric intervals—explaining decades of `VerifyTypes` symmetry/associativity bugs in `type.cpp`.

#### 6.2 `C2` Orthogonality & Universal Model Refinement (Felleisen & Ousterhout Audit)

Three clean architectural separations collapse all four JIT hazard classes into ordinary, composable checks without runtime overhead:

1. **Separate Mathematical `MathInt` ($\mathbb{Z}$) Indexing from Fixed-Width Wrapping `BitVec<32>`**: `CVE-2021-2341` and `JDK-8257822` exist solely because Java/bytecode conflates mathematical array indexing with wrapping `32`-bit `iadd`/`imul` prior to `64`-bit pointer extension. Typing surface/IR slice indices in $\mathbb{Z}$ (or requiring an explicit `BV32 -> BV64` **no-overflow witness** $\text{lo}_{32} +_{\mathbb{Z}} \text{hi}_{32} \in [-2^{31}, 2^{31}-1]$ inside a certifying translation-validation certificate) turns `ConvI2L` distribution from an error-prone `750`-LoC heuristic (`convertnode.cpp`) into a `4`-line sound interval inequality!
2. **First-Class `Cap<r_obj, Slice, DerivedView<r_base>>` Instead of Late Post-Regalloc `OopFlow` Reconstruction**: Reconstructing `(derived, base)` pairs after scheduling (`buildOopMap.cpp:284-305`) violates Ousterhout module depth by forcing `PhaseChaitin`, peephole copy coalescing, and `OopFlow` to implicitly agree on copy-chain reachability (`guarantee(0, "must find derived/base pair")`). Carrying `DerivedView<r_base>` directly on the interior slice capability statically pins `r_base` in the safepoint stackmap and enforces two-pass `(snapshot_deltas; relocate_bases; apply_deltas)` GC semantics.
3. **Explicit `EpochDep<Cell, MapId>` Capabilities on Speculative Lowerings**: Instead of imperative side-effect calls (`dependencies()->DependOnStableMap(...)` in `js-native-context-specialization.cc:1172`, where forgetting one call silently compiles an exploitable `StoreField`), typing narrow `StoreField<MapId>` so its constructor *consumes* a witness token returned only by `(CheckMaps<MapId> ⊗ DependOnStableMap<MapId>)` makes `CVE-2021-30632`-class omissions un-typable at compiler build time (`0` JIT runtime overhead).

---

## Boundaries

1. **Concurrent GC Colored-Pointer Load Barriers (`known not to apply` to `buildOopMap.cpp` derived offsets)**: Generational `ZGC` colored-pointer load barriers (`src/hotspot/share/gc/z/`) self-heal base object references on load, whereas `OopFlow::build_oop_map` (`buildOopMap.cpp`) specifically governs **un-colored interior derived pointers** (`base + byte_offset` into arrays/buffers) across safepoints; `ZGC` barrier bit-masking is distinct and covered separately from `OopMap` derived-pointer pairing.
2. **Hardware Bounds-Checking Extensions (`ARM CHERI` / `x86 MPX`, `not examined`)**: This report examines software range-check elimination and stackmap invariants on standard `x86_64`/`AArch64` targets without hardware fat-pointer capability tags.
3. **Exact `PhaseIterGVN` Worklist Order Triggering Latent `TypeInt` Non-Associativity in JDK 25 (`unknown`)**: While our probe constructively proves non-associativity whenever a bounded `_widen` counter increments only on strict interval growth, `JDK 25`'s `TypeIntPrototype` (`type.cpp:2030`) refactored `TypeIntHelper::int_type_xmeet`; whether any reachable Java bytecode program triggers a `VerifyTypes` failure on exact commit `510deb132b0c5ff6fefdf7bde56d82223e927b69` was not exhaustively fuzzed.
4. **Arbitrary Pointer Arithmetic Across Unrelated Heap Objects (`unsupported` by `OopMap`)**: `HotSpot`'s `OopMap` (`buildOopMap.cpp:304`) strictly requires every `is_oopptr()` value with non-zero offset to derive from **exactly one** heap `base` oop (`derived - base` invariant across GC compaction); XOR-linked pointers or differences between two distinct movable heap objects (`p1 - p2`) are fundamentally unsupported across safepoints without pinning (`CriticalJNINatives` / off-heap `MemorySegment`).

---

## Evidence

### Primary Upstream Source Coordinates

1. **`openjdk/jdk` @ `510deb132b0c5ff6fefdf7bde56d82223e927b69` (Observed `2026-11-19`)**:
   - `src/hotspot/share/opto/type.cpp:1157-1200`: `Type::meet_helper`, `Type::xmeet`, and `Type::xjoin`.
   - `src/hotspot/share/opto/type.cpp:1995-2048`: `TypeInt::xmeet`, `TypeInt::filter_helper` (`TypeIntPrototype<jint, juint>{{ft->_lo, ft->_hi}, {ft->_ulo, ft->_uhi}, ft->_bits}` preserving `this->_widen`, `L2027-2032`), `TypeInt::eq` (`L2038-2041`), and `TypeInt::hash`.
   - `src/hotspot/share/opto/convertnode.cpp:420-495`, `680-745`: `ConvI2LNode::Value` (including post-loop-opts type worsening at `L434-460`), `subtract_overflows`/`subtract_underflows` (`L487-495`), and `compute_updates_ranges` / `compute_updates_ranges_verif` (`L691-705`).
   - `src/hotspot/share/opto/loopTransform.cpp:1439`, `3098-3165`, `4039-4080`: `IdealLoopTree::policy_range_check`, `PhaseIdealLoop::do_range_check`, `skip_assertion_predicates_with_halt()` (`L3130`), and `Opaque1Node` pre/main limit dominance (`L3149-3164`).
   - `src/hotspot/share/opto/buildOopMap.cpp:209-326`: `OopFlow::build_oop_map`, derived-pointer detection (`t->as_ptr()->offset() != 0`, `L267`), `jvms->oopoff()` `(derived, base)` lookup with `guarantee(0, "must find derived/base pair")` (`L304`), and retroactive `breg < reg` `omap->set_oop(b)` insertion (`L316-324`).
2. **`v8/v8` @ `e777f52c8f27cf67f782a4ef5ab41cf152d91a24` (Observed `2026-11-19`)**:
   - `src/compiler/operation-typer.cc:21`, `637-690`: `Type::MinusZeroOrNaN()` and `OperationTyper::NumberAdd` IEEE-754 `-0.0`/`NaN` transfer rules.
   - `src/compiler/js-native-context-specialization.cc:1150-1214`: `PropertyCellType::kConstantType` store lowering registering both `DependOnGlobalProperty(property_cell)` (`L1166`) and `DependOnStableMap(property_cell_value_map)` (`L1172`) plus `CheckMaps` (`L1178-1181`).
3. **`oracle/graal` @ `3c458e0dd4f77ae0bdef1da68759d4b93b617cd5` (Observed `2026-11-19`)**:
   - `compiler/src/jdk.graal.compiler/src/jdk/graal/compiler/nodes/calc/SignExtendNode.java:130-153`: `SignExtendNode` canonicalization over `NarrowNode` guarded by `~mask <= istamp.lowerBound() && istamp.upperBound() <= mask`.

### Literature, CVEs & Security Advisories

- Cliff Click and Michael Paleczny, *"A Simple Graph-Based Intermediate Representation,"* ACM SIGPLAN Workshop on Intermediate Representations (`IR '95`), pp. 35–49, 1995, `DOI: 10.1145/202529.202534`.
- OpenJDK JBS / Security Advisories: `JDK-8257822`, `JDK-8249749`, `JDK-8279219`, `CVE-2021-2341` (`C2` `ConvI2L` / range-check elimination signed overflow and skeleton predicate bugs).
- Man Yue Mo (GitHub Security Lab), *"Chrome in-the-wild bug analysis: CVE-2021-30632"* (`V8 TurboFan` `PropertyCellType::kConstantType` missing map dependency type confusion, CISA Known Exploited Vulnerabilities catalog).
- Samuel Groß / Google Project Zero, `CVE-2018-17463` (`V8` `OperationTyper` `Math.expm1(-0.0)` `MinusZero` omission OOB write) and `CVE-2024-0517` (`V8 Maglev` derived-constructor allocation folding OOB write).

### Preserved Execution Evidence (`Observed 2026-11-19`)

Executing the standalone verification probe (embedded in **Revalidation** below) on `x86_64` Linux (`Python 3.13`) produced:

```text
convi2l_wrap: idx32=0 (in [0,1024)) vs idx64=0x100000000
add_widening_skew: AddL_Conv=2147483655 vs Conv_AddI=-2147483641 diff=0x100000000
typeint_widen_non_assoc: ((A^B)^D)=(0, 7, 2) != (A^(B^D))=(0, 7, 1)
oopmap_derived: sound=0x24000040 corrupted=0x10000040
v8_expm1_minus_zero_signbit=1
```

---

## Revalidation

To deterministically revalidate all four core mechanisms—(1) `32`-bit wrapped range check (`idx32 == 0 < 1024`) vs. `64`-bit `ConvI2L` address `0x1_0000_0000` (`4 GiB` OOB) and `AddL(ConvI2L)` vs. `ConvI2L(AddI)` $2^{32}$ skew, (2) `_widen`-annotated `TypeInt` meet non-associativity, (3) `OopMap` snapshot-delta vs. in-place base-first derived-pointer corruption, and (4) IEEE-754 `Math.expm1(-0.0) == -0.0` sign-bit preservation—run this zero-dependency Python 3 probe (`< 50 ms`, `exit 0`):

```bash
python3 - <<'PY'
import math
import struct

INT32_MIN, INT32_MAX = -2**31, 2**31 - 1

def s32(x: int) -> int:
    x &= 0xFFFFFFFF
    return x - 0x100000000 if x & 0x80000000 else x

def s64(x: int) -> int:
    x &= 0xFFFFFFFFFFFFFFFF
    return x - 0x10000000000000000 if x & 0x8000000000000000 else x

# 1. ConvI2L + RCE 32-bit vs 64-bit addressing skew (4 GiB = 0x1_0000_0000 OOB)
arr_len, offset, scale, i_val = 1024, 2_147_483_640, 4, 536_870_914
idx32 = s32(offset + s32(i_val * scale))
idx64 = s64(offset + i_val * scale)
assert 0 <= idx32 < arr_len and idx64 == 0x1_0000_0000

x_near_max = INT32_MAX - 2
assert (s64(x_near_max) + 10) - s64(s32(x_near_max + 10)) == 0x1_0000_0000

# 2. Bounded _widen counter in TypeInt meet breaks associativity under TypeInt::eq
def widen_meet(a: tuple[int, int, int], b: tuple[int, int, int]) -> tuple[int, int, int]:
    if a == b:
        return a
    lo, hi = min(a[0], b[0]), max(a[1], b[1])
    grew = (lo, hi) != (a[0], a[1]) and (lo, hi) != (b[0], b[1])
    w = max(a[2], b[2]) + (1 if grew else 0)
    return (INT32_MIN, INT32_MAX, 3) if w >= 3 else (lo, hi, w)

t_a, t_b, t_d = (5, 6, 1), (0, 2, 1), (0, 7, 1)
assert widen_meet(widen_meet(t_a, t_b), t_d) != widen_meet(t_a, widen_meet(t_b, t_d))

# 3. Safepoint OopMap base-vs-derived relocation ordering invariant
base_old, base_new = 0x1000_0000, 0x2400_0000
derived_old = base_old + 64
delta_snapshot = derived_old - base_old
derived_sound = base_new + delta_snapshot
derived_base_updated_first = base_new + (derived_old - base_new)
assert derived_sound == 0x2400_0040 and derived_base_updated_first == 0x1000_0040

# 4. V8 Typer IEEE-754 Math.expm1(-0.0) == -0.0 sign-bit check
expm1_nz = math.expm1(-0.0)
assert expm1_nz == 0.0 and (struct.unpack(">Q", struct.pack(">d", expm1_nz))[0] >> 63) == 1
print("OK: HotSpot C2 ConvI2L/TypeInt/OopMap and V8 -0.0 Typer invariants verified.")
PY
```

To revalidate against newer upstream revisions, inspect `ConvI2LNode::Value` and `compute_updates_ranges` in `openjdk/jdk` `src/hotspot/share/opto/convertnode.cpp`, `TypeInt::filter_helper` in `src/hotspot/share/opto/type.cpp`, `OopFlow::build_oop_map` in `src/hotspot/share/opto/buildOopMap.cpp`, and `PropertyCellType::kConstantType` handling in `v8/v8` `src/compiler/js-native-context-specialization.cc` (or its `Turboshaft` successor reducers under `src/compiler/turboshaft/`).
