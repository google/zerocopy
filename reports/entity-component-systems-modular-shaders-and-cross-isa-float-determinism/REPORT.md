# Relational Entity-Component Systems, Modular Differentiable Shaders, and Cross-ISA Bit-Exact Floating-Point Determinism

## Summary

Modern high-throughput interactive simulations, differentiable GPU renderers, and lockstep/rollback networked games sit at the intersection of three severe language, memory-layout, and hardware-determinism cliffs:

1. **Relational Archetype ECS Memory vs. Structural Invalidation (`Bevy`, `Flecs`, `EnTT`):** Archetype Entity-Component Systems invert object-oriented pointer graphs into columnar Structure-of-Arrays (SoA) tables keyed by exact component sets, enabling hardware prefetching, SIMD iteration, and automatic lock-free parallel scheduling via propositional query-disjointness proofs (`bevy_ecs` checks pairwise clause refutation over Disjunctive Normal Form `FilteredAccess::filter_sets` in `crates/bevy_ecs/src/query/access.rs`, lines 769–828). However, adding or removing a component migrates the entity between archetype tables via **swap-and-pop** (`Table::swap_remove_unchecked`, `crates/bevy_ecs/src/storage/table/mod.rs`, lines 227–236), silently redirecting any cached raw pointer or `TableRow` index to a completely different entity (`E3` overwriting `E1`'s row in Probe 3B). `Flecs` mitigates relational table-count explosion on hierarchies via cached archetype-graph edges (`table_graph.c`) and `EcsDontFragment` / `non_fragmenting_childof.c`, whereas sparse-set engines (`EnTT`) avoid full-row component copies at the cost of sparse indirection. Across FFI boundaries, foreign physics or scripting runtimes lose both generational handle safety and scheduler read/write footprint visibility.
2. **Checked Modular GPU Shaders, Automatic Differentiation, and Host↔Device Layout Drift (`Slang` / `SLANG.D`):** `Slang` (`shader-slang/slang`, SIGGRAPH 2018) replaces C-preprocessor `#define` uber-shader permutation explosions with separately type-checked interfaces, generics, and witness-table existentials lowered via either zero-overhead static specialization or tagged dynamic dispatch (which trades PSO explosion for SIMT warp divergence and worst-case register-file occupancy). `SLANG.D` (SIGGRAPH Asia 2023) embeds forward-mode (`fwd_diff`) and reverse-mode (`bwd_diff`) automatic differentiation directly into Slang IR via `IDifferentiable` and `DifferentialPair<T>`, but reverse-mode loops on register-scarce GPUs require statically bounded `[MaxIters(N)]` checkpoint tapes (**exceeding `N` at runtime is explicitly undefined behavior** per `docs/user-guide/07-autodiff.md`, line 901), reverse gradient scattering via `atomicAdd(float)` is non-deterministic under floating-point non-associativity, and host↔GPU memory layouts diverge sharply across Rust/C `#[repr(C)]`, Vulkan `std140`, Vulkan `std430`/WGSL, and Slang's internal natural layout (`slang-ir-layout.cpp`, lines 36–47): a single 4-field struct `{ vec3<f32> pos; f32 mass; f32 weights[4]; mat3x3<f32> rot; }` measures `68` bytes (`rot@32`) in `#[repr(C)]`, `128` bytes (`rot@80`) in `std140`, and `80` bytes (`rot@32`) in `std430`/WGSL.
3. **Cross-ISA Bit-Exact Floating-Point Determinism (`x86_64`, `ARM64`, `WebAssembly`, `libm`, `CORE-MATH`):** Lockstep and rollback simulations (`GGRS`, `Rapier` `enhanced-determinism`) desynchronize catastrophically on a single 1-ULP difference. Live `x86_64` Linux hardware execution (`GCC 15.2.0`) directly demonstrates four distinct divergence mechanisms:
   - **Implicit FMA contraction:** `a * b + c` for `a = 1 + 2⁻²⁷`, `b = 1 - 2⁻²⁷`, `c = -1.0` produces `-5.55111512312578270e-17` (`0xbc90000000000000`) under `-mfma -ffp-contract=fast` vs. `0.0` (`0x0000000000000000`) under `-mno-fma -ffp-contract=off` (and WebAssembly `relaxed-simd` `f32x4.relaxed_madd` codifies this as hardware-dependent nondeterminism).
   - **NaN sign/payload & `min`/`max` divergence:** `x86_64` produces negative quiet NaN `0xffc00000` for `0.0f / 0.0f` (vs. `0x7fc00000` on `ARM64` Default-NaN, `RISC-V`, and WebAssembly's deterministic profile); even on the *same* `x86_64` CPU, `qNaN1 (0x7fc01234) + qNaN2 (0x7fc05678)` flips between `0x7fc01234` (`-mno-fma` SSE `addss`) and `0x7fc05678` (`-mfma` AVX `vaddss`); and SSE `minss` is strictly non-commutative, returning its second operand on both `±0.0` ties and NaNs.
   - **SIMD reduction-tree non-associativity:** Summing the exact same 16 `f32` values produces `4.65999985` (`0x40951eb8`) scalar, `5.15999985` (`0x40a51eb8`) 4-wide, and `4.00000000` (`0x40800000`) 8-wide.
   - **Transcendental `libm` ULP drift:** System `libm` libraries (`glibc`, `UCRT`, `libSystem`, `musl`) disagree on `sin`/`cos`/`atan2`/`pow` LSBs; `Rapier`'s `enhanced-determinism` forces pure-software `rust-lang/libm` (`simba/libm_force`), while `CORE-MATH` (IEEE ARITH 2022) achieves exact **correctly rounded ($\le 0.5\text{ ULP}$)** bit-identical elementary functions across ISAs.

## Applicability

This report connects primary-source inspection across ECS runtimes, GPU shader compilers, WebAssembly specifications, and live `x86_64` floating-point execution probes:

- **ECS memory, mutation, and parallel scheduling:** Directly verified against `bevyengine/bevy` (`779770720e6ad916c1de38cf66a67d0e079ed1e3`, `crates/bevy_ecs/src/{storage/table/mod.rs,query/access.rs,world/unsafe_world_cell.rs,world/command_queue.rs}`), `SanderMertens/flecs` (`cf0e60d0d0e4be4728c4a4e7fda664c0d1f4b96b`, `src/storage/{table.c,table_graph.c,non_fragmenting_childof.c}`, `src/query/compiler/compiler.c`), and `skypjack/entt` (`1dcd7aab6548786f7672ff578639188bd2f0d837`, `src/entt/entity/sparse_set.hpp`). Note that `bevy_ecs` query conflict checking evolved to full DNF `FilteredAccess` clauses at the examined revision; older commentary assuming single-conjunction bitset filters does not apply to modern Bevy.
- **Modular shaders, autodiff, and host↔GPU layout:** Directly verified against `shader-slang/slang` (`a22c14207d52406edeaa82199df26db209625705`, `docs/design/existential-types.md`, `docs/user-guide/07-autodiff.md`, `source/slang/slang-ir-{layout,autodiff,autodiff-fwd,autodiff-rev,specialize}.cpp`), `shader-slang/slangpy` (`8dd7384b3114b48c04047fb01e3bb11cda8d263f`), He, Fatahalian, and Foley (SIGGRAPH 2018, DOI `10.1145/3214756.3214798`), and Bangaru et al. (SIGGRAPH Asia 2023, DOI `10.1145/3618353`). Layout rules for `std140`, `std430`, and `WGSL` are compared against C/Rust `#[repr(C)]` under standard 32-bit float scalar rules without `VK_EXT_scalar_block_layout`.
- **Cross-ISA floating-point determinism:** Directly verified against `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`, `document/core/exec/numerics.rst`), `WebAssembly/relaxed-simd` (`c3f9359af2cd607cc46b0a3274f90ea52543a2f2`, `proposals/relaxed-simd/Overview.md`), `bytecodealliance/wasmtime` (`3ce2209872ccf1ea115914a81e020aef66a10c51`, `crates/wasmtime/src/config.rs`), `dimforge/rapier` (`475caa3ff4646fd9a796b67d14116256f4962bc7`, `crates/rapier3d/Cargo.toml`), `rust-lang/libm` (`8f7436d260f000f054042545bb6e4c0d99fe35b2`), `gschup/ggrs` (`25bd9983dee3ecb0677be03b9e2e23d2bd6d29cb`), Sibidanov, Zimmermann, and Glondu (IEEE ARITH 2022, DOI `10.1109/ARITH54963.2022.00014`), and live `x86_64` execution (`GCC 15.2.0`). Hardware probe results were executed on `x86_64` Linux; ARM64 and RISC-V behaviors are cited from normative ISA/Wasm specifications rather than executed natively on ARM64/RISC-V silicon in this run.

## Findings

### 1. Relational Archetype ECS Storage, Swap-Remove Invalidation, and Parallel Borrow Scheduling

Basis: source + execution + derived

#### 1.1 Archetype Columnar Tables vs. Structural Mutation (`Bevy`, `Flecs`, `EnTT`)

Archetype ECS engines replace heap-fragmented polymorphic objects with an in-memory **columnar relational store**: every distinct component signature (archetype, e.g., `{Position, Velocity, Health}`) owns a dense table of parallel type-erased columns (`Table` in `bevyengine/bevy`, `crates/bevy_ecs/src/storage/table/mod.rs`, line 203; `ecs_table_t` in `SanderMertens/flecs`, `src/storage/table.c`). Entities are addressed logically via generational IDs mapped through an entity-location indirection table to `(TableId, TableRow)` (`TableId(u32)` at line 36, `TableRow(NonMaxU32)` at line 103 of `table/mod.rs`).

The fundamental structural cost of columnar archetype density is **archetype-migration pointer and row invalidation**:
- **Swap-and-Pop Row Reassignment (`table/mod.rs`, lines 227–236 & 804):** When an entity adds or removes a component, it must move from source `Table A` to destination `Table B`. To keep `Table A`'s columns densely contiguous in $O(1)$ per column, `Table::swap_remove_unchecked(&mut self, row: TableRow) -> Option<Entity>` moves the *last* entity in `Table A` (`last_element_index = self.entity_count() - 1`) into the vacated slot `row` across every column (`src_column.swap_remove_unchecked::<DROP>(last_index, row)`, line 804) and returns the moved `Entity` so the world can patch its `EntityLocation`.
- **Silent Cross-Entity Aliasing Across FFI (Probe 3B):** If a foreign C++ physics engine (`PhysX`, `Jolt`, `Bullet`), audio thread, or scripting callback caches a raw pointer `&positions[row]` or table row index `1` for `E1`, migrating `E1` swaps `E3` into `row = 1`—so the cached pointer silently mutates or reads **`E3`'s position (`30.0`) instead of `E1`'s (`10.0`)** without even crashing on an invalid address!
- **Deferred Structural Mutation Barriers (`command_queue.rs` / Flecs staging):** Because mutating archetypes mid-iteration would invalidate active column slices, ECS systems defer structural edits (`spawn`, `insert`, `remove`, `despawn`) into thread-local `CommandQueue` buffers flushed at exclusive `&mut World` synchronization barriers—creating intra-stage visibility lag and parallel barrier stalls.
- **Archetype Fragmentation & `Flecs` Non-Fragmenting Relationships (`table_graph.c` & `non_fragmenting_childof.c`):** Naive archetype tables explode combinatorially when entities carry dynamic relational pairs like `(ChildOf, parent_i)` (creating a distinct table per unique parent!). `Flecs` solves this along two axes verified in source:
  1. Cached archetype-transition graph edges (`ecs_graph_edge_t`, `flecs_table_traverse_add` / `flecs_table_traverse_remove`, `src/storage/table_graph.c`, lines 908–1085) turn repeated add/remove transitions into $O(1)$ graph hops.
  2. **`EcsDontFragment` & Non-Fragmenting `ChildOf` (`table_graph.c`, lines 942 & 1032; `src/storage/non_fragmenting_childof.c`, lines 8–70):** Relations marked `DontFragment` (including hierarchical `ChildOf` children tracked in `flecs_ordered_entities_append` / `EcsIdOrderedChildren`) store parent-child links out-of-band in per-pair records rather than splitting archetype tables, preventing table-count explosion on deep scene graphs.
- **Contrasting Sparse-Set Design (`skypjack/entt`, `src/entt/entity/sparse_set.hpp`):** `EnTT` stores each component type in its own independent sparse-set pool (`sparse` page array mapping `entity → dense_index` + dense packed component array). Adding a single component never copies untouched components of the same entity—eliminating archetype migration copies—at the cost of an extra sparse indirection per component on multi-component joins unless explicit contiguous `group` ownership is declared.

| Architectural Property | `Bevy` (`bevy_ecs`) | `Flecs` (`SanderMertens/flecs`) | `EnTT` (`skypjack/entt`) |
|---|---|---|---|
| **Primary Storage Model** | Columnar Archetype Tables (+ optional SparseSet components) | Columnar Archetype Tables + cached `ecs_graph_edge_t` + `EcsDontFragment` | Per-Component Sparse Sets (+ owning/non-owning `group`s) |
| **Single-Component Add/Remove Cost** | Copies *all* entity components to target archetype; `swap_remove` in source | Same for fragmenting components; $O(1)$ out-of-band update for `EcsDontFragment` | $O(1)$ append/swap-pop in that component's pool only |
| **Multi-Component Query Locality** | Peak (contiguous SoA slices per archetype) | Peak for fragmenting tables; indexed lookup for non-fragmenting relations | Dense only on primary pool (or owning `group`); sparse hops on others |
| **First-Class Entity Relationships** | Relationship components (`ChildOf` / custom hooks) | Native `(Rel, Target)` pairs, transitive/acyclic traits, query compiler (`compiler.c`) | Manual entity-ID components / external indices |
| **Borrow / Aliasing Safety Mechanism** | `UnsafeWorldCell<'w>` + runtime DNF `FilteredAccess` check | Single-threaded stage deferral + explicit pipeline read/write declarations | Caller-managed C++ discipline |

#### 1.2 Propositional DNF Query Disjointness Checking and `UnsafeWorldCell` Soundness

Direct inspection of `bevyengine/bevy` (`779770720e6ad916c1de38cf66a67d0e079ed1e3`) clarifies both the exact power and the exact boundaries of Bevy's parallel borrow checker:

- **DNF Propositional Disjointness (`crates/bevy_ecs/src/query/access.rs`, lines 769–828):**
  `FilteredAccess` stores a raw component `Access` bitset plus `filter_sets: Vec<AccessFilters>`, where each `AccessFilters` holds a conjunction `(with, without)` and the vector represents a **Disjunctive Normal Form (OR of ANDs)** formula. Two queries with overlapping component reads/writes are proven disjoint—and therefore schedulable concurrently without locks—iff every DNF clause of `self` is ruled out by every DNF clause of `other`:
  ```rust
  self.filter_sets.iter().all(|filter| {
      other.filter_sets.iter().all(|other_filter| filter.is_ruled_out_by(other_filter))
  })
  ```
  As explicitly documented in `access.rs` (lines 779–780) and confirmed in Probe 3C:
  - `Query<&mut C, Or<(With<A>, Without<B>)>>` **is compatible** with `Query<&mut C, (With<B>, Without<A>)>` (`True`), because `(With A)` is ruled out by `(Without A)` and `(Without B)` is ruled out by `(With B)`.
  - `Query<&mut C, Or<(Without<A>, Without<B>)>>` is **incompatible** with `Query<&mut C, Or<(With<A>, With<B>)>>` (`False`), because an entity carrying `{A}` without `{B}` matches both queries simultaneously!
  - **Complexity & Runtime Cliffs:** Conjoining filters via `FilteredAccess::extend` (lines 804–828) computes the Cartesian product `self.filter_sets.len() * other.filter_sets.len()` (exponential $O(2^k)$ blowup under nested `Or<...>` queries). Moreover, conflict validation occurs **at runtime during schedule/system initialization**, not at Rust compile time, and unordered write-write systems lacking explicit `.before()`/`.after()` edges introduce **schedule-order nondeterminism** that breaks deterministic replay and rollback netcode.
- **Aliasing Provenance Boundary (`crates/bevy_ecs/src/world/unsafe_world_cell.rs`, lines 30–94):** `UnsafeWorldCell<'w>` explicitly transfers Rust's unique-XOR-shared (`&mut` vs. `&`) aliasing proof burden from the borrow checker to runtime `FilteredAccess` disjointness plus unsafe internal table indexing. When an ECS scheduler invokes a foreign scripting system (Lua, Python, C#, Wasm), the scheduler cannot verify the foreign module's true component access footprint: either the foreign plugin serializes under exclusive `&mut World` (killing parallelism) or an inaccurate metadata manifest produces an unchecked multi-threaded data race.

### 2. Modular GPU Shaders (`Slang`), Automatic Differentiation (`SLANG.D`), and Host↔Device Memory Layout

Basis: normative + documentation + source + execution

#### 2.1 Checked Interfaces, Generics, Static Specialization, and Existential Dispatch (`Slang`, SIGGRAPH 2018)

Traditional GPU shading languages (`GLSL`, `HLSL`, `MSL`, `WGSL`) lacked checked interfaces and separate compilation, forcing engines into C-preprocessor `#define` uber-shaders with $2^N$ combinatorial variant explosions, un-typechecked dead `#ifdef` branches, and runtime Pipeline State Object (PSO) compilation stutters.

`Slang` (Yong He, Kayvon Fatahalian, and Tim Foley, *ACM TOG* 37(4), SIGGRAPH 2018, DOI `10.1145/3214756.3214798`; `shader-slang/slang`, `a22c14207d52406edeaa82199df26db209625705`) solves uber-shader bitrot through **checked interfaces**, **associated types**, **separate module compilation to Slang IR**, and two orthogonal lowering strategies documented in `docs/design/existential-types.md` (lines 7–82) and implemented in `source/slang/slang-ir-specialize.cpp`:

1. **Universal Generic Constraints (`T : IImage`) → Compile-Time Specialization (Monomorphization):** Functions like `float4 offsetImage<T : IImage>(T image, float2 uv)` are type-checked **once** against the `IImage` interface contract, compiled to portable Slang IR, and specialized per concrete material/light combination when emitting SPIR-V, DXIL, Metal, CUDA/PTX, or WGSL—yielding zero dynamic dispatch overhead at the cost of distinct specialized GPU binaries per concrete instantiation.
2. **Existential Interface Types (`IImage` used directly as a value type) → Tagged Witness-Table Dispatch:** Using an interface as a runtime value bundles `{TypeTag, WitnessTable, Payload}` (`docs/design/existential-types.md`, lines 49–79) and lowers interface calls to tagged `switch` dispatch on GPU targets lacking cheap indirect function pointers.
   - **Silicon Physics Trade-Off:** Existential dispatch eliminates PSO combinatorial explosion, *but* on SIMT GPUs (where hardware register files are statically partitioned across active warps/wavefronts), divergent lanes hitting different material tags serialize within a warp, and the compiler must statically reserve the **maximum register footprint across all possible concrete implementations**, severely lowering GPU warp occupancy. Furthermore, composing interface implementations that each bind textures/buffers via hierarchical `ParameterBlock<T>` must fit under strict hardware descriptor-set caps (e.g., Vulkan `maxBoundDescriptorSets`, frequently 4 on mobile GPUs).

#### 2.2 First-Class Differentiable Shaders (`SLANG.D`, SIGGRAPH Asia 2023)

`SLANG.D` (Bangaru et al., *ACM TOG* 42(6), Art. 262, SIGGRAPH Asia 2023, DOI `10.1145/3618353`; `shader-slang/slang`, `docs/user-guide/07-autodiff.md`, `source/slang/slang-ir-autodiff{,-fwd,-rev}.cpp`) embeds forward-mode (`fwd_diff`, Jacobian-vector product) and reverse-mode (`bwd_diff`, vector-Jacobian product) automatic differentiation directly into Slang's typed IR across generics, checked interfaces (`IDifferentiable`, `IDifferentiablePtrType`, `07-autodiff.md`, lines 960–962), branches, and loops, bridged to Python/PyTorch via `shader-slang/slangpy` (`8dd7384b3114b48c04047fb01e3bb11cda8d263f`).

Direct inspection of `docs/user-guide/07-autodiff.md` (lines 88–139, 383, 901) exposes three critical GPU autodiff constraints and soundness cliffs:
1. **Bounded Loop Checkpointing & Explicit Undefined Behavior (`07-autodiff.md`, line 901):** Reverse-mode AD requires forward primal intermediates to compute adjoints backward. On register-scarce GPUs, dynamic heap taping is infeasible; Slang therefore requires loops to have statically inferable iteration bounds or an explicit `[MaxIters(N)]` attribute (or `[ForceUnroll]`) to allocate fixed per-thread checkpoint storage. Line 901 states verbatim: *"If the actual number of iterations exceeds the provided maximum, the behavior is undefined."* Balancing register spills vs. recomputation follows Griewank's space–time checkpointing frontier (`[PreferRecompute]` vs. `[PreferCheckpoint]`).
2. **Non-Deterministic `atomicAdd(float)` Gradient Scatter:** When millions of backward rays or splats accumulate gradients concurrently into shared vertex/texel buffers via hardware float `InterlockedAdd`/`atomicAdd`, IEEE-754 addition non-associativity plus nondeterministic GPU warp scheduling produces **bit-divergent gradients on every backward pass**, complicating reproducible ML training and differential testing.
3. **Discontinuous Visibility Boundaries & Unverified Custom Derivatives:** Differentiating syntactically through hard visibility tests (`if (ray_hits_triangle)`) yields zero boundary gradients (missing Dirac-delta edge integrals), requiring manual reparameterization or `[BackwardDerivative]` overrides—whose algebraic equivalence to primal/forward-mode derivatives is **not** statically proved by the shader compiler.

#### 2.3 Host↔Device Memory Layout Divergence (`#[repr(C)]` vs. `std140` vs. `std430`/`WGSL` vs. Slang Natural Layout)

Basis: normative + source + execution

Passing structured buffers across the CPU↔GPU boundary breaks silently because CPU C/Rust ABIs and GPU shader layout standards obey mutually incompatible alignment, stride, and tail-padding rules—and even inside `shader-slang/slang` itself (`source/slang/slang-ir-layout.cpp`, lines 36–47), Slang explicitly notes three divergences between its internal VK/D3D "natural" IR layout and typical C/C++ compilers: (i) `bool` is laid out as `4` bytes (equivalent to `int`, whereas WGSL forbids `bool` in host-shareable buffers altogether!), (ii) composite sizes are *not* rounded up to alignment (allowing subsequent fields into tail padding—valid in VK/D3D, incompatible with C/C++!), and (iii) IR matrices default to row-major order.

**Empirical Offset Drift Probe (Evidence §3.2, Probe 3A):** Computing exact byte offsets for the concrete struct `{ vec3<f32> pos; f32 mass; f32 weights[4]; mat3x3<f32> rot; }`:

| Layout Standard | `pos` (`vec3<f32>`) | `mass` (`f32`) | `weights[4]` Offset & Element Stride | `rot` (`mat3x3<f32>`) Offset & Size | Total Struct Size | Silent Failure Mode vs. Rust `#[repr(C)]` |
|---|---|---|---|---|---|---|
| **Rust / C `#[repr(C)]`** (`[f32; 3]`, `[[f32; 3]; 3]`) | `@0` (align 4, 12 B) | `@12` (4 B) | `@16` (stride **4 B**, 16 B) | `@32` (36 B) | **68 B** | Baseline CPU representation |
| **Vulkan / OpenGL `std140` (Uniform Buffer)** | `@0` (align 16, 12 B) | `@12` (4 B) | `@16` (stride **16 B**, 64 B!) | **`@80`** (3×`vec4` = 48 B) | **128 B** | `weights[1..3]` and entire `rot` matrix read garbage! |
| **Vulkan `std430` / WGSL Storage Buffer** | `@0` (align 16, 12 B) | `@12` (4 B) | `@16` (stride **4 B**, 16 B) | `@32` (3×`vec4` = **48 B**) | **80 B** | `rot` columns 1–2 misaligned by 4–8 B; array-of-struct stride off by 12 B! |

In addition, bindless GPU pointer APIs (`VK_KHR_buffer_device_address` / Metal 3 argument buffers) pass raw 64-bit device addresses across asynchronous PCIe command queues, bypassing both Rust's borrow checker and static descriptor validation so freeing a CPU-managed buffer prior to Vulkan timeline-semaphore completion triggers asynchronous GPU page faults (TDR hangs).

### 3. Cross-ISA Bit-Exact Floating-Point Determinism (`x86_64`, `ARM64`, `RISC-V`, `WebAssembly`)

Basis: normative + source + execution

Rollback netcode engines (such as `gschup/ggrs`, `25bd9983dee3ecb0677be03b9e2e23d2bd6d29cb`) and deterministic lockstep physics engines (`dimforge/rapier`, `475caa3ff4646fd9a796b67d14116256f4962bc7`) transmit only compact player inputs across the network and rely on every heterogeneous client (`x86_64`, `ARM64`, browser `WebAssembly`) producing **bit-identical** simulation states every frame. Four independent hardware/compiler divergence layers destroy bit-exact determinism silently:

#### 3.1 Implicit FMA Contraction and WebAssembly `relaxed-simd` Nondeterminism

When a hardware FMA unit executes `vfmadd213sd` (`x86_64` FMA3) or `fmadd` (`ARM64`), it evaluates $\text{rn}(a \cdot b + c)$ with a **single rounding**, whereas unfused multiplication followed by addition evaluates $\text{rn}(\text{rn}(a \cdot b) + c)$ with **double rounding**. GCC defaults to `-ffp-contract=fast` (permitting contraction across statements/expressions based on optimization heuristics), and `WebAssembly/relaxed-simd` (`c3f9359af2cd607cc46b0a3274f90ea52543a2f2`, `proposals/relaxed-simd/Overview.md`, lines 40–58, 170, 326) explicitly defines `f32x4.relaxed_madd` (`0x105` / `0xaf`) as **nondeterministic**: implementations may return *either* the single-rounded fused or double-rounded unfused result depending on host CPU hardware—and even two calls in the same module are not guaranteed to agree in general!

**Measured Hardware Probe (Evidence §3.1, `GCC 15.2.0`, `x86_64` Linux):**
Evaluating `a * b + c` on `volatile double` inputs `a = 1.0 + 2⁻²⁷`, `b = 1.0 - 2⁻²⁷`, `c = -1.0` (where exact $a \cdot b = 1 - 2^{-54}$ rounds to `1.0` in binary64):
- `gcc -O2 -mfma -ffp-contract=fast`: **`-5.55111512312578270e-17`** (`0xbc90000000000000`, exact $-2^{-54}$ via single-rounded `vfmadd`)
- `gcc -O2 -mno-fma -ffp-contract=off`: **`0.00000000000000000e+00`** (`0x0000000000000000`, total cancellation via double rounding)

#### 3.2 NaN Sign/Payload Nondeterminism, `min`/`max` ISA Mismatches, and Wasm Canonicalization

IEEE 754-2008/2019 leaves quiet-NaN sign bits and payload bits partially unspecified. Inspecting `WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`, `document/core/exec/numerics.rst`, lines 1044–1063), `WebAssembly/relaxed-simd` (`Overview.md`, lines 214–234), `bytecodealliance/wasmtime` (`3ce2209872ccf1ea115914a81e020aef66a10c51`, `crates/wasmtime/src/config.rs`, lines 1747–1750, 3680, 5327–5334), and executing the inline `x86_64` probe (Evidence §3.1) yields the exact cross-ISA divergence matrix:

| Operation / Edge Case | `x86_64` (SSE / AVX) | `ARM64` (`FPCR.DN=0` vs. `DN=1`) | `RISC-V` (`F`/`D`) | WebAssembly Core Spec (Default vs. Deterministic Profile) |
|---|---|---|---|---|
| **Fresh NaN (`0.0f / 0.0f`)** | **`0xffc00000`** (negative qNaN; measured!) | `0x7fc00000` (positive qNaN) | `0x7fc00000` (canonical +qNaN) | Default: `±NaN(canon)`; Deterministic (`\PROFDET`): **`+NaN(canon)` (`0x7fc00000`)** |
| **Two-NaN Add (`qNaN₁ + qNaN₂`)** | Hardware returns 1st operand, **but `-mfma` AVX register swap flipped result to `qNaN₂` (`0x7fc05678`) vs. `-mno-fma` (`0x7fc01234`)!** | `DN=0`: propagates 1st NaN; `DN=1`: canonical `0x7fc00000` | Always canonical `0x7fc00000` | Default: any arithmetic NaN (MSB=1); Deterministic: **`+NaN(canon)`** (`wasmtime` `cranelift_nan_canonicalization(true)`) |
| **`min(±0.0)` & `min(NaN, 1.0)`** | SSE `minss` returns **2nd operand** (`minss(+0,-0)=-0`, `minss(-0,+0)=+0`, `minss(qNaN,1)=1`, `minss(1,qNaN)=qNaN`; measured!) | `fminnm` suppresses NaN (IEEE 2008 `minNum`); `fmin` propagates NaN (`-0 < +0`) | `fmin.s` = IEEE 2008 `minNum` (suppresses NaN); `fminm.s` (Zfa) propagates NaN | Core `f32.min`: propagates NaN, `-0 < +0`; `relaxed-simd` `f32x4.min`: **implementation-defined** |
| **Subnormals (FTZ/DAZ)** | Strict IEEE by default; mutable `MXCSR` bits 15/6 | Strict IEEE by default; mutable `FPCR.FZ` (bit 24) | Strict IEEE (no hardware FTZ mode in base F/D) | Strict IEEE gradual underflow mandated |

**Critical Empirical Discovery (Evidence §3.1):** Even on the **exact same `x86_64` CPU**, adding `qNaN1 (0x7fc01234) + qNaN2 (0x7fc05678)` produced **`0x7fc01234`** under `gcc -O2 -mno-fma` (legacy SSE `addss`) yet flipped to **`0x7fc05678`** under `gcc -O2 -mfma` (AVX `vaddss` operand reordering during register allocation)! Any rollback engine hashing raw float memory (`to_bits()`) without canonicalizing NaNs (or proving NaN-freedom statically) can desynchronize not just across x86 vs. ARM64, but across compiler flags on identical silicon. Enabling `wasmtime`'s `Config::cranelift_nan_canonicalization(true)` (`enable_nan_canonicalization`) emits explicit post-op canonicalization sequences at a runtime throughput penalty unless static finite-float analysis proves an expression cannot produce NaN.

#### 3.3 SIMD Reduction-Tree Non-Associativity

Because IEEE-754 floating-point addition is non-associative ($(a + b) + c \neq a + (b + c)$), auto-vectorizing a summation loop across different target SIMD widths (scalar 1-wide vs. 4-wide SSE/NEON/Wasm-v128 vs. 8-wide AVX2 vs. 16-wide AVX-512) or parallel ECS reductions changes the parenthesization tree silently.

**Measured Hardware Probe (Evidence §3.1):** Summing the exact same 16 `f32` elements `{1e7, 0.3, 0.7, 0.1, -1e7, 0.2, 0.9, 0.4, 1e7, 0.6, 0.8, 0.5, -1e7, 0.11, 0.22, 0.33}` (exact real sum = `5.16`):
- **1-wide scalar left-fold:** `4.65999985` (`0x40951eb8`)
- **4-wide SSE/NEON lanes:** `5.15999985` (`0x40a51eb8`)
- **8-wide AVX2 lanes:** `4.00000000` (`0x40800000`) — over **`1.16`** error purely from SIMD lane width!

Cross-ISA determinism mathematically requires fixing a canonical reduction topology (independent of host SIMD register width), using reproducible summation algorithms (Demmel–Nguyen `ReproBLAS` / Kulisch exact accumulators), or computing in deterministic fixed-point integer arithmetic.

#### 3.4 Transcendental `libm` ULP Drift vs. `Rapier` Software `libm` and `CORE-MATH`

IEEE 754-2019 mandates correct rounding ($\le 0.5\text{ ULP}$) only for `+`, `-`, `*`, `/`, `sqrt`, and `fma`; elementary transcendentals (`sin`, `cos`, `tan`, `atan2`, `exp`, `log`, `pow`) are merely *recommended* because of the **Table-Maker's Dilemma**. Platform math libraries (`glibc`—which even dispatches AVX2/FMA vs. scalar implementations differently across Linux CPUs—`musl`, Windows `UCRT`, Apple `libSystem`, Android `Bionic`, JS `Math.sin`, GPU SFUs) return divergent bit patterns across OSes and microarchitectures.

- **Software Single-Implementation Pinning (`dimforge/rapier`, `475caa3ff4646fd9a796b67d14116256f4962bc7`):** Inspecting `crates/rapier3d/Cargo.toml` (line 76) confirms `enhanced-determinism = ["simba/libm_force", "parry3d/enhanced-determinism"]`, routing all transcendentals away from host `libc`/`libm` into a single pure-Rust `fdlibm`/`musl`-derived software implementation (`rust-lang/libm`, `8f7436d260f000f054042545bb6e4c0d99fe35b2`, e.g., `libm/src/math/sinf.rs`) alongside deterministic hash maps (`IndexMap`). Even then, bit-exactness across ISAs still breaks if a downstream FFI C/C++ library links OS `<cmath>`, if the compiler contracts FMA inside `libm` polynomials, or if non-canonical NaNs enter state hashes.
- **Correctly Rounded Standard Math (`CORE-MATH`, IEEE ARITH 2022, DOI `10.1109/ARITH54963.2022.00014`):** Sibidanov, Zimmermann, and Glondu demonstrated that **correctly rounded ($\le 0.5\text{ ULP}$)** `binary32` and `binary64` elementary functions—mathematically guaranteed bit-identical across *every* conforming ISA and all four IEEE-754 rounding modes—can run at competitive average throughput using fast-path/accurate-path splitting around worst-case hard-to-round points (with bounded slow-path invocation on a tiny fraction of inputs).

## Boundaries

- **Unknown — Complete Compile-Time Relational Disjointness for Arbitrary First-Order ECS Queries:** `bevy_ecs` (`crates/bevy_ecs/src/query/access.rs`) decides disjointness at runtime over propositional DNF component bitsets (with worst-case exponential clause growth under nested `Or<...>`). Whether rich relational queries with multi-hop transitive joins (`Flecs` `(ChildOf, $p)`) and dynamic foreign-script accesses can be proven disjoint statically at compile time without severe false conflicts remains **unknown** from examined evidence.
- **Unknown — High-Throughput Bit-Exact Deterministic Reverse-Mode GPU Gradient Accumulation:** Eliminating float `atomicAdd` nondeterminism in `SLANG.D` reverse-mode rendering via fixed-point integer atomics or segmented warp-reduction trees carries workload-dependent memory/throughput trade-offs that were not benchmarked on live GPU silicon in this investigation (**not examined** empirically on GPU hardware; optimal general mechanism remains **unknown**).
- **Not Examined — Native `ARM64` and `RISC-V` Silicon Execution & `wasmtime` Canonicalization Benchmarks:** The hardware float probes (Evidence §3.1) were compiled and executed on `x86_64` Linux (`GCC 15.2.0`). `ARM64` (`FPCR.DN`, `fminnm`), `RISC-V` canonical NaN behavior, and `wasmtime`'s `cranelift_nan_canonicalization` runtime overhead are established from normative specifications and upstream source rather than executed natively on ARM64/RISC-V hardware.
- **Not Examined — `CORE-MATH` Worst-Case Hard-to-Round Latency Tails vs. `glibc`/`musl`:** `CORE-MATH`'s mathematical correct-rounding guarantee is verified from ARITH 2022 primary literature, but cycle-level worst-case latency tails on hard-to-round inputs were not benchmarked in this run.
- **Known Not to Apply — `Rapier` `enhanced-determinism` Alone Guaranteeing Cross-ISA Bit-Exactness:** Enabling `enhanced-determinism` in `dimforge/rapier` forces software `rust-lang/libm`, but is **known not to apply** as a standalone guarantee if compiler flags permit implicit FMA contraction (`-ffp-contract=fast`), if WebAssembly `relaxed-simd` instructions are emitted, if uncanonicalized NaNs are hashed, or if a linked C/C++ FFI library invokes host `<cmath>`.
- **Unsupported — Unbounded Dynamic Loops Inside `SLANG.D` Reverse-Mode Autodiff:** As verified directly in `shader-slang/slang` `docs/user-guide/07-autodiff.md` (line 901), dynamically unbounded loops without static iteration bounds, `[MaxIters(N)]`, or `[ForceUnroll]` are unsupported by Slang's reverse-mode checkpoint allocator, and exceeding `[MaxIters(N)]` at runtime is explicitly undefined behavior.

## Evidence

### 1. Pinned Upstream Repositories and Source Citations (Observed 2026-11-19)

- **`bevyengine/bevy` @ `779770720e6ad916c1de38cf66a67d0e079ed1e3`**:
  - `crates/bevy_ecs/src/storage/table/mod.rs`, lines 36, 103, 203, 227–236, 804: `TableId(u32)`, `TableRow(NonMaxU32)`, `Table`, and `Table::swap_remove_unchecked` swapping `last_element_index` into `row` and returning the displaced `Entity`.
  - `crates/bevy_ecs/src/query/access.rs`, lines 227, 586, 769–828, 893, 942: `FilteredAccess::is_compatible` checking pairwise DNF `filter_sets` refutation (`is_ruled_out_by`) and `FilteredAccess::extend` Cartesian product expansion.
  - `crates/bevy_ecs/src/world/unsafe_world_cell.rs`, lines 30–94: `UnsafeWorldCell<'w>` aliasing contract transfer and `Send`/`Sync` safety invariants.
- **`SanderMertens/flecs` @ `cf0e60d0d0e4be4728c4a4e7fda664c0d1f4b96b`**:
  - `src/storage/table.c` and `src/storage/table_graph.c`, lines 356–1313: `ecs_graph_edge_t`, `flecs_table_traverse_add`, `flecs_table_traverse_remove`, `flecs_table_traverse_dont_fragment`.
  - `src/storage/non_fragmenting_childof.c`, lines 8–70: `flecs_add_non_fragmenting_child_w_records` and `EcsIdOrderedChildren` avoiding per-parent archetype table fragmentation.
- **`skypjack/entt` @ `1dcd7aab6548786f7672ff578639188bd2f0d837`**:
  - `src/entt/entity/sparse_set.hpp`: sparse-page indirection + packed dense component arrays.
- **`shader-slang/slang` @ `a22c14207d52406edeaa82199df26db209625705`** & **`shader-slang/slangpy` @ `8dd7384b3114b48c04047fb01e3bb11cda8d263f`**:
  - `docs/design/existential-types.md`, lines 7–82: universal generic constraints vs. existential `{Type*, WitnessTable*, obj}` lowering.
  - `docs/user-guide/07-autodiff.md`, lines 88–139, 383, 901, 960–962: `fwd_diff`/`bwd_diff`, `DifferentialPair<T>`, `IDifferentiable`, `IDifferentiablePtrType`, and `[MaxIters(N)]` runtime UB specification.
  - `source/slang/slang-ir-layout.cpp`, lines 11–95: VK/D3D natural layout (`bool` = 4 B, unrounded composite tail padding, row-major IR matrices).
- **`WebAssembly/spec` @ `d0b2e8d5544d2049fba0521922c436e3f0fcaebe`**:
  - `document/core/exec/numerics.rst`, lines 1041–1209: canonical vs. arithmetic NaN propagation and `\PROFDET` deterministic profile (`+NaN(canon_N)`).
- **`WebAssembly/relaxed-simd` @ `c3f9359af2cd607cc46b0a3274f90ea52543a2f2`**:
  - `proposals/relaxed-simd/Overview.md`, lines 40–58, 170, 214–234, 326: `f32x4.relaxed_madd` (`0x105`/`0xaf`) and `f32x4.min`/`max` implementation-defined nondeterminism.
- **`bytecodealliance/wasmtime` @ `3ce2209872ccf1ea115914a81e020aef66a10c51`**:
  - `crates/wasmtime/src/config.rs`, lines 1747–1750, 3666–3680, 5327–5334: `Config::cranelift_nan_canonicalization` (`"enable_nan_canonicalization"`).
- **`dimforge/rapier` @ `475caa3ff4646fd9a796b67d14116256f4962bc7`**, **`rust-lang/libm` @ `8f7436d260f000f054042545bb6e4c0d99fe35b2`**, **`gschup/ggrs` @ `25bd9983dee3ecb0677be03b9e2e23d2bd6d29cb`**:
  - `rapier/crates/rapier3d/Cargo.toml`, line 76 (`enhanced-determinism = ["simba/libm_force", "parry3d/enhanced-determinism"]`); `libm/libm/src/math/sinf.rs`.

### 2. Peer-Reviewed Literature

- Yong He, Kayvon Fatahalian, and Tim Foley. *Slang: Language Mechanisms for Extensible Real-time Shading Systems*. *ACM Transactions on Graphics (SIGGRAPH 2018)*, 37(4), Art. 1. DOI `10.1145/3214756.3214798`.
- Sai Praveen Bangaru, Lifan Wu, Tzu-Mao Li, Jacob Munkberg, Gilbert Bernstein, Jonathan Ragan-Kelley, Frédo Durand, Aaron Lefohn, and Yong He. *SLANG.D: Fast, Modular and Differentiable Shader Programming*. *ACM Transactions on Graphics (SIGGRAPH Asia 2023)*, 42(6), Art. 262. DOI `10.1145/3618353`.
- Alexei Sibidanov, Paul Zimmermann, and Stéphane Glondu. *The CORE-MATH Project*. *29th IEEE Symposium on Computer Arithmetic (ARITH 2022)*. DOI `10.1109/ARITH54963.2022.00014` (HAL `hal-03721525`).

### 3. Reproducible Executable Probes (`GCC 15.2.0` & `Python 3.13`, `x86_64` Linux, 2026-11-19)

#### 3.1 Hardware FMA Contraction, NaN Payload/Sign Flip, SSE `minss`, and SIMD Reduction Width Divergence

Self-contained reproducer compiled twice from `/tmp/fp_det_probe.c` using `gcc (Debian 15.2.0-14) 15.2.0` (`-O2 -mfma -ffp-contract=fast` vs. `-O2 -mno-fma -ffp-contract=off`, linked with `-lm`):

```c
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <xmmintrin.h>

static uint32_t f32_bits(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }
static uint64_t f64_bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static float bits_f32(uint32_t u) { float x; memcpy(&x, &u, 4); return x; }
__attribute__((noinline)) static double fma_expr(double a, double b, double c) { return a * b + c; }

int main(void) {
    volatile double va = 1.0 + ldexp(1.0, -27), vb = 1.0 - ldexp(1.0, -27), vc = -1.0;
    double r = fma_expr(va, vb, vc);
    printf("FMA expr a*b+c = %.17e (hex=0x%016llx)\n", r, (unsigned long long)f64_bits(r));
    volatile float z = 0.0f;
    float nan_div = z / z;
    volatile float vq1 = bits_f32(0x7fc01234u), vq2 = bits_f32(0x7fc05678u);
    float sum12 = vq1 + vq2;
    float sum21 = vq2 + vq1;
    printf("x86_64 0.0f/0.0f     = 0x%08x\n", f32_bits(nan_div));
    printf("x86_64 qNaN1 + qNaN2 = 0x%08x | qNaN2 + qNaN1 = 0x%08x\n", f32_bits(sum12), f32_bits(sum21));
    float pz = +0.0f, nz = -0.0f, one = 1.0f, q1 = bits_f32(0x7fc01234u);
    printf("SSE minss(+0.0,-0.0)=0x%08x | minss(-0.0,+0.0)=0x%08x\n",
           f32_bits(_mm_cvtss_f32(_mm_min_ss(_mm_set_ss(pz), _mm_set_ss(nz)))),
           f32_bits(_mm_cvtss_f32(_mm_min_ss(_mm_set_ss(nz), _mm_set_ss(pz)))));
    printf("SSE minss(qNaN, 1.0)=0x%08x | minss(1.0, qNaN)=0x%08x\n",
           f32_bits(_mm_cvtss_f32(_mm_min_ss(_mm_set_ss(q1), _mm_set_ss(one)))),
           f32_bits(_mm_cvtss_f32(_mm_min_ss(_mm_set_ss(one), _mm_set_ss(q1)))));
    float vals[16] = {1e7f,0.3f,0.7f,0.1f, -1e7f,0.2f,0.9f,0.4f, 1e7f,0.6f,0.8f,0.5f, -1e7f,0.11f,0.22f,0.33f};
    volatile float s1 = 0.0f; for (int i = 0; i < 16; i++) s1 = s1 + vals[i];
    float a4[4] = {0}, a8[8] = {0};
    for (int i = 0; i < 16; i++) { a4[i % 4] += vals[i]; a8[i % 8] += vals[i]; }
    float s4 = (a4[0]+a4[1])+(a4[2]+a4[3]);
    float s8 = ((a8[0]+a8[1])+(a8[2]+a8[3]))+((a8[4]+a8[5])+(a8[6]+a8[7]));
    printf("Reduction 1-wide=%.8f (0x%08x) | 4-wide=%.8f (0x%08x) | 8-wide=%.8f (0x%08x)\n",
           (float)s1, f32_bits(s1), s4, f32_bits(s4), s8, f32_bits(s8));
    return 0;
}
```

Observed stdout on `x86_64` Linux:
```text
--- gcc -O2 -mfma -ffp-contract=fast ---
FMA expr a*b+c = -5.55111512312578270e-17 (hex=0xbc90000000000000)
x86_64 0.0f/0.0f     = 0xffc00000
x86_64 qNaN1 + qNaN2 = 0x7fc05678 | qNaN2 + qNaN1 = 0x7fc01234
SSE minss(+0.0,-0.0)=0x80000000 | minss(-0.0,+0.0)=0x00000000
SSE minss(qNaN, 1.0)=0x3f800000 | minss(1.0, qNaN)=0x7fc01234
Reduction 1-wide=4.65999985 (0x40951eb8) | 4-wide=5.15999985 (0x40a51eb8) | 8-wide=4.00000000 (0x40800000)
--- gcc -O2 -mno-fma -ffp-contract=off ---
FMA expr a*b+c = 0.00000000000000000e+00 (hex=0x0000000000000000)
x86_64 0.0f/0.0f     = 0xffc00000
x86_64 qNaN1 + qNaN2 = 0x7fc01234 | qNaN2 + qNaN1 = 0x7fc05678
SSE minss(+0.0,-0.0)=0x80000000 | minss(-0.0,+0.0)=0x00000000
SSE minss(qNaN, 1.0)=0x3f800000 | minss(1.0, qNaN)=0x7fc01234
Reduction 1-wide=4.65999985 (0x40951eb8) | 4-wide=5.15999985 (0x40a51eb8) | 8-wide=4.00000000 (0x40800000)
```

#### 3.2 Host↔Device Layout Drift, Archetype `swap_remove`, and Bevy DNF Disjointness (`Python 3.13`)
```text
=== PROBE 3A: Host-Device Struct Layout Drift ===
  Rust/C #[repr(C)]             : {'pos': 0, 'mass': 12, 'weights': 16, 'weights_stride': 4, 'rot': 32, 'size': 68}
  Vulkan std140                 : {'pos': 0, 'mass': 12, 'weights': 16, 'weights_stride': 16, 'rot': 80, 'size': 128}
  Vulkan std430 / WGSL storage  : {'pos': 0, 'mass': 12, 'weights': 16, 'weights_stride': 4, 'rot': 32, 'size': 80}

=== PROBE 3B: Archetype swap_remove Cross-Entity Pointer Aliasing ===
After E1 archetype migration (swap_remove row=1), E3 moved into row=1!
Foreign cached row=1 now silently points to entity=E3 pos=30.0 (was E1 pos=10.0)!

=== PROBE 3C: Bevy FilteredAccess DNF Disjointness Checker ===
Or(With A, Without B) vs (With B, Without A) compatible: True
Or(Without A, Without B) vs Or(With A, With B) compatible: False (counterexample entity: {A, !B})
```

## Revalidation

1. **ECS Disjointness & Archetype Migration:** Diff `bevyengine/bevy` `crates/bevy_ecs/src/query/access.rs` (`FilteredAccess::is_compatible` and `extend`) and `crates/bevy_ecs/src/storage/table/mod.rs` (`Table::swap_remove_unchecked`) against `779770720e6ad916c1de38cf66a67d0e079ed1e3`, and diff `SanderMertens/flecs` `src/storage/non_fragmenting_childof.c` against `cf0e60d0d0e4be4728c4a4e7fda664c0d1f4b96b` to track changes in non-fragmenting relationship indexing or static schedule-order conflict detection.
2. **Slang Autodiff & Layout Rules:** Diff `shader-slang/slang` `docs/user-guide/07-autodiff.md` (specifically `[MaxIters(N)]` semantics) and `source/slang/slang-ir-layout.cpp` (lines 11–95) against `a22c14207d52406edeaa82199df26db209625705` to check whether dynamic loop taping, deterministic gradient reduction intrinsics, or target-parameterized natural layout rules have landed.
3. **WebAssembly Determinism & Wasmtime Canonicalization:** Diff `WebAssembly/spec` `document/core/exec/numerics.rst` against `d0b2e8d5544d2049fba0521922c436e3f0fcaebe` and `bytecodealliance/wasmtime` `crates/wasmtime/src/config.rs` (`cranelift_nan_canonicalization`) against `3ce2209872ccf1ea115914a81e020aef66a10c51` to verify deterministic-profile NaN canonicalization and `relaxed-simd` status.
4. **Hardware Float Divergence Re-Probe:** Recompile and run the ~45-line C float probe (`-mfma -ffp-contract=fast` vs. `-mno-fma -ffp-contract=off` on `x86_64`, or `-ffp-contract=fast` vs. `-ffp-contract=off` on `ARM64` / `RISC-V` / `wasm32`) on any candidate target compiler or ISA to verify FMA contraction, `0.0f / 0.0f` NaN sign bits, two-NaN operand preservation, and SIMD reduction equivalence before shipping deterministic rollback code.
5. **Deterministic Transcendentals (`Rapier` / `CORE-MATH`):** Check `dimforge/rapier` `crates/rapier3d/Cargo.toml` (`enhanced-determinism`) against `475caa3ff4646fd9a796b67d14116256f4962bc7` and `rust-lang/libm` against `8f7436d260f000f054042545bb6e4c0d99fe35b2` to confirm whether `CORE-MATH` correctly-rounded routines have replaced `fdlibm`-derived polynomials.
