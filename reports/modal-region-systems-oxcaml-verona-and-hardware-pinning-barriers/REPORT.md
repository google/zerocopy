# Modal Region Systems, Isolated Cyclic Regions, and Hardware-Assisted Pinning Barriers

## Summary

Static multi-axis modal type systems, isolated heap regions, and hardware/JIT-assisted load barriers address three coupled problems in memory-safe systems runtimes: (1) combining stack/region allocation, uniqueness, and data-race-free concurrency without inference blowup; (2) permitting cyclic mutable graphs and hard real-time bump reclamation without stop-the-world (STW) global GC pauses; and (3) exposing GC-managed or capability-protected memory across FFI and concurrent relocation/revocation boundaries without STW root pinning.

Key established findings across the examined compilers, runtimes, and specifications:

1. **Multi-axis modal lattices stay tractable through comonadic/monadic factorization and two-sided Galois mode crossing.** Upstream `oxcaml/oxcaml` (`0cfb4ab854af0395cbbcf4e7dbdd6c2e7a9c62c1`) has scaled beyond the 3-axis calculi of ICFP 2024 (`10.1145/3674642`) and POPL 2025 (`10.1145/3704859`) to **9 modal axes**—5 comonadic (`Areality`, `Linearity`, `Portability`, `Yielding`, `Statefulness`) and 4 monadic (`Uniqueness`, `Contention`, `Visibility`, `Staticity`), four of which are 4-element `Diamond` lattices (`0b00..0b11`) rather than linear chains. Although the Cartesian product spans 8,192 points under `Locality` (12,288 under `Regionality`), per-axis solving reduces the state representation to 27 per-axis lattice elements (a 455.1x reduction), while `Mode.Crossing` encodes type-dependent mode crossing as a monotone map $f : M \to L$ possessing both a left adjoint $f_l$ and a right adjoint $f_r$, enabling one-sided constraint simplification ($f(m_1) \le f(m_2) \iff (f_l \circ f)(m_1) \le m_2 \iff m_1 \le (f_r \circ f)(m_2)$).
2. **Static region isolation (`Verona`) and dynamic real-time zones (`Extempore`) occupy fundamentally different soundness tiers.** Project Verona's runtime (`microsoft/verona-rt` `5cb8e8cf3699fa53c8a9b8dc34e4431c40d6230f`) encapsulates cyclic object graphs behind a single `Iso` entry object backed by `RegionBase` (external reference table + remembered set) and pluggable strategies (`RegionTrace` with dual trivial/non-trivial circular rings, `RegionArena`, `RegionRc`), paired with `Freeze` (immutable conversion) and lock-free multi-cown `when` acquisition (`10.1145/3622852`). By contrast, Extempore's `EXTZones` (`digego/extempore` `38bf1d2444a6166371c17abfa40dfa58f6ab962e`) implements thread-confined bump-reset arenas (`llvm_zone_t` on `thread_local llvm_zone_stack*`) with **no locks and no static escape prevention**: outward dangling pointers and cross-thread sharing are caller bugs caught only heuristically via debug AddressSanitizer poisoning (`ZONE_POISON`).
3. **Page-granularity hardware load barriers (`Cornucopia Reloaded` CLG) abolish STW revocation pauses but introduce severe sub-page false-sharing risk unless pinned/revoked objects are page-segregated.** In CheriBSD (`CTSRD-CHERI/cheribsd` `88f39900c32928d807dba245fba138808c666f34`), hardware per-page Capability Load Generation (`LCLG` vs. global `GCLG`) faults on first capability load from an uncleaned page (`vm_cheri_revoke_fault_visit`), fast-exiting on `PMAP_CAPLOADGEN_ALREADY` or `PMAP_CAPLOADGEN_CLEAN` (`PGA_CAPSTORE` clear). Under unsegregated 4 KiB pages holding 64 objects (64 B each), even a 1% density of pinned/revoked objects triggers barrier faults on 47.44% of pages (96.25% at 5% density); segregating pinned allocations onto dedicated pages drops unpinned page traps to 0.00%.
4. **Software colored-pointer barriers (Generational ZGC) and compiler safepoint stackmaps (`LLVM gc.statepoint`) expose sharp architectural trade-offs for FFI pinning.** Generational ZGC (`openjdk/jdk` `4f33273115381cd7697082fcb1bb2642dae19043`) packs 16 low-order metadata bits (`RRRR MM mm FF rr 0000`) into `zpointer` so x86-64 JIT load barriers combine validity checks and address unmasking via overlapping zeros and a single shift, paired with monotonic CAS self-healing (`ZBarrier::self_heal`), eliminating STW relocation pauses at the cost of forbidding raw native dereference of colored oops without an uncoloring barrier. LLVM `gc.statepoint` (`llvm/llvm-project` `c078d7b6876e6f21c0162671374939016b174c94`) supports moving collectors without pointer coloring by recording explicit `(base_ptr, derived_ptr)` pairs in `"gc-live"` bundles and `@llvm.experimental.gc.relocate` intrinsics—explicitly necessary because compiler passes can materialize **exterior derived pointers** outside object bounds—but every native FFI call that retains a raw pointer across a safepoint must either participate in relocation or pin the referent.

## Applicability

This report synthesizes primary source implementations, peer-reviewed type-theoretic papers, patent disclosures, and executable analytical probes across seven distinct systems that represent the major axes of the modal-region and barrier design space:

- **Modal type systems and adjoint crossing:** `oxcaml/oxcaml` (`0cfb4ab854af0395cbbcf4e7dbdd6c2e7a9c62c1`, specifically `typing/mode_intf.mli`, `typing/mode.ml`, `typing/jkind_axis.mli`, `typing/jkind_axis.ml`), cross-referenced against Lorenzen et al. (ICFP 2024, `10.1145/3674642`), Georges et al. (POPL 2025, `10.1145/3704859`), and Abel & Bernardy (ICFP 2020, `10.1145/3408972`). Findings on the 9-axis lattice and 4-element `Diamond` encodings apply specifically to the inspected `oxcaml/oxcaml` snapshot; earlier published papers describe the 3-axis (`Locality`/`Linearity`/`Uniqueness`) and 5-axis (`+Portability`/`Contention`) subsets.
- **Region-isolated and real-time arena runtimes:** `microsoft/verona-rt` (`5cb8e8cf3699fa53c8a9b8dc34e4431c40d6230f`, `src/rt/region/*`, `src/rt/cpp/when.h`), `microsoft/verona` (`ed33fdf1c2e249a0393ead1cffd6e40503c70f2c`), Cheeseman et al. (OOPSLA 2023, `10.1145/3622852`), and `digego/extempore` (`38bf1d2444a6166371c17abfa40dfa58f6ab962e`, `include/EXTZones.h`, `src/EXTZones.cpp`). Verona runtime findings characterize the C++ runtime implementation of regions and Behaviour-Oriented Concurrency (BoC); Extempore findings characterize the C++ zone allocator invoked by LLVM-compiled `xtlang` code.
- **Hardware load/pointer barriers:** `CTSRD-CHERI/cheribsd` (`88f39900c32928d807dba245fba138808c666f34`, `sys/cheri/revoke.h`, `sys/vm/vm_cheri_revoke.c`) and Filardo et al. (ASPLOS 2024, `10.1145/3620665.3640416`), targeting CHERI-enabled architectures with per-page capability load generation bits (Arm Morello prototype and CHERI-RISC-V); and Mill Computing U.S. Patents `9,524,163` and `9,747,218`, which describe architectural designs not shipped in commodity silicon.
- **Software colored-pointer barriers and compiler safepoints:** `openjdk/jdk` (`4f33273115381cd7697082fcb1bb2642dae19043`, Generational ZGC in `src/hotspot/share/gc/z/zAddress.hpp`, `zBarrier.hpp`, `zBarrier.inline.hpp`) on 64-bit x86-64 and AArch64; and `llvm/llvm-project` (`c078d7b6876e6f21c0162671374939016b174c94`, `llvm/docs/Statepoints.md`), applicable to LLVM IR using non-zero GC address spaces (`addrspace(1)`) and `RewriteStatepointsForGC`.

The analytical/combinatorial probe (`p1_modal_and_barrier_probe.py`) executes on Python 3 on Linux x86-64 and verifies exact algebraic properties of the extracted OxCaml lattices and analytical page-collision probabilities; it does not benchmark hardware traps on Morello silicon or ZGC throughput on HotSpot.

## Findings

### 1. Multi-Axis Modal Type Systems: Unified Modalities, OxCaml's 9-Axis Lattice, and Adjoint Mode Crossing

#### 1.1 Unified Modal Type Theory (Abel & Bernardy, ICFP 2020)

Basis: normative (paper formalization, `10.1145/3408972`) + derived

Abel & Bernardy (*A Unified View of Modalities in Type Systems*, ICFP 2020) formulate a single parameterized modal typing judgment where every variable binding in context $\Gamma$ carries a grade/modality drawn from a partially ordered semiring $(M, \le, +, 0, \cdot, 1)$ (or more generally a left/right-residuated lattice of modalities). Key algebraic laws governing resource/locality/capability tracking are:

- **Context scaling and addition:** Variable usage scales context grades via multiplication ($\mu \cdot \Gamma$) and merges sub-expression contexts via pointwise addition ($\Gamma_1 + \Gamma_2$), with sub-usaging governed by the lattice order $\Gamma_1 \le \Gamma_2$.
- **Modal box introduction and elimination:** Introduction of a modal type $\Box_\mu A$ scales the premise context by a left-division (residual) or multiplication $\mu \cdot \Gamma \vdash t : A \implies \Gamma \vdash \text{box}\,t : \Box_\mu A$, enforcing that any free variable captured inside $\Box_\mu A$ must satisfy a grade at least compatible with $\mu$ (the **lock / comonadic deep-crossing law**).
- **Subsumption direction (polarity):** Because modalities act contravariantly on assumptions and covariantly on conclusions, a single semiring framework encompasses both **comonadic** (context-restricting, e.g., `Global < Local`, `Many < Once`, `Portable < Nonportable`) and **monadic** (result-tainting/capability-restricting, e.g., `Unique < Aliased`, `Uncontended < Contended`) disciplines—provided opposing polarities are ordered consistently in the product lattice.

#### 1.2 Live OxCaml 9-Axis Mode Lattice and Polarity Split

Basis: source (`oxcaml/oxcaml@0cfb4ab8`, `typing/mode_intf.mli` L423–740, `typing/mode.ml` L599–800) + normative (`10.1145/3674642`, `10.1145/3704859`) + execution

While the ICFP 2024 paper (*Oxidizing OCaml with Modal Memory Management*, Lorenzen et al.) formalizes Locality, Linearity, and Uniqueness, and the POPL 2025 paper (*Data Race Freedom à la Mode*, Georges et al.) adds Portability and Contention to enforce compile-time data-race freedom in multicore OCaml, inspection of `oxcaml/oxcaml` at `0cfb4ab854af0395cbbcf4e7dbdd6c2e7a9c62c1` reveals that the production compiler already manages **9 modal axes** partitioned into two adjoint families (`Comonadic` = `Common_axis_pos` and `Monadic` = `Common_axis_neg`), plus a standalone `Forkable` axis (`Forkable | Unforkable`, `typing/mode_intf.mli` L534–548) and non-modal `jkind` axes (`Externality`, `Nullability`, `Separability` in `typing/jkind_axis.mli` L27–58):

| Axis | Polarity | Lattice Shape & Exact Constructors (`typing/mode.ml`) | Legacy Default | Semantic Role |
| :--- | :--- | :--- | :--- | :--- |
| `Areality` (`Locality` / `Regionality`) | Comonadic (`pos`) | Total order: `Global < Local` (2) or `Global < Regional < Local` (3) | `Global` | Stack/region escape prevention; `Regional` permits return from inner region into enclosing region |
| `Linearity` | Comonadic (`pos`) | Total order: `Many < Once` (2) | `Many` | Restricts closures/values to at-most-once invocation so they may capture `Unique` values |
| `Portability` | Comonadic (`pos`) | **4-element `Diamond`**: `Portable (0b00) < {Shareable (0b01), Corruptible (0b10)} < Nonportable (0b11)` | `Nonportable` | Controls whether a value/closure may cross thread/domain boundaries |
| `Yielding` | Comonadic (`pos`) | Total order: `Unyielding < Yielding` (2) | `Unyielding` | Tracks whether a computation may perform algebraic-effect yields/suspensions |
| `Statefulness` | Comonadic (`pos`) | **4-element `Diamond`**: `Stateless (0b00) < {Writing (0b01), Reading (0b10)} < Stateful (0b11)` | `Stateful` | Tracks whether a function reads/writes mutable state |
| `Uniqueness` | Monadic (`neg`) | Total order: `Unique < Aliased` (2) | `Aliased` | Guarantees single ownership for safe in-place overwrite/deallocation |
| `Contention` | Monadic (`neg`) | **4-element `Diamond`**: `Uncontended (0b00) < {Corrupted (0b01), Shared (0b10)} < Contended (0b11)` | `Uncontended` | Governs unsynchronized mutable field access across parallel domains |
| `Visibility` | Monadic (`neg`) | **4-element `Diamond`**: `Read_write (0b00) < {Read (0b01), Write (0b10)} < Immutable (0b11)` | `Read_write` | Controls read/write capability on mutable fields (dual to `Statefulness`) |
| `Staticity` | Monadic (`neg`) | Total order: `Static < Dynamic` (2) | `Dynamic` | Tracks compile-time/static availability vs. dynamic runtime values |

**Critical structural finding (4-element `Diamond` bitmask encoding):** Four of the nine axes (`Portability`, `Contention`, `Statefulness`, `Visibility`) are NOT linear chains—they are 4-element Boolean diamonds implemented via the `Diamond` functor (`typing/mode.ml` L599–769), where the two middle elements are incomparable (`0b01` and `0b10`), meet is bitwise `&`, join is bitwise `|`, and partial order is `(a & b) == a`. For example, in `Contention`, `Shared` (concurrently readable, not writable) and `Corrupted` are incomparable between `Uncontended` (`0b00`) and `Contended` (`0b11`).

**Why 9-axis inference does not explode combinatorially:**
Direct execution of `p1_modal_and_barrier_probe.py` confirms that the full Cartesian product of the 9 axes contains **$2^5 \times 4^4 = 8{,}192$** points under `Locality` and **$3 \times 2^4 \times 4^4 = 12{,}288$** points under `Regionality`. OxCaml avoids $O(\prod |A_i|)$ solver blowup through three mechanisms observable in `typing/mode.ml` and `typing/jkind_axis.mli`:

1. **Per-axis factorized solving:** Mode variables maintain independent floor/ceiling bounds per axis (`Per_axis`, `typing/mode_intf.mli` L671–691) rather than enumerating product elements. The total per-axis state sum is only **27** elements (a **455.1x** reduction vs. 12,288). `Jkind_axis.Axis_set` packs axis sets into a single unboxed integer bitfield (`type t [@@immediate]`, `typing/jkind_axis.mli` L83–84).
2. **Sparse dual-axis coupling at closure/modality boundaries:** Axes interact only through specific **adjoint dual locks** (not arbitrary cross-axis relations):
   - Crossing a closure into `Many` linearity forces captured `Unique` variables to `Aliased`;
   - Sending a closure across domains as `Portable` forces captured `Uncontended` mutable references to `Contended` (or `Shared` for `Shareable`);
   - Restricting `Statefulness` (`Stateless` / `Reading` / `Writing`) couples to `Visibility` (`Immutable` / `Read` / `Write`).
   Thus, adding new orthogonal axes (such as pinning, barrier discipline, real-time confinement, or persistence) scales **additively** ($O(k)$ per constraint) in the constraint solver as long as cross-axis interactions remain restricted to pairwise comonadic-monadic dual locks.
3. **Two-sided Galois-adjoint mode crossing (`Mode.Crossing`):** In `typing/mode.ml` L8514–8542, a type $t$'s mode-crossing capability is modeled as a monotone function $f : M \to L$ equipped with **both** a left adjoint $f_l$ and a right adjoint $f_r$, satisfying:
   $$f(m_1) \le f(m_2) \iff (f_l \circ f)(m_1) \le m_2 \iff m_1 \le (f_r \circ f)(m_2)$$
   Because an inference engine during bidirectional checking typically knows only the inferred mode $m_1$ (lower bound) or the expected mode $m_2$ (upper bound), applying the closure operator $f_r \circ f$ on the right or the interior operator $f_l \circ f$ on the left performs exact mode crossing **one-sidedly** without waiting for both sides to become ground constants. For example, an immediate `int` maps via the constant map to the unit lattice (`f_l(f(m)) = min`, `f_r(f(m)) = max`), so `int` crosses all modal axes (`Local -> Global`, `Aliased -> Unique`, `Contended -> Uncontended`) at zero runtime cost. Exhaustive evaluation in `p1_modal_and_barrier_probe.py` verifies this Galois equivalence across all $4 \times 4 = 16$ pairs of a 4-element `Diamond` lattice (`Portability` collapsing `{Portable, Shareable}` vs. `{Corruptible, Nonportable}`):
   - $f_l \circ f = \{\text{Portable} \mapsto \text{Portable},\ \text{Shareable} \mapsto \text{Portable},\ \text{Corruptible} \mapsto \text{Corruptible},\ \text{Nonportable} \mapsto \text{Corruptible}\}$
   - $f_r \circ f = \{\text{Portable} \mapsto \text{Shareable},\ \text{Shareable} \mapsto \text{Shareable},\ \text{Corruptible} \mapsto \text{Nonportable},\ \text{Nonportable} \mapsto \text{Nonportable}\}$

**Non-modal `jkind` axes and FFI/GC ignorability:** `typing/jkind_axis.mli` L27–58 additionally tracks `Externality` (`External | External64 | Internal`) and `Separability` (`Non_pointer | Non_pointer64 | Non_float | Separable | Maybe_separable`) with `upper_bound_if_is_always_gc_ignorable`. A value whose jkind satisfies `Externality = External` (e.g., tagged immediates or unboxed scalars) requires no GC scanning and can cross GC/native/real-time boundaries without barriers or pinning.

**Scaling lesson for 6+ custom systems axes:** Extending a modal system to encode GC domain, mutability, pinning, barrier class, real-time tier, and durability does **not** blow up unification complexity if (a) every axis is a small finite lattice (chain or Boolean diamond) solved independently per axis, (b) every type's mode-crossing map admits explicit left/right Galois adjoints on each axis, and (c) signatures omit legacy defaults (`Global`, `Many`, `Aliased`, `Uncontended`, `Nonportable`, etc.) during error rendering and interface printing. The real bottleneck is **type-error localization and modal-polymorphism surface syntax** when a single unification failure spans two coupled dual axes (e.g., a closure failing `Portable` because a captured field's `jkind` fails to cross `Contention`).

---

### 2. Isolated Cyclic Regions (`Project Verona`) vs. Real-Time Memory Zones (`Extempore`)

#### 2.1 Project Verona: Single-Entry `Iso` Regions, Pluggable Collectors, and Lock-Free `when`

Basis: source (`microsoft/verona-rt@5cb8e8cf`, `src/rt/region/region.h`, `region_trace.h`, `region_arena.h`, `region_rc.h`, `freeze.h`, `src/rt/cpp/when.h`) + normative (`10.1145/3622852`)

Project Verona decouples **concurrency ownership** from **per-region memory management**:

1. **Single-entry `Iso` region encapsulation (`region.h` L15–59):** Every mutable object belongs to exactly one region, whose sole external entry point (aside from explicitly tracked external references) is an `Iso` (isolated) root object. The `Iso` object points to a `RegionBase` metadata header storing:
   - The region's **remembered set** (for sub-regions / cross-region references);
   - The region's **external reference table** (mapping external tokens to internal objects without violating single-ownership transfer of the region as a whole);
   - A dispatchable strategy tag (`RegionType::Trace`, `RegionType::Arena`, `RegionType::Rc`; `region.h` L72–115).
2. **Pluggable intra-region reclamation without global GC:**
   - **`RegionTrace` (`region_trace.h` L35–85):** Tracks every object allocated in the region in **two circular linked rings**—a primary ring rooted at the `Iso` object (requiring no `last` pointer because `Iso` is always known) and a secondary ring (`next_not_root`, `last_not_root`) separating *trivial* objects (no destructor, no finalizer, no sub-regions) from *non-trivial* objects. This split enables $O(1)$ ring merging when two regions merge, and allows whole-region deallocation (`Region::release`) to skip tracing trivial objects completely when the region becomes unreachable. Internal cycles inside a live `RegionTrace` are collected locally via trace-and-sweep over only that region's objects—zero cross-thread coordination and zero global STW pauses.
   - **`RegionArena` (`region_arena.h`):** Bump-allocated region where all objects die together in $O(1)$ chunks when the `Iso` drops.
   - **`RegionRc` (`region_rc.h`):** Non-atomic reference counting strictly inside the owning thread/cown.
3. **Freezing into deeply immutable shared graphs (`freeze.h`):** `Freeze` walks an isolated region starting from its `Iso` root, collapses strongly connected components (SCCs) into shared immutable reference-counted groups, and releases the region metadata—enabling arbitrary concurrent read sharing across threads with zero locks and zero GC scanning.
4. **Deadlock-free Behaviour-Oriented Concurrency (`when.h` L26–149, `10.1145/3622852`):** Regions are owned by **cowns** (concurrent owners). A `when(c1, c2, ...) << lambda` statement constructs a `BehaviourCore` and atomically enqueues it onto all target cowns in a canonical global address order using lock-free MCS-like per-cown queues (with `Batch` accumulating multiple `when` clauses via `operator+` for atomic scheduling). The lambda receives exclusive `acquired_cown<T>` access to every listed cown's isolated region simultaneously—eliminating both data races and lock-ordering deadlocks without a global stop-the-world runtime.

**Key architectural property for zero-outward-GC-pointer isolation:** Verona enforces region closure **statically in the language type system** (`microsoft/verona`): references inside a region may point to (a) objects within the same region, (b) owned sub-regions via their `Iso` root, (c) deeply immutable (`imm`) frozen objects, or (d) cown references (which cannot be dereferenced synchronously—only scheduled asynchronously via `when`). Crucially, an `Iso` region **cannot** hold raw borrowed pointers into a sibling mutable region that outlive a `when` scope, nor can it silently leak mutable interior pointers out of the region.

#### 2.2 Extempore `EXTZones`: Dynamic Real-Time Bump Arenas Without Static Escape Soundness

Basis: source (`digego/extempore@38bf1d24`, `include/EXTZones.h` L1–67, `src/EXTZones.cpp` L1–317)

Extempore's `xtlang` targets hard real-time audio/DSP callbacks (often operating at 64-sample buffers @ 48 kHz = **1.33 ms** hard deadlines) where stop-the-world GC pauses cause audible dropouts. Inspection of `EXTZones.h` and `EXTZones.cpp` reveals a sharp contrast with Verona and OxCaml:

- **Exact layout (`EXTZones.h` L25–37):**
  ```cpp
  struct llvm_zone_t {
      void* memory;              // 32-byte aligned backing slab (LLVM_ZONE_ALIGN = 32)
      uint64_t offset;           // bump cursor
      uint64_t mark;             // saved watermark
      uint64_t size;             // slab capacity in bytes
      zone_hooks_t* cleanup_hooks; // linked list of [void]* xtlang cleanup closures
      llvm_zone_t* memories;     // overflow chain (each extension doubles size; min 1024 B)
  };
  ```
- **Per-thread zone stack & zero-lock callback reset (`EXTZones.cpp` L28, L94–100, L180–230, L301–314):** Each thread owns `thread_local llvm_zone_stack* tls_llvm_zone_stack` (default root zone 1 MiB) plus `tls_llvm_callback_zone` (1 MiB). Before every real-time callback, `llvm_zone_callback_setup()` invokes `llvm_zone_reset(zone)`, which resets `offset = 0` in $O(1)$ without freeing backing pages (avoiding `malloc`/`free` lock contention in the audio thread; in ASan builds it only re-poisons `[0, offset)` rather than the whole slab so per-sample resets stay fast, L96–99). Every `llvm_zone_malloc` stores a 32-byte header carrying the payload size (enabling `llvm_zone_ptr_size` and shallow `llvm_zone_copy_ptr` across zones, L104–110, L256–271) and zero-initializes the block (`memset(block, 0, footprint)`).
- **No static escape or thread-safety enforcement (`EXTZones.h` L5–9):** The header explicitly warns: *"Zones are thread-confined... None of the functions below take a lock. Sharing a single `llvm_zone_t` between threads is a bug in the caller, not something this allocator defends against."* Furthermore, `xtlang` does **not** statically forbid storing a pointer from a short-lived inner zone into a longer-lived outer zone or global heap, nor storing a Scheme GC pointer inside a zone without manual retention; `llvm_ptr_in_zone` (L273) provides only an opt-in runtime range check.

#### 2.3 Cross-Runtime Synthesis: Achieving Both Static Isolation and Sub-Millisecond Real-Time Deadlines

Basis: derived (from OxCaml `Regionality` + `Externality`, Verona `Iso` + `RegionArena`, Extempore `EXTZones`)

Combining the verified mechanisms above shows the exact requirements to achieve **sound, statically checked, zero-GC-pause real-time zones** (suitable for 1.3 ms audio/control loops):

1. **Modal confinement (OxCaml `Regionality` + `Externality`):** The real-time callback runs inside a lexical region whose mode forbids capturing any GC-traced pointer (`Externality = External` / `NoGcRef` jkind bound on all values entering the zone) and constrains zone-allocated references to `Local` (cannot escape the callback frame) or `Regional` (can be returned only into the explicitly supplied parent zone).
2. **Wait-free cross-boundary handoff (double-buffered/triple-buffered value swap):** Because the real-time thread cannot take a GC safepoint or lock a tracing heap, data crossing from the GC-managed control plane into the real-time zone must be **deeply copied/serialized by the GC side** into a pre-allocated, non-GC, `External`-kind swap buffer (or Verona-frozen `imm` slab freed asynchronously by a non-RT reaper thread). The RT thread performs only a single atomic pointer exchange (`acquire`/`release` swap of a pre-sized slot) and bump-allocates temporaries in its thread-local `RegionArena`/`llvm_zone_t`, resetting `offset = 0` on callback exit.
3. **Hidden cost to budget:** Even without GC pauses, `EXTZones.cpp` L124–137 (`zone_extend` calling `_aligned_malloc`/`malloc`) and L171 (`memset` zeroing every bump allocation) reveal two real-time hazards: (i) overflow extension hits the OS allocator unless the slab is pre-sized to worst-case per-tick allocation (`size >= WCET_alloc`), and (ii) GC-side packing into a swap slot pays $O(\text{payload bytes})$ copy bandwidth on the non-RT side, trading GC-thread CPU for strictly bounded $O(1)$ RT-thread latency.

---

### 3. Hardware & JIT-Assisted Pinning and Relocation Barriers

#### 3.1 Cornucopia Reloaded: Per-Page Capability Load Generation (`CLG`) Barriers

Basis: source (`CTSRD-CHERI/cheribsd@88f39900`, `sys/cheri/revoke.h` L46–326, `sys/vm/vm_cheri_revoke.c` L118–628) + normative (`10.1145/3620665.3640416`)

Original Cornucopia achieved CHERI heap temporal memory safety (preventing use-after-free by quarantining freed allocations and clearing capability tags pointing into quarantined memory) via a background sweep followed by a **stop-the-world pause** lasting tens of milliseconds to seconds on Arm Morello. **Cornucopia Reloaded** (Filardo et al., ASPLOS 2024) eliminates the STW sweep using hardware **per-page Capability Load Barriers (CLG)** available on Arm Morello and CHERI-RISC-V:

1. **Epoch parity state machine (`sys/cheri/revoke.h` L46–86, `vm_cheri_revoke.c` L118–157):**
   - `cheri_revoke_epoch_t` is a 64-bit monotonic counter where **even** epochs denote quiescent states and **odd** epochs denote an active revocation pass (`KASSERT((epoch & 1) == 0)` on async pass entry, incremented to `epoch + 1` on start and to `epoch + 2` on completion).
   - An allocation placed in quarantine during epoch `then` is safe to reuse only when `cheri_revoke_epoch_clears(now, then)` holds, defined verbatim in `revoke.h` L85 as:
     ```c
     return (cheri_revoke_epoch_ge(now, then + (then & 1) + 2));
     ```
     This guarantees at least one complete revocation pass that *started after* the object entered quarantine has fully finished before its virtual address range can be reallocated.
2. **Hardware CLG fault-and-clean protocol (`vm_cheri_revoke.c` L389–424, L592–617):**
   - Each page-table entry (PTE) stores a local capability-load-generation bit (`LCLG`), compared in hardware on every capability load against the process's global generation (`GCLG`).
   - Starting a new epoch flips `GCLG` without eagerly rewriting every PTE or halting mutators.
   - If a mutator loads a capability from a page where `LCLG != GCLG`, hardware raises a load-barrier page fault handled by `vm_cheri_revoke_fault_visit(uvms, va)`.
   - The handler calls `pmap_caploadgen_update(upmap, va, &m, PMAP_CAPLOADGEN_UPDATETLB | ...)`:
     - **`PMAP_CAPLOADGEN_ALREADY`:** Another thread or the background worker already updated `LCLG == GCLG` (spurious/raced fault) — resolve immediately.
     - **`PMAP_CAPLOADGEN_CLEAN`:** Page metadata flag `PGA_CAPSTORE` is clear (the page has never had a tagged capability stored into it, e.g., pure scalar/byte arrays) — advance `LCLG` and skip scanning completely.
     - **Dirty capability page:** Scan the single 4 KiB page against the quarantine shadow bitmap, strip validity tags from any capability whose base falls in quarantine, update `LCLG = GCLG`, refresh the TLB entry, and restart the faulting load instruction.
   - Concurrently, background kernel workers (`vm_cheri_revoke_kproc`, L161–219) sweep remaining unvisited pages using the exact same `pmap_caploadgen_update` fast-skip logic.
3. **Published empirical characteristics (`10.1145/3620665.3640416`):** On Arm Morello, Cornucopia Reloaded eliminates multi-millisecond STW pauses on interactive workloads (`pgbench`, `gRPC`), imposes no net wall-clock/CPU degradation relative to stop-the-world Cornucopia, and reduces DRAM traffic overhead (median 87% of Cornucopia's DRAM traffic overhead on SPEC CPU2006 and <50% on `pgbench`) because lazy page-level cleaning avoids redundant eager sweeps of cold or non-capability pages (`PGA_CAPSTORE == 0`).

#### 3.2 Quantitative Analysis of Page-Granularity False Sharing (CLG / `userfaultfd` WP)

Basis: execution (`p1_modal_and_barrier_probe.py`) + derived

A crucial architectural pitfall arises when applying 4 KiB page-granularity barriers—whether CHERI `CLG` or Linux `userfaultfd` write-protect (`UFFDIO_WRITEPROTECT`)—to **FFI root pinning or per-object temporal barriers** on a general-purpose heap. If pinned or revoked objects are co-located randomly with hot unpinned objects on 4 KiB pages ($K = 64$ objects per page at 64 bytes/object), the probability that a randomly chosen page contains at least one pinned/revoked object is $1 - (1 - p)^K$.

Direct execution of `p1_modal_and_barrier_probe.py` gives exact false-sharing trap probabilities:

| Pinned / Revoked Object Density $p$ | Unsegregated 4 KiB Page Trap Rate ($K=64$) | Page-Segregated Unpinned Page Trap Rate | Armed Pages (Segregated) |
| :---: | :---: | :---: | :---: |
| 0.10% | **6.20%** | 0.00% | 0.10% |
| 0.50% | **27.44%** | 0.00% | 0.50% |
| 1.00% | **47.44%** | 0.00% | 1.00% |
| 2.00% | **72.55%** | 0.00% | 2.00% |
| 5.00% | **96.25%** | 0.00% | 5.00% |
| 10.00% | **99.88%** | 0.00% | 10.00% |

**Design consequence:** At just **1% pinned objects**, nearly half (47.44%) of all unsegregated 4 KiB pages trap on every epoch flip; at 5%, 96.25% of pages trap—turning lazy page barriers into an eager trap storm (kernel entry + TLB shootdown per page). Therefore, page-level hardware barriers (`CLG`, `userfaultfd` WP, or `mprotect`) are viable for zero-STW pinning **only when coupled with allocator-level page coloring / segregated pinned-page pools** (allocating pinned-mode objects strictly on dedicated pages, or exploiting `PGA_CAPSTORE`-style no-capability page segregation for raw FFI byte buffers).

#### 3.3 Mill Architecture Pointer Events and Protection Turfs (U.S. Patents 9,524,163 & 9,747,218)

Basis: documentation (Mill Computing U.S. Patent disclosures `US-9524163-B2`, `US-9747218-B2`)

The Mill CPU architecture (Ivan Godard / Mill Computing) proposes eliminating both software write/read barriers and OS page-fault trap storms through two hardware mechanisms:

1. **Hardware Pointer Events (`US-9524163-B2`, *"Computer processor employing hardware-based pointer processing"*):** Pointers carry embedded high-order metadata/event bits recognized natively by the load/store units and pointer arithmetic (`addp`). Arithmetic overflowing into metadata bits produces a hardware `NaR` (Not-a-Result) rather than silently corrupting tag bits. Configurable pointer event bits trigger low-overhead hardware events/traps specifically on pointer loads, stores, or pointer-typed stores—offloading generational write barriers, card marking, or concurrent GC relocation checks from inline compiler code into hardware metadata checks.
2. **Thread-Specific Protection Domains / Turfs and Portals (`US-9747218-B2`, *"CPU security mechanisms employing thread-specific protection domains"*):** Rather than heavyweight process address-space switches or Intel MPK's 16-key limit, Mill defines per-thread protection domains (**turfs**) checked in hardware via protection lookaside structures and fast cross-domain calls (**portals**), enabling fine-grained memory isolation between mutually untrusted or differently managed runtime regions within a single virtual address space.

Because no Mill silicon has been commercially fabricated, latency and power figures remain unmeasured (`unknown` in `## Boundaries`); the architectural significance is as a clean reference point separating **pointer-granularity hardware barriers** (zero sub-page false sharing) from **page-granularity PTE barriers** (4 KiB false-sharing floor).

#### 3.4 OpenJDK Generational ZGC: Software Colored Pointers and Monotonic Self-Healing

Basis: source (`openjdk/jdk@4f332731`, `src/hotspot/share/gc/z/zAddress.hpp` L48–264, `zBarrier.inline.hpp` L37–95)

Generational ZGC achieves sub-millisecond pause times on commodity x86-64 and AArch64 hardware without PTE traps or custom pointer-event silicon by embedding GC state directly inside 64-bit heap references (`zpointer`):

- **Exact 16-bit low-order metadata layout (`zAddress.hpp` L48–176):**
  ```text
  [ ... heap address bits (base + offset) ... ][ RRRR | MM | mm | FF | rr | 0000 ]
                                                 ^      ^    ^    ^    ^    ^
                                                 |      |    |    |    |    +-- 4 reserved bits
                                                 |      |    |    |    +------- 2 Remembered[0,1] bits (store barrier)
                                                 |      |    |    +------------ 2 Finalizable[0,1] bits (mark barrier)
                                                 |      |    +----------------- 2 MarkedYoung[0,1] bits (mark barrier)
                                                 |      +---------------------- 2 MarkedOld[0,1] bits (mark barrier)
                                                 +----------------------------- 4 Remapped[00,01,10,11] bits (load barrier)
  ```
- **Architecture-specific fast-path encoding (`zAddress.hpp` L75–107):**
  - On **x86-64**, the low-order zero bits of aligned object addresses intentionally overlap with the high-order zero bits of `Remapped00..11`. Because the address bits begin immediately above the active single set `Remapped` bit, the JIT load barrier combines the `load_good` check and address unmasking (`zpointer -> zaddress`) into a **single speculative shift instruction** (testing the shifted-out bit via carry/flags) with zero extra mask instruction on the fast path.
  - On **AArch64**, ZGC does *not* overlap address/metadata zeros and instead stores the **bitwise complement** in the 4 remap bits (3 good bits, 1 bad bit) to match AArch64 bit-test/branch idioms.
- **Monotonic CAS self-healing (`zBarrier.inline.hpp` L41–95):** When a load or store encounters a bad color, the slow path relocates or marks the referent and updates the heap slot in-place via a relaxed CAS loop (`AtomicAccess::cmpxchg(p, ptr, heal_ptr, memory_order_relaxed)`). `ZBarrier::assert_transition_monotonicity` enforces a strict lattice upgrade invariant (`load_good`, `mark_good`, `store_good`, `marked_young`, `marked_old`, `marked_finalizable` are monotonically non-decreasing within an epoch), guaranteeing race-free concurrent self-healing without locks.
- **FFI pinning friction:** A `zpointer` is **not** a dereferenceable native C pointer (`zaddress`); passing a heap object to unmodified native C/DMA code requires either (a) an explicit JNI/FFM copy or pin outside ZGC's relocating pages, or (b) uncoloring and forbidding relocation of the backing ZPage for the duration of the native call (which defeats ZGC's compaction guarantee on that page if held indefinitely).

#### 3.5 LLVM `gc.statepoint`: Derived-Pointer Stackmaps vs. Colored Pointers

Basis: source (`llvm/llvm-project@c078d7b6`, `llvm/docs/Statepoints.md` L34–47, L179–205, L299–315)

LLVM's `gc.statepoint` infrastructure supports moving garbage collectors **without** colored pointers or per-load barriers by recording precise root maps at safepoints (`RewriteStatepointsForGC`):

- **Address-space separation:** GC-managed pointers live in a designated non-zero address space (conventionally `ptr addrspace(1)`), distinct from raw native pointers (`ptr addrspace(0)`).
- **Base vs. interior vs. exterior derived pointers (`Statepoints.md` L34–43, L299–315):** LLVM explicitly distinguishes:
  1. *Base pointers* (start of allocation);
  2. *Interior derived pointers* (offset within allocation bounds);
  3. *Exterior derived pointers* (intermediate results from loop strength reduction or GEP hoisting that point **outside** the allocation or even into another allocation's address range).
  Because exterior derived pointers cannot be mapped back to their owning allocation by runtime address inspection alone, LLVM lowers every safepoint call to a three-part relocation sequence:
  ```llvm
  %safepoint = call token (...) @llvm.experimental.gc.statepoint... (...) ["gc-live" (ptr addrspace(1) %base, ptr addrspace(1) %derived)]
  %base.reloc    = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %safepoint, i32 0, i32 0)
  %derived.reloc = call ptr addrspace(1) @llvm.experimental.gc.relocate.p1(token %safepoint, i32 0, i32 1)
  ```
  The stackmap emits explicit `(base, derived)` location pairs so the runtime computes `offset = derived - base` before relocation and writes `new_base + offset` afterward.
- **Trade-off under dense FFI pinning:** Unlike ZGC, `gc.statepoint` imposes zero load-barrier overhead on uncolored dereferences and naturally tracks exterior derived pointers. However, moving an object requires reaching a safepoint (either STW or thread-local handshake), and any native FFI callee receiving a raw `addrspace(0)` pointer derived from an `addrspace(1)` object is **invisible to `gc.relocate`**—forcing either explicit pinning of the object/page before the FFI transition or copying into non-GC memory.

---

### 4. Comparative Architecture Matrix: Zero-STW Pinning & Region Isolation Mechanisms

Basis: derived (synthesized from verified source and specification findings in Sections 1–3)

| Mechanism | Primary Enforcement Layer | Granularity | STW Pause Required? | Cyclic Graphs Allowed? | Native/FFI Raw Pointer Dereference? | Dominant Overhead / Failure Mode |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **OxCaml Modes (`Locality`/`Uniqueness`/`Portability` + `jkind`)** | Static modal type system (9 axes, Galois crossing) | Per-value / per-type | No (for `Local`/`External` values) | Yes (heap); stack locals obey LIFO | Only for `External` / non-GC values without pinning | Type-error complexity across coupled dual axes; GC still manages `Global` heap |
| **Verona `Iso` Regions + BoC `when`** | Static ownership types + runtime `RegionBase` | Per-region (`Iso` root) | No global STW (local `RegionTrace` / `RegionArena`) | Yes (isolated inside region) | Safe inside `when` scope while cown holds exclusive ownership | Cross-region mutable references forbidden; requires `Freeze` or `when` handoff |
| **Extempore `EXTZones`** | Dynamic thread-local bump stack | Per-zone slab | No ($O(1)$ `offset=0` reset) | Yes (within zone) | Yes (raw 32-byte-aligned C pointers) | **Memory-unsafe**: no static escape check; `zone_extend` calls `malloc`; `memset` per alloc |
| **Cornucopia Reloaded (`CLG`)** | Hardware PTE bit + kernel fault handler | 4 KiB page | No (lazy fault-and-clean + async kproc) | Yes (arbitrary C/C++ heap) | Yes (native CHERI capabilities) | Sub-page false-sharing trap storm (47.4% at 1% density) unless segregated; needs CHERI/Morello HW |
| **Mill Pointer Events & Turfs** | Hardware pointer metadata + protection lookaside | Per-pointer / per-turf | No | Yes | Yes (hardware-checked) | No commercial silicon available (`unknown` real-world latency/power) |
| **Generational ZGC** | Software colored `zpointer` + JIT load/store barriers | Per-pointer (64-bit oop) | Sub-ms root sync only; concurrent relocation | Yes | **No** (raw deref sees color bits; requires uncolor/pin or copy) | 16-bit metadata tax + barrier code size + CAS contention on cold self-heal |
| **LLVM `gc.statepoint`** | Compiler IR rewrite + stackmap tables | Per-safepoint `(base, derived)` pair | Yes for STW relocation, or handshake per thread | Yes | Only if object pinned or copied to `addrspace(0)` | Stackmap bloat; optimization sensitivity for exterior derived pointers; no concurrent barrier alone |

## Boundaries

- **Not examined:** Hardware microarchitectural measurements of Linux `userfaultfd` write-protect (`UFFDIO_WRITEPROTECT`) latency distributions, Intel MPK (`pkey_mprotect` 16-domain thrashing), or CHERI compressed-bounds representability alignment (`CRRL`/`CRAM`) padding overhead were not directly executed in this study.
- **Not examined:** The exact OCaml compiler solver implementation of error-message minimization and type-error localization (`SHErrLoc`-style heuristics) inside `typing/mode.ml` (beyond `Mode.Crossing` and axis definitions) was not profiled on synthetic 6-axis or 9-axis benchmark suites.
- **Unknown:** Real-world silicon cycle latency, trap overhead, and power consumption of Mill Computing's Pointer Events (`US-9524163-B2`) and Turfs/Portals (`US-9747218-B2`) are unknown because no publicly benchmarkable Mill hardware exists.
- **Unknown:** Exact measured GC-to-RT swap-slot packing overhead for a concrete 1.33 ms audio DSP workload combining OxCaml `External` jkinds or Verona `RegionArena` with a concurrent tracing collector was not benchmarked; only the structural requirements (`EXTZones` zeroing/extension mechanics and copy-bandwidth bound) are derived.
- **Known not to apply:** Extempore's `EXTZones` (`digego/extempore@38bf1d24`) does **not** enforce static zero-outward-GC-pointer closure or thread-confinement safety; claims that `xtlang` zones provide statically verified memory safety are refuted by `include/EXTZones.h` L5–9.
- **Known not to apply:** Treating OxCaml's modal axes as linear chains does **not** apply to `Portability`, `Contention`, `Statefulness`, or `Visibility` in `oxcaml/oxcaml@0cfb4ab8`, all four of which are 4-element `Diamond` lattices (`typing/mode.ml` L599–769).
- **Unsupported:** Generational ZGC's overlapping-zero single-shift x86-64 load-barrier encoding is explicitly not used on AArch64 (`zAddress.hpp` L92–106), and LLVM `gc.statepoint` cannot safely track or relocate raw `addrspace(0)` pointers passed across opaque C FFI boundaries without explicit pinning or external handle indirection.
- **Stronger conclusion avoided:** While factorized per-axis solving + Galois mode crossing keeps **constraint solving** linear in the number of axes when cross-axis interactions stay sparse, this evidence does *not* establish that arbitrary 6+ axis modal systems remain ergonomic for human programmers without carefully engineered default-projection printing and modal polymorphism syntax.

## Evidence

### Primary Git Source References (Observed 2026-11-19)

1. **`oxcaml/oxcaml` @ `0cfb4ab854af0395cbbcf4e7dbdd6c2e7a9c62c1`**
   - `typing/mode_intf.mli` L423–650: Definitions of `Locality`, `Regionality`, `Linearity`, `Portability`, `Uniqueness`, `Contention`, `Forkable`, `Yielding`, `Statefulness`, `Visibility`, `Staticity`, and `Axis` (`Comonadic` vs. `Monadic`).
   - `typing/mode.ml` L599–800: Exact `Diamond` functor encodings (`0b00..0b11`) for `Portability`, `Contention`, `Statefulness`, `Visibility`, and `Total` encoding for `Staticity`.
   - `typing/mode.ml` L8514–8542: `module Crossing` specification of monotone mode-crossing map $f$ with left/right Galois adjoints $f_l, f_r$.
   - `typing/jkind_axis.mli` L27–120: `Externality`, `Nullability`, `Separability`, `upper_bound_if_is_always_gc_ignorable`, and `Axis_set` (`type t [@@immediate]`).
2. **`microsoft/verona-rt` @ `5cb8e8cf3699fa53c8a9b8dc34e4431c40d6230f`**
   - `src/rt/region/region.h` L15–115: `RegionBase`, `Iso` root model, remembered set, external reference table, `RegionType::{Trace, Arena, Rc}`.
   - `src/rt/region/region_trace.h` L35–90: `RegionTrace` dual trivial/non-trivial circular ring lists (`next_not_root`, `last_not_root`) for $O(1)$ merge and local trace-based cycle collection.
   - `src/rt/region/freeze.h`: Deeply immutable freezing of isolated regions.
   - `src/rt/cpp/when.h` L26–149: `acquired_cown_span`, `Batch` atomic scheduling, `When` multi-cown acquisition.
3. **`digego/extempore` @ `38bf1d2444a6166371c17abfa40dfa58f6ab962e`**
   - `include/EXTZones.h` L5–43: Thread-confinement caveat (zero locks, caller bug on sharing), `llvm_zone_t` layout, `LLVM_ZONE_ALIGN = 32`.
   - `src/EXTZones.cpp` L28, L94–176, L256–314: `tls_llvm_zone_stack`, `llvm_zone_reset` (with ASan `ZONE_POISON`), `zone_extend` (doubling via `_aligned_malloc`), `llvm_zone_malloc` (`memset` zeroing + 32 B size header), `llvm_zone_callback_setup` (1 MiB callback zone).
4. **`CTSRD-CHERI/cheribsd` @ `88f39900c32928d807dba245fba138808c666f34`**
   - `sys/cheri/revoke.h` L46–86, L211–326: `cheri_revoke_epoch_t`, `cheri_revoke_epoch_clears` parity rule (`then + (then & 1) + 2`), `cheri_revoke_stats` CLG counters, `cheri_revoke_epochs`.
   - `sys/vm/vm_cheri_revoke.c` L118–219, L389–424, L592–628: Async epoch parity assertions, `vm_cheri_revoke_kproc`, `vm_cheri_revoke_fault_visit`, `pmap_caploadgen_update` (`PMAP_CAPLOADGEN_ALREADY`, `PMAP_CAPLOADGEN_CLEAN` via `PGA_CAPSTORE`).
5. **`openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043`**
   - `src/hotspot/share/gc/z/zAddress.hpp` L48–264: 16-bit low-order `zpointer` layout (`RRRRMMmmFFrr0000`), x86-64 overlapping-zero shift vs. AArch64 complemented remap bits, `ZPointerLoadShiftTable`.
   - `src/hotspot/share/gc/z/zBarrier.inline.hpp` L37–95: `ZBarrier::assert_transition_monotonicity`, `ZBarrier::self_heal` relaxed CAS loop.
6. **`llvm/llvm-project` @ `c078d7b6876e6f21c0162671374939016b174c94`**
   - `llvm/docs/Statepoints.md` L34–47, L179–205, L299–315: Base, interior derived, and exterior derived pointers; `@llvm.experimental.gc.statepoint` `"gc-live"` bundles and `@llvm.experimental.gc.relocate`.

### Published Literature & Patent Specifications

- Anton Lorenzen, Leo White, Stephen Dolan, Richard A. Eisenberg, Sam Lindley. *Oxidizing OCaml with Modal Memory Management*. PACMPL 8 (ICFP 2024), Article 253. DOI: `10.1145/3674642`.
- Aïna Linn Georges, Benjamin Peters, Laila Elbeheiry, Leo White, Stephen Dolan, Richard A. Eisenberg, Chris Casinghino, François Pottier, Derek Dreyer. *Data Race Freedom à la Mode*. PACMPL 9 (POPL 2025), Article 23. DOI: `10.1145/3704859`.
- Andreas Abel, Jean-Philippe Bernardy. *A Unified View of Modalities in Type Systems*. PACMPL 4 (ICFP 2020), Article 90. DOI: `10.1145/3408972`.
- Luke Cheeseman, Matthew J. Parkinson, Sylvan Clebsch, Marios Kogias, Sophia Drossopoulou, David Chisnall, Tobias Wrigstad, Paul Liétar. *When Concurrency Matters: Behaviour-Oriented Concurrency*. PACMPL 7 (OOPSLA2 2023). DOI: `10.1145/3622852`.
- Nathaniel Wesley Filardo et al. *Cornucopia Reloaded: Load Barriers for CHERI Heap Temporal Safety*. ASPLOS 2024. DOI: `10.1145/3620665.3640416`.
- Mill Computing, Inc. U.S. Patent `9,524,163` (*Computer processor employing hardware-based pointer processing*) and U.S. Patent `9,747,218` (*CPU security mechanisms employing thread-specific protection domains*).

### Executable Probe and Recorded Output (`Basis: execution`, 2026-11-19)

Command: `python3 /tmp/p1_modal_and_barrier_probe.py` (Python 3, Linux x86-64). Standalone probe source:

```python
import math
from itertools import product

def diamond_le(a, b): return (a & b) == a
def diamond_join(a, b): return a | b
def diamond_meet(a, b): return a & b

DIAMOND = [0b00, 0b01, 0b10, 0b11]
PORT_NAMES = {0b00: "Portable", 0b01: "Shareable", 0b10: "Corruptible", 0b11: "Nonportable"}

axes_locality = {
    "Locality": 2, "Linearity": 2, "Portability": 4, "Yielding": 2, "Statefulness": 4,
    "Uniqueness": 2, "Contention": 4, "Visibility": 4, "Staticity": 2,
}
axes_regionality = dict(axes_locality, Locality=3)
print(f"[Part A] OxCaml 9-axis product size (Locality):    {math.prod(axes_locality.values()):,}")
print(f"[Part A] OxCaml 9-axis product size (Regionality): {math.prod(axes_regionality.values()):,}")
print(f"[Part A] Factorized sum of per-axis states:        {sum(axes_regionality.values())} "
      f"(ratio {math.prod(axes_regionality.values())/sum(axes_regionality.values()):.1f}x reduction)")

f = {0b00: 0, 0b01: 0, 0b10: 1, 0b11: 1}
fl, fr = {}, {}
for y in [0, 1]:
    acc = 0b11
    for m in DIAMOND:
        if y <= f[m]: acc = diamond_meet(acc, m)
    fl[y] = acc
    acc = 0b00
    for m in DIAMOND:
        if f[m] <= y: acc = diamond_join(acc, m)
    fr[y] = acc

galois_ok = all((f[m1] <= f[m2]) == diamond_le(fl[f[m1]], m2) == diamond_le(m1, fr[f[m2]])
                for m1, m2 in product(DIAMOND, DIAMOND))
print(f"[Part A] Galois adjoint law on Diamond: {galois_ok}")
print(f"         fl o f = {{ {', '.join(f'{PORT_NAMES[k]}->{PORT_NAMES[fl[f[k]]]}' for k in DIAMOND)} }}")
print(f"         fr o f = {{ {', '.join(f'{PORT_NAMES[k]}->{PORT_NAMES[fr[f[k]]]}' for k in DIAMOND)} }}")

K = 64
for p in [0.001, 0.005, 0.01, 0.02, 0.05, 0.10]:
    p_trap = 1.0 - (1.0 - p) ** K
    print(f"  pinned_frac={p*100:5.2f}% -> unsegregated={p_trap*100:6.2f}% | segregated_unpinned=0.00%")
```

Observed stdout:

```text
[Part A] OxCaml 9-axis product size (Locality):    8,192
[Part A] OxCaml 9-axis product size (Regionality): 12,288
[Part A] Factorized sum of per-axis states:        27 (ratio 455.1x reduction)
[Part A] Galois adjoint law on Diamond: True
         fl o f = { Portable->Portable, Shareable->Portable, Corruptible->Corruptible, Nonportable->Corruptible }
         fr o f = { Portable->Shareable, Shareable->Shareable, Corruptible->Nonportable, Nonportable->Nonportable }
  pinned_frac= 0.10% -> unsegregated=  6.20% | segregated_unpinned=0.00%
  pinned_frac= 0.50% -> unsegregated= 27.44% | segregated_unpinned=0.00%
  pinned_frac= 1.00% -> unsegregated= 47.44% | segregated_unpinned=0.00%
  pinned_frac= 2.00% -> unsegregated= 72.55% | segregated_unpinned=0.00%
  pinned_frac= 5.00% -> unsegregated= 96.25% | segregated_unpinned=0.00%
  pinned_frac=10.00% -> unsegregated= 99.88% | segregated_unpinned=0.00%
```

## Revalidation

1. **OxCaml modal axis count and crossing laws:** Diff `typing/mode_intf.mli` (`module Axis`), `typing/mode.ml` (`Diamond` axis modules and `module Crossing`), and `typing/jkind_axis.mli` against `oxcaml/oxcaml@0cfb4ab854af0395cbbcf4e7dbdd6c2e7a9c62c1`. Any new modal axis or non-adjoint crossing map immediately alters the product cardinality and factorization argument.
2. **Verona regions and Extempore zones:** Diff `src/rt/region/region.h` and `src/rt/region/region_trace.h` in `microsoft/verona-rt` against `5cb8e8cf3699fa53c8a9b8dc34e4431c40d6230f`, and `include/EXTZones.h` / `src/EXTZones.cpp` in `digego/extempore` against `38bf1d2444a6166371c17abfa40dfa58f6ab962e` (specifically checking whether `xtlang` adds static escape analysis or lock-free cross-thread zone handles).
3. **CheriBSD CLG barriers and Generational ZGC pointer layout:** Diff `sys/cheri/revoke.h` (`cheri_revoke_epoch_clears`) and `sys/vm/vm_cheri_revoke.c` (`vm_cheri_revoke_fault_visit`, `pmap_caploadgen_update`) in `CTSRD-CHERI/cheribsd`, and `src/hotspot/share/gc/z/zAddress.hpp` (`ZPointer*Mask`) and `zBarrier.inline.hpp` (`self_heal`) in `openjdk/jdk`.
4. **LLVM statepoints:** Diff `llvm/docs/Statepoints.md` and `llvm/lib/Transforms/Scalar/RewriteStatepointsForGC.cpp` in `llvm/llvm-project` to check whether exterior derived-pointer relocation or `gc.statepoint` bundle syntax changes.
5. **Algebraic and page-collision probe:** Re-run the embedded Python script above with updated axis cardinalities or target object/page sizes ($K = \text{PageSize}/\text{ObjSize}$) to recompute product-vs-factorized ratios and false-sharing trap probabilities.
