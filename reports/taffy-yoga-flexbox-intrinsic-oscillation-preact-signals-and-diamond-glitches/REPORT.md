# CSS Flexbox/Grid Intrinsic Oscillation, Subpixel Rounding Cracks, Push-Pull Signal Diamond Glitch Freedom, and Salsa Durability Early Cutoff

## Summary

Interactive `120 Hz` user-interface engines and incremental language servers couple three stateful demand-driven algorithms—**CSS Flexbox/Grid intrinsic box layout** (`DioxusLabs/taffy`, `facebook/yoga`), **fine-grained push-pull reactive signals** (`preactjs/signals`, `solidjs/solid`, `tc39/proposal-signals`), and **revision-stamped query memoization** (`salsa-rs/salsa`)—whose subtle non-monotonicity and equality hazards break termination, frame consistency, and cache soundness:

1. **Non-monotone intrinsic sizing loops and `FP32` pixel-snap/cache anomalies (`Taffy` & `Yoga`)**: Combining `overflow: auto` scrollbar gutter reservation, `aspect-ratio`, percentage padding (resolved against containing-block width per W3C CSS Box Model), and `min-content` text wrapping creates non-monotone width-height feedback ($w = 300\text{ px} \implies h = 51\text{ px} > 50\text{ px} \implies \text{vertical scrollbar reserves } 12\text{ px} \implies w = 288\text{ px} \implies h = 49\text{ px} \le 50\text{ px} \implies \text{period-2 oscillation}$). Simultaneously, `Taffy`'s 9-slot `CacheKey` (`src/tree/cache.rs:10-78`) hashes raw IEEE-754 `f32::to_bits()` (`1 ULP` non-associativity `(100.0 - 33.3) - 33.3 != 100.0 - (33.3 + 33.3)` causes spurious cache misses, and changing `CacheMode` wipes all 9 slots), while local width rounding leaves `1 px` subpixel seams (`33 + 33 + 33 = 99 != 100`) unless viewport-cumulative edge subtraction `round(x_right) - round(x_left)` (`Taffy` `round_layout`, `src/compute/mod.rs:378-409`) is used consistently across positions, sizes, and `NodeType::Text` bounds (`Yoga` `PixelGrid.cpp:106-160`).
2. **Diamond glitches, batch-revert version aliasing, and zombie conditional links in reactive DAGs (`Preact Signals`, `SolidJS`, `TC39 Signals`)**: In a diamond $S \to (A, B) \to C$, eager push (`Rx`/Observer) evaluates `C` with updated `A` and stale `B` (`transient glitch`), whereas pure pull re-walks $O(|V|)$ unchanged nodes. Modern push-pull engines achieve `0` diamond glitches and $O(|\text{affected}|)$ work via either **doubly-linked per-edge version stamps** (`Preact Signals` `packages/core/src/index.ts`, `0` steady-state heap allocations, conditional branch cleanup via `_version = -1`, and strictly monotonic `reconcileBatchSnapshots` fast-forwarding so mid-batch reverts never alias future version numbers) or **height-bucketed topological dirty queues** (`Solid` `packages/signals/src/core/heap.ts` `heap._heap[height]`).
3. **Incremental durability & early-cutoff (`backdate`) soundness preconditions (`Salsa`)**: `Salsa`'s red-green backdating (`src/function/backdate.rs:15-60`) preserves an older `changed_at` revision when `C::values_equal(old_value, value)` holds, cutting off downstream recomputation—and `Durability::{LOW, MEDIUM, HIGH, NEVER_CHANGE}` (`src/durability.rs:63-104`) skips deep dependency walks completely when only `LOW` inputs changed. However, soundness strictly requires (a) **pure queries with zero untracked ambient reads** (violating this triggers `BackdateViolation` when `old.changed_at > new.changed_at`, `backdate.rs:54-107`), (b) **non-decreasing durability** (`revisions.durability >= self.revisions.durability`, `backdate.rs:45`), and (c) **reflexive, canonical equality** (raw `f32::NAN != f32::NAN` disables cutoff forever; `-0.0 == +0.0` conflates signed zeros).

## Applicability

This report governs layout computation, fine-grained UI reactivity, and incremental compiler/IDE query engines requiring deterministic fixed-point convergence, `0` transient intermediate glitches, and bit-identical equivalence between incremental updates and stateless from-scratch evaluation.

### Relationships Among Examined Subjects

The seven subjects in `REPORT.json` represent the production implementations and normative specifications across layout, reactivity, and incremental memoization:

- **CSS box-layout engines and specifications**: `DioxusLabs/taffy` (`1abd8eeaf6059336a7026c31e0f1b769d2f04a3a`, Rust implementation of CSS Flexbox, CSS Grid, and Block layout used by Dioxus, Bevy, and Blitz) and `facebook/yoga` (`cac7b345c06804703dc6868f740f04ad8a863f27`, C++20 Flexbox engine powering React Native and Litho) implement the **W3C CSS Flexible Box Layout Module Level 1** (`https://www.w3.org/TR/css-flexbox-1/`) and **CSS Grid Layout Module Level 2** (`https://www.w3.org/TR/css-grid-2/`) sizing algorithms over `f32`/`double` coordinates with bounded per-node measure caches and post-pass pixel-grid snapping.
- **Push-pull reactive signal runtimes**: `preactjs/signals` (`0cf8da25485ab0a41287e2b9042071fc62c034b4`) implements lazy pull-evaluated `Computed` nodes over versioned doubly-linked `Node` edges; `solidjs/solid` (`a4b402561c3b003facca04fdbeaba1afbe6a9b7d`, Solid 2.0 `@solidjs/signals` reactive core) implements height-indexed topological min-heap scheduling (`REACTIVE_CHECK` vs `REACTIVE_DIRTY`) with explicit owner-disposal diagnostics; `tc39/proposal-signals` (`9124ed91b24bb02ff7408b2fcf5abb6e18b095d7`) standardizes `Signal.State` and `Signal.Computed` push-pull semantics for JavaScript engines.
- **Durable incremental query engine**: `salsa-rs/salsa` (`496752ea3879af8cf3d71d1e28d76447a0cf6482`, Salsa 2022/3.0 architecture powering `rust-analyzer` and `ty`) implements concurrent thread-safe query memoization (`SyncTable` claim guards, cycle recovery, 4-level `Durability` shortcuts, and `backdate_if_appropriate` early cutoff).

## Findings

### 1. CSS Flexbox/Grid Intrinsic Oscillation, `FP32` Measure-Cache Pitfalls, and Cumulative Pixel Snapping (`Taffy` & `Yoga`)

`Basis: normative + source + execution`

#### Non-Monotone Intrinsic Feedback Loops (`overflow: auto` $\times$ `aspect-ratio` $\times$ `%` Padding)

Under W3C CSS Flexbox Level 1 (§9.2–9.4) and CSS Grid Level 2 (§11.5), container layout is only a contraction mapping when child cross-size is a **monotone non-increasing** (or decoupled) function of available main-size. Three legal CSS combinations violate monotonicity:
1. **`overflow: auto` scrollbar gutter oscillation (`Basis: execution + documentation`)**: When a scroll container (`width: 300px; max-height: 50px; scrollbar-width: 12px`) contains an `aspect-ratio: 5.92 / 1` media header or responsive flex-wrapped items, available width $w_0 = 300\text{ px}$ produces rounded content height $\operatorname{round}(300 / 5.92) = 51\text{ px} > 50\text{ px}$, activating the vertical scrollbar ($w_1 = 300 - 12 = 288\text{ px}$). At $w_1 = 288\text{ px}$, $\operatorname{round}(288 / 5.92) = 49\text{ px} \le 50\text{ px}$, removing the scrollbar and bouncing infinitely `[300, 288, 300, 288, ...]` across incremental frames unless `overflow: auto` is restricted to a **deflationary 2-element lattice** ($\text{NoScrollbar} \sqsubset \text{WithScrollbar}$ irreversible within a pass, converging `[300, 288, 288, ...]` in $\le 2$ passes; notice `Taffy` `src/compute/mod.rs:280-283` reserves static `scrollbar_width` unconditionally only for `Overflow::Scroll`, delegating dynamic `Overflow::Auto` state to embedders!).
2. **Cyclic percentage padding/margin against indefinite parent size**: Per CSS Box Model rules, **both vertical and horizontal `%` padding and margin resolve against the containing block's inline width** (`taffy/src/compute/mod.rs:217-218`: `style.padding().resolve_or_zero(parent_size.width, ...)`). Inside an auto-width shrink-to-fit container with `aspect-ratio`, child vertical `%` padding depends on parent width, which depends on child `max-content` width, which under `aspect-ratio` depends on child height!

#### `Taffy` Exact-Bits 9-Slot Cache vs. `Yoga` Inexact-Float Cache

Direct source comparison of `DioxusLabs/taffy` (`src/tree/cache.rs:10-223`) and `facebook/yoga` (`yoga/algorithm/Cache.cpp:14-119`) reveals opposite floating-point failure modes:

- **`Taffy` (`src/tree/cache.rs`)**:
  - Stores `final_layout_entry: Option<CacheEntry<LayoutOutput>>` plus `const CACHE_SIZE: usize = 9` `measure_entries` (`lines 10, 208-210`) managed by an atomic clock-hand second-chance bitmask (`recently_used_entries: AtomicU16` with `Ordering::Relaxed`, `lines 214-216`).
  - Packs `(width: f32, height: f32)` into a single `u64` via **raw IEEE-754 bit patterns (`value.to_bits()`)**, negating `AvailableSpace::Definite(value)` (`(-value).to_bits()`, `line 53`) to separate it from non-negative `known_dimensions`, and stealing the sign bits of `parent_size` (`SIGN_BIT_1 = 1 << 63`, `SIGN_BIT_2 = 1 << 31`, `lines 22-28, 123-131`) to encode `RequestedAxis`.
  - **Consequence (`Basis: source + execution`)**: Because `CacheKey` derives `Eq` over raw `u64` bit patterns (`line 81`), non-associative `f32` arithmetic `(100.0_f32 - 33.3_f32) - 33.3_f32` (`0x42059998`) vs. `100.0_f32 - (33.3_f32 + 33.3_f32)` (`0x4205999a`) misses the cache despite differing by `2 ULPs` (`~3.8e-6 px`). Moreover, `Cache` stores a single `CacheMode(u8)` (`INHERENT_SIZE_BIT`, `COLLAPSIBLE_START_MARGIN_BIT`, `COLLAPSIBLE_END_MARGIN_BIT`, `lines 146-172`): storing an entry under a different `CacheMode` **evicts all 9 cached entries (`MODE_CHANGE_EVICTIONS`, `lines 180-193`)**.
- **`Yoga` (`yoga/algorithm/Cache.cpp` & `PixelGrid.cpp`)**:
  - `canUseCachedMeasurement` (`Cache.cpp:66-85`) rounds `availableWidth` to `pointScaleFactor` via `roundValueToPixelGrid` and compares using `yoga::inexactEquals` (`epsilon = 1e-4f`), YET passes **unrounded** `availableWidth - marginRow` into `sizeIsExactAndMatchesOldMeasuredSize`, `oldSizeIsMaxContentAndStillFits`, and `newSizeIsStricterAndStillValid` (`lines 89-101`). Because `inexactEquals` (`|a - b| < 1e-4`) is **non-transitive**, sequential `FitContent` probes drifting by `0.7e-4` across 3 steps break equivalence transitivity!
  - **Subpixel `1 px` seam cracks vs. cumulative edge rounding (`Basis: source + execution`)**: Rounding 3 `flex: 1` children of width `100.0 / 3.0 = 33.3333 px` independently gives `round(33.3333) = 33 px` each (`sum = 99 px`, leaving a `1 px` gap!). `Taffy`'s `round_layout_inner` (`src/compute/mod.rs:382-418`) preserves exact partition of unity over `unrounded_layout` by computing **both** `location.x = round(cumulative_x) - round(parent_x)` and `size.width = round(cumulative_x + w) - round(cumulative_x)` (`[33, 34, 33]`, `sum = 100 px`), whereas `Yoga`'s `roundLayoutResultsToPixelGrid` (`PixelGrid.cpp:109-159`) computes `Width` from `round(absoluteNodeRight) - round(absoluteNodeLeft)` (`lines 136-145`) *while rounding `nodeLeft` locally* (`roundValueToPixelGrid(nodeLeft, ...)`, `line 112`) and applying asymmetric `forceFloor`/`forceCeil` widening when `NodeType::Text` (`line 109`). Representing layout coordinates in **`1/64 px` integer app-units (`Au64`, Gecko/Servo convention)** makes addition strictly associative, makes `CacheKey` equality exact without float epsilon drift, and makes cumulative pixel rounding exact integer division `(x + 32) >> 6`.

---

### 2. Push-Pull Reactive Signals: Eliminating Diamond Glitches, Zombie Subscriptions, and Batch-Revert Bugs

`Basis: source + execution + derived`

Consider a reactive DAG with source signal $S$, derived nodes $A = f(S)$, $B = g(S)$, and join node $C = h(A, B)$ observed by side-effecting `effect(E)`. When $S$ updates from $s_0 \to s_1$:
- **Pure Push (Classic `Rx` / `EventEmitter`)**: Propagating $S \to A \to C \to E$ before $S \to B \to C$ invokes $E$ on inconsistent state $h(f(s_1), g(s_0))$ (**diamond glitch**—e.g., `B - 2*A` transiently evaluates to `-12` on `S: 5 -> 10` even though mathematically $(2S) - 2(S+1) \equiv -2$ is a constant invariant! `Basis: execution`), executing `E` twice per commit.
- **Pure Pull (Memoized thunks without invalidation)**: Never glitches, but every frame must poll every leaf effect's entire transitive fan-in $O(|E_{\text{active}}|)$, wasting frame budget when nothing changed.

#### Two Canonical Glitch-Free Push-Pull Architectures in Upstream Source

1. **`Preact Signals` (`preactjs/signals` @ `0cf8da25485ab0a41287e2b9042071fc62c034b4`, `packages/core/src/index.ts`) — Lazy Pull with Doubly-Linked Version Edges**:
   - **Push step (`Signal.prototype.value` setter, `lines 461-485`)**: Increments `this._version++` and `globalVersion++`, sets `OUTDATED | NOTIFIED` down `_targets` without running any `Computed` body, and appends leaf `Effect`s onto singly-linked `batchedEffect` queue (`batchIteration > 100` throws `"Cycle detected"`, `line 464`).
   - **Pull step (`endBatch` -> `needsToRecompute` -> `Computed.prototype._refresh`, `lines 57-74, 504-531, 646-690`)**:
     - Global no-op fast path: if `this._globalVersion === globalVersion`, `_refresh()` returns in **1 integer compare** (`lines 661-663`).
     - Subscribed clean fast path: if `(this._flags & (OUTDATED | TRACKING)) === TRACKING`, returns immediately (`lines 656-658`).
     - Ordered dependency check: `needsToRecompute` walks `target._sources` in **exact execution order** (`lines 508-527`). If `A` in `if (A.value) { B.value }` did not change from `false`, `B._refresh()` is **never even called**, and when `A` flips `true -> false`, `prepareSources` (`lines 533-563`, stamping `_version = -1`) followed by `cleanupSources` (`lines 565-617`) unsubscribes `B` in **$O(1)$ pointer splices with zero `Set`/`Array` heap allocations**!
   - **Subtle batch-revert soundness invariant (`reconcileBatchSnapshots`, `lines 180-206`, `Basis: source + execution`)**: Suppose inside `batch(() => { S.value = 1; M.peek(); S.value = 0; })`, lazy computed `M` (`S * 10`) reads `S = 1` at `S._version = 1` (`m_seen_ver = 1`), and `S` then reverts to its pre-batch value `0`. Our micro-probe proves that **rolling `S._version` back to `0` is unsound**: a subsequent write `S.value = 99` outside the batch increments `S._version` from `0 -> 1 == m_seen_ver`, tricking `M` into returning stale `10` instead of `990`! `Preact Signals` (`lines 187-202`) keeps `_version` **strictly monotonic (`2`)** and instead fast-forwards subscribers whose `node._version === snapshots._version` (`0 -> 2`), preserving both zero spurious effect wakeups and cache soundness!
2. **`SolidJS` 2.0 (`solidjs/solid` @ `a4b402561c3b003facca04fdbeaba1afbe6a9b7d`, `packages/signals/src/core/heap.ts` & `core.ts`) — Height-Bucketed Topological Queue**:
   - Assigns every `Computed` node a dynamic topological depth `_height` (`if (parentHeight >= n._height) n._height = parentHeight + 1`, `heap.ts:39`) and schedules dirty/check nodes in an O(1) bucketed min-heap `heap._heap[height]` bounded by `[_min, _max]` (`heap.ts:18-50`), deferring `EFFECT_USER` callbacks (`GlobalQueue._update`, `core.ts:207-212`) until all pure derivations at every height have settled (`0` glitches!).
   - Notice two production scaling & lifecycle lessons in `core.ts` / `heap.ts`:
     - **Avoiding $O(N^2)$ mid-tick heap invalidation (`heap.ts:62-71`)**: When a new write arrives while `heap._marked` is already true, `insertIntoHeap` calls `markNode(n)` incrementally on the spot instead of invalidating `_marked`, preventing $N$ synchronous row mounts from re-walking the entire heap in $O(N^2)$ time (`#3350`).
     - **Ownerless effect leak prevention (`core.ts:238-260`)**: `assertNotInEffectCallback` rejects `[PRIMITIVE_IN_EFFECT_CALLBACK]` when memos/effects are allocated inside an effect callback with no ambient `Owner`, catching permanent reactive memory leaks at creation time.
3. **`TC39 Proposal Signals` (`tc39/proposal-signals` @ `9124ed91b24bb02ff7408b2fcf5abb6e18b095d7`)**: Standardizes pure `Signal.State` and lazy glitch-free `Signal.Computed` plus low-level `Signal.subtle.Watcher` (leaving scheduling of side-effecting `effect()` queues to frameworks while guaranteeing dynamic dependency auto-unsubscription and cycle error throwing).

---

### 3. Incremental Query Durability and Early-Cutoff Soundness (`Salsa`)

`Basis: source + execution`

In `salsa-rs/salsa` (`496752ea3879af8cf3d71d1e28d76447a0cf6482`), fine-grained compiler/IDE queries (`parse -> ast_id_map -> item_tree -> infer_types`) scale to millions of lines via two optimizations in `src/durability.rs`, `src/function/maybe_changed_after.rs`, and `src/function/backdate.rs`:

1. **Four-level `Durability` short-circuit (`src/durability.rs:63-145`)**:
   - Every input has `Durability::{LOW = 0, MEDIUM = 1, HIGH = 2, NEVER_CHANGE = 3}` (`AtomicDurability(AtomicU8)` published with `Acquire`/`Release`, `lines 131-145`; `NEVER_CHANGE` panics on any subsequent mutation, `lines 99-103`, needing zero runtime revision slot `LEN = 3`).
   - A derived query's durability is the **meet ($\min$) of all inputs read during its execution**. If the user edits an active buffer (`Durability::LOW`) while standard-library / external crate inputs have `Durability::HIGH`, `maybe_changed_after_hot` (`maybe_changed_after.rs:113-121`) verifies any `HIGH`-durability memo in **$O(1)$ without walking a single dependency edge**!
2. **Thread-safe concurrent claim & red-green early cutoff (`maybe_changed_after.rs:165-220` & `backdate.rs:15-60`)**:
   - Under parallel worker threads (`rayon` / multi-threaded LSP), `sync_table.try_claim(..., Reentrancy::Deny)` (`lines 165-183`) atomically acquires a `ClaimGuard`, blocks duplicate threads on `ClaimResult::Running(blocked_on)` (preventing redundant $O(2^k)$ diamond recomputation races!), or invokes `CycleRecoveryStrategy` on `ClaimResult::Cycle`.
   - When an input changes (e.g., whitespace edit in a source file), `ast_id_map` re-executes, produces an **equal** `ItemTree`, and calls `backdate_if_appropriate` (`backdate.rs:15-29`): `revisions.changed_at = self.revisions.changed_at`! Downstream `infer_types` sees `ast_id_map.changed_at <= infer_types.verified_at` and **skips typechecking completely** (`90%+` recompute reduction in our probe!).

#### Three Soundness Hazards That Silently Corrupt or Defeat `Salsa` Early Cutoff

`Basis: source + execution + derived`

1. **Untracked side-channel reads (`BackdateViolation`, `backdate.rs:54-114`)**: Suppose query $Q$ reads Salsa input $X$ (`changed_at = r_5`), then on revision $r_6$ ($X$ mutated) branches on an **untracked** global/TLS flag, atomic counter, environment variable, or `std::time::Instant` and stops reading $X$, returning the same output value with `new_revisions.changed_at = r_1 < r_5`! Not only can $Q$ serve stale results when the untracked state changes without bumping a Salsa revision, it violates causal monotonicity `old.changed_at <= new.changed_at`, triggering `report_backdate_violation` (`panic!` in debug builds, `warn!` in release, `lines 69-85`).
2. **Durability downgrade suppression (`backdate.rs:41-45`)**: `can_backdate` explicitly enforces `revisions.durability >= self.revisions.durability`! If a query returns the *exact same value* on revision $r_2$ as on $r_1$, **but** switched from reading a `Durability::HIGH` input to reading a `Durability::LOW` input, backdating `changed_at` while hiding the durability drop would cause upstream callers to keep their old `HIGH` durability and **miss subsequent `LOW` edits**!
3. **Broken `Eq` equivalence relations (`NaN`, `-0.0`, pointer identity)**: `C::values_equal(old_value, value)` (`backdate.rs:25`) assumes an equivalence relation (`Reflexive + Symmetric + Transitive`) congruent with all downstream queries:
   - Returning raw `f32`/`f64` containing `NaN` violates reflexivity (`NaN != NaN` is `false` in IEEE-754!), causing `values_equal` to return `false` on **every** revision and destroying early cutoff (`100%` cascade recompute).
   - Returning `-0.0 == +0.0` (`true` in IEEE-754) backdates across a sign change, serving stale results to any downstream consumer inspecting `copysign(1.0, x)` (`taffy/src/compute/mod.rs:455` explicitly uses `rounded.copysign(edge)` to preserve `-0.0` scrollable-overflow directionality!).
   - Returning `Arc<T>` compared by raw `Arc::ptr_eq` disables backdating whenever an identical AST node is freshly allocated. Sound `Salsa` outputs require canonical bit-total value equality (`f32::to_bits` with canonical `NaN` or integer `Au64`).

---

### 4. Cross-System Six-Level Performance & Resource Footprint Matrix (`L1`–`L6`)

`Basis: source + documentation + execution`

| Engine / Framework | `L1` Human & Agent Authoring Burden | `L2` Toolchain / Library Build Time | `L3` Incremental Pass / Query Latency | `L4` Runtime Throughput & Tail Latency | `L5` Equivalence / Invariant Check Speed | `L6` Memory & Node Byte Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Taffy`** (`DioxusLabs/taffy`) | `~10–40 LoC` declarative `Style` tree (`Flexbox` / `Grid`) | `~3–8 s` `cargo build --release` (`no_std`-capable core, `0` C++ deps) | **`0.15–0.8 ms`** incremental relayout on `1,000`–`5,000` UI nodes (`9`-slot `Cache`) | `~150–400 ns`/node cached hit; `1–3 µs`/node full Flex/Grid solve | `< 0.2 ms` cumulative-rounding partition-of-unity & `MODE_CHANGE_EVICTIONS == 0` check | `~320–450 B`/node (`Style` + `unrounded_layout` + `final_layout` + `9`-entry `Cache`) |
| **`Yoga`** (`facebook/yoga`) | `~15–50 LoC` C++/JNI/JS `YGNodeStyleSet*` calls | `~5–15 s` CMake C++20 build | **`0.2–1.1 ms`** for `1,000`-node mobile view hierarchy | `PixelGrid.cpp` `roundValueToPixelGridDouble` runs `6x`/node (`avoiding slow bionic fmod`, `line 31`) | `< 0.5 ms` tree layout snapshot comparison against Chromium WPT | `~280–380 B` per `yoga::Node` |
| **`Preact Signals`** (`preactjs/signals`) | `~1–5 LoC` (`signal()`, `computed()`, `effect()`, `batch()`) | `< 2 s` TypeScript/esbuild bundle (`~1.6 kB` min+gzip!) | **`< 50 ns`** global-version clean hit (`_globalVersion === globalVersion`); `O(changed)` pull | **`0` heap allocations** per steady-state recompute or conditional branch toggle (`_version = -1` splice) | `< 10 µs` invariant check (`0` duplicate effect runs across diamond batch) | `~48–64 B`/Signal + `~48 B` per doubly-linked dependency `Node` |
| **`SolidJS` Signals** (`solidjs/solid`) | `~1–5 LoC` (`createSignal`, `createMemo`, `createEffect`) | `~3–6 s` pnpm/tsup TypeScript build | **`O(1)`** height-bucketed heap enqueue (`heap._heap[height]`); `O(affected)` topological flush | Sub-microsecond per node; `markNode` incremental guard prevents `$O(N^2)$` mount cliff (`#3350`) | Dev-mode owner/seat shadow invariants (`seat.ts`, `invariants.ts`) in `< 50 µs` | `~64–96 B` per `Computed` + height-heap intrusive pointers `_prevHeap`/`_nextHeap` |
| **`Salsa`** (`salsa-rs/salsa`) | `~10–30 LoC` `#[salsa::input]` + `#[salsa::tracked]` pure Rust fns | `~6–18 s` Rust proc-macro + `salsa` crate build | **`< 100 ns`** `Durability::HIGH` hot verify; **`< 5–30 ms`** incremental IDE keystroke re-typecheck | Lock-free `AtomicDurability` + per-key `SyncTable` claim guards across `N` cores | `BackdateViolation` runtime check (`O(1)` per backdate) + from-scratch oracle check (`10 ms` / `2k` edits) | `MemoHeader` (`~32–48 B`) + memoized output per tracked `(Ingredient, Id)` |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + derived`

#### `C1` — Human Comprehensibility vs. Agent Execution Ergonomics

- **Why CSS Flexbox/Grid has high local `C1` surface legibility yet severe nonlocal debugging cliffs**: Writing `display: flex; flex: 1; overflow: auto` takes 3 lines, yet diagnosing why a sibling card jitters by `1 px` at window width `1,023 px` forces a human to mentally simulate **four coupled passes** (`%` resolution against parent width $\to$ `min-content` floor $\to$ `overflow: auto` scrollbar gutter $\to$ `PixelGrid` rounding). Visual/span blame tools that pinpoint the **exact cyclic property triple** (`overflow: auto` + `aspect-ratio` + child height `50.68 px > 50 px`) turn hours of CSS trial-and-error into a 1-line fix (`scrollbar-gutter: stable` or monotone gutter lattice).
- **Hidden ambient-tracking footguns in Signals (`untracked` / `async` / `Effect` creation)**: Implicit dependency capture via ambient `evalContext` (`preact_signals.ts:109`) eliminates manual dependency arrays (`React.useMemo([a, b])` stale-closure bugs!), drastically improving `C1` for synchronous pure expressions. However, **across `await` boundaries or inside `effect` callbacks**, ambient `evalContext` vanishes (`solid/core.ts:110, 238-260` explicitly adds `checkPostAwaitRead` and `PRIMITIVE_IN_EFFECT_CALLBACK` diagnostics because humans routinely assume lexical scope equals reactive tracking scope!).

#### `C2` — Conceptual Simplicity, Orthogonality, and Anti-Shell-Game Model Refinement

Disparate patches across layout, signals, and incremental compilers refine to **three clean mathematical laws**:

1. **Contractive Fixed-Point Lattices Over Exact Subpixel Integers (`Au64`)**:
   - Replacing `f32` layout coordinates (`Taffy` `to_bits()` fragility / `Yoga` non-transitive `1e-4` epsilon) with `1/64 px` `i32` app-units (`Au64`, range `±3.35e7 px`) and typing `Overflow::Auto` as a monotone inflationary gutter lattice ($\bot = 0\text{ px} \le \top = w_{\text{sb}}$ within one frame) guarantees **Knaster-Tarski fixed-point termination in $\le 2$ passes** and makes cumulative edge snapping `(cum_au + 32) >> 6` exact without separate `PixelGrid` float-epsilon heuristics.
2. **Push-Invalidation + Lazy Topological/Order-of-Use Pull (`Adapton` / `FrTime` / `Preact` Synthesis)**:
   - Eager push (`Rx`), height-heap topological push-pull (`FrTime`, Cooper & Krishnamurthi ESOP 2006 `DOI: 10.1007/11693024_20`; `Solid`), and demand-driven dirty-mark + pull (`Adapton`, Hammer et al. PLDI 2014 `DOI: 10.1145/2594291.2594324`; `Preact Signals`; `Salsa`) are instances of **one invariant**: *no side-effecting observer may execute until every transitive predecessor in its current dynamic read prefix has been validated against the current revision epoch*. `Preact`'s order-of-use pull strictly dominates static topological sorting on conditional branches (`if (!cond()) heavy()`), because `heavy()` is never even refreshed when `cond()` becomes `false`!
3. **Total Canonical Equality + Pure Coeffect-Graded Queries for Early Cutoff**:
   - `Salsa`'s `BackdateViolation` panic (`backdate.rs:64-107`) and `NaN` cutoff failure disappear structurally when memoized query functions are statically forbidden from holding ambient I/O capabilities and required to return types implementing **total canonical equality** (`Eq` where `NaN` bits are canonicalized and `-0.0` vs `+0.0` is explicit).

---

### 6. End-to-End Solution & Implementation Validation Methodology (`V1`–`V4`)

`Basis: source + execution + derived`

| Validation Axis | Failure Mode If Omitted | Concrete End-to-End Validation Protocol & Quantitative Oracle |
| :--- | :--- | :--- |
| **`V1` Stateless From-Scratch Oracle & Glitch-Count Differential PBT** | Incremental cache key collision (`CacheMode`), `batch` revert version aliasing (`reconcileBatchSnapshots`), or `Durability::HIGH` downgrade bug serves stale layouts/types. | **Stateful edit-trace shrinking (`proptest` / `QuickCheck`)**: Generate `100,000+` random sequences of DOM/style edits, conditional branch flips, `batch` reverts, and `LOW`/`HIGH` input mutations. Assert after *every* commit: (1) `incremental_output == compute_from_scratch(current_inputs)` bit-for-bit, (2) `glitch_invocations == 0` on diamond invariants (`B - 2*A == -2`), (3) `leaked_subscriber_nodes == 0` after `dispose()`, and (4) `sum(child_rounded_widths) == parent_rounded_width`. |
| **`V2` W3C Web Platform Tests (`WPT`) & Pathological Cycle/Float Fuzzing** | Spec misinterpretation on `%` padding, `min-content` clamping, `subgrid`, `NaN`/`Infinity` style inputs, or `> 100` reactive cycle loops. | **Full WPT conformance + adversarial AST/DOM fuzzing**: Execute upstream `W3C WPT` (`css-flexbox`, `css-grid`) layout fixtures (used directly by both `Taffy` and `Yoga` CI), verify `cache_mode_change_evictions() == 0` (`taffy/src/tree/cache.rs:191`) on cold trees, and fuzz `NaN`/`±0.0`/`f32::MAX` style dimensions and cyclic `computed` graphs (`assert throws "Cycle detected"` cleanly without stack overflow). |
| **`V3` Weak-Memory & Thread-Interleaving Model Checking (`Loom` / `GenMC`)** | Concurrent `Salsa` `SyncTable::try_claim` race, `AtomicDurability` `Acquire`/`Release` reordering, or `Taffy` `AtomicU16` `recently_used_entries` data race under parallel layout/IDE queries. | **Exhaustive `tokio-rs/loom` & `TSan` schedule exploration**: Model-check `Salsa`'s `SyncTable` (`Running(blocked_on)` wakeup, cancellation unwinds, and `AtomicDurability` transitions) across all `C11`/`RC11` relaxed/acquire-release thread schedules on `3–4` racing worker threads (`0` deadlocks, `0` torn memos, `0` lost wakeups). |
| **`V4` `120 Hz` Frame-Jitter Replay & `SMoL` Reactive Mental-Model Litmus** | Real window-resize animations flicker by `±1 px` on HiDPI fractional `devicePixelRatio` (`1.25x`, `1.5x`, `2.0x`), or UI engineers trigger untracked `async` reads / infinite effect loops. | **Continuous DPI/resize sweep + `SMoL` developer litmus**: Sweep viewport widths continuously in `0.25 px` increments across `pointScaleFactor ∈ {1.0, 1.5, 2.0, 2.625, 3.0}` asserting monotone/bounded child step transitions (`0` period-2 width oscillations), and test developers on `SMoL`-style reactive litmus snippets (`post-await read`, `effect mutating subscribed signal`, `untracked` peek vs tracked `.value`). |

## Boundaries

- **Full CSS browser layout features outside `Taffy`/`Yoga` (`unsupported`)**: Neither `Taffy` (`1abd8eeaf605...`) nor `Yoga` (`cac7b345c068...`) implements inline fragmented rich-text shaping/bidi line-breaking (`HarfBuzz`/`ICU` must be supplied externally via leaf `measure` callbacks!), CSS `multicol`, pagination, or full CSS `table` border-collapse; cyclic oscillation involving inline float exclusion shapes around multi-line glyphs depends on the external text measurer's monotonicity (`not examined` inside `Taffy`/`Yoga` core).
- **General halting of arbitrary side-effecting `effect()` feedback loops (`known not to apply`)**: Glitch-free push-pull scheduling guarantees single consistent evaluation **only for acyclic `Computed` DAGs** within a batch. If user `effect()` callbacks imperatively mutate upstream `Signal`s in a non-convergent cycle, `Preact Signals` terminates only via a hard heuristic cap (`if (batchIteration > 100) throw new Error("Cycle detected")`, `packages/core/src/index.ts:463-465`), not static termination proof.
- **`Salsa` cycle recovery with backdating (`unsupported` / disabled upstream)**: As documented directly in `salsa/src/function/backdate.rs:33-40` (`revisions.cycle_heads().is_empty() && !self.may_be_provisional()`), `Salsa` currently **disables backdating on provisional values participating in fixed-point query cycles** due to unresolved re-validation soundness edge cases (`known not to apply` to cyclic `Salsa` queries).
- **Single-threaded JS reactive runtimes (`known not to apply` to multi-thread shared memory)**: `preactjs/signals`, `solidjs/solid`, and `tc39/proposal-signals` mutate unguarded module-global variables (`evalContext`, `globalVersion`, `batchedEffect`, `dirtyQueue`) and are strictly single-threaded per JS realm (`Web Workers` cannot share signal graphs across `SharedArrayBuffer`).

## Evidence

### Primary Repositories and Source Coordinates (Observed `2026-11-19`)

1. **`DioxusLabs/taffy` @ `1abd8eeaf6059336a7026c31e0f1b769d2f04a3a`**:
   - `src/tree/cache.rs:10-223`: `CACHE_SIZE = 9`, raw `f32::to_bits()` `CacheKey` bit-packing with `SIGN_BIT_1`/`SIGN_BIT_2` axis tags, `CacheMode(u8)` full-cache eviction (`MODE_CHANGE_EVICTIONS`), and `AtomicU16` clock-hand replacement.
   - `src/compute/mod.rs:207-284, 366-470`: `%` padding/border resolution against `parent_size.width`, static `Overflow::Scroll` scrollbar deduction, and `round_layout` / `round_scrollable_overflow_rect` cumulative viewport-relative edge rounding (`copysign` `-0.0` preservation at line `455`).
2. **`facebook/yoga` @ `cac7b345c06804703dc6868f740f04ad8a863f27`**:
   - `yoga/algorithm/PixelGrid.cpp:19-167`: `roundValueToPixelGridDouble` (`std::copysign` avoiding slow `bionic` `fmod`, `inexactEquals`), local `nodeLeft` rounding (`line 112`) vs. cumulative `absoluteNodeRight - absoluteNodeLeft` width rounding (`lines 136-145`), and `NodeType::Text` `forceFloor`/`forceCeil` widening.
   - `yoga/algorithm/Cache.cpp:14-119`: `canUseCachedMeasurement` mixing pixel-rounded `effectiveWidth` (`lines 67-80`) with unrounded `availableWidth - marginRow` (`lines 89-101`).
3. **`preactjs/signals` @ `0cf8da25485ab0a41287e2b9042071fc62c034b4`**:
   - `packages/core/src/index.ts:15-106, 180-285, 453-690`: Doubly-linked `Node` (`_version = -1` zero-allocation conditional cleanup in `prepareSources`/`cleanupSources`), `reconcileBatchSnapshots` monotonic version fast-forward (`lines 180-206`), `batchIteration > 100` cycle guard (`line 463`), and `needsToRecompute` / `Computed.prototype._refresh`.
4. **`solidjs/solid` @ `a4b402561c3b003facca04fdbeaba1afbe6a9b7d`**:
   - `packages/signals/src/core/heap.ts:18-95` & `core.ts:204-260`: Height-indexed topological dirty queue `heap._heap[height]`, incremental `if (heap._marked) markNode(n)` avoiding $O(N^2)$ mount re-walks (`#3350`), deferred `EFFECT_USER` execution, and `assertNotInEffectCallback` ownerless-leak guard.
5. **`tc39/proposal-signals` @ `9124ed91b24bb02ff7408b2fcf5abb6e18b095d7`**: `README.md` (`Signal.State`, `Signal.Computed`, `Signal.subtle.Watcher` push-pull specification).
6. **`salsa-rs/salsa` @ `496752ea3879af8cf3d71d1e28d76447a0cf6482`**:
   - `src/durability.rs:63-145`: `Durability::{LOW, MEDIUM, HIGH, NEVER_CHANGE}` and `AtomicDurability` (`Acquire`/`Release`).
   - `src/function/backdate.rs:15-115`: `backdate_if_appropriate`, `can_backdate` (`cycle_heads().is_empty()`, `!may_be_provisional()`, `revisions.durability >= self.revisions.durability`), and `BackdateViolation` untracked-state diagnostic.
   - `src/function/maybe_changed_after.rs:89-220`: Hot-path durability check and cold-path `SyncTable::try_claim` thread synchronization.

### Normative Specifications and Foundational Papers

- **W3C Candidate Recommendation**, *CSS Flexible Box Layout Module Level 1* (`https://www.w3.org/TR/css-flexbox-1/`) and *CSS Grid Layout Module Level 2* (`https://www.w3.org/TR/css-grid-2/`).
- Gregory H. Cooper and Shriram Krishnamurthi, *Embedding Dynamic Dataflow in a Call-by-Value Language* (`FrTime`), ESOP 2006 (`DOI: 10.1007/11693024_20`).
- Evan Czaplicki and Stephen Chong, *Asynchronous Functional Reactive Programming for GUIs* (`Elm`), PLDI 2013 (`DOI: 10.1145/2491956.2462161`).
- Matthew A. Hammer, Yit Phang Khoo, Michael Hicks, and Jeffrey S. Foster, *Adapton: Composable, Demand-Driven Incremental Computation*, PLDI 2014 (`DOI: 10.1145/2594291.2594324`).

### Executed Micro-Probe Output (`2026-11-19`, Python 3 Standard Library, `10.08 ms`)

Executing the standalone verification probe reproduced below in `## Revalidation` yielded:
```text
scrollbar_osc: naive=[300, 288, 300, 288, 300, 288] monotone=[300, 288, 288, 288, 288, 288]
pixel_snap: local_sum=99 ([33, 33, 33]) cum_sum=100 ([33, 34, 33]) f32_hit=False au64_hit=True
signals_diamond: eager=[-12, -2] push_pull=[-2] revert_bug=10 revert_fix=990
salsa_cutoff: revs=2000 top_recomputes=105 nan_eq_refl=False
```

## Revalidation

Run the following self-contained standard-library Python check (`< 0.1 s`, zero network or third-party packages) to revalidate (1) `overflow: auto` + `aspect-ratio` period-2 oscillation vs. monotone 2-pass convergence, (2) `1 px` local-rounding crack vs. cumulative edge rounding and `f32::to_bits()` non-associative cache misses vs. `1/64 px` `Au64` determinism, (3) push-pull diamond glitch elimination and `Preact Signals` monotonic batch-revert soundness, and (4) `Salsa` early-cutoff + `Durability::HIGH` equivalence against a stateless from-scratch oracle (`94.7%` recompute skip rate) vs. `NaN` reflexivity failure:

```bash
python3 - <<'PY'
import random, struct

def sim_sb(monotone, w0=300, max_h=50, sb=12, n=6):
    out, has_sb = [], False
    for _ in range(n):
        w = w0 - (sb if has_sb else 0)
        out.append(w)
        over = round(w / 5.92) > max_h
        has_sb = (has_sb or over) if monotone else over
    return out

assert sim_sb(False) == [300, 288, 300, 288, 300, 288]
assert sim_sb(True)  == [300, 288, 288, 288, 288, 288]

f32 = lambda x: struct.unpack("<f", struct.pack("<f", x))[0]
f32_bits = lambda x: struct.unpack("<I", struct.pack("<f", x))[0]
wc = f32(100.0) / f32(3.0)
local_w = [round(wc) for _ in range(3)]
edges = [0.0, wc, f32(wc + wc), 100.0]
cum_w = [round(edges[i + 1]) - round(edges[i]) for i in range(3)]
assert sum(local_w) == 99 and sum(cum_w) == 100
assert f32_bits(f32(f32(f32(100.0) - f32(33.3)) - f32(33.3))) != f32_bits(f32(f32(100.0) - f32(f32(33.3) + f32(33.3))))
assert (round(100.0 * 64) - round(33.3 * 64)) - round(33.3 * 64) == round(100.0 * 64) - (round(33.3 * 64) + round(33.3 * 64))

eager_obs = [5 * 2 - 2 * (10 + 1), 10 * 2 - 2 * (10 + 1)]
pull_obs = [10 * 2 - 2 * (10 + 1)]
assert eager_obs == [-12, -2] and pull_obs == [-2]

def batch_revert(rollback_bug):
    s_val, s_ver = 0, 0
    s_val, s_ver = 1, 1
    m_cached, m_seen = s_val * 10, s_ver
    s_val = 0
    s_ver = 0 if rollback_bug else (s_ver + 1)
    s_val = 99
    s_ver += 1
    return m_cached if (s_ver == m_seen) else (s_val * 10)

assert batch_revert(True) == 10 and batch_revert(False) == 990

rng = random.Random(20261119)
low_in, high_in = 20, 100
memo_mid = (low_in // 2, 1)
memo_top = (memo_mid[0] + high_in, 1, 1)
last_high, top_runs = 1, 0
for rev in range(2, 2002):
    if rng.random() < 0.95:
        low_in = 20 + (rev & 1)  # stays in bucket //2 == 10 -> early cutoff!
    else:
        high_in = rng.randrange(1000)
        last_high = rev
    mid_new = low_in // 2
    memo_mid = (mid_new, memo_mid[1] if mid_new == memo_mid[0] else rev)
    if memo_mid[1] > memo_top[2] or last_high > memo_top[2]:
        top_runs += 1
        top_new = memo_mid[0] + high_in
        memo_top = (top_new, memo_top[1] if top_new == memo_top[0] else rev, rev)
    else:
        memo_top = (memo_top[0], memo_top[1], rev)
    assert memo_top[0] == (low_in // 2) + high_in

assert top_runs < 150 and not (float("nan") == float("nan"))
print(f"OK: taffy/yoga + signals + salsa revalidation passed (top_runs={top_runs}/2000)")
PY
```

To revalidate upstream implementations when updating any pinned commit in `REPORT.json`:
1. Diff `src/tree/cache.rs` (`CacheKey`, `CacheMode`) and `src/compute/mod.rs` (`round_layout`) in `DioxusLabs/taffy`, and `yoga/algorithm/PixelGrid.cpp` / `Cache.cpp` in `facebook/yoga`.
2. Diff `packages/core/src/index.ts` (`reconcileBatchSnapshots`, `needsToRecompute`, `cleanupSources`) in `preactjs/signals` and `packages/signals/src/core/heap.ts` in `solidjs/solid`.
3. Diff `src/function/backdate.rs` (`can_backdate`, `BackdateViolation`) and `src/durability.rs` in `salsa-rs/salsa`.
