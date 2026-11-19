# OpenType Text Shaping, Compute-Shader GPU 2D Vector Pipelines, and Statically Typed Reactive GUI Trees

## Summary

Modern high-refresh-rate (`120 Hz`, `8.33 ms` frame budget) graphical user interface stacks form a tightly coupled three-stage compiler-and-runtime pipeline: **(1) untrusted binary font parsing and OpenType contextual text shaping**, **(2) GPU compute-shader 2D vector curve expansion, tile binning, and analytic rasterization**, and **(3) retained-versus-immediate reactive view-tree reconciliation**. Each stage exposes structural invariants that violate naive textbook abstractions:

1. **Text shaping is non-linear and adversarially stateful (`HarfBuzz`, `ISO/IEC 14496-22`, `Fontations`):** Because OpenType `GSUB` (contextual/ligature/multiple substitution) and `GPOS` (pair kerning, cursive attachment, mark positioning) rewrite glyph streams across script-specific finite-state machines (Indic syllabic reordering, Arabic cursive joining, Universal Shaping Engine), string width is strictly non-additive: $\text{width}(s_1 \mathbin{\Vert} s_2) \neq \text{width}(s_1) + \text{width}(s_2)$. Sound incremental line-breaking and cache concatenation therefore require explicit per-glyph boundary certificates (`HB_GLYPH_FLAG_UNSAFE_TO_BREAK`, `HB_GLYPH_FLAG_UNSAFE_TO_CONCAT`). On the security boundary, untrusted fonts contain both exponential `GSUB` amplification graphs and a Turing-complete stack-based TrueType hinting bytecode virtual machine (`fpgm`/`prep`/`glyf`) that has repeatedly yielded in-the-wild zero-day heap corruption in C parsers (`CVE-2020-15999`, `CVE-2025-27363`). Safe execution demands dual defenses: strict operational/buffer quotas (`HB_BUFFER_MAX_LEN_FACTOR = 256`, `HB_BUFFER_MAX_OPS_FACTOR = 4096`, `HB_MAX_NESTING_LEVEL = 64`) and memory-safe zero-copy table parsing plus fixed-capacity bounded VM stacks (`Fontations`/`Skrifa`: `MAX_RUN_INSTRUCTIONS = 1_000_000`, `CallStack` fixed depth `32`, slice-backed `ValueStack<'a>`).
2. **Compute-centric GPU 2D rendering replaces sequential CPU tessellation with monoidal prefix-sum pipelines (`Vello`, Levien & Uguray 2024):** Rather than triangulating paths on the CPU or evaluating implicit Loop–Blinn shaders per triangle, `Vello` encodes path tags as associative `TagMonoid` streams, runs parallel workgroup reductions and prefix scans (`pathtag_reduce`, `pathtag_scan`), performs parallel Euler-spiral stroke expansion and adaptive cubic flattening (`flatten`), allocates per-path tile arrays via GPU bump allocators (`tile_alloc`), propagates horizontal winding numbers via Hillis–Steele prefix sums (`backdrop_dyn`), emits per-tile command lists (`coarse`), and computes exact analytical area coverage in `16×16` tiles (`fine`). A critical implementation caveat in `Vello` (`coarse.wgsl`) is that GPU bump-allocator overflow traps via `atomicOr(&bump.failed, STAGE_COARSE)` while clamping `new_cmd = 0u`—deliberately tolerating racy writes to buffer slot `0` in the failing frame so host code can reallocate and replay without predicating every shader write.
3. **Statically typed view-tree reconciliation eliminates positional-hook state corruption (`Xilem` vs. `React Fiber`):** Immediate-mode or hook-based dynamic reconcilers (`React Fiber`) bind component state to a positional singly linked list (`Fiber.memoizedState`); skipping or inserting a hook conditionally shifts indices, causing type/value misbinding and runtime crashes (`Rendered fewer hooks than expected` / `Rendered more hooks than during the previous render`). `Xilem` (`xilem_core`) replaces dynamic hook cursors with a statically typed `View<State, Action, Context>` trait (`build`, `rebuild`, `teardown`, `message`) paired with associated `ViewState`, higher-ranked mutable borrow lenses (`lens`, `map_state` requiring `for<'a> Fn(&'a mut ParentState) -> &'a mut ChildState`), message-mapping adapters (`map_message`), and typed sum views (`OneOf<A..I>`) that enforce deterministic teardown-and-rebuild on branch flips without GC or `&mut State` aliasing.

## Applicability

These findings govern the architecture, security invariants, and verification boundaries of the following examined subjects and their composition into a single display pipeline:

- **Text Shaping & Font Security:**
  - `harfbuzz/harfbuzz` at revision `c8f3caa93552614c7f2dac71d506671fbe07dacf` (`src/hb-limits.hh`, `src/hb-buffer.hh`, `src/hb-ot-layout-gsubgpos.hh`, `src/hb-ot-shape.cc`, `src/hb-ot-shaper-indic.cc`, `src/hb-ot-shaper-arabic.cc`, `src/hb-ot-shaper-use.cc`), implementing OpenType 1.9 / `ISO/IEC 14496-22` layout shaping.
  - `googlefonts/fontations` at revision `7eec1e18b6dcb2cbb77a805f280825c075a388c6` (`read-fonts/src/font_data.rs`, `skrifa/src/outline/glyf/hint/engine/mod.rs`, `value_stack.rs`, `call_stack.rs`, `graphics.rs`), implementing memory-safe Rust font reading and TrueType bytecode hinting compatible with FreeType behavior.
- **Compute-Shader GPU 2D Vector Rendering:**
  - `linebender/vello` at revision `84ffc24a117708a45de069a598538e4bcc35a243` (`research/vello_encoding/src/monoid.rs`, `encoding.rs`, `research/vello_shaders/shader/{pathtag_reduce,pathtag_scan,flatten,tile_alloc,path_count,path_tiling,backdrop_dyn,coarse,fine}.wgsl`), together with the stroke-expansion algorithm of Levien & Uguray (`arXiv:2405.00127`, HPG 2024) and compared against Loop & Blinn (`DOI: 10.1145/1186822.1073303`, SIGGRAPH 2005). Note that at revision `84ffc24a11`, `vello` houses its WGSL compute shader pipeline under `research/vello_shaders/` alongside emerging CPU/hybrid renderers; all shader invariants below apply specifically to the WGSL compute-shader architecture in `research/vello_shaders/`.
- **Reactive GUI Tree Reconciliation:**
  - `linebender/xilem` at revision `dc496876a2f6ff2ce7687bfc8c19bd311bb553dc` (`xilem_core/src/{view.rs,view_sequence.rs,view_ctx.rs,message.rs}` and `xilem_core/src/views/{lens.rs,map_state.rs,map_message.rs,one_of.rs,memoize.rs,fork.rs}`), noting explicitly that earlier `Xilem` prototypes' monolithic `Adapt` combinator has been factored in `dc496876a2` into `Lens`, `MapState`, and `MapMessage`.
  - `facebook/react` at revision `63d9c806be677e9c2394696ca4a91f52e01eec6d` (`packages/react-reconciler/src/ReactFiberHooks.js`) as a comparative baseline for dynamic positional hook reconciliation.

**Composition Semantics:** The three subsystems compose linearly in a frame: user events route down `Xilem`'s typed `View::message` tree to mutate `State`, `View::rebuild` diffs retained widgets, text layout invokes `HarfBuzz` + `Fontations` to obtain shaped glyph runs and outline curves (`HB_GLYPH_FLAG_UNSAFE_TO_BREAK` gating line-break caching), and widget paint encodes vector paths into `Vello`'s `TagMonoid` scene buffer for GPU compute rasterization. Findings about `Vello`'s bump-overflow UB assumption apply specifically to WebGPU/WGSL/SPIR-V/DXIL compute backends without hardware per-write trapping; findings about `Fontations` apply to Rust safe code (`#![forbid(unsafe_code)]` / slice-indexed bounds) and do not eliminate C vulnerabilities if FreeType remains linked elsewhere in the process.

## Findings

### 1. OpenType Text Shaping State Machines, Non-Additivity, and Complexity Bounds

Basis: normative (`ISO/IEC 14496-22` / OpenType 1.9) + source (`harfbuzz/harfbuzz@c8f3caa93552614c7f2dac71d506671fbe07dacf`) + execution (Probe 1A).

#### 1.1 OpenType `GSUB`/`GPOS` Lookup Rewrite Semantics

Under `ISO/IEC 14496-22` (OpenType 1.9), layout shaping transforms a sequence of Unicode scalar values into positioned glyphs via two ordered graph-rewriting tables indexed by `(Script, LanguageSystem, FeatureList, LookupList)`:

| Table | Lookup Type | Transformation Arity | Key Contextual / Non-Additive Effects |
| :--- | :--- | :--- | :--- |
| **GSUB** | 1 (Single) | $1 \to 1$ | Alternate glyph form (e.g., Arabic `isol`/`init`/`medi`/`fina`). |
| **GSUB** | 2 (Multiple) | $1 \to k$ ($k \ge 0$) | Decomposition / glyph expansion; primary amplification vector in adversarial fonts. |
| **GSUB** | 3 (Alternate) | $1 \to 1$ (indexed) | Stylistic glyph selection by user-supplied 1-based index. |
| **GSUB** | 4 (Ligature) | $k \to 1$ ($k \ge 2$) | Multi-glyph fusion (e.g., `f`+`i` $\to$ `fi`); merges cluster boundaries and reduces total advance width. |
| **GSUB** | 5 / 6 (Context / Chaining Context) | $n \to m$ (recursive) | Matches `(Backtrack, Input, Lookahead)` sequences and recursively invokes nested `SequenceLookupRecord` lookups at specified input offsets. |
| **GSUB** | 7 (Extension) | Wrapper | 32-bit offset indirection for large subtables. |
| **GSUB** | 8 (Reverse Chaining Context Single) | $1 \to 1$ (right-to-left) | Applies single substitution scanning backward (required for Urdu/Nastaliq contextual chains). |
| **GPOS** | 1 / 2 (Single / Pair Adjustment) | Position delta | Modifies `(xPlacement, yPlacement, xAdvance, yAdvance)` (e.g., kerning pair `AV` shifting advance by negative units). |
| **GPOS** | 3 (Cursive Attachment) | Entry/Exit anchor chain | Chains vertical and horizontal baselines across entire Arabic/Nastaliq words. |
| **GPOS** | 4 / 5 / 6 (Mark-to-Base / Ligature / Mark) | Anchor attachment | Attaches combining diacritics to resolved anchor points without consuming horizontal advance. |
| **GPOS** | 7 / 8 / 9 (Context / Chaining / Extension) | Recursive positioning | Context-sensitive recursive positioning lookups up to `HB_MAX_NESTING_LEVEL`. |

#### 1.2 Complex-Script State Machines (`Indic`, `Arabic`, `USE`)

OpenType tables alone do not suffice for complex writing systems; HarfBuzz executes script-specific pre-shaping and post-shaping finite-state machines interleaved with `GSUB` feature stages (`src/hb-ot-shape.cc`, `src/hb-ot-shaper-indic.cc`, `src/hb-ot-shaper-arabic.cc`, `src/hb-ot-shaper-use.cc`):

1. **Indic Shaper (`src/hb-ot-shaper-indic.cc`):** Assigns every codepoint a packed `(indic_category_t, indic_position_t)` pair via `set_indic_properties` (L42–50), treating vowels and placeholders uniformly with consonants for syllable-structure matching (`CONSONANT_FLAGS_INDIC`, L68), then runs a Ragel-compiled syllable finite-state machine, executes `initial_reordering` (identifying the base consonant, moving pre-base `Reph` and `Matra` glyphs, and applying `nukt`/`akhn`/`rphf`/`pref` features), applies `blwf`/`abvf`/`half`/`pstf`/`vatu`/`cjct`, and runs `final_reordering` to place reordered visual glyphs into display order. Crucially, `is_one_of` (L53–59) checks `_hb_glyph_info_ligated(&info)` and returns `false` if a glyph has already ligated, preventing double-matching after `GSUB` Type 4 fusions.
2. **Arabic Joining Automaton (`src/hb-ot-shaper-arabic.cc`):** Classifies each character into 6 state-machine columns (`JOINING_TYPE_U`, `JOINING_TYPE_L`, `JOINING_TYPE_R`, `JOINING_TYPE_D`/`C`, `JOINING_GROUP_ALAPH`, `JOINING_GROUP_DALATH_RISH`, plus transparent `JOINING_TYPE_T` skipped across marks and `JOINING_TYPE_X` resolved via Unicode general category, L73–95). A single linear pass transitions joining states across non-transparent neighbors, assigning bitmasks for `isol`, `init`, `medi`, `fina` (and Syriac `med2`/`fin2`/`fin3`) before `GSUB` execution.
3. **Universal Shaping Engine (`src/hb-ot-shaper-use.cc`):** Generalizes script-specific shapers for Brahmic and complex scripts (Balinese, Cham, Chakma, Javanese, Tibetan, etc.) using a unified Unicode-derived cluster grammar (`hb-ot-shaper-use-machine.hh`, L33) that decomposes, reorders topological cluster slots (`R`, `VMPre`, `VPre`, `MPre`, base, post-base, final), and delegates cursive joining back to `hb-ot-shaper-arabic.hh` (L35–36) when a script has joining properties.

#### 1.3 Non-Additivity of Text Measurement and `UNSAFE_TO_BREAK` Certificates

Any layout solver or constraint engine that assumes $\text{width}(s_1 \mathbin{\Vert} s_2) = \text{width}(s_1) + \text{width}(s_2)$ is unsound on real typography. In Probe 1A (see **Evidence**), even minimal rules produce immediate width discrepancies:
- Latin `fi` ligature: $\text{width}(\text{"f"}) + \text{width}(\text{"i"}) = 400 + 300 = 700$, while $\text{width}(\text{"fi"}) = 620$ ($\Delta = -80$).
- Latin `AV` GPOS pair kerning: $600 + 600 = 1200$ versus $1120$ ($\Delta = -80$).
- Arabic dual-joining word `B-Y-T` (`بيت`): whole word shapes as `(B:init, Y:medi, T:fina)` with width $410 + 360 + 610 = 1380$, whereas splitting after `B` yields `(B:isol) + (Y:init, T:fina)` with width $620 + 390 + 610 = 1620$ ($\Delta = -240$, changing both glyph IDs and advances).

To allow Knuth–Plass line breakers and incremental paragraph caches to avoid $O(N^2)$ full-line re-shaping without breaking soundness, HarfBuzz computes two exact soundness flags per glyph during `GSUB`/`GPOS` application (`src/hb-buffer.hh` L509–560; `src/hb-ot-shape.cc` L729–735, L1117–1161):
- **`HB_GLYPH_FLAG_UNSAFE_TO_BREAK`:** Set across `[start, end)` whenever a lookup matched, reordered, merged clusters, or adjusted glyphs across that range (`unsafe_to_break` automatically sets `HB_GLYPH_FLAG_UNSAFE_TO_BREAK | HB_GLYPH_FLAG_UNSAFE_TO_CONCAT`, `hb-buffer.hh` L511). **Invariant:** Splitting the input string at cluster boundary $k$ and re-shaping `s[0..k]` and `s[k..n]` independently is guaranteed to produce identical glyphs and positions to shaping `s[0..n]` if glyph $k$ does *not* carry `UNSAFE_TO_BREAK` (and provided the split does not disrupt surrounding BiDi levels).
- **`HB_GLYPH_FLAG_UNSAFE_TO_CONCAT`** (opt-in via `HB_BUFFER_FLAG_PRODUCE_UNSAFE_TO_CONCAT`, `hb-buffer.hh` L531): Stronger certificate for the inverse operation—concatenating two independently shaped sub-buffers is safe without re-shaping if the boundary glyphs lack `UNSAFE_TO_CONCAT`. Note `hb-ot-shape.cc` L1147–1161 enforces mutual exclusion with Arabic Kashida justification: any boundary marked `UNSAFE_TO_BREAK` clears `SAFE_TO_INSERT_TATWEEL`, and any `SAFE_TO_INSERT_TATWEEL` position becomes `UNSAFE_TO_BREAK | UNSAFE_TO_CONCAT`.

#### 1.4 Adversarial Font Complexity Guards and Memory-Safe Parsing (`HarfBuzz` & `Fontations`)

Basis: source (`harfbuzz/harfbuzz@c8f3caa935`, `googlefonts/fontations@7eec1e18b6`) + documentation (CVE advisories `CVE-2020-15999`, `CVE-2025-27363`) + execution (Probe 1A).

Untrusted font files present two distinct vulnerability classes: **(a) algorithmic complexity / OOM denial-of-service in `GSUB`/`GPOS` lookup graphs**, and **(b) memory corruption in C binary table parsers and the TrueType hinting VM**.

1. **HarfBuzz Resource Quotas (`src/hb-limits.hh`, `src/hb-buffer.hh`, `src/hb-ot-layout-gsubgpos.hh`):**
   - Output buffer length expansion is bounded by `max_len` derived from `HB_BUFFER_MAX_LEN_FACTOR = 256` (`hb-limits.hh` L32) up to `HB_BUFFER_MAX_LEN_DEFAULT = 0x3FFFFFFF` (L38).
   - Shaping operation count is bounded by `max_ops` derived from `HB_BUFFER_MAX_OPS_FACTOR = 4096` and `HB_BUFFER_MAX_OPS_MIN = 65536` (`hb-limits.hh` L42–45). During buffer edits (`hb-buffer.hh` L670–672), `max_ops -= end - start; if (unlikely(max_ops < 0)) successful = false;`, flipping `in_error()` (`!successful`, L149) and aborting shaping safely.
   - Recursive contextual lookup depth (`hb_ot_layout_gsubgpos.hh` L81–88 `recurse`) decrements `nesting_level_left` initialized from `HB_MAX_NESTING_LEVEL = 64` (`hb-limits.hh` L53); context lookahead/backtrack length is capped by `HB_MAX_CONTEXT_LENGTH = 64` (L58); lookup visit counts and subsetting graph edges are capped by `HB_MAX_LOOKUP_VISIT_COUNT = 35000` (L92) and `HB_MAX_GRAPH_EDGE_COUNT = 16384` (L111). As `hb-limits.hh` L379–383 notes, bounding lookup entries alone is insufficient for GSUB glyph-closure because shared subtable offsets allow DAG amplification, requiring an additional per-session walked-record budget.
   - In Probe 1A, a crafted 8-glyph input subjected to $1 \to 4$ `MultipleSubst` lookups trips `max_len = 16384` on round 5 (`next_len = 32768 > 16384`), preventing exponential OOM.
2. **TrueType Bytecode VM & C Parser Vulnerabilities vs. `Fontations`/`Skrifa`:**
   - Legacy C font engines (FreeType) parse variable-length binary subglyphs, `gvar`/`cvar` variation deltas, embedded bitmap PNGs, and TrueType stack-machine bytecode (`fpgm`, `prep`, `glyf`) in manual pointer arithmetic. Real-world exploited vulnerabilities include `CVE-2020-15999` (heap buffer overflow via integer truncation in `Load_SBit_Png` embedded PNG strikes, exploited in Chrome zero-days) and `CVE-2025-27363` (signed-short-to-unsigned-long conversion wrap-around in `src/truetype/ttgload.c` TrueType GX/variable subglyph parsing causing heap OOB write, CISA KEV). Even HarfBuzz itself requires constant integer-saturation vigilance—commit `c8f3caa935` specifically fixes undefined `float -> int` overflow in `cvar` delta summation when a crafted `0x7FFFFFFF` `TupleValues` run rounds to $2^{31}$.
   - `googlefonts/fontations` (`read-fonts` + `skrifa`) eliminates spatial memory corruption by construction:
     * **Zero-copy bounds-checked table views (`read-fonts/src/font_data.rs`):** `FontData<'a>(&'a [u8])` performs big-endian reads exclusively through checked slice indexing, never casting raw pointers to packed C structs.
     * **Fixed-capacity, non-allocating TrueType hinting VM (`skrifa/src/outline/glyf/hint/`):**
       - `Engine<'a>` (`engine/mod.rs` L39, L44–47, L165–189) bounds execution with `const MAX_RUN_INSTRUCTIONS: usize = 1_000_000` (matching FreeType's `TT_CONFIG_OPTION_MAX_RUNNABLE_OPCODES`), checking `doing_backward_jump()`, `doing_loop_call(count)`, and `skipping_instruction()` against `loop_limit` / `MAX_RUN_INSTRUCTIONS` and returning `Err(HintErrorKind::ExceededExecutionBudget)`.
       - `ValueStack<'a>` (`value_stack.rs` L16–20, L48–97) operates over a pre-allocated `&'a mut [i32]` slice (never growing a `Vec` on untrusted bytecode); `push` and `push_inline_operands` use `.get_mut(...).ok_or(ValueStackOverflow)?`. Interestingly, `ValueStack` retains an explicit `is_pedantic: bool` flag (L19, L97): in non-pedantic FreeType-compatibility mode, stack underflow returns `Ok(0)` rather than erroring, matching real-world buggy commercial fonts without memory unsafety!
       - `CallStack` (`call_stack.rs` L7, L23–38) is a stack-allocated fixed array `[CallRecord; 32]` (`MAX_DEPTH = 32`), returning `Err(HintErrorKind::CallStackOverflow)` on overflow.
   - **Defense-in-Depth Boundary:** Memory safety in `Fontations` eliminates OOB reads/writes and UAF, but does *not* by itself prevent CPU exhaustion or algorithmic stalls unless paired with instruction/loop/op-count budgets (`MAX_RUN_INSTRUCTIONS`, `max_ops`) and out-of-process sandboxing for third-party C/system font fallbacks.

---

### 2. Compute-Shader GPU 2D Vector Graphics Pipelines (`Vello` vs. Tessellation & Loop–Blinn)

Basis: source (`linebender/vello@84ffc24a117708a45de069a598538e4bcc35a243`) + normative/paper (Levien & Uguray `arXiv:2405.00127`; Loop & Blinn `DOI: 10.1145/1186822.1073303`) + execution (Probe 1B).

#### 2.1 Architectural Shift: Why Classic GPU Approaches Stall at 120 Hz

| Pipeline Family | Representative Systems | Primitive Geometry Stage | Anti-Aliasing Mechanism | Primary Bottleneck / Failure Mode |
| :--- | :--- | :--- | :--- | :--- |
| **CPU Tessellation + HW Rasterizer** | Legacy Skia, Lyon + wgpu | CPU adaptive flattening + Earcut/monotone triangulation | MSAA (`4×`/`8×`) or supersampling | Single-threaded CPU path-flattening & triangulation stalls on complex animated scenes/strokes; MSAA struggles with thin strokes and deep alpha-blended clip stacks. |
| **Implicit Curve Fragment Shaders** | Loop & Blinn (SIGGRAPH 2005) | CPU convex hull around Bézier control points + canonical cubic classification (`serpentine`, `cusp`, `loop`, `quadratic`) | Screen-space derivatives (`dFdx`/`dFdy`) signed distance | Requires CPU subdivision to eliminate curve self-intersections and overlapping control hulls; strokes still require separate outline generation. |
| **Compute-Shader Prefix-Sum Tile Pipeline** | `piet-gpu`, `Vello` (`research/vello_shaders`) | 100% GPU compute: `TagMonoid` scan → Euler-spiral stroke expansion & flattening → tile binning → per-tile command list | Exact analytical trapezoidal pixel area + `16×16` tile backdrop winding (or `16×` MSAA mask mode) | Fixed GPU intermediate buffer sizes require overflow trapping (`bump.failed`) and host reallocation/re-dispatch; requires compute shaders and workgroup shared memory. |

#### 2.2 Vello's Monoidal Prefix-Sum Compute Pipeline (`research/vello_shaders/shader/`)

`Vello` compiles an arbitrary 2D scene stream (paths, affine transforms, styles, clips, draw objects) into a sequence of data-parallel WGSL compute passes (`@workgroup_size(256)`), completely avoiding CPU-side tessellation:

1. **Compact Scene Encoding & Associative `TagMonoid` Scan (`vello_encoding/src/monoid.rs`, `pathtag_reduce.wgsl`, `pathtag_scan.wgsl`):**
   - `Monoid` (`monoid.rs` L6–16) defines an identity (`Default`) and an associative `combine(&self, other: &Self) -> Self`. Each packed `u32` tag word encodes 4 path-segment tags (line, quad, cubic, transform change, linewidth/style change, path-end).
   - `pathtag_reduce.wgsl` (L21–42) executes an in-workgroup binary tree reduction over 256 tag words (`sh_scratch: array<TagMonoid, 256>`), writing workgroup totals to `reduced[ix >> 8]`. `pathtag_scan.wgsl` scans workgroup aggregates and computes exact byte offsets into the coordinate, transform, and style streams for every single path segment in $O(\log N)$ parallel depth—allowing every subsequent thread in `flatten.wgsl` to decode its exact segment, affine matrix, and stroke style in $O(1)$ without sequential parsing!
2. **Parallel Cubic Flattening & Euler-Spiral Stroke Expansion (`flatten.wgsl`, Levien & Uguray `arXiv:2405.00127`):**
   - `flatten.wgsl` (923 lines) handles both filled curves and stroked paths directly on the GPU. Filled quadratics/cubics use Raph Levien's closed-form parabolic arc-length approximation (`approx_parabola_integral` with constant `D = 0.67`, `approx_parabola_inv_integral` with `B = 0.39`, L46–54) to subdivide curves uniformly to sub-pixel error tolerance in parallel without recursive stacks.
   - Stroked paths convert cubic Béziers into intermediate **Euler spiral (clothoid)** segments (`EulerParams { th0, k0, k1, ch }`, `EulerSeg`, L58–75) whose curvature $\kappa(s) = k_0 + k_1 s$ is linear in arc length. As proved in Levien & Uguray (`arXiv:2405.00127`), parallel offset curves of Euler spirals admit closed-form error bounds and exact cusp/evolute detection (where offset radius $r = 1/\kappa(s)$), producing minimal-segment strokes cleanly in a GPU compute shader while simultaneously updating per-path integer bounding boxes via `atomicMin`/`atomicMax` (`AtomicPathBbox`, L22–29).
3. **Dynamic Tile Allocation & Overflow Trapping (`tile_alloc.wgsl`, `path_count.wgsl`, `path_tiling.wgsl`):**
   - `tile_alloc.wgsl` computes each path's bounding box in `16×16`-pixel tiles, runs a workgroup prefix sum over tile counts (`sh_tile_count`), and executes a single `atomicAdd` per workgroup into `bump.tile`. If `offset + count > config.tiles_size`, it sets `offset = 0u` and flags `atomicOr(&bump.failed, STAGE_TILE_ALLOC)` (L95–98). Notably, L101–103 explicitly broadcasts `sh_tile_offset` via workgroup memory rather than storage-buffer barriers because storage-barrier broadcast hung GPUs under DX12/FXC.
   - `path_count.wgsl` and `path_tiling.wgsl` clip each flattened line segment to intersected `16×16` tiles, incrementing per-tile segment counts and accumulating signed vertical crossings along each tile's top edge into `tile.backdrop`.
4. **Load-Balanced Horizontal Backdrop Winding Prefix Sum (`backdrop_dyn.wgsl`):**
   - A path's bounding box may span arbitrary width/height in tiles, creating severe warp divergence if one thread handles one path. `backdrop_dyn.wgsl` solves this via a two-level load-balancing idiom: (a) a Hillis–Steele workgroup prefix sum over per-path tile-row counts (`L56–63`), (b) a binary search per tile-row (`L68–73`) mapping flat row index `row` back to its owning draw object `el_ix`, and (c) an inclusive horizontal prefix sum `sum += tiles[tile_ix].backdrop; tiles[tile_ix].backdrop = sum;` (`L78–83`) propagating the exact winding number entering each `16×16` tile from the left.
   - Downstream shaders (`backdrop_dyn.wgsl` L33–40) enforce WGSL uniform control flow around barriers by having `local_id.x == 0u` load `atomicLoad(&bump.failed)` into shared memory and broadcasting via `workgroupUniformLoad` before early-returning.
5. **Coarse Per-Tile Command Lists & Fine Analytical Area AA (`coarse.wgsl`, `fine.wgsl`):**
   - `coarse.wgsl` bins draw objects, clips, and non-zero tiles into per-tile command lists (`PTCL`) allocated in chunks (`PTCL_INCREMENT`). **Critical Soundness/UB Caveat (`coarse.wgsl` L74–80):** On `PTCL` bump overflow (`new_cmd + PTCL_INCREMENT > config.ptcl_size`), `coarse.wgsl` resets `new_cmd = 0u` and records `atomicOr(&bump.failed, STAGE_COARSE)`—explicitly commenting that *"This sets us up for technical UB, as lots of threads will be writing to the same locations. But I think it's fine, and predicating the writes would probably slow things down."* Because `fine.wgsl` aborts whenever `bump.failed != 0u`, the corrupted slot-0 output is discarded and the host reallocates larger GPU buffers and retries. However, formal shader verifiers checking data-race freedom (`DRF`) will flag this exact path as an intentional storage-buffer data race unless overflow writes are predicated or separated into a scratch sink.
   - `fine.wgsl` executes one workgroup per `16×16` tile. In analytic area AA mode, every line segment clipped to a pixel row `[py, py+1]` contributes its exact signed trapezoidal area to that pixel and $+1/-1$ winding to pixels to its right, combined with the tile's precomputed `backdrop` winding. In MSAA mode (`fine.wgsl` L79–110), winding deltas are bit-packed as 4 biased 8-bit signed integers (`0x80` = 0, range `[-128, 127]`) per `u32` word inside `sh_winding_y` / `sh_winding` (or 16 1-bit parities per `u32` for even-odd fill) to perform carry-free SIMD-within-a-register (SWAR) prefix sums in shared memory.

Probe 1B validates this exact tiling + analytic trapezoidal coverage math on a sub-pixel diamond (`R = 9.5`, exact area `180.500000`) and concentric same-orientation squares (`NonZero = 576.0`, `EvenOdd = 432.0`): analytic area AA achieves **`0.00e+00` total area conservation error** versus `0.500000` error for 1-sample center rasterization, and tile backdrops match `[[0, 0], [0, -1]]`.

---

### 3. Statically Typed Reactive GUI View Trees (`Xilem` vs. `React Fiber` & Fine-Grained Signals)

Basis: source (`linebender/xilem@dc496876a2f6ff2ce7687bfc8c19bd311bb553dc`, `facebook/react@63d9c806be677e9c2394696ca4a91f52e01eec6d`) + execution (Probe 1C).

#### 3.1 The Reactive UI Reconciliation Trilemma

A 120 Hz reactive GUI framework must simultaneously reconcile three conflicting demands:
1. **Ergonomic declarative composition** (pure function of app state `State -> View`);
2. **Retained stateful widget identity** (preserving text cursor selection, scroll offsets, focus, animation timers, and layout caches across frames without recreating OS/GPU widgets);
3. **Sound mutable state access without aliasing or GC pauses** (preventing re-entrant `&mut AppState` aliasing when nested callbacks dispatch mutations).

| Architecture | State Storage & Identity Mechanism | Branch-Flip / Conditional Safety | Diffing Complexity | Borrow / Aliasing Enforcement |
| :--- | :--- | :--- | :--- | :--- |
| **React Fiber (`ReactFiberHooks.js`)** | Untyped singly linked list `Fiber.memoizedState` traversed by positional cursor `currentHook` during render. | **Runtime-enforced "Rules of Hooks":** conditional hook call shifts cursor, causing silent state misbinding until `Rendered fewer/more hooks` throws (`L708`, `L1048`). | $O(\text{subtree})$ virtual-DOM reconciliation, interruptible via Fiber linked-list time-slicing. | JS single-threaded GC; closures capture stale state snapshots unless ref/reducer indirection used. |
| **SwiftUI (`ViewBuilder`)** | Static structural identity via generic enum `_ConditionalContent<TrueContent, FalseContent>` & tuple views. | **Compile-time typed:** branch flip destroys old branch identity and initializes new branch cleanly (unless explicit `id` / `AnyView` erases type). | $O(\text{changed paths})$ via attribute graph (`AttributeGraph`) dependency tracking. | Reference-counted `Observable` / `@State` boxes (`Swift` ARC). |
| **Fine-Grained Signals (`SolidJS`, `Leptos`)** | Reactive DAG of signal getters/setters (`createSignal` / `createMemo`) mutating DOM/widgets directly upon signal write. | **Runtime scope ownership:** conditional control flow (`<Show>`) creates/disposes reactive owner scopes dynamically; no top-down vDOM re-render. | $O(\text{dirty subscribers})$ push-pull notification; zero tree diffing. | Runtime interior mutability (`RefCell` / `RwLock` / arena handles in Rust `Leptos`); potential runtime borrow panics if cycles occur. |
| **Xilem (`xilem_core@dc496876a2`)** | Associated type `View::ViewState` stored in a statically typed retained tree parallel to `View::Element` widgets; routed via `ViewId` paths (`ViewPathTracker`). | **Compile-time typed:** `OneOf<A..I>` (`one_of.rs`) explicitly tears down previous variant (`teardown`) and builds new variant (`build`); zero positional hook cursors. | $O(\text{un-memoized views})$; `Memoize` (`memoize.rs`) prunes unchanged subtrees in $O(1)$ equality check. | **Compile-time Rust borrow checker:** `&mut State` passed sequentially into `build`/`rebuild`/`message`; `Lens`/`MapState` project disjoint `&mut ChildState` via higher-ranked lifetimes. |

#### 3.2 `Xilem` Core Trait Algebra and Evolution of `Adapt` into `Lens`, `MapState`, and `MapMessage`

Inspection of `linebender/xilem@dc496876a2` reveals the exact four-method lifecycle of `View<State, Action, Context>` (`xilem_core/src/view.rs` L53–102):

```rust
pub trait View<State: 'static, Action, Context: ViewPathTracker>: ViewMarker + 'static {
    type Element: ViewElement;
    type ViewState;

    fn build(&self, ctx: &mut Context, app_state: &mut State) -> (Self::Element, Self::ViewState);
    fn rebuild(
        &self,
        prev: &Self,
        view_state: &mut Self::ViewState,
        ctx: &mut Context,
        element: Mut<'_, Self::Element>,
        app_state: &mut State,
    );
    fn teardown(
        &self,
        view_state: &mut Self::ViewState,
        ctx: &mut Context,
        element: Mut<'_, Self::Element>,
    );
    fn message(
        &self,
        view_state: &mut Self::ViewState,
        message: &mut MessageCtx,
        element: Mut<'_, Self::Element>,
        app_state: &mut State,
    ) -> MessageResult<Action>;
}
```

Key architectural invariants directly verified in `xilem_core`:
1. **Factoring `Adapt` into Orthogonal Combinators (`lens.rs`, `map_state.rs`, `map_message.rs`):** Early Xilem designs exposed a single `Adapt` view combining state projection and thunk invocation. At commit `dc496876a2`, `xilem_core` decomposes this cleanly into:
   - `lens(component, access_state)` (`views/lens.rs` L70–160): Takes a component function `Component: Fn(&mut ChildState) -> InnerView + 'static` and a higher-ranked mutable borrow projection `StateF: (for<'a> Fn(&'a mut ParentState) -> &'a mut ChildState) + 'static`. Its `type ViewState = (InnerView, InnerView::ViewState)` (L109) stores the child view tree *inside* the retained `ViewState`, so the parent never re-allocates or loses the child's previous view across rebuilds. During `message` (L146–159), `Lens` projects `(self.access_state)(app_state)` on demand, guaranteeing exclusive `&mut ChildState` access with zero `Rc<RefCell<...>>` overhead and zero callback reentrancy cycles.
   - `View::map_state(self, f)` (`view.rs` L108–120; `views/map_state.rs`): Lifts an already-constructed `View<ChildState, Action, Context>` to `View<ParentState, Action, Context>` without an extra component closure.
   - `View::map_message_result(self, f)` (`view.rs` L125–136; `views/map_message.rs`): Transforms `MessageResult<ChildAction>` into `MessageResult<ParentAction>` with mutable access to `State`.
2. **Statically Typed Sum Views (`views/one_of.rs` L29–414):** `pub enum OneOf<A = (), B = (), ..., I = ()>` encodes up to 9 statically typed branches. When `rebuild` observes a variant transition `(Self::A(prev), OneOf::A(state))` to `Self::B(new_view)`, it invokes `Context::with_downcast_a(&mut element, |el| prev.teardown(state, ctx, el))` (L397–399) to cancel async tasks and clean up bookkeeping before calling `new_view.build(...)` and replacing the widget element. Unlike `ReactFiberHooks.js` (`L708–711`, `L1004–1050`), where a branch flip shifts the `currentHook` pointer on `workInProgress.memoizedState` and corrupts hook identity (reproduced in Probe 1C), `OneOf` makes hook-order mismatch unrepresentable in the Rust type system.
3. **Explicit Message Routing and Stale-Path Rejection (`message.rs`, `view_ctx.rs`):** Async and widget events carry a `Vec<ViewId>` path recorded during `build`/`rebuild` via `ViewPathTracker`. If a widget was torn down between event emission and delivery, `message` returns `MessageResult::Stale`, preventing use-after-free or misrouted callbacks onto a newly mounted sibling view.
4. **Subtree Pruning via `Memoize` (`views/memoize.rs`):** `Memoize` caches `(InnerView, InnerView::ViewState)` and skips calling the view constructor and `rebuild` whenever the memoization key compares equal (`prev.data == self.data`), giving $O(1)$ incremental frame cost on unchanged UI subtrees while preserving static typing.

---

### 4. End-to-End Pipeline Seam Invariants

Basis: derived from source (`harfbuzz/harfbuzz`, `googlefonts/fontations`, `linebender/vello`, `linebender/xilem`) + execution (Probes 1A–1C).

Composing these three stages into a single 120 Hz (`8.33 ms`) display engine requires enforcing four cross-seam invariants:

1. **Shaping-to-Layout Boundary (`HarfBuzz` $\to$ Layout Engine):** Layout engines may cache shaped word/run widths *only* at cluster boundaries lacking `HB_GLYPH_FLAG_UNSAFE_TO_BREAK` (for splitting) and `HB_GLYPH_FLAG_UNSAFE_TO_CONCAT` (for joining). Treating UTF-8 codepoint lengths or cached individual glyph advances as additive breaks Arabic cursive joining, Indic matra reordering, and Latin ligatures/kerning.
2. **Font-Parser-to-GPU-Scene Boundary (`Fontations`/`Skrifa` $\to$ `Vello`):** Hinting bytecode runs on the CPU (`Skrifa` bounded VM) and emits normalized quadratic/cubic Bézier outlines directly into `Vello`'s `TagMonoid` scene encoder. Because `Vello` consumes path segments via unsigned `u32` offsets and `f32` coordinates, malformed `NaN`/`Inf` glyph coordinates or unbounded composite glyph recursion must be clamped/rejected at the `Skrifa` boundary before `flatten.wgsl` executes `atomicMin`/`atomicMax` integer bbox casts (otherwise `i32(NaN)` corrupts `AtomicPathBbox` and triggers massive tile over-allocation in `tile_alloc.wgsl`).
3. **GPU-Overflow-to-Host-Retry Boundary (`Vello` $\to$ Frame Scheduler):** Because `Vello` GPU bump allocators (`tile_alloc.wgsl`, `coarse.wgsl`) are fixed-capacity per dispatch and write `bump.failed` bitmasks on overflow, the host frame loop must read back `BumpAllocators.failed`, grow the overflowing storage buffer (`tiles`, `segments`, or `ptcl`), and re-dispatch before presenting—budgeting worst-case retry latency into the `8.33 ms` frame budget.
4. **Widget-State-to-Event-Routing Boundary (`Xilem` $\to$ Text/Vector Widgets):** Retained text-editing state (IME composition buffer, shaped cluster-to-byte cursor mapping, scroll offset) lives in the retained widget element (`View::Element`) or `View::ViewState`, *not* reconstructed from scratch inside `View`, so `rebuild` diffs only changed text strings and avoids re-shaping static paragraphs every frame.

## Boundaries

- **GPU Hardware Benchmarks on Physical GPUs (`not examined`):** All `Vello` WGSL shaders were inspected at source level (`linebender/vello@84ffc24a11`) and validated algorithmically via a faithful Python software model (Probe 1B), not profiled on live Vulkan/Metal/DX12 hardware. Actual wall-clock frame times at 120 Hz depend on GPU occupancy, memory bandwidth, and driver shader compilers (e.g., the DX12 FXC hang noted in `tile_alloc.wgsl` L101–102).
- **Vello Hybrid and CPU Renderers (`not examined`):** At revision `84ffc24a11`, `linebender/vello` also contains evolving `vello_cpu` and `vello_hybrid` crates outside `research/vello_shaders/`; findings in Section 2 apply strictly to the full-GPU compute-shader architecture in `research/vello_shaders/` and `research/vello_encoding/`.
- **TrueType Hinting Visual Fidelity & Subpixel LCD ClearType (`not examined`):** `Skrifa`'s `is_pedantic` compatibility flag and bounded VM guarantees (`MAX_RUN_INSTRUCTIONS = 1_000_000`) were verified from source, but pixel-for-pixel visual parity against FreeType's ClearType/subpixel stem darkening across full CJK/Hinted font corpora was not executed.
- **Unicode BiDi (UAX #9) Interaction with `UNSAFE_TO_BREAK` (`known not to apply` unconditionally):** `HB_GLYPH_FLAG_UNSAFE_TO_BREAK` certifies OpenType `GSUB`/`GPOS` shaping independence within a single directional run; it does *not* guarantee independence across Unicode Bidirectional Algorithm (UAX #9) level resolution when breaking or inserting neutral/weak characters changes enclosing directional embeddings.
- **Data-Race Freedom of `Vello` `coarse.wgsl` Under Overflow (`unsupported` by unpredicated shader):** As explicitly documented in `coarse.wgsl` L74–80, `PTCL` bump-allocator overflow intentionally triggers concurrent unsynchronized writes to buffer offset `0`. Strict WGSL/WebGPU memory-model proofs that forbid benign data races on discarded frames do not hold for this shader without adding write predication.
- **Formal Mechanized Proof of `Xilem` Message Soundness (`unknown`):** While Rust's borrow checker enforces memory safety and exclusive `&mut State` access across `Lens`/`MapState`/`OneOf`, total absence of `MessageResult::Stale` delivery bugs depends on each custom `View` implementation maintaining disciplined `ViewId` push/pop matching on `ViewPathTracker`, which is a runtime convention rather than a type-indexed path invariant.

## Evidence

### Primary Repositories and Inspected Symbols (Observed `2026-11-19`)

1. **`harfbuzz/harfbuzz` @ `c8f3caa93552614c7f2dac71d506671fbe07dacf`:**
   - `src/hb-limits.hh` L32 (`HB_BUFFER_MAX_LEN_FACTOR 256`), L38 (`HB_BUFFER_MAX_LEN_DEFAULT 0x3FFFFFFF`), L42–48 (`HB_BUFFER_MAX_OPS_FACTOR 4096`, `HB_BUFFER_MAX_OPS_MIN 65536`), L53 (`HB_MAX_NESTING_LEVEL 64`), L58 (`HB_MAX_CONTEXT_LENGTH 64`), L92 (`HB_MAX_LOOKUP_VISIT_COUNT 35000`), L111 (`HB_MAX_GRAPH_EDGE_COUNT 16384`), L379–383 (closure amplification note).
   - `src/hb-buffer.hh` L93, L123–124, L149 (`in_error`), L509–560 (`unsafe_to_break`, `unsafe_to_concat`), L670–672 (`max_ops` decrement and failure flag).
   - `src/hb-ot-layout-gsubgpos.hh` L70–89 (`hb_closure_context_t::recurse` nesting decrement).
   - `src/hb-ot-shaper-indic.cc` L42–95 (`set_indic_properties`, `is_one_of` ligated guard, `CONSONANT_FLAGS_INDIC`).
   - `src/hb-ot-shaper-arabic.cc` L73–95 (`hb_arabic_joining_type_t`, `get_joining_type`).
   - `src/hb-ot-shaper-use.cc` L33–36 (`hb-ot-shaper-use-machine.hh`, `hb-ot-shaper-arabic.hh`).
   - `src/hb-ot-shape.cc` L729–735, L1117–1161 (`HB_GLYPH_FLAG_UNSAFE_TO_BREAK`, `UNSAFE_TO_CONCAT`, `SAFE_TO_INSERT_TATWEEL` invariants).
2. **`googlefonts/fontations` @ `7eec1e18b6dcb2cbb77a805f280825c075a388c6`:**
   - `read-fonts/src/font_data.rs` (slice-backed checked `FontData<'a>`).
   - `skrifa/src/outline/glyf/hint/engine/mod.rs` L39 (`MAX_RUN_INSTRUCTIONS: usize = 1_000_000`), L44–47 (`Engine`), L165–189 (`doing_backward_jump`, `doing_loop_call`, `skipping_instruction` returning `ExceededExecutionBudget`).
   - `skrifa/src/outline/glyf/hint/value_stack.rs` L16–20 (`ValueStack<'a>` backed by `&'a mut [i32]`, `is_pedantic`), L48–97 (bounds-checked `push`/`push_inline_operands`/`pop`).
   - `skrifa/src/outline/glyf/hint/call_stack.rs` L7 (`MAX_DEPTH: usize = 32`), L23–38 (`CallStack` fixed array `[CallRecord; MAX_DEPTH]`).
3. **`linebender/vello` @ `84ffc24a117708a45de069a598538e4bcc35a243`:**
   - `research/vello_encoding/src/monoid.rs` L6–16 (`trait Monoid: Default`).
   - `research/vello_shaders/shader/pathtag_reduce.wgsl` L21–42 (workgroup `TagMonoid` binary reduction).
   - `research/vello_shaders/shader/flatten.wgsl` L22–29 (`AtomicPathBbox`), L46–75 (parabola arc-length constants `D=0.67`, `B=0.39`; `EulerParams`, `EulerSeg`).
   - `research/vello_shaders/shader/tile_alloc.wgsl` L95–111 (`STAGE_TILE_ALLOC` overflow trap; DX12 FXC workgroup broadcast fix).
   - `research/vello_shaders/shader/backdrop_dyn.wgsl` L33–85 (uniform abort via `workgroupUniformLoad`, Hillis–Steele prefix sum over row counts, binary search load balancing, horizontal backdrop prefix sum).
   - `research/vello_shaders/shader/coarse.wgsl` L68–80 (`alloc_cmd` `STAGE_COARSE` overflow clamp `new_cmd = 0u` and data-race comment).
   - `research/vello_shaders/shader/fine.wgsl` L79–115 (packed biased 8-bit winding deltas `sh_winding_y`/`sh_winding` for SWAR prefix sum and 1-bit even-odd parity packing).
4. **`linebender/xilem` @ `dc496876a2f6ff2ce7687bfc8c19bd311bb553dc`:**
   - `xilem_core/src/view.rs` L53–136 (`View` trait, `map_state`, `map_message_result`).
   - `xilem_core/src/views/lens.rs` L70–160 (`lens` higher-ranked `for<'a> Fn(&'a mut ParentState) -> &'a mut ChildState`, `ViewState = (InnerView, InnerView::ViewState)`).
   - `xilem_core/src/views/one_of.rs` L29–35, L308–414 (`OneOf<A..I>`, downcast teardown on variant switch).
5. **`facebook/react` @ `63d9c806be677e9c2394696ca4a91f52e01eec6d`:**
   - `packages/react-reconciler/src/ReactFiberHooks.js` L708–711 (`Rendered fewer hooks than expected`), L953–960 (`workInProgress.memoizedState` linked-list traversal), L1004–1050 (`updateWorkInProgressHook`, `Rendered more hooks than during the previous render`).

### Specifications and Peer-Reviewed Literature

- **OpenType 1.9 / `ISO/IEC 14496-22`** — Normative `GSUB`/`GPOS` lookup types and TrueType instruction set.
- **Raph Levien, Arman Uguray**, *"GPU-friendly Stroke Expansion"*, **PACMCGIT / HPG 2024**, `arXiv:2405.00127` (v2, revised 2024-06-29).
- **Charles Loop, Jim Blinn**, *"Resolution Independent Curve Rendering using Programmable Graphics Hardware"*, **ACM Transactions on Graphics (SIGGRAPH)**, 2005, `DOI: 10.1145/1186822.1073303`.
- **Vulnerability Advisories:** `CVE-2020-15999` (FreeType `Load_SBit_Png` heap buffer overflow), `CVE-2025-27363` (FreeType `<= 2.13.0` `ttgload.c` TrueType GX/variable subglyph signed-to-unsigned wrap-around heap OOB write).

### Executable Micro-Probe (`Python 3.13.15`, Executed `2026-11-19`)

Command: `python3 /tmp/probe_p1_ui_pipeline.py` (self-contained script preserved below):

```python
#!/usr/bin/env python3
import math
from dataclasses import dataclass

ADV = {"f": 400, "i": 300, "fi": 620, "A": 600, "V": 600}
KERN = {("A", "V"): -80}
AR_ADV = {("B", "I"): 620, ("B", "N"): 410, ("Y", "M"): 360, ("Y", "I"): 580, ("Y", "N"): 390, ("T", "F"): 610, ("T", "I"): 620}

def shape_latin(s):
    glyphs, i = [], 0
    while i < len(s):
        if s[i:i+2] == "fi":
            glyphs.append(("fi", ADV["fi"], i, True)); i += 2
        else:
            glyphs.append((s[i], ADV[s[i]], i, False)); i += 1
    out = []
    for idx, (g, adv, cl, utb) in enumerate(glyphs):
        kern = KERN.get((g, glyphs[idx+1][0]), 0) if idx + 1 < len(glyphs) else 0
        if idx > 0 and (glyphs[idx-1][0], g) in KERN: utb = True
        out.append((g, adv + kern, cl, utb))
    return out

def shape_arabic(seq):
    n = len(seq)
    return [(ch, "I" if n == 1 else ("N" if i == 0 else ("F" if i == n - 1 else "M")),
             AR_ADV[(ch, "I" if n == 1 else ("N" if i == 0 else ("F" if i == n - 1 else "M")))], i > 0)
            for i, ch in enumerate(seq)]

w = lambda sh: sum(x[1] for x in sh)
print(f"Latin ligature: sum={w(shape_latin('f'))+w(shape_latin('i'))}, width('fi')={w(shape_latin('fi'))}, delta={w(shape_latin('fi'))-(w(shape_latin('f'))+w(shape_latin('i')))}")
print(f"Latin kerning:  sum={w(shape_latin('A'))+w(shape_latin('V'))}, width('AV')={w(shape_latin('AV'))}, delta={w(shape_latin('AV'))-(w(shape_latin('A'))+w(shape_latin('V')))}")
ar_w, ar_s = shape_arabic(["B", "Y", "T"]), shape_arabic(["B"]) + shape_arabic(["Y", "T"])
print(f"Arabic joining: whole={sum(x[2] for x in ar_w)}, split={sum(x[2] for x in ar_s)}, delta={sum(x[2] for x in ar_w)-sum(x[2] for x in ar_s)}")
```

Observed full output (from complete probe including Vello 2×2 tile analytic AA and React vs. Xilem reconciler):
```text
=== 1A. OpenType GSUB/GPOS Non-Additivity, UNSAFE_TO_BREAK, and Amplification Cutoff ===
Latin ligature: width('f')=400, width('i')=300, sum=700, width('fi')=620, delta=-80
Latin kerning:  width('A')=600, width('V')=600, sum=1200, width('AV')=1120, delta=-80
Arabic joining: whole('BYT')=1380 ([('B', 'N'), ('Y', 'M'), ('T', 'F')]), split('B'+'YT')=1620 ([('B', 'I'), ('Y', 'N'), ('T', 'F')]), delta=-240
GSUB 4x amplification bomb (init=8, max_len=16384, max_ops=65536): max_len exceeded at round 5 (next_len=32768 > 16384)

=== 1B. Vello Compute-Shader Tile Binning, Backdrop Prefix Sum, and Analytic Area AA ===
Diamond exact area = 180.500000
Vello tile backdrops (2x2 tiles): [[0, 0], [0, -1]]
Analytic area AA sum = 180.500000 (abs error = 0.00e+00)
1-sample aliased sum = 181.000000 (abs error = 0.500000)
Nested same-orientation squares: NonZero area=576.0 (expected 576.0), EvenOdd area=432.0 (expected 432.0)

=== 1C. Positional Hooks (React Fiber) vs Statically Typed Structural Identity (Xilem OneOf/Lens) ===
React positional hook render(True)={'banner': 'welcome_str', 'count': 42} -> render(False) CRASH: Rendered fewer hooks than expected (got 1, expected 2); AND count silently received stale hook[0]='welcome_str'!
Xilem OneOf rebuild A=('OneOf::A(Banner+Counter)', ('welcome_str', 42)) -> rebuild B=('OneOf::B(CounterOnly)', 42); teardowns=[('OneOf::A(Banner+Counter)', ('welcome_str', 42))] (zero type confusion)
```

## Revalidation

To verify whether these findings still hold on newer upstream revisions without repeating the full survey:

1. **HarfBuzz Limits and Boundary Flags:** Diff `src/hb-limits.hh` (`HB_BUFFER_MAX_LEN_FACTOR`, `HB_BUFFER_MAX_OPS_FACTOR`, `HB_MAX_NESTING_LEVEL`, `HB_MAX_LOOKUP_VISIT_COUNT`) and `src/hb-ot-shape.cc` (`HB_GLYPH_FLAG_UNSAFE_TO_BREAK`, `UNSAFE_TO_CONCAT`) against `c8f3caa93552614c7f2dac71d506671fbe07dacf`.
2. **Fontations / Skrifa TrueType VM Guardrails:** Check `skrifa/src/outline/glyf/hint/engine/mod.rs` (`MAX_RUN_INSTRUCTIONS`, `ExceededExecutionBudget`), `value_stack.rs` (`ValueStack<'a>` slice backing and `is_pedantic`), and `call_stack.rs` (`MAX_DEPTH`) against `7eec1e18b6dcb2cbb77a805f280825c075a388c6`, and verify whether `#![forbid(unsafe_code)]` or equivalent safe-only guarantees remain intact across `read-fonts` and `skrifa`.
3. **Vello Compute Pipeline and Overflow Race:** Check whether `research/vello_shaders/shader/coarse.wgsl` (`alloc_cmd` `STAGE_COARSE` `new_cmd = 0u`) has been promoted, deprecated in favor of `vello_hybrid`, or patched to predicate overflow writes; check `flatten.wgsl` for changes to Euler-spiral stroke expansion (`EulerParams`).
4. **Xilem Core Combinators:** Diff `xilem_core/src/view.rs` (`trait View`), `xilem_core/src/views/lens.rs` (`for<'a> Fn(&'a mut ParentState) -> &'a mut ChildState`), and `xilem_core/src/views/one_of.rs` against `dc496876a2f6ff2ce7687bfc8c19bd311bb553dc`.
