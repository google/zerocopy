# Symbolic Strided Tile Splitting, Active-Mask Uninit-Padding Independence, and In-Place Stencil Framing

## Summary

Formal separation-logic verification and safe Rust encapsulation of zero-copy 2D and multi-plane media and scientific buffers (`Dav1dPicture` / `Rav1dPicture`, `AVFrame`, `halide_buffer_t`, `ndarray::ArrayViewMut2`, `imgref::ImgRefMut`) require five invariants absent from flat 1D slice models:

1. **Three-Mode Spatial Pinning (`.uninit`, `.readOnly`, `.readWrite`):** `zerocopy::FromBytes` (`zerocopy/src/lib.rs:4360–4363`) requires every byte in a `&[T]` / `&mut [T]` slice to be initialized (`AbsByte.init b`), forcing `memorysafety/rav1d` (`src/include/dav1d/picture.rs:566–578`, `src/picture.rs:117`) to zero-fill every newly allocated picture slab (`pool.pop_init(pic_cap, 0)`). Adding `.uninit` spatial-pin entry (`MaybeUninit<u8>` / raw-pointer slabs) admits uninitialized allocations in $O(1)$, transitions written tiles to `.readWrite`, freezes reference planes into duplicable `.readOnly` pins without rational fractional-permission blowup (Charguéraud & Pottier, ESOP 2017), and harvests active sub-rectangles back to pure matrices while discarding padding.
2. **`activeMask` Universal Demonic `Uninit`-Independence on SIMD Stride-Padding Tails:** Video planes pad row strides (`stride >= width * elemSize`) and append trailing slab slack (`RAV1D_PICTURE_ALIGNMENT = 64`) for wide vector loads/stores. Indexing spatial ownership by `activeMask (y, x) := y < height ∧ x < width` asserts `AbsByte.init (spec y x)` on active coordinates and `∃ ab : AbsByte` on inactive tail bytes `[width * elemSize, ownedSpan)`, forcing consumers via wand adjunction to prove universal demonic independence (`∀ padEnv`). In strict Rust/Miri semantics, typed vector loads (`Simd<u8, N>`) over `AbsByte.uninit` are immediate UB even when masked downstream; `.uninit` tails admit only `MaybeUninit<u8>` copies, disabled `simd_masked_load` lanes, or unmasked SIMD tail *stores*, whereas unmasked hardware overread *loads* require initialized (`∀ b : UInt8, AbsByte.init b`) `FrozenPad` slabs plus lane masking before horizontal reductions.
3. **$O(M+N)$ Symbolic Signed-Stride (`ptrdiff_t` / `isize`) Sub-Splits and `ownedSpan` Shedding:** Representing tiles symbolically as `(base, width, height, elemSize, ownedSpan, stride)` with `width * elemSize <= ownedSpan <= |stride|` replaces $O((WH)^2)$ pixel-list disjointness checks with $O(1)$ binary `splitRows`/`splitCols` arithmetic ($O(M + N)$ for $M \times N$ superblock grids). Supporting negative bottom-up strides (`FFmpeg` `AVFrame::linesize < 0`, `Halide` `begin_offset`, `rav1d` `pixel_offset`) and tight final rows (`imgref::valid_min_len`) requires two boundary laws: (a) empty splits (`r == height ∨ ownedSpan == 0` in `splitRows`; `height == 0 ∨ ownedSpan == c * elemSize` in `splitCols`) must **not** advance `base` via `inbounds` `ptr::offset`; and (b) `splitCols` at column $c$ **must** shrink the left tile's `ownedSpan` to $c \cdot \mathrm{elemSize}$ while transferring trailing row padding $S - c \cdot \mathrm{elemSize}$ exclusively to the right tile.
4. **Multi-Plane Chroma Ceiling-Shift Bounds:** Under `4:2:0` and `4:2:2` subsampling (`ss_hor, ss_ver ∈ {0, 1}`), normative chroma dimensions are $(W + \mathrm{ss\_hor}) \gg \mathrm{ss\_hor}$ and $(H + \mathrm{ss\_ver}) \gg \mathrm{ss\_ver}$ (`av1-spec` `08.decoding.process.md:3028–3032`, `FFmpeg` `AV_CEIL_RSHIFT`, `rav1d` `src/recon.rs:1880`). Floor-shifting `H >> 1` on odd-height frames under-allocates chroma by 1 row whenever 128-pixel superblock rounding (`rav1d` `src/picture.rs:78–80`) is absent.
5. **Tri-Partitioned In-Place Stencil and Causal IntraBC Framing:** Overlapping footprints ($R \cap W \neq \emptyset$) decompose into disjoint read-only $(R \setminus W)$, read-modify-write $(R \cap W)$, and `.uninit`-admissible write-only $(W \setminus R)$ regions without `False` self-conjunction. Across multi-step causal sweeps such as AV1 IntraBC (`allow_intrabc`), a monotone prefix $P_k = P_0 \cup \bigcup_{j < k} W_j$ separates sequential superblock-raster soundness (`rav1d` `src/decode.rs:1996–2019`) from hardware wavefront-cone soundness (`INTRABC_DELAY_PIXELS = 256`, `gradient = 5 + use_128x128_superblock` in `av1-spec` `07.bitstream.semantics.md:3097–3115`).

## Applicability

These findings govern memory representations, unsafe Rust slice/pointer wrappers, and separation-logic specifications across the nine subjects in `REPORT.json`:

- **AV1 Specification and Codec Implementations (`AOMediaCodec/av1-spec` @ `5e04f3f75e73a5898d7616c47c52f032144b8f80`, `memorysafety/rav1d` @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4`, `FFmpeg/FFmpeg` @ `e8574d0b22b126acc76007babce536c68bc07d0a`):** Covers `Dav1dPicture` / `Rav1dPicture` (`RAV1D_PICTURE_ALIGNMENT = 64`), `Rav1dPictureDataComponent`, `DisjointMut`, `WithOffset`, `Strided`, `AVFrame::linesize`, `AV_CEIL_RSHIFT`, AV1 IntraBC (`is_mv_valid`), and in-loop deblocking / CDEF (`backup2lines`, `backup2x8`) / Loop Restoration (`lr_stripe`).
- **Rust View Crates and Byte-Validity Traits (`rust-ndarray/ndarray` @ `53df84ade302c5d4d49b91aa6e4a18d252d26cc2`, `kornelski/imgref` @ `d4e4c27772b5767f078f17a210e54bcea2a31839`, `google/zerocopy` @ `88a13ae26ef3fe4623daf37347cfe0d7dea41698`, `rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd`):** Covers `ArrayViewMut::split_at`, `RawArrayView::split_at`, `ImgRefMut::sub_image_mut`, `zerocopy::{TryFromBytes, FromZeros, FromBytes, IntoBytes}`, `MaybeUninit`, and `inbounds` `ptr::offset` vs `wrapping_offset`.
- **Halide Runtime Buffers and Lean 4 Mechanization (`halide/Halide` @ `54c1a9bd6733081c8700a7c2521871161a701fad`, `leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`):** Covers `halide_dimension_t`, `halide_buffer_t::{begin_offset, end_offset}`, and `Classical.choice`-free Lean 4 tile-splitting and stencil-framing proofs.

**Prior Corpus Coverage:** Earlier reports cover scalar Rust byte initialization (`rust-validity-initialization-padding-and-transmute-semantics`), `zerocopy` trait rules (`zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`), 1D slice splitting (`borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits`), general Rust ownership verifiers (`rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`), and `AbsByte` lenses (`lean-absbyte-typedat-lenses-and-nondeterministic-alloc-scaling`). This report addresses 2D signed-stride tile algebras, `.uninit` slab entry with `activeMask` padding independence, multi-plane ceiling bounds, and overlapping/causal stencil framing.

## Findings

### 1. Three-Mode Spatial Pinning: `.uninit` Slab Entry, `.readWrite` Mutation, and Duplicable `.readOnly` Pins

`Basis: normative + documentation + source + derived`

#### 1.1 The `FromBytes` Initialization Barrier in `rav1d` and `zerocopy`

In `google/zerocopy` (`zerocopy/src/lib.rs:4360–4363`), `pub unsafe trait FromBytes: FromZeros` requires every byte of `&[T]` / `&mut [T]` to be initialized (`"any byte value which is not uninitialized"`). In `memorysafety/rav1d`, `DisjointMut<Rav1dPictureDataComponentInner>` (`src/disjoint_mut.rs:109–141, 320–332`) forms `&mut [u8]` via `&mut *index.get_mut(self.as_mut_slice())` and casts to `&mut [BD::Pixel]` via `V::mut_slice_from(bytes)`. Because `&mut [u8]` over `AbsByte.uninit` is immediate UB in Rust, `rav1d` had to tighten C's `Dav1dPicAllocator` contract (`src/include/dav1d/picture.rs:566–578`):

```rust
/// ### Additional `rav1d` requirement:
/// The allocated data must be initialized. ...
/// If the allocated data is not initialized,
/// it is possible there will be reads of uninitialized data.
```

Consequently, `dav1d_default_picture_alloc` (`src/picture.rs:115–117`) invokes `pool.pop_init(pic_cap, 0)`, zero-filling `y_sz + 2 * uv_sz + 64` bytes ($\approx 12.7\text{ MiB}$ per 4K 10-bit `4:2:0` frame) before decoding begins.

#### 1.2 Three-Permission Spatial Pinning Lattice

Separating layout ownership from byte initialization (cf. `ty_uninit` vs `r @ ty` in Sammler et al., *RefinedC*, PLDI 2021, DOI `10.1145/3453483.3454036`) requires three spatial permission modes $\mathsf{PinPerm} ::= \mathsf{.uninit} \mid \mathsf{.readWrite} \mid \mathsf{.readOnly}$ over `AbsByte := init (b : UInt8) | uninit`:

1. **Scratch / Slab Entry (`.uninit`):** $\mathsf{Pin}(\mathsf{.uninit}, D, \_) \triangleq \bigast_{a \in D} \exists ab : \mathsf{AbsByte},\; a \mapsto ab$. Fresh `MaybeUninit<u8>` allocations and dirty recycled pool buffers (`MemPool::push`, `src/picture.rs:163–165`) satisfy `.uninit` in $O(1)$ ghost steps with zero memory writes (Weakening: `.readWrite ⊢ .uninit`).
2. **Exclusive Mutation (`.readWrite`):** $\mathsf{Pin}(\mathsf{.readWrite}, D, \nu) \triangleq \bigast_{a \in D} a \mapsto \mathsf{init}(\nu(a))$. Full-tile reconstruction upgrades $\mathsf{Pin}(\mathsf{.uninit}, D, \_) \multimap \mathsf{Pin}(\mathsf{.readWrite}, D, \nu')$, after which $\nu'$ can be harvested back to a pure matrix value.
3. **Duplicable Shared Reference Pin (`.readOnly`):** Under fractional permissions $q \in (0, 1]$ (Bornat et al., POPL 2005, DOI `10.1145/1040305.1040327`), AV1 compound inter prediction (`08.decoding.process.md:2849–2851`) reading two potentially overlapping motion-vector blocks $(D'_0, D'_1)$ from the *same* reference frame (`NUM_REF_FRAMES = 8`) forces dynamic rational splitting. Using **temporary read-only permissions** (Charguéraud & Pottier, ESOP 2017, DOI `10.1007/978-3-662-54434-1_10`) or lifetime-indexed borrows $\mathsf{Pin}_\kappa(\mathsf{.readOnly}, D, \nu)$ yields free duplication ($\mathsf{Pin}_\kappa(\mathsf{.readOnly}, D, \nu) \dashv\vdash \mathsf{Pin}_\kappa(\mathsf{.readOnly}, D, \nu) \ast \mathsf{Pin}_\kappa(\mathsf{.readOnly}, D, \nu)$) and arbitrary overlapping sub-slice projection $D' \subseteq D$ throughout epoch $\kappa$, recovering `.uninit` / `.readWrite` slab ownership when $\kappa$ ends.

---

### 2. Active-Mask Universal Demonic `Uninit`-Independence on SIMD Stride-Padding Tails

`Basis: normative + source + execution + derived`

#### 2.1 Stride Padding in `rav1d`, `FFmpeg`, and `Halide`

Codecs decouple active row byte width $W \cdot e$ from byte stride $|s| \ge W \cdot e$:
- **`rav1d` (`src/picture.rs:96–106`, `src/include/dav1d/picture.rs:32–36`):** Rounds width up to 128 pixels (`aligned_w = (p.p.w + 127) & !127`), adds `RAV1D_PICTURE_ALIGNMENT = 64` bytes when `y_stride & 1023 == 0` to prevent power-of-two cache-set conflict misses, and pads total buffer capacity by `+ 64` bytes for SIMD overreads. Thus a $1900 \times 1080$ 8-bit luma plane has active width `1900` and `y_stride = 1920`, leaving a 20-byte inactive tail `[1900, 1920)` per row.
- **`FFmpeg` (`libavutil/frame.h:513–520`) & `Halide` (`HalideBuffer.h:53`):** Align `linesize` / allocations to 16–128 bytes beyond usable row width.

#### 2.2 `activeMask` Ownership, Access Regimes, and Leaky-Reduction Counterexample

For a tile $T$ with active byte width $W \cdot e$ and owned row span $S$ ($W \cdot e \le S \le |s|$), `activeMask(y, b) := b < W * e` splits each row into initialized active bytes and existentially quantified tail bytes:
$$\mathsf{TilePin}(\mathsf{.readWrite}, T, \nu) \triangleq \bigast_{y = 0}^{H - 1} \left( \left(\bigast_{b = 0}^{W \cdot e - 1} (\mathrm{row}(T, y) + b) \mapsto \mathsf{init}(\nu(y, b))\right) \ast \left(\bigast_{b = W \cdot e}^{S - 1} \exists ab : \mathsf{AbsByte},\; (\mathrm{row}(T, y) + b) \mapsto ab\right) \right)$$
By wand adjunction $(\exists ab,\, \ell \mapsto ab) \mathrel{-\!\ast} \mathsf{WP}\, c\, \{Q\} \iff \forall ab,\, (\ell \mapsto ab \mathrel{-\!\ast} \mathsf{WP}\, c\, \{Q\})$, consumers must be verified against a **demonic padding assignment** across two distinct operational regimes:

| Access Regime | Tail Byte Invariant | Sound Vector Operations Across `[W * e, S)` | Necessary Soundness Condition |
| :--- | :--- | :--- | :--- |
| **Strict `AbsByte` MIR / Miri** | `∀ ab : AbsByte` (admits `AbsByte.uninit`) | `MaybeUninit<u8>` copy; `simd_masked_load` (`mask[i] = 0` for $i \ge W$); **unmasked wide SIMD stores** overwriting `[W * e, S)` | Zero typed scalar/SIMD loads of `[W * e, S)`; postcondition re-quantifies `∃ ab : AbsByte` |
| **`FrozenPad` Overread Slab (`rav1d` `pop_init`)** | `∀ b : UInt8, AbsByte.init b` | Unmasked hardware vector loads (`vld1q_u8`, `_mm256_loadu_si256`) within `S` | **Observational independence:** $\forall p_1, p_2,\; \mathrm{eval}(c, \nu \cup p_1)|_{\mathsf{active}} = \mathrm{eval}(c, \nu \cup p_2)|_{\mathsf{active}}$ |

In Rust/Miri and LLVM IR (without `freeze`), loading `AbsByte.uninit` into typed `Simd<u8, 16>` is immediate UB *even if* inactive lanes are subsequently masked to zero. Conversely, under `FrozenPad` (established once by `pop_init` and preserved across dirty `MemPool` reuse without re-zeroing), unmasked loads are defined, but horizontal reductions (such as CDEF variance or Wiener sums in `rav1d` `src/cdef_apply.rs`) **violate** observational independence if `simd_reduce_add(v * v)` runs before zeroing inactive lanes (`pad ≡ 0` vs `pad ≡ 255` shifts the sum by $(16 - r) \cdot 65025$).

---

### 3. $O(M+N)$ Symbolic Signed-Stride Rectangle Sub-Splits and Zero-Extent Offset Guards

`Basis: source + execution + derived`

#### 3.1 Upstream 2D Strided Representation Matrix

| System / Crate | Stride Type & Sign | Negative-Stride Base Convention | Static Concurrent 2D `&mut` Splits | Boundary / Padding Constraint |
| :--- | :--- | :--- | :--- | :--- |
| **`FFmpeg` `AVFrame`** (`frame.h:496–525`) | `int linesize[8]` (signed bytes) | `data[p]` points to **logical row `0`** (near end of buffer for `linesize < 0`) | Manual raw pointer arithmetic | Unchecked C pointers; `INT_MIN` `abs` UB (`common.h:69`) |
| **`Halide` `halide_buffer_t`** (`HalideRuntime.h:1729–1907`) | `int32_t stride` (signed elements) | `host` at logical `min`; `begin_offset()` adds `(extent - 1) * stride` when `stride < 0` (`L1856–1865`) | `Buffer::crop` / `sliced` | `size_in_bytes()` (`L1896`) omits trailing stride slack on final row |
| **`rav1d` `Rav1dPictureDataComponent`** (`picture.rs:121–289`) | `isize` (signed bytes) | Normalizes `ptr` to lowest address (`ptr.offset(-stride).sub(len)` at `L165`); `pixel_offset` starts at `(len - |stride|) / bpp` (`L248`) | `DisjointMut` checks disjointness **in debug builds only** (`disjoint_mut.rs:60–73`) | Requires `len % 64 == 0` (`L114`) and initialized bytes (`L568`) |
| **`ndarray` `ArrayViewMut2`** (`impl_raw_views.rs:113–135`) | `isize` (signed elements) | `ptr` at logical `(0, 0)`; shifts up from slice start for negative strides (`constructors.rs:62`) | Safe `split_at(Axis(0\|1), idx) -> (Self, Self)` | Guards `index == len_of(axis)` (`L117`) and zeroes empty-shape strides (`constructors.rs:58`) |
| **`imgref` `ImgRefMut`** (`src/lib.rs:141–204, 381–399, 708–729`) | `usize` (unsigned pixels, `>= width > 0`) | **Cannot represent `stride < 0`** | `rows_mut()` only; **cannot split columns** into two `&mut` views (`L383–384`) | `valid_min_len = (H - 1)*stride + W` (`L718–720`): final row lacks `[W, stride)` tail |

#### 3.2 `SymbolicTile2D` Injectivity, `ownedSpan` Shedding, and Zero-Extent Guards

Define `SymbolicTile2D := (base : Int, width height elemSize ownedSpan : Nat, stride : Int)`. Under well-formedness $\mathsf{WF}(T, L)$—requiring $e > 0$, $W \cdot e \le S$, $0 \le \mathrm{base} \le L$ when $H = 0 \lor S = 0$, and $S \le |s|$ with extreme rows $\mathrm{base}$ and $\mathrm{base} + (H - 1)s$ inside $[0, L - S]$ when $H > 0 \land S > 0$—the address map $(y, b) \mapsto \mathrm{base} + y \cdot s + b$ is **globally injective** on $[0, H) \times [0, S)$: if $\mathrm{base} + y_1 s + b_1 = \mathrm{base} + y_2 s + b_2$ with $y_1 \neq y_2$, then $|y_1 - y_2| \cdot |s| = |b_2 - b_1| < S \le |s|$, impossible since $|y_1 - y_2| \ge 1$.

Exhaustive checking across 1,376 signed-stride and zero-extent cases (preserved in **Revalidation**) isolates two mandatory split invariants:

1. **Column-Split Padding-Shedding Law (`splitCols`):** On a row with $W = 24, e = 1, s = 32, S = 32$, splitting columns at $c = 16$ produces left width $16$ and right width $8$ at $\mathrm{base} + 16$. If the left sub-tile retained $\mathrm{ownedSpan}_L = 32$, its tail $[16, 32)$ would overwrite all 8 active pixels $[16, 24)$ of the right sub-tile! Sound `splitCols(T, c)` **must** set $\mathrm{ownedSpan}_L = c \cdot e$ (zero right-padding margin) and $\mathrm{ownedSpan}_R = S - c \cdot e$ (inheriting trailing row padding $[W \cdot e, S)$), achieving exact disjointness $\llbracket T_L \rrbracket \cap \llbracket T_R \rrbracket = \emptyset$ and conservation $\llbracket T_L \rrbracket \cup \llbracket T_R \rrbracket = \llbracket T \rrbracket$.
2. **Zero-Extent Pointer-Offset Guard (`splitRows` & `splitCols`):** Stepping `base + H * s` at $r = H$ under `stride < 0` wraps **below** `0` (`(H - 1)|s| - H|s| = -|s| < 0`, immediate `inbounds` `ptr::offset` UB!), and stepping `base + r * s` when `ownedSpan == 0` overflows empty/tight allocations (`L = 0`). Generalizing `ndarray`'s `index == len_of(axis)` check (`src/impl_raw_views.rs:117`), `splitRows` must keep `bot.base = T.base` whenever `r == T.height || T.ownedSpan == 0`, and `splitCols` must keep `right.base = T.base` whenever `T.height == 0 || T.ownedSpan == c * e` (or represent offsets via `wrapping_add_signed` as in `rav1d` `src/with_offset.rs:46`).

Partitioning an $M \times N$ grid executes $M - 1$ `splitRows` steps and $N - 1$ parameterized `splitCols` steps in $O(M + N)$ obligations instead of $O((WH)^2)$ pixel-pair checks.

---

### 4. Multi-Plane Chroma Ceiling-Shift Bounds Across Subsampling Layouts

`Basis: normative + source + execution + derived`

For subsampling shifts $(\mathrm{ss}_x, \mathrm{ss}_y) \in \{0, 1\}^2$, normative chroma dimensions use **ceiling shift** $(D + s) \gg s$:
- **AV1 (`08.decoding.process.md:3028–3032`):** `lastX = ((RefUpscaledWidth[refIdx] + subX) >> subX) - 1` and `lastY = ((RefFrameHeight[refIdx] + subY) >> subY) - 1`.
- **FFmpeg (`libavutil/common.h:60–61`):** `#define AV_CEIL_RSHIFT(a, b) (((a) + (1 << (b)) - 1) >> (b))`.
- **`rav1d` (`src/recon.rs:1805, 1880`):** `let h = refp.p.p.h + ss_ver >> ss_ver;`.

On any odd luma height $H = 2k + 1$ in `4:2:0` ($\mathrm{ss}_y = 1$), luma row $y = 2k$ accesses chroma row $y \gg 1 = k$, requiring $k + 1 = (H + 1) \gg 1$ rows; floor-shifting `H >> 1 = k` under-allocates by 1 row! Note that `Rav1dPictureParameters::pic_len` (`src/picture.rs:76–82`) writes `(aligned_h >> ss_ver)` safely *only* because `aligned_h = (h + 127) & !127` is already even (`aligned_h >> 1 == (aligned_h + 1) >> 1 >= (h + 1) >> 1`). Wrappers around unrounded external buffers **must** enforce $H_{\mathrm{alloc}}(p) \ge (H + \mathrm{ss}_y) \gg \mathrm{ss}_y$.

---

### 5. Tri-Partitioned In-Place Stencil Framing and Causal IntraBC Prefix Transfer

`Basis: normative + source + execution + derived`

1. **Single-Step Overlapping Stencils (`R ∩ W ≠ ∅`):** An 8-tap edge deblocking filter reads $R = [p_3..q_3]$ and mutates $W = [p_2..q_2] \subset R$ in-place. Because $\{R \mapsto -\} \ast \{W \mapsto -\}$ collapses to `False`, the **Tri-Partitioned Footprint Rule** splits $R \cup W$ into disjoint $D_{\mathsf{RO}} = R \setminus W$ (`.readOnly`), $D_{\mathsf{RW}} = R \cap W$ (`.readWrite`), and $D_{\mathsf{WO}} = W \setminus R$ (`.uninit`), producing $\mathsf{Pin}(\mathsf{.readOnly}, D_{\mathsf{RO}}, \nu) \ast \mathsf{Pin}(\mathsf{.readWrite}, D_{\mathsf{RW}} \cup D_{\mathsf{WO}}, \nu')$. By contrast, CDEF (`src/cdef_apply.rs:40–121`) and Loop Restoration (`src/lr_apply.rs:31–57`) read *pre-filter* top/left neighbors that in-place block updates would clobber, requiring explicit disjoint `.readOnly` staging copies (`backup2lines`, `backup2x8`, `lr_lpf_line`).
2. **Causal IntraBC (`allow_intrabc`) Monotone Prefix Transfer:** AV1 IntraBC (`07.bitstream.semantics.md:1457–1460`, `08.decoding.process.md:3016`) copies $R_k$ to $W_k$ within `CurrFrame` (disabling loop filters). Across steps $k = 0..K-1$, $(\bigcup_k R_k) \cap (\bigcup_k W_k) \neq \emptyset$. Maintaining $\mathsf{Pin}(\mathsf{.readWrite}, \bigcup_{j < k} W_j, \nu) \ast \mathsf{Pin}(\mathsf{.uninit}, \bigcup_{j \ge k} W_j, \_)$ and temporarily reborrowing causal prefix $\mathcal{A}(k) \subseteq \bigcup_{j < k} W_j$ as `.readOnly` requires $R_k \subseteq \mathcal{A}(k)$:
   - **Normative AV1 Wavefront Cone (`07.bitstream.semantics.md:3085–3116`, `03.symbols.md:45–46`):** Enforces `INTRABC_DELAY_PIXELS = 256` (`INTRABC_DELAY_SB64 = 4`), `-4` luma expansion on subsampled `<8` chroma blocks, and `srcSb64Col < activeSb64Col - 4 + (5 + use_128x128_superblock) * (activeSbRow - srcSbRow)`—sound under concurrent hardware/WPP superblock rows!
   - **`rav1d` Sequential Raster Relaxation (`src/decode.rs:1965–2019`):** Clips non-conformant vectors to tile bounds and rejects only `src_bottom > sby && src_right > sbx` (after clamping `src_bottom <= sby + sb_size`), which equals $R_k \subseteq \mathcal{A}_{\mathsf{seq}}(sby, sbx)$—memory-safe for single-thread-per-tile raster decoding, **but unsound** for intra-tile row parallelism.

---

### 6. Constructive Lean 4 Mechanization of Symbolic Strided Tiles and Stencil Framing

`Basis: derived`

The self-contained Lean 4 (`v4.34.1`) module below formalizes `AbsByte`, `SymbolicTile2D` injectivity over signed strides, `splitCols` disjointness with `ownedSpan` shedding, `activeMask` independence, tri-partition completeness, and ceiling chroma bounds without `Classical.choice` or `sorry`:

```lean
namespace SpatialTileTheory

inductive AbsByte where
  | uninit : AbsByte
  | init   : UInt8 → AbsByte
  deriving DecidableEq

inductive PinPerm where
  | uninit | readOnly | readWrite
  deriving DecidableEq

structure SymbolicTile2D where
  base      : Int
  width     : Nat
  height    : Nat
  elemSize  : Nat
  ownedSpan : Nat
  stride    : Int

def SymbolicTile2D.addr (t : SymbolicTile2D) (y b : Nat) : Int :=
  t.base + Int.ofNat y * t.stride + Int.ofNat b

def SymbolicTile2D.inOwned (t : SymbolicTile2D) (off : Int) : Prop :=
  ∃ y b : Nat, y < t.height ∧ b < t.ownedSpan ∧ t.addr y b = off

theorem row_addr_injective (t : SymbolicTile2D)
    (hSpan : t.ownedSpan ≤ Int.natAbs t.stride)
    {y1 y2 b1 b2 : Nat}
    (hb1 : b1 < t.ownedSpan) (hb2 : b2 < t.ownedSpan)
    (hEq : t.addr y1 b1 = t.addr y2 b2) :
    y1 = y2 ∧ b1 = b2 := by
  unfold SymbolicTile2D.addr at hEq
  have hDiff : (Int.ofNat y1 - Int.ofNat y2) * t.stride = Int.ofNat b2 - Int.ofNat b1 := by omega
  have hAbs := congrArg Int.natAbs hDiff
  rw [Int.natAbs_mul] at hAbs
  have hy : y1 = y2 := by
    by_cases hne : y1 = y2
    · exact hne
    · exfalso
      have hPosY : 1 ≤ Int.natAbs (Int.ofNat y1 - Int.ofNat y2) := by omega
      have hGe := Nat.le_mul_of_pos_left (Int.natAbs t.stride) hPosY
      omega
  subst hy
  exact ⟨rfl, by omega⟩

def SymbolicTile2D.splitRows (t : SymbolicTile2D) (r : Nat) :
    SymbolicTile2D × SymbolicTile2D :=
  let botBase := if r == t.height || t.ownedSpan == 0 then t.base else t.base + Int.ofNat r * t.stride
  ({ t with height := r }, { t with base := botBase, height := t.height - r })

def SymbolicTile2D.splitCols (t : SymbolicTile2D) (c : Nat) :
    SymbolicTile2D × SymbolicTile2D :=
  let lb := c * t.elemSize
  let rb := if t.height == 0 || t.ownedSpan == lb then t.base else t.base + Int.ofNat lb
  ({ t with width := c, ownedSpan := lb },
   { t with base := rb, width := t.width - c, ownedSpan := t.ownedSpan - lb })

theorem splitCols_disjoint (t : SymbolicTile2D) (c : Nat)
    (hc : c ≤ t.width) (hActive : t.width * t.elemSize ≤ t.ownedSpan)
    (hSpan : t.ownedSpan ≤ Int.natAbs t.stride) (off : Int) :
    ¬ (t.splitCols c).1.inOwned off ∨ ¬ (t.splitCols c).2.inOwned off := by
  by_cases hL : (t.splitCols c).1.inOwned off
  · right
    intro ⟨y2, b2, hy2, hb2, hEq2⟩
    rcases hL with ⟨y1, b1, hy1, hb1, hEq1⟩
    dsimp [SymbolicTile2D.splitCols, SymbolicTile2D.addr] at hy1 hb1 hEq1 hy2 hb2 hEq2
    have hLeftLe : c * t.elemSize ≤ t.width * t.elemSize := Nat.mul_le_mul_right t.elemSize hc
    have hNeSpan : t.ownedSpan ≠ c * t.elemSize := by omega
    have hNeH : t.height ≠ 0 := by omega
    simp [hNeH, hNeSpan] at hEq2
    have hComb : t.addr y1 b1 = t.addr y2 (c * t.elemSize + b2) := by
      unfold SymbolicTile2D.addr; omega
    have _ := row_addr_injective t hSpan (by omega) (by omega) hComb
    omega
  · exact Or.inl hL

def AgreeOnActive (active : Nat → Bool) (m1 m2 : Nat → UInt8) : Prop :=
  ∀ i : Nat, active i = true → m1 i = m2 i

def PaddingIndependent (activeIn activeOut : Nat → Bool)
    (kernel : (Nat → UInt8) → (Nat → UInt8)) : Prop :=
  ∀ m1 m2 : Nat → UInt8, AgreeOnActive activeIn m1 m2 → AgreeOnActive activeOut (kernel m1) (kernel m2)

inductive StencilZone where | readOnly | readWrite | writeOnly | frame deriving DecidableEq

def classifyZone (inR inW : Nat → Bool) (a : Nat) : StencilZone :=
  match inR a, inW a with
  | true, false => .readOnly | true, true => .readWrite
  | false, true => .writeOnly | false, false => .frame

theorem classifyZone_complete (inR inW : Nat → Bool) (a : Nat) :
    (classifyZone inR inW a = .readOnly  ↔ inR a = true  ∧ inW a = false) ∧
    (classifyZone inR inW a = .readWrite ↔ inR a = true  ∧ inW a = true)  ∧
    (classifyZone inR inW a = .writeOnly ↔ inR a = false ∧ inW a = true)  ∧
    (classifyZone inR inW a = .frame     ↔ inR a = false ∧ inW a = false) := by
  unfold classifyZone; cases inR a <;> cases inW a <;> decide

theorem chroma_ceil_shift_bounds_last_row (h ss : Nat) (hh : 0 < h) (hss : ss ≤ 1) :
    (h - 1) / (2 ^ ss) < (h + ss) / (2 ^ ss) := by
  cases ss with
  | zero => simp; omega
  | succ s => have hs0 : s = 0 := by omega; subst hs0; simp; omega

end SpatialTileTheory
```

## Boundaries

- **Nonlinear GPU Texture Swizzles (Morton / Block-Linear / AFBC):** **known not to apply** to affine `base + y * stride + b` tiles (covered in `carry-free-gpu-swizzle-algebras-and-height-monotone-fp-error-bounds`).
- **Unmasked Typed Vector Loads Over `AbsByte.uninit` Tails:** **known not to apply** in Rust/Miri and LLVM IR without `freeze` or `MaybeUninit`; unmasked overread loads require `simd_masked_load` or a `FrozenPad` slab invariant (`∀ b : UInt8, AbsByte.init b`).
- **Intra-Tile Row Parallelism Under `rav1d` IntraBC Clipping:** **known not to apply**; `rav1d`'s `src/decode.rs:1996–2019` check permits `< 256`-px intra-row/previous-row references valid only under sequential superblock raster order.
- **Negative Strides and Multi-Column `&mut` Splitting in `imgref`:** Explicitly **unsupported** in `kornelski/imgref` (`src/lib.rs:160, 383–384`).
- **Arm MTE / CHERI Sub-Granule Tag Sharing Across `splitCols`:** **not examined** on hardware; splits where $c \cdot e \bmod 16 \neq 0$ share 16-byte MTE tag granules despite byte-level disjointness.
- **Upstream `rav1d` Relaxation of `Dav1dPicAllocator` Zero-Initialization:** Whether `memorysafety/rav1d` will replace `&mut [u8]` slice casts in `DisjointMut` with `MaybeUninit<u8>` raw pointers to drop `src/include/dav1d/picture.rs:568` is **unknown**.

## Evidence

- **`memorysafety/rav1d` @ `2e7216c20ac2a75de204d6c8d7268b75a45959b4`:** `src/include/dav1d/picture.rs` (`L32–36, 143–173, 243–271, 524–537, 566–578`); `src/picture.rs` (`L75–148, 163–165`); `src/strided.rs` (`L5–45`); `src/with_offset.rs` (`L9–55, 97–123`); `src/disjoint_mut.rs` (`L21–73, 109–141, 318–350`); `src/decode.rs` (`L1965–2019`); `src/recon.rs` (`L1805, 1880`); `src/cdef_apply.rs` (`L40–121`); `src/lr_apply.rs` (`L31–57`).
- **`AOMediaCodec/av1-spec` @ `5e04f3f75e73a5898d7616c47c52f032144b8f80`:** `03.symbols.md` (`L45–47`); `06.bitstream.syntax.md` (`L302–330, 2793–2799`); `07.bitstream.semantics.md` (`L1457–1460, 3064–3123`); `08.decoding.process.md` (`L3014–3035`).
- **`FFmpeg/FFmpeg` @ `e8574d0b22b126acc76007babce536c68bc07d0a`:** `libavutil/frame.h` (`L496–525`); `libavutil/common.h` (`L60–61`).
- **`rust-ndarray/ndarray` @ `53df84ade302c5d4d49b91aa6e4a18d252d26cc2`:** `src/impl_views/splitting.rs` (`L92–98, 142–148`); `src/impl_raw_views.rs` (`L113–135`); `src/impl_views/constructors.rs` (`L53–108`); `src/dimension/mod.rs` (`L48–62`).
- **`kornelski/imgref` @ `d4e4c27772b5767f078f17a210e54bcea2a31839`:** `src/lib.rs` (`L141–179, 288–320, 381–399, 708–729`).
- **`halide/Halide` @ `54c1a9bd6733081c8700a7c2521871161a701fad`:** `src/runtime/HalideBuffer.h` (`L53`); `src/runtime/HalideRuntime.h` (`L1729–1757, 1852–1907`).
- **`google/zerocopy` @ `88a13ae26ef3fe4623daf37347cfe0d7dea41698` & `rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd`:** `zerocopy/src/lib.rs` (`L1967, 3770, 4353–4383, 6000–6030`).
- **Literature & Execution (`2026-11-20`):** Charguéraud & Pottier, ESOP 2017 (`10.1007/978-3-662-54434-1_10`); Sammler et al., PLDI 2021 (`10.1145/3453483.3454036`); Bornat et al., POPL 2005 (`10.1145/1040305.1040327`); Liu et al., POPL 2022 (`10.1145/3498717`). Exhaustive Python probe (preserved below) verified 1,376 signed-stride/zero-extent split cases, 16-byte naive column-tail overlap, and odd-height `4:2:0` ceiling bounds.

## Revalidation

1. **Upstream Source Diffs (< 2 minutes):** Diff `Dav1dPicAllocator` (`src/include/dav1d/picture.rs`), `DisjointMut` (`src/disjoint_mut.rs`), and IntraBC clipping (`src/decode.rs`) in `memorysafety/rav1d`, plus `RawArrayView::split_at` (`src/impl_raw_views.rs`) in `rust-ndarray/ndarray`.
2. **Standalone Discriminator Probe (`python3` stdlib, < 0.2s):**
   ```python
   def revalidate_tiles():
       checked = 0
       for stride in (-32, -24, 24, 32):
           abs_s = abs(stride)
           for h in (0, 1, 3, 5):
               for w in (0, 4, 10, 12):
                   if w * 2 > abs_s:
                       continue
                   for span in (w * 2, abs_s):
                       alloc = 64 if (h == 0 or span == 0) else (h - 1) * abs_s + span
                       base = 0 if (h == 0 or span == 0 or stride > 0) else (h - 1) * abs_s
                       pts = {base + y * stride + b for y in range(h) for b in range(span)}
                       assert all(0 <= p < alloc for p in pts) and len(pts) == h * span
                       for r in range(h + 1):
                           bb = base if (r == h or span == 0) else base + r * stride
                           T1 = {base + y * stride + b for y in range(r) for b in range(span)}
                           T2 = {bb + y * stride + b for y in range(h - r) for b in range(span)}
                           assert T1.isdisjoint(T2) and (T1 | T2) == pts
                           checked += 1
                       for c in range(w + 1):
                           lb = c * 2
                           rb = base if (h == 0 or span == lb) else base + lb
                           L = {base + y * stride + b for y in range(h) for b in range(lb)}
                           R = {rb + y * stride + b for y in range(h) for b in range(span - lb)}
                           assert L.isdisjoint(R) and (L | R) == pts
                           checked += 1
       assert checked == 1376
       assert [h for h in range(1, 33) if ((h - 1) >> 1) >= (h >> 1)] == list(range(1, 33, 2))
   revalidate_tiles()
   ```
3. **Lean 4 Kernel Check:** Typecheck `SpatialTileTheory` on `leanprover/lean4` (`v4.34.1`+) and verify `#print axioms SpatialTileTheory.splitCols_disjoint` reports no `Classical.choice` or `sorryAx`.
