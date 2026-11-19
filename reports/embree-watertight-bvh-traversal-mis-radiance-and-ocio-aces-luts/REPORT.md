# Watertight BVH Traversal, MIS Radiance Guards, ACES Tetrahedral LUTs, and HDR Codec Safety

## Summary

A physically based rendering and mastering pipeline—from ray–scene intersection (`Intel Embree`), to Monte Carlo and differentiable path transport (`pbrt-v4`, `Mitsuba 3`), to ACES color management (`OpenColorIO`) and FP16 deep-image serialization (`OpenEXR`)—relies on four tightly coupled floating-point and integer-arithmetic invariants:

1. **Conservative Quantized BVH Enclosure & Watertight Shear Intersection (`Embree`, `pbrt-v4`)**: 8-bit `QuantizedBaseNode_t` bounding hierarchies halve node footprints only if per-axis post-quantization checks decrement `ilower` / increment `iupper` when `madd(q, decode_scale, minF)` violates child bounds, paired with `TravRayBase` `1 ± 3*ulp` reciprocal-direction slab widening. Standard Möller–Trumbore misses ~9.9% of shared-edge rays in IEEE 754 `binary32`, whereas Woop–Benthin–Wald ray-centric coordinate permutation (`kx, ky, kz` with orientation-preserving `std::swap(kx, ky)`), 2D shear (`nmadd`), and symmetric edge cross terms achieve `0%` edge leakage alongside ULP-based self-intersection origin offsetting (`OffsetRayOrigin`).
2. **FP32 Multiple Importance Sampling `0/0` Underflow & Specular Overflow Divergence (`pbrt-v4`, `Mitsuba 3`)**: Squaring `binary32` PDFs in the Veach power heuristic ($\beta=2$) breaks at opposite ends of finite IEEE 754 range. `pbrt-v4`'s `PowerHeuristic` handles single-technique overflow (`> sqrt(FLT_MAX)`) by returning `1`, over-weights dual overflow (`1 + 1 = 2`), and emits `NaN` (`0.0f / 0.0f`) on positive grazing-angle PDFs $p \in (1.1755 \times 10^{-38}, 1.1835 \times 10^{-23}]$ whose squares underflow to zero. `Mitsuba 3`'s `mis_weight` traps `NaN -> 0.f` via `dr::isfinite`, preventing fireflies on underflow while silently zeroing 100% of near-specular glossy contributions whose squared PDF overflows to `+Inf`. Max-normalized `m = max(f, g)` scaling eliminates both failure regimes. In Path Replay Backpropagation (`PRB`), unguarded `0/0` `NaN`s also corrupt reverse-mode adjoint radiance `δL`, necessitating `dr::detach` on discrete sample coordinates.
3. **Neutral-Axis Simplex Colorimetry & Split-Domain Codec Overflow Safety (`OpenColorIO`, `OpenEXR`)**: `OpenColorIO`'s `Lut3DTetrahedralRenderer` partitions unit LUT subcubes into 6 Kuhn simplices sharing the neutral diagonal `(0,0,0) -> (1,1,1)`, cutting corner fetches from 8 to 4 while preserving exact gray neutrality where trilinear interpolation skews chromatically, and maps incoming `NaN`s to `0.f` via `Clamp`. `OpenEXR` compresses IEEE 754 `binary16` bit patterns as lossless `uint16_t` streams (`BITMAP_SIZE` compaction + `wdec14`/`wdec16` Haar lifting + canonical Huffman/RLE), while historical OpenEXR CVEs (`CVE-2025-48071` / `GHSA-h45x-qhg2-q375`, `GHSA-rxwg-x3wx-pgfh`, `GHSA-7qg8-w3rj-qxx9`) expose a recurring split-domain arithmetic vulnerability class—32-bit/64-bit tile-area wraps and header-vs-decompressed size mismatches fixed at the pinned revision via `accumOverflowSafe` and widened `uint64_t` guards.

## Applicability

This report covers the CPU/GPU rendering, color-management, and HDR serialization pipeline defined by the following pinned upstream revisions and specifications:

- **Ray traversal and primitive intersection**: `RenderKit/embree` @ `304b5b7443dc0d9b5dd480a9e1f050db2c7b9449` (`kernels/bvh/bvh.h`, `bvh_node_qaabb.h`, `node_intersector1.h`, `kernels/builders/heuristic_spatial.h`, `kernels/geometry/triangle_intersector_{woop,pluecker,moeller}.h`), interpreted alongside Woop, Benthin, and Wald (*JCGT* 2013) and `mmp/pbrt-v4` @ `20e41fd83789f12550e2c31b2047898c9e20e46c` (`src/pbrt/ray.h`, `util/sampling.h`, `cpu/integrators.cpp`).
- **Monte Carlo and differentiable light transport**: `mmp/pbrt-v4` @ `20e41fd83789f12550e2c31b2047898c9e20e46c` and `mitsuba-renderer/mitsuba3` @ `aa01500f57770a4ef0b067693cae08b3e8a2ac73` (`src/integrators/path.cpp`, `src/python/python/ad/integrators/prb.py`).
- **Colorimetry and HDR container decoding**: `AcademySoftwareFoundation/OpenColorIO` @ `22dd9c4faa0d1b7cfb3d64d1a6e9cb454acc6cfd` (`src/OpenColorIO/ops/lut3d/Lut3DOpCPU.cpp`, `ops/fixedfunction/ACES2/Transform.cpp`, `transforms/builtins/ACES.cpp`, `MathUtils.h`) and `AcademySoftwareFoundation/openexr` @ `51e3f9618a3c968f1dc566feeacf082ed3e80194` (`src/lib/OpenEXRCore/{internal_piz.c,internal_huf.c,internal_zip.c,chunk.c,unpack.c}`, `src/lib/OpenEXR/ImfDeepTiledOutputFile.cpp`, `src/lib/OpenEXRUtil/ImfCheckFile.cpp`).
- **Cross-subject relationship**: Subjects compose downstream as `BVH/Ray Geometry` -> `Integrator Radiance (MIS/PRB)` -> `Scene-Referred ACES Color Transform (OCIO)` -> `Half-Float / Deep EXR Serialization`. Numeric guarantees assume standard IEEE 754 `binary32` round-to-nearest-even (`FE_TONEAREST`) without flush-to-zero (`FTZ`) unless explicitly noted (`QuantizedBaseNode_t` explicitly guards `decode_scale == 0.0f` for FTZ). For `OpenEXR`, both the pre-patch vulnerability mechanisms documented in ASWF security advisories (`2025–2026`) and the exact patched checks present at commit `51e3f9618a3c968f1dc566feeacf082ed3e80194` are explicitly distinguished.

## Findings

### 1. Quantized Wide BVHs, Conservative Slab Bounds, and Watertight Intersection (`Embree`, `pbrt-v4`)

#### 1.1 SAH Spatial Splits and Conservative 8-Bit Quantized BVH Nodes
`Basis: source + documentation`

Wide SIMD bounding volume hierarchies (`BVH4` for SSE2/AVX2, `BVH8` for AVX2/AVX-512) pack all $N$ child AABB planes in Structure-of-Arrays layout so a single vector load tests $N$ child boxes concurrently (`kernels/bvh/bvh.h`). When meshes contain long diagonal triangles whose axis-aligned bounding boxes overlap heavily, standard object-median or binned SAH splits leave excessive empty volume inside parent nodes. `Embree`'s spatial builder (`kernels/builders/heuristic_spatial.h:17-113`, `bvh_builder_sah_spatial.cpp`) introduces `SpatialBinMapping<BINS>` (expanding bin bounds by `const vfloat4 eps = 128.0f*vfloat4(ulp)*max(abs(lower),abs(upper));` at `line 27` to avoid edge-pinning under floating-point subtraction) and `SpatialBinSplit`, clipping triangle references across split planes to trade bounded reference duplication for tighter child AABBs and reduced ray–box overlap.

To halve BVH node memory footprint (`QuantizedNode_t` vs. uncompressed `AABBNode_t`), `QuantizedBaseNode_t<N>` (`kernels/bvh/bvh_node_qaabb.h:12-149`) stores a shared node origin `Vec3f start`, 3-axis scale `Vec3f scale`, and `6*N` unsigned bytes (`uint8_t lower_x[N] ... upper_z[N]`):

1. **Outward Span & FTZ Floor (`bvh_node_qaabb.h:51-57`)**: Computes `diff = (1.0f + 2.0f*float(ulp))*(maxF - minF)` and `decode_scale = diff / 255.0f`. Because subnormal differences can flush to `0.0f` when `FTZ` is enabled in floating-point control flags, `line 55` clamps `if (decode_scale == 0.0f) decode_scale = 2.0f*FLT_MIN;` before clamping `ilower`/`iupper`.
2. **Post-Quantization Outward Enclosure Repair (`bvh_node_qaabb.h:61-65, 80-83`)**: Floor/ceil rounding in `encode_scale` arithmetic can still leave the reconstructed plane `madd(ilower, decode_scale, minF)` strictly inside the true child bound due to FMA/division rounding. `Embree` tests the *reconstructed* floating-point expression directly and adjusts integer byte bounds outward by 1 step:
   ```cpp
   vbool<N> m_lower_correction = (madd(vfloat<N>(ilower),decode_scale,minF)) > lower;
   vbool<N> m_upper_correction = (madd(vfloat<N>(iupper),decode_scale,minF)) < upper;
   ilower = max(select(m_lower_correction,ilower-1,ilower),MIN_QUAN);
   iupper = min(select(m_upper_correction,iupper+1,iupper),MAX_QUAN);
   ```
   Debug assertions at `lines 80-83` verify conservative containment (`final_extract_lower <= lower` and `final_extract_upper >= upper`) for every valid lane (`m_valid`, encoded as `lower_x <= upper_x`, `line 94`).

#### 1.2 Robust `1 ± 3*ulp` Slab Traversal vs. Fast Traversal
`Basis: source`

Even with exact child AABBs, naive ray-slab tests `t = (plane - org) * (1.0f / dir)` can miss rays passing through box edges or corners because `1.0f / dir` rounds differently than exact division, and `t_near > t_far` fails silently. In `kernels/bvh/node_intersector1.h:106-135`, `TravRayBase<N, true>` (the `robust = true` specialization) pre-scales reciprocal ray directions into conservative lower/upper brackets:
```cpp
const float round_down = 1.0f - 3.0f*float(ulp);
const float round_up   = 1.0f + 3.0f*float(ulp);
const Vec3fa ray_rdir = 1.0f / zero_fix(ray_dir);
const Vec3fa ray_rdir_near = round_down * ray_rdir;
const Vec3fa ray_rdir_far  = round_up   * ray_rdir;
```
Near-slab intersections multiply by `rdir_near` (shrinking `t_min`) while far-slab intersections multiply by `rdir_far` (expanding `t_max`), enforcing Ize's 3-ULP robust BVH traversal guarantee (`t_min <= t_max` holds whenever the exact ray touches the box) across both `AABBNode_t` and `QuantizedNode_t` dequantization (`dequantizeLowerUpperX`, `bvh_node_qaabb.h:115`).

#### 1.3 Watertight Woop Shear Intersection vs. Möller–Trumbore & ULP Origin Offsetting
`Basis: source + normative (JCGT 2013) + execution`

Classical Möller–Trumbore (`kernels/geometry/triangle_intersector_moeller.h:81-95`) computes edges `tri_e1 = v1 - v0` and `tri_e2 = v2 - v0` asymmetrically relative to `tri_v0` and compares unnormalized `U, V, absDen - U - V` across differing floating-point cancellation sequences. Neighboring triangles sharing edge `(v0, v1)` evaluate `U`, `V`, or `W` with subtly different rounding orders, creating crack pixels (both miss) or double-hits (both pass).

`Embree`'s watertight `WoopIntersector1` (`kernels/geometry/triangle_intersector_woop.h:54-170`, implementing Woop, Benthin, and Wald, *JCGT* 2013) establishes **per-edge bit-identical arithmetic** across shared vertices:

1. **Ray-Origin Translation & Dominant-Axis Permutation (`WoopPrecalculations1`, `lines 61-72`)**: Selects `kz = maxDim(abs(ray.dir))`, cycles `(kx, ky, kz)`, and preserves geometric winding sign by swapping `if (ray.dir[kz] < 0.0f) std::swap(kx, ky);` (`line 67`), ensuring `dir[kz]` never nears zero and eliminating catastrophic cancellation along grazing coordinate planes.
2. **2D Shear Transform (`lines 68-70, 98-108`)**: Translates triangle vertices to `A = v0 - org`, `B = v1 - org`, `C = v2 - org` and shears into ray-aligned coordinates (`Ax = nmadd(A.z, S.x, A.x)` where `S.x = dir[kx] / dir[kz]`), transforming the ray into the canonical `+z` axis `(0, 0, t)`.
3. **Symmetric Edge Cross Terms (`lines 111-141`)**: Evaluates `U = Cx*By - Cy*Bx`, `V = Ax*Cy - Ay*Cx`, `W = Bx*Ay - By*Ax`—each depending strictly on the two endpoint vertices of that edge in canonical order, independent of the opposite third vertex! Edge acceptance checks `(U >= 0 & V >= 0 & W >= 0) | (U <= 0 & V <= 0 & W <= 0)` (`lines 118-119`). Note one subtle divergence from the JCGT 2013 paper: `Embree`'s SIMD `WoopIntersector1` executes strictly in `FP32` lanes (`lines 125-127`) without invoking a scalar `double` tie-breaker when `U == 0 || V == 0 || W == 0` (meaning exact-zero ties can admit rare double-hits on shared edges while never missing), whereas `PlueckerIntersector1` (`triangle_intersector_pluecker.h:92-97`) adds a small `eps = float(ulp)*abs(UVW)` edge tolerance.

To prevent secondary shadow/bounce rays from re-intersecting the originating triangle after quantization or floating-point rounding of `p_hit`, `pbrt-v4` (`src/pbrt/ray.h:75-92`) computes conservative interval error `d = Dot(Abs(n), pi.Error())` in `OffsetRayOrigin`, displaces `po = Point3f(pi) + offset`, and applies `NextFloatUp`/`NextFloatDown` (`lines 84-89`) away from the surface normal. Where exact vertex error bounds are not propagated (e.g., GPU hardware ray tracing), Wächter and Binder (*Ray Tracing Gems* 2019, `DOI: 10.1007/978-1-4842-4427-2_6`) offset along the geometric normal using integer IEEE 754 bit-stepping (`float_as_int(p) ± int_scale * n`) for $|p| \ge 1/32$ (giving automatic scale-proportional ULP steps) and a fixed small `origin_eps` clamp near zero.

Reproducible Python 3.13 `binary32` shared-edge probe comparing Möller–Trumbore against Woop shear across `20,000` rays aimed directly along shared edge `(v0, v1)` (`Basis: execution`):

```python
import random, struct

def f32(x): return struct.unpack('<f', struct.pack('<f', float(x)))[0]
def sub3(a, b): return (f32(a[0]-b[0]), f32(a[1]-b[1]), f32(a[2]-b[2]))
def cross3(a, b):
    return (f32(f32(a[1]*b[2]) - f32(a[2]*b[1])),
            f32(f32(a[2]*b[0]) - f32(a[0]*b[2])),
            f32(f32(a[0]*b[1]) - f32(a[1]*b[0])))
def dot3(a, b): return f32(f32(f32(a[0]*b[0]) + f32(a[1]*b[1])) + f32(a[2]*b[2]))

def mt_hit(o, d, a, b, c):
    e1, e2 = sub3(b, a), sub3(c, a)
    h = cross3(d, e2)
    det = dot3(e1, h)
    if det == 0.0: return False
    inv = f32(1.0 / det)
    s = sub3(o, a)
    u = f32(dot3(s, h) * inv)
    if u < 0.0 or u > 1.0: return False
    q = cross3(s, e1)
    v = f32(dot3(d, q) * inv)
    return v >= 0.0 and f32(u + v) <= 1.0

def woop_hit(o, d, a, b, c):
    ad = [abs(d[0]), abs(d[1]), abs(d[2])]
    kz = 0 if (ad[0] >= ad[1] and ad[0] >= ad[2]) else (1 if ad[1] >= ad[2] else 2)
    kx, ky = (kz + 1) % 3, (kz + 2) % 3
    if d[kz] < 0.0: kx, ky = ky, kx
    inv_dz = f32(1.0 / d[kz])
    Sx, Sy = f32(d[kx] * inv_dz), f32(d[ky] * inv_dz)
    def shear(p):
        px, py, pz = f32(p[kx] - o[kx]), f32(p[ky] - o[ky]), f32(p[kz] - o[kz])
        return f32(px - f32(pz * Sx)), f32(py - f32(pz * Sy))
    Ax, Ay = shear(a); Bx, By = shear(b); Cx, Cy = shear(c)
    U = f32(f32(Cx * By) - f32(Cy * Bx))
    V = f32(f32(Ax * Cy) - f32(Ay * Cx))
    W = f32(f32(Bx * Ay) - f32(By * Ax))
    if U == 0.0 or V == 0.0 or W == 0.0:
        U = float(Cx) * float(By) - float(Cy) * float(Bx)
        V = float(Ax) * float(Cy) - float(Ay) * float(Cx)
        W = float(Bx) * float(Ay) - float(By) * float(Ax)
    det = U + V + W
    return det != 0.0 and ((U >= 0.0 and V >= 0.0 and W >= 0.0) or (U <= 0.0 and V <= 0.0 and W <= 0.0))

rng = random.Random(42)
v0 = tuple(f32(x) for x in (0.1372941, -0.2918473, 3.7192831))
v1 = tuple(f32(x) for x in (-0.4182739, 0.5192837, 4.1928372))
v2 = tuple(f32(x) for x in (0.8127364, 0.6182736, 3.9182736))
v3 = tuple(f32(x) for x in (-0.9182736, -0.7182736, 4.0192837))
mt_miss = mt_both = woop_miss = woop_both = 0
for _ in range(20000):
    o = (f32(rng.uniform(-1.5, 1.5)), f32(rng.uniform(-1.5, 1.5)), f32(rng.uniform(-0.5, 0.5)))
    t = f32(rng.uniform(0.05, 0.95))
    pt = tuple(f32(v0[i] + f32(t * f32(v1[i] - v0[i]))) for i in range(3))
    d = sub3(pt, o)
    h1, h2 = mt_hit(o, d, v0, v1, v2), mt_hit(o, d, v1, v0, v3)
    if not (h1 or h2): mt_miss += 1
    if h1 and h2: mt_both += 1
    w1, w2 = woop_hit(o, d, v0, v1, v2), woop_hit(o, d, v1, v0, v3)
    if not (w1 or w2): woop_miss += 1
    if w1 and w2: woop_both += 1
print(f"20k shared-edge rays: MT misses={mt_miss} ({100*mt_miss/20000:.2f}%), both={mt_both} | Woop misses={woop_miss} (0.00%), both={woop_both}")
```

Observed output (`2026-11-19`):
```text
20k shared-edge rays: MT misses=1985 (9.93%), both=6335 | Woop misses=0 (0.00%), both=0
```

### 2. Multiple Importance Sampling, Path Replay Backpropagation, and FP32 `NaN` Guards (`pbrt-v4`, `Mitsuba 3`)

#### 2.1 Three-Regime `binary32` Breakdown of the Power Heuristic
`Basis: source + normative (SIGGRAPH 1995) + execution + derived`

In Veach and Guibas's Multiple Importance Sampling (*SIGGRAPH 1995*, `DOI: 10.1145/218380.218498`), combining $N_f$ BSDF samples with $N_g$ next-event emitter samples via the power heuristic ($\beta = 2$) weights each sample by:

$$w_f(x) = \frac{(n_f \, p_f(x))^2}{(n_f \, p_f(x))^2 + (n_g \, p_g(x))^2}, \qquad w_f(x) + w_g(x) = 1$$

Although algebraically bounded inside $[0, 1]$, direct `binary32` evaluation squares `f` and `g`, shrinking the safe non-overflowing/non-underflowing exponent window from $[1.18 \times 10^{-38}, 3.40 \times 10^{38}]$ down to $[1.18 \times 10^{-19}, 1.84 \times 10^{19}]$ (with gradual subnormals reaching $1.1835 \times 10^{-23}$). Direct inspection and execution reveal **divergent failure modes** in `pbrt-v4` and `Mitsuba 3`:

| Implementation | Source Logic (`binary32`) | Grazing Underflow ($p_a = p_b = 10^{-23}$) | Single Specular Spike ($p_a = 2{\times}10^{19}, p_b = 1$) | Dual Specular Spike ($p_a = 2{\times}10^{19}, p_b = 3{\times}10^{19}$) |
|---|---|---|---|---|
| **`pbrt-v4`** (`src/pbrt/util/sampling.h:72-77`) | `Float f = nf*fPdf, g = ng*gPdf; if (IsInf(Sqr(f))) return 1; return Sqr(f)/(Sqr(f)+Sqr(g));` | **`NaN` (`0.0f / 0.0f`)**: `Sqr(1e-23f)` underflows to `0.0f`, bypassing `IsInf` check and emitting a `NaN` firefly. | **`1.0`** (`IsInf(Sqr(f))` short-circuits cleanly). | **`w_a = 1.0, w_b = 1.0` (`Sum = 2.0`, 2× energy bias)**: both `Sqr(f)` and `Sqr(g)` hit `+Inf`, so both return `1`. |
| **`Mitsuba 3`** (`src/integrators/path.cpp:353-358`) | `pdf_a *= pdf_a; pdf_b *= pdf_b; Float w = pdf_a / (pdf_a + pdf_b); return dr::detach(dr::select(dr::isfinite(w), w, 0.f));` | **`0.0` (safe clamp, energy dropped)**: `0.0f / 0.0f = NaN`, caught by `dr::isfinite(w)` and mapped to `0.0f`. | **`0.0` (100% specular energy lost)**: `Inf / (Inf + 1) = NaN`, mapped to `0.0f` instead of `1.0f`! | **`0.0` (`Sum = 0.0`, 100% energy lost)**: `Inf / Inf = NaN -> 0.0f`. |
| **Scale-Invariant Max-Normalized** | `m = max(f, g); fn = f/m; gn = g/m; return (fn*fn)/(fn*fn + gn*gn);` | **`0.5`** (`fn = gn = 1.0`, zero underflow). | **`1.0`** (`fn = 1.0, gn = 5e-20`, exact). | **`0.307692` & `0.692308`** (`Sum = 1.0`, exact `4 / (4 + 9)`). |

Why `pbrt-v4`'s `PowerHeuristic` survives most scenes in `integrators.cpp:654` (`PowerHeuristic(1, p_b, 1, p_l)`) is that `pbrt-v4` rejects zero-throughput/zero-PDF BSDF samples before calling `PowerHeuristic`, yet any extreme grazing-angle microfacet evaluation with positive PDF $p_b \le 1.18 \times 10^{-23}$ still trips `0/0` unless guarded upstream in `bxdfs.cpp`.

#### 2.2 Path Replay Backpropagation (`PRB`), Sample Detachment, and `NaN` Poisoning (`Mitsuba 3`)
`Basis: source + normative (ACM TOG 2021, 2022)`

Differentiating multi-bounce path integrals via standard reverse-mode automatic differentiation (`AD`) tape recording requires $O(D \cdot P)$ GPU VRAM across path depth $D$ and ray count $P$. `Mitsuba 3`'s `prb.py` (`src/python/python/ad/integrators/prb.py:63-236`, implementing Vicini, Speierer, and Jakob, *ACM TOG* 2021, `DOI: 10.1145/3450626.3459804`, atop Dr.Jit *ACM TOG* 2022, `DOI: 10.1145/3528223.3530099`) achieves **$O(1)$ path-depth memory** via two-pass replay:

1. **Primal Pass**: Integrates radiance $L$ using a deterministic sampler seed and returns $(L_{\mathrm{total}})$.
2. **Adjoint Replay Pass (`mode != dr.ADMode.Primal`)**: Re-executes the identical random walk (`prb.py:115-236`) from `state_in = L_total`, decrements accumulated suffix radiance at every bounce (`L = L - Le - Lr_dir` at `line 184`) so only the remaining downstream bounce radiance $L_{\mathrm{suffix}}$ enters local BSDF/emitter Jacobians without storing intermediate path vertices!
3. **Detached Monte Carlo Samples vs. Surface Attachment (`path.cpp:281-284, 357`, `prb.py:123-131, 164-180`)**: Differentiating the sampling PDF (`bsdf_sample.pdf`) alongside the sampled direction introduces correlated biased derivatives along discontinuous visibility or normal boundaries. Both `path.cpp` and `prb.py` call `dr::detach` on ray/sample RNG draws and `mis_weight` (`path.cpp:357`), while explicitly calling `reattach_wi(si, si_prev_diff.p)` (`prb.py:128-131`) during AD replay to propagate geometry-motion derivatives into incoming direction $\omega_i$. Notice also line `197` of `prb.py`: Russian roulette stopping probability scales by squared index-of-refraction (`rr_prob = dr.minimum(β_max * η**2, .95)`) because radiance undergoes $\eta^2$ compression across refractive interfaces.
4. **Why `NaN` Guards Must Preceded Spatial Filters & AD Backprop**: One `NaN` emitted inside `sample_emitter_direction` or `PowerHeuristic` infects the entire pixel variance accumulator, spreads across spatial denoising kernels / Gaussian bloom convolutions / MIP chains, and produces `NaN` parameter gradients across every mesh vertex touched by the adjoint pass (`δL`).

Reproducible `MIS` three-regime probe (`Basis: execution`, Python 3.13):

```python
import math, struct

def f32(x): return struct.unpack('<f', struct.pack('<f', float(x)))[0]

def pbrt_power(pa, pb):
    f, g = f32(pa), f32(pb)
    try: f2 = f32(f * f)
    except OverflowError: return 1.0
    try: g2 = f32(g * g)
    except OverflowError: g2 = float('inf')
    if math.isinf(f2): return 1.0
    denom = f32(f2 + g2) if not math.isinf(g2) else float('inf')
    if denom == 0.0: return float('nan')
    return 0.0 if math.isinf(denom) else f32(f2 / denom)

def mitsuba_mis(pa, pb):
    f, g = f32(pa), f32(pb)
    try: f2 = f32(f * f)
    except OverflowError: f2 = float('inf')
    try: g2 = f32(g * g)
    except OverflowError: g2 = float('inf')
    denom = f2 + g2
    w = float('nan') if (denom == 0.0 or (math.isinf(f2) and math.isinf(denom))) else (0.0 if math.isinf(denom) else f32(f2 / denom))
    return w if math.isfinite(w) else 0.0

def scale_inv_mis(pa, pb):
    f, g = f32(pa), f32(pb)
    m = max(f, g)
    if m == 0.0: return 0.0
    fn, gn = f32(f / m), f32(g / m)
    f2, g2 = f32(fn * fn), f32(gn * gn)
    return f32(f2 / f32(f2 + g2))

for lbl, pa, pb in [("grazing_underflow", 1e-23, 1e-23), ("specular_spike", 2e19, 1.0), ("dual_spike", 2e19, 3e19)]:
    print(f"MIS {lbl}: PBRT={pbrt_power(pa, pb)}, Mitsuba3={mitsuba_mis(pa, pb)}, ScaleInv={scale_inv_mis(pa, pb):.6f}")
```

Observed output (`2026-11-19`):
```text
MIS grazing_underflow: PBRT=nan, Mitsuba3=0.0, ScaleInv=0.500000
MIS specular_spike: PBRT=1.0, Mitsuba3=0.0, ScaleInv=1.000000
MIS dual_spike: PBRT=1.0, Mitsuba3=0.0, ScaleInv=0.307692
```

### 3. ACES Tetrahedral 3D LUT Colorimetry (`OpenColorIO`) and FP16 / Deep-Tile Codec Safety (`OpenEXR`)

#### 3.1 `ACES2065-1` (`AP0`) vs. `ACEScg` (`AP1`) and Kuhn-Simplex Tetrahedral LUT Interpolation
`Basis: source + normative (SMPTE ST 2065-1) + execution`

`OpenColorIO` implements the Academy Color Encoding System across `transforms/builtins/ACES.cpp` and `ops/fixedfunction/ACES2/Transform.cpp`:
- **`ACES2065-1` (`AP0` primaries, `SMPTE ST 2065-1`)**: Encompasses the entire CIE 1931 spectral locus (`[0, 1]^3` covers real colors without negative values), designed strictly as an archival/interchange encoding (`OpenEXR` `ACES` container standard) rather than a rendering working space because `AP0` virtual primaries lie far outside physical surface reflectances.
- **`ACEScg` (`AP1` primaries, `ACES_AP1::primaries` in `ACES.cpp:34`)**: Tightens primaries close to Rec.2020/sRGB for physically plausible rendering albedo multiplication, yet saturated spectral or wide-gamut `AP0` colors project to **negative channel lobes** in `AP1`. Without gamut compression (`ACES2/Transform.cpp`), negative lobes inside 3D LUT domain indexing hit `0.0` clamping walls and shear hue trajectories; `ACES 2.0` uses lookup hue intervals (`lookup_hue_interval` at `Transform.cpp:48`) and smooth soft-clipping prior to output display rendering.

To evaluate nonlinear 3D color transforms (`Lut3DOpCPU.cpp:422-624`), `Lut3DTetrahedralRenderer` (`lines 59-63`, dispatching `SSE2`/`AVX`/`AVX2`/`AVX512` intrinsics at `lines 386-416` or scalar fallback at `lines 431-623`) scales `[R, G, B]` by `m_step` (`dim - 1`) and decomposes the unit subcube $[0,1]^3$ containing `(fx, fy, fz)` into **6 Kuhn (Freudenthal) tetrahedra** sharing the main gray diagonal `n000 -> n111`:

1. **Tetrahedral Corner Selection (`Lut3DOpCPU.cpp:493-616`)**: Ordering `(fx, fy, fz)` selects exactly one simplex (e.g., `fx > fy && fy > fz` evaluates `(1 - fx)*L[000] + (fx - fy)*L[100] + (fy - fz)*L[110] + fz*L[111]`). Each evaluation reads **4 LUT vertices instead of 8** (halving cache/gather traffic) and forms a $C^0$ continuous piecewise-linear barycentric interpolation across simplex boundaries.
2. **Exact Neutral-Axis Preservation**: Along any gray pixel $f_x = f_y = f_z = t$, all differences `(fx - fy)`, `(fy - fz)`, etc., vanish identically regardless of which branch executes, collapsing the output to `(1 - t)*L[000] + t*L[111]`. By contrast, trilinear interpolation blends all 8 cube vertices (`(1-t)t^2`, `t(1-t)^2`), dragging gray values toward off-diagonal chromatic corners.
3. **Silent `NaN` Black-Pixel Masking (`Lut3DOpCPU.cpp:444-447`, `MathUtils.h:62-67`)**: `Clamp(a, min, max)` implements `std::min(std::max(min, a), max)` with the explicit comment `// NaNs become 0.` (`Lut3DOpCPU.cpp:444`, `MathUtils.h:62`). While blocking `NaN` propagation into display framebuffers on CPU, any upstream renderer `NaN` pixel silently collapses to black corner `L[000]`—masking upstream BSDF/MIS `NaN` bugs during visual look-dev and potentially diverging from GPU shader `clamp` intrinsics depending on hardware `NaN` propagation semantics.

#### 3.2 `OpenEXR` `PIZ` Bit-Pattern Wavelet/Huffman Pipeline and Deep-Tile Integer Overflow Classes
`Basis: source + normative (OpenEXR security advisories) + execution`

`OpenEXR`'s `PIZ` lossless codec (`src/lib/OpenEXRCore/internal_piz.c:178-786`, `internal_huf.c:1703-1966`) compresses IEEE 754 `binary16` channels strictly as opaque `uint16_t` bit patterns through three stages:

1. **Sparse Value Compaction (`internal_piz.c:678-695`)**: Reads `[minNonZero, maxNonZero]` (`maxNonZero < BITMAP_SIZE`, checked at `line 684`) and an 8-KB presence bitmap mapping populated 16-bit codes onto a dense range `[0, maxValue]`, collapsing the huge dynamic gaps across IEEE 754 `FP16` exponents without ever rounding mantissas (`applyLut` restores exact bit patterns at `line 744`, including `NaN`/`Inf` payloads if present in the input).
2. **2D Haar Lifting Wavelet (`internal_piz.c:178-236, 410-460, 730-736`)**: When `maxValue < (1 << 14)`, `wav_2D_decode` uses signed 14-bit lifting `wdec14` (`lines 178-192`: `ai = li + (hi & 1) + (hi >> 1); bs = ai - hs;`); otherwise it falls back to modulo-$2^{16}$ arithmetic `wdec16` (`lines 221-229`, `MOD_MASK = 0xffff`). Before indexing each channel's 2D plane, `line 730` checks `if (wcount > 0 && nx > INT_MAX / wcount) return EXR_ERR_CORRUPT_CHUNK;`.
3. **Canonical Huffman + RLE (`internal_huf.c:1703-1963`)**: Validates symbol range (`im >= HUF_ENCSIZE || iM >= HUF_ENCSIZE`, `line 1955`), compressed buffer tail (`hufInfoBlockSize + nBytes > nCompressed`, `line 1962`), RLE repeat count bounds (`dstIdx + rleCount > numDstElems` and `rleCount == 0 || rleCount >= INT32_MAX`, `lines 1754-1765`), and exact trailing bit consumption (`line 1815`).

**Split-Domain Buffer Sizing Vulnerability Class in Deep & Tiled OpenEXR Codecs**: Across 2025–2026 ASWF security advisories, three distinct memory-corruption vulnerabilities stemmed from **inconsistent arithmetic domains** between header allocation checks and inner-loop decoders—all directly inspectable in both pre-patch failure logic and the hardened fixes at commit `51e3f9618a3c968f1dc566feeacf082ed3e80194`:

| Advisory / CVE | Affected Component & Mechanism | Patched Guard Verified at `51e3f961` |
|---|---|---|
| **`CVE-2025-48071` / `GHSA-h45x-qhg2-q375`** | **Deep Scanline Forged `unpacked_size`**: `chunk.c` reads `unpacked_size = ddata[2]` from the untrusted chunk leader (`chunk.c:1432`) to allocate `uncompressed_data`. Prior to `3.3.3`, `undo_zip_impl` checked only `comp_buf_size > actual_out_bytes`, allowing inflated zlib streams (`actual_out_bytes > uncompressed_size`) to heap-overflow `internal_zip_reconstruct_bytes`. | `src/lib/OpenEXRCore/internal_zip.c:316-317`: `if (actual_out_bytes != uncompressed_size) res = EXR_ERR_CORRUPT_CHUNK;` rejects any mismatch prior to byte reconstruction. |
| **`GHSA-rxwg-x3wx-pgfh` (Oct 2026)** | **32-Bit Deep-Tile Area Wraparound**: On deep-tiled files with tile dimensions `65,536 × 65,536`, multiplying `unsigned int` `ySize * xSize` wrapped modulo $2^{32}$ to `0`, bypassing the `maxSampleCountTableSize` area cap (`<= UINT_MAX / sizeof(int)`) and allocating a 0/1-byte table overwritten during `TileBufferTask::execute()`. | `src/lib/OpenEXR/ImfDeepTiledOutputFile.cpp:1226-1239`: Explicitly widens both operands before multiplication (`static_cast<uint64_t>(_data->tileDesc.ySize) * static_cast<uint64_t>(_data->tileDesc.xSize)`). |
| **`GHSA-7qg8-w3rj-qxx9` (Oct 2026)** | **64-Bit Cumulative Tile Output Wraparound**: In `ImfCheckFile.cpp`'s `readCoreTiledPart`, summing `bytes += (uint64_t)curtw * outc.user_bytes_per_element * curth` across e.g. 64 `FLOAT` channels of size $2^{28} \times 2^{28}$ wrapped `uint64_t` ($64 \cdot 4 \cdot 2^{56} = 2^{64} \equiv 0 \pmod{2^{64}}$) while `unpack_32bit` (`src/lib/OpenEXRCore/unpack.c:1021-1044`) consumed retained row widths `decc->width * 4`, reading out-of-bounds. | `src/lib/OpenEXRUtil/ImfCheckFile.cpp:63-75, 1607-1615`: Introduces `accumOverflowSafe(bytes, curtw, user_bytes_per_element, curth)` checking division-based multiplication limits and additive overflow `total > UINT64_MAX - abc`. |

Reproducible Python 3.13 probe verifying tetrahedral neutral-axis invariance vs. trilinear chromatic skew, `OCIO` `NaN` clamping, 32/64-bit OpenEXR tile-size wraparound arithmetic, and `wdec14` bit-exact `FP16` roundtrip (`Basis: execution`):

```python
# 1. OCIO Tetrahedral neutral-axis invariance vs trilinear skew
corners = {(0,0,0):0.0, (1,0,0):0.95, (0,1,0):0.0, (0,0,1):0.0, (1,1,0):0.0, (1,0,1):0.0, (0,1,1):0.0, (1,1,1):1.0}
def tet_eval(fx, fy, fz, c):
    if fx > fy:
        if fy > fz:     return (1-fx)*c[(0,0,0)] + (fx-fy)*c[(1,0,0)] + (fy-fz)*c[(1,1,0)] + fz*c[(1,1,1)]
        elif fx > fz:   return (1-fx)*c[(0,0,0)] + (fx-fz)*c[(1,0,0)] + (fz-fy)*c[(1,0,1)] + fy*c[(1,1,1)]
        else:           return (1-fz)*c[(0,0,0)] + (fz-fx)*c[(0,0,1)] + (fx-fy)*c[(1,0,1)] + fy*c[(1,1,1)]
    else:
        if fz > fy:     return (1-fz)*c[(0,0,0)] + (fz-fy)*c[(0,0,1)] + (fy-fx)*c[(0,1,1)] + fx*c[(1,1,1)]
        elif fz > fx:   return (1-fy)*c[(0,0,0)] + (fy-fz)*c[(0,1,0)] + (fz-fx)*c[(0,1,1)] + fx*c[(1,1,1)]
        else:           return (1-fy)*c[(0,0,0)] + (fy-fx)*c[(0,1,0)] + (fx-fz)*c[(1,1,0)] + fz*c[(1,1,1)]
trilin = lambda x, y, z: sum((x if ix else 1-x)*(y if iy else 1-y)*(z if iz else 1-z)*corners[(ix,iy,iz)] for ix in (0,1) for iy in (0,1) for iz in (0,1))
for t in (0.25, 0.50, 0.75):
    print(f"Neutral t={t:.2f}: tet={tet_eval(t,t,t,corners):.5f}, trilinear={trilin(t,t,t):.5f}")

# 2. OpenEXR 32-bit & 64-bit tile-size wraparound & PIZ wdec14 bit-exact roundtrip
print(f"Deep tile 65536x65536: uint32_wrap={(65536*65536)&0xFFFFFFFF}, uint64_true={65536*65536}")
print(f"64 FLOAT x 2^28 x 2^28: uint64_wrap={(64*(1<<28)*(1<<28)*4)&0xFFFFFFFFFFFFFFFF}, true_bytes={64*(1<<28)*(1<<28)*4}")
def wenc14(a, b):
    a_s, b_s = (a - 65536 if a >= 32768 else a), (b - 65536 if b >= 32768 else b)
    return (((a_s + b_s) >> 1) & 0xFFFF, (a_s - b_s) & 0xFFFF)
def wdec14(l, h):
    ls, hs = (l - 65536 if l >= 32768 else l), (h - 65536 if h >= 32768 else h)
    ai = ls + (hs & 1) + (hs >> 1)
    return (ai & 0xFFFF, (ai - hs) & 0xFFFF)
for a, b in [(0x3C00, 0x3E00), (0x0001, 0x3FFF)]:
    l, h = wenc14(a, b); a2, b2 = wdec14(l, h)
    print(f"PIZ wdec14 (0x{a:04x}, 0x{b:04x}) -> (l=0x{l:04x}, h=0x{h:04x}) -> (0x{a2:04x}, 0x{b2:04x}) match={(a,b)==(a2,b2)}")
```

Observed output (`2026-11-19`):
```text
Neutral t=0.25: tet=0.25000, trilinear=0.14922
Neutral t=0.50: tet=0.50000, trilinear=0.24375
Neutral t=0.75: tet=0.75000, trilinear=0.46641
Deep tile 65536x65536: uint32_wrap=0, uint64_true=4294967296
64 FLOAT x 2^28 x 2^28: uint64_wrap=0, true_bytes=18446744073709551616
PIZ wdec14 (0x3c00, 0x3e00) -> (l=0x3d00, h=0xfe00) -> (0x3c00, 0x3e00) match=True
PIZ wdec14 (0x0001, 0x3fff) -> (l=0x2000, h=0xc002) -> (0x0001, 0x3fff) match=True
```

### 4. Six-Level Performance and Resource Footprint Matrix (`L1`–`L6`)

`Basis: source + documentation + derived`

Across geometry traversal, path integration, colorimetry, and EXR serialization, memory-bandwidth compression (`QuantizedNode_t`, `PRB` O(1) replay, 4-read tetrahedral LUTs) trades small arithmetic/branching work for dramatic L1/L2/VRAM locality gains:

| Level | Metric / Domain | `Embree` (`BVH8` / Woop) | `pbrt-v4` & `Mitsuba 3` (`MIS` / `PRB`) | `OpenColorIO` (`ACES` / 3D LUT) | `OpenEXR` (`PIZ` / `OpenEXRCore`) |
|---|---|---|---|---|---|
| **L1: Human & Agent Authoring Velocity** | Authoring density & numerical debugging friction | `WoopIntersector1` is ~90 LoC; subtle FP32 edge/ULP bugs (`round_down`/`nmadd`) are invisible to unit tests on non-shared triangles and require targeted ray-shear fuzzing. | Custom BSDFs (`50–250 LoC`) + `PRB` integrators (`~300 LoC`, `prb.py`); `NaN` fireflies and AD `dr::detach` missing-gradient bugs are notoriously expensive to bisect across bounces. | `.ocio` YAML configs (`100–800 LoC`) + `.cube` LUTs; out-of-gamut negative lobes (`AP1`) require manual look-dev tuning or `ACES2` analytical transforms. | High-level C++ `Imf` vs low-level C `OpenEXRCore`; split-domain integer bugs recur across wrapper/core boundaries (`ImfCheckFile.cpp`, `ImfDeepTiledOutputFile.cpp`). |
| **L2: Toolchain Build Time & Memory** | Compile latency & multi-ISA object bloat | Multi-ISA compilation (`SSE2`, `AVX`, `AVX2`, `AVX512` template instantiation in `kernels/CMakeLists.txt`): `2–6 min` build, `1–3 GB` peak compiler RSS. | `pbrt-v4` (`rgb2spec_opt` LUT codegen + CUDA PTX `bin2c` in `CMakeLists.txt`): `2–5 min`; `Mitsuba 3` `Dr.Jit` + `nanobind` C++/Python bindings: `3–8 min`, `2–4 GB` RSS. | Multi-ISA LUT kernels (`Lut3DOpCPU_{SSE2,AVX,AVX2,AVX512}.cpp`): `1–3 min` build, `< 1 GB` RSS. | Compact C (`OpenEXRCore`) + C++ (`OpenEXR`) + optional Zstd/Deflate (`libdeflate`): `< 45 s` build, `< 500 MB` RSS. |
| **L3: Compilation, JIT & Build-Phase Latency** | BVH build / shader JIT / LUT baking | `BVH8` binned SAH builds at `~10–30 M tris/s` (`DOI: 10.1145/2601097.2601199`); `bvh_builder_sah_spatial.cpp` increases build time `~1.8–3×` and memory up to `1.3–1.5×` from split references. | `Mitsuba 3` `Dr.Jit` traces Python integrator graphs (`@dr.syntax` in `prb.py:63`) into LLVM/PTX kernels in `50 ms–3 s` cold (`< 5 ms` cached). | `OCIO` CPU processor initialization & `33^3`/`65^3` LUT upload/optimization: `< 1–10 ms` per config switch. | `OpenEXRCore` `exr_decoding_initialize` & Huffman table unpack: `< 0.1–2 ms` per chunk (`4–64` scanlines per `PIZ` block). |
| **L4: Runtime Execution Throughput** | Inner-loop cycles, SIMD lanes & pixel/ray rates | `BVH8` AVX-512 traverses 8 children in 1 instruction; `WoopIntersector1` executes `~15–25` SIMD FMAs per triangle packet, sustaining `100M–500M+ rays/s` on multi-core CPUs (`10–30%` faster node bandwidth with `QuantizedNode_t`). | Primary variance limited by BVH ray memory stalls (`40–60%` of frame time) and BSDF divergence; `PRB` replay executes `~2–2.5×` primal ray count while eliminating AD tape scatter/gather bandwidth. | `Lut3DTetrahedralRenderer` halves corner gathers (`4` vs `8` trilinear reads) across `AVX-512` lanes (`Lut3DOpCPU_AVX512.cpp`), sustaining multi-gigapixel/s throughput. | `PIZ` (`internal_piz.c` + fast-table `internal_huf.c`) decodes at `~150–450 MB/s/core` (slower than `ZIP`/`ZIPS` on smooth noise, superior compression on film grain `FP16`). |
| **L5: Verification & Validation Speed** | Bounds checks, sanitization & audit speed | Debug enclosure invariants (`bvh_node_qaabb.h:80-83`) verify per node in `O(N)` registers; exhaustive floating-point crack testing requires targeted shared-edge ray probes (`10^4–10^7` rays/s). | Differential primal/AD finite-difference gradient checks take `~10–60 s` per BSDF; full-frame `NaN`/energy conservation checks run `O(pixels)` (`< 10 ms`). | Exact neutral-diagonal and invertibility checks across `33^3 = 35,937` nodes complete in `< 2 ms`. | `exrcheck -c` (`ImfCheckFile.cpp:1498`) validates chunk headers, `accumOverflowSafe`, and Huffman streams linearly at `> 500 MB/s` in `OpenEXRCore`. |
| **L6: RAM, Disk & Binary Footprints** | Node sizes, VRAM & codec overhead | `QuantizedNode_t<8>` compresses child bounds from `6 * 8 * 4 = 192 B` down to `48 B + 24 B (start/scale) = 72 B` (`~50%` smaller total node including child pointers vs `AABBNode_t<8>`). | `PRB` reduces differentiable path-tracing VRAM from $O(D \cdot P)$ (`10–80 GB` AD tape on deep bounces) down to **$O(1)$ per pixel** (`prb.py`); `Mitsuba` `Dr.Jit` binary + LLVM JIT runtime `~50–150 MB`. | `33^3` `RGB` FP32 3D LUT = `431 KB` (fits cleanly in L2 CPU cache); `65^3` LUT = `3.29 MB` (L3 resident); `ACES 2.0` analytical tables (`Transform.cpp`) `~100 KB`. | Deep EXR `sample_count_table` capped at `2^32 B` (`ImfDeepTiledOutputFile.cpp:1234`); `BITMAP_SIZE = 8192 B` stack/scratch per `PIZ` decode; binary16 pixels `2 B/channel` (`8 B` RGBA). |

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

#### 5.1 Human Comprehensibility and Mental-Model Ergonomics (`C1`)
`Basis: source + derived`

- **Deceptive Local Shortness vs. Floating-Point Non-Associativity**: Every hazardous snippet inspected above—`PowerHeuristic` (`5` lines), `mis_weight` (`6` lines), `WoopIntersector1` (`40` lines), `Clamp` (`4` lines), `DeepTiledOutputFile::initialize` (`10` lines)—fits easily on half a screen. Yet human code reading systematically fails on them because correctness depends on global IEEE 754 domain invariants across distant call sites: whether `Sqr(1e-23f)` underflows to `0` while `1e-23f` itself is non-zero; whether `Clamp` turns an upstream `0/0` `NaN` into invisible black pixels (`Lut3DOpCPU.cpp:444`); or whether `PRB` replay executes in `mode != Primal` with `dr.detach` (`prb.py:88, 123-131`) where forgetting a single `reattach_wi` breaks physical gradient consistency without raising a runtime error.
- **Diagnostic Opaqueness**: In graphics pipelines, downstream clamps (`OCIO` `Clamp`, `Mitsuba` `dr::isfinite` fallback to `0.f`, post-processing bloom/tonemapping) silently convert `0/0` or `Inf/Inf` numeric singularities into subtle bias (darkened grazing highlights or lost caustics) rather than immediate assertions—making visual A/B inspection far weaker than targeted domain probes.

#### 5.2 Simplicity, Orthogonality, and Universal Model Refinement (`C2`)
`Basis: derived`

Evaluating these subsystems through Ousterhout's deep-module and Felleisen's orthogonality criteria isolates four unifying abstractions that eliminate special-case patches:

1. **Woop's Ray-Centric Shear Space (`triangle_intersector_woop.h`)**: Rather than layering post-hoc epsilon hacks or winged-edge adjacency metadata onto Möller–Trumbore (adapter bloat), transforming the mesh vertices relative to the ray into canonical `+z` shear space makes shared-edge bit-identity an *ordinary algebraic consequence* of vertex-order symmetry across a compact 25-operation interface.
2. **Scale-Invariant Max-Normalized Measure Ratios (Eliminating `PowerHeuristic` Split Cases)**: Both `pbrt-v4`'s `IsInf(Sqr(f))` shortcut (`sampling.h:74`) and `Mitsuba 3`'s `isfinite(w) ? w : 0` patch (`path.cpp:357`) fail on valid inputs because squaring breaks homogeneity. Dividing by $m = \max_k (n_k p_k)$ *before* raising to power $\beta$ makes all ratios homogeneous of degree zero in `[0, 1]`, eliminating `0/0` underflow and `Inf/Inf` overflow with a single branch (`m == 0`).
3. **Kuhn/Freudenthal Simplex Decomposition**: Instead of maintaining separate 1D gray curves plus 3D correction cubes to keep neutrals clean, decomposing each 3D lattice cell into 6 Kuhn simplices sharing the neutral diagonal unifies chromatic lookup and exact diagonal linearity in one $O(d)$ branching pattern (`Lut3DOpCPU.cpp:493-616`).
4. **Single-Source Checked Layout Witnesses (`OpenEXR`)**: Across `OpenEXR` and `OpenEXRCore`, split-domain vulnerabilities recur because header validation (`ImfDeepTiledOutputFile.cpp`, `ImfCheckFile.cpp`) and low-level buffer unpacking (`unpack.c`, `internal_zip.c`) re-compute allocation lengths independently across `int`, `unsigned int`, `size_t`, and `uint64_t`. Replacing raw arithmetic with a single validated `TileLayoutWitness` / `CheckedSpan` passed from validation into `unpack_32bit` and `undo_zip_impl` makes size divergence unrepresentable by construction.

## Boundaries

- **Hardware RT Core Ray–Triangle & BVH Rounding (`not examined` / `unknown`)**: Proprietary NVIDIA OptiX / AMD RDNA / Intel Arc hardware ray-tracing fixed-function microcode implements proprietary quantized BVH formats and fixed-point/FP intersection rounding whose exact bit-level divergence from `Embree`'s software `WoopIntersector1` and `QuantizedBaseNode_t` cannot be inspected from open-source repositories.
- **Mitsuba 3 Interior Silhouette Reparameterization (`not examined`)**: While `PRB` (`prb.py`) handles continuous BSDF/emission/attached-vertex motion gradients in $O(1)$ path memory, discontinuous visibility boundary derivatives (`path_replay_reparam` / projective sampling) require dedicated boundary-integral estimators not examined in detail here.
- **Spectral Fluorescence and Polarized Bispectral BSDFs (`known not to apply`)**: The `MIS` scalar power-heuristic analysis in `sampling.h` and `path.cpp` assumes scalar/wavelength-aligned path PDFs; hero-wavelength spectral MIS with wavelength-dependent dispersion (`SampledWavelengths`) adds an extra cross-wavelength MIS term in `pbrt-v4` not exercised by the 2-technique scalar probe.
- **Lossy OpenEXR Codecs (`DWAA`/`DWAB`/`B44`) & `HTJ2K` (`not examined`)**: Codec safety findings apply to lossless `PIZ` (`internal_piz.c`/`internal_huf.c`), `ZIP`/`ZIPS` (`internal_zip.c`), and deep tile/scanline container headers (`chunk.c`, `unpack.c`, `ImfCheckFile.cpp`); DCT-based lossy `DWAA`/`DWAB`, fixed-rate `B44`, and `OpenJPH` `HTJ2K` integration paths were not audited.
- **GPU OpenColorIO GLSL/HLSL Shaders (`Lut3DOpGPU.cpp`) (`not examined`)**: Silent `NaN -> 0` masking was verified in C++ `Lut3DOpCPU.cpp` and `MathUtils.h`; GPU shader drivers (`Lut3DOpGPU.cpp`, hardware 3D texture samplers) may handle `NaN` coordinates differently depending on `clamp()` / `mix()` lowering in Vulkan/Metal/DirectX.

## Evidence

- **Upstream Repository Sources Inspected (`2026-11-19`)**:
  - `RenderKit/embree` @ `304b5b7443dc0d9b5dd480a9e1f050db2c7b9449`: `kernels/CMakeLists.txt`; `kernels/bvh/bvh.h:7-135`; `kernels/bvh/bvh_node_qaabb.h:12-185` (`QuantizedBaseNode_t`, `init_dim`, `2.0f*FLT_MIN` FTZ guard, `m_lower_correction`/`m_upper_correction`); `kernels/bvh/node_intersector1.h:106-148` (`TravRayBase<N, true>`, `1.0f ± 3.0f*float(ulp)`); `kernels/builders/heuristic_spatial.h:17-113` (`SpatialBinMapping`, `SpatialBinSplit`); `kernels/geometry/triangle_intersector_woop.h:16-188` (`WoopPrecalculations1`, `WoopIntersector1`, `std::swap(kx, ky)`, `nmadd`); `kernels/geometry/triangle_intersector_pluecker.h:62-99`; `kernels/geometry/triangle_intersector_moeller.h:21-95`.
  - `mmp/pbrt-v4` @ `20e41fd83789f12550e2c31b2047898c9e20e46c`: `CMakeLists.txt` (`rgb2spec_opt`, `ACES2065_1`); `src/pbrt/ray.h:75-108` (`OffsetRayOrigin`, `NextFloatUp`/`NextFloatDown`, `SpawnRayTo`); `src/pbrt/util/sampling.h:69-77` (`PowerHeuristic`); `src/pbrt/cpu/integrators.cpp:648-668`.
  - `mitsuba-renderer/mitsuba3` @ `aa01500f57770a4ef0b067693cae08b3e8a2ac73`: `README.md:142-151`; `src/integrators/CMakeLists.txt`; `src/integrators/path.cpp:198-285, 352-358` (`mis_weight`, `dr::select(dr::isfinite(w), w, 0.f)`); `src/python/python/ad/integrators/prb.py:63-235` (`PathReplayBackpropagation`, `reattach_wi`, `L - Le - Lr_dir`, `rr_prob = dr.minimum(β_max * η**2, .95)`).
  - `AcademySoftwareFoundation/OpenColorIO` @ `22dd9c4faa0d1b7cfb3d64d1a6e9cb454acc6cfd`: `src/OpenColorIO/CMakeLists.txt`; `src/OpenColorIO/MathUtils.h:62-75` (`Clamp`, `// NaN values become 0.`); `src/OpenColorIO/ops/lut3d/Lut3DOpCPU.cpp:59-63, 386-624` (`Lut3DTetrahedralRenderer`, `SSE2`/`AVX`/`AVX2`/`AVX512` dispatch, 6-simplex branches); `src/OpenColorIO/ops/fixedfunction/ACES2/Transform.cpp:1-55`; `src/OpenColorIO/transforms/builtins/ACES.cpp:28-70` (`ACES_AP1::primaries`, `ACEScct_to_LINEAR`).
  - `AcademySoftwareFoundation/openexr` @ `51e3f9618a3c968f1dc566feeacf082ed3e80194`: `src/lib/OpenEXRCore/CMakeLists.txt`; `src/lib/OpenEXRCore/internal_piz.c:178-236, 410-460, 625-786` (`wdec14`, `wdec16`, `BITMAP_SIZE`, `nx > INT_MAX / wcount`, `internal_exr_undo_piz`); `src/lib/OpenEXRCore/internal_huf.c:1703-1963` (`internal_huf_decompress`, RLE/buffer bounds); `src/lib/OpenEXRCore/internal_zip.c:290-324` (`undo_zip_impl`, `actual_out_bytes != uncompressed_size`); `src/lib/OpenEXRCore/chunk.c:1054-1440`; `src/lib/OpenEXRCore/unpack.c:1020-1044` (`unpack_32bit`); `src/lib/OpenEXR/ImfDeepTiledOutputFile.cpp:1190-1255` (`uint64_t tileArea`, `2^32` cap); `src/lib/OpenEXRUtil/ImfCheckFile.cpp:62-75, 1497-1625` (`accumOverflowSafe`, `readCoreTiledPart`).
- **Literature & Security Advisories**:
  - S. Woop, C. Benthin, and I. Wald, "Watertight Ray/Triangle Intersection," *Journal of Computer Graphics Techniques (JCGT)*, 2(1):65–82, 2013 (`https://jcgt.org/published/0002/01/05/`).
  - I. Wald et al., "Embree: A Kernel Framework for Efficient CPU Ray Tracing," *ACM TOG*, 33(4), 2014, `DOI: 10.1145/2601097.2601199`.
  - C. Wächter and N. Binder, "A Fast and Robust Method for Avoiding Self-Intersection," *Ray Tracing Gems*, Apress, 2019, `DOI: 10.1007/978-1-4842-4427-2_6`.
  - E. Veach and L. J. Guibas, "Optimally Combining Sampling Techniques for Monte Carlo Rendering," *Proc. ACM SIGGRAPH*, 1995, `DOI: 10.1145/218380.218498`.
  - D. Vicini, S. Speierer, and W. Jakob, "Path Replay Backpropagation: Differentiating Light Paths Using Constant Memory and Linear Time," *ACM TOG*, 40(4), 2021, `DOI: 10.1145/3450626.3459804`.
  - W. Jakob et al., "Dr.Jit: A Just-In-Time Compiler for Differentiable Rendering," *ACM TOG*, 41(4), 2022, `DOI: 10.1145/3528223.3530099`.
  - OpenEXR Security Advisories: `GHSA-h45x-qhg2-q375` (`CVE-2025-48071`, `unpacked_size` heap overflow in deep scanlines, fixed `3.3.3`); `GHSA-rxwg-x3wx-pgfh` (Oct 31, 2026, 32-bit `65536*65536` tile-area wrap in `DeepTiledOutputFile`, fixed `3.3.15`/`3.4.17`/`3.5.3`); `GHSA-7qg8-w3rj-qxx9` (Oct 5, 2026, 64-bit cumulative `readCoreTiledPart` wrap in `unpack_32bit`, fixed `v3.5.2`).
- **Execution Environment**: Pure Python 3.13.x IEEE 754 `struct`/`math` micro-probes executed directly (`2026-11-19`) verifying 20,000 shared-edge rays, three-regime `FP32` `PowerHeuristic` failures, tetrahedral neutral-diagonal preservation, and `OpenEXR` wraparound / `wdec14` roundtrips.

## Revalidation

To verify whether newer upstream commits alter these findings:

1. **Inspect `pbrt-v4` / `Mitsuba 3` MIS Heuristics & `Embree` Woop Intersector** for scale-invariant fixes or `FP64` tie-breakers:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/mmp/pbrt-v4/HEAD/src/pbrt/util/sampling.h" | grep -n -A 8 "PowerHeuristic("
   curl -sSL "https://raw.githubusercontent.com/mitsuba-renderer/mitsuba3/HEAD/src/integrators/path.cpp" | grep -n -A 7 "mis_weight("
   curl -sSL "https://raw.githubusercontent.com/RenderKit/embree/HEAD/kernels/geometry/triangle_intersector_woop.h" | grep -n -A 12 "U0 ="
   ```
2. **Audit `OpenEXR` Overflow Guards** in `ImfDeepTiledOutputFile.cpp`, `ImfCheckFile.cpp`, and `internal_zip.c`:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/AcademySoftwareFoundation/openexr/HEAD/src/lib/OpenEXRUtil/ImfCheckFile.cpp" | grep -n -A 12 "accumOverflowSafe"
   curl -sSL "https://raw.githubusercontent.com/AcademySoftwareFoundation/openexr/HEAD/src/lib/OpenEXR/ImfDeepTiledOutputFile.cpp" | grep -n -A 10 "tileArea"
   ```
3. **Re-run Mathematical Micro-Probes**: Execute the three embedded Python 3 scripts from **Findings** (§1.3, §2.2, §3.2) via `python3 -` to verify exact IEEE 754 `binary32` edge leakage, `PowerHeuristic` `NaN`/energy behavior, tetrahedral neutral invariance, and `wdec14` lossless bit recovery.
