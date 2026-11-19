# Units of Measure, Coordinate-Frame Types, and Geometric CAD Compilers

## Summary

Physical quantities, spatial coordinates, geometric predicates, and digital fabrication programs fail silently when lowered onto raw `float[N]` arrays and unconstrained IEEE-754 arithmetic, because distinct mathematical symmetries—scaling groups, affine torsors, contravariant/covariant tensor actions, exact sign topology, and physical object equivalence—are erased before the ABI or compiler backend. Direct inspection of production compilers, libraries, specifications, and local execution probes yields six load-bearing engineering findings:

1. **Units of measure require equational unification modulo an Abelian group, yet fail at affine, angular, matrix, and ABI boundaries**: In `dotnet/fsharp` (`ConstraintSolver.fs:L800-L977`), measure inference reduces $m_1 = m_2$ to $m_1 \cdot m_2^{-1} = 1$, pivots non-rigid variables using internal `Measure.RationalPower`, and normalizes generalized type schemes into a unique Hermite/reduced-row-echelon integer exponent matrix via rational GCD (`NormalizeExponentsInTypeScheme`). Relational parametricity guarantees scaling invariance (Kennedy, POPL 1997), but the free Abelian group excludes affine points (`mp-units` `quantity_point`: `point - point = vector`, `point + point` illegal), logarithmic scales, non-dimensionless angles, and heterogeneous matrices. Worse, units are erased across FFI and file boundaries: NASA's *Mars Climate Orbiter Mishap Investigation Board Phase I Report* (1999) found the failure occurred in a **file exchanged between two programs** (`"delivered in lb-sec instead of the specified and expected units of Newton-sec"`), where an in-language type checker never sees the mismatch.
2. **Coordinate-frame types require `(scheme × frame × object)` plus transformation-group variance (`Gator`, `sguaba`)**: Gator (`cucapra/gator`, OOPSLA 2020 `10.1145/3428241`) indexes shader types by coordinate scheme (`cart3`, `hom`), reference frame (`model`, `world`, `view`, `projection`), and geometric object (`point`, `vector`, `direction`, `normal`), synthesizing paths across `canon` transformation graphs (`aPosition in hom<projection>`). Points, tangent vectors, surface normals, and pseudovectors (cross products) obey distinct transformation laws: under non-uniform scale $M = \operatorname{diag}(4, 0.5, 1)$, applying $M$ directly to a unit normal causes a **`75.75°`** orthogonality error relative to $M t$, whereas covariant $(M^{-1})^T n$ preserves exact $90^\circ$ perpendicularity; under reflection ($\det R = -1$), $(Ru)\times(Rv) = -R(u\times v)$. Moreover, $\mathrm{SO}(3)$ topology forbids any continuous Euclidean representation in $\le 4$ dimensions (Zhou et al., CVPR 2019), and robotics/graphics standards (`ROS REP 103`, `glTF 2.0`, `WebGPU`, `Vulkan`) disagree normatively on up-axis, handedness, clip-$z$ range, and quaternion component order.
3. **Adaptive exact geometric predicates prevent topological collapse but depend strictly on IEEE-754 rounding (`Shewchuk`, `georust/robust`)**: On a $64\times 64 = 4096$-point Kettner et al. near-collinear lattice, naive `double` `orient2d` returns the **wrong sign on 2562/4096 points (62.5%)**, whereas Shewchuk's expansion-based predicate returns **0/4096 errors** under `gcc -O2 -ffp-contract=off`. Compiling the same exact predicate with **`gcc -O3 -ffast-math`** reduces Dekker's 17-operation `two_prod` to a single `mulsd` instruction (hardcoding residual `y = 0.0`) and causes **1991/4096 wrong signs (48.6%)**. Even without `-ffast-math`, **`-mfma -ffp-contract=fast`** causes standalone Veltkamp `split(1/3)` to collapse to `ahi == a, alo == 0.0` (breaking its 26-bit splitting invariant) and causes naive `orient2d` to violate antisymmetry (`orient2d(a,b,c) != -orient2d(b,a,c)`) on **1570/4096 points**.
4. **Implicit surface compilers treat rendering as abstract interpretation (`Fidget`, `libfive`)**: Fidget (`mkeeter/fidget`) lowers expression DAGs to reverse-order SSA tapes (`SsaTape`), register-allocated bytecode, and `x86_64`/`aarch64` JIT kernels, using interval evaluation with `Choice::{Left,Right,Both}` to prune dead CSG branches per spatial cell. Source inspection of `fidget-core/src/types/interval.rs:L5-L15` reveals that Fidget **explicitly does not set IEEE-754 directed rounding modes** (`"so it may not be _perfect_"`), which leaks containment by 1 ULP on boundary `f32` sums (`1.0 + 2^-25` rounds to `1.0`), and uses `[NaN, NaN]` + `Choice::Both` to avoid unsound pruning on division by zero or negative square roots. Affine arithmetic eliminates interval dependency blowup, cutting quadtree box evaluations by **2.37×** (`252` vs. `596`) on a depth-6 test with linear variable cancellation.
5. **CAD decompilation (`Szalinski`) faces non-transitive approximate equality in e-graphs**: Szalinski (`uwplse/szalinski`, PLDI 2020 `10.1145/3385412.3386012`) recovers parameterized loops via `egg` equality saturation and degree-1/2 list solvers (`src/solve.rs`). Source inspection of `src/num.rs:L85-L112` shows `unify_close_nums` sorts all `Cad::Num` nodes and unions adjacent pairs within `ABS_EPSILON = 1e-4` / `REL_EPSILON = 1e-4`, computing single-linkage transitive closure: a chain of 101 numbers spaced by `9e-5` across `[0.0, 0.009]` collapses into **one e-class** ($90\times$ epsilon drift).
6. **Declarative diagramming (`Penrose`) and fabrication languages (`Knitout`, G-code)**: Penrose (`penrose/penrose`, `Optimizer.ts`) compiles `Domain`/`Substance`/`Style` relations into an **exterior point penalty** problem solved by **L-BFGS** with reverse-mode autodiff (`initConstraintWeight = 1e3`, `weightGrowthFactor = 10`, `uoStop = 1e-2`, `epStop = 1e-3`), making compiled geometry inherently relational and seed-dependent. Fabrication ISAs contrast modal, context-sensitive G-code (`G90`/`G91`, `G20`/`G21`) against `knitout` v0.6 (`textiles-lab/knitout`), for which Lin et al. (SIGGRAPH 2023 `10.1145/3592449`) define **fenced tangle** knot-theoretic semantics proving compiler rewrites preserve physical knit topology.

## Applicability

This report synthesizes primary source inspections, normative standards, peer-reviewed theorems, and local execution probes across sixteen pinned subjects spanning four connected technical layers:

- **Dimensional analysis and affine quantity type systems**: `dotnet/fsharp` (`57f77cbac4923aa41cf308711553232dfd608da7`), `mpusz/mp-units` (`566b8615a74e84fba824952a5c1dddc1935d9a2e`), and `iliekturtles/uom` (`a465bcc2b3bf67f9f12fc0b133d371762d9d8fe4`).
- **Coordinate-frame type systems and normative spatial conventions**: `cucapra/gator` (`f506d64a29daac9e7f4f7d77a7b2c4cbd268fb8a`, OOPSLA 2020 `10.1145/3428241`), `helsing-ai/sguaba` (`4a71898daac0b40fef3748491a15a2c1c16cb9c7`), `ros-infrastructure/rep` (`11ca24a41f31480dfb9562ba99f2a5b93d3ebda5`, REPs 103 and 105), `KhronosGroup/glTF` (`8846b1aa225dd8430322c03150919df47e3122ae`, glTF 2.0), `gpuweb/gpuweb` (`d178d9145ab1652ec933e71a8c30e8f6470f00a3`), and `KhronosGroup/Vulkan-Docs` (`f7de774cace1509af0f10b8d859c973b5354ff62`).
- **Exact geometric predicates, kernels, and implicit CAD compilers**: `georust/robust` (`654f34cb8cdb3ae21bf59ef3472f92652942cd74`) implementing Shewchuk (1997, `10.1007/PL00009321`), `CGAL/cgal` (`7305123709c59d1ce7d2f5c17a154c8e7691f630`), `mkeeter/fidget` (`1879743ddc1d73dac14a42a8184a3c5b758dcca5`), `libfive/libfive` (`918387a9220dbac2f7ab32fb35e274c6794439cf`), and `mkeeter/mpr` (`eb63defa00239571984e579039166ea575da0dad`).
- **CAD decompilation, constrained optimization diagramming, and fabrication**: `uwplse/szalinski` (`9ce7acc3c766c8a6f5edd9c431e276502c331b6d`, PLDI 2020 `10.1145/3385412.3386012`), `egraphs-good/egg` (`73975c9819efb4af2f3c6c1b44fa53f8c5742574`), `penrose/penrose` (`d46d92b7b39c6ef6539a38e8a8f7472ebb5d0502`), and `textiles-lab/knitout` (`17b868c5a48cf8ce2d25bbfb7d23f2ab7ba55ddf`, v0.6; semantics `10.1145/3592449`).

**Scope relationships and constraints**: Subjects are compared along three seams: static elimination of physical/geometric category errors, preservation of topological exactness across floating-point compilation, and semantic equivalence of fabricated outputs. Local C/Python probes ran on x86_64 Linux with `gcc (Debian 15.2.0-14) 15.2.0` and Python 3.13; compiler code-generation observations apply strictly to that compiler/architecture unless revalidated elsewhere. Real-to-float roundoff analyzers (`Rosa`, `Daisy`, `FPTaylor`, `VCFloat2`) and general rendering/mesh-processing performance tuning are out of scope.

## Findings

### 1. Units of Measure: Abelian-Group Inference, Parametricity, and Algebraic Boundaries

#### 1.1 F# Measure Unification and Hermite/RREF Normalization (`dotnet/fsharp`)
Basis: source (`dotnet/fsharp@57f77cbac4923aa41cf308711553232dfd608da7`, `src/Compiler/Checking/ConstraintSolver.fs:L800-L977`, `src/Compiler/TypedTree/TypedTree.fs:L4803-L4821`) + documentation (Kennedy, POPL 1997; Kennedy, CEFP 2009) + execution (Probe 2D under Evidence)

Kennedy's unit-of-measure type system (implemented in F#) indexes numeric types by elements of the free Abelian group generated by base unit constructors and unit variables (`1`, $u_1 \cdot u_2$, $u^{-1}$). Unifying two unit expressions $m_1 = m_2$ cannot use syntactic Hindley-Milner unification because $m \cdot s^{-1} = s^{-1} \cdot m$ and $u \cdot u^{-1} = 1$; it requires **equational unification modulo the Abelian-group axioms**.

Direct inspection of `dotnet/fsharp` (`ConstraintSolver.fs:L800-L977`) reveals how the production F# compiler actually implements this solver—using **internal rational exponents during pivoting**, then restoring integer exponents at generalization:

1. **Reduction to unity (`UnifyMeasures`, `L825-L826`)**: Unifying $m_1$ with $m_2$ delegates to `UnifyMeasureWithOne (Measure.Prod(ms1, Measure.Inv ms2))`.
2. **Rational pivoting (`UnifyMeasureWithOne`, `L806-L822`)**: Collects rigid and non-rigid measure variables with non-zero exponents. If no non-rigid variable exists, checks `measureEquiv ms 1` (aborting otherwise). If a preferred non-rigid variable $v$ has non-zero exponent $e$, it solves $v^e \cdot m' = 1$ in one step by substituting:
   $$v := (m')^{-1/e} = \prod_i c_i^{-e'_i / e} \prod_j v_j^{-e''_j / e}$$
   represented internally with `Measure.RationalPower` (`TypedTree.fs:L4821`).
3. **Unique normal form and rational-GCD elimination (`SimplifyMeasuresInTypeScheme`, `L908-L976`)**: Before generalizing a polymorphic type scheme, F# transforms the exponent matrix (rows = unit variables/base units, columns = measure positions in the type skeleton) into an upper-triangular reduced row echelon form (`L945-L964`, guaranteeing canonical printing and decidable signature equivalence), then calls `NormalizeExponentsInTypeScheme` (`L929-L937`) to compute the rational GCD `expGcd` of each generalizable variable $v$'s exponents across the scheme and substitute $v := (v')^{1/\text{expGcd}}$.

Probe 2D (under Evidence) traces F#'s exact algorithm on $u^2 \cdot v^{-3} = m^2 \cdot s^{-4}$:
- Pivoting on $u$ ($e = 2$) yields $u = v^{3/2} \cdot m^1 \cdot s^{-2}$, $v = v^1$.
- Computing $\gcd_{\mathbb{Q}}(1, 3/2) = 1/2$ and substituting $v := (v')^2$ produces the normalized integer scheme **$v = (v')^2$, $u = (v')^3 \cdot m \cdot s^{-2}$** (all integer exponents, no fractional powers exposed in user-visible F# syntax).

**Relational parametricity (Kennedy, POPL 1997; Atkey, Johann, Kennedy, POPL 2013)**: Because unit-polymorphic code cannot inspect the scale factor of an abstract unit variable `'u`, every well-typed polymorphic function satisfies **scaling invariance**—changing the base scale of `'u` by any $k > 0$ commutes with execution (the Buckingham $\Pi$-theorem in type-theoretic form). This yields strong non-definability theorems (e.g., no polymorphic function `float<'u> -> float<'u^2> -> float<'u>` can add its arguments).

#### 1.2 Where the Free Abelian Group Breaks & The ABI Erasure Boundary
Basis: source (`mpusz/mp-units@566b8615a7`, `docs/users_guide/framework_basics/the_affine_space.md:L1-L45`; `iliekturtles/uom@a465bcc2b3`) + documentation (NASA MCO Phase I Report, Nov 10, 1999; Hart, *Multidimensional Analysis*, 1995)

Five structural classes fall outside Kennedy's free Abelian group $\mathbb{Z}^n$:
1. **Affine quantities (torsors)**: Celsius/Fahrenheit temperatures, calendar timestamps, and spatial positions are points in an affine space over a vector space of differences. As `mp-units` documents (`the_affine_space.md:L20-L43`), `point - point -> vector` and `point + vector -> point` are valid, whereas `point + point`, `vector - point`, and scaling a `point` are ill-typed. Treating `0°C` as a vector quantity produces nonsense (`10°C + 10°C = 20°C` vs. `566.3 K`).
2. **Angles and dimensionless aliasing**: SI defines the radian as $\text{m}/\text{m} = 1$ (dimensionless), so pure SI unit systems conflate **energy** ($\text{N}\cdot\text{m}$) with **torque** ($\text{N}\cdot\text{m}/\text{rad}$) and **frequency** ($\text{Hz} = \text{s}^{-1}$) with **angular velocity** ($\text{rad}/\text{s}$), making missing factors of $2\pi$ type-check silently unless angle/cycle are distinguished as quantity kinds or explicit base dimensions.
3. **Logarithmic scales**: Decibels (dB), pH, and Richter magnitudes map multiplication to addition and require an explicit reference level (e.g., $\text{dBm}$ vs. $\text{dBW}$).
4. **Transcendentals and heterogeneous matrices**: `exp`, `log`, `sin`, `cos` require dimensionless arguments; Taylor series require index-dependent unit exponents; state-space control matrices ($x' = Ax + Bu$) have distinct units in every matrix cell (Hart 1995: multiplicatively consistent dimensioned matrices factor as outer products $r_i \cdot c_j^{-1}$, which standard HM-with-units cannot type without dependent/matrix-indexed dimensions).
5. **ABI / file erasure (Mars Climate Orbiter)**: Units are erased at compilation into raw IEEE-754 floats. In the *Mars Climate Orbiter Mishap Investigation Board Phase I Report* (Nov 10, 1999, p. 14), the root technical failure was not in-process arithmetic, but an **inter-program file interface**: the ground-software `Small Forces` output file `"was delivered in lb-sec instead of the specified and expected units of Newton-sec"` (a factor of $4.44822$). Without schema-level or ABI-level unit descriptors, in-language unit checking stops at the first serialization or FFI call.

#### 1.3 Cross-Language Unit & Quantity System Comparison
Basis: source (`dotnet/fsharp`, `mpusz/mp-units`, `iliekturtles/uom`, `helsing-ai/sguaba`) + documentation

| System (Pinned Revision) | Exponent Algebra | Affine Space (`Point` vs. `Vector`) | Angle / Quantity-Kind Separation | Heterogeneous Frame Support | Runtime Overhead |
|---|---|---|---|---|---|
| **F# Units of Measure** (`dotnet/fsharp@57f77cbac4`) | Free Abelian group $\mathbb{Z}^n$ (rational pivot + GCD normalization internally) | Not built-in (must wrap manually) | Manual measure tags (`[<Measure>] type rad`); no auto-conversion | No native frame graph | Zero (erased to `float`/`float32`) |
| **C++ `mp-units`** (`mpusz/mp-units@566b8615a7`) | Rational powers (`ratio`) + ISQ quantity-kind hierarchy | Built-in (`quantity_point` over `quantity` + explicit `point_origin`) | Distinguishes `torque` vs. `energy`, `radian` vs. `1` via ISQ `quantity_spec` | Scalar/vector/tensor character tags; no 3D frame graph | Zero (template erasure + compile-time conversion factors) |
| **Rust `uom`** (`iliekturtles/uom@a465bcc2b3`) | Integer exponents (`typenum::Integer`) over SI/ISQ base vector | Partial (distinct `ThermodynamicTemperature` vs. `TemperatureInterval`) | `Angle` distinct quantity; dimensionless aliasing avoided via distinct trait types | None | Zero (`PhantomData`, single scalar storage) |
| **Rust `sguaba`** (`helsing-ai/sguaba@4a71898daa`) | Delegates scalar units to `uom` | Built-in (`Coordinate<In>` point vs. `Vector<In>` displacement) | Orientation/Yaw-Pitch-Roll + `RigidBodyTransform<From, To>` | Built-in (`system!` macro for `NedLike`, `FrdLike`, `Ecef`, custom frames) | Zero-cost phantom frame tags (3-float/matrix payload) |

---

### 2. Coordinate-Frame Types, Geometric Variance, Rotations, and Spatial Conventions

#### 2.1 Gator: `(Coordinate Scheme × Reference Frame × Geometric Object)` (`cucapra/gator`)
Basis: source (`cucapra/gator@f506d64a29daac9e7f4f7d77a7b2c4cbd268fb8a`, `src/check.ml:L83-L250`, `benchmarks/benchmarks/glsl_defs.lgl:L166-L506`, `benchmarks/benchmarks/bump/default/vertex.lgl`) + documentation (Geisler, Yoon, Kabra, He, Sanders, Sampson, OOPSLA 2020 `10.1145/3428241`)

In raw GLSL/WGSL/HLSL shaders, positions, tangent vectors, surface normals, homogeneous coordinates, and RGB colors all share `vec3` or `vec4`, allowing silent frame mixing (e.g., dotting a model-space normal with a world-space light direction). Gator introduces **geometry types** formed as `scheme<frame>.object` (`MemberTyp (ParTyp(scheme, [frame]), ParTyp(object, ...))` in `src/check.ml:L157-L173`), encoding three orthogonal components:
1. **Reference frame**: e.g., `frame model has dimension 3; frame world has dimension 3; frame view has dimension 3; frame projection has dimension 3;` (`vertex.lgl:L4-L7`).
2. **Coordinate scheme**: e.g., `cart2`, `cart3` (backed by `float[3]`), `hom` (projective homogeneous backed by `float[4]`), or non-linear schemes such as spherical coordinates (`glsl_defs.lgl:L333-L484`).
3. **Geometric object**: `point`, `vector`, `direction`, `normal`, `transformation<target>`, `normalTransformation<target>` (`glsl_defs.lgl:L167-L175`).

**Automatic canonical path synthesis (`canon` and `in`)**: Declaring transformation uniforms or conversion functions with the `canon` qualifier populates Gator's typed transformation graph:
- `canon hom<r>.point homify(cart3<r>.point v)` appends $w = 1.0$, whereas `canon hom<r>.vector homify(cart3<r>.vector v)` appends $w = 0.0$ (`glsl_defs.lgl:L488-L498`), enforcing that translations affect points but leave vectors invariant.
- `canon cart3<r>.point hom_reduce(hom<r>.point v)` performs perspective division `vec3(v) / v[3]`, whereas `hom_reduce(hom<r>.vector v)` drops $w$ without dividing (`glsl_defs.lgl:L500-L506`).
- Writing `gl_Position = aPosition in hom<projection>;` (`vertex.lgl:L27`) instructs the compiler to find a path in the `canon` graph (`cart3<model>.point` $\to$ `hom<model>.point` $\to$ `hom<world>.point` $\to$ `hom<view>.point` $\to$ `hom<projection>.point`) and emit `uProjection * uView * uModel * vec4(aPosition, 1.0)`, erasing all geometry types to standard GLSL.

**Primary-source subtlety on `normal` subtyping in `glsl_defs.lgl:L173,L339,L380-L394`**: In Gator's benchmark library, `object normal is direction;` and `object direction is vector;`. Because `cart3` declares both `canon this<target>.vector *(canon transformation<target> m, direction v)` (`L380`) and `canon this<target>.vector *(canon normalTransformation<target> m, normal d)` (`L392`), a user-supplied `normalTransformation` uniform (`uNormal`) is selected for `normal` conversions when registered as `canon` between frames where `cart3` `transformation` is absent, while `hom` omits `normalTransformation` altogether (`L444-L484`). However, because `normal <: direction <: vector`, explicit multiplication `uModel3x3 * aNormal` would still type-check via upcasting if a 3×3 `cart3` `transformation` were in scope—showing why separating covectors from contravariant vectors as *disjoint* types (not subtypes) is strictly safer when non-uniform scales occur.

#### 2.2 Variance of Points, Vectors, Normals, and Pseudovectors (Execution Proof)
Basis: execution (Probe 2B under Evidence) + derived (linear algebra / tensor representations of $\mathrm{GL}(3)$ and $\mathrm{Aff}(3)$)

Four 3-float geometric objects obey four distinct group representations under an invertible linear map $M \in \mathrm{GL}(3)$ and translation $t \in \mathbb{R}^3$:

| Geometric Object | Storage | Transformation under $(M, t)$ | Algebraic Representation | Failure When Mistyped as Contravariant Vector |
|---|---|---|---|---|
| **Point** $p$ | `f32[3]` | $M p + t$ (homogeneous $w=1$) | Affine torsor ($\mathrm{Aff}(3)$) | Adding two points breaks origin invariance; losing $w=1$ drops translation |
| **Tangent vector** $v$ | `f32[3]` | $M v$ (homogeneous $w=0$) | Standard contravariant ($V$) | Setting $w=1$ spuriously translates directions |
| **Surface normal** $n$ | `f32[3]` | $(M^{-1})^T n$ (then normalize) | Dual / covariant covector ($V^*$) | Non-uniform scale tilts normal off perpendicular, corrupting shading & collisions |
| **Pseudovector** $u \times v$ | `f32[3]` | $(\det M)(M^{-1})^T (u \times v)$ ($\det R \cdot R$ for orthogonal $R$) | Determinant-twisted axial vector ($\Lambda^2 V \cong V^* \otimes \det$) | Reflection ($\det R = -1$) flips orientation, inverting back-face culling and torque sign |

Probe 2B (under Evidence) evaluates a surface with tangent $t = (1, 1, 0)$ and unit normal $n = (-1/\sqrt{2}, 1/\sqrt{2}, 0)$ ($n \cdot t = 0$, angle $= 90^\circ$) transformed by non-uniform scale $M = \operatorname{diag}(4, 0.5, 1)$:
- **Naive $M n$ vs. $M t$**: angle becomes **`165.749967°`** (a **`75.75°` orthogonality error**, dot product `-11.136932`!).
- **Covariant $(M^{-1})^T n$ vs. $M t$**: angle remains **`90.000000°`** (error `0.000000°`, dot product `0.000e+00`, because $((M^{-1})^T n)^T (Mt) = n^T M^{-1} M t = n^T t = 0$).
- **Reflection $R = \operatorname{diag}(-1, 1, 1)$** on $u=(1,0,0), v=(0,1,0)$: $(Ru)\times(Rv) = (0, 0, -1) \ne R(u\times v) = (0, 0, +1)$ (flipped by $\det R = -1$).

#### 2.3 Topology of $\mathrm{SO}(3)$, Cross-API Conventions, and Dynamic Frames
Basis: normative (`ros-infrastructure/rep@11ca24a41f`, `rep-0103.rst:L50-L176`, `rep-0105.rst`; `KhronosGroup/glTF@8846b1aa22`, `Specification.adoc:L728-L895`; `gpuweb/gpuweb@d178d9145a`, `spec/index.bs:L878-L925`; `KhronosGroup/Vulkan-Docs@f7de774cac`, `chapters/vertexpostproc.adoc:L885-L910,L1491-L1520`) + documentation (Zhou et al., CVPR 2019)

**Topological impossibility for rotations**: Because $\mathrm{SO}(3) \cong \mathbb{R}P^3$ is not homeomorphic to any Euclidean space or sphere, every 3-angle Euler parameterization suffers gimbal-lock singularities (and 24 distinct intrinsic/extrinsic axis conventions, noted in `rep-0103.rst:L166-L168`), unit quaternions $S^3$ form a **double cover** ($q$ and $-q$ denote the same rotation, requiring hemisphere alignment before SLERP/averaging), and Zhou et al. (CVPR 2019, pp. 5745–5753) proved that **no continuous representation of $\mathrm{SO}(3)$ exists in $\mathbb{R}^d$ for $d \le 4$** (the lowest continuous Euclidean embedding is 5D/6D Gram-Schmidt). Passing a quaternion across an ABI that disagrees on scalar-first `(w, x, y, z)` vs. scalar-last `(x, y, z, w)` yields a unit-norm quaternion denoting the wrong rotation without tripping any runtime invariant check.

**Normative spatial & coordinate convention matrix (every cell anchored to pinned specification text)**:

| Standard / API (Pinned SHA) | Handedness | Up / Forward Axes | Linear Unit | Quaternion Order | Clip / NDC Depth $z$ & Screen $Y$ |
|---|---|---|---|---|---|
| **ROS REP 103** (`rep-0103.rst:L54-L176`) | Right-handed (`L97`) | Body: `+X` forward, `+Y` left, `+Z` up (`L107-L109`); ENU (`+X` E, `+Y` N, `+Z` U); `_optical`: `+Z` fwd, `+X` right, `+Y` down (`L130-L132`) | Meters (SI, `L43,L57`); radians (`L76`) | `(x, y, z, w)` in ROS `geometry_msgs/Quaternion` (REP 103 mandates quaternion #1 preferred, `L150`) | N/A (3D world/body robotics frames; REP 105 defines `earth -> map -> odom -> base_link`) |
| **glTF 2.0** (`Specification.adoc:L728-L885`) | Right-handed (`L730`) | `+Y` up, `+Z` asset front, `+X` asset left (`L732`) | Meters (`L737,L2186`); radians (`L739`) | Scalar-last **`XYZW`** (`[rx, ry, rz, rw]`, `L870,L3279`) | Asset space only (column-major TRS matrix `L875-L881`) |
| **WebGPU** (`spec/index.bs:L878-L925`) | Left-handed NDC (`x` right, `y` up, `z` into screen; `L878-L885,L4979`) | NDC bottom-left `(-1,-1,z)`; Framebuffer top-left `(0,0)`, `+Y` down (`L905-L908`) | Dimensionless NDC | N/A | $x,y \in [-1, 1]$, **$z \in [0, 1]$** (`L880-L882`) |
| **Vulkan 1.x** (`vertexpostproc.adoc:L889-L907`) | Right-handed NDC with `+Y` down in framebuffer | Clip/NDC `+Y` points **down** (unless negative viewport height is used) | Dimensionless NDC | N/A | $-w_c \le x_c, y_c \le w_c$; **$0 \le z_c \le w_c$** default (`VK_EXT_depth_clip_control` allows $-w_c$, `L895-L907`) |

**Moving frames, geodetic datums, and empirical tables**: Robotics transform trees (`REP 105`: `earth -> map -> odom -> base_link`) index transforms by **timestamp**; querying a transform across unsynchronized sensors invites silent extrapolation drift. At planetary scale, plate-fixed datums (e.g., NAD83) drift relative to Earth-centered datums (ITRF/WGS84) by centimeters per year due to tectonic plate motion, making raw `(lat, lon)` ambiguous at the meter level without explicit `(datum, epoch)`. Likewise, UTC, TAI, and GPS time scales differ by irregular, empirically announced leap seconds—meaning conversions between physical reference frames and time scales depend on **versioned empirical tables published after software ships**, not pure closed-form mathematical functions.

---

### 3. Adaptive Exact Geometric Predicates, Degeneracy, and Kernels

#### 3.1 Shewchuk's Error-Free Transformations and Compiler-Flag Fragility (Execution Proof)
Basis: source (`georust/robust@654f34cb8cdb3ae21bf59ef3472f92652942cd74`, `src/lib.rs:L52-L2185`) + documentation (Shewchuk, *DCG* 1997 `10.1007/PL00009321`; Kettner, Mehlhorn, Pion, Schirra, Yap, *Comput. Geom.* 2008 `inria-00344310`) + execution (Probe 2A under Evidence on GCC 15.2.0)

Mesh booleans, Delaunay triangulations, and convex hulls branch on polynomial determinant signs (`orient2d`, `orient3d`, `incircle`, `insphere`). Near collinearity or cocircularity, floating-point roundoff causes predicate signs to violate fundamental geometric axioms (antisymmetry, transitivity, "a point outside a convex polygon sees at least one edge"), inducing infinite loops, crashes, or non-manifold topology (Kettner et al. 2008).

Shewchuk (1997) solves this via **adaptive-precision floating-point expansions**:
1. **Error-Free Transformations (EFTs)**: Exact addition (`Two-Sum` in 6 FP ops without magnitude test; `Fast-Two-Sum` in 3 ops when $|a| \ge |b|$) and exact multiplication (`Two-Product` via Veltkamp's `Split` with `SPLITTER = 2^27 + 1 = 134217729.0`, `georust/robust` `src/lib.rs:L53,L1997-L2073`) represent the exact sum or product of two IEEE-754 doubles as a non-overlapping two-double pair `(x, y)` where `x + y` equals the exact real result with zero rounding loss.
2. **Staged floating-point filters**: `orient2d` first evaluates the fast `double` determinant and compares its magnitude against a precomputed error bound (`ccwerrboundA = (3 + 16ε)ε * detsum`). Only when the sign is uncertain does it escalate through progressively tighter expansion stages (`orient2dadapt`), paying exact-arithmetic cost exclusively near degeneracy.

**Critical compiler-flag fragility verified directly on `gcc (Debian 15.2.0-14) 15.2.0` (Probe 2A under Evidence)**:
Tested on a $64 \times 64 = 4096$-point Kettner-style near-collinear lattice ($q = (12 + 2^{-49}, 12 + 2^{-49})$, $r = (24 + 2^{-48}, 24 + 2^{-48})$, $p_{i,j} = (0.5 + i\cdot 2^{-53}, 0.5 + j\cdot 2^{-53})$ where exact $\operatorname{sgn}(\text{orient2d}(p, q, r)) = \operatorname{sgn}(j - i)$):

| Compilation Mode (`gcc 15.2.0`) | Naive `orient2d` Wrong Signs | Naive Antisymmetry Failures (`orient2d(p,q,r) != -orient2d(q,p,r)`) | Shewchuk Exact `orient2d` Wrong Signs | Veltkamp `split(1/3)` Output | Dekker `two_prod(1/3, 1/7)` Residual `y` |
|---|---|---|---|---|---|
| **`-O2 -ffp-contract=off`** (strict IEEE-754) | **2562 / 4096** (62.5%) | 0 / 4096 | **0 / 4096** (0.0%) | `ahi=0.3333333358...`, `alo=-2.4835e-9` (valid 26-bit split) | `-2.64338815386942019e-18` (exact, `diff=0`) |
| **`-O2 -mfma -ffp-contract=fast`** (FMA contraction) | **817 / 4096** (19.9%) | **1570 / 4096** (38.3%) | 0 / 4096 *(only via accidental `vfnmadd` cancellation—see below)* | **`ahi == a`, `alo == 0.0` (BROKEN!)** | `-2.64338815386942019e-18` *(coincidental double-FMA)* |
| **`-O3 -ffast-math`** (reassociation) | **2562 / 4096** (62.5%) | **2562 / 4096** (62.5%) | **1991 / 4096** (48.6%, **BROKEN!**) | Collapsed (`alo == 0.0`) | **`0.0` (BROKEN! Single `mulsd` instruction; `diff=2.643e-18`)** |

**Assembly audit (`gcc -S` on `two_prod_dekker` and `split_noinline`)**:
- Under `-O3 -ffast-math`, GCC algebraically reassociates Dekker's 17-operation `two_prod` and `two_sum` error recoveries to `0.0`, emitting **one single `mulsd %xmm1, %xmm0` instruction** and storing constant `0.0` into `*y`—silently destroying exactness across nearly half the near-collinear grid (`1991/4096` wrong signs).
- Under `-O2 -mfma -ffp-contract=fast`, GCC contracts `abig = SPLITTER*a - a` and `ahi = SPLITTER*a - abig` into `vfmsub132sd`, which algebraically evaluates exact $(2^{27}+1)a - 2^{27}a = a$, **completely breaking Veltkamp's splitting invariant** (`split_noinline(1/3)` returns `ahi == a, alo == 0.0`). Inlined `two_prod_dekker` escaped error on x86_64 *solely by coincidence* because GCC simultaneously contracted `err1 = p - ahi*bhi` into `vfnmadd231sd`, computing `-fma(a, b, -p)` directly; across any non-inlined TU boundary or standalone `split` call, FMA contraction corrupts exactness. Conversely, hardware `fma(a, b, -p)` replaces Dekker's 17-op `two_prod` directly in 2 ops when explicitly invoked via IEEE `fma()`.
- **ABI hazard**: Object files do not record floating-point compilation flags; LTO inlining strict-compiled predicate C code into a `-ffast-math` translation unit silently voids exactness.

#### 3.2 Exact Constructions, Symbolic Perturbation, Tolerant B-Reps, and Topological Naming
Basis: source (`CGAL/cgal@7305123709`) + documentation (Yap, *Comput. Geom.* 1997 `10.1016/0925-7721(95)00040-2`; Edelsbrunner & Mücke, *ACM TOG* 1990; Sherman, Michel, Carbin, ICFP 2019; Kripac, *CAD* 1997)

Exact predicates alone do not handle **constructions** (e.g., intersecting two planes or rotating a mesh creates new vertex coordinates whose bit-length grows exponentially across cascaded booleans, and curved intersections/rotations leave $\mathbb{Q}$ for algebraic/real numbers):
- **Yap's Exact Geometric Computation (EGC) & CGAL (`CGAL/cgal@7305123709`)**: Separates *predicates* from *constructions*. CGAL's `Exact_predicates_inexact_constructions_kernel` (`Epick`) guarantees consistent branching on existing inputs, while `Exact_predicates_exact_constructions_kernel` (`Epeck`) wraps constructed objects in **lazy DAGs** evaluated first via interval arithmetic and escalated to arbitrary-precision rationals/algebraic numbers (`GMP`/`CORE`/`LEDA`) only when an interval sign contains zero.
- **Degeneracies & Simulation of Simplicity (Edelsbrunner & Mücke 1990)**: Infinitesimally perturbs coordinates symbolically by powers of $\varepsilon$ so general-position algorithms never hit zero-determinant branches, though post-processing must collapse zero-volume artifacts.
- **Exact-real solid modeling (`StoneWorks`, Sherman et al., ICFP 2019)**: Formulates solid geometry over constructive reals with continuity-preserving predicates, trading speed for soundness on curved geometry.
- **Tolerant industrial B-rep kernels & the topological naming problem**: Commercial boundary-representation kernels (Parasolid, ACIS, OpenCASCADE) attach per-entity floating-point tolerances to vertices/edges/faces to glue inconsistent trim curves—causing brittle boolean failures and cross-kernel healing passes. Independently of numerics, history-based parametric CAD suffers the **topological naming problem** (Kripac 1997; FreeCAD): downstream features (fillets, sketches) bind to upstream faces/edges by fragile sequential indices (`Face6`), so an upstream edit that splits or reorders faces silently attaches fillets to the wrong geometry unless faces carry derivation-based provenance.

**Shape representation closure comparison**:

| Representation | Closed Under Exact Boolean (`∪`, `∩`, `\`)? | Closed Under Arbitrary Rotation? | Closed Under Exact Offset (`d(p, S) ≤ r`)? | Exact Predicates / Topology Guarantee |
|---|---|---|---|---|
| **Float triangle mesh (STL/OBJ)** | No (roundoff creates non-manifold self-intersections) | Approximate (vertex rounding) | No (requires remeshing) | None unless coupled with exact EGC/mesh-arrangements |
| **Rational EGC polyhedra (CGAL `Epeck`)** | Yes (exact over $\mathbb{Q}$; bit-length grows per cascade) | No (requires rational rotation approximations or algebraic numbers) | No (spherical/cylindrical rounds leave polyhedra) | Exact topological consistency |
| **NURBS B-Rep (OpenCASCADE/STEP)** | Approximate (intersection of degree-$d$ patches has degree $d^2$, approximated by splines) | Yes (exact affine transforms of control points) | Approximate | Heuristic tolerant stitching; vulnerable to topological naming breakage |
| **Implicit SDF / F-rep (`Fidget`/`libfive`)** | Yes (exact closed-form `min`/`max` composition) | Yes (exact domain coordinate warp $f(R^{-1} p)$) | Yes (for exact SDFs: $f(p) - r$) | Dependent on abstract domain soundness (interval/affine rounding!) during meshing |

---

### 4. Implicit Surface Compilation: Fidget's SSA Tapes, JIT, and Abstract Interpretation

#### 4.1 Compilation Pipeline and Interval Rounding Audit (`mkeeter/fidget`)
Basis: source (`mkeeter/fidget@1879743ddc1d73dac14a42a8184a3c5b758dcca5`, `fidget-core/src/compiler/ssa_tape.rs:L12-L150`, `fidget-core/src/types/interval.rs:L5-L725`; `libfive/libfive@918387a922`; `mkeeter/mpr@eb63defa00`) + documentation (Keeter, SIGGRAPH 2020; Comba & Stolfi, SIBGRAPI 1993) + execution (Probe 2C under Evidence)

Fidget treats a 3D shape $S = \{p \in \mathbb{R}^3 \mid f(p) \le 0\}$ as a closed-form functional program and renders/meshes it via **abstract interpretation over spatial boxes**:
1. **DAG deduplication & reverse SSA flattening (`ssa_tape.rs:L22-L150`)**: Math expressions are hash-consed into a DAG (`Context`), then flattened into a straight-line reverse-order `SsaTape` (`Vec<SsaOp>`) where constants become immediates and choice operations (`min`/`max`/`and`/`or`) are counted explicitly (`choice_count`).
2. **Register allocation & JIT (`reg_tape.rs`, `fidget-jit`)**: An LRU register allocator packs `SsaTape` into fixed registers (`RegTape`) for VM interpretation or hand-written `x86_64`/`aarch64` JIT code generation targeting four evaluators: scalar point (`f32`), SIMD float slice, dual-number gradient (`Grad`), and interval (`Interval`).
3. **Interval-guided tape specialization (`Choice`)**: Evaluating a tape over a 3D spatial box $B = [x_0, x_1] \times [y_0, y_1] \times [z_0, z_1]$ returns an enclosure $[f_{\min}, f_{\max}]$ plus a per-node trace of `Choice::{Left, Right, Both}` (`interval.rs:L326-L405`).
   - If $f_{\min} > 0$, the box is provably outside; if $f_{\max} < 0$, provably inside—both terminate recursion immediately.
   - If $0 \in [f_{\min}, f_{\max}]$, any `min(a, b)` node where `a.upper < b.lower` emits `Choice::Left`, allowing Fidget to **specialize (prune)** the tape for all child octants by deleting the unreachable `b` subtree!

**Primary-source soundness audit of `fidget-core/src/types/interval.rs`**:
- **Unrounded `f32` arithmetic (`L5-L15`)**: Fidget's doc comment explicitly warns:
  ```rust
  /// # Warning
  /// This implementation does not set rounding modes, so it may not be _perfect_.
  ```
  Endpoints are computed in default round-to-nearest-even `f32` without `FE_DOWNWARD`/`FE_UPWARD` or `next_down`/`next_up` widening. Probe 2C verifies a concrete containment failure: for $x = [1.0, 1.0]$ and $y = [2^{-25}, 2^{-25}]$ (both exact `f32`), the exact real sum is $1 + 2^{-25}$, yet unrounded `f32` interval addition computes upper bound `1.0` (`contains exact? False`), whereas 1-ULP outward widening (`next_up_f32`) gives `1.0000001192` (`contains exact? True`). Consequently, Fidget's interval pruning trades strict mathematical soundness on 1-ULP razor-thin or tangent boundaries for JIT throughput without FPU control-word stalls.
- **NaN and domain-singularity policy (`L32-L45, L236-L405, L702-L725`)**: The only valid intervals are `[lower, upper]` (`lower <= upper`) or `[NaN, NaN]`. Division/reciprocal by an interval containing `0.0`, `sqrt` on `lower < 0.0`, `ln` on `lower <= 0.0`, and `tan` spanning an asymptote all return `[NaN, NaN]`. Crucially, `min`, `max`, `and`, `or` return `(NaN, Choice::Both)` whenever either operand `has_nan()` (`L333-L405`), preventing speculative branch pruning across singularities.
- **Interval dependency over-estimation vs. affine arithmetic (Probe 2C)**: When a spatial variable occurs multiple times (e.g., $f(x, y) = (x + y) - x + y^2 - 0.5$ over $[-1, 1]^2$), interval arithmetic ignores the correlation between $+x$ and $-x$, widening every box by $\Delta x$. Probe 2C's depth-6 quadtree subdivision confirms:
  - **Interval Arithmetic**: `596` box evaluations, `128` unresolved leaf cells.
  - **Affine Arithmetic** (Comba & Stolfi 1993): `252` box evaluations, `64` unresolved leaf cells (**2.37× fewer evaluations**, exact $x$-cancellation).

---

### 5. CAD Decompilation (`Szalinski`), Constrained Diagramming (`Penrose`), and Fabrication (`Knitout`)

#### 5.1 Szalinski: Equality Saturation CAD Decompilation & Single-Linkage Constant Drift
Basis: source (`uwplse/szalinski@9ce7acc3c766c8a6f5edd9c431e276502c331b6d`, `src/num.rs:L9-L112`, `src/solve.rs:L76-L137`; `egraphs-good/egg@73975c9819`) + documentation (Nandi et al., ICFP 2018; Nandi et al., PLDI 2020 `10.1145/3385412.3386012`) + execution (Probe 2D under Evidence)

Compiling parametric CAD into flat triangle meshes destroys loop structure and user parameters. Building on ICFP 2018 CSG-to-mesh semantics and the `egg` equality saturation engine (`egraphs-good/egg@73975c9819`), **Szalinski** takes flat CSG expressions (e.g., unions of translated primitives) and recovers structured loops (`Fold`/`Map2`/`Repeat`) by combining algebraic CAD rewrite rules (`src/rules.rs`) with arithmetic list solvers (`src/solve.rs`):
- `solve_deg1` (`src/solve.rs:L78-L103`) fits linear progressions $a \cdot i + b$ from the first two list elements, tries snapping $(a, b)$ to multiples of `SOLVE_ROUND = 0.01`, and accepts the closed-form formula if every element satisfies `is_close`.
- `solve_deg2` (`src/solve.rs:L105-L127`) fits quadratic progressions $a \cdot i^2 + b \cdot i + c$ for lists of length $> 3$.

**Primary-source audit of approximate numeric equivalence (`src/num.rs:L12-L112`)**: Because floating-point constants extracted from meshes contain numerical noise, Szalinski defines `ABS_EPSILON = 0.0001`, `REL_EPSILON = 0.0001`, and `is_close(a, b)` (`|a-b| <= 1e-4 || |a-b| <= max(|a|,|b|) * 1e-4`), then executes `unify_close_nums(egraph)` (`L85-L112`):
1. Collects all `Cad::Num` nodes across all e-classes,
2. Sorts them numerically (`nums.sort()`), and
3. Calls `egraph.union(e0, e1)` on every adjacent pair `(num0, num1)` satisfying `num0.is_close(num1)`.

Because approximate equality is **non-transitive**, unioning adjacent sorted pairs computes the **single-linkage transitive closure**! Probe 2D executes the exact `unify_close_nums` algorithm on 101 constants in `[0.0, 0.009]` spaced by `9e-5 < 1e-4`: all 101 constants perform `100` unions and collapse into **1 single e-class**, equating `0.0` with `0.009` (**90× `ABS_EPSILON`**). Thus Szalinski's constant unification is a heuristic recovery pass rather than a tolerance-bounded sound congruence; verifying synthesized CAD against the input mesh requires an independent post-hoc geometric check (e.g., Hausdorff distance).

#### 5.2 Penrose: Relational Compilation via Exterior-Point L-BFGS Optimization
Basis: source (`penrose/penrose@d46d92b7b39c6ef6539a38e8a8f7472ebb5d0502`, `packages/core/src/engine/Optimizer.ts:L6-L180`, `Lbfgs.ts`, `Autodiff.ts`) + documentation (Ye et al., SIGGRAPH 2020)

Penrose compiles mathematical specifications split across three DSLs—**Domain** (type/predicate schema), **Substance** (mathematical objects/relations), and **Style** (visual mapping emitting `encourage` objectives $f(x)$ and `ensure` constraints $g_j(x) \le 0$)—into positioned SVG diagrams. Direct inspection of `Optimizer.ts:L6-L157` resolves its exact numerical compilation mechanism:
- **Exterior point penalty formulation (`L11, L77-L97`)**: Reduces constrained layout to a sequence of unconstrained problems minimizing
  $$\phi(x, \lambda) = f(x) + \lambda \sum_j \max(g_j(x), 0)^2$$
  starting at `initConstraintWeight = 1e3` and multiplying $\lambda$ by `weightGrowthFactor = 10` per outer exterior-point round (`EPround`) until `stateChange < epStop` or `energyChange < epStop` (`epStop = 1e-3`, `L131-L148`).
- **Inner L-BFGS + reverse-mode autodiff (`Lbfgs.ts`, `Autodiff.ts`)**: Minimizes $\phi(\cdot, \lambda)$ over `Float64Array` state vectors until $\|\nabla \phi(x)\| < \text{uoStop}$ (`uoStop = 1e-2`, with source comment `L95-L96` noting tighter `1e-5` tolerances cause line-search interval collapse under autodiff).

This architecture shares a deep compiler property with parametric CAD sketch solvers: a declarative constraint specification defines a **relation**, not a function. Non-convex optimization has no global completeness guarantee, depends on random initialization seeds and floating-point library rounding, and can jump between distinct valid branches/chiralities across solver updates unless paired with a solution lockfile and an independent constraint-satisfaction checker.

#### 5.3 Fabrication Instruction Sets: Modal G-Code vs. `knitout` Fenced-Tangle Semantics
Basis: source (`textiles-lab/knitout@17b868c5a48cf8ce2d25bbfb7d23f2ab7ba55ddf`, `knitout.html`) + documentation (NIST RS274NGC v3, 2000; McCann et al., *ACM TOG* 2016; Lin, Narayanan, Ikarashi, Ragan-Kelley, Bernstein, McCann, *ACM TOG* 42(4), Article 143, 2023 `10.1145/3592449`)

- **Modal G-code (NIST RS274NGC)**: Encodes CNC toolpaths via global modal groups (`G90` absolute vs. `G91` incremental coordinates; `G20` inches vs. `G21` millimeters; active plane `G17`/`G18`/`G19`). A single move `G1 X10.0` has no local denotation independent of arbitrarily distant preceding mode switches, and dialect divergence across machine controllers forces ad-hoc, unverified post-processors.
- **`knitout` v0.6 (`knitout.html`)**: Defines a portable, machine-independent instruction stream (`.k` files) for V-bed knitting machines with explicit version magic strings, required `;;Carriers` headers, explicit carriage-pass directionality, and needle-bed operations (`in`, `out`, `knit`, `tuck`, `split`, `miss`, `xfer`, `rack`, `drop`, `amiss`).
- **Knot-theoretic semantics (Lin et al., SIGGRAPH 2023 `10.1145/3592449`)**: Existing knitting representations were either incomplete or overly syntactic (unable to equate different valid needle schedules that produce the same textile). Lin et al. give `knitout` a formal operational validity relation (tracking needle occupancy, carrier alignment, and empty start/end completeness) together with a denotational domain of **fenced tangles** (extending mathematical knot theory). Under fenced-tangle equivalence, they prove a sequence of compiler rewrite rules sound—guaranteeing that retargeted or optimized instruction schedules produce the **same topological knit object**. Crucially, the guarantee is purely **topological**: continuous physical yarn mechanics (tension, friction, elasticity limits) remain outside the formal equivalence relation and rely on heuristic bounds.

## Boundaries

- **Not examined**:
  - Geometric Dimensioning and Tolerancing (GD&T, ISO GPS / ASME Y14.5) tolerance-zone stack-up analysis, finite-element meshing quality metrics, and Building Information Modeling (BIM/IFC) schemas.
  - Full formal proof of Gator's type soundness theorem for arbitrary user-defined non-linear coordinate schemes beyond `cart2`/`cart3`/`hom`.
  - Complete machine-checked formalizations of Shewchuk's adaptive predicates in Coq/Lean/Isabelle (beyond `georust/robust` source inspection and C execution testing).
  - Continuous yarn-tension physics simulations for machine knitting and non-planar multi-axis robotic additive manufacturing toolpaths.
- **Unknown**:
  - Whether Haskell's GHC `uom-plugin` or dependent-type systems (Idris/Lean/Agda) can ergonomically type Hart's heterogeneous dimensioned matrices *and* matrix inverses without exponential constraint blowup on large control models.
  - Exact performance overhead of replacing Fidget's unrounded `f32` interval JIT with IEEE-754 outward-rounded intervals (`FE_UPWARD` trick via negated lower bounds `(-lo, hi)` using SIMD `max`/`min` without changing MXCSR/FPCR mode bits!) on complex 10K-node CSG trees.
- **Known not to apply**:
  - **Attractive stronger conclusion rejected**: *"Compiling Shewchuk's exact predicates with `-O2 -mfma -ffp-contract=fast` is always safe because our `orient2d` test got 0 errors."* — **False.** Our probe proved that `-mfma -ffp-contract=fast` breaks Veltkamp's standalone `split` (`ahi == a, alo == 0.0`); inlined `two_prod_dekker` passed only through accidental simultaneous FMA contraction of `err1 = p - ahi*bhi`, which is neither guaranteed across compilers/flags nor across non-inlined calls.
  - **Attractive stronger conclusion rejected**: *"Fidget's interval arithmetic strictly guarantees zero missed thin surface features."* — **False.** Source inspection (`fidget-core/src/types/interval.rs:L8-L9`) and Probe 2C confirm Fidget omits directed rounding, allowing 1-ULP containment leaks on boundary expressions.
  - **Attractive stronger conclusion rejected**: *"Szalinski's `egg` e-graph preserves a fixed geometric tolerance $\varepsilon$ across rewrites."* — **False.** `src/num.rs:L85-L112` computes single-linkage transitive closure over sorted constants, permitting unbounded chaining drift ($90\times \varepsilon$ demonstrated in Probe 2D).
  - **Attractive stronger conclusion rejected**: *"In-language unit-of-measure types prevent Mars Climate Orbiter–class bugs."* — **False** unless unit metadata crosses serialization and FFI schemas; MCO failed in a file exchanged between two separate programs.
- **Unsupported**:
  - Continuous Euclidean representations of 3D rotations $\mathrm{SO}(3)$ in $\le 4$ real coordinates (mathematically impossible; Zhou et al., CVPR 2019).
  - Direct addition of affine points (`point + point`) or scaling of affine points in affine-safe quantity algebras (`mp-units`, Gator).

## Evidence

### Primary Git Repositories & Source Anchors (Observed 2026-11-19)
- **`dotnet/fsharp`** (`57f77cbac4923aa41cf308711553232dfd608da7`):
  - `src/Compiler/Checking/ConstraintSolver.fs:L800-L977` — `UnifyMeasureWithOne` (`L806-L822`), `UnifyMeasures` (`L825-L826`), `SimplifyMeasure` (`L831-L858`), `NormalizeExponentsInTypeScheme` (`L929-L937`), reduced-row-echelon normal form specification (`L939-L964`).
  - `src/Compiler/TypedTree/TypedTree.fs:L4803-L4821` — `Measure.RationalPower`.
- **`mpusz/mp-units`** (`566b8615a74e84fba824952a5c1dddc1935d9a2e`): `docs/users_guide/framework_basics/the_affine_space.md:L1-L45` (affine point vs. displacement vector algebra).
- **`iliekturtles/uom`** (`a465bcc2b3bf67f9f12fc0b133d371762d9d8fe4`): `README.md`.
- **`cucapra/gator`** (`f506d64a29daac9e7f4f7d77a7b2c4cbd268fb8a`):
  - `src/check.ml:L83-L250` — subtyping, `chi_object_lookup` (`scheme<frame>.object`), `least_common_parent`.
  - `benchmarks/benchmarks/glsl_defs.lgl:L166-L506` — `prototype geometry`, `cart2`, `cart3`, `hom`, `normal`, `normalTransformation`, `canon` `homify`/`hom_reduce`.
  - `benchmarks/benchmarks/bump/default/vertex.lgl:L1-L34` — `canon` uniform declarations and `aPosition in hom<projection>`.
- **`helsing-ai/sguaba`** (`4a71898daac0b40fef3748491a15a2c1c16cb9c7`): `README.md` (`Coordinate`, `Vector`, `system!`, `Pose`, `Orientation`).
- **`ros-infrastructure/rep`** (`11ca24a41f31480dfb9562ba99f2a5b93d3ebda5`): `rep-0103.rst:L40-L176` (SI units, right-handed axes, ENU/NED/`_optical`, quaternion preference, 24 Euler conventions) and `rep-0105.rst`.
- **`KhronosGroup/glTF`** (`8846b1aa225dd8430322c03150919df47e3122ae`): `specification/2.0/Specification.adoc:L728-L895,L2186,L3279` (right-handed, `+Y` up, `+Z` front, meters, radians, XYZW quaternions).
- **`gpuweb/gpuweb`** (`d178d9145ab1652ec933e71a8c30e8f6470f00a3`): `spec/index.bs:L878-L925,L4979` (left-handed NDC, `z ∈ [0, 1]`, framebuffer top-left `+Y` down).
- **`KhronosGroup/Vulkan-Docs`** (`f7de774cace1509af0f10b8d859c973b5354ff62`): `chapters/vertexpostproc.adoc:L885-L910,L1491-L1520` (clip volume `0 <= z_c <= w_c` default, `VK_EXT_depth_clip_control`).
- **`georust/robust`** (`654f34cb8cdb3ae21bf59ef3472f92652942cd74`): `src/lib.rs:L52-L53,L77-L1332,L1997-L2185` (`SPLITTER = 134_217_729f64`, `orient2d`, `orient3d`, `incircle`, `insphere`, `two_product`, `split`, `two_sum`, `fast_two_sum`).
- **`CGAL/cgal`** (`7305123709c59d1ce7d2f5c17a154c8e7691f630`).
- **`mkeeter/fidget`** (`1879743ddc1d73dac14a42a8184a3c5b758dcca5`):
  - `fidget-core/src/types/interval.rs:L5-L725` — rounding-mode warning (`L8-L9`), `[NaN, NaN]` invariant (`L32-L45`), `min`/`max` `Choice::Both` on `NaN` (`L326-L405`), `div`/`recip`/`sqrt` domain handling.
  - `fidget-core/src/compiler/ssa_tape.rs:L12-L150` — reverse SSA flattening and `choice_count`.
- **`libfive/libfive`** (`918387a9220dbac2f7ab32fb35e274c6794439cf`) & **`mkeeter/mpr`** (`eb63defa00239571984e579039166ea575da0dad`).
- **`uwplse/szalinski`** (`9ce7acc3c766c8a6f5edd9c431e276502c331b6d`): `src/num.rs:L9-L112` (`ABS_EPSILON = 1e-4`, `REL_EPSILON = 1e-4`, `unify_close_nums`), `src/solve.rs:L76-L137` (`SOLVE_ROUND = 0.01`, `solve_deg1`, `solve_deg2`).
- **`egraphs-good/egg`** (`73975c9819efb4af2f3c6c1b44fa53f8c5742574`).
- **`penrose/penrose`** (`d46d92b7b39c6ef6539a38e8a8f7472ebb5d0502`): `packages/core/src/engine/Optimizer.ts:L6-L180` (exterior-point penalty $\phi(x, \lambda)$, `initConstraintWeight = 1e3`, `weightGrowthFactor = 10`, `uoStop = 1e-2`, `epStop = 1e-3`, L-BFGS).
- **`textiles-lab/knitout`** (`17b868c5a48cf8ce2d25bbfb7d23f2ab7ba55ddf`): `knitout.html` (Knitout `.k` File Format v0.6).

### Peer-Reviewed Literature & Reports
- A. Kennedy, *Relational Parametricity and Units of Measure*, POPL 1997; *Types for Units-of-Measure: Theory and Practice*, CEFP 2009; R. Atkey, P. Johann, A. Kennedy, *Abstraction and Invariance for Algebraically Indexed Types*, POPL 2013.
- Mars Climate Orbiter Mishap Investigation Board, *Phase I Report*, November 10, 1999 (`https://llis.nasa.gov/llis_lib/pdf/1009464main1_0641-mr.pdf`).
- D. Geisler, I. Yoon, A. Kabra, H. He, Y. Sanders, A. Sampson, *Geometry Types for Graphics Programming*, PACMPL 4 (OOPSLA 2020), `10.1145/3428241`.
- Y. Zhou, C. Barnes, J. Lu, J. Yang, H. Li, *On the Continuity of Rotation Representations in Neural Networks*, CVPR 2019, pp. 5745–5753.
- J. R. Shewchuk, *Adaptive Precision Floating-Point Arithmetic and Fast Robust Geometric Predicates*, *Discrete & Computational Geometry* 18(3):305–363, 1997, `10.1007/PL00009321`.
- L. Kettner, K. Mehlhorn, S. Pion, S. Schirra, C. Yap, *Classroom Examples of Robustness Problems in Geometric Computations*, *Computational Geometry* 40(1), 2008 (`inria-00344310`).
- C. K. Yap, *Towards Exact Geometric Computation*, *Computational Geometry* 7:3–23, 1997, `10.1016/0925-7721(95)00040-2`.
- C. Nandi, M. Willsey, A. Anderson, J. R. Wilcox, E. Darulova, D. Grossman, Z. Tatlock, *Synthesizing Structured CAD Models with Equality Saturation and Inverse Transformations* (Szalinski), PLDI 2020, `10.1145/3385412.3386012` (`arXiv:1909.12252`).
- K. Ye, W. Ni, M. Krieger, D. Ma'ayan, J. Wise, J. Aldrich, J. Sunshine, K. Crane, *Penrose: From Mathematical Notation to Beautiful Diagrams*, *ACM Trans. Graph.* 39(4), Article 144, SIGGRAPH 2020.
- J. Lin, V. Narayanan, Y. Ikarashi, J. Ragan-Kelley, G. Bernstein, J. McCann, *Semantics and Scheduling for Machine Knitting Compilers*, *ACM Trans. Graph.* 42(4), Article 143, 2023, `10.1145/3592449`.

### Local Execution Probes (2026-11-19, x86_64 Linux, GCC 15.2.0, Python 3.13)
- **Probe 2A (Shewchuk `orient2d`, Veltkamp `split`, and Dekker `two_prod` under GCC 15.2.0 flags)**:
  Minimal C kernel compiled with `gcc -O2 -ffp-contract=off`, `gcc -O2 -mfma -ffp-contract=fast`, and `gcc -O3 -ffast-math`:
  ```c
  #define SPLITTER 134217729.0 /* 2^27 + 1 */
  __attribute__((noinline)) void split_noinline(double a, double *ahi, double *alo) {
    double c = SPLITTER * a, abig = c - a; *ahi = c - abig; *alo = a - *ahi;
  }
  __attribute__((noinline)) void two_prod_dekker(double a, double b, double *x, double *y) {
    double p = a * b, ca = SPLITTER * a, abig = ca - a, ahi = ca - abig, alo = a - ahi;
    double cb = SPLITTER * b, bbig = cb - b, bhi = cb - bbig, blo = b - bhi;
    double err1 = p - (ahi * bhi), err2 = err1 - (alo * bhi), err3 = err2 - (ahi * blo);
    *x = p; *y = (alo * blo) - err3;
  }
  ```
  Evaluated alongside expansion-summed `orient2d` on $64\times 64$ lattice $q=(12+2^{-49},12+2^{-49})$, $r=(24+2^{-48},24+2^{-48})$, $p_{i,j}=(0.5+i\cdot 2^{-53},0.5+j\cdot 2^{-53})$ and inputs `a = 1.0/3.0`, `b = 1.0/7.0` (via `volatile double`):
  - `gcc -O2 -ffp-contract=off`: `naive_wrong = 2562/4096`, `shewchuk_wrong = 0/4096`; `split_noinline(1/3)` valid (`ahi != a`, `alo = -2.4835e-9`); Dekker `two_prod(1/3, 1/7)` `diff = 0.0`.
  - `gcc -O2 -mfma -ffp-contract=fast`: `naive_antisym_fail = 1570/4096`; `split_noinline(1/3)` broken (`ahi == a`, `alo == 0.0`).
  - `gcc -O3 -ffast-math`: `shewchuk_wrong = 1991/4096`; `two_prod_dekker` compiled to single `mulsd`, returning `y = 0.0` (`diff = 2.643e-18`).
- **Probe 2B (Geometric variance)**: Under $M = \operatorname{diag}(4, 0.5, 1)$ on tangent $t=(1,1,0)$ and normal $n=(-1/\sqrt{2}, 1/\sqrt{2}, 0)$, naive `M*n` yields `75.749967°` orthogonality error (`dot = -11.136932`) vs. `(M^-1)^T*n` exact `90.000000°` (`dot = 0.0`); reflection `R = diag(-1, 1, 1)` flips cross product sign of $(1,0,0)\times(0,1,0)$.
- **Probe 2C (Fidget intervals vs. affine arithmetic)**: Unrounded `f32` `1.0 + 2^-25` yields upper `1.0` (`contains exact? False`) vs. outward-widened `1.0000001192` (`True`); depth-6 quadtree on `(x+y) - x + y^2 - 0.5` over `[-1, 1]^2` took `596` IA box evals (`128` leaves) vs. `252` AA evals (`64` leaves, `2.37x` reduction).
- **Probe 2D (F# rational-GCD & Szalinski single-linkage)**: F# rational-GCD normalization turns $u^2 v^{-3} = m^2 s^{-4}$ into $v = (v')^2, u = (v')^3 m s^{-2}$; Szalinski `unify_close_nums` collapses 101 constants in `[0.0, 0.009]` spaced by `9e-5` into 1 e-class (`90x ABS_EPSILON`).

## Revalidation

1. **Re-run Shewchuk & Veltkamp compiler probe after any toolchain/ISA change**: Compile `orient2d` + standalone `split` + Dekker `two_prod` with the project's actual release C/Rust flags (including LTO!) and check both `0/4096` exactness on the near-collinear lattice and `ahi != a` on `split(1/3)` in assembly/runtime. On Rust/LLVM targets, verify `rustc` does not contract across `f64` operations (`-C target-feature=+fma` without explicit `mul_add`) when wrapping `georust/robust`.
2. **Re-check Fidget rounding policy**: Inspect `fidget-core/src/types/interval.rs` on newer `mkeeter/fidget` commits to check whether directed rounding (or negation-trick outward rounding) has been introduced for `Interval` evaluation and JIT emission.
3. **Re-check coordinate conventions on spec revision**: Diff `ros-infrastructure/rep` (`rep-0103.rst`), `KhronosGroup/glTF` (`Specification.adoc` §Coordinate System), `gpuweb/gpuweb` (`spec/index.bs` §Coordinate Systems), and `KhronosGroup/Vulkan-Docs` (`vertexpostproc.adoc`) whenever targeting a new major graphics/asset spec version.
4. **Re-check F# measure solver and Szalinski/Penrose algorithms**: Diff `dotnet/fsharp` `ConstraintSolver.fs` (`UnifyMeasureWithOne`, `NormalizeExponentsInTypeScheme`), `uwplse/szalinski` `src/num.rs` (`unify_close_nums`), and `penrose/penrose` `Optimizer.ts` if adopting newer upstream releases.
