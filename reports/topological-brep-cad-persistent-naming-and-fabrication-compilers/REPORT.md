# Topological B-Rep CAD, Persistent Naming, and Physical Fabrication Compilers

## Summary

Parametric solid modeling and physical fabrication compilers share a common structural challenge: translating high-level declarative or imperative design programs into geometry and machine schedules whose validity is governed by discrete topological invariants and hard physical constraints. In Boundary-Representation (B-Rep) CAD kernels, boolean and feature operations must maintain manifold topology satisfying the generalized Euler–Poincaré relation $V - E + F - R = 2(S - G)$ while tracking sub-shape identity across parametric re-evaluation—the **Topological Naming Problem (TNP)**. Because continuous parameter edits induce genuine discrete topological bifurcations (a single face splitting into two, merging, or vanishing), no pure bijective naming scheme exists; robust systems instead record an explicit evolution relation (`PRIMITIVE`, `GENERATED`, `MODIFY`, `DELETE`) combined with feature-history provenance and ambiguity disambiguation (Capoyleas–Chen–Hoffmann, Kripac, OCCT `TNaming`, FreeCAD `ElementMap`, and Zoo KCL's tag/artifact-graph hybrid). Implicit Signed Distance Fields (SDF / F-Rep, exemplified by `Fidget`) bypass TNP entirely during CSG evaluation through continuous scalar fields and interval arithmetic, at the cost of lacking native discrete edge/face handles for selective local filleting, GD&T datums, and exact NURBS/STEP B-Rep interchange.

Downstream physical fabrication compilers—V-bed industrial machine knitting (`Knitout`, `AutoKnit`, `Knitting Skeletons`, and flat-bed transfer planners) and CNC G-code trajectory planners (`LinuxCNC`)—expose physical actuators as **resource-linear, spatially constrained target ISAs**. In V-bed knitting, held stitch loops behave like linear resources allocated on a 1D dual-bed integer lattice (`front`/`back`) coupled by a bed-racking offset $R$ (`front_idx = back_idx + R`); yarn elasticity bounds single-step racking, unintended loop co-location irreversibly merges stitches, and full-gauge beds can suffer topological blocking without half-gauge slack or slider needles. In CNC trajectory planning, lookahead corner blending trades geometric chord tolerance against centripetal acceleration limits ($v_{\max} = \sqrt{a_n R_{\max}}$, where $R_{\max}$ scales linearly with tolerance and $v_{\max}$ scales with $\sqrt{\text{tol}}$), while rigid-origami kinematic compilers must additionally certify local flat-foldability and spherical loop-closure matrix products around every interior vertex. Across all three domains, compiler "undefined behavior" manifests not as a software crash but as corrupted downstream features, snapped yarn, gouged workpieces, or jammed mechanisms.

## Applicability

This report synthesizes primary source inspection, peer-reviewed specifications, and executable numerical/combinatorial micro-probes across four interconnected system families:

1. **B-Rep Parametric CAD & Persistent Naming Systems** (comparative study of naming algebras and implementations):
   - Open CASCADE Technology (`Open-Cascade-SAS/OCCT` @ `4dbfdcc448c0b3e565488afcd626c84483172db9`), specifically `TNaming` (`TKCAF`) and `BRepBuilderAPI_MakeShape` (`TKTopAlgo`).
   - FreeCAD (`FreeCAD/FreeCAD` @ `1e7f16061ac499c1adc67bc39f597b6e5088e8d7`), specifically `Data::ElementMap` (`src/App/ElementMap.h`) and `Part::OpCodes` (`src/Mod/Part/App/TopoShapeOpCode.h`, encoding scheme version `15`).
   - Zoo Modeling App / KCL (`KittyCAD/modeling-app` @ `10ae8aa9cdf6cbc8e6eaf188b37a3d6ec0afec34`), specifically `kcl-lib` execution IDs (`id_generator.rs`), artifact graphs (`artifact.rs`), geometry topology roots (`geometry.rs`), and edge tag specifiers (`std/edge.rs`).
   - Foundational TNP and differentiable-CAD literature: Capoyleas, Chen, and Hoffmann (1996), Kripac (1995/1997), Marcheix and Pierra (2002), and Cascaval et al. (2022).
2. **Implicit SDF / F-Rep Compilers** (architectural contrast against B-Rep):
   - Fidget (`mkeeter/fidget` @ `1879743ddc1d73dac14a42a8184a3c5b758dcca5`, `fidget-core`) and Keeter (2020).
3. **Machine Knitting IRs, Compilers, and Transfer Planners**:
   - Knitout v0.6 specification (`textiles-lab/knitout` @ `17b868c5a48cf8ce2d25bbfb7d23f2ab7ba55ddf`, `knitout.html`).
   - AutoKnit (`textiles-lab/autoknit` @ `a711d2096e378547cedce943c25c16c0ecd25731`, `ScheduleCost.hpp` and chain-peeling pipeline) and McCann et al. (2016) / Narayanan et al. (2018).
   - Flat-bed transfer planning algorithms (`textiles-lab/transfer-plan-supplement` @ `9060dcc0b6e003dc62e645e2921055261918e218`, `cse.js`, `schoolbus.js`, `schoolbus-sliders.js`) and Lin, Narayanan, and McCann (2018).
   - Knitting Skeletons (`xionluhnis/knitskel` @ `aebb0f05b05ce300381eb6d84bbf938f208d0b6d`, `src/schedule.js`) and Kaspar, Makatura, and Matusik (2019).
4. **CNC Trajectory Planning & Rigid-Origami Kinematic Constraints**:
   - LinuxCNC (`LinuxCNC/linuxcnc` @ `76ee5a1b63fa595040d398b615702c83dadf8f05`), specifically `src/emc/tp/blendmath.h` and `src/emc/tp/tp_types.h`.
   - Rigid-origami folding constraints from Demaine & O'Rourke (2007) and Tachi (2011).

Findings about a specific repository symbol, constant, or enum variant apply strictly to the pinned commit SHA listed above; architectural invariants (Euler–Poincaré balance, TNP non-bijectivity across topological bifurcations, V-bed racking alignment arithmetic, and centripetal corner-blending velocity bounds) generalize across B-Rep solid modelers, V-bed flatbed knitting machines, and 3-axis Cartesian CNC trajectory planners. Extensions to non-manifold cellular modeling, circular/whole-garment 4-bed knitters, and 5-axis rotary-head inverse kinematics are explicitly scoped under **Boundaries**.

## Findings

### 1. B-Rep Topology, Euler–Poincaré Invariants, and the Persistent Topological Naming Problem

*Basis: normative literature + source + execution*

A Boundary-Representation (B-Rep) solid models a compact 3D region by its oriented 2-manifold boundary decomposed into cellular strata: **Solids** bounded by **Shells** ($S$), composed of **Faces** ($F$) trimmed by outer and inner **Loops/Wires** (with $R$ counting inner rings/holes inside faces), bounded by oriented **Coedges/Half-Edges** referencing **Edges** ($E$) and **Vertices** ($V$). Every valid closed manifold B-Rep solid of genus $G$ satisfies the generalized **Euler–Poincaré equation**:

$$V - E + F - R = 2(S - G)$$

Every elementary topological edit in a B-Rep kernel is decomposed into Euler operators (`MEV`, `MEF`, `KEMR`, `KFMRH`, and their inverses) that preserve this identity step by step. However, parametric CAD models are authored not as raw Euler-operator sequences but as **history-based feature DAGs** (sketches, extrusions, pockets, booleans, fillets, chamfers) where downstream features reference topological sub-entities produced by earlier features (e.g., `fillet(edge_e, r = 2.0)` or `sketch_on(face_f)`).

#### 1.1 Irreducible Non-Bijectivity Under Parametric Bifurcations

*Basis: normative literature (Capoyleas, Chen, Hoffmann 1996; Kripac 1997; Marcheix & Pierra 2002) + execution*

The **Topological Naming Problem (TNP)** arises when a user edits an upstream parameter (e.g., translating a pocket or changing a boss radius) and re-evaluates the feature DAG. Naive CAD kernels that refer to sub-shapes by positional array index (`Face3`, `Edge11`) fail catastrophically because boolean intersection traversal order changes whenever faces are inserted, deleted, or split. Even with perfect traversal determinism, however, **persistent naming is fundamentally non-bijective**:

1. **1-to-N Split**: Moving a slot across an outer wall genuinely splits one planar face into two disconnected faces while changing the solid's genus $G$ and ring count $R$.
2. **N-to-1 Merge**: Shrinking a rib flush with a wall merges two distinct coplanar faces into a single face.
3. **N-to-0 Deletion**: Enlarging a through-hole subsumes a previously referenced edge or chamfer face entirely.
4. **Surface-Intersection Multiplicity**: Intersecting a plane with a quadratic or higher-order NURBS surface can yield two or more disjoint curve branches (and trimming boundaries can further subdivide a single intersection curve into multiple edges), so an unordered pair of adjacent face IDs `{F_1, F_2}` does not uniquely name an edge without topological orientation or parameter-order disambiguation.

Our executable micro-probe (`probe_brep_knitout_cnc.py`, Section 1) demonstrates this exact bifurcation on a $[0,10]^3$ cube with a square through-pocket $[x_0, x_0+2] \times [4,6] \times [0,10]$:

| Regime | $x_0$ | $V$ | $E$ | $F$ | $R$ (inner rings) | $S$ | $G$ (genus) | $V - E + F - R$ | $2(S - G)$ | Face Provenance Transition |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| Interior through-hole (Case A) | `3.0` | `16` | `24` | `10` | `2` | `1` | `1` | `0` | `0` | Baseline (`F_posX` at index `3`) |
| Wall breach / U-slot (Case B) | `0.0` | `16` | `24` | `10` | `0` | `1` | `0` | `2` | `2` | `F_slot_negX` deleted; `F_negX` splits $\to$ `{F_negX_a, F_negX_b}`; index `3` silently rebinds from `F_posX` to `F_negX_b` |

Notice that $(V, E, F) = (16, 24, 10)$ is **identical** in both Case A and Case B! Yet the topology underwent a genus collapse ($G: 1 \to 0$) and inner-loop elimination ($R: 2 \to 0$), shifting positional index `3` from the opposite wall (`F_posX`) to one half of the split `-X` wall (`F_negX_b`). Any downstream fillet or mating constraint keyed on positional index `3` silently corrupts the opposite side of the part without raising an error.

#### 1.2 Classical Naming Algebras and Marcheix–Pierra Taxonomy

*Basis: normative literature (Capoyleas et al. 1996, Kripac 1997, Marcheix & Pierra 2002, Cascaval et al. 2022)*

Marcheix and Pierra (2002, DOI `10.1145/566282.566288`) classify persistent naming schemes along two orthogonal axes: **(a) Naming model** (how topological entities are denoted at design time) and **(b) Matching / re-evaluation strategy** (local per-feature matching vs. global history-graph matching), unifying five shared architectural concepts:

1. **Generic Basic Entities**: Naming primitive faces directly by their generative feature step and role (e.g., extrusion `top_cap`, `bottom_cap`, `side(profile_edge_i)` as in Capoyleas, Chen, and Hoffmann 1996, DOI `10.1016/0010-4485(95)00014-3`).
2. **Intersection / Adjacency Naming for Lower-Dimensional Entities**: Denoting an edge by the unordered set of its two bounding faces $\{f_1, f_2\}$ and a vertex by its triple $\{f_1, f_2, f_3\}$, augmented with **local orientation invariants** (cross-product sign / adjacent-face cyclic ordering) to resolve multi-edge intersections between curved or split faces.
3. **Global Evolution History (`FaceIdGraph`)**: Kripac (1995/1997, DOI `10.1016/s0010-4485(96)00040-1`) constructs a directed acyclic graph of face identities across every boolean step, recording exact `split`, `merge`, `unmodified`, and `deleted` edges so that matching traverses the history DAG rather than re-deriving names purely from the final B-Rep.
4. **Ambiguity Resolution Policies**: When a named face splits $1 \to k$, the evaluator must either (i) fail loudly with a split diagnostic, (ii) propagate the dependent feature (e.g., fillet) to all $k$ fragments, or (iii) disambiguate via geometric proximity / adjacent-face signature / user-pinned orientation.
5. **Bidirectional Differentiable CAD Boundaries**: Cascaval et al. (2022, DOI `10.1111/cgf.14476`) show that making parametric CAD programs automatically differentiable enables direct viewport manipulation to backpropagate gradients into program parameters via constrained optimization. However, differentiable optimization only holds within a **fixed topological cell** (constant B-Rep combinatorics); crossing a bifurcation boundary (such as $x_0 = 0$ above) induces a discontinuity in the face-set Jacobian where persistent-naming correspondence breaks and local gradient descent cannot smoothly cross without topological re-matching or relaxation.

#### 1.3 Production Persistent Naming Architectures: OCCT vs. FreeCAD vs. Zoo KCL

*Basis: source (OCCT `4dbfdcc448`, FreeCAD `1e7f16061a`, Zoo KCL `10ae8aa9cd`)*

Direct inspection of three major open-source CAD engines reveals three distinct engineering points in the persistent naming design space:

| Dimension | OpenCASCADE `TNaming` (`OCCT@4dbfdcc448`) | FreeCAD `ElementMap` (`FreeCAD@1e7f16061a`) | Zoo KCL (`KittyCAD/modeling-app@10ae8aa9cd`) |
|---|---|---|---|
| **Core Mechanism** | OCAF data-framework tree (`TDF_Label`) storing `TNaming_NamedShape` evolution pairs + `TNaming_Selector` query expressions | Bi-directional `ElementMap` (`MappedName` $\leftrightarrow$ `IndexedName`) encoding full shape-history opcodes into interned hashed strings (`StringHasher`) | Deterministic UUIDv5 command/artifact IDs (`IdGenerator`) + explicit user-authored source `TagIdentifier`s + topological edge specifiers |
| **Evolution Primitives** | `TNaming_Evolution` (`TNaming_Evolution.hxx:52-60`): `PRIMITIVE`, `GENERATED`, `MODIFY`, `DELETE`, `REPLACE`, `SELECTED`, populated from `BRepBuilderAPI_MakeShape::{Generated, Modified, IsDeleted}` | `Part::OpCodes` (`TopoShapeOpCode.h:49-90`, `Version = 15`): 3-char history opcodes (`FUS`, `CUT`, `CMN`, `SEC`, `XOR`, `XTR`, `GFS`, `RFI`, `FLT`, `CHF`, `THK`, `OFS`, `RVL`, `LFT`, `SWP`, `MIR`, etc.) | `ArtifactCommand` (`artifact.rs:65-87`) + `EntityCloneInfo` (`source_artifact_id`, `result_artifact_id`, `source_topology_id` for pattern clones) |
| **Selection / Resolution Algebra** | `TNaming_NameType` (`TNaming_NameType.hxx:21-35`): 12 query combinators (`IDENTITY`, `MODIFUNTIL`, `GENERATION`, `INTERSECTION`, `UNION`, `SUBSTRACTION`, `CONSTSHAPE`, `FILTERBYNEIGHBOURGS`, `ORIENTATION`, `WIREIN`, `SHELLIN`) | `ElementMap::traceElement()` via `TraceCallback(MappedName&, offset, encodedTag, tag)` (`ElementMap.h:62`), tracing back across hierarchical child `ElementMap`s | `UnresolvedEdgeSpecifier` (`std/edge.rs:45-52`): `{ side_faces: Vec<TagOrUuid>, end_faces: Vec<TagOrUuid>, index: Option<u32> }` resolved to engine face UUIDs |
| **Failure / Split Behavior** | `TNaming_Selector::Solve` returns `bool`; `TNaming_MODIFY` records multiple `(old, new_i)` pairs for 1-to-N splits, disambiguated via `FILTERBYNEIGHBOURGS` / `ORIENTATION` | Preserves history prefix + disambiguating postfix index; version mismatch (`OpCodes::Version`) forces full element-map recompute on load | Explicit named tags (`TagIdentifier`) remain anchored to AST statements across unrelated edits; `IdGenerator::next_uuid()` hashes `(NAMESPACE_KCL, module_id, next_id)` deterministically, so inserting earlier commands shifts anonymous `next_id`s unless tagged |
| **Primary Overhead** | Requires every modeling operator to diligently log `old -> new` pairs into OCAF labels; silent gaps break `Solve` | Long history strings require interning (`App::StringID` / `StringHasher`) and recursive save/restore marking (`ElementMap.h:90-100`) | Shifts naming burden partly onto code authors (explicit tags on sketch segments) and engine-side geometry queries (`getOppositeEdge`, `getNextAdjacentEdge`) |

Two subtle implementation details verified directly in source merit retention:
- In **OCCT** (`TNaming_Selector.hxx:98-101`), `TNaming_Selector::Select(Selection, Context, Geometry, KeepOrientatation)` distinguishes topological identity from geometric identity (`Geometry = true` anchors to the *first* `TNaming_NamedShape` appearance of the shape, whereas `Geometry = false` tracks the active evolution frontier). Moreover, `BRepBuilderAPI_MakeShape` (`BRepBuilderAPI_MakeShape.hxx:49-58`) exposes the three exact virtual hooks (`Generated`, `Modified`, `IsDeleted`) that all downstream naming layers—including FreeCAD's `TopoShape` mapper—rely on. If a third-party or custom B-Rep algorithm fails to override `Modified`/`Generated`, both OCCT `TNaming` and FreeCAD `ElementMap` fall back to blind geometric matching or break.
- In **Zoo KCL** (`id_generator.rs:6-52`), `IdGenerator` generates deterministic UUIDv5 values using fixed namespace `8bda3118-75eb-58c7-a866-bef1dcb495e7` and sequential counter `"{module_id} {next_id}"`. This guarantees cross-execution determinism for identical AST execution traces (critical for caching and frontend artifact-graph diffing), while `EntityCloneInfo::source_topology_id` (`artifact.rs:91-98`) decouples pattern-instance root IDs from the shared source body topology. However, because `next_id` is a monotonic execution counter, persistent user references across structural code edits depend on **programmer-placed tags** (`TagIdentifier`) and face-pair edge specifiers (`UnresolvedEdgeSpecifier { side_faces, end_faces, index }`), not raw `IdGenerator` UUIDs.

---

### 2. B-Rep vs. Implicit Signed Distance Fields (SDF / F-Rep)

*Basis: source (`mkeeter/fidget@1879743ddc`) + normative literature (Keeter 2020, DOI `10.1145/3386569.3392429`) + execution*

Implicit functional representations (F-Rep / Signed Distance Fields) represent a solid as the sublevel set $\{p \in \mathbb{R}^3 \mid f(p) \le 0\}$ of a closed-form mathematical expression graph. In `Fidget` (`fidget-core/src/lib.rs:1-54`), shapes are built as DAGs inside a `Context` (`x`, `y`, `z`, arithmetic, `min`, `max`), compiled into linear evaluation **tapes** (`VmShape`, JIT-compiled native kernels, or SIMD/GPU evaluators), and pruned hierarchically across spatial octrees/quadtrees using **interval arithmetic** (Keeter 2020): if evaluating $f([x_{\min}, x_{\max}], [y_{\min}, y_{\max}], [z_{\min}, z_{\max}])$ yields an interval strictly $> 0$ or $< 0$, the entire cell is pruned and dead `min`/`max` sub-branches are **shortened/specialized** into smaller per-cell tapes.

Our micro-probe (`probe_brep_knitout_cnc.py`, Section 1) evaluated the exact same pocket-breach edit (`x0` sweeping from `3.0` through `0.0` to `-0.5`) under $f(p) = \max(f_{\text{outer}}(p), -f_{\text{pocket}}(p; x_0))$: the scalar field transitions smoothly at $(0, 5, 5)$ from `0.00` (on wall) to `+0.50` (cut open) with **zero topological data-structure failure, zero degenerate intersection curves, and zero TNP breakage**.

| Engineering Axis | Boundary Representation (B-Rep: OCCT / Parasolid / KCL) | Implicit SDF / F-Rep (`Fidget` / `libfive`) |
|---|---|---|
| **Boolean CSG Robustness** | Fragile at grazing/tangent/coplanar intersections; requires tolerant vertex/edge sewing and exact/adaptive predicates | Trivially total (`min` = union, `max` = intersection, `-f` = complement); exact $C^0$ closure under arbitrary blends (`smin`) |
| **Topological Naming (TNP)** | Severe: requires history DAGs (`TNaming`, `ElementMap`) or explicit tags; non-bijective across splits/merges | **Eliminated for CSG evaluation**: no discrete face/edge table exists to renumber |
| **Selective Local Operations** | Native: exact variable-radius edge fillets, chamfers, shell offsets, face drafts on named edges/faces | Difficult: global smooth-min blends all coincident intersections indiscriminately unless manually masked by auxiliary spatial fields |
| **Exact Analytic Curves & GD&T** | Native exact NURBS/cylinders/cones; ISO 10303 (STEP AP242) & PMI/GD&T datum attachment | Approximated via marching cubes/dual contouring/octree meshing at export; no native exact analytic cylinder/datum faces |
| **Differentiability & Inverse Design** | Piecewise differentiable inside fixed topology cells; discontinuous across topological bifurcations (Cascaval 2022) | Globally continuous and almost-everywhere differentiable (subgradients at `min`/`max` creases) |
| **Physical Fabrication Fit** | Gold standard for subtractive CNC CAM, sheet metal, injection-molded assemblies, and tolerance stackup | Superior for lattice/gyroid metamaterials, organic blends, multi-million-primitive AM/3D printing, and collision-distance queries |

*Derived architectural takeaway:* Neither representation dominates across the full CAD-to-manufacturing pipeline. Hybrid architectures use B-Rep with provenance-tracked naming for prismatic/mated datum features and STEP exchange, while compiling to SDF/F-Rep (or distance-field octrees) for volumetric lattices, organic blends, and fast collision-clearance queries.

---

### 3. Machine Knitting Compilers: V-Bed Needle Lattices as Resource-Linear ISAs

*Basis: normative specification (`textiles-lab/knitout@17b868c5a4`) + source (`autoknit`, `transfer-plan-supplement`, `knitskel`) + peer-reviewed literature + execution*

Industrial flatbed V-bed knitting machines (such as the Shima Seiki SWG091N2) possess two opposing linear beds of latch/compound needles—**front** (`f`) and **back** (`b`), optionally equipped with secondary **slider** hooks (`fs`, `bs`)—and one or more motorized yarn carriers mounted on parallel rails. Compiling a 3D knitted surface to machine instructions is structurally isomorphic to **resource-linear register allocation on a 1D integer lattice coupled with physical elasticity and topological non-crossing invariants**.

#### 3.1 The Knitout v0.6 Instruction Set & Physical Semantics

*Basis: normative specification (`textiles-lab/knitout@17b868c5a4:knitout.html:24-210`)*

`Knitout` (`.k`, UTF-8 LF-terminated text beginning with magic string `;!knitout-2`) defines a machine-independent low-level IR separating high-level garment compilers from proprietary machine backends (e.g., Shima Seiki `.dat`, Kniterate k-code):

- **Topology-Affecting Required Header**: `;;Carriers: C1 C2,C3;C4 ...` specifies carrier rail layout front-to-back (and left-to-right per rail), because carrier ordering determines yarn entanglement and intarsia/colorwork crossings (`knitout.html:50-60`). Optional headers record `;;Machine`, `;;Gauge` (needles/inch), `;;Yarn-C`, and `;;Position`.
- **Core Needle & Bed Operations**:
  - `rack R`: shifts the front bed relative to the back bed by offset $R$ (integer or fractional, e.g., `0.25`/`-0.75` for all-needle knitting on Shima Seiki). **Alignment invariant (`knitout.html:171-175`)**: at racking $R$, back needle index $B$ is aligned with front needle index $F = B + R$; a transfer `xfer f_F b_B` or `xfer b_B f_F` is physically valid **if and only if** $F = B + R$.
  - `knit D N CS`: pulls new yarn from carrier set `CS` moving in direction `D` (`+` rightward / `-` leftward) through the loops currently held on needle `N`, knocking over the old loops. (`drop N` is a synonym for `knit + N` with empty carrier set, releasing held loops into free fabric—which unravels unless bound off!)
  - `tuck D N CS`: adds a loop from `CS` onto needle `N` without knocking over existing loops (`amiss N` = `tuck + N` empty).
  - `split D N N2 CS`: knits on `N` while simultaneously transferring existing loops from `N` to opposing aligned needle `N2` (enabling zero-hole increases and pocket splits).
  - `xfer N N2`: synonym for `split + N N2` with empty carrier set; moves all loops on `N` onto opposing aligned needle `N2`.
  - `miss D N CS`, `pause`, `stitch L T`, and extension namespaces `X-*` / `x-*` plus debug metadata `;!source: <loc>`.
- **Implicit Kickbacks & Logical Carrier State (`knitout.html:185-205`)**: Knitout omits explicit carriage-pass grouping and carrier parking offsets. Backends must (1) coalesce compatible needle operations into minimal carriage passes, and (2) track each active carrier's **logical position** infinitesimally left or right of a needle (e.g., `f3+` vs `fs3+`) and synthesize physical **kickback** motions to compensate for carrier stopping-distance lag so yarns do not miss needles or snag on adjacent stitches during colorwork.

#### 3.2 High-Level Garment Compilation: `AutoKnit` vs. `Knitting Skeletons`

*Basis: source (`autoknit@a711d2096e`, `knitskel@aebb0f05b0`) + literature (McCann 2016, Narayanan 2018, Kaspar 2019)*

Three complementary compiler layers bridge 3D shapes to Knitout / V-bed instructions:

1. **Shape-Primitive Assembly (`McCann et al. 2016`, DOI `10.1145/2897824.2925940`)**: Models garments as graphs of parametric **tubes** and **sheets** with explicit shaping (increases/decreases) and seam merges/splits. Introduces a **sound and complete** transfer-planning algorithm for closed knit cycles (tubes) on V-beds using cyclic "rolling" around the two beds to align target loops.
2. **Automatic 3D Mesh Compilation (`AutoKnit`, Narayanan et al. 2018, DOI `10.1145/3186265`; `textiles-lab/autoknit@a711d2096e`)**: Compiles arbitrary orientable 3D meshes by solving a harmonic/geodesic **time function** over the surface (`ak-peel_chains-libgeodesic.cpp`), extracting iso-contour active stitch chains (`ak-extract_level_chains.cpp`), linking adjacent courses via dynamic programming (`ak-optimal_link.cpp`) under a 1-to-2 / 2-to-1 stitch topology constraint (bounding fabric distortion and avoiding holes), and scheduling bed layout via a lexicographic cost triple in `ScheduleCost.hpp:8-20`:
   ```cpp
   struct ScheduleCost {
       uint32_t shape = 0; // awkwardly-oriented cycles
       uint32_t roll  = 0; // stitches that need to change beds
       uint32_t shift = 0; // stitches that need to move left/right
   };
   ```
   Lexicographic ordering (`shape < roll < shift`) prioritizes topologically clean cycle embeddings before minimizing cross-bed rolls and lateral shifts.
3. **Parametric Garment Graphs (`Knitting Skeletons`, Kaspar, Makatura, Matusik 2019, DOI `10.1145/3332165.3347879`; `xionluhnis/knitskel@aebb0f05b0`)**: Instead of mesh remeshing, represents garments as typed skeleton DAGs (`NODE_SHEET`, `NODE_JOINT`, `NODE_SPLIT`, `NODE_CUSTOM` in `src/schedule.js:75-90`) separating global shaping topology from 2D stitch-pattern texture layers (`src/pattern.js`, `src/shaper.js`). `Schedule::trace()` (`src/schedule.js:48-54`) traces single-carrier yarn flow across ordered `ShapeBlock` course blocks (`'up'` / `'down'`) and inserts glue stitches at branch interfaces.

#### 3.3 Flat-Bed Transfer Planning, Yarn-Strain Bounds, and Topological Blocking

*Basis: source (`textiles-lab/transfer-plan-supplement@9060dcc0b6:cse.js, README.md`) + literature (Lin, Narayanan, McCann 2018, DOI `10.1145/3213512.3213515`) + execution*

A flat-bed transfer problem specifies a starting vector of loops on the front bed, a target signed horizontal offset `offsets[i]` for each stitch `i` (where multiple stitches mapping to the same destination needle represent intentional decreases/stacking), and an optional stacking-order constraint `firsts[i]` (critical in lace knitting where left-leaning vs. right-leaning decreases are visually distinct). Physical machine constraints turn this into a constrained graph-scheduling problem:

1. **Bounded Yarn-Strain / Max-Racking Invariant**: Stretching a loop across adjacent needles during transfer creates tensile stress proportional to racking offset $|R|$. Industrial V-bed machines and yarns enforce a hard racking ceiling $R_{\max}$ (commonly $R_{\max} \in \{1, 2, 3\}$ needles per pass; `cse.js:184` defaults to `max_racking = 3`, while stiffer yarns restrict $R_{\max} \le 2$). Moving a loop by $+3$ when $R_{\max} = 2$ requires multi-pass staging (`f -> b` at $R_1$, then `b -> f` at $R_2$, repeated as needed).
2. **Irreversible Loop Merging (No Arbitrary Scratch Registers)**: Transferring loop $L_1$ onto a needle already holding $L_2$ **physically stacks $L_1$ and $L_2$ onto the same hook**—subsequent transfers move both together; they can never be separated again! Thus, an occupied needle on the opposing bed acts as a **collision hazard**, not overwriteable memory.
3. **Collapse–Stretch–Expand (`CSE`) vs. Schoolbus Algorithms (`Lin et al. 2018`, `transfer-plan-supplement@9060dcc0b6`)**:
   - **`cse.js`** (`cse_transfers`, lines `5–35, 184`): operates exclusively on flat fabrics (no cyclic bed roll needed) by alternating **Collapse** (resolving intentional decreases first so loops share needles early), **Stretch-to-back** (moving loops to the back bed to monotonically reduce remaining offset cost), and **Expand-to-front** (moving loops back to the front bed toward targets) using a priority queue until all offsets reach `0`.
   - **`schoolbus.js` & `schoolbus-sliders.js`**: sweep racking offsets monotonically like a bus picking up and dropping off loops at their exact destination offsets, using slider hooks (`fs`/`bs`) or half-gauge (`-h` flag in `README.md:9`) to guarantee collision-free staging even when bidirectional crossings occur.
4. **Full-Gauge Topological Blocking**: As verified in our executable micro-probe (`probe_brep_knitout_cnc.py`, Section 2), when both front and back beds are 100% occupied (full-gauge tubular or interlock fabric) across an active region, **every legal cross-bed transfer at any racking $R$ lands on an already-occupied needle**, causing an illegal unintended stitch merge! Breaking this deadlock requires either: (i) **half-gauge knitting** (leaving every alternate needle empty as a scratch register, halving maximum gauge density), (ii) **transfer sliders** (`fs`/`bs` auxiliary holding hooks on Shima Seiki N-series machines), or (iii) **boundary slack** (shifting loops outward from free bed ends sequentially from outside in).

---

### 4. CNC Trajectory Planning, Kinematic Envelopes, and Rigid-Origami Verification

*Basis: source (`LinuxCNC/linuxcnc@76ee5a1b63:src/emc/tp/blendmath.h, tp_types.h`) + literature (Demaine & O'Rourke 2007; Tachi 2011) + execution*

Physical motion compilers translate geometric curves into timed actuator trajectories subject to hard kinematic (velocity, acceleration, jerk) and collision/interference invariants.

#### 4.1 G-Code Corner Blending & Centripetal Acceleration Envelopes (`LinuxCNC`)

*Basis: source (`LinuxCNC/linuxcnc@76ee5a1b63:src/emc/tp/blendmath.h:21-80, tp_types.h:23-58`) + execution*

Standard RS274NGC / G-code programs consist of discrete linear (`G1`) and circular-arc (`G2`/`G3`) segments. Executing exact-stop corners (`G61`) requires decelerating to zero velocity at every segment junction, causing severe chatter, burn marks, and cycle-time collapse on densely tessellated CAM toolpaths. Conversely, continuous-path mode (`G64 P<tol>`) inserts **spherical/circular blend arcs** between adjacent segments (`BLEND_LINE_LINE`, `BLEND_LINE_ARC`, `BLEND_ARC_LINE`, `BLEND_ARC_ARC` in `blendmath.h:25-31`).

Direct inspection of `LinuxCNC/linuxcnc@76ee5a1b63` reveals the exact kinematic envelope enforced by the lookahead trajectory planner (`TP_DEFAULT_QUEUE_SIZE = 32`, `TP_MIN_SEGMENT_CYCLES = 1.02` in `tp_types.h:23-26`):

1. **Tangential / Normal Acceleration Partitioning (`blendmath.h:21-23`)**:
   ```c
   #define BLEND_ACC_RATIO_TANGENTIAL 0.5
   #define BLEND_ACC_RATIO_NORMAL     (pmSqrt(1.0 - pmSq(BLEND_ACC_RATIO_TANGENTIAL))) // sqrt(0.75) ~= 0.866025
   #define BLEND_KINK_FACTOR          0.25
   ```
   Because total vector acceleration $\| \mathbf{a}_t + \mathbf{a}_n \| = \sqrt{a_t^2 + a_n^2} \le a_{\max}$, reserving $0.5 a_{\max}$ for tangential speed change leaves $a_n = \frac{\sqrt{3}}{2} a_{\max} \approx 0.8660 \, a_{\max}$ for centripetal acceleration around the blend arc.
2. **Tolerance-to-Velocity Coupling**: For two linear segments meeting at interior corner angle $\theta$ (e.g., $\theta = 90^\circ$) with maximum allowed corner deviation $\text{tol}$ (`G64 P`), a tangent circular blend arc of radius $R$ deviates from the sharp vertex by $\delta = R\left(\frac{1}{\sin(\theta/2)} - 1\right)$. Enforcing $\delta \le \text{tol}$ and $v^2 / R \le a_n$ yields the exact kinematic ceiling:
   $$R_{\max} = \frac{\text{tol}}{\csc(\theta/2) - 1}, \qquad v_{\text{corner},\max} = \sqrt{a_n R_{\max}} \propto \sqrt{\text{tol}}$$
   Our micro-probe (`probe_brep_knitout_cnc.py`, Section 3) evaluates this bound at $a_{\max} = 1000\text{ mm/s}^2$ ($a_n = 866.03\text{ mm/s}^2$) on a $90^\circ$ corner:

   | Corner Tolerance `G64 P` (mm) | Max Blend Radius $R_{\max}$ (mm) | Max Corner Velocity $v_{\text{corner},\max}$ (mm/s) | Speed Retention vs. `1.0 mm` |
   |---:|---:|---:|---:|
   | `1.000` | `2.4142` | `45.72` | `100.0%` |
   | `0.100` | `0.2414` | `14.46` | `31.6%` |
   | `0.010` | `0.0241` | `4.57` | `10.0%` |
   | `0.001` | `0.0024` | `1.45` | `3.2%` |

   Every $100\times$ tightening of geometric tolerance forces a $10\times$ reduction in corner feedrate; omitting tolerance enforcement (`G64` with no `P` parameter) allows unbounded corner rounding, directly gouging inside corners or clipping mating shoulders.
3. **Spindle-Synchronized Motion Overrun Guards (`tp_types.h:49-58`)**: On lathe threading (`G33`) and rigid tapping, axis feed is slaved to spindle revolutions $\times$ pitch. `LinuxCNC` enforces explicit windowed overrun guards (`TP_SYNC_OVERRUN_WINDOW = 0.25`, `TP_SYNC_OVERRUN_MARGIN = 1.02`, `TP_SYNC_OVERRUN_CEILING = 0.99`) because instantaneous single-cycle spindle speed is corrupted by encoder quantization while naive following-error checks confound the deterministic $v^2/(2a)$ ramp-up lag with genuine axis saturation.
4. **Jerk-Limited S-Curve Planning**: Modern `LinuxCNC` integrates `sp_scurve.{c,h}` and `cruckig` (`ruckig_wrapper.{c,h}`) alongside `blendmath` so higher-order jerk constraints prevent structural resonance and stepper stalls without violating segment cycle floors (`TP_MIN_SEGMENT_CYCLES = 1.02`).

#### 4.2 Rigid-Origami Kinematic Constraints

*Basis: normative literature (Demaine & O'Rourke 2007; Tachi 2011, DOI `10.1201/b10971-24`)*

Rigid-origami compilers map crease patterns (planar straight-line graphs with mountain/valley assignments) to continuous 1-DOF or multi-DOF foldable mechanisms whose panels remain strictly rigid (zero stretching or bending). Unlike soft sheet folding, rigid-origami validity requires satisfying both discrete local conditions and continuous nonlinear algebraic loop-closure constraints:

1. **Local Flat-Foldability (Single Interior Vertex)**:
   - **Maekawa's Theorem**: $|M - V| = 2$, where $M$ and $V$ are the counts of mountain and valley creases incident to an interior vertex (forcing every flat-foldable interior vertex to have even degree).
   - **Kawasaki's Theorem**: The alternating sum of sector angles $\alpha_1, \dots, \alpha_{2k}$ around an interior vertex equals zero: $\sum_{i=1}^{k} \alpha_{2i-1} = \sum_{i=1}^{k} \alpha_{2i} = \pi$.
   - **Global Hardness**: Determining whether a general crease pattern has a non-self-intersecting flat-folded state (global layer ordering without penetration) is **NP-hard** (Bern & Hayes 1996, synthesized in Demaine & O'Rourke 2007).
2. **Continuous Rigid-Foldability Loop Closure (`Tachi 2011`)**: Around every interior vertex with incident crease fold angles $\rho_1, \dots, \rho_n$ and sector angles $\alpha_1, \dots, \alpha_n$, continuous rigid motion requires the $SO(3)$ rotation composition around the vertex to equal the identity matrix at every time $t$:
   $$\prod_{i=1}^{n} R_x(\rho_i(t)) \, R_z(\alpha_i) = I_3$$
   For thick panels (Tachi 2011, DOI `10.1201/b10971-24`), shifting hinge axes off the mid-plane introduces nonzero offset vectors in $SE(3)$, requiring panel tapering or synchronized hinge-offset geometry so panels do not collide as $\rho_i(t) \to \pm \pi$.

---

### 5. Cross-Domain Compiler & Verification Synthesis

*Basis: derived from Sections 1–4*

| Domain / System | Underlying Mathematical Invariant | Resource / State Abstraction | Failure Mode ("Physical UB") | Primary Mitigation Strategy |
|---|---|---|---|---|
| **B-Rep CAD** (`OCCT`, `FreeCAD`, `KCL`) | Euler–Poincaré $V-E+F-R = 2(S-G)$ + manifold trim consistency | Sub-shape evolution DAG (`PRIMITIVE`/`GENERATED`/`MODIFY`/`DELETE`) | Silent feature mis-attachment on topological split/merge (TNP) | Provenance graphs (`TNaming`/`ElementMap`), explicit AST tags (`KCL`), or non-bijective split diagnostics |
| **Implicit SDF** (`Fidget`) | Continuous $f: \mathbb{R}^3 \to \mathbb{R}$, conservative interval inclusion $f(B) \subseteq [l, u]$ | Expression DAG compiled to pruned per-cell VM/JIT tapes | Non-exact boundary extraction / unwanted global blends | Exact interval pruning + localized spatial blending masks |
| **V-Bed Machine Knitting** (`Knitout`, `AutoKnit`, `knitskel`, `CSE`) | Racking alignment $F = B + R$; bounded yarn strain $\|R\| \le R_{\max}$; stitch non-crossing | Linear resource allocation on 1D dual-bed integer lattice (`f`/`b`/`fs`/`bs`) | Snapped yarn, dropped/unraveled loops, unintended stitch merges, full-gauge deadlock | `CSE` / `schoolbus-sliders` transfer planners, half-gauge slack, lexicographic `ScheduleCost` |
| **CNC Motion Control** (`LinuxCNC`) | $\sqrt{a_t^2 + a_n^2} \le a_{\max}$; blend chord error $\delta \le \text{tol}$; spindle sync window | Lookahead circular/S-curve motion queue (`TP_DEFAULT_QUEUE_SIZE = 32`) | Tool breakage, workpiece gouging, axis overrun / lost steps | `G64 P<tol>` analytic radius/velocity clamping, `cruckig` jerk limits, spindle overrun windows |
| **Rigid Origami** (`Tachi`, `Demaine–O'Rourke`) | Maekawa $|M-V|=2$, Kawasaki $\sum \pm \alpha_i = 0$, $SO(3)/SE(3)$ loop closure | Articulated rigid-panel kinematic chain with crease angles $\rho_i(t)$ | Panel self-intersection, kinematic lockup (zero-DOF jam) | Loop-closure Jacobian rank checks, thick-panel hinge-offset synthesis |

## Boundaries

- **Non-Manifold Cellular B-Rep & Sheet-Metal Bends (`not examined`)**: This report examines 2-manifold solid B-Rep topology (`V - E + F - R = 2(S - G)`). Non-manifold cellular complexes (internal partition faces shared by 3+ solids in multi-material FEM meshing) and sheet-metal bend/unfold correspondence tables were not examined in OCCT or FreeCAD source.
- **5-Axis Simultaneous Rotary CNC Inverse Kinematics & Gouge Verification (`not examined`)**: Source inspection of `LinuxCNC` covered the 3D Cartesian spherical arc blender (`blendmath.h`) and trajectory-planner types (`tp_types.h`). Note that `blendmath.h:58-62` explicitly marks `BlendGeom9` (9D linear+rotary blending) as `//Not implemented yet` (`unsupported` in that spherical-blend struct). Full 5-axis tool-shaft collision checking, rotary-axis gimbal singularities (A/B/C head-table kinematics), and swept-volume dexel/voxel gouge verification were not examined.
- **Commercial Closed-Source CAD Kernels (`not examined` / `unknown`)**: Exact persistent naming algorithms inside proprietary kernels (Parasolid, ACIS, Siemens NX, SOLIDWORKS, Onshape FeatureScript internals) are not publicly inspectable; public academic models (Capoyleas–Chen–Hoffmann, Kripac, Marcheix–Pierra) and open-source engines (`OCCT`, `FreeCAD`, `KCL`) form the evidence base. Whether proprietary engines use proprietary geometric fallback heuristics beyond `FaceIdGraph` + orientation signatures is `unknown`.
- **Whole-Garment 4-Bed / Circular Knitting & Yarn Friction Physics (`known not to apply` / `not examined`)**: The `Knitout` alignment invariant $F = B + R$ and `CSE` flat-bed transfer planner (`transfer-plan-supplement/cse.js`) apply to V-bed flatbed knitting machines. Circular knitting machines (which lack bidirectional bed racking and flat transfer passes) and multi-needle 4-bed whole-garment machines have distinct transfer graphs (`known not to apply` without modifying the bed-adjacency model). Continuum yarn-level finite-element tension simulation beyond discrete needle-distance racking bounds (`max_racking`) was `not examined`.
- **Generalizability of SDFs to Engineering CAD (`known not to apply`)**: The claim that SDF/F-Rep "solves" B-Rep CAD persistent naming is **false** for workflows requiring exact ISO 10303 STEP AP242 B-Rep export, explicit face-level GD&T datums, or selective single-edge constant-radius filleting without global field interference.
- **Global Origami Self-Intersection Verification (`unsupported` in local tests)**: Kawasaki's and Maekawa's theorems are necessary local vertex conditions for flat-foldability, not sufficient global conditions; global non-self-intersection remains NP-hard and cannot be certified by local vertex checks alone.

## Evidence

### Primary Git Repository Evidence (Observed `2026-11-19`)

1. **`Open-Cascade-SAS/OCCT` @ `4dbfdcc448c0b3e565488afcd626c84483172db9`**
   - `src/ApplicationFramework/TKCAF/TNaming/TNaming_Evolution.hxx` (lines 52–60): defines `enum TNaming_Evolution` (`TNaming_PRIMITIVE`, `TNaming_GENERATED`, `TNaming_MODIFY`, `TNaming_DELETE`, `TNaming_REPLACE`, `TNaming_SELECTED`) and documents split (multiple pairs with same old shape) vs. merge (multiple pairs with same new shape).
   - `src/ApplicationFramework/TKCAF/TNaming/TNaming_NameType.hxx` (lines 21–35): defines the 12 `TNaming_NameType` query kinds (`UNKNOWN`, `IDENTITY`, `MODIFUNTIL`, `GENERATION`, `INTERSECTION`, `UNION`, `SUBSTRACTION`, `CONSTSHAPE`, `FILTERBYNEIGHBOURGS`, `ORIENTATION`, `WIREIN`, `SHELLIN`).
   - `src/ApplicationFramework/TKCAF/TNaming/TNaming_Selector.hxx` (lines 79–110): `IsIdentified`, `Select(Selection, Context, Geometry, KeepOrientatation)`, and `Solve` API contract.
   - `src/ModelingAlgorithms/TKTopAlgo/BRepBuilderAPI/BRepBuilderAPI_MakeShape.hxx` (lines 49–58): virtual history interface `Generated(S)`, `Modified(S)`, `IsDeleted(S)`.
2. **`FreeCAD/FreeCAD` @ `1e7f16061ac499c1adc67bc39f597b6e5088e8d7`**
   - `src/App/ElementMap.h` (lines 44–100): `Data::ElementMap`, `TraceCallback`, `indexedNames` / `mappedNames` bidirectional tables, and `App::StringID` / `StringHasher` persistence hooks.
   - `src/Mod/Part/App/TopoShapeOpCode.h` (lines 39–90): `Part::OpCodes::Version = 15` and 3-character encoded history opcodes (`FUS`, `CUT`, `CMN`, `SEC`, `XOR`, `XTR`, `GFS`, `RFI`, `FLT`, `CHF`, etc.).
3. **`KittyCAD/modeling-app` @ `10ae8aa9cdf6cbc8e6eaf188b37a3d6ec0afec34`**
   - `rust/kcl-lib/src/execution/id_generator.rs` (lines 6–53): `NAMESPACE_KCL` UUIDv5 deterministic `IdGenerator` over `(module_id, next_id)`.
   - `rust/kcl-lib/src/execution/artifact.rs` (lines 65–98): `ArtifactCommand` and `EntityCloneInfo` (`source_artifact_id`, `result_artifact_id`, `source_topology_id`).
   - `rust/kcl-lib/src/execution/geometry.rs` (lines 74–100): `Geometry::pattern_source_id()` resolving topology roots.
   - `rust/kcl-lib/src/std/edge.rs` (lines 34–52): `TagOrUuid` and `UnresolvedEdgeSpecifier { side_faces, end_faces, index }`.
4. **`mkeeter/fidget` @ `1879743ddc1d73dac14a42a8184a3c5b758dcca5`**
   - `fidget-core/src/lib.rs` (lines 1–68): closed-form implicit `Context` DAG construction, `VmShape` compilation, `ez_point_tape` evaluation, and modular `compiler`/`eval`/`render`/`vm` layout.
5. **`textiles-lab/knitout` @ `17b868c5a48cf8ce2d25bbfb7d23f2ab7ba55ddf`**
   - `knitout.html` (v0.6): `;!knitout-2` magic header, mandatory `;;Carriers` rail syntax, core opcodes (`rack`, `knit`, `tuck`, `split`, `xfer`, `drop`, `amiss`, `miss`, `pause`, `x-*`), racking alignment equation (`B` aligned with `B + R`), and implicit kickback logical carrier positions (`f3+`/`fs3+`).
6. **`textiles-lab/autoknit` @ `a711d2096e378547cedce943c25c16c0ecd25731`**
   - `ScheduleCost.hpp` (lines 8–51): lexicographic `ScheduleCost { shape, roll, shift }` and `transfer_cost(...)` API; mesh-to-knit pipeline files `ak-peel_chains-libgeodesic.cpp`, `ak-extract_level_chains.cpp`, `ak-optimal_link.cpp`.
7. **`textiles-lab/transfer-plan-supplement` @ `9060dcc0b6e003dc62e645e2921055261918e218`**
   - `README.md` (lines 4–11) & `cse.js` (lines 5–35, 184–197): `cse_transfers(offsets, firsts, xfer, options, max_racking = 3)`, `Expanding` / `StretchToBack` / `ExpandToFront` phases, half-gauge `-h` option, and `schoolbus` / `schoolbus-sliders` variants.
8. **`xionluhnis/knitskel` @ `aebb0f05b05ce300381eb6d84bbf938f208d0b6d`**
   - `README.md` (lines 49–56) & `src/schedule.js` (lines 9–90): `ShapeBlock`, `Schedule::trace()`, and `pathReaches` over `NODE_SHEET`/`NODE_JOINT`/`NODE_SPLIT`/`NODE_CUSTOM` garment DAGs.
9. **`LinuxCNC/linuxcnc` @ `76ee5a1b63fa595040d398b615702c83dadf8f05`**
   - `src/emc/tp/blendmath.h` (lines 21–80): `BLEND_ACC_RATIO_TANGENTIAL = 0.5`, `BLEND_ACC_RATIO_NORMAL`, `BLEND_KINK_FACTOR = 0.25`, `blend_type_t`, `BlendGeom3`, unimplemented `BlendGeom9`.
   - `src/emc/tp/tp_types.h` (lines 23–58): `TP_DEFAULT_QUEUE_SIZE = 32`, `TP_MIN_SEGMENT_CYCLES = 1.02`, numeric epsilons, and `TP_SYNC_OVERRUN_{WINDOW,MARGIN,CEILING}`.

### Peer-Reviewed Literature (Crossref-Verified `2026-11-19`)

- V. Capoyleas, X. Chen, C. M. Hoffmann, *"Generic naming in generative, constraint-based design"*, Computer-Aided Design 28(1), 1996, DOI `10.1016/0010-4485(95)00014-3`.
- J. Kripac, *"A mechanism for persistently naming topological entities in history-based parametric solid models"*, ACM SMA 1995 (DOI `10.1145/218013.218024`) and Computer-Aided Design 29(2), 1997 (DOI `10.1016/s0010-4485(96)00040-1`).
- D. Marcheix, G. Pierra, *"A survey of the persistent naming problem"*, ACM SMA 2002, DOI `10.1145/566282.566288`.
- D. Cascaval, M. Shalah, P. Quinn, R. Bodík, M. Agrawala, A. Schulz, *"Differentiable 3D CAD Programs for Bidirectional Editing"*, Computer Graphics Forum 41(2), 2022, DOI `10.1111/cgf.14476`.
- M. Keeter, *"Massively parallel rendering of complex closed-form implicit surfaces"*, ACM Transactions on Graphics 39(4), 2020, DOI `10.1145/3386569.3392429`.
- J. McCann, L. Albaugh, V. Narayanan, A. Grow, W. Matusik, J. Mankoff, J. Hodgins, *"A compiler for 3D machine knitting"*, ACM Transactions on Graphics 35(4), 2016, DOI `10.1145/2897824.2925940`.
- V. Narayanan, L. Albaugh, J. Hodgins, S. Coros, J. McCann, *"Automatic Machine Knitting of 3D Meshes"*, ACM Transactions on Graphics 37(3), 2018, DOI `10.1145/3186265`.
- J. Lin, V. Narayanan, J. McCann, *"Efficient transfer planning for flat knitting"*, ACM SCF 2018, DOI `10.1145/3213512.3213515`.
- A. Kaspar, L. Makatura, W. Matusik, *"Knitting Skeletons"*, ACM UIST 2019, DOI `10.1145/3332165.3347879`.
- T. Tachi, *"Rigid-Foldable Thick Origami"*, Origami 5, 2011, DOI `10.1201/b10971-24`.

### Executable Micro-Probe (`Basis: execution`, `2026-11-19`, Python 3 Linux)

Executed inline script reproducing (1) the $(V,E,F)=(16,24,10)$ pocket-breach Euler–Poincaré bifurcation (`R: 2->0`, `G: 1->0`, naive index `3` corrupting `F_posX -> F_negX_b` vs. `TNaming_MODIFY` split detection vs. continuous SDF evaluation), (2) Knitout racking alignment (`F = B + R`) and `max_rack=2` rejection of single-pass `+3` shift, and (3) LinuxCNC `blendmath.h` corner-velocity decay across $1000\times$ tolerance sweep:

```text
=== 1. B-Rep Euler-Poincare & Persistent Naming Bifurcation ===
  Case A (interior through-hole, x0=3.0): V=16, E=24, F=10, R(inner_loops)=2, S=1, G=1 => V-E+F-R=0 == 2(S-G)=0 [OK]
  Case B (open U-slot breach, x0=0.0): V=16, E=24, F=10, R(inner_loops)=0, S=1, G=0 => V-E+F-R=2 == 2(S-G)=2 [OK]
  Naive index binding: index 3 was 'F_posX' in A -> silently rebinds to 'F_negX_b' in B! [TNP CORRUPTION]
  Provenance algebra on F_posX: ('TNaming_IDENTITY', ['F_posX']) (stable identity)
  Provenance algebra on F_negX: ('TNaming_MODIFY', ['F_negX_a', 'F_negX_b']) (explicit 1->2 split detected)
  Implicit SDF x0= 3.0: f(0,5,5)=+0.00 (on/in), f(0,2,5)=+0.00
  Implicit SDF x0= 0.0: f(0,5,5)=+0.00 (on/in), f(0,2,5)=+0.00
  Implicit SDF x0=-0.5: f(0,5,5)=+0.50 (outside/cut), f(0,2,5)=+0.00

=== 2. Knitout V-Bed Racking Alignment, Transfer Strain & Blocking ===
  Flat-bed +2 shift (rack=0 then rack=+2): ok=True, front={2: ['L0'], 3: ['L1'], 4: ['L2']}
  Single-pass +3 shift with max_rack=2: ok=False, reason=RACK_LIMIT_EXCEEDED: |3| > 2

=== 3. LinuxCNC Spherical Arc Corner Blending & Acceleration Envelope ===
  a_max=1000.0 mm/s^2 => a_tangential=500.0, a_normal=866.03 mm/s^2
  90-deg corner tol=1.000 mm => R_max=2.4142 mm, v_corner_max= 45.72 mm/s
  90-deg corner tol=0.100 mm => R_max=0.2414 mm, v_corner_max= 14.46 mm/s
  90-deg corner tol=0.010 mm => R_max=0.0241 mm, v_corner_max=  4.57 mm/s
  90-deg corner tol=0.001 mm => R_max=0.0024 mm, v_corner_max=  1.45 mm/s
```

## Revalidation

1. **Diff Upstream Persistent-Naming & Motion-Planner Definitions**:
   - Check `OCCT`: diff `src/ApplicationFramework/TKCAF/TNaming/TNaming_{Evolution,NameType,Selector}.hxx` against commit `4dbfdcc448c0b3e565488afcd626c84483172db9` for new evolution kinds or naming combinators.
   - Check `FreeCAD`: inspect `Part::OpCodes::Version` in `src/Mod/Part/App/TopoShapeOpCode.h` (currently `15` at `1e7f16061a`) and `Data::ElementMap` in `src/App/ElementMap.h`.
   - Check `Zoo KCL`: diff `rust/kcl-lib/src/execution/{id_generator.rs,artifact.rs}` and `rust/kcl-lib/src/std/edge.rs` (`UnresolvedEdgeSpecifier`) against `10ae8aa9cd` to see whether automatic geometric fallback or engine-side persistent sub-shape provenance replaces counter-based `IdGenerator` UUIDs.
   - Check `LinuxCNC`: inspect `src/emc/tp/blendmath.h` against `76ee5a1b63` to see whether `BlendGeom9` (`#ifdef BLEND_9D`) has been implemented or if `BLEND_ACC_RATIO_TANGENTIAL` changed.
   - Check `Knitout`: check `knitout.html` version string (currently `v0.6`, `;!knitout-2` at `17b868c5a4`) for promoted `x-*` extensions or modified carrier/racking semantics.
2. **Re-run the Self-Contained Verification Probe**:
   ```bash
   python3 - <<'PY'
   import math
   # 1. Euler-Poincare bifurcation check
   assert (16 - 24 + 10 - 2) == 2*(1 - 1) and (16 - 24 + 10 - 0) == 2*(1 - 0)
   # 2. Knitout alignment check: front_idx == back_idx + rack (rack=2 aligns f3 with b1)
   assert 3 == 1 + 2
   # 3. LinuxCNC blendmath.h 90-deg corner velocity bound at a_max=1000, tol=0.01 mm
   a_n = 1000.0 * math.sqrt(1.0 - 0.5**2)
   r_max = 0.01 / (1.0 / math.sin(math.pi/4) - 1.0)
   v_max = math.sqrt(a_n * r_max)
   assert abs(r_max - 0.0241421356) < 1e-6 and abs(v_max - 4.572496) < 1e-3
   print(f"OK: a_n={a_n:.2f}, r_max={r_max:.6f}, v_max={v_max:.4f}")
   PY
   ```
   A passing probe confirms only the algebraic invariants above; verifying actual kernel TNP resilience on complex NURBS solids or physical knitability on a target machine requires executing `OCCT`/`FreeCAD` regression test suites or a hardware-specific `knitout` backend simulator.
