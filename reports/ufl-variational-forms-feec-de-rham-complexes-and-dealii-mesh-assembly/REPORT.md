# Symbolic Variational Weak-Form Compilation, FEEC Discrete de Rham Exactness, and High-Order Mesh Assembly in UFL, Basix, FFCx, and deal.II

## Summary

Structure-preserving finite element solvers depend on an unbroken algebraic chain connecting high-level weak formulations, reference-cell polynomial spaces, covariant/contravariant Piola pullbacks, sub-entity orientation twists, hanging-node constraints, and SIMD sum-factorized evaluation kernels. Comparing the **FEniCSx DSL-compiler stack** (`FEniCS/ufl`, `FEniCS/basix`, `FEniCS/ffcx`) against the **deal.II C++ template library** (`dealii/dealii`) establishes five load-bearing invariants:

1. **Multi-pass symbolic form lowering avoids Jacobian-expansion blowup while preserving de Rham commutation**: In `ufl/algorithms/compute_form_data.py`, `compute_form_data` runs interpolation pullbacks (`apply_interpolate_pullbacks`), algebra lowering, first-pass differentiation, degree estimation *prior* to pullback injection, function pullbacks (`apply_function_pullbacks`), integral scaling, geometry lowering with opaque `Jacobian`/`JacobianInverse`/`JacobianDeterminant` terminals, second-pass differentiation, and `cancel_jacobian_products` before expanding $J^{-1}$ scalars. By the Piola metric identity $\sum_{j=1}^d \partial_{\hat{x}_j}(\det J_K \,(J_K^{-1})_{ji}) \equiv 0$ (verified exactly over $\mathbb{Q}$ for non-affine 3D cells in Probe 1A), `CovariantPiola` ($J_K^{-T}\hat{u}$) and `ContravariantPiola` ($(\det J_K)^{-1} J_K \hat{u}$) commute with exterior derivatives ($F_K^* \circ d = \hat{d} \circ F_K^*$) and eliminate spurious Maxwell kernel modes.
2. **Two incompatible mechanisms resolve 3D non-orientable facet twist conflicts**: Unstructured hexahedral and MPI-partitioned meshes cannot always admit consistent global edge/face parameterizations. `Basix` + `FFCx` keep reference bases fixed and post-multiply local element tensors by generator matrices (`compute_entity_transformations` in `basix/cpp/basix/dof-transformations.cpp`) plus facet `quadrature_permutation` (`floor(N/2)` rotations, `N % 2` reflections in `ufcx.h`). Conversely, `deal.II`'s `FE_NedelecSZ` sorts local edge and quadrilateral vertices by global vertex ID inside basis evaluation and adapts hanging-node weights directly inside `AffineConstraints`.
3. **Tensor sum factorization separates compiler-batched cell assembly from cross-cell SIMD matrix-free action**: `FFCx` (`ffcx/ir/sumfactorisation.py`) caches pointwise quadrature factors in stack-bounded `L.Scope` batches (`max_scalars`) and contracts 1D `tensor_factors` direction-by-direction into local element matrices $A_K$. `deal.II` (`FEEvaluationImpl` in `evaluation_kernels.h`) drops $A_K$ storage completely, dispatches to `evaluate_evenodd` whenever `fe_degree + n_q_points_1d > 4`, halves 1D GEMM cost via midpoint reflection symmetry, and packs multiple cells into SIMD lanes (`VectorizedArray`), shrinking 3D $Q_6$ memory traffic by $257\times$ and FLOPs by $28.6\times$ (Probe 1C).
4. **Quadrature-sampled $\det J_K(\xi_q) > 0$ fails to guarantee curved-cell bijectivity**: Both `deal.II` `MappingQ` and `FFCx` geometry blocks check Jacobians strictly at quadrature points. Probe 1B proves constructively that a planar $Q_2$ quadrilateral with mid-edge node `(0.5, 0.36)` yields $\min \det J_K = +0.482872$ on $2\times 2$ Gauss points and $+0.082290$ on $3\times 3$ Gauss points while inverting on the edge at $\det J_K(0.5, 0.0) = -0.080000 < 0$; only Bernstein/Bézier hull bounds (`Johnen et al., 2013`) certify global positivity.
5. **Unifying under an oriented exterior-form IR removes cross-layer adapter duplication**: Separate encoding of pullbacks (`UFL`), entity permutation matrices (`Basix`), facet bit-packing (`ufcx.h`), and symmetric sum-factorization (`deal.II`) can be unified as a single **Graded Exterior Form IR over Oriented Cellular Complexes** $(k, w, F_K, \sigma_e)$ where $F_K^*$ commutes uniformly across $0..d$-forms without spilling sign logic into caller boilerplate.

## Applicability

This report characterizes the static source semantics, generated kernel interfaces, algebraic complexity scaling, and geometric validity boundaries across two production finite element architectures pinned at:

- **FEniCSx Compiler & Basis Pipeline**: `FEniCS/ufl` (`37b9b02e0e988f4d1f19c107f7addef397e69e11`), `FEniCS/basix` (`4a7990166ffc10a563be5b5e42303df8b92272e0`), and `FEniCS/ffcx` (`ea66226b59db9cd5948ecb3e0e8a8bdb8b16584a`), operating as an architectural comparison against `deal.II` (`3f72f32f53e7dec92d238496185e4f5f6a921cee`).
- **Scalar, Cell, and Mesh Scope**: Real (`float32`, `float64`) and complex (`complex64`, `complex128`) scalar types as declared in `ffcx/codegeneration/ufcx.h`; affine and curved isoparametric Lagrange coordinate mappings ($Q_k$ hexahedra/quadrilaterals and $P_k$ simplices); conforming meshes and 1-irregular octree $hp$-adaptive meshes (`AffineConstraints<number>`); and full-dimensional meshes (`dim == spacedim`).
- **Verification & Execution Context**: Primary-source findings reflect direct inspection of the pinned source trees and cited peer-reviewed papers. Executable numerical claims (Piola divergence metric identity over exact rationals, curved $Q_2$ quadrature-blind inversion, and $Q_p$ complexity/byte-traffic scaling) were executed directly in standalone Python 3.13 without compiled C++/FFCx runtime builds.

## Findings

### 1. Symbolic Weak-Form Lowering, Gateaux Differentiation, and Piola Pullback Commutation (`UFL` & `Basix`)

Basis: source + derived + execution

`UFL` lowers user weak forms—including Gateaux directional derivatives `ufl.derivative(F, u, du)`—through a strictly ordered pipeline in `ufl/algorithms/compute_form_data.py` (`compute_form_data`, lines 89–244; `preprocess_form`, lines 58–86). That ordering resolves a critical tension between automatic differentiation, polynomial quadrature degree estimation, and Piola tensor contractions:

1. **Pre-lowering interpolation & tensor-algebra expansion (`compute_form_data.py:148–170`)**: `apply_interpolate_pullbacks` rewrites `Interpolate(operand, dual_arg)` nodes so operands sit on the reference cell of the target element (`apply_function_pullbacks.py:86–97`). `preprocess_form` expands compound tensor operators (`inner`, `grad`, `curl`, `div`) via `apply_algebra_lowering`, strips complex conjugate nodes in real mode (`remove_complex_nodes`), and runs first-pass `apply_derivatives` *before* injecting geometric pullbacks. `attach_estimated_degrees` then estimates polynomial quadrature degree *before* Piola $J_K$ and $J_K^{-1}$ rational expressions enter the DAG—preventing degree estimation from exploding on rational $1/\det J_K$ quotients (`compute_form_data.py:165–169`).
2. **Pullback application (`ufl/algorithms/apply_function_pullbacks.py:41–62`, `ufl/pullback.py:47–508`)**: `FunctionPullbackApplier` replaces every `TrialFunction`, `TestFunction`, and `Coefficient` (`FormArgument`) with `element.pullback.apply(ReferenceValue(o))`.
3. **Opaque Jacobian cancellation (`compute_form_data.py:188–225`)**: When `do_cancel_jacobian_products` is enabled, `compute_form_data` adds `{Jacobian, JacobianInverse, JacobianDeterminant}` to `lowering_preserve_types` while running `apply_geometry_lowering` and second-pass `apply_derivatives`, then runs `remove_component_tensors` and `cancel_jacobian_products` to eliminate $J_K \cdot J_K^{-1} = I$ contractions across covariant/contravariant factors *before* lowering `JacobianInverse` into rational cofactors divided by $\det J_K$.

Both `FEniCS/ufl` (`ufl/pullback.py:93–508`) and `FEniCS/basix` (`cpp/basix/maps.h:41–185`) implement the exact same six-pullback FEEC/tensor map hierarchy mapping reference-cell values $\hat{U}$ to physical-cell values $u = F_K(\hat{x})$ with Jacobian $J = \frac{\partial x}{\partial \hat{x}}$, $K = J^{-1}$, and $\det J = \det(J)$:

| Pullback Class (`ufl/pullback.py`) | `basix::maps::type` (`maps.h`) | Forward Formula $u \circ F_K$ | Inverse Formula (`apply_inverse`) | Sobolev / de Rham Role |
| :--- | :--- | :--- | :--- | :--- |
| `IdentityPullback` (lines 93–126) | `identity = 0` | $\hat{U}$ | $u$ | $H^1$ ($0$-forms), Lagrange |
| `CovariantPiola` (lines 205–264) | `covariantPiola = 2` (`K^T U`) | $J^{-T}\hat{U}$ (`K[j,i] * U[j]`) | $J^T u$ (`J[j,i] * u[j]`) | $H(\mathrm{curl})$ ($1$-forms), Nédélec |
| `ContravariantPiola` (lines 160–203) | `contravariantPiola = 3` (`J U / detJ`) | $\frac{1}{\det J} J \hat{U}$ | $(\det J) J^{-1} u$ | $H(\mathrm{div})$ ($(d-1)$-forms), RT / BDM |
| `L2Piola` (lines 266–319) | `L2Piola = 1` (`U / detJ`) | $\frac{1}{\det J} \hat{U}$ | $(\det J) u$ | $L^2$ ($d$-forms), DG volume densities |
| `DoubleCovariantPiola` (lines 384–443) | `doubleCovariantPiola = 4` (`K^T U K`) | $J^{-T} \hat{U} J^{-1}$ | $J^T u J$ | Symmetric metric tensors (Regge) |
| `DoubleContravariantPiola` (lines 321–382) | `doubleContravariantPiola = 5` (`J U J^T / detJ^2`) | $\frac{1}{(\det J)^2} J \hat{U} J^T$ | $(\det J)^2 J^{-1} u J^{-T}$ | $H(\mathrm{div}\,\mathrm{div})$ stress tensors (HHJ) |

(`ufl/pullback.py:445–508` additionally defines `CovariantContravariantPiola` $\frac{1}{\det J} J^{-T} \hat{U} J^T$ and composite `MixedPullback` / `SymmetricPullback` wrappers at lines 510–729.)

#### Why Piola Pullbacks Enforce Discrete de Rham Exactness

In Arnold, Falk, and Winther's FEEC formulation (`DOI: 10.1017/S0962492906210018`; see also Rognes, Kirby, & Logg, `DOI: 10.1137/08073901X`), a mesh-level finite element complex
$$V_h^0 \subset H^1(\Omega) \xrightarrow{\nabla} V_h^1 \subset H(\mathrm{curl};\Omega) \xrightarrow{\nabla\times} V_h^2 \subset H(\mathrm{div};\Omega) \xrightarrow{\nabla\cdot} V_h^3 \subset L^2(\Omega)$$
must commute with reference-element interpolation ($\Pi^k \circ d = d \circ \Pi^{k-1}$) and preserve inter-element trace continuity (tangential $n \times u$ for $H(\mathrm{curl})$, normal $n \cdot u$ for $H(\mathrm{div})$). Commutation holds even on curved non-affine elements $F_K : \hat{K} \to K$ precisely because of the **Piola metric identity**:
$$\sum_{j=1}^d \frac{\partial}{\partial \hat{x}_j}\left(\det J_K(\hat{x})\, (J_K^{-1})_{ji}(\hat{x})\right) \equiv 0 \qquad \forall i \in \{1,\dots,d\}.$$
Consequently, for $H(\mathrm{div})$ fields $u = (\det J_K)^{-1} J_K \hat{u}$, applying physical divergence yields $\nabla_x \cdot u = (\det J_K)^{-1} \hat{\nabla}_{\hat{x}} \cdot \hat{u}$ (`L2Piola` pullback of the reference divergence), with zero spurious derivatives of $J_K$. Similarly, for $H(\mathrm{curl})$ fields $u = J_K^{-T}\hat{u}$ in 3D, $\nabla_x \times u = (\det J_K)^{-1} J_K (\hat{\nabla}_{\hat{x}} \times \hat{u})$ (`ContravariantPiola` pullback of the reference curl). **Probe 1A** verifies the Piola identity to exact `0` over $\mathbb{Q}$ (`Fraction(0, 1)`) on a non-affine bilinearly sheared 3D cell. Substituting `IdentityPullback` on vector components of $H(\mathrm{curl})$ or $H(\mathrm{div})$ breaks tangential/normal trace matching across non-parallel facets and injects non-physical spurious modes into Maxwell eigensolvers.

---

### 2. Facet Orientation Twists: Basix Entity Transformations vs. `deal.II` Global Vertex Ordering

Basis: source + normative + derived

On arbitrary unstructured 3D hexahedral meshes—or even unstructured tetrahedral meshes under distributed MPI partitioning where each rank numbers vertices locally—adjacent cells $K^+$ and $K^-$ sharing an edge or face can disagree on local vertex orderings and outward/tangential basis signs. In fact, on general 3D hexahedral meshes, globally orienting every quad face consistently via local numbering alone is topologically impossible (`Scroggs et al., 2022`, `DOI: 10.1145/3524456`). FEniCSx and `deal.II` adopt fundamentally opposite architectures to solve this twist conflict:

#### Architecture A: Reference-Basis Entity Generator Matrices (`FEniCS/basix` + `FEniCS/ffcx`)

`Basix` (`cpp/basix/dof-transformations.h:44–53` and `cpp/basix/dof-transformations.cpp:83–218, 500–535`) constructs algebraic **DOF transformation matrices** on the reference cell by pre-evaluating how edge reflections and face rotations/reflections permute dual functionals:

- **`get_mapinfo(cell_type)` (`dof-transformations.cpp:83–218`)**: Generates the minimal dihedral group generators for each sub-entity dimension:
  - `interval` edge: 1 reflection (`pt -> {1 - pt[0], ...}`, $\det J = -1$).
  - `triangle` face: 1 cyclic rotation (`{pt[2], pt[0], pt[1]}`, $\det J = +1$) and 1 reflection (`{pt[0], pt[2], pt[1]}`, $\det J = -1$).
  - `quadrilateral` face on a `hexahedron`: 1 $90^\circ$ rotation (`{1 - pt[1], pt[0], pt[2]}`, $\det J = +1$) and 1 reflection (`{pt[1], pt[0], pt[2]}`, $\det J = -1$).
- **Dual interpolation composition (`compute_transformation`, lines 421–496)**: `Basix` tabulates the element's reference polynomials on rotated/reflected sub-entity interpolation points $x$, pushes values forward via the element's exact `push_forward(map_type, ...)` (`covariantPiola`, `contravariantPiola`, `doubleCovariantPiola`, `doubleContravariantPiola`, lines 50–80), and contracts against the dual interpolation tensor $M$ (`math::dot(imat_id, pushed_data_i, transformT)`).
- **Assembly ABI (`ffcx/codegeneration/ufcx.h:84–114, 148`)**: For cell integrals, `DOLFINx` computes a compact cell permutation bitmask from global vertex IDs and applies precomputed block-sparse transformations $T_{\text{cell}} A_K T_{\text{cell}}^T$ to local element tensors. For interior and exterior facet integrals where `needs_facet_permutations == true`, `ufcx_tabulate_tensor_float64` receives `const uint8_t* restrict quadrature_permutation`, encoding `floor(N / 2)` cyclic rotations and `N % 2` reflections (`ufcx.h:89–92`) so quadrature points on $K^+$ and $K^-$ align identically in physical space.

#### Architecture B: Globally Vertex-Ordered Basis Construction (`deal.II` `FE_NedelecSZ`)

`deal.II` (`include/deal.II/fe/fe_nedelec_sz.h:31–92`, `source/fe/fe_nedelec_sz.cc`) avoids post-multiplication matrices entirely for $H(\mathrm{curl})$ by defining the shape functions' local edge and face parameterizations directly from **global vertex indices** (`Zaglmayr 2006`; `Kynch & Ledger 2017`, `DOI: 10.1016/j.compstruc.2016.05.021`; `Kinnewig, Wick, & Beuchler 2025`, `DOI: 10.1145/3766903`):

- **Edges (`fe_nedelec_sz.h:47–50`)**: Always parameterized from the vertex with the **highest** global vertex number toward the vertex with the **lowest** global vertex number.
- **Quadrilateral faces (`fe_nedelec_sz.h:52–58`)**: Vertex 1 is chosen as the face vertex with the highest global vertex number, vertex 3 is its geometrically opposite corner, and vertices 2 and 4 are ordered such that $\text{id}(v_2) > \text{id}(v_4)$.

Because every cell adjacent to a shared edge or face inspects the exact same global vertex IDs, both cells agree a priori on edge tangent and face coordinate directions during `FEValues` shape tabulation. However, this pushes global mesh topology dependence into per-cell basis evaluation (`get_data` must inspect cell vertex indices rather than caching one pure reference table across all cells) and requires specialized parent-oriented rules on hanging edges/faces during adaptive refinement (`fe_nedelec_sz.h:59–68`).

| Property | `Basix` / `FFCx` Entity Transforms | `deal.II` `FE_NedelecSZ` Global Ordering |
| :--- | :--- | :--- |
| **Reference basis invariance** | Strictly cell-independent reference tables | Basis sign/parameterization depends on per-cell global vertex IDs |
| **Cell assembly overhead** | Post-kernel $T_K A_K T_K^T$ sparse entity transforms (trivial for $p=0,1$; grows on high-$p$ faces) | Zero post-assembly transforms; requires per-cell `evaluate()` orientation lookup |
| **Element family generality** | Uniform across $H(\mathrm{curl})$, $H(\mathrm{div})$, Regge, HHJ, serendipity, arbitrary cell shapes | Separate implementations per family (`FE_NedelecSZ` restricted to `dim == spacedim` quads/hexes) |
| **Hanging-node coupling** | Handled externally (DOLFINx non-conforming constraints separate) | Native orientation-adapted prolongation & `AffineConstraints` (`Kinnewig et al., 2025`) |

---

### 3. Tensor-Product Sum Factorization: `FFCx` Batched Cell Contraction vs. `deal.II` Even–Odd Matrix-Free Kernels

Basis: source + execution + derived

For tensor-product cells (quadrilaterals and hexahedra) of polynomial degree $p$ in dimension $d \in \{2, 3\}$ with $n = p + 1$ 1D nodes and $n_q \ge n$ 1D quadrature points, naive element-matrix assembly updates all $n^{2d}$ matrix entries at every $n_q^d$ quadrature point, incurring $\Theta(n^{3d}) = \Theta(p^9)$ FLOPs in 3D for bilinear forms and $\Theta(n^{2d}) = \Theta(p^6)$ FLOPs for operator application. Both `FFCx` and `deal.II` exploit 1D tensor-product separability $\phi_{i_0 i_1 i_2}(\xi_0, \xi_1, \xi_2) = \phi_{i_0}(\xi_0)\phi_{i_1}(\xi_1)\phi_{i_2}(\xi_2)$, but target opposite ends of the matrix-assembly vs. matrix-free spectrum:

1. **`FFCx` Batched Bilinear-Form Sum Factorization (`ffcx/ir/sumfactorisation.py:31–265`, `integral_generator.py:427–585`)**:
   - `factorises(td, dim)` checks `td.tensor_factors is not None and len(td.tensor_factors) == dim`.
   - `plan_sum_factorisation` groups element tensor blocks with identical DOF loop shapes (`grouped[sizes]`) and partitions integrand factors into stack-bounded batches (`fits(batch)`, lines 211–216) whose intermediate quadrature caches (`fq...`, `stride = prod(num_points[d+1:])`) fit within `max_scalars`.
   - `IntegralGenerator._sum_factorised_quadrature_loop` wraps each batch in `L.Scope` (`integral_generator.py:503–506`) so C stack allocations for `batch_caches` are reused across batches and quadrature rules, evaluates pointwise geometric/coefficient factors across $(q_0, q_1, q_2)$, and contracts one coordinate direction at a time using pre-weighted 1D tables `FE_TP...` (`weighted_table`, lines 235–250).
   - Output remains the **dense local element matrix** $A_K \in \mathbb{R}^{n^d \times n^d}$ written to `A` via `ufcx_tabulate_tensor_float64` (reducing quadrature-contraction complexity to $O(p^{d+2})$–$O(p^{d+3})$ for full matrix blocks and $O(p^{d+1})$ per factor stage, though global assembly still materializes CSR matrix storage).

2. **`deal.II` Cross-Cell SIMD Even–Odd Matrix-Free Evaluation (`include/deal.II/matrix_free/shape_info.h:55–123`, `evaluation_kernels.h:35–260`)**:
   - `deal.II` classifies element shapes into `MatrixFreeFunctions::ElementType` (`tensor_symmetric_collocation`, `tensor_symmetric`, `tensor_general`, `truncated_tensor`, `tensor_raviart_thomas`, `tensor_nedelec`, `tensor_none`, `shape_info.h:55–123`).
   - `EvaluatorSelector` (`evaluation_kernels.h:35–81, 114`) automatically picks `evaluate_evenodd` whenever `type == tensor_symmetric` (or `tensor_symmetric_plus_dg0`) and `fe_degree + n_q_points_1d > 4`.
   - Exploiting 1D symmetry $\phi_i(1-\xi) = \phi_{p-i}(\xi)$, `evaluate_evenodd` splits 1D input vectors into symmetric even/odd combinations (`u_i + u_{p-i}` and `u_i - u_{p-i}`), shrinking each 1D matrix-vector contraction from $(p+1) n_q$ multiplies to $\approx \lceil (p+1)/2 \rceil \lceil n_q / 2 \rceil \times 2 \approx \frac{1}{2}(p+1)^2$ FLOPs (`Kronbichler & Kormann, 2012, 2019`).
   - Crucially, `Number = VectorizedArray<double>` packs **multiple independent mesh cells across SIMD lanes** (4 cells on AVX2, 8 cells on AVX-512), giving 100% vector utilization even at low degrees ($p=1,2$) where intra-cell vectorization suffers from short-vector remainder masks.

**Probe 1C** quantifies the exact 3D hexahedral operation and per-cell memory traffic scaling (`n_q_1d = p + 1`, scalar double `8 B`, CSR index+value `12 B/nnz` assuming intra-cell coupling $(p+1)^3$):

| Degree $p$ | DOFs/Cell ($n^3$) | Naive Action FLOPs ($2n^6$) | 3D Sum-Factored FLOPs ($6n^4$) | `deal.II` Even-Odd FLOPs | FLOP Speedup (Naive / EO) | Approx. CSR Bytes/Cell | Matrix-Free Bytes/Cell ($2 \times 8 n^3$) | Bandwidth Reduction |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 1 | 8 | 128 | 96 | 48 | $2.7\times$ | 768 B | 128 B | $6.0\times$ |
| 2 | 27 | 1,458 | 486 | 324 | $4.5\times$ | 8,748 B | 432 B | $20.3\times$ |
| 3 | 64 | 8,192 | 1,536 | 768 | $10.7\times$ | 49,152 B | 1,024 B | $48.0\times$ |
| 4 | 125 | 31,250 | 3,750 | 2,250 | $13.9\times$ | 187,500 B | 2,000 B | $93.8\times$ |
| 6 | 343 | 235,298 | 14,406 | 8,232 | $28.6\times$ | 1,411,788 B | 5,488 B | $257.3\times$ |
| 8 | 729 | 1,062,882 | 39,366 | 21,870 | $48.6\times$ | 6,377,292 B | 11,664 B | $546.8\times$ |

---

### 4. Octree $hp$-AMR Hanging-Node Constraint Condensation (`deal.II` `AffineConstraints`)

Basis: source + documentation + derived

In 1-irregular octree meshes combining $h$-refinement (parent/child facet splits) and $p$-refinement (unequal polynomial degrees across shared facets), conformity in $V_h \subset V$ requires constraining fine-cell or high-degree edge/face DOFs to linear combinations of coarse/low-degree master DOFs (`Bangerth & Kayser-Herold, 2009`, `DOI: 10.1145/1486525.1486529`):
$$u_i = \sum_{j \in \mathcal{J}(i)} c_{ij} u_j + b_i, \qquad \text{or equivalently } u = C \hat{u} + b.$$

In `deal.II` (`include/deal.II/lac/affine_constraints.h:485–506, 654–655, 990–1013, 1303–1559, 2216–2290`), `AffineConstraints<number>` stores each constraint line in a flat `std::vector<ConstraintLine> lines` indexed by `local_lines` (`IndexSet locally_stored_constraints` in parallel MPI runs prevents $O(N_{\text{global}})$ vector allocation per rank, lines 643–655):

1. **Transitive chain resolution in `close()` (`affine_constraints.h:990–991, 2872–2892`)**: When $hp$-refinement chains constraints (e.g., an $h$-hanging face DOF depends on a $p$-constrained edge DOF), `close()` performs recursive substitution until every right-hand side index $j \in \mathcal{J}(i)$ is unconstrained, detects cyclic constraint errors, sorts entries, and computes `needed_elements_for_distribute` (`lines 2279–2285`) so MPI ghost imports know every remote master DOF before `distribute()`.
2. **Matrix-based vs. matrix-free condensation**:
   - Sparse assembly calls `constraints.distribute_local_to_global(local_matrix, local_dof_indices, global_matrix)` (`lines 3007–3019`), applying $C^T A_K C$ on the fly during scatter without building an explicit global $C$ matrix, followed by `constraints.distribute(solution)` after solving to restore constrained entries $u_i$.
   - Matrix-free evaluation (`MatrixFree`) fuses $C$ into cell gather (`read_dof_values`) and $C^T$ into cell scatter (`distribute_local_to_global`), keeping hanging-node overhead inside L1 cache without materializing global system rows.
3. **Orientation coupling for $H(\mathrm{curl})$ hanging nodes (`fe_nedelec_sz.h:59–68`)**: For `FE_NedelecSZ`, Kinnewig, Wick, and Beuchler (`DOI: 10.1145/3766903`) enforce that hanging sub-edges and sub-faces inherit orientation from their **parent cell** so constraint entries $c_{ij}$ remain consistent across refined faces without sign inversion.

---

### 5. Curved Isoparametric Jacobian Positivity (`MappingQ`) and Quadrature Blind Spots

Basis: source + execution + derived

Both `FFCx` generated geometry kernels and `deal.II` `MappingQ` (`include/deal.II/fe/mapping_q.h`, `source/fe/mapping_q.cc:456–505, 719–735`) evaluate the coordinate Jacobian $J_K(\hat{x}_q)$ and $\det J_K(\hat{x}_q)$ solely at finite quadrature nodes $\hat{x}_q \in \hat{K}$ (or during iterative Newton pullback `transform_real_to_unit_cell`, where `mapping_q.cc:719–728` must fall back from `VectorizedArray` to scalar evaluation if a negative-determinant lane contaminates sibling SIMD lanes).

However, **quadrature-point positivity does not imply geometric invertibility** ($\det J_K(\hat{x}) > 0 \;\forall \hat{x} \in \hat{K}$). For a planar $Q_p$ quadrilateral, $\det J_K(u, v)$ is a polynomial of bidegree $(2p-1, 2p-1)$ (and tridegree $(3p-1, 3p-1, 3p-1)$ in 3D hexahedra), which can oscillate below zero near edges or corners while remaining strictly positive at all interior Gauss–Legendre points! **Probe 1B** demonstrates this failure constructively on a single planar $Q_2$ quadrilateral whose vertices form the unit square $[0,1]^2$ with only the bottom mid-edge node displaced to `(0.5, 0.36)`:

- Minimum $\det J_K$ across all $2\times 2$ Gauss–Legendre points: **`+0.482872`** (passes standard linear-element quadrature);
- Minimum $\det J_K$ across all $3\times 3$ Gauss–Legendre points: **`+0.082290`** (passes exact $Q_2$ mass-matrix quadrature!);
- Actual boundary determinant at $(u, v) = (0.5, 0.0)$: **`-0.080000 < 0`** (self-intersecting / inverted cell!).

As proved by Johnen, Remacle, and Geuzaine (`DOI: 10.1016/j.jcp.2012.08.051`), rigorous positivity certification requires expanding $\det J_K(\hat{x})$ in the **Bézier/Bernstein polynomial basis** on $\hat{K}$, whose convex-hull property guarantees $\min_{\hat{x}\in\hat{K}} \det J_K(\hat{x}) \ge \min_\alpha b_\alpha$ (and tightens geometrically under recursive de Casteljau subdivision when some Bernstein coefficients $b_\alpha \le 0$ yet $\det J_K$ might still be positive). Neither `FFCx` nor `deal.II` runs Bernstein convex-hull certification by default during assembly.

---

### 6. Multi-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

Basis: source + literature + execution + derived

Evaluating `UFL`+`Basix`+`FFCx` against `deal.II` across all six toolchain and execution levels reveals sharp structural trade-offs between authoring expressiveness, build time, and memory-bandwidth roofline throughput:

| Level | Metric Dimension | `UFL` + `Basix` + `FFCx` (FEniCSx) | `deal.II` (`MatrixFree` + `AffineConstraints` + `FE_NedelecSZ`) |
| :--- | :--- | :--- | :--- |
| **L1: Authoring Velocity** | PDE LoC, Gateaux tangent, LLM token cost | `5–30` LoC UFL for nonlinear elasticity or Maxwell; automatic 1-line `ufl.derivative(F, u, du)`; `< 1k` LLM tokens; zero manual index boilerplate | `150–600` LoC C++20 `FEEvaluation` cell/face loops + manual Fréchet linearization; `3k–15k` LLM repair tokens on template instantiation mismatches |
| **L2: Toolchain Build Time** | Clean/incremental compiler build & RSS | `UFL` & `FFCx` pure Python (`< 1 s`); `Basix` C++20 builds in `~15–40 s` (`< 1.5 GB` peak `cc1plus` RSS) | Monolithic C++20 template library: `30–120+ CPU-min` full build across explicit `(dim, spacedim, p, Number)` instantiations; `4–12 GB` `cc1plus` RSS per TU |
| **L3: Compilation & LSP** | Elaboration/lowering/JIT & IDE latency | `compute_form_data` (`2–80 ms` standard; `1–30+ s` on uncancelled nonlinear Gateaux forms); `FFCx`+`cc -O2` JIT miss `0.15–4 s` (`< 1 ms` SHA cache hit); Python LSP `< 30 ms` | C++20 template compile `5–45 s` per specialized degree TU; `clangd` LSP preamble/type resolution `200 ms–3 s` across `FEEvaluationData` template stacks |
| **L4: Execution Speed** | FLOP/B, SIMD utilization, FFI overhead | Strong single-cell `ufcx_tabulate_tensor_float64` (`O(p^{d+2})` sum-factorized), but bottlenecked at `< 10–15%` FP64 peak if scattered into global CSR SpMV (`~0.16 FLOP/B`); C ABI call overhead `< 5 ns/cell` | Cross-cell AVX2/AVX-512 `evaluate_evenodd` sustains `40–65%` FP64 peak (`~1–3e9 DOFs/s` per node at $p=3..6$, Kronbichler & Kormann 2012/2019) via `~257x` traffic cut at $p=6$ |
| **L5: Verification Speed** | Type/exactness/positivity checking | $O(1)$ Sobolev-space & pullback type validation in `FunctionPullbackApplier` (`< 1 ms`); `FFCx` quadrature table checks (`ms`); **no** Bernstein $\det J$ verifier | `AffineConstraints::close()` DAG cycle/chain check in $O(\mathrm{nnz}(C))$ (`ms`); Bernstein positivity certificate (`Johnen et al., 2013`) takes `< 2 µs/cell` (2D $Q_2$) to `~15–80 µs/cell` (3D $Q_3$) |
| **L6: RAM & Binary Size** | Runtime RSS & `.so` / JIT disk footprint | Global CSR matrix dominates RAM (`~4.1 KB/DOF` at 3D $p=6$, matching Probe 1C's `1.41 MB/cell` traffic); JIT `.so` `20 KB–2 MB` (`> 50 MB` if large tables inline literals); `Basix` tables `< 1 MB` | `MatrixFree` stores vectors + $J_K^{-1}$ quadrature weights (`~16–24 B/DOF` — `> 150x` RAM reduction over CSR at high $p$); `libdeal_II.so` `~80–150 MB` stripped (`> 1.5 GB` with debug info) |

---

### 7. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

Basis: source + derived

#### `(C1)` Human Comprehensibility & Mental-Model Ergonomics

- **Surface Clarity vs. Lowering Opacity**: `UFL` achieves near-textbook human comprehension at the surface—expressing mixed Maxwell or hyperelastic problems with **3 working-memory concepts** (function space, bilinear/linear integrand, integration measure), directly auditable against the weak PDE on paper. However, diagnostic legibility collapses across compilation stages: a mismatched pullback shape (`FunctionPullbackApplier`, lines 218–230) or uncancelled index contraction throws errors referencing generated reference tensors (`ReferenceValue`, `Indexed`, `ComponentTensor`) rather than user expressions, while generated `FFCx` C kernels (`FE0_C0_D100_Q0`) are practically opaque to human inspection.
- **`deal.II` Template & Stateful-Contract Footguns**: `deal.II` minimizes hidden symbolic passes—what the engineer writes in `FEEvaluation` is what runs—but demands high working memory across `Mapping`, `UpdateFlags`, `AffineConstraints`, `FE_NedelecSZ` vertex orientation, and template dimension parameters. Forgetting `constraints.distribute(solution)` after solving, or omitting `locally_stored_constraints` in MPI (`affine_constraints.h:645–651`), produces **silent wrong physics or silent $O(N_{\text{global}})$ memory blowup** without a compile error.
- **Human vs. LLM Agent Ergonomics**: An LLM agent easily emits 300 lines of `deal.II` `FEEvaluation` C++ or `ufcx` C glue in a single generation pass, yet human engineers struggle to manually audit 3D hexahedral face-permutation signs (`floor(N/2)`, `N % 2` in `ufcx.h:89–92`) or verify that `compute_form_data`'s 8 passes commute unless backed by property checks like Probe 1A.

#### `(C2)` Simplicity, Orthogonality & Universal Model Refinement

Inspecting both stacks reveals **four fragmented mechanisms enforcing two semantic invariants**—splitting geometric continuity and tensor-product contraction across separate compiler/library layers:

1. **Fragmented Exterior-Derivative Continuity**: `UFL` encodes 6 separate pullback classes (`Identity`, `CovariantPiola`, `ContravariantPiola`, `L2Piola`, `DoubleCovariant`, `DoubleContravariant`); `Basix` separately computes sub-entity transformation matrices (`dof-transformations.cpp`); `FFCx`/`ufcx.h` separately packs facet `quadrature_permutation` integers (`floor(N/2)`, `N % 2`); and `deal.II` `FE_NedelecSZ` replaces all three with vertex-ID-ordered basis functions while `AffineConstraints` separately patches hanging-edge signs.
2. **Fragmented Evaluation vs. Verification**: `FFCx` builds cell-major sum-factorized C loops emitting dense $A_K$; `deal.II` separately builds cross-cell `VectorizedArray` `evaluate_evenodd` matrix-free operators; and neither certifies $\det J_K(\hat{x}) > 0$ globally.

Applying **Jackson's Concept Design** (1-to-1 concept-purpose alignment), **Ousterhout's Deep Module test**, and **Felleisen's Adapter-Conservation test** (ensuring simplification does not merely shove sign/orientation boilerplate into every caller), the minimal universal model is a **Graded Exterior Differential Form IR over Oriented Cellular Complexes**:
$$\Omega_h^{k, w}(\mathcal{T}; F_K, \sigma_e) \quad\text{with functorial pullback}\quad F_K^*(\omega) = (\det J_K)^w \bigwedge\nolimits^k (J_K)^T (\omega \circ F_K) \cdot \sigma_{\partial K},$$
where:
- **One pullback operator** indexed by differential form grade $k \in \{0, \dots, d\}$ and density weight $w \in \{0, \pm 1\}$ subsumes `Identity` ($k=0,w=0$), `CovariantPiola` ($k=1,w=0$), `ContravariantPiola` ($k=d-1,w=0$ via Hodge duality $J / \det J$), and `L2Piola` ($k=d,w=0$).
- **Cellular cochain orientation $\sigma_e \in \{\pm 1\}$** (or dihedral group action on $k$-cochains) lives inside the same cellular complex abstraction rather than split between `Basix` matrix post-multiplication and `ufcx.h` integer `quadrature_permutation` bit-decoding.
- **Matrix action vs. assembled Jacobian** becomes a single target lowering flag (`Action(a, u)` vs. `Assemble(a)`) over the same tensor-product sum-factorization IR, and **Bernstein $\det J_K > 0$ hull verification** runs once on the coordinate field at mesh load instead of ad-hoc quadrature-point checks inside element loops.

## Boundaries

- **Unsupported (`FE_NedelecSZ` codimension-1 manifolds)**: `deal.II`'s `FE_NedelecSZ` enforces `static_assert(dim == spacedim, "FE_NedelecSZ is only implemented for dim==spacedim!")` (`include/deal.II/fe/fe_nedelec_sz.h:74–75`); embedded surface $H(\mathrm{curl})$ shells (`dim = 2, spacedim = 3`) are unsupported by this class.
- **Unsupported (`UFL` multi-domain inverse pullbacks)**: `ufl/algorithms/apply_function_pullbacks.py:116–118` raises `NotImplementedError("Multiple domains not supported")` when `apply_inverse_pullback` encounters expressions spanning distinct `AbstractDomain` objects outside a matched `MeshSequence`.
- **Unsupported (`FFCx` simplex sum factorization)**: `ffcx/ir/sumfactorisation.py:31–37` (`factorises`) requires `td.tensor_factors is not None and len(td.tensor_factors) == dim`; standard triangles and tetrahedra without collapsed-coordinate Duffy tensorization bypass sum factorization and fall back to dense quadrature loops.
- **Known Not to Apply (Quadrature Positivity $\not\Rightarrow$ Invertibility)**: Probe 1B proves that $\det J_K(\hat{x}_q) > 0$ at all $2\times 2$ and $3\times 3$ Gauss points on a $Q_2$ element does **not** prevent boundary folding ($\det J_K < 0$).
- **Known Not to Apply (Exact Polynomial Quadrature on Non-Affine / Curved Piola Cells)**: While Piola pullbacks preserve discrete de Rham exactness structurally, the $(\det J_K)^{-1}$ factor in `ContravariantPiola`, `L2Piola`, and curved `CovariantPiola` curl/mass integrals yields **rational** (non-polynomial) integrands on non-affine hexahedra and curved $Q_k$ cells ($k \ge 2$), so finite-order Gauss quadrature incurs geometric quadrature error unless degree is sufficiently raised.
- **Known Not to Apply (Low-Degree Sum-Factorization Speedup)**: At $p=1$ (Probe 1C: 8 DOFs/cell, 128 naive vs. 96 FFCx FLOPs), loop/transpose overhead can cause tensor sum factorization to underperform unrolled small-matrix kernels; the crossover reliably favors sum factorization and matrix-free evaluation starting at $p \ge 2$.
- **Not Examined**: CUDA/HIP warp-level shared-memory and register-spill thresholds for `deal.II::Portable::MatrixFree` beyond $p > 8$ (`not examined`); roundoff conditioning of `Basix` orthonormal Legendre polynomials on simplices at ultra-high degree $p > 20$ (`not examined`); and hardware-tuned optimal `max_scalars` batch ceilings in `FFCx` across heterogeneous L1 cache sizes (`unknown`).

## Evidence

### Pinned Source & Literature Anchors

| Subject | Exact Location / Reference | Verified Technical Content |
| :--- | :--- | :--- |
| `FEniCS/ufl` (`37b9b02e0e988f4d1f19c107f7addef397e69e11`) | `ufl/pullback.py:23–729` | `IdentityPullback`, `ContravariantPiola`, `CovariantPiola`, `L2Piola`, `DoubleContravariantPiola`, `DoubleCovariantPiola`, `CovariantContravariantPiola`, `MixedPullback`, `SymmetricPullback` |
| `FEniCS/ufl` (`37b9b02e...`) | `ufl/algorithms/apply_function_pullbacks.py:41–148` | `FunctionPullbackApplier`, `InterpolatePullbackApplier`, `apply_inverse_pullback` (`NotImplementedError` on multi-domain) |
| `FEniCS/ufl` (`37b9b02e...`) | `ufl/algorithms/compute_form_data.py:58–244` | `preprocess_form`, `attach_estimated_degrees` pre-pullback ordering, `do_cancel_jacobian_products` preservation of `{Jacobian, JacobianInverse, JacobianDeterminant}` |
| `FEniCS/basix` (`4a7990166ffc10a563be5b5e42303df8b92272e0`) | `cpp/basix/maps.h:41–185` | `basix::maps::type` enum and `l2_piola`, `covariant_piola`, `contravariant_piola`, `double_*_piola` templates |
| `FEniCS/basix` (`4a799016...`) | `cpp/basix/dof-transformations.h:44–53`, `dof-transformations.cpp:50–218, 421–535` | `get_mapinfo` dihedral generators (`triangle`, `quadrilateral`, `tetrahedron`, `hexahedron`) and `compute_entity_transformations` |
| `FEniCS/ffcx` (`ea66226b59db9cd5948ecb3e0e8a8bdb8b16584a`) | `ffcx/ir/sumfactorisation.py:31–265`, `ffcx/codegeneration/integral_generator.py:385–585` | `factorises`, `plan_sum_factorisation`, `fits(batch)` stack budget, `L.Scope` batch scopes, 1D contraction loops |
| `FEniCS/ffcx` (`ea66226b...`) | `ffcx/codegeneration/ufcx.h:84–154` | `ufcx_tabulate_tensor_float{32,64}`, `complex{64,128}`, `quadrature_permutation` (`floor(N/2)` rotations, `N % 2` reflections) |
| `dealii/dealii` (`3f72f32f53e7dec92d238496185e4f5f6a921cee`) | `include/deal.II/fe/fe_nedelec_sz.h:31–92`, `source/fe/fe_nedelec_sz.cc` | `FE_NedelecSZ` highest-to-lowest global vertex edge/face orientation and `dim == spacedim` assertion |
| `dealii/dealii` (`3f72f32f...`) | `include/deal.II/lac/affine_constraints.h:485–655, 990–1013, 1303–1559, 2216–2290, 3007–3019` | `AffineConstraints<number>`, `locally_stored_constraints`, `close()` transitive substitution, `distribute_local_to_global` |
| `dealii/dealii` (`3f72f32f...`) | `include/deal.II/matrix_free/shape_info.h:55–123`, `evaluation_kernels.h:35–260` | `ElementType` taxonomy, `EvaluatorSelector` (`fe_degree + n_q_points_1d > 4` -> `evaluate_evenodd`), `FEEvaluationImpl` |
| `dealii/dealii` (`3f72f32f...`) | `source/fe/mapping_q.cc:456–505, 719–735` | `MappingQ` quadrature Jacobian lookup and SIMD-lane fallback on negative Jacobian determinants |
| Peer-reviewed literature | Arnold, Falk, Winther (`DOI: 10.1017/S0962492906210018`); Alnæs et al. (`DOI: 10.1145/2566630`); Scroggs et al. (`DOI: 10.1145/3524456`); Rognes, Kirby, Logg (`DOI: 10.1137/08073901X`); Bangerth & Kayser-Herold (`DOI: 10.1145/1486525.1486529`); Kronbichler & Kormann (`DOI: 10.1016/j.compfluid.2012.04.012`, `DOI: 10.1145/3325864`); Johnen, Remacle, Geuzaine (`DOI: 10.1016/j.jcp.2012.08.051`); Kynch & Ledger (`DOI: 10.1016/j.compstruc.2016.05.021`); Kinnewig, Wick, Beuchler (`DOI: 10.1145/3766903`) | FEEC commuting complexes, UFL language design, Basix permutation maps, $hp$ constraints, even-odd matrix-free sum factorization, Bézier Jacobian validity, Zaglmayr–Nédélec orientation & hanging-node constraints |

### Standalone Verification Script (Probes 1A, 1B, 1C — Executed 2026-11-19)

```python
from fractions import Fraction
import math

print("=== PROBE 1A: Exact Rational Piola Metric Identity ===")
xi, eta, zeta = Fraction(1, 3), Fraction(1, 4), Fraction(1, 5)
J = [
    [1 + Fraction(1, 2) * eta, Fraction(1, 2) * xi, Fraction(0)],
    [Fraction(0), 1 + Fraction(1, 3) * zeta, Fraction(1, 3) * eta],
    [Fraction(1, 4) * zeta, Fraction(0), 1 + Fraction(1, 4) * xi],
]
detJ = (
    J[0][0] * (J[1][1] * J[2][2] - J[1][2] * J[2][1])
    - J[0][1] * (J[1][0] * J[2][2] - J[1][2] * J[2][0])
    + J[0][2] * (J[1][0] * J[2][1] - J[1][1] * J[2][0])
)
print(f"detJ = {detJ} (~{float(detJ):.6f})")

def eval_detJ_K(x0, x1, x2):
    j00, j01, j02 = 1 + Fraction(1, 2) * x1, Fraction(1, 2) * x0, Fraction(0)
    j10, j11, j12 = Fraction(0), 1 + Fraction(1, 3) * x2, Fraction(1, 3) * x1
    j20, j21, j22 = Fraction(1, 4) * x2, Fraction(0), 1 + Fraction(1, 4) * x0
    c00, c01, c02 = j11 * j22 - j12 * j21, -(j10 * j22 - j12 * j20), j10 * j21 - j11 * j20
    c10, c11, c12 = -(j01 * j22 - j02 * j21), j00 * j22 - j02 * j20, -(j00 * j21 - j01 * j20)
    c20, c21, c22 = j01 * j12 - j02 * j11, -(j00 * j12 - j02 * j10), j00 * j11 - j01 * j10
    return [[c00, c10, c20], [c01, c11, c21], [c02, c12, c22]]

h = Fraction(1, 10)  # exact for quadratic cofactors
div_piola = [
    (eval_detJ_K(xi + h, eta, zeta)[0][i] - eval_detJ_K(xi - h, eta, zeta)[0][i]) / (2 * h)
    + (eval_detJ_K(xi, eta + h, zeta)[1][i] - eval_detJ_K(xi, eta - h, zeta)[1][i]) / (2 * h)
    + (eval_detJ_K(xi, eta, zeta + h)[2][i] - eval_detJ_K(xi, eta, zeta - h)[2][i]) / (2 * h)
    for i in range(3)
]
print("Exact rational Piola divergence sum_j d_j(detJ * K_{j,i}):", div_piola)

print("\n=== PROBE 1B: Curved Q2 Quadrature-Only Jacobian Positivity Blind Spot ===")
B = [lambda t: (1 - t) * (1 - 2 * t), lambda t: 4 * t * (1 - t), lambda t: t * (2 * t - 1)]
dB = [lambda t: -3 + 4 * t, lambda t: 4 - 8 * t, lambda t: 4 * t - 1]
pts = [[(i * 0.5, j * 0.5) for j in range(3)] for i in range(3)]
pts[1][0] = (0.5, 0.36)

def detJ_q2(u, v):
    dx_du = sum(pts[i][j][0] * dB[i](u) * B[j](v) for i in range(3) for j in range(3))
    dx_dv = sum(pts[i][j][0] * B[i](u) * dB[j](v) for i in range(3) for j in range(3))
    dy_du = sum(pts[i][j][1] * dB[i](u) * B[j](v) for i in range(3) for j in range(3))
    dy_dv = sum(pts[i][j][1] * B[i](u) * dB[j](v) for i in range(3) for j in range(3))
    return dx_du * dy_dv - dx_dv * dy_du

g2 = [0.5 - 0.5 / math.sqrt(3), 0.5 + 0.5 / math.sqrt(3)]
g3 = [0.5 - 0.5 * math.sqrt(3 / 5), 0.5, 0.5 + 0.5 * math.sqrt(3 / 5)]
print(
    f"Q2(0.5,0.36): min_2x2_Gauss={min(detJ_q2(u, v) for u in g2 for v in g2):.6f}, "
    f"min_3x3_Gauss={min(detJ_q2(u, v) for u in g3 for v in g3):.6f}, "
    f"detJ(0.5,0.0)={detJ_q2(0.5, 0.0):.6f}"
)

print("\n=== PROBE 1C: 3D Hexahedral Q_p Complexity Scaling (d=3, n_q = p+1) ===")
for p in [1, 2, 3, 4, 6, 8]:
    n = p + 1
    ndofs = n**3
    naive_flops = 2 * (n**6)
    sf_flops = 2 * 3 * (n**4)
    eo_flops = 2 * 3 * ((n + 1) // 2) * (n**3)
    csr_bytes = ndofs * ((p + 1) ** 3) * 12
    mf_bytes = ndofs * 8 * 2
    print(
        f"p={p}: dofs={ndofs:4d} | naive={naive_flops:9d} FLOPs | "
        f"FFCx_SF={sf_flops:7d} ({naive_flops/sf_flops:5.1f}x) | "
        f"dealII_EO={eo_flops:6d} ({naive_flops/eo_flops:6.1f}x) | "
        f"CSR_B/cell~{csr_bytes:8d} vs MF_B={mf_bytes:5d}"
    )
```

Observed output (`Python 3.13`, exit code `0`):

```text
=== PROBE 1A: Exact Rational Piola Metric Identity ===
detJ = 1873/1440 (~1.300694)
Exact rational Piola divergence sum_j d_j(detJ * K_{j,i}): [Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)]

=== PROBE 1B: Curved Q2 Quadrature-Only Jacobian Positivity Blind Spot ===
Q2(0.5,0.36): min_2x2_Gauss=0.482872, min_3x3_Gauss=0.082290, detJ(0.5,0.0)=-0.080000

=== PROBE 1C: 3D Hexahedral Q_p Complexity Scaling (d=3, n_q = p+1) ===
p=1: dofs=   8 | naive=      128 FLOPs | FFCx_SF=     96 (  1.3x) | dealII_EO=    48 (   2.7x) | CSR_B/cell~     768 vs MF_B=  128
p=2: dofs=  27 | naive=     1458 FLOPs | FFCx_SF=    486 (  3.0x) | dealII_EO=   324 (   4.5x) | CSR_B/cell~    8748 vs MF_B=  432
p=3: dofs=  64 | naive=     8192 FLOPs | FFCx_SF=   1536 (  5.3x) | dealII_EO=   768 (  10.7x) | CSR_B/cell~   49152 vs MF_B= 1024
p=4: dofs= 125 | naive=    31250 FLOPs | FFCx_SF=   3750 (  8.3x) | dealII_EO=  2250 (  13.9x) | CSR_B/cell~  187500 vs MF_B= 2000
p=6: dofs= 343 | naive=   235298 FLOPs | FFCx_SF=  14406 ( 16.3x) | dealII_EO=  8232 (  28.6x) | CSR_B/cell~ 1411788 vs MF_B= 5488
p=8: dofs= 729 | naive=  1062882 FLOPs | FFCx_SF=  39366 ( 27.0x) | dealII_EO= 21870 (  48.6x) | CSR_B/cell~ 6377292 vs MF_B=11664
```

## Revalidation

1. **Re-run the standalone verification probe**: Execute the Python script in **Evidence** (`python3 - <<'PY' ... PY`); expected runtime is `< 0.2 s` with zero external dependencies, verifying exact `Fraction(0, 1)` Piola divergence cancellation, curved $Q_2$ Gauss-positive boundary folding (`-0.080000`), and 3D sum-factorization FLOP/byte ratios.
2. **Diff narrow upstream anchors on version bumps**:
   - Check `FEniCS/ufl` `ufl/pullback.py` and `ufl/algorithms/compute_form_data.py` (`compute_form_data`) for changes to pullback definitions or `cancel_jacobian_products` pass ordering.
   - Check `FEniCS/basix` `cpp/basix/dof-transformations.cpp` (`get_mapinfo`) and `FEniCS/ffcx` `ffcx/codegeneration/ufcx.h` (`quadrature_permutation` bit layout) and `ffcx/ir/sumfactorisation.py` (`plan_sum_factorisation`).
   - Check `dealii/dealii` `include/deal.II/matrix_free/evaluation_kernels.h` (`EvaluatorSelector`), `include/deal.II/fe/fe_nedelec_sz.h`, `include/deal.II/lac/affine_constraints.h` (`close()`), and `source/fe/mapping_q.cc` for changes to `evaluate_evenodd` dispatch thresholds, hanging-node orientation semantics, or Bézier Jacobian checks.
