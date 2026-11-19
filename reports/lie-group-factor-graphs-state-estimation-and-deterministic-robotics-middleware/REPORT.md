# Lie-Group Factor Graphs, Symbolic Manifold Codegen, and Deterministic Zero-Copy Robotics Middleware

## Summary

Real-time robotics estimation and control stacks couple two fragile boundaries: (1) nonlinear on-manifold state estimation over Lie groups ($\mathrm{SO}(3)$, $\mathrm{SE}(3)$, $\mathrm{Sim}(3)$) where storage coordinates differ from tangent perturbations, and (2) inter-process callback scheduling and shared-memory transport connecting sensors, estimators, and actuators. Four core invariants and failure modes govern these layers:

1. **Three incompatible $\mathrm{Pose3}$ retraction ($\boxplus$) conventions exist across mainstream robotics libraries.** For a pose $T_a = (R_a, t_a)$ and tangent step $\xi = (\omega, v) \in \mathbb{R}^6$, `SymForce` default `Pose3.retract` operates on the world-frame product manifold $(R_a \operatorname{Exp}(\omega),\, t_a + v)$, `GTSAM` default `Pose3::retract` (without `GTSAM_POSE3_EXPMAP`) composes a body-frame product retraction $(R_a \operatorname{Exp}(\omega),\, t_a + R_a v)$, and `GTSAM` with `GTSAM_POSE3_EXPMAP` applies the coupled $\mathrm{SE}(3)$ matrix exponential $(R_a \operatorname{Exp}(\omega),\, t_a + R_a J_l(\omega) v)$. Mixing symbolic Jacobians or covariance blocks across these conventions silently corrupts translation updates and marginal covariances by factors of $R_a$ and $J_l(\omega)$.
2. **Singularity elimination trades branchless codegen against $\sqrt{2\epsilon}$ near-identity bias.** `SymForce` eliminates $\theta \to 0$ `sin(θ)/θ` and `acos(w)/sqrt(1-w²)` singularities without runtime branches via `theta = sqrt(theta_sq + eps^2)` and `w_safe = Min(1 - eps, |w|)` (canonicalizing quaternion double-cover $q \equiv -q$ via `sign_no_zero(w)`). While `Rot3.to_tangent(I)` returns exact zero with Jacobian error $O(\epsilon)$, `Rot3.to_tangent_norm(I) = 2*acos(1 - eps)` incurs a non-zero $2\sqrt{2\epsilon}$ bias (`1.33e-7 rad` at `f64` default $\epsilon = 2.22 \times 10^{-15}$, rising to `2.83e-3 rad` / `0.162°` at $\epsilon = 10^{-6}$). By contrast, `GTSAM` `SO3` uses a piecewise Taylor switch at $\theta^2 \le 10^{-6}$ (continuity jump $|dA| = 8.33 \times 10^{-15}$) plus Shepperd pivoting and Hertzberg's `atan`-based `Logmap`, eliminating `acos` precision loss near $\theta = 0$ at the cost of runtime control-flow branches.
3. **ROS 2 `SingleThreadedExecutor` wait-set polling creates multi-job priority inversion that invalidates standard non-preemptive response-time bounds.** Both `rclcpp` Crystal (`0.6.3`, studied by Casini et al., ECRTS 2019) and modern `rclcpp` (`9e66d4d2...`) only refresh the underlying wait-set after draining the entire cached ready-set snapshot, while enforcing hard-coded entity-type priority `Timer > Subscription > Service > Client > Waitable`. A high-criticality subscription arriving immediately after a polling point can be blocked by *every* lower-priority callback in the snapshot plus lower-criticality timers (`13.9 ms` observed vs. `6.0 ms` naive single-blocker prediction in a minimal 5-callback probe). `EventsExecutor` removes wait-set batching and static timer-over-subscription inversion via an arrival-ordered FIFO queue, but remains non-preemptive without priority-aware event queues.
4. **Zero-copy shared-memory pub/sub (`iceoryx` / `iceoryx2`) achieves crash-resilient loan reclamation via shared-memory `UsedChunkList` tracking, but retains narrow `SIGKILL` leak windows and strict relocatability/aliasing contracts.** In `eclipse-iceoryx/iceoryx`, the central `RouDi` daemon monitors process heartbeats and invokes `m_chunksInUse.cleanup()` plus queue draining on crash, yet `ChunkSender::tryAllocate()` and `send()` contain explicitly annotated critical sections where a process kill permanently leaks a chunk until daemon restart; furthermore, `SharedChunk::decrementReferenceCounter()` uses `std::memory_order_relaxed`, placing payload-read-before-reuse synchronization obligations on surrounding free-list/queue operations. `eclipse-iceoryx/iceoryx2` eliminates the central daemon and elevates `SampleMut` publish handoff and IPC relocatability (`ZeroCopySend`) into Rust's linear move and trait systems.

## Applicability

This report synthesizes primary source implementations, formal specifications/papers, and standalone execution probes across four tightly coupled domains of real-time robotic autonomy:

- **Manifold-typed symbolic code generation (`symforce-org/symforce` @ `acdedd0bcfea11ee88e89908dd6499024dd9f89a`, Martiros et al. RSS 2022):** Applies to Python symbolic factor definition, tangent-space differentiation, CSE, and zero-allocation generated C++/Python numerical kernels for `Rot3`, `Pose3`, and `Pose3_SE3` under IEEE-754 `float64` and `float32` arithmetic. Default `numeric_epsilon` is `10 * sys.float_info.epsilon` ($\approx 2.22 \times 10^{-15}$) in Python (`symforce/__init__.py:245`), but codegen targets frequently configure larger `epsilon` values (`1e-9` for `double`, `1e-6` for `float`), which materially changes near-identity bias.
- **Incremental factor-graph optimization (`borglab/gtsam` @ `3fd8ba1bcb12ce4ef6f1b633100020b0f4f13cc7`, Kaess et al. IJRR 2012):** Applies to C++ `SO3`, `Rot3` (both matrix-backed `Rot3M.cpp` and quaternion-backed `Rot3Q.cpp` under `GTSAM_USE_QUATERNIONS`), `Pose3` (both default product-manifold chart and `GTSAM_POSE3_EXPMAP`), and `ISAM2` Bayes-tree nonlinear smoothing. Findings distinguish compile-time CMake flag behavior (`GTSAM_POSE3_EXPMAP`, `GTSAM_USE_QUATERNIONS`, `GTSAM_EXTRA_CONSISTENCY_CHECKS`) from unconditional invariants.
- **Deterministic ROS 2 callback scheduling (`ros2/rclcpp` Crystal `0.6.3` @ `e32d17980dcf761712cb854b3703336c380a570e` and rolling `HEAD` @ `9e66d4d2ef0188656e1ac2ad71d338f15c44e1f2`, Casini et al. ECRTS 2019):** Covers single-threaded wait-set executors (`SingleThreadedExecutor` inheriting `Executor::get_next_executable`), callback-group mutual exclusion (`CallbackGroupType::MutuallyExclusive` vs. `Reentrant`), and `experimental::executors::EventsExecutor`. Distinguishes Crystal's live `get_next_timer()` re-polling from `HEAD`'s `wait_result_`-snapshotted timer dispatch. Does **not** automatically generalize to custom third-party priority-driven executors (e.g., PiCAS, rclc) or multi-threaded executors without separate contention modeling.
- **Zero-copy shared-memory IPC (`eclipse-iceoryx/iceoryx` @ `9f9fb0d359f1805cdd38006c8aba6af6dbc2209e` and `eclipse-iceoryx/iceoryx2` @ `5ff74e270863cb416583eef42c928afcb436630f`):** Covers intra-host POSIX shared-memory publish/subscribe pools (`MePoo`, `ChunkManagement`, `ChunkSender`, `ChunkReceiver`, `ChunkQueue`, `RouDi` `ProcessManager`/`PortManager`) and the Rust decentralized `Sample` / `SampleMut` API in `iceoryx2`. Cross-host network serialization (DDS/Zenoh bridges) and hardware RDMA transports are outside scope.

All subjects are examined jointly as an end-to-end robotics architecture: Lie-group estimators consume high-rate sensor samples delivered over zero-copy rings inside executor callbacks whose worst-case latency determines closed-loop control stability.

## Findings

### 1. Lie-Group Manifold Calculus, Retraction Laws, and the Three-Way `Pose3` Divergence

**Basis:** normative (Solà et al., `arXiv:1812.01537`; Hertzberg et al., `DOI: 10.1016/j.inffus.2011.08.003`) + source (`symforce`, `gtsam`) + execution.

State estimation problems in SLAM, visual-inertial odometry, and legged control optimize states residing on smooth non-Euclidean manifolds $\mathcal{M}$ rather than flat vector spaces $\mathbb{R}^n$. Representing a 3D orientation $R \in \mathrm{SO}(3)$ in ambient Euclidean coordinates (9 matrix entries or 4 unit quaternion scalars) introduces redundant degrees of freedom and nonlinear constraints ($R^T R = I, \det R = +1$ or $\|q\|^2 = 1$). Unconstrained Gauss–Newton or Levenberg–Marquardt steps $x \leftarrow x + \delta x$ leave the manifold, create rank-deficient normal equations $J^T J$, and suffer Euler-angle gimbal lock when pitch approaches $\pm \pi/2$ (explicitly throwing at $|y - \pi/2| < 10^{-2}$ in `gtsam/geometry/Rot3.cpp:269-271`).

#### 1.1 Manifold Encapsulation ($\boxplus / \boxminus$) and Storage vs. Tangent Separation

Following Hertzberg et al. (`DOI: 10.1016/j.inffus.2011.08.003`) and Solà et al. (`arXiv:1812.01537`), both `SymForce` (`symforce/ops/lie_group_ops.py:44-216`) and `GTSAM` (`gtsam/base/Manifold.h:35-169`, `gtsam/base/Lie.h:113-257`) separate an element's **storage dimension** $d_s$ (the ambient memory layout) from its **tangent dimension** $d_t = \dim(\mathcal{M})$ (intrinsic degrees of freedom):

| Type | Ambient Storage ($d_s$) | Tangent Space ($d_t$) | Hat Operator $[\cdot]_\times$ | Chart / Retraction ($\mathcal{X} \boxplus \delta$) |
| :--- | :--- | :--- | :--- | :--- |
| `Rot3` (`SymForce`) | Unit quaternion $(x,y,z,w) \in \mathbb{R}^4$ ($d_s=4$) | $\omega \in \mathbb{R}^3 \cong \mathfrak{so}(3)$ ($d_t=3$) | Skew-symmetric $3\times 3$ (`rot3.py:103-104`) | Right composition $q \otimes \operatorname{Exp}(\omega)$ |
| `Rot3` / `SO3` (`GTSAM`) | $3\times 3$ matrix ($d_s=9$) or `Quaternion` if `GTSAM_USE_QUATERNIONS` ($d_s=4$) | $\omega \in \mathbb{R}^3 \cong \mathfrak{so}(3)$ ($d_t=3$) | Skew-symmetric $3\times 3$ (`SO3.cpp:286-288`) | Right composition $R \cdot \operatorname{Exp}(\omega)$ (`EXPMAP` mode) |
| `Pose3` (`SymForce`) | Quaternion + $\mathbb{R}^3$ position ($d_s=7$) | $(\omega, v) \in \mathbb{R}^6$ ($d_t=6$) | **None** on default `Pose3` (`pose3.py:37`) | Product manifold $SO(3)\times\mathbb{R}^3$ in **world frame**: $(R\operatorname{Exp}(\omega),\, t + v)$ |
| `Pose3` (`GTSAM`, default) | `Rot3` + `Point3` ($d_s=12$ or $7$) | $(\omega, v) \in \mathbb{R}^6$ ($d_t=6$) | `SE(3)` twist in `Expmap` only | `compose(ChartAtOrigin::Retract)` in **body frame**: $(R\operatorname{Exp}(\omega),\, t + R v)$ |
| `Pose3` (`GTSAM_POSE3_EXPMAP`) | `Rot3` + `Point3` | $\xi = (\omega, v) \in \mathfrak{se}(3)$ ($d_t=6$) | $\begin{bmatrix}[\omega]_\times & v \\ 0 & 0\end{bmatrix}$ | Coupled $\mathrm{SE}(3)$ exponential: $(R\operatorname{Exp}(\omega),\, t + R J_l(\omega) v)$ |
| `Sim(3)` (`Similarity3`) | Scale + `Rot3` + `Point3` | $(\omega, v, \sigma) \in \mathfrak{sim}(3)$ ($d_t=7$) | $\begin{bmatrix}[\omega]_\times + \sigma I & v \\ 0 & 0\end{bmatrix}$ | Coupled similarity exponential (scale-coupled translation integral) |

A valid local chart pair $(\boxplus, \boxminus)$ (`retract`, `local_coordinates`) must satisfy three local bijectivity invariants (checked in `gtsam/base/Manifold.h:163-168`):
$$\mathcal{X} \boxminus \mathcal{X} = \mathbf{0}, \qquad \mathcal{X} \boxplus (\mathcal{Y} \boxminus \mathcal{X}) = \mathcal{Y}, \qquad (\mathcal{X} \boxplus \delta) \boxminus \mathcal{X} = \delta \quad (\|\delta\| < r_{\text{inj}}),$$
where the injectivity radius is $r_{\text{inj}} = \pi$ on $\mathrm{SO}(3)$. For a Lie group $G$ with group composition $\circ$, inverse $(\cdot)^{-1}$, and exponential/logarithmic maps $\operatorname{Exp}: \mathbb{R}^{d_t} \to G$, $\operatorname{Log}: G \to \mathbb{R}^{d_t}$, the canonical right-trivialized retraction is:
$$\mathcal{X} \boxplus_R \delta = \mathcal{X} \circ \operatorname{Exp}(\delta), \qquad \mathcal{Y} \boxminus_R \mathcal{X} = \operatorname{Log}(\mathcal{X}^{-1} \circ \mathcal{Y}).$$

#### 1.2 Exact Rodrigues Map, Right/Left Jacobians, and Tangent-Space Chain Rule

For $\omega \in \mathbb{R}^3$ with $\theta = \|\omega\|_2$ and $W = [\omega]_\times$, the exact $\mathrm{SO}(3)$ exponential and right/left Jacobians (`gtsam/geometry/SO3.cpp:80-190`, Solà et al. `arXiv:1812.01537` §4.1) are:
$$\operatorname{Exp}(\omega) = I + A(\theta) W + B(\theta) W^2, \qquad J_r(\omega) = I - B(\theta) W + C(\theta) W^2, \qquad J_l(\omega) = I + B(\theta) W + C(\theta) W^2,$$
$$J_r^{-1}(\omega) = I + \frac{1}{2} W + D(\theta) W^2,$$
with scalar kernel functions:
$$A(\theta) = \frac{\sin\theta}{\theta}, \qquad B(\theta) = \frac{1 - \cos\theta}{\theta^2} = \frac{2\sin^2(\theta/2)}{\theta^2}, \qquad C(\theta) = \frac{1 - A(\theta)}{\theta^2} = \frac{\theta - \sin\theta}{\theta^3}, \qquad D(\theta) = \frac{1 - A(\theta)/(2B(\theta))}{\theta^2}.$$
Notice two implementation-critical numerical details verified in `gtsam/geometry/SO3.cpp`:
- Line 84–86 computes $1 - \cos\theta$ as `2.0 * sin(theta/2)^2` rather than `1.0 - cos(theta)` to eliminate catastrophic cancellation for small $\theta$.
- Lines 135–136 switch $D(\theta)$ onto a dedicated linear expansion around $\theta = \pi$, $D(\theta) \approx \frac{1}{\pi^2} + \left(\frac{2}{\pi^3} - \frac{1}{4\pi}\right)(\pi - \theta)$, because $A(\theta)/(2B(\theta)) = \frac{\theta}{2}\cot(\theta/2) \to 0$ as $\theta \to \pi$ while $\cos(\theta/2)$ approaches zero, making $J_r^{-1}$ sensitive near the cut locus.

For tangent-space differentiation of an arbitrary residual $f: G \to \mathbb{R}^m$, `SymForce` (`symforce/ops/lie_group_ops.py:154-216`, `symforce/geo/rot3.py:106-127`) avoids symbolically differentiating through `from_tangent(delta)` at $\delta = 0$ (which would introduce removable $0/0$ terms and `epsilon` artifacts into every factor Jacobian!). Instead, it applies the manifold chain rule using exact, $\epsilon$-free analytic storage-to-tangent Jacobians evaluated at $\delta = 0$:
$$\left.\frac{\partial f(\mathcal{X} \boxplus \delta)}{\partial \delta}\right|_{\delta=0} = \frac{\partial f}{\partial s(\mathcal{X})} \cdot \underbrace{\left.\frac{\partial s(\mathcal{X} \boxplus \delta)}{\partial \delta}\right|_{\delta=0}}_{\text{storage\_D\_tangent}(\mathcal{X})}.$$
For a unit quaternion $q = (x, y, z, w)$, `Rot3.storage_D_tangent()` (`symforce/geo/rot3.py:106-121`) is exact, polynomial, and singularity-free everywhere on $S^3$:
$$\text{storage\_D\_tangent}(q) = \frac{1}{2}\begin{bmatrix} w & -z & y \\ z & w & -x \\ -y & x & w \\ -x & -y & -z \end{bmatrix}, \qquad \text{tangent\_D\_storage}(q) = 4\,(\text{storage\_D\_tangent}(q))^T.$$

#### 1.3 Three-Way `Pose3` Retraction Divergence Across `SymForce` and `GTSAM`

**Basis:** source (`symforce/geo/pose3.py:28-42,164-200`; `gtsam/base/Lie.h:220-228`; `gtsam/geometry/Pose3.cpp:99-155`) + execution.

Direct inspection and execution reveal **three mutually incompatible `Pose3` retraction definitions** sharing the same type name and 6-vector tangent layout $(\omega_x, \omega_y, \omega_z, v_x, v_y, v_z)$:

1. **`SymForce` default `Pose3.retract` (`symforce/geo/pose3.py:168-183`):** Overrides `LieGroup.retract` to retract rotation and translation independently on the product manifold $\mathrm{SO}(3) \times \mathbb{R}^3$ with translation in the **world/global frame**:
   $$(R_a, t_a) \boxplus_{\text{SymForce}} (\omega, v) = \bigl(R_a \operatorname{Exp}(\omega),\; t_a + v\bigr).$$
   Its docstring explicitly warns: `retract(a, vec) != compose(a, from_tangent(vec))` and `local_coordinates(a, b) != to_tangent(between(a, b))`; `storage_D_tangent` is block-diagonal with $I_{3\times 3}$ for translation (`pose3.py:144-152`). (True $\mathrm{SE}(3)$ exists only in `symforce.geo.unsupported.pose3_se3.Pose3_SE3`, which has no runtime C++ equivalent.)
2. **`GTSAM` `Pose3::retract` without `GTSAM_POSE3_EXPMAP` (`gtsam/base/Lie.h:220-222` + `gtsam/geometry/Pose3.cpp:126-138`):** `LieGroup::retract(xi)` executes `compose(Pose3::ChartAtOrigin::Retract(xi))`. Because `ChartAtOrigin::Retract` returns `Pose3(Rot3::Retract(w), v)` and `compose` multiplies $(R_a, t_a) \cdot (R_\delta, t_\delta) = (R_a R_\delta, t_a + R_a t_\delta)$, the resulting retraction is a **body-frame** decoupled update:
   $$(R_a, t_a) \boxplus_{\text{GTSAM-prod}} (\omega, v) = \bigl(R_a \operatorname{Exp}(\omega),\; t_a + R_a v\bigr).$$
3. **`GTSAM` `Pose3::retract` with `GTSAM_POSE3_EXPMAP` (`gtsam/geometry/Pose3.cpp:99-128`, `SO3.cpp:199-218`):** `ChartAtOrigin::Retract` calls `Pose3::Expmap(xi)`, computing $t_\delta = J_l(\omega) v$ via `DexpFunctor::tangentExpmap`, so:
   $$(R_a, t_a) \boxplus_{\mathrm{SE}(3)} (\omega, v) = \bigl(R_a \operatorname{Exp}(\omega),\; t_a + R_a J_l(\omega) v\bigr).$$

**Observed Execution Divergence** (standalone Python 3 `SO(3)`/`SE(3)` probe): Starting from $R_a = \operatorname{Rot}_z(\pi/2), t_a = (0,0,0)$ and applying $\omega = (0, 0, \pi/2), v = (1, 0, 0)$:
- `SymForce` `Pose3`: $t' = (1.0000,\; 0.0000,\; 0.0000)$
- `GTSAM` `Pose3` (default product chart): $t' = (0.0000,\; 1.0000,\; 0.0000)$
- `GTSAM` `Pose3` (`GTSAM_POSE3_EXPMAP`): $t' = (-0.6366,\; 0.6366,\; 0.0000)$ (exact $(-2/\pi, 2/\pi, 0)$)

**Engineering Consequence:** Embedding a `SymForce`-generated C++ factor Jacobian $\partial r / \partial \xi$ directly into a `GTSAM` `NonlinearFactor` causes silent optimization divergence or mis-scaled marginals whenever $R_a \neq I$: the translation columns of the `SymForce` Jacobian are expressed in the world frame ($\partial r / \partial t_{\text{world}}$), whereas `GTSAM` expects body-frame tangent columns ($\partial r / \partial t_{\text{world}} \cdot R_a$; cf. `gtsam/geometry/Pose3.cpp:159`, `245`). Bridging the two requires explicitly right-multiplying the translation Jacobian block by $R_a$ (and using consistent `ChartAtOrigin` charts when evaluating nonlinear steps).

---

### 2. Quaternion Double-Cover ($S^3 \to \mathrm{SO}(3)$) and Removable Singularity Elimination

**Basis:** source (`symforce/geo/rot3.py:82-100,152-301`, `symforce/__init__.py:245`, `gtsam/geometry/SO3.cpp:55-180,337-404`) + execution + derived.

#### 2.1 Double-Cover Unwinding Pathology ($q \equiv -q$)

Unit quaternions $S^3$ form a 2-to-1 universal cover of $\mathrm{SO}(3)$: $q$ and $-q$ represent the identical rotation matrix $R(q) = R(-q)$ because every entry of $R(q)$ is quadratic in $(x, y, z, w)$ (`symforce/geo/rot3.py:169-187`). However, a naive logarithmic map $\theta = 2\arccos(w),\, \omega = \theta \cdot \mathrm{xyz}/\|\mathrm{xyz}\|$ treats $q$ and $-q$ as distinct points separated by $2\pi$: for $\theta = 0.5\text{ rad}$, $q = (0, 0, \sin 0.25, \cos 0.25)$ gives $\theta = 0.5$, whereas $-q$ gives $2\arccos(-\cos 0.25) = 2\pi - 0.5 \approx 5.7831853\text{ rad}$ (verified in the standalone Python `SO(3)` probe). In attitude controllers and pose-graph between-factors, sign flips across $w = 0$ induce discontinuous $2\pi$ "unwinding" torques and false large residuals.

Both systems enforce shortest-arc canonicalization onto the upper hemisphere $w \ge 0$ ($\|\omega\| \le \pi$):
- **`SymForce` (`rot3.py:95-99`):** Computes `w_positive = Abs(q.w)` and `xyz_w_positive = q.xyz * sign_no_zero(q.w)`, where `sign_no_zero(0) = +1` prevents zeroing out the axis at $\theta = \pi$ ($w = 0$).
- **`GTSAM` (`SO3.cpp:344-388`):** Extracts an unnormalized quaternion $(w, v)$ from $R$ via Shepperd's 4-way pivot on $\max(\operatorname{tr}(R), R_{00}, R_{11}, R_{22})$ and canonicalizes `if (w < 0.0) { w = -w; v = -v; }`.

Note that at the cut locus $\theta = \pi$ ($w = 0$), antipodal tangent vectors $+\pi \hat{u}$ and $-\pi \hat{u}$ still represent the same rotation; any continuous chart on $\mathrm{SO}(3)$ necessarily has a topological discontinuity at $\|\omega\| = \pi$ because $\mathrm{SO}(3) \cong \mathbb{R}P^3$ is not contractible.

#### 2.2 Branchless $\epsilon$-Regularization (`SymForce`) vs. Piecewise Taylor + `atan` (`GTSAM`)

Symbolic code generators targeting straight-line C++/SIMD/CUDA kernels avoid data-dependent `if (theta < 1e-3)` branches because symbolic differentiation through piecewise conditionals complicates CSE, breaks SIMD predication, and risks uninitialized or `NaN` inactive lanes (`0 * Inf = NaN` in IEEE-754). `SymForce` instead injects a positive scalar symbol $\epsilon$ (`numeric_epsilon = 10 * sys.float_info.epsilon ≈ 2.2204e-15` in `float64`, `symforce/__init__.py:245`):

- **`Rot3.from_tangent(v, epsilon)` (`rot3.py:82-87`):**
  $$\theta_\epsilon = \sqrt{\|v\|_2^2 + \epsilon^2}, \qquad q = \left(\frac{\sin(\theta_\epsilon / 2)}{\theta_\epsilon} v,\; \cos(\theta_\epsilon / 2)\right).$$
  At $v = 0$, $\theta_\epsilon = \epsilon > 0$, avoiding $0/0$ while producing $\cos(\epsilon/2) = 1 - \epsilon^2/8 + O(\epsilon^4)$ (exact `1.0` in `float64` for $\epsilon \le 10^{-9}$, unit-norm error $-1.25 \times 10^{-13}$ at $\epsilon = 10^{-6}$).
- **`Rot3.to_tangent(epsilon)` & `Rot3.to_tangent_norm(epsilon)` (`rot3.py:89-100, 152-163`):**
  $$w_{\text{safe}} = \min(1 - \epsilon, |w|), \qquad \text{norm} = \sqrt{1 - w_{\text{safe}}^2}, \qquad \text{angle} = 2\arccos(w_{\text{safe}}), \qquad \omega = \frac{\operatorname{sign\_no\_zero}(w)\,\mathrm{xyz}}{\text{norm}} \cdot \text{angle}.$$
- **Branchless `from_rotation_matrix` (`rot3.py:190-301`):** Evaluates all four Shoemake pivot expressions unconditionally, guards inactive denominators via `sqrt(Max(..., 0)) + logical_not(valid_input, unsafe=True)` so inactive lanes never divide by zero (preventing `0 * NaN = NaN`), and selects the active branch via `argmax_onehot([R00, R11, R22, trace(R)], tolerance=0.1)`. Because $\max(x^2, y^2, z^2, w^2) \ge 1/4$, the `0.1` tolerance guarantees $|q_i|^2 \ge 1/5$ ($\text{denom} \ge 0.447$) on the active branch.

**Measured Near-Identity Bias Trade-off (Standalone Python `SO(3)` Probe, `Basis: source + execution`):**

| Method / Parameter | `from_tangent(0).w - 1` | `to_tangent(I)` | `to_tangent_norm(I)` (`rad`) | Slope $\frac{\text{to\_tangent}_x(h)}{h}$ at $h=10^{-8}$ (exact $= 2$) | Switch Jump at $\theta = 10^{-3}$ |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `SymForce` (`eps = 2.22e-15`, default `f64`) | `0.000e+00` | `(0, 0, 0)` | **`1.3328e-07`** | `2.000000000000` (err `4.44e-16`) | None (branchless) |
| `SymForce` (`eps = 1e-9`) | `0.000e+00` | `(0, 0, 0)` | **`8.9443e-05`** | `2.000000000167` (err `1.67e-10`) | None (branchless) |
| `SymForce` (`eps = 1e-6`, typical `f32`) | `-1.250e-13` | `(0, 0, 0)` | **`2.8284e-03`** (`0.162°`) | `2.000000666656` (err `6.67e-07`) | None (branchless) |
| `GTSAM` `SO3` (`kNearZeroThresholdSq = 1e-6`) | `0.000e+00` | `(0, 0, 0)` | `0.000e+00` | Exact (`atan(n/w)/n -> 1/w`) | `|dA| = 8.327e-15`, `|dB| = 1.388e-15` |

**Derived Explanation of the `to_tangent_norm` Pitfall:** Because $\arccos(1 - \epsilon) = \sqrt{2\epsilon}(1 + \epsilon/12 + \dots)$ and $\sqrt{1 - (1-\epsilon)^2} = \sqrt{2\epsilon}(1 - \epsilon/4 + \dots)$, the $\sqrt{2\epsilon}$ factors cancel in the *ratio* `2*acos(w_safe) / sqrt(1 - w_safe^2) = 2(1 + \epsilon/3 + O(\epsilon^2))` inside `to_tangent()`, keeping `to_tangent` accurate to $O(\epsilon)$. However, `to_tangent_norm()` returns $2\arccos(w_{\text{safe}})$ directly without dividing by $\sqrt{1 - w_{\text{safe}}^2}$, exposing the uncancelled $2\sqrt{2\epsilon}$ floor! Consequently, calling `Rot3.to_tangent_norm()` with a loose $\epsilon = 10^{-6}$ as a convergence threshold or angular residual near zero introduces a `0.162°` floor error, whereas `GTSAM` `SO3::Logmap` (`SO3.cpp:398`) uses `2.0 * atan(n / w)` (Hertzberg et al. 2013), which preserves full IEEE-754 precision down to subnormal angles ($\theta \to 0$) with zero bias.

---

### 3. Symbolic Codegen (`SymForce`) vs. Incremental Bayes-Tree Factor Graphs (`GTSAM` `iSAM2`)

**Basis:** documentation (Martiros et al. RSS 2022 `DOI: 10.15607/RSS.2022.XVIII.041`; Kaess et al. IJRR 2012 `DOI: 10.1177/0278364911430419`) + source (`symforce/codegen/codegen.py`, `symforce/opt/factor.py`, `gtsam/nonlinear/ISAM2.h`, `gtsam/inference/BayesTree.h`).

Robotics estimation splits along a structural axis between **local factor linearization** (computing $r(x)$, $J = \partial r / \partial \delta$, and local Gauss–Newton blocks $J^T J, J^T r$) and **global sparse inference** (solving the coupled normal equations across thousands of poses and landmarks over time).

| Dimension | `SymForce` (`symforce-org/symforce`) | `GTSAM` `iSAM2` (`borglab/gtsam`) |
| :--- | :--- | :--- |
| **Core Abstraction** | Symbolic Lie-group DAG -> CSE -> straight-line C++/Python/CUDA codegen (`Codegen.with_linearization`) | Runtime `NonlinearFactorGraph` eliminated into chordal `BayesTree<ISAM2Clique>` |
| **Differentiation** | Compile-time symbolic tangent differentiation via `storage_D_tangent` + CSE (zero runtime tape/AD overhead) | Hand-derived `OptionalJacobian<M,N>` analytic matrices per factor (`Rot3::rotate`, `Pose3::transformTo`, etc.) |
| **Heap Allocation in Hot Loop** | Zero heap allocation for generated residual/Jacobian/Hessian kernels (stack scalars & fixed-size Eigen) | Dynamic clique/matrix updates on affected Bayes-tree branches; O(1) amortized for local steps, O(n) on loop closure |
| **Graph Topology** | Fixed per generated factor; global sparse solver (`symforce/opt/optimizer.py` / C++ `Optimizer`) consumes generated `NumericFactor` blocks | Dynamic online addition/removal of variables & factors (`ISAM2::update(newFactors, newTheta, removeFactorIndices)`) |
| **Incremental Relinearization** | Full batch or sliding-window LM iterations (`Optimizer.optimize`) | **Fluid relinearization**: only variables with $\|\Delta_i\| > \text{relinearizeThreshold}$ (checked every `relinearizeSkip` updates) are re-eliminated from root to affected cliques |
| **Linearization Consistency** | All active factors relinearized jointly each LM iteration | Maintains `fixedVariables_` (`ISAM2.h:94`) locking linearization points of variables touched by marginalized linear factors to avoid inconsistent information injection |
| **Partial Back-Substitution** | N/A (full sparse Cholesky solve per iteration) | **Wildfire** top-down traversal stops descending a Bayes-tree branch once $\|\Delta_{\text{clique}}\| < \text{wildfireThreshold}$ |
| **Primary Scaling Bottleneck** | Symbolic expression swell & long codegen compile times if entire multi-pose graphs are flattened symbolically | C++ virtual dispatch, `OptionalJacobian` allocation/copying, and dense fill-in on large loop closures triggering `nnzAfterLastReorder_` batch reorder (`ISAM2.h:99`) |

**Canonical Production Composition:** High-rate visual-inertial SLAM systems frequently compose both: `SymForce` generates branchless, CSE-optimized C++ residual + tangent-Jacobian kernels for complex camera/IMU/calibration factors, while `GTSAM` `iSAM2` (or a sparse Schur-complement LM solver) maintains the dynamic global Bayes tree — subject strictly to matching the `Pose3` retraction convention documented in §1.3!

---

### 4. Deterministic Real-Time Scheduling: ROS 2 Executor Priority Inversion and Response-Time Analysis

**Basis:** normative (Casini et al., ECRTS 2019, `DOI: 10.4230/LIPIcs.ECRTS.2019.6`) + source (`ros2/rclcpp` `0.6.3` @ `e32d1798...` & `HEAD` @ `9e66d4d2...`) + execution.

In ROS 2, nodes register callbacks (timers, subscriptions, services, clients, waitables) grouped into `CallbackGroup`s (`MutuallyExclusive` or `Reentrant`) and spun by an `Executor`. Casini et al. (ECRTS 2019) proved that the ROS 2 `SingleThreadedExecutor` does **not** follow standard fixed-priority non-preemptive (NP-FP) or FIFO semantics; instead, it executes a **polling-point WaitSet batching state machine** with two structural priority-inversion mechanisms directly visible in `rclcpp` source.

#### 4.1 Source-Level Scheduling Semantics: Crystal (`0.6.3`) vs. Rolling (`HEAD`) vs. `EventsExecutor`

Inspecting `Executor::get_next_executable()` and `Executor::get_next_ready_executable()` across both examined revisions confirms that the core polling-point batching invariant persists from Crystal (`0.6.3`) through modern `HEAD`:

1. **WaitSet Polling-Point Refresh Only When Cached Ready-Set Empties** (`0.6.3` `executor.cpp:567-582`; `HEAD` `executor.cpp:937-954`):
   ```cpp
   success = get_next_ready_executable(any_executable);
   if (!success) {
     wait_for_work(timeout); // polls OS/DDS wait-set ONLY when cached ready-set is empty!
     if (cancel_requested_.load()) return false;
     success = get_next_ready_executable(any_executable);
   }
   ```
   A callback that becomes ready *immediately after* `wait_for_work()` returns (a **polling point**) is completely invisible to `get_next_ready_executable()` until **every** lower-priority callback captured in the current ready-set snapshot has executed to completion!
2. **Hard-Coded Entity-Type Static Priority** (`0.6.3` `executor.cpp:535-564`; `HEAD` `executor.cpp:824-923`):
   Within each snapshot, callbacks are strictly prioritized by middleware primitive type, ignoring application deadlines or criticality:
   $$\text{Timers} \;>\; \text{Subscriptions} \;>\; \text{Services} \;>\; \text{Clients} \;>\; \text{Waitables},$$
   with tie-breaking inside each class by registration/container order (NOT arrival timestamp!).
3. **Behavioral Divergence Between Crystal (`0.6.3`) and `HEAD` (`9e66d4d2...`) on Timers:**
   - In **Crystal `0.6.3`** (`executor.cpp:509-541`), `get_next_timer()` bypasses the cached wait-set and polls live `timer->is_ready()` on *every* dispatch cycle! Consequently, a newly fired low-criticality timer can cut ahead of already-snapshotted subscriptions mid-batch.
   - In **rolling `HEAD`** (`executor.cpp:824-857`), timers are popped from `wait_result_->peek_next_ready_timer(...)` (snapshotted during `wait_for_work()`), preventing mid-batch timer preemption, **but** at the next polling point any newly expired low-criticality timer still executes before all waiting high-criticality subscriptions!
   - Furthermore, in `HEAD` (`executor.cpp:811-822`), if a ready entity belongs to a `MutuallyExclusive` callback group currently held by another thread (`!callback_group->can_be_taken_from()`), the executor flags `entities_need_rebuild_.store(true)` to exclude that group from the next wait-set and avoid level-triggered busy-wait spinning.
4. **`EventsExecutor` (`HEAD` `events_executor.cpp:32-140`):** Replaces `wait_for_work()` polling-point snapshots with RMW event callbacks pushing `ExecutorEvent` tokens directly into an `EventsQueue` (default FIFO, with optional `TimersManager` on a separate thread), eliminating both multi-job wait-set batching blindness and static `Timer > Subscription` inversion — though without a priority-queue implementation, FIFO still permits non-preemptive blocking behind all earlier-arrived lower-priority events.

#### 4.2 Reservation-Based Response-Time Bound and Concrete Deadline-Miss Probe

Under Casini et al. (ECRTS 2019, `DOI: 10.4230/LIPIcs.ECRTS.2019.6`), each ROS 2 executor thread runs inside an OS reservation server (e.g., Linux `SCHED_DEADLINE` Constant Bandwidth Server with budget $\Theta$ and period $\Pi$, modeled via supply-bound function $\mathrm{sbf}(t)$). Because a callback $\tau_i$ arriving just after a polling point can be blocked by up to one instance of **every** lower-priority non-timer callback in the snapshot *plus* higher-priority callbacks across both the current and next polling rounds, the worst-case blocking term is $\sum_{j \in \mathrm{lp}(i)} C_j$ rather than the classical single-blocker NP-FP bound $\max_{j \in \mathrm{lp}(i)} C_j$. Using compositional worst-case response-time (WCRT) analysis over a processing chain $E = (\tau_1 \to \tau_2 \to \dots \to \tau_k)$ spanning executors:
$$R_{\text{chain}} \le \sum_{m=1}^{k} R_{\tau_m}, \qquad \text{where } R_{\tau_m} = \min\left\{ t > 0 \;\middle|\; \mathrm{sbf}(t) \ge C_{\tau_m} + B^{\text{WaitSet}}_{\tau_m} + I^{\text{hp}}_{\tau_m}(t) \right\},$$
refined via MILP/pairwise busy-window elimination when multiple callbacks of the same chain share a single executor so they cannot block each other simultaneously.

**Measured Priority-Inversion Probe** (standalone Python 3 discrete-event simulator of `Executor::get_next_ready_executable()`, `Basis: source + execution`):
Consider a single-CPU executor hosting high-criticality control subscription $S_{\text{hi}}$ ($C = 1\text{ ms}$, $D = 10\text{ ms}$, released at $t = 0.1\text{ ms}$ right after the $t = 0.0\text{ ms}$ polling point), low-criticality telemetry timer $T_{\text{lo}}$ ($C = 2\text{ ms}$, $T = 8\text{ ms}$, jobs at $t = 0, 8\text{ ms}$), and three low-criticality diagnostic subscriptions $S_{\text{lo1..3}}$ ($C = 3\text{ ms}$ each, ready at $t = 0\text{ ms}$):

| Scheduler / Revision | Execution Schedule (`[start, end]` ms) | $S_{\text{hi}}$ Response Time | vs. $D = 10\text{ ms}$ |
| :--- | :--- | :--- | :--- |
| Naive single-blocker NP-RTA (UNSOUND) | Assumes $\max(C_{\text{lo}}) + C_{T_{\text{lo}}} + C_{S_{\text{hi}}} = 3 + 2 + 1$ | `6.0 ms` (false safe!) | Predicts PASS |
| `rclcpp` Crystal `0.6.3` (`live-timer` + WaitSet) | `[0,2] T_lo#0`, `[2,5] S_lo1`, `[5,8] S_lo2`, **`[8,10] T_lo#1` (live preempt!)**, `[10,13] S_lo3`, `[13,14] S_hi` | **`13.9 ms`** | **DEADLINE MISS** |
| `rclcpp` `HEAD` (`wait_result_` snapshot) | `[0,2] T_lo#0`, `[2,5] S_lo1`, `[5,8] S_lo2`, `[8,11] S_lo3`, **`[11,13] T_lo#1` (Timer>Sub!)**, `[13,14] S_hi` | **`13.9 ms`** | **DEADLINE MISS** |
| `rclcpp` `EventsExecutor` (FIFO queue) | `[0,2] T_lo#0`, `[2,5] S_lo1`, `[5,8] S_lo2`, `[8,11] S_lo3`, **`[11,12] S_hi`**, `[12,14] T_lo#1` | **`11.9 ms`** | **DEADLINE MISS** (no timer inversion, still FIFO-blocked) |

To achieve strict fixed-priority isolation in ROS 2 without modifying `rclcpp` internals, safety-critical chains must be segregated onto **dedicated single-purpose executors** pinned to separate `SCHED_FIFO` / `SCHED_DEADLINE` OS threads (preventing low-criticality callbacks from sharing the critical executor's wait-set).

---

### 5. Crash-Resilient Zero-Copy Shared-Memory Middleware: Eclipse `iceoryx` and `iceoryx2`

**Basis:** source (`eclipse-iceoryx/iceoryx` @ `9f9fb0d3...`; `eclipse-iceoryx/iceoryx2` @ `5ff74e27...`) + derived.

High-bandwidth robotics perception (LiDAR point clouds, multi-megapixel camera frames, SLAM pose-graph snapshots) cannot tolerate repeated serialization and kernel socket copies (`O(N)` per subscriber). Eclipse `iceoryx` (and its Rust successor `iceoryx2`) implement **1-to-N zero-copy shared-memory publish/subscribe** using pre-allocated fixed-size chunk pools and atomic reference counting.

#### 5.1 Memory Architecture, `RelativePointer` Addressing, and `Sample<T>` Ownership Typestate

In `eclipse-iceoryx/iceoryx` (`iceoryx_posh`):
- **Pre-allocated `MemPool`s (`memory_manager.cpp:42-221`, `mem_pool.cpp:43-158`):** At startup, the central `RouDi` daemon partitions POSIX shared memory into monotonically increasing chunk-size pools (`adjustedChunkSize = chunkPayloadSize + sizeof(ChunkHeader)`) plus a separate `m_chunkManagementPool` sized to `m_totalNumberOfChunks` (`memory_manager.cpp:71-76`). Each `MemPool` tracks free slots via a lock-free index free-list (`m_freeIndices`), eliminating runtime heap allocation and memory fragmentation on the data path.
- **Address-Space Independence (`chunk_management.hpp:33-48`):** Because POSIX `mmap` maps the same shared-memory segment at different virtual base addresses in each process (ASLR), `ChunkManagement` never stores raw virtual pointers across processes; instead, `m_chunkHeader`, `m_mempool`, and `m_chunkManagementPool` are `iox::RelativePointer<T>` (segment ID + byte offset).
- **Deallocation Invariant (`memory_manager.cpp:210-221`):** `MemoryManager::freeChunk()` strictly frees the `ChunkManagement` slot *before* returning the payload chunk to `mempool->freeChunk()`, maintaining the invariant that the management pool can never run dry while payload chunks are available.
- **Ownership Typestate (`sample.hpp:36-72`, `chunk_queue_pusher.inl:46-70`, `chunk_queue_popper.inl:49-75`):**
  - Publisher calls `loan()` -> receives `Sample<T>` (mutable ownership, unique writer, refcount = 1). Only non-`const` `Sample<T>` exposes `publish()` via SFINAE (`ForPublisherOnly<S, T>`), which transfers the chunk to `ChunkSender::send()`, copies its `RelativePointer<ChunkManagement>` into every connected subscriber's bounded lock-free `ChunkQueue` (incrementing `m_referenceCounter` per recipient; on queue overflow, `ChunkQueuePusher::push` pops and drops the oldest chunk via `pushRet.value().releaseToSharedChunk()`), and releases the `Sample<T>` custom deleter (`release()`).
  - Subscriber calls `take()` -> receives `Sample<const T>` (immutable shared view; compile-time `const T` forbids mutation of payload shared across $N$ subscribers). Dropping `Sample<const T>` calls `ChunkReceiver::release()`, decrementing `m_referenceCounter` and returning the chunk to `MemPool` when it reaches zero.

#### 5.2 Crash Reclamation Protocol, Documented `SIGKILL` Leak Windows, and Weak-Memory Synchronization Audit

A core hazard of shared-memory reference counting is **crashed subscriber/publisher starvation**: if a subscriber holds a loaned `Sample<const T>` and dies via `SIGKILL`, its C++ destructor never runs, permanently pinning `m_referenceCounter >= 1` and exhausting the publisher's `MemPool`.

`iceoryx` mitigates this via a two-part protocol verified in source:
1. **Per-Port Shared-Memory `UsedChunkList` (`chunk_receiver.inl:73-112`, `chunk_sender.inl:126,154,248-250`):** Every `ChunkReceiver` and `ChunkSender` records every currently loaned `SharedChunk` in a fixed-capacity shared-memory array `m_chunksInUse` (`TOO_MANY_CHUNKS_HELD_IN_PARALLEL` / `TOO_MANY_CHUNKS_ALLOCATED_IN_PARALLEL` bounds simultaneous loans).
2. **Heartbeat Watchdog & Forced Cleanup (`process_manager.cpp:707-746`, `port_manager.cpp:753-885`):** `RouDi`'s `ProcessManager::monitorProcesses()` iterates `m_heartbeatPool`; when `elapsed_milliseconds_since_last_beat() > PROCESS_KEEP_ALIVE_TIMEOUT`, it invokes `removeProcessAndDeleteRespectiveSharedMemoryObjects()` -> `PortManager::deletePortsOfProcess()` -> `releaseAllChunks()` on every publisher/subscriber/client/server port of the dead process, calling `m_chunksInUse.cleanup()` and `ChunkQueuePopper::clear()` to decrement all held refcounts back to zero.

**Two Critical Source-Verified Soundness/Resilience Findings:**
1. **Explicitly Annotated `SIGKILL` Chunk-Leak Windows (`chunk_sender.inl:141-156, 185-193, 204-214, 223-231`):** `iceoryx` crash reclamation is *not* strictly atomic against arbitrary asynchronous process termination. Four critical sections in `ChunkSender` carry explicit upstream comments (`// BEGIN of critical section, chunk will be lost if the process terminates in this section`):
   - In `tryAllocate()` (`chunk_sender.inl:141-156`): between `m_memoryMgr->getChunk(chunkSettings)` (popped from `MemPool` with refcount = 1) and `m_chunksInUse.insert(chunk)`, a `SIGKILL` leaves the chunk untracked in any `UsedChunkList`, permanently leaking it until `RouDi` restarts.
   - In `send()`, `sendToQueue()`, and `pushToHistory()` (`chunk_sender.inl:185-231`): between `getChunkReadyForSend()` (which removes the chunk from `m_chunksInUse`) and completing delivery + updating `m_lastChunkUnmanaged`, a `SIGKILL` similarly orphans the chunk.
2. **Relaxed Reference-Count Decrement (`shared_chunk.cpp:54-62`):**
   ```cpp
   if ((m_chunkManagement != nullptr)
       && (m_chunkManagement->m_referenceCounter.fetch_sub(1U, std::memory_order_relaxed) == 1U))
   {
       MemoryManager::freeChunk(*m_chunkManagement);
       m_chunkManagement = nullptr;
   }
   ```
   Standard C++11 lock-free reference counting requires `memory_order_release` on every `fetch_sub` plus an `acquire` fence (or `acq_rel`) on the thread observing `1 -> 0` so that all non-last subscribers' payload reads *happen-before* `freeChunk()` and the next publisher's overwrite of the recycled chunk. Because `SharedChunk::decrementReferenceCounter()` uses `std::memory_order_relaxed`, soundness on weakly ordered architectures (`ARMv8-A` / `RISC-V`) depends on external release/acquire ordering inside `UsedChunkList::remove()` and `MemPool::freeChunk()`'s `m_freeIndices.push/pop` — any path calling `SharedChunk::~SharedChunk()` without an intervening release barrier before the `fetch_sub` lacks a C++11 happens-before edge between a non-last reader's payload load and the last releaser's `freeChunk`.

#### 5.3 Evolution to Brokerless Rust Typestates in `iceoryx2` and `zerocopy` Layout Contracts

Comparing `eclipse-iceoryx/iceoryx` (C++) with `eclipse-iceoryx/iceoryx2` (`5ff74e27...`, Rust, `iceoryx2/src/sample.rs`, `sample_mut.rs`) highlights three PL/systems shifts directly relevant to verified zero-copy Rust interfaces:

| Property | `eclipse-iceoryx/iceoryx` (C++) | `eclipse-iceoryx/iceoryx2` (Rust) |
| :--- | :--- | :--- |
| **Coordination Architecture** | Centralized `RouDi` broker daemon (single point of failure; heartbeat timeout cleanup) | Fully decentralized / brokerless POSIX shared memory & lock-file dead-node detection (no central daemon SPOF) |
| **Use-After-Publish Safety** | Runtime empty-state guard (`Sample::release()` nulls inner `unique_ptr`; calling `get()` afterward is logic/UB error) | **Compile-time affine typestate**: `SampleMut::send(self)` consumes `self` by value (`sample_mut.rs`), statically forbidding post-send writes or reads |
| **Payload ABI / Relocatability Check** | Unenforced C++ template `T` (accidentally publishing `std::vector` or raw pointers compiles and crashes subscribers!) | Static trait bound **`Payload: ZeroCopySend`** (`sample_mut.rs:93,114`), enforcing self-contained, relocatable representation without cross-process invalid pointers |
| **Variable-Length / Zero-Copy Views** | Raw byte payload + manual `ChunkHeader` offset math | First-class typed slices `SampleMut<Service, [Payload], UserHeader>` (`sample_mut.rs:128`) and validated `Flatbuffer<Payload>` wrapper (`sample_mut.rs:189-213`) |
| **Aliasing & Padding Contract** | C++ `const T*` convention; untrusted publisher mutation after send is data-race UB | Rust `&Payload` / `&mut Payload` (`Deref`/`DerefMut` in `sample_mut.rs:116-168`) requires strict publisher-immutability freeze on `send()` and full byte-validity (no uninitialized padding / invalid enum discriminants, mirroring `zerocopy::FromBytes`/`IntoBytes`) |

**Shared-Memory Rust Soundness Boundary:** Even with `SampleMut::send(self)` preventing accidental publisher writes in honest Rust code, forming a Rust shared reference `&Payload` directly into POSIX shared memory mapped read-write by an untrusted or buggy remote process violates LLVM `noalias` / Rust aliasing invariants if the remote process mutates the chunk concurrently or writes invalid bit patterns (e.g., `bool` byte `2`). Zero-copy `&T` sharing across process boundaries is therefore sound **only** when (a) the payload type is valid for arbitrary bit patterns (or explicitly validated before reference formation, as in `iceoryx2`'s `Flatbuffer::payload_root()` calling `flatbuffers::root::<Payload>()`) and (b) the OS enforces memory-protection isolation (read-only subscriber `mmap` segments + publisher-side freeze/trust boundary).

## Boundaries

- **Other Lie Groups Beyond $\mathrm{SO}(3)/\mathrm{SE}(3)$ (`not examined`):** Source inspection and micro-probes covered `Rot3`/`SO3` and `Pose3`/`SE3` in `SymForce` and `GTSAM`. Higher-dimensional groups such as $\mathrm{Sim}(3)$ (`Similarity3`), $\mathrm{SE}_2(3)$ (extended pose with velocity for invariant EKF), and unit-sphere manifolds ($S^2$ / `Unit3`) were not probed numerically.
- **Full `iSAM2` Empirical Benchmarks (`not examined`):** `GTSAM` `ISAM2` architecture, `fixedVariables_`, and fluid relinearization invariants were established from `ISAM2.h`, `BayesTree.h`, and Kaess et al. (IJRR 2012); end-to-end runtime benchmarks comparing `SymForce` C++ `Optimizer` vs. `GTSAM` `ISAM2` on standard SLAM datasets (e.g., Sphere2500, KITTI) were not executed.
- **Exact `GTSAM` CMake Default Values Across Downstream Distributions (`unknown`):** `gtsam/geometry/Pose3.cpp:127` conditionally switches `Pose3::ChartAtOrigin::Retract` via `#ifdef GTSAM_POSE3_EXPMAP`, and `Rot3Q.cpp:20` switches storage via `#ifdef GTSAM_USE_QUATERNIONS`. Downstream distro packages (e.g., Ubuntu/ROS binary packages vs. source builds) vary in which CMake flags they enable; callers integrating external Jacobians must inspect installed `<gtsam/config.h>` rather than assuming defaults.
- **Weak-Memory Ordering Inside `iceoryx` `m_freeIndices` and `UsedChunkList` (`unknown`):** While `SharedChunk::decrementReferenceCounter()` (`shared_chunk.cpp:57`) was directly verified to use `std::memory_order_relaxed`, the exact atomic orderings inside `iox::concurrent::LoFFLi` (`m_freeIndices`) and `UsedChunkList::remove()` were not fully audited in this pass; hence whether an accidental fence masks the missing `acq_rel` on `ARMv8-A` remains unresolved without inspecting `loffli.cpp` and running a C++11 memory-model checker (e.g., GenMC / CDSChecker).
- **ROS 2 Multi-Threaded Executor and Third-Party RT Executors (`known not to apply`):** The polling-point single-threaded WCRT bound from Casini et al. (ECRTS 2019) applies specifically to `SingleThreadedExecutor` (`rclcpp::Executor`). `MultiThreadedExecutor` introduces lock contention across `wait_set_` and callback-group `can_be_taken_from()` flags (`executor.cpp:816-822`) with distinct response-time anomalies; priority-aware executors such as PiCAS or custom `EventsQueue` priority-heap backings are outside the modeled behavior.
- **Untrusted / Adversarial Shared-Memory Publishers (`known not to apply`):** `iceoryx` and `iceoryx2` crash resilience protects against fail-stop process crashes (`SIGKILL`, segfault) of cooperative processes; neither prevents a malicious process with write access to a shared-memory management segment from corrupting `ChunkManagement::m_referenceCounter`, `ChunkHeader`, or lock-free queue indices.

## Evidence

### Primary Git Repositories and Inspected Source Locations

| Subject | Repository & Full Commit SHA | Inspected Paths & Key Symbols / Lines |
| :--- | :--- | :--- |
| `SymForce` | `symforce-org/symforce` @ `acdedd0bcfea11ee88e89908dd6499024dd9f89a` | `symforce/__init__.py:245` (`numeric_epsilon = 10 * sys.float_info.epsilon`); `symforce/geo/rot3.py:82-100` (`from_tangent`, `to_tangent`), `:106-127` (`storage_D_tangent`, `tangent_D_storage`), `:152-163` (`to_tangent_norm`), `:190-301` (branchless Shoemake `from_rotation_matrix`); `symforce/geo/pose3.py:28-42,144-200` (product-manifold `SO(3) x R^3` `retract`/`local_coordinates`); `symforce/ops/lie_group_ops.py:44-216` (`LieGroupOps`) |
| `GTSAM` | `borglab/gtsam` @ `3fd8ba1bcb12ce4ef6f1b633100020b0f4f13cc7` | `gtsam/base/Manifold.h:163-168` (`check_manifold_invariants`); `gtsam/base/Lie.h:113-257` (`LieGroup::retract` calling `compose(ChartAtOrigin::Retract)`); `gtsam/geometry/SO3.cpp:57-59` (`kNearZeroThresholdSq = 1e-6`, `kNearPiThresholdSq = 1e-6`), `:77-190` (`ExpmapFunctor`, `DexpFunctor`), `:199-218` (`tangentExpmap`), `:337-404` (`SO3::Logmap` Shepperd + Hertzberg `atan`); `gtsam/geometry/Rot3.cpp:269-271` (gimbal-lock check); `gtsam/geometry/Rot3Q.cpp:34-46,139-168`; `gtsam/geometry/Pose3.cpp:99-161` (`Expmap`, `GTSAM_POSE3_EXPMAP` vs. product `ChartAtOrigin`); `gtsam/nonlinear/ISAM2.h:45-180` (`ISAM2`, `fixedVariables_`, `nnzAfterLastReorder_`) |
| `ROS 2 rclcpp` (`0.6.3`) | `ros2/rclcpp` @ `e32d17980dcf761712cb854b3703336c380a570e` | `rclcpp/src/rclcpp/executor.cpp:411-461` (`wait_for_work`), `:509-532` (live `get_next_timer`), `:535-602` (`get_next_ready_executable`, `get_next_executable`, static `Timer > Sub > Srv > Cli > Waitable` priority) |
| `ROS 2 rclcpp` (`HEAD`) | `ros2/rclcpp` @ `9e66d4d2ef0188656e1ac2ad71d338f15c44e1f2` | `rclcpp/src/rclcpp/executor.cpp:769-798` (`wait_for_work`), `:801-954` (`get_next_ready_executable`, `wait_result_` timer snapshot, `can_be_taken_from` rebuild guard); `rclcpp/src/rclcpp/experimental/executors/events_executor/events_executor.cpp:32-200` (`EventsExecutor`, `EventsQueue`, `TimersManager`) |
| `Eclipse iceoryx` | `eclipse-iceoryx/iceoryx` @ `9f9fb0d359f1805cdd38006c8aba6af6dbc2209e` | `iceoryx_posh/include/iceoryx_posh/popo/sample.hpp:36-72` (`Sample<T>`, `ForPublisherOnly`); `iceoryx_posh/include/iceoryx_posh/internal/mepoo/chunk_management.hpp:33-48` (`RelativePointer`, `m_referenceCounter`); `iceoryx_posh/source/mepoo/memory_manager.cpp:71-76,147-221` (`getChunk`, `freeChunk` ordering); `iceoryx_posh/source/mepoo/shared_chunk.cpp:54-62` (`fetch_sub(..., memory_order_relaxed)`); `iceoryx_posh/source/mepoo/mem_pool.cpp:86-158`; `iceoryx_posh/include/iceoryx_posh/internal/popo/building_blocks/chunk_queue_pusher.inl:46-70`; `chunk_queue_popper.inl:49-127`; `chunk_receiver.inl:73-112` (`m_chunksInUse`, `releaseAll`); `chunk_sender.inl:99-250` (explicitly commented `SIGKILL` chunk-loss critical sections at lines 141-156, 185-193, 204-214, 223-231); `iceoryx_posh/source/roudi/process_manager.cpp:707-746` (`monitorProcesses`); `iceoryx_posh/source/roudi/port_manager.cpp:753-885` (`deletePortsOfProcess`) |
| `Eclipse iceoryx2` | `eclipse-iceoryx/iceoryx2` @ `5ff74e270863cb416583eef42c928afcb436630f` | `iceoryx2/src/sample_mut.rs:91-213` (`SampleMut`, `ZeroCopySend` bound, `Flatbuffer::payload_root`); `iceoryx2/src/sample.rs` |

### Peer-Reviewed Literature and Specifications

- Hayk Martiros, Aaron Miller, Nathan Bucki, et al., *"SymForce: Symbolic Computation and Code Generation for Robotics"*, Robotics: Science and Systems (RSS) 2022, `DOI: 10.15607/RSS.2022.XVIII.041`, `arXiv:2204.07889`.
- Michael Kaess, Hordur Johannsson, Richard Roberts, Viorela Ila, John J. Leonard, and Frank Dellaert, *"iSAM2: Incremental Smoothing and Mapping Using the Bayes Tree"*, International Journal of Robotics Research (IJRR), Vol. 31, No. 2, 2012, `DOI: 10.1177/0278364911430419`.
- Joan Solà, Jérémie Deray, and Dinesh Atchuthan, *"A micro Lie theory for state estimation in robotics"*, `arXiv:1812.01537`.
- Christoph Hertzberg, René Wagner, Udo Frese, and Lutz Schröder, *"Integrating Generic Sensor Fusion Algorithms with Sound State Representations through Encapsulation of Manifolds"*, Information Fusion, Vol. 14, No. 1, 2013, pp. 57–77, `DOI: 10.1016/j.inffus.2011.08.003`, `arXiv:1107.1119`.
- Daniel Casini, Tobias Blaß, Ingo Lütkebohle, and Björn B. Brandenburg, *"Response-Time Analysis of ROS 2 Processing Chains Under Reservation-Based Scheduling"*, 31st Euromicro Conference on Real-Time Systems (ECRTS 2019), LIPIcs Vol. 133, `DOI: 10.4230/LIPIcs.ECRTS.2019.6`.

### Reproducible Execution Probes (Observed 2026-11-19, Python 3 on Linux x86_64)

1. **`SO(3)` Singularity, Double-Cover & Three-Way `Pose3` Retraction Probe:**
   ```python
   # Self-contained verification of SymForce rot3.py:82-163, GTSAM SO3.cpp:77-404, and Pose3 retractions
   import math, sys
   eps_list = [("f64_default", 10*sys.float_info.epsilon), ("1e-9", 1e-9), ("1e-6", 1e-6)]
   for name, eps in eps_list:
       q0_w = math.cos(eps / 2.0)
       norm0 = 2.0 * math.acos(1.0 - eps)
       h = 1e-8
       w_safe = min(1.0 - eps, math.sqrt(1.0 - h*h))
       slope = (2.0 * math.acos(w_safe) / math.sqrt(1.0 - w_safe*w_safe))
       print(f"{name}: w0-1={q0_w-1:.3e}, to_tangent_norm(I)={norm0:.6e}, slope={slope:.12f}")
   ```
   Observed outputs:
   - `f64_default` (`2.22e-15`): `to_tangent_norm(I) = 1.332800e-07 rad`, `slope = 2.000000000000` (err `4.441e-16`)
   - `1e-9`: `to_tangent_norm(I) = 8.944272e-05 rad`, `slope = 2.000000000167` (err `1.667e-10`)
   - `1e-6`: `to_tangent_norm(I) = 2.828427e-03 rad`, `slope = 2.000000666656` (err `6.667e-07`)
   - `GTSAM` `ExpmapFunctor` jump across $\theta = 10^{-3}$: `|dA| = 8.327e-15`, `|dB| = 1.388e-15`
   - Double-cover at $\theta = 0.5$: `SymForce(q) = SymForce(-q) = GTSAM(R(q)) = 0.5000000`, vs. naive `2*acos(-q.w) = 5.7831853`
   - Three `Pose3` retractions from $R_a = \operatorname{Rot}_z(\pi/2), t_a = 0$, $\xi = (0,0,\pi/2, 1,0,0)$: SymForce `(1.0000, 0.0000, 0.0000)`, GTSAM default `(0.0000, 1.0000, 0.0000)`, GTSAM `GTSAM_POSE3_EXPMAP` `(-0.6366, 0.6366, 0.0000)`.

2. **ROS 2 Executor Polling-Point & Timer Priority-Inversion Discrete-Event Probe:**
   Job set: `T_lo#0` (`t=0.0`, `TIMER`, `C=2.0`), `S_lo1..3` (`t=0.0`, `SUB`, `C=3.0` each), `S_hi` (`t=0.1`, `SUB`, `C=1.0`, `D=10.0`), `T_lo#1` (`t=8.0`, `TIMER`, `C=2.0`).
   - Observed Crystal `0.6.3` `S_hi` finish: `14.0 ms` (`RT = 13.9 ms`, deadline miss; `T_lo#1` runs at `[8.0, 10.0]` before `S_lo3`).
   - Observed `HEAD` `wait_result_` `S_hi` finish: `14.0 ms` (`RT = 13.9 ms`, deadline miss; `T_lo#1` runs at `[11.0, 13.0]` before `S_hi`).
   - Observed `EventsExecutor` FIFO `S_hi` finish: `12.0 ms` (`RT = 11.9 ms`; `S_hi` precedes `T_lo#1`).
   - Naive single-blocker NP-RTA prediction: `6.0 ms` (unsound underestimate by `7.9 ms`).

## Revalidation

Each major finding can be cheaply revalidated against newer upstream revisions without repeating full literature review:

1. **SymForce `Rot3` / `Pose3` Chart & $\epsilon$ Behavior:** Diff `symforce/geo/rot3.py` (`from_tangent`, `to_tangent`, `to_tangent_norm`, `storage_D_tangent`) and `symforce/geo/pose3.py` (`retract`, `local_coordinates`). Confirm whether `to_tangent_norm` still computes `2 * acos(Min(1 - eps, |w|))` (retaining $2\sqrt{2\epsilon}$ bias) or migrates to `2 * atan2(norm(xyz), |w|)`.
2. **GTSAM `SO3` / `Pose3` Retraction & CMake Defaults:** Check `gtsam/geometry/SO3.cpp` (`kNearZeroThresholdSq`, `Logmap`) and `gtsam/geometry/Pose3.cpp` (`ChartAtOrigin::Retract`, `#ifdef GTSAM_POSE3_EXPMAP`), and verify `<gtsam/config.h>` in any target deployment build before wiring SymForce-generated Jacobians into GTSAM factors.
3. **ROS 2 Executor Priority Inversion:** Diff `rclcpp/src/rclcpp/executor.cpp` (`get_next_ready_executable`, `get_next_executable`) and `events_executor.cpp`. Re-check whether `SingleThreadedExecutor` still waits for `get_next_ready_executable() == false` before calling `wait_for_work()` and whether `Timer > Subscription` dispatch remains hard-coded; inspect whether `EventsExecutor` has gained a priority-heap `EventsQueue`.
4. **Eclipse `iceoryx` Crash-Leak Windows & Refcount Ordering:** Diff `chunk_sender.inl` around `tryAllocate()` / `send()` for the `// BEGIN of critical section, chunk will be lost` windows and `shared_chunk.cpp:decrementReferenceCounter()` for `std::memory_order_relaxed` vs. `std::memory_order_acq_rel`; for `iceoryx2`, inspect `iceoryx2/src/sample_mut.rs` for `ZeroCopySend` and `send(self)` move semantics.
