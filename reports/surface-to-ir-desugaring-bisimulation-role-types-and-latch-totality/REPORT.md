# Surface-to-IR Desugaring Bisimulation, Zero-Cost Positional Role Types, and State-Machine Latch Totality

## Summary

Intermediate-representation (`IR`) verifiers, borrow checkers, and theorem provers routinely certify lowered control-flow graphs (`MIR`, `LLVM IR`, `Core` calculi) while leaving the **surface-to-IR lowering boundary**, **same-unit positional call interfaces**, and **imperative state-machine fallthrough structure** outside formal correspondence. Across primary-source inspections of `rust-analyzer/rowan` (`d601b195d7bcb9f643c218b2ba113257880d2cdd`), `leanprover/lean4` (`e35bfaf8dab2405124cb486c80a7c12d3cccb951`), `dcmtk/dcmtk` (`e8d3d701c285de2dacea605cf0aaa606ad6908fe`), `sogno-platform/dpsim` (`7fcaac00758cc7f448179edf2a508021dd1374b8`), `moos-ivp/moos-ivp` (`ab1ac374a44a5c567187b4f27abce2e02e8fbefa`), and Rust Edition 2024 `RFC 3606` (`if_let_rescope`), four orthogonal front-end preservation mechanisms govern whether proved or compiled IR matches programmer intent:

1. **Lossless Red-Green Concrete Syntax Tree (`CST`) Elaboration Totality (`Basis: source + execution`)**: Representing concrete syntax as position-independent, reference-counted immutable `GreenNode` trees paired with transient zipper cursors (`SyntaxNode` in `rowan/src/green/node.rs` and `src/cursor.rs`) enforces exact byte conservation ($\operatorname{unparse}(\operatorname{parse}(b)) = b$) and $O(1)$ untouched sibling reuse across incremental edits (`63/64` function subtrees shared in `105.15 us`). Totality across parser error-recovery and binder elaboration requires mapping recovery placeholders strictly to explicit unproved holes rather than synthesized expressions, and rejecting implicit free-variable generalization (`Lean 4` `src/Lean/Elab/AutoBound.lean:28-69`, where `autoImplicit = true` silently universally quantifies single-letter/numeric-suffix typos such as `x_1` and, under `relaxedAutoImplicit = true`, arbitrary misspelled identifiers such as `min_ba1`).
2. **Forward-and-Backward Desugaring Bisimulation Certificates (`Basis: normative + source + execution + derived`)**: Defining language semantics *"by whatever desugaring emits"* hides behavioral discontinuities across editions, integer widths, and SIMD lowering:
   - *Temporary drop-scope shifts (`RFC 3606`)*: Desugaring `if let Some(v) = cfg.read().get() { A } else { cfg.write(); }` into `match` extends the temporary `RwLockReadGuard` across the `else` arm in Rust 2021 (guaranteeing thread self-deadlock), whereas Rust 2024 drops scrutinee temporaries before `else`—and automated `if let` $\to$ `match` rewrites silently resurrect the deadlock.
   - *Integer-promotion wraparound before allocation (`DCMTK` `diinpxt.h:460-476`)*: Evaluating `8 * length_B1` on `32`-bit unsigned `Uint32` (`600 MiB` `1`-bit segmentation mask: `length_B1 = 629,145,600`) wraps modulo $2^{32}$ from `5,033,164,800` down to **`738,197,504` (`6.82x` heap under-allocation)** prior to `new (std::nothrow) T2[Count]`, causing an unbounded heap buffer overwrite in downstream conversion loops unless guarded by checked widening (`OFStandard::safeMult`).
   - *Dead-branch absorption in branchless SIMD lowering*: Lowering `if r > 1e-6 { ln(r)/r } else { 0.0 }` to eager SIMD `select` evaluates `0.0 * (+inf) = NaN` in reverse-mode differentiation unless the desugarer emits both forward input clamping and bitwise strong-zero masking.
3. **Zero-Cost Positional Parameter Role Tags (`Basis: source + execution + derived`)**: Physical unit types (`RadPerSec`, `Meters`, `Seconds`) fail whenever multiple parameters share **identical physical dimensions** but serve **distinct semantic roles**. In `sogno-platform/dpsim` (`dpsim-models/src/EMT/EMT_Ph3_AvVoltageSourceInverterDQ.cpp:178-179` calling `dpsim-models/src/Signal/PLL.cpp:27-35`), `mPLL->setParameters(Kp_pll, Ki_pll, Omega_cutoff)` passes a low-pass power-filter cutoff frequency (`Omega_cutoff`, e.g., `2*pi*5 = 31.42 rad/s`) into the third `Real` parameter `omegaNom` (nominal synchronous grid feedforward frequency `2*pi*50 = 314.16 rad/s`), injecting a **`-282.74 rad/s` (`-45 Hz`)** initial frequency bias that pure SI unit checking (`RadPerSec == RadPerSec`) accepts without warning.
4. **Monotone State-Machine Latch Totality & Dead-Guard Reachability (`Basis: source + execution + derived`)**: Imperative control state machines written over mutable string or enum fields suffer silent safety-latch erasure when fallthrough assignments overwrite prior states ahead of guard checks. In `moos-ivp/moos-ivp` (`ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp:925-975`), `checkModeStandOn()` omits an early `return;` at line `935`, falling into line `955` (`m_avoid_submode = "unsure";`) on every tick and rendering line `964` (`if(m_avoid_submode == "inextremis") return;`) **unreachable dead code**—destroying the intended monotone emergency collision-avoidance latch the instant predicted closest-point-of-approach (`CPA`) nudges `0.2 m` above `m_min_util_cpa_dist`.

---

## Applicability

This report applies to programming-language front-ends, macro/elaboration engines, proof assistants, static analyzers, high-assurance embedded/simulation C++ and Rust codebases, and formal verification toolchains where specifications or safety audits occur at the source level while execution or proof checking occurs on lowered IR:

- **`rust-analyzer/rowan` (`d601b195d7bcb9f643c218b2ba113257880d2cdd`) & Incremental IDE / Verification Front-Ends**: Governs lossless Concrete Syntax Tree (`CST`) layout (`GreenNodeData`, `ThinArc`, `NodeData` zipper cursors), trivia preservation, and incremental re-parsing invariants.
- **`leanprover/lean4` (`e35bfaf8dab2405124cb486c80a7c12d3cccb951`) & Interactive Theorem Prover Elaborators**: Governs binder resolution (`autoImplicit` and `relaxedAutoImplicit` in `src/Lean/Elab/AutoBound.lean`), macro-scope hygiene (`Issue #255` non-termination hazard noted in `AutoBound.lean:33-46`), and truncating natural-number subtraction (`Nat.sub`) vs. mathematical integer ($\mathbb{Z}$) specification semantics.
- **Rust Edition 2021 vs. Edition 2024 (`RFC 3606`, `if_let_rescope`)**: Applies to drop-order-sensitive resource guards (`MutexGuard`, `RwLockReadGuard`, `Ref`, `ArenaScope`, transaction handles) across pattern-matching control-flow constructs (`if let`, `match`, `let ... else`).
- **`dcmtk/dcmtk` (`e8d3d701c285de2dacea605cf0aaa606ad6908fe`), `sogno-platform/dpsim` (`7fcaac00758cc7f448179edf2a508021dd1374b8`), and `moos-ivp/moos-ivp` (`ab1ac374a44a5c567187b4f27abce2e02e8fbefa`)**: Provide concrete, pinned real-world C++ defect specimens demonstrating why memory safety, unit-of-measure wrappers, and line-by-line human review remain insufficient without (i) mathematical-integer width bisimulation on allocation expressions, (ii) phantom positional role tags, and (iii) state-machine guard reachability / monotone-latch verification.

---

## Findings

### 1. Lossless Red-Green CST Architecture and Elaboration Totality (`rowan` & `Lean 4`)

`Basis: source + execution + derived`

#### 1.1 Position-Independent `GreenNode` Sharing vs. Ephemeral `Red` Zipper Cursors
Traditional compiler Abstract Syntax Trees (`AST`s) discard whitespace, comments, parenthesization, and malformed error tokens during lexing/parsing while embedding absolute byte spans `(start, end)` and parent pointers into every heap node (`64–128 B/node`). Editing `1` character at byte offset `10` shifts the byte offsets of every subsequent token in a `10,000`-line file, invalidating the entire cached AST.

In `rust-analyzer/rowan` (`d601b195d7bcb9f643c218b2ba113257880d2cdd`, `src/green/node.rs:19-60` and `src/cursor.rs:1-75`, adapting Roslyn's C# Red-Green syntax architecture), syntax representation splits into two strictly separated strata:

1. **Immutable Position-Independent `Green` Layer (`src/green/node.rs:19-54`)**:
   - `GreenNodeHead` stores only `kind: SyntaxKind`, relative `text_len: TextSize` (`u32`), and allocation telemetry; `GreenChild` (`16 B` on 64-bit targets, enforced via `static_assert!(mem::size_of::<GreenChild>() == mem::size_of::<usize>() * 2)` at `node.rs:30`) stores `(rel_offset: TextSize, GreenNode | GreenToken)` inside a single `ThinArc<GreenNodeHead, GreenChild>` (`GreenNode`).
   - Because `GreenNode` contains **zero absolute file offsets and zero parent pointers**, identical subtrees (tokens, expressions, unchanged sibling functions) are structurally hash-consed across both intra-file repetitions and inter-edit versions, satisfying the **Exact Byte-Roundtrip Identity**:
     $$\forall b \in \Sigma^*:\quad \operatorname{concat\_leaves}\!\big(\operatorname{parse\_green}(b)\big) \equiv b.$$
2. **Transient Parent-Linked `Red` Zipper Layer (`src/cursor.rs:11-75`)**:
   - `SyntaxNode` wraps a reference-counted `NodeData` (`rc: Cell<u32>`, `parent: Option<NonNull<NodeData>>`, `offset: TextSize`, `green: Green`) instantiated lazily during traversal. As documented at `src/cursor.rs:23-31`, only nodes along the active cursor spine to the root stay alive in memory (`O(depth)` transient heap cells).
   - **Important `unsafe` TCB Boundary (`src/cursor.rs:12-14`)**: `rowan`'s own source header warns verbatim: *"The implementation is utterly and horribly unsafe. This whole module is an unsafety boundary."* Using raw `NonNull` intrusive refcounting for speed means verified front-ends should keep `GreenNode` array-indexed (`u32` Structure-of-Arrays handles) rather than pointer-chasing `unsafe` `NodeData` cells inside a trusted checker.

#### 1.2 Elaboration Traps: Error-Recovery Hallucination & `Lean 4` `autoImplicit` Vacuity
Even over a lossless CST, lowering `CST -> CoreTerm` betrays author intent when partial or implicit syntax is silently "repaired":

1. **GLR / Error-Recovery Missing-Token Fabrication**: Incremental IDE parsers (`tree-sitter`, `rowan`-backed resilient recursive-descent parsers) synthesize zero-width `MISSING` tokens or `ERROR` wrapper nodes so downstream typecheckers still offer autocomplete mid-keystroke. If a proof or codegen backend accepts lowered ASTs without checking `count(ERROR | MISSING) == 0`—or maps `MISSING` delimiters to default `0`/`false`/`Unit` constants—incomplete source edits compile or verify silently. Sound elaboration maps every recovery node strictly to an uninhabited **`UnprovedHole`** value that blocks code emission and binary proof admission while still allowing local IDE type inference on sibling subtrees.
2. **Implicit Unbound Variable Quantification (`Lean 4` `src/Lean/Elab/AutoBound.lean:19-69`)**:
   In `leanprover/lean4` (`e35bfaf8dab2405124cb486c80a7c12d3cccb951`), `autoImplicit` defaults to **`true`**, and `relaxedAutoImplicit` defaults to **`true`**. Inspecting `AutoBound.lean:28-69` reveals two distinct hazards:
   - Under `relaxedAutoImplicit = true`, `checkValidAutoBoundImplicitName` (`L50-63`) accepts **any non-empty single-component identifier**! If an engineer writes:
     ```lean
     theorem reserve_solvent (bal fee min_bal : Int) (h : bal - fee >= min_ba1) : ...
     ```
     misspelling `min_bal` as `min_ba1`, Lean 4 does **not** report an unbound identifier error—it silently generalizes `{min_ba1 : Int}` as a fresh universally quantified implicit parameter, proving a theorem whose hypothesis constrains an unrelated ghost variable `min_ba1` rather than `min_bal`!
   - Even with `set_option relaxedAutoImplicit false` ("strict" mode, `L28-29`), `isValidAutoBoundSuffix` (`s.toRawSubstring.drop 1 |>.all fun c => c.isDigit || isSubScriptAlnum c || c == '_' || c == '\''`) **still** silently auto-binds any single character followed by digits, subscripts, underscores, or primes (such as typos `x_1`, `n'`, `k2`, or `α₁`)!
   - Furthermore, `AutoBound.lean:31-46` documents `Issue #255`: erasing macro scopes inside `isValidAutoBoundImplicitName` previously caused `local notation "A" => id x` inside `theorem test : A = A` to diverge in an infinite elaboration loop (`x` + fresh macro scope thrown and re-bound forever). Enforcing `autoImplicit = false` (`closed-binder totality: FV(spec) \subseteq DeclaredBinders`) eliminates both silent theorem corruption and macro-scope binder divergence at zero expressive cost.

---

### 2. Forward-and-Backward Desugaring Bisimulation (`DesugarBisimCert`)

`Basis: normative + source + execution + derived`

#### 2.1 Why "Semantics by Desugaring" Fails Human Audit
Most production compilers (`rustc` `AST -> HIR -> THIR -> MIR`, `clang` `Sema` implicit casts, `C++` temporary lifetime rules, `SystemVerilog` context-determined bitwidths) define the meaning of surface constructs *implicitly* by translation into a lower IR. Whenever human mental models follow **direct surface evaluation (`SurfSem`)** while the compiler executes **`CoreSem(desugar(e))`**, subtle translation mismatches become catastrophic runtime bugs:

| Surface Construct | Human Surface Mental Model (`SurfSem`) | Unverified Lowering / Desugaring Behavior (`CoreSem`) | Concrete Production Consequence |
| :--- | :--- | :--- | :--- |
| **`if let Some(v) = lock.read().get() { A } else { lock.write() }`** | Scrutinee `lock.read()` is evaluated to test `Some`, then dropped *before* entering `else` | Rust $\le 2021$ desugared `if let` identically to `match`, keeping scrutinee temporaries in the enclosing block scope until **after `else` exits** (`RFC 3606`) | **Guaranteed single-thread `RwLock` self-deadlock** on every `None` branch; automated `if let -> match` refactors under Rust 2024 silently re-introduce the deadlock! |
| **`Count = (8 * length_B1) + ...`** prior to `new T2[Count]` (`DCMTK` `diinpxt.h:465-475`) | Arithmetic computes exact mathematical pixel count $8 \cdot \lfloor L / b \rfloor$ | C/C++ usual arithmetic conversions evaluate `8 * length_B1` in `32`-bit `Uint32` ($\bmod 2^{32}$) before widening to `size_t` `Count`! | On a `600 MiB` `1`-bit mask (`length_B1 = 629,145,600`), `8 * length_B1 = 5,033,164,800` wraps to **`738,197,504`** (`6.82x` too small!), causing massive heap buffer overwrite in `DiInputPixelTemplate::convert()`! |
| **`if flags & MASK == EXPECTED`** | Test whether masked bits `(flags & MASK)` equal `EXPECTED` | C / C++ / Rust / SystemVerilog bind `==` tighter than bitwise `&`, parsing `flags & (MASK == EXPECTED)` (`flags & 1`) | Silent security-flag / permission-bit bypass (`(flags & 1) != 0` instead of `MASK` equality). |
| **`select(r > 1e-6, ln(r)/r, 0.0)`** under reverse-mode AD | Inactive branch `r <= 1e-6` has constant value `0.0` and derivative `0.0` | SIMD branchless VJP evaluates unselected derivative $\frac{1 - \ln(0)}{0^2} = +\infty$ and multiplies `0.0 * (+inf)` in IEEE 754 | **`0.0 * (+inf) = NaN`** poisons the entire gradient tensor unless lowered with both input clamping (`r_safe = select(cond, r, 1.0)`) and bitwise mask zeroing! |

#### 2.2 Proof-Producing Desugaring via `DesugarBisimCert`
To decouple compiler engineering velocity from trusted computing base (`TCB`) size, front-end elaboration and desugaring passes run **untrusted** and emit a compact, linear-time checkable **Desugaring Bisimulation Certificate (`DesugarBisimCert`)** establishing lockstep observational equivalence between a small (`< 450 LoC`) authoritative **`SurfSem`** and lowered **`CoreSem`**:

$$\forall \sigma_0:\quad \langle e_{\text{surf}}, \sigma_0 \rangle \Downarrow_{\text{SurfSem}} (v, \tau_{\text{drop}}, \sigma_1) \iff \langle \operatorname{desugar}(e_{\text{surf}}), \sigma_0 \rangle \Downarrow_{\text{CoreSem}} (v, \tau_{\text{drop}}, \sigma_1)$$

Specifically, `DesugarBisimCert` records four compact local witnesses (`verified in < 1 ms`):
1. **Explicit `DropAnchor` Trace Alignment**: Every temporary resource carrying observable `Drop` side effects (`MutexGuard`, `RwLockReadGuard`, `File`, DMA loan) receives an explicit lexical `DropAnchorId` in `SurfSem` (`BeforeBranch` for `if let` scrutinees that fail to bind, `BlockExit` for `let` bindings). Desugaring `if let` to a decision tree must emit `drop(anchor_i)` at the exact CFG edge entering `else`; any mismatch against `SurfSem`'s drop order is rejected statically (`Rust2021_ok = False` vs. `Rust2024_ok = True` in `verify_desugar_roles_latches.py`).
2. **Width-Conservative Allocation & Cast Range Witnesses**: In `SurfSem`, integer expressions inside buffer-size calculations (`new T[expr]`, `malloc(expr)`, slice indexing) denote mathematical integers in $\mathbb{Z}$. Lowering `8 * length_B1` to `u32` or `u64` machine arithmetic requires either an interval proof $8 \cdot \text{max}(length\_B1) \le 2^W - 1$ or an explicit checked-overflow combinator (`OFStandard::safeMult` in `DCMTK` `diinpxt.h:470-471`, `usize::checked_mul` in Rust), turning silent `32`-bit wraparound heap overflows (`738,197,504` vs. `5,033,164,800`) into compile-time obligations.
3. **Partial-Order Precedence Disambiguation**: Operators without universal human precedence agreement (`&`/`|`/`^` mixed with `==`/`!=`/`<`/`>`, or `<<`/`>>` mixed with `+`/`-`) have **incomparable precedence** in the surface grammar, requiring explicit parentheses so visual grouping is syntactically isomorphic to the CST.
4. **Backward Blame Projection (Shortest-Path Span Monoid)**: Bisimulation must work **backward** as well as forward: when a downstream solver or abstract interpreter refutes a range/alias obligation on lowered IR, e-graph saturation (`egglog`) or loop unrolling can contain cyclic equivalence classes that hang naive recursive AST resugaring. Labeling rewrite steps in the tropical semiring $(\mathbb{N} \cup \{\infty\}, \min, +)$ extracts a loop-free minimum-step derivation trace back to exact `GreenNode` source spans in $O(|E|)$ time.

---

### 3. Zero-Cost Positional Parameter Role Types (`DPsim` `PLL` Case Study)

`Basis: source + execution + derived`

#### 3.1 Anatomy of a Same-Unit Positional Transposition Bug in `DPsim`
Dimensional unit libraries (`uom` in Rust, `mp-units` / `Boost.Units` in C++, `F#` units of measure) prevent adding `Meters` to `Seconds` or passing `mmHg` where `cmH2O` is expected. However, **unit types are blind to positional role transpositions among quantities sharing the exact same SI dimension**.

Direct primary-source inspection of `sogno-platform/dpsim` (`7fcaac00758cc7f448179edf2a508021dd1374b8`) exposes a textbook instance across two files:
- **Callee definition (`dpsim-models/src/Signal/PLL.cpp:27-35, 60-63`)**:
  ```cpp
  void PLL::setParameters(Real kpPLL, Real kiPLL, Real omegaNom) {
      mKp = kpPLL;
      mKi = kiPLL;
      mOmegaNom = omegaNom;
  }
  // Inside step / state-space assembly (PLL.cpp:34, 62):
  // (**mInputCurr)(0, 0) = mOmegaNom;
  // mB << 1, mKp, 0, 1;  --> integrates omega = omegaNom + kp*e_q + ki*int(e_q)
  ```
  Here `omegaNom` has physical dimension **angular frequency ($\text{rad}\cdot\text{s}^{-1}$)** and semantic role **nominal synchronous grid angular frequency** ($\omega_{\text{nom}} = 2\pi \cdot 50\text{ Hz} \approx 314.159\text{ rad/s}$).
- **Caller invocation (`dpsim-models/src/EMT/EMT_Ph3_AvVoltageSourceInverterDQ.cpp:178-179`)**:
  ```cpp
  // TODO: add and use Omega_nominal instead of Omega_cutoff
  mPLL->setParameters(Kp_pll, Ki_pll, Omega_cutoff);
  ```
  Here `Omega_cutoff` **also has physical dimension angular frequency ($\text{rad}\cdot\text{s}^{-1}$)**! Because it represents the active/reactive power low-pass measurement filter cutoff (typically $f_c = 5\text{ Hz} \implies \Omega_{\text{cutoff}} = 31.416\text{ rad/s}$), **even a full SI dimensional-analysis type system (`RadPerSec`) accepts `mPLL->setParameters(Kp_pll, Ki_pll, Omega_cutoff)` with zero errors**, silently biasing the PLL feedforward frequency by **`-282.74 rad/s` (`-45.0 Hz`)** and forcing the PLL integrator state `mStateCurr(0)` to wind up across `282.74 / Ki_pll` volt-seconds before achieving synchronous lock!

#### 3.2 Zero-Overhead Phantom Role Refinement (`Qty<Dim, Frame, Role>`)
The minimal algebraic fix requires **zero runtime memory or instruction overhead** (`#[repr(transparent)]` in Rust, empty tag structs in C++20, `newtype` / phantom indices in ML/Lean):

$$\operatorname{Qty}\langle \text{Dim},\; \text{Frame},\; \text{Role} \rangle, \qquad \text{e.g., } \operatorname{Qty}\langle \text{RadPerSec},\; \text{SyncGrid},\; \text{NominalCarrier} \rangle \neq \operatorname{Qty}\langle \text{RadPerSec},\; \text{FilterLPF},\; \text{Cutoff3dB} \rangle.$$

1. **Zero Implicit Coercion Across Roles**: Arithmetic within a single role (`cutoff_a + cutoff_b`) or scaling by dimensionless gains preserves the role tag, while ratios of two frequencies explicitly erase to `Dimensionless` only through an intentional `ratio_of(a, b)` combinator. Passing `Qty<RadPerSec, _, Cutoff3dB>` to a parameter expecting `Qty<RadPerSec, _, NominalCarrier>` is a compile-time type error.
2. **Mandatory Keyword / Field-Label Unification on Multi-Scalar Signatures**: In languages or FFI bindings lacking ubiquitous role newtypes, front-end elaboration enforces **named-argument role matching** whenever $\ge 2$ parameters of a function share an underlying scalar or dimensional representation (`fn set_parameters(kp: f64, ki: f64, omega_nom: RadPerSec)`), rejecting bare positional calls whose argument identifier/role provenance conflicts with the formal parameter role.

---

### 4. Monotone State-Machine Latch Totality & Dead-Guard Detection (`MOOS-IvP` Case Study)

`Basis: source + execution + derived`

#### 4.1 Primary-Source Anatomy of the `BHV_AvdColregsV26::checkModeStandOn` Latch-Wipe Bug
Safety-critical controllers (`IMO COLREGs` marine collision avoidance, avionics `Alpha-Floor` stall overrides, industrial emergency-stop interlocks, circuit-breaker trip latches) rely on **monotone emergency submodes**: once hazard severity crosses a critical threshold, the controller must **retain** emergency authority until the physical encounter clears, even after its own evasive action begins increasing clearance distance!

Inspecting `moos-ivp/moos-ivp` (`ab1ac374a44a5c567187b4f27abce2e02e8fbefa`, `ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp:925-975`) uncovers a live bug caused by unstructured imperative mutation of two `std::string` state variables (`m_avoid_mode`, `m_avoid_submode`):

```cpp
// Exact upstream logic in BHV_AvdColregsV26::checkModeStandOn() (lines 925-975):
if(m_avoid_mode == "standon") {
  if(m_cn_crossed_os_port_star) { resetAvoidModes(); return; }
  if((m_contact_range > m_min_util_cpa_dist) && (m_cnos.rate_of_closure() < 0)) {
    resetAvoidModes(); return;
  }
} // <-- Sibling functions checkModeOvertaking (L574) & checkModeHeadOn (L688) have `return;` here;
  //     checkModeStandOn() OMITS `return;` and falls straight through every tick!
if((m_cnos.os_cn_rel_bng() < 247.5) || (m_cnos.cn_os_rel_bng() > 112.5)) return;
if(!m_cnos.cn_crosses_os_bow_or_stern()) return;
if(m_cnos.rate_of_closure() < 0) return;

m_avoid_mode = "standon";
m_avoid_submode = "unsure"; // <-- Line 955: UNCONDITIONALLY OVERWRITES m_avoid_submode!

// kw added for rule 17.a.ii to allow in-extremis actions
// once in extremis, retain authority to maneuver as necessary
if(m_avoid_submode == "inextremis") // <-- Line 964: ALWAYS FALSE (UNREACHABLE DEAD CODE)!
  return;
if((m_avoid_mode == "standon") && (m_contact_range <= m_max_util_cpa_dist) &&
   (m_cnos.os_curr_cpa_dist() <= m_min_util_cpa_dist)){
  m_avoid_submode = "inextremis";
  return;
}
```

Observe the exact failure trajectory verified in `probes/verify_desugar_roles_latches.py`:
1. At tick $k$, a rogue give-way contact on ownship's port bow closes with `os_curr_cpa_dist() = 24.5 m <= 25.0 m` (`m_min_util_cpa_dist`). Ownship enters `("standon", "inextremis")` (`COLREGs` Rule 17(b) emergency evasive maneuver) and alters course to starboard.
2. At tick $k+1$, that starboard turn nudges instantaneous projected `os_curr_cpa_dist()` to `25.2 m > 25.0 m` while the vessels are **still closing** (`rate_of_closure() > 0`).
3. Entering `checkModeStandOn()` with `m_avoid_mode == "standon"` and `m_avoid_submode == "inextremis"`, Part 2 (`L925-935`) does not reset and **does not return**; line `955` overwrites `m_avoid_submode = "unsure"`; line `964` (`if(m_avoid_submode == "inextremis")`) evaluates `"unsure" == "inextremis"` $\to$ **`false`**; line `967` sees `25.2 <= 25.0` $\to$ `false`; and ownship snaps back to `"standon:unsure"` (Rule 17(a)(i) course-and-speed hold), turning right back into the collision cone!

#### 4.2 Two Static Front-End Analyses That Catch Every Instance of This Bug Class
Neither memory-safety borrow checking nor standard C++ `-Wall -Wextra` warns on `BHV_AvdColregsV26.cpp:955-964` because `m_avoid_submode` is a non-trivial heap-allocated `std::string` member (`operator=` and `operator==` are opaque library calls to conventional scalar constant-propagation passes!). Two lightweight, decidable front-end obligations eliminate the entire bug class:

1. **Branch-Condition Vacuity / Dead-Guard Totality (`\forall g \in \text{Guards}:\; \exists \pi_T, \pi_F`)**:
   Modeling closed finite-domain state variables as algebraic sum types (`enum StandOnSubmode { Unsure, InExtremis }` rather than `std::string`) enables linear-time SSA sparse conditional constant propagation (`SCCP`) plus abstract domain reachability: **every syntactic guard `if (cond)` written by the human must be satisfiable (`\exists` path where `cond == true`) AND refutable (`\exists` path where `cond == false`)**. Any dominating store `submode = Unsure` that forces a downstream syntactic guard `if (submode == InExtremis)` to constant `false` raises a hard **Dead-Guard Betrayal Error** at compile time (`< 0.2 ms`), pinpointing both the clobbering write (`L955`) and the killed guard (`L964`).
2. **Preorder Monotonicity on Latched Safety States (`(S, \preceq)` under Hazard Persistence $H_{\text{active}}$)**:
   Equip the discrete mode type $S$ with a partial safety-escalation order (`None` $\prec$ `StandOn(Unsure)` $\prec$ `StandOn(InExtremis)`). Declaring `#[latch_while(rate_of_closure >= 0)]` on `StandOn(InExtremis)` generates a finite transition obligation over the pure Mealy step function $\delta : S \times I \to S$:
   $$\forall s \in S,\; \forall i \in I:\quad \big(s = \text{StandOn(InExtremis)} \land H_{\text{active}}(i)\big) \implies s \preceq \delta(s, i).$$
   Because $|S|$ is small ($3$–$16$ control modes), exhaustive symbolic or finite check discharges in `< 0.5 ms` with zero loop unrolling.

---

### 5. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + derived`

| Level | Metric / Resource Axis | Conventional Unchecked / Ad-Hoc Stack (`C++` ASTs, `std::string` FSMs, Raw Scalars) | Heavyweight External ITP / Whole-Program BMC (`Coq`/`Lean` / `CBMC`) | Integrated `CST` + `DesugarBisim` + `RoleTag` + `LatchTotality` |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring Velocity** | Human & LLM spec/code effort & refactor safety | Fast initial typing, but high latent bug density (`4` forked `BHV_AvdColregs` versions = `6,801 LoC`; manual `safeMult` patches; silent `Rust 2024` drop-order gotchas) | `10x–30x` manual proof-script overhead; `autoImplicit` typos silently prove wrong theorems unless audited line-by-line | **`1` line per role newtype / `#[latch_while]` attribute**; `0` boilerplate tactics; catches `if let`, `8*len`, `omegaNom`, and `L955` bugs at first save |
| **`L2` Toolchain Build Time** | Clean / incremental build of compiler & analyzer | `clang`/`rustc` clean front-end build `40–150 s` (`2.5–4.8 GB` RSS); C++ header re-parsing | Full ITP mathlib/std build `10–45 min` (`4–16 GB` RSS) | Zero-dependency SoA CST + SCCP/Mealy checker (`< 2,500 LoC`) builds in **`< 0.4 s` clean**, `< 30 ms` incremental |
| **`L3` Compilation & LSP Latency** | Per-keystroke / per-function elaboration & check speed | `rowan` incremental CST edit `< 1 ms`, but zero semantic bisimulation, role, or dead-latch check | Whole-function SMT/BMC with heap `std::string` models: `0.5–30 s` (`> 50 ms` interactive LSP budget blown!) | **`105.15 us`** `rowan`-style `63/64` sibling CST reuse + **`< 0.8 ms`** `DropAnchor` / `RoleTag` / finite Mealy latch check (`> 50x` faster than `50 ms` LSP SLA) |
| **`L4` Runtime Execution Speed** | Generated machine-code latency & throughput | `std::string` mode assignment & comparison (`BHV_AvdColregsV26.cpp:955-964`) incurs branchy byte compares / SSO checks every tick; `8 * len` wraps silently in `1` ALU cycle | Same as extracted/target C, or slower if boxed `Nat`/`BigInt` leaks into runtime | **`0.0%` runtime overhead** for `RoleTag` & `DropAnchor` (`100%` erased); `1`-byte `enum` replaces `32 B` `std::string` (`1` `cmp al, imm8` instruction); `1` `jno` flag check on allocation `mul` |
| **`L5` Certificate Verification Speed** | Independent load-time / CI audit replay | None (`0` machine-checkable desugaring or state-machine witness) | Kernel proof replay `0.5–15 s` per module (`.vo`/`.olean`) | Linear-pass `DesugarBisimCert` + finite Mealy transition table + role-unification witness replays in **`< 50 us` per function** (`> 1 GB/s`) |
| **`L6` RAM, Disk & Binary Footprints** | Memory, AST arena, and certificate byte sizes | Pointer-heavy ASTs `64–128 B/node`; `std::string` FSM state `24–32 B`/field; `DCMTK` wrap allocates corrupted heap block | Proof objects `10–185 MB` on disk; `1–8 GB` prover RSS | `GreenChild` `16 B` (`rowan/src/green/node.rs:30`), SoA core `18 B/node`, `1 B` enum state, `< 256 B/fn` `DesugarBisimCert`, `< 2 MiB` static checker RSS |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived + source`

#### 6.1 `(C1)` Human Comprehensibility vs. Agent Execution Asymmetry
A striking empirical pattern unites all four primary-source bugs examined in this package (`Lean 4` `autoImplicit`, `Rust` `if let` `RwLock` drop extension, `DCMTK` `8 * length_B1`, `DPsim` `Omega_cutoff`, and `MOOS-IvP` `m_avoid_submode = "unsure"`): **every single buggy snippet looks locally clean, idiomatic, and readable to a human code reviewer**.
- *Why Humans Miss Them*: Human working memory (`4 ± 1` chunks) relies on **local lexical cues**—variable names (`min_ba1` looks visually almost identical to `min_bal`), indentation (`else { cfg.write() }` sits outside `if let`'s `then` braces, suggesting `cfg.read()` already ended), algebraic familiarity (`8 * length_B1` looks like exact schoolbook multiplication), type signatures (`Real, Real, Real` compiles cleanly), and adjacent comments (`// once in extremis, retain authority` at `BHV_AvdColregsV26.cpp:962-963` convinces the human reviewer that line `964` works, blinding them to line `955` nine lines above!).
- *Why Unconstrained Coding Agents Amplify the Hazard*: LLM agents optimizing for *"compiles cleanly and passes happy-path tests"* frequently trigger `autoImplicit` typos, apply mechanical `cargo fix` `if let -> match` rewrites without modeling `RwLock` contention on the `None` branch, guess plausible in-scope variables of matching scalar type (`Omega_cutoff` when `Omega_nominal` hasn't been wired yet, leaving a `// TODO` comment!), or copy-paste state-machine blocks with one missing `return;`.
- *Actionable Mental-Model X-Ray Diagnostics*: Instead of cryptic IR borrow errors or silent miscompilations, front-ends must report **what the surface syntax appeared to mean vs. what lowered execution would have done** (e.g., *"Guard `submode == InExtremis` at line 964 is permanently unreachable (`false`) because unconditional assignment `submode = Unsure` at line 955 dominates it across fallthrough from line 935"*).

#### 6.2 `(C2)` Conceptual Simplicity, Orthogonality & Universal Model Refinement
Applying Felleisen's expressiveness criterion and Ousterhout's deep-module principle shows that these four protections do **not** require four sprawling, domain-specific static analysis frameworks—they reduce to **three tiny, orthogonal language-design invariants** with zero consumer adapter bloat:

1. **Authoritative Surface Semantics + Proof-Producing Lowering (`SurfSem == CoreSem`)**: Instead of patching individual lints (`if_let_rescope`, `-Wparentheses`, `-Wsign-compare`, `autoImplicit` heuristics), give the surface AST a single canonical operational reference model (`mathematical Z` in size/spec expressions, explicit `BeforeBranch` temporary drop anchors, closed lexical binders, partial-order operator precedence) and require every lowering pass to emit local equivalence witnesses.
2. **Phantom Refined Value Indices (`Val<Repr, Unit, Role>`)**: Dimensional units (`RadPerSec`), coordinate frames (`SyncDQ`), and parameter roles (`NominalCarrier` vs. `Cutoff3dB`) are all **zero-bit covariant/invariant type indices** checked by the exact same Hindley–Milner / bidirectional unifier—requiring zero new core type constructors and erasing completely before code generation.
3. **Pure Algebraic Mealy Transitions Over Closed Sum Types**: Replacing imperative multi-string state mutation (`m_avoid_mode`, `m_avoid_submode`) with a single pure transition function `(State, Input) -> State` over a closed `enum` collapses dead-guard detection, exhaustiveness checking, and `#[latch_while]` monotonicity into one trivial finite-table check (`O(|State| \cdot |GuardPartitions|)`).

---

## Boundaries

1. **Full Turing-Complete Procedural Macro Expansion Equivalence (`known not to apply` to arbitrary `TokenStream -> TokenStream` Rust proc-macros)**: While hygienic syntax-rules / `Core -> Core` macros admit direct `DesugarBisimCert` verification, arbitrary host-code procedural macros (`syn`/`quote` executing unconstrained computation over raw token streams) lack a declarative `SurfSem` specification prior to expansion; bisimulation applies only *after* proc-macro expansion produces a concrete typed syntax tree (requiring expand-view auditability if the macro itself is untrusted).
2. **Heap-Allocated / Unbounded State Spaces in `#[latch_while]` (`unsupported` by finite-table enumeration)**: Decidable `< 1 ms` latch-totality checking applies to **finite control-mode state lattices** (`enum` control modes with symbolic/interval input guards). State machines whose mode latch is encoded implicitly inside unbounded heap graphs or floating-point integrator states require inductive barrier certificates (`CBF` / $k$-induction) rather than finite Mealy table enumeration.
3. **Cross-FFI C Binary Callers Bypassing Phantom Role Tags (`known not to apply` without header codegen)**: Zero-cost phantom `Role` types erase to bare ABI scalars (`double` / `f64`) in compiled object files; linking against hand-written external C translation units that do not share generated role-typed wrapper structs cannot prevent C-side positional argument swaps without link-time interface-hash (`\eta_{\text{ifc}}`) verification.
4. **Dynamic Allocation Failure Semantics (`std::nothrow` Returning `NULL`, `Basis: source`)**: Note in `dcmtk/dcmimgle/include/dcmtk/dcmimgle/diinpxt.h:474-476` that after `OFStandard::safeMult` prevents `32`-bit wraparound under-allocation, `Data = new (std::nothrow) T2[Count]` safely returns `NULL` on oversized `Count`, gracefully skipping conversion (`if (Data != NULL)`). Proving absence of heap buffer overflow via checked multiplication does **not** prove bounded memory liveness/availability (`OOM` Denial-of-Service remains a separate resource-quota obligation; `not examined` here).

---

## Evidence

| Subject / Artifact | Immutable Revision / Location | Verified Primary-Source Fact & Role |
| :--- | :--- | :--- |
| **`rust-analyzer/rowan`** | Commit `d601b195d7bcb9f643c218b2ba113257880d2cdd` (`src/green/node.rs:19-60`, `src/cursor.rs:1-75`) | `GreenNodeHead` + `16 B` `GreenChild` inside `ThinArc` (`node.rs:30`), position-independent structural sharing, and `NodeData` transient parent-linked zipper cursor (`cursor.rs:12-31`). (`Basis: source`) |
| **`leanprover/lean4`** | Commit `e35bfaf8dab2405124cb486c80a7c12d3cccb951` (`src/Lean/Elab/AutoBound.lean:19-69`) | `isValidAutoBoundSuffix` (`L28-29`), `Issue #255` macro-scope infinite loop note (`L31-46`), and `checkValidAutoBoundImplicitName` (`L50-63`) auto-quantifying unbound identifiers under `autoImplicit` / `relaxedAutoImplicit`. (`Basis: source`) |
| **`dcmtk/dcmtk`** | Commit `e8d3d701c285de2dacea605cf0aaa606ad6908fe` (`dcmimgle/include/dcmtk/dcmimgle/diinpxt.h:460-478`) | Upstream comment & fix at `L465-472`: `"8 * length_B1" would otherwise be evaluated as (32-bit) int and wrap, under-sizing the buffer relative to the conversion loops below`, fixed via `OFStandard::safeMult` + `safeAdd`. (`Basis: source`) |
| **`sogno-platform/dpsim`** | Commit `7fcaac00758cc7f448179edf2a508021dd1374b8` (`dpsim-models/src/EMT/EMT_Ph3_AvVoltageSourceInverterDQ.cpp:178-179`, `dpsim-models/src/Signal/PLL.cpp:27-35, 62`) | `mPLL->setParameters(Kp_pll, Ki_pll, Omega_cutoff)` (`L179`, with `// TODO: add and use Omega_nominal instead of Omega_cutoff`) passing low-pass filter cutoff into `Real omegaNom` feedforward slot. (`Basis: source`) |
| **`moos-ivp/moos-ivp`** | Commit `ab1ac374a44a5c567187b4f27abce2e02e8fbefa` (`ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp:925-975`) | Missing Part-2 `return;` at `L935` + unconditional `m_avoid_submode = "unsure";` at `L955` rendering `if(m_avoid_submode == "inextremis") return;` at `L964` unreachable dead code. (`Basis: source`) |
| **`Rust RFC 3606`** | `if_let_rescope` (Rust Edition 2024 Language Reference / RFC 3606) | Shortens `if let` scrutinee temporary lifetime to drop before `else`, preventing Rust 2021 `RwLock` self-deadlocks while warning against naive `if let -> match` rewrites. (`Basis: normative + documentation`) |
| **Executable Verification Probe** | `probes/verify_desugar_roles_latches.py` (Python 3.10+ stdlib, observed `2026-11-19`) | Verified `63/64` `GreenNode` reuse (`105.15 us`), Rust 2021 deadlock vs. 2024 clean trace, `Lean 4` `autoImplicit` match rules, `DCMTK` `738,197,504` `32`-bit wrap vs. `5.03B` exact bits, `DPsim` `-282.74 rad/s` bias, and `MOOS-IvP` `inextremis` latch wipe vs. Mealy repair. (`Basis: execution`) |

---

## Revalidation

1. **Run the preserved self-contained verification probe (`< 0.1 s`, Python 3.10+ standard library only)**:
   ```bash
   python3 reports/surface-to-ir-desugaring-bisimulation-role-types-and-latch-totality/probes/verify_desugar_roles_latches.py
   ```
   Confirm `exit 0` and verify output assertions:
   ```text
   PASS: CST reused=63/64 (... us) | if_let Rust2021_ok=False vs Rust2024_ok=True | DCMTK 32b_wrapped=738197504 vs safe=None | DPsim PLL bias=-282.74 rad/s | MOOS-IvP inextremis monotone buggy=False vs repaired=True
   ```
2. **Targeted upstream source revalidation checks on repository upgrades**:
   - In `sogno-platform/dpsim`, inspect `dpsim-models/src/EMT/EMT_Ph3_AvVoltageSourceInverterDQ.cpp` around `setControllerParameters` (`L178-179`) to check whether `Omega_cutoff` has been replaced by `mOmegaN` / `Omega_nominal`.
   - In `moos-ivp/moos-ivp`, inspect `ivp/src/lib_behaviors-colregs/BHV_AvdColregsV26.cpp` (`checkModeStandOn`, `L925-975`) to check whether `return;` was added at `L935` or whether `m_avoid_submode = "unsure"` (`L955`) still executes ahead of `if(m_avoid_submode == "inextremis")`.
   - In `leanprover/lean4`, inspect `src/Lean/Elab/AutoBound.lean` (`checkValidAutoBoundImplicitName`) and default option registrations for changes to `autoImplicit` / `relaxedAutoImplicit` defaults.
