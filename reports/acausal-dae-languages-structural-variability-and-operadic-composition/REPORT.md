# Acausal DAE Languages: Structural Index Reduction, Structural Variability, Co-Simulation Interfaces, and Operadic Composition (Modelica, ModelingToolkit, FMI, Port-Hamiltonian Systems, AlgebraicJulia)

## Summary

An acausal (equation-based) modeling language states components as undirected equations over connector variables and decides only after composition which equation computes which variable. Every hard property of the result is therefore a property of the *composite*: the number of equations and unknowns, the differentiation index, the set of state variables, and the algebraic loops. The findings below are organized around what does and does not survive composition and around what a compiler must do before a numerical solver can run.

- **Index is not compositional.** Two capacitor models that are each structural index 1 become index 2 when their pins are joined, because `connect` adds an equality between two differentiated variables. The specification says the same thing in words: many models "have a DAE index of 2 or 3, i.e., the overall number of states of the model is less than the sum of the states of the sub-components".
- **Structural analysis is the same computation under two names and can be wrong in two directions.** Pantelides' algorithm and Pryce's Sigma-method inspect only which derivative orders occur where. (a) They can *over-differentiate*: for a family of linear constant-coefficient systems built for this report, the differentiation index is 1 for every size while the algorithm differentiates one equation `k` times and reports structural index `k+1`; this is the phenomenon of Reißig, Martinson and Barton (2000). (b) They can *fail silently unless the Jacobian is checked*: `x1'+x2'+x1 = f1, x1'+x2'+x2 = f2` is reported as an index-0 system with 2 degrees of freedom, its system Jacobian has rank 1, and the true index is 1; subtracting one equation from the other repairs the analysis.
- **Production tooling compensates with a linear pre-pass, not with a decision procedure.** StateSelection.jl (the engine behind ModelingToolkit 11) runs "structural singularity removal" on the integer-coefficient linear subsystem before Pantelides, uses fraction-free elimination when the dummy-derivative Jacobian is an integer matrix, falls back to graph matching otherwise, warns "The DAE system is singular!" on rank deficiency, and lists dynamic pivoting and polynomial Jacobians as unimplemented.
- **Modelica 3.6 fixes the equation count, not the structure.** Conditional equations whose condition is not a parameter expression must have the same number of equations in each branch, and every non-partial model must be locally balanced; yet the same specification describes the flattened result as a hybrid DAE in which discrete variables may disable parts of the system. How mode changes are analyzed is left to tools. Hydra (Functional Hybrid Modelling) instead rebuilds, re-flattens and re-JIT-compiles the whole system at every event and does no symbolic index reduction.
- **FMI turns an acausal model into a causal C interface whose every advanced capability is optional and off by default.** State save/restore, directional and adjoint derivatives, variable step size, intermediate update, early return and event mode all default to `false` in the 2.0.5 and 3.0.2 schemas. An algebraic loop at a co-simulation communication point cannot be solved by get/set calls; it requires restoring a saved state and repeating the step. Missing dependency information must be read as "every output depends on every input".
- **Explicit co-simulation manufactures energy.** In the probe, a lossless two-mass oscillator split across two units with held inputs multiplies its energy by `1.3e3` (`H = 0.05`), `2.2e6` (`H = 0.1`) and `4.3e12` (`H = 0.2`) over 200 time units; three fixed-point passes per step, which need state restore, hold the energy ratio within `1e-4` of 1.
- **Energy balance composes where index does not.** A power-conserving interconnection of port-Hamiltonian systems is again port-Hamiltonian, with summed Hamiltonians and united dissipation; the same source notes that such interconnections "commonly" produce algebraic constraints. A coupling that is not skew-symmetric loses the guarantee (probe: `dH/dt` reaches `+60`).
- **Operadic composition composes syntax by colimit; semantics is a separate claim per formalism.** Catlab composes structured multicospans along an undirected wiring diagram by computing a colimit. AlgebraicDynamics' resource sharers glue state variables and *add* vector fields, so composites stay ordinary differential equations by construction, which is a different law from Modelica's potential-equality and flow-sum connection. Decapodes composes PDE diagrams the same way and compiles them through the discrete exterior calculus; its documentation treats numerical stability as something found by running the model.

## Applicability

The subjects in `REPORT.json` are independent artifacts examined side by side; the report compares them and makes no claim about running them together.

- **Modelica**: the LaTeX sources of Language Specification 3.6 at tag `v3.6`. Tag `v3.7` exists in the same repository and was not examined. Statements marked normative are from the specification's main text; text inside the specification's `nonnormative` environments and the appendix "Modelica DAE Representation" is reported as documentation. No Modelica tool was run, so nothing here describes Dymola or OpenModelica behavior.
- **FMI**: the AsciiDoc sources and XML schemas of the standard at tags `v2.0.5` and `v3.0.2` (the newest 2.0.x and 3.0.x tags present on the observation date). Behavior shared by both versions and behavior specific to one is separated in section 7. No FMU was built or imported.
- **ModelingToolkit.jl 11.48.0 and StateSelection.jl 1.11.1**: source and README/NEWS at the pinned revisions. `Project.toml` of ModelingToolkit requires StateSelection `1.10.5`-compatible versions; the StateSelection revision examined (1.11.1) is the repository head on the observation date, not necessarily the version a given ModelingToolkit installation resolves. No Julia code was executed.
- **Hydra 0.4.3 and Modelyze 1.14**: source, README and bundled examples; neither was built. The research papers on Functional Hybrid Modelling and the Modelyze technical report (UCB/EECS-2012-173) were not read.
- **Catlab.jl 0.17.6, AlgebraicDynamics.jl 0.2.2, Decapodes.jl 0.6.9**: source and documentation at the pinned revisions; not executed. Decapodes delegates diagram syntax to DiagrammaticEquations.jl and mesh operators to CombinatorialSpaces.jl, neither of which was examined.
- **Papers**: abstracts (Crossref or arXiv) for Pantelides 1988, Mattsson and Söderlind 1993, Reißig, Martinson and Barton 2000, Benveniste, Caillaud and Malandain (arXiv:2008.05166), Caillaud, Malandain and Thibault (HSCC 2020), Baez and Courser, Libkind et al., Morris et al.; the introduction, the definitions with the pendulum example, and the opening of the failure discussion of Tan, Nedialkov and Pryce (arXiv:1608.06691, within sections 1-3); Definition 2.1, section 2.7 and the opening of chapter 6 of van der Schaft and Jeltsema (2014) from a full-text copy. Pryce's 2001 paper defining the Sigma-method was identified by metadata only; the definitions used here are quoted from Tan, Nedialkov and Pryce, of which Pryce is a co-author.
- **Execution evidence** is the Python probe under Evidence. It implements the structural algorithms and small numerical experiments from their definitions; it executes none of the subject tools. Its linear-algebra results are exact (rational arithmetic); its simulations use a fixed-step classical Runge-Kutta scheme and are statements about those specific experiments.

## Findings

### 1. What "acausal" means normatively (Modelica 3.6)

- **Connection equations.** Each connection set generates, for variables that are neither `flow` nor `stream`, the equalities `a1 = a2 = ... = an`, and for `flow` variables the zero-sum `z1 + z2 + (-z3) + ... + zn = 0`, with sign +1 for inside connectors and -1 for outside connectors. A connection set contains only flow or only non-flow variables. For a non-partial, non-expandable connector class the number of flow variables must equal the number of variables that are neither `parameter`, `constant`, `input`, `output`, `stream` nor `flow` (so potentials and flows come in pairs). Flow variables of operator-record type require addition, negation and a zero that "should define an additive group". Basis: normative (`chapters/connectors.tex`).
- **Balance.** A `model` or `block` is *locally balanced* if its local number of unknowns equals its local equation size "for all legal values of constants and parameters"; all non-partial models and blocks must be locally balanced, from which the specification derives the guarantee that all simulation models are *globally balanced*. Basis: normative (`chapters/classes.tex`, section "Balanced Models").
- **Perfect matching rule** (previously "single assignment rule"): "There must exist a perfect matching of variables to equations after flattening, where a variable can only be matched to equations that can contribute to solving for the variable". Basis: normative (`chapters/equations.tex`).
- **Counting is not solvability.** The specification's capacitor example is 5 equations in 5 unknowns; it notes that replacing the constitutive equation by `C*der(u) = 0` keeps the model balanced "but the equations would be singular". The introduction adds: "satisfying the semantic restrictions does not guarantee that the model can be initialized from the initial conditions and simulated", and "The Modelica specification does not define how to simulate a model. However, it defines a set of equations that the simulation result should satisfy as well as possible." Basis: documentation (non-normative example and introduction).
- **Index reduction is assumed, not specified.** "Many Modelica models ... are higher index systems, and can only be reasonably simulated if symbolic index reduction is performed"; the DAE appendix says "the algorithm of Pantelides should to be applied to differentiate certain parts of the equations in order to reduce the index" (wording as in the source). A tool "may reject simulating a model if parameters cannot be evaluated during translation". The only language-level handles are the `stateSelect` attribute with values `never`, `avoid`, `default`, `prefer`, `always`, and `reinit(x, expr)`, which is legal only inside a `when`-equation and "implies `stateSelect = StateSelect.always`" on `x`. Basis: normative for the attribute and `reinit`; documentation for the appendix.

Derived reading: the language-level contract is a counting discipline plus a matching condition; index, state selection and numerical nonsingularity are quality-of-implementation matters. A component-level check (local balance) therefore cannot certify the composite beyond equation count.

### 2. Structural analysis: one computation, two presentations

**Sigma-method** (definitions as given by Tan, Nedialkov and Pryce). For `n` equations `f_i = 0` in `n` variables `x_j`:

- *Signature matrix* `Sigma = (sigma_ij)`: `sigma_ij` is the order of the highest derivative of `x_j` occurring in `f_i`, or `-inf` if `x_j` does not occur.
- *Highest-value transversal* (HVT): `n` positions, one per row and column, maximizing the sum of entries; the maximum is `Val(Sigma)`. Finite value means structurally well posed.
- *Offsets*: integers `c_i >= 0`, `d_j` with `d_j - c_i >= sigma_ij` everywhere and equality on an HVT; the elementwise smallest solution is the canonical offset pair. `c_i` is the number of times equation `i` is differentiated.
- *System Jacobian*: `J_ij = d f_i / d x_j^(sigma_ij)` if `d_j - c_i = sigma_ij`, else 0. The method *succeeds* if `J` is nonsingular at a consistent point.
- *Structural index and degrees of freedom*: `nu_S = max_i c_i + (1 if min_j d_j = 0 else 0)`; `dof = Val(Sigma) = sum_j d_j - sum_i c_i`.

The same source states that Pantelides' algorithm and the Sigma-method "both produce the same structural index, when applied to first-order systems", that this index "is an upper bound for the differentiation index, and often they are the same", and that when the Sigma-method fails with an identically singular system Jacobian "Pantelides's algorithm fails as well". Basis: documentation (paper text).

**Pantelides' algorithm** as implemented in `StateSelection.jl/src/pantelides.jl`: for each equation, try to extend a matching between equations and *highest-derivative* variables by an augmenting path; if none exists, every variable and equation visited by the search is differentiated (new derivative variables and new equations are appended, and the assignment is transferred to the derivatives), and the search repeats from the differentiated equation. It throws `InvalidSystemException("System is structurally singular")` when non-empty equations outnumber eligible variables, and aborts after `maxiters = 8000` rounds with the comment that this "should never be reached, otherwise, the index would be on the order of thousands". Basis: source.

**Where it sits in ModelingToolkit 11.48.0.** `NEWS.md` records that "index reduction, structural singularity removal and tearing" moved to StateSelection.jl and ModelingToolkitTearing.jl, which "are AGPL licensed", and that the `mtkcompile` remaining in ModelingToolkitBase "does not perform index reduction and requires that all differential equations are explicit in the derivative". In the full package, a fully determined system goes through `dummy_derivative(sys, state)`, which reaches `StateSelection.dummy_derivative_graph!`; that function first runs `pantelides!` and then selects dummy derivatives. Systems that are not fully determined go to tearing only. Basis: source (`src/systems/systemstructure.jl`, `src/structural_transformation/symbolics_tearing.jl`) + documentation (`NEWS.md`).

Execution check of the equivalence on the report's examples (probe section A): the two implementations return identical differentiation counts wherever both were run. For the Cartesian pendulum (`x'' = lambda x`, `y'' = lambda y - g`, `x^2 + y^2 = L^2`) both give `c = (0,0,2)`, and the Sigma-method gives `d = (2,2,0)`, `nu_S = 3`, `dof = 2`, the values printed in the cited paper's Example 1.

### 3. The two failure directions of structural analysis

**Over-differentiation at fixed true index.** Reißig, Martinson and Barton: "the structural index of a linear differential-algebraic equation (DAE) with constant coefficients and with index 1 may be arbitrarily high ... Pantelides' algorithm applied to DAEs of index 1 may perform an arbitrarily high number of iterations and differentiations." Basis: documentation (abstract).

A family exhibiting this, constructed for this report (whether it coincides with the paper's own example was not checked): for `k >= 1` and `n = 2k+1` unknowns,

```text
x_{2b}' + x_{2b+1}' + x_{2b-1} = a_{2b-1}(t)      b = 1..k
x_{2b}' + x_{2b+1}' + x_{2b}   = a_{2b}(t)        b = 1..k
                      x_{2k+1} = a_{2k+1}(t)
```

| `k` | `n` | Pantelides differentiation counts `c` | structural index | differentiation index (derivative array, exact) |
|---|---|---|---|---|
| 1 | 3 | `(0,0,1)` | 2 | 1 |
| 2 | 5 | `(0,0,1,1,2)` | 3 | 1 |
| 3 | 7 | `(0,0,1,1,2,2,3)` | 4 | 1 |
| 4 | 9 | `(0,0,1,1,2,2,3,3,4)` | 5 | 1 |

For `n <= 7` the probe also confirms the Sigma-method system Jacobian has full rank, so this is the "succeeds but over-differentiates" case: the analysis is usable, only wasteful. The cause is visible in the equations: each pair shares the expression `x_{2b}' + x_{2b+1}'`, whose difference is an algebraic relation that a pattern-only analysis cannot see. Basis: execution; the explanation is derived.

**Failure that looks like success.** For `x1' + x2' + x1 = f1`, `x1' + x2' + x2 = f2` the signature matrix is all ones: `Val = 2`, `c = (0,0)`, `d = (1,1)`, structural index 0, 2 degrees of freedom. The system Jacobian `[[1,1],[1,1]]` has rank 1 and the exact differentiation index is 1. After replacing the second equation by the difference of the two, the analysis gives `c = (0,1)`, index 1, 1 degree of freedom, and a nonsingular Jacobian. Basis: execution. Tan, Nedialkov and Pryce describe the general situation: the methods "can fail on simple, solvable DAEs and give incorrect structural information including the index", for example when the pendulum equations are premultiplied by a random nonsingular constant matrix; "nonsingularity of the Jacobian produced by SA indicates a success". Basis: documentation.

**What a production implementation does about it** (`StateSelection.jl`):

- README, "Structural Singularity Removal": a pre-pass before Pantelides, motivated thus: "because pantelides is a structural algorithm, it can accidentally fail to fully reduce the index for systems which have full structural rank, but are numerically singular. One common source of such systems are conservation laws commonly used in hierachical modeling tools ... the numerical singularity is static and apparent in the constant linear coefficients of the integer-linear subsystem". The pass "applies a change of basis" to that subsystem "to make the numerical rank-deficiency structurally apparent". The row operation in the previous paragraph is an instance.
- `dummy_derivative_graph!` (`src/partial_state_selection.jl`) carries the comment "TODO: making the algorithm more robust. 1. If the Jacobian is a integer matrix, use Bareiss to check linear independence. (done) 2. If the Jacobian is a single row, generate pivots. (Dynamic state selection.) 3. If the Jacobian is a polynomial matrix, use Gröbner basis (?)". With an integer Jacobian it selects dummy derivatives by a fraction-free null-space computation; otherwise by bipartite matching; if the rank found differs from the number of rows it emits `@warn "The DAE system is singular!"` and continues.

Basis: documentation (README) + source. Derived: outside the integer-linear subsystem the implementation trusts structure; cancellations that depend on parameter values or nonlinear identities are not detected at compile time by this pipeline.

### 4. After the differentiations: drift, dummy derivatives, pivots

Mattsson and Söderlind (abstract): parts of the DAE are differentiated and appended; "For each additional equation, a derivative is selected to be replaced by a new algebraic variable called a dummy derivative. The resulting augmented system is at most index 1, but no longer overdetermined ... No constraint stabilization is necessary in the subsequent numerical treatment." The StateSelection README states the selection problem's stakes: Pantelides "produces systems that are over-determined in their differential relations ... the choice of which relations to remove can radically affect the numerical properties", and "a numerical integrator may need to switch the set of chosen states dynamically at runtime (known as dynamic state selection)". Basis: documentation.

Probe section B on the unit pendulum (classical Runge-Kutta, 20 time units, released from `(0.6, -0.8)` at rest):

| Formulation | `h = 1e-2` | `h = 1e-3` |
|---|---|---|
| Integrate `x, y, x', y'` with the multiplier taken from the twice-differentiated constraint; residual `abs(x^2 + y^2 - 1)` | `1.493e-05` | `1.494e-09` |
| Dummy-derivative form: integrate `x, x'` only; `y` and `y'` recomputed from the constraint and its first derivative | 0 by construction | 0 by construction |

The differentiated formulation satisfies only the second derivative of the constraint, so the constraint itself is met to integration accuracy (fourth order here) and nothing pulls it back. The dummy-derivative form has no drift but divides by `y`: started at the bottom with speed 5 (enough to rise above the horizontal), it fails at `t = 0.394` as `x -> 1`, `y -> 0`. That is the pivot whose run-time replacement the source code lists as not yet implemented and for which Modelica offers only static `stateSelect` hints. Basis: execution; the connection to the tools is derived.

### 5. Index and solvability belong to the composite

Probe section A, capacitors: a capacitor closed by a current source (`C v' = i`, `i = I(t)`) has `c = (0,0)`, `d = (1,0)`, structural index 1. Two capacitors joined at both pins (`C1 v1' = i1`, `C2 v2' = i2`, `v1 = v2`, `i1 + i2 = 0`) have `c = (0,0,1,0)`, structural index 2, exact differentiation index 2 and 1 degree of freedom instead of 2: the potential equality from `connect` must be differentiated. Basis: execution.

The port-Hamiltonian monograph makes the same observation about network modeling in general: it "admits quite arbitrary interconnection equations between the subsystems", in contrast with signal-flow modeling where inputs of one subsystem equal outputs of another, and "algebraic constraints due to interconnection constraints between the 'outputs' of the subsystems commonly arise"; its worked example is an LC circuit with two capacitors. Basis: documentation.

Derived consequences for separate compilation: (i) a component cannot be compiled to a fixed input/output function before its neighbors are known, because the neighbor decides which of its variables are states; (ii) a component boundary across which symbolic differentiation is impossible (opaque compiled code) blocks index reduction of any constraint that spans the boundary; (iii) any per-component certificate must be about something that composes, such as equation/unknown balance (section 1) or power balance (section 9).

### 6. Structural variability

- **Modelica 3.6.** "The `if`-equations in equation sections which do not have exclusively parameter expressions as switching conditions shall have the same number of equations in each branch", with the rationale that otherwise "the number of equations may change during simulation although the number of unknowns remains the same". Basis: normative. The DAE appendix nevertheless describes the semantics as a hybrid DAE "which may have discontinuities, a variable structure and/or which are controlled by a discrete-event system", in which "the number of state variables, algebraic variables and residue equations of a DAE may change at event instants by disabling the appropriate part of the DAE", and gives the event iteration (solve with `pre` values fixed; repeat until discrete variables stop changing). Basis: documentation. Derived: equation *count* is static while the *active structure* may vary, and the specification does not say how index reduction interacts with that variation.
- **Multi-mode analysis literature.** Benveniste, Caillaud and Malandain: "Multimode DAE are much more difficult than DAE. The main difficulty is the handling of the events of mode change ... Some models are well handled, others are not, with no clear boundary between the two classes"; their approach's "core is the structural analysis of multimode DAE systems", and it relies on nonstandard analysis "to cast hybrid systems dynamics to discrete time dynamics with infinitesimal step size". Caillaud, Malandain and Thibault (HSCC 2020): a structural analysis for multimode DAEs that "generalizes J. Pryce's Sigma-method to the multimode case and uses Binary Decision Diagrams (BDD) to represent the mode-dependent structure", determining "as a function of the mode, the set of latent equations, the leading variables and the state vector". The project page for the IsamDAE tool describes the two prevailing alternatives and their costs: a single mode-independent structural analysis that "often yields simulation code that is incorrect in some modes, which results in errors such as division by zero errors at runtime", or re-analysis at every mode change, which "makes it impossible to guarantee at compile time that a multimode model is structurally sound in all possible modes". Basis: documentation (abstracts and project page; papers' bodies and the tool itself not examined).
- **Hydra.** `switch sr1 ev mk` runs the signal relation `sr1` until the event expression `ev` fires and then continues with the relation that the function `mk` builds from the values at that instant (`examples/BreakingPendulum.hs`: `switch (pendulum l phi0) [fun| ... -> time - $t$ |] freeFall`). In `src/Hydra/Stages/Simulate.hs`, when the solver reports an event the simulator frees the solver and the JIT-compiled code and calls itself with the updated symbol table: event handling, flattening, validation, LLVM code generation and solver creation run again. Validation checks only that the numbers of equations and variables agree. There is no index-reduction stage; residual functions are handed to a Sundials-based solver, and the repository's `TODO` lists "Implement support for higher index systems using symbolic methods instead of currently used numerical methods" and "Impulses can be introduced in addition to events to avoid a complete code regeneration in some cases". Basis: source.
- **Modelyze.** The host language treats equations as data: Pantelides' algorithm, symbolic differentiation and index reduction are ordinary libraries written in Modelyze (`library/pantelides.moz`, `differentiation.moz`, `indexreduction.moz`), mode switching is a library-level `hybridchart` construct (`demo/breakingpendulum.moz`), and the OCaml runtime calls the Sundials IDA solver. Basis: source (file inventory and headers only).

### 7. FMI 2.0.5 and 3.0.2 as the causal foreign interface

**Capability flags** (attribute names are from the XML schemas; every one has `default="false"` unless noted):

| Capability | FMI 2.0.5 | FMI 3.0.2 |
|---|---|---|
| Save and restore complete internal state | `canGetAndSetFMUstate` | `canGetAndSetFMUState` |
| Serialize saved state | `canSerializeFMUstate` | `canSerializeFMUState` |
| Jacobian-vector products | `providesDirectionalDerivative` | `providesDirectionalDerivatives` |
| Vector-Jacobian products | absent | `providesAdjointDerivatives` |
| Variable communication step (co-simulation) | `canHandleVariableCommunicationStepSize` | `canHandleVariableCommunicationStepSize` |
| Input interpolation / intermediate access | `canInterpolateInputs` | `providesIntermediateUpdate`, `recommendedIntermediateInputSmoothness` (default 0) |
| Return before the end of the requested step | absent | `mightReturnEarlyFromDoStep`, `canReturnEarlyAfterIntermediateUpdate` |
| Event mode in co-simulation | absent | `hasEventMode` |
| Output derivatives | `maxOutputDerivativeOrder` (default 0) | `maxOutputDerivativeOrder` (default 0) |

Basis: normative (`schema/fmi2ModelDescription.xsd`; `schema/fmi3InterfaceType.xsd`). Note the spelling change `FMUstate` to `FMUState` and the plural `Derivatives` between versions.

**Rules shared by both versions.**

- *Dependencies.* If the `dependencies` attribute of an unknown is absent, "it must be assumed that the unknown depends on all knowns" (3.0.2; 2.0.5: "If not present, it must be assumed that the `Unknown` depends on all `Knowns`"). 3.0.2 restates this for loop detection: "If this data is not provided, the worst case must be assumed: all output variables depend algebraically on all input variables."
- *Loops at communication points.* In co-simulation the step function, not the getter, performs the computation, so algebraic loops at communication points "cannot be handled by an appropriate sequence of" get and set calls, unlike in initialization, event and continuous-time modes. 3.0.2: "Repeating a communication step requires to reset the FMU state to the previous communication point with `fmi3SetFMUState` and repeating the `fmi3DoStep` with new input values." 2.0.5: "Redoing a step is only possible if the FMU state has been recorded at the beginning of the current (failed) step with `fmi2GetFMUState`."
- *Rejected steps.* 2.0.5 `fmi2DoStep` may return `fmi2Discard` ("the slave computed successfully only a subinterval"); "If possible, the master should retry the simulation with a shorter communication step size", which again presupposes saved state. The argument `noSetFMUStatePriorToCurrentPoint` tells the unit that no earlier state will be restored.

**Specific to 3.0.2.**

- *Loop taxonomy.* "Artificial" loops (resolvable by ordering get/set calls using dependency information) versus "real" loops, which "might be solved iteratively, for example with a Newton method", the importer computing a residual through set/get sequences; "In Step Mode, `fmi3SetFMUState` is required to restore the FMU state before the next iteration".
- *Derivatives.* `fmi3GetDirectionalDerivative` computes `v_sensitivity = J . v_seed`; `fmi3GetAdjointDerivative` computes `v_sensitivity^T = v_seed^T . J`; listed uses include "Newton algorithms to solve algebraic loops".
- *Terminals.* Terminal member variables carry a `variableKind`: `signal` ("The values in connected terminals are intended to be equal") or `inflow`/`outflow` ("Variables which fulfill Kirchhoff's current law", with `0 = sum of inflowing quantities`). But "Algebraic loops in systems of connected FMUs are not addressed or resolved by the terminals. The FMU standard does not require that the causality of the terminal member variables in connected terminals match. This must be handled by the importer." Terminals therefore *document* acausal connector semantics on top of a causal interface; they do not restore it.
- *Early return* lets a unit stop a step before the requested end, for example when it detects an event.

Basis: normative text of the standards at the two tags, except bracketed/italic passages, which the standards mark as non-normative explanation (the loop examples and the terminal remark are of that kind).

**Derived boundary contract.** An importer that wants a mathematically meaningful coupling needs, per unit: (1) dependency information, else it must assume full feedthrough; (2) state save/restore, else it cannot iterate a loop or retry a step in co-simulation; (3) directional derivatives, else Newton iterations need finite differences across the interface; (4) for constraints spanning two units, nothing in either version: neither exposes the symbolic structure needed for the index reduction of section 5, so a coupling that would raise the index in an acausal tool appears instead as a loop over held inputs. All four are optional or absent, so the interface type alone does not tell a consumer which coupling algorithms are admissible.

### 8. What explicit coupling does to a conservative system

Probe section C. A lossless system (two unit masses, each on a unit spring, joined by a unit coupling spring) is split into unit 1 (mass 1 and the coupling spring; input: position of mass 2; output: coupling force) and unit 2 (mass 2; input: force; output: position). Each unit integrates internally with 20 Runge-Kutta micro-steps per communication step `H`.

| `H` | energy ratio after 200 time units, inputs held from the start of each step (no rollback needed) | same, three fixed-point passes per step using the mean of start and end outputs (each pass restores the saved unit states) |
|---|---|---|
| 0.2 | 4295447990353.13 | 0.999901 |
| 0.1 | 2235345.12 | 0.999999 |
| 0.05 | 1328.10 | 1.000000 |

The explicit scheme's error is not a small bias: the coupled system has no dissipation, and the lag between an output and its use as an input injects energy every step. The iterated scheme removes the growth at the cost of exactly the capability that section 7 shows to be optional. Basis: execution. The figures are for this system, this splitting and this extrapolation; other couplings (for example with damping, or force/force splitting) were not tried.

### 9. Power ports: what port-Hamiltonian structure guarantees

Definitions and theorem as stated by van der Schaft and Jeltsema:

- A *Dirac structure* on a flow space `F` with effort space `E = F*` is a subspace `D` of `F x E` with (1) `<e | f> = 0` for all `(f, e)` in `D` and (2) `dim D = dim F`. "Property (1) corresponds to power-conservation."
- "the power-conserving interconnection of port-Hamiltonian systems defines another port-Hamiltonian system"; the proof rests on the fact that "the composition of Dirac structures through a number of pairs of shared flow and effort variables leads to another Dirac structure"; "the Hamiltonian of the interconnected port-Hamiltonian system will be the sum of the Hamiltonians of its subsystems, while similarly the energy-dissipation relation of the interconnected system is obtained as the union of the energy-dissipating relations of the subsystems".
- Interconnection commonly yields port-Hamiltonian *differential-algebraic* systems (section 5).

Basis: documentation (monograph text).

Probe section D, exact rational arithmetic: two linear input-state-output systems `x_i' = (J_i - R_i) x_i + G_i u_i`, `y_i = G_i^T x_i` with `H_i = |x_i|^2 / 2`, `J_i` skew, `R_1 = diag(1,2)`, `R_2 = 0`. With the power-conserving feedback `u1 = -y2`, `u2 = y1` the coupling blocks are negatives of each other's transpose and the maximum of `dH/dt` over the integer grid `[-2,2]^4` is 0. With a gain mismatch `u2 = 3 y1` the coupling is no longer skew and `dH/dt = +60` at `x = (2,2,2,2)`. Basis: execution.

Derived comparison with sections 1 and 7: a Modelica connector pairs a potential with a flow and Kirchhoff's laws make an ideal connection power-conserving when the product of the pair is power, but the language does not require component equations to be passive, and FMI's `inflow`/`outflow` kinds carry the zero-sum convention without any effort/flow pairing. Passivity is therefore a property a consumer must establish separately in both.

### 10. Operadic composition in the AlgebraicJulia stack

- **Undirected wiring diagrams.** Catlab's schema `SchUWD` has objects `Box`, `Port`, `OuterPort`, `Junction` and maps `box : Port -> Box`, `junction : Port -> Junction`, `outer_junction : OuterPort -> Junction`. Ports have no direction; boxes sharing a junction are glued there. Basis: source (`src/wiring_diagrams/Undirected.jl`).
- **Composition is a colimit.** `oapply(composite::UndirectedWiringDiagram, cospans::AbstractVector{<:StructuredMulticospan{L}})` builds a bipartite diagram whose first-kind vertices are the junctions (as `L(foot)`) and second-kind vertices are the boxes' apexes, with one edge per port, and returns the colimit with legs for the outer ports; feet meeting at a junction must be equal ("Feet of cospans are not equal"). The dual method for multispans takes a limit. Basis: source (`src/wiring_diagrams/Algebras.jl`). This is the computational form of Baez and Courser's structured cospans: for a left adjoint `L : A -> X` between categories with finite colimits, cospans `L(a) -> x <- L(b)` form a symmetric monoidal (double) category, with circuits, Petri nets and reaction networks as examples. Basis: documentation (abstract).
- **A dynamical semantics that stays within ODEs.** AlgebraicDynamics' `oapply` for resource sharers computes the composite state set as a pushout of the port functions against the junction map and defines the composite vector field by evaluating each box on its own states and then summing the contributions that land on the same glued state ("add along junctions"); for discrete systems the *increments* are summed. Libkind et al. establish such systems as algebras of wiring-diagram operads and show "Euler's method is functorial for undirected systems". Basis: source (`src/uwd_dynam.jl`) + documentation (abstract).
- **PDE diagrams.** Decapodes composes typed diagrams of differential forms with `oapply(pattern, [Open(model, [:n, :w]), ...])`; "the output of oapply is another Decapode", so composition is hierarchical. Boundary conditions are separate components applied as masks: the generated simulation applies a boundary condition "immediately after the impacted value is computed", which "means that the boundary conditions on a variable have no immediate impact on the variables this variable is dependent on". The FAQ's recommended workflow includes discovering by a trial run that a formulation "is unstable" and reformulating. Morris et al. report solutions "consistent with state-of-the-art open source tools as demonstrated by benchmark comparisons with SU2" and "areas requiring further development". Basis: documentation (`docs/src/concepts/composition.md`, `docs/src/bc/bc_debug.md`, `docs/src/faq/faq.md`; abstract).

Derived contrast between the two connection laws. A junction shared by resource sharers means "same state variable, rates add". A Modelica connection set means "potentials equal, flows sum to zero" as *additional algebraic equations* over variables the components keep. The first never produces an algebraic constraint, so the composite of ODEs is an ODE and index questions cannot arise; the second is what produces section 5's index change. Two capacitors on a shared node illustrate that the laws are not interchangeable: the rate-adding law would give the shared voltage the sum of two independent rates `i1/C1 + i2/C2`, whereas circuit theory gives `(C1 + C2) v' = i_total`. The operadic *syntax* (a diagram and a colimit) is common to both; whether composition commutes with the intended semantics has to be shown per semantics, and for constraint-style connection it does not commute with "being an ODE of index 0".

### 11. What composes

| Property | Composes under acausal connection? | Composes under UWD gluing of resource sharers? | Composes across FMI co-simulation? | Evidence |
|---|---|---|---|---|
| Equation/unknown balance | Yes (local balance implies global balance) | Yes (pushout of state sets) | Not applicable (causal) | section 1; section 10 |
| Differentiation index | No | Trivially (always 0) | Hidden: cross-unit constraints become held-input loops | sections 5, 7, 10 |
| Structural analysis correctness | No guarantee even for one system | Not needed | Not available across units | section 3 |
| Choice of states | No (depends on neighbors; may change at run time) | Yes (union modulo gluing) | Fixed inside each unit | sections 4, 5 |
| Energy / passivity | Only if components are passive and coupling is power-conserving; not enforced by Modelica | Not addressed | Not preserved by explicit stepping | sections 8, 9 |
| Numerical stability of the discretization | Not addressed by the language | Euler's method functorial (per Libkind et al.) | No | sections 8, 10 |
| Mode structure | Count fixed, active structure varies; analysis left to tools | Not addressed | Event mode optional (3.0.2) | sections 6, 7 |

Basis: derived from the cited sections.

## Boundaries

- **Not examined**: Modelica 3.7; stream connectors, overdetermined connectors, clocked and state-machine semantics; any Modelica tool; tearing and block-lower-triangular ordering algorithms beyond their mention in StateSelection's README; initialization; FMI Scheduled Execution, clocks, and layered standards; FMI model-exchange numerics; the bodies of Pantelides (1988), Mattsson and Söderlind (1993), Reißig et al. (2000), Pryce (2001), Benveniste et al., and the HSCC papers; the IsamDAE tool; bond graphs; DiagrammaticEquations.jl and CombinatorialSpaces.jl; decorated cospans and the original operad-of-wiring-diagrams paper beyond their abstracts; mesh-quality requirements of discrete exterior calculus; any proof-assistant formalization of the algorithms.
- **Not executed**: no subject tool was run. Tool behavior is from source and documentation at the pinned revisions; the probe is an independent implementation of the published definitions.
- **Unknown**: whether the report's over-differentiation family is the one in Reißig et al.; which StateSelection version a given ModelingToolkit 11.48.0 environment resolves and whether the cited comments are identical there; how Dymola or OpenModelica handle the cancellation example; how the nonstandard-analysis treatment of mode changes computes restart values (only the abstract-level description was read); whether Decapodes offers any stability diagnostics beyond trial runs.
- **Known not to apply**: structural analysis is not a decision procedure for solvability or index (section 3 gives both a wasteful success and an undetected-unless-checked failure); local balance does not imply nonsingularity; FMI terminals do not resolve causality or loops (explicit statement in 3.0.2); the rate-adding composition of resource sharers does not model constraint coupling; Hydra at the pinned revision does not perform symbolic index reduction.
- **Unsupported by the subjects**: Modelica 3.6: conditional equations with differing equation counts under non-parameter conditions. FMI 2.0.5: adjoint derivatives, early return, event mode in co-simulation. StateSelection at the pinned revision: dynamic state selection and polynomial-Jacobian rank tests (listed as to-do). Hydra: impulses and higher-index systems by symbolic methods (listed as to-do).
- **Stronger conclusions the evidence does not establish**: that explicit co-simulation is always unstable (one conservative system, one splitting); that iterated coupling is always sufficient; that port-Hamiltonian structure is preserved by time discretization (not examined); that any tool mishandles a particular industrial model; that the all-modes structural analysis scales to a given model (the project page claims sub-exponential time for models with exponentially many modes; not reproduced).

## Evidence

All repository observations were made on 2026-11-19 from source archives of the pinned revisions; papers were read the same day.

**Repositories (path: what was read)**

- `modelica/ModelicaSpecification` @ `c1258346b941d8a67b151f1dbf3f1c6092638ba1` (tag `v3.6`): `chapters/connectors.tex` (connection-set equations; flow/non-flow rules; connector balance rule), `chapters/classes.tex` (section "Balanced Models"; capacitor example; `StateSelect` enumeration), `chapters/equations.tex` (`if`-equation rule; perfect matching rule; `reinit`), `chapters/dae.tex` (hybrid DAE simulation procedure; event iteration; index remarks), `chapters/introduction.tex`.
- `modelica/fmi-standard` @ `913d6b6908f6e6f59457bf299e875f17c818b921` (tag `v2.0.5`): `schema/fmi2ModelDescription.xsd`, `docs/2_2_common_schema.adoc` (dependencies), `docs/4_1_co-simulation_math.adoc`, `docs/4_2_co-simulation_api.adoc` (`fmi2DoStep` status values, `noSetFMUStatePriorToCurrentPoint`).
- `modelica/fmi-standard` @ `b8778deaf5b746ba4a2f6c155d53f8a33eebbd33` (tag `v3.0.2`): `schema/fmi3InterfaceType.xsd`, `docs/2_2_common_mechanisms.adoc` (sections "Algebraic Loops", "Getting Partial Derivatives"), `docs/2_4_common_schema.adoc` (capability flags, dependencies, terminals and `variableKind`), `docs/4_1_co-simulation_math.adoc` (early return), `docs/4_2_co-simulation_api.adoc` (Step Mode).
- `SciML/ModelingToolkit.jl` @ `a640aa9fdf11e8524dc2fafff6cd16eabadc3433`: `Project.toml`, `NEWS.md` (section on the split into ModelingToolkitBase), `src/systems/systemstructure.jl`, `src/structural_transformation/{pantelides.jl,symbolics_tearing.jl}`.
- `JuliaComputing/StateSelection.jl` @ `0b698cfc3732c681763c3a4be1e7e367aa4d241c`: `README.md`, `src/pantelides.jl` (`pantelides!`), `src/partial_state_selection.jl` (`dummy_derivative_graph!`), `src/singularity_removal.jl` (`structural_singularity_removal!`), `Project.toml`.
- `giorgidze/Hydra` @ `e5b59d0baff27f06368caeb1e9860f1395913ca5`: `README`, `TODO`, `Hydra.cabal`, `src/Hydra/Stages/{Simulate,Validate,JIT}.hs`, `examples/BreakingPendulum.hs`.
- `david-broman/modelyze` @ `e48c934283e683e268a9dfd0fed49d3c10277298`: `README.md`, `library/` inventory and `library/indexreduction.moz` header, `demo/breakingpendulum.moz`, `src/eval.ml` (IDA calls).
- `AlgebraicJulia/Catlab.jl` @ `692bd5e9d4b792a01bc507a59a19c2311b321359`: `src/wiring_diagrams/Undirected.jl` (`SchUWD`), `src/wiring_diagrams/Algebras.jl` (`oapply` methods).
- `AlgebraicJulia/AlgebraicDynamics.jl` @ `d5fc9e47165f5c1c83db79e30c43c6224a94d082`: `src/uwd_dynam.jl` (`oapply`, `induced_states`, `induced_dynamics`).
- `AlgebraicJulia/Decapodes.jl` @ `13c6d4525d61e07c30f54fa9d954268f725280bf`: `README.md`, `docs/src/concepts/composition.md`, `docs/src/bc/bc_debug.md`, `docs/src/faq/faq.md`.

**Papers (identifier: what was read)**

- Tan, Nedialkov, Pryce, arXiv:1608.06691v1: abstract; within sections 1-3, the introduction, the Sigma-method definitions, the pendulum example, and the first failure examples.
- van der Schaft and Jeltsema, DOI `10.1561/2600000002`: Definition 2.1, section 2.7, opening of chapter 6.
- Abstracts with Crossref-confirmed metadata: Pantelides, DOI `10.1137/0909014`; Mattsson and Söderlind, DOI `10.1137/0914043`; Reißig, Martinson, Barton, DOI `10.1137/S1064827599353853`. Abstract via the authors' project page, metadata via Crossref: Caillaud, Malandain, Thibault, DOI `10.1145/3365365.3382201`; the IsamDAE description is from the same project site (`team.inria.fr/hycomes/software/isamdae/`, read 2026-11-19, not an immutable source).
- arXiv abstracts: Benveniste, Caillaud, Malandain, arXiv:2008.05166v2; Baez and Courser, arXiv:1911.04630v3; Libkind, Baas, Patterson, Fairbanks, arXiv:2105.12282v3 (DOI `10.4204/EPTCS.372.14`); Morris et al., arXiv:2401.17432v1 (DOI `10.1016/j.jocs.2024.102345`).
- Metadata only, cited for identification: Pryce, DOI `10.1023/A:1021998624799`; Benveniste et al., HSCC 2017, DOI `10.1145/3049797.3049806`; Fong, arXiv:1502.00872; Spivak, arXiv:1305.0297; Patterson, Lynch, Fairbanks, DOI `10.32408/compositionality-4-5`; Ma et al., arXiv:2103.05244.

**Probe (execution).** Environment: CPython 3.13.15, Linux x86_64, standard library only. Save the following as `/tmp/daeprobe/probe_dae.py` and run `python3 /tmp/daeprobe/probe_dae.py` (about 15 seconds). Section A implements the Sigma-method, Pantelides' algorithm and an exact derivative-array index test for linear constant-coefficient systems `A x' + B x = f(t)`; B integrates the pendulum; C is the co-simulation experiment; D the port-Hamiltonian check.

```python
#!/usr/bin/env python3
"""Acausal-DAE micro-probes (Python 3.10+, standard library only; exact rational linear algebra)."""
import itertools, math
from fractions import Fraction as Fr

# --- A. Structural analysis two ways: Pryce's Sigma-method and Pantelides' algorithm ---
def sigma_method(S):                       # S[i][j] = highest derivative order of x_j in f_i, or None
    n = len(S); best = None
    for p in itertools.permutations(range(n)):          # highest-value transversal by brute force
        if all(S[i][p[i]] is not None for i in range(n)):
            v = sum(S[i][p[i]] for i in range(n))
            if best is None or v > best[0]: best = (v, p)
    if best is None: return None                         # structurally singular
    val, p = best; c = [0] * n
    while True:                                          # smallest offsets: d_j - c_i >= S_ij, equality on HVT
        d = [max(S[i][j] + c[i] for i in range(n) if S[i][j] is not None) for j in range(n)]
        c2 = [d[p[i]] - S[i][p[i]] for i in range(n)]
        if c2 == c: break
        c = c2
    return dict(val=val, c=c, d=d, index=max(c) + (1 if 0 in d else 0))
def pantelides(S):                         # returns how many times each equation gets differentiated
    n = len(S); var_id = {}; vdiff = []; edges = []; ediff = []; assign = {}
    def var(j, o):
        for k in range(o + 1):
            if (j, k) not in var_id: var_id[(j, k)] = len(vdiff); vdiff.append(None)
            if k: vdiff[var_id[(j, k - 1)]] = var_id[(j, k)]
        return var_id[(j, o)]
    for i in range(n):
        edges.append({var(j, k) for j in range(n) if S[i][j] is not None for k in range(S[i][j] + 1)}); ediff.append(None)
    def augment(e, ce, cv):
        ce.add(e)
        for v in edges[e]:
            if vdiff[v] is None and v not in assign: assign[v] = e; return True
        for v in edges[e]:
            if vdiff[v] is None and v not in cv:
                cv.add(v)
                if augment(assign[v], ce, cv): assign[v] = e; return True
        return False
    inv = {}
    for i in range(n):
        e = i
        while True:
            ce, cv = set(), set()
            if augment(e, ce, cv): break
            for v in list(cv):
                j, o = next(k for k, x in var_id.items() if x == v); var(j, o + 1)
            for q in list(ce):
                ediff[q] = len(edges); edges.append(set()); ediff.append(None)
                for v in edges[q]: edges[ediff[q]] |= {v, vdiff[v]} if vdiff[v] is not None else {v}
            for v in cv: assign[vdiff[v]] = ediff[assign[v]]
            e = ediff[e]
    cnt = []
    for i in range(n):
        k, e = 0, i
        while ediff[e] is not None: e = ediff[e]; k += 1
        cnt.append(k)
    return cnt
def rank(M):
    M = [r[:] for r in M]; r = 0
    for c in range(len(M[0]) if M else 0):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r
def diff_index(A, B, kmax=8):              # differentiation index of A x' + B x = f(t) from the derivative array
    n = len(A)
    if rank(A) == n: return 0
    for nu in range(1, kmax + 1):          # rows: nu+1 time-derivatives of the system; unknowns x', ..., x^(nu+1)
        D = [[Fr(0)] * (n * (nu + 1)) for _ in range(n * (nu + 1))]
        for b in range(nu + 1):
            for i in range(n):
                for j in range(n):
                    D[b * n + i][b * n + j] = Fr(A[i][j])
                    if b: D[b * n + i][(b - 1) * n + j] = Fr(B[i][j])
        if rank(D) == n + rank([row[n:] for row in D]): return nu      # x' uniquely determined
    return None
def struct_of(A, B): return [[1 if A[i][j] else (0 if B[i][j] else None) for j in range(len(A))] for i in range(len(A))]
def sysjac(A, B, r):                       # Sigma-method system Jacobian d f_i / d x_j^(d_j - c_i)
    n = len(A); o = lambda i, j: r['d'][j] - r['c'][i]
    return [[Fr(A[i][j]) if o(i, j) == 1 else Fr(B[i][j]) if o(i, j) == 0 else Fr(0) for j in range(n)] for i in range(n)]
pend = [[2, None, 0], [None, 2, 0], [0, 0, None]]        # x''=lam*x ; y''=lam*y-g ; x^2+y^2=L^2   (vars x, y, lam)
r = sigma_method(pend); print('A pendulum      :', r, 'DOF=%d' % (r['val']), 'pantelides c=%s' % pantelides(pend))
cap1 = [[1, 0], [None, 0]]                               # C v' = i ; i = I(t)                     (vars v, i)
r = sigma_method(cap1); print('A capacitor+src :', r, 'pantelides c=%s' % pantelides(cap1))
A2 = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]   # C1 v1'=i1; C2 v2'=i2; v1=v2; i1+i2=0 (vars v1 v2 i1 i2)
B2 = [[0, 0, -1, 0], [0, 0, 0, -1], [1, -1, 0, 0], [0, 0, 1, 1]]
r = sigma_method(struct_of(A2, B2))
print('A 2 caps joined :', r, 'pantelides c=%s' % pantelides(struct_of(A2, B2)), 'true diff index=%s' % diff_index(A2, B2))
for k in range(1, 5):                                    # family: structural index k+1, differentiation index 1
    n = 2 * k + 1; A = [[0] * n for _ in range(n)]; B = [[int(i == j) for j in range(n)] for i in range(n)]
    for b in range(k):
        for i in (2 * b, 2 * b + 1): A[i][2 * b + 1] = A[i][2 * b + 2] = 1
    S = struct_of(A, B); r = sigma_method(S) if n <= 7 else None; c = pantelides(S)
    if r: assert r['c'] == c and rank(sysjac(A, B, r)) == n
    print('A family k=%d n=%d: pantelides c=%s structural index=%d  true diff index=%s  rank(A)=%d'
          % (k, n, c, max(c) + 1, diff_index(A, B), rank([[Fr(x) for x in row] for row in A])))
A3 = [[1, 1], [1, 1]]; B3 = [[1, 0], [0, 1]]             # x1'+x2'+x1=f1 ; x1'+x2'+x2=f2
r = sigma_method(struct_of(A3, B3))
print('A cancellation  :', r, 'rank(system Jacobian)=%d of 2' % rank(sysjac(A3, B3, r)), 'true diff index=%s' % diff_index(A3, B3))
A4 = [[1, 1], [0, 0]]; B4 = [[1, 0], [-1, 1]]            # same system after row2 := row2 - row1
r = sigma_method(struct_of(A4, B4))
print('A after rowop   :', r, 'rank(system Jacobian)=%d of 2' % rank(sysjac(A4, B4, r)), 'true diff index=%s' % diff_index(A4, B4))

# --- B. Pendulum: differentiated-constraint ODE drifts; dummy-derivative form does not, but has a pivot ---
g = 9.81
def rk4(f, s, h):
    k1 = f(s); k2 = f([a + h / 2 * b for a, b in zip(s, k1)]); k3 = f([a + h / 2 * b for a, b in zip(s, k2)])
    k4 = f([a + h * b for a, b in zip(s, k3)]); return [a + h / 6 * (p + 2 * q + 2 * r_ + w) for a, p, q, r_, w in zip(s, k1, k2, k3, k4)]
def f_ode(s):                              # index-0 form: lambda from the twice-differentiated constraint
    x, y, vx, vy = s; lam = (g * y - vx * vx - vy * vy) / (x * x + y * y); return [vx, vy, lam * x, lam * y - g]
def f_dd(s):                               # dummy derivatives: y, y' demoted to algebraic unknowns (pivot: y != 0)
    x, vx = s; y = -math.sqrt(1 - x * x); vy = -x * vx / y; return [vx, (g * y - vx * vx - vy * vy) * x]
for h in (1e-2, 1e-3):
    s = [0.6, -0.8, 0.0, 0.0]; d = [0.6, 0.0]
    for _ in range(round(20 / h)): s = rk4(f_ode, s, h); d = rk4(f_dd, d, h)
    print('B h=%g t=20: |x^2+y^2-1| ODE-with-differentiated-constraint=%.3e  dummy-derivative form=%.1e (y recomputed)'
          % (h, abs(s[0] ** 2 + s[1] ** 2 - 1), 0.0))
d = [0.0, 5.0]; t = 0.0                    # enough energy to swing above the horizontal: pivot y -> 0
try:
    while t < 5: d = rk4(f_dd, d, 1e-3); t += 1e-3
    print('B swing-over: no failure')
except (ValueError, ZeroDivisionError) as e: print('B swing-over: dummy pivot fails at t=%.3f x=%.6f (%s)' % (t, d[0], type(e).__name__))

# --- C. Co-simulation of a split oscillator: explicit (Jacobi, zero-order hold) vs iterated with rollback ---
def cosim(H, T, iters):
    x1, v1, x2, v2 = 1.0, 0.0, 0.0, 0.0; kc = 1.0; m = 20
    E = lambda: 0.5 * (v1 * v1 + v2 * v2) + 0.5 * (x1 * x1 + x2 * x2) + 0.5 * kc * (x1 - x2) ** 2
    def unit1(s, u): return rk4(lambda q: [q[1], -q[0] - kc * (q[0] - u)], s, H / m)     # input: x2 ; output: force
    def unit2(s, u): return rk4(lambda q: [q[1], -q[0] + u], s, H / m)                   # input: force ; output: x2
    E0 = E()
    for _ in range(round(T / H)):
        a0, b0 = [x1, v1], [x2, v2]; u1, u2 = x2, kc * (x1 - x2)        # outputs sampled at the communication point
        for it in range(iters + 1):
            a, b = a0[:], b0[:]                                          # restore saved unit states (rollback)
            for _ in range(m): a = unit1(a, u1); b = unit2(b, u2)
            u1, u2 = 0.5 * (b0[0] + b[0]), 0.5 * kc * ((a0[0] - b0[0]) + (a[0] - b[0]))   # midpoint of old/new outputs
        x1, v1, x2, v2 = a[0], a[1], b[0], b[1]
    return E() / E0
for H in (0.2, 0.1, 0.05):
    print('C H=%-4g T=200: E/E0 explicit=%.4f  iterated(3 passes, needs state restore)=%.6f' % (H, cosim(H, 200, 0), cosim(H, 200, 3)))

# --- D. Port-Hamiltonian interconnection: skew coupling keeps dH/dt <= 0; a gain mismatch breaks it ---
def mat(n, m, f): return [[Fr(f(i, j)) for j in range(m)] for i in range(n)]
def mul(X, Y): return [[sum(X[i][k] * Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]
def tr(X): return [list(c) for c in zip(*X)]
J1 = mat(2, 2, lambda i, j: (j - i) * 3); R1 = mat(2, 2, lambda i, j: (i == j) * (i + 1)); G1 = mat(2, 1, lambda i, j: i + 1)
J2 = mat(2, 2, lambda i, j: (i - j) * 2); R2 = mat(2, 2, lambda i, j: 0); G2 = mat(2, 1, lambda i, j: 2 - i)
def composite(gain):                       # u1 = -y2, u2 = gain*y1 with y_i = G_i^T grad H_i, H = |x|^2/2
    C = mul(G1, tr(G2)); Z = [[Fr(0)] * 4 for _ in range(4)]
    for i in range(2):
        for j in range(2):
            Z[i][j] = J1[i][j] - R1[i][j]; Z[2 + i][2 + j] = J2[i][j] - R2[i][j]
            Z[i][2 + j] = -C[i][j]; Z[2 + i][j] = gain * C[j][i]
    return Z
for gain in (1, 3):
    Z = composite(gain); sym = [[(Z[i][j] + Z[j][i]) / 2 for j in range(4)] for i in range(4)]   # dH/dt = x^T sym x
    worst = max((sum(x[i] * sym[i][j] * x[j] for i in range(4) for j in range(4)), x)
                for x in itertools.product(range(-2, 3), repeat=4))
    print('D gain=%d: coupling block skew=%s  max dH/dt over integer grid=%s at x=%s'
          % (gain, all(Z[i][2 + j] == -Z[2 + j][i] for i in range(2) for j in range(2)), worst[0], worst[1]))
```

Output observed:

```text
A pendulum      : {'val': 2, 'c': [0, 0, 2], 'd': [2, 2, 0], 'index': 3} DOF=2 pantelides c=[0, 0, 2]
A capacitor+src : {'val': 1, 'c': [0, 0], 'd': [1, 0], 'index': 1} pantelides c=[0, 0]
A 2 caps joined : {'val': 1, 'c': [0, 0, 1, 0], 'd': [1, 1, 0, 0], 'index': 2} pantelides c=[0, 0, 1, 0] true diff index=2
A family k=1 n=3: pantelides c=[0, 0, 1] structural index=2  true diff index=1  rank(A)=1
A family k=2 n=5: pantelides c=[0, 0, 1, 1, 2] structural index=3  true diff index=1  rank(A)=2
A family k=3 n=7: pantelides c=[0, 0, 1, 1, 2, 2, 3] structural index=4  true diff index=1  rank(A)=3
A family k=4 n=9: pantelides c=[0, 0, 1, 1, 2, 2, 3, 3, 4] structural index=5  true diff index=1  rank(A)=4
A cancellation  : {'val': 2, 'c': [0, 0], 'd': [1, 1], 'index': 0} rank(system Jacobian)=1 of 2 true diff index=1
A after rowop   : {'val': 1, 'c': [0, 1], 'd': [1, 1], 'index': 1} rank(system Jacobian)=2 of 2 true diff index=1
B h=0.01 t=20: |x^2+y^2-1| ODE-with-differentiated-constraint=1.493e-05  dummy-derivative form=0.0e+00 (y recomputed)
B h=0.001 t=20: |x^2+y^2-1| ODE-with-differentiated-constraint=1.494e-09  dummy-derivative form=0.0e+00 (y recomputed)
B swing-over: dummy pivot fails at t=0.394 x=0.999999 (ValueError)
C H=0.2  T=200: E/E0 explicit=4295447990353.1313  iterated(3 passes, needs state restore)=0.999901
C H=0.1  T=200: E/E0 explicit=2235345.1153  iterated(3 passes, needs state restore)=0.999999
C H=0.05 T=200: E/E0 explicit=1328.1044  iterated(3 passes, needs state restore)=1.000000
D gain=1: coupling block skew=True  max dH/dt over integer grid=0 at x=(0, 0, 2, 2)
D gain=3: coupling block skew=False  max dH/dt over integer grid=60 at x=(2, 2, 2, 2)
```

## Revalidation

- **Algorithmic claims** (sections 2-5, 9): rerun the probe. Section A is exact and deterministic; its internal assertion fails if the two structural algorithms disagree or if the family's system Jacobian is singular. Sections B and C are floating-point but deterministic on IEEE-754 doubles.
- **Whether a tool handles the two failure directions**: feed it the 2-equation cancellation system and the `k = 2` family from section 3 and compare the number of differentiations and the reported state count with the table. In ModelingToolkit this is a `mtkcompile` call on five linear equations; the expected healthy outcome for the cancellation system is one state, not two.
- **StateSelection status**: `grep -n "Dynamic" src/partial_state_selection.jl` and read the to-do comment in `dummy_derivative_graph!`; if items 2 or 3 are marked done, the "unsupported" entries above are stale. `grep -n "structurally singular\|maxiters" src/pantelides.jl` confirms the two exits.
- **ModelingToolkit split**: `grep -n "StateSelection" Project.toml NEWS.md` in a newer revision shows whether index reduction still lives outside the base package.
- **Modelica rules**: in a newer specification tag, search `chapters/equations.tex` for "same number of equations in each branch" and "perfect matching rule", and `chapters/connectors.tex` for the two connection-set equation forms.
- **FMI flags**: `grep -n 'default=' schema/fmi3InterfaceType.xsd` (or the 2.0 schema) lists every capability default in one screen; search `docs/` for "Algebraic loops in systems of connected FMUs are not addressed or resolved by the terminals" and for "cannot be handled by an appropriate sequence" to confirm the two key sentences survive.
- **Hydra and Modelyze** are not under active development at the pinned revisions; re-check only if a successor is substituted (look for an index-reduction stage in the simulation pipeline and for regeneration on events).
- **Operadic composition**: confirm that `oapply` for `StructuredMulticospan` in Catlab still ends in a `colimit` call and that AlgebraicDynamics' `induced_dynamics` still sums over `preimage(state_map, i)`.
- **Paper statements** do not change; re-read only when replacing an abstract-level citation by the paper body.
