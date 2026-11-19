# Post-CMOS Compilation Targets: Analog ODE Devices, Analog Quantum Simulators, the OpenQASM 3 Real-Time Boundary and QEC Decoding, Neuromorphic Processes, Genetic Circuits, and Droplet Microfluidics

## Summary

Six families of compilers target substrates that are not clocked digital logic. For each, this report records what the "instruction set" actually is, what the compiler solves, what interface the result has with classical code, and where the usual compiler assumptions (exact values, free fan-out, composable modules, copyable data, timing as an optimization detail) fail.

1. **Analog ODE compilation is the choice of a scaling transform inside a physical envelope.** Jaunt formulates magnitude and time scaling as a geometric program whose solution yields "a physically realizable, recoverable, and observable simulation"; Legno extends it to a "mixture of geometric programming and SMT constraints" that also selects block modes, uses per-instance empirical gain/noise models, and bounds noise-to-signal ratios, and reports the first compiled computations on a physical device of its class (HCDCv2). A model device reproduces the three regimes: unscaled programs saturate, over-attenuated ones are noise-dominated, and only a window of scale factors recovers the trajectory.
2. **Ark is not a noise-aware scaling compiler; it is a language for defining analog compute paradigms.** A paradigm declares node and edge types, production rules that turn edges into terms of differential equations, and validation rules over local graph structure; derived languages add nonidealities by inheriting types (for example attributes with random mismatch) under rules that keep parent programs valid. Operating-range saturation and noise budgets are Jaunt's and Legno's subject.
3. **SimuQ compiles a Hamiltonian, not a circuit.** A device is described as an abstract analog instruction set (signal lines, instructions with local variables, machine-wide global variables, each instruction contributing a Hamiltonian term); compilation is a numerical solve that matches coefficients of every product term, relaxing per-instruction on/off switches to continuous values, rounding, and re-solving by least squares to a tolerance. An unsolved system raises an exception; a solved one is correct only up to that tolerance.
4. **OpenQASM 3's `extern` is a real-time foreign-function interface with no latency contract.** The specification says externs "may be neither fast nor guaranteed to return", are "not required to be idempotent", and that invoking one "will *schedule* a classical computation, but does not wait for that computation to terminate"; how they are "defined and registered" is explicitly not addressed. Timing, by contrast, is first-class: `duration` and `stretch` values are resolved to constants at compile time, and `box` forbids moving operations across its boundary.
5. **A QEC decoder is a hard-real-time co-processor whose throughput is a stability condition.** If syndrome generation outpaces decoding by a factor f > 1, waits before successive logical non-Clifford gates grow geometrically (Terhal). Two published operating points bound current practice and must not be conflated: 63 µs average decoder latency at distance 5 with a 1.1 µs cycle, on a superconducting processor with a software decoder on a workstation; and 446 ns end-to-end decoding-feedback latency at distance 3 on a three-board FPGA prototype measured in loopback *without qubits*. A "sub-500 ns" figure is therefore a prototype measurement, not a requirement stated by OpenQASM 3 or by any specification examined.
6. **In Lava the same process has several implementations with different numerics.** A `LIF` process is bound at run time, by a run configuration and tags, to a floating-point model or to a bit-accurate fixed-point model of Loihi; transcribing both update rules and driving them with the same input gives spike trains that diverge after roughly a hundred steps. The repository is archived at the examined commit.
7. **Cello compiles Verilog to DNA by assigning characterized repressor gates under biochemical constraints**, and its published yield states the limit of the module abstraction: 45 of 60 circuits correct in every output state, 92% of output states as predicted. Retroactivity is one mechanism behind that limit: with the parameters of Del Vecchio et al., binding sites downstream of a component attenuate its output oscillation to 8.8% of the isolated amplitude.
8. **Puddle treats droplets as consumable resources, but static enforcement is weaker in the examined source than the paper states.** API calls consume droplet ids and return new ones; the paper says the Rust frontend prevents reuse "through its ownership-based type system", yet at the examined commit `DropletId` derives `Clone, Copy`, so passing it by value does not move it. The Python wrapper enforces single use dynamically.

## Applicability

**Subjects and their relationship.** The report is a comparison across substrates; subjects are not layered on one another. For each family there is at least one paper read in full or in abstract and, where an open implementation exists, its source at a pinned commit:

| Family | Papers | Source |
|---|---|---|
| Analog ODE devices | Jaunt and Legno (full text, author-hosted) | none examined |
| Analog paradigm languages | Ark (full text, arXiv) | `WangYuNeng/Ark` |
| Analog quantum simulation | SimuQ (abstract only) | `PicksPeng/SimuQ` |
| Real-time quantum control | OpenQASM 3 paper (arXiv v2, full text) | `openqasm/openqasm` (specification text) |
| Real-time QEC decoding | Terhal's review, the surface-code experiment paper, the FPGA prototype preprint (full text) | none examined |
| Neuromorphic | none read in full | `lava-nc/lava` (six files) |
| Genetic circuits | Cello (abstract via PubMed); Del Vecchio, Ninfa, Sontag (full text via PubMed Central) | `CIDARLAB/Cello-v2` |
| Droplet microfluidics | Puddle (full text, author-hosted) | `uwmisl/puddle` |

**Scope of each kind of claim.**

- Paper statements apply to the copy fetched on the observation date; bibliographic identity was confirmed against Crossref. Author-hosted PDFs and arXiv versions may differ from the version of record.
- Source statements apply to the exact commits in `REPORT.json`, which are default-branch heads on the observation date. The OpenQASM repository builds its specification with `version = os.getenv('VERSION','Live')`; the text read is the live, unreleased specification at that commit, not a numbered release.
- No device, simulator or framework listed above was executed. The four execution results are small models written for this report (standard-library Python 3.13.15), with sources reproduced under Evidence. They characterize mechanisms as described in the cited papers and source: a saturating noisy integrator device (not the HCDCv2), a throughput recurrence (not a decoder), a scalar transcription of two Lava process models (not Lava, which could not be run without NumPy), and the published retroactivity model.
- Decoder latency figures are properties of one experiment each (code distance, hardware, what the latency interval includes). They do not generalize across distance or platform.
- Out of scope: quantum algorithms and error-correcting code design, device physics beyond what constrains a compiler, resistive crossbars, photonic and annealing machines, DNA strand-displacement compilers, and reversible computing.

## Findings

### 1. What changes per substrate

| Substrate (system) | What a "signal" is | What the compiler solves | Limits fan-out or composition | Dominant error source | Timescale reported | Correctness notion in use | Basis |
|---|---|---|---|---|---|---|---|
| Programmable analog device (Jaunt, Legno) | continuous voltage or current, bounded range | block configuration and routing, then scale factors and a time constant | every block port has an operating range; a signal drives a fixed set of ports | saturation, noise, quantization at the digital interface, per-instance manufacturing variation | 0.50-5.92 ms and 0.28-5.67 µJ per computation (Legno) | constraint satisfaction plus measured waveform quality | documentation |
| Analog paradigm (Ark) | a node variable governed by an ODE of declared order | ODE system from production rules; validity from local graph patterns | validation rules bound degree per node/edge type pattern | mismatch (modelled as sampled attributes) | n/a (simulation) | validator verdict; simulation | documentation + source |
| Analog quantum simulator (SimuQ) | a Hamiltonian term with tunable coefficient | variable values and instruction switches matching target coefficients | "Instructions sharing a signal line cannot be called simultaneously" | approximation residual; device noise (not modelled in the solve) | n/a | residual norm below tolerance | source |
| Gate-model QPU with real-time control (OpenQASM 3) | qubit operations with durations; classical bits | stretch durations as a linear system | coherence time; non-local timing side effects | decoherence during delays | "within the qubit coherence time" | none for timing of externs | normative + documentation |
| QEC decoder | stream of syndrome bits per cycle | corrections / Pauli frame | decoding rate must not fall below generation rate | decoder latency and accuracy | 1.1 µs cycle; 63 µs or 446 ns latency (two different systems) | logical error rate, measured | documentation |
| Neuromorphic process graph (Lava) | spikes on ports between processes, per algorithmic time step | binding of each process to a process model | hardware resources required by the chosen model | fixed-point truncation and saturation | discrete time steps in phases | none across models | source |
| Genetic circuit (Cello) | steady-state promoter activity in relative units | assignment of library gates to netlist nodes | each repressor usable once; toxicity; roadblocking; load on shared species | context dependence, growth burden, retroactivity | protein half-life about 1 h in the retroactivity model | predicted versus measured output states | documentation + source |
| Droplet microfluidics (Puddle) | a droplet with volume and location | placement and routing on an electrode grid, incrementally | droplets are consumed by use; grid area; failed electrodes | actuation failures, evaporation | operations "might take several seconds" | runtime detection and re-planning | documentation + source |

The recurring pattern: the target description is not an instruction set with exact semantics but a set of parametrized physical behaviours with validity ranges, and compilation contains a numerical or combinatorial *solve* that can fail or succeed only approximately.

### 2. Analog ODE compilation: Jaunt and Legno

**2.1 The scaling transform.** A programmable analog device computes the solution of an ODE by configuring integrators, multipliers and other blocks so that the circuit's own dynamics are those of the target system. The compiler may replace each state variable `x` by `X = a*x` and run the device at a different speed than the modelled system; the mathematical trajectory is recoverable by undoing these factors. Jaunt's abstract states the three requirements: the scaled computation "executes within the operating constraints of the device, preserves the recoverable dynamics of the original simulation, and executes slowly enough to observe these dynamics at the sampled digital outputs", and the paper formulates the problem "as a constraint satisfaction problem (specifically, a geometric program)" whose solution "delivers scaling factors that, when applied to the digital inputs and outputs of the analog device, deliver a physically realizable, recoverable, and observable simulation". It also states the negative result that motivates the work: "unscaled configurations produce incorrect simulations because they violate the operating ranges of the device".

Why a geometric program: substituting `X = a*x`, `Y = b*y` into a polynomial ODE rewrites every coefficient as a *monomial* in the scale factors. For the Van der Pol system `x' = y, y' = mu*(1 - x^2)*y - x` the device program is `dX/dt = (a/b)*Y`, `dY/dt = mu*Y - (mu/a^2)*X*X*Y - (b/a)*X`. Range constraints such as `|a*x| <= 1` and `|(b/a)*X| <= port limit` are then posynomial inequalities, which is the constraint class geometric programming accepts.

Basis: documentation (Jaunt abstract and introduction); the monomial observation is derived.

**2.2 What Legno adds.** Legno is "a compilation toolchain for programmable analog devices" that targets "the HCDCv2, a programmable analog device designed to execute general nonlinear dynamical systems", and claims to be "the first compiler to successfully target a physical (as opposed to simulated) programmable analog device for dynamical systems". Its structure, in the paper's terms:

- inputs: a Dynamical System Specification (DSS), an Analog Device Specification (ADS), and an Empirical Model Database, "a repository of empirically derived models that describe how each individual block instance deviates from the block specification in the ADS". The paper's example entry for one multiplier instance in one mode reads `z:{gain:0.755781,noise:0.01}` for the output port, next to `gain:1.0,noise:0.0` for the instance's other ports.
- `LGraph`, a "graph synthesis engine" with "a staged synthesis pipeline (generation, assembly, and routing)" that produces an analog device program (ADP): block instances at locations, connections, and a time constant (the paper's example: `timescale 40000;`).
- `LScale`, which "completes the configuration of the parametric behavior of the blocks and scales the signals and values in the program" by solving the *unified scaling constraint problem*: "The USCP is comprised of a mixture of geometric programming and SMT constraints over positive integer-valued and positive real-valued variables"; its variables include mode selections, "the time constant and scale factor variables", and property variables that "resolve to constant values when the mode variables are instantiated".
- quality targets: "The Analog Quality Measure (AQM) is a parameter that specifies the minimum allowed signal-to-noise ratio for the analog signals in the ADP. For constant analog signals, the AQM specifies the upper bound for the ratio of the noise to the magnitude of the signal (noise/|signal| <= AQM)"; a Digital Quality Measure (DQM) "specifies the minimum allowed signal-to-noise ratio for the digital signals in the ADP". The emitted program "respects the frequency and current range limitations of the device block, ensures that the noise and quantization errors fall within the provided measures, and compensates for manufacturing variations found in the device".

Reported result: evaluation "on the Sendyne S100Asy RevU development board on twelve benchmarks from physics, controls, and biology"; "The computations execute in 0.50-5.92 ms and consume 0.28-5.67 µJ of energy."

Three consequences for anyone treating such a device as a compilation target:

1. The target is an *individual calibrated chip*: per-instance empirical models are compiler inputs, so the same ADP is not portable between two devices of the same design.
2. The scale factors and time constant are the calling convention between the digital host and the analog computation. The host must apply them to inputs and invert them on outputs; nothing in the signal itself records them.
3. Correctness is quantitative. The compiler's guarantee is that constraints (ranges, AQM/DQM) hold under the models; agreement with the ideal trajectory is then measured.

Basis: documentation (Legno paper).

**2.3 Execution: the three regimes on a model device.** A model device with operating range [-1, 1] on every signal, white noise of fixed standard deviation at each integrator input, and a fixed integrator rate runs the scaled Van der Pol program for several choices of `(a, b)` (source under Evidence, E1).

```text
ideal Van der Pol: max|x| = 2.009 over t in [0,20.0]  (device range is [-1,1])
       a        b  clipped steps   RMS error of recovered x  verdict
   1.000   1.0000          11395                     0.8972  SATURATED
   0.450   0.3300              0                     0.0102  ok
   0.200   0.1500              0                     0.0195  ok
   0.020   0.0150              0                     0.1849  NOISE-DOMINATED
   0.002   0.0015              0                     2.3961  NOISE-DOMINATED
time scaling: 20.0 simulation time units take 0.200 ms of wall-clock at KAPPA=100000/s;
             a digital sampler at 10 kHz would see only 2 samples -> observability constraint
```

Unscaled, the program clips on 11,395 of 20,000 steps and the recovered trajectory is wrong (RMS error 0.90 against an amplitude of 2.0). Scale factors that keep signals near, but inside, the range recover it to about 0.5-1% of amplitude. Reducing the factors by a further order of magnitude leaves no clipping but lets the fixed noise floor dominate after the recovery map divides by `a`. The last two lines show the third constraint: at a device rate of 10^5 per second the whole computation lasts 0.2 ms, so a slow sampler observes almost nothing - Jaunt's "observable" requirement, and the reason time scaling is part of the same optimization.

Basis: execution (model written for this report; not a simulation of the HCDCv2).

### 3. Ark: a language for analog compute paradigms

Ark's own description: "a programming language for describing analog compute paradigms" that "enables progressive incorporation of analog behaviors into computations, and deploys a validator and dynamical system compiler for verifying and simulating computations". Its intermediate representation is "a novel, unified intermediate representation termed a dynamical graph (DG) for both analog computations and analog circuit descriptions". A paradigm definition "declares node and edge types and defines production rules and validation rules over node and edge types":

| Construct | Paper grammar | Meaning | Implementation at the pinned commit |
|---|---|---|---|
| node type | `node-type(p, Reduc)` with `Reduc ::= sum \| mul` | a state variable of differential order `p`; contributions of incident edges are combined by sum or product | `ark/specification/cdg_types.py`: `NodeType` carries `order` and `reduction`, inherited from the base type |
| attribute | `attr v = SigT`, `SigT ::= real[x0,x1] \| real[x0,x1] mm(s0,s1) \| int[i0,i1] \| lambd(v*)` | bounded parameters; `mm` marks mismatch | `attribute_type.py` (`AnalogAttr` with a value range, `DigitalAttr`, `FunctionAttr`); `attribute_def.py`: `AttrDefMismatch`, "the value is sampled from a normal distribution to model the random mismatch in hardware", with relative (`rstd`) or absolute (`std`) deviation |
| production rule | `prod(v0 : v1, v2 : v3 -> v4 : v5) ProdExpr` | for an edge of a given type between nodes of given types, the algebraic term added to a node's equation | `production_rule.py` (`ProdRule`), expressions in `rule_keyword.py` |
| validation rule | `match(VAtom, VAtom, ...)` patterns with degree bounds | which neighbour patterns, and how many, a node of a type may have | `validation_rule.py`: `ValPattern(target, edge_type, node_types, deg_range)`; `validator.py` with `solver.py`, where `SMTSolver.solve_validation_matrix` creates a pysmt integer variable for every admissible (row, column) entry of a boolean match matrix, constrains each row to sum to 1 and each column sum to lie in that column's degree range, and reports validity as satisfiability |

The example in the paper makes the role of validation concrete: the transmission-line language "requires valid TLNs to have alternating I and V nodes to ensure the Telegrapher's equations are faithfully implemented", and a graph with a V-V connection "is reported invalid".

*Nonidealities by inheritance.* A derived language "may define node and edge types that inherit from types in the parent language" under three constraints quoted from the paper: derived types "inherit the parent type's node order and reduction operator, and inherit all attributes and initial value declarations"; redefined attributes "must retain the same datatype (real, integer, lambda) and operate on a smaller value range than the parent attribute"; and "Production and validation rules from the parent class cannot be overridden or removed. Any new production or validation rules must include one new type from the derived class." These are substitutability conditions: a computation written against the ideal paradigm remains a valid computation of the nonideal one.

The paper applies the language to "a transmission-line based analog PUF (TLN), a cellular non-linear network (CNN) analog accelerator, and an oscillator-based computing (OBC) analog accelerator".

*What Ark is not.* It does not compile onto an existing reconfigurable chip, choose scale factors, or enforce operating ranges and signal-to-noise bounds of a physical device; those are the functions of Jaunt and Legno (Finding 2). In the examined source, `AttrDefMismatch.check()` "only check whether the nominal value is in range and does not check the random value".

Basis: documentation (Ark paper) + source.

### 4. SimuQ: compiling Hamiltonians to analog instruction sets

SimuQ's abstract describes "the first framework for quantum Hamiltonian simulation that supports Hamiltonian programming and pulse-level compilation to heterogeneous analog quantum simulators": users "specify the target quantum system with Hamiltonian Modeling Language"; "the Hamiltonian-level programmability of analog quantum simulators is specified through a new abstraction called the abstract analog instruction set (AAIS)"; and "a solver-based compilation" generates "executable pulse schedules for real devices", demonstrated "on superconducting (IBM), neutral-atom (QuEra), and trapped-ion (IonQ) quantum devices".

**The target description (source, `src/simuq/qmachine.py`).** "A quantum machine is essentially a container of signal lines, instructions and (local or global) variables." "A signal line contains multiple instructions. Instructions sharing a signal line cannot be called simultaneously." "Global variables are defined for the QMachine as a globally tunable parameter. They will be fixed for the whole experiment." "Local variables can be tuned for each call of the instruction." Each instruction carries a Hamiltonian expression in those variables (`ins.set_ham(...)`), and a machine may have an always-on system Hamiltonian (`set_sys_ham`).

A complete example is the global-drive Rydberg machine in `src/simuq/aais/rydberg1d_global.py`: atom positions are global variables (`rydberg.add_global_variable(init_value=l * i)`); the system Hamiltonian is the van der Waals interaction `(C_6 / (x[i] - x[j]) ** 6) * noper[i] * noper[j]` with `C_6 = 862690 * 2.0 * np.pi`; one signal line carries a native "Detuning" instruction with one local variable `d` and Hamiltonian `-d * n_i` summed over atoms; another carries a native Rabi-drive instruction with local variables `o` (amplitude) and `p` (phase) and Hamiltonian `o/2 * (cos(p) X_i - sin(p) Y_i)`. Geometry, a physical constant and the set of simultaneously available controls are thus all part of the "instruction set".

**The compilation problem (source, `src/simuq/solver.py`).** The docstring of the core routine states the method: "Each product term of the target Hamiltonian is used to build an equation, as the constant side. The other side contains all the possible contributor of this product in the machine's instructions. Since a instruction is either selected or not, we represent it by a switch variable for each instruction. Then it turns to a mixed equation solving problem ({0, 1} variables and continuous varibales). Currently, this is solved by first treating the switch variables as continuous variables, truncating them and solving the equations again with switch variables set to 0 or 1." The solver is `scipy.optimize.least_squares`; after each round the L1 norm of the residual is compared with a tolerance (`if np.linalg.norm(f_sol[1:], 1) > tol: return False`; defaults `1e-2` in `find_sol`, `1e-1` in `generate_as`). If no assignment is found the entry point logs and raises `Exception("No solution is found.")`. Other stated limits: "Met complex coefficients, not implemented yet."; "Trotter order > 2 is not supported."

Consequences:

1. *Compilation is incomplete and approximate by construction.* Relax-round-re-solve is a heuristic for a mixed-integer nonlinear system; failure to find a solution does not prove none exists, and success means a residual below a user tolerance, not operator equality.
2. *The accuracy budget is not unified.* The solve's residual, the Trotterization error when instructions cannot run simultaneously, and device noise are separate quantities; the examined solver bounds only the first.
3. *Target descriptions are executable code.* An AAIS is a Python function constructing a `QMachine`; there is no declarative, checkable target file comparable to an instruction-set description.

Basis: documentation (abstract) + source. The SimuQ paper body was not read.

### 5. OpenQASM 3: the real-time boundary

**5.1 Two classes of classical computation.** The specification (`source/language/classical.rst`) opens: "We envision two levels of classical control: simple, low-level instructions embedded as part of a quantum circuit and high-level external functions which perform more complex classical computations." Low-level instructions "are likely to have known durations and many such instructions might be executed within the qubit coherence time. The external, or `extern`, functions execute complex blocks of classical code that may be neither fast nor guaranteed to return." The paper frames the same split as "real-time classical computations that must be performed within the coherence times of the qubits, and near-time computations with less stringent timing", and states the language chooses "to focus on the real-time domain".

**5.2 The `extern` contract, clause by clause.**

| Property | Specification text | Consequence |
|---|---|---|
| Declaration | "`extern name(inputs) -> output;` where `inputs` is a comma-separated list of type names and `output` is a single type name" | signature only; no body, no effect or timing annotation |
| Types | "any number of arguments whose types correspond to the classical types of OpenQASM. Inputs are passed by value. They can return zero or one values whose type is any classical type in OpenQASM except real constants." "The type and size of each argument must be known at compile time to define data flow and enable scheduling." | data layout is static; the scheduler knows what flows, not how long it takes |
| Linking | "`extern` functions are defined outside of OpenQASM. The compiler toolchain is expected to link `extern` functions when building an executable." "We do not address issues such as how the `extern` functions are defined and registered." | the ABI is implementation-defined |
| Placement | "`extern` functions run on a global processor concurrently with operations on local processors, if possible. `extern` functions can write to the global controller's memory, which may not be directly accessible by the local controllers." | a hardware topology is assumed: global and local controllers |
| Effects | "The functions are not required to be idempotent. They may change the state of the process providing the function." | calls cannot be freely duplicated, reordered or retried |
| Call semantics | "invoking an `extern` function will *schedule* a classical computation, but does not wait for that computation to terminate." | the call is asynchronous; when the result becomes available is not specified here |
| Termination | "may be neither fast nor guaranteed to return" | no deadline and no liveness guarantee |

An `extern` used for decoding or feedback is therefore a call whose physical meaningfulness (does the answer arrive inside the coherence budget?) depends on a quantity - worst-case latency - that the type does not carry and the specification does not constrain. The same keyword also links hardware resources in the pulse grammar (`extern port drive_port0`, `extern frame xy_frame0`, and waveform or capture functions such as `extern gaussian(complex[float[size]] amp, duration d, duration sigma) -> waveform;`), specified through "an external linkage that will be resolved at compile-time via vendor supplied translation units".

Basis: normative (live specification text at the pinned commit) + documentation (paper abstract).

**5.3 Timing is first-class and resolved statically.** From `source/language/delays.rst`:

- units are SI times or a "Backend-dependent unit, `dt`, equivalent to the duration of one waveform sample on the backend";
- "`stretch` type which is a sub-type of `duration`. Stretchable durations have variable non-negative duration that are permitted to grow as necessary to satisfy constraints. Stretch variables are resolved at compile time into target-appropriate durations that satisfy a user's specified design intent."
- "All operations on durations happen at compile time since ultimately all durations, including stretches, will be resolved to constants." "Negative durations are allowed, however passing a negative duration to a `gate[duration]` or `box[duration]` expression will result in an error."
- `box`: "optimizing operations within a `box` definition is permitted, and optimizations that move operations from one side to the other side of a box are permitted, but moving operations either into or out of the box as part of an optimization is forbidden."

The paper describes the solver: "We treat duration values to be variables in a linear system of inequalities that the compiler must solve", the goal being that any circuit "with mapped qubits and defcals gives rise to a set of stretch problems that, if bounded and feasible, provides explicit timing for all operations within every basic block"; elsewhere it says the stretch problem "is solved through multiobjective linear programming".

Two observations. `box` is a source-level *optimization barrier with stated semantics* - the construct that fault-hardening and dynamical-decoupling code needs and that general-purpose languages lack. And static resolution means durations cannot depend on run-time values, which is exactly the gap an asynchronous `extern` of unknown latency falls into.

Basis: normative (specification text) + documentation (paper §5).

### 6. Real-time QEC decoding: stability condition and two measured operating points

**6.1 The backlog argument.** Terhal's review states the requirement and its proof sketch: decoding "should never lead to a increasing backlog of syndrome data. Let rproc be the rate (in bauds) at which syndrome bits are processed and rgen be the rate at which these syndrome bits are generated. We can argue that if rgen/rproc = f > 1, a small initial backlog in processing syndrome data will [lead] to an exponential slow down during the computation". The argument: at a logical T gate the correct follow-up depends on the Pauli frame, so the backlog `D1` must be decoded first; that takes long enough to generate `D2 = f*D1` new bits, and so on; "the backlog data record that we have acquired at the k = poly(n)th gate is Dk = f^k D1".

Expressed as a recurrence and executed (source under Evidence, E2):

```text
wait (in syndrome rounds) before the k-th T gate may complete; G = 100 rounds between gates
  k          f=0.5          f=0.9          f=1.0         f=1.01          f=1.1          f=2.0
  1            0.0            0.0            0.0            1.0           10.0          100.0
  2            0.0            0.0            0.0            2.0           21.0          300.0
  3            0.0            0.0            0.0            3.0           33.1          700.0
  4            0.0            0.0            0.0            4.1           46.4         1500.0
  5            0.0            0.0            0.0            5.1           61.1         3100.0
  6            0.0            0.0            0.0            6.2           77.2         6300.0
  7            0.0            0.0            0.0            7.2           94.9        12700.0
  8            0.0            0.0            0.0            8.3          114.4        25500.0
  9            0.0            0.0            0.0            9.4          135.8        51100.0
 10            0.0            0.0            0.0           10.5          159.4       102300.0
 11            0.0            0.0            0.0           11.6          185.3       204700.0
 12            0.0            0.0            0.0           12.7          213.8       409500.0

f = 1.1: ratio of successive waits -> 1.205, 1.187, 1.174, 1.163, 1.154 (-> f)

published operating points expressed in the same units (latency / cycle time):
  63 us average decoder latency at 1.1 us cycle time -> 57.3 cycles of constant lag (f <= 1)
  446 ns decode-feedback latency against a 1.1 us cycle -> 0.41 cycles
  446 ns decode-feedback latency against a 1.0 us cycle -> 0.45 cycles
  446 ns decode-feedback latency against a 0.5 us cycle -> 0.89 cycles
```

For f <= 1 the wait is zero in this idealization; for any f > 1, however small, waits grow without bound and the ratio of successive waits tends to f. Throughput at least equal to the syndrome rate is thus a *stability* condition; latency below that threshold adds a constant delay per dependent gate.

Basis: documentation (Terhal 2015, the passage quoted) + derived + execution.

**6.2 Two measurements.**

| | Surface-code memory on a superconducting processor | Integrated control-and-decoding FPGA prototype |
|---|---|---|
| Source | Google Quantum AI and Collaborators, *Nature* 638:920-926 (2025) | Liu, Lee, Xu, Huang, Wu, arXiv:2603.16203v1 (17 March 2026) |
| Figure | "an average decoder latency of 63 µs at distance-5 up to a million cycles, with a cycle time of 1.1 µs" | "an end-to-end QEC decoding-feedback latency of 446 ns for a distance-3 surface code, including syndrome aggregation, network communication, syndrome decoding, and error distribution" |
| Qubits involved | yes: a 101-qubit distance-7 memory and "a distance-5 code integrated with a real-time decoder" | no: "We evaluate the real-time performance of the QEC system without physical qubits by looping the RF gate outputs back into the readout ADCs to emulate qubit measurement signals" |
| Decoder | software: measurements "transmitted to a specialized workstation via low-latency Ethernet", "a specialized version of the Sparse Blossom algorithm", operating "on a constant-sized graph buffer ... which does not grow with the total number of cycles" | hardware decoder integrated on "a three-board prototype based on AMD ZCU216 RFSoCs", built on "RISC-Q, a generator for RISC-V-based quantum control architectures" |
| What the interval covers | decoder latency (average) | "the time elapsed from when the final 0/1 syndrome results become available on the leaf nodes to when the decoded error information is returned from the root node and ready for feedback control"; 10,000 runs; "Each experiment emulates three rounds of syndrome measurements" |
| Scaling statement | "We maintain below-threshold performance when decoding in real time" | extrapolation only: "the architecture can achieve sub-microsecond decoding-feedback latency up to a distance-21 surface code (~881 physical qubits) when scaled to larger hardware configurations" |

In units of the first system's cycle, 63 µs is a constant lag of about 57 cycles (stable, because the buffer does not grow); 446 ns would be under half of a 1.1 µs cycle, but the second paper itself notes "there is no universally defined QEC cycle time" and reports no cycle. The two numbers measure different intervals on different hardware at different distances, one with qubits and one without.

Basis: documentation (the two papers, as quoted); the cycle-unit arithmetic is derived.

**6.3 The interface that is missing.** Putting Findings 5 and 6 together: the decoder is reached from the control program through a mechanism the language specifies only as an asynchronous, possibly non-returning `extern`; the property that makes the composite system work is a throughput bound plus a latency bound; and neither appears in any type or contract examined. Each experiment establishes it by measurement for one configuration.

Basis: derived.

### 7. Lava: one process, several process models

**7.1 Structure (source).** A Lava `Process` declares ports and variables only. `LIF` (`src/lava/proc/lif/process.py`) has `a_in = InPort(...)`, `s_out = OutPort(...)` and variables `u`, `v`, `du`, `dv`, `bias_mant`, `bias_exp`, `vth`; its docstring gives the intended dynamics `u[t] = u[t-1] * (1-du) + a_in`, spike when `v[t] > vth`. Behaviour comes from a `ProcessModel` attached with decorators: `@implements(proc=LIF, protocol=LoihiProtocol)`, `@requires(CPU)`, `@tag(...)`. Communication inside a model is explicit message passing on ports (`self.a_in.recv()`, `self.s_out.send(...)`).

`LoihiProtocol` (`src/lava/magma/core/sync/protocols/loihi_protocol.py`) fixes the phases of a time step: `SPK`, `PRE_MGMT`, `LRN`, `POST_MGMT`, `HOST`; "A ProcessModel implementing this synchronization protocol adheres to the phases of execution of the neuromorphic processor Loihi."

Which model runs is decided by a run configuration (`src/lava/magma/core/run_configs.py`: `Loihi1SimCfg`, `Loihi1HwCfg`, `Loihi2SimCfg`, `Loihi2HwCfg`). The documented precedence: an explicit `exception_proc_model_map` `{Process: ProcessModel}` first; otherwise, among the available models, the one whose tag list contains the requested `select_tag` (the docstring: "By setting select_tag=\"fixed_pt\", it will select ProcessModels that implement a fixed-point implementation of the Lava Processes in the architecture that is to be executed"), or sub-process models if `select_sub_proc_model` is set; with no tag, "the first available ProcessModel is returned that requires the correct computing hardware".

**7.2 Two models of `LIF` with different arithmetic (source, `src/lava/proc/lif/models.py`).**

| | `PyLifModelFloat` (tag `floating_pt`) | `PyLifModelBitAcc` (tags `bit_accurate_loihi`, `fixed_pt`) |
|---|---|---|
| current | `u = u * (1 - du) + a_in` | `u = sign(p) * (abs(p) >> 12) + (a_in << 6)` with `p = u * (4096 - (du + ds_offset))`, `ds_offset = 1`; wrapped into 24 bits |
| voltage | `v = v * (1 - dv) + u + bias_mant` | `v = clip(sign(q) * (abs(q) >> 12) + u + effective_bias, -(2**23) + 1, 2**23 - 1)` with `q = v * (4096 - (dv + dm_offset))`, `dm_offset = 0` |
| spike | `v > vth` | `v > (vth << 6)` |
| parameter domains | floating point | `du`, `dv` unsigned 12-bit; `bias_mant` signed 13-bit with 3-bit exponent `bias_exp`; `vth` unsigned 17-bit; state 24-bit |
| stated omissions | - | the docstring lists as currently missing "(compared to Loihi 1 hardware)": "refractory period after spiking" and "axonal delays" |

The source explains `ds_offset`: "ds_offset and dm_offset are 1-bit registers in Loihi 1, which are added to du and dv variables to compute effective decay constants ... They enable setting decay constant values to exact 4096 = 2**12." Overflow of the current is "handled by wrapping around", while voltage is clipped: two different overflow semantics in one neuron.

**7.3 Execution: the two update rules diverge.** Scalar transcriptions of both rules were driven with the same pseudo-random integer input for 2,000 steps, giving the float model the numerically corresponding parameters (`du/4096`, `dv/4096`, `vth*64`, input `*64`) (source under Evidence, E3).

```text
   du    dv   vth | float spikes fixed spikes  common  first divergence (step)
  410   205   100 |          128          126      13                      152
 4095     0    50 |           37           36       1                      105
    0     0  2000 |          698          654      91                       93
   40    20   600 |          279          272      23                      105
    1     1  5000 |          294          254      44                      146
```

Spike counts differ by 2-14%, the first step at which exactly one of the two models spikes is between 93 and 152, and thereafter only a minority of spikes coincide in time. No parameter choice in the float model reproduces the fixed-point decay exactly, because of `ds_offset` and truncation toward zero. A network validated with the floating-point models is therefore a different dynamical system from the one the fixed-point (hardware-faithful) models execute; the framework selects between them by tag without any stated equivalence.

Basis: source + execution (transcription written for this report; Lava itself was not run).

**7.4 Project status.** The README at the examined commit begins "THIS PROJECT IS ARCHIVED": "Intel will not provide or guarantee development of or support for this project"; "All Lava repositories are archived"; and it announces a "next-generation Loihi architecture and SDK ... built on open-standard AI frameworks". It also states that "Specific sensitive components supporting architectures like Intel Loihi may remain proprietary to Intel", and that the extension for running on Loihi hardware "is available for members of the Intel Neuromorphic Research Community". The mapping from process models to Loihi chips is therefore not in the examined repository.

Basis: source (README).

### 8. Cello and the limits of genetic modules

**8.1 What Cello reports.** From the abstract: "a user writes Verilog code that is automatically transformed into a DNA sequence. Algorithms build a circuit diagram, assign and connect gates, and simulate performance. Reliable circuit design requires the insulation of gates from genetic context, so that they function identically when used in different circuits. We used Cello to design 60 circuits for *Escherichia coli* (880,000 base pairs of DNA), for which each DNA sequence was built as predicted by the software with no additional tuning. Of these, 45 circuits performed correctly in every output state (up to 10 regulators and 55 parts), and across all circuits 92% of the output states functioned as predicted."

Read as a compiler result: every design passed the tool's own simulation, and one in four still failed in at least one input state when built.

Basis: documentation (abstract, via PubMed).

**8.2 The target description (source, Cello v2).** A user constraint file (UCF) is the target description. The sample `Eco1C1G1T1.UCF.json` examined (under `sample-input/DNACompiler/systolic/systolic4b9/`) is a JSON array of records tagged by `collection`:

| Collection | Count | Content |
|---|---|---|
| `header` | 1 | `organism` "Escherichia coli NEB 10-beta", full genotype, growth `media`, version `EcoJS4ib` |
| `measurement_std` | 1 | signal unit `REU` with the normalization equation against a reference plasmid |
| `logic_constraints` | 1 | `{"type": "NOR", "max_instances": 9}` plus an unbounded `OUTPUT_OR` |
| `gates` | 21 | e.g. `{"regulator": "PhlF", "group_name": "PhlF", "gate_name": "P3_PhlF", "gate_type": "NOR", "system": "TetR"}`; 12 distinct `group_name` values (AmeR, AmtR, BM3R1, BetI, HlyIIR, IcaRA, LitR, LmrA, PhlF, PsrA, QacR, SrpR) |
| `response_functions` | 21 | `"equation": "ymin+(ymax-ymin)/(1.0+(x/K)^n)"` with fitted `ymax`, `ymin`, `K`, `n` and input thresholds `off_threshold`, `on_threshold` |
| `gate_toxicity` | 21 | tabulated relative `growth` as a function of gate `input` |
| `gate_cytometry` | 21 | `cytometry_data` records with `input`, `output_bins`, `output_counts`: measured output distributions per input level |
| `gate_parts`, `parts` | 21, 120 | DNA parts and sequences |
| `eugene_rules` | 2 | placement rules such as `"STARTSWITH pTac"` |
| `genetic_locations` | 1 | the plasmid or locus the circuit is inserted into |

(The file also contains a few records in other collections; it is not strict JSON - it has a trailing comma - and was parsed after removing it.) The target description thus names the host strain and growth medium, bounds the number of gates, gives each gate a steady-state transfer function with validity thresholds, and attaches a growth-burden table. Several library gates share a repressor (`group_name`); the assignment code draws new gates only from groups with no gate in use (`GateManager.getRandomGateFromUnassignedGroup`, documented "Get a random gate from an unassigned group"), so a repressor is a use-once resource. The evident reason - two gates driven by the same repressor would not be independent signals - is an inference, not a statement found in the source.

**8.3 Technology mapping (source).** `SimulatedAnnealing.java` in `cello-technologymapping` assigns library gates to netlist nodes by simulated annealing: constants `MAXTEMP = 100.0`, `MINTEMP = 0.001`, `STEPS = 600`, `D_GROWTH_THRESHOLD = 0.75`. Each step proposes a gate swap or a tandem-promoter order swap; a proposal that increases the number of roadblocked nodes is undone; toxicity is evaluated and proposals falling "below minimum growth threshold" are rejected immediately (or accepted immediately if the circuit is already below threshold and the swap helps); otherwise acceptance has probability `Math.exp((after - before) / temperature)` on the circuit score. After annealing, a circuit that still has roadblocked nodes aborts with `CelloException("Circuit has roadblocked nodes.")`.

Basis: source.

**8.4 Retroactivity: why a characterized gate changes when connected.** Del Vecchio, Ninfa and Sontag define retroactivity as the property "that plays a role analogous to non-zero output impedance in electrical systems" and state when it matters: "retroactivity is large when the amount of transcription factor is comparable to, or smaller than, the amount of promoter-binding sites, or when the affinity of such binding sites is high." Their model: an isolated component `dX/dt = k(t) - delta*X`; connected to downstream promoter sites `p` with complex `C`, total `pTOT`, the upstream equation gains the term `s = koff*C - kon*(pTOT - C)*X`, "the retroactivity to the output".

Because binding is fast, `C` tracks `pTOT*X/(X + kd)` with `kd = koff/kon`; substituting into the conserved total `d(X + C)/dt = k - delta*X` gives the reduced dynamics

```text
dX/dt = (k(t) - delta*X) * (1 - R(X)),     R(X) = 1 / (1 + (1 + X/kd)^2 / (pTOT/kd)).
```

`R` lies in [0, 1): the load does not change the steady state for constant input but slows every transient by the factor `1 - R`. The full and reduced models were integrated with the paper's Figure 3 parameters (`k(t) = 0.01(1 + sin(wt))`, `w = 0.005`, `kon = koff = 10`, `delta = 0.01`, `X(0) = 5`) for several loads (source under Evidence, E4):

```text
isolated          : amplitude 0.8944  mean 1.0000  (free X)
  pTOT  amplitude   ratio  peak lag (time units)  R(mean X)  max |full-reduced|
     0     0.8944   1.000                    0.0      0.000            5.00e-05
     1     0.8358   0.934                   13.8      0.196            1.18e-04
    10     0.4903   0.548                  109.7      0.706            1.43e-04
   100     0.0786   0.088                  213.9      0.963            3.09e-05
```

At the paper's `pTOT = 100` the oscillation amplitude of free `X` is 8.8% of the isolated value and its peak lags by about 214 time units (the input period is about 1,257); even `pTOT = 10` reduces it to 55%. The reduced model agrees with the full one to about 1e-4. The remedy the paper proposes is an insulation device with "a large input gain and a similarly large negative feedback", realized by "a phosphorylation-dephosphorylation cycle" whose fast timescale provides the insulation.

Connection to 8.2: none of the collection names in the examined UCF describes the load a gate's input places on its driver or its demand on shared cellular resources; the transfer functions are steady-state. Whether Cello's gate characterization or scoring accounts for loading in some other way was not examined.

Basis: documentation (paper text and Figure 3 caption) + derived (reduction) + execution.

### 9. Puddle: droplets as consumable resources

**9.1 The API and its resource discipline (paper).** Puddle exposes a "syscall-like API": `mix(d1, d2) -> d`, `split(d) -> (d1, d2)`, `heat(d, temp, time) -> d'`, input/output, and sensing calls. Manipulation calls "are functional, consuming their droplet id arguments and returning new ones", because "Droplets are physical resources that can only be consumed once." All calls except sensing are non-blocking; sensing calls "force the system to 'flush the queue'". On enforcement the paper says: "It is the programmer's responsibility to not reuse droplets ids that have been consumed. An imperative interface (like heat in Figure 5) can help prevent this problem by changing the droplet id that the wrapper object refers to. The Rust frontend statically prevents droplet reuse through its ownership-based type system."

**9.2 What the examined source does.**

- *Core API (Rust).* `puddle-core/src/grid/droplet.rs` declares `#[derive(PartialEq, Eq, PartialOrd, Hash, Ord, Clone, Copy)] pub struct DropletId { pub id: usize, pub process_id: ProcessId }`, and `puddle-core/src/process/process.rs` declares `pub fn mix(&self, d1: DropletId, d2: DropletId) -> PuddleResult<DropletId>`, `pub fn split(&self, d: DropletId) -> PuddleResult<(DropletId, DropletId)>`, `pub fn heat(&self, d: DropletId, temperature: f32, seconds: f64) -> PuddleResult<DropletId>`. Because `DropletId` is `Copy`, passing it by value leaves the caller's binding usable; Rust's ownership rules therefore do not reject a second use of the same id through this API at this commit. Misuse can only surface at run time (the error type includes `NonExistentDropletId(usize)`).
- *Python wrapper.* `puddle-python/puddle/puddle.py` gives each `Droplet` object a `valid` flag; `_use()` raises `DropletConsumed('{} already used!')` if the flag is clear and clears it otherwise; operations such as `move` call `_use()` and then `_renew(result_id)`. This is a dynamic single-use check on wrapper objects, stronger than "the programmer's responsibility" but weaker than a static guarantee, and it guards wrapper objects rather than ids (the constructor refuses direct calls unless passed `i_know_what_im_doing=True`).

The paper's static-prevention sentence and the examined core API disagree; the disagreement is recorded, not resolved (the paper may describe a different frontend or revision). The inference about the Rust API rests on the language rule for `Copy` types; the crate was not compiled here.

**9.3 Planning, errors and what the user can recover from (paper).** A command passes through the stages API Call, Plan, Simulate & Record and Execute, with Rollback and Replan on a detected error (the paper's figure "The life of a command"); "Commands may be rejected if the API call was malformed or a feasible execution plan cannot be found. The user can recover from rejected commands, but not from failures to replan accepted ones." Errors are detected with a computer-vision system; "In rare cases, however, an error can result in a situation that is unrecoverable (e.g. the number of failed electrodes prevents routing). Because actuation API calls are non-blocking, the program may have progressed with the assumption that the promised droplets will be actually produced. Therefore, Puddle treats this case as unrecoverable and throws an exception to the user." The source tree mirrors the pipeline (`puddle-core/src/plan/{place,route,sched}.rs`, `exec.rs`). The physical world also shows through the API: the paper's example program compares a droplet's volume before and after heating and prints "we lost some volume!".

The design choice is explicit in the paper: prior work trades "programming expressiveness for the ability to statically plan microfluidic execution", whereas Puddle will "maximize expressiveness and ease-of-use while trading off some efficiency and ahead-of-time guarantees". A promise-like non-blocking API over a failure-prone device means a failure may be reported after the program has already acted on the promised result.

Basis: documentation (paper) + source; the `Copy` consequence is derived.

### 10. Interface invariants that recur

Derived from the findings above; each is a statement about the boundary between a conventional digital host and the substrate.

1. **The recovery map is part of the compiled artifact.** Analog scale factors and time constants (Finding 2), the classical decoding of a sampled quantum result, and the relative units of a genetic signal are all needed to interpret outputs and are not carried by the signal.
2. **A target description is a set of parametrized behaviours with validity ranges, often per device instance and per environment.** Legno's empirical model database, SimuQ's `QMachine` constructors, Cello's UCF with strain and medium, and Lava's tagged process models all play the role of an instruction-set description, and none is exact.
3. **Compilation includes a solve that can fail or be approximate**: a geometric/SMT program, a least-squares fit, a linear program for stretches, simulated annealing, placement and routing. Callers must handle "no solution" and "solution within tolerance" as normal outcomes.
4. **Timing is semantics.** Coherence windows, decoder throughput, observability of a fast analog run, protein half-lives and droplet evaporation each make a correct sequence of operations wrong if executed at the wrong rate. Only OpenQASM 3 among the examined systems gives durations a type; none gives a latency type to foreign code.
5. **Connection changes behaviour.** Analog ports have ranges and loads, simultaneous analog-quantum instructions share signal lines, genetic gates load their drivers, droplets occupy shared grid area. Compositional reasoning needs interfaces that carry load and demand, not only input/output behaviour.
6. **Some values are linear by physics.** Droplets and uniquely named repressors cannot be duplicated; the examined systems enforce this by a library-wide instance bound (Cello) or a run-time flag (Puddle's Python wrapper), not by a static type in the examined code.

Basis: derived.

## Boundaries

**Not examined.**

- The SimuQ paper body; the Cello paper body and supplementary material (only the abstract); the original Cello repository `CIDARLAB/cello`; the *Nature Protocols* description of Cello 2.0; Arco (the configuration-synthesis predecessor of Jaunt).
- Any execution of Ark, SimuQ, Lava, Cello or Puddle, or of an OpenQASM 3 toolchain; any hardware.
- Lava beyond six files (README, the LIF process and models, run configurations, the Python process-model base, the Loihi protocol); in particular its compiler and runtime packages and the proprietary Loihi extension. Statements about Loihi 2 hardware features (for example graded spikes with integer payloads) were seen only in a search-result excerpt of a vendor brief and are not relied on.
- Decoder implementations (for example matching or union-find decoders) and their source; decoder accuracy; parallel-window decoding; trapped-ion or neutral-atom real-time QEC demonstrations.
- Other post-CMOS substrates: resistive crossbars and analog in-memory computing, photonics, annealers, probabilistic-bit machines, chemical reaction networks and DNA strand displacement, continuous-flow microfluidics and biochemical safety type systems.
- Resource competition (shared ribosomes and polymerases) and evolutionary stability of genetic circuits.

**Unknown.**

- Whether any OpenQASM 3 implementation attaches timing or latency information to `extern` declarations; the specification text examined does not, and implementations were not surveyed.
- Whether the Puddle paper's Rust frontend with static reuse prevention existed at some other revision or in another crate; at the examined commit the core API does not provide it.
- How Legno's guarantees degrade as a device drifts after calibration; the paper's empirical models are measured per instance, and recalibration policy was not found in the passages read.
- Whether Cello's scoring or gate characterization captures retroactivity or resource load indirectly.
- The decoding-feedback latency of the FPGA prototype when connected to real qubits and at distances above 3; the preprint gives an extrapolation only.

**Known not to apply.**

- A "sub-500 ns" decoder deadline is not part of OpenQASM 3. The specification contains no numeric latency requirement for externs; the 446 ns figure is a measurement on one FPGA prototype in loopback.
- OpenQASM 3 was published in *ACM Transactions on Quantum Computing* 3(3), 2022 (Crossref record for doi:10.1145/3505636), not at a programming-languages conference.
- Ark does not perform device-level scaling for saturation or noise; that description fits Jaunt and Legno.
- The 63 µs and 446 ns latencies are not comparable as "the same quantity improved": they differ in code distance, decoder platform, measured interval and the presence of qubits.
- The Lava float and fixed-point LIF models are not interchangeable implementations of one semantics (Finding 7.3).

**Unsupported (by the subject's own statement).**

- OpenQASM 3: "We do not address issues such as how the `extern` functions are defined and registered."
- SimuQ at the examined commit: complex coefficients ("not implemented yet") and Trotter order above 2.
- Lava bit-accurate LIF model: "refractory period after spiking" and "axonal delays" are listed as missing relative to Loihi 1 hardware; the project is archived.
- Puddle: recovery from a failure to re-plan an already accepted command ("unrecoverable").
- Cello: circuits whose assignment leaves roadblocked nodes (compilation aborts).

**Attractive conclusions the evidence does not establish.**

- "Linear types solve droplet reuse in Puddle." The paper asserts static prevention for a Rust frontend; the examined API takes a `Copy` id.
- "A design that passes the genetic-circuit compiler works." The tool's own published yield is 45 of 60 fully correct.
- "Real-time decoding is solved at sub-microsecond latency." One figure is at distance 3 without qubits; the other, with qubits, is 63 µs.
- "Analog compilation is verified." The compilers examined enforce range and noise constraints under empirical models and report measured accuracy; no refinement theorem between the ideal ODE and device behaviour was found.
- The model-device and transcription results are illustrations of mechanisms, not measurements of the HCDCv2 or of Lava.

## Evidence

All evidence was acquired on 2026-11-19.

### Git sources

Commits are default-branch heads resolved on the observation date with `git ls-remote https://github.com/<owner>/<repo>.git HEAD`; files were read from archives or raw files at exactly these commits.

| Repository | Commit | Paths and symbols relied on |
|---|---|---|
| `WangYuNeng/Ark` | `b7c92449685b4e4be2abc4f50157dd766304ccf2` | `README.md`; `ark/specification/cdg_types.py` (`CDGType`, `NodeType`, `EdgeType`); `attribute_type.py` (`AnalogAttr`, `DigitalAttr`, `FunctionAttr`); `attribute_def.py` (`AttrDef`, `AttrDefMismatch`); `production_rule.py` (`ProdRule`); `validation_rule.py` (`ValPattern`); `ark/validator.py` (`ArkValidator`); `ark/solver.py` (`SMTSolver.solve_validation_matrix`) |
| `PicksPeng/SimuQ` | `eb82d67e7d4acbc5c000a6292d1a697f7f5337f9` | `README.md`; `src/simuq/qmachine.py` (module docstring, `QMachine`, `SignalLine`, `Instruction`); `src/simuq/aais/rydberg1d_global.py` (`generate_qmachine`); `src/simuq/solver.py` (`solve_aligned` docstring and tolerance checks, `find_sol`, `generate_as`) |
| `openqasm/openqasm` | `f059a268b2372a53d99212538cfd3b9f4c373147` | `source/language/classical.rst` (introduction; section "Extern function calls"); `source/language/delays.rst` (sections "Duration and stretch types", "Operations on durations", "Boxed expressions"); `source/language/openpulse.rst` (extern ports, frames, waveform and capture functions); `source/conf.py` (`version = os.getenv('VERSION','Live')`) |
| `lava-nc/lava` | `646fa535764c3b0bd1bf24b956aaf64561bf97f6` | `README.md`; `src/lava/proc/lif/process.py` (`LIF`); `src/lava/proc/lif/models.py` (`AbstractPyLifModelFloat`, `AbstractPyLifModelFixed`, `PyLifModelFloat`, `PyLifModelBitAcc`); `src/lava/magma/core/run_configs.py` (`AbstractLoihiRunCfg` docstring; `Loihi1SimCfg`, `Loihi1HwCfg`, `Loihi2SimCfg`, `Loihi2HwCfg`); `src/lava/magma/core/sync/protocols/loihi_protocol.py` (`Phase`, `LoihiProtocol`) |
| `CIDARLAB/Cello-v2` | `1b93575b8aa7e40e132381e3a9b29b1aa7f7a8e4` | `README.md`; `sample-input/DNACompiler/systolic/systolic4b9/Eco1C1G1T1.UCF.json`; `cello/cello-technologymapping/src/main/java/org/cellocad/v2/technologyMapping/algorithm/SimulatedAnnealing/SimulatedAnnealing.java` (constants, swap/accept logic, roadblock and toxicity handling) |
| `uwmisl/puddle` | `a298abc15d8dd2215477ad171f830c04f3314e1f` | `puddle-core/src/grid/droplet.rs` (`DropletId` derive list); `puddle-core/src/process/process.rs` (`PuddleError`, `mix`, `split`, `heat`, `combine_into`); `puddle-core/src/plan/` (file names); `puddle-python/puddle/puddle.py` (`Droplet._use`, `_renew`, `DropletConsumed`) |

Head commits were also resolved for `CIDARLAB/cello` (`11644045e5ab677965a8e5765db2fb8535484a53`), `quantumlib/Stim` (`ffe0d043598ed5df0851a3e6b4920359a23fafbd`) and `oscarhiggott/PyMatching` (`6f63b2b9474ba0fa7e511fe52bffdce858a06984`), but their contents were not examined and no claim rests on them.

### Papers

| Work | Identity | What was read |
|---|---|---|
| Achour, Rinard. *Time Dilation and Contraction for Programmable Analog Devices with Jaunt.* ASPLOS 2018, pp. 229-242 | doi:10.1145/3173162.3173179 | full text, `https://people.csail.mit.edu/rinard/paper/asplos18.pdf` |
| Achour, Rinard. *Noise-Aware Dynamical System Compilation for Analog Devices with Legno.* ASPLOS 2020, pp. 149-166 | doi:10.1145/3373376.3378449 | full text, `https://people.csail.mit.edu/sachour/docs/asplos20-legno.pdf` |
| Wang, Cowan, Rührmair, Achour. *Design of Novel Analog Compute Paradigms with Ark.* ASPLOS 2024 (Volume 2), pp. 269-286 | doi:10.1145/3620665.3640419; arXiv:2309.08774 | full text (arXiv PDF) |
| Peng, Young, Liu, Wu. *SimuQ: A Framework for Programming Quantum Hamiltonian Simulation with Analog Compilation.* PACMPL 8(POPL), 2024, pp. 2425-2455 | doi:10.1145/3632923; arXiv:2303.02775 | abstract only |
| Cross, Javadi-Abhari, Alexander, De Beaudrap, Bishop, Heidel, Ryan, Sivarajah, Smolin, Gambetta, Johnson. *OpenQASM 3: A Broader and Deeper Quantum Assembly Language.* ACM Trans. Quantum Computing 3(3), 2022, pp. 1-50 | doi:10.1145/3505636; arXiv:2104.14722v2 | full text (arXiv PDF) |
| Terhal. *Quantum error correction for quantum memories.* Rev. Mod. Phys. 87(2), 2015, pp. 307-346 | doi:10.1103/RevModPhys.87.307; arXiv:1302.3428 | the backlog passage, in the arXiv full text |
| Google Quantum AI and Collaborators. *Quantum error correction below the surface code threshold.* Nature 638(8052), 2025, pp. 920-926 | doi:10.1038/s41586-024-08449-y; arXiv:2408.13687 | arXiv HTML: abstract, real-time decoding description |
| Liu, Lee, Xu, Huang, Wu. *A Scalable Open-Source QEC System with Sub-Microsecond Decoding-Feedback Latency.* Preprint, submitted 17 March 2026 | arXiv:2603.16203v1 | arXiv HTML: abstract, evaluation section |
| Nielsen, Der, Shin, Vaidyanathan, Paralanov, Strychalski, Ross, Densmore, Voigt. *Genetic circuit design automation.* Science 352(6281), 2016 | doi:10.1126/science.aac7341; PMID 27034378 | abstract (PubMed) |
| Del Vecchio, Ninfa, Sontag. *Modular cell biology: retroactivity and insulation.* Molecular Systems Biology 4(1), 2008 | doi:10.1038/msb4100204; PMCID PMC2267736 | full text (PubMed Central; display equations are images there, so the model was taken from the surrounding text and the Figure 3 caption) |
| Willsey, Stephenson, Takahashi, Vaid, Nguyen, Piszczek, Betts, Newman, Joshi, Strauss, Ceze. *Puddle: A Dynamic, Error-Correcting, Full-Stack Microfluidics Platform.* ASPLOS 2019, pp. 183-197 | doi:10.1145/3297858.3304027 | full text, `https://www.mwillsey.com/assets/2019-asplos-puddle.pdf` |

Bibliographic fields were checked against the Crossref REST API (`https://api.crossref.org/works/<doi>`) or the arXiv listing page.

### Execution environment

Python 3.13.15, standard library only; all probes are deterministic (fixed seeds).

### E1. Model analog device with saturation, noise and a fixed rate (Finding 2.3)

Run `python3 analog_scaling.py`. Output is the block in Finding 2.3.

```python
#!/usr/bin/env python3
"""analog_scaling.py -- why an analog ODE compiler must choose magnitude and
time scale factors.  A model analog device integrates continuously but
  (1) every signal saturates outside the operating range [-1, +1],
  (2) every integrator input carries additive noise of fixed standard deviation,
  (3) integrators run at a fixed device rate (KAPPA wall-clock rate units).
Target dynamics: Van der Pol  x' = y,  y' = mu*(1 - x^2)*y - x,  x(0)=2, y(0)=0,
whose limit cycle has |x| <= ~2.0 and |y| <= ~2.7 (outside the device range).

Scaling transform (the compiler's "calling convention"): X = a*x, Y = b*y and
t_wall = t / KAPPA.  Substituting gives the device program
      dX/dt = (a/b) * Y
      dY/dt = mu*Y - (mu/a^2) * X*X*Y - (b/a) * X
Every rewritten coefficient is a MONOMIAL in the scale factors (a/b, 1/a^2,
b/a), which is why range constraints of the form  |coeff * signal| <= 1  form a
geometric program.  Recovery: x = X/a, y = Y/b, t = KAPPA * t_wall."""
import math, random

MU, T_END, DT = 1.0, 20.0, 1e-3
KAPPA = 1.0e5            # device integrator rate (model value, not a real chip constant)
NOISE = 2.0e-3           # per-integrator-input noise std, in device units

def sat(v): return max(-1.0, min(1.0, v))

def ideal():
    x, y, out = 2.0, 0.0, []
    def f(x, y): return y, MU * (1 - x * x) * y - x
    for i in range(int(T_END / DT)):
        k1 = f(x, y); k2 = f(x + DT / 2 * k1[0], y + DT / 2 * k1[1])
        k3 = f(x + DT / 2 * k2[0], y + DT / 2 * k2[1]); k4 = f(x + DT * k3[0], y + DT * k3[1])
        x += DT / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0])
        y += DT / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])
        out.append(x)
    return out

def device(a, b, seed=1):
    """Simulate the scaled program on the saturating, noisy device; return recovered x(t)."""
    rng = random.Random(seed)
    X, Y, out, clipped = sat(a * 2.0), sat(b * 0.0), [], 0
    for i in range(int(T_END / DT)):
        prod = sat(X * X)                    # multiplier block (output saturates)
        prod2 = sat(prod * Y)                # second multiplier block
        dX = (a / b) * Y
        dY = MU * Y - (MU / (a * a)) * prod2 - (b / a) * X
        # noise enters at integrator inputs; sqrt(DT) scaling = white noise in continuous time
        X2 = X + DT * dX + NOISE * math.sqrt(DT) * rng.gauss(0, 1)
        Y2 = Y + DT * dY + NOISE * math.sqrt(DT) * rng.gauss(0, 1)
        if abs(X2) > 1 or abs(Y2) > 1 or abs(X * X) > 1: clipped += 1
        X, Y = sat(X2), sat(Y2)
        out.append(X / a)                    # recovery map
    return out, clipped

def rms(u, v): return math.sqrt(sum((p - q) ** 2 for p, q in zip(u, v)) / len(u))

if __name__ == "__main__":
    ref = ideal()
    amp = max(abs(v) for v in ref)
    print(f"ideal Van der Pol: max|x| = {amp:.3f} over t in [0,{T_END}]  (device range is [-1,1])")
    print(f"{'a':>8s} {'b':>8s} {'clipped steps':>14s} {'RMS error of recovered x':>26s}  verdict")
    for a, b in [(1.0, 1.0), (0.45, 0.33), (0.2, 0.15), (0.02, 0.015), (0.002, 0.0015)]:
        rec, clipped = device(a, b)
        e = rms(rec, ref)
        verdict = "SATURATED" if clipped else ("ok" if e < 0.05 * amp else "NOISE-DOMINATED")
        print(f"{a:8.3f} {b:8.4f} {clipped:14d} {e:26.4f}  {verdict}")
    print(f"time scaling: {T_END} simulation time units take {T_END / KAPPA * 1e3:.3f} ms of wall-clock at KAPPA={KAPPA:g}/s;")
    print("             a digital sampler at 10 kHz would see only", int(T_END / KAPPA * 1e4), "samples -> observability constraint")
```

### E2. Decoder backlog recurrence (Finding 6.1)

Run `python3 qec_backlog.py`. Output is the block in Finding 6.1.

```python
#!/usr/bin/env python3
"""qec_backlog.py -- the decoder-throughput stability condition as arithmetic.

Model (Terhal, Rev. Mod. Phys. 87:307, 2015, backlog argument): syndrome data
is generated at rate r_gen (one round per time unit here) and decoded at rate
r_proc; f = r_gen / r_proc.  A logical non-Clifford (T) gate cannot complete
until every syndrome round generated before it has been decoded, and the
quantum computer keeps generating rounds while it waits.  A T gate is requested
G rounds after the previous one completes.

  t_k = time the k-th T gate is requested,  c_k = time it completes.
  decoded(t) = t / f while the decoder is saturated (f >= 1), else it keeps up.
  c_k = max(t_k, f * t_k),   t_{k+1} = c_k + G.
"""

def schedule(f, G=100.0, n=12):
    t, rows = G, []
    for k in range(1, n + 1):
        c = max(t, f * t)
        rows.append((k, t, c, c - t))
        t = c + G
    return rows

if __name__ == "__main__":
    print("wait (in syndrome rounds) before the k-th T gate may complete; G = 100 rounds between gates")
    print(f"{'k':>3s} " + " ".join(f"{'f=' + str(f):>14s}" for f in (0.5, 0.9, 1.0, 1.01, 1.1, 2.0)))
    table = {f: schedule(f) for f in (0.5, 0.9, 1.0, 1.01, 1.1, 2.0)}
    for i in range(12):
        print(f"{i + 1:3d} " + " ".join(f"{table[f][i][3]:14.1f}" for f in (0.5, 0.9, 1.0, 1.01, 1.1, 2.0)))
    print()
    f = 1.1
    w = [r[3] for r in table[f]]
    print("f = 1.1: ratio of successive waits ->", ", ".join(f"{w[i + 1] / w[i]:.3f}" for i in range(6, 11)), "(-> f)")
    print()
    print("published operating points expressed in the same units (latency / cycle time):")
    print(f"  63 us average decoder latency at 1.1 us cycle time -> {63 / 1.1:.1f} cycles of constant lag (f <= 1)")
    for cyc in (1.1, 1.0, 0.5):
        print(f"  446 ns decode-feedback latency against a {cyc} us cycle -> {0.446 / cyc:.2f} cycles")
```

### E3. Scalar transcription of two Lava LIF process models (Finding 7.3)

Run `python3 lif_float_vs_fixed.py`. Output is the block in Finding 7.3.

```python
#!/usr/bin/env python3
"""lif_float_vs_fixed.py -- scalar transcription of the two CPU ProcessModels that
implement the same `LIF` Process in Lava (file src/lava/proc/lif/models.py):

  PyLifModelFloat  (tag "floating_pt"):
      u <- u*(1-du) + a_in ;  v <- v*(1-dv) + u + bias ;  spike iff v > vth ;  v <- 0 on spike
  PyLifModelBitAcc (tags "bit_accurate_loihi", "fixed_pt"), 24-bit state, 12-bit decays:
      u <- sign(p)*(|p| >> 12) + (a_in << 6),  p = u*(4096 - (du + ds_offset)),  ds_offset = 1,
           wrapped into 24 bits
      v <- clip(sign(q)*(|q| >> 12) + u + bias, -(2^23)+1, 2^23-1),  q = v*(4096 - (dv + dm_offset)),
           dm_offset = 0
      spike iff v > (vth << 6) ;  v <- 0 on spike

Both are driven with the same integer input train.  The float model is given
the numerically corresponding parameters (du/4096, dv/4096, vth*64, a_in*64),
i.e. the mapping a user would naturally write, so every difference in the
spike trains is due to the fixed-point semantics (ds_offset, truncation)."""
import random

def sgn(x): return (x > 0) - (x < 0)

def run_float(inputs, du, dv, vth, bias=0.0):
    u = v = 0.0
    spikes = []
    for t, a in enumerate(inputs):
        u = u * (1 - du) + a
        v = v * (1 - dv) + u + bias
        if v > vth:
            spikes.append(t); v = 0.0
    return spikes

def run_fixed(inputs, du, dv, vth, bias_mant=0, bias_exp=0):
    MAXV = 2 ** 23
    u = v = 0
    eff_vth = vth << 6
    eff_bias = bias_mant << bias_exp
    spikes = []
    for t, a in enumerate(inputs):
        p = u * (4096 - (du + 1))                      # ds_offset = 1
        u = sgn(p) * (abs(p) >> 12) + (a << 6)
        if u > MAXV: u -= 2 * MAXV
        elif u <= -MAXV: u += 2 * MAXV
        q = v * (4096 - (dv + 0))                      # dm_offset = 0
        v = sgn(q) * (abs(q) >> 12) + u + eff_bias
        v = max(-MAXV + 1, min(MAXV - 1, v))
        if v > eff_vth:
            spikes.append(t); v = 0
    return spikes

if __name__ == "__main__":
    rng = random.Random(7)
    T = 2000
    inputs = [rng.choice([0, 0, 0, 1, 2, 3]) for _ in range(T)]
    print(f"{'du':>5s} {'dv':>5s} {'vth':>5s} | {'float spikes':>12s} {'fixed spikes':>12s} {'common':>7s} {'first divergence (step)':>24s}")
    for du, dv, vth in [(410, 205, 100), (4095, 0, 50), (0, 0, 2000), (40, 20, 600), (1, 1, 5000)]:
        sf = run_float([a * 64 for a in inputs], du / 4096, dv / 4096, vth * 64)
        sx = run_fixed(inputs, du, dv, vth)
        common = len(set(sf) & set(sx))
        first = next((t for t in range(T) if (t in set(sf)) != (t in set(sx))), None)
        print(f"{du:5d} {dv:5d} {vth:5d} | {len(sf):12d} {len(sx):12d} {common:7d} {str(first):>24s}")
```

### E4. Retroactivity model, full and reduced (Finding 8.4)

Run `python3 retroactivity.py` (about fifteen seconds). Output is the block in Finding 8.4.

```python
#!/usr/bin/env python3
"""retroactivity.py -- loading of a transcriptional component by downstream
binding sites (model and parameters of Del Vecchio, Ninfa, Sontag 2008, Fig. 3).

Isolated upstream component (their eq. 2):   dX/dt = k(t) - delta*X
Connected to promoter sites p (their eq. 3): dX/dt = k(t) - delta*X + koff*C - kon*(pTOT - C)*X
                                             dC/dt =               - koff*C + kon*(pTOT - C)*X
with k(t) = 0.01*(1 + sin(w*t)), w = 0.005, kon = koff = 10, delta = 0.01, pTOT = 100, X(0) = 5.

Reduced model checked here (derivation: binding is fast, so C ~ pTOT*X/(X+kd), kd = koff/kon;
the total X + C obeys d(X+C)/dt = k - delta*X; differentiating C gives)
        dX/dt = (k(t) - delta*X) * (1 - R(X)),   R(X) = 1 / (1 + (1 + X/kd)^2 / (pTOT/kd)).
The stiff full system is integrated with backward Euler + Newton."""
import math

W, KON, KOFF, DELTA, X0 = 0.005, 10.0, 10.0, 0.01, 5.0
KD = KOFF / KON

def k(t): return 0.01 * (1.0 + math.sin(W * t))

def isolated(T, dt):
    x, out = X0, []
    for i in range(int(T / dt)):
        t = (i + 1) * dt
        x = (x + dt * k(t)) / (1 + dt * DELTA)          # backward Euler (linear, exact solve)
        out.append(x)
    return out

def connected(T, dt, ptot):
    x, c, out = X0, 0.0, []
    for i in range(int(T / dt)):
        t = (i + 1) * dt
        xn, cn = x, c
        for _ in range(50):                               # Newton on the 2x2 implicit system
            s = KOFF * cn - KON * (ptot - cn) * xn
            f1 = xn - x - dt * (k(t) - DELTA * xn + s)
            f2 = cn - c - dt * (-s)
            ds_dx, ds_dc = -KON * (ptot - cn), KOFF + KON * xn
            a11, a12 = 1 + dt * DELTA - dt * ds_dx, -dt * ds_dc
            a21, a22 = dt * ds_dx, 1 + dt * ds_dc
            det = a11 * a22 - a12 * a21
            dx, dc = (f1 * a22 - a12 * f2) / det, (a11 * f2 - a21 * f1) / det
            xn, cn = xn - dx, cn - dc
            if abs(dx) + abs(dc) < 1e-13: break
        x, c = xn, cn
        out.append(x)
    return out

def reduced(T, dt, ptot):
    x, out = X0, []
    def R(x): return 1.0 / (1.0 + (1.0 + x / KD) ** 2 / (ptot / KD)) if ptot else 0.0
    # free X after fast binding equilibrates with total X0 conserved: solve x + ptot*x/(x+KD) = X0
    lo, hi = 0.0, X0
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid + ptot * mid / (mid + KD) > X0: hi = mid
        else: lo = mid
    x = (lo + hi) / 2
    for i in range(int(T / dt)):
        t = i * dt
        f = lambda xx, tt: (k(tt) - DELTA * xx) * (1 - R(xx))
        k1 = f(x, t); k2 = f(x + dt / 2 * k1, t + dt / 2); k3 = f(x + dt / 2 * k2, t + dt / 2); k4 = f(x + dt * k3, t + dt)
        x += dt / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        out.append(x)
    return out

def tail_stats(xs, dt, T):
    n = int((2 * math.pi / W) / dt)                      # last full period of the input
    seg = xs[-n:]
    hi, lo = max(seg), min(seg)
    t_peak = (len(xs) - n + seg.index(hi)) * dt
    return (hi - lo) / 2, (hi + lo) / 2, t_peak

if __name__ == "__main__":
    T, dt = 12000.0, 0.05
    iso = isolated(T, dt)
    a0, m0, tp0 = tail_stats(iso, dt, T)
    print(f"isolated          : amplitude {a0:.4f}  mean {m0:.4f}  (free X)")
    print(f"{'pTOT':>6s} {'amplitude':>10s} {'ratio':>7s} {'peak lag (time units)':>22s} {'R(mean X)':>10s} {'max |full-reduced|':>19s}")
    for ptot in (0.0, 1.0, 10.0, 100.0):
        con = connected(T, dt, ptot)
        red = reduced(T, dt, ptot)
        a, m, tp = tail_stats(con, dt, T)
        n = int((2 * math.pi / W) / dt)
        err = max(abs(p - q) for p, q in zip(con[-n:], red[-n:]))
        Rm = 1.0 / (1.0 + (1.0 + m / KD) ** 2 / (ptot / KD)) if ptot else 0.0
        print(f"{ptot:6.0f} {a:10.4f} {a / a0:7.3f} {tp - tp0:22.1f} {Rm:10.3f} {err:19.2e}")
```

## Revalidation

Cheapest discriminating checks:

1. **OpenQASM `extern` contract (minutes).** In a checkout of `openqasm/openqasm`, re-read `source/language/classical.rst`, section "Extern function calls", for the four sentences this report depends on: "may be neither fast nor guaranteed to return", "not required to be idempotent", "does not wait for that computation to terminate", and "We do not address issues such as how the `extern` functions are defined and registered." Any added timing, deadline or effect annotation changes Findings 5.2 and 6.3. In `delays.rst`, confirm that stretches are still "resolved at compile time" and that `box` still forbids moving operations across its boundary.
2. **Puddle droplet ids.** In `puddle-core/src/grid/droplet.rs` check whether `DropletId` still derives `Copy`. If it does not, and API methods take it by value, static single-use enforcement holds and Finding 9.2 must be revised. A decisive test where a Rust toolchain is available: a two-line program that passes the same `DropletId` to `mix` twice; it compiles if and only if the type is `Copy`.
3. **Lava LIF models.** Diff `src/lava/proc/lif/models.py` against the pinned commit for `ds_offset`, `dm_offset`, `decay_shift`, `vth_shift`, `act_shift` and the two `subthr_dynamics` bodies; then re-run E3 (output must match byte for byte if nothing changed). Where NumPy and Lava are installable, the stronger check is to run one `LIF` process under `Loihi1SimCfg(select_tag="floating_pt")` and `Loihi1SimCfg(select_tag="fixed_pt")` with identical input and compare spike times. Re-read the README for the archive notice.
4. **Decoder latency table.** These figures date quickly. Before reuse, check for newer results and, for each number, record code distance, whether qubits were in the loop, what interval the latency covers, and the cycle time. Re-read arXiv:2603.16203 for a later version with qubit-in-the-loop measurements.
5. **SimuQ solver.** In `src/simuq/solver.py` confirm the relax-truncate-re-solve description in the `solve_aligned` docstring and the residual tests against `tol`; a change to an exact or certified solver would change Finding 4's consequences.
6. **Cello target description.** Re-parse a sample UCF and list its `collection` names; a collection describing load, retroactivity or resource demand would change the last paragraph of Finding 8.4. Confirm the constants `STEPS`, `MAXTEMP`, `MINTEMP`, `D_GROWTH_THRESHOLD` in `SimulatedAnnealing.java`.
7. **Ark.** Confirm `AttrDefMismatch` and the three inheritance constraints against the paper and `ark/specification/`; confirm `ark/solver.py` still discharges validation through an SMT query.
8. **Mechanism models (seconds).** Re-run E1, E2, E4; outputs must match byte for byte. They depend only on the cited equations.

What cannot be revalidated cheaply: Legno's and Jaunt's device results (they require the HCDCv2 hardware and toolchain), the Cello yield (wet-lab construction of 60 circuits), and both decoder latencies (their respective hardware). For those, this report preserves the published statements and their stated conditions only.
