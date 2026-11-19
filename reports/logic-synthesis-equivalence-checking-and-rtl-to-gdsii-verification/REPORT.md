# Logic Synthesis, Equivalence Checking, and RTL-to-GDSII Verification

## Summary

Formal verification anchored at register-transfer level (RTL) Verilog/SystemVerilog or architectural ISA specifications leaves an unverified lowering chasm across logic synthesis, technology mapping, sequential retiming, physical place-and-route (PnR), static timing closure, and silicon fabrication. Closing this gap requires separating five distinct soundness layers that standard Boolean equivalence checks conflate:

1. **Verified vs. Synthesis-Guided Lowering (`Lutsig` / `Silver` vs. `Lakeroad`):** HOL4-verified compilation (`CakeML/hardware`: Silver `ag32` in PLDI 2019 and Lutsig in CPP 2021) transports source-level functional theorems down to bit-blasted, technology-mapped FPGA LUT/`Carry4` netlists (`compile_glue_thm`), removing intermediate Verilog/RTL semantics from the trusted computing base (TCB) while leaving Verilog pretty-printing, PnR, clocking, and bitstream encoding outside the theorem prover. Sketch-guided program synthesis (`uwsampl/lakeroad`, ASPLOS 2024) automates heterogeneous FPGA DSP/LUT/carry technology mapping over vendor HDL simulation models via Yosys BTOR extraction and Rosette SMT queries (`f_lr`), achieving 2–3.5× more optimal mappings than commercial tools on microbenchmarks while placing Rosette, SMT solvers (Bitwuzla/Z3), and vendor simulation models inside its TCB.
2. **Combinational vs. Sequential Equivalence Checking (`Yosys`, `EQY`, `ABC`):** Standard combinational equivalence checking (`CEC` via AIG/FRAIG SAT-sweeping in `berkeley-abc/abc` `cecCec.c` or latch-matched `YosysHQ/eqy` partitioning) is tractable only when gold and gate netlists preserve a 1-to-1 flip-flop (FF) correspondence. Once sequential retiming (`dretime` in `abc.cc`, `Abc_NtkRetime` in `retCore.c`) or FSM re-encoding moves registers across combinational cones, 1-to-1 `CEC` fails or becomes inapplicable and must be replaced by PSPACE-complete Sequential Equivalence Checking (`SEC` via `IC3`/`PDR` in `pdrCore.c` or k-induction in `YosysHQ/yosys` `equiv_induct.cc`), where mismatched initial register values break equivalence at cycle $t=0$ even when steady-state induction holds.
3. **4-State `1'bX` Don't-Care Destruction:** Default synthesis passes (`Yosys` `opt_expr` without `-keepdc`, `opt_expr -mux_undef`, and `abc.cc` undef-to-zero replacement) convert IEEE 1800 4-state `1'bX` values into arbitrary 2-state don't-care optimization freedom (`x ^ x -> 0`, `sel ? 1'bx : a -> a`, `State::Sx -> 0`). The resulting gate netlist passes 2-state `CEC` while silently diverging from 4-state RTL simulation (X-optimism).
4. **Glitch-Safe Masking Destruction (`DOM` / `PINI`):** Functional equivalence (`CEC`/`SEC`) preserves steady-state cycle-boundary Boolean values but does **not** preserve physical side-channel non-interference. Standard Boolean refactoring, cross-share CSE (`opt_merge`), or sequential retiming that removes or moves barrier registers in Domain-Oriented Masking (`DOM`) or Probe-Isolating Non-Interference (`PINI`) gadgets causes 1st-order glitch-extended probes (verified post-synthesis by `IAIK/coco-alma`) to jump from $0.000000\text{ bits}$ to $1.000000\text{ bit}$ of secret leakage while remaining 100% functionally equivalent.
5. **Timing Closure (`STA`) and Sub-Gate Analog Trojans (`A2`):** Functional netlists fail in silicon whenever multi-corner Static Timing Analysis (`OpenSTA` `PathEnd.cc` / `Crpr.cc`) leaves negative setup or hold slack—especially frequency-independent hold violations at fast-fast (FF) corners requiring post-synthesis buffer insertion (`OpenROAD`). Below the digital abstraction entirely, capacitor-charge analog hardware Trojans (`A2`, IEEE S&P 2016, fabricated in 65 nm CMOS on an `OR1200` processor) require a single-gate footprint in layout filler whitespace, evade RTL verification, `CEC`/`SEC`, DRC, and functional test vectors, and overwrite privileged architectural flip-flops directly via analog charge accumulation.

## Applicability

This report characterizes the formal verification boundary between behavioral RTL hardware descriptions and physical silicon/FPGA realizations across open-source synthesis/verification toolchains, mechanized hardware compilers, timing sign-off engines, and hardware security analyses:

- **Mechanized ITP hardware lowering:** `CakeML/hardware` @ `6da9399c3b93ddcefc3a3bc46f5ffeea7faeb0e8` (Lutsig verified Verilog-to-netlist compiler and HOL4 translation-validation LEC, CPP 2021, DOI `10.1145/3437992.3439916`) and `CakeML/hardware` @ `dc281059bd3a19e478fb211aadda1c2ac7891fa9` (Silver `ag32` processor theories from PLDI 2019, DOI `10.1145/3314221.3314622`, pinned separately because upstream `README.md` notes newer Verilog semantics commits broke `ag32` builds).
- **SMT-backed FPGA technology mapping:** `uwsampl/lakeroad` @ `c5c5a9ac4efc250374df7f9a37d59087a6cc7ba1` and its ASPLOS 2024 specification (`arXiv:2401.16526`, DOI `10.1145/3620665.3640387`), targeting heterogeneous FPGA primitives (e.g., Xilinx UltraScale+ `DSP48E2`/`LUT`/`CARRY8`, Lattice ECP5 `MULT18X18D`/`ALU24B`/`ALU54A`, Intel `altmult_accum`, SOFA).
- **Production open-source synthesis and equivalence checking:** `YosysHQ/yosys` @ `e4a169b8fea4c1e7121518937854672efa41c658`, `YosysHQ/eqy` @ `33015166c47398dff1ac72a699f4212891bb0618`, and `berkeley-abc/abc` @ `4f928c689ff6f1eedec245efc03897f4d2098bcf`, analyzed as a coupled RTL-to-gate synthesis and CEC/SEC verification pipeline.
- **Post-synthesis masking verification:** `IAIK/coco-alma` @ `95c80df5d6d704bf525f47ef6e58e98e27fedf97` paired with the formal PINI/DOM definitions (Cassiers & Standaert, IEEE TIFS 2020, DOI `10.1109/TIFS.2020.2971153`; Gross, Mangard & Korak, CCS 2016).
- **Post-synthesis timing sign-off and physical implementation:** `parallaxsw/OpenSTA` @ `cc510896e8e097771100d7dec4f5cbfdb3d6d71a` (setup/hold slack and CRPR formulation) and `The-OpenROAD-Project/OpenROAD` @ `4d08cb17e317284548659fd7040238db3206d940` (autonomous RTL-to-GDSII physical design context).
- **Sub-gate analog threat model:** `A2: Analog Malicious Hardware` (Yang, Hicks, Dong, Austin & Sylvester, IEEE S&P 2016, DOI `10.1109/SP.2016.10`).

**Relationship among subjects:** The subjects represent sequential and orthogonal stages of the RTL-to-GDSII verification stack rather than competing versions of one tool. `CakeML/hardware` and `Lakeroad` attempt to build correctness-by-construction into RTL-to-netlist synthesis; `Yosys`/`EQY`/`ABC` represent the industrial/open-source synthesis-plus-post-hoc-LEC paradigm; `CocoAlma` checks a hyperproperty (glitch-extended probing security) strictly orthogonal to `CEC`/`SEC`; `OpenSTA`/`OpenROAD` govern physical delay validity below logical equivalence; and `A2` demonstrates an adversarial physical fault class below all digital netlist abstractions. Results on specific optimization flags (`-keepdc`, `-mux_undef`, `-dff`, `keepff`) are tied directly to the inspected source revisions; broader principles (e.g., 4-state vs. 2-state divergence, retiming vs. CEC, glitch leakage under barrier removal, frequency-independence of hold violations) generalize to commercial EDA suites (Synopsys Design Compiler/Formality, Cadence Genus/Conformal, Xilinx Vivado) by identical mathematical mechanisms, though vendor-specific flag names and default heuristics were not directly examined.

## Findings

### 1. The RTL-to-GDSII Verification Chasm and Trust Boundary Decomposition

Basis: source + documentation + derived

Machine-code verification anchored at an architectural ISA specification (such as a Sail ISA model or an L3 HOL4 ISA model) proves properties of software assuming the physical processor implements that ISA faithfully on every clock cycle. Lowering a verified processor or accelerator from behavioral RTL to fabricated silicon traverses seven distinct semantic transformations, each introducing failure modes invisible to adjacent layers:

| Pipeline Stage | Representation | Primary Verification Oracle | Soundness Gap If Unchecked |
| :--- | :--- | :--- | :--- |
| **1. ISA / Spec to Behavioral RTL** | L3/Sail/HOL4 ISA $\to$ Verilog/SV | ITP refinement (`ag32EqScript.sml`), bounded/inductive model checking | Microarchitectural pipeline hazards, reset/interrupt corner cases |
| **2. RTL Elaboration & High-Level Opt** | Verilog AST $\to$ RTLIL / FIRRTL (`Yosys` `opt`) | `equiv_make`/`equiv_induct` (`-undef`), Lutsig `compile_correct` | 4-state `1'bX` collapsed to 2-state don't-care (`opt_expr -mux_undef`); masking registers merged or deleted |
| **3. Logic Opt & Sequential Retiming** | AIG / FRAIG (`ABC` `dc2`, `fraig`, `dretime`, `scorr`) | Combinational `CEC` (`cecCec.c`) or Sequential `SEC` (`pdrCore.c`) | Retiming changes FF count/reset values (breaking 1:1 `CEC`); cross-share logic merging breaks `PINI`/`DOM` |
| **4. Technology Mapping** | Gate/LUT/DSP netlist (`ABC` `if`/`&nf`, `Lakeroad`, `Lutsig`) | `LECScript.sml` (HOL4), Rosette SMT (`f_lr`), post-map `CEC`/`EQY` | Vendor primitive misconfiguration (e.g. `DSP48E2` port/mode constraints); undef-to-zero loss at `abc.cc` boundary |
| **5. Physical Design (PnR, CTS, Sizing)** | Placed/routed DEF/netlist (`OpenROAD`) | Post-PnR `LEC`, DRC, LVS | Buffer insertion, gate sizing, hold-fix cell swaps, and clock-tree synthesis mutate netlist after pre-PnR `LEC` |
| **6. Timing & Signal Integrity Closure** | Parasitic SPEF + Liberty + SDC (`OpenSTA`) | Multi-corner `STA` (setup/hold/CRPR/AOCV/SI) | Setup/hold metastability violations; clock-tree skew races; crosstalk glitches |
| **7. Foundry Mask & Silicon Fabrication** | GDSII/OASIS $\to$ 65 nm..2 nm CMOS | Post-silicon validation, optical/EM inspection | Fabrication-time analog Trojans (`A2` switched-capacitor charge pump) invisible to all digital checks |

A single end-to-end correctness theorem holds only if **every** adjacent stage shares a mechanically checked interface (removing intermediate representations from the TCB) or is checked by a sound post-hoc oracle whose abstraction preserves the property of interest (functional safety, `1'bX` safety, glitch non-interference, and timing closure).

---

### 2. Mechanized Hardware Lowering in HOL4: Silver (PLDI 2019) and Lutsig (CPP 2021)

Basis: source + normative (published HOL4 theorems in `CakeML/hardware`) + documentation

The `CakeML/hardware` project closes the software-to-netlist verification gap inside the HOL4 interactive theorem prover in two linked stages:

#### 2.1 End-to-End ISA-to-Verilog Connection: CakeML + Silver (`ag32`)

In *Verified Compilation on a Verified Processor* (Lööw, Kumar, Tan, Myreen, Norrish, Abrahamsson & Fox, PLDI 2019, DOI `10.1145/3314221.3314622`), the CakeML verified Standard ML compiler targets **Silver** (`ag32`), a 32-bit processor formalized in L3/HOL4 and lowered to Verilog via a proof-producing translator. In `CakeML/hardware` @ `dc281059bd3a19e478fb211aadda1c2ac7891fa9`, `ag32/ag32EqScript.sml` proves the simulation theorem `INIT_REL_circuit`:

```sml
val INIT_REL_circuit_lem = Q.store_thm("INIT_REL_circuit_lem",
 `!n cstep s facc init fext.
   cstep = circuit facc init fext /\
   INIT (fext 0) init s /\
   is_lab_env fext_accessor_circuit cstep fext /\
   is_acc accelerator_f cstep ==>
   ?m. REL (fext m) (cstep m) (FUNPOW Next n s)`, ...);
```

This relates $n$ architectural ISA steps (`FUNPOW Next n s`) to $m$ clock cycles of the HOL circuit model (`cstep m`) under environmental assumptions (`is_lab_env`: memory and interrupt protocol compliance; `is_acc`: accelerator contract), which the proof-producing translator transports to a Verilog AST. Crucially, however, in the 2019 Silver stack, Verilog synthesis and FPGA mapping remained outside HOL4 (executed by commercial Vivado/Quartus tools).

#### 2.2 Verified Verilog-to-Netlist Synthesis and Hybrid LEC: Lutsig (CPP 2021)

**Lutsig** (Lööw, CPP 2021, DOI `10.1145/3437992.3439916`, `CakeML/hardware` @ `6da9399c3b93ddcefc3a3bc46f5ffeea7faeb0e8`) removes Verilog semantics and RTL-to-netlist lowering from the TCB by compiling a typed subset of Verilog (`verilog/verilogScript.sml`) down to technology-mapped FPGA netlists inside HOL4.

Inspection of `compiler/RTLScript.sml`, `compiler/fullCompilerScript.sml`, `compiler/LECScript.sml`, and `compiler/compileScript.sml` establishes the exact architecture and semantic contract:

1. **Two-state netlist target with oracle-resolved `X`:** `compiler/RTLScript.sml` defines netlist types strictly as 2-state Booleans (`rtltype = CBool_t | CArray_t num`; `value = CBool bool | CArray (bool list)`). At the source Verilog level (`Lutsig` Section 4.1), blocking/non-blocking `X` assignments (`e = X`, `e <= X`) are modeled via nondeterministic oracle bits (`fbits` / `NDetCell`). The pass `RTLDeterminizer` (`RTLDeterminizerProofScript.sml`) resolves every `NDetCell` to a deterministic Boolean, proving refinement (the deterministic netlist matches *some* oracle choice `vfbits` of the nondeterministic Verilog semantics).
2. **Verified compilation pipeline (`compile_correct`):** `compiler/fullCompilerScript.sml` composes dependency sorting (`sort_by_deps_correct`), type checking (`typecheck_sound`), preprocessing (`preprocess_correct`), RTL netlist generation (`rtl_compile_correct`), determinization (`rtl_determinizer_correct`), unused-register removal (`rtl_rem_unused_regs_correct`), and bit-blasting (`blast_circuit_correct`) into a single theorem:
   ```sml
   Theorem compile_correct:
    !m circuit fbits vfext rtlfext n.
    compile m = INR circuit ⇒
    vertype_fext m.fextty vfext ∧ same_fext vfext rtlfext ⇒
    blasted_circuit circuit ∧
    rtltype_extenv (circuit_extenv circuit) rtlfext ∧
    (∀var i. MEM var (FLAT (MAP vwrites m.combs)) ⇒ ~MEM (var, i) (MAP FST (circuit_regs circuit))) ∧
    ?cenv' fbits'. circuit_run_no_pseudos rtlfext fbits circuit n = INR (cenv', fbits') /\
                   ?vfbits. case sort_run vfext vfbits m n of
                              INL e => T
                            | INR (venv', vfbits') => verilog_netlist_rel m venv' cenv'
   ```
   Notice the exact semantic subtlety in the `INL e => T` branch: if the source Verilog program produces a runtime error (`INL e`, such as out-of-bounds array indexing or type failure), the compiler is permitted to emit any deterministic behavior—analogous to CompCert's undefined-behavior refinement.
3. **Hybrid translation-validation technology mapping (`LECScript.sml` + `compile_glue_thm`):** Rather than verifying an aggressive LUT-packing heuristic directly, Lutsig runs an unverified greedy technology mapper (`GreedyTechMapLib.sml`) targeting `CellLUT` (FPGA $k$-LUTs) and `Carry4` (arithmetic carry chains, `LECScript.sml` lines 48–62), then invokes a proof-producing combinational equivalence checker (`LECLib.sml` / `LECScript.sml`) that constructs a HOL4 theorem proving `circuit_run_no_pseudos fext fbits tech_circuit n = circuit_run_no_pseudos fext fbits circuit n`. `compiler/compileScript.sml` (`Theorem compile_glue_thm`) composes `compile_correct` with this per-compilation LEC theorem to transport source Verilog correctness all the way to the LUT/`Carry4` netlist.
4. **Remaining TCB boundary:** As documented explicitly in Lutsig Section 3 (Figure 1, steps `(I) -> (J) -> (K)`), **Verilog pretty-printing**, **placement and routing (PnR)**, **clocking / timing closure**, and **FPGA bitstream encoding** remain unverified external steps outside HOL4.

---

### 3. Sketch-Guided Program Synthesis for Heterogeneous FPGA Technology Mapping (`Lakeroad`)

Basis: source (`uwsampl/lakeroad` @ `c5c5a9ac4efc250374df7f9a37d59087a6cc7ba1`) + documentation (`arXiv:2401.16526`, ASPLOS 2024)

While Lutsig targets homogeneous LUT + `Carry4` fabrics and ABC maps generic gate graphs via structural cut enumeration (`if`), modern FPGAs rely heavily on deeply configurable hard primitives such as Xilinx UltraScale+ `DSP48E2` (nearly 100 ports/parameters, 75-page manual) or Lattice ECP5 `MULT18X18D`/`ALU54A`. Commercial synthesizers map to these via handwritten syntactic pattern rules that miss valid configurations (e.g., `add_mul_and` failing to pack onto one `DSP48E2`).

`uwsampl/lakeroad` (Smith et al., ASPLOS 2024, DOI `10.1145/3620665.3640387`) recasts technology mapping as **sketch-guided program synthesis**:

1. **Formal synthesis specification (`f_lr` and `f*_lr`):** Section 3 of `arXiv:2401.16526` defines Lakeroad as a partial function $f_{\text{lr}} : \text{Sketch} \times \mathcal{L}_{\text{beh}} \times \text{Time} \rightharpoonup \mathcal{L}_{\text{struct}}$, where a sketch $\Psi = (\psi, h)$ maps syntactic holes $\blacksquare_x$ (configuration parameters, LUT truth tables, mux selectors, port bindings) to finite domains in $\mathcal{L}_{\text{struct}}$.
   - For combinational designs ($t = 0$), Rosette solves $\exists h.\ \forall \text{inputs}.\ \text{Interp}(\Psi[h], \text{inputs}, 0) = \text{Interp}(d, \text{inputs}, 0)$.
   - For pipelined sequential designs ($t > 0$), $f_{\text{lr}}(\Psi, d, t)$ checks equivalence *at cycle $t$* (permitting initialization/pipeline-fill divergence for cycles $< t$), generalized to $f^*_{\text{lr}}$ checking cycles $t \dots t+n$.
   - Well-formedness (`W1`–`W4`, acyclicity of combinational edges) guarantees `Interp` is primitive recursive in $(p, t, n)$ (Lemma 3.1), ensuring Rosette's symbolic evaluation to SMT formulas always terminates.
2. **Automated semantics extraction from vendor HDL:** Rather than hand-modeling each vendor primitive in Rosette, Lakeroad runs Yosys to compile vendor-published simulation Verilog models (e.g., `DSP48E2.v`, `ALU24B.v`) into BTOR2, which `racket/btor.rkt` translates directly into executable Rosette bitvector functions (`racket/generated/lattice-ecp5-mult18x18d.rkt`, etc.) using immutable state hashes (`init-hash`, `merged-input-state-hash`, `output-state-hash`).
3. **Architecture-independent sketch templates (`racket/sketches.rkt`):** `all-sketch-generators` tries ordered blueprints (`bitwise-sketch-generator`, `carry-sketch-generator`, `bitwise-with-carry-sketch-generator`, `comparison-sketch-generator`, `multiplication-sketch-generator`, plus `single-dsp-sketch-generator` and `two-dsp-sketch-generator`), querying Rosette (`rosette-synthesize` with Bitwuzla/Z3 in `racket/synthesize.rkt`) under per-template timeouts (`with-deep-time-limit`, clearing `clear-vc!` / `clear-terms!` on timeout).
4. **Correctness & TCB comparison vs. Lutsig:** Across ASPLOS 2024 microbenchmarks, Lakeroad yields 2–3.5× more optimal mappings than commercial tools and 6–44× more than open-source tools. However, its TCB (Section 3.4) strictly includes: (a) Rosette and underlying SMT solvers (Bitwuzla/Z3, without proof-certificate checking in an ITP), (b) Yosys BTOR extraction and Lakeroad's Racket encoder/Verilog emitter, (c) fidelity of **vendor-published Verilog simulation models** to real silicon (which are themselves 2-state/4-state behavioral approximations lacking timing or analog physics), and (d) bounded $t$-cycle equivalence rather than unbounded inductive SEC for arbitrary stateful feedback loops.

---

### 4. Combinational and Sequential Equivalence Checking (`Yosys`, `EQY`, `ABC`)

Basis: source (`YosysHQ/yosys`, `YosysHQ/eqy`, `berkeley-abc/abc`) + execution (Micro-Probe 1, Probe 2)

Post-hoc Logic Equivalence Checking (LEC) is the dominant industrial mechanism for validating untrusted synthesis optimizations. Source inspection of `Yosys`, `EQY`, and `ABC` reveals the exact algorithmic boundary between tractable `CEC` and PSPACE-complete `SEC`.

#### 4.1 AIG, FRAIG SAT-Sweeping, and Combinational Equivalence (`ABC` `cecCec.c` & `Yosys` `abc.cc`)

In `YosysHQ/yosys` (`passes/techmap/abc.cc`, lines 32–35), the default ABC synthesis scripts apply aggressive structural rewriting and SAT-sweeping:

```text
ABC_COMMAND_LIB: "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf {D}; &put"
ABC_COMMAND_LUT: "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; dch -f; if; mfs2"
```

- `strash` converts the network to a structurally hashed **And-Inverter Graph (AIG)** (2-input AND nodes + complemented edges).
- `&fraig -x` builds a **Functionally Reduced AIG (FRAIG)** by random simulation to group candidate equivalent nodes followed by incremental SAT queries to merge provably equivalent internal cuts.
- `dc2` performs DAG-aware AIG rewriting; `&dch -f` computes structural choices (recording equivalent subgraphs so technology mapping `if` / `&nf` can choose minimum-area/delay cuts).
- `berkeley-abc/abc` (`src/proof/cec/cecCec.c`) checks combinational equivalence of two designs by constructing a miter AIG, running random/guided simulation (`Cec_ManSimulateCombOutputs`) to catch quick counterexamples, and applying FRAIG SAT-sweeping to collapse internal equivalent cones bottom-up until miter outputs reduce to constant `0` (or SAT yields an input witness `Abc_Cex_t`).
- **Critical `-dff` gating in Yosys `abc.cc`:** By inspection of `AbcModuleState::prepare_cell` (`passes/techmap/abc.cc`, lines 390–395), Yosys skips built-in flip-flops (`if (!dff_mode) return false;`) unless `-dff` is explicitly passed. Consequently, `scorr` (sequential signal correspondence) and `dretime` (delay-driven sequential retiming) in the default script operate on flip-flops **only** when `-dff` is enabled (and `-keepff` pins `is_port = true` on `ff.sig_q` at lines 465–470 to prevent `dretime`/`scorr` from deleting or moving named registers).

#### 4.2 Partitioned LEC (`EQY`) vs. Sequential Equivalence Checking (`equiv_induct`, `ABC` `pdrCore.c`, `retCore.c`)

- **`Yosys` `$equiv` flow and `EQY` partitioning:** `YosysHQ/yosys` (`passes/equiv/equiv_make.cc`) clones gold and gate modules, renames matching public wires/cells with `_gold`/`_gate` suffixes, inserts `$equiv` miter cells (optionally mapping re-encoded FSM states via `.fsm`/`.map` directives in `read_encfiles()`), and proves them with `equiv_simple` (combinational backward cone traversal stopping at flip-flops or shared nodes, `passes/equiv/equiv_simple.cc` lines 105–130) or `equiv_induct` (bounded k-induction up to `cfg.max_seq`, `passes/equiv/equiv_induct.cc`, explicitly proving base-case consistency `ez_step_is_consistent[step]` before inductive step). `YosysHQ/eqy` (`src/eqy_partition.cc`) scales this by decomposing gold/gate netlists along matched register/wire boundaries (`gold_matches`, `gate_matches`, `group`/`solo`/`bind` rules) into independent per-partition subproblems.
- **Why retiming defeats `CEC` and `EQY`:** `berkeley-abc/abc` (`src/opt/ret/retCore.c`, `Abc_NtkRetime`) implements six sequential retiming modes (Mode 1 forward, Mode 2 backward, Mode 3 min-area, Mode 4 min-delay, Mode 5 min-area+min-delay, Mode 6 Pan's l-value algorithm). Retiming moves flip-flops across combinational gates, changing both the **count** and **encoding** of state elements. Because no 1-to-1 FF cut exists, `CEC` and default latch-matched `EQY` fail.
- **PSPACE-complete `SEC` (`IC3`/`PDR`):** Proving equivalence across retiming requires verifying that the product machine $\mathcal{M}_{\text{gold}} \times \mathcal{M}_{\text{gate}}$ never reaches an output-mismatch state from the initial state $I_0$ across unbounded cycles. `berkeley-abc/abc` (`src/proof/pdr/pdrCore.c`) implements **Property Directed Reachability (`IC3`/`PDR`)**, maintaining a monotone sequence of over-approximating frame clauses $F_0, F_1, \dots, F_k$ and generalizing counterexample-to-induction cubes via minimal inductive clause (MIC) SAT queries (`Pdr_ManGipSetMicDomain`) until an inductive invariant $F_i = F_{i+1}$ separates initial states from bad states.
- **Initial-state retiming hazard (Execution witness):** Backward retiming across inverting or non-zero-preserving logic (e.g., pulling two input registers $r_a(0)=0, r_b(0)=0$ backward across a `NAND` gate into a single output register $r_y$) requires transforming the reset value to $r_y(0) = \neg(0 \wedge 0) = 1$. As confirmed by Micro-Probe 1 (Probe 2 below), naive zero-initialization $r_y(0)=0$ satisfies the inductive transition step with `0` step counterexamples yet **violates SEC at $t=0$** ($y_{\text{gold}}(0)=1 \ne 0=y_{\text{gate}}(0)$). Even worse, backward retiming across certain non-surjective multi-output cones has *no* equivalent initial state without adding explicit reset-cycle muxes (the Singhal–Pixley–Rudell–Brayton initial-state retiming obstruction).

---

### 5. Why Synthesis Destroys `1'bX` Safety and `PINI`/`DOM` Glitch Immunity

Basis: source (`YosysHQ/yosys`, `IAIK/coco-alma`) + execution (Micro-Probe 1, Probes 1 & 3) + normative (`IEEE TIFS 2020`, `CCS 2016`)

Two high-consequence classes of RTL bugs arise specifically because logic synthesis optimizes strictly for 2-state steady-state Boolean equivalence.

#### 5.1 4-State `1'bX` Don't-Care Exploitation (X-Optimism)

IEEE 1800 SystemVerilog defines 4-state logic (`0`, `1`, `X`, `Z`), where `1'bX` represents unknown/uninitialized state or unreachable/error branches. Synthesis tools treat `1'bX` as a **don't-care** (any concrete `0` or `1` is a valid refinement):

1. **`opt_expr` default `keepdc = false` (`YosysHQ/yosys` `passes/opt/opt_expr.cc`, lines 35–40, 194–203):**
   ```cpp
   else if (!config.keepdc) {
       if (cell->type == ID($xor)) {
           if (bit_a == bit_b) bit_a = bit_b = RTLIL::State::S0;
       } else if (cell->type == ID($xnor)) {
           if (bit_a == bit_b) bit_a = bit_b = RTLIL::State::S1;
       }
   }
   ```
   When `x = 1'bx`, 4-state RTL simulation computes `x ^ x == 1'bx`, whereas `opt_expr` without `-keepdc` silently folds `x ^ x` to constant `1'b0`.
2. **`opt_expr -mux_undef` (`passes/opt/opt_expr.cc`, lines 1185–1189, 1513–1525):** When enabled (forwarded via `opt -mux_undef`, `passes/opt/opt.cc` line 90), any `$mux` or `$pmux` branch whose data or select input is `State::Sx` is deleted (`replace_cell(cell, "mux_undef", ID::Y, cell->getPort(ID::A))`). Thus `sel ? 1'bx : a` synthesizes unconditionally to `a`, discarding `sel` entirely.
3. **ABC boundary undef loss (`passes/techmap/abc.cc`, lines 1146–1147):** Because ABC's AIG representation is strictly 2-state, Yosys explicitly replaces constant undef bits crossing into ABC with constant zero (`Replacing %d occurrences of constant undef bits with constant zero bits`).
4. **SAT equivalence checker asymmetry (`kernel/satgen.h`, lines 76–105, 182–220):** Yosys's `SatGen` defaults to `model_undef(false)` (pure 2-state SAT). Only when `-undef` is explicitly passed (`model_undef = true`) does `SatGen` encode dual-rail `(def_bit, undef_bit)` tracking, and even then `equiv_induct.cc` forces initial register states and primary inputs to be defined (`ez->assume(ez->NOT(satgen.importUndefSigBit(bit, 1)))`). Consequently, default 2-state `CEC` reports gold and gate netlists as **equivalent** even when 4-state simulation diverges on uninitialized reset paths or `case` default `X`-assignments (demonstrated quantitatively in Micro-Probe 1, Probe 1).

#### 5.2 Glitch-Extended Probing and Synthesis Destruction of `DOM` / `PINI` Masking

Hardware side-channel countermeasures split every secret bit $x$ into $d+1$ uniform Boolean shares $x = x_0 \oplus \dots \oplus x_d$ so that any $d$ probes reveal zero information ($d$-probing security). In physical CMOS circuits, however, combinational gates switch at unequal arrival times, producing **transient glitches** that cause a single physical wire probe to observe *all* stable signals in its combinational fan-in cone back to the nearest register (synchronization) boundary—the **glitch-extended robust probing model** (Faust et al., CHES 2018; Cassiers & Standaert, **PINI**, IEEE TIFS 2020, DOI `10.1109/TIFS.2020.2971153`).

Inspection of `IAIK/coco-alma` @ `95c80df5d6d704bf525f47ef6e58e98e27fedf97` (`examples/gadgets/design/dom_and.v` and `SatChecker.py`) demonstrates the exact structural invariant that synthesis violates:

- In **Domain-Oriented Masking (`DOM-AND`)** (Gross, Mangard & Korak, CCS 2016; `dom_and_1storder` in `dom_and.v`):
  - Same-domain terms: $A_0 = x_0 \wedge y_0$, $B_1 = x_1 \wedge y_1$.
  - Cross-domain blinded terms registered **before** recombination:
    $$R_0 \Leftarrow (x_0 \wedge y_1) \oplus z, \qquad R_1 \Leftarrow (x_1 \wedge y_0) \oplus z$$
  - Output shares: $Q_0 = R_0 \oplus (x_0 \wedge y_0)$, $Q_1 = R_1 \oplus (x_1 \wedge y_1)$.
- The register $R_0$ acts as a **glitch barrier**: at $Q_0$, a glitch-extended probe observes $(x_0, y_0, R_0)$ where $R_0 = (x_0 \wedge y_1) \oplus z$ is freshly blinded by uniform $z$, giving $I(\text{probe}; (x, y)) = 0.000000\text{ bits}$.
- **How synthesis breaks DOM/PINI while passing CEC/SEC:**
  1. **Register retiming (`dretime`) or removal (`opt_dff`):** Moving $R_0$ downstream past the final XOR (or merging/optimizing registers across pipeline boundaries) places $(x_0, y_0, y_1, z)$ in the **same combinational cone** driving $Q_0$. Even though $Q_0 \oplus Q_1 = x \wedge y$ remains 100% functionally identical, Micro-Probe 1 (Probe 3) proves that a single glitch-extended probe at $Q_0$ now observes $(x_0, y_0, y_1, z)$, yielding **$I(\text{probe}; (x, y)) = 1.000000\text{ bit}$** (complete recovery of secret $y = y_0 \oplus y_1$ in one probe).
  2. **Algebraic factoring / CSE (`opt_expr`, `opt_merge`, `ABC` `dc2`/`fraig`):** Factoring $(x_0 \wedge y_0) \oplus (x_0 \wedge y_1) \to x_0 \wedge (y_0 \oplus y_1)$ directly computes the unmasked secret $y_0 \oplus y_1 = y$ on an internal wire! Even with `(* keep = 1 *)` / `(* dont_touch = "true" *)` attributes in RTL, standard synthesis passes across hierarchy flattening (`flatten`), `opt_share`, or unguarded ABC rewriting (`-keepff` omitted) can merge cross-share subexpressions or reorder MUX/XOR trees unless explicitly verified **on the post-synthesis gate netlist**.
  3. **Post-synthesis verification (`IAIK/coco-alma`):** `SatChecker.py` (lines 15–17) explicitly constructs three separate SAT propagation layers on the synthesized Yosys JSON gate netlist (`parse.py`): `node_vars_stable` (steady-state probing), `node_vars_trans` (combinational glitch propagation back to register barriers), and `node_vars_diff` (register transition leakage across consecutive cycles). Only post-synthesis netlist verification (after `keep`/`dont_touch` hardening and re-run after PnR) certifies that synthesis did not destroy masking.

---

### 6. Multi-Corner Static Timing Analysis (`OpenSTA`), Physical Resizing (`OpenROAD`), and Sub-Gate Analog Trojans (`A2`)

Basis: source (`parallaxsw/OpenSTA`, `The-OpenROAD-Project/OpenROAD`) + execution (Micro-Probe 1, Probe 4) + normative (`Yang et al., IEEE S&P 2016`)

#### 6.1 Static Timing Closure Equations and CRPR (`OpenSTA`)

Logical equivalence (even verified in HOL4) guarantees nothing if setup or hold timing windows are violated in silicon, driving flip-flops into **metastability**. Inspection of `parallaxsw/OpenSTA` @ `cc510896e8e097771100d7dec4f5cbfdb3d6d71a` (`search/PathEnd.cc` lines 728–755 and `search/Crpr.cc` lines 53–103) establishes the exact sign-off slack equations:

- **Setup Check (max/late data vs. min/early capture clock, worst at Slow-Slow / high-T / low-V corner):**
  $$T_{\text{arr,late}} = T_{\text{clk,launch,late}} + T_{\text{cq,max}} + T_{\text{comb,max}}$$
  $$T_{\text{req,setup}} = T_{\text{clk}} + T_{\text{clk,cap,early}} - T_{\text{su}} - T_{\text{uncert}} + \text{CRPR}$$
  $$\text{Slack}_{\text{setup}} = T_{\text{req,setup}} - T_{\text{arr,late}} \ge 0$$
- **Hold Check (min/early data vs. max/late capture clock, worst at Fast-Fast / low-T / high-V corner):**
  $$T_{\text{arr,early}} = T_{\text{clk,launch,early}} + T_{\text{cq,min}} + T_{\text{comb,min}}$$
  $$T_{\text{req,hold}} = T_{\text{clk,cap,late}} + T_{\text{hold}} + T_{\text{uncert}} - \text{CRPR}$$
  $$\text{Slack}_{\text{hold}} = T_{\text{arr,early}} - T_{\text{req,hold}} \ge 0$$

Two critical physical verification properties follow directly from these equations (verified quantitatively in Micro-Probe 1, Probe 4):
1. **Clock Reconvergence Pessimism Removal (`CRPR`, `Crpr.cc` lines 53–70):** On-Chip Variation (OCV) derates launch and capture clock trees oppositely (e.g., `0.90` early vs. `1.10` late). For the shared trunk upstream of the clock divergence point (`crpr_clk_path`), a single clock edge cannot physically travel both fast and slow simultaneously. `CheckCrpr::maxCrpr` computes $|T_{\text{common,late}} - T_{\text{common,early}}|$ and credits it back. Without CRPR, short paths experience large **false hold violations** (`-52.0 ps` in Probe 4 turning into `+8.0 ps` PASS with CRPR), causing physical resizers to insert gratuitous delay buffers that degrade area, power, and setup slack.
2. **Hold violations are frequency-independent:** Notice $T_{\text{clk}}$ **does not appear** in the hold equation (for same-edge capture). Unlike a setup violation—which can be rescued post-silicon by lowering clock frequency—a real hold violation (`-12.0 ps` on a short shift-register path in Probe 4) causes permanent silicon failure at *every* clock frequency, requiring physical delay-buffer insertion during PnR (`OpenROAD`). Furthermore, because PnR resizing, buffer insertion, and clock-tree synthesis mutate the gate netlist *after* synthesis, **LEC and glitch-probing verification must be re-executed on the post-PnR (pre-GDSII) netlist**, not merely the post-synthesis netlist.

#### 6.2 Sub-Gate Analog Hardware Trojans (`A2`, IEEE S&P 2016)

Even a formally verified HOL4 RTL-to-netlist proof, post-PnR `SEC`, post-PnR `CocoAlma` glitch proof, and clean multi-corner `OpenSTA` sign-off share a fundamental **digital-abstraction boundary**: they assume the fabricated silicon implements only the digital cells and interconnect present in the verified netlist.

*A2: Analog Malicious Hardware* (Yang, Hicks, Dong, Austin & Sylvester, IEEE S&P 2016, DOI `10.1109/SP.2016.10`) demonstrated a fabrication-time attack below this boundary on an actual **65 nm GP CMOS tapeout of the OR1200 32-bit RISC processor**:

- **Trigger mechanism:** Instead of a multi-hundred-gate digital counter (easily caught by area/power anomaly checks, netlist inspection, or functional ATPG testing), A2 uses a **single-gate-footprint switched-capacitor charge pump** (`C_unit` + `C_main` built from MOS capacitors placed in empty filler whitespace of an ~80%-utilized placed-and-routed layout).
- **Charge accumulation dynamics:** Each rare toggle of a software-controllable victim wire transfers an incremental charge packet $\Delta V = \frac{C_{\text{unit}}}{C_{\text{unit}} + C_{\text{main}}}(V_{\text{DD}} - V_0)$ onto $C_{\text{main}}$ while subthreshold leakage continuously drains $C_{\text{main}}$. Normal workloads toggle the victim wire too infrequently for $V(C_{\text{main}})$ to overcome leakage; an attacker running a tight unprivileged instruction loop toggles the wire rapidly until $V(C_{\text{main}})$ crosses a compact voltage detector threshold.
- **Payload:** Upon crossing threshold, the detector drives an asynchronous overwrite on the flip-flop holding the `OR1200` processor's **supervisor/privilege mode bit** (`SR[SM]`), escalating unprivileged user code directly to kernel/supervisor privilege without executing any privileged instruction or violating any ISA-level invariant in the RTL.
- **Why every RTL-to-netlist verifier misses A2:** (1) Inserted at GDSII/mask fabrication time after RTL/netlist sign-off; (2) occupies filler/decoupling-capacitor whitespace with negligible static power or area delta; (3) inactive under functional manufacturing test vectors because charge leaks away unless driven at sustained rare-toggle frequency; (4) relies on analog capacitance/leakage physics wholly absent from Boolean AIGs, HOL4 netlist models, and digital Liberty cell timing tables.

---

### 7. Executable Verification Micro-Probe Results

Basis: execution (Python 3.13.5, stdlib only, deterministic exhaustive verification)

Running `/tmp/probe_synthesis_hazards.py` reproduces all four core failure mechanisms quantitatively:

```text
=== PROBE 1: 4-State Verilog (1'bX) vs 2-State Synthesis (Yosys opt_expr) ===
x ^ x divergences (4-state RTL vs opt_expr !keepdc): [('X', 'X', 0)]
mux(sel, a, 1'bx) 4-state divergences (count=4): [(1, 0, 'X', 0), (1, 1, 'X', 1), ('X', 0, 'X', 0), ('X', 1, 'X', 1)]
mux(sel, a, 1'bx) divergences where sel,a in {0,1} (RTL='X' vs gate=a): [(1, 0, 'X', 0), (1, 1, 'X', 1)]

=== PROBE 2: Sequential Retiming (CEC Failure vs SEC Inductive Proof & Reset Bug) ===
Backward-retimed AND (init 0,0 -> 0): base_ok=True, step_cex=0 (SEC PROVED; 2 FFs != 1 FF so 1:1 CEC inapplicable)
Backward-retimed NAND naive zero-init (init 0,0 -> 0): base_ok=False, step_cex=0 (t=0 SEC VIOLATION: gold=1, gate=0)
Backward-retimed NAND fixed init (init 0,0 -> 1): base_ok=True, step_cex=0 (SEC PROVED)

=== PROBE 3: DOM-AND 1st-Order Glitch-Extended Probing vs Synthesis Register Removal ===
Functional masking correctness (q0 ^ q1 == x & y for all 32 states): True
Intact DOM-AND Stage-1 glitch probe (x0, y1, z) I(probe; x,y) = 0.000000 bits
Intact DOM-AND Stage-2 glitch probe (x0, y0, reg_q) I(probe; x,y) = 0.000000 bits
Retimed/unregistered DOM-AND glitch probe (x0, y0, y1, z) I(probe; x,y) = 1.000000 bits (LEAKS full y = y0^y1!)

=== PROBE 4: Multi-Corner STA Setup/Hold Slack & CRPR (OpenSTA PathEnd.cc Equations) ===
Setup (T_clk=1000ps): arrival=1248.0ps, req_no_crpr=1286.0ps (slack=+38.0ps), req_with_crpr=1346.0ps (slack=+98.0ps)
Hold (normal short path, T_comb_min=25ps): arrival=412.0ps, req_no_crpr=464.0ps (slack=-52.0ps FALSE VIOLATION), req_with_crpr=404.0ps (slack=+8.0ps PASS)
Hold (shift-reg T_comb_min=5ps): arrival=392.0ps, req_with_crpr=404.0ps (slack=-12.0ps REAL VIOLATION regardless of T_clk!)
```

## Boundaries

- **Commercial proprietary EDA tools (`Synopsys Design Compiler/Formality`, `Cadence Genus/Conformal`, `Xilinx Vivado`):** **not examined** directly due to licensing restrictions. While the underlying mathematical properties (4-state `1'bX` don't-care semantics, CEC vs. SEC retiming barriers, glitch-barrier destruction, and setup/hold/CRPR STA equations) apply generically, specific proprietary flags, default optimization passes, and undocumented heuristics are not characterized here.
- **Physical Layout-vs-Schematic (`LVS`), Design Rule Checking (`DRC`), and FPGA bitstream reverse-engineering/verification:** **not examined** at source level. Neither `Lutsig` nor `Lakeroad` verifies PnR or bitstream encoding (`Lutsig` explicitly places `(I) -> (J) -> (K)` outside its HOL4 TCB).
- **Multi-clock-domain crossings (`CDC`) and asynchronous reset synchronizers:** **not examined**. Both `Lutsig` and `Lakeroad` assume a single synchronous clock domain; multi-clock metastability (`MTBF`) and CDC convergence analysis require separate structural/formal CDC checkers beyond single-clock `STA` and `SEC`.
- **Higher-order ($d \ge 2$) transition/coupling leakage and physical EM/optical Trojan detection countermeasures:** **not examined** empirically. `IAIK/coco-alma` checks glitch-extended probing and register transition leakage (`node_vars_diff`), whereas physical electromagnetic/capacitive coupling between adjacent routed wires and post-silicon side-channel/backside-imaging defenses against `A2` lie outside digital netlist verification.
- **Lutsig support for full IEEE 1800 SystemVerilog and Silver build compatibility at HEAD:** **unsupported** at `CakeML/hardware` @ `6da9399c3b93ddcefc3a3bc46f5ffeea7faeb0e8`. Lutsig compiles a deliberately restricted Verilog subset (no implicit array resizing, single clock, no analog/tristate `Z` buses), and `README.md` notes that the `ag32` Silver theories require pinning back to `dc281059bd3a19e478fb211aadda1c2ac7891fa9`.
- **Unbounded sequential verification in Lakeroad:** **unsupported** in `f_lr` / `f*_lr` (`arXiv:2401.16526` Section 3.1, 3.5), which checks bounded $t$-cycle (or $t \dots t+n$) pipeline equivalence via SMT rather than unbounded inductive `SEC` for general feedback state machines.
- **What passing `CEC`/`SEC` does NOT establish:** Clean `CEC` or `SEC` establishes *only* 2-state cycle-boundary functional equivalence under the checked reset/input constraints; it must **never** be mistaken for a proof of 4-state `1'bX` equivalence, `DOM`/`PINI` glitch security, multi-corner timing closure, or absence of fabrication-time analog hardware Trojans.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)
- `CakeML/hardware` @ `6da9399c3b93ddcefc3a3bc46f5ffeea7faeb0e8`:
  - `README.md`: repository structure (`verilog/`, `compiler/`, `translator/`, `ag32/`) and explicit note pinning Silver builds to `dc281059bd3a19e478fb211aadda1c2ac7891fa9`.
  - `compiler/RTLScript.sml` (lines 1–110): 2-state netlist datatypes (`rtltype = CBool_t | CArray_t num`, `value = CBool bool | CArray (bool list)`).
  - `compiler/fullCompilerScript.sml` (`Theorem compile_correct`, `Triviality compile_correct_alt`): full HOL4 proof composing dependency sorting, type checking, preprocessing, RTL compilation, `RTLDeterminizer`, unused-register elimination, and bit-blasting.
  - `compiler/LECScript.sml` (lines 1–100): `cell_inps_ok` (`CellLUT`, `Carry4`, rejecting `NDetCell`/`CellArrayWrite`), `Eval_def` for proof-producing combinational equivalence checking.
  - `compiler/compileScript.sml` (`Theorem compile_glue_thm`): composition of `compile_correct` with per-run translation-validation LEC theorem.
- `CakeML/hardware` @ `dc281059bd3a19e478fb211aadda1c2ac7891fa9`:
  - `ag32/ag32EqScript.sml` (`REL_circuit`, `INIT_circuit`, `INIT_REL_circuit_lem`, `INIT_REL_circuit`): HOL4 refinement between Silver `ag32` ISA `FUNPOW Next n s` and hardware cycle steps `cstep m`.
- `uwsampl/lakeroad` @ `c5c5a9ac4efc250374df7f9a37d59087a6cc7ba1`:
  - `racket/synthesize.rkt` (lines 1–140): `synthesize-any`, `synthesize-all`, `synthesize-with-sketch`, `rosette-synthesize` with Bitwuzla solver and `with-deep-time-limit` timeout wrapper.
  - `racket/sketches.rkt` (lines 1–110): `all-sketch-generators`, `sketch-inputs` struct, `bitwise-sketch-generator` with Rosette `(?? boolean?)` holes.
  - `racket/btor.rkt` (lines 1–110): Yosys BTOR2-to-Rosette state-hash translation (`init-hash`, `merged-input-state-hash`, `output-state-hash`).
- `YosysHQ/yosys` @ `e4a169b8fea4c1e7121518937854672efa41c658`:
  - `passes/opt/opt.cc` (lines 28–97): `OptPass` pipeline ordering (`opt_expr`, `opt_merge`, `opt_muxtree`, `opt_reduce`, `opt_share`, `opt_dff`, `opt_clean`) and `-mux_undef` / `-keepdc` forwarding.
  - `passes/opt/opt_expr.cc` (lines 33–41, 194–206, 1185–1189, 1513–1572): `keepdc = false` default folding `$xor`/`$xnor` on identical `State::Sx` inputs; `mux_undef` collapsing `$mux`/`$pmux` with undef inputs/selectors.
  - `passes/techmap/abc.cc` (lines 32–35, 133, 390–395, 464–470, 1138–1147): default `ABC_COMMAND_{LIB,CTR,LUT,DFL}` containing `&fraig -x`, `scorr`, `dc2`, `dretime`, `dch -f`, `if`/`&nf`; `dff_mode` gating of FFs; `keepff` pinning; silent replacement of constant undef bits with constant zero.
  - `passes/techmap/abc9.cc` (lines 90–135): ABC9 FPGA mapping script orchestration.
  - `passes/equiv/equiv_make.cc` (lines 1–140), `equiv_simple.cc` (lines 1–120), `equiv_induct.cc` (lines 1–120), and `kernel/satgen.h` (lines 68–222): `$equiv` cell creation, `.fsm`/`.map` encfiles, `model_undef = false` default, base-case consistency check, and undef assumption on initial registers.
- `YosysHQ/eqy` @ `33015166c47398dff1ac72a699f4212891bb0618`:
  - `src/eqy_partition.cc` (lines 1–120): `EqyPartitionWorker` matching gold/gate signal drivers, `FfInitVals`, and partition grouping rules.
- `berkeley-abc/abc` @ `4f928c689ff6f1eedec245efc03897f4d2098bcf`:
  - `src/proof/cec/cecCec.c` (lines 1–120): `Cec_ManSimulateCombOutputs`, `Cec_ManPrintCexSummary` combinational miter checking.
  - `src/proof/pdr/pdrCore.c`: IC3/PDR incremental frame reachability and MIC domain generalization (`Pdr_ManGipSetMicDomain`).
  - `src/opt/ret/retCore.c` (lines 1–110): `Abc_NtkRetime` Modes 1–6 (forward, backward, min-area, min-delay, combined, Pan's l-value retiming).
- `IAIK/coco-alma` @ `95c80df5d6d704bf525f47ef6e58e98e27fedf97`:
  - `readme.md` (lines 1–100): Yosys-based `parse.py` netlist extraction workflow and FMCAD 2021 / USENIX Security 2021 citations.
  - `SatChecker.py` (lines 1–110): `Formula` maintaining `node_vars_stable`, `node_vars_trans`, and `node_vars_diff` SAT encodings.
  - `examples/gadgets/design/dom_and.v`: 1st-, 2nd-, and 3rd-order `DOM-AND` Verilog implementations showing barrier registers (`AX_BY_Z0_q`, etc.) isolating cross-domain products before final XOR.
- `parallaxsw/OpenSTA` @ `cc510896e8e097771100d7dec4f5cbfdb3d6d71a`:
  - `search/PathEnd.cc` (lines 705–760): `PathEndClkConstrained::requiredTime`, `requiredTimeNoCrpr`, and `slack` sign definitions for `TimingRole::setup()` vs. hold.
  - `search/Crpr.cc` (lines 53–105): `CheckCrpr::maxCrpr` and `checkCrpr` common-pin clock reconvergence pessimism removal.
- `The-OpenROAD-Project/OpenROAD` @ `4d08cb17e317284548659fd7040238db3206d940`:
  - `README.md` (lines 1–55): end-to-end RTL-to-GDSII physical design flow architecture integrating synthesis, PnR, and OpenSTA.

### Peer-Reviewed Primary Literature
- Lööw, A., Kumar, R., Tan, Y. K., Myreen, M. O., Norrish, M., Abrahamsson, O., & Fox, A. (2019). *Verified Compilation on a Verified Processor*. PLDI 2019. DOI `10.1145/3314221.3314622`.
- Lööw, A. (2021). *Lutsig: A Verified Verilog Compiler for Verified Circuit Development*. CPP 2021. DOI `10.1145/3437992.3439916`. (Full PDF text inspected via `https://cakeml.org/cpp21.pdf`.)
- Smith, G. H., Kushigian, B., Canumalla, V., Cheung, A., Lyubomirsky, S., Porncharoenwase, S., Just, R., Bernstein, G. L., & Tatlock, Z. (2024). *FPGA Technology Mapping Using Sketch-Guided Program Synthesis*. ASPLOS 2024. DOI `10.1145/3620665.3640387`, `arXiv:2401.16526`. (Full PDF text inspected.)
- Cassiers, G., & Standaert, F.-X. (2020). *Trivially and Efficiently Composing Masked Gadgets with Probe Isolating Non-Interference*. IEEE Transactions on Information Forensics and Security (TIFS), DOI `10.1109/TIFS.2020.2971153`.
- Gross, H., Mangard, S., & Korak, T. (2016). *Domain-Oriented Masking: Compact Masked Hardware Implementations with Arbitrary Protection Order*. CCS 2016 (TIS workshop).
- Yang, K., Hicks, M., Dong, Q., Austin, T., & Sylvester, D. (2016). *A2: Analog Malicious Hardware*. IEEE Symposium on Security and Privacy (S&P 2016), pp. 18–37. DOI `10.1109/SP.2016.10`.

### Reproducible Executable Micro-Probe (`probe_synthesis_hazards.py`)
Self-contained Python 3 probe (no third-party dependencies) reproducing Probes 1–4 above:

```python
#!/usr/bin/env python3
import itertools, math
from collections import Counter, defaultdict

def v_xor(a, b): return 'X' if (a == 'X' or b == 'X') else (a ^ b)
def v_mux(s, a, b): return a if s == 0 else (b if s == 1 else (a if a == b else 'X'))

# Probe 1: 4-state RTL vs Yosys opt_expr (!keepdc / -mux_undef)
assert [(x, v_xor(x, x), 0) for x in (0, 1, 'X') if v_xor(x, x) != 0] == [('X', 'X', 0)]
assert [(s, a, v_mux(s, a, 'X'), a) for s in (0, 1) for a in (0, 1) if v_mux(s, a, 'X') != a] == [
    (1, 0, 'X', 0), (1, 1, 'X', 1)
]

# Probe 2: Backward retiming SEC base-case check (AND vs NAND)
def check_sec(ra0, rb0, ry0, op):
    inv = lambda ra, rb, ry: ry == op(ra, rb)
    base = inv(ra0, rb0, ry0) and (op(ra0, rb0) == ry0)
    cex = [t for t in itertools.product((0, 1), repeat=5)
           if inv(t[0], t[1], t[2]) and (not inv(t[3], t[4], op(t[3], t[4])) or op(t[0], t[1]) != t[2])]
    return base, len(cex)

assert check_sec(0, 0, 0, lambda u, v: u & v) == (True, 0)
assert check_sec(0, 0, 0, lambda u, v: 1 - (u & v)) == (False, 0)
assert check_sec(0, 0, 1, lambda u, v: 1 - (u & v)) == (True, 0)

# Probe 3: DOM-AND 1st-order glitch-extended probing mutual information
def mi_bits(counts):
    tot = sum(counts.values())
    px, py = defaultdict(float), defaultdict(float)
    for (x, y), c in counts.items(): px[x] += c/tot; py[y] += c/tot
    return sum((c/tot)*math.log2((c/tot)/(px[x]*py[y])) for (x, y), c in counts.items())

c_intact, c_retimed = Counter(), Counter()
for x, y, x0, y0, z in itertools.product((0, 1), repeat=5):
    y1 = y ^ y0
    reg_q = (x0 & y1) ^ z
    c_intact[((x, y), (x0, y0, reg_q))] += 1
    c_retimed[((x, y), (x0, y0, y1, z))] += 1
assert abs(mi_bits(c_intact) - 0.0) < 1e-12
assert abs(mi_bits(c_retimed) - 1.0) < 1e-12

# Probe 4: OpenSTA setup/hold slack + CRPR
crpr = 300.0 * (1.10 - 0.90)  # 60.0 ps
arr_h = 300.0*0.90 + 80.0*0.90 + 45.0 + 25.0  # 412.0 ps
req_h_nocrpr = 300.0*1.10 + 90.0*1.10 + 35.0  # 464.0 ps
assert (arr_h - req_h_nocrpr) == -52.0 and (arr_h - (req_h_nocrpr - crpr)) == 8.0
print("ALL SYNTHESIS/EQUIVALENCE/DOM/STA PROBES PASSED")
```

## Revalidation

1. **Check upstream Yosys/ABC/EQY defaults against a newer commit:** Diff `passes/opt/opt_expr.cc` (specifically `OptExprConfig::keepdc` and `mux_undef` handling), `passes/techmap/abc.cc` (`ABC_COMMAND_*`, `prepare_cell` `dff_mode`/`keepff`, and `undef_bits_lost`), and `kernel/satgen.h` (`model_undef` default). If Yosys changes default `-keepdc` or adds native 4-state `X`-preserving ABC passes, re-evaluate Section 5.1.
2. **Check Lutsig / Lakeroad TCB boundaries:** Inspect `CakeML/hardware` `compiler/compileScript.sml` (`compile_glue_thm`) and `README.md` to determine whether PnR/bitstream verification or `ag32` compatibility has been updated at a newer commit, and inspect `uwsampl/lakeroad` `racket/synthesize.rkt` and `racket/sketches.rkt` to check whether unbounded sequential induction or proof-producing SMT checking has been added.
3. **Check masking preservation in any concrete synthesis flow:** Run `python3 parse.py` and `verify.py` from `IAIK/coco-alma` on the **post-synthesis and post-PnR** flattened gate netlist of a `DOM`/`PINI` gadget (such as `examples/gadgets/design/dom_and.v`) with and without `(* keep = 1 *)` and `-dff`/`dretime`; confirm zero transient leaks (`node_vars_trans`).
4. **Rerun the mathematical micro-probe:** Execute the inline Python snippet above (`python3 probe_synthesis_hazards.py`); it completes in `<50 ms` and deterministically checks all four invariants (`1'bX` divergence, retiming reset failure, DOM glitch mutual information jump from `0.0` to `1.0` bit, and OpenSTA hold/CRPR slack arithmetic).
5. **Revalidate post-PnR sign-off discipline:** For any real tapeout or FPGA deployment, verify that (a) `SEC`/`CEC` is re-run against the post-PnR netlist after buffer insertion and gate resizing, (b) `OpenSTA` reports non-negative setup and hold slack across all PVT corners with CRPR enabled, and (c) foundry trust assumptions explicitly account for out-of-band analog fabrication threats (`A2`) not covered by digital verification.
