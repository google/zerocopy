# Glitch-Resistant Hardware Masking: Threshold Implementations, Domain-Oriented Masking, PINI/HPC Gadgets, Gate-Level Verifiers, and Dual-Rail Precharge Logic

## Summary

Idealized $d$-probing circuits such as Ishai–Sahai–Wagner (ISW) Boolean multipliers fail at first order in real CMOS silicon because **combinational glitches**, **state-register transitions**, and **capacitive wire coupling** allow a single physical observation to depend jointly on all signals in a combinational fan-in cone or across adjacent clock cycles. Direct enumeration of an unregistered first-order ISW AND gadget confirms that while the stable output carries $I((a,b); c_1) = 0.000000\text{ bits}$, a single glitch-extended probe on $c_1$ observes the entire 5-wire fan-in cone $(a_0, a_1, b_0, b_1, r)$ with $I = 2.000000\text{ bits}$, and skewed input arrival before a late fresh mask creates a direct first-order mean bias ($\mathbb{E}[v_3] = 0.25$ for $a \cdot b = 0$ versus $0.75$ for $a \cdot b = 1$) plus toggle-count mutual information $I = 0.226948\text{ bits}$.

Four hardware countermeasure families address these physical defaults with sharply different share counts, randomness budgets, composability rules, and verification requirements:

1. **Threshold Implementations (TI)** eliminate single-stage glitch leakage without fresh randomness by splitting degree-$t$ nonlinear functions into $s \ge td + 1$ shares satisfying **correctness**, **$d$-th order non-completeness**, and **uniformity**. However, non-completeness alone does not compose across registered stages: exact enumeration of a canonical 3-share non-complete AND shows non-uniform output distributions ($7/16$ for $(0,0,0)$ versus $3/16$ for weight-2 tuples when $x \cdot y = 0$), leaking $I((x,y); (z_1, z_2)) = 0.039699\text{ bits}$ into a cascaded second stage unless fresh remasking or $s \ge 4$ uniform sharings are used.
2. **Domain-Oriented Masking (DOM)** restores the optimal $n = d + 1$ share count by isolating shares into $d + 1$ domains and inserting synchronization registers after XORing cross-domain terms with $d(d+1)/2$ fresh random bits. DOM satisfies **robust Non-Interference (NI)**—not Strong NI (SNI) or Probe-Isolating NI (PINI). Composing `DOM(x, x)` without an intervening refresh leaks $I(x; \mathcal{O}_{\text{glitch}}(t_{0,d})) = 1.000000\text{ bit}$, and omitting optional inner-domain pipeline registers (`Pipeline = 0` in OpenTitan `prim_dom_and_2share.sv`) introduces cross-cycle mask cancellation ($I = 0.204434\text{ bits}$) if inputs change before cross-domain registers update.
3. **Probe-Isolating Non-Interference (PINI) and Hardware Private Circuits (`HPC1` / `HPC2`)** enforce domain isolation *per probe* so arbitrary gadget compositions—including shared-input self-composition `HPC2(x, x)` without external refresh—remain glitch-robustly secure at arbitrary order $d$. `HPC2` matches DOM's optimal $d(d+1)/2$ randomness per multiplication while shifting to asymmetric input latencies ($1$ and $0$ cycles, output at $2$ cycles) using register-decoupled terms $u_{ij} = \overline{a_i} \cdot r_{ij}$, $v_{ij} = b_j \oplus r_{ij}$, and $w_{ij} = a_i \cdot \mathrm{Reg}(v_{ij})$.
4. **Dual-Rail Precharge Logic (`SABL`, `WDDL`)** attempts signal-independent switching energy via precharge-evaluate cycles rather than secret sharing, but is broken by **Early Propagation Effects (EPE)**—leaking $I(a; t_{\text{switch}}) = 1.000000\text{ bit}$ on a standard WDDL AND even at zero routing capacitance mismatch—and by differential backend routing asymmetries ($\Delta C / C = 5\%$ directly yields $\Delta E / E = 5\%$).

Gate-level verification spans three distinct soundness-scalability points: **SILVER** (exact Sylvan ROBDD statistical independence across `Probing`, `NI`, `SNI`, `PINI`, and `Uniformity` on constrained small gadgets), **REBECCA** (Z3 Fourier correlation-set over-approximation that handles moderate netlists with zero false negatives but potential false positives), **fullVerif** (Yosys + Icarus Verilog control-trace compositional PINI/Affine dataflow checking over full ciphers given pre-verified atomic gadgets), and **PROLEAD** (bit-sliced Monte Carlo $G$-test simulation scaling to full hardware netlists under glitch, transition, relaxed-enabler, and combined fault models, bounded by statistical power rather than exhaustive formal proof). Across every scheme, **RTL synthesis tools silently destroy glitch resistance** by reordering XOR/AND trees, merging registers, or collapsing redundant domains unless explicit synthesis barriers (`keep`, `preserve`, `dont_touch`, `prim_xor2`/`prim_flop_en`) are enforced and verified on the post-synthesis netlist.

## Applicability

This report characterizes gate-level hardware masking schemes, dual-rail precharge logic styles, and automated netlist-level probing verifiers targeting synchronous CMOS ASIC and FPGA implementations. Its findings apply to the combination and comparative evaluation of the durable primary subjects recorded in `REPORT.json`:

- **Masking gadget and RTL implementations**: `hgrosz/aes-dom` (`b34d018349e5f10805a03c3c46c5ad65d3127196`, arbitrary-order VHDL DOM-indep and DOM-dep multipliers), `cassiersg/fullverif` (`227f31215d8269c3b78bb0ebaebf6a1db6bc198e`, parameterized Verilog `MSKand_DOM`, `MSKand_HPC1`, `MSKand_HPC2`, `MSKref`), and `lowRISC/opentitan` (`1e061997389b1c257043b0dbd2388a19a6c2f6f1`, production 2-share `prim_dom_and_2share.sv`, `aes_sbox_dom.sv`, `aes_sbox.sv`).
- **Automated netlist verification frameworks**: `ChairImpSec/PROLEAD` (`2c8c8486d84f58b121b7198fc267ce520d29d39a`, simulation-based robust/relaxed probing and FIESTA fault analysis), `Chair-for-Security-Engineering/SILVER` (`0a3c85fc5a60d76eedb84d996473df28fc18ef42`, exact Sylvan ROBDD verifier), `IAIK/REBECCA` (`09c93f8994ca09352e967221c4c407d060e8ea99`, Z3 Fourier correlation-set verifier), and `cassiersg/fullverif` (`227f31215d8269c3b78bb0ebaebf6a1db6bc198e`, Rust compositional verifier).
- **Normative formal models and logic-style specifications**: ISW $d$-probing (CRYPTO 2003), Robust Probing Model $(g,t,c)$ (Faust et al., TCHES 2018), TI (Nikova et al., ICISC 2006; Bilgin et al., ASIACRYPT 2014; Reparaz et al., CRYPTO 2015), DOM (Gross et al., ACM TIS 2016), SNI (Barthe et al., CCS 2016), PINI and HPC1/HPC2 (Cassiers and Standaert, IEEE TIFS 2020; Cassiers et al., IEEE TC 2021), and SABL/WDDL/EPE analyses (Tiri et al., ESSCIRC 2002, DATE 2004, CARDIS 2004; Suzuki and Saeki, CHES 2006).

**Notation warning across upstream codebases:** Academic masking papers typically denote the **protection order** by $d$ and the number of Boolean shares by $n = d + 1$ (e.g., first-order masking has $d = 1, n = 2$). By contrast, `cassiersg/fullverif`'s Verilog modules (`MSKand_DOM.v`, `MSKand_HPC1.v`, `MSKand_HPC2.v`, `MSKref.v`) use parameter `d` for the **number of shares** (`parameter d=2` for first-order masking, with `n_rnd = d*(d-1)/2`). In `hgrosz/aes-dom`, the generic is named `SHARES` (`NUM_MASKS := SHARES*(SHARES-1)/2`). Throughout this report, $d$ denotes the **security / probing order** and $n$ denotes the **share count** ($n = d + 1$ for DOM/HPC, $n \ge td + 1$ for standard TI), with code-specific parameter names explicitly disambiguated whenever source modules are quoted.

**Scope boundaries:** Findings in this report address gate-level cryptographic hardware circuits and netlist verifiers. CPU-wide software-on-hardware co-verification (masked RISC-V assembly running on Ibex or OTBN pipelines) and analog power-delivery equalizers are outside this report's primary scope and treated separately.

## Findings

### 1. Why CMOS Physical Defaults Break Ideal $d$-Probing Circuits at First Order

`Basis: normative + derived + execution`

In the original Ishai–Sahai–Wagner (ISW, CRYPTO 2003, DOI `10.1007/978-3-540-45146-4_27`) $d$-probing model, an adversary places up to $d$ noiseless probes on wires of a Boolean circuit and observes only the final steady-state Boolean value of each wire per clock cycle. Under this idealized model, an unregistered first-order ($d = 1, n = 2$) ISW AND gate over input sharings $(a_0, a_1)$ with $a_0 \oplus a_1 = a$, $(b_0, b_1)$ with $b_0 \oplus b_1 = b$, and fresh uniform mask $r \in \mathbb{F}_2$:

$$c_0 = (a_0 \cdot b_0) \oplus r, \qquad c_1 = \big(((a_0 \cdot b_1) \oplus r) \oplus (a_1 \cdot b_0)\big) \oplus (a_1 \cdot b_1)$$

is provably $1$-probing secure because every individual intermediate wire is statistically independent of $(a, b)$.

In physical static CMOS circuits, Mangard, Pramstaller, and Oswald (CHES 2005, DOI `10.1007/11545262_12`) demonstrated that masked hardware S-boxes leak at first order, and Faust, Grosso, Merino Del Pozo, Paglialonga, and Standaert (TCHES 2018, DOI `10.13154/tches.v2018.i3.89-120`) formalized the three physical defaults as the **$(g, t, c)$-robust probing model**:

1. **Glitches ($g$ — combinational propagation):** Because standard-cell propagation delays and interconnect RC delays vary across paths, a combinational gate evaluates repeatedly on intermediate, non-simultaneous combinations of its input arrivals within a single clock period. A **$g$-extended probe** on wire $w$ conservatively reveals **all primary inputs and synchronization-register outputs in the combinational fan-in cone** $\mathrm{Cone}_{\text{comb}}(w)$ (halting only at clocked flip-flops).
2. **Transitions ($t$ — temporal state recombination):** Dynamic CMOS switching energy is proportional to the Hamming distance $\mathrm{HD}(v^{(k-1)}, v^{(k)}) = \mathrm{HW}(v^{(k-1)} \oplus v^{(k)})$ between consecutive stable states of a register or bus wire. A **$t$-extended probe** on wire $w$ at cycle $k$ reveals the pair $(w^{(k-1)}, w^{(k)})$. If a single register or datapath wire holds share $x_0$ in cycle $k-1$ and share $x_1$ in cycle $k$, then $w^{(k-1)} \oplus w^{(k)} = x_0 \oplus x_1 = x$ leaks the unmasked secret at first order.
3. **Coupling ($c$ — capacitive crosstalk and substrate/routing coupling):** Adjacent metal wires experience mutual capacitance $C_c$ (Miller effect): switching wire $w_1$ alters the effective load capacitance and transient current of neighboring wire $w_2$ depending on whether they switch in the same or opposite directions. A **$c$-extended probe** reveals a neighborhood of physically adjacent wires, breaking separation even across non-interacting logic cones unless placement/shielding or multi-cycle isolation enforces physical distance.

#### Concrete First-Order Breakdown of Unregistered ISW AND

Exhaustive enumeration over all $2^5 = 32$ uniform input/mask states $(a_0, a_1, b_0, b_1, r) \in \mathbb{F}_2^5$ (Sub-probe 1A in **Evidence**) quantifies the exact collapse:

| Observation Model on Unregistered ISW $c_1$ | Observed Function / Cone | Mutual Information $I((a,b); \mathcal{O})$ | Security Verdict |
| :--- | :--- | :---: | :---: |
| Ideal stable $1$-probe (`ISW`) | $c_1$ (steady state) | `0.000000` bits | PASS (ideal only) |
| Glitch-extended $1$-probe ($g$-robust) | $(a_0, a_1, b_0, b_1, r)$ | `2.000000` bits | **FAIL (full secret recovery)** |
| Physical skewed arrival (late mask $r$, intermediate $v_3$) | $v_3 = (a_0 b_1) \oplus (a_1 b_0) \oplus (a_1 b_1) = (a \cdot b) \oplus (a_0 b_0)$ | $\mathbb{E}[v_3] = 0.25$ ($ab=0$) vs. $0.75$ ($ab=1$) | **FAIL (0.50 first-order mean bias)** |
| Physical skewed arrival (total cycle toggle count) | $\sum_{j} \mathbf{1}[s_j \neq s_{j+1}]$ | `0.226948` bits (mean uniform `1.25`, variance leaks) | **FAIL (distribution & variance leak)** |

Notice the algebraic root cause of the transient mean bias: before the late fresh mask $r$ arrives, the intermediate node $v_3 = (a_0 b_1) \oplus (a_1 b_0) \oplus (a_1 b_1)$ equals $(a \cdot b) \oplus (a_0 \cdot b_0)$. Because $a_0 \cdot b_0$ is biased ($\Pr[a_0 b_0 = 1] = 1/4$ rather than $1/2$), $v_3$ directly leaks $a \cdot b$ in the **first-order mean** ($\Delta \mathbb{E}[v_3] = +0.50$) during the glitch window.

---

### 2. Threshold Implementations (TI): Non-Completeness, Uniformity, and Higher-Order Scaling

`Basis: normative + derived + execution`

Nikova, Rechberger, and Rijmen (ICISC 2006, DOI `10.1007/11935308_38`) introduced **Threshold Implementations (TI)** to achieve provable first-order glitch resistance using secret sharing and combinational component isolation, *without* requiring fresh randomness inside single nonlinear stages. Given a Boolean function $z = f(x, y)$ of algebraic degree $t$, a TI splits each input into $s_{\text{in}}$ shares and constructs $s_{\text{out}}$ component functions $f_0, \dots, f_{s_{\text{out}}-1}$ separated by synchronization registers after each nonlinear layer, satisfying three axioms:

1. **Correctness:** $\bigoplus_{i=0}^{s_{\text{out}}-1} f_i(\mathbf{x}, \mathbf{y}) = f\big(\bigoplus_j x_j, \bigoplus_j y_j\big)$.
2. **$d$-th Order Non-Completeness:** Every combination of up to $d$ component functions $\{f_{i_1}, \dots, f_{i_d}\}$ is syntactically independent of at least one input share index $k \in \{0, \dots, s_{\text{in}}-1\}$ of every secret input variable. Consequently, even arbitrary glitches inside those $d$ component circuits cannot depend on all shares of any secret, guaranteeing statistical independence under $d$ glitch-extended probes *provided the input sharing is uniform*.
3. **Uniformity:** For every secret input tuple, when input sharings are drawn uniformly at random conditioned on the secret, the output sharing $(f_0, \dots, f_{s_{\text{out}}-1})$ must also be uniformly distributed over all valid sharings of the output value.

#### Share Count Lower Bound and Higher-Order Multivariate Pitfall

To represent a degree-$t$ monomial $x^{(1)} \cdots x^{(t)}$ such that any $d$ output shares omit at least one share index of every variable, Bilgin, Gierlichs, Nikova, Nikov, and Rijmen (ASIACRYPT 2014, DOI `10.1007/978-3-662-45611-5_19`) proved the minimum input-share bound for direct non-complete TI:

$$s_{\text{in}} \ge t \cdot d + 1, \qquad s_{\text{out}} \ge \binom{s_{\text{in}}}{t} \text{ (uncompressed) or } s_{\text{in}} \text{ (compressed where valid)}.$$

For quadratic ($t = 2$) Boolean multiplication (`AND` / Keccak $\chi$ / tower-field AES inversion):
- At $d = 1$: $s_{\text{in}} \ge 3$ shares.
- At $d = 2$: $s_{\text{in}} \ge 5$ shares.
- Critically, Reparaz, Bilgin, Nikova, Gierlichs, and Verbauwhede (CRYPTO 2015, DOI `10.1007/978-3-662-47989-6_37`) showed that higher-order TI ($d \ge 2$) still leaks against **multivariate glitch probes across consecutive register stages** unless fresh remasking registers separate nonlinear layers, leading to the consolidated $(d+1)$-share registered architecture (which directly bridges TI to DOM and HPC).

#### Exact Execution Witness of TI Uniformity Failure Under Composition

Consider the textbook 3-share ($s = 3, t = 2, d = 1$) non-complete TI of $z = x \cdot y$:

$$z_0 = x_1 y_1 \oplus x_1 y_2 \oplus x_2 y_1, \quad z_1 = x_2 y_2 \oplus x_2 y_0 \oplus x_0 y_2, \quad z_2 = x_0 y_0 \oplus x_0 y_1 \oplus x_1 y_0.$$

Direct enumeration over all $2^6 = 64$ input share assignments (Sub-probe 1B in **Evidence**) proves both why stage 1 passes and why un-remasked stage 2 fails:
- **Stage 1 correctness:** `100%` ($z_0 \oplus z_1 \oplus z_2 = x \cdot y$).
- **Stage 1 non-completeness (glitch-robust):** The combinational cone of $z_0$ sees $(x_1, x_2, y_1, y_2)$ (omitting share index $0$), giving $I((x, y); (x_1, x_2, y_1, y_2)) = 0.000000\text{ bits}$.
- **Output uniformity VIOLATION:** A uniform 3-share encoding of a bit $z \in \{0, 1\}$ must assign probability $4/16 = 0.25$ to each of the 4 valid tuples. Instead, exact counts yield:
  - When $x \cdot y = 0$ (each of $(0,0), (0,1), (1,0)$): $(0,0,0)$ occurs with probability **`7/16`** (`0.4375`), while $(0,1,1), (1,0,1), (1,1,0)$ each occur with probability **`3/16`** (`0.1875`).
  - When $x \cdot y = 1$ ($(1,1)$): $(0,0,1), (0,1,0), (1,0,0)$ each occur with probability **`5/16`** (`0.3125`), while $(1,1,1)$ occurs with probability **`1/16`** (`0.0625`).
- **Stage 2 cascade breach:** Feeding the registered non-uniform sharing $(z_0, z_1, z_2)$ directly into a second non-complete TI stage $w = z \cdot u$ exposes $(z_1, z_2)$ to a single glitch probe on $w_0$, yielding **`I((x, y); (z1, z2)) = 0.039699 bits`** (first-order side-channel leakage!). Inserting 2 bits of fresh remasking $(r_0, r_1)$ via $(z_0 \oplus r_0, z_1 \oplus r_1, z_2 \oplus r_0 \oplus r_1)$ restores exact uniformity and drops stage-2 mutual information to `0.000000` bits.

---

### 3. Domain-Oriented Masking (DOM): Architecture, Variants, and Compositional Boundaries

`Basis: normative + source + execution`

Gross, Mangard, and Korak (ACM CCS TIS 2016, DOI `10.1145/2996366.2996426`; ePrint `2016/486`) introduced **Domain-Oriented Masking (DOM)**, reducing the share count from TI's $td + 1$ down to the information-theoretic minimum $n = d + 1$ shares for any security order $d \ge 1$. Each share index $i \in \{0, \dots, d\}$ defines a **share domain**. Linear gates operate strictly within each domain; nonlinear multiplication creates $n^2$ partial products $a_i b_j$, split into:
- **Inner-domain terms** ($i = j$): $a_i b_i$ stays inside domain $i$ without fresh randomness.
- **Cross-domain terms** ($i \neq j$): each unordered pair $\{i, j\}$ ($i < j$) shares one fresh uniform random bit $z_{ij}$ (total $d(d+1)/2 = n(n-1)/2$ random bits per bit-level multiplier) to mask both $a_i b_j \oplus z_{ij}$ and $a_j b_i \oplus z_{ij}$. **Mandatory synchronization registers** latch the masked cross-domain terms *before* they are XOR-integrated with inner-domain terms into output share $q_i$:

$$q_i = \mathrm{Reg}_{\text{opt}}(a_i b_i) \oplus \bigoplus_{j \neq i} \mathrm{Reg}(a_i b_j \oplus z_{\min(i,j),\max(i,j)}).$$

#### Primary-Source Inspection Across Three DOM Implementations

1. **`cassiersg/fullverif` (`lib_v/MSKand_DOM.v:1–35`)**:
   - Annotated at line 1 with `(* fv_prop = "NI", fv_strat = "assumed", fv_order=d *)` (where `d` is the share count $n$).
   - Registers **every** term (`rfrsh_reg[j] <= mult_wire ^ rnd_mat[i][j]` for all $j \in [0, n-1]$, with `rnd_mat[i][i] = 0`, lines 16 and 27–31), then reduces `assign out[i] = ^rfrsh_reg;` (line 25). Latency: $1$ clock cycle; randomness: $n(n-1)/2$ bits.
2. **`hgrosz/aes-dom` (`real_dom_shared_mul_gf2.vhdl:50–267`) — `DOM-dep` vs. `DOM-indep`**:
   - Standard **`DOM-indep`** (`shared_mul_gf2.vhdl`) requires inputs $X$ and $Y$ to be **independently shared**. In composite-field AES S-boxes (e.g., computing $x^2 \cdot x$ or $x \cdot y$ where $x$ and $y$ share common ancestor masks), inputs are *dependent*.
   - **`DOM-dep`** (`real_dom_shared_mul_gf2.vhdl`) handles dependent inputs by blinding $Y$ with a fresh $n$-share blinding vector $B$: computing $X \cdot (Y \oplus B) \oplus X \cdot B$, where $Y \oplus B$ is safely unmasked after a register stage (`BlindedYxDP`, lines 187–200) and $X \cdot B$ is computed via `DOM-indep` (`shared_mul_gf2`, lines 214–224). For $n = 2$ (`FIRST_ORDER_OPTIMIZATION = "yes"`, lines 105–172), a single blinding share `BxDI(0)` plus `ZxDI(0)` reduces multiplier area from 4 to 3 $\mathrm{GF}(2^2)$ multipliers per share.
3. **`lowRISC/opentitan` (`hw/ip/prim/rtl/prim_dom_and_2share.sv:28–173` and `hw/ip/aes/rtl/aes_sbox_dom.sv:1–160`)**:
   - Production 2-share `prim_dom_and_2share` explicitly exposes `parameter bit Pipeline = 1'b0` (line 30). When `Pipeline == 1'b1` (lines 93–112), inner-domain products `t_a0b0_d` and `t_a1b1_d` are registered (`u_prim_flop_tab01`) alongside cross-domain terms (`u_prim_flop_t01`). When `Pipeline == 1'b0` (lines 113–121), inner-domain registers are omitted, and the RTL source explicitly documents the hazard: *"this can cause SCA leakage as during the clock cycle in which new data arrives, the new inner-domain terms are integrated with the previous, reshared cross-domain terms."*
   - **Execution verification of the `Pipeline = 0` hazard (Sub-probe 1A):** If domain-0 inputs switch before `t0_q` updates so that `q0` transitions from $(a_0 b_0) \oplus t_{0,q}$ to $(a_1 b_1) \oplus t_{0,q}$, the XOR transition cancels $t_{0,q}$ (and therefore the fresh mask $z$!) completely, yielding **`I((a,b); (q0_old, q0_new)) = 0.204434 bits`**. OpenTitan therefore sets `.Pipeline(1)` in `keccak_2share.sv:243` and enforces a formal SVA `StableTwoCycles_M` assumption (`prim_dom_and_2share.sv:162–166`) whenever `Pipeline == 0`.
   - OpenTitan's `aes_sbox_dom.sv` (default `SecSBoxImpl = SBoxImplDom`) uses 5-cycle unpipelined DOM-dep stages consuming **28 bits of PRD per S-box evaluation** (`prd_1[7:0], prd_2[3:0], prd_3[7:0], prd_4[7:0]`, lines 45–50), increasing full AES-128/192/256 block latency from `12/14/16` cycles (combinational Canright) to `56/66/72` cycles (`hw/ip/aes/doc/theory_of_operation.md:313`). It explicitly deprecates the combinational masked Canright S-boxes (`SBoxImplCanrightMasked`, `SBoxImplCanrightMaskedNoreuse`) due to glitch-induced correlation-enhanced collision leakage (lines 316–318).

#### Exact Compositional Failure of DOM: Why NI Is Insufficient

Both `Chair-for-Security-Engineering/SILVER` (`README.md:38–46` on `test/dom/dom1.nl`) and our Sub-probe 1A establish the exact security hierarchy of first-order DOM-indep:
- `probing.standard (d <= 1)`: **PASS**; `probing.robust (d <= 1)`: **PASS**
- `NI.standard (d <= 1)`: **PASS**; `NI.robust (d <= 1)`: **PASS**
- `SNI.standard (d <= 1)`: **PASS**; **`SNI.robust (d <= 1)`: FAIL** (output probe `<out:line18>` extends across register boundary or internal share interaction)
- **`PINI.standard (d <= 1)`: FAIL** (`<and:line6>`); **`PINI.robust (d <= 1)`: FAIL** (`<reg:line14>`)

**Concrete failure witness (Sub-probe 1A):** Wiring the same input sharing $(x_0, x_1)$ to both inputs of `DOM-indep` (i.e., `DOM(x, x)` without an intervening SNI refresh) exposes $(x_0, x_1, r)$ inside the combinational fan-in cone of `t0_d = (a0 & b1) ^ r`, yielding **`I(x; cone(t0_d)) = 1.000000 bit`** under a single glitch-extended probe—even though `DOM-indep` passes `NI.robust` on independent inputs (`0.000000` bits across all 5 cones). Because NI only bounds the *cardinality* of required input shares ($|I| \le t$ for $t$ probes) without constraining *which share indices* are touched, two inputs sharing the same secret allow a single probe on `t0_d` to touch index `0` of input `a` and index `1` of input `b`, reconstructing $x_0 \oplus x_1 = x$.

---

### 4. Composable Hardware Masking: NI, SNI, PINI, and Hardware Private Circuits (`HPC1` / `HPC2`)

`Basis: normative + source + execution`

To compose large circuits (full AES, Keccak, Ascon, PRESENT) without monolithic exponential verification, Barthe et al. (ACM CCS 2016, DOI `10.1145/2976749.2978427`) introduced **Non-Interference (NI)** and **Strong Non-Interference (SNI)**, and Cassiers and Standaert (IEEE TIFS 2020, DOI `10.1109/TIFS.2020.2971153`) introduced **Probe-Isolating Non-Interference (PINI)**, instantiated in silicon as **Hardware Private Circuits (`HPC1`, `HPC2`)** by Cassiers, Grégoire, Levi, and Standaert (IEEE TC 2021, DOI `10.1109/TC.2020.3022979`; ePrint `2020/185`).

#### Formal Definitions (in the Glitch-Extended $d$-Probing Model)

Let a gadget $G$ take $k$ shared inputs $\mathbf{x}^{(1)}, \dots, \mathbf{x}^{(k)}$ (each with share indices $i \in \{0, \dots, d\}$) and produce shared output $\mathbf{y}$. Let an adversary place $t_1$ internal glitch-extended probes and $t_2$ output probes with $t_1 + t_2 \le d$, where the output probes target share indices $O \subseteq \{0, \dots, d\}$ ($|O| = t_2$).

- **$d$-NI (Non-Interference):** The joint distribution of all $t_1 + t_2$ probes can be perfectly simulated using at most $t_1 + t_2$ shares of each input variable. *(Not trivially composable: shared fan-out requires ad-hoc SNI refreshes.)*
- **$d$-SNI (Strong Non-Interference):** The joint distribution of all $t_1 + t_2$ probes can be simulated using at most $t_1$ shares of each input variable—*independent of the number of output probes $t_2$*. *(Composable, but even linear gadgets like XOR are not SNI without costly refresh insertions.)*
- **$d$-PINI (Probe-Isolating Non-Interference):** There exists a set of share indices $A \subseteq \{0, \dots, d\}$ with $|A| \le t_1$ such that all $t_1 + t_2$ probes can be simulated using **only input share indices in $A \cup O$** (the *same* index set across every input variable!).

**Trivial Composition Theorem (Cassiers & Standaert, IEEE TIFS 2020):** Every share-wise linear/affine gadget (`XOR`, `NOT`, `Reg`, `Mux` with public select) is trivially $d$-PINI (with $A = \emptyset$ for outputs and $|A| \le 1$ per internal wire), and **any arbitrary acyclic or cyclic composition of $d$-PINI gadgets is automatically $d$-PINI** (and therefore $d$-probing secure in the glitch-extended model) with **zero refresh insertions required**. This is literally the 10-line theorem implemented in `cassiersg/fullverif/fullverif-check/src/comp_prop.rs:23–32`: verifying a composite module claims `PINI` reduces to verifying that its dataflow graph obeys domain/latency/randomness independence (`tg_graph.rs`) and every subgadget satisfies `kind.is_pini()`.

#### `HPC1` vs. `HPC2` RTL Mechanics (`cassiersg/fullverif/lib_v/`)

1. **`HPC1` (`MSKand_HPC1.v:1–37`, `MSKand_HPC1.vh:1–3`, `MSKref.v:1–133`):**
   - Composes an SNI mask-refresh gadget `MSKref` on `inb` (`inb_ref`) feeding a `MSKand_DOM` multiplier (`ina`, `inb_ref`), delaying `rnd_mul` by 3 register stages (`delay_mat_rnd`, lines 22–32) to align with `MSKref`.
   - Total randomness: `ref_n_rnd + n*(n-1)/2` bits (where `MSKref.v` uses $1$ random bit at $n=2$, $2$ at $n=3$, $n$ at $n \in \{4,5\}$, and structured multi-stage ring/cross refreshes up to $n = 16$).
   - Asymmetric latency: `inb` latency $= 2$, `ina` latency $= 3$, `out` latency $= 4$ (difference of 1 cycle between `inb` and `ina`, plus 1 cycle DOM multiplier latency).
2. **`HPC2` (`MSKand_HPC2.v:1–57`, `MSKand_HPC2.vh:1–2`):**
   - Achieves $d$-PINI using **only $n(n-1)/2 = d(d+1)/2$ random bits**—matching DOM-indep with **zero extra refresh randomness**!
   - Key algebraic decomposition in `MSKand_HPC2.v:31–55` (for each output share $i$ and every $j \neq i$):
     ```verilog
     // Cycle 0 -> Cycle 1 registers:
     v[j2]    <= inb[j] ^ rnd_mat[i][j];          // blinds b_j in domain j with r_{ij}
     inb_prev <= inb;                             // delays b_i by 1 cycle
     rnd_prev <= rnd;                             // delays r_{ij} by 1 cycle
     // Cycle 1 -> Cycle 2 registers:
     aibi     <= ina[i] & inb_prev[i];            // pure domain i
     u[j2]    <= (~ina[i]) & rnd_mat_prev[i][j];  // depends only on domain i + r_{ij}
     w[j2]    <= ina[i] & v[j2];                  // a_i AND reg(b_j ^ r_{ij})!
     // Cycle 2 combinational integration:
     out[i]    = aibi ^ ^u ^ ^w;
     ```
   - **Correctness identity:** For $a_i = 0$, $u_{ij} \oplus w_{ij} = r_{ij} \oplus 0 = r_{ij}$; for $a_i = 1$, $u_{ij} \oplus w_{ij} = 0 \oplus (b_j \oplus r_{ij}) = b_j \oplus r_{ij}$. In both cases, $u_{ij} \oplus w_{ij} = (a_i \cdot b_j) \oplus r_{ij}$.
   - **Why `HPC2` is $d$-PINI whereas `DOM` is not:** Every wire in `v[j2]` sees only `(b_j, r_ij)` (domain $j$); every wire in `u[j2]` sees only `(a_i, r_ij)` (domain $i$); every wire in `w[j2]` sees `(a_i, Reg(b_j ^ r_ij))`, which is **uniformly masked by `r_ij` even if `a_i` is known** (and cannot glitch back to raw `b_j` because `v[j2]` is registered!). Therefore, **every internal glitch-extended probe touches at most ONE share domain**!
   - **Execution verification (Sub-probe 1A):** Exhaustive enumeration confirms `HPC2` correctness (`True`) and verifies self-composed **`HPC2(x, x)`** (identical input sharing fed to both ports with zero external refresh): **`max I(x; cone(w)) = 0.000000 bits` across all 10 combinational cones**—whereas `DOM(x, x)` leaks `1.000000 bit`!
   - **Latency caveat:** `HPC2` has asymmetric input latencies (`inb` at cycle `0`, `ina` at cycle `1`, `out` at cycle `2`; `MSKand_HPC2.v:6–10`). Feeding an `ina` signal one cycle early without balancing registers breaks correctness or exposes timing skew.

#### Comparative Matrix of Hardware Masking Schemes (Order $d$, Quadratic Gate $t=2$)

| Scheme | Shares $n$ | Fresh Random Bits / AND | Latency (Cycles) | Glitch-Robust Security Notion | Composes Without External Refresh? | Representative Pinned RTL |
| :--- | :---: | :---: | :---: | :--- | :---: | :--- |
| **Unregistered ISW** | $d+1$ | $d(d+1)/2$ | $0$ | **Broken at $d=1$** | No | N/A (software model only) |
| **TI (non-complete)** | $\ge 2d+1$ | $0$ (if uniform) | $1$ | $d$-probing (stage 1; $d \ge 2$ needs remask) | Only if uniform (fails for 3-share AND) | `Chair-for-Security-Engineering/SILVER` tests |
| **DOM-indep** | $d+1$ | $d(d+1)/2$ | $1$ | $d$-NI (fails SNI.robust & PINI) | No (fails on `DOM(x,x)` / dependent inputs) | `MSKand_DOM.v`, `prim_dom_and_2share.sv` |
| **DOM-dep** | $d+1$ | $d(d+1)/2 + (d+1)$ (opt: $+2$ at $d=1$) | $1$–$2$ | $d$-probing (dependent inputs) | Restricted (not PINI) | `real_dom_shared_mul_gf2.vhdl`, `aes_sbox_dom.sv` |
| **HPC1** | $d+1$ | $d(d+1)/2 + R_{\text{ref}}(d+1)$ | $2$ (asym: `inb` 2, `ina` 1) | **$d$-PINI** | **Yes (trivial)** | `MSKand_HPC1.v` |
| **HPC2** | $d+1$ | $d(d+1)/2$ | $2$ (asym: `inb` 2, `ina` 1) | **$d$-PINI** | **Yes (trivial)** | `MSKand_HPC2.v` |

---

### 5. Gate-Level Robust-Probing Verifiers: SILVER, REBECCA, fullVerif, and PROLEAD

`Basis: normative + source + documentation`

Direct inspection of the four pinned upstream repositories reveals complementary architectural trade-offs across **soundness** (zero false negatives), **completeness** (zero false positives), **physical leakage coverage** (glitches, transitions, coupling, faults), and **netlist scalability**:

| Verifier & Pinned Revision | Verification Core | Physical Models Supported | Security Notions Checked | Soundness / Completeness | Scalability Ceiling & Practical Prerequisite |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **SILVER** (`0a3c85fc...`) | Exact Sylvan parallel ROBDD / MTBDD probability distributions (`mtbdd_statindependence`) | Standard & glitch-extended (`robustModel`, `Silver.cpp:248–660`) | `Probing`, `NI`, `SNI`, `PINI`, `Uniformity` | **Sound & Complete** (exact distribution; 0 FP, 0 FN) | Gadgets & S-boxes (~10–30 inputs/masks; exponential in fan-in `1 << extended.size()`); requires constrained cell library (`set_dont_use` on `FA*`, `HA*`, `AOI*`, `OAI*`, `MUX*`, $\ge 3$-input cells, `README.md:90–118`) |
| **REBECCA** (`09c93f89...`) | Z3 SMT over Boolean Fourier correlation sets (`Z3Checker.py`) | `stable` & `transient` (glitches, lines 106–190) | $d$-probing (`check_security`) & independence (`IndepChecker.py`) | **Sound**, Incomplete (conservative over-approx; 0 FN, possible FP) | Moderate pipelined circuits & S-boxes; lacks VCD execution trace so control-heavy CPUs trigger false positives |
| **fullVerif** (`227f3121...`) | Rust graph dataflow checker (`tg_graph.rs`, `comp_prop.rs`) + Yosys + Icarus Verilog control trace | Glitch-extended via pre-verified atomic `PINI`/`Affine` gadgets | Compositional `PINI`, `Affine` (assumes atomic gadget proofs) | **Sound** modulo atomic gadget assumptions (`fv_strat = "assumed"`) | **Full ciphers** (AES, PRESENT) at arbitrary order $d$ in seconds; cannot verify non-composable/flattened custom RTL |
| **PROLEAD** (`2c8c8486...`) | Bit-sliced 64-trace parallel Monte Carlo simulation + contingency-table $G$-test (`ProbingSets.cpp:67–85`) | Glitch-extended, **Relaxed-Robust** (`Enabler.hpp`), **Transitional** (`transitional_leakage`), Multivariate (`distance`), **Combined Faults** (FIESTA), GDSII layout (`inc/Hardware/gds/`) | `ps`, `ni`, `sni`, `pini` (`prolead_config.schema.json:221–225`) | **Statistical** (type-I $\alpha$, type-II $\beta$, `effect_size`; compact mode can miss leaks) | **Full ciphers & large masked accelerators** (e.g., OpenTitan OTBN MAI gadgets); runtime scales with `number_of_simulations` and probe-set count |

#### Key Algorithmic Internals Verified Directly From Source

1. **SILVER (`Chair-for-Security-Engineering/SILVER`, `src/Silver.cpp:616–720`):**
   - Every wire stores a Sylvan BDD `getFunction()` and, for glitch propagation, a BDD variable set `getRegisters()` capturing all registers/inputs in its combinational fan-in cone.
   - In `check_PINI` (lines 650–658), when `robustModel == true`, a probe expands to `extended = BddSet(observation).toVector()` and enumerates all $2^{|\text{extended}|} - 1$ non-empty subsets (`for (int comb = 1; comb < (1 << extended.size()); comb++)`), computing exact joint statistical independence via `mtbdd_statindependence`. This exactness guarantees zero false positives—allowing SILVER to certify subtle schemes like non-uniform TI stages or verify exact output uniformity (`check_Uniform`)—at the price of exponential blowup if combinational fan-in cones exceed $\sim 20$ signals.
2. **REBECCA (`IAIK/REBECCA`, `Z3Checker.py:106–190`):**
   - Represents every node's stable and transient Walsh–Hadamard (Fourier) spectrum over-approximation as Boolean indicator vectors `variables_stable[node]` and `variables_transient[node]`.
   - Linear gates (`xor`/`xnor`, lines 106–117) propagate **exact XOR** in `stable` mode (`out = in1 ^ in2`), but relax to the **4-way disjunction** `empty ∨ copy(in1) ∨ copy(in2) ∨ xor(in1, in2)` in `transient` mode—capturing the physical reality that a glitching XOR gate exposes either input individually before both settle.
   - Nonlinear gates (`and`/`or`, lines 127–139) use the 4-way disjunction in both `stable` and `transient` modes.
   - Registers (`dff`/`dffsr`, lines 181–190) act as **glitch barriers**: `variables_transient[gate] == variables_stable[in1]`, resetting transient correlation sets back to the pre-clock stable correlation set.
   - A leak exists iff Z3 finds $\le d$ activated nodes whose XOR parity cancels all masks while retaining at least one secret variable (lines 61–88).
3. **PROLEAD (`ChairImpSec/PROLEAD`, `src/Hardware/ProbingSets.cpp`, `inc/Hardware/Enabler.hpp`, `prolead_config.schema.json`):**
   - Evaluates 64 simulations simultaneously in `uint64_t` bit-slices, accumulating per-probing-set contingency tables across secret input `groups` (e.g., fixed-vs-random) and testing statistical independence via the log-likelihood ratio **$G$-test** (`ComputeGTest`, `ProbingSets.cpp:67–85`) with power analysis driven by `beta_threshold` and `effect_size` via `boost::math::chi_squared_distribution`.
   - Implements the **Robust-but-Relaxed probing model** (Müller & Moradi, ePrint `2024/1277`) via `Enabler` (`Enabler.hpp:9–24`), which evaluates cell-specific `glitch_expr_` and `propagation_expr_` on each simulation trace so that a gate whose controlling input is constant-0 (e.g., a gated blanker or disabled multiplexer path) does not spuriously extend glitches.
   - Supports **transitional leakage** (`transitional_leakage: true`), **multivariate probing** (`variate: "multivariate"` / `"exclusive_multivariate"` with cycle `distance`), **combined side-channel + fault injection** (`fault_injection.fault_locations`, FIESTA, ePrint `2025/1287`), and **GDSII physical layout scanning** (`inc/Hardware/gds/GDSScanner.hpp`, `GDSProbe.hpp`) for physical coupling/probe-surface modeling.
   - **Soundness caveat documented directly in `prolead_config.schema.json:18–20`:** Enabling `performance.compact_distributions: true` compresses probe observations (e.g., to Hamming weights) for memory efficiency and explicitly warns: *"It is possible that PROLEAD oversees leakage due to the compression."*

---

### 6. Dual-Rail Precharge Logic (`SABL`, `WDDL`): Routing Asymmetry and Early Propagation Pitfalls

`Basis: normative + derived + execution`

Dual-Rail Precharge Logic (DPL) attempts to equalize CMOS dynamic switching energy per clock cycle *without secret sharing* by representing every logical bit $a$ as a complementary pair $(a, \bar{a})$ cycling between:
- **Precharge phase:** $(a, \bar{a}) = (0, 0)$ (every rail discharged).
- **Evaluation phase:** $(a, \bar{a}) \in \{(0, 1), (1, 0)\}$ (exactly one rail charges $0 \to 1$).

Two principal designs dominate the literature:
- **SABL (Sense Amplifier Based Logic; Tiri, Akmal, Verbauwhede, ESSCIRC 2002, IEEE Xplore 1136696):** Custom full-custom dynamic differential CMOS cells containing an internal discharge path that connects every internal node to ground during precharge, attempting to equalize *internal* parasitic capacitance switching regardless of input pattern. Requires custom standard-cell characterization and full-custom layout.
- **WDDL (Wave-Dynamic Differential Logic; Tiri and Verbauwhede, DATE 2004, DOI `10.1109/DATE.2004.1268856`):** Synthesizable from ordinary static CMOS standard cells using only positive (monotone) dual-rail compound gates—for example, WDDL AND maps $(a, \bar{a}), (b, \bar{b}) \mapsto (q = a \land b,\; \bar{q} = \bar{a} \lor \bar{b})$—so a precharge front (`0`) propagates monotonically through combinational logic without glitches.

Despite theoretical appeal, **two physical effects break WDDL (and practical SABL/DPL) at first order**:

1. **Early Propagation Effect (EPE; Suzuki and Saeki, CHES 2006, DOI `10.1007/11894063_21`):**
   - In WDDL AND ($q = a \land b$, $\bar{q} = \bar{a} \lor \bar{b}$), the OR gate generating $\bar{q}$ fires as soon as *either* $\bar{a} = 1$ or $\bar{b} = 1$ arrives—without waiting for the second input!
   - **Execution witness (Sub-probe 1C):** With zero capacitance mismatch ($\Delta C = 0$) and input $a$ arriving at $t = 0$ before $b$ at $t = \Delta t > 0$:
     - $(a=0, b=0) \implies \bar{a}=1 \implies \bar{q}$ switches $0 \to 1$ at **`t = 0` (EARLY)**.
     - $(a=0, b=1) \implies \bar{a}=1 \implies \bar{q}$ switches $0 \to 1$ at **`t = 0` (EARLY)**.
     - $(a=1, b=0) \implies \bar{a}=0 \implies \bar{q}$ waits for $\bar{b}=1$ and switches at **`t = Δt` (LATE)**.
     - $(a=1, b=1) \implies q$ waits for $b=1$ and switches at **`t = Δt` (LATE)**.
   - Even though every evaluation charges exactly one rail with identical total energy $E$, the **switching timestamp** leaks **`I(a; switch_time) = 1.000000 bit`** directly into time-resolved power and electromagnetic traces! Eliminating EPE requires custom dual-rail synchronizing cells (e.g., DRSL / SecLib / BCDL) that stall evaluation until both rails arrive, incurring severe area/delay overhead ($3\times$–$6\times$).
2. **Differential Backend Routing Capacitance Mismatch and Crosstalk:**
   - Standard EDA place-and-route engines route $q$ and $\bar{q}$ independently across different metal layers, via counts, wire lengths, and aggressor neighbors. If $C_q = C_0(1 + \varepsilon/2)$ and $C_{\bar{q}} = C_0(1 - \varepsilon/2)$, the switching energy difference $\Delta E / E_{\text{avg}} = \varepsilon$ directly correlates with the secret bit $q$ (`5%` mismatch $\implies$ `5%` deterministic power delta, Sub-probe 1C).
   - Tiri and Verbauwhede (CARDIS 2004, DOI `10.1007/1-4020-8147-2_10`) mitigated this via the **"fat wire"** backend flow—routing each differential pair as a single double-width abstract wire and splitting it post-routing—yet residual within-die process variation, asymmetric neighbor crosstalk, and FPGA LUT/switchbox asymmetry still leave measurable first-order leakage. Consequently, DPL is treated in modern high-assurance designs (such as OpenTitan) as a **hiding** layer at best, never a standalone substitute for provable Boolean masking.

---

### 7. Synthesis and Compiler-Pass Invariants at the RTL-to-Netlist Boundary

`Basis: source + documentation + derived`

Just as optimizing C/Rust compilers break software masking by coalescing shares across registers or simplifying `(x ^ r) ^ r -> x`, **RTL logic synthesis tools (Synopsys Design Compiler, Yosys, Vivado) silently destroy hardware glitch resistance** unless constrained by strict structural barriers:

1. **XOR/AND re-association before synchronization registers:** In DOM (`(a0 & b1) ^ z`), if synthesis distributes or reorders the XOR across an upstream gate or combines `(a0 & b0) ^ ((a0 & b1) ^ z)` across a retimed register boundary, both shares enter the same combinational cone. OpenTitan explicitly instantiates synthesis-barrier primitives `prim_xor2` (`prim_dom_and_2share.sv:69–75, 128–134`), `prim_flop_en` (`aes_sbox_dom.sv:118–127`), and `prim_buf`, accompanied by an explicit banner (`aes_sbox_dom.sv:31–39`): *"Without the proper primitives, synthesis tools might heavily optimize the design. The result is likely insecure."*
2. **Register retiming and constant/redundant logic folding:** Allowing `compile_ultra` autoungrouping or register retiming collapses `HPC2` registers `u`, `v`, `w` (`MSKand_HPC2.v:36`) or `MSKref` share registers (`MSKref.v:13, 18`), destroying PINI isolation. Both `fullverif` (`(* syn_keep = "true", keep = "true", syn_preserve = "true", preserve = "true" *)`) and `SILVER` (`compile_ultra -no_autoungroup`, `README.md:124`) mandate hierarchy and register preservation.
3. **Complex multi-input standard cell mapping (`AOI`/`OAI`/`MUX`/`FA`):** Mapping masked logic into compound cells hides internal glitch paths and violates cell-level leakage assumptions; `SILVER` explicitly blacklists `FA*`, `HA*`, `AOI*`, `OAI*`, `MUX*`, and $\ge 3$-input gates (`README.md:90–118`).
4. **Mandatory post-synthesis verification invariant:** Security properties proved on behavioral RTL do **not** transfer across unverified synthesis. Every gate-level verifier (`SILVER`, `REBECCA`, `PROLEAD`, `fullVerif`) operates on the **post-synthesis mapped netlist** (with `dont_touch` preserved through place-and-route for physical coupling isolation).

## Boundaries

- **Known not to apply — Ideal $d$-probing proofs to physical CMOS without register barriers:** Proving ISW or software-style Boolean masking secure in the standard (glitch-free) $d$-probing model does **not** imply first-order physical security in combinational CMOS hardware; Sub-probe 1A demonstrates complete $2.000000$-bit glitch-cone exposure and $0.50$ transient mean bias at $d=1$.
- **Known not to apply — DOM-indep to arbitrary composition or unpipelined consecutive inputs:** DOM-indep is verified `NI.robust`, not `SNI.robust` or `PINI` (`SILVER/README.md:43–45`; Sub-probe 1A `DOM(x,x)` leaks `1.000000 bit`). Unpipelined DOM (`Pipeline = 0`) leaks across consecutive cycles unless inputs remain stable for two full clocks (`prim_dom_and_2share.sv:158–166`).
- **Known not to apply — PROLEAD statistical pass as an absolute formal proof:** Passing PROLEAD with `N` simulations establishes absence of leakage above the configured `effect_size` at false-negative rate $\beta$ for the evaluated probing sets and input groups; it is **not** a deductive formal proof for arbitrarily small leakage biases or unsimulated control states, and `compact_distributions: true` explicitly sacrifices completeness (`prolead_config.schema.json:18–20`).
- **Known not to apply — WDDL/SABL dual-rail logic against EPE and localized EM:** Dual-rail precharge logic provides hiding rather than cryptographic order-$d$ masking; EPE leaks at zero routing mismatch (`1.000000 bit` in Sub-probe 1C), and near-field electromagnetic probes can spatially resolve individual complementary rails even when global supply currents cancel.
- **Unsupported — Full-cipher exhaustive verification in SILVER and dynamic control-flow CPUs in REBECCA:** SILVER's ROBDD probability tables scale only to gadgets and S-boxes (not full pipelined cipher cores), and REBECCA (`IAIK/REBECCA`) does not ingest execution traces (VCDs), causing false positives on sequential circuits with muxed control paths (addressed instead by execution-aware tools such as CocoAlma).
- **Not examined — Post-layout SPICE transistor-level capacitive coupling extraction and 3rd-generation HPC3 / low-latency GLM gadgets:** This investigation inspected RTL, gate-level netlist verifier code, and analytic/exhaustive discrete models; transistor-level SPICE simulations of capacitive wire coupling ($c$-probing on specific PDKs such as Sky130/Nangate45), `HPC3` (`Chair-for-Security-Engineering/HPC3`), and low-latency masking (e.g., GLM / LMDPL / CAPA) were not executed.
- **Unknown — Exact physical coupling leakage threshold under modern sub-7nm FinFET interconnect stacks:** Gate-level verifiers (even PROLEAD's `gds` bounding-box scanner) abstract interconnect crosstalk into geometric/Boolean probe neighborhoods; exact quantitative mutual-capacitance leakage thresholds depend on foundry PDK metal-stack parasitics not publicly standardized across nodes.

## Evidence

### Pinned Upstream Repositories and Source Citations (Observed 2026-11-19)

- **`ChairImpSec/PROLEAD` @ `2c8c8486d84f58b121b7198fc267ce520d29d39a`** (resolved via `git -c protocol.version=0 ls-remote`):
  - `README.md:27–31` — publication lineage (PROLEAD TCHES 2022, PROLEAD_SW TCHES 2023, Robust-but-Relaxed ePrint `2024/1277`, FIESTA ePrint `2025/1287`).
  - `prolead_config.schema.json:18–20, 206–388` — `compact_distributions` leakage-oversight warning, `notion` (`ps`/`ni`/`sni`/`pini`), `transitional_leakage`, `variate`, `distance`, `effect_size`, `probe_placement`, `extension_routes`, `fault_injection`.
  - `inc/Hardware/Enabler.hpp:9–24` — `Enabler` class with `glitch_expr_` and `propagation_expr_` for relaxed glitch propagation.
  - `src/Hardware/ProbingSets.cpp:67–85` — `ProbingSet::ComputeGTest` and `IsSampleSizeSufficient` (`boost::math::chi_squared_distribution`, `beta_threshold`, `effect_size`).
  - `inc/Hardware/gds/` — `GDSScanner.hpp`, `GDSProbe.hpp`, `AttackedSurface.hpp`.
- **`Chair-for-Security-Engineering/SILVER` @ `0a3c85fc5a60d76eedb84d996473df28fc18ef42`**:
  - `README.md:35–47` — recorded verification output for 1st-order DOM (`test/dom/dom1.nl`): `NI.robust PASS`, `SNI.robust FAIL (<out:line18>)`, `PINI.standard FAIL (<and:line6>)`, `PINI.robust FAIL (<reg:line14>)`, `uniformity PASS`.
  - `README.md:85–128` — Design Compiler `set_dont_use` cell restrictions and `-no_autoungroup` requirement.
  - `inc/Silver.hpp:60–78` and `src/Silver.cpp:172–720` — `check_Uniform`, `check_Probing`, `check_NI`, `check_SNI`, `check_PINI` using Sylvan ROBDDs and `mtbdd_statindependence`.
- **`IAIK/REBECCA` @ `09c93f8994ca09352e967221c4c407d060e8ea99`**:
  - `README.md:1–87` — Yosys netlist parsing and `stable`/`transient` CLI modes.
  - `Z3Checker.py:56–190` — Z3 Boolean Fourier correlation-set encoding for ports, linear gates (exact XOR stable, 4-way disjunction transient), nonlinear gates (4-way disjunction), and registers (glitch barrier copying `stable` to `transient`).
- **`cassiersg/fullverif` @ `227f31215d8269c3b78bb0ebaebf6a1db6bc198e`**:
  - `lib_v/MSKand_DOM.v:1–35` — `fv_prop = "NI"`, $n(n-1)/2$ random bits, 1-cycle latency.
  - `lib_v/MSKand_HPC1.v:1–37`, `lib_v/MSKand_HPC1.vh:1–3`, `lib_v/MSKref.v:1–133` — `fv_prop = "PINI"`, SNI refresh + DOM multiplier composition.
  - `lib_v/MSKand_HPC2.v:1–57`, `lib_v/MSKand_HPC2.vh:1–2` — `fv_prop = "PINI"`, $n(n-1)/2$ random bits, `u`, `v`, `w`, `aibi` registered pipeline with asymmetric input latencies (`1` and `0`, output `2`).
  - `fullverif-check/src/comp_prop.rs:5–38` — `check_sec_prop` enforcing `Affine` and `PINI` subgadget composition closure.
- **`hgrosz/aes-dom` @ `b34d018349e5f10805a03c3c46c5ad65d3127196`**:
  - `real_dom_shared_mul_gf2.vhdl:50–267` — `DOM-dep` blinding-based multiplier with `FIRST_ORDER_OPTIMIZATION` and general arbitrary-order `SHARES` paths.
- **`lowRISC/opentitan` @ `1e061997389b1c257043b0dbd2388a19a6c2f6f1`**:
  - `hw/ip/prim/rtl/prim_dom_and_2share.sv:28–173` — `Pipeline` parameter, `prim_xor2` synthesis barriers (lines 69, 128), `StableTwoCycles_M` SVA assumption (lines 162–166), and `prd_o = t1_q` reuse.
  - `hw/ip/aes/rtl/aes_sbox_dom.sv:5–160` and `hw/ip/aes/doc/theory_of_operation.md:191–200, 303–319` — 5-cycle DOM-dep AES S-box (28 PRD bits, CocoAlma-verified), synthesis warning banner, and deprecation of combinational masked Canright S-boxes.

### Normative Papers and DOIs

- Ishai, Sahai, Wagner (CRYPTO 2003): `10.1007/978-3-540-45146-4_27`
- Mangard, Pramstaller, Oswald (CHES 2005): `10.1007/11545262_12`
- Nikova, Rechberger, Rijmen (ICISC 2006): `10.1007/11935308_38`
- Bilgin et al. (ASIACRYPT 2014): `10.1007/978-3-662-45611-5_19`
- Reparaz et al. (CRYPTO 2015): `10.1007/978-3-662-47989-6_37`
- Gross, Mangard, Korak (ACM CCS TIS 2016): `10.1145/2996366.2996426` (`eprint.iacr.org/2016/486`)
- Barthe et al. (ACM CCS 2016): `10.1145/2976749.2978427`
- Faust et al. (TCHES 2018): `10.13154/tches.v2018.i3.89-120`
- Bloem et al. (EUROCRYPT 2018, REBECCA): `10.1007/978-3-319-93387-0` (`eprint.iacr.org/2017/897`)
- Cassiers and Standaert (IEEE TIFS 2020, PINI): `10.1109/TIFS.2020.2971153`
- Knichel, Sasdrich, Moradi (ASIACRYPT 2020, SILVER): `10.1007/978-3-030-64837-4_26`
- Cassiers et al. (IEEE TC 2021, HPC1/HPC2/fullVerif): `10.1109/TC.2020.3022979` (`eprint.iacr.org/2020/185`)
- Müller and Moradi (TCHES 2022, PROLEAD): `10.46586/tches.v2022.i4.311-348`
- Tiri, Akmal, Verbauwhede (ESSCIRC 2002, SABL): IEEE Xplore `1136696`
- Tiri and Verbauwhede (DATE 2004, WDDL; CARDIS 2004, fat-wire routing): `10.1109/DATE.2004.1268856`, `10.1007/1-4020-8147-2_10`
- Suzuki and Saeki (CHES 2006, EPE): `10.1007/11894063_21`

### Reproducible Execution Micro-Probe (Observed 2026-11-19, Python 3)

Command:

```bash
python3 - <<'PY'
import itertools, math
from collections import Counter, defaultdict

def mi(pairs):
    n = len(pairs)
    px, py, pxy = Counter(x for x, _ in pairs), Counter(y for _, y in pairs), Counter(pairs)
    return max(0.0, sum((c / n) * math.log2((c / n) / ((px[x] / n) * (py[y] / n))) for (x, y), c in pxy.items()))

states5 = list(itertools.product([0, 1], repeat=5))
states3 = list(itertools.product([0, 1], repeat=3))

# 1A: ISW-unreg vs DOM-indep vs DOM(x,x) vs DOM Pipeline=0 vs HPC2(x,x)
print("ISW stable:", f"{mi([((a0^a1,b0^b1), (((a0&b1)^r)^(a1&b0))^(a1&b1)) for a0,a1,b0,b1,r in states5]):.6f}")
print("ISW glitch:", f"{mi([((a0^a1,b0^b1), (a0,a1,b0,b1,r)) for a0,a1,b0,b1,r in states5]):.6f}")
v3_means = {(a,b): sum(((a0&b1)^(a1&b0)^(a1&b1)) for a0,a1,b0,b1,r in states5 if (a0^a1,b0^b1)==(a,b))/8.0 for a,b in itertools.product([0,1],repeat=2)}
print("ISW v3_means:", v3_means)
togs = [((a0^a1,b0^b1), sum(u!=v for u,v in zip([0, a0&b1, (a0&b1)^(a1&b0), (a0&b1)^(a1&b0)^(a1&b1), (((a0&b1)^(a1&b0))^(a1&b1))^r], [a0&b1, (a0&b1)^(a1&b0), (a0&b1)^(a1&b0)^(a1&b1), (((a0&b1)^(a1&b0))^(a1&b1))^r]))) for a0,a1,b0,b1,r in states5]
print("ISW toggle MI:", f"{mi(togs):.6f}")
print("DOM(x,x) t0_d glitch:", f"{mi([(x0^x1, (x0,x1,r)) for x0,x1,r in states3]):.6f}")
print("DOM Pipe=0 q0 trans:", f"{mi([((a0^a1,b0^b1), ((a0&b0)^((a0&b1)^z), (a1&b1)^((a0&b1)^z))) for a0,a1,b0,b1,z in states5]):.6f}")
hpc2_max = max(
    mi([(x0^x1, obs(x0,x1,r)) for x0,x1,r in states3])
    for obs in [
        lambda x0,x1,r: (x1, r),
        lambda x0,x1,r: (x0, r),
        lambda x0,x1,r: (x0, x1^r),
        lambda x0,x1,r: (x1, x0^r),
        lambda x0,x1,r: (x0&x0, (1^x0)&r, x0&(x1^r)),
        lambda x0,x1,r: (x1&x1, (1^x1)&r, x1&(x0^r)),
    ]
)
print("HPC2(x,x) max glitch MI:", f"{hpc2_max:.6f}")

# 1B: 3-share TI non-completeness vs non-uniformity cascade
all6 = list(itertools.product([0, 1], repeat=6))
ti3 = lambda x0,x1,x2,y0,y1,y2: ((x1&y1)^(x1&y2)^(x2&y1), (x2&y2)^(x2&y0)^(x0&y2), (x0&y0)^(x0&y1)^(x1&y0))
print("TI-3 stage1 cone(z0):", f"{mi([((x0^x1^x2,y0^y1^y2), (x1,x2,y1,y2)) for x0,x1,x2,y0,y1,y2 in all6]):.6f}")
print("TI-3 stage2 no-remask:", f"{mi([((x0^x1^x2,y0^y1^y2), ti3(x0,x1,x2,y0,y1,y2)[1:]) for x0,x1,x2,y0,y1,y2 in all6]):.6f}")
print("TI-3 stage2 remasked:", f"{mi([((x0^x1^x2,y0^y1^y2), (z1^r1, z2^r0^r1)) for x0,x1,x2,y0,y1,y2 in all6 for z0,z1,z2 in [ti3(x0,x1,x2,y0,y1,y2)] for r0,r1 in itertools.product([0,1],repeat=2)]):.6f}")

# 1C: WDDL EPE timing leak at DeltaC = 0
print("WDDL EPE I(a; t_switch):", f"{mi([(a, 'EARLY' if ((a&0)|((1-a)|0)) else 'LATE') for a,b in itertools.product([0,1],repeat=2)]):.6f}")
PY
```

Recorded output (`exit 0`):

```text
ISW stable: 0.000000
ISW glitch: 2.000000
ISW v3_means: {(0, 0): 0.25, (0, 1): 0.25, (1, 0): 0.25, (1, 1): 0.75}
ISW toggle MI: 0.226948
DOM(x,x) t0_d glitch: 1.000000
DOM Pipe=0 q0 trans: 0.204434
HPC2(x,x) max glitch MI: 0.000000
TI-3 stage1 cone(z0): 0.000000
TI-3 stage2 no-remask: 0.039699
TI-3 stage2 remasked: 0.000000
WDDL EPE I(a; t_switch): 1.000000
```

## Revalidation

1. **Mathematical and counterexample invariants (seconds):** Rerun the inline Python 3 probe under **Evidence** to re-verify all exact mutual-information witnesses (`ISW`, `DOM`, `HPC2`, `TI-3`, `WDDL EPE`); zero external dependencies are required.
2. **Upstream verifier capability and configuration checks:**
   - Diff `ChairImpSec/PROLEAD` `prolead_config.schema.json` and `inc/Hardware/Enabler.hpp` against revision `2c8c8486d84f58b121b7198fc267ce520d29d39a` to check whether new probing notions, relaxed-model cell rules, or fault-injection hooks have changed.
   - Diff `Chair-for-Security-Engineering/SILVER` `src/Silver.cpp` against `0a3c85fc5a60d76eedb84d996473df28fc18ef42` and `cassiersg/fullverif` `lib_v/MSKand_HPC2.v` + `fullverif-check/src/comp_prop.rs` against `227f31215d8269c3b78bb0ebaebf6a1db6bc198e` to check for new gadget definitions or compositional properties beyond `PINI`/`Affine`.
   - Diff `lowRISC/opentitan` `hw/ip/prim/rtl/prim_dom_and_2share.sv` and `hw/ip/aes/rtl/aes_sbox_dom.sv` against `1e061997389b1c257043b0dbd2388a19a6c2f6f1` to confirm default `SecSBoxImpl`, `Pipeline` settings, and `prim_xor2`/`prim_flop_en` synthesis barriers remain intact.
3. **Post-synthesis netlist sign-off for any concrete RTL change:** Synthesizing a target gadget or cipher with Yosys or Design Compiler and executing `SILVER` (for small gadgets requiring exact `PINI`/`Uniformity`), `fullVerif` (for PINI-composed ciphers), or `PROLEAD` (with `compact_distributions: false`, `transitional_leakage: true`, and sufficient simulation budget for the desired `effect_size`) directly revalidates whether synthesis preserved glitch and transition isolation.
