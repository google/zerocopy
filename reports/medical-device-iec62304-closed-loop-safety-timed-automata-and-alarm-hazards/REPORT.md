# Medical Device Safety under IEC 62304: Closed-Loop Timed Automata, Concurrent Interlock Races, Formal HMI Number-Entry Verification, and Alarm Hazards

## Summary

Safety-critical medical software fails predominantly at **closed-loop cyber-physical and human-machine boundaries**, not in isolated unit logic. Four cross-cutting formal invariants govern regulatory assurance (IEC 62304 Class C, IEC 60601-1-8) and mechanized verification across implantable devices, radiation therapy accelerators, and programmable infusion pumps:

1. **Open-Loop Verification Is Blind to Organ-Device Feedback Loops (Pacemaker-Mediated Tachycardia):** Verifying a dual-chamber `DDD` pacemaker in isolation confirms single-device timing bounds (`TLRI = 1000 ms`, `TURI = 400 ms`) while completely missing **Endless-Loop Tachycardia (ELT / PMT)**. When coupled to a physiological Virtual Heart Model (`VHM`) with retrograde ventriculoatrial conduction in $[150, 200]\text{ ms}$ and default `TPVARP = 100 ms`, symbolic Difference Bound Matrix (DBM) zone exploration immediately discovers an infinite closed-loop re-entry cycle locking ventricular pacing to the Upper Rate Limit (`400 ms` = `150 bpm`). Proving freedom from sustained PMT requires closed-loop composition and either a dynamic intervention (`ELT_count` extending `TPVARP -> 500 ms` after 8 consecutive `VP–AS` beats so retrograde activation is reclassified as Atrial Refractory `AR`) or a static `TPVARP > Tretromax` bound (at the clinical cost of narrowing the atrial tracking window).
2. **Exact DBM Bit-Encoding and Asymmetric LU-Extrapolation Govern Timed-Automata Soundness:** Real-time reachability over dense clocks (Alur–Dill timed automata) is decided in UPPAAL's `UDBM` engine via canonical $O(n^3)$ Floyd–Warshall shortest-path closure over bit-packed `raw_t` bounds `(bound * 2) | strictness` (`dbm_STRICT = 0`, `dbm_WEAK = 1`), with branchless constraint addition `(x + y) - ((x | y) & 1)` and exact negation `1 - c`. Ensuring termination requires clock-bound extrapolation (`dbm_extrapolateMaxBounds` / `dbm_extrapolateLUBounds`), which is sound and complete for diagonal-free automata—whereas hand-translating verified automata to imperative code can introduce silent state-index bugs (as directly observed in the companion MATLAB reference `pacemaker_DDD.m:159`, where the `URI` switch reads `VRP`'s state index `pace_para{4,2}` instead of `pace_para{5,2}`).
3. **Removing Hardware Interlocks Turns Concurrency Races and 1-Byte Overflows into Lethal Hazards (Therac-25):** Replacing electromechanical interlocks with unverified real-time assembly exposed two fatal defects documented by Leveson and Turner (1993): (a) an 8-second race between concurrent data entry (`Datent`) and bending-magnet positioning (`Magnet`/`Ptime`, which cleared the shared edit flag on its first pass), firing an unflattened 25 MeV electron beam with the turntable in the open position while reporting a cryptic, routinely overridden `Malfunction 54`; and (b) incrementing an 8-bit `Class3` interlock flag (`Class3 = (Class3 + 1) & 0xFF`), which silently rolled over to `0` on every 256th `Set-Up Test` cycle and bypassed collimator verification (`CHKCOL`).
4. **Silent Key-Drop Semantics, Chevron Non-Reversibility, and Blanket Alarm Muting Cause Clinical Overdoses and Missed Emergencies:** Formal PVS/PVSio-web models of Generic PCA (`GPCA`) and commercial infusion pumps (`MDNumberpad.pvs`, `alarisGP.pvs`) expose concrete, reproducible HMI defects: silent `.` key ignoring above `THRESHOLD_ONE_DECIMAL = 100` turning intended `100.5 mL/h` into `1005.0 mL/h` ($10\times$ overdose), dropped decimal keystrokes turning `1.5` into `15.0`, `cancelClicked` failing to clear `rejectKeys` (`MDNumberpad.pvs:64-73`), and chevron key step discontinuities breaking `dn(up(v)) == v` at `99.9 -> 100.0 -> 99.0` and `999.0 -> 1000.0 -> 990.0`. Under IEC 62304 Clause 4.3 (Amd 1:2015) and IEC 60601-1-8 (Amd 2:2020), software mediating dose delivery or High-Priority alarms is Class C unless isolated by independent external hardware risk controls, and active `Audio Paused` states must be preempted immediately by any newly arriving High- or Medium-Priority alarm condition.

## Applicability

This report coalesces primary-source technical artifacts, formal models, and regulatory specifications across four interconnected verification domains:

- **Timed-automata symbolic engine (`UPPAALModelChecker/UDBM`):** Direct C/C++ source audit at commit `85ff047c0640577030d59d80cbe2c750b369cf26` (`include/dbm/constraints.h`, `src/dbm.c`), grounded in Alur and Dill (1994), Bengtsson and Yi (2004), and Behrmann, Bouyer, Larsen, and Pelánek (2006).
- **Closed-loop cardiac device verification (`mlab-upenn/MedCPS`):** Direct inspection of the UPPAAL XML model and TCTL query suite (`assets/downloads/vhm/PM_verify.zip` -> `PM_all.xml` and `PM_all.q`, generated with UPPAAL 4.0.9) and companion MATLAB model (`assets/downloads/vhm/pacemaker_DDD.m`) at commit `d5faf3e16dc92c8e7c54b05b25f9fd0180e75e05`, corresponding to Jiang, Pajic, and Mangharam (Proc. IEEE 2012) and Jiang, Pajic, Moarref, Alur, and Mangharam (TACAS 2012).
- **Infusion-pump formal HMI models (`pvsioweb/pvsio-web`):** Direct inspection of PVS theories at commit `7ea915e6cb9207fa06e841eabce8c19009d67548` — specifically `examples/projects/gpcaUI/gpcaUI.pvs`, `examples/projects/gpcaUI/NFM2013/{reference_model_th,refined_model_th}.pvs`, `examples/demos/GPCA/{AlarmingComponent,GPCA_Limits}.pvs`, `examples/projects/BaxterColleague/MDNumberpad.pvs`, and `examples/projects/AlarisGP/alarisGP.pvs` — corresponding to Masci et al. (SAFECOMP 2013; CAV 2015).
- **Retrospective accident forensics & medical safety standards:** Primary analysis of the Therac-25 accidents (Leveson & Turner, *IEEE Computer* 1993) and normative lifecycle/alarm rules from **IEC 62304:2006 + Amd 1:2015** and **IEC 60601-1-8:2006 + Amd 1:2012 + Amd 2:2020** (integrated with ISO 14971 risk management).

**Subject relationships:** `UDBM` provides the exact symbolic zone data structure underlying UPPAAL's verification of the `MedCPS` closed-loop pacemaker/heart model (`PM_all.xml`); `pvsio-web` exemplifies deductive theorem-proving and refinement-based verification (`reference_model_th` -> `refined_model_th`) for discrete clinical HMIs; Therac-25 illustrates the historical failure mode when software safety classification, concurrency verification, and hardware interlocks are absent; IEC 62304 and IEC 60601-1-8 establish the regulatory traceability and alarm-state invariants binding all three technical domains. Exact line-level findings apply to the pinned commits above; the formal properties (open-loop vs. closed-loop soundness gap, DBM canonicalization/extrapolation, uint8 counter rollover, decimal-drop multiplication hazards, and alarm audio-pause preemption) generalize across safety-critical cyber-physical medical systems.

## Findings

### 1. Alur–Dill Timed Automata and UPPAAL DBM Symbolic Zone Verification

Basis: normative + source + execution

#### Timed-Automaton Semantics

Alur and Dill (1994, *Theoretical Computer Science* 126(2):183–235, DOI `10.1016/0304-3975(94)90010-8`) define a timed automaton as a tuple $\mathcal{A} = (L, l_0, C, \Sigma, E, I)$ over finite locations $L$, initial location $l_0$, real-valued nonnegative clocks $C = \{x_1, \dots, x_n\}$, actions $\Sigma$, edges $E \subseteq L \times \Phi(C) \times \Sigma \times 2^C \times L$, and location invariants $I: L \to \Phi(C)$. Clock constraints $\Phi(C)$ are conjunctions of atomic bounds $x_i \prec c$ or diagonal constraints $x_i - x_j \prec c$ with $\prec \in \{<, \le\}$ and $c \in \mathbb{Z}$. Operational semantics alternate between:
- **Delay transitions:** $(l, u) \xrightarrow{d} (l, u + d)$ for $d \in \mathbb{R}_{\ge 0}$ iff $u + d' \models I(l)$ for all $0 \le d' \le d$;
- **Discrete transitions:** $(l, u) \xrightarrow{a} (l', u')$ iff $(l, g, a, r, l') \in E$, $u \models g$, $u' = u[r \mapsto 0]$, and $u' \models I(l')$.

UPPAAL extends this with broadcast channels (`chan!`/`chan?`), urgent/committed locations (which forbid time elapse, with committed locations taking atomic priority over non-committed ones), and bounded integer variables. Reachability for timed automata is **PSPACE-complete** (Alur & Dill 1994).

#### Exact `UDBM` Bit-Packed Representation and Operations

Direct inspection of `UPPAALModelChecker/UDBM` (`85ff047c0640577030d59d80cbe2c750b369cf26`) documents how dense clock zones $Z = \{u \in \mathbb{R}_{\ge 0}^n \mid \forall i,j \in \{0,\dots,n\},\; u_i - u_j \prec_{ij} c_{ij}\}$ (with reference clock $x_0 \equiv 0$) are represented and manipulated:

1. **Bit-Packed `raw_t` Encoding (`include/dbm/constraints.h:35-186`):**
   - Each matrix entry `D[i, j]` is a signed 32-bit `raw_t` packing the integer bound and strictness bit:
     $$\text{raw}(b, s) = (2 b) \mid s, \qquad s \in \{\texttt{dbm\_STRICT} = 0\text{ (}<\text{)},\; \texttt{dbm\_WEAK} = 1\text{ (}\le\text{)}\}$$
   - Decoding recovers `bound = raw >> 1` and `strictness = raw & 1`.
   - Constants: `dbm_LE_ZERO = 1` ($\le 0$), `dbm_INFINITY = INT_MAX >> 1`, `dbm_LS_INFINITY = dbm_INFINITY << 1` ($< \infty$), `dbm_LE_OVERFLOW = dbm_LS_INFINITY >> 1` (overflow guard).
   - **Exact branchless addition (`dbm_addRawRaw`, line 185):**
     ```c
     (x == dbm_LS_INFINITY || y == dbm_LS_INFINITY)
         ? dbm_LS_INFINITY
         : (x + y) - ((x | y) & 1)
     ```
     Truth table verification: $(\le a) + (\le b) = (2a+1)+(2b+1)-1 = 2(a+b)+1 \equiv (\le a+b)$; $(\le a) + (< b) = (2a+1)+(2b)-1 = 2(a+b) \equiv (< a+b)$; $(< a) + (< b) = 2a + 2b - 0 = 2(a+b) \equiv (< a+b)$.
   - **Exact complement negation (`dbm_negRaw`, line 151):** `1 - c`, satisfying $\neg(< a) = 1 - 2a = 2(-a) + 1 \equiv (\le -a)$ and $\neg(\le a) = 1 - (2a+1) = 2(-a) \equiv (< -a)$.

2. **Canonical Closure and Emptiness (`src/dbm.c:1020-1080`, `dbm_close`):**
   - Runs $O((n+1)^3)$ Floyd–Warshall shortest-path tightening `D[i,j] = min(D[i,j], D[i,k] + D[k,j])`.
   - A zone is **empty iff a negative cycle exists**, detected immediately by `D[k,k] < dbm_LE_ZERO` (i.e., $0 < 0$ or $0 \le -c$). Canonical form makes zone equality $Z_1 = Z_2$ and inclusion $Z_1 \subseteq Z_2$ exact entry-wise comparisons.

3. **Core Zone Operators & Finite Abstraction (`src/dbm.c:1877-2065`):**
   - **Time elapse (`dbm_up`):** Sets `D[i, 0] = dbm_LS_INFINITY` for all $i \ge 1$ (removing upper bounds on individual clocks while preserving all clock differences $x_i - x_j$).
   - **Clock reset ($x_k := 0$):** Copies row/column `0` into row/column `k` (`D[k, j] = D[0, j]`, `D[i, k] = D[i, 0]`, `D[k, k] = dbm_LE_ZERO`).
   - **Max-bound extrapolation (`dbm_extrapolateMaxBounds`, lines 1877–1921, $\text{Extra}_M$):** Uses per-clock maximum constant $M(x_i)$ to replace bounds $> M(x_i)$ with $< \infty$ and bounds $< -M(x_j)$ with $(< -M(x_j))$, guaranteeing a finite quotient state space (Bengtsson & Yi 2004, DOI `10.1007/978-3-540-27755-2_3`).
   - **Asymmetric Lower/Upper-bound extrapolation (`dbm_extrapolateLUBounds`, lines 1992–2041, $\text{Extra}_{LU}$; `dbm_diagonalExtrapolateLUBounds`, lines 2056+, $\text{Extra}_{LU}^+$):** Separates per-clock maximum **lower-bound** constants $L(x_i)$ (from guards $x_i \ge c, x_i > c$) from **upper-bound** constants $U(x_i)$ (from invariants/guards $x_i \le c, x_i < c$), replacing `D[i,j] > L[i]` with `< inf` and `D[i,j] < -U[j]` with `< -U[j]`. Behrmann, Bouyer, Larsen, and Pelánek (2006, *STTT* 8(3):204–215, DOI `10.1007/s10009-005-0190-0`) proved $\text{Extra}_{LU}^+$ is sound and complete for reachability on **diagonal-free** timed automata while yielding exponentially fewer symbolic zones than symmetric $k$-normalization.

---

### 2. Closed-Loop Dual-Chamber (`DDD`) Pacemaker and Virtual Heart Model Verification

Basis: source + execution + documentation

#### Architectural Decomposition of `PM_all.xml` (`mlab-upenn/MedCPS` @ `d5faf3e16d`)

Jiang, Pajic, and Mangharam (*Proc. IEEE* 2012, DOI `10.1109/JPROC.2011.2161241`) and Jiang, Pajic, Moarref, Alur, and Mangharam (TACAS 2012, DOI `10.1007/978-3-642-28756-5_14`) formalize a dual-chamber `DDD` pacemaker (sensing and pacing both atrium and ventricle, with dual inhibited/triggered response) composed in closed loop with a physiological **Virtual Heart Model (VHM)** / Random Heart Model (`RanA`, `RanV`, and bidirectional AV conduction automaton `cond`).

Inspection of the exact UPPAAL model `assets/downloads/vhm/PM_verify.zip` -> `PM_all.xml` and `PM_all.q` reveals every timing constant, channel, and automaton:

| Component Template | Clocks & Key Parameters (ms) | Locations & Invariants | Normative Clinical Function |
|---|---|---|---|
| `LRI` (Lower Rate Interval) | `t`; `TLRI = 1000`, `TAVI = 150` | `LRI` (`t <= TLRI - TAVI = 850`), `ASed` | Guarantees ventricular rate $\ge 60\text{ bpm}$ (`V–V <= 1000 ms`); emits atrial pace `AP!` at AEI = `850 ms` if no `AS`/`VS`/`VP` resets `t`. |
| `AVI` (Atrioventricular Interval) | `t`, global `clk`; `TAVI = 150`, `TURI = 400` | `Idle`, `AVI` (`t <= 150`), `WaitURI` (`clk <= 400`) | Started by `AP?` or `AS?`; paces ventricle `VP!` at `t >= 150` if `clk >= 400`, else stalls in `WaitURI` until `clk >= 400` (enforcing Upper Rate Limit $\le 150\text{ bpm}$); inhibited by intrinsic `VS?`. |
| `PVARP` (Post-Ventricular Atrial Refractory & Blanking) | `t`; `TPVAB = 50`, `TPVARP = 100` (mutable to `500`) | `Idle`, `PVAB` (`t <= 50`), `PVARP` (`t <= TPVARP`), committed `{ABl, inter, inter1}` | Entered on `VP?`/`VS?`. Atrial events during `PVAB` ($[0,50]\text{ ms}$) emit `ABlock!` (blanked); during `PVARP` ($[50,100]\text{ ms}$) emit `AR!` (refractory, **do not** start `AVI`); in `Idle` emit `AS!`. Restores `TPVARP = 100` on `PVARP -> Idle`. |
| `VRP` (Ventricular Refractory) | `t`; `TVRP = 150` | `Idle`, `VRP`, `VB`, `inter` | Blocks post-ventricular noise / T-wave oversensing for `150 ms` after `VP?`/`VS?`. |
| `URI` (Upper Rate Interval) | Global `clk`; `TURI = 400` | `URI` (resets `clk = 0` on `VS?`/`VP?`) | Tracks minimum allowable elapsed time since last ventricular event. |
| `cond` (Heart AV Conduction) | `t`; `Tante = [150, 200]`, `Tretro = [150, 200]` | `Idle`, `Ante` (`t <= 200`), `Retro` (`t <= 200`) | Models physiological antegrade (`AP`/`Aget` $\to$ `V_act!` in `[150,200] ms`) and **retrograde** (`VP`/`Vget` $\to$ `A_act!` in `[150,200] ms`) AV-node conduction. |
| `VPAS` + `ELT_count` (Anti-ELT) | `t`; retrograde window `[150, 200] ms`, count `8` | `VPAS: {Init, vp1, AS1, cancel}`; `ELT_count: Init..E8` (committed `E8`) | Counts 8 consecutive `VP -> AS` intervals falling in `[150, 200] ms`; on `E8 -> Init`, sets `TPVARP = 500` for one cycle to break endless-loop tachycardia. |
| `interval` + `Counter2` + `dur_count` (Mode Switch) | `t`; `thresh = 400`, 8 ventricular beats | `PAVI_MS`, `PLRI_MS` (`DDD <-> VDI`) | Detects supraventricular tachycardia (SVT / atrial fibrillation with `A–A <= 400 ms`) and switches pacing mode from atrial-tracking `DDD` to non-tracking `VDI`. |

#### Exact Mechanism of Pacemaker-Mediated Tachycardia (PMT / ELT) and TCTL Properties

Look at the exact closed-loop inequality exposed by `PM_all.xml`:
$$\texttt{TPVARP} = 100\text{ ms} \;<\; \texttt{Tretromin} = 150\text{ ms} \;\le\; t_{\text{retro}} \;\le\; \texttt{Tretromax} = 200\text{ ms}$$

1. A ventricular pace `VP!` (or premature ventricular contraction `Vget!`) resets `PVARP` ($t = 0$) and `URI` (`clk = 0`), and simultaneously launches `cond: Idle -> Retro` ($t = 0$).
2. At $t = 100\text{ ms}$, `PVARP` expires (`PVARP -> Idle`).
3. At $t \in [150, 200]\text{ ms}$, retrograde depolarization reaches the atrium (`cond` fires `A_act!`). Because `PVARP` is already in `Idle`, the pacemaker misinterprets the retrograde wave as a physiological sinus P-wave (`AS!`), triggering `AVI` (`t = 0`).
4. `AVI` expires at $t + 150 \in [300, 350]\text{ ms} < \texttt{TURI} = 400\text{ ms}$, entering `WaitURI`, and fires a new `VP!` at **exactly `clk = 400 ms` (`150 bpm`)**.
5. That `VP!` restarts `cond: Idle -> Retro`, creating a self-sustaining **Endless-Loop Tachycardia (ELT / PMT)** driven entirely by the pacemaker itself!

`PM_all.q` codifies six UPPAAL TCTL queries over composed monitors (`PURI_test`, `Pvv`, `Pvp_vp`, `PMS`, `PELT_det`):
- `A[] (PURI_test.interval imply PURI_test.t >= TURI)` — Upper Rate Limit safety invariant (holds).
- `A[] (Pvv.two_a imply Pvv.t <= TLRI)` — Lower Rate Limit bradycardia invariant for V–V intervals (holds; `PM_all.q:9` explicitly notes this invariant does **not** hold for A–A intervals).
- `E[] (not Pvp_vp.err)` — Existential witness checking whether sustained fast `VP–VP` tachycardia (PMT during SVT) is reachable.
- `A<> (PMS.err)` — Mode-Switch liveness (verifies `DDD -> VDI` switch eventually completes under fast atrial intervals `[100, 400] ms`).
- `E[] (not Pvp_vp.err && not PELT_det.err)` — Closed-loop ELT termination verification when `VPAS` + `ELT_count` are enabled.
- `A[] (not deadlock)` — Global deadlock freedom.

#### Symbolic DBM Micro-Probe Verification (Probe 2A)

Basis: execution

Running our self-contained Python `UDBM` bit-encoded DBM zone explorer (implementing `dbm_addRawRaw`, `dbm_close`, `dbm_up`, `dbm_reset`, `dbm_and`, and `dbm_extrapolateLUBounds` directly from `UPPAALModelChecker/UDBM`) over the exact `PM_all.xml` parameters (`TAVI=150, TURI=400, Tretromin=150, Tretromax=200`) reproduces the closed-loop verification dichotomy:

| Closed-Loop Configuration | Max `VP–AS` Streak | `VP–VP` Interval Range (ms) | Retrograde `AR` Blocks | Symbolic Zones Explored | Safety Verdict |
|---|---:|---|---:|---:|---|
| Open-loop (no retrograde `cond`) | 0 | N/A (no re-entry) | 0 | 2 | **False negative** (misses PMT) |
| Closed-loop `TPVARP = 100 ms`, no anti-ELT | $\ge 12$ (unbounded) | `[400, 400]` (150 bpm lock) | 0 | 48 | **UNSAFE: Endless-Loop PMT** |
| Closed-loop `TPVARP = 100 ms`, with `ELT_count` (`8 -> 500 ms`) | 7 (8th triggers extension) | `[400, 400]` during 8-beat burst | 1 (loop broken!) | 35 | **SAFE: Bounded ELT terminated** |
| Closed-loop static `TPVARP = 210 ms > Tretromax` | 0 | N/A | 1 (immediate block) | 3 | **SAFE (zero PMT)**, narrower tracking window |

#### Model-to-Code Fidelity Gap Observed in Companion Implementation

Basis: source

Direct inspection of `mlab-upenn/MedCPS` `assets/downloads/vhm/pacemaker_DDD.m` (lines 157–186) reveals a concrete manual-translation defect between the verified UPPAAL timed automaton and imperative reference code:
- `pace_para` stores row `4` = `VRP` and row `5` = `URI`.
- On line 159, the `URI` update block executes `switch pace_para{4,2}` (reading the **VRP** state index!) while lines 164 and 183 write to `pace_para{5,2}` (the **URI** state index!).
- Consequently, `URI` state transitions in that MATLAB script are erroneously gated by `VRP`'s timer/state (`TVRP = 150 ms`) instead of `URI`'s own state (`TURI = 400 ms`). This exemplifies why IEC 62304 Class C assurance favors automated code synthesis (e.g., `UPP2SF` / Simulink-to-C generation) or formal refinement verification rather than unverified manual recoding of model-checked automata.

---

### 3. Therac-25 Concurrent Interlock Races and 1-Byte Overflow Forensics

Basis: documentation + execution + derived

Leveson and Turner (*IEEE Computer* 26(7):18–41, July 1993, DOI `10.1109/MC.1993.274940`) investigated six massive radiation overdoses (1985–1987, resulting in deaths and severe permanent injuries) on the AECL Therac-25 medical linear accelerator (PDP-11 real-time assembly). Unlike its predecessor Therac-20—which retained electromechanical hardware interlocks that independently blocked unshielded high-current beams—Therac-25 **eliminated hardware interlocks and delegated safety exclusively to unverified concurrent software** reused from earlier designs.

#### Defect 1: The 8-Second `Datent` / `Magnet` / `Ptime` Race Condition (Tyler, Texas — March & April 1986)

- **Mechanism:** Therac-25 operated in two physical modes: low-current **Electron mode** (direct electron beam, turntable open with scanning magnets) and high-current **25 MeV X-ray mode** (requires rotating a heavy tungsten target/beam-flattener into the beam path via the turntable).
- Experienced operators frequently typed `x` (X-ray) by habit, realized the error, pressed cursor-up to edit to `e` (Electron), and hit Enter—completing the edit in under **8 seconds**.
- Concurrently, entering the initial mode had launched the `Magnet` subroutine, which took **~8 seconds** to set the bending magnets and called `Ptime` in a timing loop. `Ptime` checked a shared edit-request flag (`Tphase`/data-entry flag) and **cleared it on its first pass**, never re-checking if `Datent` modified the prescription during the remaining ~7.5 seconds of magnet setup.
- **Physical failure:** `Datent` rotated the turntable to the open Electron position (no flattening target), while `Magnet` left the electron gun at high-current 25 MeV X-ray power, delivering $\sim 16{,}500\text{–}25{,}000\text{ rad}$ (vs. a prescribed $\sim 200\text{ rad}$) to a tiny cross-section.
- **Alarm & HMI failure (`Malfunction 54`):** Ion chambers saturated and triggered a treatment pause displaying only **`MALFUNCTION 54`** ("dose input 2" — ambiguous between underdose and overdose, registering as few as 6 monitor units) alongside a `P` (**Proceed**) override key. Because transient pauses occurred up to 40 times per day during routine clinical operation, alarm desensitization led operators to press `P`, delivering repeated lethal exposures.

#### Defect 2: `Class3` 1-Byte Unsigned Counter Rollover (Yakima, Washington — January 1987)

- **Mechanism:** A shared single-byte variable `Class3` indicated whether upper-collimator / turntable hardware verification (`CHKCOL`) was required (`Class3 != 0` $\implies$ run `CHKCOL` and inhibit beam if misaligned; `Class3 == 0` $\implies$ bypass check).
- Instead of assigning a constant non-zero boolean (`Class3 := 1`), the `Set-Up Test` loop **incremented** the byte (`Class3++`, mod 256) on every pass.
- On every **256th pass** (`0xFF -> 0x00`), `Class3` overflowed to `0`. Pressing the `Set` button during that exact cycle skipped `CHKCOL` completely and fired an unshielded high-energy beam.

#### Executable Verification (Probe 2B)

Basis: execution

Probe 2B formalizes both failure modes:
- **Tyler race model:** Sweeping edit completion time $t_{\text{edit}} \in [0.5, 12.0]\text{ s}$ (`0.5 s` increments) with `Ptime` flag clearing at `0.5 s` and `Magnet` completion at `8.0 s` reaches `(X_25MeV_HighCurrent, E_Open_NoTarget)` for every $t_{\text{edit}} \in [1.0\text{ s}, 7.5\text{ s}]$ (`14/24` sampled timings).
- **Yakima `Class3` rollover model:** Simulating `class3 = (class3 + 1) & 0xFF` over 1,024 `Set-Up Test` cycles triggers `CHKCOL` interlock bypass at exact cycles `[256, 512, 768, 1024]` (rate `1/256`).

**Architectural lesson (still load-bearing under IEC 62304 Amd 1:2015):** Software-only interlocks without independent hardware fail-safe supervision (e.g., physical turntable limit switches wired directly into the klystron/beam-enable relay) violate defense-in-depth, and safety flags must never be implemented via wrapping integer counters or unguarded shared memory between asynchronous UI and actuator tasks.

---

### 4. Formal Verification of Infusion-Pump HMI Number-Entry and Refinement Invariants (`GPCA` / `PVSio-web`)

Basis: source + execution + documentation

Infusion pump programming errors (10× and 100× dose/rate overdoses caused by decimal-point drop, silent key rejection, wraparound, and mode confusion) are a leading cause of FDA Class I medical device recalls. Masci, Ayoub, Curzon, Lee, Sokolsky, and Thimbleby (SAFECOMP 2013, LNCS 8153:228–240, DOI `10.1007/978-3-642-40793-2_21`; CAV 2015, LNCS 9206:470–478, DOI `10.1007/978-3-319-21690-4_30`) coupled the **PVS** higher-order logic theorem prover to interactive visual prototypes in **`PVSio-web`** to formally verify FDA Generic Patient-Controlled Analgesia (`GPCA`) and commercial infusion-pump user interfaces.

#### Refinement Verification Architecture (`pvsioweb/pvsio-web` @ `7ea915e6cb`)

Inspection of `examples/projects/gpcaUI/NFM2013/{reference_model_th,refined_model_th}.pvs` and `examples/projects/gpcaUI/gpcaUI.pvs` shows a two-layer deductive safety proof pattern:

1. **Abstract Requirement Theory (`reference_model_th.pvs:12-15`):** Declares an uninterpreted state space `ui_state`, transition relation `trans(st0, st1)`, and inductive safety axiom `R1_Axiom`:
   ```pvs
   R1_Axiom: AXIOM
     (init?(st) => vtbi_settings_in_range?(vmin, vmax)(st)) AND
     ((vtbi_settings_in_range?(vmin, vmax)(st0) AND trans(st0, st1)) =>
       vtbi_settings_in_range?(vmin, vmax)(st1))
   ```
2. **Concrete Theory Interpretation (`refined_model_th.pvs:5-21`):** Instantiates `reference_model_th` with `ui_state := gpcaUI.gpcaui_state`, `init? := gpcaui_init?`, `trans` ranging over `{gpcaui_on, gpcaui_start, gpcaui_tick}`, `vmin := 0`, `vmax := max`, and `vtbi_settings_in_range?` asserting `vmin <= display(st) <= vmax AND vmin <= vtbi(st) <= vmax`. PVS automatically generates **Type Correctness Conditions (TCCs)** requiring mechanized proof of `R1_Axiom` under the concrete mapping.
3. **Subtyping and Unit Isolation (`examples/demos/GPCA/GPCA_Limits.pvs:4-18`):** Dependent predicate subtypes enforce static bounds (`device_real: TYPE = {r: nonneg_real | r <= 99999.99}`, `Cursor: TYPE = {i: int | i >= -2 AND i <= 4}`) and explicit physical unit distinctions (`DoseRATE_unit = {mg_per_hour}`, `VTBI_unit = {mL}`, `Time_unit = {minutes, seconds}`) so unit-mismatch assignments fail typechecking.
4. **Alarm-Controller Handshake (`examples/demos/GPCA/AlarmingComponent.pvs:13-75`):** Models `CheckReady` state transitions (`Normal -> Checking -> {s1, s2}`) gated by precondition predicates (`per_E_Clock`, `per_E_RequestToStart`, `per_E_Restart`, `per_tick`) that block infusion start unless `isPumpReady(st)` holds (while explicitly flagging line 75 `E_AlarmClear(st: State): State = st` as an unrefined abstract stub needing concrete `ErrCond := 0` refinement).

#### Concrete HMI Hazards Verified Directly from Primary PVS Models (Probe 2C)

Basis: source + execution

Transcribing and exhaustively checking two commercial-pump PVS models in `pvsioweb/pvsio-web` exposes **four exact formal HMI hazards**:

| Model & Source Location | Defect Class | Exact Witness / Counterexample | Clinical Consequence |
|---|---|---|---|
| `BaxterColleague/MDNumberpad.pvs:43-49` | **Silent Decimal-Point Rejection** | Keystroke sequence `[1, 0, 0, DOT, 5, OK]` (intended `100.5 mL/h`) $\implies$ `dotClicked` silently ignores `DOT` because `dispval(st) >= THRESHOLD_ONE_DECIMAL` (`100`), producing **`programmedValue = 1005.0`** | **$10\times$ bolus/rate overdose** with zero audio/visual warning |
| `BaxterColleague/MDNumberpad.pvs:13-32` | **Key-Bounce / Dropped-Decimal Multiplication** | Intended `1.5 mL/h` with hardware switch bounce or missed `.` registers `[1, 5, OK]` $\implies$ **`programmedValue = 15.0`** | **$10\times$ overdose** unless range/DERS hard limits or digit-by-digit confirmation catches it |
| `BaxterColleague/MDNumberpad.pvs:13-73` | **Stale `rejectKeys` Lockout & Guard Asymmetry** | `[9, 9, 9, 9, CANCEL, OK]` hits `TOO_HIGH` (`rejectKeys := true`), then `cancelClicked` (line 72) restores the display string **without clearing `rejectKeys := false`**, locking out `OK` (`programmedValue = 0.0`) and `DOT`, while `digitClicked` (lines 13–41) omits `NOT rejectKeys(st)` entirely | Mode confusion / frozen `OK` key while digits still mutate hidden state |
| `AlarisGP/alarisGP.pvs:37-58` | **Chevron Step-Size Non-Reversibility** | Exhaustive scan over all valid rates in `[0.0, 1200.0]` reveals **2 boundary violations** of `dn(up(v)) == v`: `99.9 -> up -> 100.0 -> dn -> 99.0` ($\Delta = -0.9$) and `999.0 -> up -> 1000.0 -> dn -> 990.0` ($\Delta = -9.0$) | Operator attempting to undo a single overshoot click lands 10× farther down than expected |

#### Design Rules for Formally Verified Clinical Number-Entry HMIs

Basis: normative + derived

1. **No Silent Key Drops (Feedback/Rejection Invariant):** Every out-of-grammar keystroke (e.g., `.` when disallowed, second `.`, overflow digit) must either produce an unmistakable modal error requiring explicit acknowledgment or be physically/visually disabled—never silently discarded while subsequent digits concatenate into the integer mantissa.
2. **Reversibility & Local Consistency:** For chevron/incremental interfaces, single-step inverse invariance `dn(up(v)) = v` (and explicit decimal-place cursor control as in `gpcaUI.pvs:129-202`) prevents boundary hysteresis jumps; furthermore, `up`/`dn` should avoid wraparound (`0 -> max` or `max -> 0`).
3. **Hard vs. Soft Dose Error Reduction System (DERS) Guardrails:** Distinguish soft clinical limits (overridable with explicit clinician confirmation) from hard pharmacological ceiling invariants (`max_rate`, `max_bolus`, `lockout_interval`) enforced in a safety-isolated Class C controller independent of UI presentation code.

---

### 5. Regulatory Lifecycle Traceability (`IEC 62304`) and Alarm Systems (`IEC 60601-1-8`)

Basis: normative + execution

#### IEC 62304:2006 + Amd 1:2015 Software Safety Classification (Clause 4.3) and SOUP

IEC 62304 defines software lifecycle processes integrated with **ISO 14971** risk management. Under **Clause 4.3** (significantly revised in **Amendment 1:2015**), every software system—and optionally segregated software items within it—receives a safety class based on worst-case harm assuming software failure **with probability 1** (software failure probability is never assigned $< 1$ to downgrade severity):

| Safety Class | Hazardous Situation Consequence (IEC 62304 Cl. 4.3) | Mandatory Lifecycle Rigor Highlights | Typical Medical Subsystem Examples |
|---|---|---|---|
| **Class A** | Cannot contribute to a hazardous situation, or risk remains acceptable **after accounting for risk control measures external to the software** (Amd 1:2015) | Software development plan, requirements, verification, release, configuration & problem resolution (Cl. 5.1, 5.2, 5.8, 8, 9) | Standalone hospital administrative logging, non-diagnostic display themes isolated behind hardware-checked read-only buses |
| **Class B** | Can contribute to a hazardous situation resulting in **non-serious injury** | Adds software architectural design, software integration & integration testing, detailed risk-control traceability, SOUP functional/performance specs (Cl. 5.3, 5.6, 7) | Secondary telemetry display, non-life-sustaining comfort settings |
| **Class C** | Can contribute to a hazardous situation resulting in **death or serious injury** | Adds **software detailed design (Cl. 5.4)**, **software unit implementation & verification with acceptance criteria (Cl. 5.5)**, explicit memory/timing/interface segregation proof, and rigorous anomaly analysis for every **SOUP** item | Pacemaker pacing/sensing firmware, infusion-pump motor/bolus/DERS controller, radiation beam/interlock control, **High-Priority alarm routing** |

**Key Clause 4.3 Segregation Rule (Amd 1:2015):** A manufacturer may downgrade a software item from Class C to Class B/A **only if** (a) an external hardware risk control measure (e.g., an independent hardware watchdog + electromechanical beam/pump cutoff) reduces risk to an acceptable level regardless of arbitrary software misbehavior, OR (b) software items are **segregated** (hardware MPU/MMU memory isolation, temporal partitioning, non-shared execution stacks) so that failure of the lower-class item cannot propagate to the Class C safety kernel. **SOUP** (Software of Unknown Provenance — RTOS kernels, C standard libraries, GUI frameworks, networking stacks) inherits the highest safety class of any software item whose failure it can cause unless isolated by verified segregation barriers; every SOUP anomaly list must be evaluated against the ISO 14971 hazard analysis.

#### IEC 60601-1-8:2006 + Amd 1:2012 + Amd 2:2020 Alarm Systems and Hazard Invariants

IEC 60601-1-8 specifies normative visual, auditory, and state-machine invariants for medical alarm systems to combat both **missed emergencies** and **clinical alarm fatigue**:

| Alarm Priority | Clinical Urgency | Visual Signal | Auditory Burst Pattern | Required State-Machine Invariants |
|---|---|---|---|---|
| **High Priority** | Immediate threat of death or irreversible injury (e.g., asystole, ventilator disconnect, upstream occlusion / air-in-line) | Flashing **red** indicator (higher duty/frequency than Medium) | Rapid **10-pulse** repeating burst (two 5-pulse sub-bursts; Amd 2:2020 adds validated Auditory Icons/Pointers) | Software path is normally **Class C**; **must preempt** any active `Audio Paused` state triggered for earlier alarms; latching recommended for transient life-threatening events so clinicians see missed spikes |
| **Medium Priority** | Prompt clinical attention needed; reversible injury or moderate deterioration (e.g., low battery, near-empty reservoir) | Flashing **yellow** indicator | Repeating **3-pulse** burst | Must preempt lower-priority visual/auditory presentation; must break `Audio Paused` when newly generated |
| **Low Priority** | Operator awareness / technical advisory | Steady (or slow) **yellow** (or cyan) indicator | **1- or 2-pulse** burst (optional repeat) | Cannot mask or suppress Medium/High priority visual or auditory indicators |

**Alarm-State Verification Invariants (Executable Probe 2C):**
1. **Priority Preemption Over `Audio Paused`:** Operator-initiated `Audio Paused` (bounded duration, typically $\le 120\text{ s}$ justified by risk analysis) may silence **only the currently active/acknowledged alarm conditions present at pause time**. If a **new** High- or Medium-priority condition triggers during `Audio Paused`, the controller **must break the pause immediately** and sound the new alarm. Probe 2C demonstrates that a naive global mute timer (`blanket_mute`) violates this invariant at `t = 20 s` when `OCCLUSION_UPSTREAM (HIGH)` arrives 15 seconds after pausing `LOW_BATT (LOW)`, whereas a condition-set-tracked IEC 60601-1-8 controller produces zero violations.
2. **Latching vs. Non-Latching Consistency:** For transient critical faults (e.g., transient ventricular tachycardia or intermittent occlusion), a **latching** alarm retains visual/auditory indication after the physiological condition self-clears until explicit operator acknowledgment (`ACK`), preventing silent recovery from hiding dangerous instability.
3. **Visual-Auditory-State Correspondence:** Every active `Audio Paused` / `Alarm Off` inactivation state must display a persistent, unmistakable status indicator; silencing an alarm must never clear the underlying fault or disable hardware safety cutoffs (directly addressing the Therac-25 `Malfunction 54` + `P` proceed failure mode).

## Boundaries

- **Not examined:**
  - Continuous physiological ODE/PDE cardiac electrophysiology models (e.g., Hodgkin–Huxley, Luo–Rudy, monodomain/bidomain reaction-diffusion meshes) and stochastic timed automata / Statistical Model Checking (`UPPAAL SMC`) for noisy ECG/EGM sensing thresholds were not audited at source level.
  - Hardware-in-the-loop (HIL) analog sensing front-ends (pacemaker lead impedance, electromagnetic interference EMI filtering, T-wave oversensing circuits) and mechanical infusion-pump flow sensors (ultrasonic air-in-line, peristaltic occlusion pressure transducers) were not examined.
  - Full-text licensed ISO/IEC normative PDFs for `IEC 62304:2006+Amd1:2015`, `IEC 60601-1-8:2006+Amd2:2020`, `ISO 14971:2019`, and `IEC 62366-1` (usability engineering) are paywalled standards; regulatory summaries here are cross-checked against public engineering references and FDA/academic compliance literature rather than line-numbered normative clause text.
  - Post-2015 FDA cybersecurity guidance (e.g., wireless telemetry / BLE/MICS RF authentication for ICDs and networked smart pumps under FDA Section 524B) was not examined.
- **Unsupported:**
  - Diagonal clock constraints ($x_i - x_j \prec c$) in UPPAAL/UDBM timed automata are **not** preserved by naive $\text{Extra}_M$ or $\text{Extra}_{LU}$ extrapolation alone (Behrmann et al. 2006); sound symbolic reachability for automata containing diagonal guards requires explicit diagonal splitting or alternative abstractions (`UDBM` provides `dbm_diagonalExtrapolateLUBounds` alongside zone splitting inside the UPPAAL engine).
  - Running the full PVS theorem prover (`SRI-CSL/PVS`) or binary UPPAAL 4.0.9 GUI verifier locally was unavailable in the sandbox environment; verification of `PM_all.xml` and `MDNumberpad.pvs`/`alarisGP.pvs` was executed via faithful standalone Python transcriptions of the exact `UDBM` DBM algorithms and PVS state transition functions.
- **Unknown:**
  - Whether later proprietary revisions of the Baxter Colleague or CareFusion/BD Alaris GP firmware modified the exact `dotClicked` / `cancelClicked` / chevron boundary behaviors modeled in `pvsioweb/pvsio-web` (`7ea915e6cb`) is not determinable from the archived academic PVS models alone.
  - Whether the `switch pace_para{4,2}` index bug in `mlab-upenn/MedCPS` `assets/downloads/vhm/pacemaker_DDD.m:159` was fixed in later private lab branches or successor MATLAB toolboxes (`PRETgroup/PACER-Heart-Model`) was not checked.
- **Known not to apply:**
  - Open-loop verification results for a `DDD` pacemaker (`PM_all.xml` without `Pcond`) are **known not to apply** to patients with intact retrograde VA conduction, where closed-loop feedback induces Endless-Loop PMT.
  - The IEC 62304 Clause 4.3 Amd 1:2015 classification downgrade via external risk controls does **not** apply if the external risk control itself depends on the same CPU, shared power rail, or unsegregated memory space as the software being classified.

## Evidence

### Primary Source Repositories and Line Citations

1. **`UPPAALModelChecker/UDBM`** @ `85ff047c0640577030d59d80cbe2c750b369cf26` (observed 2026-11-19):
   - `include/dbm/constraints.h`: lines 35 (`raw_t = int32_t`), 48–66 (`dbm_INFINITY`, `dbm_STRICT = 0`, `dbm_WEAK = 1`, `dbm_LE_ZERO = 1`, `dbm_LS_INFINITY`), 72 (`dbm_bound2raw: (bound * 2) | strict`), 91 (`dbm_raw2bound`), 146–152 (`dbm_negRaw: 1 - c`), 179–186 (`dbm_addRawRaw: (x + y) - ((x | y) & 1)`).
   - `src/dbm.c`: lines 1020–1080 (`dbm_close` $O(n^3)$ Floyd–Warshall canonicalization), 1877–1921 (`dbm_extrapolateMaxBounds`), 1992–2041 (`dbm_extrapolateLUBounds`), 2043–2065 (`dbm_diagonalExtrapolateLUBounds`).
2. **`mlab-upenn/MedCPS`** @ `d5faf3e16dc92c8e7c54b05b25f9fd0180e75e05` (observed 2026-11-19):
   - `assets/downloads/vhm/PM_verify.zip` -> `PM_all.xml`: global declarations (`TAVI=150, TLRI=1000, TPVARP=100, TPVAB=50, TVRP=150, TURI=400, thresh=400`), templates `AVI`, `LRI`, `PVARP`, `VRP`, `URI`, `cond(150,200,150,200)`, `VPAS` (`150 <= t <= 200`), `ELT_count` (`E8 -> Init: TPVARP=500`), `interval`/`Counter2`/`dur_count`, and closed-loop `system` compositions.
   - `assets/downloads/vhm/PM_verify.zip` -> `PM_all.q`: lines 1–31 (6 UPPAAL TCTL queries for URI, LRI, PMT, Mode-Switch, ELT termination, and deadlock freedom).
   - `assets/downloads/vhm/pacemaker_DDD.m`: lines 157–186 (URI timer block erroneously switching on `pace_para{4,2}` instead of `pace_para{5,2}`).
3. **`pvsioweb/pvsio-web`** @ `7ea915e6cb9207fa06e841eabce8c19009d67548` (observed 2026-11-19):
   - `examples/projects/gpcaUI/NFM2013/reference_model_th.pvs`: lines 1–17 (`R1_Axiom` inductive range safety invariant).
   - `examples/projects/gpcaUI/NFM2013/refined_model_th.pvs`: lines 1–23 (PVS theory interpretation mapping `gpcaUI.gpcaui_state` into `reference_model_th`).
   - `examples/projects/gpcaUI/gpcaUI.pvs`: lines 4–220 (state record, `gpcaui_on`, `gpcaui_start`, `gpcaui_tick`, `Cursor` $[-2, 4]$, `set_accuracy`, `up`/`dn`/`lf`/`rt`).
   - `examples/demos/GPCA/AlarmingComponent.pvs`: lines 1–87 (`CheckReady` state machine, `per_E_*` preconditions, abstract stub `E_AlarmClear` on line 75).
   - `examples/demos/GPCA/GPCA_Limits.pvs`: lines 1–20 (subtyped bounds and physical units `mL`, `mg_per_hour`, `minutes`, `seconds`).
   - `examples/projects/BaxterColleague/MDNumberpad.pvs`: lines 13–73 (`digitClicked`, `dotClicked` silently ignoring `.` when `dispval >= 100`, `cancelClicked` omitting `rejectKeys := false`, `digitClicked` omitting `NOT rejectKeys(st)`).
   - `examples/projects/AlarisGP/alarisGP.pvs`: lines 37–58 (`alaris_up`/`alaris_dn` boundary asymmetry noted at line 47 `-- note: dn(100) = 99 (and not 99.9)`), 68–118 (`press_UP`/`press_DN` acceleration).

### Peer-Reviewed Publications and Regulatory Standards

- R. Alur and D. L. Dill, "A theory of timed automata," *Theoretical Computer Science*, vol. 126, no. 2, pp. 183–235, 1994. DOI: `10.1016/0304-3975(94)90010-8`.
- J. Bengtsson and W. Yi, "Timed Automata: Semantics, Algorithms and Tools," *Lectures on Concurrency and Petri Nets*, LNCS vol. 3098, pp. 87–124, Springer, 2004. DOI: `10.1007/978-3-540-27755-2_3`.
- G. Behrmann, P. Bouyer, K. G. Larsen, and R. Pelánek, "Lower and Upper Bounds in Zone-Based Abstractions of Timed Automata," *Int. J. Softw. Tools Technol. Transf. (STTT)*, vol. 8, no. 3, pp. 204–215, 2006. DOI: `10.1007/s10009-005-0190-0`.
- Z. Jiang, M. Pajic, and R. Mangharam, "Cyber–Physical Modeling of Implantable Cardiac Medical Devices," *Proceedings of the IEEE*, vol. 100, no. 1, pp. 122–137, Jan. 2012. DOI: `10.1109/JPROC.2011.2161241`.
- Z. Jiang, M. Pajic, S. Moarref, R. Alur, and R. Mangharam, "Modeling and Verification of a Dual Chamber Implantable Pacemaker," *TACAS 2012*, LNCS vol. 7214, pp. 188–203, Springer, 2012. DOI: `10.1007/978-3-642-28756-5_14`.
- N. G. Leveson and C. S. Turner, "An Investigation of the Therac-25 Accidents," *IEEE Computer*, vol. 26, no. 7, pp. 18–41, July 1993. DOI: `10.1109/MC.1993.274940`.
- P. Masci, A. Ayoub, P. Curzon, I. Lee, O. Sokolsky, and H. Thimbleby, "Model-Based Development of the Generic PCA Infusion Pump User Interface Prototype in PVS," *SAFECOMP 2013*, LNCS vol. 8153, pp. 228–240, Springer, 2013. DOI: `10.1007/978-3-642-40793-2_21`.
- P. Masci, P. Oladimeji, Y. Zhang, P. L. Jones, P. Curzon, and H. W. Thimbleby, "PVSio-web 2.0: Joining PVS to HCI," *CAV 2015*, LNCS vol. 9206, pp. 470–478, Springer, 2015. DOI: `10.1007/978-3-319-21690-4_30`.
- IEC 62304:2006 + Amendment 1:2015, *Medical device software — Software life cycle processes*.
- IEC 60601-1-8:2006 + Amendment 1:2012 + Amendment 2:2020, *Medical electrical equipment — Part 1-8: General requirements for basic safety and essential performance — Collateral Standard: General requirements, tests and guidance for alarm systems in medical electrical equipment and medical electrical systems*.
- ISO 14971:2019, *Medical devices — Application of risk management to medical devices*.

### Self-Contained Executable Micro-Probes (Python 3 stdlib, Executed 2026-11-19)

Command: `python3 /tmp/probe_med_safety.py` (Python 3 standard library `math` only):

```python
#!/usr/bin/env python3
import math

# --- Probe 2A: Exact UDBM raw_t DBM engine + PM_all.xml closed-loop PMT check ---
S, W, INF_B = 0, 1, (1 << 30) - 1
LS_INF, LE_ZERO = INF_B << 1, 1
raw = lambda b, s=W: (b * 2) | s
rb = lambda r: r >> 1
radd = lambda x, y: LS_INF if (x == LS_INF or y == LS_INF) else (x + y) - ((x | y) & 1)

def close(m):
    n = len(m)
    for k in range(n):
        for i in range(n):
            if i == k or m[i][k] == LS_INF: continue
            mik = m[i][k]
            for j in range(n):
                if m[k][j] != LS_INF:
                    s = radd(mik, m[k][j])
                    if s < m[i][j]: m[i][j] = s
        if m[k][k] < LE_ZERO: return False
    return True

def up(m):
    for i in range(1, len(m)): m[i][0] = LS_INF
def band(m, i, j, b, s=W):
    r = raw(b, s)
    if r < m[i][j]: m[i][j] = r; return close(m)
    return True
def reset(m, c):
    for k in range(len(m)): m[c][k] = m[0][k]; m[k][c] = m[k][0]
    m[c][c] = LE_ZERO
def extrap_lu(m, L, U):
    n = len(m)
    for j in range(1, n):
        if rb(m[0][j]) < -U[j]: m[0][j] = raw(-U[j], S) if U[j] >= 0 else LE_ZERO
    for i in range(1, n):
        for j in range(n):
            if i == j: continue
            b = rb(m[i][j])
            if b > L[i] and b != INF_B: m[i][j] = LS_INF
            elif b < -U[j]: m[i][j] = raw(-U[j], S)
    close(m)

def check_pmt(tpv, retro, anti_elt=False, max_vp=12):
    L = U = [0, 150, 500, 400, 200]
    q = [(("Idle", "PVARP", "Retro" if retro else "Idle", 0, tpv, 1), [[LE_ZERO]*5 for _ in range(5)])]
    seen, max_elt, vv, ar = set(), 0, [], 0
    while q:
        (avi, pv, rt, elt, cpv, vpc), m = q.pop(0)
        if vpc > max_vp: continue
        mt = [r[:] for r in m]; up(mt); ok = True
        if pv == "PVARP": ok &= band(mt, 2, 0, cpv)
        if rt == "Retro": ok &= band(mt, 4, 0, 200)
        if avi == "AVI": ok &= band(mt, 1, 0, 150)
        if avi == "WaitURI": ok &= band(mt, 3, 0, 400)
        if not ok: continue
        me = [r[:] for r in mt]; extrap_lu(me, L, U)
        sig = (avi, pv, rt, elt, cpv, vpc, tuple(map(tuple, me)))
        if sig in seen: continue
        seen.add(sig); max_elt = max(max_elt, elt)
        if pv == "PVARP":
            m1 = [r[:] for r in mt]
            if band(m1, 0, 2, -cpv): q.append(((avi, "Idle", rt, elt, tpv, vpc), m1))
        if rt == "Retro":
            m1 = [r[:] for r in mt]
            if band(m1, 0, 4, -150):
                if pv == "PVARP": ar += 1; q.append(((avi, pv, "Idle", 0, cpv, vpc), m1))
                elif pv == "Idle" and avi == "Idle":
                    ne, npv = elt + 1, cpv
                    if anti_elt and ne >= 8: npv, ne = 500, 0
                    reset(m1, 1); q.append((("AVI", "Idle", "Idle", ne, npv, vpc), m1))
        if avi == "AVI":
            m1 = [r[:] for r in mt]
            if band(m1, 0, 1, -150) and band(m1, 3, 0, 400, S): q.append((("WaitURI", pv, rt, elt, cpv, vpc), m1))
            m2 = [r[:] for r in mt]
            if band(m2, 0, 1, -150) and band(m2, 0, 3, -400):
                vv.append((-rb(m2[0][3]), rb(m2[3][0]))); reset(m2, 2); reset(m2, 3)
                if retro: reset(m2, 4)
                q.append((("Idle", "PVARP", "Retro" if retro else "Idle", elt, cpv, vpc+1), m2))
        if avi == "WaitURI":
            m1 = [r[:] for r in mt]
            if band(m1, 0, 3, -400):
                vv.append((-rb(m1[0][3]), rb(m1[3][0]))); reset(m1, 2); reset(m1, 3)
                if retro: reset(m1, 4)
                q.append((("Idle", "PVARP", "Retro" if retro else "Idle", elt, cpv, vpc+1), m1))
    return max_elt, (min(a for a,_ in vv) if vv else None), ar, len(seen)

for lbl, args in [("open_loop",(100,False,False)), ("pmt_no_anti",(100,True,False)),
                  ("pmt_anti_elt",(100,True,True)), ("static_210ms",(210,True,False))]:
    print(f"2A {lbl:13s}: max_streak={check_pmt(*args)[0]} min_vv={check_pmt(*args)[1]} ar_blocks={check_pmt(*args)[2]} zones={check_pmt(*args)[3]}")

# --- Probe 2B: Therac-25 Class3 uint8 rollover ---
c3, hits = 0, []
for i in range(1, 1025):
    c3 = (c3 + 1) & 0xFF
    if c3 == 0: hits.append(i)
print("2B Class3 bypass cycles:", hits)

# --- Probe 2C: MDNumberpad silent DOT drop & AlarisGP chevron non-reversibility ---
def md_run(keys):
    dv, dot, dd, rej, pv = 0.0, False, 0, False, 0.0
    for k in keys:
        if isinstance(k, int):
            t = round(dv + k*(10**(-(dd+1))), 4) if (dot and dd < 2 and not ((dv>=100 and dd==0) or (dv>=10 and dd==1))) else (dv if dot else dv*10+k)
            if dot and dd < 2 and not ((dv>=100 and dd==0) or (dv>=10 and dd==1)): dd += 1
            if 0 <= t < 1200: dv = t
            else: rej = True
        elif k == "DOT" and not rej and not dot and dv < 100: dot = True
        elif k == "OK" and not rej:
            if dv >= 0.1: pv = dv
            else: rej = True
    return dv, rej, pv

trim = lambda x: 1200.0 if x > 1200 else (0.0 if x < 0 else x)
a_up = lambda v: trim(math.floor(round(v*10,6)+1)/10) if v<100 else (trim(float(math.floor(v+1))) if v<1000 else trim(float((math.floor(v/10)+1)*10)))
a_dn = lambda v: trim((math.ceil(round(v*10,6))-1)/10) if v<100 else (trim(float(math.ceil(v-1))) if v<1000 else trim(float((math.ceil(v/10)-1)*10)))
bad = [(t/10, a_up(t/10), a_dn(a_up(t/10))) for t in range(12000)
       if not ((t>=1000 and t%10) or (t>=10000 and t%100)) and a_up(t/10)<1200 and abs(a_dn(a_up(t/10))-t/10)>1e-6]
print("2C MDNumberpad [1,0,0,DOT,5,OK]:", md_run([1,0,0,"DOT",5,"OK"]), "| AlarisGP dn(up(v))!=v:", bad)
```

Observed output (2026-11-19):
```text
2A open_loop    : max_streak=0 min_vv=None ar_blocks=0 zones=2
2A pmt_no_anti  : max_streak=12 min_vv=400 ar_blocks=0 zones=48
2A pmt_anti_elt : max_streak=7 min_vv=400 ar_blocks=1 zones=35
2A static_210ms : max_streak=0 min_vv=None ar_blocks=1 zones=3
2B Class3 bypass cycles: [256, 512, 768, 1024]
2C MDNumberpad [1,0,0,DOT,5,OK]: (1005.0, False, 1005.0) | AlarisGP dn(up(v))!=v: [(99.9, 100.0, 99.0), (999.0, 1000.0, 990.0)]
```

## Revalidation

1. **UDBM encoding and extrapolation stability:** Against a newer `UPPAALModelChecker/UDBM` revision, diff `include/dbm/constraints.h` (`dbm_bound2raw`, `dbm_addRawRaw`, `dbm_negRaw`) and `src/dbm.c` (`dbm_close`, `dbm_extrapolateLUBounds`, `dbm_diagonalExtrapolateLUBounds`) to confirm bit-encoding invariants and LU-extrapolation preconditions remain unchanged.
2. **Closed-loop pacemaker verification:** Re-run `PM_all.xml` with `PM_all.q` in UPPAAL (or execute the inline Python DBM script in `< 0.2 s`) whenever pacemaker intervals (`TAVI`, `TLRI`, `TURI`, `TPVARP`, `TPVAB`, `TVRP`) or patient retrograde bounds (`Tretromin`, `Tretromax`) change; additionally verify whether `mlab-upenn/MedCPS` `assets/downloads/vhm/pacemaker_DDD.m:159` has corrected `pace_para{4,2}` to `pace_para{5,2}`.
3. **Infusion-pump HMI & alarm regression checks:** When modifying clinical number-entry or alarm state machines, discharge PVS refinement TCCs (`reference_model_th` -> `refined_model_th`), run exhaustive boundary scans for decimal-drop/reversibility violations across every display resolution threshold (`10`, `100`, `1000`), and verify via model checking that every newly arriving IEC 60601-1-8 High/Medium alarm condition preempts any active `Audio Paused` state and latches until explicit operator acknowledgment.
4. **Regulatory standard updates:** Check ISO/IEC catalogs for IEC 62304 Edition 2 (successor to `2006+Amd1:2015` addressing health software and Class A/B/C harmonization) and IEC 60601-1-8 Edition 3 updates before relying on clause-level safety-class downgrade arguments.
