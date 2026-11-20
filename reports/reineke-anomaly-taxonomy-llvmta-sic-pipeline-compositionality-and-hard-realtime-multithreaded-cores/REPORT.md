# Timing anomalies, timing compositionality and hardware-thread isolation: formal definitions, the composition rules they license, and how FlexPRET, SIC, Patmos, LLVMTA and platin encode interference

## Summary

- **Two different properties.** A *timing anomaly* (Lundqvist–Stenström 1999; Reineke et al. 2006) means that following the locally slower alternative does not bound the global time. *Timing compositionality* (Hahn–Jacobs–Reineke 2016, after Hahn–Reineke–Wilhelm) means that some monotone operator ⊕ satisfies `|τ| ≤ ⊕_j tc_j(τ)` for every trace τ. The usual linear operator `i + Σ_k p_k·n_k` with *direct-effect* penalties is broken by *amplification* (global increase > local increase), not by counter-intuitive anomalies. Reineke et al. 2006 exclude amplification from their definition, so "anomaly-free" in that sense does **not** imply "fully timing-compositional".
- **In-order cores amplify too.** Hahn–Jacobs–Reineke show amplification on a 5-stage in-order core with a 1-entry store buffer and a first-come-first-served bus that gives data accesses priority over fetches. Their per-benchmark sound bus penalties reach 3× the memory latency (out-of-order core with a store buffer). SIC (Hahn–Reineke 2018) enforces program-order bus access. It is provably free of counter-intuitive anomalies and has *constant-bounded* penalties: p for a p-cycle prolongation, 2·ml per data-cache miss and 5·ml per instruction-cache miss, where ml is the memory latency. It is about 6–7% slower than an in-order baseline. Rouizi et al. 2025 show that SIC still amplifies relative to the direct effect.
- **Hardware threads.** FlexPRET's "per-thread register files" are address partitions (`Cat(thread, addr)`) of one `SyncReadMem` of depth `32 * threads`, whose 2R/1W ports are time-multiplexed. Hard real-time threads (HRTTs) are isolated by an 8-slot table plus stalls and flushes that touch only same-thread instructions, at +35% LUTs and +10% FFs over 4-thread round-robin. Patmos is single-threaded and dual-issue: both slots share one register file, and any stall stalls the whole pipeline, so platin costs a basic block by summation.
- **Tools.** LLVMTA models round-robin bus blocking either *integrated* (it splits states per blocking cycle, up to `NumConcurrentCores * accLat`) or *compositionally* (`ub_base + ub_accesses × MaxBlockingPerAccess`, optionally as one joint ILP). platin has no co-runner model: interference enters only as per-request memory latency. Multicore response-time analysis (Altmeyer et al. 2015; Davis et al. 2018) *assumes* timing-compositional cores.
- **Grade.** Sequential composition `(b,a)+(b′,a′)`, closed by `τ(b,a) = b + w·a` and composed in parallel by `max_i τ`, is sound under conditions S1–S6 (F7): a compositional core or a base bound, an arbiter with a per-access wait w, bounded access time, complete access counts, no domino effects, and no unmodelled shared state. Bounds that depend on co-runners (`min(A_y, v·S)`) violate the lax interchange law, so with them barriers can lower bounds. In toy models only: `max` is unsound under sharing; `sum` is unsound under TDM and on an anomaly-prone core; and under round-robin arbitration the direct-effect bound fails only on the anomaly-prone core.

## Applicability

The papers define the properties, the hardware sources show how isolation is realized, and the analyzer sources show how interference becomes a bound. Papers were read in full (author copies or open-access versions) except where Boundaries says otherwise. Every DOI was verified against registry metadata: Crossref for the ACM, IEEE, Springer and Elsevier DOIs, and DataCite or the doi.org handle record for the Dagstuhl (`10.4230`) DOIs. dblp and landing pages were also checked where they could be read.

Pinned sources (HEAD on the observation date unless noted):
- Hardware: `pretis/flexpret@53af96f5beb22c1bb6a77f455b6ec73066885a12` (last commit 2024-11-07) and `t-crest/patmos@4c72814972c8e19d69c987e3b29d764efb6a7d8c` (last commit 2026-01-08).
- platin: the Patmos build script `t-crest/patmos-misc@c62a7eb93c966f1c0b8dc86e77f439e11a3cd56a` (`build.sh` 1243–1245: `clone_update ${GITHUB_BASEURL}/patmos-platin.git`) selects `t-crest/patmos-platin@f842eecc741a3caef9b7a2a6da2287eed35540ec`. `t-crest/platin@68257be7fd620da95c62051254753623743de9e7` is a separate multi-architecture variant whose HEAD merge is titled "Add FLEXPRET Support to Platin".
- LLVMTA: the paper names `https://gitlab.cs.uni-saarland.de/reineke/llvmta` as the canonical repository; it was not fetched. The code examined is the GitHub mirror `TU-Dortmund-CS-LS12-DAES-teaching/llvmta@c758822aa746aac6e5fa57356733a41a5b333ada`. Its HEAD commit is by a paper co-author, and the paper says the tool "was exposed to TU Dortmund University in 2020". Equality with GitLab is **unknown**.

Scope: source claims hold at exactly these SHAs. For FlexPRET, `flex = true` gives the slot scheduler with bypassing; `flex = false` gives fixed round-robin, and the non-bypassing datapath is used only if also `threads ≥ 4`. Paper numbers hold for the reported configurations. SIC results are for the paper's Verilog/LLVMTA model of an ARM subset; no public RTL was located. Toy-probe results hold only for the toy models in `support/`.

## Findings

### F1. Formal definitions of timing anomalies

Basis: normative (the paper definitions) + derived (the last column).

| Source | Model | Definition | Amplification counted? |
|---|---|---|---|
| Lundqvist–Stenström 1999, Def. 1 | The first instruction's latency is changed by +i or −d cycles; C is the change in total time | Anomaly ⇔ `C > i ∨ C < 0` (increase) or `C < −d ∨ C > 0` (decrease) | **Yes** (`C > i`) |
| LS 1999, Condition 1 | Resources are in-order (allocated in program order) or out-of-order | "If a processor only contains in-order resources no timing anomalies can occur." Reineke 2006 notes that Lundqvist's thesis later corrected this | — |
| Reineke et al. 2006, Defs. 1–7 | Cycle-level transition system `T=(S,R)`; locality constraints (convex predicates for micro-operations); retirement function ρ; abstract model `C(P)=(T,L,ρ)` | π is a local-worst-case path ⇔ for every l and every π′ with the same prefix, `|π|_l| ≥ |π′|_l|`. Anomaly ⇔ ∃P, σ, and a non-local-worst-case path π with `|π| > |π′|` for **all** local-worst-case paths π′ | **No**: excluded because such cases "do not pose problems for timing analysis" |
| Cassez–Hansen–Olesen 2012, Defs. 7, 10 | Concrete deterministic hardware; per-instruction completion time `Ctime` | `h ⊑time h′` ⇔ `∀j: Ctime(trace[j],h) ≤ Ctime(trace[j],h′)`. Anomaly-free for (P,d) ⇔ `∃W ∀h: h ⊑time W` (Lemma 11: every pair of states has a common upper bound) | Not addressed |
| Rouizi et al. 2025, Defs. 1–2 (after Binder et al.) | Pairs of in-order traces with causal regions | CI: a favourable variation `lat_s^α < lat_s^β` yet `ΔPre_α+ΔPost_α > ΔPre_β+ΔPost_β` at a causally linked event. AMP: the same with an unfavourable variation | **Yes**, as a separate class |

Reineke et al. 2006 name three classes (Sec. 4). **Scheduling** anomalies: only a pivot task's length differs, and greedy schedulers cannot prevent them. **Speculation** anomalies: the task set itself changes, as when a miss on the first speculative fetch lets the branch resolve before prefetches pollute the cache. **Cache** anomalies: with ColdFire 5307 pseudo-round-robin replacement, a hit can leave a worse cache state than a miss. The last two "can also happen on in-order architectures". LS 1999 also shows a miss penalty of 11 cycles against a nominal 8 (Anomaly 2), and a **domino effect** in which a 1-cycle initial delay costs k cycles over k iterations, so no constant bounds it (Anomaly 3).

### F2. Timing compositionality and which combination of bounds each property licenses

Basis: normative (HJR 2016 Def. 1 and Eqs. 2, 6–8; SIC Thms. IV.3–7) + derived (the "licensed" columns).

- **Decomposition (HJR Def. 1).** Functions `tc_j : T → W_j` with a monotone `⊕` such that `∀τ. |τ| ≤ ⊕_j tc_j(τ)`. Monotonicity of ⊕ gives `max_τ|τ| ≤ ⊕_j max_τ tc_j(τ) ≤ ⊕_j Analysis_j(p)`.
- **Naive operator (Eq. 2):** `i + mp·cm + bp·ba + rp·dr`, with direct-effect penalties (line reload, one access, refresh latency).
- **Remedies (Sec. 4).** (a) *Stall* the core while a bus access is blocked. (b) *Sound penalty*: a per-event penalty bp′ ≥ direct + indirect effect; impossible under domino effects. (c) *Compositional base bound*: `b + bp·ba`, where b maximizes `(Σ_e time_e·x_e) − bp·i` subject to `Σ_e blocked_e·x_e ≤ i`. This b absorbs all of the program's indirect effects.

| Core property | Sequential composition licensed | Interference composition licensed | Invalidated by |
|---|---|---|---|
| Anomaly-free (Reineke 2006 / Cassez 2012) | Local-worst-case pruning; analyze one most-pessimistic boundary state | Nothing by itself | Out-of-order resources, speculation, non-LRU replacement |
| Monotone progress order (SIC Thm. IV.3; Lemma IV.1: progress depends only on older instructions) | Thm. IV.4: more progress implies no later finish | Thm. IV.6: a p-cycle prolongation costs ≤ p. Thm. IV.7: data miss ≤ 2·ml, instruction miss ≤ 5·ml (write-through) | Speculation and fetch/data reordering (both removed in SIC); write-back caches need larger p |
| Fully timing-compositional | `+` | `i + Σ p_k·n_k` with direct penalties p_k | Any amplification, e.g. store buffer + FCFS bus (HJR Fig. 4) |
| Constant-bounded effects | `+` | `i + Σ p′_k·n_k` with p′_k ≥ direct + bounded indirect effect | Domino effects |
| Non-compositional | Integrated analysis | Base bound `b + bp·ba` | — (about 3% overestimation on average and up to 13%, versus semi-integrated analysis) |

This three-way classification is attributed to Wilhelm et al., TCAD 2009, by HJR 2016 and the SIC paper (not examined). SIC notes that full compositionality of the ARM7 was only conjectured.

### F3. Anomaly class × composition-rule matrix

Basis: derived from F1/F2 + execution (toy probes A/B; toy model only). ✗ means the rule can be unsound; "n.e." means not established.

| Mechanism | Local-worst-case pruning | `sum` bound on co-run makespan | `T + w·a`, direct w | Base bound `b + w·a` |
|---|---|---|---|---|
| Out-of-order allocation | ✗ (LS Anomaly 1; toy A) | ✗ (toy B, ooo/rr) | ✗ (toy B witness) | ✓ if b covers all interference amounts |
| Speculation / prefetch | ✗ (Reineke Fig. 2) | n.e. | ✗ (derived: a prolongation changes how far speculation runs) | ✓ |
| Non-LRU replacement | ✗ | n.e. | n.e. | ✓ |
| Store buffer + FCFS bus | ✗ per Hahn–Reineke; none found by Rouizi (≤4 instructions) | n.e. | ✗ (HJR Fig. 4) | ✓ |
| Domino effect | ✗ | ✗ (derived) | ✗ (no finite p) | ✓ per program |
| Stall-on-access core (toy "blocking") | ✓ (toy A in-order: 0/200,000) | ✓ for work-conserving arbitration; ✗ under TDM | ✓ for round-robin; under TDM only with TDM's w | ✓ (b = T) |

### F4. FlexPRET: how the register file, issue slots and scheduler are shared

Basis: source (`pretis/flexpret@53af96f5beb22c1bb6a77f455b6ec73066885a12`, quoted verbatim) + documentation (RTAS 2014).

`src/main/scala/Core/RegisterFile.scala`:

```scala
35:  val regDepth = 32 * threads
42:  private def regfileAddress(thread: UInt, addr: UInt): UInt = {
43:    Mux(thread <= (threads - 1).U, Cat(thread, addr), 0.U)
44:  }
50:  val regfile = SyncReadMem(regDepth, UInt(32.W))
81:    when(port.enable && port.addr =/= 0.U && port.thread <= (threads - 1).U) {
```

`Datapath.scala` 170–171 and 426 bind the ports to pipeline-stage thread IDs: `val regfile = Module(RegisterFile(readPorts = 2, writePorts = 1))`, `regfile.io.read(0).thread := if_reg_tid`, `regfile.io.write(0).thread := mem_reg_tid`. Derived: the thread index forms the high address bits and comes from the scheduler, so no thread can name another thread's registers. The "files" are one memory whose 2R/1W ports serve whichever thread is in fetch or writeback. RTAS 2014: "only a single dedicated block RAM is used for all register files".

`src/main/scala/Core/scheduler.scala`:

```scala
53:  def threadActive(i: UInt): Bool = { (io.thread_modes(i) === TMODE_HA) || (io.thread_modes(i) === TMODE_SA) }
58:  } else if(conf.roundRobin) {
61:    currentThread := Mux(currentThread < (conf.threads - 1).U, currentThread + 1.U, 0.U)
69:    val slotRequest = io.slots.map(i => i =/= SLOT_D)
70:    val slotGrantOH = RRArbiterMaskMethod(slotRequest, slotOH)
76:    val threadModeRequest = io.thread_modes.map(i => i === TMODE_SA)
86:      when(slotSelected =/= SLOT_S && threadActive(slotSelected(conf.threadBits-1,0))) {
89:      } .elsewhen(threadModeGrantValid) {
```

Encodings (`constants.scala` 130–147): 8 slots of 4 bits; `SLOT_T0..T7 = 0..7`, `SLOT_S = 14`, `SLOT_D = 15`; `TMODE_HA=0, HZ=1, SA=2, SZ=3`. Non-disabled slots are visited round-robin. A slot naming an active thread issues that thread. An `S` slot, or a slot whose thread sleeps, goes to the next active soft real-time thread (SRTT) in a second round-robin. `config.scala` 82: `val roundRobin = !flex`. Stalls preserve isolation (`control.scala` 255–257): `!(dec_stall && (io.if_tid === io.dec_tid)) && stall_count(io.if_tid) === 0.U`. Only a fetch from the *same* thread is killed, and its slot is not reassigned. All loads and multiplies stall the same thread's next fetch by one cycle (462–473, "Simplier than detecting load-use"), so their cost does not depend on what follows.

| Resource | Sharing | HRTT isolation | Residual coupling (derived) |
|---|---|---|---|
| Register file | Address-partitioned; ports time-multiplexed | Value (thread ID in the address) and timing (slots) | none observed |
| Fetch/issue | Slot table + SRTT round-robin | Exactly the prescribed slots ("scheduled at a constant rate") | SRTTs depend on HRTT sleep and wake, by design |
| ALU/multiplier/LSU | One instruction per stage | Follows from interleaving | Hazard cost depends on the thread's own frequency: a taken branch costs 3/2/1 thread cycles at frequency 1, 1/2, 1/3+ |
| `lock.scala` | One lock, "No fairness guarantee … Meant to be used as a spinlock" | **None** | Unbounded wait unless the software protocol bounds it |
| Bus (`loadstore.scala` 201) | `io.bus.addr := Cat(io.thread, ...)` | not examined | unknown |

Cost (RTAS 2014; Virtex-5 at 80 MHz): Base-4T-RR vs Base-1T is +5% LUTs and +42% FFs; FlexPRET-4T vs Base-4T-RR is +35% LUTs and +10% FFs; timing instructions add +79% FFs and +10% LUTs. Task τA takes E = 4·10⁵ cycles at frequency 1 (4 ms at 100 MHz) and 3.65·10⁵ thread cycles at 1/2 (7.3 ms). Halving the frequency multiplies latency by 7.3/4 = 1.825 rather than 2 (derived), because fewer hazard cycles are wasted.

### F5. SIC, in-order SMT and Patmos: what is shared, what is guaranteed

Basis: normative (SIC theorems) + source (Patmos) + documentation (papers) + derived.

| Design | Threads | Register file | Issue / functional units | Guarantee | Analysis enabled | Reported cost |
|---|---|---|---|---|---|---|
| FlexPRET (F4) | 1–8 | One address-partitioned memory | 1 issue per cycle, chosen by the slot table | HRTT timing independent of co-runners | Per-thread WCET from E_{1/X}; latency = E/(f·x) | +35% LUT / +10% FF over 4T-RR |
| SIC (Hahn–Reineke 2018) | 1 | Private | 5-stage in-order; no branch prediction or speculation; fetches after an instruction-cache miss wait until no older instruction can still access data memory | No CI anomalies (Thm. IV.5); constant-bounded penalties (Thms. IV.6–7) | Local-worst-case-only WCET analysis (about 4× faster); interference-free low-level analysis for multicore (about 30× faster than a base-bound analysis of the in-order core) | 6–7% slower at ml = 12; 60 MHz in both; 5046 vs 5037 LEs (+0.2%) on Cyclone IV |
| PTARM-like thread (SIC paper) | 4-way interleaved (one thread built) | Per thread, 16×32-bit | Memory stage usable every 4th cycle | Fixed latency per instruction | Trivially compositional | 65 MHz (+8.3%), 4294 LEs (−14.8%); one thread about 2× slower than SIC, total throughput about 2× SIC |
| In-order SMT (Mische et al. 2010) / MERASA | One hard real-time thread (HRT) plus others (SIC paper's description) | not examined | not examined | HRT "temporally isolated" (secondary) | Analyze the HRT like a single-thread core | not examined |
| Patmos | 1 (`hardware/config/default.xml` 5–6: `<pipeline dual="true" />`, `<cores count="1" />`) | `Mem(REG_COUNT, …)`, `2*PIPE_COUNT` read and `PIPE_COUNT` write ports (`RegisterFile.scala` 19, 23), shared by both slots | Dual issue: `val dual = decReg.instr_a(INSTR_WIDTH - 1) && decReg.instr_a(26, 22) =/= OPCODE_ALUL;` (`Decode.scala` 64). "multiplication only in first pipeline" (`Execute.scala` 167). Memory and stack operations decoded from the first slot only (`Decode.scala` 152–167) | Global stall: `val enable = memory.io.ena_out & icache.io.ena_out & !dcache.io.scIO.stall & execute.io.ena_out` (`Patmos.scala` 144) | Additive per-instruction cost in platin | not measured |

The SIC authors note that FlexPRET threads "configured to use several pipeline stages may exhibit the same timing anomalies as a regular pipelined processor". FlexPRET isolates threads *from each other*; it does not make any single thread anomaly-free. Rouizi et al. enumerated all SIC programs of up to 5 instructions (about 6,000 scenarios and more than 21 million trace pairs; 8 days on an i7-1185G7 with TLC 2.19). They found no CI anomalies, but AMP anomalies in both SIC and its unrestricted base core. They then prove that SIC is CI-free (Lemma 3) and that it is AMP-free whenever `ΔPre_α = 0` (Lemma 4). In their example, SIC's own 5·ml penalty is 15 cycles. So SIC is CI-free and compositional with *constant-bounded* penalties, not *direct-effect* penalties. One disagreement remains: Hahn–Reineke say conventional in-order pipelines "feature timing anomalies", but Rouizi et al.'s causal CI definition found none in the base core for programs of up to 4 instructions. Whether the definition or the length bound explains this is **unknown**.

Multicore Patmos (`hardware/src/main/scala/ocp/TdmArbiter.scala`) uses a fixed slot table: lines 19–20 `val period = cnt * (burstLen + 2)` and `val slotLen = burstLen + 2`; line 30 `(cntReg === (i*slotLen).U).asUInt`. The header comment (line 3) nevertheless says "Pseudo round robin arbitration". Derived: master i can start only in its own slot, so the wait before an access starts is at most `period − 1` cycles, independent of co-runners. This is MRTA Eq. 16 with v = 1.

### F6. How the analyzers encode interference from co-running code

Basis: source (LLVMTA mirror, platin) + normative/documentation (papers) + derived.

**LLVMTA** (`TU-Dortmund-CS-LS12-DAES-teaching/llvmta@c758822aa746aac6e5fa57356733a41a5b333ada`):
- `--ta-muarch-type` (`lib/Util/Options.cpp` 63–80) accepts `fixedlatency`, `pret` ("Single thread of a four-way thread-interleaved PRET pipeline"), `inorder`, `strictlyinorder` and `outoforder`. `--ta-shared-bus` (100–108) accepts `none` ("each access request is granted immediately") or `roundRobin`.
- `lib/LLVMPasses/DispatchMemory.cpp` 193–194 sets `blockingCyclingMemoryConfig.maxBlockingPerAccess = NumConcurrentCores * accLat;`, where accLat is the cache-line latency or `Latency + PerWordLatency`. Derived: k co-runners, each with one outstanding access, give round-robin blocking ≤ k·accLat. The formula is therefore exact if the option counts *other* cores; its help text does not settle this.
- *Integrated mode* (`include/Memory/BlockingCyclingMemory.h` 379–389): unless `SHAREDBUSBLOCKING` is selected, while `addedBlocking.getLb() < MaxBlockingPerAccess` each state splits into `longerBlocked` and `noLongerBlocked`. Every blocking amount is explored, which captures anomalies.
- *Compositional mode* (`include/LLVMPasses/DispatchPathAnalysis.h` 634–665): a separate ILP maximizes the number of accesses, and the bound is `res.get().ub + resUbAccesses.get().ub * MaxBlockingPerAccess`. With `--ta-compana-joint-ilp` a single ILP maximizes `time + MaxBlockingPerAccess·accesses`, so both terms come from the same path.
- `--ta-stall-on=busblocking,dramrefresh` (Options.cpp 147–162) implements the stalling remedy. `--ta-co-runner-sensitive` with `--ta-conc-acc-cyc-bounds` runs an arrival-curve fixed point (`doCoRunnerSensitivePathAnalysis`).

**platin.** In `t-crest/patmos-platin@f842eecc741a3caef9b7a2a6da2287eed35540ec`, `lib/arch/patmos.rb` 240–252 computes `cycles + (instr.bundled? ? 0 : 1) + flushes`, with `flushes = 3` for a call that has no delay slots. Edge costs (254–267) are 3 for a non-delayed return or `BRCF`, otherwise 2, and `num_slots` is 2. Caches are costed separately in the IPET (`lib/analysis/wca.rb`). Timing comes from a PML `MemoryConfig` (`read-latency`, `read-transfer-time`, write analogues, burst sizes; `t-crest/platin@68257be7fd620da95c62051254753623743de9e7` `lib/core/pml.yml` 478–515; `patmos-platin` `lib/core/pml.yml` 513–516 has the same fields and no arbitration field). `platin pml-config` can override them with `--gtime`, `--tdelay`, `--rdelay` and `--wdelay` (`t-crest/platin` `lib/tools/pml-config.rb` 67–78). Derived: there is no co-runner object. Interference can only enter as an inflated per-request latency, which is sound for Patmos TDM if the latency includes the `period − 1` wait. Patmos `wcet/config_de2_115.pml` is single-core timing (16-byte transfers, `read-transfer-time: 21`). The FlexPRET model in `t-crest/platin` (`lib/arch/flexpret.rb`) charges `cycles + cycle_cost(instr) + 1` (162–168) with every `cycle_cost` equal to 1 (196–252). It cites a "hifive1 simulator trace" (line 13) and the SiFive FE310 datasheet (line 197), registers as `"riscv32"` (305), and has no thread or slot parameter. Derived: it does not encode FlexPRET's frequency-dependent hazard costs.

**Multicore response-time analysis** (Altmeyer et al. 2015; Davis et al. 2018) computes `R_i = PD_i + I_PROC(i,x,R_i) + BUS(i,x,R_i)·d_main + I_DRAM(i,x,R_i)` (Eq. 32). For round-robin with v slots per core, `BUS = S_i^x(t) + Σ_{y≠x} min(A_n^y(t), v·S_i^x(t)) + 1` (Eq. 15). For TDMA with ℓ cores, `BUS = S_i^x(t) + ((ℓ−1)·v)·S_i^x(t) + 1` (Eq. 16). Fixed-priority, processor-priority and FIFO buses are Eqs. 12–14. The stated assumptions are timing-compositional cores, constant `d_main`, atomic non-split transactions, and one access at a time per core. Davis et al. add that separate preemption costs are "restricted to architectures without timing anomalies".

### F7. Restating composition rules as an algebraic timing grade

Basis: derived (statements and proofs given here) + execution (toy probes; toy model only).

A grade `g(P) = (b, a) ∈ G = ℕ × ℕ^k` pairs a base time b with access counts a_k for each shared resource k. Sequential composition is componentwise `+`, so `(G,+,0)` is a commutative monoid. For n threads under an arbiter with per-access wait `w_k`, define `τ(b,a) = b + Σ_k w_k·a_k`; then `T(P_1∥…∥P_n) ≤ max_i τ(g(P_i))`.

1. **Homomorphism.** `τ(g(P;Q)) = τ(g(P)) + τ(g(Q))`.
2. **Lax interchange.** Because `max(x+y, z+u) ≤ max(x,z) + max(y,u)`, the bound for `(P;P′)∥(Q;Q′)` is at most the bound for `(P∥Q);(P′∥Q′)`. With a per-access charge, adding a barrier never lowers the bound.
3. **Co-runner-sensitive terms break it.** `w·min(a_P, a_Q)` (the shape of MRTA's `min(A_y, v·S)`) is superadditive: `min(x+y, z+u) ≥ min(x,z) + min(y,u)`. With `a_P=2, a_P′=0, a_Q=0, a_Q′=2`, the unsynchronized composition is charged 2 interfering accesses and the barrier version 0. A barrier can therefore lower the bound, correctly reflecting the overlaps it rules out. The cost is that the bound is no longer a function of each thread's own grade.

| Id | Side condition | Source | Failure without it |
|---|---|---|---|
| S1 | Core compositional with penalty w, **or** b is a base bound over all interference amounts | HJR Secs. 3–4; SIC Thm. IV.6 | Toy witness: `C=9 > 4+2·2` (anomaly-prone core) |
| S2 | Arbiter with a per-access wait: RR `w=(n−1)·d`; TDM slot table: wait before start ≤ `period−1` | MRTA Eqs. 15–16; `TdmArbiter.scala` 19–30 | Toy fixed priority: 3141/40,000 violations of the RR bound |
| S3 | Bounded access duration (constant `d_main`; refresh modelled separately) | MRTA Sec. 3.1, Eq. 31 | Needs its own term |
| S4 | a counts every access, including preemption reloads (`MD_k + γ`) | MRTA Eq. 23 | Unsound (derived) |
| S5 | No domino effects when a constant penalty is used | LS Anomaly 3; HJR 4.2 | No finite w (derived) |
| S6 | No unmodelled shared state (locks, I/O) | FlexPRET `lock.scala` | Not covered by any slot grade |

Special cases. Whole-pipeline interleaving at frequency 1/X (FlexPRET HRTT, PTARM) is the grade `τ(E) = X·E_{1/X}`: independent of co-runners and satisfying interchange, but E itself depends on X. `sum` (`T(P∥Q) ≤ T(P)+T(Q)`) holds for work-conserving arbitration on a compositional core and fails under TDM and on anomaly-prone cores (toy B).

### F8. Executable toy probes (support/)

Basis: execution (toy models of greedy two-resource scheduling and of two threads sharing one unit; **not** FlexPRET, SIC, Patmos or any real core). Host: x86_64 Linux VM (Intel Xeon at 2.60 GHz), CPython 3.13.15, single-threaded, standard library only.

- `python3 support/probe_anomaly.py 1 200000` (4.9 s): on random programs of 3–6 tasks with pivot latency 1 vs 3, the greedy (out-of-order) scheduler gave 216 counter-intuitive and 215 amplifying cases; strict in-order issue gave 0 and 0. Smallest witness: resources `[0,1,1,1,0]`, deps `[[],[],[0],[1],[3]]`, latencies `[h,2,1,1,1]`. Makespan is 5 at h=1 and 4 at h=3 (in-order: 5 and 6). PRNG initializer 2 gives 220, 214, 0, 0. Derived: in-order issue computes `start_i = max(start_{i−1}, free(res_i), max finish(deps))`. This is a (max,+) term in which each latency occurs at most once on any path, so time is monotone and 1-Lipschitz in every latency (LS Condition 1 for this toy).
- `python3 support/probe_composition.py 7 20000` (11.6 s). Counts are violations over 40,000 thread instances; `sum` and independence are counted per trial:

| Core / arbitration | `C≤T` | `T+a(n−1)d` | `T+a(nd−1)` | `sum` | independence |
|---|---|---|---|---|---|
| blocking / RR | 23534 | **0** | 0 | **0** | 8947 |
| blocking / fixed priority | 20019 | 3141 | 1710 | 0 | 5299 |
| blocking / TDM | 31433 | 3790 | **0** | 8259 | **0** |
| blocking / interleave (`C≤2T`: 0) | 38747 | 30120 | 12576 | 16966 | **0** |
| ooo / RR | 24797 | **25** | 0 | **21** | 7258 |
| ooo / TDM | 30670 | 2145 | **1** | 11053 | **0** |

PRNG initializer 11 gives the same pattern (ooo/RR: 21 and 28; ooo/TDM: 2).
- `python3 support/probe_witness.py 7 200000`: thread 0 is `S; S(dep 0)`, thread 1 is `P; S(dep 0); S; P(dep 2)`, and T_iso = 4 for both. Under RR, the blocked request at t=0 lets the older `S(dep 0)` take thread 1's port at t=2. That delays the producer of the last `P`, so C₁ = 9 > `T + a(n−1)d` = 8 = `T₀ + T₁`: an indirect effect of the HJR kind.

### F9. Performance and resource matrix (L1–L6)

| Level | Values (measured / cited / derived) | Not measured |
|---|---|---|
| L1 authoring | FlexPRET `RegisterFile.scala` 85 lines, `scheduler.scala` 98; platin `flexpret.rb` 307 (`wc -l`, measured). SIC proofs are "lengthy case distinctions" | person-months, repair cost |
| L2 build | LLVMTA README: "requires a lot or RAM"; use the "lowRes" configuration with 16 GB. platin needs Ruby and lpsolve | build times |
| L3 analysis | Base bound: ×3.4–16.5 runtime (geometric mean 8.6) and ×2.1–7.5 memory (4.8); full run < 7.5 h and 9.5 GiB at 3.3 GHz (HJR). SIC analysis about 4× faster (single core) and about 30× faster than a base-bound analysis (multicore). TLC detection: 16 h for 4 instructions, 8 days for 5 (Rouizi). Toy probes: 4.9 s and 11.6 s (measured) | LLVMTA and platin per benchmark |
| L4 timing/throughput | SIC −6–7%. PTARM thread about 2× slower, about 2× aggregate throughput. FlexPRET τA 4 → 7.3 ms. LS 1999 code modifications < 27% pessimism. Base bound about +3% on average, up to +13%. Sound penalty up to 3·ml | Patmos dual-issue gain; FlexPRET WCETs |
| L5 proof checking | SIC proofs are on paper; Rouizi uses bounded model checking | checker speed |
| L6 footprint | LEs: 5046 SIC, 5037 in-order, 4294 PTARM-like (a 4-thread PTARM needs ≥1536 more). FlexPRET registers: 8 threads × 32 × 4 B = 1 KiB in one block RAM (derived). Patmos register file 4R/2W when dual-issue (derived). HJR peak 9.5 GiB | analyzer RSS |

### F10. Comprehensibility (C1) and model simplicity (C2)

- **C1.** `b + w·a` has three numbers, side conditions S1–S6, and a per-event explanation ("waited for at most n−1 accesses"). A base bound is equally sound but opaque, because b absorbs indirect effects that no single access explains. SIC's Lemma IV.1 is a *local* invariant that a human can check and that implies the global properties. Out-of-order anomalies show up only by comparing two whole traces (the toy witness needs a 9-cycle side-by-side), so diagnosis is non-local. FlexPRET's per-thread table (E_1, E_{1/2}, E_{1/3+}) is auditable, but the lock and the soft threads sit outside it.
- **C2.** Stalling, sound penalties and base bounds are one schema, `|τ| ≤ b + Σ p_k·n_k`, that differs only in where indirect effects are paid: hardware makes them 0, p_k pays per event, b pays per program. Round-robin, TDM and interleaving are one wait function `w(n)`; interleaving applies it to every instruction. One ratio `ρ = Δglobal/Δlocal` covers both anomaly kinds: no anomaly is `0 ≤ ρ ≤ 1`, counter-intuitive is `ρ < 0`, amplification is `ρ > 1`. Reineke 2006 and Cassez 2012 constrain only `ρ ≥ 0`. Realization quirks that should not enter the model: data-over-fetch priority, store-buffer depth, pseudo-round-robin replacement, FlexPRET's fixed 2-cycle loads.

### F11. Validation coverage (V1–V4)

| Level | Exists | Not found |
|---|---|---|
| V1 spec adequacy | Cassez et al. find examples where earlier definitions "do not align with common observations". Rouizi et al. test two definitions by exhaustive bounded enumeration. Toy A shows the definitions are non-vacuous | Mutation testing of composition operators |
| V2 checker/lowering | platin `--enable-trace-analysis`; `--use-trace-facts` is "unsafe bounds, only for benchmarking" (`wcet/analyse_wcet.sh`). LLVMTA analyzes machine IR "rather than on the binary", with "a made-up address mapping" | Differential fuzzing of LLVMTA or platin |
| V3 silicon | FPGA runs: FlexPRET (Virtex-5) and SIC (Cyclone IV, cycles compared against static bounds); Patmos FPGA board configurations | Post-silicon isolation testing |
| V4 plant/human | FlexPRET avionics study is simulation only | HIL or human studies |

## Boundaries

- **Not examined (full text):** Hahn–Reineke–Wilhelm, SIGBED Review 12(1) (DOI 10.1145/2752801.2752805; its definition is reported only via HJR 2016's restatement); Gebhard, WCET 2010 (DOI 10.4230/OASIcs.WCET.2010.1); Mische et al., ARCS 2010 (DOI 10.1007/978-3-642-11950-7_2) and the CarCore sources, so the in-order SMT row is secondary; Paolieri et al., ISCA 2009 (DOI 10.1145/1555754.1555764; abstract only); the SIC journal version (DOI 10.1007/s11241-019-09341-z); T-CREST, JSA 2015 (DOI 10.1016/j.sysarc.2015.04.002); Wilhelm et al., TCAD 2009 (DOI 10.1109/TCAD.2009.2013287); Binder et al. 2020–2022; Kirner et al. 2009.
- **Unknown:** whether the LLVMTA mirror equals the GitLab tree; whether `NumConcurrentCores` counts co-runners or all cores; FlexPRET bus arbitration; whether SIC RTL is public; the cause of the CI disagreement in F5.
- **Known not to apply:** anomaly-freedom does not imply direct-effect compositionality (SIC, per Rouizi). HRTT isolation does not make a thread anomaly-free. The max of isolated times is not a sound parallel bound once threads can wait on a shared resource. platin's FlexPRET model does not model interleaving.
- **Unsupported:** PML has no co-runner or arbitration object. LLVMTA buses are `none` and `roundRobin` only.
- **Attractive but unestablished:** that the toy counts transfer to real cores; that platin with an inflated latency is tight; that the grades are precise (only soundness is argued).

## Evidence

All evidence was acquired on 2026-11-20 (UTC).
- `pretis/flexpret@53af96f5beb22c1bb6a77f455b6ec73066885a12`, `src/main/scala/Core/`: `RegisterFile.scala` 31–85; `scheduler.scala` 17–98; `Datapath.scala` 50–51, 143–178, 425–429; `control.scala` 231–285, 445–483, 559–565; `config.scala` 39–89; `constants.scala` 130–149; `lock.scala`; `loadstore.scala` 136–140, 198–204; plus `README.md`.
- `t-crest/patmos@4c72814972c8e19d69c987e3b29d764efb6a7d8c`: `hardware/src/main/scala/patmos/{RegisterFile.scala 15–56, Decode.scala 60–70 and 152–170, Execute.scala 153–190, Patmos.scala 136–148}`; `hardware/src/main/scala/ocp/TdmArbiter.scala`; `hardware/config/default.xml` 5–6; `wcet/{README.md, Makefile, analyse_wcet.sh, config_de2_115.pml}`.
- `t-crest/patmos-platin@f842eecc741a3caef9b7a2a6da2287eed35540ec`: `lib/arch/patmos.rb` 126–267; `lib/analysis/wca.rb`. `t-crest/platin@68257be7fd620da95c62051254753623743de9e7`: `lib/arch/flexpret.rb`; `lib/core/pml.yml` 475–516; `lib/tools/pml-config.rb` 55–170. `t-crest/patmos-misc@c62a7eb93c966f1c0b8dc86e77f439e11a3cd56a`: `build.sh` 744–750, 1243–1245.
- `TU-Dortmund-CS-LS12-DAES-teaching/llvmta@c758822aa746aac6e5fa57356733a41a5b333ada`: `include/Util/Options.h` 44–158 and 266–298 and 524–545; `lib/Util/Options.cpp` 63–168 and 557–567; `lib/LLVMPasses/DispatchMemory.cpp` 175–197; `include/Memory/BlockingCyclingMemory.h` 41–62 and 340–430; `include/LLVMPasses/DispatchPathAnalysis.h` 634–665 and 840–860; `README.md`.
- `patmos-platin` `lib/core/pml.yml` 505–520 was also checked.
- Papers and the parts relied on: LS 1999 (Def. 1, Condition 1, Anomalies 1–3, Sec. 4); Reineke 2006 (Defs. 1–7, Sec. 4); Cassez 2012 (Defs. 7, 10, 12, 15; Lemma 11); HJR 2016 (Def. 1, Eqs. 2–8, Sec. 3.1, Table 3, Sec. 5); SIC 2018 (Fig. 5, Lemmas IV.1–2, Thms. IV.3–7, Table I, Sec. VI); Rouizi 2025 (Defs. 1–2, Sec. 5, Lemmas 3–4); Zimmer 2014 (Secs. III–IV); Altmeyer 2015 (Eqs. 11–32); Davis 2018 (Secs. 2–3); Hahn 2022 (Secs. 3–6). Every DOI cited here, including those listed under Boundaries, was checked against Crossref (ACM, IEEE, Springer and Elsevier) or DataCite and the doi.org handle record (Dagstuhl `10.4230`), in addition to dblp and the readable landing pages.
- Execution: commands in F8. Outputs: `support/probe_anomaly.out`, `support/probe_anomaly_prng2.out`, `support/probe_composition.out`, `support/probe_composition_prng11.out`, `support/probe_witness.out`. Scripts: `support/probe_{anomaly,composition,witness}.py`.

## Revalidation

- **FlexPRET:** diff `src/main/scala/Core/{RegisterFile,scheduler,control}.scala` against the pin. The findings hold while `Cat(thread, addr)`, the `SLOT_S`/sleeping-slot delegation and the `io.if_tid === io.dec_tid` stall test remain.
- **Patmos and platin:** check the single `enable` in `Patmos.scala`, the pure sum in `patmos-platin/lib/arch/patmos.rb#path_wcet`, and `period`/`slotLen` in `TdmArbiter.scala`.
- **LLVMTA:** grep for `maxBlockingPerAccess =` and `SHAREDBUSBLOCKING` (preferably in the GitLab tree) and compare with the cited lines.
- **Toy claims:** `python3 support/probe_composition.py 7 20000` and `python3 support/probe_witness.py 7 200000` on CPython 3.8+ must reproduce `support/*.out` exactly. That re-establishes only the toy facts.
- **Theory:** re-read HJR Eqs. 6–8, SIC Thms. IV.6–7 and Rouizi Lemmas 3–4. Revisit F2 and F5 if a newer SIC version claims direct-effect compositionality.
