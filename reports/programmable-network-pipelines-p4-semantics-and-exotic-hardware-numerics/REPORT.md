# Programmable Network Pipelines, P4 Semantics, and Exotic Hardware Numerics

## Summary

Two hardware-constrained domains invalidate core assumptions of imperative compiler IRs (C, Rust, LLVM IR) and IEEE 754 floating-point optimizers:

1. **Feed-forward programmable switch pipelines (`RMT` / `PISA`, `P4_16`, `Petr4`, `P4v`, `Domino`, `Chipmunk`)**: Sustaining line-rate packet processing at ~1 GHz mandates a strictly feed-forward, bounded-depth DAG (FSM parser -> fixed-width Packet Header Vector (`PHV`) -> fixed match-action stages -> deparser) with no general backward jumps, heap, or pointers. Any per-packet stateful update to switch register $R[k]$ must close read-compute-write in **one clock cycle** inside a stage Stateful ALU (`SALU`). `P4_16` itself has subtle semantics—unspecified reads of invalid headers, **valid-sibling field havoc** upon writing an invalid `header_union` member, and left-to-right **copy-in / copy-out** calling semantics isolating opaque `extern` side effects—requiring mechanized operational semantics (`Petr4`), control-plane-assumed SMT verification (`P4v`), and Tarjan-SCC partitioning (`Domino`) or CEGIS bitvector synthesis (`Chipmunk`).
2. **Post-IEEE-754 exotic hardware numerics (`FP8 E4M3FN`/`E5M2`, `IEEE P3109 v4.1`, `OCP MXFP8`/`MXFP6`/`MXFP4`, `Posit`/`Quire`, hardware Stochastic Rounding, and DSP saturation)**:
   - **Narrow floats**: OCP `E4M3` (`E4M3FN`) omits infinities (`0x7F`/`0xFF` = `NaN`, max finite `448`, bias 7), while **IEEE P3109 Interim Report v4.1** omits `-0.0` (`0x80` = single `NaN`, signed bias $2^{K-P-1}$, `Binary8p4sf` max finite `240`). Standard IEEE-754 rewrites (`isinf`, `x - x -> 0`, `(2.0 * x) * 0.5 -> x`, and bitwise sign-flip negation `x ^ 0x80`) are **actively unsound** (`0x00 ^ 0x80` maps `+0.0` to `-0.0` in OCP `E4M3FN` but corrupts `+0.0` into `NaN` in `P3109 Binary8p4sf` and `E4M3FNUZ`).
   - **Microscaling (`OCP MX v1.0`)**: Sharing one 8-bit `E8M0` (also called `UE8M0`) exponent across **32 elements** (`MXFP8`/`MXFP6`/`MXFP4`/`MXINT8`) destroys disjoint element mutability (`&mut block[i]`): mutating one element either rescales `E8M0` and silently flushes up to 31 unmodified siblings to `0.0`, or clamps the written element; `E8M0 = 0xFF` poisons all 32 elements to `NaN`.
   - **Exact super-accumulators vs probabilistic rounding**: **Posit Standard (2022) `Quire`** fixed-point accumulators ($16n$ bits: 128/256/512 bits for `posit8/16/32`) restore **true associativity** across up to $2^{31}$ exact products before final rounding. Conversely, hardware **Stochastic Rounding (`SR`)** consumes PRNG entropy: illegal pure CSE (`let y = sr(x); y + y`) **doubles variance** ($4\sigma^2$ vs $2\sigma^2$), corrupts output support, and makes nonlinear products `sr(x) * sr(x)` **strictly biased** ($\mathbb{E} = x^2 + \operatorname{Var}(\text{SR}(x))$).

Every encoding, rewrite counterexample, `MXFP4` sibling drift, `Quire16` permutation invariance, exhaustive `SR` CSE proof, DSP `Q1.15` corner case, `P4_16` `header_union` havoc / copy-in-copy-out divergence, and `Domino` Tarjan-SCC SALU check is reproduced by `support/verify_p4_salu_and_exotic_numerics.py`.

---

## Applicability

This report applies to compilers, static analyzers, and formal verifiers targeting:

1. **Feed-forward programmable network switch data planes**: Reference `RMT` (Bosshart et al. 2013), `P4_16` (`p4lang/p4-spec` v1.2.5+HEAD), `Petr4` formal semantics and Coq `P4light` (`verified-network-toolchain/petr4`; Doenges et al. POPL 2021), `P4v` (Liu et al. SIGCOMM 2018), `Domino` (`packet-transactions/domino-compiler`; Sivaraman et al. SIGCOMM 2016), and `Chipmunk` (`chipmunk-project/chipmunk`; Gao et al. SIGCOMM 2020).
2. **Post-IEEE-754 ML, scientific, and DSP hardware arithmetic**: OCP/Micikevicius `FP8` (`E4M3FN`/`E5M2`), **OCP Microscaling Formats (MX) Specification v1.0** (`microsoft/microxcaling`), **IEEE SA WG P3109 Interim Report v4.1** (2026-09-14, `P3109/Public`), **Standard for Posit Arithmetic (2022)** (`stillwater-sc/universal` v5.18.0), stochastic rounding theory and hardware ISAs (Croci et al. 2022; P3109 v4.1; Graphcore IPU; NVIDIA Blackwell PTX 8.7+ `cvt.rs`), and saturating DSP fixed-point arithmetic (`ISO/IEC TR 18037`, LLVM `llvm.sadd.sat` / `llvm.smul.fix.sat`, ARM `SQDMULH`/`VQADD`).

### Relationship to Adjacent Reference Packages

This report cross-references—and intentionally does not duplicate—three existing packages in this corpus:

- `rust-floating-point-semantics-llvm-lowering-and-isa-behavior`: Normative baseline for Rust `f32`/`f64` IEEE 754-2019 semantics, NaN payloads, LLVM lowering, and x86-64/AArch64/i386 scalar ISA rules. Use *this* report for non-IEEE-754 narrow/block formats (`E4M3FN`, `P3109`, `MXFP4/6/8`), `Posit`/`Quire`, and stochastic rounding where those IEEE-754 scalar assumptions break.
- `lean-ieee754-floatspec-cryptography-and-constant-time`: Covers Lean 4 IEEE 754 mechanization (`FloatSpec`, `fp-lean`). Use *this* report for generalizing mechanized arithmetic to `IEEE P3109`'s parameterized `Binary{K, P, Σ, ∆}`, atomic block-scaled types, and probabilistic rounding effects.
- `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`: Covers ordered SIMD reductions and `reassoc` certificates for non-associative IEEE 754 arithmetic. Use *this* report for exact associative `Posit` `Quire` monoids and non-associative saturating DSP integers.

### Version and Dialect Distinctions

- **IEEE P3109 Interim Report v4.1 (2026-09-14)** is an unapproved draft subject to change before balloting. Its signed format encoding (`0x80` = single `NaN`, no `-0.0`, bias $2^{K-P-1}$) differs from deployed **OCP FP8 / MX v1.0** (`0x7F`/`0xFF` = `NaN`, `-0.0` at `0x80`, bias 7 for `E4M3`) and matches **AGQ** (`AMD gfx940`/Graphcore `FNUZ`) on signed special values. Both conventions are documented side-by-side below.
- **`P4_16` (`p4lang/p4-spec`)**: Pinned at commit `0370191bea5d26cd17c3ed25a6849d2df306b56b` (v1.2.5 from October 2024 plus subsequent commits through September 2026, including fixed-width unsigned `bit<W>` `/` and `%`). Historical ambiguities analyzed by `Petr4` (POPL 2021, against P4_16 v1.2.0–v1.2.2) are distinguished from resolved text in v1.2.5+.
- **Posit Standard (2022)** fixes $es = 2$ and quire width $16n$ bits; generalized libraries (`stillwater-sc/universal`) also parameterize arbitrary $(n, es)$ and variable quire guard capacities.

---

## Findings

### 1. Feed-Forward Programmable Switch Pipelines (`RMT` / `PISA`)

Basis: normative + documentation + derived

Terabit programmable switching ASICs derived from **Reconfigurable Match Tables (`RMT`)** (Bosshart et al., SIGCOMM 2013) and commercial `PISA` architectures (e.g., Intel Tofino) sustain deterministic line rate by removing dynamic memory, pointers, caches, and arbitrary control-flow loops from the hardware data path:

| Architectural Dimension | General-Purpose CPU (`eBPF`/DPDK) | Reference `RMT` (Bosshart et al. 2013) | Typical `PISA` / Tofino Pipeline | Compiler / Verification Constraint |
|---|---|---|---|---|
| **Clock & Throughput** | Variable IPC, cache stalls, branch mispredicts | 1 GHz, 640 Gbps aggregate (e.g., 64 × 10 Gb/s), 1 pkt/cycle | ~1 GHz, multi-Tbps across pipes, fixed ns/stage | Zero pipeline stalls; exact deterministic WCET |
| **Control Topology** | Arbitrary CFGs, backward loops, recursion | **Strictly feed-forward DAG**: 32 match-action stages | Strictly feed-forward DAG (~12–20 physical stages) | No general loops in MAU; recirculation halves port bandwidth |
| **Working Storage** | Unbounded heap, call stack, raw pointers | Fixed **4096-bit (512 B) `PHV`** (Packet Header Vector) | Fixed 8/16/32-bit PHV containers passed stage-to-stage | Zero heap/pointers; hard-capped PHV liveness budget |
| **Lookup & Action** | Sequential load/store + scalar ALU | Per-stage SRAM (exact) + TCAM (ternary/LPM) + VLIW ALUs | Match crossbars + SRAM/TCAM + VLIW + single-cycle `SALU` | Independent actions run in parallel; RAW chains increment stage |
| **Wire Framing** | Pointer arithmetic over `sk_buff`/`mbuf` | Programmable FSM **Parser** -> PHV -> MAU -> **Deparser** | TCAM-driven bounded FSM Parser + Deparser | Parser cycles require bounded extraction / header stacks |

**Why C / LLVM IR fails on RMT/PISA**: LLVM IR hardcodes flat byte-addressed pointer memory (`alloca`, `getelementptr`, arbitrary aliasing), arbitrary CFG back-edges, and stack spilling. In an RMT pipeline, stage $s$ processes packet $p_t$ on the exact cycle stage $s-1$ processes $p_{t+1}$; backward edges physically collide with trailing packets, and exceeding PHV width, stage count, or SRAM/TCAM banks triggers hard compile-time failure rather than cache spills. Sound switch languages therefore require: (1) **header-validity typestates** banning unextracted header dereferences, (2) **bounded-depth DAG control types** forbidding unbounded recursion/loops, and (3) **stage-resource and single-cycle state-update effect checks**.

---

### 2. `P4_16` Semantics, Underspecification Traps, and Formal Verification (`Petr4` & `P4v`)

Basis: normative + source + execution + derived

Even `P4_16` (`p4lang/p4-spec` @ `0370191bea...`, `p4-16/spec/P4-16-spec.adoc`) exhibits non-obvious operational traps that diverge from conventional imperative languages and caused concrete bugs in `p4c`.

#### 2.1 Unspecified Values, Invalid Headers, and `header_union` Sibling Havoc

Per `P4-16-spec.adoc` L5156–L5271 (*"Reading uninitialized values and writing fields of invalid headers"*):

- **Value-level nondeterminism ("unspecified value"), not C UB**: Reading an uninitialized variable, an uninitialized field of a valid header, any field of an invalid header, or an out-of-range header stack element yields an **unspecified value** that may vary across repeated reads; `stack[oob].isValid()` yields an undefined boolean that need not be consistent across calls (L5186–L5196). Unlike C undefined behavior, unspecified values do *not* license arbitrary miscompilation—unspecified `enum`/`error` values must still match `default`/`_`, all-don't-care `ternary`, and 0-prefix `lpm` keys (L5198–L5209).
- **Standalone invalid write (no-op) vs `header_union` invalid write (valid-sibling havoc)**:
  - Writing to a field of a currently invalid standalone header or out-of-range stack element **must not modify any currently defined state** and keeps the header invalid (L5220–L5234).
  - **Hardware overlay hazard (L5211–L5218)**: Inside a `header_union u1` where `u1.h1` is valid and `u1.h2` is invalid, **attempting to write a field of invalid `u1.h2` may corrupt any or all fields of valid sibling `u1.h1`**, while leaving every member's validity bit unchanged (`u1.h1.isValid() == true`, `u1.h2.isValid() == false`).
- **Coq mechanization (`verified-network-toolchain/petr4` @ `9508676128...`, `coq/lib/P4light/Semantics/Semantics.v`)**:
  - Models every bit as `option bool` (`Sval = @ValueBase (option bool)`), parameterized by oracle `read_one_bit : option bool -> bool -> Prop` (L40, L405, L1032).
  - `write_header_field` (L843–L859) separates valid (`Some true`), invalid (`Some false`), and out-of-bounds (`None`) headers.
  - `havoc_header` and `update_union_member` (L889–L913) map `uninit_sval_of_sval None` over every sibling's fields on invalid-member union updates, faithfully encoding L5211–L5218 (verified in probe Part 4a).

#### 2.2 Call by Copy-In / Copy-Out and `extern` Opacity

Per `P4-16-spec.adoc` L1454–L1649, all P4 parsers, controls, actions, functions, and `extern` methods use **copy-in / copy-out** parameter passing with strict 6-step evaluation (L1565–L1581):

1. Evaluate arguments **left to right**.
2. Supply defaults for omitted parameters.
3. For each `out` / `inout` argument, **capture its resolved l-value location immediately** (before later arguments execute—so `f(s[a].z, g(a))` copies back into `s[old_a].z`, not `s[new_a].z`, L1599–L1614).
4. Copy argument values into fresh non-aliased temporaries. Pure `out` parameters recursively initialize `header`/`header_union`/header-stack members to invalid (and stack `nextIndex` to 0) while leaving scalar `bit<W>` uninitialized (L1503–L1518).
5. Invoke the callee on the non-aliased temporaries.
6. On return, copy `out` / `inout` temporaries **left to right** into the l-values saved in Step 3.

Concrete aliasing divergence (`P4-16-spec.adoc` L1552–L1592; probe Part 4b):

```p4
extern void f(inout bit<8> x, in bit<8> y); // x = x + y
extern bit<8> g(inout bit<8> z);            // z = z + 10; return z
bit<8> a = 5;
f(a, g(a));
// P4_16 copy-in/copy-out (Petr4 Semantics.v L1008-L1086):
//   tmp1 = a (5); tmp2 = g(a) (a:=15, tmp2=15); f(tmp1, tmp2) => tmp1=20; a = tmp1 => a == 20
// Naive call-by-reference:
//   g(a) mutates a:=15 first; f(&a, 15) reads mutated a => a = 15 + 15 == 30
```

**Why `P4_16` mandates copy-in/copy-out (L1620–L1649)**: Directionless `extern` objects (registers, meters, checksum units) are passed by reference and hold opaque hardware state. Copy-in/copy-out prevents `extern`s from capturing pointers into P4 variables, confining their effects to `out`/`inout` parameters at call boundaries, while eliminating intra-callee parameter aliasing on architectures without pointer registers. Because `extern` internals remain unspecified by `P4_16`, formal tools must parameterize semantics by an explicit target/extern model.

#### 2.3 Formal Verification Frameworks (`Petr4` and `P4v`)

| System | Formal Mechanism | Proven Guarantees | Architecture / Control-Plane Model | Empirical Results & Discovered Defects |
|---|---|---|---|---|
| **`Petr4`** (Doenges et al., POPL 2021; Coq `Poulet4` + OCaml) | Stratified core calculus + executable definitional interpreter (`lib/eval.ml` -> Coq `Poulet4.Interpreter`) + Coq `P4light`/`P4cub` | **Type soundness & termination** via structural induction on the stratified type system (parser-free fragment) | Modular **target functor** (V1Model, eBPF) + bit-level oracle `read_one_bit` | 792/792 `p4c` parser tests, 782/792 typechecker tests, 95/121 `p4c` STF tests (+ 40 custom STF tests); found **12 `p4c` bugs** (Fig. 23) & **8 `P4_16` spec ambiguities** (Fig. 24) |
| **`P4v`** (Liu et al., SIGCOMM 2018) | P4 -> Dijkstra's **Guarded Command Language (`GCL`)** -> weakest preconditions -> **Z3** SMT | Automated proof of header-validity safety, parser/deparser consistency, and assertions | Explicit **control-plane interface assumptions** (concise first-order table invariants) prune spurious counterexamples | Verified industrial **`switch.p4`** in **< 3 minutes** with a few hundred lines of control-plane annotations |

Key defects uncovered by `Petr4` (POPL 2021, Figs. 23–24):
- **Nominal/structural split & tuple bleed**: `p4c` typed controls structurally in architectures and nominally elsewhere, and gave list expressions tuple types—permitting illegal tuple-to-struct assignment.
- **Grammar ambiguity**: `TYPE TYPE_IDENTIFIER` produced a shift/reduce conflict between function return types and `type` (newtype) declarations; empty annotation lists were ambiguous between expression lists and key-value pairs.
- **Untyped constant folding**: Front-end constant folding in `p4c` turned ill-typed programs into well-typed ones.
- **Fixed-width `/` and `%` drift**: `P4_16` originally allowed `/` and `%` only on positive compile-time `int` values while `p4c` accepted fixed-width `bit<W>`—a spec gap closed upstream in `p4lang/p4-spec` commit `0370191bea5d26cd17c3ed25a6849d2df306b56b` (2026-09-17).

---

### 3. Single-Cycle Stateful ALU (`SALU`) Synthesis (`Domino` & `Chipmunk`)

Basis: documentation + source + execution + derived

Stateful data-plane algorithms (sketches, heavy-hitter trackers, flowlet switching, CONGA, active queue management) update persistent SRAM registers $R[k]$ per packet.

#### 3.1 The Single-Cycle Feedback Wall

At ~1 GHz line rate (1 packet/cycle), splitting a read-compute-write cycle on $R[k]$ across stages $s$ and $s+1$ creates a read-after-write hazard with trailing packet $i+1$ entering stage $s$ one cycle later. Because cross-stage forwarding stalls break line rate:

> **Invariant (Single-Cycle SALU Closure):** Every data-dependence cycle through persistent switch state must execute completely within **one clock cycle** inside a single stage's **Stateful ALU (`SALU`)** atom.

#### 3.2 `Domino`: Packet Transactions and Tarjan-SCC Partitioning

**Domino** (Sivaraman et al., SIGCOMM 2016; `packet-transactions/domino-compiler` @ `1ed941aa40...`) enforces an **all-or-nothing** contract: sequential C-like *packet transactions* either compile to line-rate microcode preserving atomic per-packet semantics or fail compilation statically.

Exact compilation pipeline inspected in `domino-compiler` (`partitioning.cc` L19–L193, `sketch_backend.cc` L15–L85):
1. **If-conversion, SSA, and `stateful_flanks`**: Predicates branches and hoists each persistent state variable (scalar or array) to **exactly one read and one write** (`partitioning.cc` L26–L45).
2. **Bidirectional state-loop edges (`handle_state_vars`, L42–L44)**: Inserts **both** `edge(read(v), write(v))` and `edge(write(v), read(v))` alongside forward packet-field RAW edges (`depends`, L78–L138).
3. **Tarjan SCC condensation (`dep_graph.condensation`, L157–L158)**: Collapses every cyclic dependence through persistent state into one **indivisible codelet**. Mutually dependent state variables (`A' = f(A, B); B' = g(A, B)`) collapse into a single SCC.
4. **Critical-path DAG schedule (`critical_path_schedule`, L161)**: Assigns minimum pipeline stages on the acyclic condensed graph.
5. **Banzai atom matching (`sketch_backend.cc` L15–L40)**: Checks each stateful SCC via `SKETCH` against single-cycle Banzai atom templates (`RAW`, `PredRAW`, `IfElseRAW`, `Sub`, `NestedIfs`, `Pair`); failure aborts compilation.

Probe Part 4d reproduces this scheduler: a flowlet transaction schedules in 4 stages (`{0: [1,4] (last_time), 1: [2], 2: [3], 3: [5,6,7] (flowlet_id)}`), a mutually coupled `(A, B)` cycle is **rejected** on 1-variable `RAW` atoms (`SCC [1,2,3,4,5,6]` couples 2 state variables) but **accepted** in 1 stage on a 2-variable `Pair` atom, and a stateful `mul` cycle (`ewma = ewma * pkt_len`) is **rejected** even on `Pair`.

#### 3.3 `Chipmunk`: Whole-Pipeline Synthesis and Domain-Specific Slicing

**Chipmunk** (Gao et al., SIGCOMM 2020; `chipmunk-project/chipmunk` @ `a86eb9030c...`) removes Domino's rigid AST-partitioning false rejections by framing whole-pipeline allocation and code generation as bitvector **program synthesis**:

- **Parameterized SALU templates (`example_alus/stateful_alus/{raw,pred_raw,if_else_raw,sub,nested_ifs,pair}.alu`)**: Encode single-cycle hardware circuits with synthesis holes (`Mux2/3/4`, `Opt`, `rel_op`, `arith_op`, `C()`), including 2-register atomic `pair.alu`.
- **Parallel CEGIS + Z3 verification (`chipc/compiler.py` L182–L259, `iterative_solver.py` L57–L130)**: Explores stage-to-state-group assignments (`_salu_config_<stage>_<group>`) in parallel with `SKETCH`, then verifies full bit-width equivalence in **Z3** (`Mode.VERIFY`), adding `|StateAndPacket|` counterexamples iteratively.
- **Domain-specific slicing (`compiler.py` L45–L102)**: Slices synthesis by independent `output_packet_fields` and `output_state_groups`, yielding **1×–387× (average 51×) speedup**, compiling transactions Domino rejects (often in fewer stages), with a backend targeting **Intel Tofino**.

---

### 4. Narrow Post-IEEE-754 Formats (`FP8 E4M3FN` / `E5M2`) and `IEEE P3109 v4.1`

Basis: normative + documentation + source + execution + derived

Narrow ML floating-point formats reclaim IEEE-754 special-value bit patterns to recover dynamic range. Critically, **OCP FP8/MX v1.0** and **IEEE P3109 Interim Report v4.1** disagree on `NaN` bit patterns, negative zero, and exponent bias.

#### 4.1 Bit-Level Format Taxonomy

Verified directly from Micikevicius et al. (2022, Table 1), OCP MX v1.0 (§5.3, Tables 2–5 & 7), and **IEEE SA WG P3109 Interim Report v4.1** (2026-09-14, §3.1–3.2, §4.7.6, Annex B Tables 3–7, Annex F):

| Format | $K$ | $P$ (incl. impl.) | $\Sigma$ / $\Delta$ | Bias ($B$) | Zero(s) | `Inf`(s) | `NaN`(s) | Max Finite ($M_{hi}$) | Min Subnorm |
|---|---:|---:|---|---:|---|---|---|---|---|
| **OCP `FP8 E4M3` (`E4M3FN`)** | 8 | 4 (3 expl.) | Signed / Finite | 7 | `0x00`, `0x80` | **None** | `0x7F`, `0xFF` | $\pm 448 = 1.75 \cdot 2^8$ | $2^{-9}$ |
| **OCP `FP8 E5M2`** | 8 | 3 (2 expl.) | Signed / Extended | 15 | `0x00`, `0x80` | `0x7C`, `0xFC` | `0x7D..7F`, `0xFD..FF` | $\pm 57344 = 1.75 \cdot 2^{15}$ | $2^{-16}$ |
| **AGQ (`gfx940`/Graphcore) `E4M3FNUZ`** | 8 | 4 (3 expl.) | Signed / Finite | 8 | `0x00` only | **None** | `0x80` (1 NaN) | $\pm 240 = 1.875 \cdot 2^7$ | $2^{-10}$ |
| **P3109 v4.1 `Binary8p4sf`** | 8 | 4 (3 expl.) | Signed / Finite | $2^{8-4-1}=8$ | `0x00` only | **None** | `0x80` (1 NaN) | $\pm 240 = 1.875 \cdot 2^7$ | $2^{-10}$ |
| **P3109 v4.1 `Binary8p4se`** | 8 | 4 (3 expl.) | Signed / Extended | $2^{8-4-1}=8$ | `0x00` only | `0x7F`, `0xFF` | `0x80` (1 NaN) | $\pm 224 = 1.75 \cdot 2^7$ | $2^{-10}$ |
| **P3109 v4.1 `Binary8p3se`** | 8 | 3 (2 expl.) | Signed / Extended | $2^{8-3-1}=16$ | `0x00` only | `0x7F`, `0xFF` | `0x80` (1 NaN) | $\pm 57344$ ($e_{\max}=15$) | $2^{-17}$ |
| **OCP `FP6 E3M2`** | 6 | 3 (2 expl.) | Signed / Finite | 3 | `0x00`, `0x20` | **None** | **None** | $\pm 28.0 = 1.75 \cdot 2^4$ | $2^{-4}$ |
| **OCP `FP6 E2M3`** | 6 | 4 (3 expl.) | Signed / Finite | 1 | `0x00`, `0x20` | **None** | **None** | $\pm 7.5 = 1.875 \cdot 2^2$ | $2^{-3}$ |
| **OCP `FP4 E2M1`** | 4 | 2 (1 expl.) | Signed / Finite | 1 | `0x0`, `0x8` | **None** | **None** | $\pm 6.0 = 1.5 \cdot 2^2$ | $2^{-1} = 0.5$ |
| **P3109 v4.1 `Binary4p2sf`** | 4 | 2 (1 expl.) | Signed / Finite | $2^{4-2-1}=2$ | `0x0` only | **None** | `0x8` (1 NaN) | $\pm 3.0 = 1.5 \cdot 2^1$ | $2^{-2} = 0.25$ |
| **OCP `E8M0` (MX scale)** | 8 | 1 (0 expl.) | Unsigned / Finite | 127 | **None** (`0x00`=$2^{-127}$) | **None** | `0xFF` (1 NaN) | $2^{127}$ (`0xFE`) | $2^{-127}$ |
| **P3109 v4.1 `Binary8p1uf`** | 8 | 1 (0 expl.) | Unsigned / Finite | $2^{8-1}=128$ | `0x00` (0.0) | **None** | `0xFF` (1 NaN) | $2^{126}$ (`0xFE`) | $2^{-127}$ (`0x01`) |

**IEEE P3109 v4.1 projection semantics (§3.1, §4.2, §4.7.2–4.7.6, Annex B)**:
- Every format `Binary{K, P, Σ, ∆}` ($K > 2$; $0 < P < K$ signed, $0 < P \le K$ unsigned; bias $B = 2^{K-P-1}$ signed / $2^{K-P}$ unsigned) encodes `0.0` at `0`, `1.0` at $2^{K-2}$ (signed) / $2^{K-1}$ (unsigned), and a **single `NaN`** at $2^{K-1}$ (signed—reclaiming `-0.0`) or $2^K - 1$ (unsigned).
- Operations are exception-free and compose via $\omega\text{Decode} \to \text{exact math over }\mathbb{R}_\omega \to \omega\text{RoundToPrecision}_{P,B,\mu} \to \omega\text{Saturate}_{M_{lo},M_{hi}} \to \omega\text{Encode}$.
- **Rounding precedes saturation (§4.7.3 Note 1)**: Under `NearestTiesToEven`, values strictly below $M_{hi} + \frac{1}{2}\text{ulp}(M_{hi})$ round to $M_{hi}$ rather than overflowing.
- **Saturation modes (§4.7.5)**: `SatFinite` clamps all out-of-range finite values and $\pm\infty$ to $[M_{lo}, M_{hi}]$; `SatPropagate` preserves representable $\pm\infty$ and clamps finite overflows to $[M_{lo}, M_{hi}]$; **`SatNone` maps overflow on any `Finite` domain ($\Delta = \text{Finite}$) to `NaN`** (except directed rounding toward finite limits, L1064–L1072), matching OCP `E4M3` `OVF` mode (Table 3).

#### 4.2 Actively Unsound IEEE-754 Compiler Rewrites

Unlike scalar `f32`/`f64` rules in `rust-floating-point-semantics-llvm-lowering-and-isa-behavior` and IEEE mechanizations in `lean-ieee754-floatspec-cryptography-and-constant-time`, applying standard IEEE-754 folds to `E4M3FN` or `P3109` silently miscompiles programs (all verified in probe Part 1b):

| IEEE-754 Rewrite / Assumption | Root Cause of Unsoundness | Verified Counterexample |
|---|---|---|
| **Overflow-to-`Inf` (`isinf(x + y)`, `minNum(x, 100.0)`)** | Finite formats lack `±Inf`; `E4M3FN OVF` and `P3109 (SatNone, Finite)` produce **`NaN`** on overflow. | `E4M3FN_OVF(256 + 256) = NaN` (`0x7F`); `P3109_8p4sf_SatNone(160 + 160) = NaN` (`0x80`). |
| **`ninf`-guarded cancellation `(2.0 * x) * 0.5 -> x`** | Under `SAT` / `SatFinite`, overflow silently clamps to $M_{hi}$ **without generating `Inf` or `NaN`**. | For exact `x = 256.0` (`0x78`): `E4M3FN_SAT(256 * 2) * 0.5 = 448 * 0.5 = 224.0 != 256.0`. |
| **`x - x -> 0.0` (finite-input assumption)** | Overflow on finite inputs yields `NaN` in `OVF`/`SatNone`, so folding `x - x -> 0` erases `NaN`. | `x = E4M3FN_OVF(256 + 256) = NaN`; `x - x` is `NaN`, not `0.0`. |
| **Bitwise sign-flip negation `x ^ (1 << (K-1))`** | Safe for IEEE-754 and OCP `E4M3FN` (`-0.0`), but **turns `+0.0` into `NaN`** in P3109 signed formats and `E4M3FNUZ`! | `0x00 ^ 0x80 = 0x80`: decodes to `-0.0` in OCP `E4M3FN`, but **`NaN`** in `P3109 Binary8p4sf` and `E4M3FNUZ`. |
| **Signed-zero preservation (`copysign(1.0, -0.0)`)** | P3109 signed formats have no `-0.0`; `ωDecodeExternal(-0.0) = 0` (§4.8.1 L1163). | Both `+0.0` and `-0.0` encode to `0x00`. |

---

### 5. OCP Microscaling (`MXFP8`, `MXFP6`, `MXFP4`, `MXINT8`) and Block-Coupled Mutability

Basis: normative + source + execution + derived

**OCP Microscaling Formats (MX) Specification v1.0** (September 2023; `microsoft/microxcaling` @ `7bc41952de...`) packs $k = 32$ narrow elements $P_1, \dots, P_{32}$ with one shared 8-bit unsigned power-of-two scale $X$ (`E8M0`; renamed `UE8M0` in later hardware docs):

| OCP MX Format | Element ($P_i$) | $d$ (bits) | $k$ | Scale ($X$) | $w$ (bits) | Block Bits ($w + kd$) | Bits / Elem | Max Elem Pow2 |
|---|---|---:|---:|---|---:|---:|---:|---:|
| **`MXFP8` (E5M2)** | FP8 `E5M2` | 8 | 32 | `E8M0` | 8 | 264 (33 B) | 8.25 | $2^{15}$ |
| **`MXFP8` (E4M3)** | FP8 `E4M3` | 8 | 32 | `E8M0` | 8 | 264 (33 B) | 8.25 | $2^{8} = 256$ |
| **`MXFP6` (E3M2)** | FP6 `E3M2` | 6 | 32 | `E8M0` | 8 | 200 (25 B) | 6.25 | $2^{4} = 16$ |
| **`MXFP6` (E2M3)** | FP6 `E2M3` | 6 | 32 | `E8M0` | 8 | 200 (25 B) | 6.25 | $2^{2} = 4$ |
| **`MXFP4` (E2M1)** | FP4 `E2M1` | 4 | 32 | `E8M0` | 8 | 136 (17 B) | 4.25 | $2^{2} = 4$ |
| **`MXINT8`** | INT8 (scale $2^{-6}$) | 8 | 32 | `E8M0` | 8 | 264 (33 B) | 8.25 | $2^{0} = 1$ |

*Variant note*: Physical interleaving of $X$ and $P_i$ is left unspecified by OCP MX v1.0 (§5.1). NVIDIA Blackwell's **`NVFP4`** adapts microscaling to $k = 16$ elements with an `E4M3` block scale plus a per-tensor `FP32` global scale.

**Normative OCP MX v1.0 semantics (§5.1, §6.1–§6.3, Tables 1–7)**:
1. **`E8M0` scale & block `NaN` broadcast (§5.1, Table 7)**: $e \in [0, 254] \implies X = 2^{e-127}$; $e = \text{0xFF} \implies X = \text{NaN}$, which **forces $v_i = \text{NaN}$ for all $1 \le i \le 32$ regardless of $P_i$**. Otherwise $v_i = P_i$ if $P_i \in \{\text{Inf}, \text{NaN}\}$, implementation-defined if $|X P_i| > V_{\max\text{Float32}}$, else $v_i = X P_i$.
2. **Factored block dot product (§6.1)**: $C = X^{(A)} X^{(B)} \sum_{i=1}^{32} P_i^{(A)} P_i^{(B)}$ (internal accumulation precision and reduction order are implementation-defined).
3. **Shared scale rule (§6.3)**: $X = 2^{\lfloor \log_2(\max_i |V_i|) \rfloor - e_{\max}^{\text{pow2}}}$, $P_i = \text{quant}_{\text{RTNE,sat}}(V_i / X)$. For `MXFP4` (`E2M1` codebook $\{0, \pm 0.5, \pm 1, \pm 1.5, \pm 2, \pm 3, \pm 4, \pm 6\}$, $e_{\max}^{\text{pow2}} = 2$), $X = 2^{\lfloor \log_2(\max_i |V_i|) \rfloor - 2}$. IEEE P3109 v4.1 §5 generalizes this to parameterized `ConvertToBlockMaxAbsFinite` and `BlockDotProduct` with explicit $S = 0$ and $S = \pm\infty$ rules (§5.4.2).

#### Why Shared-Exponent Blocks Destroy Element-Wise `&mut elem` Borrowing

Rust/C++/LLVM array references assume **disjoint element framing**: mutating `&mut arr[31]` cannot alter `arr[0..31]`. In an `MXFP4` block, mutating slot 31 triggers an irreconcilable dilemma (verified in probe Part 2):

- **Before mutation**: $V_{0..30} \in \{0.5, 0.75, 1.5\}$, $V_{31} = 1.0 \implies \max |V| = 1.5 \implies X = 2^{-2} = 0.25$ (`E8M0 = 0x7D`). All **32/32 elements** quantize with **0% error**.
- **Rescaling write (`V[31] = 128.0`)**: $X$ jumps from `0x7D` ($0.25$) to `0x84` ($32.0$). Slot 31 encodes exactly ($32.0 \times 4.0 = 128.0$), but every untouched sibling $V_{0..30} \le 1.5$ scales to $\le 0.046875 < 0.25$ and **silently flushes to `0.0`** (31/31 siblings destroyed!). Writing `NaN` via `E8M0 = 0xFF` poisons all 32 slots.
- **Fixed-scale write (freeze `E8M0 = 0x7D`)**: Siblings stay intact, but slot 31 clamps to $0.25 \times 6.0 = 1.5$ (**98.83% write corruption**).

**Sound PL / IR interface**: Prohibit raw element `&mut` borrows (`&mut E2M1`) into block-scaled storage; expose only atomic whole-block lenses matching P3109 §5 Group KA/E:

```rust
#[repr(C)]
pub struct MxFp4Block { scale: u8 /* E8M0 */, packed: [u8; 16] /* 32 x 4-bit E2M1 */ }
impl MxFp4Block {
    pub fn quantize(elems: [f32; 32]) -> Self;     // whole-block atomic write
    pub fn dequantize(&self) -> [f32; 32];         // whole-block read
    pub fn dot(&self, rhs: &Self) -> f32;          // hardware factored MAC (OCP §6.1)
    // Intentionally NO `IndexMut<usize>` / `fn elem_mut(&mut self, i: usize) -> &mut E2M1`!
}
```

---

### 6. Exact `Posit`/`Quire` Accumulation, Probabilistic Stochastic Rounding, and DSP Saturation

Basis: normative + documentation + source + execution + derived

#### 6.1 `Posit` Standard (2022) and Exact Associative `Quire` Super-Accumulators

Verified against **Standard for Posit Arithmetic (2022)** (2 March 2022, §§3.1–3.4, §5.11, Table 1) and `stillwater-sc/universal` (`9f0e5da5e8...`, `quire_impl.hpp` & `posit/attributes.hpp`):

- **Posit encoding ($es = 2$ fixed)**: `000...0` = `0`, `100...0` = **`NaR`** (unique non-real unifying `NaN` and $\pm\infty$). All nonzero finite posits decode uniquely via $p = ((1 - 3s) + f) \cdot 2^{(1 - 2s)(4r + e + s)}$, yielding $\text{minPos} = 2^{-4n+8}$ and $\text{maxPos} = 2^{4n-8}$ with tapered precision peaking near $\pm 1$.
- **Exact `Quire` layout ($16n$ bits, §3.4 Fig. 4)**: Fixed-point 2's-complement register of `1` sign bit + `31` carry guard bits + `(8n - 16)` integer bits + `(8n - 16)` fraction bits (`NaR` = $-2^{16n-1}$, else $q = 2^{16-8n} \cdot \text{signed}_{16n}(\text{bits})$). Every product of two $n$-bit posits lands exactly inside the $(I, F)$ bits, and the 31 carry bits hold up to **$2^{31}$ exact products** (or $2^{23+4n}$ exact sums) with zero rounding:

| Format | Frac Bits | $\text{minPos}$ | $\text{maxPos}$ | `pIntMax` | Quire Width ($16n$) | Layout (`S+C+I+F`) | Exact Dot Terms | Exact Sum Limit |
|---|---|---|---|---:|---:|---|---:|---:|
| **`posit8`** | 0–3 | $2^{-24}$ | $2^{24}$ | 16 | **128 bits** | `1+31+48+48` | $\le 2^{31}$ | $2^{55}$ |
| **`posit16`** | 0–11 | $2^{-56}$ | $2^{56}$ | 1024 | **256 bits** | `1+31+112+112` | $\le 2^{31}$ | $2^{87}$ |
| **`posit32`** | 0–27 | $2^{-120}$ | $2^{120}$ | $2^{23}$ | **512 bits** | `1+31+240+240` | $\le 2^{31}$ | $2^{151}$ |

- **Monoid associativity vs IEEE 754 (`ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`)**: Within the $2^{31}$-term guard band (prior to single final `qToP` rounding), `qMulAdd`/`qAddQ` is exact integer addition—an **associative, commutative monoid** making parallel tree-reduction order bit-invariant. In probe Part 3b across all 24 permutations of $(+1024 \cdot 32) + (-1024 \cdot 32) + (1 \cdot 2^{-10}) + (1 \cdot 2^{-10}) = 2^{-9}$, **IEEE `binary16` produces three order-dependent results `[0.0, 0.0009765625, 0.001953125]`**, while **256-bit `Quire16` yields exact `1/512` across all 24 permutations**.
- **Software quire double-rounding trap (`stillwater-sc/universal`, `quire_impl.hpp` L44–L61)**: Converting a quire to another format via IEEE `double` causes double rounding unless intermediate conversion rounds to odd and target range/significand fits strictly inside `double` (`quire_converts_through_double_v`), and wrapping targets (`is_modulo`) must bypass `double` to preserve saturation.

#### 6.2 Hardware Stochastic Rounding (`SR`) as a Probabilistic Effect

Verified against Croci, Fasi, Higham, Mary, and Mikaitis (2022, DOI `10.1098/rsos.211631`), **IEEE P3109 v4.1** (§4.7.4 L992–L1018 & §5.3 L2619–L2628), Graphcore IPU, and NVIDIA Blackwell PTX 8.7+ `cvt.rs`:

- **Mode 1 (`SR_1`) vs Mode 2 (`SR_2`)**: For $x \in [x_1, x_2]$ ($x_1 < x_2$), Mode 1 rounds to $x_2$ with probability $p = (x - x_1)/(x_2 - x_1)$ and $x_1$ with $1 - p$, giving **unbiased expectation** $\mathbb{E}[\text{SR}_1(x)] = x$ and **exact variance** $\operatorname{Var}(\text{SR}_1(x)) = (x - x_1)(x_2 - x) \le \frac{1}{4}(x_2 - x_1)^2$. (Mode 2 uses fair coin $p = 1/2$, which is biased.) Mean-zero, mean-independent rounding errors form a **martingale**, giving Azuma–Hoeffding error bounds $\mathcal{O}(\sqrt{n}u)$ (vs $\mathcal{O}(nu)$ for RN) and eliminating **stagnation** (probe Part 3d: adding $2^{-10}$ 10,000 times to `1.0` in `E4M3FN` stagnates permanently at `1.0` under RN, whereas SR converges to `11.0`, nearest grid point to exact `10.765625`).
- **Finite-$N$-bit hardware comparators (IEEE P3109 v4.1 §4.7.4)**: With $0 \le R < 2^N$ and $\nu = \tilde{S} - \lfloor \tilde{S} \rfloor$:
  - `StochasticA_{N,R}`: $\lfloor \nu \cdot 2^N \rfloor + R \ge 2^N$
  - `StochasticB_{N,R}`: $\lfloor \nu \cdot 2^{N+1} \rfloor + (2R + 1) \ge 2^{N+1}$ (half-LSB offset removing truncation bias)
  - `StochasticC_{N,R}`: $\text{RNITE}(\nu \cdot 2^N) + R \ge 2^N$
  Vector/block ops (§5.3) lift $R$ to per-lane sequences $[R_1, \dots, R_B]$.
- **Compiler CSE / LICM corruption (verified exhaustively over all $2^4 = 16$ PRNG states in probe Part 3c, $x = 11/8 \in [1, 2]$, $\operatorname{Var}(\text{SR}) = 15/64$)**:
  1. **CSE doubles variance & corrupts support**: `let y = sr(x); y + y` yields $\operatorname{Var} = 4 \cdot (15/64) = \mathbf{15/16}$ vs independent `sr(x) + sr(x)` $\operatorname{Var} = 2 \cdot (15/64) = \mathbf{15/32}$ ($2\times$ inflation) and **removes `3` ($x_1 + x_2$) from the output support**.
  2. **CSE injects bias into nonlinear consumers**: Independent $\mathbb{E}[\text{SR}(x; R_1) \cdot \text{SR}(x; R_2)] = x^2$ (unbiased), whereas CSE `let y = sr(x); y * y` shifts expectation to $\mathbb{E}[y^2] = x^2 + \operatorname{Var}(\text{SR}(x)) = x^2 + \mathbf{15/64}$ (strictly biased).
  3. **LICM destroys martingale independence**: Hoisting `sr(delta)` out of an accumulation loop correlates all iterations to one draw.
- **Implicit-PRNG vs explicit-entropy ISAs**:
  - **Implicit-PRNG hardware** (e.g., Graphcore IPU internal tile PRNG) must carry a **non-pure probabilistic/entropy effect** in compiler IR forbidding CSE/GVN/LICM across SR ops.
  - **Explicit-entropy hardware** (NVIDIA Blackwell PTX 8.7+ `cvt.rs`):
    ```ptx
    cvt.rs.satfinite.e2m1x4.f32 d, {a0, a1, a2, a3}, rbits; // pure given explicit .u32 rbits
    ```
    Externalizing `rbits` makes `cvt.rs` pure as a function of `(inputs, rbits)` and moves non-duplicability cleanly onto the linear/affine PRNG stream producing distinct `rbits` per call.

#### 6.3 DSP Fixed-Point Saturation and Circular Addressing

Verified against ISO/IEC TR 18037 (`_Fract`, `_Accum`, `_Sat`), LLVM IR (`llvm.sadd.sat`, `llvm.smul.fix.sat`), and ARM NEON/MVE (`SQDMULH`, `VQADD`) + probe Part 3e:

- **`Q1.15` `-1.0 * -1.0` wrap vs saturation**: Wrapping `(-32768 * -32768) >> 15` overflows `+32768` to `-32768` (`-1.0`, sign inversion in IIR/FIR filters); ARM `SQDMULH` saturates to `+32767` ($1 - 2^{-15}$).
- **Non-associativity of saturating addition**: `sat_add(sat_add(20000, 20000), -10000) = 22767 != 30000 = sat_add(20000, sat_add(20000, -10000))`. Compilers must forbid reassociating `llvm.sadd.sat` reductions unless widened into a guard-bit accumulator (`_Accum` / 40-bit MAC).
- **Hardware circular addressing**: DSP modulo ring-buffer addressing units (TI C6x, Hexagon, Cortex-M DSP) wrap pointers at power-of-two boundaries without branches, clashing with C/LLVM `inbounds GEP` pointer-provenance rules and requiring first-class ring-buffer slice abstractions.

---

### 7. Cross-Domain Compiler and Verification Design Rules

Basis: derived

| Hardware Reality | Broken Imperative / IEEE-754 Assumption | Required PL / IR / Verification Primitive |
|---|---|---|
| **RMT/PISA feed-forward switch** | Arbitrary CFG loops, heap/stack, pointers | Bounded DAG control types, stratified non-recursive typing (`Petr4`), static PHV/stage budgets |
| **`P4_16` invalid headers & `header_union`** | Defined reads, disjoint struct-field writes | Header-validity typestate + `option bool` oracle (`Petr4` `Sval`) + union `havoc_header` |
| **`P4_16` `extern` isolation** | Call-by-reference parameter aliasing | Left-to-right **copy-in / copy-out** with eager l-value capture + control-plane invariants (`P4v`) |
| **Single-cycle `SALU` state updates** | Multi-stage register RMW chains | Bidirectional state-loop **Tarjan SCC condensation** (`Domino`) + sliced CEGIS/Z3 synthesis (`Chipmunk`) |
| **`FP8 E4M3FN` & `P3109 v4.1` formats** | IEEE `±Inf`, `-0.0`, `xor`-MSB neg, `ninf` folds | Parameterized `Binary{K, P, Σ, ∆}` + `(RoundMode, SatMode)` projection; ban `xor`-MSB when `NaN = 2^{K-1}` |
| **`OCP MXFP8/6/4` shared `E8M0` scale** | Disjoint `&mut arr[i]` element borrows | Opaque atomic `MxBlock<32, Elem, E8M0>` with whole-block quantize/dequantize/dot lenses |
| **Posit `Quire` ($16n$-bit accumulator)** | Non-associative FP reduction trees | Exact associative-commutative monoid type (within $2^{31}$ guard band) + single final `qToP` |
| **Hardware Stochastic Rounding (`SR`)** | Pure referential transparency (CSE/LICM) | Probabilistic/entropy effect (implicit PRNG) OR linear/affine explicit `rbits` token (`cvt.rs`) |
| **DSP `Q1.15` saturation & modulo buffers** | Associative integer `add`, flat `inbounds` ptrs | Non-associative `llvm.sadd.sat`/`llvm.smul.fix.sat` + guard-bit widening + ring-buffer views |

---

## Boundaries

- **Not examined — Commercial Intel Tofino proprietary compiler internals**: Public `RMT`, `P4_16`, `Domino`, and `Chipmunk` sources were inspected directly; proprietary Barefoot/Intel `bf-p4c` passes, Tofino-1/2/3 crossbar routing constraints, and confidential register-ALU micro-op encodings were **not examined**.
- **Not examined — Gate-level CMOS area, power, and RTL synthesis**: Physical gate counts, timing closure, and RTL verification (e.g., RISC-V `PERCIVAL` posit/quire units, `RMT` TCAM power, or `SR` LFSR/Philox area) were **not examined**.
- **Not examined — Post-v1.0 OCP MX drafts**: Only **OCP Microscaling Formats (MX) Specification v1.0** (September 2023) and `microsoft/microxcaling` were verified from primary text; subsequent draft revisions (e.g., v1.1 renaming `E8M0` -> `UE8M0`) were **not examined** normatively.
- **Unknown — Final balloted IEEE Std 3109**: **IEEE P3109 Interim Report v4.1** (2026-09-14) is an unapproved draft subject to change; whether the final balloted standard preserves every `Binary{K, P, Σ, ∆}` encoding, `SatNone` on `Finite` domains, and `StochasticA/B/C` rule is **unknown**.
- **Unknown — Proof-carrying certificates for `Chipmunk` -> `Tofino` compilation**: `Chipmunk` verifies synthesized pipelines with Z3 inside CEGIS, but independently checkable end-to-end equivalence certificates (e.g., Lean 4 / Coq) from `Domino` transactions to switch binaries remain **unknown** (not implemented in `chipmunk-project/chipmunk`).
- **Known not to apply — `Petr4` termination theorem on cyclic parsers**: `Petr4`'s mechanized termination proof (POPL 2021 §3.5) is **known not to apply** to arbitrary `P4_16` parsers with cyclic transitions; it covers only the parser-free match-action/control/function fragment.
- **Known not to apply — `Quire` associativity beyond $2^{31}$ maximal products or post-`qToP`**: Exact associativity is **known not to apply** once accumulation exceeds the 31-bit carry guard (order-dependent `NaR` overflow) or after rounding back to posit via `qToP`.
- **Known not to apply — Implicit-PRNG CSE hazard on explicit-`rbits` PTX `cvt.rs`**: Because Blackwell `cvt.rs` takes explicit `rbits`, standard CSE does not merge calls with distinct `rbits`; the compiler obligation shifts to preventing reuse of identical `rbits`.
- **Unsupported — `P4_16` dynamic allocation, pointers, recursion, and IEEE floats**: Explicitly **unsupported** by `P4_16`.
- **Unsupported — Per-element `NaN`/`Inf` in OCP `FP4 E2M1`, `FP6 E2M3`/`E3M2`, and `MXINT8`**: Explicitly **unsupported** by OCP MX v1.0 (§5.3.2–§5.3.4); `E8M0 = 0xFF` is the sole block-wide `NaN` representation.

---

## Evidence

All primary-source evidence and probe executions were acquired on `2026-11-19`:

### 1. Pinned Git Repositories

1. **`p4lang/p4-spec`** @ `0370191bea5d26cd17c3ed25a6849d2df306b56b` (v1.2.5 + HEAD, 2026-09-17): `p4-16/spec/P4-16-spec.adoc` L7–L8 (v1.2.5), L1454–L1649 (copy-in/copy-out, 6-step order, `f(a,g(a))`, `f(s[a].z,g(a))`, `out` invalid init, `extern` isolation), L3303–L3325 (eval order), L5156–L5271 (unspecified reads, invalid header writes, `header_union` havoc L5211–L5218), L6042–L6120 (parser machine), L7784–L7820 (pipeline machine).
2. **`verified-network-toolchain/petr4`** @ `9508676128a00ec5b23da4139c3c74849f2a8b1c` (2024-02-03): `lib/eval.ml` L1–L10 (`Poulet4.Interpreter.interp`); `coq/lib/P4light/Semantics/Semantics.v` L40/L405 (`Sval`, `read_one_bit`), L843–L859 (`write_header_field`), L889–L913 (`havoc_header`, `update_union_member`), L984–L1086 (`exec_arg`, `exec_func_copy_in`, `exec_call_copy_out`), L1157–L1166 (`exec_isValid`).
3. **`packet-transactions/domino-compiler`** @ `1ed941aa40da23964f1428e17705a0b147309e68` (2019-02-20): `partitioning.cc` L19–L54 (`handle_state_vars` bidirectional `read <-> write` edges), L78–L138 (`depends`), L154–L193 (Tarjan `condensation` + `critical_path_schedule`); `sketch_backend.cc` L15–L85 (`StateResult` SKETCH harness).
4. **`chipmunk-project/chipmunk`** @ `a86eb9030c7accfd552dc4c899fa247193588251` (2020-01-06): `chipc/compiler.py` L40–L125 (slicing), L182–L259 (`parallel_codegen` + Z3 `verify`); `chipc/iterative_solver.py` L41–L130 (CEGIS counterexamples); `example_alus/stateful_alus/{raw,pred_raw,if_else_raw,sub,nested_ifs,pair}.alu`.
5. **`P3109/Public`** @ `2d45cf2fe0314d32251f5439d9d3ed078f93fbb9` (2026-09-24): `CITATION.cff` (v4.1); `IEEE P3109 Interim Report.pdf` (v4.1, 2026-09-14) §3.1–3.2 (pp. 11–12), §4.2 & §4.7.2–4.7.6 (pp. 13, 20–25, `StochasticA/B/C`, `SatFinite/SatPropagate/SatNone`, `ωEncode`), §5.1–5.8 (pp. 56–65, block ops & SR), Annex B (pp. 70–72, Tables 3–7), Annex F (p. 77, OCP/AGQ/TSL matrix).
6. **`microsoft/microxcaling`** @ `7bc41952de394f5cc5e782baf132e7c7542eb4e4` (2024-08-19): `mx/formats.py` L57–L125 (`_get_format_params`); `mx/mx_ops.py` L49–L92 (`_shared_exponents`).
7. **`stillwater-sc/universal`** @ `9f0e5da5e8e756423570bdbc3e4632d9ae588611` (v5.18.0, 2026-11-19): `include/sw/universal/number/quire/quire_impl.hpp` L25–L90 (`quire`, `quire_converts_through_double_v`); `include/sw/universal/number/posit/attributes.hpp` L1–L90.

### 2. Standards and Peer-Reviewed Publications

- **Bosshart et al. (2013)**: *"Forwarding Metamorphosis: Fast Programmable Match-Action Processing in Hardware for SDN"*, ACM SIGCOMM 2013, DOI `10.1145/2486001.2486011`.
- **Doenges et al. (2021)**: *"Petr4: Formal Foundations for P4 Data Planes"*, *Proc. ACM Program. Lang.* 5(POPL), Art. 41, DOI `10.1145/3434322`, `arXiv:2011.05948`.
- **Liu et al. (2018)**: *"p4v: Practical Verification for Programmable Data Planes"*, ACM SIGCOMM 2018, DOI `10.1145/3230543.3230582`.
- **Sivaraman et al. (2016)**: *"Packet Transactions: High-Level Programming for Line-Rate Switches"*, ACM SIGCOMM 2016, DOI `10.1145/2934872.2934900`.
- **Gao et al. (2020)**: *"Switch Code Generation Using Program Synthesis"*, ACM SIGCOMM 2020, DOI `10.1145/3387514.3405874`.
- **Open Compute Project (Sep 2023)**: *"OCP Microscaling Formats (MX) Specification v1.0"* (B. Darvish Rouhani et al.), §§5.1–6.3, Tables 1–7.
- **Micikevicius et al. (2022)**: *"FP8 Formats for Deep Learning"*, `arXiv:2209.05433v2` (29 Sep 2022), DOI `10.48550/arXiv.2209.05433`, §§2–3, Table 1.
- **Posit Working Group (2 Mar 2022)**: *"Standard for Posit Arithmetic (2022)"* (NSCC Singapore), §§3.1–3.4, §5.11, Table 1, Figs. 1–4.
- **Croci, Fasi, Higham, Mary, and Mikaitis (2022)**: *"Stochastic Rounding: Implementation, Error Analysis and Applications"*, *Royal Society Open Science* 9(3), DOI `10.1098/rsos.211631`.

### 3. Executable Probe (`support/verify_p4_salu_and_exotic_numerics.py`)

Executed on Linux with Python 3 stdlib only (`exit 0`, wall time `0.15s`):

```console
python3 -B reports/programmable-network-pipelines-p4-semantics-and-exotic-hardware-numerics/support/verify_p4_salu_and_exotic_numerics.py
```

Verified outputs:
- **Part 1 (`FP8` & `P3109 v4.1`)**: Exhaustive 256-codepoint tables confirmed OCP `E4M3FN` (0 Infs, 2 NaNs `0x7F`/`0xFF`, max `448`), OCP `E5M2` (2 Infs, 6 NaNs, max `57344`), P3109 `Binary8p4sf` (bias 8, 1 NaN `0x80`, max `240`), `Binary8p4se` (max `224`), `Binary4p2sf` (max `3.0`, `0x8` NaN); verified `E4M3FN_OVF(256+256)=NaN`, `E4M3FN_SAT(256*2)*0.5=224.0!=256.0`, and `0x00^0x80` -> `-0.0` (`E4M3FN`) vs `NaN` (`P3109 Binary8p4sf`).
- **Part 2 (`OCP MXFP4`)**: Initial `E8M0=0x7D` ($2^{-2}$) quantized 32/32 elements exactly; mutating `elem[31]=128.0` under re-scale moved `E8M0->0x84` ($32.0$) and flushed 31/31 siblings to `0.0`, while holding `E8M0` fixed clamped `elem[31]` to `1.5` (98.83% error); `E8M0=0xFF` poisoned 32/32 elements to `NaN`.
- **Part 3 (`Quire16`, `SR`, `DSP Q1.15`)**: 256-bit `Quire16` returned exact `1/512` across all 24 permutations vs IEEE `binary16` `[0.0, 0.0009765625, 0.001953125]`; exhaustive $N=4$ `StochasticA` verified $\mathbb{E}[\text{SR}(11/8)]=11/8$, $\operatorname{Var}=15/64$, CSE variance doubling (`15/16` vs `15/32`), support loss (`3`), and nonlinear product bias (`+15/64`); 10,000-step `E4M3FN` RN stagnated at `1.0` vs SR `11.0` (exact `10.765625`); `Q1.15` wrap `-1*-1=-32768` vs sat `+32767` and `sat_add` non-associativity (`22767!=30000`).
- **Part 4 (`P4_16` & `Domino` SALU)**: Confirmed `header_union` invalid-write sibling havoc (`ipv4.valid=True, ipv4.ttl=None`), `copy-in/copy-out` `f(a,g(a))` `a=20` vs call-by-ref `a=30`, unguarded invalid-header typestate catch, and Tarjan-SCC SALU scheduling (4-stage flowlet accept; coupled `(A,B)` reject on 1-var `RAW` vs 1-stage accept on `Pair`; stateful `mul` cycle reject).

---

## Revalidation

1. **Rerun the standalone probe** (< 1 s, Python 3.10+ stdlib only):
   ```console
   python3 -B reports/programmable-network-pipelines-p4-semantics-and-exotic-hardware-numerics/support/verify_p4_salu_and_exotic_numerics.py
   ```
   Establishes bit-level, statistical, and graph-theoretic consistency of the modeled rules; does not detect upstream specification changes.
2. **Diff `P3109/Public` from `2d45cf2fe0314d32251f5439d9d3ed078f93fbb9`**: Check `CITATION.cff` and diff §3.1 (`Binary{K,P,Σ,∆}` bias and `NaN` code point $2^{K-1}$), §4.7.4 (`StochasticA/B/C`), §4.7.5 (`SatNone` on `Finite`), and §5 (block operations) upon newer drafts or final balloting.
3. **Diff `p4lang/p4-spec` from `0370191bea5d26cd17c3ed25a6849d2df306b56b`**: Inspect changes to `p4-16/spec/P4-16-spec.adoc` around `Calling convention: call by copy in/copy out` and `Reading uninitialized values and writing fields of invalid headers`.
4. **Check post-v1.0 OCP MX specifications**: Compare scale encoding (`E8M0`/`UE8M0`), `0xFF` NaN broadcast, block size $k=32$, and element formats (`E2M1`, `E2M3`, `E3M2`, `E4M3`, `E5M2`) against §5.
5. **Audit new accelerator SR instructions**: Check each new ISA manual for whether stochastic rounding consumes **implicit PRNG state** (requiring a non-pure probabilistic effect blocking CSE/LICM) or takes an **explicit random-bit operand** (pure given `rbits`, shifting non-duplicability to the entropy stream).
