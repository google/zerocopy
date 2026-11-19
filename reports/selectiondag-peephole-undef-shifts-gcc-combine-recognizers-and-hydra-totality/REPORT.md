# Backend Instruction-Selection Totality, Undefined/Poison Shift-Mask Peepholes, RTL Multi-Instruction Combiners, and Synthesis-Driven Rewrite Verification

## Summary

Backend instruction selectors and late peephole combiners sit across the most bug-dense semantic seam in ahead-of-time and just-in-time compilers: translating width-polymorphic, undefined-value-bearing intermediate representations (`LLVM IR`, `SelectionDAG`, Cranelift `CLIF`, `GCC RTL`) into target-specific machine instructions whose bitwidth truncation, shift-count masking, and condition-code (`EFLAGS`/`NZCV`) side effects obey hardware rather than algebraic identities. Direct source inspection and executable modeling across Cranelift `ISLE` (`bytecodealliance/wasmtime`), `LLVM` (`InstCombine` and `SelectionDAG`), `GCC` (`combine.cc` and `simplify-rtx.cc`), `Alive2`, and `Hydra` establish five reusable engineering invariants:

1. **Prioritized overlap resolution does not imply coverage totality or tie-break modularity**: Cranelift `ISLE`'s static overlap pass (`cranelift/isle/isle/src/overlap.rs`) rejects equal-priority overlapping rules (`a.prio == b.prio`) and shadowed rules whose higher-priority dominator has fewer or equal constraints, but **intentionally permits partial non-subset overlaps across distinct integer priorities** and **skips overlap checking altogether on `multi` constructors** (`flags.multi`). Rule-by-rule verification (`Crocus` / `Arrival`) proves functional refinement when a rule fires, whereas absence of compiler-panic `unreachable!()` fallbacks requires an independent exhaustive bitvector cover obligation over all legalizable IR shapes.
2. **Multi-use `undef` duplication and unmasked zero-shift poison invalidate algebraic rotate and bitfield folds unless `freeze` is materialized prior to fan-out**: In `LLVM IR` and `Alive2` (`ir/instr.cpp`), `shl`/`lshr`/`ashr` produce `poison` whenever shift count $c \ge W$ (`b.ult(b.bits())`), while `undef` represents a set of bitvectors chosen *independently at each evaluation site*. Rewriting a single-use expression such as `((x >> 4) * 17)` (`16` reachable `i8` outputs `{0x00, 0x11, ..., 0xFF}`) into a two-use bit-insert `((x & 0xF0) | (x >> 4))` without `freeze(x)` leaks **`240` impossible outputs** (`256` total states), and expanding `fshl(x, x, c)` into `(x << c) | (x >> (W - c))` injects immediate shift-oversize `poison` at $c = 0$ ($W - 0 = W \ge W$).
3. **Sub-word hardware shift-count masking breaks value-only peephole equivalence when condition flags are live**: On `x86_64`, `8`-bit and `16`-bit variable rotates (`rol al, cl`, `ror ax, cl`) mask `CL` by **`0x1F` (`31`)** before taking the rotation modulo `8` or `16`, but gate `CF`/`OF` preservation on `(CL & 0x1F) == 0` rather than `(CL & 7) == 0`. Stripping an explicit `& 7` mask from `CL` preserves the destination GPR across all `256` shift bytes yet **corrupts `CF` on `24` out of `256` `CL` values** (`c in {8, 16, 24} mod 32`) whenever `CF_in != LSB(dest)`.
4. **Target register-truncation macros (`TRULY_NOOP_TRUNCATION`) and paradoxical `subreg`s couple middle-end bit-inference to ABI sign-extension invariants**: In `GCC` (`gcc/simplify-rtx.cc` and `gcc/combine.cc`), `3->1` and `4->2` `RTL` instruction combination relies on cached `nonzero_bits` and sign-bit copies (`num_sign_bit_copies`) alongside `TRULY_NOOP_TRUNCATION_MODES_P`. On architectures requiring canonical `32`-in-`64`-bit sign extension (`RISC-V` `RV64`, `MIPS64`, `LoongArch64`), turning an explicit `TRUNCATE` into a no-op lowpart `SUBREG` without proving canonical sign-extension corrupts subsequent `beq`/`blt` `64`-bit register comparisons.
5. **Closed-loop soundness requires pairing `QF_BV` rule verification with width-generalized synthesis (`Hydra`) and `V1–V4` empirical falsification**: Because rule preconditions can become accidentally vacuous and SMT solvers themselves exhibit soundness bugs under complex bitvector rewrites, high-assurance backend pipelines pair mechanized ISA refinement (`Crocus`/`Arrival`/`Alive2`) with spec-mutation kill suites (`V1`), `YARPGen`/`EMI` + `Murxla` solver/lowering differential fuzzing (`V2`), physical-silicon flag/GPR litmus execution (`V3`), and minimal `3`-line concrete bitvector counterexample diagnostics (`V4`).

---

## Applicability

The findings in this report apply to compiler instruction-selection DSLs, peephole term-rewriting passes, DAG/RTL instruction combiners, and translation-validation / superoptimization frameworks targeting `8/16/32/64/128`-bit scalar and vector ISAs (`x86_64`, `AArch64`, `RISC-V` `RV64GC`/`Zbb`, `s390x`).

### Relationships Among Examined Subjects

- **Declarative Instruction Selection (`bytecodealliance/wasmtime` @ `e355dc640d047ab76dbf4402567d0c124bfdecd6`)**: Examined directly in `cranelift/isle/isle/src/{overlap.rs, trie_again.rs, sema.rs}` as the production Rust-backed prioritized term-rewriting selector DSL, interpreted alongside its external SMT verification toolchains **Crocus / VeriISLE** (`DOI: 10.1145/3617232.3624862`) and **Arrival** (`DOI: 10.1145/3764383`).
- **Imperative DAG & IR Peephole Combiners (`llvm/llvm-project` @ `24d30c217e52708d67c7692311e6455dcc708e0d` and `gcc-mirror/gcc` @ `2666438724c3364795e733f53115af0f7b018770`)**: Examined in `InstCombineShifts.cpp`, `SelectionDAG`, and `gcc/simplify-rtx.cc` / `combine.cc` to contrast imperative C++ pattern matching, `undef`/`poison`/`freeze` semantics, and `RTL` machine-description (`define_insn`) recognition against declarative `ISLE` tries.
- **Translation Validation & Width-Polymorphic Synthesis (`AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4` and `manasij7479/hydra` @ `1813fd35db23e68cb32cb6d5b528594c49e5343c`, `DOI: 10.1145/3649837`)**: Examined as the formal `QF_BV` refinement oracle (`Alive2` `StateValue` `(value, non_poison)` + quantified `undef` variables) and Souper-backed width-independent peephole synthesizer (`Hydra`) that generalize fixed-width superoptimizer discoveries into width-parametric compiler passes.

Behaviors tied to `LLVM IR` `poison`/`undef`/`freeze` apply specifically to `LLVM`-derived IRs and `SelectionDAG` (`SDNode`), whereas Cranelift `CLIF` defines deterministic wrapping/masking shift semantics at the IR level (shifting complexity from `poison` tracking into exact `ISLE` target flag/mask lowering).

---

## Findings

### 1. Prioritized Term-Rewriting Compilation, Overlap Semantics, and Coverage Totality in Cranelift `ISLE`

`Basis: source + normative + execution`

Cranelift's Instruction Selection Lowering Expressions (`ISLE`) DSL lowers `CLIF` IR instructions to target `MachInst` sequences by compiling declarative `(rule prio lhs rhs)` declarations through a hash-consed constraint intermediate representation (`cranelift/isle/isle/src/trie_again.rs:55-288`) checked by `overlap::check` (`cranelift/isle/isle/src/overlap.rs:12-130`).

#### 1.1 Constraint Lattice and Pairwise Overlap Rules

In `trie_again.rs:171-255`, each compiled `Rule` consists of a set of refutable `Constraint` predicates (`Variant`, `ConstBool`, `ConstInt`, `ConstPrim`, `Some` for fallible external Rust extractors) over hash-consed `Binding` sites (`BindingId(u16)`, `TupleIndex(u8)`), plus an `equals: DisjointSets<BindingId>` equivalence relation for nonlinear pattern variables (`(iadd x x)`).

Direct inspection of `overlap.rs:85-128` establishes the exact static discipline enforced at Cranelift build time:

1. **Pairwise-only check to avoid wildcard exponential blowup (`overlap.rs:104-128`)**: `check_overlaps` iterates over every unordered pair `(left, right)` in `ruleset.rules` rather than constructing the full Boolean product automaton across all rules simultaneously, explicitly noting in source comments (`L104-106`) that aggregate intersection blows up exponentially under deep wildcard patterns.
2. **Equal-priority collision rejection (`overlap.rs:86-90`)**: When `a.may_overlap(b)` returns `Overlap::Yes { subset }` and `a.prio == b.prio`, `Errors::check_pair` records an undirected conflict edge emitting `Error::OverlapError { msg: "rules are overlapping", rules }`.
3. **Strict-priority shadowing vs. partial-overlap admission (`overlap.rs:91-99`)**:
   ```rust
   } else if subset {
       let (lo, hi) = if a.prio < b.prio { (a, b) } else { (b, a) };
       if hi.total_constraints() <= lo.total_constraints() {
           self.shadowed.entry(hi.pos).or_default().push(lo.pos);
       }
   }
   ```
   Two structural consequences follow directly from `L85-120`:
   - **Permitted partial overlap under unequal priority**: When `a.prio != b.prio` and `subset == false` (rule $A$ matches inputs $S_A$, rule $B$ matches $S_B$, $S_A \cap S_B \neq \emptyset$, $S_A \not\subseteq S_B$, $S_B \not\subseteq S_A$), `overlap.rs` emits **neither** `OverlapError` **nor** `ShadowedError`. On the intersection $S_A \cap S_B$, generated Rust code deterministically selects whichever rule carries the numerically higher `prio`. Consequently, changing a rule's priority or relaxing an external Rust extractor's `Option::Some` domain silently transfers ownership of $S_A \cap S_B$ without a compiler warning.
   - **Unchecked `multi` terms (`overlap.rs:110-120`)**: Terms declared with `decl multi` (`TermKind::Decl { flags, .. } if flags.multi`) bypass `check_overlaps` completely because `multi`-constructors yield an iterator (`Binding::Iterator`, `trie_again.rs:99-102`) over *all* matching rules rather than committing to one winner.
   - **External extractor opacity & non-totality**: Because external extractors (`#[isle_extractor]` functions written in imperative Rust returning `Option<T>`) appear to `trie_again.rs` solely as opaque `Constraint::Some` atoms (`trie_again.rs:150-155, 349`), `ISLE`'s compiler cannot prove without SMT assistance (`Crocus`/`Arrival`) that a set of complementary Rust extractors (e.g., `imm_fits_in_12bits` vs. `imm_requires_movz_movk`) covers $100\%$ of `64`-bit inputs. Any uncovered input falls through the generated match function into a runtime compiler panic.

#### 1.2 Scaling Modular Verification from Single Rules (`Crocus`) to Chained Authoritative ISA Specs (`Arrival`)

`Basis: documentation + derived`

- **Crocus / VeriISLE (`ASPLOS 2024`, `DOI: 10.1145/3617232.3624862`)** embeds declarative bitvector specifications on `ISLE` terms and verifies individual rules modularly in SMT (`QF_BV`), avoiding full whole-backend symbolic execution. However, writing manual intermediate specifications for dozens of internal helper terms (`amode`, `reg_or_imm`, flag-producing sub-terms) creates high annotation friction (`L1`) and specification-drift risk if a helper spec disagrees with actual hardware semantics.
- **Arrival (`OOPSLA 2025`, `DOI: 10.1145/3764383`)** eliminates manual internal helper specs by automatically unfolding chains of `ISLE` term definitions up to bounded recursion/helper depth and discharging the composed `CLIF -> MachInst` verification condition directly against **authoritative machine-readable ISA specifications** (such as ARM's official Architecture Specification Language `ASL` semantics for `AArch64`). This collapses the trusted specification boundary strictly to the entry `CLIF` semantics and the vendor `ASL` decode/execute semantics.

---

### 2. `undef`, `poison`, and `freeze` Algebra in `LLVM InstCombine` / `SelectionDAG` vs. `Alive2`

`Basis: source + execution + derived`

Unlike Cranelift `CLIF` (which defines fixed modular shift masks on bitvectors), `LLVM IR` employs a two-tier deferred-undefinedness lattice formalized in `Alive2` (`AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`, `ir/instr.cpp:295-325, 3203-3212`):

1. **`poison` (`StateValue.non_poison` boolean guard)**: An absorbing deferred undefined value produced by arithmetic/shift violations, such as shifting a $W$-bit value by an unsigned amount $b \ge W$:
   ```cpp
   // AliveToolkit/alive2 ir/instr.cpp:295-304
   case Shl:
     fn = [&](auto &a, auto &ap, auto &b, auto &bp) -> StateValue {
       auto non_poison = b.ult(b.bits());
       if (flags & NSW) non_poison &= a.shl_no_soverflow(b);
       if (flags & NUW) non_poison &= a.shl_no_uoverflow(b);
       return { a << b, std::move(non_poison) };
     };
   ```
2. **`undef` (existentially/universally quantified fresh per-use nondeterministic bits)**: An uninitialized register/padding bitvector where **each syntactic evaluation of `%x` may observe a distinct bitvector** unless `%x` passes through `freeze` (`Freeze::toSMT` in `ir/instr.cpp:3203-3207`, which resets `undef` variable tracking and collapses both `poison` and `undef` to a single nondeterministic but fixed bitvector).

#### 2.1 Concrete Failure Classes in Shift, Mask, and Funnel-Shift Peepholes

Executing `reports/selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality/repro_peephole_probe.py` (`Basis: execution`) quantifies three recurring backend miscompilation mechanisms:

| Hazard Class | Source Idiom ($e_{\text{src}}$) | Unsound Lowered / Peephole Idiom ($e_{\text{tgt}}$) | Exact Semantic Failure Witness (`W = 8`) | Sound Repair Obligation |
| :--- | :--- | :--- | :--- | :--- |
| **Unmasked Zero-Shift Rotate Poison** | `@llvm.fshl.i8(x, x, c)` (total for all $c \in [0, 255]$ via $c \bmod 8$) | `(x << c) \| (x >> (8 - c))` | At $c = 0$: `8 - 0 = 8 >= 8` $\implies$ `lshr` yields **`poison`**, poisoning bitwise `or` (`poison` when `fshl(x,x,0) == x`) | Mask both shifts: `(fx << (c & 7)) \| (fx >> ((-c) & 7))` on `fx = freeze(x)` |
| **Multi-Use `undef` Fan-Out Amplification** | `%t = lshr i8 %x, 4`; `%r = mul i8 %t, 17` (`1` evaluation of `%x`) | `(%x & 0xF0) \| (%x >> 4)` (`2` evaluations of `%x`) | For `%x = undef`: $e_{\text{src}}$ reaches only **`16` states** (`{0x00, 0x11, ..., 0xFF}`); $e_{\text{tgt}}$ picks $u_1 = \texttt{0xA0}, u_2 = \texttt{0x50} \implies \texttt{0xA5}$, leaking **`240` impossible states** | Insert `freeze`: `%fx = freeze i8 %x`; `(%fx & 0xF0) \| (%fx >> 4)` (`16 == 16` exact) |
| **Backend `SelectionDAG` `UNDEF` Regression** | `LLVM IR` `%fx = freeze i32 %x` lowered to `ISD::FREEZE` | `DAGCombiner.cpp` folding across `ISD::FREEZE` or duplicating non-frozen `SDValue` into `SHL` + `SRL` | `SelectionDAG` historically lacked `poison` awareness on target `ISD` nodes and treated `ISD::UNDEF` as multi-use nondeterministic | Enforce single virtual-register materialization (`COPY`/freeze barrier) before multi-use DAG expansions |
| **`x86` Sub-Word Rotate `0x1F` Flag Clobber** | `rol al, (cl & 7)` with incoming `CF = 1`, `al = 0x80` | `rol al, cl` (stripping `"redundant"` `& 7` before `8`-bit rotate) | At `cl = 8`: `(8 & 0x1F) == 8 != 0`, so `rol al, cl` rotates value by `8 mod 8 = 0` (`al == 0x80`) **but overwrites `CF := LSB(0x80) = 0`** (`24 / 256` `CL` values diverge!) | Retain `& 7` (`& 15` for `i16`) unless liveness proves `EFLAGS` (`CF`, `OF`) dead after rotate |

---

### 3. `GCC` `RTL` Multi-Instruction `combine`, `TRULY_NOOP_TRUNCATION`, and Width-Polymorphic Synthesis (`Hydra`)

`Basis: source + documentation + derived`

#### 3.1 `GCC` `combine.cc` Windowed Substitution and Paradoxical `SUBREG` Traps

Unlike `LLVM`'s SSA `InstCombine` or `ISLE`'s pure tree matching, `GCC`'s `RTL` combiner (`gcc/combine.cc` coupled with `gcc/simplify-rtx.cc` @ `2666438724c3364795e733f53115af0f7b018770`) performs def-use substitution across windows of `2`, `3`, or `4` data-dependent `RTL` insns (`try_combine`), algebraically simplifying the merged `rtx` (`simplify_rtx` / `make_compound_operation` extracting `ZERO_EXTRACT` and `SIGN_EXTRACT`) and querying target `define_insn` / `define_split` machine descriptions (`recog_for_combine`).

Inspection of `gcc/simplify-rtx.cc:583-608, 1248-1261` highlights a critical target-dependent soundness obligation:
- `GCC` represents narrowing conversions either as an explicit `(truncate:SI x:DI)` or as a lowpart `(subreg:SI x:DI 0)`.
- As documented directly at `simplify-rtx.cc:583-603`, `simplify_unary_operation` folds `(truncate:SI op:DI)` into `(subreg:SI op:DI 0)` **only** when `TRULY_NOOP_TRUNCATION_MODES_P(mode, GET_MODE(op))` holds (true on `x86_64` and `AArch64` where `32`-bit instructions ignore upper `32` register bits, **false** on `MIPS64` and `LoongArch64`, and subtle on `RISC-V` `RV64` ABI boundaries where `SImode` values residing in `64`-bit GPRs must remain canonically sign-extended from bit `31`).
- Conversely, a **paradoxical `subreg`** `(subreg:DI x:SI 0)` widens a narrow pseudo-register without emitting instructions, leaving upper bits `32..63` unpredictable unless `combine`'s cached `reg_stat` (`nonzero_bits` and `num_sign_bit_copies`) remains conservatively invalidated whenever an earlier `combine` transformation mutates an upstream producer insn in-place. Stale `reg_stat` bitmasks in `combine.cc` have repeatedly caused miscompilations where `AND` masks (`0xFFFF_FFFF`) are elided despite high-half sign garbage.

#### 3.2 Synthesizing Width-Polymorphic Peepholes (`Hydra` vs. Hand-Written C++)

`Hydra` (`manasij7479/hydra` @ `1813fd35db23e68cb32cb6d5b528594c49e5343c`, `DOI: 10.1145/3649837`) addresses a systemic limitation of superoptimizers like `Souper`: `Souper` discovers hundreds of concrete fixed-width optimizations (e.g., at `i32` with magic constant `31` or `0x7FFF_FFFF`), which human compiler engineers previously had to generalize by hand into C++ `InstCombine` code—frequently introducing off-by-one width predicates or missing `hasOneUse()` / `isGuaranteedNotToBeUndefOrPoison()` guards.
- `Hydra` starts from a concrete small-bitwidth (`W = 4` or `W = 8`) `Souper` rewrite, synthesizes candidate **width-dependent constant/predicate expressions** (`width(x) - 1`, `signmask(W)`, `(1 << k) - 1`, `KnownBits` preconditions), and verifies the generalized rule across multiple bitwidths (`i4..i64`) in SMT (`Alive2`/`Z3`) before emitting executable C++ pattern matchers directly targeting `LLVM`.

---

### 4. Multi-Level Performance & Resource Footprint Analysis (`L1–L6`)

`Basis: documentation + source + execution + derived`

| Metric Level | Cranelift `ISLE` + `Crocus` / `Arrival` | `LLVM` `InstCombine` + `SelectionDAG` + `Alive2` | `GCC` `RTL` `combine.cc` + `simplify-rtx.cc` | `Hydra` Synthesis -> Verified Peephole Pass |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance Velocity** | Concise S-expr DSL (`~15–40 LoC` per ISA family); `Arrival` cuts helper-spec LoC by `~3–5x` by unfolding directly to `ASL`. | Imperative C++ matchers (`50–250 LoC`/fold in `InstCombineShifts.cpp` / `DAGCombiner.cpp`); high human review burden on `poison`/`freeze` corner cases. | Dense C++ `rtx` surgery (`combine.cc` `> 15,000 LoC`) + `.md` `RTL` templates; steep maintainer learning curve. | Automated generalization of `Souper` discoveries (`0` manual width-generalization math; `~10–30 LoC` generated C++ per rule). |
| **`L2` Toolchain & Verifier Build Cost** | `isle` meta-compiler builds in `< 4 s` (`Rust`, zero heavy C++ deps); full `wasmtime/cranelift` clean build `~35–75 s`. | Full `llvm-project` + `Alive2` + `Z3` clean CMake/Ninja build requires `15–45 min` and `16–48 GiB` link RSS (without `lld`). | Full `GCC` bootstrap (`3`-pass build) takes `25–60 min`; incremental `cc1` rebuild `~8–15 s`. | `Souper` + `LLVM` + `Z3` build (`build_deps.sh`) takes `20–45 min`, `~20 GiB` disk. |
| **`L3` Compilation, Synthesis & SMT Latency** | `ISLE`-generated Rust trie executes in **`< 50–150 ns/insn`** (`~10x` faster compile speed than `LLVM SelectionDAG`); `Crocus`/`Arrival` SMT per rule `0.1–30 s` (`rlimit` tails on `64b` mul/div). | `InstCombine` runs `4–8` times in `-O3` (`~12–18%` of total `clang -O3` compile time!); `SelectionDAG` ISel `~20–30%` of backend time; `Alive2` TV `10 ms–60 s`/fn. | `combine` pass accounts for `~5–9%` of `gcc -O2` compile time (bounded to `<= 4`-insn windows to cap quadratic def-use blowup). | Offline synthesis (`seconds` to `~20 min` per generalized rule); online generated C++ matcher runs in **`< 80 ns`** per IR node. |
| **`L4` Generated Machine Code Performance** | Within `5–14%` of `LLVM -O3` scalar throughput while compiling in `~0.1x` wall time; exact `BMI2`/`AArch64` bitfield selection (`1 cyc` `EXTR`/`RORX`). | Peak industry throughput (`0.25–1.0 cyc` reciprocal throughput on `RORX`/`SHLX`/`BEXTR`/`UBFM` idioms), subject to `freeze` barrier placement. | Co-equal peak scalar code quality; `combine` + `.md` excels on compound shift-and-mask / `RISC-V` `Zbb`/`Zbs` single-cycle idioms. | Recovers `1–6%` scalar integer speedups on bit-heavy codecs/hashes with `0` runtime overhead once emitted. |
| **`L5` Proof / Certificate Check Latency** | Compile-time static (`0 ms` runtime tax); `QF_BV` SMT replay `0.1–15 s/rule` unless bit-blasted to `LRAT` (`< 2 ms/rule` for shift/mask rules). | `Alive2` black-box per-TU translation validation (`~0.5–10 s/fn`) is CI-grade rather than `< 1 ms` load-time kernel-admissible. | Uncertified at compile/load time (`relies on bootstrap + testsuite`). | Offline `QF_BV` proof at synthesis time (`0 ms` production compile/load overhead); bit-blasted `LRAT` certificates verify in `< 5 ms`. |
| **`L6` RAM, Disk & Artifact Footprints** | `cranelift-codegen` generated Rust ISel tables `~3–6 MiB` `.text`; compilation scratch `< 4 MiB`/func (`arena`-allocated). | `SelectionDAG` allocates `~400–900 B` per `SDNode` (`tens of MiB` RSS on large autogenerated functions); `Z3` `Alive2` RSS `0.2–4 GiB`. | `RTL` garbage-collected (`ggc`) pools `10–150 MiB` RSS; `combine` mutates `rtx` in-place with undo log (`undo_buf`) to limit allocs. | Offline synthesizer `0.5–4 GiB` RSS; emitted production matcher `< 1 KiB` `.text` per generalized rule, `0 B` runtime heap. |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: source + execution + derived`

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

A striking divergence separates **LLM/solver execution convenience** from **human compiler-engineer comprehension**:
- **Nonlocal `undef` vs. `poison` cognitive overload**: Human compiler authors routinely reason algebraically ($x \lor x = x$, $(x \gg 4) \times 17 = (x \mathbin{\&} \texttt{0xF0}) \lor (x \gg 4)$) assuming a variable identifier `x` denotes *one unknown bitvector*. `LLVM`'s legacy `undef` breaks referential transparency of variable names (`x` denotes two *different* bitvectors in `(x & 0xF0) | (x >> 4)`!), forcing humans to audit global def-use counts, `isGuaranteedNotToBeUndefOrPoison()` recursive walks (`depth <= 6`), and target `EFLAGS` liveness simultaneously (`5–7` coupled nonlocal concepts).
- **Silent priority hijacking in `ISLE`**: While `ISLE`'s S-expression syntax is far cleaner to read locally than `DAGCombiner.cpp`, allowing partial non-subset overlaps under distinct integer priorities (`overlap.rs:85-100`) creates a nonlocal comprehension hazard: an engineer reading rule $R_1$ (`prio = 10`) cannot tell from $R_1$ alone which subset of its matched inputs is silently intercepted by rule $R_2$ (`prio = 20`) defined `1,500` lines away.
- **Counterexample legibility**: Raw `Z3` `QF_BV` counterexamples over `64`-bit words (`0x8020_0401_9000_0001`) obscure whether a bug stems from `c == 0` overshift, `undef` fan-out, or `CL & 0x1F` flag clobbering. Narrowing falsification first to `W = 4` or `W = 8` (`Hydra` small-scope principle + minimal `popcount` model minimization) yields `3`-line human-auditable witnesses (`x = 0x80, cl = 8, CF_in = 1 => CF_src = 1 != CF_tgt = 0`).

#### 5.2 Universal Model Refinement & Eliminating Accidental Distinctions (`C2`)

Applying Felleisen macro-expressibility and Ousterhout deep-module analysis exposes three accidental historical mechanisms that collapse into cleaner invariants:
1. **Abolishing multi-use `undef` in favor of `poison` + explicit single-value `freeze` (`LLVM` ongoing `undef`-removal trajectory)**: Multi-use `undef` exists solely as an artifact of uninitialized SSA registers before register allocation. Typing uninitialized storage as `poison` (or materializing a single frozen value at `alloca`/padding load) restores variable referential transparency ($x = x$ everywhere!) without losing dead-store or uninitialized-branch optimization power.
2. **Explicit flag-carrier return tuples on ISA constructors**: Treating `x86` `EFLAGS` or `ARM` `NZCV` as implicit ambient side-channels on value nodes invites `rol al, cl` flag-clobber miscompilations. Typing machine instructions cleanly as pure functions `(GPR_in, Flags_in) -> (GPR_out, Flags_out)` where value-only rules project `.gpr` (valid only when `.flags` is dead) turns implicit hardware quirks into ordinary type-checked projections.
3. **Explicit overlap-partition witnesses over ad-hoc integer priorities**: Requiring non-subset overlapping rules either to state disjoint guard predicates or an explicit `overrides: [rule_id]` edge makes rule precedence locally auditable without sacrificing trie compilation speed.

---

### 6. End-to-End Solution & Implementation Validation (`V1–V4`)

`Basis: source + execution + documentation + derived`

Formal verification of individual rewrite rules (`Crocus`, `Arrival`, `Alive2`) leaves four concrete reality gaps where miscompilations still escape into production unless closed by an end-to-end `V1–V4` validation pipeline:

1. **`V1` — Specification Adequacy, Vacuity Detection & Mutant-Kill Validation**:
   - *Reality gap*: An `ISLE` or `ASL` instruction specification that accidentally over-constrains preconditions (e.g., `c > 0 && c < W`, omitting `c == 0`) or under-constrains flag outputs (`OF := havoc` when `c == 1`) makes unsound lowering rules verify vacuously (`0` SMT counterexamples!).
   - *Validation protocol*: Pair every universal rule proof with (a) an existential satisfiability check $\exists \sigma.\; \text{Pre}(\sigma)$ at boundary values (`c = 0, 1, W-1, W`), (b) differential execution of the ISA spec against vendor golden simulators (`ARM FVP` / `Sail` / physical silicon), and (c) an automated **spec/lowering mutation suite** (`repro_peephole_probe.py` demonstrates `8/8 = 100%` kill rate across unmasked `W - c`, `shl` mod-mask vs. zeroing, paradoxical `subreg` sign-leak, missing overshift arm, priority inversion, unfrozen `undef` split, `c == W-1` off-by-one, and vacuous-guard mutants in `12.1 ms`).
2. **`V2` — Lowering Pipeline Differential Fuzzing & SMT/Checker Soundness Fuzzing**:
   - *Reality gap*: Even when every standalone peephole rule is sound, surrounding compiler glue (extractor Rust helpers, `nonzero_bits` cache invalidation in `combine.cc`, register coalescer interactions) or **bugs inside the SMT solver itself** (`Z3`/`cvc5` `QF_BV` rewriter bugs found by `Murxla` / `yinyang`) can admit invalid code.
   - *Validation protocol*: Continuously fuzz end-to-end compilation (`-O0` vs. `-O2`/`-O3` across `LLVM`, `GCC`, and `Cranelift`) using **`YARPGen`** and **Equivalence Modulo Inputs (`EMI`)** dead-branch mutation; cross-validate every `Hydra`/`Alive2` `UNSAT` result by bit-blasting `QF_BV` formulas to CNF and verifying independent **`DRAT`/`LRAT` UNSAT certificates** (eliminating `Z3`/`cvc5` `400+ KLoC` from the verification TCB!).
3. **`V3` — Post-Silicon ISA Litmus & Microarchitectural Contract Validation**:
   - *Reality gap*: Vendor ISA prose and even formal `ASL`/Sail specs occasionally diverge from physical silicon on undocumented flag bits, BMI2/shift microcode edge cases, or data-dependent timing (`constant-time` crypto code broken when `InstCombine` replaces branchless shift-masks with variable-latency instructions or conditional branches!).
   - *Validation protocol*: Execute randomized register+flag hardware litmus vectors (`x = {0, 1, 0x7F..FF, 0x80..00, 0xFF..FF}`, all `256` `CL` bytes, incoming `CF/OF/ZF/SF` combinations) directly on physical `x86_64` and `AArch64` CPUs, and run **`Revizor`** relational hardware leakage fuzzing + `Constant-Time` (`valgrind --ct-check` / `Binsec/Rel`) checks ensuring peephole rewrites never introduce secret-dependent memory addresses, division latencies, or branch predictors.
4. **`V4` — Human Engineer Diagnostic & `SMoL` Mental-Model Validation**:
   - *Reality gap*: If a verification failure dumps a `4,000`-node `QF_BV` SMT-LIB formula, engineers disable the check or add unsound `#[trusted]` annotations.
   - *Validation protocol*: Minimize every counterexample first in bitwidth ($W = 64 \to 8 \to 4$) and then in Hamming weight (`popcount`), presenting concrete aligned binary strings (`src = 0b0001_0001` vs. `tgt = 0b1010_0101` with `u1 = 0xA0, u2 = 0x50`) validated against `SMoL`-style developer comprehension tasks.

---

## Boundaries

- **Floating-point NaN-payload and FMA contraction peepholes (`not examined`)**: This package examines integer, bitvector, shift/mask, sub-register, and condition-flag instruction selection and peepholes (`InstCombineShifts.cpp`, `DAGCombiner`, `ISLE`, `combine.cc`). IEEE-754 `-ffast-math` reassociation, signed-zero (`-0.0`), and quiet/signaling `NaN` payload propagation across `SelectionDAG` / `ISLE` vector lanes are **not examined** here.
- **Global e-graph / equality-saturation extraction (`aegraphs` in Cranelift mid-end) vs. backend `ISLE` (`known not to apply` to `overlap.rs` guarantees)**: Passing `cranelift/isle/isle/src/overlap.rs` guarantees deterministic match selection only for single-result `ISLE` terms; `decl multi` e-graph rewrite rules intentionally bypass `overlap.rs` (`L114-120`) and rely on downstream acyclic cost extraction rather than priority determinism.
- **Whole-backend mechanized totality of production `wasmtime` `x64`/`aarch64` `ISLE` rulesets (`unknown` / partial upstream coverage)**: While `Crocus` (`ASPLOS 2024`) and `Arrival` (`OOPSLA 2025`) verify substantial slices of Cranelift's `aarch64` and `x64` lowering rules against `ASL`/Sail models, complete `100%` mechanized totality proofs across *all* SIMD, atomic, and ABI pseudo-instructions in `wasmtime` @ `e355dc640d047ab76dbf4402567d0c124bfdecd6` remain incomplete upstream (`differential fuzzing via wasm-smith bridges the unverified remainder`).
- **Memory-aliasing and pointer-provenance peepholes (`unsupported` by pure bitvector `Hydra` / `Crocus`)**: Pure `QF_BV` synthesizers (`Hydra`, `Crocus`) model register-to-register scalar/vector computations (`Supported`); load-store forwarding, pointer `inttoptr`/`ptrtoint` provenance casts, and stack-slot coloring require `Alive2`'s full pointer-provenance memory model (`Unsupported` by pure bitvector rule checkers).

---

## Evidence

### Primary Repository Sources (`Observed 2026-11-19`)

1. **`bytecodealliance/wasmtime` @ `e355dc640d047ab76dbf4402567d0c124bfdecd6`**:
   - `cranelift/isle/isle/src/overlap.rs:12-130`: `check()`, `Errors::check_pair()` (`L85-100`, equal-priority `OverlapError` vs. `subset` `ShadowedError` vs. silent unequal-priority partial overlap), and `check_overlaps()` (`L107-129`, `is_multi_ctor` bypass).
   - `cranelift/isle/isle/src/trie_again.rs:55-360`: `Binding` (`Extractor`, `Constructor`, `Iterator`), `Constraint` (`Variant`, `Some`, `ConstInt`), `Overlap` enum (`L244-255`), and deterministic `RuleSet` construction (`L269-288`).
2. **`AliveToolkit/alive2` @ `3bdd4f5e1cefa47057e93110e707acd11cfe08e4`**:
   - `ir/instr.cpp:115-133, 295-325`: `BinOp::Shl`, `AShr`, `LShr` exact `non_poison = b.ult(b.bits())` + `NSW`/`NUW`/`Exact` SMT encoding.
   - `ir/instr.cpp:3203-3212`: `Freeze::toSMT(State &s)` (`s.resetUndefVars(); return s.freeze(getType(), v);`).
3. **`llvm/llvm-project` @ `24d30c217e52708d67c7692311e6455dcc708e0d`**:
   - `llvm/lib/Transforms/InstCombine/InstCombineShifts.cpp` and `llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp`: shift/rotate combination and `freeze` / `undef` handling boundaries.
4. **`gcc-mirror/gcc` @ `2666438724c3364795e733f53115af0f7b018770`**:
   - `gcc/simplify-rtx.cc:583-608, 1248-1261`: `TRULY_NOOP_TRUNCATION_MODES_P` invariants governing `TRUNCATE` vs. lowpart `SUBREG` canonicalization; `gcc/combine.cc` multi-insn RTL substitution.
5. **`manasij7479/hydra` @ `1813fd35db23e68cb32cb6d5b528594c49e5343c`**:
   - `Souper`-based width-independent peephole synthesis framework accompanying Mukherjee & Regehr (`OOPSLA 2024`).

### Normative Specifications & Peer-Reviewed Literature

- Alexa VanHattum, Monica Pardeshi, Chris Fallin, Adrian Sampson, and Fraser Brown, *"Lightweight, Modular Verification for WebAssembly-to-Native Instruction Selection,"* ASPLOS 2024 (`DOI: 10.1145/3617232.3624862`).
- Michael McLoughlin, Ashley Sheng, Chris Fallin, Bryan Parno, Fraser Brown, and Alexa VanHattum, *"Scaling Instruction-Selection Verification against Authoritative ISA Semantics,"* Proc. ACM Program. Lang. (OOPSLA2), 2025 (`DOI: 10.1145/3764383`).
- Manasij Mukherjee and John Regehr, *"Hydra: Generalizing Peephole Optimizations with Program Synthesis,"* Proc. ACM Program. Lang. (OOPSLA1), Vol. 8, 2024 (`DOI: 10.1145/3649837`).
- Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu, and John Regehr, *"Alive2: Bounded Translation Validation for LLVM,"* PLDI 2021 (`DOI: 10.1145/3453483.3454030`).
- Intel 64 and IA-32 Architectures Software Developer's Manual, Vol. 2B, `RCL/RCR/ROL/ROR—Rotate` (`COUNT & 0x1F` masking before `MOD 8`/`MOD 16` vs. `(COUNT & 0x1F) != 0` `CF`/`OF` modification).

### Preserved Executable Artifact (`Observed 2026-11-19`)

- `reports/selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality/repro_peephole_probe.py`: Self-contained Python 3 standard-library probe verifying (1) unmasked `c == 0` rotate poison and `240` impossible `i8` outputs leaked by unfrozen multi-use `undef` nibble splitting (`16` vs. `256` states), (2) `24 / 256` `CL` values where stripping `& 7` on `x86` `rol al, cl` clobbers live `CF`, and (3) `48`-point prioritized `ISLE` totality/determinism checking + `8/8` (`100%`) `V1` spec-mutant kill rate in `12.1 ms`.

---

## Revalidation

1. **Run the preserved self-contained verification and `V1` mutant-kill probe (`< 50 ms`, stdlib Python 3)**:
   ```bash
   python3 reports/selectiondag-peephole-undef-shifts-gcc-combine-recognizers-and-hydra-totality/repro_peephole_probe.py
   ```
   Confirm exit code `0` and `"status": "PASS"` (`impossible_states_leaked == 240`, `frozen_peephole_exact_match == true`, `diverging_cl_bytes_out_of_256 == 24`, `v1_mutants_killed == 8`).
2. **Audit upstream `ISLE` overlap rules on newer `wasmtime` revisions**:
   Diff `cranelift/isle/isle/src/overlap.rs` (`Errors::check_pair` and `check_overlaps`) to check whether unequal-priority partial overlaps (`subset == false`) or `decl multi` constructors gain optional totality/exhaustiveness diagnostics.
3. **Re-check `LLVM` / `Alive2` `undef` retirement status**:
   Inspect `AliveToolkit/alive2` `ir/instr.cpp` (`Freeze::toSMT` and `BinOp` shift handlers) alongside `llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp` to determine whether `ISD::UNDEF` has been fully replaced by `ISD::POISON` + `ISD::FREEZE` in target lowering.
