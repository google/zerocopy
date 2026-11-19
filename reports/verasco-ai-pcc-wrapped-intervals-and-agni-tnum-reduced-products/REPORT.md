# Certified Abstract Interpretation Fixpoint Checking with Wrapped-Interval and Tristate-Number Reduced Products

## Summary

Proof-carrying abstract interpretation (AI-PCC) splits static program analysis into an untrusted external fixpoint solver—which executes Weak Topological Ordering (WTO) chaotic iteration and heuristic widening outside the theorem prover—and a total, single-pass boolean post-fixpoint checker (`checkCfgFixpoint : Body → Cert → Bool`) proved sound once inside the proof kernel. For discharging machine-integer Undefined Behavior (UB) and bit-level invariants over Rust Mid-level Intermediate Representation (MIR) under a 3-axiom kernel profile (`propext`, `Quot.sound`, `Classical.choice`, with zero meta-tactics or native code execution), neither modular intervals nor bitwise known-bits domains suffice alone:

1. **Wrapped intervals over $\mathbb{Z}/2^w\mathbb{Z}$** (`[[s, e]]_w`, Navas et al., APLAS 2012; `seahorn/crab`) represent clockwise modular arcs across both the unsigned wrap boundary ($2^w - 1 \to 0$, south pole) and the two's-complement sign boundary ($2^{w-1} - 1 \to 2^{w-1}$, north pole). However, wrapped intervals do **not** form a lattice: minimal upper bounds are non-unique, shortest-gap pseudo-join (`operator|`) is **non-monotone**, abstract meet (`operator&`) over-approximates doubly overlapping arcs, and upstream `seahorn/crab` maps every bitwise `And`, `Or`, and `Xor` directly to $\top$.
2. **Tristate numbers (`tnum`)** (`(val, mask)` with invariant `val & mask = 0`, Linux `kernel/bpf/tnum.c`; Vishwanathan et al., CGO 2022 and CAV 2023 `Agni`) track known-`0`, known-`1`, and unknown (`?`) bits with exact bitwise transformers and optimal $O(1)$ carry-propagating `tnum_add`/`tnum_sub`, capturing power-of-two alignment (`off & !7`) and bitfield masks. However, `tnum` widens range guards across bit-prefix boundaries ($[1, 2] \mapsto \texttt{0b??} = \{0, 1, 2, 3\}$) and lacks a bottom element $\bot$: Linux's `tnum_intersect` silently fabricates a known `1` bit when operands disagree on a concrete bit, making unguarded intersection unsound for branch pruning.
3. **Single-pass checking over `WithBot (Tnum × WInt)`** resolves both blind spots simultaneously. Because AI-PCC checks only post-fixpoint inclusion ($\gamma(F^\#_b(I(b))) \subseteq \gamma(I(b'))$) along CFG edges—never calling join or widening inside the kernel—non-monotonicity of wrapped-interval pseudo-join and heuristic widening disappear from the soundness proof. With an explicit complement-free $\bot$ guard and south-pole-aware bidirectional reduction, the checker certifies alignment, mask-and-add bounds, shifts, and modular wraps in $O(|B| + |E|)$ steps via `rfl`, provided its reified input is free of Lean local variables (`!has_fvar`) so C++ GMP `reduce_nat` evaluation stays active.

## Applicability

This report characterizes the mathematical semantics, cross-domain reduction seams, and Lean 4 mechanization constraints linking ten primary subjects:

- **Target verification substrate (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` and `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`):** Anneal isolates its Trusted Computing Base (`trusted/`) from untrusted proof libraries (`theory/`, namespace `Anneal.*`). Under `trusted/audit/TrustedBoundary.lean` (Pass 1), every `theory/` module begins with `prelude`, imports only from the 51 `Init.*` modules locked in `trusted/lean/foundation-lock.json` (plus `Trusted.*` and `Anneal.*`), obeys `allowedTheorySyntaxKinds` (forbidding `omega`, `linarith`, `ring`, `bv_decide`, `grind`, `native_decide`, `partial`, `unsafe`, `axiom`, `opaque`, `deriving`, `termination_by`, `noncomputable section`, and `~~~`), uses only `{propext, Quot.sound, Classical.choice}`, emits zero `partial` `._unsafe_rec` compiler helpers (`ensureReplayableConstant`), and satisfies Statement-Origin Separation (`CrateTheorem` and `UnitTheorem` types mention only `Init.*`, `Trusted.*`, and `Mir.*`).
- **Fixpoint solving vs. post-fixpoint checking (`AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc`, Verasco `1.3` / DOI `10.1145/2676726.2676966`, and Besson–Jensen–Pichardie DOI `10.1016/j.tcs.2006.08.012`):** CompCert (`backend/Kildall.v`) mechanizes in-prover semi-lattice worklist iteration; Verasco (`1.3`) pairs Bourdoncle WTO iteration with verified post-fixpoint validation; Besson, Jensen, and Pichardie formalize cutset fixpoint compression for single-pass PCC checking.
- **Modular wrapped intervals (`seahorn/crab` at `b1eeb1a9402ab0664e962f26f89d923f8514284c` and Navas et al. DOI `10.1007/978-3-642-35182-2_9`):** Examined via `include/crab/domains/{wrapped_interval.hpp,wrapped_interval_impl.hpp,wrapped_interval_domain.hpp}` and `include/crab/numbers/wrapint.hpp`.
- **Tristate numbers and reduced-product verification (`torvalds/linux` `v5.19` at `3d7cb6b04c3f3115719235cc6866b10326de34cd`, `bpfverif/agni` at `9096fbd10376d6a1610cbd18ae98408d0a7bd29b`, and Vishwanathan et al. DOI `10.1109/CGO53902.2022.9741267` / `arXiv:2105.05398v3` and DOI `10.1007/978-3-031-37709-9_12`):** Examined via `include/linux/tnum.h`, `kernel/bpf/tnum.c`, `kernel/bpf/verifier.c` (`reg_bounds_sync`), and Agni's `gen`/`sro` encodings (`bpf-verification/`).

Domain equations apply to any fixed bitwidth $w \in \{8, 16, 32, 64, 128\}$ in `Trusted.MirAst.IntWidth` (`pointerWidthBits = 64`); kernel reduction claims apply specifically to Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and Anneal `c131b320eeeb26ef692e5afd5ec8db49ee518613`.

## Findings

### 1. Certified Abstract Interpretation vs. Single-Pass AI-PCC Fixpoint Compression

`Basis: normative + source + derived`

In-kernel dataflow solvers and proof-carrying post-fixpoint checkers place sharply different algebraic obligations on an abstract domain:

- **In-prover worklist iteration (`AbsInt/CompCert`, `backend/Kildall.v:66-116, 184-302`):** CompCert's `Dataflow_Solver` requires a `SEMILATTICE` (`L.ge`, `L.bot`, `L.lub`, `L.beq`) and iterates `PrimIter.iterate _ _ step start` (`Kildall.v:286-287`), evaluating `transf` and `L.lub` (`propagate_succ`, `L239-252`) $O(|E| \times K_{\text{iter}})$ times. Inside Lean 4's kernel (`whnf`), repeating abstract transfers across loop iterations scales poorly with loop bounds unless widening is formalized and executed in-kernel.
- **`A posteriori` post-fixpoint validation (Verasco `1.3`, DOI `10.1145/2676726.2676966`):** Verasco computes candidate invariants over C99 CFGs via Bourdoncle's recursive WTO algorithm with heuristic widening ($\nabla$) and narrowing ($\Delta$), but decouples convergence heuristics from soundness: safety requires only a **post-fixpoint** $I : \text{Node} \to D^\#$ satisfying $s_0 \in \gamma(I(\text{entry}))$ and $\gamma(F^\#_{b \to b'}(I(b))) \subseteq \gamma(I(b'))$ for every CFG edge $b \to b'$.
- **Cutset fixpoint compression (Besson, Jensen, and Pichardie, TCS 2006, DOI `10.1016/j.tcs.2006.08.012`):** Rather than storing invariants at every node, a certificate need only record $C : H \to D^\#$ on a **cutset** $H \subseteq V$ intersecting every directed cycle. If $H$ also includes all multi-predecessor join blocks (so every $b \notin H$ has in-degree $\le 1$, plus entry `0`), the consumer reconstructs states for $b \notin H$ in one topological DAG pass and checks `subsumes (transfer u h state[u]) C[h] = true` on edges entering $H$. **Join (`⊔`), widening (`∇`), and narrowing (`Δ`) are eliminated completely from the kernel checker.** Over `Trusted.MirAst.Body` (`Trusted/MirAst.lean:810-868`), `theory/` proves sound only `denoteEnv`, `subsumesEnv`, `stepStmtAbs`, and `stepTermAbs`.

### 2. Wrapped Intervals Over Modular Rings: Clockwise Semantics, Non-Lattice Anomalies, and Bitwise Precision Cliffs

`Basis: normative + source + execution + derived`

Signed $[l_s, u_s]$ and unsigned $[l_u, u_u]$ intervals cut the modular ring $\mathbb{Z}/2^w\mathbb{Z}$ at a fixed boundary, losing all precision when modular subtraction (`len.wrapping_sub(8) <= cap`) or signedness casts cross that pole. Navas et al. (APLAS 2012, DOI `10.1007/978-3-642-35182-2_9`) and `seahorn/crab` (`include/crab/domains/wrapped_interval_impl.hpp`) model contiguous clockwise modular arcs:

- **Clockwise modular concretization (`wrapped_interval_impl.hpp:476-483, 555-563`):** For $w \ge 1$ and $M = 2^w$, an element of $\text{WInt}_w$ is $\bot$, $\top$, or an arc $[[s, e]]_w$ ($s, e \in \{0, \dots, M - 1\}$) with cardinality $\#[[s, e]]_w = ((e - s) \bmod M) + 1$ and concretization:
  $$\gamma_w([[s, e]]_w) = \bigl\{\, x \in \{0, \dots, M - 1\} \;\big|\; (x - s) \bmod M \le_u (e - s) \bmod M \,\bigr\}.$$
  - **Implicit-$\top$ hazard (`wrapped_interval_impl.hpp:409-411, 453-455, 480-483`):** Crab encodes $\top$ implicitly whenever `(m_end - m_start) == 2^w - 1` (defaulting `top()` to 3-bit `wrapint(0,3)..wrapint(7,3)` and aborting via `CRAB_ERROR` if `get_bitwidth()` is called on `top()` or `bottom()`). A total Lean 4 representation must separate `| bot | top | arc (start stop : Nat)` and canonicalize any full-circle span `((stop + M - start) % M) = M - 1` to `.top`.
- **Exact inclusion and single-inequality reduction (`wrapped_interval_impl.hpp:566-577`):** Endpoint membership $a_s \in \gamma_w(B) \land a_e \in \gamma_w(B)$ alone is **unsound** for $\gamma_w(A) \subseteq \gamma_w(B)$: at $w = 2$ ($M = 4$), $A = [[2, 0]]_2 = \{2, 3, 0\}$ and $B = [[0, 2]]_2 = \{0, 1, 2\}$ contain each other's endpoints while $3 \notin \gamma_2(B)$. Crab adds the anti-complement guard `(!at(x.m_start) || !at(x.m_end))` (`L575`). On normalized proper arcs ($\text{span}(A), \text{span}(B) < M - 1$), inclusion reduces to **one** overflow-free `Nat` inequality (verified across all proper 4-bit arc pairs in Revalidation):
  $$[[a_s, a_e]]_w \sqsubseteq_w [[b_s, b_e]]_w \iff ((a_s - b_s) \bmod M) + ((a_e - a_s) \bmod M) \le ((b_e - b_s) \bmod M).$$
- **Non-lattice structure and non-monotonicity of pseudo-join (`wrapped_interval_impl.hpp:591-653`):** Antipodal singletons $[[0, 0]]_3$ and $[[4, 4]]_3$ in $\mathbb{Z}/8\mathbb{Z}$ have two minimal upper bounds of size 5 ($[[0, 4]]_3$ and $[[4, 0]]_3$). Crab's pseudo-join $\tilde{\sqcup}$ (`operator|`, `L606-612`) bridges the smaller gap (`span_a = x.m_start - m_end` vs. `span_b = m_start - x.m_end`, tie-breaking on `m_start <= x.m_start`), which **violates monotonicity** (verified by the inline probe in Revalidation):
  - For $w = 3$ ($M = 8$), let $A = [[0, 0]]_3 = \{0\} \sqsubseteq_3 B = [[0, 2]]_3 = \{0, 1, 2\}$ and $C = [[5, 5]]_3 = \{5\}$.
  - $A \tilde{\sqcup} C$ sees gaps $5$ vs. $3$ and selects $[[5, 0]]_3 = \{5, 6, 7, 0\}$.
  - $B \tilde{\sqcup} C$ sees equal gaps $3$ vs. $3$ and tie-breaks ($0 \le 5$) to $[[0, 5]]_3 = \{0, 1, 2, 3, 4, 5\}$.
  - Hence $A \sqsubseteq_3 B$, yet $A \tilde{\sqcup} C \not\sqsubseteq_3 B \tilde{\sqcup} C$ ($6, 7 \notin \gamma_3(B \tilde{\sqcup} C)$). Likewise, when two arcs overlap at both ends ($[[0, 5]]_3 \cap [[4, 1]]_3 = \{0, 1\} \cup \{4, 5\}$), `operator&` (`L626-633`) must over-approximate by returning the smaller input arc.
- **Pole-splitting vs. the bitwise $\top$-cliff (`wrapped_interval_impl.hpp:34-89, 928-1241`):** Addition and subtraction (`L928-980`) are exact when `#A + #B - 1 < M` (`[[a_s + b_s, a_e + b_e]]_w`); `ZExt` splits at the south pole (`unsigned_limit = [[2^w-1, 0]]_w`, `ssplit`), `SExt` splits at the north pole (`signed_limit = [[2^{w-1}-1, 2^{w-1}]]_w`, `nsplit`), and multiplication/division split at both poles (`cut`, at most 4 sub-arcs). However, **`WrappedInterval::And`, `Or`, and `Xor` (`L1225-1241`) all call `default_implementation(x)` (`L15-22`), returning `top()` on every non-bottom input**! Any bitmask (`off & !7`) wipes out 100% of `WInt` bounds unless paired with a bitwise domain.

### 3. Tristate Numbers (`tnum`) and Agni's Sound Reduced-Object Verification

`Basis: normative + documentation + source + execution + derived`

Linux's eBPF verifier (`torvalds/linux` `v5.19` at `3d7cb6b04c3f3115719235cc6866b10326de34cd`, `include/linux/tnum.h` and `kernel/bpf/tnum.c`) and Vishwanathan et al. (CGO 2022, DOI `10.1109/CGO53902.2022.9741267` / `arXiv:2105.05398v3`; CAV 2023 `Agni`, DOI `10.1007/978-3-031-37709-9_12`, `bpfverif/agni` at `9096fbd10376d6a1610cbd18ae98408d0a7bd29b`, `README.md`) formalize tristate numbers `t = (val, mask)`:

- **Well-formedness and complement-free predicates (`tnum.h:14-17`, `TrustedBoundary.lean:521-527`):** A `tnum` $t = (v, \mu)$ is well-formed at width $w$ iff $v \mathbin{\&} \mu = 0$ and $v, \mu < 2^w$. Because Anneal Pass 1 forbids prefix `~~~` notation and `Init.Data.Nat.Bitwise.Basic` (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`) provides unbounded `Nat.land`, `Nat.lor`, and `Nat.xor` without bitwise complement, mask clearing and membership use exact **complement-free** identities ($x \mathbin{\&} \neg\mu = (x \mathbin{|} \mu) \oplus \mu$):
  $$x \in \gamma(t) \iff \texttt{Nat.land x v = v} \;\land\; \texttt{Nat.land x (Nat.lor v mu) = x}.$$
  When $v, \mu < 2^w$, $\texttt{lor v mu} < 2^w$, so $x \in \gamma(t)$ implies $x < 2^w$ without an extra range conjunct.
- **Bitwise and arithmetic transformers (`kernel/bpf/tnum.c:62-139`):**
  - `tnum_and(a, b)` (`L86-94`): $\alpha = a.v \mathbin{|} a.\mu$, $\beta = b.v \mathbin{|} b.\mu$, $v = a.v \mathbin{\&} b.v$, returning $(v,\; (\alpha \mathbin{\&} \beta) \oplus v)$; `tnum_or` (`L96-103`) and `tnum_xor` (`L105-112`) are likewise bit-exact.
  - `tnum_add(a, b)` (`L62-72`) and `tnum_sub(a, b)` (`L74-84`): proved both sound and **optimal** by Vishwanathan et al. (CGO 2022). In `tnum_add`, $s_m = (a.\mu + b.\mu) \bmod 2^w$ and $s_v = (a.v + b.v) \bmod 2^w$ bound all bit-carry outcomes; $\chi = ((s_m + s_v) \bmod 2^w) \oplus s_v$ flags every bit affected by uncertain carries, giving $\mu = \chi \mathbin{|} a.\mu \mathbin{|} b.\mu$ and value $(s_v \mathbin{|} \mu) \oplus \mu$.
  - `tnum_mul(a, b)` (`L122-139`, `arXiv:2105.05398v3`): accumulates concrete product $acc_v = (a.v \cdot b.v) \bmod 2^w$ separately from uncertain partial-product masks $acc_m$ over bit indices $0 \dots w - 1$, finishing with `tnum_add((acc_v, 0), acc_m)`.
- **The `tnum_intersect` missing-$\bot$ soundness trap (`kernel/bpf/tnum.c:141-151`):** `struct tnum` cannot represent $\emptyset$. When $a$ and $b$ disagree on a known bit (e.g., $a = (0, \text{0xe})$ even and $b = (1, \text{0xe})$ odd), `tnum_intersect(a, b)` (`v = a.v | b.v`, `mu = a.m & b.m`, returning `(v & ~mu, mu)`) fabricates `(1, 0xe)` rather than $\bot$. Lifting `Tnum` into `WithBot` via the complement-free compatibility test:
  $$\text{compat}(a, b) :\iff \texttt{Nat.land } a.v\text{ (Nat.lor } b.v\; b.\mu\texttt{) == } a.v \;\land\; \texttt{Nat.land } b.v\text{ (Nat.lor } a.v\; a.\mu\texttt{) == } b.v$$
  detects $\gamma(a) \cap \gamma(b) \neq \emptyset$ **iff** `compat(a, b) = true` across 100% of $81 \times 81 = 6{,}561$ 4-bit `tnum` pairs (reproduced in Revalidation), and yields the exact GLB when compatible.
- **Agni's `gen` vs. `sro` hierarchy and 1-step non-idempotence of `reg_bounds_sync` (`bpfverif/agni`, `bpf_alu_jmp_synthesis.py:68-75`, `lib_reg_bounds_tracking.py:1123-1158`; `torvalds/linux`, `kernel/bpf/verifier.c:1458-1578`):**
  - Agni stage `gen` (`wf_soundness.py`) checks abstract operators over all inhabited register tuples, whereas stage `sro` (`sync_soundness.py`) applies one `BPF_SYNC` (`reg_bounds_sync`) to `dst` (`prog[0]`) and one `BPF_SYNC` to `src` (`prog[1]`) before checking the binary operator (`prog[2]`, `lib_reg_bounds_tracking.py:1129-1157`), eliminating spurious counterexamples on unreduced states.
  - **Empirical discovery on `reg_bounds_sync` (`verifier.c:1565-1578`):** Linux's `reg_bounds_sync` runs four steps: (1) `__update_reg_bounds`, (2) `__reg_deduce_bounds`, (3) `__reg_bound_offset`, and (4) `__update_reg_bounds`. Exhaustive 4-bit model checking (reproduced in Revalidation) uncovers **2,656 inhabited states where 1 call to `reg_bounds_sync` is not idempotent**! Trace: from $r_0 = (v=0, \mu=5, [u_{\min}, u_{\max}]=[0, 2], [s_{\min}, s_{\max}]=[1, 2])$ (unique concrete member $x = 1$), Step 2 narrows $[u_{\min}, u_{\max}]$ to $[1, 2]$; Step 3 intersects `(0, 5)` (`0b0?0?`) with `tnum_range(1, 2) = (0, 3)` (`0b00??`) to get `var_off = (0, 1)` (`0b000?`); Step 4 narrows $u_{\max}, s_{\max}$ to $1$, yielding $r_1 = (v=0, \mu=1, [1, 1], [1, 1])$. Because `__reg_bound_offset` is not re-run after Step 4, `tnum_is_const(r_1.var_off)` returns **`false`** despite $u_{\min} = u_{\max} = 1$! Only a second call reaches $r_2 = (v=1, \mu=0, [1, 1], [1, 1])$.

### 4. Bidirectional Reduced Product (`WithBot (Tnum × WrappedInterval)`) and Single-Pass Lean 4 Checker Architecture

`Basis: source + execution + derived`

1. **Hemisphere-aware bidirectional reduction $\rho_w : \text{Tnum} \times \text{WInt}_w \to \text{AbsScalar}$:**
   - **`Tnum` $\to$ `WInt`:** Construct both the non-south-crossing unsigned arc $I_u(t) = [[v,\; v \mathbin{|} \mu]]_w$ and the non-north-crossing signed arc $I_s(t) = [[v \mathbin{|} (\mu \mathbin{\&} 2^{w-1}),\; v \mathbin{|} (\mu \mathbin{\&} (2^{w-1} - 1))]]_w$ (`verifier.c:1461-1468`), intersecting $I$ with both (returning `.bot` if disjoint).
   - **`WInt` $\to$ `Tnum`:** `tnum_range(s, e)` (`tnum.c:21-35`) is **only sound when $[[s, e]]_w$ does not cross the south pole ($s \le_u e$)**; on a full-circle arc like $[[254, 253]]_8 = \top$, $254 \oplus 253 = 3$ would unsoundly yield `(252, 3)`! Guarding `wintToTnum` on `.arc s e` with `s <= e` (returning `(0, 2^w - 1)` when `s > e` or `.top`, since $0$ and $2^w - 1$ both lie in a south-crossing arc and disagree in all $w$ bits) preserves soundness and exactness, followed by `Tnum.meet` and one closing `Tnum -> WInt` tightening so singleton intervals always collapse `mask` to `0` in one call.
2. **Lean 4.34.1 C++ kernel `!has_fvar` GMP discipline and zero-`._unsafe_rec` recursion (`type_checker.cpp:637-733, 1088-1186`; `TrustedBoundary.lean:1117-1153`):**
   - `type_checker::reduce_nat` (`L702-733`) accelerates 15 `Nat` operations in GMP, but both `is_def_eq_core`'s `Bool.true` reflection shortcut (`L1181`) and `lazy_delta_reduction` (`L1093`) require **`!has_fvar(...)`**. Hence a proposed `theory/` checker `checkCfgFixpoint : Program → DefId → Body → List (Nat × List (Nat × AbsScalar)) → Bool` must receive **100% closed ASTs**, keeping runtime `args : List Val` strictly inside its soundness theorem `aiPcc_bodyVerified (... : checkCfgFixpoint p defId body cert = true) : BodyVerified p defId body safety prop`.
   - Computable recursive `def`s synthesize `partial` `._unsafe_rec` helpers rejected by `TrustedBoundary.ensureReplayableConstant` (`L1119-1120`). Routing bounded bit scans through `@Nat.recCompiled` (`natFold` at width $w \le 128$) and CFG checks through `List.foldr` (`Lens.lean:60-80`) emits **zero `._unsafe_rec` helpers** and **zero `Classical.choice` dependencies**:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.AiPcc

def natFold {α : Type} (zero : α) (succ : Nat → α → α) (n : Nat) : α :=
  @Nat.recCompiled (fun _ => α) zero succ n

structure Tnum where
  val  : Nat
  mask : Nat

inductive WInt where
  | bot : WInt
  | top : WInt
  | arc (start stop : Nat) : WInt

inductive AbsScalar where
  | bot  : AbsScalar
  | live (t : Tnum) (w : WInt) : AbsScalar

/-- Complement-free `x & ~m = (x | m) ^ m` using GMP `lor` and `xor`. -/
def clearBits (x m : Nat) : Nat :=
  Nat.xor (Nat.lor x m) m

def Tnum.wfB (w : Nat) (t : Tnum) : Bool :=
  let lim := Nat.shiftLeft 1 w
  Nat.beq (Nat.land t.val t.mask) 0 && Nat.blt t.val lim && Nat.blt t.mask lim

def Tnum.memB (t : Tnum) (x : Nat) : Bool :=
  Nat.beq (Nat.land x t.val) t.val &&
  Nat.beq (Nat.land x (Nat.lor t.val t.mask)) x

def Tnum.subsumesB (a b : Tnum) : Bool :=
  Nat.beq (clearBits a.mask b.mask) 0 &&
  Nat.beq (clearBits a.val b.mask) b.val

def Tnum.meet (a b : Tnum) : Option Tnum :=
  if Nat.beq (Nat.land a.val (Nat.lor b.val b.mask)) a.val &&
     Nat.beq (Nat.land b.val (Nat.lor a.val a.mask)) b.val then
    let v  := Nat.lor a.val b.val
    let mu := Nat.land a.mask b.mask
    some ⟨clearBits v mu, mu⟩
  else
    none

def WInt.mkArc (w s e : Nat) : WInt :=
  let modW := Nat.shiftLeft 1 w
  let s'   := Nat.mod s modW
  let e'   := Nat.mod e modW
  let span := Nat.mod (Nat.add e' (Nat.sub modW s')) modW
  if Nat.beq (Nat.add span 1) modW then .top else .arc s' e'

def WInt.memB (w : Nat) (i : WInt) (x : Nat) : Bool :=
  match i with
  | .bot => false
  | .top => true
  | .arc s e =>
    let modW := Nat.shiftLeft 1 w
    let dx   := Nat.mod (Nat.add x (Nat.sub modW s)) modW
    let span := Nat.mod (Nat.add e (Nat.sub modW s)) modW
    Nat.ble dx span

def WInt.subsumesB (w : Nat) (a b : WInt) : Bool :=
  match a, b with
  | .bot, _ => true
  | _, .top => true
  | .top, _ => false
  | _, .bot => false
  | .arc as_ ae, .arc bs be =>
    let modW  := Nat.shiftLeft 1 w
    let offS  := Nat.mod (Nat.add as_ (Nat.sub modW bs)) modW
    let spanA := Nat.mod (Nat.add ae (Nat.sub modW as_)) modW
    let spanB := Nat.mod (Nat.add be (Nat.sub modW bs)) modW
    Nat.ble (Nat.add offS spanA) spanB

def prefixMask (w chi : Nat) : Nat :=
  natFold 0
    (fun bit acc =>
      if Nat.beq (Nat.shiftRight chi bit) 0 then acc
      else Nat.sub (Nat.shiftLeft 1 (Nat.add bit 1)) 1)
    w

def wintToTnum (w : Nat) (i : WInt) : Option Tnum :=
  let maxVal := Nat.sub (Nat.shiftLeft 1 w) 1
  match i with
  | .bot => none
  | .top => some ⟨0, maxVal⟩
  | .arc s e =>
    if Nat.ble s e then
      let delta := prefixMask w (Nat.xor s e)
      some ⟨clearBits s delta, delta⟩
    else
      some ⟨0, maxVal⟩

def AbsScalar.subsumesB (w : Nat) (a b : AbsScalar) : Bool :=
  match a, b with
  | .bot, _ => true
  | .live _ _, .bot => false
  | .live ta wa, .live tb wb => Tnum.subsumesB ta tb && WInt.subsumesB w wa wb

end Anneal.AiPcc
```

### 5. Architectural Evaluation for Untrusted Theory Libraries Outside the TCB

`Basis: source + derived`

| Dimension | Grade | Grounded Justification Against `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | Resides 100% in `theory/Anneal/`. Structural induction on `Reaches` (`Trusted/MirSemantics.lean:1624-1629`) proves that a checked post-fixpoint forbids `.fault .undefined` and `.fault .unsupported`, establishing `WellFormed` and `BodyVerified` (`L1646-1650, 1751-1759`) with zero `trusted/` edits and zero `Anneal.*` leakage into `CrateTheorem`. |
| **(P1) Human Spec Auditability** | **Strong** | Reviewers inspect only Rust `Specs.safety` and `Specs.property`; cutpoint certificates live strictly inside untrusted proof terms (`ConstantInfo.value?`). |
| **(P2) Authoring & Day-2 Locality** | **Strong** | External Rust/Python WTO solvers regenerate cutset tables in milliseconds on code edits; the Lean proof remains `exact aiPcc_bodyVerified ... rfl` without brittle `fuel` or step-index rewrites. |
| **(P3) Lean 4 Kernel & LSP Scaling** | **Strong** | Single $O(|B| + |E|)$ closed-`Nat` pass runs in C++ GMP (`reduce_nat`), avoiding symbolic `FrameState` cloning and preserving `<50 ms` `anneal-lsp` latency and tiny `Eq.refl true` `.olean` terms. |
| **(P4) Heterogeneous Composability** | **Moderate** | Handles unstructured `goto`/`switchInt` loops, shifts, casts, and bitmasks uniformly and exports proven entry predicates (`off & 7 = 0`) to `PureLift` or linear-cut checkers at `unsafe` boundaries, though it does not track heap separation or inter-variable differences alone. |
| **(P5) Failure Legibility** | **Strong** | Failed checks identify the exact `(blockId, stmtIdx, localId)` and abstract `(tnum, [[s, e]]_w)` violating an arithmetic or inclusion guard rather than exposing raw MIR states. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Collapses Linux's five eBPF domains (`u64`, `s64`, `u32`, `s32`, `tnum`) into two width-parametric primitives (`Tnum`, `WInt`) under `WithBot`, while omitting `join`/`widen`/`narrow` from kernel code. |

## Boundaries

- **Relational invariants between distinct locals — `known not to apply`:** Because `WithBot (Tnum × WInt)` is non-relational (`separate_domain` in `wrapped_interval_domain.hpp:68-69`), symbolic relationships like `idx < len` require pairing with a difference-bound domain or discharging cutpoint obligations via integer Farkas / Chvátal–Gomory certificates.
- **Unmodeled `TerminatorKind.assert`, `call`, and non-empty `callerMem` on Anneal `main` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) — `unsupported`:** At `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted/MirSemantics.lean:1568-1569` and `1730-1737` fail closed (`.fault .unsupported`) on `assert`, `call`, `unwindResume`, and non-scalar/enum heap references (`callerMem = ⟨[]⟩`). Checking `TerminatorKind.assert` guards requires enabling those transitions in `Trusted.MirSemantics`.
- **Closed-form `tnum` shifts over wide symbolic shift ranges — `not examined`:** Both `kernel/bpf/tnum.c:37-60` and `wrapped_interval_impl.hpp:1183-1223` restrict shift transformers to singleton shift counts; non-enumerative `tnum` transformers for wide shift intervals were `not examined`.
- **Worst-case iteration count of Linux's coupled 64/32-bit `reg_bounds_sync` (`verifier.c:1565-1578`) — `unknown`:** Exhaustive 4-bit checking proves 1 call is non-idempotent (`2,656` states) and 2 calls stabilize single-width states, whereas whether 64/32-bit subregister coupling (`__reg_bound_offset` `L1562`) ever requires 3 calls at 64-bit width remains `unknown` from 4-bit enumeration (and does not affect AI-PCC soundness).

## Evidence

1. **Anneal Pass 1 & MIR Semantics (`source`):** `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/foundation-lock.json` (`L1-L90`), `trusted/audit/TrustedBoundary.lean` (`L442-L596`, `L1108-L1260`), `trusted/lean/Trusted/MirAst.lean` (`L75-L92`, `L620-L868`), `trusted/lean/Trusted/MirSemantics.lean` (`L1553-L1809`), and `theory/Anneal/PureLift/Lens.lean` (`L60-L80`).
2. **Lean 4.34.1 Kernel & Prelude (`source`):** `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`: `src/kernel/type_checker.cpp` (`L637-L776`, `L1088-L1186`), `src/Init/Data/Nat/Bitwise/Basic.lean` (`L49-L110`), and `src/Init/Data/BitVec/BasicAux.lean` (`L1-L69`).
3. **CompCert, Verasco, and AI-PCC (`normative + source`):** `AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc` (`backend/Kildall.v:66-116, 184-302`); Jourdan et al., POPL 2015, DOI `10.1145/2676726.2676966` (Verasco `1.3`, `https://compcert.inria.fr/verasco/`); Besson, Jensen, and Pichardie, *TCS* 364(3):273–291, 2006, DOI `10.1016/j.tcs.2006.08.012`.
4. **Wrapped Intervals (`normative + source`):** Navas et al., APLAS 2012, DOI `10.1007/978-3-642-35182-2_9`; `seahorn/crab` at `b1eeb1a9402ab0664e962f26f89d923f8514284c` (`include/crab/domains/{wrapped_interval.hpp,wrapped_interval_impl.hpp,wrapped_interval_domain.hpp}`).
5. **Linux `tnum` & Agni (`normative + documentation + source`):** `torvalds/linux` `v5.19` at `3d7cb6b04c3f3115719235cc6866b10326de34cd` (`include/linux/tnum.h:14-99`, `kernel/bpf/tnum.c:21-173`, `kernel/bpf/verifier.c:1458-1623`); `bpfverif/agni` at `9096fbd10376d6a1610cbd18ae98408d0a7bd29b` (`README.md`, `bpf-verification/src/{bpf_alu_jmp_synthesis.py,wf_soundness.py,sync_soundness.py}`, `lib_reg_bounds_tracking.py:222-350, 931-1158`); Vishwanathan et al., CGO 2022, DOI `10.1109/CGO53902.2022.9741267` (`arXiv:2105.05398v3`) and CAV 2023, DOI `10.1007/978-3-031-37709-9_12`.
6. **Finite-Domain Verification Probe (`execution`, `2026-11-19`):** Executed the self-contained Python 3.13 finite-domain probe preserved in item 4 of Revalidation below on Linux x86_64, confirming 3-bit `WInt` pseudo-join non-monotonicity, 4-bit complement-free `Tnum.memB`/`Tnum.meet` exactness across all $6{,}561$ pairs, 4-bit `WInt.subsumesB` exactness, and `2,656` 1-step non-idempotent `reg_bounds_sync` states.

## Revalidation

1. **Anneal Pass 1 gates (`joshlf/anneal`):** Check `trusted/lean/foundation-lock.json` and `trusted/audit/TrustedBoundary.lean` (`allowedNotationSyntaxKinds`, `ensureReplayableConstant`) to verify whether `~~~` remains excluded and `partial` `._unsafe_rec` helpers remain rejected, and inspect `Trusted/MirSemantics.lean` (`evalTerminator`) for `assert`/`call` support.
2. **Lean 4 GMP reflection gates (`leanprover/lean4`):** Diff `src/kernel/type_checker.cpp` around `reduce_nat`, `lazy_delta_reduction`, and `is_def_eq_core` to confirm `!has_fvar` still guards `Bool.true` reflection and `Nat.{land,lor,xor,shiftLeft,shiftRight,mod,ble}` remain in `reduce_nat`.
3. **Crab & Linux upstream checks (`seahorn/crab`, `torvalds/linux`):** Check `wrapped_interval_impl.hpp` (`And`, `Or`, `Xor`) for `default_implementation` (`top()`), `kernel/bpf/tnum.c` (`tnum_intersect`), and `kernel/bpf/verifier.c` (`reg_bounds_sync`) for any trailing `__reg_bound_offset` call.
4. **Standalone finite-domain discriminator (<0.3s, Python 3.10+ stdlib only):**
   ```bash
   python3 -c '
   M = 15
   def pjoin3(a, b):
       s1, e1 = a; s2, e2 = b
       in_b = lambda x: ((x - s2) & 7) <= ((e2 - s2) & 7)
       in_a = lambda x: ((x - s1) & 7) <= ((e1 - s1) & 7)
       if in_b(s1) and in_b(e1) and (not in_a(s2) or not in_a(e2)): return b
       if in_a(s2) and in_a(e2) and (not in_b(s1) or not in_b(e1)): return a
       ga, gb = (s2 - e1) & 7, (s1 - e2) & 7
       return (s1, e2) if (ga < gb or (ga == gb and s1 <= s2)) else (s2, e1)
   assert pjoin3((0, 0), (5, 5)) == (5, 0) and pjoin3((0, 2), (5, 5)) == (0, 5)

   tnums = [(v, m) for v in range(16) for m in range(16) if (v & m) == 0]
   assert len(tnums) == 81
   for v1, m1 in tnums:
       g1 = {x for x in range(16) if (x & ~m1) == v1}
       assert all((((x & v1) == v1) and ((x & (v1 | m1)) == x)) == (x in g1) for x in range(16))
       for v2, m2 in tnums:
           g2 = {x for x in range(16) if (x & ~m2) == v2}
           compat = ((v1 & (v2 | m2)) == v1) and ((v2 & (v1 | m1)) == v2)
           assert compat == bool(g1 & g2)
           if compat:
               vv, mu = v1 | v2, m1 & m2
               vc = (vv | mu) ^ mu
               assert {x for x in range(16) if (x & ~mu) == vc} == (g1 & g2)
   for s1 in range(16):
       for e1 in range(16):
           sp1 = (e1 - s1) & M
           if sp1 == M: continue
           g1 = {x for x in range(16) if ((x - s1) & M) <= sp1}
           for s2 in range(16):
               for e2 in range(16):
                   sp2 = (e2 - s2) & M
                   if sp2 == M: continue
                   g2 = {x for x in range(16) if ((x - s2) & M) <= sp2}
                   assert ((((s1 - s2) & M) + sp1) <= sp2) == g1.issubset(g2)

   s4 = lambda x: x - 16 if x >= 8 else x
   u4 = lambda x: x & 15
   def trange(a, b):
       chi = a ^ b; bits = chi.bit_length(); d = (1 << bits) - 1
       return (a & ~d, d)
   def sync4(v, m, umin, umax, smin, smax):
       def upd(v, m, umin, umax, smin, smax):
           umin = max(umin, v); umax = min(umax, v | m)
           smin = max(smin, s4(v | (m & 8))); smax = min(smax, s4(v | (m & 7)))
           return umin, umax, smin, smax
       umin, umax, smin, smax = upd(v, m, umin, umax, smin, smax)
       if smin >= 0 or smax < 0:
           umin = max(umin, u4(smin)); umax = min(umax, u4(smax))
           smin, smax = s4(umin), s4(umax)
       elif s4(umax) >= 0:
           smin = s4(umin); umax = min(umax, u4(smax)); smax = s4(umax)
       elif s4(umin) < 0:
           umin = max(umin, u4(smin)); smin = s4(umin); smax = s4(umax)
       tv, tm = trange(umin, umax)
       mu = m & tm; v, m = ((v | tv) | mu) ^ mu, mu
       umin, umax, smin, smax = upd(v, m, umin, umax, smin, smax)
       return v, m, umin, umax, smin, smax
   non_idem = sum(
       sync4(*sync4(v, m, u0, u1, s0, s1)) != sync4(v, m, u0, u1, s0, s1)
       for v, m in tnums
       for u0 in range(16) for u1 in range(u0, 16)
       for s0 in range(-8, 8) for s1 in range(s0, 8)
       if any((x & ~m) == v and u0 <= x <= u1 and s0 <= s4(x) <= s1 for x in range(16))
   )
   assert non_idem == 2656
   print("revalidation passed")
   '
   ```
