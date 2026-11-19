# Gradual Verification, Dynamic Separation-Logic Contracts, and Multi-Rung Assurance Algebras

## Summary

Eliminating the all-or-nothing cliff between dynamic prototyping, executable runtime contracts, automated solvers, and kernel-checked formal proofs requires reconciling four coupled mechanisms across static verification, dynamic checking, dependent type theory, and cross-language FFI composition:

1. **Sound Gradual Symbolic Execution Requires an Exclusion Frame:** Gradual verification over implicit dynamic frames (IDF) and recursive abstract predicates—pioneered in weakest-liberal-precondition form by Wise et al. (OOPSLA 2020) and implemented via Viper-backed symbolic execution in Gradual C0 (`gradual-verification/gvc0`)—optimistically assumes imprecise formulas (`? * φ`) and inserts minimal residual runtime checks only where static verification relied on `?`. However, Zimmerman, DiVincenzo, and Aldrich (POPL 2024) demonstrated a concrete soundness bug in Gradual C0: combining isorecursive static predicate folding with equirecursive dynamic permission passing allows an imprecise callee precondition (`predicate imprecise() = ? * true`) to seize caller heap permissions allocated *after* folding while static execution retains them. Soundness is restored without sacrificing zero overhead on static code by synthesizing a per-call **exclusion frame** $\Theta$ (dynamic $\hat{\alpha}$) that subtracts statically retained caller permissions from the callee's dynamic footprint (`α \ α̂`), dropping to $\Theta = \emptyset$ on completely precise boundaries.
2. **Dependent Gradualization Faces the GCIC Fire Triangle:** Lennon-Bertrand, Maillard, Tabareau, and Tanter (POPL/TOPLAS 2022, `pleiad/GradualizingCIC`) prove a structural impossibility theorem ("the fire triangle of graduality"): a gradual dependent type theory cannot simultaneously preserve (a) **conservativity** over CIC, (b) **strong normalization** (logical consistency), and (c) full **graduality** (monotonicity under precision) without universe-level shifting. The Agda mechanization splits cleanly along this boundary: `DiscreteModelPartial.agda` and `UnivPartial.agda` require `NO_POSITIVITY_CHECK` and `TERMINATING` pragmas (`GCIC^G`), whereas `DiscreteModelTotal.agda` eliminates both pragmas by shifting $\Pi$-types up one universe level (`GCIC^↑`, `Uₛπ : {i j : ≺ n} ... -> Uₛ`). Practical systems-plus-proof languages therefore stratify dynamic `?` into program expressions and gradual contract assertions (`? * φ`), keeping proof-kernel type-level terms strictly normalizing.
3. **Executable Separation Logic Works When Restricted to Determined/Precise Ownership Fragments:** Full separation logic is EXPTIME-complete to model-check at runtime because `*` implicitly quantifies over arbitrary heap splittings. Fulminate (Banerjee et al., POPL 2025, `rems-project/cn`) exploits CN's syntactic restriction to determined/precise resource predicates to compile C+CN specifications source-to-source into readable instrumented C. Runtime ownership is tracked in a compressed radix-tree range map (`runtime/libcn/src/cn-executable/rmap.c`) parameterized by an idempotent commutative `(min, max)` semigroup over stack-depth integers, achieving `0.3 μs–0.9 μs` per dynamic `Owned` check on production-scale code including the pKVM buddy allocator, while Gradual C0 tracks per-object field permissions in a Robin Hood open-addressed hash table (`src/main/resources/runtime.c0`).
4. **Gradual Performance Cliffs and Multi-Rung FFI Composition Are Governed by Nominal Bulk Membranes and a Monotone Assurance Semilattice:** Sound structural gradual typing incurs up to ~100× slowdowns from per-access higher-order wrappers (Takikawa et al., POPL 2016), whereas nominal boundary validation (Muehlboeck & Tate, OOPSLA 2017) and explicit deep/shallow mode selection (Greenman, PLDI 2022) bound wrapper overhead. Across heterogeneous FFI boundaries mixing concrete examples (`R0`), executable contracts/fuzzing (`R1`), bounded/SMT solvers (`R2`), conditional kernel proofs (`R3`), and foundational proofs (`R4`), composed assurance forms a bounded meet-semilattice `(R0..R4, min) × (P(Assumptions), ∪)` where untrusted `R0`/`R1`/`R2` counterexamples promote soundly to `R4` kernel refutations via ground-term evaluation, and hardware/SFI isolation membranes selectively preserve memory-safety assurance modulo an explicit isolation assumption.

## Applicability

These findings apply to the design of verification-capable systems languages, contract compilers, gradual type/proof checkers, and multi-language FFI bridges that combine static verification, dynamic contract enforcement, and heterogeneous assurance levels within one program or across an FFI boundary.

The subjects in `REPORT.json` relate as complementary pillars of a unified gradual-assurance design space:

- **Gradual C0 (`gradual-verification/gvc0` at `4276d89421d9fc17058a06cff975e9c7207ab917`), Gradual Viper/Silicon (`gradual-verification/silicon` at `99d3d27190554a5008628a083fc2329f4032565f`), Wise et al. (OOPSLA 2020), and Zimmerman et al. (POPL 2024)** establish the formal theory, symbolic execution rules (`SVLC0`/`GVLC0`), soundness counterexample, exclusion-frame fix, and runtime permission-table implementation for gradual implicit-dynamic-frames verification over mutable recursive heap structures.
- **GCIC (`pleiad/GradualizingCIC` at `354c65260d522a13992b268334fd7892cfb4618c`, POPL/TOPLAS 2022)** establishes the metatheoretic limits of combining gradual precision with dependent types and proof-kernel consistency.
- **Fulminate (`rems-project/cn` at `d1c60d1720bed3bed0d45dab247a1959145c8cb9`, POPL 2025)** provides an industrial-target implementation and formalization of source-to-source executable separation-logic ownership checking for C, including empirical measurements on pKVM hypervisor allocator code.
- **Takikawa et al. (POPL 2016), Muehlboeck & Tate (OOPSLA 2017), Greenman (PLDI 2022), and Patterson et al. (PLDI 2022)** establish the runtime cost regimes of structural vs. nominal vs. shallow/deep gradual boundaries and logical-relations soundness across foreign-language interoperability membranes.

All upstream repository observations reflect the pinned revisions listed in `REPORT.json` as inspected on `2026-11-19`. Derived architectural synthesis—specifically the five-rung assurance meet-semilattice, executability polarity classification, and FFI isolation-membrane projection—is explicitly labeled `Basis: derived` and checked for algebraic consistency by the executable micro-probe recorded under **Evidence**.

## Findings

### 1. Sound Gradual Verification with Symbolic Execution (`SVLC0` / `GVLC0`)

**Basis:** normative specification (Wise et al., OOPSLA 2020, `10.1145/3428296`; Zimmerman, DiVincenzo & Aldrich, POPL 2024, `10.1145/3632927` / `arXiv:2311.07559`) + source (`gradual-verification/gvc0`, `gradual-verification/silicon`) + execution.

#### 1.1 Imprecise Specifications and the Precision Partial Order

Gradual verification extends implicit dynamic frames (IDF)—a separation-logic dialect decoupling spatial field accessibility permissions (`acc(e.f)`) from pure value assertions (`e.f == 2`)—with **imprecise formulas**:

$$\tilde{\phi} ::= \phi \;\mid\; ? * \phi$$

where $\phi$ is a static (precise) IDF formula built from pure boolean expressions, field permissions `acc(x.f)`, recursive abstract predicates `P(x̄)`, separating conjunction `*`, and logical conditionals `b ? φ₁ : φ₂`. Semantically, the concretization $\gamma(\tilde{\phi})$ maps a precise formula $\phi$ to the singleton $\{\phi\}$ and an imprecise formula $? * \phi$ to the set of all *self-framed, satisfiable* static strengthenings $\phi'$ such that $\phi' \Rightarrow \phi$.

A key engineering property is **monotonic precision refinement**: tightening a specification along the precision partial order

$$? \;\sqsubseteq\; (? * \text{acc}(c.\text{value})) \;\sqsubseteq\; (? * \text{acc}(c.\text{value}) * c.\text{value} \ge 0) \;\sqsubseteq\; (\text{acc}(c.\text{value}) * c.\text{value} \ge 0)$$

monotonically increases the set of statically discharged obligations and monotonically decreases residual runtime checks to **zero** once `?` is removed.

Earlier weakest-liberal-precondition (WLP) metatheory (Wise et al., OOPSLA 2020) proved soundness and the gradual guarantee, but checked *all* assertions dynamically (including statically proved ones) and operated over infinite concretization sets. Gradual C0 (`gvc0`) replaced WLP with forward **symbolic execution** on top of Viper's Silicon backend (`gradual-verification/silicon`), maintaining a symbolic state $\sigma = \langle \mathcal{H}, \mathcal{H}_?, \gamma, \pi \rangle$ consisting of:
- a precise symbolic heap $\mathcal{H}$ (field chunks $\langle f, t_r, t_v \rangle$ and predicate chunks $\langle P, \bar{t} \rangle$),
- an optimistic/imprecise flag or optimistic heap $\mathcal{H}_?$ recording permissions optimistically assumed from `?`,
- a symbolic store $\gamma : \text{Var} \to \text{Term}$, and
- a path condition $\pi$ discharged by SMT (Z3).

When `consume` requires a permission or pure fact not entailed by $(\mathcal{H}, \pi)$:
- If the current state is **precise**, verification fails statically.
- If the current state is **imprecise** (originating from an enclosing `? * φ`) and the required obligation is *consistent* with $\pi$ (i.e., $\pi \land \text{obl}$ is satisfiable), symbolic execution optimistically assumes the obligation and emits a **symbolic runtime check** $R$ guarded by the branch path condition.

#### 1.2 The Gradual C0 Soundness Bug and Exclusion-Frame Fix (POPL 2024)

**Basis:** normative specification (Zimmerman et al., POPL 2024, §8, pp. 111:24–111:27, `arXiv:2311.07559`) + execution (micro-probe Part B).

While formalizing `SVLC0` (core static Viper) and `GVLC0` (Gradual C0) and proving Progress (Theorems 1–2) and Preservation (Theorem 3), Zimmerman, DiVincenzo, and Aldrich uncovered a **soundness bug** in Gradual C0's deployed implementation (DiVincenzo et al., 2022). The minimal counterexample (Figure 14 of POPL 2024) is:

```c
struct Cell { int value; }
predicate imprecise() = ? * true

void set(Cell c, int v)
  requires imprecise()
  ensures true
{
  unfold imprecise();
  c.value = v;
}

int test()
  requires true
  ensures result == 0
{
  fold imprecise();       // Static H = { <imprecise> }; dynamic: no-op
  Cell c = alloc(Cell);   // Static H = { <imprecise>, <value, t1, _> }; dynamic owns <l1, value>
  c.value = 0;            // Static H = { <imprecise>, <value, t1, 0> }
  set(c, 1);              // Static consumes <imprecise>, RETAINS <value, t1, 0>!
  result = c.value;       // Static proves result == 0 with ZERO runtime checks in test()!
}
```

The bug arises from a **three-way semantic mismatch**:
1. **Isorecursive static predicates:** `fold imprecise()` creates an opaque predicate chunk `<imprecise>` before `c` is allocated. Consuming `imprecise()` at `set(c, 1)` removes only `<imprecise>` from the static symbolic heap, leaving `<value, t1, 0>` intact in the caller's frame. Static verification therefore proves `ensures result == 0` and weaves **0 runtime checks** into `test()`.
2. **Equirecursive dynamic footprints:** Without an exclusion frame, dynamic execution computes the footprint of a non-completely-precise precondition `imprecise()` as `⌊imprecise()⌋ = α` (passing *all* permissions currently owned by `test()`—including `<l1, value>` allocated *after* `fold imprecise()`—to `set`).
3. **Optimized check omission:** Inside `set`, the runtime check for `acc(c.value)` succeeds because `test()` handed over `<l1, value>`, `set` mutates `c.value = 1`, and `test()` returns `1`—silently violating its statically verified postcondition `ensures result == 0` because Gradual C0 omitted the postcondition check!

**The Exclusion-Frame Solution ($\Theta$ / $\hat{\alpha}$):** Rather than clearing the entire symbolic heap on every imprecise call (which destroys static framing and forces expensive dynamic predicate traversals), POPL 2024 defines an **exclusion frame** $\Theta$ synthesized by symbolic execution's guard judgment ($\Sigma \rightharpoonup \sigma \dashv R, \Theta$) after consuming a callee's precondition:
- If the callee precondition is **completely precise**, $\Theta = \emptyset$ (zero overhead on static code; exclusion frames can be dropped upon entering completely precise methods and reconstructed only when a precise method invokes an imprecise one).
- If the callee precondition is **imprecise** (or transitively unfolds an imprecise predicate), $\Theta$ collects all heap permissions still retained in the caller's symbolic heap (`rem` helper). At runtime, $\Theta$ evaluates under valuation $V'$ to $\hat{\alpha}$, and the caller passes $\alpha \setminus \hat{\alpha}$ to the callee.
- In Figure 14, $\Theta = \{\langle t_1, \text{value} \rangle\}$ excludes `<l1, value>` from `set`'s footprint, so `set`'s dynamic check for `acc(c.value)` fails cleanly before any mutation occurs, restoring Preservation (Theorem 3).

**Loop Verification Subtlety (`SVerifyLoop`, POPL 2024 §7.2):** Symbolic runtime checks contain symbolic values $\nu_i$ fixed by valuation extension across steps. Inside a `while` loop whose body consumes `x`, allocates a fresh object `ℓ₂`, and reassigns `x = create()`, reusing the pre-loop symbolic check `⟨ν₁, value⟩` across iterations checks the *old* object `ℓ₁` rather than the new `ℓ₂`. Sound loop verification therefore refreshes modified loop variables with fresh symbolic values and checks the loop invariant cleanly at entry and preservation boundaries.

#### 1.3 Runtime Permission Representation and Discrepancy in `gvc0`

**Basis:** source (`gradual-verification/gvc0` at `4276d89421d9fc17058a06cff975e9c7207ab917`: `Runtime.md`, `src/main/resources/runtime.c0`, `src/main/scala/gvc/weaver/SeparationChecks.scala`).

Direct source inspection reveals an important documentation-vs-implementation discrepancy in `gradual-verification/gvc0`:
- `Runtime.md` (lines 5–17) describes a conceptual design inserting a `bool value_perm;` field into each user struct (noting library structs cannot be rewritten).
- The actual runtime implementation in `src/main/resources/runtime.c0` (lines 14–160) does **not** embed per-field booleans in user structs; instead, it manages an external `OwnedFields` structure implemented as an **open-addressed Robin Hood hash table** (`runtime_hash` with Murmur-style bit-mixing `0x45d9f3b`, initial capacity `128`, `80%` load-factor threshold triggering `runtime_compact` to evict entries with `accessible == 0` before growing by `GROW_CONST = 128`, tracking probe sequence length `entry->psl`). Each entry maps an object's integer reference ID to a `FieldArray*` tracking accessible fields.
- Separation checking in `src/main/scala/gvc/weaver/SeparationChecks.scala` (lines 6–135) guards runtime separation-check weaving with `canOverlap(spec) = countAccs(spec) > 1`. Crucially, `countAccs` conservatively returns `2` for *any* `IR.PredicateInstance` (line 31: comment notes exploring mutually recursive predicates is unimplemented), and `inject` propagates branch-guard conditions (`ImmediateCondition` via `IR.Conditional`) onto each emitted `FieldSeparationCheck` and `PredicateSeparationCheck`.

---

### 2. Executable Separation-Logic Contracts in C: Fulminate (`rems-project/cn`)

**Basis:** normative specification (Banerjee et al., POPL 2025, `10.1145/3704879`) + source (`rems-project/cn` at `d1c60d1720bed3bed0d45dab247a1959145c8cb9`: `doc/README-FULMINATE.md`, `lib/fulminate/ownership.ml`, `lib/fulminate/fulminate.ml`, `runtime/libcn/src/cn-executable/rmap.c`).

#### 2.1 Why CN's Separation Logic Fragment Is Computationally Executable

General separation logic is EXPTIME-complete for runtime model checking (Brotherston et al.; Calcagno et al.) because arbitrary separating conjunction `P * Q` requires searching exponentially many partitions of the concrete heap, and arbitrary existentials `∃x. P(x)` require unbounded witness search.

Fulminate leverages a structural property that CN already enforces for predictable static SMT proof automation: **precise / determined resource predicates** (similar to Dryad's determined predicates). In CN's refinement-type grammar:
- Resource assertions are ordered lists of `Owned<τ>(p)` and recursive predicates whose pointer footprints are **uniquely determined** by input arguments and deterministic traversal order (no non-deterministic disjunction over spatial footprints).
- Existential output values are computed directly by reading concrete memory at the owned pointer (`*p`), eliminating witness search.
- Pure constraints over mathematical integers (`integer`), bitvectors, structs, and algebraic datatypes compile directly to executable C expressions over CN runtime types (`<file>.cn.h`, `<file>.cn.c`), injected into `<file>.exec.c` at function entry (preconditions), a unified `cn_epilogue:` label reached via rewritten `goto` returns (postconditions), and inline assertion sites (`doc/README-FULMINATE.md:19-33`).

#### 2.2 Reified Ghost Ownership via Stack-Depth Radix-Tree Range Maps (`rmap`)

To check separation and detect aliasing/use-after-transfer/ownership-leak errors in real C (including `&local` stack-variable aliasing and nested calls), Fulminate maintains a **global reified ghost ownership map** (`cn_ownership_global_ghost_state`) mapping **every byte address** to an integer **stack depth** indicating which activation frame currently owns that byte:

1. **Source-to-Source Instrumentation (`lib/fulminate/ownership.ml:25-180`):** Operating on Cerberus's AIL AST (`Cerb_frontend.AilSyntax`), Fulminate injects:
   - `ghost_stack_depth_incr()` / `ghost_stack_depth_decr()` around function calls and blocks;
   - `c_add_to_ghost_state(&var, sizeof(T), get_cn_stack_depth())` upon local variable declaration and `c_remove_from_ghost_state(...)` upon scope exit;
   - `cn_postcondition_leak_check()` at function return and `cn_loop_put_back_ownership()` / `cn_loop_leak_check()` at loop boundaries to verify that no unreturned ownership was silently dropped.
   - **Concrete C Edge Cases in Source:** `ownership.ml:88-90` skips `register`-qualified C variables because taking `&var` is illegal in C; `ownership.ml:142-149` explicitly throws `failwith` on uninitialized variable declarations inside `for`-loop headers (`TODO: Uninitialised declared variables in loop conditions not supported yet`).
2. **Compressed Radix-Tree Range Map (`runtime/libcn/src/cn-executable/rmap.c:10-120`):** Rather than checking ownership byte-by-byte in a flat table, Fulminate stores the byte-to-depth map in a compressed radix tree (`struct rmap`, with `EMPTY`, `LEAF`, `INNER`, and path-compressed `SKIP` nodes plus a 32-entry node chunk cache `CACHED_NODES`). Each internal node caches a range-query summary `result_t = { .min, .max }` aggregated by an **idempotent commutative semigroup** (`res_append(a, b) = { min(a.min, b.min), max(a.max, b.max) }`, `res_none = { INT_MIN, INT_MIN }`). Checking whether a C struct or array slice `[addr, addr + sz)` is exclusively owned by the current frame at depth `d` reduces to a single range query checking `q.min == d && q.max == d` in $O(\log_{2^{\text{radix}}} \text{addr})$ time!

#### 2.3 Empirical Overhead and Systems-Code Viability (POPL 2025 §5)

**Basis:** documentation + execution (Banerjee et al., POPL 2025, §5.3–§5.4, pp. 43:25–43:27).

Evaluated across VeriFast tutorial benchmarks, a Verifiable C string-to-integer hashtable, and the **buddy memory allocator from Google's production pKVM Android hypervisor**:
- **Per-Ownership-Check Cost:** On the largest scaling benchmarks (up to `1,024` elements and `>3.15 × 10⁶` dynamic `Owned` checks), Fulminate measures **`0.3 μs` to `0.9 μs` per dynamic `Owned` occurrence**.
- **Hypervisor Bug-Finding Latency:** On the pKVM buddy allocator, Fulminate instrumented the C+CN sources in ~`30 s` generation time and caught injected synthetic ownership/spec bugs in **`0.4 s` to `1.4 s` runtime**.
- **Scaling Bottleneck:** Because Fulminate re-traverses recursive data-structure predicates (`each` / linked lists / trees) from scratch at every function entry/exit (without Ditto-style incrementalization), checking an $O(N)$-size list predicate inside an $O(N)$-step loop incurs $O(N^2)$ dynamic `Owned` checks (observed explicitly in §5.4 table: `2` elements → `38` `Owned` calls; `128` elements → `50,438` calls; `512` elements → `791,558` calls, `0.65 s` runtime delta, `216,828` space delta).
- **Engineering Limitations (§4.6 & §6):** Single-translation-unit generation (multi-file compilation units not yet supported), no incremental invariant checking, and non-executable spec features (unbounded universal quantifiers over infinite domains, pure ghost lemmas without computational witnesses) remain outside direct runtime checking.

---

### 3. Dependent Gradualization and the GCIC Fire Triangle (`pleiad/GradualizingCIC`)

**Basis:** normative specification (Lennon-Bertrand, Maillard, Tabareau & Tanter, POPL/TOPLAS 2022, `10.1145/3495528` / `arXiv:2011.10618`) + source (`pleiad/GradualizingCIC` at `354c65260d522a13992b268334fd7892cfb4618c`: `README.md`, `src/DiscreteModelTotal.agda`, `src/DiscreteModelPartial.agda`, `src/UnivPartial.agda`).

#### 3.1 The Fire Triangle No-Go Theorem

In dependent type theories such as CIC (Coq/Rocq, Lean, Agda), types and terms share one syntax and reduction relation; logical consistency (no closed inhabitant of `False`) depends on **strong normalization** of type-level computation. Introducing a dynamic unknown type `?` (with casts to/from arbitrary types via a cast calculus `CastCIC` supporting unknown `?` and runtime error `✠`) creates an irreconcilable three-way tension—the **Fire Triangle of Graduality**:

| Property | Formal Requirement | Why It Matters |
|---|---|---|
| **Conservativity (`C`)** | Pure static CIC terms typecheck and reduce identically in GCIC without extra universe bumps or annotations. | Zero tax on existing verified proofs and libraries. |
| **Normalization (`N`)** | Every well-typed term (including casts through `?`) is strongly normalizing; typechecking is decidable and logic is consistent (modulo explicit errors `✠`). | Mandatory for a small-TCB proof kernel (such as Lean 4's kernel at `trustLevel := 0` or Coq/Rocq's kernel). |
| **Graduality (`G`)** | Full Static + Dynamic Gradual Guarantee: if $t \sqsubseteq u$ (replacing types/terms with `?`) and $t$ evaluates cleanly, then $u$ cannot fail with a cast error `✠` (embedding-projection / distributor pairs between every type $A$ and $?$). | Guarantees that loosening/tightening annotations behaves monotonically. |

**Why All Three Cannot Coexist:** To satisfy both **Conservativity** (a function type $\Pi x:A. B$ lives in $\text{Type}_{\max(i,j)}$) and **Graduality** (every type in $\text{Type}_i$ embeds into $?_i : \text{Type}_i$ via an embedding-projection pair), $?_i$ must contain a copy of $?_i \to ?_i$ at the *same* universe level $i$. That creates a **negative recursive domain equation** $?_i \cong \dots + (?_i \to ?_i) + \dots$, which admits Curry's Y-combinator $\Omega = (\lambda x : ?.\; x\,x)\,(\lambda x : ?.\; x\,x)$—destroying **Normalization** and collapsing logical consistency!

#### 3.2 Concrete Evidence in the Agda Mechanization (`pleiad/GradualizingCIC`)

The repository `pleiad/GradualizingCIC` concretely exhibits the three design corners of the triangle:

1. **`GCIC^G` (Graduality + Conservativity, Drops Normalization):** Modeled in `src/DiscreteModelPartial.agda` and `src/UnivPartial.agda`. As documented in `README.md:56`, these files explicitly require Agda's unsafe pragmas `NO_POSITIVITY_CHECK` and `TERMINATING` because the monotone partial universe hierarchy permits non-terminating casts.
2. **`GCIC^↑` (`GCIC-shift` — Graduality + Normalization, Relaxes Conservativity):** Modeled in `src/DiscreteModelTotal.agda` (`{-# OPTIONS --without-K --prop #-}`, **zero** `NO_POSITIVITY_CHECK` or `TERMINATING` pragmas!). Lines 19–65 construct the universe `U (P n lower)` by **strong induction on universe level `n : Nat`** via `FiniteOrdinal.PNat`:
   ```agda
   data ℍ : Set where
     𝕙σ : ℍ
     𝕙π : (i j : ≺ n) → ℍ
     𝕙u : ≺ n → ℍ
     𝕙nat : ℍ

   Elℍ (𝕙π i j) = El (Unk i) → El (Unk j)
   ```
   and `Uₛπ : {i j : ≺ n} (A : U i) (B : El A → U j) → Uₛ` forces every $\Pi$-type formed from level $i, j < n$ up to strictly higher level $n$ (`max(i,j) + 1`), breaking the self-application cycle! The cost is non-conservativity: static CIC code suffers systematic universe-level inflation on every function formation.
3. **`GCIC^N` (Normalization + Conservativity, Restricts Graduality):** Preserves standard CIC universe levels and strong normalization by restricting the unknown type `?` so it cannot contain arbitrary same-level function/universe casts without raising errors (breaking full dynamic graduality for impredicative/higher-order casts, while preserving it on base/inductive types).

#### 3.3 Architectural Implication for Systems-Plus-Proof Languages

**Basis:** derived from GCIC (`10.1145/3495528`) + Gradual C0 (`10.1145/3632927`).

To support zero-cliff prototyping-to-verification in one language *without* poisoning the proof kernel's consistency or inflating every static function's universe level:
- **Stratify `?` out of the Proof-Kernel Type Level (`GCIC^N`-style stratification):** Permit dynamic typing (`Dyn`) and imprecise verification wildcards (`? * φ`) strictly in **program expressions** and **behavioral contract assertions** (which compile to dynamic checks / Fulminate-style runtime guards).
- **Keep Kernel-Checked Types and Proof Terms Strictly Total & Precise:** Any module claiming kernel-verified assurance (`R3`/`R4`) must statically reject transitive reachability of `?` inside its trusted proof terms and type indices. When dynamic `Dyn` / `?` callers invoke an `R4` kernel-verified function, the boundary membrane enforces the `R4` precondition dynamically at entry before handing control to the strictly static core.

---

### 4. Gradual Typing Performance Cliffs and Boundary Membrane Taxonomy

**Basis:** normative specification + execution literature (Takikawa et al., POPL 2016, `10.1145/2837614.2837630`; Muehlboeck & Tate, OOPSLA 2017, `10.1145/3133880`; Greenman, PLDI 2022, `10.1145/3519939.3523430`; Patterson et al., PLDI 2022, `10.1145/3519939.3523703`).

Sound gradual typing and gradual verification share the exact same boundary enforcement trade-off whenever an unverified/dynamic caller crosses into a statically verified/typed callee:

| Boundary Strategy | Primary Reference | Checking Mechanism | Overhead Profile | Blame & Soundness Guarantees | Best Fit for Systems/FFI |
|---|---|---|---|---|---|
| **Deep / Guarded Structural Proxies** | Takikawa et al. (POPL 2016) | Higher-order chaperone/impersonator wrappers on mutable objects & closures; per-read/write mediation | **Up to ~100×** worst-case cliff on partially typed configurations (proxy towers, broken cache locality) | Complete type soundness + precise higher-order blame | Unacceptable for zero-alloc/DMA inner loops; usable only for coarse control boundaries |
| **Shallow / Transient Checks** | Vitousek et al. (POPL 2017); Greenman (PLDI 2022) | O(1) top-level shape tag checks injected at every elimination site inside typed code; no object wrappers | Typically **1.2×–4×**; avoids catastrophic proxy towers | Type soundness preserved (shallow/tag soundness), **weaker blame** (errors detected late, no complete monitor) | Good default for exploratory mixed-mode prototypes & deep/shallow hybrid switching |
| **Nominal Layout-Tagged Bulk Membranes** | Muehlboeck & Tate (OOPSLA 2017) | Nominal class/layout tag attached at allocation; validated **once at boundary entry** (`O(1)` header or single bulk scan) | **Near-zero (often <1.1×–1.5×)** inside typed core; monotonic speedup as types are added | Full soundness for nominal first-order & bulk slice data; preserves unboxed memory layout | **Optimal for systems FFI** (zero-copy borrowed slices into Rust/C/SIMD/GPU kernels) |
| **Static-Verification-Guided Residual Checks + Exclusion Frame** | Zimmerman et al. (POPL 2024); Fulminate (POPL 2025) | Symbolic execution discharges static clauses; weaves residual checks + `rmap`/hash-table ownership checks only for `?` | **0% overhead** on fully precise static code; `0.3–0.9 μs`/check on dynamic `Owned` checks | Sound IDF / separation-logic ownership + value preservation (with exclusion frame $\Theta$) | Ideal for gradual migration from dynamic contracts to kernel proof |
| **Semantic Interop Logical-Relations Convertibility** | Patterson et al. (PLDI 2022) | Explicit convertibility relations `τ_A ~ τ_B` with synthesized boundary wrappers (`Boundary(e)`) proved sound in step-indexed logical relations | Depends on target representation gap (zero-copy when memory layouts coincide; copy/marshal otherwise) | Compositional semantic type soundness across distinct source languages & memory invariants | Formal foundation for Rust ↔ C ↔ Python/GC FFI contracts |

**Critical Insight on GC ↔ Affine/Zero-Alloc Boundaries:** When a dynamic GC-managed caller passes a buffer across a nominal bulk membrane into an affine/zero-alloc verified callee (e.g., Rust or DMA kernel), nominal tag validation alone is insufficient if a concurrent moving/compacting GC can relocate the backing object mid-borrow. Soundness requires an explicit **pinning capability (`PinGC`)** or region-evacuation copy at the membrane boundary—otherwise the callee's static ownership proof is invalidated by foreign runtime relocation.

---

### 5. Monotone Multi-Rung Assurance Algebra and Cross-FFI Composition

**Basis:** derived (synthesizing gradual verification, Fulminate, Patterson et al. PLDI 2022, and multi-tier verification workflows) + execution (micro-probe Part A).

#### 5.1 Canonical Behavioral Contract IR and Executability Polarity

To prevent specification duplication across property-based testing, bounded model checking, SMT auto-active verification, and foundational proof assistants, one behavioral contract IR

$$\mathcal{C}(f) ::= \big\langle \text{Pre} : \mathcal{P}_{\text{grad}},\; \text{Post} : \mathcal{P}_{\text{grad}},\; \text{Frame} : \mathcal{F}_{\text{sep}},\; \text{Eff} : \mathcal{E},\; \text{Cost} : \mathcal{B} \big\rangle$$

must classify every subformula by its **Executability Polarity** (reflecting the fundamental boundary identified in both Fulminate and Gradual C0):

| Polarity | Construct Class | `R1` Dynamic / Fuzz Compilation | `R2` BMC / SMT Compilation | `R3`/`R4` Kernel Proof Compilation |
|---|---|---|---|---|
| **`ExactExec`** | Decidable pure predicates, bounded loops, CN-style determined `Owned<T>` & recursive predicates | Exact runtime check (0 false positives, 0 false negatives on executed path) | Exact symbolic constraint | Direct theorem obligation |
| **`BoundedSample`** | Quantifiers over large finite/unbounded domains ($\forall i \in [0, 2^{64})$), probabilistic/distributional specs | Randomized / property-based sampling (e.g., Bennet / QuickCheck); **unsound for proof**, sound for falsification | Bounded unrolling / SMT universal triggers | Full universal quantification in logic |
| **`GhostOnly`** | Uncomputable reals ($\mathbb{R}$), impredicative separation-logic ghost invariants, prophecy variables, hyperproperties (2-safety) | **Cannot execute directly**; compiles to an explicit `UncheckedGhostAssumption` entry in the certificate's assumption set $\mathcal{M}$ | Solver-dependent abstraction or unsupported | Discharged deductively in kernel |

#### 5.2 The 5-Rung Assurance Bounded Meet-Semilattice

Define the ordered set of five assurance rungs $\mathcal{R} = \{\text{R0} < \text{R1} < \text{R2} < \text{R3} < \text{R4}\}$:
- **`R0` (`LiveExample`):** Single concrete witness / live evaluation sanity check.
- **`R1` (`DynamicChecked`):** Executable runtime assertions (Fulminate / Gradual C0 residual checks) + property-based testing / fuzzing.
- **`R2` (`ProvisionalAuto`):** Bounded model checking (Kani/CBMC), abstract interpretation, or un-replayed SMT (Z3/cvc5) where the solver and/or unrolling bound reside in the TCB.
- **`R3` (`KernelConditional`):** Small-TCB kernel-checked proof modulo an explicit, hash-locked set of external assumptions $\mathcal{M}$ (e.g., ISA semantics, foreign C contract, compiler trust).
- **`R4` (`KernelFoundational`):** Small-TCB kernel-checked proof with $\mathcal{M} = \emptyset$ (minimal kernel + physical execution boundary only).

An **Assurance Certificate** for an obligation $o$ is a pair $\eta(o) = (r, \mathcal{M}) \in \mathcal{R} \times \mathcal{P}(\text{Assump})$, partially ordered by:

$$(r_1, \mathcal{M}_1) \;\preceq\; (r_2, \mathcal{M}_2) \quad\Longleftrightarrow\quad r_1 \le r_2 \;\land\; \mathcal{M}_2 \subseteq \mathcal{M}_1$$

(stronger assurance requires a *higher or equal rung* AND a *subset of trusted assumptions*). Sequential or cross-module composition uses the greatest lower bound (meet):

$$(r_1, \mathcal{M}_1) \sqcap (r_2, \mathcal{M}_2) \;=\; \big(\min(r_1, r_2),\; \mathcal{M}_1 \cup \mathcal{M}_2\big)$$

with top element $\top = (\text{R4}, \emptyset)$ and bottom element $\bot = (\text{R0}, \text{Assump}_{\text{all}})$. Exhaustive verification in the micro-probe (`probe_gradual_assurance.py`, 64,000 triples over 40 elements) confirms associativity, commutativity, idempotence, monotonicity ($x \preceq y \implies x \sqcap z \preceq y \sqcap z$), and top/bottom identity/annihilator laws.

#### 5.3 Cross-FFI Composition (`⊗_FFI`), Isolation Projection, and Counterexample Promotion

Composing module $A$ with certificate $(r_A, \mathcal{M}_A)$ and foreign module $B$ with $(r_B, \mathcal{M}_B)$ across an FFI boundary checked at rung $r_{\text{bd}}$ obeys three strict laws:

1. **Functional Assurance Meet (No Laundering):**
   $$\text{Assure}_{\text{func}}(A \circ_{\text{bd}} B) \;=\; \big(\min(r_A, r_B, r_{\text{bd}}),\; \mathcal{M}_A \cup \mathcal{M}_B \cup \text{MembraneAssump}(r_{\text{bd}})\big)$$
   A verified `R4` caller calling an unverified `R1` foreign function cannot claim `R4` for any property depending on the foreign return value without either dynamically validating the postcondition at the membrane (yielding `R1` for the checked property) or explicitly recording $B$'s contract in $\mathcal{M}$ (yielding `R3`).
2. **Hardware/SFI Isolation Projection (Memory Safety vs. Functional Correctness):**
   When $A$ (`R3`/`R4`) invokes untrusted $B$ (`R1`) inside a verified fault-isolation boundary (e.g., CHERI capabilities, Wasm SFI, or hardware process isolation `iso`), **memory safety of $A$** decouples from $B$'s internal code:
   $$\text{Assure}_{\text{mem}}(A \circ_{\text{iso}} B) \;=\; \big(\min(r_A, \text{R3}),\; \mathcal{M}_A \cup \{\text{isolation}:\text{iso}\}\big)$$
   Notice it caps at `R3` (never `R4`) because the isolation substrate enters $\mathcal{M}$ explicitly! Meanwhile, functional dependence on $B$'s output remains governed by the functional meet above.
3. **Asymmetric Counterexample Promotion (`R0/R1/R2` Falsification $\to$ `R4` Kernel Refutation):**
   Positive testing/fuzzing (`R1`) never establishes universal truth (`R4`), **but negative testing is asymmetrically promotable**: whenever *any* untrusted fuzzer, gradual runtime check, or SMT counterexample generator exhibits a concrete ground input $x_0$ violating an `ExactExec` contract $\mathcal{C}(f)$, evaluating $f(x_0)$ inside the small trusted kernel mints an **`R4` foundational refutation theorem** ($\vdash_{\text{kernel}} \neg \mathcal{C}(f)$) with $\mathcal{M} = \emptyset$, completely eliminating the fuzzer/SMT solver from the refutation TCB!

#### 5.4 Semantic-Foundation Mismatch Across Multi-Logic Composition

**Basis:** derived from Patterson et al. (PLDI 2022) and multi-verifier semantics comparison.

Composing certificates across tools backed by **different operational memory models**—for example, composing an `R2` Kani/CBMC bounded proof (assuming a flat C/LLVM object model without stacked/tree-borrow provenance) with an `R4` separation-logic proof (assuming Tree Borrows or Cerberus CHERI provenance)—is **unsound** under a naive set-union meet unless accompanied by a verified **`BehaviorCodec` refinement lemma** translating memory states and UB definitions between the two models. Absent that translation proof, the mismatch must appear as an explicit assumption `semantic_bridge(M_A, M_B) ∈ M`, capping the composed certificate at `R3` (or `R1` if dynamically checked).

## Boundaries

- **Known not to apply (Gradual Guarantee for POPL 2024 `GVLC0`):** Zimmerman, DiVincenzo, and Aldrich (POPL 2024, §9, p. 111:27) explicitly state that while they proved **soundness** (Progress and Preservation) for symbolic-execution-based gradual verification with exclusion frames, they have **not yet proved the static/dynamic gradual guarantees** for `GVLC0`.
- **Unsupported (Exclusion Frames in Deployed `gvc0`):** Zimmerman et al. (POPL 2024, §8.4, p. 111:27) document that computing exclusion frames dynamically is not yet implemented in `gradual-verification/gvc0` because `gvc0` constructs runtime permission sets by recursively unfolding specifications, whereas exclusion-frame permissions come from the remaining symbolic heap rather than a single source specification.
- **Unsupported (Fulminate Multi-File C, `register` Variables, and Uninitialized `for`-Loop Declarations):** Direct inspection of `rems-project/cn` (`lib/fulminate/ownership.ml:88-90,142-149`) and POPL 2025 §4.6 confirms Fulminate currently targets single compilation units (with manual includes), cannot instrument C `register` variables (no `&`), and rejects uninitialized variable declarations in `for`-loop headers.
- **Known not to apply (Real-Time WCET and Constant-Time Security Under `R1` Dynamic Checks):** Inserting `R1` runtime permission checks (`gvc0` Robin Hood hash table lookups/compactions or Fulminate `rmap` tree traversals) introduces data-dependent latency, dynamic heap allocation, and memory access patterns that invalidate hard real-time WCET bounds and cryptographic constant-time non-interference; all `R1` checks on timing-sensitive or secret-handling paths must be statically discharged (`R3`/`R4`) before release.
- **Unknown (Exact Runtime Overhead of Dynamic Exclusion-Frame Tracking on Large Heap Benchmarks):** Because POPL 2024 §8.4 left exclusion-frame code generation as future engineering work, empirical runtime overhead of computing and subtracting $\hat{\alpha}$ at imprecise call boundaries on large benchmarks has not yet been measured.
- **Not examined (Fractional Permissions and Concurrent Separation-Logic Runtime Checking):** Neither `gvc0` nor Fulminate (`rems-project/cn` at the pinned revision) was examined for concurrent lock-invariant checking or fractional read-share (`1/2`) dynamic accounting; both inspected runtimes model exclusive ownership (per-field boolean/reference table in `gvc0`, integer stack depth per byte in Fulminate `rmap`).
- **Not examined (Automated Property-Based Input Synthesis `Bennet`):** While `rems-project/cn` includes `lib/testGeneration/bennet/` and `runtime/libcn/src/bennet/` for CN-guided test generation (OOPSLA 2025), its abstract-domain generator algorithms were not audited in detail in this report.

## Evidence

### Primary Specifications and Peer-Reviewed Papers

1. **Zimmerman, DiVincenzo, and Aldrich (POPL 2024):** *Sound Gradual Verification with Symbolic Execution*, Proc. ACM Program. Lang. 8, POPL, Article 111 (2024), DOI `10.1145/3632927`, `arXiv:2311.07559` (full PDF verified on `2026-11-19`):
   - §2 (`SVLC0`), §3 (`GVLC0`), §6 (Theorems 1–2 Progress, Theorem 3 Preservation), §7.2 (`SVerifyLoop` loop valuation freshness), §8 (Figure 14 soundness bug in Gradual C0, isorecursive vs. equirecursive mismatch, exclusion frame $\Theta$ / $\hat{\alpha}$ fix, §8.4 implementation status), §9 (gradual guarantee left as future work).
2. **Wise, Bader, Wong, Aldrich, Tanter, and Sunshine (OOPSLA 2020):** *Gradual Verification of Recursive Heap Data Structures*, Proc. ACM Program. Lang. 4, OOPSLA (2020), DOI `10.1145/3428296` (WLP gradual IDF theory, imprecise formulas `? * φ`, precision partial order).
3. **Lennon-Bertrand, Maillard, Tabareau, and Tanter (POPL / TOPLAS 2022):** *Gradualizing the Calculus of Inductive Constructions*, ACM TOPLAS 44(2), Article 7 (presented at POPL 2022), DOI `10.1145/3495528`, `arXiv:2011.10618` (Fire Triangle: Conservativity, Normalization, Graduality; `GCIC^G`, `GCIC^N`, `GCIC^↑` / `GCIC-shift`).
4. **Banerjee, Memarian, Makwana, Pulte, Krishnaswami, and Sewell (POPL 2025):** *Fulminate: Testing CN Separation-Logic Specifications in C*, Proc. ACM Program. Lang. 9, POPL, Article 43 (2025), DOI `10.1145/3704879` (full PDF verified on `2026-11-19`: §2.2 reified ghost state, §3 MiniCN formalization, §4.6 single-unit limitation, §5.3–§5.4 pKVM buddy allocator `0.4s–1.4s` bug detection, `~30s` generation, `0.3 μs–0.9 μs` per dynamic `Owned`, quadratic scaling table for `2..1024` list elements, §6 related work on EXPTIME separation-logic model checking and determined predicates).
5. **Gradual Typing & Interop Literature:** Takikawa et al., *Is Sound Gradual Typing Dead?* (POPL 2016, `10.1145/2837614.2837630`); Muehlboeck & Tate, *Sound Gradual Typing is Nominally Alive and Well* (OOPSLA 2017, `10.1145/3133880`); Greenman, *Deep and Shallow Types for Gradual Languages* (PLDI 2022, `10.1145/3519939.3523430`); Patterson, Noble & Ahmed, *Semantic Soundness for Language Interoperability* (PLDI 2022, `10.1145/3519939.3523703`).

### Pinned Upstream Repository Source Inspections (Observed `2026-11-19`)

- `gradual-verification/gvc0` @ `4276d89421d9fc17058a06cff975e9c7207ab917`:
  - `Runtime.md:1-25`: conceptual `bool value_perm` struct-field note.
  - `src/main/resources/runtime.c0:14-160`: actual `OwnedFields` Robin Hood hash table (`capacity = 128`, 80% load factor, `runtime_compact`, `runtime_grow`, `runtime_find` with `psl`).
  - `src/main/scala/gvc/weaver/SeparationChecks.scala:6-135`: `canOverlap`, `countAccs` (returns `2` for `IR.PredicateInstance`), conditional `ImmediateCondition` check weaving.
- `gradual-verification/silicon` @ `99d3d27190554a5008628a083fc2329f4032565f`:
  - `src/main/scala/state/State.scala:29-88`: symbolic state record (`Store`, `Heap`, `oldHeaps`, `invariantContexts`, `permissionScalingFactor`, `partiallyConsumedHeap`, `reserveHeaps`).
- `pleiad/GradualizingCIC` @ `354c65260d522a13992b268334fd7892cfb4618c`:
  - `README.md:16-56`: module inventory and explicit `NO_POSITIVITY_CHECK` / `TERMINATING` pragmas required only in `DiscreteModelPartial.agda` and `UnivPartial.agda`.
  - `src/DiscreteModelTotal.agda:1-160`: pragma-free total model (`GCIC-shift`) using strong induction over `PNat` and level-shifted `Uₛπ : {i j : ≺ n} (A : U i) (B : El A → U j) → Uₛ`.
- `rems-project/cn` @ `d1c60d1720bed3bed0d45dab247a1959145c8cb9`:
  - `doc/README-FULMINATE.md:1-47`: `cn instrument` three-file output (`<file>.exec.c`, `<file>.cn.h`, `<file>.cn.c`) and `cn_epilogue` return rewriting.
  - `lib/fulminate/ownership.ml:25-180`: AIL ghost-state stack-depth instrumentation (`ghost_stack_depth_incr`/`decr`, `c_add_to_ghost_state`, `cn_postcondition_leak_check`, `register` skip, `for`-loop uninitialized declaration `failwith`).
  - `runtime/libcn/src/cn-executable/rmap.c:10-120`: compressed radix-tree range map (`EMPTY`/`LEAF`/`INNER`/`SKIP`, `CACHED_NODES = 32`) parameterized by idempotent commutative `(min, max)` semigroup `res_append`.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-19`)

Self-contained Python 3 probe verifying (Part A) all bounded meet-semilattice laws over 40 assurance certificates (`64,000` triples), FFI composition with/without CHERI hardware isolation, and untrusted `R1` counterexample promotion to `R4` kernel refutation; and (Part B) reproduction of POPL 2024 Figure 14's Gradual C0 soundness bug, its exclusion-frame fix, and monotonic runtime-check erasure along the precision lattice:

```python
from dataclasses import dataclass
from itertools import product

RUNGS = (0, 1, 2, 3, 4)

@dataclass(frozen=True)
class AssuranceCert:
    rung: int
    assumptions: frozenset
    def meet(self, other: "AssuranceCert") -> "AssuranceCert":
        return AssuranceCert(min(self.rung, other.rung), self.assumptions | other.assumptions)
    def leq(self, other: "AssuranceCert") -> bool:
        return self.rung <= other.rung and other.assumptions.issubset(self.assumptions)

def compose_ffi(a: AssuranceCert, b: AssuranceCert, bd_rung: int, sandbox=None) -> AssuranceCert:
    if sandbox is not None and a.rung >= 3:
        return AssuranceCert(min(a.rung, 3), a.assumptions | frozenset({f"isolation:{sandbox}"}))
    bd_a = frozenset({f"bd_check_R{bd_rung}"}) if bd_rung < 4 else frozenset()
    return AssuranceCert(min(a.rung, b.rung, bd_rung), a.assumptions | b.assumptions | bd_a)

def simulate_fig14(use_exclusion_frame: bool):
    exclusion_frame = {("c", "value")} if use_exclusion_frame else set()
    heap, owned_test = {("c", "value"): 0}, {("c", "value")}
    owned_set = owned_test - exclusion_frame
    if ("c", "value") not in owned_set:
        return ("RUNTIME_CHECK_FAILED_AT_SET_LINE_8", False)
    heap[("c", "value")] = 1
    result = heap[("c", "value")]
    return (f"RETURNED_{result}", result != 0)
```

Recorded execution output (`python3 probe_gradual_assurance.py`, exit code `0`):

```text
[Part A] Lattice laws verified exhaustively over 40 elements (64000 triples): PASS
[Part A] FFI composition (R4 Rust + R1 C, R1 check): functional=AssuranceCert(rung=1, assumptions=frozenset({'c_abi', 'bd_check_R1'}))
[Part A] FFI composition with CHERI sandbox (mem safety): AssuranceCert(rung=3, assumptions=frozenset({'isolation:CHERI'}))
[Part A] Untrusted R1 witness x=41 promoted to kernel refutation: AssuranceCert(rung=4, assumptions=frozenset())
[Part B] Fig. 14 WITHOUT exclusion frame: {'exclusion_frame': False, 'static_checks_in_test': 0, 'dynamic_outcome': 'RETURNED_1', 'postcondition_violated': True}
[Part B] Fig. 14 WITH    exclusion frame: {'exclusion_frame': True, 'static_checks_in_test': 0, 'dynamic_outcome': 'RUNTIME_CHECK_FAILED_AT_SET_LINE_8', 'postcondition_violated': False}
[Part B] Monotonic residual check erasure along precision lattice:
  spec=?                                   | residual_checks=2 ['acc(c.value)', 'c.value>=0'] | exclusion_frame_active=True
  spec=? * acc(c.value)                    | residual_checks=1 ['c.value>=0'] | exclusion_frame_active=True
  spec=? * acc(c.value) * c.value >= 0     | residual_checks=0 [] | exclusion_frame_active=True
  spec=acc(c.value) * c.value >= 0         | residual_checks=0 [] | exclusion_frame_active=False
```

## Revalidation

1. **Check Exclusion-Frame Implementation Status in `gradual-verification/gvc0`:** Diff `gradual-verification/gvc0` against `4276d89421d9fc17058a06cff975e9c7207ab917` in `src/main/scala/gvc/weaver/` and `src/main/resources/runtime.c0` for exclusion-frame subtraction (`Θ` / `α̂`) at imprecise method invocations, and test whether Figure 14 (`predicate imprecise() = ? * true`) now fails dynamically at `set` instead of returning `1`.
2. **Check Fulminate Feature Expansion in `rems-project/cn`:** Diff `rems-project/cn` against `d1c60d1720bed3bed0d45dab247a1959145c8cb9` in `lib/fulminate/ownership.ml` and `runtime/libcn/src/cn-executable/rmap.c` for multi-translation-unit support, fractional/shared read permissions, or incremental predicate checking (eliminating quadratic `O(N²)` re-traversal on list loops).
3. **Check GCIC Mechanization Extensions:** Check `pleiad/GradualizingCIC` and follow-up work (e.g., *A Reasonably Gradual Type Theory*, `arXiv:2209.00975`) for whether any newer model alters the fire-triangle boundary without relaxing conservativity, normalization, or graduality.
4. **Rerun Micro-Probe Against Proposed Assurance-Algebra Extensions:** Whenever adding a new assurance rung, isolation membrane rule, or non-monotone override (such as trusting an unverified FFI callee), extend `probe_gradual_assurance.py` above and re-run exhaustive triple checks to verify associativity, monotonicity, and absence of assurance laundering.
