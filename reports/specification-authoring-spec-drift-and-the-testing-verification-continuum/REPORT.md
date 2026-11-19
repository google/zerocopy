# Specification Authoring, Specification-Implementation Drift, and the Testing-to-Verification Continuum

## Summary

Formal verification of systems software routinely bottlenecks on three coupled obstacles: **the specification wall** (authoring faithful, minimal, frame-complete contracts whose downstream proof size grows quadratically with formal-statement size across 15,018 Isabelle lemmas in seL4 and the Archive of Formal Proofs), **specification-implementation drift** (divergence between design models, unverified boundary assumptions, and evolving production code—responsible for all 16 bugs uncovered by Fonseca et al. in IronFleet, Verdi, and Chapar and for the manual translation gap in AWS's TLA+ practice), and the **assurance discontinuity** separating dynamic testing/fuzzing from bounded model checking and deductive proof.

Four concrete techniques examined in this report bridge that discontinuity:

1. **Precondition-aware executable specifications (`QuickCheck`, `QuickChick`, `FuzzChick`, `Bennet`)**: Naive generate-and-filter property testing (`==>`) suffers discard starvation on sparse relational or heap-layout invariants (100.0% discards across 10,000 trials in the companion probe). Deriving certified constructive generators from inductive relations (`QuickChick`), adding AFL-style edge-coverage guidance (`FuzzChick`), or compiling separation-logic preconditions via product abstract domains (`Bennet` in `rems-project/cn`) eliminates discard starvation while testing the same specification later used for proof.
2. **Runtime separation-logic checking via reified ownership ghost state (`CN` / `Fulminate`)**: Because CN restricts separation logic to linear resource types (`Owned<cty>`, `Block<cty>`, bounded `each(...)`, user predicates) syntactically separated from pure constraints, `Fulminate` compiles CN pre-/postconditions into executable C checks over a flat byte-to-stack-depth ghost map $G : \mathrm{Addr} \rightharpoonup \mathrm{StackDepth}$ (implemented via the radix-tree interval map `rmap` in `rems-project/cn`). It dynamically catches aliasing, frame violations, ownership leaks, and functional bugs at 0.3–0.9 μs per dynamic `Owned` check on Google's pKVM buddy allocator before any proof effort.
3. **Gradual verification (`? * P`) with sound symbolic execution and exclusion frames (`Gradual C0` / `silicon-gv`)**: Explicitly imprecise formulas (`? * P`) allow gradual migration from dynamic checks to static proof, cutting runtime overhead by 11–34% on average over checking all obligations dynamically. However, mixing static *isorecursive* predicate consumption with dynamic *equirecursive* permission passing caused a concrete soundness bug in `Gradual C0` (Zimmerman, DiVincenzo & Aldrich, POPL 2024, Fig. 14) where an imprecise callee mutates a statically framed field after the caller's postcondition check is elided; soundness requires passing a statically computed **exclusion frame** $\hat{\alpha}$ so callees receive only $\alpha \setminus \hat{\alpha}$.
4. **Unified multi-engine harnesses (`Bolero`, `Kani`, `Crux-MIR`) and epistemic asymmetry for counterexample promotion**: Running one Rust harness across fuzzers, deterministic RNG/exhaustive engines, and `Kani` CBMC (`camshaft/bolero`)—or combining Kani function contracts with `--concrete-playback`—unifies bug finding and bounded verification, subject to explicit slice bounds (`MAX_LEN = 256`) and generator-vacuity checks (`kani::cover!`). Crucially, verification and falsification are **epistemically asymmetric**: proving $\forall x \in D,\, P(x) \implies Q(x, \llbracket f \rrbracket(x))$ requires trusted full-domain reasoning, whereas disproving it requires only replaying one concrete witness $x_0$ discovered by an *untrusted* fuzzer, PRNG, or SMT solver through a small trusted kernel evaluator (`trust_level = 0`), rejecting spurious witnesses while halting doomed proof searches with zero TCB expansion.

## Applicability

This report synthesizes peer-reviewed literature, pinned upstream repositories, and an executable Python 3.10+ probe (`support/verify_spec_continuum_and_fulminate.py`) covering C, Rust, C0, Haskell, and Rocq/Coq specification and testing toolchains.

### Subject Relationships

The 21 durable subjects in `REPORT.json` form five coordinated groups:

- **Cost and drift baselines**: Matichuk et al. (ICSE 2015), Newcombe et al. (CACM 2015), Bornholt et al. (SOSP 2021), and Fonseca et al. (EuroSys 2017) establish proof-size scaling, model-to-code translation drift, executable reference modeling, and residual TCB-boundary bug distributions.
- **Executable specs & precondition-aware PBT**: Claessen & Hughes (ICFP 2000), Lampropoulos et al. (POPL 2018, OOPSLA 2019), `QuickChick/QuickChick` (`ed334c76a7fbd6eefe9b1e618e42ce9c70dd8691`), and Aamer & Pierce (OOPSLA 2025, `Bennet`).
- **Runtime separation-logic checking**: Banerjee et al. (POPL 2025, `Fulminate`), `rems-project/cn` (`d1c60d1720bed3bed0d45dab247a1959145c8cb9`), and `rems-project/cerberus` (`e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e`, recording CN's extraction out of `backend/cn/`).
- **Gradual verification**: Bader, Aldrich & Tanter (VMCAI 2018), Wise et al. (OOPSLA 2020), Zimmerman, DiVincenzo & Aldrich (POPL 2024 / `arXiv:2311.07559`), DiVincenzo et al. (TOPLAS 2025 / `arXiv:2210.02428`), `gradual-verification/gvc0` (`4276d89421d9fc17058a06cff975e9c7207ab917`), and `gradual-verification/silicon-gv` (`03a17ab4e796683d36cf203572ec93d572f69c3f`).
- **Unified Rust harnesses & symbolic playback**: `camshaft/bolero` (`968b6b3510acbc22123e035278b1665e671a4c21`, v0.13.7), `model-checking/kani` (`c25a57bcbf8c8af41617e7171a535a3518ce514a`), and `GaloisInc/crucible` (`2e37f7e1f06730125075e4b1ec1d19b8af5736cb`, `crux-mir/` and `crux-test-gen/`).

### Corpus Cross-References and Scope Boundaries

- For vacuity detection, semantic mutation testing of operational models, negative canary suites, and Lean 4 kernel scaling, see **`anneal-vacuity-mutation-oracles-and-verification-scaling`**.
- For compiler differential testing, `Csmith` campaigns, test reduction, and `rustc`/`Miri`/`MiniRust` bug records, see **`compiler-differential-testing-fuzzing-reduction-and-bug-records`**.
- For auto-active VCGen architectures (`Dafny`, `Boogie`, `Viper`, `F*`, `Why3`) and SMT obligation encodings, see **`dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures`**.
- Source observations apply strictly to the pinned revisions in `REPORT.json`; paper-to-HEAD divergences (`rmap` in `rems-project/cn`, `OwnedFields` vs. `Runtime.md` in `gvc0`) are explicitly noted. The standalone Python probe models simplified imperative heaps and bitvectors to test structural invariants rather than production runtime throughput.

## Findings

### 1. The Specification Wall, Superlinear Proof Scaling, and Spec-Implementation Drift

Basis: documentation + derived (Matichuk et al. ICSE 2015; Klein et al. SOSP 2009 / TOCS 2014; Newcombe et al. CACM 2015; Fonseca et al. EuroSys 2017; Yang et al. PLDI 2011; Bornholt et al. SOSP 2021).

Authoring specifications that are simultaneously **faithful** to engineering intent, **minimal** (free of leaky internal details), and **frame-complete** (bounding all mutated state and external assumptions) frequently exceeds implementation complexity. Three empirical studies anchor this wall:

1. **Quadratic proof growth in formal-statement size**: Matichuk et al. (ICSE 2015, DOI `10.1109/ICSE.2015.85`) analyzed 15,018 Isabelle lemmas (~215,000 proof lines across seL4 and the two largest software verification entries in the Archive of Formal Proofs) and found a consistent **quadratic relationship** between formal-statement size and proof size. Because human proof effort scales roughly linearly with proof size, every extra auxiliary invariant, frame clause, or representation-specific conjunct inflates downstream proof effort superlinearly. In seL4 itself (Klein et al., SOSP 2009, DOI `10.1145/1629575.1629596`; TOCS 2014, DOI `10.1145/2560537`), ~8.7k lines of C required ~200k lines of Isabelle (~20:1) while initially leaving boot code, hand-written assembly, cache/TLB management, and hardware semantics in the TCB.
2. **Residual bugs concentrate at unverified specification and boundary seams**: Fonseca et al. (EuroSys 2017, DOI `10.1145/3064176.3064183`) audited IronFleet, Verdi, and Chapar and uncovered **16 bugs** causing server crashes, incorrect client responses, and violated safety guarantees. All 16 lived outside the mechanized proofs—in specifications, unverified assumptions about the OS/network/serialization layers, or extraction/runtime shims. Similarly, Yang et al. (PLDI 2011, DOI `10.1145/1993498.1993532`) spent ~6 CPU-years running Csmith and found **0 wrong-code bugs** in CompCert's formally verified middle-end, while uncovering real bugs in its unverified front-end and back-end glue (see `compiler-differential-testing-fuzzing-reduction-and-bug-records`).
3. **Design-level drift under manual translation**: Newcombe et al. (CACM 2015, DOI `10.1145/2699417`) showed how AWS used TLA+ and TLC across DynamoDB, S3, EBS, and an internal lock manager—finding a **35-step** replication/group-membership data-loss trace in DynamoDB missed by reviews and stress testing. Because AWS engineers manually translated verified TLA+ designs into production C++/Java, ongoing code edits create silent **spec-implementation drift** unless models are updated in lockstep. On S3's ShardStore storage node, Bornholt et al. (SOSP 2021, DOI `10.1145/3477132.3483540`) narrowed this gap by pairing an executable reference model with property-based and crash-consistency tests run directly against the production Rust code.

#### Taxonomy of Specification Fragility and Drift

| Failure / Friction Class | Concrete Mechanism | Empirical Precedent | Structural Mitigation |
| :--- | :--- | :--- | :--- |
| **Frame & aliasing boilerplate** | `modifies`/`reads` clauses, `old()` snapshots, predicate `fold`/`unfold`, and disjointness lemmas recur at every caller. | seL4 / Viper / VeriFast heap proofs; raw-pointer and FFI boundaries beyond Rust `&mut`. | Ownership-type framing, implicit dynamic frames (see `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures`), or runtime ownership checks (`Fulminate`). |
| **Representation-coupled invariants** | Loop invariants and separation-logic ghost state expose private fields (intrusive links, hash-table probe lengths), breaking callers on refactors. | Matichuk et al. (ICSE 2015) quadratic proof growth in statement size. | Opaque abstract predicates and refinement against small executable reference models (ShardStore). |
| **Silent TCB & boundary drift** | Proofs assume idealized allocator, syscall, FFI ABI, or hardware contracts that diverge from reality. | Fonseca et al. (EuroSys 2017): 16/16 bugs at TCB/spec/shim seams; Csmith on CompCert's unverified front-end. | Execute boundary specs dynamically against real runtimes (`Fulminate`, differential oracles, negative mutation canaries—see `anneal-vacuity-mutation-oracles-and-verification-scaling`). |
| **Vacuous or over-weak contracts** | Unsatisfiable `requires`, contradictory axioms, or trivial `ensures` pass deductive proof silently. | Unguarded BMC harnesses (`bolero-kani` unsatisfiable generators; `model-checking/kani#2792`). | Executable spec testing, reachability `cover!` checks, spec mutation, and pre-proof falsification. |

---

### 2. Executable Specifications and Precondition-Aware Property-Based Testing

Basis: normative (Claessen & Hughes ICFP 2000; Lampropoulos et al. POPL 2018 & OOPSLA 2019; Aamer & Pierce OOPSLA 2025) + source (`QuickChick/QuickChick@ed334c76a7`, `rems-project/cn@d1c60d1720`) + execution (`support/verify_spec_continuum_and_fulminate.py`).

#### The `==>` Precondition-Sparsity Wall (`QuickCheck`)

Claessen & Hughes (ICFP 2000, DOI `10.1145/351240.351266`) introduced QuickCheck's type-driven `Arbitrary` generators, conditional properties (`==>`), and distribution monitors. Under `P ==> Q`, inputs are sampled uniformly by type and discarded whenever `P x` is false. On sparse systems preconditions—well-typed ASTs, balanced trees, or disjoint sorted memory ranges—acceptance probability decays exponentially. In `support/verify_spec_continuum_and_fulminate.py` (Part 3), checking 6 strictly ordered, non-empty, disjoint intervals within `[0, 255]` via generate-and-filter yields **0 valid inputs in 10,000 random trials (100.0% discard rate)**, whereas a constructive generator sampling $2k$ distinct sorted endpoints yields **1,000 / 1,000 valid inputs (0.0% discard rate)**.

#### Inductive-Relation Generators, Coverage Feedback, and Abstract-Domain Synthesis

Three lines of tooling compile specifications directly into valid input generators so the generator cannot drift from the formal precondition:

1. **Narrowing-derived certified generators (`QuickChick`, POPL 2018)**: Lampropoulos, Paraskevopoulou & Pierce (POPL 2018, DOI `10.1145/3158133`) compile Coq/Rocq inductive relations into sized backtracking generators via narrowing-inspired unification (`plugin/arbitrarySizedST.ml`, `plugin/unifyQC.ml.cppo` in `QuickChick/QuickChick@ed334c76a7`) and certify soundness and completeness inside the proof assistant (`src/DependentClasses.v:13-48`, `src/Decidability.v:17`):
   ```coq
   Class CorrectSizedST {A : Type} (P : A -> Prop) {G} `{Producer G} (g : nat -> G (option A)) :=
     { corrST : [ set x | exists s, semProdOpt (g s) x ] <--> P }.

   Class GenSizedSuchThat (A : Type) (P : A -> Prop) :=
     { arbitrarySizeST : nat -> G (option A) }.
   ```
   `CorrectSizedST` ensures the union of producible values across sizes equals `P` exactly—preventing both false-alarm invalid inputs and silent blind spots.
2. **Coverage-guided structured PBT (`FuzzChick`, OOPSLA 2019)**: Lampropoulos, Hicks & Pierce (OOPSLA 2019, DOI `10.1145/3360607`) fuse QuickChick's invariant-preserving generators with AFL-style edge-coverage guidance (`fuzz/Fuzz.ml:1-28`, `fuzz/SHM.c` in `QuickChick/QuickChick@ed334c76a7`, maintaining a $2^{16}$-entry `trace_bits` shared-memory bitmap via `setup_shm_prim_aux` and `copy_trace_bits`), mutating structured inputs to reach sparse semantic branches (e.g., abstract-machine noninterference bugs) without breaking syntactic validity.
3. **Separation-logic heap generator synthesis (`Bennet`, OOPSLA 2025)**: Aamer & Pierce (OOPSLA 2025, DOI `10.1145/3764115`) compile CN separation-logic preconditions directly into randomized C heap generators inside `rems-project/cn@d1c60d1720` (`lib/testGeneration/bennet/`). In `lib/testGeneration/bennet/bennet.ml:35-68`, `parse_domain` composes `AbstractDomains.Ownership` with product numeric/bitwise abstract domains (`WrappedInterval`, `Tristate`, `Congruence`) across a seven-stage compilation pipeline (`stage1/`–`stage7/`) with optional SMT pruning (`symbolic/`). One CN specification therefore drives randomized heap generation (`cn test`), runtime checking (`Fulminate`), and static verification (`cn verify`).

---

### 3. Runtime Separation-Logic Checking via Reified Ownership Ghost State (`CN` & `Fulminate`)

Basis: normative (Pulte et al. POPL 2023; Banerjee et al. POPL 2025) + source (`rems-project/cn@d1c60d1720`, `rems-project/cerberus@e29a8ec9f2`) + execution (`support/verify_spec_continuum_and_fulminate.py`).

#### Deterministic Computational Interpretation of CN's Fragment

General separation logic resists dynamic checking because $P * Q$ existentially quantifies over arbitrary heap splittings $h = h_1 \uplus h_2$. CN (Pulte, Makwana, T. Sewell, Memarian, P. Sewell & Krishnaswami, POPL 2023, DOI `10.1145/3571194`) restricts separation logic for predictable SMT proof automation of low-level C (including Google's pKVM hypervisor): it syntactically separates linear resource predicates (`Owned<cty>`, `Block<cty>` for uninitialized bytes, user-defined predicates, and bounded iterated separating conjunctions `each (bty x; guard) { p(...) }`) from pure boolean constraints, ordered sequentially as dependent telescopes (`take id = resource; constraint; let id = t`).

Banerjee, Memarian, Makwana, Pulte, Krishnaswami & Sewell (POPL 2025, Art. 43, DOI `10.1145/3704879`) show that these same restrictions yield a deterministic left-to-right operational semantics: evaluating `take id = Owned<cty>(ptr)` deterministically locates `[ptr, ptr + sizeof(cty))` and transfers its ownership without searching over heap partitions.

#### Five-Step Stack-Depth Ownership Protocol and Bisimulation Theorem

Fulminate compiles C+CN source to instrumented C maintaining one global reified ghost map $G : \mathrm{Addr} \rightharpoonup \mathrm{StackDepth}$ and a call-depth counter `cn_stack_depth` (Banerjee et al., POPL 2025, §2.3 & §3; `rems-project/cn@d1c60d1720`, `lib/fulminate/ownership.ml:25-39`, `lib/fulminate/fulminate.ml:27-91`, `runtime/libcn/src/cn-executable/utils.c:13-29, 309-630`):

1. **Creation**: Globals, parameters, and block-scoped locals call `c_add_to_ghost_state(ptr, size, stack_depth)` (`utils.c:452-457`) mapping their bytes to `cn_stack_depth`.
2. **Destruction**: Scope exits call `c_remove_from_ghost_state(ptr, size)` (`utils.c:468-471`) unmapping local footprints.
3. **Precondition acquisition (`PRE`)**: Function entry increments `cn_stack_depth` (`ghost_stack_depth_incr`, `utils.c:313-314`). Each `requires` resource calls `cn_get_ownership(ptr, size)` (`utils.c:478-487`), checking every byte is mapped to `cn_stack_depth - 1` (caller depth) and updating it to `cn_stack_depth` (callee depth). If an unverified caller aliases `Owned(p) * Owned(q)` with `p == q`, the second call sees depth `sd` instead of `sd - 1` and traps immediately.
4. **Postcondition return (`POST`) & leak check**: Function exit calls `cn_put_ownership(ptr, size)` (`utils.c:510-520`, moving `sd -> sd - 1`), decrements `cn_stack_depth` (`utils.c:322-323`), and runs `cn_postcondition_leak_check()` (`utils.c:330-338`), checking `rmap_find_range(0UL, -1UL, cn_ownership_global_ghost_state).max <= cn_stack_depth` to catch unreturned resources. Loops use parallel framing (`cn_loop_get_ownership`, `cn_loop_put_back_ownership`, `cn_loop_leak_check`; `utils.c:343-395, 489-508`).
5. **Per-access frame enforcement (`C_ACCESS`)**: `collect_memory_accesses` (`fulminate.ml:27-91`) instruments every C `Load`, `Store`, `StoreOp`, and `Postfix` lvalue with `c_ownership_check(..., cn_stack_depth, C_ACCESS)` (`utils.c:585-630`), catching reads or writes to live caller-owned memory omitted from `requires`.

Banerjee et al. (POPL 2025, Theorems 3.4 & 3.5, Corollary 3.6) prove exact **bisimulation** between an abstract per-frame resource-passing semantics $c_r = \langle e, S_r, H, R \rangle$ and the flat ghost-map semantics $c_g = \langle e, S, H, G \rangle$:

$$G = \biguplus_{i=0}^{\mathrm{sd}-1} \{ n \mapsto i \mid \mathrm{Owned}(n) \in R_i \} \uplus \{ n \mapsto \mathrm{sd} \mid \mathrm{Owned}(n) \in R \}, \qquad \mathrm{check\_res}(n \in R) \iff \mathrm{check\_imp}(G(n) = \mathrm{sd}).$$

#### Evolution from POPL 2025 Prototype to Pinned `rems-project/cn` & Cost Profile

- **Standalone extraction**: `backend/cn/` is no longer in `rems-project/cerberus@e29a8ec9f2`; CN, Fulminate, and Bennet live in `rems-project/cn@d1c60d1720` with unified CLI subcommands (`bin/main.ml:7-13`: `wf`, `verify`, `test`, `instrument`, `seq-test`).
- **Radix-tree interval map (`rmap`)**: `runtime/libcn/include/cn-executable/rmap.h:15-30` and `utils.c:13, 435-606` represent `ownership_ghost_state` as an interval map with range extrema queries (`rmap_find_range(k0, k1, map) -> {min, max}`), verifying contiguous multi-byte regions in one check when `res.min == res.max == expected_stack_depth` and scanning byte-by-byte only on errors (`utils.c:609-630`).
- **Partial boundaries & interactive inference**: `utils.h:27-38` and `utils.c:441-449, 558-615` add `WILDCARD_DEPTH` (exempting unverified memory) and `correct_missing_ownership` (reporting and repairing missing ownership entries mid-run to surface multiple missing frame clauses at once).
- **Measured costs & limits**: On Google's pKVM buddy allocator (Banerjee et al., POPL 2025, §5.4), instrumentation generation took ~30 s, synthetic bugs were caught in 0.4–1.4 s, and per-dynamic-`Owned` cost measured **0.3–0.9 μs** on the largest examples. Cost grows polynomially in recursive data-structure size due to predicate re-traversal across recursive calls, and temporary instrumentation objects use a non-freeing bump allocator (`runtime/libcn/include/cn-executable/bump_alloc.h`).
- **Companion probe verification (`support/verify_spec_continuum_and_fulminate.py`, Part 1)**: Instrumenting `checked_swap(p, q)` passes on disjoint cells (`owned_checks=4`, caller cell `r` preserved) and dynamically catches aliased `swap(p, p)` (`OwnershipAliasingError`), unauthorized read of caller cell `r` (`FrameViolationError`), unreturned `Owned(q)` (`OwnershipLeakError`), and corrupted output (`PostconditionViolationError`).

---

### 4. Gradual Verification (`? * P`), Check Minimization, and the Iso-/Equirecursive Soundness Hazard

Basis: normative (Bader, Aldrich & Tanter VMCAI 2018; Wise et al. OOPSLA 2020; Zimmerman, DiVincenzo & Aldrich POPL 2024; DiVincenzo et al. TOPLAS 2025) + source (`gradual-verification/gvc0@4276d89421`, `gradual-verification/silicon-gv@03a17ab4e7`) + execution (`support/verify_spec_continuum_and_fulminate.py`).

#### Imprecise Specifications, Residual Weaving, and Runtime Framing Overhead

Bader, Aldrich & Tanter (VMCAI 2018, DOI `10.1007/978-3-319-73721-8_2`) introduced **imprecise formulas** `? * P` that are optimistically strengthened statically whenever consistent with a proof goal, inserting residual runtime checks only where static precision is absent and rejecting provably contradictory partial specs at compile time. Wise, Bader, Wong, Aldrich, Tanter & Sunshine (OOPSLA 2020, DOI `10.1145/3428296`) extended gradual verification to recursive heap data structures under **implicit dynamic frames (IDF)** (`acc(x->f)` and recursive predicates), but their WLP semantics checked *every* obligation dynamically regardless of static proofs.

DiVincenzo et al. (`arXiv:2210.02428` / ACM TOPLAS 2025, DOI `10.1145/3704808`) built **Gradual C0** (`gradual-verification/gvc0@4276d89421`) atop a gradual symbolic-execution fork of Viper (`gradual-verification/silicon-gv@03a17ab4e7`):

- **Runtime permission tracking (`OwnedFields` vs. `Runtime.md`)**: While early note `gvc0/Runtime.md:5-18` sketches per-field `bool value_perm` struct fields, the actual implementation (`src/main/resources/runtime.h0:1-24`, `src/main/scala/gvc/weaver/CheckRuntime.scala:32-63`, `docs/baseline_perm_tracking.md:1-27`) tags each struct instance with `_id` (`_instanceCounter`) and passes an `OwnedFields` Robin-Hood hash table (`FieldArray { int psl; int id; int length; int accessible; bool[] contents; }`). Precise preconditions split a fresh `_contextFields` subset from the caller's `_ownedFields` (framing untouched permissions) and rejoin on return; imprecise preconditions pass the caller's `_ownedFields` directly.
- **Residual check weaving**: `src/main/scala/gvc/weaver/Weaver.scala:7-21` runs `Collector.collect` $\to$ `CheckScope.scope` $\to$ `Dependencies.calculate` $\to$ `Checker.insert`, weaving only checks emitted under static optimism. `SeparationChecks.scala:7-34` elides overlap checks when `canOverlap(spec) = countAccs(spec) > 1` is false (conservatively scoring `PredicateInstance` as `2`).
- **Overhead profile**: Gradual C0 cuts runtime overhead by **11–34% on average** compared to Wise et al.'s fully dynamic baseline and drops to zero residual checks at full precision, while exhibiting predictable worst-case overhead cliffs whenever imprecise recursive predicates force repeated $O(n)$ heap traversals inside loops or recursion.

#### The POPL 2024 Iso-/Equirecursive Soundness Bug and Exclusion-Frame Fix

While proving soundness for Gradual C0 and a core subset of Viper, Zimmerman, DiVincenzo & Aldrich (POPL 2024, DOI `10.1145/3632927`, `arXiv:2311.07559` §8.1–8.3) uncovered a subtle **soundness bug** in Gradual C0's check minimization (`arXiv:2311.07559`, Fig. 14):

```c
struct Cell { int value; }
predicate imprecise() = ? * true

void set(Cell c, int v)
  requires imprecise()
  ensures true
{
  unfold imprecise();
  c.value = v; // gradual symbolic execution emits dynamic check acc(c.value)
}

int test()
  requires true
  ensures result == 0
{
  fold imprecise();       // static H = { imprecise() } (isorecursive)
  Cell c = alloc(Cell);   // static H = { imprecise(), value(t1, _) }
  c.value = 0;            // static H = { imprecise(), value(t1, 0) }
  set(c, 1);              // statically consumes imprecise(); c.value == 0 stays framed!
  result = c.value;       // statically proved result == 0 -> postcondition check ELIDED!
}
```

**Mechanism of unsoundness**: Static symbolic execution interprets predicates **isorecursively**, so consuming `imprecise()` at `set(c, 1)` leaves `value(t1, 0)` framed in `test()`'s static heap and optimizes away `test()`'s runtime `result == 0` check. Dynamic execution, however, interprets `imprecise()` **equirecursively** (`fold`/`unfold` are no-ops), sees `? * true`, and passes *all* of `test()`'s caller permissions $\alpha$—including `acc(c.value)`—to `set(c, 1)`. `set`'s dynamic `acc(c.value)` check succeeds, `c.value` becomes `1`, and `test()` silently returns `1`, **violating its statically verified postcondition `ensures result == 0`**.

**Why the exclusion frame $\hat{\alpha}$ fixes it cleanly (`arXiv:2311.07559` §8.3)**: Clearing the static heap on imprecise predicate consumption or dropping imprecise predicates on `alloc` destroys static check minimization and contradicts Wise et al.'s semantics of `?` (a predicate folded at line 14 cannot hold permissions to an object allocated at line 15). Instead, symbolic execution computes an **exclusion frame** $\hat{\alpha}$ of caller permissions statically framed across the call (`{c.value}`) and passes $\alpha \setminus \hat{\alpha}$ dynamically to `set`. `set`'s dynamic `acc(c.value)` check then traps immediately, preserving both soundness and check minimization.

**Companion probe verification (`support/verify_spec_continuum_and_fulminate.py`, Part 2)**: Demonstrates monotonic residual-check reduction (`4 -> 3 -> 1 -> 0` across refinement stages) and directly reproduces Figure 14: naive mode returns `1` (`soundness_preserved=false`), whereas exclusion-frame mode traps at `set`'s write (`Missing dynamic acc(1.value) on write`, `soundness_preserved=true`).

---

### 5. Unified Multi-Engine Harnesses Across Fuzzing, PBT, and Bounded Model Checking

Basis: source (`camshaft/bolero@968b6b3510`, `model-checking/kani@c25a57bcbf`, `GaloisInc/crucible@2e37f7e1f0`, `rems-project/cn@d1c60d1720`, `QuickChick/QuickChick@ed334c76a7`) + documentation + derived.

Single-harness multi-engine tools prevent contract duplication across unit tests, fuzzers, and model checkers, though each introduces concrete boundedness and vacuity seams:

| Tool / Pinned Revision | Shared Spec / Harness Artifact | Backends | Modular Contract Support | Counterexample Playback | Key Boundedness / Vacuity Seam |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`Bolero` v0.13.7** (`camshaft/bolero@968b6b3510`) | Rust `bolero::check!()` + `TypeGenerator` / `ValueGenerator` / optional `arbitrary::Arbitrary` | `LibFuzzerEngine`, `AflEngine`, `HonggfuzzEngine`, `KaniEngine`, `TestEngine` (`corpus`/`crashes` + `rand_xoshiro` + `exhaustive::Driver`) | Delegates to Kani attributes; no native contract language | Saves failing inputs under `crashes/` for `cargo test` replay | `bolero-kani` hard-caps slices at `MAX_LEN = 256`; `kani::cover!(was_valid, ...)` does not fail vacuous generators (`kani#2792`). No `proptest` backend. |
| **`Kani`** (`model-checking/kani@c25a57bcbf`) | Rust `#[kani::proof]`, `#[kani::requires]`, `#[kani::ensures]`, `#[kani::modifies]`, `#[kani::recursion]` | CBMC bit-precise BMC over `rustc` MIR | `__kani_check_<fn>` (assume pre / assert post) & `__kani_replace_<fn>` (assert pre / havoc / assume post); `#[kani::stub_verified]` | `-Z concrete-playback` emits `#[test]` calling `kani::concrete_playback_run(Vec<Vec<u8>>, harness)` | Playback skips non-panic UB checks (`concrete-playback.md:81-83`) and multiple failures; stubbed return `Arbitrary` cannot re-enter stubbed fn. |
| **`Crux-MIR`** (`GaloisInc/crucible@2e37f7e1f0`) | Rust `#[crux::test]` + `crux-test-gen` typed grammars | Crucible symbolic simulation over `mir-json` (schema v14) + Yices / Z3 | Function overrides (`src/Mir/Overrides.hs`) | Solver counterexample models; grammar test synthesis | Tightly coupled to `mir-json` schema (~2-release retention; breaks across Rust toolchain bumps). |
| **`CN` + `Fulminate` + `Bennet`** (`rems-project/cn@d1c60d1720`) | C `/*@ requires ... ensures ... @*/` separation-logic refinement types | `cn verify` (SMT), `cn instrument` (`Fulminate`), `cn test` (`Bennet` PBT), `cn seq-test` | Native SL modular pre/postconditions + Coq/Lean lemma export (`cn_to_coq.ml`, `lemmata_lean.ml`) | Failing C test harnesses with concrete heap traces | Polynomial runtime cost on recursive predicates; non-freeing bump allocator (`bump_alloc.h`). |
| **`QuickChick`** (`QuickChick/QuickChick@ed334c76a7`) | Rocq/Coq `Prop` specs & inductive relations | Extracted OCaml random/exhaustive testing, `FuzzChick` (AFL shm), Rocq proofs | Full Rocq theorems + certified `CorrectSizedST` generators | Shrunk counterexamples in Rocq/OCaml | Extraction trust gap unless witness is replayed inside kernel. |

#### Source-Verified Mechanics in `Bolero`, `Kani`, and `Crux-MIR`

- **`Bolero` engine dispatch & `bolero-kani` seams (`camshaft/bolero@968b6b3510`)**: `lib/bolero/src/lib.rs:7-24` and `lib/bolero/Cargo.toml:25-44` dispatch `DefaultEngine` via `cfg_if!` across `fuzzing_libfuzzer`, `fuzzing_afl`, `fuzzing_honggfuzz`, `kani`, and fallback `TestEngine` (`lib/bolero/src/test/mod.rs:1-90`). Inspection of `Cargo.toml` manifests and `CHANGELOG.md` confirms Bolero v0.13.7 uses its own `bolero-generator` plus optional `arbitrary = "1.0"`, with no `proptest` backend. In `lib/bolero-kani/src/lib.rs:32-42, 85-90`, `KaniInput::with_slice` bounds symbolic slices to `const MAX_LEN: usize = 256`, and `KaniEngine::run` emits `kani::cover!(was_valid, "the generator should produce at least one valid value")` with a `TODO` referencing `model-checking/kani#2792` because unsatisfiable filters otherwise pass silently.
- **`Kani` inductive contracts & concrete playback (`model-checking/kani@c25a57bcbf`)**: To avoid unrolling deep loops or recursion (e.g., up to ~96 steps for 64-bit `gcd`; `docs/src/reference/experimental/contracts.md:16-19`), `library/kani_macros/src/sysroot/contracts/mod.rs:13-90` uses a two-phase proc-macro state machine (handling outside-in single-attribute expansion and renamed attributes) to synthesize `__kani_check_<fn>` (assuming `requires`, injecting `ensures` before every `return` via `PostconditionInjector`) and `__kani_replace_<fn>` (asserting `requires`, havocking returns via `kani::any()`, assuming `ensures`). For `#[kani::recursion]`, a global re-entry flag flips from `false` to `true` on entry to `__kani_check_<fn>`, routing recursive self-calls to `__kani_replace_<fn>` for 1-step inductive verification. On failure, `-Z concrete-playback` (`docs/src/reference/experimental/concrete-playback.md:1-88`, `kani-driver/src/concrete_playback/playback.rs:73-90`) serializes CBMC witness bytes into a runnable `#[test]` calling `kani::concrete_playback_run`, but explicitly omits non-panic UB checks (which do not trap in native Rust execution) and multi-failure harnesses.
- **`Crux-MIR` (`GaloisInc/crucible@2e37f7e1f0`)**: `crux-mir/README.md:51-65` and `crux-mir/overview.md:1-80` ingest `mir-json` schema v14, apply MIR rewrites (`NoMutParams`, `AllocateEnum`, `AssociatedTypes`, `ExpandSuperTraits`), translate into Crucible CFGs (`Mir.Trans`), and discharge symbolic assertions via Yices/Z3, complemented by typed grammar generation in `crux-test-gen/README.md:1-80`.

---

### 6. Epistemic Asymmetry and Promoting Untrusted Counterexamples to Kernel Refutations

Basis: normative (first-order/constructive logic; Blanchette & Nipkow ITP 2010; Bulwahn CPP 2012) + execution (`support/verify_spec_continuum_and_fulminate.py`) + derived.

Conflating **proof checking** (universal soundness inside a minimal TCB) with **fast epistemic truth discovery** forces users and automated provers to pay heavy kernel-reduction costs on false claims. The continuum resolves this through a sharp logical asymmetry.

#### The Verification-vs-Falsification Asymmetry

For a universally quantified executable claim $\Phi \equiv \forall x \in D,\, P(x) \implies Q(x, \llbracket f \rrbracket(x))$:

- **Proving $\Phi$** must cover every $x \in D$ inside the TCB; any unsoundness in a solver, fuzzer, or abstraction invalidates the proof unless independently checked.
- **Disproving $\Phi$ ($\vdash \neg \Phi$)** requires only one concrete witness $x_0$ passing three ground checks inside the tiny trusted kernel evaluator: (1) $x_0 \in D$, (2) $\mathsf{eval}_{\mathrm{kernel}}(P(x_0)) = \mathsf{true}$, and (3) $\mathsf{eval}_{\mathrm{kernel}}(Q(x_0, \llbracket f \rrbracket(x_0))) = \mathsf{false}$. From (1)–(3), the kernel derives $\exists x \in D,\, P(x) \land \neg Q(x, \llbracket f \rrbracket(x)) \vdash \neg \Phi$ at **`trust_level = 0`**—with **zero TCB dependence** on how $x_0$ was discovered (fuzzer, PRNG, native binary, or SMT solver).

#### Why Kernel Replay Is Essential: Lessons from ITP Counterexample Finders

Untrusted counterexamples must never bypass trusted replay: **Isabelle/HOL `Nitpick`** (Blanchette & Nipkow, ITP 2010, DOI `10.1007/978-3-642-14052-5_11`) maps HOL goals to finite Kodkod/SAT models and must separate *genuine* from *potential* (potentially spurious) counterexamples caused by finite-scope truncation or partial axiomatizations; **Isabelle `Quickcheck`** (Bulwahn, CPP 2012, DOI `10.1007/978-3-642-35308-6_10`) runs random, exhaustive, and narrowing tests via compiled code generation, where code-equation mismatches can still yield unverified traces unless re-checked in the kernel.

#### Four-Tier Evidence Stratification

| Evidence Tier | TCB Scope | Typical Engines | Positive Authority | Refutation Authority |
| :--- | :--- | :--- | :--- | :--- |
| **Tier 0: Kernel-Checked Proof / Refutation** | `trust_level = 0` (minimal kernel + locked semantics) | Dependent-type kernel proof or kernel-replayed witness $\langle x_0, \pi \rangle$ | **Unconditional** (relative to kernel + semantics) | **Unconditional** (`¬Φ` minted; halts doomed VCGen) |
| **Tier 1: Conditional Deductive Proof** | Kernel + hash-locked environment/FFI assumptions | Modular proofs with `Assumptions.*` or `#[kani::stub_verified]` over unproved FFI | **Conditional** on explicit assumption manifest | Promotes to Tier 0 if witness avoids unmodeled assumptions |
| **Tier 2: Provisional Symbolic / Native Eval** | Kernel + external SMT/BMC or native evaluator (`Lean.ofReduceBool`, `vm_compute`) | Unreconstructed Z3/CVC5, `Kani`, `Crux-MIR`, native evaluators | **Provisional only** (fenced from final Tier 0 certs) | Concrete witness **promotes to Tier 0** on kernel replay; spurious models rejected |
| **Tier 3: Untrusted Empirical Fuzzing / PBT** | Zero TCB weight | `QuickCheck`, `QuickChick`/`FuzzChick`, `Bolero`, `Fulminate`, `Bennet` | **None** | Failing witness **promotes to Tier 0** on kernel replay; short-circuits proof search |

#### Companion Probe Execution (`support/verify_spec_continuum_and_fulminate.py`, Part 4)

Part 4 pairs a ~30-line `TrustedRefutationKernel` with an untrusted boundary/PRNG fuzzer:

- **Spurious witness rejection**: All three adversarial/forged witnesses—`out_of_domain` `(-1, 8)`, `precondition_violated_non_pow2` `(10, 3)`, and `postcondition_actually_holds` `(13, 8)`—are rejected with `SpuriousWitnessError`.
- **Contract & loop-invariant refutation short-circuiting VCGen**: The untrusted fuzzer discovers both a wrapping `u32` alignment overflow witness `[4294967295, 2] -> 0` (promoted to `trust_level = 0`, `cert_sha256_prefix = "3a4a48ea82370097"`) and a preservation counterexample `[362, 896]` (`observed_next_acc = 167 != 65703`) against a buggy `u16` triangular-sum loop invariant (`trust_level = 0`, `cert_sha256_prefix = "cc4567782a76bda1"`), short-circuiting expensive deductive VCGen (`expensive_vcgen_short_circuited = true`).

## Boundaries

- **not examined**:
  - **Concurrent and weak-memory runtime ownership monitoring**: Neither `Fulminate` (`rems-project/cn@d1c60d1720`) nor `Gradual C0` (`gradual-verification/gvc0@4276d89421`) was evaluated on multi-threaded shared-memory code or weak-memory models (RC11/IMM); Fulminate's stack-depth ghost map assumes a single sequential call stack.
  - **Gradual dependent type theory (GCIC / fire triangle)**: Scope is restricted to gradual imperative/heap *program verification* (`? * P`), not gradual dependent type systems.
  - **Local compilation and timing of pKVM or `cc0` benchmarks**: Reported microsecond and percentage figures are taken directly from peer-reviewed primary papers rather than locally re-benchmarked.
  - **Auto-active VCGen counterexample internals (`Dafny`, `F*`, `Why3`, `Viper`)**: Covered in `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures`.
- **unknown**:
  - **Live exclusion-frame status in `gradual-verification/gvc0@4276d89421`**: Source inspection confirmed `OwnedFields`, `SeparationChecks.scala`, and `Weaver.scala`, and `arXiv:2311.07559` (§8) documents reporting the bug and fix to the authors, but live compilation and execution of the Figure 14 `.c0` test case through `gvc0` + `silicon-gv` + `cc0` was not performed.
  - **Multi-year maintenance cost of unified CN + Fulminate + Bennet specs**: Published pKVM evaluations establish subsystem feasibility, not longitudinal churn costs across years of kernel refactoring.
- **known not to apply**:
  - **Claim that `camshaft/bolero` runs `proptest` as an engine**: At `968b6b3510acbc22123e035278b1665e671a4c21` (`v0.13.7`), `lib/bolero/src/lib.rs`, `Cargo.toml` manifests, and `CHANGELOG.md` show Bolero uses `bolero-generator` + optional `arbitrary` across `LibFuzzerEngine`, `AflEngine`, `HonggfuzzEngine`, `KaniEngine`, and `TestEngine`—with no `proptest` backend.
  - **Claim that CN/Fulminate still live in `rems-project/cerberus/backend/cn/`**: Absent at `rems-project/cerberus@e29a8ec9f2`; moved to `rems-project/cn@d1c60d1720`.
  - **Claim that kernel counterexample promotion handles non-executable specs**: Ground replay only refutes claims whose domain, preconditions, step semantics, and postconditions are concretely decidable/executable; unbounded higher-order quantifiers, non-constructive existential ghost state, or unspecified demonic UB cannot be refuted by concrete ground evaluation alone.
  - **Claim that `bolero-kani` proves unbounded slices or generator satisfiability**: `lib/bolero-kani/src/lib.rs:34-41, 87` caps slices at `MAX_LEN = 256` and emits non-failing `kani::cover!` (`kani#2792`).
- **unsupported**:
  - **Concrete playback of non-panic UB checks in Kani**: `model-checking/kani@c25a57bcbf` (`docs/src/reference/experimental/concrete-playback.md:81-86`) explicitly documents that `-Z concrete-playback` does not generate unit tests for non-panic UB checks or multiple assertion failures in one harness.
  - **Instrumentation memory reclamation and thread safety in Fulminate**: `rems-project/cn@d1c60d1720` (`bump_alloc.h`, `utils.c:15-21`) and Banerjee et al. (POPL 2025, §5.4) rely on a non-freeing bump allocator and unsynchronized single-threaded global ghost state.

## Evidence

All bibliographic records, pinned repository inspections, and probe executions were verified on **2026-11-19**.

### Primary Publications

- Claessen & Hughes, *QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs*, ICFP 2000, pp. 268–279, DOI `10.1145/351240.351266`.
- Klein et al., *seL4: Formal Verification of an OS Kernel*, SOSP 2009, DOI `10.1145/1629575.1629596`; *Comprehensive Formal Verification of an OS Microkernel*, ACM TOCS 2014, DOI `10.1145/2560537`.
- Blanchette & Nipkow, *Nitpick: A Counterexample Generator for Higher-Order Logic Based on a Relational Model Finder*, ITP 2010, DOI `10.1007/978-3-642-14052-5_11`.
- Yang, Chen, Eide & Regehr, *Finding and Understanding Bugs in C Compilers*, PLDI 2011, DOI `10.1145/1993498.1993532`.
- Bulwahn, *The New Quickcheck for Isabelle: Random, Exhaustive and Symbolic Testing under One Roof*, CPP 2012, DOI `10.1007/978-3-642-35308-6_10`.
- Newcombe, Rath, Zhang, Munteanu, Brooker & Deardeuff, *How Amazon Web Services Uses Formal Methods*, CACM 58(4):66–73, 2015, DOI `10.1145/2699417`.
- Matichuk, Murray, Andronick, Jeffery, Klein & Staples, *Empirical Study Towards a Leading Indicator for Cost of Formal Software Verification*, ICSE 2015, DOI `10.1109/ICSE.2015.85`.
- Fonseca, Zhang, Wang & Krishnamurthy, *An Empirical Study on the Correctness of Formally Verified Distributed Systems*, EuroSys 2017, DOI `10.1145/3064176.3064183`.
- Lampropoulos, Paraskevopoulou & Pierce, *Generating Good Generators for Inductive Relations*, PACMPL 2(POPL), 2018, DOI `10.1145/3158133`.
- Bader, Aldrich & Tanter, *Gradual Program Verification*, VMCAI 2018, DOI `10.1007/978-3-319-73721-8_2`.
- Lampropoulos, Hicks & Pierce, *Coverage Guided, Property Based Testing*, PACMPL 3(OOPSLA), 2019, DOI `10.1145/3360607`.
- Wise, Bader, Wong, Aldrich, Tanter & Sunshine, *Gradual Verification of Recursive Heap Data Structures*, PACMPL 4(OOPSLA), 2020, DOI `10.1145/3428296`.
- Bornholt et al., *Using Lightweight Formal Methods to Validate a Key-Value Storage Node in Amazon S3*, SOSP 2021, DOI `10.1145/3477132.3483540`.
- Pulte, Makwana, T. Sewell, Memarian, P. Sewell & Krishnaswami, *CN: Verifying Systems C Code with Separation-Logic Refinement Types*, PACMPL 7(POPL), Art. 1, 2023, DOI `10.1145/3571194`.
- Zimmerman, DiVincenzo & Aldrich, *Sound Gradual Verification with Symbolic Execution*, PACMPL 8(POPL), 2024, DOI `10.1145/3632927`, `arXiv:2311.07559` (PDF §2.1, §2.8, §8.1–8.3, Fig. 14 inspected directly).
- DiVincenzo, McCormack, Gouni, Gorenburg, Ramos-Dávila, Zhang, Zimmerman, Sunshine, Tanter & Aldrich, *Gradual C0: Symbolic Execution for Gradual Verification*, ACM TOPLAS 2025, DOI `10.1145/3704808`, `arXiv:2210.02428`.
- Banerjee, Memarian, Makwana, Pulte, Krishnaswami & Sewell, *Fulminate: Testing CN Separation-Logic Specifications in C*, PACMPL 9(POPL), Art. 43, 2025, DOI `10.1145/3704879` (open-access PDF §2.3–2.4, §3 Thms. 3.4–3.5 & Cor. 3.6, §5.4 inspected directly).
- Aamer & Pierce, *Bennet: Randomized Specification Testing for Heap-Manipulating Programs*, PACMPL 9(OOPSLA), 2025, DOI `10.1145/3764115`.

### Pinned Upstream Repository Source Inspections

- **`rems-project/cn` @ `d1c60d1720bed3bed0d45dab247a1959145c8cb9`**: `bin/main.ml:7-13`; `lib/fulminate/{ownership.mli:20-38,ownership.ml:25-39,fulminate.ml:27-91,extract.ml:20-66}`; `runtime/libcn/include/cn-executable/{utils.h:18-45,rmap.h:15-30,bump_alloc.h}`; `runtime/libcn/src/cn-executable/utils.c:13-29,309-395,441-630`; `lib/testGeneration/bennet/bennet.ml:35-68`.
- **`rems-project/cerberus` @ `e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e`**: `backend/` directory confirming extraction of `cn/` to `rems-project/cn`.
- **`gradual-verification/gvc0` @ `4276d89421d9fc17058a06cff975e9c7207ab917`** & **`gradual-verification/silicon-gv` @ `03a17ab4e796683d36cf203572ec93d572f69c3f`**: `Runtime.md:1-25`, `docs/baseline_perm_tracking.md:1-27`, `Validation.md:1-49`, `Transformation.md:1-55`, `src/main/resources/runtime.h0:1-24`, `src/main/scala/gvc/weaver/{CheckRuntime.scala:32-63,Weaver.scala:7-21,SeparationChecks.scala:6-100}`.
- **`QuickChick/QuickChick` @ `ed334c76a7fbd6eefe9b1e618e42ce9c70dd8691`**: `src/DependentClasses.v:13-70`, `src/Decidability.v:17`, `plugin/arbitrarySizedST.ml`, `fuzz/Fuzz.ml:1-28`.
- **`camshaft/bolero` @ `968b6b3510acbc22123e035278b1665e671a4c21` (`v0.13.7`)**: `lib/bolero/{src/lib.rs:7-24,Cargo.toml:14-57,src/test/mod.rs:1-90}`, `lib/bolero-generator/Cargo.toml:14-41`, `lib/bolero-kani/src/lib.rs:24-90`.
- **`model-checking/kani` @ `c25a57bcbf8c8af41617e7171a535a3518ce514a`**: `docs/src/reference/experimental/{contracts.md:1-74,concrete-playback.md:1-88}`, `library/kani_macros/src/sysroot/contracts/mod.rs:13-90`, `kani-driver/src/concrete_playback/playback.rs:73-90`.
- **`GaloisInc/crucible` @ `2e37f7e1f06730125075e4b1ec1d19b8af5736cb`**: `crux-mir/{README.md:51-65,overview.md:1-80}`, `crux-test-gen/README.md:1-80`.

### Preserved Standalone Executable Probe

- **Script**: `support/verify_spec_continuum_and_fulminate.py` (Python 3.10+, standard library only).
- **Command**: `python3 -B reports/specification-authoring-spec-drift-and-the-testing-verification-continuum/support/verify_spec_continuum_and_fulminate.py`
- **Observed deterministic result (2026-11-19, exit `0`)**:
  - `fulminate_ownership_monitor`: disjoint `swap` passes (`owned_checks=4`, `p_after=20`, `q_after=10`, `r_framed=99`); catches `OwnershipAliasingError`, `FrameViolationError`, `OwnershipLeakError`, and `PostconditionViolationError`.
  - `gradual_verification_and_popl24`: residual checks drop `4 -> 3 -> 1 -> 0` (0% $\to$ 100% reduction); naive Fig. 14 returns `1` (`soundness_preserved=false`); exclusion-frame Fig. 14 traps at callee write (`soundness_preserved=true`).
  - `precondition_sparsity`: naive generate-and-filter `0/10000` (`100.0%` discard) vs. constructive inductive generator `1000/1000` (`0.0%` discard).
  - `counterexample_promotion`: rejects 3 spurious witnesses (`out_of_domain`, `precondition_violated_non_pow2`, `postcondition_actually_holds`); promotes wrapping `u32` alignment witness `[4294967295, 2] -> 0` (`trust_level=0`, `cert_sha256_prefix="3a4a48ea82370097"`) and buggy `u16` loop-invariant witness `[362, 896] -> 167 != 65703` (`trust_level=0`, `cert_sha256_prefix="cc4567782a76bda1"`); `expensive_vcgen_short_circuited=true`.

## Revalidation

1. **Re-run the standalone probe**:
   ```console
   python3 -B reports/specification-authoring-spec-drift-and-the-testing-verification-continuum/support/verify_spec_continuum_and_fulminate.py
   ```
   A zero exit code re-verifies the Fulminate stack-depth transitions, POPL 2024 exclusion-frame behavior, precondition-sparsity benchmark, and `TrustedRefutationKernel` witness gate.
2. **Diff `rems-project/cn` runtime and Bennet domains**: Check `runtime/libcn/src/cn-executable/utils.c`, `runtime/libcn/include/cn-executable/{rmap.h,bump_alloc.h}`, and `lib/testGeneration/bennet/bennet.ml` for concurrent ownership tracking, instrumentation memory reclamation, fractional permissions, or additional abstract domains beyond `d1c60d1720bed3bed0d45dab247a1959145c8cb9`.
3. **Check `camshaft/bolero` and `model-checking/kani` seams**: Inspect `lib/bolero-kani/src/lib.rs` (for configurable `MAX_LEN` and resolution of `model-checking/kani#2792`), `lib/bolero/Cargo.toml` (for new engines beyond v0.13.7), and `model-checking/kani` `docs/src/reference/experimental/{contracts.md,concrete-playback.md}` (for contract stabilization or non-panic UB playback).
4. **Verify live exclusion-frame execution in `gradual-verification/gvc0`**: Compile and run the 19-line Figure 14 `.c0` test case from `arXiv:2311.07559` against `gvc0` + `silicon-gv` + `cc0` whenever a C0 toolchain is available to confirm whether live HEAD enforces exclusion frames dynamically.
